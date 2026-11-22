// Tiny stack VM, make.fun tiny-stack-vm-01, ISA v1. Fresh implementation from
// ISA.md (vm.mjs as tie-breaker). Runs every program under MAKEFUN_INPUT_DIR;
// per instance id writes stdout.bin and exit.txt into MAKEFUN_OUTPUT_DIR.
// Plain `node`, stdlib only. Deterministic.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const STACK = 256, CALLS = 64, WORDS = 256, STEPS = 1_000_000, OUT = 65_536;

function run(p: Uint8Array, inp: Uint8Array): { out: Uint8Array; code: number } {
  const n = p.length;
  const st = new Int32Array(STACK), cs = new Int32Array(CALLS), mem = new Int32Array(WORDS);
  const buf = new Uint8Array(OUT);
  let sp = 0, cp = 0, ol = 0, ip = 0, pc = 0, steps = 0;
  const end = (code: number) => ({ out: buf.slice(0, ol), code });
  // Single dispatch: each case checks its own immediate cutoff, stack
  // underflow and overflow first, in the same order the separate decode
  // pass used to (imm cutoff 9, underflow 2, overflow 3), then executes.
  // Traps end the run, so counting a trapping step is unobservable.
  for (;;) {
    if (steps === STEPS) return end(10);
    if (pc < 0 || pc >= n) return end(9);
    const op = p[pc];
    steps++;
    switch (op) {
      case 0x00: return end(0); // HALT
      case 0x01: // PUSH8, sign-extended
        if (pc + 1 >= n) return end(9);
        if (sp >= STACK) return end(3);
        st[sp++] = (p[pc + 1] << 24) >> 24;
        pc += 2;
        break;
      case 0x02: // PUSH32 LE
        if (pc + 4 >= n) return end(9);
        if (sp >= STACK) return end(3);
        st[sp++] = p[pc + 1] | (p[pc + 2] << 8) | (p[pc + 3] << 16) | (p[pc + 4] << 24);
        pc += 5;
        break;
      case 0x03: // POP
        if (sp < 1) return end(2);
        sp--;
        pc++;
        break;
      case 0x04: // DUP
        if (sp < 1) return end(2);
        if (sp >= STACK) return end(3);
        st[sp] = st[sp - 1]; sp++;
        pc++;
        break;
      case 0x05: // SWAP
        if (sp < 2) return end(2);
        { const t = st[sp - 1]; st[sp - 1] = st[sp - 2]; st[sp - 2] = t; }
        pc++;
        break;
      case 0x06: // OVER
        if (sp < 2) return end(2);
        if (sp >= STACK) return end(3);
        st[sp] = st[sp - 2]; sp++;
        pc++;
        break;
      case 0x07: // ROT
        if (sp < 3) return end(2);
        { const a = st[sp - 3]; st[sp - 3] = st[sp - 2]; st[sp - 2] = st[sp - 1]; st[sp - 1] = a; }
        pc++;
        break;
      case 0x17: // NEG, wraps
        if (sp < 1) return end(2);
        st[sp - 1] = (-st[sp - 1]) | 0;
        pc++;
        break;
      case 0x1b: // NOT
        if (sp < 1) return end(2);
        st[sp - 1] = ~st[sp - 1];
        pc++;
        break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: { // ( a b -- r ), b on top
        if (sp < 2) return end(2);
        const b = st[sp - 1], a = st[sp - 2];
        let r: number;
        switch (op) {
          case 0x10: r = (a + b) | 0; break;
          case 0x11: r = (a - b) | 0; break;
          case 0x12: r = Math.imul(a, b); break; // low 32 bits
          case 0x13: if (b === 0) return end(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; break; // DIV truncates
          case 0x14: if (b === 0) return end(4); r = b === -1 ? 0 : (a % b) | 0; break; // MOD, sign of a
          case 0x15: if (b === 0) return end(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; break; // DIVU
          case 0x16: if (b === 0) return end(4); r = ((a >>> 0) % (b >>> 0)) | 0; break; // MODU
          case 0x18: r = a & b; break;
          case 0x19: r = a | b; break;
          case 0x1a: r = a ^ b; break;
          case 0x1c: r = a << (b & 31); break;
          case 0x1d: r = a >> (b & 31); break;
          case 0x1e: r = (a >>> (b & 31)) | 0; break;
          case 0x20: r = a === b ? 1 : 0; break;
          case 0x21: r = a < b ? 1 : 0; break;
          default: r = (a >>> 0) < (b >>> 0) ? 1 : 0; break; // LTU
        }
        st[sp - 2] = r; sp--;
        pc++;
        break;
      }
      case 0x30: { // JMP, signed offset from nx = pc + 3
        if (pc + 2 >= n) return end(9);
        pc = pc + 3 + (((p[pc + 1] | (p[pc + 2] << 8)) << 16) >> 16);
        break;
      }
      case 0x31: case 0x32: { // JZ/JNZ, signed offset from nx = pc + 3
        if (pc + 2 >= n) return end(9);
        if (sp < 1) return end(2);
        const v = st[--sp];
        const rel = ((p[pc + 1] | (p[pc + 2] << 8)) << 16) >> 16;
        pc = (op === 0x31) === (v === 0) ? pc + 3 + rel : pc + 3;
        break;
      }
      case 0x33: // CALL, unsigned absolute address
        if (pc + 2 >= n) return end(9);
        if (cp === CALLS) return end(7);
        cs[cp++] = pc + 3;
        pc = p[pc + 1] | (p[pc + 2] << 8);
        break;
      case 0x34: // RET
        if (cp === 0) return end(8);
        pc = cs[--cp];
        break;
      case 0x40: { // LOAD
        if (sp < 1) return end(2);
        const addr = st[sp - 1];
        if (addr < 0 || addr >= WORDS) return end(6);
        st[sp - 1] = mem[addr];
        pc++;
        break;
      }
      case 0x41: { // STORE: ( v addr -- ), addr on top
        if (sp < 2) return end(2);
        const addr = st[sp - 1];
        if (addr < 0 || addr >= WORDS) return end(6);
        mem[addr] = st[sp - 2]; sp -= 2;
        pc++;
        break;
      }
      case 0x50: { // PRINT: decimal ASCII; writes nothing if it would pass the limit
        if (sp < 1) return end(2);
        const s = String(st[sp - 1]);
        if (ol + s.length > OUT) return end(11);
        sp--;
        for (let i = 0; i < s.length; i++) buf[ol++] = s.charCodeAt(i);
        pc++;
        break;
      }
      case 0x51: // PUTC: one byte, v AND 255
        if (sp < 1) return end(2);
        if (ol + 1 > OUT) return end(11);
        buf[ol++] = st[--sp] & 255;
        pc++;
        break;
      case 0x52: // IN: next input byte, -1 once used up
        if (sp >= STACK) return end(3);
        st[sp++] = ip < inp.length ? inp[ip++] : -1;
        pc++;
        break;
      case 0x53: // EXIT
        if (sp < 1) return end(2);
        return end(st[--sp] & 255);
      default: return end(5); // unknown opcode
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(new Uint8Array(readFileSync(join(I, id, 'program.bin'))), new Uint8Array(readFileSync(join(I, id, 'input.bin'))));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), r.code + '\n');
}
