// tiny-stack-vm-02: exact, fast interpreter for make.fun's tiny stack ISA v1.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const IMM = new Uint8Array(256).fill(255);
const POP = new Uint8Array(256);
const PSH = new Uint8Array(256);
const def = (b: number, imm: number, pop: number, psh: number): void => {
  IMM[b] = imm; POP[b] = pop; PSH[b] = psh;
};
def(0x00, 0, 0, 0); // HALT
def(0x01, 1, 0, 1); // PUSH8
def(0x02, 4, 0, 1); // PUSH32
def(0x03, 0, 1, 0); // POP
def(0x04, 0, 1, 2); // DUP
def(0x05, 0, 2, 2); // SWAP
def(0x06, 0, 2, 3); // OVER
def(0x07, 0, 3, 3); // ROT
def(0x10, 0, 2, 1); // ADD
def(0x11, 0, 2, 1); // SUB
def(0x12, 0, 2, 1); // MUL
def(0x13, 0, 2, 1); // DIV
def(0x14, 0, 2, 1); // MOD
def(0x15, 0, 2, 1); // DIVU
def(0x16, 0, 2, 1); // MODU
def(0x17, 0, 1, 1); // NEG
def(0x18, 0, 2, 1); // AND
def(0x19, 0, 2, 1); // OR
def(0x1a, 0, 2, 1); // XOR
def(0x1b, 0, 1, 1); // NOT
def(0x1c, 0, 2, 1); // SHL
def(0x1d, 0, 2, 1); // SHR
def(0x1e, 0, 2, 1); // SHRU
def(0x20, 0, 2, 1); // EQ
def(0x21, 0, 2, 1); // LT
def(0x22, 0, 2, 1); // LTU
def(0x30, 2, 0, 0); // JMP
def(0x31, 2, 1, 0); // JZ
def(0x32, 2, 1, 0); // JNZ
def(0x33, 2, 0, 0); // CALL
def(0x34, 0, 0, 0); // RET
def(0x40, 0, 1, 1); // LOAD
def(0x41, 0, 2, 0); // STORE
def(0x50, 0, 1, 0); // PRINT
def(0x51, 0, 1, 0); // PUTC
def(0x52, 0, 0, 1); // IN
def(0x53, 0, 1, 0); // EXIT

const BAD = 255; // decoded marker: byte names no opcode -> trap 5
const CUT = 254; // decoded marker: immediate cut off by program end -> trap 9

function run(p: Uint8Array, inp: Uint8Array): { c: number; o: Uint8Array } {
  const n = p.length;
  const dc = new Uint8Array(n).fill(BAD);
  const ag = new Int32Array(n);
  for (let i = 0; i < n; i++) {
    const b = p[i];
    const im = IMM[b];
    if (im === 255) continue;
    if (i + 1 + im > n) { dc[i] = CUT; continue; }
    dc[i] = b;
    if (b === 0x01) ag[i] = (p[i + 1] << 24) >> 24; // PUSH8: sign-extended byte
    else if (b === 0x02) ag[i] = p[i + 1] | (p[i + 2] << 8) | (p[i + 3] << 16) | (p[i + 4] << 24);
    else if (b === 0x30 || b === 0x31 || b === 0x32) ag[i] = ((p[i + 1] | (p[i + 2] << 8)) << 16) >> 16;
    else if (b === 0x33) ag[i] = p[i + 1] | (p[i + 2] << 8);
  }
  const D = new Int32Array(256); // data stack
  const C = new Int32Array(64); // call stack
  const M = new Int32Array(256); // memory
  const out = new Uint8Array(65536);
  let sp = 0, cp = 0, pc = 0, ip = 0, ol = 0, s = 0;
  const trap = (k: number): { c: number; o: Uint8Array } => ({ c: k, o: out.subarray(0, ol) });
  for (;;) {
    if (s === 1000000) return trap(10);
    if (pc < 0 || pc >= n) return trap(9);
    const o = dc[pc];
    if (o === BAD) return trap(5);
    if (o === CUT) return trap(9);
    s++;
    if (sp < POP[o]) return trap(2); // stack underflow
    if (sp - POP[o] + PSH[o] > 256) return trap(3); // stack overflow
    pc = pc + 1 + IMM[o];
    switch (o) {
      case 0x00: return { c: 0, o: out.subarray(0, ol) }; // HALT
      case 0x01: case 0x02: D[sp++] = ag[pc - 1 - IMM[o]]; break;
      case 0x03: sp--; break; // POP
      case 0x04: D[sp] = D[sp - 1]; sp++; break; // DUP
      case 0x05: { const t = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = t; break; } // SWAP
      case 0x06: D[sp] = D[sp - 2]; sp++; break; // OVER
      case 0x07: { const a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break; } // ROT
      case 0x17: D[sp - 1] = -D[sp - 1] | 0; break; // NEG
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break; // NOT
      case 0x30: pc += ag[pc - 3]; break; // JMP
      case 0x31: if (D[--sp] === 0) pc += ag[pc - 3]; break; // JZ
      case 0x32: if (D[--sp] !== 0) pc += ag[pc - 3]; break; // JNZ
      case 0x33: // CALL
        if (cp === 64) return trap(7);
        C[cp++] = pc; pc = ag[pc - 3]; break;
      case 0x34: // RET
        if (cp === 0) return trap(8);
        pc = C[--cp]; break;
      case 0x40: { // LOAD
        const a = D[sp - 1];
        if (a < 0 || a > 255) return trap(6);
        D[sp - 1] = M[a]; break;
      }
      case 0x41: { // STORE
        const a = D[sp - 1];
        if (a < 0 || a > 255) return trap(6);
        M[a] = D[sp - 2]; sp -= 2; break;
      }
      case 0x50: { // PRINT
        const t = String(D[sp - 1]);
        if (ol + t.length > 65536) return trap(11);
        sp--;
        for (let i = 0; i < t.length; i++) out[ol++] = t.charCodeAt(i);
        break;
      }
      case 0x51: // PUTC
        if (ol + 1 > 65536) return trap(11);
        out[ol++] = D[--sp] & 255; break;
      case 0x52: D[sp++] = ip < inp.length ? inp[ip++] : -1; break; // IN
      case 0x53: return { c: D[--sp] & 255, o: out.subarray(0, ol) }; // EXIT
      default: { // two-operand arithmetic / logic / compare
        const b = D[sp - 1], a = D[sp - 2];
        let r: number;
        switch (o) {
          case 0x10: r = (a + b) | 0; break;
          case 0x11: r = (a - b) | 0; break;
          case 0x12: r = Math.imul(a, b); break; // exact low 32 bits
          case 0x13:
            if (b === 0) return trap(4);
            r = a === -2147483648 && b === -1 ? a : (a / b) | 0; break;
          case 0x14:
            if (b === 0) return trap(4);
            r = b === -1 ? 0 : (a % b) | 0; break;
          case 0x15:
            if (b === 0) return trap(4);
            r = Math.floor((a >>> 0) / (b >>> 0)) | 0; break;
          case 0x16:
            if (b === 0) return trap(4);
            r = ((a >>> 0) % (b >>> 0)) | 0; break;
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
        sp -= 2; D[sp++] = r;
      }
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(
    new Uint8Array(readFileSync(join(I, id, 'program.bin'))),
    new Uint8Array(readFileSync(join(I, id, 'input.bin'))),
  );
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.o);
  writeFileSync(join(O, id, 'exit.txt'), `${r.c}\n`);
}
