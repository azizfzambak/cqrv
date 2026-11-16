// OpenQASM 3 — wt8_3 (CQRV, report §8.4.3); unverified emitter (§5.3)
OPENQASM 3.0;
include "stdgates.inc";
qubit[12] x;
qubit[13] anc;
bit[315] c;
bit[12] out;
h x[0];
h x[1];
h x[2];
h x[3];
h x[4];
h x[5];
h x[6];
h x[7];
h x[8];
h x[9];
h x[10];
h x[11];
// cqrv: alloc anc[0]
h anc[0];
t anc[0];
cx x[0], anc[0];
cx x[1], anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
tdg x[0];
tdg x[1];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
h anc[0];
s anc[0];
cx x[1], x[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx x[2], anc[1];
cx x[0], anc[1];
cx anc[1], x[2];
cx anc[1], x[0];
tdg x[2];
tdg x[0];
t anc[1];
cx anc[1], x[2];
cx anc[1], x[0];
h anc[1];
s anc[1];
cx x[1], x[0];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx x[3], anc[2];
cx x[4], anc[2];
cx anc[2], x[3];
cx anc[2], x[4];
tdg x[3];
tdg x[4];
t anc[2];
cx anc[2], x[3];
cx anc[2], x[4];
h anc[2];
s anc[2];
cx x[4], x[3];
// cqrv: alloc anc[3]
h anc[3];
t anc[3];
cx x[5], anc[3];
cx x[3], anc[3];
cx anc[3], x[5];
cx anc[3], x[3];
tdg x[5];
tdg x[3];
t anc[3];
cx anc[3], x[5];
cx anc[3], x[3];
h anc[3];
s anc[3];
cx x[4], x[3];
// cqrv: alloc anc[4]
h anc[4];
t anc[4];
cx x[6], anc[4];
cx x[7], anc[4];
cx anc[4], x[6];
cx anc[4], x[7];
tdg x[6];
tdg x[7];
t anc[4];
cx anc[4], x[6];
cx anc[4], x[7];
h anc[4];
s anc[4];
cx x[1], x[0];
cx x[2], x[0];
cx x[7], x[6];
// cqrv: alloc anc[5]
h anc[5];
t anc[5];
cx x[0], anc[5];
cx x[6], anc[5];
cx anc[5], x[0];
cx anc[5], x[6];
tdg x[0];
tdg x[6];
t anc[5];
cx anc[5], x[0];
cx anc[5], x[6];
h anc[5];
s anc[5];
cx x[7], x[6];
cx x[2], x[0];
cx x[1], x[0];
cx x[4], x[3];
cx x[5], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[6], x[0];
cx x[7], x[0];
// cqrv: alloc anc[6]
h anc[6];
t anc[6];
cx x[3], anc[6];
cx x[0], anc[6];
cx anc[6], x[3];
cx anc[6], x[0];
tdg x[3];
tdg x[0];
t anc[6];
cx anc[6], x[3];
cx anc[6], x[0];
h anc[6];
s anc[6];
cx x[7], x[0];
cx x[6], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx x[5], x[3];
cx x[4], x[3];
cx anc[1], anc[0];
cx anc[3], anc[2];
// cqrv: alloc anc[7]
h anc[7];
t anc[7];
cx anc[0], anc[7];
cx anc[2], anc[7];
cx anc[7], anc[0];
cx anc[7], anc[2];
tdg anc[0];
tdg anc[2];
t anc[7];
cx anc[7], anc[0];
cx anc[7], anc[2];
h anc[7];
s anc[7];
cx anc[3], anc[2];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
// cqrv: alloc anc[8]
h anc[8];
t anc[8];
cx anc[4], anc[8];
cx anc[0], anc[8];
cx anc[8], anc[4];
cx anc[8], anc[0];
tdg anc[4];
tdg anc[0];
t anc[8];
cx anc[8], anc[4];
cx anc[8], anc[0];
h anc[8];
s anc[8];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
// cqrv: alloc anc[9]
h anc[9];
t anc[9];
cx anc[0], anc[9];
cx anc[6], anc[9];
cx anc[9], anc[0];
cx anc[9], anc[6];
tdg anc[0];
tdg anc[6];
t anc[9];
cx anc[9], anc[0];
cx anc[9], anc[6];
h anc[9];
s anc[9];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[1], x[0];
cx x[2], x[0];
cx x[3], x[0];
cx x[4], x[0];
cx x[5], x[0];
cx x[6], x[0];
cx x[7], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
cx anc[6], anc[0];
// cqrv: alloc anc[10]
h anc[10];
t anc[10];
cx x[0], anc[10];
cx anc[0], anc[10];
cx anc[10], x[0];
cx anc[10], anc[0];
tdg x[0];
tdg anc[0];
t anc[10];
cx anc[10], x[0];
cx anc[10], anc[0];
h anc[10];
s anc[10];
cx anc[6], anc[0];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[7], x[0];
cx x[6], x[0];
cx x[5], x[0];
cx x[4], x[0];
cx x[3], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx anc[8], anc[7];
cx anc[9], anc[7];
x anc[7];
// cqrv: alloc anc[11]
h anc[11];
t anc[11];
cx anc[10], anc[11];
cx anc[7], anc[11];
cx anc[11], anc[10];
cx anc[11], anc[7];
tdg anc[10];
tdg anc[7];
t anc[11];
cx anc[11], anc[10];
cx anc[11], anc[7];
h anc[11];
s anc[11];
x anc[7];
cx anc[9], anc[7];
cx anc[8], anc[7];
// cqrv: alloc anc[12]
h anc[12];
t anc[12];
cx anc[11], anc[12];
cx x[8], anc[12];
cx anc[12], anc[11];
cx anc[12], x[8];
tdg anc[11];
tdg x[8];
t anc[12];
cx anc[12], anc[11];
cx anc[12], x[8];
h anc[12];
s anc[12];
z anc[12];
h anc[12];
c[0] = measure anc[12];
if (c[0]) { cz anc[11], x[8]; }
if (c[0]) { x anc[12]; }
// cqrv: free anc[12]
cx anc[8], anc[7];
cx anc[9], anc[7];
x anc[7];
h anc[11];
c[1] = measure anc[11];
if (c[1]) { cz anc[10], anc[7]; }
if (c[1]) { x anc[11]; }
// cqrv: free anc[11]
x anc[7];
cx anc[9], anc[7];
cx anc[8], anc[7];
cx x[1], x[0];
cx x[2], x[0];
cx x[3], x[0];
cx x[4], x[0];
cx x[5], x[0];
cx x[6], x[0];
cx x[7], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
cx anc[6], anc[0];
h anc[10];
c[2] = measure anc[10];
if (c[2]) { cz x[0], anc[0]; }
if (c[2]) { x anc[10]; }
// cqrv: free anc[10]
cx anc[6], anc[0];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[7], x[0];
cx x[6], x[0];
cx x[5], x[0];
cx x[4], x[0];
cx x[3], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
h anc[9];
c[3] = measure anc[9];
if (c[3]) { cz anc[0], anc[6]; }
if (c[3]) { x anc[9]; }
// cqrv: free anc[9]
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
h anc[8];
c[4] = measure anc[8];
if (c[4]) { cz anc[4], anc[0]; }
if (c[4]) { x anc[8]; }
// cqrv: free anc[8]
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[3], anc[2];
h anc[7];
c[5] = measure anc[7];
if (c[5]) { cz anc[0], anc[2]; }
if (c[5]) { x anc[7]; }
// cqrv: free anc[7]
cx anc[3], anc[2];
cx anc[1], anc[0];
cx x[4], x[3];
cx x[5], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[6], x[0];
cx x[7], x[0];
h anc[6];
c[6] = measure anc[6];
if (c[6]) { cz x[3], x[0]; }
if (c[6]) { x anc[6]; }
// cqrv: free anc[6]
cx x[7], x[0];
cx x[6], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx x[5], x[3];
cx x[4], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[7], x[6];
h anc[5];
c[7] = measure anc[5];
if (c[7]) { cz x[0], x[6]; }
if (c[7]) { x anc[5]; }
// cqrv: free anc[5]
cx x[7], x[6];
cx x[2], x[0];
cx x[1], x[0];
h anc[4];
c[8] = measure anc[4];
if (c[8]) { cz x[6], x[7]; }
if (c[8]) { x anc[4]; }
// cqrv: free anc[4]
cx x[4], x[3];
h anc[3];
c[9] = measure anc[3];
if (c[9]) { cz x[5], x[3]; }
if (c[9]) { x anc[3]; }
// cqrv: free anc[3]
cx x[4], x[3];
h anc[2];
c[10] = measure anc[2];
if (c[10]) { cz x[3], x[4]; }
if (c[10]) { x anc[2]; }
// cqrv: free anc[2]
cx x[1], x[0];
h anc[1];
c[11] = measure anc[1];
if (c[11]) { cz x[2], x[0]; }
if (c[11]) { x anc[1]; }
// cqrv: free anc[1]
cx x[1], x[0];
h anc[0];
c[12] = measure anc[0];
if (c[12]) { cz x[0], x[1]; }
if (c[12]) { x anc[0]; }
// cqrv: free anc[0]
h x[0];
h x[1];
h x[2];
h x[3];
h x[4];
h x[5];
h x[6];
h x[7];
x x[0];
x x[1];
x x[2];
x x[3];
x x[4];
x x[5];
x x[6];
x x[7];
// cqrv: alloc anc[0]
h anc[0];
t anc[0];
cx x[0], anc[0];
cx x[1], anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
tdg x[0];
tdg x[1];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
h anc[0];
s anc[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx x[2], anc[1];
cx x[3], anc[1];
cx anc[1], x[2];
cx anc[1], x[3];
tdg x[2];
tdg x[3];
t anc[1];
cx anc[1], x[2];
cx anc[1], x[3];
h anc[1];
s anc[1];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx x[4], anc[2];
cx x[5], anc[2];
cx anc[2], x[4];
cx anc[2], x[5];
tdg x[4];
tdg x[5];
t anc[2];
cx anc[2], x[4];
cx anc[2], x[5];
h anc[2];
s anc[2];
// cqrv: alloc anc[3]
h anc[3];
t anc[3];
cx x[6], anc[3];
cx x[7], anc[3];
cx anc[3], x[6];
cx anc[3], x[7];
tdg x[6];
tdg x[7];
t anc[3];
cx anc[3], x[6];
cx anc[3], x[7];
h anc[3];
s anc[3];
// cqrv: alloc anc[4]
h anc[4];
t anc[4];
cx anc[0], anc[4];
cx anc[1], anc[4];
cx anc[4], anc[0];
cx anc[4], anc[1];
tdg anc[0];
tdg anc[1];
t anc[4];
cx anc[4], anc[0];
cx anc[4], anc[1];
h anc[4];
s anc[4];
// cqrv: alloc anc[5]
h anc[5];
t anc[5];
cx anc[2], anc[5];
cx anc[3], anc[5];
cx anc[5], anc[2];
cx anc[5], anc[3];
tdg anc[2];
tdg anc[3];
t anc[5];
cx anc[5], anc[2];
cx anc[5], anc[3];
h anc[5];
s anc[5];
// cqrv: alloc anc[6]
h anc[6];
t anc[6];
cx anc[4], anc[6];
cx anc[5], anc[6];
cx anc[6], anc[4];
cx anc[6], anc[5];
tdg anc[4];
tdg anc[5];
t anc[6];
cx anc[6], anc[4];
cx anc[6], anc[5];
h anc[6];
s anc[6];
// cqrv: alloc anc[7]
h anc[7];
t anc[7];
cx anc[6], anc[7];
cx x[8], anc[7];
cx anc[7], anc[6];
cx anc[7], x[8];
tdg anc[6];
tdg x[8];
t anc[7];
cx anc[7], anc[6];
cx anc[7], x[8];
h anc[7];
s anc[7];
z anc[7];
h anc[7];
c[13] = measure anc[7];
if (c[13]) { cz anc[6], x[8]; }
if (c[13]) { x anc[7]; }
// cqrv: free anc[7]
h anc[6];
c[14] = measure anc[6];
if (c[14]) { cz anc[4], anc[5]; }
if (c[14]) { x anc[6]; }
// cqrv: free anc[6]
h anc[5];
c[15] = measure anc[5];
if (c[15]) { cz anc[2], anc[3]; }
if (c[15]) { x anc[5]; }
// cqrv: free anc[5]
h anc[4];
c[16] = measure anc[4];
if (c[16]) { cz anc[0], anc[1]; }
if (c[16]) { x anc[4]; }
// cqrv: free anc[4]
h anc[3];
c[17] = measure anc[3];
if (c[17]) { cz x[6], x[7]; }
if (c[17]) { x anc[3]; }
// cqrv: free anc[3]
h anc[2];
c[18] = measure anc[2];
if (c[18]) { cz x[4], x[5]; }
if (c[18]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[19] = measure anc[1];
if (c[19]) { cz x[2], x[3]; }
if (c[19]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[20] = measure anc[0];
if (c[20]) { cz x[0], x[1]; }
if (c[20]) { x anc[0]; }
// cqrv: free anc[0]
x x[0];
x x[1];
x x[2];
x x[3];
x x[4];
x x[5];
x x[6];
x x[7];
h x[0];
h x[1];
h x[2];
h x[3];
h x[4];
h x[5];
h x[6];
h x[7];
z x[8];
// cqrv: alloc anc[0]
h anc[0];
t anc[0];
cx x[0], anc[0];
cx x[1], anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
tdg x[0];
tdg x[1];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
h anc[0];
s anc[0];
cx x[1], x[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx x[2], anc[1];
cx x[0], anc[1];
cx anc[1], x[2];
cx anc[1], x[0];
tdg x[2];
tdg x[0];
t anc[1];
cx anc[1], x[2];
cx anc[1], x[0];
h anc[1];
s anc[1];
cx x[1], x[0];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx x[3], anc[2];
cx x[4], anc[2];
cx anc[2], x[3];
cx anc[2], x[4];
tdg x[3];
tdg x[4];
t anc[2];
cx anc[2], x[3];
cx anc[2], x[4];
h anc[2];
s anc[2];
cx x[4], x[3];
// cqrv: alloc anc[3]
h anc[3];
t anc[3];
cx x[5], anc[3];
cx x[3], anc[3];
cx anc[3], x[5];
cx anc[3], x[3];
tdg x[5];
tdg x[3];
t anc[3];
cx anc[3], x[5];
cx anc[3], x[3];
h anc[3];
s anc[3];
cx x[4], x[3];
// cqrv: alloc anc[4]
h anc[4];
t anc[4];
cx x[6], anc[4];
cx x[7], anc[4];
cx anc[4], x[6];
cx anc[4], x[7];
tdg x[6];
tdg x[7];
t anc[4];
cx anc[4], x[6];
cx anc[4], x[7];
h anc[4];
s anc[4];
cx x[1], x[0];
cx x[2], x[0];
cx x[7], x[6];
// cqrv: alloc anc[5]
h anc[5];
t anc[5];
cx x[0], anc[5];
cx x[6], anc[5];
cx anc[5], x[0];
cx anc[5], x[6];
tdg x[0];
tdg x[6];
t anc[5];
cx anc[5], x[0];
cx anc[5], x[6];
h anc[5];
s anc[5];
cx x[7], x[6];
cx x[2], x[0];
cx x[1], x[0];
cx x[4], x[3];
cx x[5], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[6], x[0];
cx x[7], x[0];
// cqrv: alloc anc[6]
h anc[6];
t anc[6];
cx x[3], anc[6];
cx x[0], anc[6];
cx anc[6], x[3];
cx anc[6], x[0];
tdg x[3];
tdg x[0];
t anc[6];
cx anc[6], x[3];
cx anc[6], x[0];
h anc[6];
s anc[6];
cx x[7], x[0];
cx x[6], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx x[5], x[3];
cx x[4], x[3];
cx anc[1], anc[0];
cx anc[3], anc[2];
// cqrv: alloc anc[7]
h anc[7];
t anc[7];
cx anc[0], anc[7];
cx anc[2], anc[7];
cx anc[7], anc[0];
cx anc[7], anc[2];
tdg anc[0];
tdg anc[2];
t anc[7];
cx anc[7], anc[0];
cx anc[7], anc[2];
h anc[7];
s anc[7];
cx anc[3], anc[2];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
// cqrv: alloc anc[8]
h anc[8];
t anc[8];
cx anc[4], anc[8];
cx anc[0], anc[8];
cx anc[8], anc[4];
cx anc[8], anc[0];
tdg anc[4];
tdg anc[0];
t anc[8];
cx anc[8], anc[4];
cx anc[8], anc[0];
h anc[8];
s anc[8];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
// cqrv: alloc anc[9]
h anc[9];
t anc[9];
cx anc[0], anc[9];
cx anc[6], anc[9];
cx anc[9], anc[0];
cx anc[9], anc[6];
tdg anc[0];
tdg anc[6];
t anc[9];
cx anc[9], anc[0];
cx anc[9], anc[6];
h anc[9];
s anc[9];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[1], x[0];
cx x[2], x[0];
cx x[3], x[0];
cx x[4], x[0];
cx x[5], x[0];
cx x[6], x[0];
cx x[7], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
cx anc[6], anc[0];
// cqrv: alloc anc[10]
h anc[10];
t anc[10];
cx x[0], anc[10];
cx anc[0], anc[10];
cx anc[10], x[0];
cx anc[10], anc[0];
tdg x[0];
tdg anc[0];
t anc[10];
cx anc[10], x[0];
cx anc[10], anc[0];
h anc[10];
s anc[10];
cx anc[6], anc[0];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[7], x[0];
cx x[6], x[0];
cx x[5], x[0];
cx x[4], x[0];
cx x[3], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx anc[8], anc[7];
cx anc[9], anc[7];
x anc[7];
// cqrv: alloc anc[11]
h anc[11];
t anc[11];
cx anc[10], anc[11];
cx anc[7], anc[11];
cx anc[11], anc[10];
cx anc[11], anc[7];
tdg anc[10];
tdg anc[7];
t anc[11];
cx anc[11], anc[10];
cx anc[11], anc[7];
h anc[11];
s anc[11];
x anc[7];
cx anc[9], anc[7];
cx anc[8], anc[7];
// cqrv: alloc anc[12]
h anc[12];
t anc[12];
cx anc[11], anc[12];
cx x[9], anc[12];
cx anc[12], anc[11];
cx anc[12], x[9];
tdg anc[11];
tdg x[9];
t anc[12];
cx anc[12], anc[11];
cx anc[12], x[9];
h anc[12];
s anc[12];
z anc[12];
h anc[12];
c[21] = measure anc[12];
if (c[21]) { cz anc[11], x[9]; }
if (c[21]) { x anc[12]; }
// cqrv: free anc[12]
cx anc[8], anc[7];
cx anc[9], anc[7];
x anc[7];
h anc[11];
c[22] = measure anc[11];
if (c[22]) { cz anc[10], anc[7]; }
if (c[22]) { x anc[11]; }
// cqrv: free anc[11]
x anc[7];
cx anc[9], anc[7];
cx anc[8], anc[7];
cx x[1], x[0];
cx x[2], x[0];
cx x[3], x[0];
cx x[4], x[0];
cx x[5], x[0];
cx x[6], x[0];
cx x[7], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
cx anc[6], anc[0];
h anc[10];
c[23] = measure anc[10];
if (c[23]) { cz x[0], anc[0]; }
if (c[23]) { x anc[10]; }
// cqrv: free anc[10]
cx anc[6], anc[0];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[7], x[0];
cx x[6], x[0];
cx x[5], x[0];
cx x[4], x[0];
cx x[3], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
h anc[9];
c[24] = measure anc[9];
if (c[24]) { cz anc[0], anc[6]; }
if (c[24]) { x anc[9]; }
// cqrv: free anc[9]
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
h anc[8];
c[25] = measure anc[8];
if (c[25]) { cz anc[4], anc[0]; }
if (c[25]) { x anc[8]; }
// cqrv: free anc[8]
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[3], anc[2];
h anc[7];
c[26] = measure anc[7];
if (c[26]) { cz anc[0], anc[2]; }
if (c[26]) { x anc[7]; }
// cqrv: free anc[7]
cx anc[3], anc[2];
cx anc[1], anc[0];
cx x[4], x[3];
cx x[5], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[6], x[0];
cx x[7], x[0];
h anc[6];
c[27] = measure anc[6];
if (c[27]) { cz x[3], x[0]; }
if (c[27]) { x anc[6]; }
// cqrv: free anc[6]
cx x[7], x[0];
cx x[6], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx x[5], x[3];
cx x[4], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[7], x[6];
h anc[5];
c[28] = measure anc[5];
if (c[28]) { cz x[0], x[6]; }
if (c[28]) { x anc[5]; }
// cqrv: free anc[5]
cx x[7], x[6];
cx x[2], x[0];
cx x[1], x[0];
h anc[4];
c[29] = measure anc[4];
if (c[29]) { cz x[6], x[7]; }
if (c[29]) { x anc[4]; }
// cqrv: free anc[4]
cx x[4], x[3];
h anc[3];
c[30] = measure anc[3];
if (c[30]) { cz x[5], x[3]; }
if (c[30]) { x anc[3]; }
// cqrv: free anc[3]
cx x[4], x[3];
h anc[2];
c[31] = measure anc[2];
if (c[31]) { cz x[3], x[4]; }
if (c[31]) { x anc[2]; }
// cqrv: free anc[2]
cx x[1], x[0];
h anc[1];
c[32] = measure anc[1];
if (c[32]) { cz x[2], x[0]; }
if (c[32]) { x anc[1]; }
// cqrv: free anc[1]
cx x[1], x[0];
h anc[0];
c[33] = measure anc[0];
if (c[33]) { cz x[0], x[1]; }
if (c[33]) { x anc[0]; }
// cqrv: free anc[0]
h x[0];
h x[1];
h x[2];
h x[3];
h x[4];
h x[5];
h x[6];
h x[7];
x x[0];
x x[1];
x x[2];
x x[3];
x x[4];
x x[5];
x x[6];
x x[7];
// cqrv: alloc anc[0]
h anc[0];
t anc[0];
cx x[0], anc[0];
cx x[1], anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
tdg x[0];
tdg x[1];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
h anc[0];
s anc[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx x[2], anc[1];
cx x[3], anc[1];
cx anc[1], x[2];
cx anc[1], x[3];
tdg x[2];
tdg x[3];
t anc[1];
cx anc[1], x[2];
cx anc[1], x[3];
h anc[1];
s anc[1];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx x[4], anc[2];
cx x[5], anc[2];
cx anc[2], x[4];
cx anc[2], x[5];
tdg x[4];
tdg x[5];
t anc[2];
cx anc[2], x[4];
cx anc[2], x[5];
h anc[2];
s anc[2];
// cqrv: alloc anc[3]
h anc[3];
t anc[3];
cx x[6], anc[3];
cx x[7], anc[3];
cx anc[3], x[6];
cx anc[3], x[7];
tdg x[6];
tdg x[7];
t anc[3];
cx anc[3], x[6];
cx anc[3], x[7];
h anc[3];
s anc[3];
// cqrv: alloc anc[4]
h anc[4];
t anc[4];
cx anc[0], anc[4];
cx anc[1], anc[4];
cx anc[4], anc[0];
cx anc[4], anc[1];
tdg anc[0];
tdg anc[1];
t anc[4];
cx anc[4], anc[0];
cx anc[4], anc[1];
h anc[4];
s anc[4];
// cqrv: alloc anc[5]
h anc[5];
t anc[5];
cx anc[2], anc[5];
cx anc[3], anc[5];
cx anc[5], anc[2];
cx anc[5], anc[3];
tdg anc[2];
tdg anc[3];
t anc[5];
cx anc[5], anc[2];
cx anc[5], anc[3];
h anc[5];
s anc[5];
// cqrv: alloc anc[6]
h anc[6];
t anc[6];
cx anc[4], anc[6];
cx anc[5], anc[6];
cx anc[6], anc[4];
cx anc[6], anc[5];
tdg anc[4];
tdg anc[5];
t anc[6];
cx anc[6], anc[4];
cx anc[6], anc[5];
h anc[6];
s anc[6];
// cqrv: alloc anc[7]
h anc[7];
t anc[7];
cx anc[6], anc[7];
cx x[9], anc[7];
cx anc[7], anc[6];
cx anc[7], x[9];
tdg anc[6];
tdg x[9];
t anc[7];
cx anc[7], anc[6];
cx anc[7], x[9];
h anc[7];
s anc[7];
z anc[7];
h anc[7];
c[34] = measure anc[7];
if (c[34]) { cz anc[6], x[9]; }
if (c[34]) { x anc[7]; }
// cqrv: free anc[7]
h anc[6];
c[35] = measure anc[6];
if (c[35]) { cz anc[4], anc[5]; }
if (c[35]) { x anc[6]; }
// cqrv: free anc[6]
h anc[5];
c[36] = measure anc[5];
if (c[36]) { cz anc[2], anc[3]; }
if (c[36]) { x anc[5]; }
// cqrv: free anc[5]
h anc[4];
c[37] = measure anc[4];
if (c[37]) { cz anc[0], anc[1]; }
if (c[37]) { x anc[4]; }
// cqrv: free anc[4]
h anc[3];
c[38] = measure anc[3];
if (c[38]) { cz x[6], x[7]; }
if (c[38]) { x anc[3]; }
// cqrv: free anc[3]
h anc[2];
c[39] = measure anc[2];
if (c[39]) { cz x[4], x[5]; }
if (c[39]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[40] = measure anc[1];
if (c[40]) { cz x[2], x[3]; }
if (c[40]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[41] = measure anc[0];
if (c[41]) { cz x[0], x[1]; }
if (c[41]) { x anc[0]; }
// cqrv: free anc[0]
x x[0];
x x[1];
x x[2];
x x[3];
x x[4];
x x[5];
x x[6];
x x[7];
h x[0];
h x[1];
h x[2];
h x[3];
h x[4];
h x[5];
h x[6];
h x[7];
z x[9];
// cqrv: alloc anc[0]
h anc[0];
t anc[0];
cx x[0], anc[0];
cx x[1], anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
tdg x[0];
tdg x[1];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
h anc[0];
s anc[0];
cx x[1], x[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx x[2], anc[1];
cx x[0], anc[1];
cx anc[1], x[2];
cx anc[1], x[0];
tdg x[2];
tdg x[0];
t anc[1];
cx anc[1], x[2];
cx anc[1], x[0];
h anc[1];
s anc[1];
cx x[1], x[0];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx x[3], anc[2];
cx x[4], anc[2];
cx anc[2], x[3];
cx anc[2], x[4];
tdg x[3];
tdg x[4];
t anc[2];
cx anc[2], x[3];
cx anc[2], x[4];
h anc[2];
s anc[2];
cx x[4], x[3];
// cqrv: alloc anc[3]
h anc[3];
t anc[3];
cx x[5], anc[3];
cx x[3], anc[3];
cx anc[3], x[5];
cx anc[3], x[3];
tdg x[5];
tdg x[3];
t anc[3];
cx anc[3], x[5];
cx anc[3], x[3];
h anc[3];
s anc[3];
cx x[4], x[3];
// cqrv: alloc anc[4]
h anc[4];
t anc[4];
cx x[6], anc[4];
cx x[7], anc[4];
cx anc[4], x[6];
cx anc[4], x[7];
tdg x[6];
tdg x[7];
t anc[4];
cx anc[4], x[6];
cx anc[4], x[7];
h anc[4];
s anc[4];
cx x[1], x[0];
cx x[2], x[0];
cx x[7], x[6];
// cqrv: alloc anc[5]
h anc[5];
t anc[5];
cx x[0], anc[5];
cx x[6], anc[5];
cx anc[5], x[0];
cx anc[5], x[6];
tdg x[0];
tdg x[6];
t anc[5];
cx anc[5], x[0];
cx anc[5], x[6];
h anc[5];
s anc[5];
cx x[7], x[6];
cx x[2], x[0];
cx x[1], x[0];
cx x[4], x[3];
cx x[5], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[6], x[0];
cx x[7], x[0];
// cqrv: alloc anc[6]
h anc[6];
t anc[6];
cx x[3], anc[6];
cx x[0], anc[6];
cx anc[6], x[3];
cx anc[6], x[0];
tdg x[3];
tdg x[0];
t anc[6];
cx anc[6], x[3];
cx anc[6], x[0];
h anc[6];
s anc[6];
cx x[7], x[0];
cx x[6], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx x[5], x[3];
cx x[4], x[3];
cx anc[1], anc[0];
cx anc[3], anc[2];
// cqrv: alloc anc[7]
h anc[7];
t anc[7];
cx anc[0], anc[7];
cx anc[2], anc[7];
cx anc[7], anc[0];
cx anc[7], anc[2];
tdg anc[0];
tdg anc[2];
t anc[7];
cx anc[7], anc[0];
cx anc[7], anc[2];
h anc[7];
s anc[7];
cx anc[3], anc[2];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
// cqrv: alloc anc[8]
h anc[8];
t anc[8];
cx anc[4], anc[8];
cx anc[0], anc[8];
cx anc[8], anc[4];
cx anc[8], anc[0];
tdg anc[4];
tdg anc[0];
t anc[8];
cx anc[8], anc[4];
cx anc[8], anc[0];
h anc[8];
s anc[8];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
// cqrv: alloc anc[9]
h anc[9];
t anc[9];
cx anc[0], anc[9];
cx anc[6], anc[9];
cx anc[9], anc[0];
cx anc[9], anc[6];
tdg anc[0];
tdg anc[6];
t anc[9];
cx anc[9], anc[0];
cx anc[9], anc[6];
h anc[9];
s anc[9];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[1], x[0];
cx x[2], x[0];
cx x[3], x[0];
cx x[4], x[0];
cx x[5], x[0];
cx x[6], x[0];
cx x[7], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
cx anc[6], anc[0];
// cqrv: alloc anc[10]
h anc[10];
t anc[10];
cx x[0], anc[10];
cx anc[0], anc[10];
cx anc[10], x[0];
cx anc[10], anc[0];
tdg x[0];
tdg anc[0];
t anc[10];
cx anc[10], x[0];
cx anc[10], anc[0];
h anc[10];
s anc[10];
cx anc[6], anc[0];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[7], x[0];
cx x[6], x[0];
cx x[5], x[0];
cx x[4], x[0];
cx x[3], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx anc[8], anc[7];
cx anc[9], anc[7];
x anc[7];
// cqrv: alloc anc[11]
h anc[11];
t anc[11];
cx anc[10], anc[11];
cx anc[7], anc[11];
cx anc[11], anc[10];
cx anc[11], anc[7];
tdg anc[10];
tdg anc[7];
t anc[11];
cx anc[11], anc[10];
cx anc[11], anc[7];
h anc[11];
s anc[11];
x anc[7];
cx anc[9], anc[7];
cx anc[8], anc[7];
// cqrv: alloc anc[12]
h anc[12];
t anc[12];
cx anc[11], anc[12];
cx x[9], anc[12];
cx anc[12], anc[11];
cx anc[12], x[9];
tdg anc[11];
tdg x[9];
t anc[12];
cx anc[12], anc[11];
cx anc[12], x[9];
h anc[12];
s anc[12];
z anc[12];
h anc[12];
c[42] = measure anc[12];
if (c[42]) { cz anc[11], x[9]; }
if (c[42]) { x anc[12]; }
// cqrv: free anc[12]
cx anc[8], anc[7];
cx anc[9], anc[7];
x anc[7];
h anc[11];
c[43] = measure anc[11];
if (c[43]) { cz anc[10], anc[7]; }
if (c[43]) { x anc[11]; }
// cqrv: free anc[11]
x anc[7];
cx anc[9], anc[7];
cx anc[8], anc[7];
cx x[1], x[0];
cx x[2], x[0];
cx x[3], x[0];
cx x[4], x[0];
cx x[5], x[0];
cx x[6], x[0];
cx x[7], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
cx anc[6], anc[0];
h anc[10];
c[44] = measure anc[10];
if (c[44]) { cz x[0], anc[0]; }
if (c[44]) { x anc[10]; }
// cqrv: free anc[10]
cx anc[6], anc[0];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[7], x[0];
cx x[6], x[0];
cx x[5], x[0];
cx x[4], x[0];
cx x[3], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
h anc[9];
c[45] = measure anc[9];
if (c[45]) { cz anc[0], anc[6]; }
if (c[45]) { x anc[9]; }
// cqrv: free anc[9]
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
h anc[8];
c[46] = measure anc[8];
if (c[46]) { cz anc[4], anc[0]; }
if (c[46]) { x anc[8]; }
// cqrv: free anc[8]
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[3], anc[2];
h anc[7];
c[47] = measure anc[7];
if (c[47]) { cz anc[0], anc[2]; }
if (c[47]) { x anc[7]; }
// cqrv: free anc[7]
cx anc[3], anc[2];
cx anc[1], anc[0];
cx x[4], x[3];
cx x[5], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[6], x[0];
cx x[7], x[0];
h anc[6];
c[48] = measure anc[6];
if (c[48]) { cz x[3], x[0]; }
if (c[48]) { x anc[6]; }
// cqrv: free anc[6]
cx x[7], x[0];
cx x[6], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx x[5], x[3];
cx x[4], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[7], x[6];
h anc[5];
c[49] = measure anc[5];
if (c[49]) { cz x[0], x[6]; }
if (c[49]) { x anc[5]; }
// cqrv: free anc[5]
cx x[7], x[6];
cx x[2], x[0];
cx x[1], x[0];
h anc[4];
c[50] = measure anc[4];
if (c[50]) { cz x[6], x[7]; }
if (c[50]) { x anc[4]; }
// cqrv: free anc[4]
cx x[4], x[3];
h anc[3];
c[51] = measure anc[3];
if (c[51]) { cz x[5], x[3]; }
if (c[51]) { x anc[3]; }
// cqrv: free anc[3]
cx x[4], x[3];
h anc[2];
c[52] = measure anc[2];
if (c[52]) { cz x[3], x[4]; }
if (c[52]) { x anc[2]; }
// cqrv: free anc[2]
cx x[1], x[0];
h anc[1];
c[53] = measure anc[1];
if (c[53]) { cz x[2], x[0]; }
if (c[53]) { x anc[1]; }
// cqrv: free anc[1]
cx x[1], x[0];
h anc[0];
c[54] = measure anc[0];
if (c[54]) { cz x[0], x[1]; }
if (c[54]) { x anc[0]; }
// cqrv: free anc[0]
h x[0];
h x[1];
h x[2];
h x[3];
h x[4];
h x[5];
h x[6];
h x[7];
x x[0];
x x[1];
x x[2];
x x[3];
x x[4];
x x[5];
x x[6];
x x[7];
// cqrv: alloc anc[0]
h anc[0];
t anc[0];
cx x[0], anc[0];
cx x[1], anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
tdg x[0];
tdg x[1];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
h anc[0];
s anc[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx x[2], anc[1];
cx x[3], anc[1];
cx anc[1], x[2];
cx anc[1], x[3];
tdg x[2];
tdg x[3];
t anc[1];
cx anc[1], x[2];
cx anc[1], x[3];
h anc[1];
s anc[1];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx x[4], anc[2];
cx x[5], anc[2];
cx anc[2], x[4];
cx anc[2], x[5];
tdg x[4];
tdg x[5];
t anc[2];
cx anc[2], x[4];
cx anc[2], x[5];
h anc[2];
s anc[2];
// cqrv: alloc anc[3]
h anc[3];
t anc[3];
cx x[6], anc[3];
cx x[7], anc[3];
cx anc[3], x[6];
cx anc[3], x[7];
tdg x[6];
tdg x[7];
t anc[3];
cx anc[3], x[6];
cx anc[3], x[7];
h anc[3];
s anc[3];
// cqrv: alloc anc[4]
h anc[4];
t anc[4];
cx anc[0], anc[4];
cx anc[1], anc[4];
cx anc[4], anc[0];
cx anc[4], anc[1];
tdg anc[0];
tdg anc[1];
t anc[4];
cx anc[4], anc[0];
cx anc[4], anc[1];
h anc[4];
s anc[4];
// cqrv: alloc anc[5]
h anc[5];
t anc[5];
cx anc[2], anc[5];
cx anc[3], anc[5];
cx anc[5], anc[2];
cx anc[5], anc[3];
tdg anc[2];
tdg anc[3];
t anc[5];
cx anc[5], anc[2];
cx anc[5], anc[3];
h anc[5];
s anc[5];
// cqrv: alloc anc[6]
h anc[6];
t anc[6];
cx anc[4], anc[6];
cx anc[5], anc[6];
cx anc[6], anc[4];
cx anc[6], anc[5];
tdg anc[4];
tdg anc[5];
t anc[6];
cx anc[6], anc[4];
cx anc[6], anc[5];
h anc[6];
s anc[6];
// cqrv: alloc anc[7]
h anc[7];
t anc[7];
cx anc[6], anc[7];
cx x[9], anc[7];
cx anc[7], anc[6];
cx anc[7], x[9];
tdg anc[6];
tdg x[9];
t anc[7];
cx anc[7], anc[6];
cx anc[7], x[9];
h anc[7];
s anc[7];
z anc[7];
h anc[7];
c[55] = measure anc[7];
if (c[55]) { cz anc[6], x[9]; }
if (c[55]) { x anc[7]; }
// cqrv: free anc[7]
h anc[6];
c[56] = measure anc[6];
if (c[56]) { cz anc[4], anc[5]; }
if (c[56]) { x anc[6]; }
// cqrv: free anc[6]
h anc[5];
c[57] = measure anc[5];
if (c[57]) { cz anc[2], anc[3]; }
if (c[57]) { x anc[5]; }
// cqrv: free anc[5]
h anc[4];
c[58] = measure anc[4];
if (c[58]) { cz anc[0], anc[1]; }
if (c[58]) { x anc[4]; }
// cqrv: free anc[4]
h anc[3];
c[59] = measure anc[3];
if (c[59]) { cz x[6], x[7]; }
if (c[59]) { x anc[3]; }
// cqrv: free anc[3]
h anc[2];
c[60] = measure anc[2];
if (c[60]) { cz x[4], x[5]; }
if (c[60]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[61] = measure anc[1];
if (c[61]) { cz x[2], x[3]; }
if (c[61]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[62] = measure anc[0];
if (c[62]) { cz x[0], x[1]; }
if (c[62]) { x anc[0]; }
// cqrv: free anc[0]
x x[0];
x x[1];
x x[2];
x x[3];
x x[4];
x x[5];
x x[6];
x x[7];
h x[0];
h x[1];
h x[2];
h x[3];
h x[4];
h x[5];
h x[6];
h x[7];
z x[9];
// cqrv: alloc anc[0]
h anc[0];
t anc[0];
cx x[0], anc[0];
cx x[1], anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
tdg x[0];
tdg x[1];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
h anc[0];
s anc[0];
cx x[1], x[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx x[2], anc[1];
cx x[0], anc[1];
cx anc[1], x[2];
cx anc[1], x[0];
tdg x[2];
tdg x[0];
t anc[1];
cx anc[1], x[2];
cx anc[1], x[0];
h anc[1];
s anc[1];
cx x[1], x[0];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx x[3], anc[2];
cx x[4], anc[2];
cx anc[2], x[3];
cx anc[2], x[4];
tdg x[3];
tdg x[4];
t anc[2];
cx anc[2], x[3];
cx anc[2], x[4];
h anc[2];
s anc[2];
cx x[4], x[3];
// cqrv: alloc anc[3]
h anc[3];
t anc[3];
cx x[5], anc[3];
cx x[3], anc[3];
cx anc[3], x[5];
cx anc[3], x[3];
tdg x[5];
tdg x[3];
t anc[3];
cx anc[3], x[5];
cx anc[3], x[3];
h anc[3];
s anc[3];
cx x[4], x[3];
// cqrv: alloc anc[4]
h anc[4];
t anc[4];
cx x[6], anc[4];
cx x[7], anc[4];
cx anc[4], x[6];
cx anc[4], x[7];
tdg x[6];
tdg x[7];
t anc[4];
cx anc[4], x[6];
cx anc[4], x[7];
h anc[4];
s anc[4];
cx x[1], x[0];
cx x[2], x[0];
cx x[7], x[6];
// cqrv: alloc anc[5]
h anc[5];
t anc[5];
cx x[0], anc[5];
cx x[6], anc[5];
cx anc[5], x[0];
cx anc[5], x[6];
tdg x[0];
tdg x[6];
t anc[5];
cx anc[5], x[0];
cx anc[5], x[6];
h anc[5];
s anc[5];
cx x[7], x[6];
cx x[2], x[0];
cx x[1], x[0];
cx x[4], x[3];
cx x[5], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[6], x[0];
cx x[7], x[0];
// cqrv: alloc anc[6]
h anc[6];
t anc[6];
cx x[3], anc[6];
cx x[0], anc[6];
cx anc[6], x[3];
cx anc[6], x[0];
tdg x[3];
tdg x[0];
t anc[6];
cx anc[6], x[3];
cx anc[6], x[0];
h anc[6];
s anc[6];
cx x[7], x[0];
cx x[6], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx x[5], x[3];
cx x[4], x[3];
cx anc[1], anc[0];
cx anc[3], anc[2];
// cqrv: alloc anc[7]
h anc[7];
t anc[7];
cx anc[0], anc[7];
cx anc[2], anc[7];
cx anc[7], anc[0];
cx anc[7], anc[2];
tdg anc[0];
tdg anc[2];
t anc[7];
cx anc[7], anc[0];
cx anc[7], anc[2];
h anc[7];
s anc[7];
cx anc[3], anc[2];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
// cqrv: alloc anc[8]
h anc[8];
t anc[8];
cx anc[4], anc[8];
cx anc[0], anc[8];
cx anc[8], anc[4];
cx anc[8], anc[0];
tdg anc[4];
tdg anc[0];
t anc[8];
cx anc[8], anc[4];
cx anc[8], anc[0];
h anc[8];
s anc[8];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
// cqrv: alloc anc[9]
h anc[9];
t anc[9];
cx anc[0], anc[9];
cx anc[6], anc[9];
cx anc[9], anc[0];
cx anc[9], anc[6];
tdg anc[0];
tdg anc[6];
t anc[9];
cx anc[9], anc[0];
cx anc[9], anc[6];
h anc[9];
s anc[9];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[1], x[0];
cx x[2], x[0];
cx x[3], x[0];
cx x[4], x[0];
cx x[5], x[0];
cx x[6], x[0];
cx x[7], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
cx anc[6], anc[0];
// cqrv: alloc anc[10]
h anc[10];
t anc[10];
cx x[0], anc[10];
cx anc[0], anc[10];
cx anc[10], x[0];
cx anc[10], anc[0];
tdg x[0];
tdg anc[0];
t anc[10];
cx anc[10], x[0];
cx anc[10], anc[0];
h anc[10];
s anc[10];
cx anc[6], anc[0];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[7], x[0];
cx x[6], x[0];
cx x[5], x[0];
cx x[4], x[0];
cx x[3], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx anc[8], anc[7];
cx anc[9], anc[7];
x anc[7];
// cqrv: alloc anc[11]
h anc[11];
t anc[11];
cx anc[10], anc[11];
cx anc[7], anc[11];
cx anc[11], anc[10];
cx anc[11], anc[7];
tdg anc[10];
tdg anc[7];
t anc[11];
cx anc[11], anc[10];
cx anc[11], anc[7];
h anc[11];
s anc[11];
x anc[7];
cx anc[9], anc[7];
cx anc[8], anc[7];
// cqrv: alloc anc[12]
h anc[12];
t anc[12];
cx anc[11], anc[12];
cx x[10], anc[12];
cx anc[12], anc[11];
cx anc[12], x[10];
tdg anc[11];
tdg x[10];
t anc[12];
cx anc[12], anc[11];
cx anc[12], x[10];
h anc[12];
s anc[12];
z anc[12];
h anc[12];
c[63] = measure anc[12];
if (c[63]) { cz anc[11], x[10]; }
if (c[63]) { x anc[12]; }
// cqrv: free anc[12]
cx anc[8], anc[7];
cx anc[9], anc[7];
x anc[7];
h anc[11];
c[64] = measure anc[11];
if (c[64]) { cz anc[10], anc[7]; }
if (c[64]) { x anc[11]; }
// cqrv: free anc[11]
x anc[7];
cx anc[9], anc[7];
cx anc[8], anc[7];
cx x[1], x[0];
cx x[2], x[0];
cx x[3], x[0];
cx x[4], x[0];
cx x[5], x[0];
cx x[6], x[0];
cx x[7], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
cx anc[6], anc[0];
h anc[10];
c[65] = measure anc[10];
if (c[65]) { cz x[0], anc[0]; }
if (c[65]) { x anc[10]; }
// cqrv: free anc[10]
cx anc[6], anc[0];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[7], x[0];
cx x[6], x[0];
cx x[5], x[0];
cx x[4], x[0];
cx x[3], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
h anc[9];
c[66] = measure anc[9];
if (c[66]) { cz anc[0], anc[6]; }
if (c[66]) { x anc[9]; }
// cqrv: free anc[9]
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
h anc[8];
c[67] = measure anc[8];
if (c[67]) { cz anc[4], anc[0]; }
if (c[67]) { x anc[8]; }
// cqrv: free anc[8]
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[3], anc[2];
h anc[7];
c[68] = measure anc[7];
if (c[68]) { cz anc[0], anc[2]; }
if (c[68]) { x anc[7]; }
// cqrv: free anc[7]
cx anc[3], anc[2];
cx anc[1], anc[0];
cx x[4], x[3];
cx x[5], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[6], x[0];
cx x[7], x[0];
h anc[6];
c[69] = measure anc[6];
if (c[69]) { cz x[3], x[0]; }
if (c[69]) { x anc[6]; }
// cqrv: free anc[6]
cx x[7], x[0];
cx x[6], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx x[5], x[3];
cx x[4], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[7], x[6];
h anc[5];
c[70] = measure anc[5];
if (c[70]) { cz x[0], x[6]; }
if (c[70]) { x anc[5]; }
// cqrv: free anc[5]
cx x[7], x[6];
cx x[2], x[0];
cx x[1], x[0];
h anc[4];
c[71] = measure anc[4];
if (c[71]) { cz x[6], x[7]; }
if (c[71]) { x anc[4]; }
// cqrv: free anc[4]
cx x[4], x[3];
h anc[3];
c[72] = measure anc[3];
if (c[72]) { cz x[5], x[3]; }
if (c[72]) { x anc[3]; }
// cqrv: free anc[3]
cx x[4], x[3];
h anc[2];
c[73] = measure anc[2];
if (c[73]) { cz x[3], x[4]; }
if (c[73]) { x anc[2]; }
// cqrv: free anc[2]
cx x[1], x[0];
h anc[1];
c[74] = measure anc[1];
if (c[74]) { cz x[2], x[0]; }
if (c[74]) { x anc[1]; }
// cqrv: free anc[1]
cx x[1], x[0];
h anc[0];
c[75] = measure anc[0];
if (c[75]) { cz x[0], x[1]; }
if (c[75]) { x anc[0]; }
// cqrv: free anc[0]
h x[0];
h x[1];
h x[2];
h x[3];
h x[4];
h x[5];
h x[6];
h x[7];
x x[0];
x x[1];
x x[2];
x x[3];
x x[4];
x x[5];
x x[6];
x x[7];
// cqrv: alloc anc[0]
h anc[0];
t anc[0];
cx x[0], anc[0];
cx x[1], anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
tdg x[0];
tdg x[1];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
h anc[0];
s anc[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx x[2], anc[1];
cx x[3], anc[1];
cx anc[1], x[2];
cx anc[1], x[3];
tdg x[2];
tdg x[3];
t anc[1];
cx anc[1], x[2];
cx anc[1], x[3];
h anc[1];
s anc[1];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx x[4], anc[2];
cx x[5], anc[2];
cx anc[2], x[4];
cx anc[2], x[5];
tdg x[4];
tdg x[5];
t anc[2];
cx anc[2], x[4];
cx anc[2], x[5];
h anc[2];
s anc[2];
// cqrv: alloc anc[3]
h anc[3];
t anc[3];
cx x[6], anc[3];
cx x[7], anc[3];
cx anc[3], x[6];
cx anc[3], x[7];
tdg x[6];
tdg x[7];
t anc[3];
cx anc[3], x[6];
cx anc[3], x[7];
h anc[3];
s anc[3];
// cqrv: alloc anc[4]
h anc[4];
t anc[4];
cx anc[0], anc[4];
cx anc[1], anc[4];
cx anc[4], anc[0];
cx anc[4], anc[1];
tdg anc[0];
tdg anc[1];
t anc[4];
cx anc[4], anc[0];
cx anc[4], anc[1];
h anc[4];
s anc[4];
// cqrv: alloc anc[5]
h anc[5];
t anc[5];
cx anc[2], anc[5];
cx anc[3], anc[5];
cx anc[5], anc[2];
cx anc[5], anc[3];
tdg anc[2];
tdg anc[3];
t anc[5];
cx anc[5], anc[2];
cx anc[5], anc[3];
h anc[5];
s anc[5];
// cqrv: alloc anc[6]
h anc[6];
t anc[6];
cx anc[4], anc[6];
cx anc[5], anc[6];
cx anc[6], anc[4];
cx anc[6], anc[5];
tdg anc[4];
tdg anc[5];
t anc[6];
cx anc[6], anc[4];
cx anc[6], anc[5];
h anc[6];
s anc[6];
// cqrv: alloc anc[7]
h anc[7];
t anc[7];
cx anc[6], anc[7];
cx x[10], anc[7];
cx anc[7], anc[6];
cx anc[7], x[10];
tdg anc[6];
tdg x[10];
t anc[7];
cx anc[7], anc[6];
cx anc[7], x[10];
h anc[7];
s anc[7];
z anc[7];
h anc[7];
c[76] = measure anc[7];
if (c[76]) { cz anc[6], x[10]; }
if (c[76]) { x anc[7]; }
// cqrv: free anc[7]
h anc[6];
c[77] = measure anc[6];
if (c[77]) { cz anc[4], anc[5]; }
if (c[77]) { x anc[6]; }
// cqrv: free anc[6]
h anc[5];
c[78] = measure anc[5];
if (c[78]) { cz anc[2], anc[3]; }
if (c[78]) { x anc[5]; }
// cqrv: free anc[5]
h anc[4];
c[79] = measure anc[4];
if (c[79]) { cz anc[0], anc[1]; }
if (c[79]) { x anc[4]; }
// cqrv: free anc[4]
h anc[3];
c[80] = measure anc[3];
if (c[80]) { cz x[6], x[7]; }
if (c[80]) { x anc[3]; }
// cqrv: free anc[3]
h anc[2];
c[81] = measure anc[2];
if (c[81]) { cz x[4], x[5]; }
if (c[81]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[82] = measure anc[1];
if (c[82]) { cz x[2], x[3]; }
if (c[82]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[83] = measure anc[0];
if (c[83]) { cz x[0], x[1]; }
if (c[83]) { x anc[0]; }
// cqrv: free anc[0]
x x[0];
x x[1];
x x[2];
x x[3];
x x[4];
x x[5];
x x[6];
x x[7];
h x[0];
h x[1];
h x[2];
h x[3];
h x[4];
h x[5];
h x[6];
h x[7];
z x[10];
// cqrv: alloc anc[0]
h anc[0];
t anc[0];
cx x[0], anc[0];
cx x[1], anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
tdg x[0];
tdg x[1];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
h anc[0];
s anc[0];
cx x[1], x[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx x[2], anc[1];
cx x[0], anc[1];
cx anc[1], x[2];
cx anc[1], x[0];
tdg x[2];
tdg x[0];
t anc[1];
cx anc[1], x[2];
cx anc[1], x[0];
h anc[1];
s anc[1];
cx x[1], x[0];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx x[3], anc[2];
cx x[4], anc[2];
cx anc[2], x[3];
cx anc[2], x[4];
tdg x[3];
tdg x[4];
t anc[2];
cx anc[2], x[3];
cx anc[2], x[4];
h anc[2];
s anc[2];
cx x[4], x[3];
// cqrv: alloc anc[3]
h anc[3];
t anc[3];
cx x[5], anc[3];
cx x[3], anc[3];
cx anc[3], x[5];
cx anc[3], x[3];
tdg x[5];
tdg x[3];
t anc[3];
cx anc[3], x[5];
cx anc[3], x[3];
h anc[3];
s anc[3];
cx x[4], x[3];
// cqrv: alloc anc[4]
h anc[4];
t anc[4];
cx x[6], anc[4];
cx x[7], anc[4];
cx anc[4], x[6];
cx anc[4], x[7];
tdg x[6];
tdg x[7];
t anc[4];
cx anc[4], x[6];
cx anc[4], x[7];
h anc[4];
s anc[4];
cx x[1], x[0];
cx x[2], x[0];
cx x[7], x[6];
// cqrv: alloc anc[5]
h anc[5];
t anc[5];
cx x[0], anc[5];
cx x[6], anc[5];
cx anc[5], x[0];
cx anc[5], x[6];
tdg x[0];
tdg x[6];
t anc[5];
cx anc[5], x[0];
cx anc[5], x[6];
h anc[5];
s anc[5];
cx x[7], x[6];
cx x[2], x[0];
cx x[1], x[0];
cx x[4], x[3];
cx x[5], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[6], x[0];
cx x[7], x[0];
// cqrv: alloc anc[6]
h anc[6];
t anc[6];
cx x[3], anc[6];
cx x[0], anc[6];
cx anc[6], x[3];
cx anc[6], x[0];
tdg x[3];
tdg x[0];
t anc[6];
cx anc[6], x[3];
cx anc[6], x[0];
h anc[6];
s anc[6];
cx x[7], x[0];
cx x[6], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx x[5], x[3];
cx x[4], x[3];
cx anc[1], anc[0];
cx anc[3], anc[2];
// cqrv: alloc anc[7]
h anc[7];
t anc[7];
cx anc[0], anc[7];
cx anc[2], anc[7];
cx anc[7], anc[0];
cx anc[7], anc[2];
tdg anc[0];
tdg anc[2];
t anc[7];
cx anc[7], anc[0];
cx anc[7], anc[2];
h anc[7];
s anc[7];
cx anc[3], anc[2];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
// cqrv: alloc anc[8]
h anc[8];
t anc[8];
cx anc[4], anc[8];
cx anc[0], anc[8];
cx anc[8], anc[4];
cx anc[8], anc[0];
tdg anc[4];
tdg anc[0];
t anc[8];
cx anc[8], anc[4];
cx anc[8], anc[0];
h anc[8];
s anc[8];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
// cqrv: alloc anc[9]
h anc[9];
t anc[9];
cx anc[0], anc[9];
cx anc[6], anc[9];
cx anc[9], anc[0];
cx anc[9], anc[6];
tdg anc[0];
tdg anc[6];
t anc[9];
cx anc[9], anc[0];
cx anc[9], anc[6];
h anc[9];
s anc[9];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[1], x[0];
cx x[2], x[0];
cx x[3], x[0];
cx x[4], x[0];
cx x[5], x[0];
cx x[6], x[0];
cx x[7], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
cx anc[6], anc[0];
// cqrv: alloc anc[10]
h anc[10];
t anc[10];
cx x[0], anc[10];
cx anc[0], anc[10];
cx anc[10], x[0];
cx anc[10], anc[0];
tdg x[0];
tdg anc[0];
t anc[10];
cx anc[10], x[0];
cx anc[10], anc[0];
h anc[10];
s anc[10];
cx anc[6], anc[0];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[7], x[0];
cx x[6], x[0];
cx x[5], x[0];
cx x[4], x[0];
cx x[3], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx anc[8], anc[7];
cx anc[9], anc[7];
x anc[7];
// cqrv: alloc anc[11]
h anc[11];
t anc[11];
cx anc[10], anc[11];
cx anc[7], anc[11];
cx anc[11], anc[10];
cx anc[11], anc[7];
tdg anc[10];
tdg anc[7];
t anc[11];
cx anc[11], anc[10];
cx anc[11], anc[7];
h anc[11];
s anc[11];
x anc[7];
cx anc[9], anc[7];
cx anc[8], anc[7];
// cqrv: alloc anc[12]
h anc[12];
t anc[12];
cx anc[11], anc[12];
cx x[10], anc[12];
cx anc[12], anc[11];
cx anc[12], x[10];
tdg anc[11];
tdg x[10];
t anc[12];
cx anc[12], anc[11];
cx anc[12], x[10];
h anc[12];
s anc[12];
z anc[12];
h anc[12];
c[84] = measure anc[12];
if (c[84]) { cz anc[11], x[10]; }
if (c[84]) { x anc[12]; }
// cqrv: free anc[12]
cx anc[8], anc[7];
cx anc[9], anc[7];
x anc[7];
h anc[11];
c[85] = measure anc[11];
if (c[85]) { cz anc[10], anc[7]; }
if (c[85]) { x anc[11]; }
// cqrv: free anc[11]
x anc[7];
cx anc[9], anc[7];
cx anc[8], anc[7];
cx x[1], x[0];
cx x[2], x[0];
cx x[3], x[0];
cx x[4], x[0];
cx x[5], x[0];
cx x[6], x[0];
cx x[7], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
cx anc[6], anc[0];
h anc[10];
c[86] = measure anc[10];
if (c[86]) { cz x[0], anc[0]; }
if (c[86]) { x anc[10]; }
// cqrv: free anc[10]
cx anc[6], anc[0];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[7], x[0];
cx x[6], x[0];
cx x[5], x[0];
cx x[4], x[0];
cx x[3], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
h anc[9];
c[87] = measure anc[9];
if (c[87]) { cz anc[0], anc[6]; }
if (c[87]) { x anc[9]; }
// cqrv: free anc[9]
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
h anc[8];
c[88] = measure anc[8];
if (c[88]) { cz anc[4], anc[0]; }
if (c[88]) { x anc[8]; }
// cqrv: free anc[8]
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[3], anc[2];
h anc[7];
c[89] = measure anc[7];
if (c[89]) { cz anc[0], anc[2]; }
if (c[89]) { x anc[7]; }
// cqrv: free anc[7]
cx anc[3], anc[2];
cx anc[1], anc[0];
cx x[4], x[3];
cx x[5], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[6], x[0];
cx x[7], x[0];
h anc[6];
c[90] = measure anc[6];
if (c[90]) { cz x[3], x[0]; }
if (c[90]) { x anc[6]; }
// cqrv: free anc[6]
cx x[7], x[0];
cx x[6], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx x[5], x[3];
cx x[4], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[7], x[6];
h anc[5];
c[91] = measure anc[5];
if (c[91]) { cz x[0], x[6]; }
if (c[91]) { x anc[5]; }
// cqrv: free anc[5]
cx x[7], x[6];
cx x[2], x[0];
cx x[1], x[0];
h anc[4];
c[92] = measure anc[4];
if (c[92]) { cz x[6], x[7]; }
if (c[92]) { x anc[4]; }
// cqrv: free anc[4]
cx x[4], x[3];
h anc[3];
c[93] = measure anc[3];
if (c[93]) { cz x[5], x[3]; }
if (c[93]) { x anc[3]; }
// cqrv: free anc[3]
cx x[4], x[3];
h anc[2];
c[94] = measure anc[2];
if (c[94]) { cz x[3], x[4]; }
if (c[94]) { x anc[2]; }
// cqrv: free anc[2]
cx x[1], x[0];
h anc[1];
c[95] = measure anc[1];
if (c[95]) { cz x[2], x[0]; }
if (c[95]) { x anc[1]; }
// cqrv: free anc[1]
cx x[1], x[0];
h anc[0];
c[96] = measure anc[0];
if (c[96]) { cz x[0], x[1]; }
if (c[96]) { x anc[0]; }
// cqrv: free anc[0]
h x[0];
h x[1];
h x[2];
h x[3];
h x[4];
h x[5];
h x[6];
h x[7];
x x[0];
x x[1];
x x[2];
x x[3];
x x[4];
x x[5];
x x[6];
x x[7];
// cqrv: alloc anc[0]
h anc[0];
t anc[0];
cx x[0], anc[0];
cx x[1], anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
tdg x[0];
tdg x[1];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
h anc[0];
s anc[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx x[2], anc[1];
cx x[3], anc[1];
cx anc[1], x[2];
cx anc[1], x[3];
tdg x[2];
tdg x[3];
t anc[1];
cx anc[1], x[2];
cx anc[1], x[3];
h anc[1];
s anc[1];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx x[4], anc[2];
cx x[5], anc[2];
cx anc[2], x[4];
cx anc[2], x[5];
tdg x[4];
tdg x[5];
t anc[2];
cx anc[2], x[4];
cx anc[2], x[5];
h anc[2];
s anc[2];
// cqrv: alloc anc[3]
h anc[3];
t anc[3];
cx x[6], anc[3];
cx x[7], anc[3];
cx anc[3], x[6];
cx anc[3], x[7];
tdg x[6];
tdg x[7];
t anc[3];
cx anc[3], x[6];
cx anc[3], x[7];
h anc[3];
s anc[3];
// cqrv: alloc anc[4]
h anc[4];
t anc[4];
cx anc[0], anc[4];
cx anc[1], anc[4];
cx anc[4], anc[0];
cx anc[4], anc[1];
tdg anc[0];
tdg anc[1];
t anc[4];
cx anc[4], anc[0];
cx anc[4], anc[1];
h anc[4];
s anc[4];
// cqrv: alloc anc[5]
h anc[5];
t anc[5];
cx anc[2], anc[5];
cx anc[3], anc[5];
cx anc[5], anc[2];
cx anc[5], anc[3];
tdg anc[2];
tdg anc[3];
t anc[5];
cx anc[5], anc[2];
cx anc[5], anc[3];
h anc[5];
s anc[5];
// cqrv: alloc anc[6]
h anc[6];
t anc[6];
cx anc[4], anc[6];
cx anc[5], anc[6];
cx anc[6], anc[4];
cx anc[6], anc[5];
tdg anc[4];
tdg anc[5];
t anc[6];
cx anc[6], anc[4];
cx anc[6], anc[5];
h anc[6];
s anc[6];
// cqrv: alloc anc[7]
h anc[7];
t anc[7];
cx anc[6], anc[7];
cx x[10], anc[7];
cx anc[7], anc[6];
cx anc[7], x[10];
tdg anc[6];
tdg x[10];
t anc[7];
cx anc[7], anc[6];
cx anc[7], x[10];
h anc[7];
s anc[7];
z anc[7];
h anc[7];
c[97] = measure anc[7];
if (c[97]) { cz anc[6], x[10]; }
if (c[97]) { x anc[7]; }
// cqrv: free anc[7]
h anc[6];
c[98] = measure anc[6];
if (c[98]) { cz anc[4], anc[5]; }
if (c[98]) { x anc[6]; }
// cqrv: free anc[6]
h anc[5];
c[99] = measure anc[5];
if (c[99]) { cz anc[2], anc[3]; }
if (c[99]) { x anc[5]; }
// cqrv: free anc[5]
h anc[4];
c[100] = measure anc[4];
if (c[100]) { cz anc[0], anc[1]; }
if (c[100]) { x anc[4]; }
// cqrv: free anc[4]
h anc[3];
c[101] = measure anc[3];
if (c[101]) { cz x[6], x[7]; }
if (c[101]) { x anc[3]; }
// cqrv: free anc[3]
h anc[2];
c[102] = measure anc[2];
if (c[102]) { cz x[4], x[5]; }
if (c[102]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[103] = measure anc[1];
if (c[103]) { cz x[2], x[3]; }
if (c[103]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[104] = measure anc[0];
if (c[104]) { cz x[0], x[1]; }
if (c[104]) { x anc[0]; }
// cqrv: free anc[0]
x x[0];
x x[1];
x x[2];
x x[3];
x x[4];
x x[5];
x x[6];
x x[7];
h x[0];
h x[1];
h x[2];
h x[3];
h x[4];
h x[5];
h x[6];
h x[7];
z x[10];
// cqrv: alloc anc[0]
h anc[0];
t anc[0];
cx x[0], anc[0];
cx x[1], anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
tdg x[0];
tdg x[1];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
h anc[0];
s anc[0];
cx x[1], x[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx x[2], anc[1];
cx x[0], anc[1];
cx anc[1], x[2];
cx anc[1], x[0];
tdg x[2];
tdg x[0];
t anc[1];
cx anc[1], x[2];
cx anc[1], x[0];
h anc[1];
s anc[1];
cx x[1], x[0];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx x[3], anc[2];
cx x[4], anc[2];
cx anc[2], x[3];
cx anc[2], x[4];
tdg x[3];
tdg x[4];
t anc[2];
cx anc[2], x[3];
cx anc[2], x[4];
h anc[2];
s anc[2];
cx x[4], x[3];
// cqrv: alloc anc[3]
h anc[3];
t anc[3];
cx x[5], anc[3];
cx x[3], anc[3];
cx anc[3], x[5];
cx anc[3], x[3];
tdg x[5];
tdg x[3];
t anc[3];
cx anc[3], x[5];
cx anc[3], x[3];
h anc[3];
s anc[3];
cx x[4], x[3];
// cqrv: alloc anc[4]
h anc[4];
t anc[4];
cx x[6], anc[4];
cx x[7], anc[4];
cx anc[4], x[6];
cx anc[4], x[7];
tdg x[6];
tdg x[7];
t anc[4];
cx anc[4], x[6];
cx anc[4], x[7];
h anc[4];
s anc[4];
cx x[1], x[0];
cx x[2], x[0];
cx x[7], x[6];
// cqrv: alloc anc[5]
h anc[5];
t anc[5];
cx x[0], anc[5];
cx x[6], anc[5];
cx anc[5], x[0];
cx anc[5], x[6];
tdg x[0];
tdg x[6];
t anc[5];
cx anc[5], x[0];
cx anc[5], x[6];
h anc[5];
s anc[5];
cx x[7], x[6];
cx x[2], x[0];
cx x[1], x[0];
cx x[4], x[3];
cx x[5], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[6], x[0];
cx x[7], x[0];
// cqrv: alloc anc[6]
h anc[6];
t anc[6];
cx x[3], anc[6];
cx x[0], anc[6];
cx anc[6], x[3];
cx anc[6], x[0];
tdg x[3];
tdg x[0];
t anc[6];
cx anc[6], x[3];
cx anc[6], x[0];
h anc[6];
s anc[6];
cx x[7], x[0];
cx x[6], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx x[5], x[3];
cx x[4], x[3];
cx anc[1], anc[0];
cx anc[3], anc[2];
// cqrv: alloc anc[7]
h anc[7];
t anc[7];
cx anc[0], anc[7];
cx anc[2], anc[7];
cx anc[7], anc[0];
cx anc[7], anc[2];
tdg anc[0];
tdg anc[2];
t anc[7];
cx anc[7], anc[0];
cx anc[7], anc[2];
h anc[7];
s anc[7];
cx anc[3], anc[2];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
// cqrv: alloc anc[8]
h anc[8];
t anc[8];
cx anc[4], anc[8];
cx anc[0], anc[8];
cx anc[8], anc[4];
cx anc[8], anc[0];
tdg anc[4];
tdg anc[0];
t anc[8];
cx anc[8], anc[4];
cx anc[8], anc[0];
h anc[8];
s anc[8];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
// cqrv: alloc anc[9]
h anc[9];
t anc[9];
cx anc[0], anc[9];
cx anc[6], anc[9];
cx anc[9], anc[0];
cx anc[9], anc[6];
tdg anc[0];
tdg anc[6];
t anc[9];
cx anc[9], anc[0];
cx anc[9], anc[6];
h anc[9];
s anc[9];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[1], x[0];
cx x[2], x[0];
cx x[3], x[0];
cx x[4], x[0];
cx x[5], x[0];
cx x[6], x[0];
cx x[7], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
cx anc[6], anc[0];
// cqrv: alloc anc[10]
h anc[10];
t anc[10];
cx x[0], anc[10];
cx anc[0], anc[10];
cx anc[10], x[0];
cx anc[10], anc[0];
tdg x[0];
tdg anc[0];
t anc[10];
cx anc[10], x[0];
cx anc[10], anc[0];
h anc[10];
s anc[10];
cx anc[6], anc[0];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[7], x[0];
cx x[6], x[0];
cx x[5], x[0];
cx x[4], x[0];
cx x[3], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx anc[8], anc[7];
cx anc[9], anc[7];
x anc[7];
// cqrv: alloc anc[11]
h anc[11];
t anc[11];
cx anc[10], anc[11];
cx anc[7], anc[11];
cx anc[11], anc[10];
cx anc[11], anc[7];
tdg anc[10];
tdg anc[7];
t anc[11];
cx anc[11], anc[10];
cx anc[11], anc[7];
h anc[11];
s anc[11];
x anc[7];
cx anc[9], anc[7];
cx anc[8], anc[7];
// cqrv: alloc anc[12]
h anc[12];
t anc[12];
cx anc[11], anc[12];
cx x[10], anc[12];
cx anc[12], anc[11];
cx anc[12], x[10];
tdg anc[11];
tdg x[10];
t anc[12];
cx anc[12], anc[11];
cx anc[12], x[10];
h anc[12];
s anc[12];
z anc[12];
h anc[12];
c[105] = measure anc[12];
if (c[105]) { cz anc[11], x[10]; }
if (c[105]) { x anc[12]; }
// cqrv: free anc[12]
cx anc[8], anc[7];
cx anc[9], anc[7];
x anc[7];
h anc[11];
c[106] = measure anc[11];
if (c[106]) { cz anc[10], anc[7]; }
if (c[106]) { x anc[11]; }
// cqrv: free anc[11]
x anc[7];
cx anc[9], anc[7];
cx anc[8], anc[7];
cx x[1], x[0];
cx x[2], x[0];
cx x[3], x[0];
cx x[4], x[0];
cx x[5], x[0];
cx x[6], x[0];
cx x[7], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
cx anc[6], anc[0];
h anc[10];
c[107] = measure anc[10];
if (c[107]) { cz x[0], anc[0]; }
if (c[107]) { x anc[10]; }
// cqrv: free anc[10]
cx anc[6], anc[0];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[7], x[0];
cx x[6], x[0];
cx x[5], x[0];
cx x[4], x[0];
cx x[3], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
h anc[9];
c[108] = measure anc[9];
if (c[108]) { cz anc[0], anc[6]; }
if (c[108]) { x anc[9]; }
// cqrv: free anc[9]
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
h anc[8];
c[109] = measure anc[8];
if (c[109]) { cz anc[4], anc[0]; }
if (c[109]) { x anc[8]; }
// cqrv: free anc[8]
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[3], anc[2];
h anc[7];
c[110] = measure anc[7];
if (c[110]) { cz anc[0], anc[2]; }
if (c[110]) { x anc[7]; }
// cqrv: free anc[7]
cx anc[3], anc[2];
cx anc[1], anc[0];
cx x[4], x[3];
cx x[5], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[6], x[0];
cx x[7], x[0];
h anc[6];
c[111] = measure anc[6];
if (c[111]) { cz x[3], x[0]; }
if (c[111]) { x anc[6]; }
// cqrv: free anc[6]
cx x[7], x[0];
cx x[6], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx x[5], x[3];
cx x[4], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[7], x[6];
h anc[5];
c[112] = measure anc[5];
if (c[112]) { cz x[0], x[6]; }
if (c[112]) { x anc[5]; }
// cqrv: free anc[5]
cx x[7], x[6];
cx x[2], x[0];
cx x[1], x[0];
h anc[4];
c[113] = measure anc[4];
if (c[113]) { cz x[6], x[7]; }
if (c[113]) { x anc[4]; }
// cqrv: free anc[4]
cx x[4], x[3];
h anc[3];
c[114] = measure anc[3];
if (c[114]) { cz x[5], x[3]; }
if (c[114]) { x anc[3]; }
// cqrv: free anc[3]
cx x[4], x[3];
h anc[2];
c[115] = measure anc[2];
if (c[115]) { cz x[3], x[4]; }
if (c[115]) { x anc[2]; }
// cqrv: free anc[2]
cx x[1], x[0];
h anc[1];
c[116] = measure anc[1];
if (c[116]) { cz x[2], x[0]; }
if (c[116]) { x anc[1]; }
// cqrv: free anc[1]
cx x[1], x[0];
h anc[0];
c[117] = measure anc[0];
if (c[117]) { cz x[0], x[1]; }
if (c[117]) { x anc[0]; }
// cqrv: free anc[0]
h x[0];
h x[1];
h x[2];
h x[3];
h x[4];
h x[5];
h x[6];
h x[7];
x x[0];
x x[1];
x x[2];
x x[3];
x x[4];
x x[5];
x x[6];
x x[7];
// cqrv: alloc anc[0]
h anc[0];
t anc[0];
cx x[0], anc[0];
cx x[1], anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
tdg x[0];
tdg x[1];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
h anc[0];
s anc[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx x[2], anc[1];
cx x[3], anc[1];
cx anc[1], x[2];
cx anc[1], x[3];
tdg x[2];
tdg x[3];
t anc[1];
cx anc[1], x[2];
cx anc[1], x[3];
h anc[1];
s anc[1];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx x[4], anc[2];
cx x[5], anc[2];
cx anc[2], x[4];
cx anc[2], x[5];
tdg x[4];
tdg x[5];
t anc[2];
cx anc[2], x[4];
cx anc[2], x[5];
h anc[2];
s anc[2];
// cqrv: alloc anc[3]
h anc[3];
t anc[3];
cx x[6], anc[3];
cx x[7], anc[3];
cx anc[3], x[6];
cx anc[3], x[7];
tdg x[6];
tdg x[7];
t anc[3];
cx anc[3], x[6];
cx anc[3], x[7];
h anc[3];
s anc[3];
// cqrv: alloc anc[4]
h anc[4];
t anc[4];
cx anc[0], anc[4];
cx anc[1], anc[4];
cx anc[4], anc[0];
cx anc[4], anc[1];
tdg anc[0];
tdg anc[1];
t anc[4];
cx anc[4], anc[0];
cx anc[4], anc[1];
h anc[4];
s anc[4];
// cqrv: alloc anc[5]
h anc[5];
t anc[5];
cx anc[2], anc[5];
cx anc[3], anc[5];
cx anc[5], anc[2];
cx anc[5], anc[3];
tdg anc[2];
tdg anc[3];
t anc[5];
cx anc[5], anc[2];
cx anc[5], anc[3];
h anc[5];
s anc[5];
// cqrv: alloc anc[6]
h anc[6];
t anc[6];
cx anc[4], anc[6];
cx anc[5], anc[6];
cx anc[6], anc[4];
cx anc[6], anc[5];
tdg anc[4];
tdg anc[5];
t anc[6];
cx anc[6], anc[4];
cx anc[6], anc[5];
h anc[6];
s anc[6];
// cqrv: alloc anc[7]
h anc[7];
t anc[7];
cx anc[6], anc[7];
cx x[10], anc[7];
cx anc[7], anc[6];
cx anc[7], x[10];
tdg anc[6];
tdg x[10];
t anc[7];
cx anc[7], anc[6];
cx anc[7], x[10];
h anc[7];
s anc[7];
z anc[7];
h anc[7];
c[118] = measure anc[7];
if (c[118]) { cz anc[6], x[10]; }
if (c[118]) { x anc[7]; }
// cqrv: free anc[7]
h anc[6];
c[119] = measure anc[6];
if (c[119]) { cz anc[4], anc[5]; }
if (c[119]) { x anc[6]; }
// cqrv: free anc[6]
h anc[5];
c[120] = measure anc[5];
if (c[120]) { cz anc[2], anc[3]; }
if (c[120]) { x anc[5]; }
// cqrv: free anc[5]
h anc[4];
c[121] = measure anc[4];
if (c[121]) { cz anc[0], anc[1]; }
if (c[121]) { x anc[4]; }
// cqrv: free anc[4]
h anc[3];
c[122] = measure anc[3];
if (c[122]) { cz x[6], x[7]; }
if (c[122]) { x anc[3]; }
// cqrv: free anc[3]
h anc[2];
c[123] = measure anc[2];
if (c[123]) { cz x[4], x[5]; }
if (c[123]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[124] = measure anc[1];
if (c[124]) { cz x[2], x[3]; }
if (c[124]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[125] = measure anc[0];
if (c[125]) { cz x[0], x[1]; }
if (c[125]) { x anc[0]; }
// cqrv: free anc[0]
x x[0];
x x[1];
x x[2];
x x[3];
x x[4];
x x[5];
x x[6];
x x[7];
h x[0];
h x[1];
h x[2];
h x[3];
h x[4];
h x[5];
h x[6];
h x[7];
z x[10];
// cqrv: alloc anc[0]
h anc[0];
t anc[0];
cx x[0], anc[0];
cx x[1], anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
tdg x[0];
tdg x[1];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
h anc[0];
s anc[0];
cx x[1], x[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx x[2], anc[1];
cx x[0], anc[1];
cx anc[1], x[2];
cx anc[1], x[0];
tdg x[2];
tdg x[0];
t anc[1];
cx anc[1], x[2];
cx anc[1], x[0];
h anc[1];
s anc[1];
cx x[1], x[0];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx x[3], anc[2];
cx x[4], anc[2];
cx anc[2], x[3];
cx anc[2], x[4];
tdg x[3];
tdg x[4];
t anc[2];
cx anc[2], x[3];
cx anc[2], x[4];
h anc[2];
s anc[2];
cx x[4], x[3];
// cqrv: alloc anc[3]
h anc[3];
t anc[3];
cx x[5], anc[3];
cx x[3], anc[3];
cx anc[3], x[5];
cx anc[3], x[3];
tdg x[5];
tdg x[3];
t anc[3];
cx anc[3], x[5];
cx anc[3], x[3];
h anc[3];
s anc[3];
cx x[4], x[3];
// cqrv: alloc anc[4]
h anc[4];
t anc[4];
cx x[6], anc[4];
cx x[7], anc[4];
cx anc[4], x[6];
cx anc[4], x[7];
tdg x[6];
tdg x[7];
t anc[4];
cx anc[4], x[6];
cx anc[4], x[7];
h anc[4];
s anc[4];
cx x[1], x[0];
cx x[2], x[0];
cx x[7], x[6];
// cqrv: alloc anc[5]
h anc[5];
t anc[5];
cx x[0], anc[5];
cx x[6], anc[5];
cx anc[5], x[0];
cx anc[5], x[6];
tdg x[0];
tdg x[6];
t anc[5];
cx anc[5], x[0];
cx anc[5], x[6];
h anc[5];
s anc[5];
cx x[7], x[6];
cx x[2], x[0];
cx x[1], x[0];
cx x[4], x[3];
cx x[5], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[6], x[0];
cx x[7], x[0];
// cqrv: alloc anc[6]
h anc[6];
t anc[6];
cx x[3], anc[6];
cx x[0], anc[6];
cx anc[6], x[3];
cx anc[6], x[0];
tdg x[3];
tdg x[0];
t anc[6];
cx anc[6], x[3];
cx anc[6], x[0];
h anc[6];
s anc[6];
cx x[7], x[0];
cx x[6], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx x[5], x[3];
cx x[4], x[3];
cx anc[1], anc[0];
cx anc[3], anc[2];
// cqrv: alloc anc[7]
h anc[7];
t anc[7];
cx anc[0], anc[7];
cx anc[2], anc[7];
cx anc[7], anc[0];
cx anc[7], anc[2];
tdg anc[0];
tdg anc[2];
t anc[7];
cx anc[7], anc[0];
cx anc[7], anc[2];
h anc[7];
s anc[7];
cx anc[3], anc[2];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
// cqrv: alloc anc[8]
h anc[8];
t anc[8];
cx anc[4], anc[8];
cx anc[0], anc[8];
cx anc[8], anc[4];
cx anc[8], anc[0];
tdg anc[4];
tdg anc[0];
t anc[8];
cx anc[8], anc[4];
cx anc[8], anc[0];
h anc[8];
s anc[8];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
// cqrv: alloc anc[9]
h anc[9];
t anc[9];
cx anc[0], anc[9];
cx anc[6], anc[9];
cx anc[9], anc[0];
cx anc[9], anc[6];
tdg anc[0];
tdg anc[6];
t anc[9];
cx anc[9], anc[0];
cx anc[9], anc[6];
h anc[9];
s anc[9];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[1], x[0];
cx x[2], x[0];
cx x[3], x[0];
cx x[4], x[0];
cx x[5], x[0];
cx x[6], x[0];
cx x[7], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
cx anc[6], anc[0];
// cqrv: alloc anc[10]
h anc[10];
t anc[10];
cx x[0], anc[10];
cx anc[0], anc[10];
cx anc[10], x[0];
cx anc[10], anc[0];
tdg x[0];
tdg anc[0];
t anc[10];
cx anc[10], x[0];
cx anc[10], anc[0];
h anc[10];
s anc[10];
cx anc[6], anc[0];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[7], x[0];
cx x[6], x[0];
cx x[5], x[0];
cx x[4], x[0];
cx x[3], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx anc[8], anc[7];
cx anc[9], anc[7];
x anc[7];
// cqrv: alloc anc[11]
h anc[11];
t anc[11];
cx anc[10], anc[11];
cx anc[7], anc[11];
cx anc[11], anc[10];
cx anc[11], anc[7];
tdg anc[10];
tdg anc[7];
t anc[11];
cx anc[11], anc[10];
cx anc[11], anc[7];
h anc[11];
s anc[11];
x anc[7];
cx anc[9], anc[7];
cx anc[8], anc[7];
// cqrv: alloc anc[12]
h anc[12];
t anc[12];
cx anc[11], anc[12];
cx x[10], anc[12];
cx anc[12], anc[11];
cx anc[12], x[10];
tdg anc[11];
tdg x[10];
t anc[12];
cx anc[12], anc[11];
cx anc[12], x[10];
h anc[12];
s anc[12];
z anc[12];
h anc[12];
c[126] = measure anc[12];
if (c[126]) { cz anc[11], x[10]; }
if (c[126]) { x anc[12]; }
// cqrv: free anc[12]
cx anc[8], anc[7];
cx anc[9], anc[7];
x anc[7];
h anc[11];
c[127] = measure anc[11];
if (c[127]) { cz anc[10], anc[7]; }
if (c[127]) { x anc[11]; }
// cqrv: free anc[11]
x anc[7];
cx anc[9], anc[7];
cx anc[8], anc[7];
cx x[1], x[0];
cx x[2], x[0];
cx x[3], x[0];
cx x[4], x[0];
cx x[5], x[0];
cx x[6], x[0];
cx x[7], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
cx anc[6], anc[0];
h anc[10];
c[128] = measure anc[10];
if (c[128]) { cz x[0], anc[0]; }
if (c[128]) { x anc[10]; }
// cqrv: free anc[10]
cx anc[6], anc[0];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[7], x[0];
cx x[6], x[0];
cx x[5], x[0];
cx x[4], x[0];
cx x[3], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
h anc[9];
c[129] = measure anc[9];
if (c[129]) { cz anc[0], anc[6]; }
if (c[129]) { x anc[9]; }
// cqrv: free anc[9]
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
h anc[8];
c[130] = measure anc[8];
if (c[130]) { cz anc[4], anc[0]; }
if (c[130]) { x anc[8]; }
// cqrv: free anc[8]
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[3], anc[2];
h anc[7];
c[131] = measure anc[7];
if (c[131]) { cz anc[0], anc[2]; }
if (c[131]) { x anc[7]; }
// cqrv: free anc[7]
cx anc[3], anc[2];
cx anc[1], anc[0];
cx x[4], x[3];
cx x[5], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[6], x[0];
cx x[7], x[0];
h anc[6];
c[132] = measure anc[6];
if (c[132]) { cz x[3], x[0]; }
if (c[132]) { x anc[6]; }
// cqrv: free anc[6]
cx x[7], x[0];
cx x[6], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx x[5], x[3];
cx x[4], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[7], x[6];
h anc[5];
c[133] = measure anc[5];
if (c[133]) { cz x[0], x[6]; }
if (c[133]) { x anc[5]; }
// cqrv: free anc[5]
cx x[7], x[6];
cx x[2], x[0];
cx x[1], x[0];
h anc[4];
c[134] = measure anc[4];
if (c[134]) { cz x[6], x[7]; }
if (c[134]) { x anc[4]; }
// cqrv: free anc[4]
cx x[4], x[3];
h anc[3];
c[135] = measure anc[3];
if (c[135]) { cz x[5], x[3]; }
if (c[135]) { x anc[3]; }
// cqrv: free anc[3]
cx x[4], x[3];
h anc[2];
c[136] = measure anc[2];
if (c[136]) { cz x[3], x[4]; }
if (c[136]) { x anc[2]; }
// cqrv: free anc[2]
cx x[1], x[0];
h anc[1];
c[137] = measure anc[1];
if (c[137]) { cz x[2], x[0]; }
if (c[137]) { x anc[1]; }
// cqrv: free anc[1]
cx x[1], x[0];
h anc[0];
c[138] = measure anc[0];
if (c[138]) { cz x[0], x[1]; }
if (c[138]) { x anc[0]; }
// cqrv: free anc[0]
h x[0];
h x[1];
h x[2];
h x[3];
h x[4];
h x[5];
h x[6];
h x[7];
x x[0];
x x[1];
x x[2];
x x[3];
x x[4];
x x[5];
x x[6];
x x[7];
// cqrv: alloc anc[0]
h anc[0];
t anc[0];
cx x[0], anc[0];
cx x[1], anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
tdg x[0];
tdg x[1];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
h anc[0];
s anc[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx x[2], anc[1];
cx x[3], anc[1];
cx anc[1], x[2];
cx anc[1], x[3];
tdg x[2];
tdg x[3];
t anc[1];
cx anc[1], x[2];
cx anc[1], x[3];
h anc[1];
s anc[1];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx x[4], anc[2];
cx x[5], anc[2];
cx anc[2], x[4];
cx anc[2], x[5];
tdg x[4];
tdg x[5];
t anc[2];
cx anc[2], x[4];
cx anc[2], x[5];
h anc[2];
s anc[2];
// cqrv: alloc anc[3]
h anc[3];
t anc[3];
cx x[6], anc[3];
cx x[7], anc[3];
cx anc[3], x[6];
cx anc[3], x[7];
tdg x[6];
tdg x[7];
t anc[3];
cx anc[3], x[6];
cx anc[3], x[7];
h anc[3];
s anc[3];
// cqrv: alloc anc[4]
h anc[4];
t anc[4];
cx anc[0], anc[4];
cx anc[1], anc[4];
cx anc[4], anc[0];
cx anc[4], anc[1];
tdg anc[0];
tdg anc[1];
t anc[4];
cx anc[4], anc[0];
cx anc[4], anc[1];
h anc[4];
s anc[4];
// cqrv: alloc anc[5]
h anc[5];
t anc[5];
cx anc[2], anc[5];
cx anc[3], anc[5];
cx anc[5], anc[2];
cx anc[5], anc[3];
tdg anc[2];
tdg anc[3];
t anc[5];
cx anc[5], anc[2];
cx anc[5], anc[3];
h anc[5];
s anc[5];
// cqrv: alloc anc[6]
h anc[6];
t anc[6];
cx anc[4], anc[6];
cx anc[5], anc[6];
cx anc[6], anc[4];
cx anc[6], anc[5];
tdg anc[4];
tdg anc[5];
t anc[6];
cx anc[6], anc[4];
cx anc[6], anc[5];
h anc[6];
s anc[6];
// cqrv: alloc anc[7]
h anc[7];
t anc[7];
cx anc[6], anc[7];
cx x[10], anc[7];
cx anc[7], anc[6];
cx anc[7], x[10];
tdg anc[6];
tdg x[10];
t anc[7];
cx anc[7], anc[6];
cx anc[7], x[10];
h anc[7];
s anc[7];
z anc[7];
h anc[7];
c[139] = measure anc[7];
if (c[139]) { cz anc[6], x[10]; }
if (c[139]) { x anc[7]; }
// cqrv: free anc[7]
h anc[6];
c[140] = measure anc[6];
if (c[140]) { cz anc[4], anc[5]; }
if (c[140]) { x anc[6]; }
// cqrv: free anc[6]
h anc[5];
c[141] = measure anc[5];
if (c[141]) { cz anc[2], anc[3]; }
if (c[141]) { x anc[5]; }
// cqrv: free anc[5]
h anc[4];
c[142] = measure anc[4];
if (c[142]) { cz anc[0], anc[1]; }
if (c[142]) { x anc[4]; }
// cqrv: free anc[4]
h anc[3];
c[143] = measure anc[3];
if (c[143]) { cz x[6], x[7]; }
if (c[143]) { x anc[3]; }
// cqrv: free anc[3]
h anc[2];
c[144] = measure anc[2];
if (c[144]) { cz x[4], x[5]; }
if (c[144]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[145] = measure anc[1];
if (c[145]) { cz x[2], x[3]; }
if (c[145]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[146] = measure anc[0];
if (c[146]) { cz x[0], x[1]; }
if (c[146]) { x anc[0]; }
// cqrv: free anc[0]
x x[0];
x x[1];
x x[2];
x x[3];
x x[4];
x x[5];
x x[6];
x x[7];
h x[0];
h x[1];
h x[2];
h x[3];
h x[4];
h x[5];
h x[6];
h x[7];
z x[10];
// cqrv: alloc anc[0]
h anc[0];
t anc[0];
cx x[0], anc[0];
cx x[1], anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
tdg x[0];
tdg x[1];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
h anc[0];
s anc[0];
cx x[1], x[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx x[2], anc[1];
cx x[0], anc[1];
cx anc[1], x[2];
cx anc[1], x[0];
tdg x[2];
tdg x[0];
t anc[1];
cx anc[1], x[2];
cx anc[1], x[0];
h anc[1];
s anc[1];
cx x[1], x[0];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx x[3], anc[2];
cx x[4], anc[2];
cx anc[2], x[3];
cx anc[2], x[4];
tdg x[3];
tdg x[4];
t anc[2];
cx anc[2], x[3];
cx anc[2], x[4];
h anc[2];
s anc[2];
cx x[4], x[3];
// cqrv: alloc anc[3]
h anc[3];
t anc[3];
cx x[5], anc[3];
cx x[3], anc[3];
cx anc[3], x[5];
cx anc[3], x[3];
tdg x[5];
tdg x[3];
t anc[3];
cx anc[3], x[5];
cx anc[3], x[3];
h anc[3];
s anc[3];
cx x[4], x[3];
// cqrv: alloc anc[4]
h anc[4];
t anc[4];
cx x[6], anc[4];
cx x[7], anc[4];
cx anc[4], x[6];
cx anc[4], x[7];
tdg x[6];
tdg x[7];
t anc[4];
cx anc[4], x[6];
cx anc[4], x[7];
h anc[4];
s anc[4];
cx x[1], x[0];
cx x[2], x[0];
cx x[7], x[6];
// cqrv: alloc anc[5]
h anc[5];
t anc[5];
cx x[0], anc[5];
cx x[6], anc[5];
cx anc[5], x[0];
cx anc[5], x[6];
tdg x[0];
tdg x[6];
t anc[5];
cx anc[5], x[0];
cx anc[5], x[6];
h anc[5];
s anc[5];
cx x[7], x[6];
cx x[2], x[0];
cx x[1], x[0];
cx x[4], x[3];
cx x[5], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[6], x[0];
cx x[7], x[0];
// cqrv: alloc anc[6]
h anc[6];
t anc[6];
cx x[3], anc[6];
cx x[0], anc[6];
cx anc[6], x[3];
cx anc[6], x[0];
tdg x[3];
tdg x[0];
t anc[6];
cx anc[6], x[3];
cx anc[6], x[0];
h anc[6];
s anc[6];
cx x[7], x[0];
cx x[6], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx x[5], x[3];
cx x[4], x[3];
cx anc[1], anc[0];
cx anc[3], anc[2];
// cqrv: alloc anc[7]
h anc[7];
t anc[7];
cx anc[0], anc[7];
cx anc[2], anc[7];
cx anc[7], anc[0];
cx anc[7], anc[2];
tdg anc[0];
tdg anc[2];
t anc[7];
cx anc[7], anc[0];
cx anc[7], anc[2];
h anc[7];
s anc[7];
cx anc[3], anc[2];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
// cqrv: alloc anc[8]
h anc[8];
t anc[8];
cx anc[4], anc[8];
cx anc[0], anc[8];
cx anc[8], anc[4];
cx anc[8], anc[0];
tdg anc[4];
tdg anc[0];
t anc[8];
cx anc[8], anc[4];
cx anc[8], anc[0];
h anc[8];
s anc[8];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
// cqrv: alloc anc[9]
h anc[9];
t anc[9];
cx anc[0], anc[9];
cx anc[6], anc[9];
cx anc[9], anc[0];
cx anc[9], anc[6];
tdg anc[0];
tdg anc[6];
t anc[9];
cx anc[9], anc[0];
cx anc[9], anc[6];
h anc[9];
s anc[9];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[1], x[0];
cx x[2], x[0];
cx x[3], x[0];
cx x[4], x[0];
cx x[5], x[0];
cx x[6], x[0];
cx x[7], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
cx anc[6], anc[0];
// cqrv: alloc anc[10]
h anc[10];
t anc[10];
cx x[0], anc[10];
cx anc[0], anc[10];
cx anc[10], x[0];
cx anc[10], anc[0];
tdg x[0];
tdg anc[0];
t anc[10];
cx anc[10], x[0];
cx anc[10], anc[0];
h anc[10];
s anc[10];
cx anc[6], anc[0];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[7], x[0];
cx x[6], x[0];
cx x[5], x[0];
cx x[4], x[0];
cx x[3], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx anc[8], anc[7];
cx anc[9], anc[7];
x anc[7];
// cqrv: alloc anc[11]
h anc[11];
t anc[11];
cx anc[10], anc[11];
cx anc[7], anc[11];
cx anc[11], anc[10];
cx anc[11], anc[7];
tdg anc[10];
tdg anc[7];
t anc[11];
cx anc[11], anc[10];
cx anc[11], anc[7];
h anc[11];
s anc[11];
x anc[7];
cx anc[9], anc[7];
cx anc[8], anc[7];
// cqrv: alloc anc[12]
h anc[12];
t anc[12];
cx anc[11], anc[12];
cx x[11], anc[12];
cx anc[12], anc[11];
cx anc[12], x[11];
tdg anc[11];
tdg x[11];
t anc[12];
cx anc[12], anc[11];
cx anc[12], x[11];
h anc[12];
s anc[12];
z anc[12];
h anc[12];
c[147] = measure anc[12];
if (c[147]) { cz anc[11], x[11]; }
if (c[147]) { x anc[12]; }
// cqrv: free anc[12]
cx anc[8], anc[7];
cx anc[9], anc[7];
x anc[7];
h anc[11];
c[148] = measure anc[11];
if (c[148]) { cz anc[10], anc[7]; }
if (c[148]) { x anc[11]; }
// cqrv: free anc[11]
x anc[7];
cx anc[9], anc[7];
cx anc[8], anc[7];
cx x[1], x[0];
cx x[2], x[0];
cx x[3], x[0];
cx x[4], x[0];
cx x[5], x[0];
cx x[6], x[0];
cx x[7], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
cx anc[6], anc[0];
h anc[10];
c[149] = measure anc[10];
if (c[149]) { cz x[0], anc[0]; }
if (c[149]) { x anc[10]; }
// cqrv: free anc[10]
cx anc[6], anc[0];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[7], x[0];
cx x[6], x[0];
cx x[5], x[0];
cx x[4], x[0];
cx x[3], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
h anc[9];
c[150] = measure anc[9];
if (c[150]) { cz anc[0], anc[6]; }
if (c[150]) { x anc[9]; }
// cqrv: free anc[9]
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
h anc[8];
c[151] = measure anc[8];
if (c[151]) { cz anc[4], anc[0]; }
if (c[151]) { x anc[8]; }
// cqrv: free anc[8]
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[3], anc[2];
h anc[7];
c[152] = measure anc[7];
if (c[152]) { cz anc[0], anc[2]; }
if (c[152]) { x anc[7]; }
// cqrv: free anc[7]
cx anc[3], anc[2];
cx anc[1], anc[0];
cx x[4], x[3];
cx x[5], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[6], x[0];
cx x[7], x[0];
h anc[6];
c[153] = measure anc[6];
if (c[153]) { cz x[3], x[0]; }
if (c[153]) { x anc[6]; }
// cqrv: free anc[6]
cx x[7], x[0];
cx x[6], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx x[5], x[3];
cx x[4], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[7], x[6];
h anc[5];
c[154] = measure anc[5];
if (c[154]) { cz x[0], x[6]; }
if (c[154]) { x anc[5]; }
// cqrv: free anc[5]
cx x[7], x[6];
cx x[2], x[0];
cx x[1], x[0];
h anc[4];
c[155] = measure anc[4];
if (c[155]) { cz x[6], x[7]; }
if (c[155]) { x anc[4]; }
// cqrv: free anc[4]
cx x[4], x[3];
h anc[3];
c[156] = measure anc[3];
if (c[156]) { cz x[5], x[3]; }
if (c[156]) { x anc[3]; }
// cqrv: free anc[3]
cx x[4], x[3];
h anc[2];
c[157] = measure anc[2];
if (c[157]) { cz x[3], x[4]; }
if (c[157]) { x anc[2]; }
// cqrv: free anc[2]
cx x[1], x[0];
h anc[1];
c[158] = measure anc[1];
if (c[158]) { cz x[2], x[0]; }
if (c[158]) { x anc[1]; }
// cqrv: free anc[1]
cx x[1], x[0];
h anc[0];
c[159] = measure anc[0];
if (c[159]) { cz x[0], x[1]; }
if (c[159]) { x anc[0]; }
// cqrv: free anc[0]
h x[0];
h x[1];
h x[2];
h x[3];
h x[4];
h x[5];
h x[6];
h x[7];
x x[0];
x x[1];
x x[2];
x x[3];
x x[4];
x x[5];
x x[6];
x x[7];
// cqrv: alloc anc[0]
h anc[0];
t anc[0];
cx x[0], anc[0];
cx x[1], anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
tdg x[0];
tdg x[1];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
h anc[0];
s anc[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx x[2], anc[1];
cx x[3], anc[1];
cx anc[1], x[2];
cx anc[1], x[3];
tdg x[2];
tdg x[3];
t anc[1];
cx anc[1], x[2];
cx anc[1], x[3];
h anc[1];
s anc[1];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx x[4], anc[2];
cx x[5], anc[2];
cx anc[2], x[4];
cx anc[2], x[5];
tdg x[4];
tdg x[5];
t anc[2];
cx anc[2], x[4];
cx anc[2], x[5];
h anc[2];
s anc[2];
// cqrv: alloc anc[3]
h anc[3];
t anc[3];
cx x[6], anc[3];
cx x[7], anc[3];
cx anc[3], x[6];
cx anc[3], x[7];
tdg x[6];
tdg x[7];
t anc[3];
cx anc[3], x[6];
cx anc[3], x[7];
h anc[3];
s anc[3];
// cqrv: alloc anc[4]
h anc[4];
t anc[4];
cx anc[0], anc[4];
cx anc[1], anc[4];
cx anc[4], anc[0];
cx anc[4], anc[1];
tdg anc[0];
tdg anc[1];
t anc[4];
cx anc[4], anc[0];
cx anc[4], anc[1];
h anc[4];
s anc[4];
// cqrv: alloc anc[5]
h anc[5];
t anc[5];
cx anc[2], anc[5];
cx anc[3], anc[5];
cx anc[5], anc[2];
cx anc[5], anc[3];
tdg anc[2];
tdg anc[3];
t anc[5];
cx anc[5], anc[2];
cx anc[5], anc[3];
h anc[5];
s anc[5];
// cqrv: alloc anc[6]
h anc[6];
t anc[6];
cx anc[4], anc[6];
cx anc[5], anc[6];
cx anc[6], anc[4];
cx anc[6], anc[5];
tdg anc[4];
tdg anc[5];
t anc[6];
cx anc[6], anc[4];
cx anc[6], anc[5];
h anc[6];
s anc[6];
// cqrv: alloc anc[7]
h anc[7];
t anc[7];
cx anc[6], anc[7];
cx x[11], anc[7];
cx anc[7], anc[6];
cx anc[7], x[11];
tdg anc[6];
tdg x[11];
t anc[7];
cx anc[7], anc[6];
cx anc[7], x[11];
h anc[7];
s anc[7];
z anc[7];
h anc[7];
c[160] = measure anc[7];
if (c[160]) { cz anc[6], x[11]; }
if (c[160]) { x anc[7]; }
// cqrv: free anc[7]
h anc[6];
c[161] = measure anc[6];
if (c[161]) { cz anc[4], anc[5]; }
if (c[161]) { x anc[6]; }
// cqrv: free anc[6]
h anc[5];
c[162] = measure anc[5];
if (c[162]) { cz anc[2], anc[3]; }
if (c[162]) { x anc[5]; }
// cqrv: free anc[5]
h anc[4];
c[163] = measure anc[4];
if (c[163]) { cz anc[0], anc[1]; }
if (c[163]) { x anc[4]; }
// cqrv: free anc[4]
h anc[3];
c[164] = measure anc[3];
if (c[164]) { cz x[6], x[7]; }
if (c[164]) { x anc[3]; }
// cqrv: free anc[3]
h anc[2];
c[165] = measure anc[2];
if (c[165]) { cz x[4], x[5]; }
if (c[165]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[166] = measure anc[1];
if (c[166]) { cz x[2], x[3]; }
if (c[166]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[167] = measure anc[0];
if (c[167]) { cz x[0], x[1]; }
if (c[167]) { x anc[0]; }
// cqrv: free anc[0]
x x[0];
x x[1];
x x[2];
x x[3];
x x[4];
x x[5];
x x[6];
x x[7];
h x[0];
h x[1];
h x[2];
h x[3];
h x[4];
h x[5];
h x[6];
h x[7];
z x[11];
// cqrv: alloc anc[0]
h anc[0];
t anc[0];
cx x[0], anc[0];
cx x[1], anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
tdg x[0];
tdg x[1];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
h anc[0];
s anc[0];
cx x[1], x[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx x[2], anc[1];
cx x[0], anc[1];
cx anc[1], x[2];
cx anc[1], x[0];
tdg x[2];
tdg x[0];
t anc[1];
cx anc[1], x[2];
cx anc[1], x[0];
h anc[1];
s anc[1];
cx x[1], x[0];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx x[3], anc[2];
cx x[4], anc[2];
cx anc[2], x[3];
cx anc[2], x[4];
tdg x[3];
tdg x[4];
t anc[2];
cx anc[2], x[3];
cx anc[2], x[4];
h anc[2];
s anc[2];
cx x[4], x[3];
// cqrv: alloc anc[3]
h anc[3];
t anc[3];
cx x[5], anc[3];
cx x[3], anc[3];
cx anc[3], x[5];
cx anc[3], x[3];
tdg x[5];
tdg x[3];
t anc[3];
cx anc[3], x[5];
cx anc[3], x[3];
h anc[3];
s anc[3];
cx x[4], x[3];
// cqrv: alloc anc[4]
h anc[4];
t anc[4];
cx x[6], anc[4];
cx x[7], anc[4];
cx anc[4], x[6];
cx anc[4], x[7];
tdg x[6];
tdg x[7];
t anc[4];
cx anc[4], x[6];
cx anc[4], x[7];
h anc[4];
s anc[4];
cx x[1], x[0];
cx x[2], x[0];
cx x[7], x[6];
// cqrv: alloc anc[5]
h anc[5];
t anc[5];
cx x[0], anc[5];
cx x[6], anc[5];
cx anc[5], x[0];
cx anc[5], x[6];
tdg x[0];
tdg x[6];
t anc[5];
cx anc[5], x[0];
cx anc[5], x[6];
h anc[5];
s anc[5];
cx x[7], x[6];
cx x[2], x[0];
cx x[1], x[0];
cx x[4], x[3];
cx x[5], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[6], x[0];
cx x[7], x[0];
// cqrv: alloc anc[6]
h anc[6];
t anc[6];
cx x[3], anc[6];
cx x[0], anc[6];
cx anc[6], x[3];
cx anc[6], x[0];
tdg x[3];
tdg x[0];
t anc[6];
cx anc[6], x[3];
cx anc[6], x[0];
h anc[6];
s anc[6];
cx x[7], x[0];
cx x[6], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx x[5], x[3];
cx x[4], x[3];
cx anc[1], anc[0];
cx anc[3], anc[2];
// cqrv: alloc anc[7]
h anc[7];
t anc[7];
cx anc[0], anc[7];
cx anc[2], anc[7];
cx anc[7], anc[0];
cx anc[7], anc[2];
tdg anc[0];
tdg anc[2];
t anc[7];
cx anc[7], anc[0];
cx anc[7], anc[2];
h anc[7];
s anc[7];
cx anc[3], anc[2];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
// cqrv: alloc anc[8]
h anc[8];
t anc[8];
cx anc[4], anc[8];
cx anc[0], anc[8];
cx anc[8], anc[4];
cx anc[8], anc[0];
tdg anc[4];
tdg anc[0];
t anc[8];
cx anc[8], anc[4];
cx anc[8], anc[0];
h anc[8];
s anc[8];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
// cqrv: alloc anc[9]
h anc[9];
t anc[9];
cx anc[0], anc[9];
cx anc[6], anc[9];
cx anc[9], anc[0];
cx anc[9], anc[6];
tdg anc[0];
tdg anc[6];
t anc[9];
cx anc[9], anc[0];
cx anc[9], anc[6];
h anc[9];
s anc[9];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[1], x[0];
cx x[2], x[0];
cx x[3], x[0];
cx x[4], x[0];
cx x[5], x[0];
cx x[6], x[0];
cx x[7], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
cx anc[6], anc[0];
// cqrv: alloc anc[10]
h anc[10];
t anc[10];
cx x[0], anc[10];
cx anc[0], anc[10];
cx anc[10], x[0];
cx anc[10], anc[0];
tdg x[0];
tdg anc[0];
t anc[10];
cx anc[10], x[0];
cx anc[10], anc[0];
h anc[10];
s anc[10];
cx anc[6], anc[0];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[7], x[0];
cx x[6], x[0];
cx x[5], x[0];
cx x[4], x[0];
cx x[3], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx anc[8], anc[7];
cx anc[9], anc[7];
x anc[7];
// cqrv: alloc anc[11]
h anc[11];
t anc[11];
cx anc[10], anc[11];
cx anc[7], anc[11];
cx anc[11], anc[10];
cx anc[11], anc[7];
tdg anc[10];
tdg anc[7];
t anc[11];
cx anc[11], anc[10];
cx anc[11], anc[7];
h anc[11];
s anc[11];
x anc[7];
cx anc[9], anc[7];
cx anc[8], anc[7];
// cqrv: alloc anc[12]
h anc[12];
t anc[12];
cx anc[11], anc[12];
cx x[11], anc[12];
cx anc[12], anc[11];
cx anc[12], x[11];
tdg anc[11];
tdg x[11];
t anc[12];
cx anc[12], anc[11];
cx anc[12], x[11];
h anc[12];
s anc[12];
z anc[12];
h anc[12];
c[168] = measure anc[12];
if (c[168]) { cz anc[11], x[11]; }
if (c[168]) { x anc[12]; }
// cqrv: free anc[12]
cx anc[8], anc[7];
cx anc[9], anc[7];
x anc[7];
h anc[11];
c[169] = measure anc[11];
if (c[169]) { cz anc[10], anc[7]; }
if (c[169]) { x anc[11]; }
// cqrv: free anc[11]
x anc[7];
cx anc[9], anc[7];
cx anc[8], anc[7];
cx x[1], x[0];
cx x[2], x[0];
cx x[3], x[0];
cx x[4], x[0];
cx x[5], x[0];
cx x[6], x[0];
cx x[7], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
cx anc[6], anc[0];
h anc[10];
c[170] = measure anc[10];
if (c[170]) { cz x[0], anc[0]; }
if (c[170]) { x anc[10]; }
// cqrv: free anc[10]
cx anc[6], anc[0];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[7], x[0];
cx x[6], x[0];
cx x[5], x[0];
cx x[4], x[0];
cx x[3], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
h anc[9];
c[171] = measure anc[9];
if (c[171]) { cz anc[0], anc[6]; }
if (c[171]) { x anc[9]; }
// cqrv: free anc[9]
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
h anc[8];
c[172] = measure anc[8];
if (c[172]) { cz anc[4], anc[0]; }
if (c[172]) { x anc[8]; }
// cqrv: free anc[8]
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[3], anc[2];
h anc[7];
c[173] = measure anc[7];
if (c[173]) { cz anc[0], anc[2]; }
if (c[173]) { x anc[7]; }
// cqrv: free anc[7]
cx anc[3], anc[2];
cx anc[1], anc[0];
cx x[4], x[3];
cx x[5], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[6], x[0];
cx x[7], x[0];
h anc[6];
c[174] = measure anc[6];
if (c[174]) { cz x[3], x[0]; }
if (c[174]) { x anc[6]; }
// cqrv: free anc[6]
cx x[7], x[0];
cx x[6], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx x[5], x[3];
cx x[4], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[7], x[6];
h anc[5];
c[175] = measure anc[5];
if (c[175]) { cz x[0], x[6]; }
if (c[175]) { x anc[5]; }
// cqrv: free anc[5]
cx x[7], x[6];
cx x[2], x[0];
cx x[1], x[0];
h anc[4];
c[176] = measure anc[4];
if (c[176]) { cz x[6], x[7]; }
if (c[176]) { x anc[4]; }
// cqrv: free anc[4]
cx x[4], x[3];
h anc[3];
c[177] = measure anc[3];
if (c[177]) { cz x[5], x[3]; }
if (c[177]) { x anc[3]; }
// cqrv: free anc[3]
cx x[4], x[3];
h anc[2];
c[178] = measure anc[2];
if (c[178]) { cz x[3], x[4]; }
if (c[178]) { x anc[2]; }
// cqrv: free anc[2]
cx x[1], x[0];
h anc[1];
c[179] = measure anc[1];
if (c[179]) { cz x[2], x[0]; }
if (c[179]) { x anc[1]; }
// cqrv: free anc[1]
cx x[1], x[0];
h anc[0];
c[180] = measure anc[0];
if (c[180]) { cz x[0], x[1]; }
if (c[180]) { x anc[0]; }
// cqrv: free anc[0]
h x[0];
h x[1];
h x[2];
h x[3];
h x[4];
h x[5];
h x[6];
h x[7];
x x[0];
x x[1];
x x[2];
x x[3];
x x[4];
x x[5];
x x[6];
x x[7];
// cqrv: alloc anc[0]
h anc[0];
t anc[0];
cx x[0], anc[0];
cx x[1], anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
tdg x[0];
tdg x[1];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
h anc[0];
s anc[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx x[2], anc[1];
cx x[3], anc[1];
cx anc[1], x[2];
cx anc[1], x[3];
tdg x[2];
tdg x[3];
t anc[1];
cx anc[1], x[2];
cx anc[1], x[3];
h anc[1];
s anc[1];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx x[4], anc[2];
cx x[5], anc[2];
cx anc[2], x[4];
cx anc[2], x[5];
tdg x[4];
tdg x[5];
t anc[2];
cx anc[2], x[4];
cx anc[2], x[5];
h anc[2];
s anc[2];
// cqrv: alloc anc[3]
h anc[3];
t anc[3];
cx x[6], anc[3];
cx x[7], anc[3];
cx anc[3], x[6];
cx anc[3], x[7];
tdg x[6];
tdg x[7];
t anc[3];
cx anc[3], x[6];
cx anc[3], x[7];
h anc[3];
s anc[3];
// cqrv: alloc anc[4]
h anc[4];
t anc[4];
cx anc[0], anc[4];
cx anc[1], anc[4];
cx anc[4], anc[0];
cx anc[4], anc[1];
tdg anc[0];
tdg anc[1];
t anc[4];
cx anc[4], anc[0];
cx anc[4], anc[1];
h anc[4];
s anc[4];
// cqrv: alloc anc[5]
h anc[5];
t anc[5];
cx anc[2], anc[5];
cx anc[3], anc[5];
cx anc[5], anc[2];
cx anc[5], anc[3];
tdg anc[2];
tdg anc[3];
t anc[5];
cx anc[5], anc[2];
cx anc[5], anc[3];
h anc[5];
s anc[5];
// cqrv: alloc anc[6]
h anc[6];
t anc[6];
cx anc[4], anc[6];
cx anc[5], anc[6];
cx anc[6], anc[4];
cx anc[6], anc[5];
tdg anc[4];
tdg anc[5];
t anc[6];
cx anc[6], anc[4];
cx anc[6], anc[5];
h anc[6];
s anc[6];
// cqrv: alloc anc[7]
h anc[7];
t anc[7];
cx anc[6], anc[7];
cx x[11], anc[7];
cx anc[7], anc[6];
cx anc[7], x[11];
tdg anc[6];
tdg x[11];
t anc[7];
cx anc[7], anc[6];
cx anc[7], x[11];
h anc[7];
s anc[7];
z anc[7];
h anc[7];
c[181] = measure anc[7];
if (c[181]) { cz anc[6], x[11]; }
if (c[181]) { x anc[7]; }
// cqrv: free anc[7]
h anc[6];
c[182] = measure anc[6];
if (c[182]) { cz anc[4], anc[5]; }
if (c[182]) { x anc[6]; }
// cqrv: free anc[6]
h anc[5];
c[183] = measure anc[5];
if (c[183]) { cz anc[2], anc[3]; }
if (c[183]) { x anc[5]; }
// cqrv: free anc[5]
h anc[4];
c[184] = measure anc[4];
if (c[184]) { cz anc[0], anc[1]; }
if (c[184]) { x anc[4]; }
// cqrv: free anc[4]
h anc[3];
c[185] = measure anc[3];
if (c[185]) { cz x[6], x[7]; }
if (c[185]) { x anc[3]; }
// cqrv: free anc[3]
h anc[2];
c[186] = measure anc[2];
if (c[186]) { cz x[4], x[5]; }
if (c[186]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[187] = measure anc[1];
if (c[187]) { cz x[2], x[3]; }
if (c[187]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[188] = measure anc[0];
if (c[188]) { cz x[0], x[1]; }
if (c[188]) { x anc[0]; }
// cqrv: free anc[0]
x x[0];
x x[1];
x x[2];
x x[3];
x x[4];
x x[5];
x x[6];
x x[7];
h x[0];
h x[1];
h x[2];
h x[3];
h x[4];
h x[5];
h x[6];
h x[7];
z x[11];
// cqrv: alloc anc[0]
h anc[0];
t anc[0];
cx x[0], anc[0];
cx x[1], anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
tdg x[0];
tdg x[1];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
h anc[0];
s anc[0];
cx x[1], x[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx x[2], anc[1];
cx x[0], anc[1];
cx anc[1], x[2];
cx anc[1], x[0];
tdg x[2];
tdg x[0];
t anc[1];
cx anc[1], x[2];
cx anc[1], x[0];
h anc[1];
s anc[1];
cx x[1], x[0];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx x[3], anc[2];
cx x[4], anc[2];
cx anc[2], x[3];
cx anc[2], x[4];
tdg x[3];
tdg x[4];
t anc[2];
cx anc[2], x[3];
cx anc[2], x[4];
h anc[2];
s anc[2];
cx x[4], x[3];
// cqrv: alloc anc[3]
h anc[3];
t anc[3];
cx x[5], anc[3];
cx x[3], anc[3];
cx anc[3], x[5];
cx anc[3], x[3];
tdg x[5];
tdg x[3];
t anc[3];
cx anc[3], x[5];
cx anc[3], x[3];
h anc[3];
s anc[3];
cx x[4], x[3];
// cqrv: alloc anc[4]
h anc[4];
t anc[4];
cx x[6], anc[4];
cx x[7], anc[4];
cx anc[4], x[6];
cx anc[4], x[7];
tdg x[6];
tdg x[7];
t anc[4];
cx anc[4], x[6];
cx anc[4], x[7];
h anc[4];
s anc[4];
cx x[1], x[0];
cx x[2], x[0];
cx x[7], x[6];
// cqrv: alloc anc[5]
h anc[5];
t anc[5];
cx x[0], anc[5];
cx x[6], anc[5];
cx anc[5], x[0];
cx anc[5], x[6];
tdg x[0];
tdg x[6];
t anc[5];
cx anc[5], x[0];
cx anc[5], x[6];
h anc[5];
s anc[5];
cx x[7], x[6];
cx x[2], x[0];
cx x[1], x[0];
cx x[4], x[3];
cx x[5], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[6], x[0];
cx x[7], x[0];
// cqrv: alloc anc[6]
h anc[6];
t anc[6];
cx x[3], anc[6];
cx x[0], anc[6];
cx anc[6], x[3];
cx anc[6], x[0];
tdg x[3];
tdg x[0];
t anc[6];
cx anc[6], x[3];
cx anc[6], x[0];
h anc[6];
s anc[6];
cx x[7], x[0];
cx x[6], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx x[5], x[3];
cx x[4], x[3];
cx anc[1], anc[0];
cx anc[3], anc[2];
// cqrv: alloc anc[7]
h anc[7];
t anc[7];
cx anc[0], anc[7];
cx anc[2], anc[7];
cx anc[7], anc[0];
cx anc[7], anc[2];
tdg anc[0];
tdg anc[2];
t anc[7];
cx anc[7], anc[0];
cx anc[7], anc[2];
h anc[7];
s anc[7];
cx anc[3], anc[2];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
// cqrv: alloc anc[8]
h anc[8];
t anc[8];
cx anc[4], anc[8];
cx anc[0], anc[8];
cx anc[8], anc[4];
cx anc[8], anc[0];
tdg anc[4];
tdg anc[0];
t anc[8];
cx anc[8], anc[4];
cx anc[8], anc[0];
h anc[8];
s anc[8];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
// cqrv: alloc anc[9]
h anc[9];
t anc[9];
cx anc[0], anc[9];
cx anc[6], anc[9];
cx anc[9], anc[0];
cx anc[9], anc[6];
tdg anc[0];
tdg anc[6];
t anc[9];
cx anc[9], anc[0];
cx anc[9], anc[6];
h anc[9];
s anc[9];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[1], x[0];
cx x[2], x[0];
cx x[3], x[0];
cx x[4], x[0];
cx x[5], x[0];
cx x[6], x[0];
cx x[7], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
cx anc[6], anc[0];
// cqrv: alloc anc[10]
h anc[10];
t anc[10];
cx x[0], anc[10];
cx anc[0], anc[10];
cx anc[10], x[0];
cx anc[10], anc[0];
tdg x[0];
tdg anc[0];
t anc[10];
cx anc[10], x[0];
cx anc[10], anc[0];
h anc[10];
s anc[10];
cx anc[6], anc[0];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[7], x[0];
cx x[6], x[0];
cx x[5], x[0];
cx x[4], x[0];
cx x[3], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx anc[8], anc[7];
cx anc[9], anc[7];
x anc[7];
// cqrv: alloc anc[11]
h anc[11];
t anc[11];
cx anc[10], anc[11];
cx anc[7], anc[11];
cx anc[11], anc[10];
cx anc[11], anc[7];
tdg anc[10];
tdg anc[7];
t anc[11];
cx anc[11], anc[10];
cx anc[11], anc[7];
h anc[11];
s anc[11];
x anc[7];
cx anc[9], anc[7];
cx anc[8], anc[7];
// cqrv: alloc anc[12]
h anc[12];
t anc[12];
cx anc[11], anc[12];
cx x[11], anc[12];
cx anc[12], anc[11];
cx anc[12], x[11];
tdg anc[11];
tdg x[11];
t anc[12];
cx anc[12], anc[11];
cx anc[12], x[11];
h anc[12];
s anc[12];
z anc[12];
h anc[12];
c[189] = measure anc[12];
if (c[189]) { cz anc[11], x[11]; }
if (c[189]) { x anc[12]; }
// cqrv: free anc[12]
cx anc[8], anc[7];
cx anc[9], anc[7];
x anc[7];
h anc[11];
c[190] = measure anc[11];
if (c[190]) { cz anc[10], anc[7]; }
if (c[190]) { x anc[11]; }
// cqrv: free anc[11]
x anc[7];
cx anc[9], anc[7];
cx anc[8], anc[7];
cx x[1], x[0];
cx x[2], x[0];
cx x[3], x[0];
cx x[4], x[0];
cx x[5], x[0];
cx x[6], x[0];
cx x[7], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
cx anc[6], anc[0];
h anc[10];
c[191] = measure anc[10];
if (c[191]) { cz x[0], anc[0]; }
if (c[191]) { x anc[10]; }
// cqrv: free anc[10]
cx anc[6], anc[0];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[7], x[0];
cx x[6], x[0];
cx x[5], x[0];
cx x[4], x[0];
cx x[3], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
h anc[9];
c[192] = measure anc[9];
if (c[192]) { cz anc[0], anc[6]; }
if (c[192]) { x anc[9]; }
// cqrv: free anc[9]
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
h anc[8];
c[193] = measure anc[8];
if (c[193]) { cz anc[4], anc[0]; }
if (c[193]) { x anc[8]; }
// cqrv: free anc[8]
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[3], anc[2];
h anc[7];
c[194] = measure anc[7];
if (c[194]) { cz anc[0], anc[2]; }
if (c[194]) { x anc[7]; }
// cqrv: free anc[7]
cx anc[3], anc[2];
cx anc[1], anc[0];
cx x[4], x[3];
cx x[5], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[6], x[0];
cx x[7], x[0];
h anc[6];
c[195] = measure anc[6];
if (c[195]) { cz x[3], x[0]; }
if (c[195]) { x anc[6]; }
// cqrv: free anc[6]
cx x[7], x[0];
cx x[6], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx x[5], x[3];
cx x[4], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[7], x[6];
h anc[5];
c[196] = measure anc[5];
if (c[196]) { cz x[0], x[6]; }
if (c[196]) { x anc[5]; }
// cqrv: free anc[5]
cx x[7], x[6];
cx x[2], x[0];
cx x[1], x[0];
h anc[4];
c[197] = measure anc[4];
if (c[197]) { cz x[6], x[7]; }
if (c[197]) { x anc[4]; }
// cqrv: free anc[4]
cx x[4], x[3];
h anc[3];
c[198] = measure anc[3];
if (c[198]) { cz x[5], x[3]; }
if (c[198]) { x anc[3]; }
// cqrv: free anc[3]
cx x[4], x[3];
h anc[2];
c[199] = measure anc[2];
if (c[199]) { cz x[3], x[4]; }
if (c[199]) { x anc[2]; }
// cqrv: free anc[2]
cx x[1], x[0];
h anc[1];
c[200] = measure anc[1];
if (c[200]) { cz x[2], x[0]; }
if (c[200]) { x anc[1]; }
// cqrv: free anc[1]
cx x[1], x[0];
h anc[0];
c[201] = measure anc[0];
if (c[201]) { cz x[0], x[1]; }
if (c[201]) { x anc[0]; }
// cqrv: free anc[0]
h x[0];
h x[1];
h x[2];
h x[3];
h x[4];
h x[5];
h x[6];
h x[7];
x x[0];
x x[1];
x x[2];
x x[3];
x x[4];
x x[5];
x x[6];
x x[7];
// cqrv: alloc anc[0]
h anc[0];
t anc[0];
cx x[0], anc[0];
cx x[1], anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
tdg x[0];
tdg x[1];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
h anc[0];
s anc[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx x[2], anc[1];
cx x[3], anc[1];
cx anc[1], x[2];
cx anc[1], x[3];
tdg x[2];
tdg x[3];
t anc[1];
cx anc[1], x[2];
cx anc[1], x[3];
h anc[1];
s anc[1];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx x[4], anc[2];
cx x[5], anc[2];
cx anc[2], x[4];
cx anc[2], x[5];
tdg x[4];
tdg x[5];
t anc[2];
cx anc[2], x[4];
cx anc[2], x[5];
h anc[2];
s anc[2];
// cqrv: alloc anc[3]
h anc[3];
t anc[3];
cx x[6], anc[3];
cx x[7], anc[3];
cx anc[3], x[6];
cx anc[3], x[7];
tdg x[6];
tdg x[7];
t anc[3];
cx anc[3], x[6];
cx anc[3], x[7];
h anc[3];
s anc[3];
// cqrv: alloc anc[4]
h anc[4];
t anc[4];
cx anc[0], anc[4];
cx anc[1], anc[4];
cx anc[4], anc[0];
cx anc[4], anc[1];
tdg anc[0];
tdg anc[1];
t anc[4];
cx anc[4], anc[0];
cx anc[4], anc[1];
h anc[4];
s anc[4];
// cqrv: alloc anc[5]
h anc[5];
t anc[5];
cx anc[2], anc[5];
cx anc[3], anc[5];
cx anc[5], anc[2];
cx anc[5], anc[3];
tdg anc[2];
tdg anc[3];
t anc[5];
cx anc[5], anc[2];
cx anc[5], anc[3];
h anc[5];
s anc[5];
// cqrv: alloc anc[6]
h anc[6];
t anc[6];
cx anc[4], anc[6];
cx anc[5], anc[6];
cx anc[6], anc[4];
cx anc[6], anc[5];
tdg anc[4];
tdg anc[5];
t anc[6];
cx anc[6], anc[4];
cx anc[6], anc[5];
h anc[6];
s anc[6];
// cqrv: alloc anc[7]
h anc[7];
t anc[7];
cx anc[6], anc[7];
cx x[11], anc[7];
cx anc[7], anc[6];
cx anc[7], x[11];
tdg anc[6];
tdg x[11];
t anc[7];
cx anc[7], anc[6];
cx anc[7], x[11];
h anc[7];
s anc[7];
z anc[7];
h anc[7];
c[202] = measure anc[7];
if (c[202]) { cz anc[6], x[11]; }
if (c[202]) { x anc[7]; }
// cqrv: free anc[7]
h anc[6];
c[203] = measure anc[6];
if (c[203]) { cz anc[4], anc[5]; }
if (c[203]) { x anc[6]; }
// cqrv: free anc[6]
h anc[5];
c[204] = measure anc[5];
if (c[204]) { cz anc[2], anc[3]; }
if (c[204]) { x anc[5]; }
// cqrv: free anc[5]
h anc[4];
c[205] = measure anc[4];
if (c[205]) { cz anc[0], anc[1]; }
if (c[205]) { x anc[4]; }
// cqrv: free anc[4]
h anc[3];
c[206] = measure anc[3];
if (c[206]) { cz x[6], x[7]; }
if (c[206]) { x anc[3]; }
// cqrv: free anc[3]
h anc[2];
c[207] = measure anc[2];
if (c[207]) { cz x[4], x[5]; }
if (c[207]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[208] = measure anc[1];
if (c[208]) { cz x[2], x[3]; }
if (c[208]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[209] = measure anc[0];
if (c[209]) { cz x[0], x[1]; }
if (c[209]) { x anc[0]; }
// cqrv: free anc[0]
x x[0];
x x[1];
x x[2];
x x[3];
x x[4];
x x[5];
x x[6];
x x[7];
h x[0];
h x[1];
h x[2];
h x[3];
h x[4];
h x[5];
h x[6];
h x[7];
z x[11];
// cqrv: alloc anc[0]
h anc[0];
t anc[0];
cx x[0], anc[0];
cx x[1], anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
tdg x[0];
tdg x[1];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
h anc[0];
s anc[0];
cx x[1], x[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx x[2], anc[1];
cx x[0], anc[1];
cx anc[1], x[2];
cx anc[1], x[0];
tdg x[2];
tdg x[0];
t anc[1];
cx anc[1], x[2];
cx anc[1], x[0];
h anc[1];
s anc[1];
cx x[1], x[0];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx x[3], anc[2];
cx x[4], anc[2];
cx anc[2], x[3];
cx anc[2], x[4];
tdg x[3];
tdg x[4];
t anc[2];
cx anc[2], x[3];
cx anc[2], x[4];
h anc[2];
s anc[2];
cx x[4], x[3];
// cqrv: alloc anc[3]
h anc[3];
t anc[3];
cx x[5], anc[3];
cx x[3], anc[3];
cx anc[3], x[5];
cx anc[3], x[3];
tdg x[5];
tdg x[3];
t anc[3];
cx anc[3], x[5];
cx anc[3], x[3];
h anc[3];
s anc[3];
cx x[4], x[3];
// cqrv: alloc anc[4]
h anc[4];
t anc[4];
cx x[6], anc[4];
cx x[7], anc[4];
cx anc[4], x[6];
cx anc[4], x[7];
tdg x[6];
tdg x[7];
t anc[4];
cx anc[4], x[6];
cx anc[4], x[7];
h anc[4];
s anc[4];
cx x[1], x[0];
cx x[2], x[0];
cx x[7], x[6];
// cqrv: alloc anc[5]
h anc[5];
t anc[5];
cx x[0], anc[5];
cx x[6], anc[5];
cx anc[5], x[0];
cx anc[5], x[6];
tdg x[0];
tdg x[6];
t anc[5];
cx anc[5], x[0];
cx anc[5], x[6];
h anc[5];
s anc[5];
cx x[7], x[6];
cx x[2], x[0];
cx x[1], x[0];
cx x[4], x[3];
cx x[5], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[6], x[0];
cx x[7], x[0];
// cqrv: alloc anc[6]
h anc[6];
t anc[6];
cx x[3], anc[6];
cx x[0], anc[6];
cx anc[6], x[3];
cx anc[6], x[0];
tdg x[3];
tdg x[0];
t anc[6];
cx anc[6], x[3];
cx anc[6], x[0];
h anc[6];
s anc[6];
cx x[7], x[0];
cx x[6], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx x[5], x[3];
cx x[4], x[3];
cx anc[1], anc[0];
cx anc[3], anc[2];
// cqrv: alloc anc[7]
h anc[7];
t anc[7];
cx anc[0], anc[7];
cx anc[2], anc[7];
cx anc[7], anc[0];
cx anc[7], anc[2];
tdg anc[0];
tdg anc[2];
t anc[7];
cx anc[7], anc[0];
cx anc[7], anc[2];
h anc[7];
s anc[7];
cx anc[3], anc[2];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
// cqrv: alloc anc[8]
h anc[8];
t anc[8];
cx anc[4], anc[8];
cx anc[0], anc[8];
cx anc[8], anc[4];
cx anc[8], anc[0];
tdg anc[4];
tdg anc[0];
t anc[8];
cx anc[8], anc[4];
cx anc[8], anc[0];
h anc[8];
s anc[8];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
// cqrv: alloc anc[9]
h anc[9];
t anc[9];
cx anc[0], anc[9];
cx anc[6], anc[9];
cx anc[9], anc[0];
cx anc[9], anc[6];
tdg anc[0];
tdg anc[6];
t anc[9];
cx anc[9], anc[0];
cx anc[9], anc[6];
h anc[9];
s anc[9];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[1], x[0];
cx x[2], x[0];
cx x[3], x[0];
cx x[4], x[0];
cx x[5], x[0];
cx x[6], x[0];
cx x[7], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
cx anc[6], anc[0];
// cqrv: alloc anc[10]
h anc[10];
t anc[10];
cx x[0], anc[10];
cx anc[0], anc[10];
cx anc[10], x[0];
cx anc[10], anc[0];
tdg x[0];
tdg anc[0];
t anc[10];
cx anc[10], x[0];
cx anc[10], anc[0];
h anc[10];
s anc[10];
cx anc[6], anc[0];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[7], x[0];
cx x[6], x[0];
cx x[5], x[0];
cx x[4], x[0];
cx x[3], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx anc[8], anc[7];
cx anc[9], anc[7];
x anc[7];
// cqrv: alloc anc[11]
h anc[11];
t anc[11];
cx anc[10], anc[11];
cx anc[7], anc[11];
cx anc[11], anc[10];
cx anc[11], anc[7];
tdg anc[10];
tdg anc[7];
t anc[11];
cx anc[11], anc[10];
cx anc[11], anc[7];
h anc[11];
s anc[11];
x anc[7];
cx anc[9], anc[7];
cx anc[8], anc[7];
// cqrv: alloc anc[12]
h anc[12];
t anc[12];
cx anc[11], anc[12];
cx x[11], anc[12];
cx anc[12], anc[11];
cx anc[12], x[11];
tdg anc[11];
tdg x[11];
t anc[12];
cx anc[12], anc[11];
cx anc[12], x[11];
h anc[12];
s anc[12];
z anc[12];
h anc[12];
c[210] = measure anc[12];
if (c[210]) { cz anc[11], x[11]; }
if (c[210]) { x anc[12]; }
// cqrv: free anc[12]
cx anc[8], anc[7];
cx anc[9], anc[7];
x anc[7];
h anc[11];
c[211] = measure anc[11];
if (c[211]) { cz anc[10], anc[7]; }
if (c[211]) { x anc[11]; }
// cqrv: free anc[11]
x anc[7];
cx anc[9], anc[7];
cx anc[8], anc[7];
cx x[1], x[0];
cx x[2], x[0];
cx x[3], x[0];
cx x[4], x[0];
cx x[5], x[0];
cx x[6], x[0];
cx x[7], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
cx anc[6], anc[0];
h anc[10];
c[212] = measure anc[10];
if (c[212]) { cz x[0], anc[0]; }
if (c[212]) { x anc[10]; }
// cqrv: free anc[10]
cx anc[6], anc[0];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[7], x[0];
cx x[6], x[0];
cx x[5], x[0];
cx x[4], x[0];
cx x[3], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
h anc[9];
c[213] = measure anc[9];
if (c[213]) { cz anc[0], anc[6]; }
if (c[213]) { x anc[9]; }
// cqrv: free anc[9]
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
h anc[8];
c[214] = measure anc[8];
if (c[214]) { cz anc[4], anc[0]; }
if (c[214]) { x anc[8]; }
// cqrv: free anc[8]
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[3], anc[2];
h anc[7];
c[215] = measure anc[7];
if (c[215]) { cz anc[0], anc[2]; }
if (c[215]) { x anc[7]; }
// cqrv: free anc[7]
cx anc[3], anc[2];
cx anc[1], anc[0];
cx x[4], x[3];
cx x[5], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[6], x[0];
cx x[7], x[0];
h anc[6];
c[216] = measure anc[6];
if (c[216]) { cz x[3], x[0]; }
if (c[216]) { x anc[6]; }
// cqrv: free anc[6]
cx x[7], x[0];
cx x[6], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx x[5], x[3];
cx x[4], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[7], x[6];
h anc[5];
c[217] = measure anc[5];
if (c[217]) { cz x[0], x[6]; }
if (c[217]) { x anc[5]; }
// cqrv: free anc[5]
cx x[7], x[6];
cx x[2], x[0];
cx x[1], x[0];
h anc[4];
c[218] = measure anc[4];
if (c[218]) { cz x[6], x[7]; }
if (c[218]) { x anc[4]; }
// cqrv: free anc[4]
cx x[4], x[3];
h anc[3];
c[219] = measure anc[3];
if (c[219]) { cz x[5], x[3]; }
if (c[219]) { x anc[3]; }
// cqrv: free anc[3]
cx x[4], x[3];
h anc[2];
c[220] = measure anc[2];
if (c[220]) { cz x[3], x[4]; }
if (c[220]) { x anc[2]; }
// cqrv: free anc[2]
cx x[1], x[0];
h anc[1];
c[221] = measure anc[1];
if (c[221]) { cz x[2], x[0]; }
if (c[221]) { x anc[1]; }
// cqrv: free anc[1]
cx x[1], x[0];
h anc[0];
c[222] = measure anc[0];
if (c[222]) { cz x[0], x[1]; }
if (c[222]) { x anc[0]; }
// cqrv: free anc[0]
h x[0];
h x[1];
h x[2];
h x[3];
h x[4];
h x[5];
h x[6];
h x[7];
x x[0];
x x[1];
x x[2];
x x[3];
x x[4];
x x[5];
x x[6];
x x[7];
// cqrv: alloc anc[0]
h anc[0];
t anc[0];
cx x[0], anc[0];
cx x[1], anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
tdg x[0];
tdg x[1];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
h anc[0];
s anc[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx x[2], anc[1];
cx x[3], anc[1];
cx anc[1], x[2];
cx anc[1], x[3];
tdg x[2];
tdg x[3];
t anc[1];
cx anc[1], x[2];
cx anc[1], x[3];
h anc[1];
s anc[1];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx x[4], anc[2];
cx x[5], anc[2];
cx anc[2], x[4];
cx anc[2], x[5];
tdg x[4];
tdg x[5];
t anc[2];
cx anc[2], x[4];
cx anc[2], x[5];
h anc[2];
s anc[2];
// cqrv: alloc anc[3]
h anc[3];
t anc[3];
cx x[6], anc[3];
cx x[7], anc[3];
cx anc[3], x[6];
cx anc[3], x[7];
tdg x[6];
tdg x[7];
t anc[3];
cx anc[3], x[6];
cx anc[3], x[7];
h anc[3];
s anc[3];
// cqrv: alloc anc[4]
h anc[4];
t anc[4];
cx anc[0], anc[4];
cx anc[1], anc[4];
cx anc[4], anc[0];
cx anc[4], anc[1];
tdg anc[0];
tdg anc[1];
t anc[4];
cx anc[4], anc[0];
cx anc[4], anc[1];
h anc[4];
s anc[4];
// cqrv: alloc anc[5]
h anc[5];
t anc[5];
cx anc[2], anc[5];
cx anc[3], anc[5];
cx anc[5], anc[2];
cx anc[5], anc[3];
tdg anc[2];
tdg anc[3];
t anc[5];
cx anc[5], anc[2];
cx anc[5], anc[3];
h anc[5];
s anc[5];
// cqrv: alloc anc[6]
h anc[6];
t anc[6];
cx anc[4], anc[6];
cx anc[5], anc[6];
cx anc[6], anc[4];
cx anc[6], anc[5];
tdg anc[4];
tdg anc[5];
t anc[6];
cx anc[6], anc[4];
cx anc[6], anc[5];
h anc[6];
s anc[6];
// cqrv: alloc anc[7]
h anc[7];
t anc[7];
cx anc[6], anc[7];
cx x[11], anc[7];
cx anc[7], anc[6];
cx anc[7], x[11];
tdg anc[6];
tdg x[11];
t anc[7];
cx anc[7], anc[6];
cx anc[7], x[11];
h anc[7];
s anc[7];
z anc[7];
h anc[7];
c[223] = measure anc[7];
if (c[223]) { cz anc[6], x[11]; }
if (c[223]) { x anc[7]; }
// cqrv: free anc[7]
h anc[6];
c[224] = measure anc[6];
if (c[224]) { cz anc[4], anc[5]; }
if (c[224]) { x anc[6]; }
// cqrv: free anc[6]
h anc[5];
c[225] = measure anc[5];
if (c[225]) { cz anc[2], anc[3]; }
if (c[225]) { x anc[5]; }
// cqrv: free anc[5]
h anc[4];
c[226] = measure anc[4];
if (c[226]) { cz anc[0], anc[1]; }
if (c[226]) { x anc[4]; }
// cqrv: free anc[4]
h anc[3];
c[227] = measure anc[3];
if (c[227]) { cz x[6], x[7]; }
if (c[227]) { x anc[3]; }
// cqrv: free anc[3]
h anc[2];
c[228] = measure anc[2];
if (c[228]) { cz x[4], x[5]; }
if (c[228]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[229] = measure anc[1];
if (c[229]) { cz x[2], x[3]; }
if (c[229]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[230] = measure anc[0];
if (c[230]) { cz x[0], x[1]; }
if (c[230]) { x anc[0]; }
// cqrv: free anc[0]
x x[0];
x x[1];
x x[2];
x x[3];
x x[4];
x x[5];
x x[6];
x x[7];
h x[0];
h x[1];
h x[2];
h x[3];
h x[4];
h x[5];
h x[6];
h x[7];
z x[11];
// cqrv: alloc anc[0]
h anc[0];
t anc[0];
cx x[0], anc[0];
cx x[1], anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
tdg x[0];
tdg x[1];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
h anc[0];
s anc[0];
cx x[1], x[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx x[2], anc[1];
cx x[0], anc[1];
cx anc[1], x[2];
cx anc[1], x[0];
tdg x[2];
tdg x[0];
t anc[1];
cx anc[1], x[2];
cx anc[1], x[0];
h anc[1];
s anc[1];
cx x[1], x[0];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx x[3], anc[2];
cx x[4], anc[2];
cx anc[2], x[3];
cx anc[2], x[4];
tdg x[3];
tdg x[4];
t anc[2];
cx anc[2], x[3];
cx anc[2], x[4];
h anc[2];
s anc[2];
cx x[4], x[3];
// cqrv: alloc anc[3]
h anc[3];
t anc[3];
cx x[5], anc[3];
cx x[3], anc[3];
cx anc[3], x[5];
cx anc[3], x[3];
tdg x[5];
tdg x[3];
t anc[3];
cx anc[3], x[5];
cx anc[3], x[3];
h anc[3];
s anc[3];
cx x[4], x[3];
// cqrv: alloc anc[4]
h anc[4];
t anc[4];
cx x[6], anc[4];
cx x[7], anc[4];
cx anc[4], x[6];
cx anc[4], x[7];
tdg x[6];
tdg x[7];
t anc[4];
cx anc[4], x[6];
cx anc[4], x[7];
h anc[4];
s anc[4];
cx x[1], x[0];
cx x[2], x[0];
cx x[7], x[6];
// cqrv: alloc anc[5]
h anc[5];
t anc[5];
cx x[0], anc[5];
cx x[6], anc[5];
cx anc[5], x[0];
cx anc[5], x[6];
tdg x[0];
tdg x[6];
t anc[5];
cx anc[5], x[0];
cx anc[5], x[6];
h anc[5];
s anc[5];
cx x[7], x[6];
cx x[2], x[0];
cx x[1], x[0];
cx x[4], x[3];
cx x[5], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[6], x[0];
cx x[7], x[0];
// cqrv: alloc anc[6]
h anc[6];
t anc[6];
cx x[3], anc[6];
cx x[0], anc[6];
cx anc[6], x[3];
cx anc[6], x[0];
tdg x[3];
tdg x[0];
t anc[6];
cx anc[6], x[3];
cx anc[6], x[0];
h anc[6];
s anc[6];
cx x[7], x[0];
cx x[6], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx x[5], x[3];
cx x[4], x[3];
cx anc[1], anc[0];
cx anc[3], anc[2];
// cqrv: alloc anc[7]
h anc[7];
t anc[7];
cx anc[0], anc[7];
cx anc[2], anc[7];
cx anc[7], anc[0];
cx anc[7], anc[2];
tdg anc[0];
tdg anc[2];
t anc[7];
cx anc[7], anc[0];
cx anc[7], anc[2];
h anc[7];
s anc[7];
cx anc[3], anc[2];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
// cqrv: alloc anc[8]
h anc[8];
t anc[8];
cx anc[4], anc[8];
cx anc[0], anc[8];
cx anc[8], anc[4];
cx anc[8], anc[0];
tdg anc[4];
tdg anc[0];
t anc[8];
cx anc[8], anc[4];
cx anc[8], anc[0];
h anc[8];
s anc[8];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
// cqrv: alloc anc[9]
h anc[9];
t anc[9];
cx anc[0], anc[9];
cx anc[6], anc[9];
cx anc[9], anc[0];
cx anc[9], anc[6];
tdg anc[0];
tdg anc[6];
t anc[9];
cx anc[9], anc[0];
cx anc[9], anc[6];
h anc[9];
s anc[9];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[1], x[0];
cx x[2], x[0];
cx x[3], x[0];
cx x[4], x[0];
cx x[5], x[0];
cx x[6], x[0];
cx x[7], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
cx anc[6], anc[0];
// cqrv: alloc anc[10]
h anc[10];
t anc[10];
cx x[0], anc[10];
cx anc[0], anc[10];
cx anc[10], x[0];
cx anc[10], anc[0];
tdg x[0];
tdg anc[0];
t anc[10];
cx anc[10], x[0];
cx anc[10], anc[0];
h anc[10];
s anc[10];
cx anc[6], anc[0];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[7], x[0];
cx x[6], x[0];
cx x[5], x[0];
cx x[4], x[0];
cx x[3], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx anc[8], anc[7];
cx anc[9], anc[7];
x anc[7];
// cqrv: alloc anc[11]
h anc[11];
t anc[11];
cx anc[10], anc[11];
cx anc[7], anc[11];
cx anc[11], anc[10];
cx anc[11], anc[7];
tdg anc[10];
tdg anc[7];
t anc[11];
cx anc[11], anc[10];
cx anc[11], anc[7];
h anc[11];
s anc[11];
x anc[7];
cx anc[9], anc[7];
cx anc[8], anc[7];
// cqrv: alloc anc[12]
h anc[12];
t anc[12];
cx anc[11], anc[12];
cx x[11], anc[12];
cx anc[12], anc[11];
cx anc[12], x[11];
tdg anc[11];
tdg x[11];
t anc[12];
cx anc[12], anc[11];
cx anc[12], x[11];
h anc[12];
s anc[12];
z anc[12];
h anc[12];
c[231] = measure anc[12];
if (c[231]) { cz anc[11], x[11]; }
if (c[231]) { x anc[12]; }
// cqrv: free anc[12]
cx anc[8], anc[7];
cx anc[9], anc[7];
x anc[7];
h anc[11];
c[232] = measure anc[11];
if (c[232]) { cz anc[10], anc[7]; }
if (c[232]) { x anc[11]; }
// cqrv: free anc[11]
x anc[7];
cx anc[9], anc[7];
cx anc[8], anc[7];
cx x[1], x[0];
cx x[2], x[0];
cx x[3], x[0];
cx x[4], x[0];
cx x[5], x[0];
cx x[6], x[0];
cx x[7], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
cx anc[6], anc[0];
h anc[10];
c[233] = measure anc[10];
if (c[233]) { cz x[0], anc[0]; }
if (c[233]) { x anc[10]; }
// cqrv: free anc[10]
cx anc[6], anc[0];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[7], x[0];
cx x[6], x[0];
cx x[5], x[0];
cx x[4], x[0];
cx x[3], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
h anc[9];
c[234] = measure anc[9];
if (c[234]) { cz anc[0], anc[6]; }
if (c[234]) { x anc[9]; }
// cqrv: free anc[9]
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
h anc[8];
c[235] = measure anc[8];
if (c[235]) { cz anc[4], anc[0]; }
if (c[235]) { x anc[8]; }
// cqrv: free anc[8]
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[3], anc[2];
h anc[7];
c[236] = measure anc[7];
if (c[236]) { cz anc[0], anc[2]; }
if (c[236]) { x anc[7]; }
// cqrv: free anc[7]
cx anc[3], anc[2];
cx anc[1], anc[0];
cx x[4], x[3];
cx x[5], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[6], x[0];
cx x[7], x[0];
h anc[6];
c[237] = measure anc[6];
if (c[237]) { cz x[3], x[0]; }
if (c[237]) { x anc[6]; }
// cqrv: free anc[6]
cx x[7], x[0];
cx x[6], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx x[5], x[3];
cx x[4], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[7], x[6];
h anc[5];
c[238] = measure anc[5];
if (c[238]) { cz x[0], x[6]; }
if (c[238]) { x anc[5]; }
// cqrv: free anc[5]
cx x[7], x[6];
cx x[2], x[0];
cx x[1], x[0];
h anc[4];
c[239] = measure anc[4];
if (c[239]) { cz x[6], x[7]; }
if (c[239]) { x anc[4]; }
// cqrv: free anc[4]
cx x[4], x[3];
h anc[3];
c[240] = measure anc[3];
if (c[240]) { cz x[5], x[3]; }
if (c[240]) { x anc[3]; }
// cqrv: free anc[3]
cx x[4], x[3];
h anc[2];
c[241] = measure anc[2];
if (c[241]) { cz x[3], x[4]; }
if (c[241]) { x anc[2]; }
// cqrv: free anc[2]
cx x[1], x[0];
h anc[1];
c[242] = measure anc[1];
if (c[242]) { cz x[2], x[0]; }
if (c[242]) { x anc[1]; }
// cqrv: free anc[1]
cx x[1], x[0];
h anc[0];
c[243] = measure anc[0];
if (c[243]) { cz x[0], x[1]; }
if (c[243]) { x anc[0]; }
// cqrv: free anc[0]
h x[0];
h x[1];
h x[2];
h x[3];
h x[4];
h x[5];
h x[6];
h x[7];
x x[0];
x x[1];
x x[2];
x x[3];
x x[4];
x x[5];
x x[6];
x x[7];
// cqrv: alloc anc[0]
h anc[0];
t anc[0];
cx x[0], anc[0];
cx x[1], anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
tdg x[0];
tdg x[1];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
h anc[0];
s anc[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx x[2], anc[1];
cx x[3], anc[1];
cx anc[1], x[2];
cx anc[1], x[3];
tdg x[2];
tdg x[3];
t anc[1];
cx anc[1], x[2];
cx anc[1], x[3];
h anc[1];
s anc[1];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx x[4], anc[2];
cx x[5], anc[2];
cx anc[2], x[4];
cx anc[2], x[5];
tdg x[4];
tdg x[5];
t anc[2];
cx anc[2], x[4];
cx anc[2], x[5];
h anc[2];
s anc[2];
// cqrv: alloc anc[3]
h anc[3];
t anc[3];
cx x[6], anc[3];
cx x[7], anc[3];
cx anc[3], x[6];
cx anc[3], x[7];
tdg x[6];
tdg x[7];
t anc[3];
cx anc[3], x[6];
cx anc[3], x[7];
h anc[3];
s anc[3];
// cqrv: alloc anc[4]
h anc[4];
t anc[4];
cx anc[0], anc[4];
cx anc[1], anc[4];
cx anc[4], anc[0];
cx anc[4], anc[1];
tdg anc[0];
tdg anc[1];
t anc[4];
cx anc[4], anc[0];
cx anc[4], anc[1];
h anc[4];
s anc[4];
// cqrv: alloc anc[5]
h anc[5];
t anc[5];
cx anc[2], anc[5];
cx anc[3], anc[5];
cx anc[5], anc[2];
cx anc[5], anc[3];
tdg anc[2];
tdg anc[3];
t anc[5];
cx anc[5], anc[2];
cx anc[5], anc[3];
h anc[5];
s anc[5];
// cqrv: alloc anc[6]
h anc[6];
t anc[6];
cx anc[4], anc[6];
cx anc[5], anc[6];
cx anc[6], anc[4];
cx anc[6], anc[5];
tdg anc[4];
tdg anc[5];
t anc[6];
cx anc[6], anc[4];
cx anc[6], anc[5];
h anc[6];
s anc[6];
// cqrv: alloc anc[7]
h anc[7];
t anc[7];
cx anc[6], anc[7];
cx x[11], anc[7];
cx anc[7], anc[6];
cx anc[7], x[11];
tdg anc[6];
tdg x[11];
t anc[7];
cx anc[7], anc[6];
cx anc[7], x[11];
h anc[7];
s anc[7];
z anc[7];
h anc[7];
c[244] = measure anc[7];
if (c[244]) { cz anc[6], x[11]; }
if (c[244]) { x anc[7]; }
// cqrv: free anc[7]
h anc[6];
c[245] = measure anc[6];
if (c[245]) { cz anc[4], anc[5]; }
if (c[245]) { x anc[6]; }
// cqrv: free anc[6]
h anc[5];
c[246] = measure anc[5];
if (c[246]) { cz anc[2], anc[3]; }
if (c[246]) { x anc[5]; }
// cqrv: free anc[5]
h anc[4];
c[247] = measure anc[4];
if (c[247]) { cz anc[0], anc[1]; }
if (c[247]) { x anc[4]; }
// cqrv: free anc[4]
h anc[3];
c[248] = measure anc[3];
if (c[248]) { cz x[6], x[7]; }
if (c[248]) { x anc[3]; }
// cqrv: free anc[3]
h anc[2];
c[249] = measure anc[2];
if (c[249]) { cz x[4], x[5]; }
if (c[249]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[250] = measure anc[1];
if (c[250]) { cz x[2], x[3]; }
if (c[250]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[251] = measure anc[0];
if (c[251]) { cz x[0], x[1]; }
if (c[251]) { x anc[0]; }
// cqrv: free anc[0]
x x[0];
x x[1];
x x[2];
x x[3];
x x[4];
x x[5];
x x[6];
x x[7];
h x[0];
h x[1];
h x[2];
h x[3];
h x[4];
h x[5];
h x[6];
h x[7];
z x[11];
// cqrv: alloc anc[0]
h anc[0];
t anc[0];
cx x[0], anc[0];
cx x[1], anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
tdg x[0];
tdg x[1];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
h anc[0];
s anc[0];
cx x[1], x[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx x[2], anc[1];
cx x[0], anc[1];
cx anc[1], x[2];
cx anc[1], x[0];
tdg x[2];
tdg x[0];
t anc[1];
cx anc[1], x[2];
cx anc[1], x[0];
h anc[1];
s anc[1];
cx x[1], x[0];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx x[3], anc[2];
cx x[4], anc[2];
cx anc[2], x[3];
cx anc[2], x[4];
tdg x[3];
tdg x[4];
t anc[2];
cx anc[2], x[3];
cx anc[2], x[4];
h anc[2];
s anc[2];
cx x[4], x[3];
// cqrv: alloc anc[3]
h anc[3];
t anc[3];
cx x[5], anc[3];
cx x[3], anc[3];
cx anc[3], x[5];
cx anc[3], x[3];
tdg x[5];
tdg x[3];
t anc[3];
cx anc[3], x[5];
cx anc[3], x[3];
h anc[3];
s anc[3];
cx x[4], x[3];
// cqrv: alloc anc[4]
h anc[4];
t anc[4];
cx x[6], anc[4];
cx x[7], anc[4];
cx anc[4], x[6];
cx anc[4], x[7];
tdg x[6];
tdg x[7];
t anc[4];
cx anc[4], x[6];
cx anc[4], x[7];
h anc[4];
s anc[4];
cx x[1], x[0];
cx x[2], x[0];
cx x[7], x[6];
// cqrv: alloc anc[5]
h anc[5];
t anc[5];
cx x[0], anc[5];
cx x[6], anc[5];
cx anc[5], x[0];
cx anc[5], x[6];
tdg x[0];
tdg x[6];
t anc[5];
cx anc[5], x[0];
cx anc[5], x[6];
h anc[5];
s anc[5];
cx x[7], x[6];
cx x[2], x[0];
cx x[1], x[0];
cx x[4], x[3];
cx x[5], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[6], x[0];
cx x[7], x[0];
// cqrv: alloc anc[6]
h anc[6];
t anc[6];
cx x[3], anc[6];
cx x[0], anc[6];
cx anc[6], x[3];
cx anc[6], x[0];
tdg x[3];
tdg x[0];
t anc[6];
cx anc[6], x[3];
cx anc[6], x[0];
h anc[6];
s anc[6];
cx x[7], x[0];
cx x[6], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx x[5], x[3];
cx x[4], x[3];
cx anc[1], anc[0];
cx anc[3], anc[2];
// cqrv: alloc anc[7]
h anc[7];
t anc[7];
cx anc[0], anc[7];
cx anc[2], anc[7];
cx anc[7], anc[0];
cx anc[7], anc[2];
tdg anc[0];
tdg anc[2];
t anc[7];
cx anc[7], anc[0];
cx anc[7], anc[2];
h anc[7];
s anc[7];
cx anc[3], anc[2];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
// cqrv: alloc anc[8]
h anc[8];
t anc[8];
cx anc[4], anc[8];
cx anc[0], anc[8];
cx anc[8], anc[4];
cx anc[8], anc[0];
tdg anc[4];
tdg anc[0];
t anc[8];
cx anc[8], anc[4];
cx anc[8], anc[0];
h anc[8];
s anc[8];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
// cqrv: alloc anc[9]
h anc[9];
t anc[9];
cx anc[0], anc[9];
cx anc[6], anc[9];
cx anc[9], anc[0];
cx anc[9], anc[6];
tdg anc[0];
tdg anc[6];
t anc[9];
cx anc[9], anc[0];
cx anc[9], anc[6];
h anc[9];
s anc[9];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[1], x[0];
cx x[2], x[0];
cx x[3], x[0];
cx x[4], x[0];
cx x[5], x[0];
cx x[6], x[0];
cx x[7], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
cx anc[6], anc[0];
// cqrv: alloc anc[10]
h anc[10];
t anc[10];
cx x[0], anc[10];
cx anc[0], anc[10];
cx anc[10], x[0];
cx anc[10], anc[0];
tdg x[0];
tdg anc[0];
t anc[10];
cx anc[10], x[0];
cx anc[10], anc[0];
h anc[10];
s anc[10];
cx anc[6], anc[0];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[7], x[0];
cx x[6], x[0];
cx x[5], x[0];
cx x[4], x[0];
cx x[3], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx anc[8], anc[7];
cx anc[9], anc[7];
x anc[7];
// cqrv: alloc anc[11]
h anc[11];
t anc[11];
cx anc[10], anc[11];
cx anc[7], anc[11];
cx anc[11], anc[10];
cx anc[11], anc[7];
tdg anc[10];
tdg anc[7];
t anc[11];
cx anc[11], anc[10];
cx anc[11], anc[7];
h anc[11];
s anc[11];
x anc[7];
cx anc[9], anc[7];
cx anc[8], anc[7];
// cqrv: alloc anc[12]
h anc[12];
t anc[12];
cx anc[11], anc[12];
cx x[11], anc[12];
cx anc[12], anc[11];
cx anc[12], x[11];
tdg anc[11];
tdg x[11];
t anc[12];
cx anc[12], anc[11];
cx anc[12], x[11];
h anc[12];
s anc[12];
z anc[12];
h anc[12];
c[252] = measure anc[12];
if (c[252]) { cz anc[11], x[11]; }
if (c[252]) { x anc[12]; }
// cqrv: free anc[12]
cx anc[8], anc[7];
cx anc[9], anc[7];
x anc[7];
h anc[11];
c[253] = measure anc[11];
if (c[253]) { cz anc[10], anc[7]; }
if (c[253]) { x anc[11]; }
// cqrv: free anc[11]
x anc[7];
cx anc[9], anc[7];
cx anc[8], anc[7];
cx x[1], x[0];
cx x[2], x[0];
cx x[3], x[0];
cx x[4], x[0];
cx x[5], x[0];
cx x[6], x[0];
cx x[7], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
cx anc[6], anc[0];
h anc[10];
c[254] = measure anc[10];
if (c[254]) { cz x[0], anc[0]; }
if (c[254]) { x anc[10]; }
// cqrv: free anc[10]
cx anc[6], anc[0];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[7], x[0];
cx x[6], x[0];
cx x[5], x[0];
cx x[4], x[0];
cx x[3], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
h anc[9];
c[255] = measure anc[9];
if (c[255]) { cz anc[0], anc[6]; }
if (c[255]) { x anc[9]; }
// cqrv: free anc[9]
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
h anc[8];
c[256] = measure anc[8];
if (c[256]) { cz anc[4], anc[0]; }
if (c[256]) { x anc[8]; }
// cqrv: free anc[8]
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[3], anc[2];
h anc[7];
c[257] = measure anc[7];
if (c[257]) { cz anc[0], anc[2]; }
if (c[257]) { x anc[7]; }
// cqrv: free anc[7]
cx anc[3], anc[2];
cx anc[1], anc[0];
cx x[4], x[3];
cx x[5], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[6], x[0];
cx x[7], x[0];
h anc[6];
c[258] = measure anc[6];
if (c[258]) { cz x[3], x[0]; }
if (c[258]) { x anc[6]; }
// cqrv: free anc[6]
cx x[7], x[0];
cx x[6], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx x[5], x[3];
cx x[4], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[7], x[6];
h anc[5];
c[259] = measure anc[5];
if (c[259]) { cz x[0], x[6]; }
if (c[259]) { x anc[5]; }
// cqrv: free anc[5]
cx x[7], x[6];
cx x[2], x[0];
cx x[1], x[0];
h anc[4];
c[260] = measure anc[4];
if (c[260]) { cz x[6], x[7]; }
if (c[260]) { x anc[4]; }
// cqrv: free anc[4]
cx x[4], x[3];
h anc[3];
c[261] = measure anc[3];
if (c[261]) { cz x[5], x[3]; }
if (c[261]) { x anc[3]; }
// cqrv: free anc[3]
cx x[4], x[3];
h anc[2];
c[262] = measure anc[2];
if (c[262]) { cz x[3], x[4]; }
if (c[262]) { x anc[2]; }
// cqrv: free anc[2]
cx x[1], x[0];
h anc[1];
c[263] = measure anc[1];
if (c[263]) { cz x[2], x[0]; }
if (c[263]) { x anc[1]; }
// cqrv: free anc[1]
cx x[1], x[0];
h anc[0];
c[264] = measure anc[0];
if (c[264]) { cz x[0], x[1]; }
if (c[264]) { x anc[0]; }
// cqrv: free anc[0]
h x[0];
h x[1];
h x[2];
h x[3];
h x[4];
h x[5];
h x[6];
h x[7];
x x[0];
x x[1];
x x[2];
x x[3];
x x[4];
x x[5];
x x[6];
x x[7];
// cqrv: alloc anc[0]
h anc[0];
t anc[0];
cx x[0], anc[0];
cx x[1], anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
tdg x[0];
tdg x[1];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
h anc[0];
s anc[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx x[2], anc[1];
cx x[3], anc[1];
cx anc[1], x[2];
cx anc[1], x[3];
tdg x[2];
tdg x[3];
t anc[1];
cx anc[1], x[2];
cx anc[1], x[3];
h anc[1];
s anc[1];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx x[4], anc[2];
cx x[5], anc[2];
cx anc[2], x[4];
cx anc[2], x[5];
tdg x[4];
tdg x[5];
t anc[2];
cx anc[2], x[4];
cx anc[2], x[5];
h anc[2];
s anc[2];
// cqrv: alloc anc[3]
h anc[3];
t anc[3];
cx x[6], anc[3];
cx x[7], anc[3];
cx anc[3], x[6];
cx anc[3], x[7];
tdg x[6];
tdg x[7];
t anc[3];
cx anc[3], x[6];
cx anc[3], x[7];
h anc[3];
s anc[3];
// cqrv: alloc anc[4]
h anc[4];
t anc[4];
cx anc[0], anc[4];
cx anc[1], anc[4];
cx anc[4], anc[0];
cx anc[4], anc[1];
tdg anc[0];
tdg anc[1];
t anc[4];
cx anc[4], anc[0];
cx anc[4], anc[1];
h anc[4];
s anc[4];
// cqrv: alloc anc[5]
h anc[5];
t anc[5];
cx anc[2], anc[5];
cx anc[3], anc[5];
cx anc[5], anc[2];
cx anc[5], anc[3];
tdg anc[2];
tdg anc[3];
t anc[5];
cx anc[5], anc[2];
cx anc[5], anc[3];
h anc[5];
s anc[5];
// cqrv: alloc anc[6]
h anc[6];
t anc[6];
cx anc[4], anc[6];
cx anc[5], anc[6];
cx anc[6], anc[4];
cx anc[6], anc[5];
tdg anc[4];
tdg anc[5];
t anc[6];
cx anc[6], anc[4];
cx anc[6], anc[5];
h anc[6];
s anc[6];
// cqrv: alloc anc[7]
h anc[7];
t anc[7];
cx anc[6], anc[7];
cx x[11], anc[7];
cx anc[7], anc[6];
cx anc[7], x[11];
tdg anc[6];
tdg x[11];
t anc[7];
cx anc[7], anc[6];
cx anc[7], x[11];
h anc[7];
s anc[7];
z anc[7];
h anc[7];
c[265] = measure anc[7];
if (c[265]) { cz anc[6], x[11]; }
if (c[265]) { x anc[7]; }
// cqrv: free anc[7]
h anc[6];
c[266] = measure anc[6];
if (c[266]) { cz anc[4], anc[5]; }
if (c[266]) { x anc[6]; }
// cqrv: free anc[6]
h anc[5];
c[267] = measure anc[5];
if (c[267]) { cz anc[2], anc[3]; }
if (c[267]) { x anc[5]; }
// cqrv: free anc[5]
h anc[4];
c[268] = measure anc[4];
if (c[268]) { cz anc[0], anc[1]; }
if (c[268]) { x anc[4]; }
// cqrv: free anc[4]
h anc[3];
c[269] = measure anc[3];
if (c[269]) { cz x[6], x[7]; }
if (c[269]) { x anc[3]; }
// cqrv: free anc[3]
h anc[2];
c[270] = measure anc[2];
if (c[270]) { cz x[4], x[5]; }
if (c[270]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[271] = measure anc[1];
if (c[271]) { cz x[2], x[3]; }
if (c[271]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[272] = measure anc[0];
if (c[272]) { cz x[0], x[1]; }
if (c[272]) { x anc[0]; }
// cqrv: free anc[0]
x x[0];
x x[1];
x x[2];
x x[3];
x x[4];
x x[5];
x x[6];
x x[7];
h x[0];
h x[1];
h x[2];
h x[3];
h x[4];
h x[5];
h x[6];
h x[7];
z x[11];
// cqrv: alloc anc[0]
h anc[0];
t anc[0];
cx x[0], anc[0];
cx x[1], anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
tdg x[0];
tdg x[1];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
h anc[0];
s anc[0];
cx x[1], x[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx x[2], anc[1];
cx x[0], anc[1];
cx anc[1], x[2];
cx anc[1], x[0];
tdg x[2];
tdg x[0];
t anc[1];
cx anc[1], x[2];
cx anc[1], x[0];
h anc[1];
s anc[1];
cx x[1], x[0];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx x[3], anc[2];
cx x[4], anc[2];
cx anc[2], x[3];
cx anc[2], x[4];
tdg x[3];
tdg x[4];
t anc[2];
cx anc[2], x[3];
cx anc[2], x[4];
h anc[2];
s anc[2];
cx x[4], x[3];
// cqrv: alloc anc[3]
h anc[3];
t anc[3];
cx x[5], anc[3];
cx x[3], anc[3];
cx anc[3], x[5];
cx anc[3], x[3];
tdg x[5];
tdg x[3];
t anc[3];
cx anc[3], x[5];
cx anc[3], x[3];
h anc[3];
s anc[3];
cx x[4], x[3];
// cqrv: alloc anc[4]
h anc[4];
t anc[4];
cx x[6], anc[4];
cx x[7], anc[4];
cx anc[4], x[6];
cx anc[4], x[7];
tdg x[6];
tdg x[7];
t anc[4];
cx anc[4], x[6];
cx anc[4], x[7];
h anc[4];
s anc[4];
cx x[1], x[0];
cx x[2], x[0];
cx x[7], x[6];
// cqrv: alloc anc[5]
h anc[5];
t anc[5];
cx x[0], anc[5];
cx x[6], anc[5];
cx anc[5], x[0];
cx anc[5], x[6];
tdg x[0];
tdg x[6];
t anc[5];
cx anc[5], x[0];
cx anc[5], x[6];
h anc[5];
s anc[5];
cx x[7], x[6];
cx x[2], x[0];
cx x[1], x[0];
cx x[4], x[3];
cx x[5], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[6], x[0];
cx x[7], x[0];
// cqrv: alloc anc[6]
h anc[6];
t anc[6];
cx x[3], anc[6];
cx x[0], anc[6];
cx anc[6], x[3];
cx anc[6], x[0];
tdg x[3];
tdg x[0];
t anc[6];
cx anc[6], x[3];
cx anc[6], x[0];
h anc[6];
s anc[6];
cx x[7], x[0];
cx x[6], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx x[5], x[3];
cx x[4], x[3];
cx anc[1], anc[0];
cx anc[3], anc[2];
// cqrv: alloc anc[7]
h anc[7];
t anc[7];
cx anc[0], anc[7];
cx anc[2], anc[7];
cx anc[7], anc[0];
cx anc[7], anc[2];
tdg anc[0];
tdg anc[2];
t anc[7];
cx anc[7], anc[0];
cx anc[7], anc[2];
h anc[7];
s anc[7];
cx anc[3], anc[2];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
// cqrv: alloc anc[8]
h anc[8];
t anc[8];
cx anc[4], anc[8];
cx anc[0], anc[8];
cx anc[8], anc[4];
cx anc[8], anc[0];
tdg anc[4];
tdg anc[0];
t anc[8];
cx anc[8], anc[4];
cx anc[8], anc[0];
h anc[8];
s anc[8];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
// cqrv: alloc anc[9]
h anc[9];
t anc[9];
cx anc[0], anc[9];
cx anc[6], anc[9];
cx anc[9], anc[0];
cx anc[9], anc[6];
tdg anc[0];
tdg anc[6];
t anc[9];
cx anc[9], anc[0];
cx anc[9], anc[6];
h anc[9];
s anc[9];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[1], x[0];
cx x[2], x[0];
cx x[3], x[0];
cx x[4], x[0];
cx x[5], x[0];
cx x[6], x[0];
cx x[7], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
cx anc[6], anc[0];
// cqrv: alloc anc[10]
h anc[10];
t anc[10];
cx x[0], anc[10];
cx anc[0], anc[10];
cx anc[10], x[0];
cx anc[10], anc[0];
tdg x[0];
tdg anc[0];
t anc[10];
cx anc[10], x[0];
cx anc[10], anc[0];
h anc[10];
s anc[10];
cx anc[6], anc[0];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[7], x[0];
cx x[6], x[0];
cx x[5], x[0];
cx x[4], x[0];
cx x[3], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx anc[8], anc[7];
cx anc[9], anc[7];
x anc[7];
// cqrv: alloc anc[11]
h anc[11];
t anc[11];
cx anc[10], anc[11];
cx anc[7], anc[11];
cx anc[11], anc[10];
cx anc[11], anc[7];
tdg anc[10];
tdg anc[7];
t anc[11];
cx anc[11], anc[10];
cx anc[11], anc[7];
h anc[11];
s anc[11];
x anc[7];
cx anc[9], anc[7];
cx anc[8], anc[7];
// cqrv: alloc anc[12]
h anc[12];
t anc[12];
cx anc[11], anc[12];
cx x[11], anc[12];
cx anc[12], anc[11];
cx anc[12], x[11];
tdg anc[11];
tdg x[11];
t anc[12];
cx anc[12], anc[11];
cx anc[12], x[11];
h anc[12];
s anc[12];
z anc[12];
h anc[12];
c[273] = measure anc[12];
if (c[273]) { cz anc[11], x[11]; }
if (c[273]) { x anc[12]; }
// cqrv: free anc[12]
cx anc[8], anc[7];
cx anc[9], anc[7];
x anc[7];
h anc[11];
c[274] = measure anc[11];
if (c[274]) { cz anc[10], anc[7]; }
if (c[274]) { x anc[11]; }
// cqrv: free anc[11]
x anc[7];
cx anc[9], anc[7];
cx anc[8], anc[7];
cx x[1], x[0];
cx x[2], x[0];
cx x[3], x[0];
cx x[4], x[0];
cx x[5], x[0];
cx x[6], x[0];
cx x[7], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
cx anc[6], anc[0];
h anc[10];
c[275] = measure anc[10];
if (c[275]) { cz x[0], anc[0]; }
if (c[275]) { x anc[10]; }
// cqrv: free anc[10]
cx anc[6], anc[0];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[7], x[0];
cx x[6], x[0];
cx x[5], x[0];
cx x[4], x[0];
cx x[3], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
h anc[9];
c[276] = measure anc[9];
if (c[276]) { cz anc[0], anc[6]; }
if (c[276]) { x anc[9]; }
// cqrv: free anc[9]
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
h anc[8];
c[277] = measure anc[8];
if (c[277]) { cz anc[4], anc[0]; }
if (c[277]) { x anc[8]; }
// cqrv: free anc[8]
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[3], anc[2];
h anc[7];
c[278] = measure anc[7];
if (c[278]) { cz anc[0], anc[2]; }
if (c[278]) { x anc[7]; }
// cqrv: free anc[7]
cx anc[3], anc[2];
cx anc[1], anc[0];
cx x[4], x[3];
cx x[5], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[6], x[0];
cx x[7], x[0];
h anc[6];
c[279] = measure anc[6];
if (c[279]) { cz x[3], x[0]; }
if (c[279]) { x anc[6]; }
// cqrv: free anc[6]
cx x[7], x[0];
cx x[6], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx x[5], x[3];
cx x[4], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[7], x[6];
h anc[5];
c[280] = measure anc[5];
if (c[280]) { cz x[0], x[6]; }
if (c[280]) { x anc[5]; }
// cqrv: free anc[5]
cx x[7], x[6];
cx x[2], x[0];
cx x[1], x[0];
h anc[4];
c[281] = measure anc[4];
if (c[281]) { cz x[6], x[7]; }
if (c[281]) { x anc[4]; }
// cqrv: free anc[4]
cx x[4], x[3];
h anc[3];
c[282] = measure anc[3];
if (c[282]) { cz x[5], x[3]; }
if (c[282]) { x anc[3]; }
// cqrv: free anc[3]
cx x[4], x[3];
h anc[2];
c[283] = measure anc[2];
if (c[283]) { cz x[3], x[4]; }
if (c[283]) { x anc[2]; }
// cqrv: free anc[2]
cx x[1], x[0];
h anc[1];
c[284] = measure anc[1];
if (c[284]) { cz x[2], x[0]; }
if (c[284]) { x anc[1]; }
// cqrv: free anc[1]
cx x[1], x[0];
h anc[0];
c[285] = measure anc[0];
if (c[285]) { cz x[0], x[1]; }
if (c[285]) { x anc[0]; }
// cqrv: free anc[0]
h x[0];
h x[1];
h x[2];
h x[3];
h x[4];
h x[5];
h x[6];
h x[7];
x x[0];
x x[1];
x x[2];
x x[3];
x x[4];
x x[5];
x x[6];
x x[7];
// cqrv: alloc anc[0]
h anc[0];
t anc[0];
cx x[0], anc[0];
cx x[1], anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
tdg x[0];
tdg x[1];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
h anc[0];
s anc[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx x[2], anc[1];
cx x[3], anc[1];
cx anc[1], x[2];
cx anc[1], x[3];
tdg x[2];
tdg x[3];
t anc[1];
cx anc[1], x[2];
cx anc[1], x[3];
h anc[1];
s anc[1];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx x[4], anc[2];
cx x[5], anc[2];
cx anc[2], x[4];
cx anc[2], x[5];
tdg x[4];
tdg x[5];
t anc[2];
cx anc[2], x[4];
cx anc[2], x[5];
h anc[2];
s anc[2];
// cqrv: alloc anc[3]
h anc[3];
t anc[3];
cx x[6], anc[3];
cx x[7], anc[3];
cx anc[3], x[6];
cx anc[3], x[7];
tdg x[6];
tdg x[7];
t anc[3];
cx anc[3], x[6];
cx anc[3], x[7];
h anc[3];
s anc[3];
// cqrv: alloc anc[4]
h anc[4];
t anc[4];
cx anc[0], anc[4];
cx anc[1], anc[4];
cx anc[4], anc[0];
cx anc[4], anc[1];
tdg anc[0];
tdg anc[1];
t anc[4];
cx anc[4], anc[0];
cx anc[4], anc[1];
h anc[4];
s anc[4];
// cqrv: alloc anc[5]
h anc[5];
t anc[5];
cx anc[2], anc[5];
cx anc[3], anc[5];
cx anc[5], anc[2];
cx anc[5], anc[3];
tdg anc[2];
tdg anc[3];
t anc[5];
cx anc[5], anc[2];
cx anc[5], anc[3];
h anc[5];
s anc[5];
// cqrv: alloc anc[6]
h anc[6];
t anc[6];
cx anc[4], anc[6];
cx anc[5], anc[6];
cx anc[6], anc[4];
cx anc[6], anc[5];
tdg anc[4];
tdg anc[5];
t anc[6];
cx anc[6], anc[4];
cx anc[6], anc[5];
h anc[6];
s anc[6];
// cqrv: alloc anc[7]
h anc[7];
t anc[7];
cx anc[6], anc[7];
cx x[11], anc[7];
cx anc[7], anc[6];
cx anc[7], x[11];
tdg anc[6];
tdg x[11];
t anc[7];
cx anc[7], anc[6];
cx anc[7], x[11];
h anc[7];
s anc[7];
z anc[7];
h anc[7];
c[286] = measure anc[7];
if (c[286]) { cz anc[6], x[11]; }
if (c[286]) { x anc[7]; }
// cqrv: free anc[7]
h anc[6];
c[287] = measure anc[6];
if (c[287]) { cz anc[4], anc[5]; }
if (c[287]) { x anc[6]; }
// cqrv: free anc[6]
h anc[5];
c[288] = measure anc[5];
if (c[288]) { cz anc[2], anc[3]; }
if (c[288]) { x anc[5]; }
// cqrv: free anc[5]
h anc[4];
c[289] = measure anc[4];
if (c[289]) { cz anc[0], anc[1]; }
if (c[289]) { x anc[4]; }
// cqrv: free anc[4]
h anc[3];
c[290] = measure anc[3];
if (c[290]) { cz x[6], x[7]; }
if (c[290]) { x anc[3]; }
// cqrv: free anc[3]
h anc[2];
c[291] = measure anc[2];
if (c[291]) { cz x[4], x[5]; }
if (c[291]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[292] = measure anc[1];
if (c[292]) { cz x[2], x[3]; }
if (c[292]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[293] = measure anc[0];
if (c[293]) { cz x[0], x[1]; }
if (c[293]) { x anc[0]; }
// cqrv: free anc[0]
x x[0];
x x[1];
x x[2];
x x[3];
x x[4];
x x[5];
x x[6];
x x[7];
h x[0];
h x[1];
h x[2];
h x[3];
h x[4];
h x[5];
h x[6];
h x[7];
z x[11];
// cqrv: alloc anc[0]
h anc[0];
t anc[0];
cx x[0], anc[0];
cx x[1], anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
tdg x[0];
tdg x[1];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
h anc[0];
s anc[0];
cx x[1], x[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx x[2], anc[1];
cx x[0], anc[1];
cx anc[1], x[2];
cx anc[1], x[0];
tdg x[2];
tdg x[0];
t anc[1];
cx anc[1], x[2];
cx anc[1], x[0];
h anc[1];
s anc[1];
cx x[1], x[0];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx x[3], anc[2];
cx x[4], anc[2];
cx anc[2], x[3];
cx anc[2], x[4];
tdg x[3];
tdg x[4];
t anc[2];
cx anc[2], x[3];
cx anc[2], x[4];
h anc[2];
s anc[2];
cx x[4], x[3];
// cqrv: alloc anc[3]
h anc[3];
t anc[3];
cx x[5], anc[3];
cx x[3], anc[3];
cx anc[3], x[5];
cx anc[3], x[3];
tdg x[5];
tdg x[3];
t anc[3];
cx anc[3], x[5];
cx anc[3], x[3];
h anc[3];
s anc[3];
cx x[4], x[3];
// cqrv: alloc anc[4]
h anc[4];
t anc[4];
cx x[6], anc[4];
cx x[7], anc[4];
cx anc[4], x[6];
cx anc[4], x[7];
tdg x[6];
tdg x[7];
t anc[4];
cx anc[4], x[6];
cx anc[4], x[7];
h anc[4];
s anc[4];
cx x[1], x[0];
cx x[2], x[0];
cx x[7], x[6];
// cqrv: alloc anc[5]
h anc[5];
t anc[5];
cx x[0], anc[5];
cx x[6], anc[5];
cx anc[5], x[0];
cx anc[5], x[6];
tdg x[0];
tdg x[6];
t anc[5];
cx anc[5], x[0];
cx anc[5], x[6];
h anc[5];
s anc[5];
cx x[7], x[6];
cx x[2], x[0];
cx x[1], x[0];
cx x[4], x[3];
cx x[5], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[6], x[0];
cx x[7], x[0];
// cqrv: alloc anc[6]
h anc[6];
t anc[6];
cx x[3], anc[6];
cx x[0], anc[6];
cx anc[6], x[3];
cx anc[6], x[0];
tdg x[3];
tdg x[0];
t anc[6];
cx anc[6], x[3];
cx anc[6], x[0];
h anc[6];
s anc[6];
cx x[7], x[0];
cx x[6], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx x[5], x[3];
cx x[4], x[3];
cx anc[1], anc[0];
cx anc[3], anc[2];
// cqrv: alloc anc[7]
h anc[7];
t anc[7];
cx anc[0], anc[7];
cx anc[2], anc[7];
cx anc[7], anc[0];
cx anc[7], anc[2];
tdg anc[0];
tdg anc[2];
t anc[7];
cx anc[7], anc[0];
cx anc[7], anc[2];
h anc[7];
s anc[7];
cx anc[3], anc[2];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
// cqrv: alloc anc[8]
h anc[8];
t anc[8];
cx anc[4], anc[8];
cx anc[0], anc[8];
cx anc[8], anc[4];
cx anc[8], anc[0];
tdg anc[4];
tdg anc[0];
t anc[8];
cx anc[8], anc[4];
cx anc[8], anc[0];
h anc[8];
s anc[8];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
// cqrv: alloc anc[9]
h anc[9];
t anc[9];
cx anc[0], anc[9];
cx anc[6], anc[9];
cx anc[9], anc[0];
cx anc[9], anc[6];
tdg anc[0];
tdg anc[6];
t anc[9];
cx anc[9], anc[0];
cx anc[9], anc[6];
h anc[9];
s anc[9];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[1], x[0];
cx x[2], x[0];
cx x[3], x[0];
cx x[4], x[0];
cx x[5], x[0];
cx x[6], x[0];
cx x[7], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
cx anc[6], anc[0];
// cqrv: alloc anc[10]
h anc[10];
t anc[10];
cx x[0], anc[10];
cx anc[0], anc[10];
cx anc[10], x[0];
cx anc[10], anc[0];
tdg x[0];
tdg anc[0];
t anc[10];
cx anc[10], x[0];
cx anc[10], anc[0];
h anc[10];
s anc[10];
cx anc[6], anc[0];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[7], x[0];
cx x[6], x[0];
cx x[5], x[0];
cx x[4], x[0];
cx x[3], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx anc[8], anc[7];
cx anc[9], anc[7];
x anc[7];
// cqrv: alloc anc[11]
h anc[11];
t anc[11];
cx anc[10], anc[11];
cx anc[7], anc[11];
cx anc[11], anc[10];
cx anc[11], anc[7];
tdg anc[10];
tdg anc[7];
t anc[11];
cx anc[11], anc[10];
cx anc[11], anc[7];
h anc[11];
s anc[11];
x anc[7];
cx anc[9], anc[7];
cx anc[8], anc[7];
// cqrv: alloc anc[12]
h anc[12];
t anc[12];
cx anc[11], anc[12];
cx x[11], anc[12];
cx anc[12], anc[11];
cx anc[12], x[11];
tdg anc[11];
tdg x[11];
t anc[12];
cx anc[12], anc[11];
cx anc[12], x[11];
h anc[12];
s anc[12];
z anc[12];
h anc[12];
c[294] = measure anc[12];
if (c[294]) { cz anc[11], x[11]; }
if (c[294]) { x anc[12]; }
// cqrv: free anc[12]
cx anc[8], anc[7];
cx anc[9], anc[7];
x anc[7];
h anc[11];
c[295] = measure anc[11];
if (c[295]) { cz anc[10], anc[7]; }
if (c[295]) { x anc[11]; }
// cqrv: free anc[11]
x anc[7];
cx anc[9], anc[7];
cx anc[8], anc[7];
cx x[1], x[0];
cx x[2], x[0];
cx x[3], x[0];
cx x[4], x[0];
cx x[5], x[0];
cx x[6], x[0];
cx x[7], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
cx anc[6], anc[0];
h anc[10];
c[296] = measure anc[10];
if (c[296]) { cz x[0], anc[0]; }
if (c[296]) { x anc[10]; }
// cqrv: free anc[10]
cx anc[6], anc[0];
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx x[7], x[0];
cx x[6], x[0];
cx x[5], x[0];
cx x[4], x[0];
cx x[3], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
cx anc[4], anc[0];
cx anc[5], anc[0];
h anc[9];
c[297] = measure anc[9];
if (c[297]) { cz anc[0], anc[6]; }
if (c[297]) { x anc[9]; }
// cqrv: free anc[9]
cx anc[5], anc[0];
cx anc[4], anc[0];
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[2], anc[0];
cx anc[3], anc[0];
h anc[8];
c[298] = measure anc[8];
if (c[298]) { cz anc[4], anc[0]; }
if (c[298]) { x anc[8]; }
// cqrv: free anc[8]
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[3], anc[2];
h anc[7];
c[299] = measure anc[7];
if (c[299]) { cz anc[0], anc[2]; }
if (c[299]) { x anc[7]; }
// cqrv: free anc[7]
cx anc[3], anc[2];
cx anc[1], anc[0];
cx x[4], x[3];
cx x[5], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[6], x[0];
cx x[7], x[0];
h anc[6];
c[300] = measure anc[6];
if (c[300]) { cz x[3], x[0]; }
if (c[300]) { x anc[6]; }
// cqrv: free anc[6]
cx x[7], x[0];
cx x[6], x[0];
cx x[2], x[0];
cx x[1], x[0];
cx x[5], x[3];
cx x[4], x[3];
cx x[1], x[0];
cx x[2], x[0];
cx x[7], x[6];
h anc[5];
c[301] = measure anc[5];
if (c[301]) { cz x[0], x[6]; }
if (c[301]) { x anc[5]; }
// cqrv: free anc[5]
cx x[7], x[6];
cx x[2], x[0];
cx x[1], x[0];
h anc[4];
c[302] = measure anc[4];
if (c[302]) { cz x[6], x[7]; }
if (c[302]) { x anc[4]; }
// cqrv: free anc[4]
cx x[4], x[3];
h anc[3];
c[303] = measure anc[3];
if (c[303]) { cz x[5], x[3]; }
if (c[303]) { x anc[3]; }
// cqrv: free anc[3]
cx x[4], x[3];
h anc[2];
c[304] = measure anc[2];
if (c[304]) { cz x[3], x[4]; }
if (c[304]) { x anc[2]; }
// cqrv: free anc[2]
cx x[1], x[0];
h anc[1];
c[305] = measure anc[1];
if (c[305]) { cz x[2], x[0]; }
if (c[305]) { x anc[1]; }
// cqrv: free anc[1]
cx x[1], x[0];
h anc[0];
c[306] = measure anc[0];
if (c[306]) { cz x[0], x[1]; }
if (c[306]) { x anc[0]; }
// cqrv: free anc[0]
h x[0];
h x[1];
h x[2];
h x[3];
h x[4];
h x[5];
h x[6];
h x[7];
x x[0];
x x[1];
x x[2];
x x[3];
x x[4];
x x[5];
x x[6];
x x[7];
// cqrv: alloc anc[0]
h anc[0];
t anc[0];
cx x[0], anc[0];
cx x[1], anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
tdg x[0];
tdg x[1];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[1];
h anc[0];
s anc[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx x[2], anc[1];
cx x[3], anc[1];
cx anc[1], x[2];
cx anc[1], x[3];
tdg x[2];
tdg x[3];
t anc[1];
cx anc[1], x[2];
cx anc[1], x[3];
h anc[1];
s anc[1];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx x[4], anc[2];
cx x[5], anc[2];
cx anc[2], x[4];
cx anc[2], x[5];
tdg x[4];
tdg x[5];
t anc[2];
cx anc[2], x[4];
cx anc[2], x[5];
h anc[2];
s anc[2];
// cqrv: alloc anc[3]
h anc[3];
t anc[3];
cx x[6], anc[3];
cx x[7], anc[3];
cx anc[3], x[6];
cx anc[3], x[7];
tdg x[6];
tdg x[7];
t anc[3];
cx anc[3], x[6];
cx anc[3], x[7];
h anc[3];
s anc[3];
// cqrv: alloc anc[4]
h anc[4];
t anc[4];
cx anc[0], anc[4];
cx anc[1], anc[4];
cx anc[4], anc[0];
cx anc[4], anc[1];
tdg anc[0];
tdg anc[1];
t anc[4];
cx anc[4], anc[0];
cx anc[4], anc[1];
h anc[4];
s anc[4];
// cqrv: alloc anc[5]
h anc[5];
t anc[5];
cx anc[2], anc[5];
cx anc[3], anc[5];
cx anc[5], anc[2];
cx anc[5], anc[3];
tdg anc[2];
tdg anc[3];
t anc[5];
cx anc[5], anc[2];
cx anc[5], anc[3];
h anc[5];
s anc[5];
// cqrv: alloc anc[6]
h anc[6];
t anc[6];
cx anc[4], anc[6];
cx anc[5], anc[6];
cx anc[6], anc[4];
cx anc[6], anc[5];
tdg anc[4];
tdg anc[5];
t anc[6];
cx anc[6], anc[4];
cx anc[6], anc[5];
h anc[6];
s anc[6];
// cqrv: alloc anc[7]
h anc[7];
t anc[7];
cx anc[6], anc[7];
cx x[11], anc[7];
cx anc[7], anc[6];
cx anc[7], x[11];
tdg anc[6];
tdg x[11];
t anc[7];
cx anc[7], anc[6];
cx anc[7], x[11];
h anc[7];
s anc[7];
z anc[7];
h anc[7];
c[307] = measure anc[7];
if (c[307]) { cz anc[6], x[11]; }
if (c[307]) { x anc[7]; }
// cqrv: free anc[7]
h anc[6];
c[308] = measure anc[6];
if (c[308]) { cz anc[4], anc[5]; }
if (c[308]) { x anc[6]; }
// cqrv: free anc[6]
h anc[5];
c[309] = measure anc[5];
if (c[309]) { cz anc[2], anc[3]; }
if (c[309]) { x anc[5]; }
// cqrv: free anc[5]
h anc[4];
c[310] = measure anc[4];
if (c[310]) { cz anc[0], anc[1]; }
if (c[310]) { x anc[4]; }
// cqrv: free anc[4]
h anc[3];
c[311] = measure anc[3];
if (c[311]) { cz x[6], x[7]; }
if (c[311]) { x anc[3]; }
// cqrv: free anc[3]
h anc[2];
c[312] = measure anc[2];
if (c[312]) { cz x[4], x[5]; }
if (c[312]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[313] = measure anc[1];
if (c[313]) { cz x[2], x[3]; }
if (c[313]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[314] = measure anc[0];
if (c[314]) { cz x[0], x[1]; }
if (c[314]) { x anc[0]; }
// cqrv: free anc[0]
x x[0];
x x[1];
x x[2];
x x[3];
x x[4];
x x[5];
x x[6];
x x[7];
h x[0];
h x[1];
h x[2];
h x[3];
h x[4];
h x[5];
h x[6];
h x[7];
z x[11];
h x[11];
cp(2*pi*(-1)/4) x[11], x[10];
h x[10];
cp(2*pi*(-1)/8) x[11], x[9];
cp(2*pi*(-1)/4) x[10], x[9];
h x[9];
cp(2*pi*(-1)/16) x[11], x[8];
cp(2*pi*(-1)/8) x[10], x[8];
cp(2*pi*(-1)/4) x[9], x[8];
h x[8];
out = measure x;
