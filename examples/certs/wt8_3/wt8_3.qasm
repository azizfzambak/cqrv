// OpenQASM 3 — wt8_3 (CQRV, report §8.4.3); unverified emitter (§5.3)
OPENQASM 3.0;
include "stdgates.inc";
qubit[8] x;
qubit[12] anc;
bit[19] c;
bit[8] out;
h x[0];
h x[1];
h x[2];
h x[3];
h x[4];
h x[5];
h x[6];
h x[7];
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
z anc[11];
cx anc[8], anc[7];
cx anc[9], anc[7];
x anc[7];
h anc[11];
c[0] = measure anc[11];
if (c[0]) { cz anc[10], anc[7]; }
if (c[0]) { x anc[11]; }
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
c[1] = measure anc[10];
if (c[1]) { cz x[0], anc[0]; }
if (c[1]) { x anc[10]; }
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
c[2] = measure anc[9];
if (c[2]) { cz anc[0], anc[6]; }
if (c[2]) { x anc[9]; }
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
c[3] = measure anc[8];
if (c[3]) { cz anc[4], anc[0]; }
if (c[3]) { x anc[8]; }
// cqrv: free anc[8]
cx anc[3], anc[0];
cx anc[2], anc[0];
cx anc[1], anc[0];
cx anc[5], anc[4];
cx anc[1], anc[0];
cx anc[3], anc[2];
h anc[7];
c[4] = measure anc[7];
if (c[4]) { cz anc[0], anc[2]; }
if (c[4]) { x anc[7]; }
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
c[5] = measure anc[6];
if (c[5]) { cz x[3], x[0]; }
if (c[5]) { x anc[6]; }
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
c[6] = measure anc[5];
if (c[6]) { cz x[0], x[6]; }
if (c[6]) { x anc[5]; }
// cqrv: free anc[5]
cx x[7], x[6];
cx x[2], x[0];
cx x[1], x[0];
h anc[4];
c[7] = measure anc[4];
if (c[7]) { cz x[6], x[7]; }
if (c[7]) { x anc[4]; }
// cqrv: free anc[4]
cx x[4], x[3];
h anc[3];
c[8] = measure anc[3];
if (c[8]) { cz x[5], x[3]; }
if (c[8]) { x anc[3]; }
// cqrv: free anc[3]
cx x[4], x[3];
h anc[2];
c[9] = measure anc[2];
if (c[9]) { cz x[3], x[4]; }
if (c[9]) { x anc[2]; }
// cqrv: free anc[2]
cx x[1], x[0];
h anc[1];
c[10] = measure anc[1];
if (c[10]) { cz x[2], x[0]; }
if (c[10]) { x anc[1]; }
// cqrv: free anc[1]
cx x[1], x[0];
h anc[0];
c[11] = measure anc[0];
if (c[11]) { cz x[0], x[1]; }
if (c[11]) { x anc[0]; }
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
z anc[6];
h anc[6];
c[12] = measure anc[6];
if (c[12]) { cz anc[4], anc[5]; }
if (c[12]) { x anc[6]; }
// cqrv: free anc[6]
h anc[5];
c[13] = measure anc[5];
if (c[13]) { cz anc[2], anc[3]; }
if (c[13]) { x anc[5]; }
// cqrv: free anc[5]
h anc[4];
c[14] = measure anc[4];
if (c[14]) { cz anc[0], anc[1]; }
if (c[14]) { x anc[4]; }
// cqrv: free anc[4]
h anc[3];
c[15] = measure anc[3];
if (c[15]) { cz x[6], x[7]; }
if (c[15]) { x anc[3]; }
// cqrv: free anc[3]
h anc[2];
c[16] = measure anc[2];
if (c[16]) { cz x[4], x[5]; }
if (c[16]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[17] = measure anc[1];
if (c[17]) { cz x[2], x[3]; }
if (c[17]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[18] = measure anc[0];
if (c[18]) { cz x[0], x[1]; }
if (c[18]) { x anc[0]; }
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
out = measure x;
