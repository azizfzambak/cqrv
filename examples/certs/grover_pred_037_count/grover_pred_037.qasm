// OpenQASM 3 — grover_pred_037 (CQRV, report §8.4.3); unverified emitter (§5.3)
OPENQASM 3.0;
include "stdgates.inc";
qubit[12] x;
qubit[8] anc;
bit[165] c;
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
cx x[3], anc[0];
cx anc[0], x[0];
cx anc[0], x[3];
tdg x[0];
tdg x[3];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[3];
h anc[0];
s anc[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx anc[0], anc[1];
cx x[7], anc[1];
cx anc[1], anc[0];
cx anc[1], x[7];
tdg anc[0];
tdg x[7];
t anc[1];
cx anc[1], anc[0];
cx anc[1], x[7];
h anc[1];
s anc[1];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx anc[1], anc[2];
cx x[8], anc[2];
cx anc[2], anc[1];
cx anc[2], x[8];
tdg anc[1];
tdg x[8];
t anc[2];
cx anc[2], anc[1];
cx anc[2], x[8];
h anc[2];
s anc[2];
z anc[2];
h anc[2];
c[0] = measure anc[2];
if (c[0]) { cz anc[1], x[8]; }
if (c[0]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[1] = measure anc[1];
if (c[1]) { cz anc[0], x[7]; }
if (c[1]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[2] = measure anc[0];
if (c[2]) { cz x[0], x[3]; }
if (c[2]) { x anc[0]; }
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
c[3] = measure anc[7];
if (c[3]) { cz anc[6], x[8]; }
if (c[3]) { x anc[7]; }
// cqrv: free anc[7]
h anc[6];
c[4] = measure anc[6];
if (c[4]) { cz anc[4], anc[5]; }
if (c[4]) { x anc[6]; }
// cqrv: free anc[6]
h anc[5];
c[5] = measure anc[5];
if (c[5]) { cz anc[2], anc[3]; }
if (c[5]) { x anc[5]; }
// cqrv: free anc[5]
h anc[4];
c[6] = measure anc[4];
if (c[6]) { cz anc[0], anc[1]; }
if (c[6]) { x anc[4]; }
// cqrv: free anc[4]
h anc[3];
c[7] = measure anc[3];
if (c[7]) { cz x[6], x[7]; }
if (c[7]) { x anc[3]; }
// cqrv: free anc[3]
h anc[2];
c[8] = measure anc[2];
if (c[8]) { cz x[4], x[5]; }
if (c[8]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[9] = measure anc[1];
if (c[9]) { cz x[2], x[3]; }
if (c[9]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[10] = measure anc[0];
if (c[10]) { cz x[0], x[1]; }
if (c[10]) { x anc[0]; }
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
cx x[3], anc[0];
cx anc[0], x[0];
cx anc[0], x[3];
tdg x[0];
tdg x[3];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[3];
h anc[0];
s anc[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx anc[0], anc[1];
cx x[7], anc[1];
cx anc[1], anc[0];
cx anc[1], x[7];
tdg anc[0];
tdg x[7];
t anc[1];
cx anc[1], anc[0];
cx anc[1], x[7];
h anc[1];
s anc[1];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx anc[1], anc[2];
cx x[9], anc[2];
cx anc[2], anc[1];
cx anc[2], x[9];
tdg anc[1];
tdg x[9];
t anc[2];
cx anc[2], anc[1];
cx anc[2], x[9];
h anc[2];
s anc[2];
z anc[2];
h anc[2];
c[11] = measure anc[2];
if (c[11]) { cz anc[1], x[9]; }
if (c[11]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[12] = measure anc[1];
if (c[12]) { cz anc[0], x[7]; }
if (c[12]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[13] = measure anc[0];
if (c[13]) { cz x[0], x[3]; }
if (c[13]) { x anc[0]; }
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
c[14] = measure anc[7];
if (c[14]) { cz anc[6], x[9]; }
if (c[14]) { x anc[7]; }
// cqrv: free anc[7]
h anc[6];
c[15] = measure anc[6];
if (c[15]) { cz anc[4], anc[5]; }
if (c[15]) { x anc[6]; }
// cqrv: free anc[6]
h anc[5];
c[16] = measure anc[5];
if (c[16]) { cz anc[2], anc[3]; }
if (c[16]) { x anc[5]; }
// cqrv: free anc[5]
h anc[4];
c[17] = measure anc[4];
if (c[17]) { cz anc[0], anc[1]; }
if (c[17]) { x anc[4]; }
// cqrv: free anc[4]
h anc[3];
c[18] = measure anc[3];
if (c[18]) { cz x[6], x[7]; }
if (c[18]) { x anc[3]; }
// cqrv: free anc[3]
h anc[2];
c[19] = measure anc[2];
if (c[19]) { cz x[4], x[5]; }
if (c[19]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[20] = measure anc[1];
if (c[20]) { cz x[2], x[3]; }
if (c[20]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[21] = measure anc[0];
if (c[21]) { cz x[0], x[1]; }
if (c[21]) { x anc[0]; }
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
cx x[3], anc[0];
cx anc[0], x[0];
cx anc[0], x[3];
tdg x[0];
tdg x[3];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[3];
h anc[0];
s anc[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx anc[0], anc[1];
cx x[7], anc[1];
cx anc[1], anc[0];
cx anc[1], x[7];
tdg anc[0];
tdg x[7];
t anc[1];
cx anc[1], anc[0];
cx anc[1], x[7];
h anc[1];
s anc[1];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx anc[1], anc[2];
cx x[9], anc[2];
cx anc[2], anc[1];
cx anc[2], x[9];
tdg anc[1];
tdg x[9];
t anc[2];
cx anc[2], anc[1];
cx anc[2], x[9];
h anc[2];
s anc[2];
z anc[2];
h anc[2];
c[22] = measure anc[2];
if (c[22]) { cz anc[1], x[9]; }
if (c[22]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[23] = measure anc[1];
if (c[23]) { cz anc[0], x[7]; }
if (c[23]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[24] = measure anc[0];
if (c[24]) { cz x[0], x[3]; }
if (c[24]) { x anc[0]; }
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
c[25] = measure anc[7];
if (c[25]) { cz anc[6], x[9]; }
if (c[25]) { x anc[7]; }
// cqrv: free anc[7]
h anc[6];
c[26] = measure anc[6];
if (c[26]) { cz anc[4], anc[5]; }
if (c[26]) { x anc[6]; }
// cqrv: free anc[6]
h anc[5];
c[27] = measure anc[5];
if (c[27]) { cz anc[2], anc[3]; }
if (c[27]) { x anc[5]; }
// cqrv: free anc[5]
h anc[4];
c[28] = measure anc[4];
if (c[28]) { cz anc[0], anc[1]; }
if (c[28]) { x anc[4]; }
// cqrv: free anc[4]
h anc[3];
c[29] = measure anc[3];
if (c[29]) { cz x[6], x[7]; }
if (c[29]) { x anc[3]; }
// cqrv: free anc[3]
h anc[2];
c[30] = measure anc[2];
if (c[30]) { cz x[4], x[5]; }
if (c[30]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[31] = measure anc[1];
if (c[31]) { cz x[2], x[3]; }
if (c[31]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[32] = measure anc[0];
if (c[32]) { cz x[0], x[1]; }
if (c[32]) { x anc[0]; }
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
cx x[3], anc[0];
cx anc[0], x[0];
cx anc[0], x[3];
tdg x[0];
tdg x[3];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[3];
h anc[0];
s anc[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx anc[0], anc[1];
cx x[7], anc[1];
cx anc[1], anc[0];
cx anc[1], x[7];
tdg anc[0];
tdg x[7];
t anc[1];
cx anc[1], anc[0];
cx anc[1], x[7];
h anc[1];
s anc[1];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx anc[1], anc[2];
cx x[10], anc[2];
cx anc[2], anc[1];
cx anc[2], x[10];
tdg anc[1];
tdg x[10];
t anc[2];
cx anc[2], anc[1];
cx anc[2], x[10];
h anc[2];
s anc[2];
z anc[2];
h anc[2];
c[33] = measure anc[2];
if (c[33]) { cz anc[1], x[10]; }
if (c[33]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[34] = measure anc[1];
if (c[34]) { cz anc[0], x[7]; }
if (c[34]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[35] = measure anc[0];
if (c[35]) { cz x[0], x[3]; }
if (c[35]) { x anc[0]; }
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
c[36] = measure anc[7];
if (c[36]) { cz anc[6], x[10]; }
if (c[36]) { x anc[7]; }
// cqrv: free anc[7]
h anc[6];
c[37] = measure anc[6];
if (c[37]) { cz anc[4], anc[5]; }
if (c[37]) { x anc[6]; }
// cqrv: free anc[6]
h anc[5];
c[38] = measure anc[5];
if (c[38]) { cz anc[2], anc[3]; }
if (c[38]) { x anc[5]; }
// cqrv: free anc[5]
h anc[4];
c[39] = measure anc[4];
if (c[39]) { cz anc[0], anc[1]; }
if (c[39]) { x anc[4]; }
// cqrv: free anc[4]
h anc[3];
c[40] = measure anc[3];
if (c[40]) { cz x[6], x[7]; }
if (c[40]) { x anc[3]; }
// cqrv: free anc[3]
h anc[2];
c[41] = measure anc[2];
if (c[41]) { cz x[4], x[5]; }
if (c[41]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[42] = measure anc[1];
if (c[42]) { cz x[2], x[3]; }
if (c[42]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[43] = measure anc[0];
if (c[43]) { cz x[0], x[1]; }
if (c[43]) { x anc[0]; }
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
cx x[3], anc[0];
cx anc[0], x[0];
cx anc[0], x[3];
tdg x[0];
tdg x[3];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[3];
h anc[0];
s anc[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx anc[0], anc[1];
cx x[7], anc[1];
cx anc[1], anc[0];
cx anc[1], x[7];
tdg anc[0];
tdg x[7];
t anc[1];
cx anc[1], anc[0];
cx anc[1], x[7];
h anc[1];
s anc[1];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx anc[1], anc[2];
cx x[10], anc[2];
cx anc[2], anc[1];
cx anc[2], x[10];
tdg anc[1];
tdg x[10];
t anc[2];
cx anc[2], anc[1];
cx anc[2], x[10];
h anc[2];
s anc[2];
z anc[2];
h anc[2];
c[44] = measure anc[2];
if (c[44]) { cz anc[1], x[10]; }
if (c[44]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[45] = measure anc[1];
if (c[45]) { cz anc[0], x[7]; }
if (c[45]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[46] = measure anc[0];
if (c[46]) { cz x[0], x[3]; }
if (c[46]) { x anc[0]; }
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
c[47] = measure anc[7];
if (c[47]) { cz anc[6], x[10]; }
if (c[47]) { x anc[7]; }
// cqrv: free anc[7]
h anc[6];
c[48] = measure anc[6];
if (c[48]) { cz anc[4], anc[5]; }
if (c[48]) { x anc[6]; }
// cqrv: free anc[6]
h anc[5];
c[49] = measure anc[5];
if (c[49]) { cz anc[2], anc[3]; }
if (c[49]) { x anc[5]; }
// cqrv: free anc[5]
h anc[4];
c[50] = measure anc[4];
if (c[50]) { cz anc[0], anc[1]; }
if (c[50]) { x anc[4]; }
// cqrv: free anc[4]
h anc[3];
c[51] = measure anc[3];
if (c[51]) { cz x[6], x[7]; }
if (c[51]) { x anc[3]; }
// cqrv: free anc[3]
h anc[2];
c[52] = measure anc[2];
if (c[52]) { cz x[4], x[5]; }
if (c[52]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[53] = measure anc[1];
if (c[53]) { cz x[2], x[3]; }
if (c[53]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[54] = measure anc[0];
if (c[54]) { cz x[0], x[1]; }
if (c[54]) { x anc[0]; }
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
cx x[3], anc[0];
cx anc[0], x[0];
cx anc[0], x[3];
tdg x[0];
tdg x[3];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[3];
h anc[0];
s anc[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx anc[0], anc[1];
cx x[7], anc[1];
cx anc[1], anc[0];
cx anc[1], x[7];
tdg anc[0];
tdg x[7];
t anc[1];
cx anc[1], anc[0];
cx anc[1], x[7];
h anc[1];
s anc[1];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx anc[1], anc[2];
cx x[10], anc[2];
cx anc[2], anc[1];
cx anc[2], x[10];
tdg anc[1];
tdg x[10];
t anc[2];
cx anc[2], anc[1];
cx anc[2], x[10];
h anc[2];
s anc[2];
z anc[2];
h anc[2];
c[55] = measure anc[2];
if (c[55]) { cz anc[1], x[10]; }
if (c[55]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[56] = measure anc[1];
if (c[56]) { cz anc[0], x[7]; }
if (c[56]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[57] = measure anc[0];
if (c[57]) { cz x[0], x[3]; }
if (c[57]) { x anc[0]; }
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
c[58] = measure anc[7];
if (c[58]) { cz anc[6], x[10]; }
if (c[58]) { x anc[7]; }
// cqrv: free anc[7]
h anc[6];
c[59] = measure anc[6];
if (c[59]) { cz anc[4], anc[5]; }
if (c[59]) { x anc[6]; }
// cqrv: free anc[6]
h anc[5];
c[60] = measure anc[5];
if (c[60]) { cz anc[2], anc[3]; }
if (c[60]) { x anc[5]; }
// cqrv: free anc[5]
h anc[4];
c[61] = measure anc[4];
if (c[61]) { cz anc[0], anc[1]; }
if (c[61]) { x anc[4]; }
// cqrv: free anc[4]
h anc[3];
c[62] = measure anc[3];
if (c[62]) { cz x[6], x[7]; }
if (c[62]) { x anc[3]; }
// cqrv: free anc[3]
h anc[2];
c[63] = measure anc[2];
if (c[63]) { cz x[4], x[5]; }
if (c[63]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[64] = measure anc[1];
if (c[64]) { cz x[2], x[3]; }
if (c[64]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[65] = measure anc[0];
if (c[65]) { cz x[0], x[1]; }
if (c[65]) { x anc[0]; }
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
cx x[3], anc[0];
cx anc[0], x[0];
cx anc[0], x[3];
tdg x[0];
tdg x[3];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[3];
h anc[0];
s anc[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx anc[0], anc[1];
cx x[7], anc[1];
cx anc[1], anc[0];
cx anc[1], x[7];
tdg anc[0];
tdg x[7];
t anc[1];
cx anc[1], anc[0];
cx anc[1], x[7];
h anc[1];
s anc[1];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx anc[1], anc[2];
cx x[10], anc[2];
cx anc[2], anc[1];
cx anc[2], x[10];
tdg anc[1];
tdg x[10];
t anc[2];
cx anc[2], anc[1];
cx anc[2], x[10];
h anc[2];
s anc[2];
z anc[2];
h anc[2];
c[66] = measure anc[2];
if (c[66]) { cz anc[1], x[10]; }
if (c[66]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[67] = measure anc[1];
if (c[67]) { cz anc[0], x[7]; }
if (c[67]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[68] = measure anc[0];
if (c[68]) { cz x[0], x[3]; }
if (c[68]) { x anc[0]; }
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
c[69] = measure anc[7];
if (c[69]) { cz anc[6], x[10]; }
if (c[69]) { x anc[7]; }
// cqrv: free anc[7]
h anc[6];
c[70] = measure anc[6];
if (c[70]) { cz anc[4], anc[5]; }
if (c[70]) { x anc[6]; }
// cqrv: free anc[6]
h anc[5];
c[71] = measure anc[5];
if (c[71]) { cz anc[2], anc[3]; }
if (c[71]) { x anc[5]; }
// cqrv: free anc[5]
h anc[4];
c[72] = measure anc[4];
if (c[72]) { cz anc[0], anc[1]; }
if (c[72]) { x anc[4]; }
// cqrv: free anc[4]
h anc[3];
c[73] = measure anc[3];
if (c[73]) { cz x[6], x[7]; }
if (c[73]) { x anc[3]; }
// cqrv: free anc[3]
h anc[2];
c[74] = measure anc[2];
if (c[74]) { cz x[4], x[5]; }
if (c[74]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[75] = measure anc[1];
if (c[75]) { cz x[2], x[3]; }
if (c[75]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[76] = measure anc[0];
if (c[76]) { cz x[0], x[1]; }
if (c[76]) { x anc[0]; }
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
cx x[3], anc[0];
cx anc[0], x[0];
cx anc[0], x[3];
tdg x[0];
tdg x[3];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[3];
h anc[0];
s anc[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx anc[0], anc[1];
cx x[7], anc[1];
cx anc[1], anc[0];
cx anc[1], x[7];
tdg anc[0];
tdg x[7];
t anc[1];
cx anc[1], anc[0];
cx anc[1], x[7];
h anc[1];
s anc[1];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx anc[1], anc[2];
cx x[11], anc[2];
cx anc[2], anc[1];
cx anc[2], x[11];
tdg anc[1];
tdg x[11];
t anc[2];
cx anc[2], anc[1];
cx anc[2], x[11];
h anc[2];
s anc[2];
z anc[2];
h anc[2];
c[77] = measure anc[2];
if (c[77]) { cz anc[1], x[11]; }
if (c[77]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[78] = measure anc[1];
if (c[78]) { cz anc[0], x[7]; }
if (c[78]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[79] = measure anc[0];
if (c[79]) { cz x[0], x[3]; }
if (c[79]) { x anc[0]; }
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
c[80] = measure anc[7];
if (c[80]) { cz anc[6], x[11]; }
if (c[80]) { x anc[7]; }
// cqrv: free anc[7]
h anc[6];
c[81] = measure anc[6];
if (c[81]) { cz anc[4], anc[5]; }
if (c[81]) { x anc[6]; }
// cqrv: free anc[6]
h anc[5];
c[82] = measure anc[5];
if (c[82]) { cz anc[2], anc[3]; }
if (c[82]) { x anc[5]; }
// cqrv: free anc[5]
h anc[4];
c[83] = measure anc[4];
if (c[83]) { cz anc[0], anc[1]; }
if (c[83]) { x anc[4]; }
// cqrv: free anc[4]
h anc[3];
c[84] = measure anc[3];
if (c[84]) { cz x[6], x[7]; }
if (c[84]) { x anc[3]; }
// cqrv: free anc[3]
h anc[2];
c[85] = measure anc[2];
if (c[85]) { cz x[4], x[5]; }
if (c[85]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[86] = measure anc[1];
if (c[86]) { cz x[2], x[3]; }
if (c[86]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[87] = measure anc[0];
if (c[87]) { cz x[0], x[1]; }
if (c[87]) { x anc[0]; }
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
cx x[3], anc[0];
cx anc[0], x[0];
cx anc[0], x[3];
tdg x[0];
tdg x[3];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[3];
h anc[0];
s anc[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx anc[0], anc[1];
cx x[7], anc[1];
cx anc[1], anc[0];
cx anc[1], x[7];
tdg anc[0];
tdg x[7];
t anc[1];
cx anc[1], anc[0];
cx anc[1], x[7];
h anc[1];
s anc[1];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx anc[1], anc[2];
cx x[11], anc[2];
cx anc[2], anc[1];
cx anc[2], x[11];
tdg anc[1];
tdg x[11];
t anc[2];
cx anc[2], anc[1];
cx anc[2], x[11];
h anc[2];
s anc[2];
z anc[2];
h anc[2];
c[88] = measure anc[2];
if (c[88]) { cz anc[1], x[11]; }
if (c[88]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[89] = measure anc[1];
if (c[89]) { cz anc[0], x[7]; }
if (c[89]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[90] = measure anc[0];
if (c[90]) { cz x[0], x[3]; }
if (c[90]) { x anc[0]; }
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
c[91] = measure anc[7];
if (c[91]) { cz anc[6], x[11]; }
if (c[91]) { x anc[7]; }
// cqrv: free anc[7]
h anc[6];
c[92] = measure anc[6];
if (c[92]) { cz anc[4], anc[5]; }
if (c[92]) { x anc[6]; }
// cqrv: free anc[6]
h anc[5];
c[93] = measure anc[5];
if (c[93]) { cz anc[2], anc[3]; }
if (c[93]) { x anc[5]; }
// cqrv: free anc[5]
h anc[4];
c[94] = measure anc[4];
if (c[94]) { cz anc[0], anc[1]; }
if (c[94]) { x anc[4]; }
// cqrv: free anc[4]
h anc[3];
c[95] = measure anc[3];
if (c[95]) { cz x[6], x[7]; }
if (c[95]) { x anc[3]; }
// cqrv: free anc[3]
h anc[2];
c[96] = measure anc[2];
if (c[96]) { cz x[4], x[5]; }
if (c[96]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[97] = measure anc[1];
if (c[97]) { cz x[2], x[3]; }
if (c[97]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[98] = measure anc[0];
if (c[98]) { cz x[0], x[1]; }
if (c[98]) { x anc[0]; }
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
cx x[3], anc[0];
cx anc[0], x[0];
cx anc[0], x[3];
tdg x[0];
tdg x[3];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[3];
h anc[0];
s anc[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx anc[0], anc[1];
cx x[7], anc[1];
cx anc[1], anc[0];
cx anc[1], x[7];
tdg anc[0];
tdg x[7];
t anc[1];
cx anc[1], anc[0];
cx anc[1], x[7];
h anc[1];
s anc[1];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx anc[1], anc[2];
cx x[11], anc[2];
cx anc[2], anc[1];
cx anc[2], x[11];
tdg anc[1];
tdg x[11];
t anc[2];
cx anc[2], anc[1];
cx anc[2], x[11];
h anc[2];
s anc[2];
z anc[2];
h anc[2];
c[99] = measure anc[2];
if (c[99]) { cz anc[1], x[11]; }
if (c[99]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[100] = measure anc[1];
if (c[100]) { cz anc[0], x[7]; }
if (c[100]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[101] = measure anc[0];
if (c[101]) { cz x[0], x[3]; }
if (c[101]) { x anc[0]; }
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
c[102] = measure anc[7];
if (c[102]) { cz anc[6], x[11]; }
if (c[102]) { x anc[7]; }
// cqrv: free anc[7]
h anc[6];
c[103] = measure anc[6];
if (c[103]) { cz anc[4], anc[5]; }
if (c[103]) { x anc[6]; }
// cqrv: free anc[6]
h anc[5];
c[104] = measure anc[5];
if (c[104]) { cz anc[2], anc[3]; }
if (c[104]) { x anc[5]; }
// cqrv: free anc[5]
h anc[4];
c[105] = measure anc[4];
if (c[105]) { cz anc[0], anc[1]; }
if (c[105]) { x anc[4]; }
// cqrv: free anc[4]
h anc[3];
c[106] = measure anc[3];
if (c[106]) { cz x[6], x[7]; }
if (c[106]) { x anc[3]; }
// cqrv: free anc[3]
h anc[2];
c[107] = measure anc[2];
if (c[107]) { cz x[4], x[5]; }
if (c[107]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[108] = measure anc[1];
if (c[108]) { cz x[2], x[3]; }
if (c[108]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[109] = measure anc[0];
if (c[109]) { cz x[0], x[1]; }
if (c[109]) { x anc[0]; }
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
cx x[3], anc[0];
cx anc[0], x[0];
cx anc[0], x[3];
tdg x[0];
tdg x[3];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[3];
h anc[0];
s anc[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx anc[0], anc[1];
cx x[7], anc[1];
cx anc[1], anc[0];
cx anc[1], x[7];
tdg anc[0];
tdg x[7];
t anc[1];
cx anc[1], anc[0];
cx anc[1], x[7];
h anc[1];
s anc[1];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx anc[1], anc[2];
cx x[11], anc[2];
cx anc[2], anc[1];
cx anc[2], x[11];
tdg anc[1];
tdg x[11];
t anc[2];
cx anc[2], anc[1];
cx anc[2], x[11];
h anc[2];
s anc[2];
z anc[2];
h anc[2];
c[110] = measure anc[2];
if (c[110]) { cz anc[1], x[11]; }
if (c[110]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[111] = measure anc[1];
if (c[111]) { cz anc[0], x[7]; }
if (c[111]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[112] = measure anc[0];
if (c[112]) { cz x[0], x[3]; }
if (c[112]) { x anc[0]; }
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
c[113] = measure anc[7];
if (c[113]) { cz anc[6], x[11]; }
if (c[113]) { x anc[7]; }
// cqrv: free anc[7]
h anc[6];
c[114] = measure anc[6];
if (c[114]) { cz anc[4], anc[5]; }
if (c[114]) { x anc[6]; }
// cqrv: free anc[6]
h anc[5];
c[115] = measure anc[5];
if (c[115]) { cz anc[2], anc[3]; }
if (c[115]) { x anc[5]; }
// cqrv: free anc[5]
h anc[4];
c[116] = measure anc[4];
if (c[116]) { cz anc[0], anc[1]; }
if (c[116]) { x anc[4]; }
// cqrv: free anc[4]
h anc[3];
c[117] = measure anc[3];
if (c[117]) { cz x[6], x[7]; }
if (c[117]) { x anc[3]; }
// cqrv: free anc[3]
h anc[2];
c[118] = measure anc[2];
if (c[118]) { cz x[4], x[5]; }
if (c[118]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[119] = measure anc[1];
if (c[119]) { cz x[2], x[3]; }
if (c[119]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[120] = measure anc[0];
if (c[120]) { cz x[0], x[1]; }
if (c[120]) { x anc[0]; }
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
cx x[3], anc[0];
cx anc[0], x[0];
cx anc[0], x[3];
tdg x[0];
tdg x[3];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[3];
h anc[0];
s anc[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx anc[0], anc[1];
cx x[7], anc[1];
cx anc[1], anc[0];
cx anc[1], x[7];
tdg anc[0];
tdg x[7];
t anc[1];
cx anc[1], anc[0];
cx anc[1], x[7];
h anc[1];
s anc[1];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx anc[1], anc[2];
cx x[11], anc[2];
cx anc[2], anc[1];
cx anc[2], x[11];
tdg anc[1];
tdg x[11];
t anc[2];
cx anc[2], anc[1];
cx anc[2], x[11];
h anc[2];
s anc[2];
z anc[2];
h anc[2];
c[121] = measure anc[2];
if (c[121]) { cz anc[1], x[11]; }
if (c[121]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[122] = measure anc[1];
if (c[122]) { cz anc[0], x[7]; }
if (c[122]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[123] = measure anc[0];
if (c[123]) { cz x[0], x[3]; }
if (c[123]) { x anc[0]; }
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
c[124] = measure anc[7];
if (c[124]) { cz anc[6], x[11]; }
if (c[124]) { x anc[7]; }
// cqrv: free anc[7]
h anc[6];
c[125] = measure anc[6];
if (c[125]) { cz anc[4], anc[5]; }
if (c[125]) { x anc[6]; }
// cqrv: free anc[6]
h anc[5];
c[126] = measure anc[5];
if (c[126]) { cz anc[2], anc[3]; }
if (c[126]) { x anc[5]; }
// cqrv: free anc[5]
h anc[4];
c[127] = measure anc[4];
if (c[127]) { cz anc[0], anc[1]; }
if (c[127]) { x anc[4]; }
// cqrv: free anc[4]
h anc[3];
c[128] = measure anc[3];
if (c[128]) { cz x[6], x[7]; }
if (c[128]) { x anc[3]; }
// cqrv: free anc[3]
h anc[2];
c[129] = measure anc[2];
if (c[129]) { cz x[4], x[5]; }
if (c[129]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[130] = measure anc[1];
if (c[130]) { cz x[2], x[3]; }
if (c[130]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[131] = measure anc[0];
if (c[131]) { cz x[0], x[1]; }
if (c[131]) { x anc[0]; }
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
cx x[3], anc[0];
cx anc[0], x[0];
cx anc[0], x[3];
tdg x[0];
tdg x[3];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[3];
h anc[0];
s anc[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx anc[0], anc[1];
cx x[7], anc[1];
cx anc[1], anc[0];
cx anc[1], x[7];
tdg anc[0];
tdg x[7];
t anc[1];
cx anc[1], anc[0];
cx anc[1], x[7];
h anc[1];
s anc[1];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx anc[1], anc[2];
cx x[11], anc[2];
cx anc[2], anc[1];
cx anc[2], x[11];
tdg anc[1];
tdg x[11];
t anc[2];
cx anc[2], anc[1];
cx anc[2], x[11];
h anc[2];
s anc[2];
z anc[2];
h anc[2];
c[132] = measure anc[2];
if (c[132]) { cz anc[1], x[11]; }
if (c[132]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[133] = measure anc[1];
if (c[133]) { cz anc[0], x[7]; }
if (c[133]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[134] = measure anc[0];
if (c[134]) { cz x[0], x[3]; }
if (c[134]) { x anc[0]; }
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
c[135] = measure anc[7];
if (c[135]) { cz anc[6], x[11]; }
if (c[135]) { x anc[7]; }
// cqrv: free anc[7]
h anc[6];
c[136] = measure anc[6];
if (c[136]) { cz anc[4], anc[5]; }
if (c[136]) { x anc[6]; }
// cqrv: free anc[6]
h anc[5];
c[137] = measure anc[5];
if (c[137]) { cz anc[2], anc[3]; }
if (c[137]) { x anc[5]; }
// cqrv: free anc[5]
h anc[4];
c[138] = measure anc[4];
if (c[138]) { cz anc[0], anc[1]; }
if (c[138]) { x anc[4]; }
// cqrv: free anc[4]
h anc[3];
c[139] = measure anc[3];
if (c[139]) { cz x[6], x[7]; }
if (c[139]) { x anc[3]; }
// cqrv: free anc[3]
h anc[2];
c[140] = measure anc[2];
if (c[140]) { cz x[4], x[5]; }
if (c[140]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[141] = measure anc[1];
if (c[141]) { cz x[2], x[3]; }
if (c[141]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[142] = measure anc[0];
if (c[142]) { cz x[0], x[1]; }
if (c[142]) { x anc[0]; }
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
cx x[3], anc[0];
cx anc[0], x[0];
cx anc[0], x[3];
tdg x[0];
tdg x[3];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[3];
h anc[0];
s anc[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx anc[0], anc[1];
cx x[7], anc[1];
cx anc[1], anc[0];
cx anc[1], x[7];
tdg anc[0];
tdg x[7];
t anc[1];
cx anc[1], anc[0];
cx anc[1], x[7];
h anc[1];
s anc[1];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx anc[1], anc[2];
cx x[11], anc[2];
cx anc[2], anc[1];
cx anc[2], x[11];
tdg anc[1];
tdg x[11];
t anc[2];
cx anc[2], anc[1];
cx anc[2], x[11];
h anc[2];
s anc[2];
z anc[2];
h anc[2];
c[143] = measure anc[2];
if (c[143]) { cz anc[1], x[11]; }
if (c[143]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[144] = measure anc[1];
if (c[144]) { cz anc[0], x[7]; }
if (c[144]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[145] = measure anc[0];
if (c[145]) { cz x[0], x[3]; }
if (c[145]) { x anc[0]; }
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
c[146] = measure anc[7];
if (c[146]) { cz anc[6], x[11]; }
if (c[146]) { x anc[7]; }
// cqrv: free anc[7]
h anc[6];
c[147] = measure anc[6];
if (c[147]) { cz anc[4], anc[5]; }
if (c[147]) { x anc[6]; }
// cqrv: free anc[6]
h anc[5];
c[148] = measure anc[5];
if (c[148]) { cz anc[2], anc[3]; }
if (c[148]) { x anc[5]; }
// cqrv: free anc[5]
h anc[4];
c[149] = measure anc[4];
if (c[149]) { cz anc[0], anc[1]; }
if (c[149]) { x anc[4]; }
// cqrv: free anc[4]
h anc[3];
c[150] = measure anc[3];
if (c[150]) { cz x[6], x[7]; }
if (c[150]) { x anc[3]; }
// cqrv: free anc[3]
h anc[2];
c[151] = measure anc[2];
if (c[151]) { cz x[4], x[5]; }
if (c[151]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[152] = measure anc[1];
if (c[152]) { cz x[2], x[3]; }
if (c[152]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[153] = measure anc[0];
if (c[153]) { cz x[0], x[1]; }
if (c[153]) { x anc[0]; }
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
cx x[3], anc[0];
cx anc[0], x[0];
cx anc[0], x[3];
tdg x[0];
tdg x[3];
t anc[0];
cx anc[0], x[0];
cx anc[0], x[3];
h anc[0];
s anc[0];
// cqrv: alloc anc[1]
h anc[1];
t anc[1];
cx anc[0], anc[1];
cx x[7], anc[1];
cx anc[1], anc[0];
cx anc[1], x[7];
tdg anc[0];
tdg x[7];
t anc[1];
cx anc[1], anc[0];
cx anc[1], x[7];
h anc[1];
s anc[1];
// cqrv: alloc anc[2]
h anc[2];
t anc[2];
cx anc[1], anc[2];
cx x[11], anc[2];
cx anc[2], anc[1];
cx anc[2], x[11];
tdg anc[1];
tdg x[11];
t anc[2];
cx anc[2], anc[1];
cx anc[2], x[11];
h anc[2];
s anc[2];
z anc[2];
h anc[2];
c[154] = measure anc[2];
if (c[154]) { cz anc[1], x[11]; }
if (c[154]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[155] = measure anc[1];
if (c[155]) { cz anc[0], x[7]; }
if (c[155]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[156] = measure anc[0];
if (c[156]) { cz x[0], x[3]; }
if (c[156]) { x anc[0]; }
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
c[157] = measure anc[7];
if (c[157]) { cz anc[6], x[11]; }
if (c[157]) { x anc[7]; }
// cqrv: free anc[7]
h anc[6];
c[158] = measure anc[6];
if (c[158]) { cz anc[4], anc[5]; }
if (c[158]) { x anc[6]; }
// cqrv: free anc[6]
h anc[5];
c[159] = measure anc[5];
if (c[159]) { cz anc[2], anc[3]; }
if (c[159]) { x anc[5]; }
// cqrv: free anc[5]
h anc[4];
c[160] = measure anc[4];
if (c[160]) { cz anc[0], anc[1]; }
if (c[160]) { x anc[4]; }
// cqrv: free anc[4]
h anc[3];
c[161] = measure anc[3];
if (c[161]) { cz x[6], x[7]; }
if (c[161]) { x anc[3]; }
// cqrv: free anc[3]
h anc[2];
c[162] = measure anc[2];
if (c[162]) { cz x[4], x[5]; }
if (c[162]) { x anc[2]; }
// cqrv: free anc[2]
h anc[1];
c[163] = measure anc[1];
if (c[163]) { cz x[2], x[3]; }
if (c[163]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[164] = measure anc[0];
if (c[164]) { cz x[0], x[1]; }
if (c[164]) { x anc[0]; }
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
