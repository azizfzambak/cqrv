// OpenQASM 3 — fr_n3 (CQRV, report §8.4.3); unverified emitter (§5.3)
OPENQASM 3.0;
include "stdgates.inc";
qubit[3] x;
qubit[2] anc;
bit[6] c;
bit[3] out;
h x[0];
h x[1];
h x[2];
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
cx anc[0], anc[1];
cx x[2], anc[1];
cx anc[1], anc[0];
cx anc[1], x[2];
tdg anc[0];
tdg x[2];
t anc[1];
cx anc[1], anc[0];
cx anc[1], x[2];
h anc[1];
s anc[1];
z anc[1];
h anc[1];
c[0] = measure anc[1];
if (c[0]) { cz anc[0], x[2]; }
if (c[0]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[1] = measure anc[0];
if (c[1]) { cz x[0], x[1]; }
if (c[1]) { x anc[0]; }
// cqrv: free anc[0]
h x[0];
h x[1];
h x[2];
x x[0];
x x[1];
x x[2];
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
cz anc[0], x[2];
h anc[0];
c[2] = measure anc[0];
if (c[2]) { cz x[0], x[1]; }
if (c[2]) { x anc[0]; }
// cqrv: free anc[0]
x x[0];
x x[1];
x x[2];
h x[0];
h x[1];
h x[2];
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
cx anc[0], anc[1];
cx x[2], anc[1];
cx anc[1], anc[0];
cx anc[1], x[2];
tdg anc[0];
tdg x[2];
t anc[1];
cx anc[1], anc[0];
cx anc[1], x[2];
h anc[1];
s anc[1];
z anc[1];
h anc[1];
c[3] = measure anc[1];
if (c[3]) { cz anc[0], x[2]; }
if (c[3]) { x anc[1]; }
// cqrv: free anc[1]
h anc[0];
c[4] = measure anc[0];
if (c[4]) { cz x[0], x[1]; }
if (c[4]) { x anc[0]; }
// cqrv: free anc[0]
h x[0];
h x[1];
h x[2];
x x[0];
x x[1];
x x[2];
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
cz anc[0], x[2];
h anc[0];
c[5] = measure anc[0];
if (c[5]) { cz x[0], x[1]; }
if (c[5]) { x anc[0]; }
// cqrv: free anc[0]
x x[0];
x x[1];
x x[2];
h x[0];
h x[1];
h x[2];
out = measure x;
