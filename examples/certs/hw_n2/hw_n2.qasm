// OpenQASM 3 — hw_n2 (CQRV, report §8.4.3); unverified emitter (§5.3)
OPENQASM 3.0;
include "stdgates.inc";
qubit[2] x;
qubit[1] anc;
bit[2] c;
bit[2] out;
h x[0];
h x[1];
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
z anc[0];
h anc[0];
c[0] = measure anc[0];
if (c[0]) { cz x[0], x[1]; }
if (c[0]) { x anc[0]; }
// cqrv: free anc[0]
h x[0];
h x[1];
x x[0];
x x[1];
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
z anc[0];
h anc[0];
c[1] = measure anc[0];
if (c[1]) { cz x[0], x[1]; }
if (c[1]) { x anc[0]; }
// cqrv: free anc[0]
x x[0];
x x[1];
h x[0];
h x[1];
out = measure x;
