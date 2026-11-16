OPENQASM 3.0;
include "stdgates.inc";
bit[6] c;
qubit[133] q;
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
rz(pi*1/2) q[42];
sx q[42];
rz(pi*1/2) q[42];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
rz(pi*1/4) q[43];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
rz(pi*1/4) q[44];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
cz q[45], q[44];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
cz q[35], q[44];
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
cz q[44], q[45];
cz q[44], q[35];
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
rz(pi*-1/4) q[35];
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
rz(pi*1/4) q[44];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
rz(pi*-1/4) q[45];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
cz q[44], q[45];
cz q[44], q[35];
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
rz(pi*1/2) q[44];
cz q[44], q[43];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
cz q[42], q[43];
rz(pi*1/2) q[42];
sx q[42];
rz(pi*1/2) q[42];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
cz q[43], q[44];
cz q[43], q[42];
rz(pi*1/2) q[42];
sx q[42];
rz(pi*1/2) q[42];
rz(pi*-1/4) q[42];
rz(pi*1/2) q[42];
sx q[42];
rz(pi*1/2) q[42];
rz(pi*1/4) q[43];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
rz(pi*-1/4) q[44];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
cz q[43], q[44];
cz q[43], q[42];
rz(pi*1/2) q[42];
sx q[42];
rz(pi*1/2) q[42];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
rz(pi*1/2) q[43];
rz(pi*1) q[43];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
c[0] = measure q[43];
if (c[0]) {
  rz(pi*1/2) q[42];
}
if (c[0]) {
  sx q[42];
}
if (c[0]) {
  rz(pi*1/2) q[42];
}
if (c[0]) {
  cz q[43], q[42];
}
if (c[0]) {
  rz(pi*1/2) q[42];
}
if (c[0]) {
  sx q[42];
}
if (c[0]) {
  rz(pi*1/2) q[42];
}
if (c[0]) {
  rz(pi*1/2) q[43];
}
if (c[0]) {
  sx q[43];
}
if (c[0]) {
  rz(pi*1/2) q[43];
}
if (c[0]) {
  cz q[42], q[43];
}
if (c[0]) {
  rz(pi*1/2) q[43];
}
if (c[0]) {
  sx q[43];
}
if (c[0]) {
  rz(pi*1/2) q[43];
}
if (c[0]) {
  rz(pi*1/2) q[42];
}
if (c[0]) {
  sx q[42];
}
if (c[0]) {
  rz(pi*1/2) q[42];
}
if (c[0]) {
  cz q[43], q[42];
}
if (c[0]) {
  rz(pi*1/2) q[42];
}
if (c[0]) {
  sx q[42];
}
if (c[0]) {
  rz(pi*1/2) q[42];
}
if (c[0]) {
  cz q[44], q[43];
}
if (c[0]) {
  rz(pi*1/2) q[42];
}
if (c[0]) {
  sx q[42];
}
if (c[0]) {
  rz(pi*1/2) q[42];
}
if (c[0]) {
  cz q[43], q[42];
}
if (c[0]) {
  rz(pi*1/2) q[42];
}
if (c[0]) {
  sx q[42];
}
if (c[0]) {
  rz(pi*1/2) q[42];
}
if (c[0]) {
  rz(pi*1/2) q[43];
}
if (c[0]) {
  sx q[43];
}
if (c[0]) {
  rz(pi*1/2) q[43];
}
if (c[0]) {
  cz q[42], q[43];
}
if (c[0]) {
  rz(pi*1/2) q[43];
}
if (c[0]) {
  sx q[43];
}
if (c[0]) {
  rz(pi*1/2) q[43];
}
if (c[0]) {
  rz(pi*1/2) q[42];
}
if (c[0]) {
  sx q[42];
}
if (c[0]) {
  rz(pi*1/2) q[42];
}
if (c[0]) {
  cz q[43], q[42];
}
if (c[0]) {
  rz(pi*1/2) q[42];
}
if (c[0]) {
  sx q[42];
}
if (c[0]) {
  rz(pi*1/2) q[42];
}
rz(pi*1/2) q[42];
sx q[42];
rz(pi*1/2) q[42];
x q[42];
if (c[0]) {
  x q[43];
}
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
rz(pi*1/4) q[43];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
rz(pi*1/2) q[42];
sx q[42];
rz(pi*1/2) q[42];
cz q[43], q[42];
rz(pi*1/2) q[42];
sx q[42];
rz(pi*1/2) q[42];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
cz q[42], q[43];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
rz(pi*1/2) q[42];
sx q[42];
rz(pi*1/2) q[42];
cz q[43], q[42];
rz(pi*1/2) q[42];
sx q[42];
rz(pi*1/2) q[42];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
c[1] = measure q[44];
if (c[1]) {
  rz(pi*1/2) q[35];
}
if (c[1]) {
  sx q[35];
}
if (c[1]) {
  rz(pi*1/2) q[35];
}
if (c[1]) {
  cz q[44], q[35];
}
if (c[1]) {
  rz(pi*1/2) q[35];
}
if (c[1]) {
  sx q[35];
}
if (c[1]) {
  rz(pi*1/2) q[35];
}
if (c[1]) {
  rz(pi*1/2) q[44];
}
if (c[1]) {
  sx q[44];
}
if (c[1]) {
  rz(pi*1/2) q[44];
}
if (c[1]) {
  cz q[35], q[44];
}
if (c[1]) {
  rz(pi*1/2) q[44];
}
if (c[1]) {
  sx q[44];
}
if (c[1]) {
  rz(pi*1/2) q[44];
}
if (c[1]) {
  rz(pi*1/2) q[35];
}
if (c[1]) {
  sx q[35];
}
if (c[1]) {
  rz(pi*1/2) q[35];
}
if (c[1]) {
  cz q[44], q[35];
}
if (c[1]) {
  rz(pi*1/2) q[35];
}
if (c[1]) {
  sx q[35];
}
if (c[1]) {
  rz(pi*1/2) q[35];
}
if (c[1]) {
  cz q[45], q[44];
}
if (c[1]) {
  rz(pi*1/2) q[35];
}
if (c[1]) {
  sx q[35];
}
if (c[1]) {
  rz(pi*1/2) q[35];
}
if (c[1]) {
  cz q[44], q[35];
}
if (c[1]) {
  rz(pi*1/2) q[35];
}
if (c[1]) {
  sx q[35];
}
if (c[1]) {
  rz(pi*1/2) q[35];
}
if (c[1]) {
  rz(pi*1/2) q[44];
}
if (c[1]) {
  sx q[44];
}
if (c[1]) {
  rz(pi*1/2) q[44];
}
if (c[1]) {
  cz q[35], q[44];
}
if (c[1]) {
  rz(pi*1/2) q[44];
}
if (c[1]) {
  sx q[44];
}
if (c[1]) {
  rz(pi*1/2) q[44];
}
if (c[1]) {
  rz(pi*1/2) q[35];
}
if (c[1]) {
  sx q[35];
}
if (c[1]) {
  rz(pi*1/2) q[35];
}
if (c[1]) {
  cz q[44], q[35];
}
if (c[1]) {
  rz(pi*1/2) q[35];
}
if (c[1]) {
  sx q[35];
}
if (c[1]) {
  rz(pi*1/2) q[35];
}
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
x q[35];
if (c[1]) {
  x q[44];
}
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
rz(pi*1/4) q[44];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
x q[45];
cz q[45], q[44];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
cz q[35], q[44];
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
cz q[44], q[45];
cz q[44], q[35];
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
rz(pi*-1/4) q[35];
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
rz(pi*1/4) q[44];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
rz(pi*-1/4) q[45];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
cz q[44], q[45];
cz q[44], q[35];
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
rz(pi*1/2) q[44];
cz q[44], q[43];
x q[43];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
rz(pi*1/2) q[42];
sx q[42];
rz(pi*1/2) q[42];
cz q[43], q[42];
rz(pi*1/2) q[42];
sx q[42];
rz(pi*1/2) q[42];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
cz q[42], q[43];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
rz(pi*1/2) q[42];
sx q[42];
rz(pi*1/2) q[42];
cz q[43], q[42];
rz(pi*1/2) q[42];
sx q[42];
rz(pi*1/2) q[42];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
c[2] = measure q[44];
if (c[2]) {
  rz(pi*1/2) q[35];
}
if (c[2]) {
  sx q[35];
}
if (c[2]) {
  rz(pi*1/2) q[35];
}
if (c[2]) {
  cz q[44], q[35];
}
if (c[2]) {
  rz(pi*1/2) q[35];
}
if (c[2]) {
  sx q[35];
}
if (c[2]) {
  rz(pi*1/2) q[35];
}
if (c[2]) {
  rz(pi*1/2) q[44];
}
if (c[2]) {
  sx q[44];
}
if (c[2]) {
  rz(pi*1/2) q[44];
}
if (c[2]) {
  cz q[35], q[44];
}
if (c[2]) {
  rz(pi*1/2) q[44];
}
if (c[2]) {
  sx q[44];
}
if (c[2]) {
  rz(pi*1/2) q[44];
}
if (c[2]) {
  rz(pi*1/2) q[35];
}
if (c[2]) {
  sx q[35];
}
if (c[2]) {
  rz(pi*1/2) q[35];
}
if (c[2]) {
  cz q[44], q[35];
}
if (c[2]) {
  rz(pi*1/2) q[35];
}
if (c[2]) {
  sx q[35];
}
if (c[2]) {
  rz(pi*1/2) q[35];
}
if (c[2]) {
  cz q[45], q[44];
}
if (c[2]) {
  rz(pi*1/2) q[35];
}
if (c[2]) {
  sx q[35];
}
if (c[2]) {
  rz(pi*1/2) q[35];
}
if (c[2]) {
  cz q[44], q[35];
}
if (c[2]) {
  rz(pi*1/2) q[35];
}
if (c[2]) {
  sx q[35];
}
if (c[2]) {
  rz(pi*1/2) q[35];
}
if (c[2]) {
  rz(pi*1/2) q[44];
}
if (c[2]) {
  sx q[44];
}
if (c[2]) {
  rz(pi*1/2) q[44];
}
if (c[2]) {
  cz q[35], q[44];
}
if (c[2]) {
  rz(pi*1/2) q[44];
}
if (c[2]) {
  sx q[44];
}
if (c[2]) {
  rz(pi*1/2) q[44];
}
if (c[2]) {
  rz(pi*1/2) q[35];
}
if (c[2]) {
  sx q[35];
}
if (c[2]) {
  rz(pi*1/2) q[35];
}
if (c[2]) {
  cz q[44], q[35];
}
if (c[2]) {
  rz(pi*1/2) q[35];
}
if (c[2]) {
  sx q[35];
}
if (c[2]) {
  rz(pi*1/2) q[35];
}
x q[35];
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
if (c[2]) {
  x q[44];
}
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
rz(pi*1/4) q[44];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
x q[45];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
cz q[45], q[44];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
cz q[35], q[44];
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
cz q[44], q[45];
cz q[44], q[35];
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
rz(pi*-1/4) q[35];
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
rz(pi*1/4) q[44];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
rz(pi*-1/4) q[45];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
cz q[44], q[45];
cz q[44], q[35];
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
rz(pi*1/2) q[44];
cz q[44], q[43];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
cz q[42], q[43];
rz(pi*1/2) q[42];
sx q[42];
rz(pi*1/2) q[42];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
cz q[43], q[44];
cz q[43], q[42];
rz(pi*1/2) q[42];
sx q[42];
rz(pi*1/2) q[42];
rz(pi*-1/4) q[42];
rz(pi*1/2) q[42];
sx q[42];
rz(pi*1/2) q[42];
rz(pi*1/4) q[43];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
rz(pi*-1/4) q[44];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
cz q[43], q[44];
cz q[43], q[42];
rz(pi*1/2) q[42];
sx q[42];
rz(pi*1/2) q[42];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
rz(pi*1/2) q[43];
rz(pi*1) q[43];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
c[3] = measure q[43];
if (c[3]) {
  rz(pi*1/2) q[42];
}
if (c[3]) {
  sx q[42];
}
if (c[3]) {
  rz(pi*1/2) q[42];
}
if (c[3]) {
  cz q[43], q[42];
}
if (c[3]) {
  rz(pi*1/2) q[42];
}
if (c[3]) {
  sx q[42];
}
if (c[3]) {
  rz(pi*1/2) q[42];
}
if (c[3]) {
  rz(pi*1/2) q[43];
}
if (c[3]) {
  sx q[43];
}
if (c[3]) {
  rz(pi*1/2) q[43];
}
if (c[3]) {
  cz q[42], q[43];
}
if (c[3]) {
  rz(pi*1/2) q[43];
}
if (c[3]) {
  sx q[43];
}
if (c[3]) {
  rz(pi*1/2) q[43];
}
if (c[3]) {
  rz(pi*1/2) q[42];
}
if (c[3]) {
  sx q[42];
}
if (c[3]) {
  rz(pi*1/2) q[42];
}
if (c[3]) {
  cz q[43], q[42];
}
if (c[3]) {
  rz(pi*1/2) q[42];
}
if (c[3]) {
  sx q[42];
}
if (c[3]) {
  rz(pi*1/2) q[42];
}
if (c[3]) {
  cz q[44], q[43];
}
if (c[3]) {
  rz(pi*1/2) q[42];
}
if (c[3]) {
  sx q[42];
}
if (c[3]) {
  rz(pi*1/2) q[42];
}
if (c[3]) {
  cz q[43], q[42];
}
if (c[3]) {
  rz(pi*1/2) q[42];
}
if (c[3]) {
  sx q[42];
}
if (c[3]) {
  rz(pi*1/2) q[42];
}
if (c[3]) {
  rz(pi*1/2) q[43];
}
if (c[3]) {
  sx q[43];
}
if (c[3]) {
  rz(pi*1/2) q[43];
}
if (c[3]) {
  cz q[42], q[43];
}
if (c[3]) {
  rz(pi*1/2) q[43];
}
if (c[3]) {
  sx q[43];
}
if (c[3]) {
  rz(pi*1/2) q[43];
}
if (c[3]) {
  rz(pi*1/2) q[42];
}
if (c[3]) {
  sx q[42];
}
if (c[3]) {
  rz(pi*1/2) q[42];
}
if (c[3]) {
  cz q[43], q[42];
}
if (c[3]) {
  rz(pi*1/2) q[42];
}
if (c[3]) {
  sx q[42];
}
if (c[3]) {
  rz(pi*1/2) q[42];
}
rz(pi*1/2) q[42];
sx q[42];
rz(pi*1/2) q[42];
x q[42];
if (c[3]) {
  x q[43];
}
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
c[4] = measure q[44];
if (c[4]) {
  rz(pi*1/2) q[35];
}
if (c[4]) {
  sx q[35];
}
if (c[4]) {
  rz(pi*1/2) q[35];
}
if (c[4]) {
  cz q[44], q[35];
}
if (c[4]) {
  rz(pi*1/2) q[35];
}
if (c[4]) {
  sx q[35];
}
if (c[4]) {
  rz(pi*1/2) q[35];
}
if (c[4]) {
  rz(pi*1/2) q[44];
}
if (c[4]) {
  sx q[44];
}
if (c[4]) {
  rz(pi*1/2) q[44];
}
if (c[4]) {
  cz q[35], q[44];
}
if (c[4]) {
  rz(pi*1/2) q[44];
}
if (c[4]) {
  sx q[44];
}
if (c[4]) {
  rz(pi*1/2) q[44];
}
if (c[4]) {
  rz(pi*1/2) q[35];
}
if (c[4]) {
  sx q[35];
}
if (c[4]) {
  rz(pi*1/2) q[35];
}
if (c[4]) {
  cz q[44], q[35];
}
if (c[4]) {
  rz(pi*1/2) q[35];
}
if (c[4]) {
  sx q[35];
}
if (c[4]) {
  rz(pi*1/2) q[35];
}
if (c[4]) {
  cz q[45], q[44];
}
if (c[4]) {
  rz(pi*1/2) q[35];
}
if (c[4]) {
  sx q[35];
}
if (c[4]) {
  rz(pi*1/2) q[35];
}
if (c[4]) {
  cz q[44], q[35];
}
if (c[4]) {
  rz(pi*1/2) q[35];
}
if (c[4]) {
  sx q[35];
}
if (c[4]) {
  rz(pi*1/2) q[35];
}
if (c[4]) {
  rz(pi*1/2) q[44];
}
if (c[4]) {
  sx q[44];
}
if (c[4]) {
  rz(pi*1/2) q[44];
}
if (c[4]) {
  cz q[35], q[44];
}
if (c[4]) {
  rz(pi*1/2) q[44];
}
if (c[4]) {
  sx q[44];
}
if (c[4]) {
  rz(pi*1/2) q[44];
}
if (c[4]) {
  rz(pi*1/2) q[35];
}
if (c[4]) {
  sx q[35];
}
if (c[4]) {
  rz(pi*1/2) q[35];
}
if (c[4]) {
  cz q[44], q[35];
}
if (c[4]) {
  rz(pi*1/2) q[35];
}
if (c[4]) {
  sx q[35];
}
if (c[4]) {
  rz(pi*1/2) q[35];
}
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
x q[35];
if (c[4]) {
  x q[44];
}
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
rz(pi*1/4) q[44];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
x q[45];
cz q[45], q[44];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
cz q[35], q[44];
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
cz q[44], q[45];
cz q[44], q[35];
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
rz(pi*-1/4) q[35];
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
rz(pi*1/4) q[44];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
rz(pi*-1/4) q[45];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
cz q[44], q[45];
cz q[44], q[35];
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
rz(pi*1/2) q[44];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
cz q[43], q[44];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
cz q[44], q[43];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
cz q[43], q[44];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
cz q[43], q[42];
x q[42];
rz(pi*1/2) q[42];
sx q[42];
rz(pi*1/2) q[42];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
c[5] = measure q[43];
if (c[5]) {
  rz(pi*1/2) q[35];
}
if (c[5]) {
  sx q[35];
}
if (c[5]) {
  rz(pi*1/2) q[35];
}
if (c[5]) {
  cz q[44], q[35];
}
if (c[5]) {
  rz(pi*1/2) q[35];
}
if (c[5]) {
  sx q[35];
}
if (c[5]) {
  rz(pi*1/2) q[35];
}
if (c[5]) {
  rz(pi*1/2) q[44];
}
if (c[5]) {
  sx q[44];
}
if (c[5]) {
  rz(pi*1/2) q[44];
}
if (c[5]) {
  cz q[35], q[44];
}
if (c[5]) {
  rz(pi*1/2) q[44];
}
if (c[5]) {
  sx q[44];
}
if (c[5]) {
  rz(pi*1/2) q[44];
}
if (c[5]) {
  rz(pi*1/2) q[35];
}
if (c[5]) {
  sx q[35];
}
if (c[5]) {
  rz(pi*1/2) q[35];
}
if (c[5]) {
  cz q[44], q[35];
}
if (c[5]) {
  rz(pi*1/2) q[35];
}
if (c[5]) {
  sx q[35];
}
if (c[5]) {
  rz(pi*1/2) q[35];
}
if (c[5]) {
  cz q[45], q[44];
}
if (c[5]) {
  rz(pi*1/2) q[35];
}
if (c[5]) {
  sx q[35];
}
if (c[5]) {
  rz(pi*1/2) q[35];
}
if (c[5]) {
  cz q[44], q[35];
}
if (c[5]) {
  rz(pi*1/2) q[35];
}
if (c[5]) {
  sx q[35];
}
if (c[5]) {
  rz(pi*1/2) q[35];
}
if (c[5]) {
  rz(pi*1/2) q[44];
}
if (c[5]) {
  sx q[44];
}
if (c[5]) {
  rz(pi*1/2) q[44];
}
if (c[5]) {
  cz q[35], q[44];
}
if (c[5]) {
  rz(pi*1/2) q[44];
}
if (c[5]) {
  sx q[44];
}
if (c[5]) {
  rz(pi*1/2) q[44];
}
if (c[5]) {
  rz(pi*1/2) q[35];
}
if (c[5]) {
  sx q[35];
}
if (c[5]) {
  rz(pi*1/2) q[35];
}
if (c[5]) {
  cz q[44], q[35];
}
if (c[5]) {
  rz(pi*1/2) q[35];
}
if (c[5]) {
  sx q[35];
}
if (c[5]) {
  rz(pi*1/2) q[35];
}
x q[35];
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
if (c[5]) {
  x q[43];
}
x q[45];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
