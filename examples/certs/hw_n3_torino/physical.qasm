OPENQASM 3.0;
include "stdgates.inc";
bit[8] c;
qubit[133] q;
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/4) q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
cz q[63], q[64];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
cz q[65], q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
cz q[64], q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*-1/4) q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
cz q[64], q[65];
rz(pi*1/4) q[64];
cz q[64], q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*-1/4) q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
cz q[64], q[65];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
cz q[65], q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
cz q[64], q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
cz q[65], q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/4) q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
cz q[65], q[66];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
cz q[67], q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
cz q[66], q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*-1/4) q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
cz q[66], q[67];
rz(pi*1/4) q[66];
cz q[66], q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
rz(pi*-1/4) q[67];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
cz q[66], q[67];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/2) q[66];
rz(pi*1) q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
c[0] = measure q[66];
if (c[0]) {
  rz(pi*1/2) q[65];
}
if (c[0]) {
  sx q[65];
}
if (c[0]) {
  rz(pi*1/2) q[65];
}
if (c[0]) {
  cz q[66], q[65];
}
if (c[0]) {
  rz(pi*1/2) q[65];
}
if (c[0]) {
  sx q[65];
}
if (c[0]) {
  rz(pi*1/2) q[65];
}
if (c[0]) {
  rz(pi*1/2) q[66];
}
if (c[0]) {
  sx q[66];
}
if (c[0]) {
  rz(pi*1/2) q[66];
}
if (c[0]) {
  cz q[65], q[66];
}
if (c[0]) {
  rz(pi*1/2) q[66];
}
if (c[0]) {
  sx q[66];
}
if (c[0]) {
  rz(pi*1/2) q[66];
}
if (c[0]) {
  rz(pi*1/2) q[65];
}
if (c[0]) {
  sx q[65];
}
if (c[0]) {
  rz(pi*1/2) q[65];
}
if (c[0]) {
  cz q[66], q[65];
}
if (c[0]) {
  rz(pi*1/2) q[65];
}
if (c[0]) {
  sx q[65];
}
if (c[0]) {
  rz(pi*1/2) q[65];
}
if (c[0]) {
  cz q[66], q[67];
}
if (c[0]) {
  rz(pi*1/2) q[66];
}
if (c[0]) {
  sx q[66];
}
if (c[0]) {
  rz(pi*1/2) q[66];
}
if (c[0]) {
  cz q[65], q[66];
}
if (c[0]) {
  rz(pi*1/2) q[66];
}
if (c[0]) {
  sx q[66];
}
if (c[0]) {
  rz(pi*1/2) q[66];
}
if (c[0]) {
  rz(pi*1/2) q[65];
}
if (c[0]) {
  sx q[65];
}
if (c[0]) {
  rz(pi*1/2) q[65];
}
if (c[0]) {
  cz q[66], q[65];
}
if (c[0]) {
  rz(pi*1/2) q[65];
}
if (c[0]) {
  sx q[65];
}
if (c[0]) {
  rz(pi*1/2) q[65];
}
if (c[0]) {
  rz(pi*1/2) q[66];
}
if (c[0]) {
  sx q[66];
}
if (c[0]) {
  rz(pi*1/2) q[66];
}
if (c[0]) {
  cz q[65], q[66];
}
if (c[0]) {
  rz(pi*1/2) q[66];
}
if (c[0]) {
  sx q[66];
}
if (c[0]) {
  rz(pi*1/2) q[66];
}
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
if (c[0]) {
  x q[66];
}
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/4) q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
x q[67];
c[1] = measure q[65];
if (c[1]) {
  cz q[63], q[64];
}
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
x q[63];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
x q[64];
if (c[1]) {
  x q[65];
}
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/4) q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
cz q[64], q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
cz q[65], q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
cz q[64], q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
cz q[63], q[64];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
cz q[65], q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
cz q[64], q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*-1/4) q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
cz q[64], q[65];
rz(pi*1/4) q[64];
cz q[64], q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*-1/4) q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
cz q[64], q[65];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
cz q[65], q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
cz q[64], q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
cz q[65], q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
cz q[65], q[66];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
cz q[67], q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
cz q[66], q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*-1/4) q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
cz q[66], q[67];
rz(pi*1/4) q[66];
cz q[66], q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
rz(pi*-1/4) q[67];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
cz q[66], q[67];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/2) q[66];
rz(pi*1) q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
c[2] = measure q[66];
if (c[2]) {
  rz(pi*1/2) q[65];
}
if (c[2]) {
  sx q[65];
}
if (c[2]) {
  rz(pi*1/2) q[65];
}
if (c[2]) {
  cz q[66], q[65];
}
if (c[2]) {
  rz(pi*1/2) q[65];
}
if (c[2]) {
  sx q[65];
}
if (c[2]) {
  rz(pi*1/2) q[65];
}
if (c[2]) {
  rz(pi*1/2) q[66];
}
if (c[2]) {
  sx q[66];
}
if (c[2]) {
  rz(pi*1/2) q[66];
}
if (c[2]) {
  cz q[65], q[66];
}
if (c[2]) {
  rz(pi*1/2) q[66];
}
if (c[2]) {
  sx q[66];
}
if (c[2]) {
  rz(pi*1/2) q[66];
}
if (c[2]) {
  rz(pi*1/2) q[65];
}
if (c[2]) {
  sx q[65];
}
if (c[2]) {
  rz(pi*1/2) q[65];
}
if (c[2]) {
  cz q[66], q[65];
}
if (c[2]) {
  rz(pi*1/2) q[65];
}
if (c[2]) {
  sx q[65];
}
if (c[2]) {
  rz(pi*1/2) q[65];
}
if (c[2]) {
  cz q[66], q[67];
}
if (c[2]) {
  rz(pi*1/2) q[66];
}
if (c[2]) {
  sx q[66];
}
if (c[2]) {
  rz(pi*1/2) q[66];
}
if (c[2]) {
  cz q[65], q[66];
}
if (c[2]) {
  rz(pi*1/2) q[66];
}
if (c[2]) {
  sx q[66];
}
if (c[2]) {
  rz(pi*1/2) q[66];
}
if (c[2]) {
  rz(pi*1/2) q[65];
}
if (c[2]) {
  sx q[65];
}
if (c[2]) {
  rz(pi*1/2) q[65];
}
if (c[2]) {
  cz q[66], q[65];
}
if (c[2]) {
  rz(pi*1/2) q[65];
}
if (c[2]) {
  sx q[65];
}
if (c[2]) {
  rz(pi*1/2) q[65];
}
if (c[2]) {
  rz(pi*1/2) q[66];
}
if (c[2]) {
  sx q[66];
}
if (c[2]) {
  rz(pi*1/2) q[66];
}
if (c[2]) {
  cz q[65], q[66];
}
if (c[2]) {
  rz(pi*1/2) q[66];
}
if (c[2]) {
  sx q[66];
}
if (c[2]) {
  rz(pi*1/2) q[66];
}
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
if (c[2]) {
  x q[66];
}
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/4) q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
x q[67];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
c[3] = measure q[65];
if (c[3]) {
  cz q[63], q[64];
}
x q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
x q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
if (c[3]) {
  x q[65];
}
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/4) q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
cz q[64], q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
cz q[65], q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
cz q[64], q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
cz q[63], q[64];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
cz q[65], q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
cz q[64], q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*-1/4) q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
cz q[64], q[65];
rz(pi*1/4) q[64];
cz q[64], q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*-1/4) q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
cz q[64], q[65];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
cz q[65], q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
cz q[64], q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
cz q[65], q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
cz q[65], q[66];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
cz q[67], q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
cz q[66], q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*-1/4) q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
cz q[66], q[67];
rz(pi*1/4) q[66];
cz q[66], q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
rz(pi*-1/4) q[67];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
cz q[66], q[67];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/2) q[66];
rz(pi*1) q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
c[4] = measure q[66];
if (c[4]) {
  rz(pi*1/2) q[65];
}
if (c[4]) {
  sx q[65];
}
if (c[4]) {
  rz(pi*1/2) q[65];
}
if (c[4]) {
  cz q[66], q[65];
}
if (c[4]) {
  rz(pi*1/2) q[65];
}
if (c[4]) {
  sx q[65];
}
if (c[4]) {
  rz(pi*1/2) q[65];
}
if (c[4]) {
  rz(pi*1/2) q[66];
}
if (c[4]) {
  sx q[66];
}
if (c[4]) {
  rz(pi*1/2) q[66];
}
if (c[4]) {
  cz q[65], q[66];
}
if (c[4]) {
  rz(pi*1/2) q[66];
}
if (c[4]) {
  sx q[66];
}
if (c[4]) {
  rz(pi*1/2) q[66];
}
if (c[4]) {
  rz(pi*1/2) q[65];
}
if (c[4]) {
  sx q[65];
}
if (c[4]) {
  rz(pi*1/2) q[65];
}
if (c[4]) {
  cz q[66], q[65];
}
if (c[4]) {
  rz(pi*1/2) q[65];
}
if (c[4]) {
  sx q[65];
}
if (c[4]) {
  rz(pi*1/2) q[65];
}
if (c[4]) {
  cz q[66], q[67];
}
if (c[4]) {
  rz(pi*1/2) q[66];
}
if (c[4]) {
  sx q[66];
}
if (c[4]) {
  rz(pi*1/2) q[66];
}
if (c[4]) {
  cz q[65], q[66];
}
if (c[4]) {
  rz(pi*1/2) q[66];
}
if (c[4]) {
  sx q[66];
}
if (c[4]) {
  rz(pi*1/2) q[66];
}
if (c[4]) {
  rz(pi*1/2) q[65];
}
if (c[4]) {
  sx q[65];
}
if (c[4]) {
  rz(pi*1/2) q[65];
}
if (c[4]) {
  cz q[66], q[65];
}
if (c[4]) {
  rz(pi*1/2) q[65];
}
if (c[4]) {
  sx q[65];
}
if (c[4]) {
  rz(pi*1/2) q[65];
}
if (c[4]) {
  rz(pi*1/2) q[66];
}
if (c[4]) {
  sx q[66];
}
if (c[4]) {
  rz(pi*1/2) q[66];
}
if (c[4]) {
  cz q[65], q[66];
}
if (c[4]) {
  rz(pi*1/2) q[66];
}
if (c[4]) {
  sx q[66];
}
if (c[4]) {
  rz(pi*1/2) q[66];
}
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
if (c[4]) {
  x q[66];
}
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/4) q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
x q[67];
c[5] = measure q[65];
if (c[5]) {
  cz q[63], q[64];
}
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
x q[63];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
x q[64];
if (c[5]) {
  x q[65];
}
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/4) q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
cz q[64], q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
cz q[65], q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
cz q[64], q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
cz q[63], q[64];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
cz q[65], q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
cz q[64], q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*-1/4) q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
cz q[64], q[65];
rz(pi*1/4) q[64];
cz q[64], q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*-1/4) q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
cz q[64], q[65];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
cz q[65], q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
cz q[64], q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
cz q[65], q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
cz q[65], q[66];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
cz q[67], q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
cz q[66], q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*-1/4) q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
cz q[66], q[67];
rz(pi*1/4) q[66];
cz q[66], q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
rz(pi*-1/4) q[67];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
cz q[66], q[67];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/2) q[66];
rz(pi*1) q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
c[6] = measure q[66];
if (c[6]) {
  rz(pi*1/2) q[65];
}
if (c[6]) {
  sx q[65];
}
if (c[6]) {
  rz(pi*1/2) q[65];
}
if (c[6]) {
  cz q[66], q[65];
}
if (c[6]) {
  rz(pi*1/2) q[65];
}
if (c[6]) {
  sx q[65];
}
if (c[6]) {
  rz(pi*1/2) q[65];
}
if (c[6]) {
  rz(pi*1/2) q[66];
}
if (c[6]) {
  sx q[66];
}
if (c[6]) {
  rz(pi*1/2) q[66];
}
if (c[6]) {
  cz q[65], q[66];
}
if (c[6]) {
  rz(pi*1/2) q[66];
}
if (c[6]) {
  sx q[66];
}
if (c[6]) {
  rz(pi*1/2) q[66];
}
if (c[6]) {
  rz(pi*1/2) q[65];
}
if (c[6]) {
  sx q[65];
}
if (c[6]) {
  rz(pi*1/2) q[65];
}
if (c[6]) {
  cz q[66], q[65];
}
if (c[6]) {
  rz(pi*1/2) q[65];
}
if (c[6]) {
  sx q[65];
}
if (c[6]) {
  rz(pi*1/2) q[65];
}
if (c[6]) {
  cz q[66], q[67];
}
if (c[6]) {
  rz(pi*1/2) q[66];
}
if (c[6]) {
  sx q[66];
}
if (c[6]) {
  rz(pi*1/2) q[66];
}
if (c[6]) {
  cz q[65], q[66];
}
if (c[6]) {
  rz(pi*1/2) q[66];
}
if (c[6]) {
  sx q[66];
}
if (c[6]) {
  rz(pi*1/2) q[66];
}
if (c[6]) {
  rz(pi*1/2) q[65];
}
if (c[6]) {
  sx q[65];
}
if (c[6]) {
  rz(pi*1/2) q[65];
}
if (c[6]) {
  cz q[66], q[65];
}
if (c[6]) {
  rz(pi*1/2) q[65];
}
if (c[6]) {
  sx q[65];
}
if (c[6]) {
  rz(pi*1/2) q[65];
}
if (c[6]) {
  rz(pi*1/2) q[66];
}
if (c[6]) {
  sx q[66];
}
if (c[6]) {
  rz(pi*1/2) q[66];
}
if (c[6]) {
  cz q[65], q[66];
}
if (c[6]) {
  rz(pi*1/2) q[66];
}
if (c[6]) {
  sx q[66];
}
if (c[6]) {
  rz(pi*1/2) q[66];
}
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
if (c[6]) {
  x q[66];
}
x q[67];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
c[7] = measure q[65];
if (c[7]) {
  cz q[63], q[64];
}
x q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
x q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
if (c[7]) {
  x q[65];
}
