OPENQASM 3.0;
include "stdgates.inc";
bit[1] c;
qubit[133] q;
rz(pi*1/2) q[61];
sx q[61];
rz(pi*1/2) q[61];
rz(pi*1/4) q[61];
rz(pi*1/2) q[61];
sx q[61];
rz(pi*1/2) q[61];
cz q[60], q[61];
rz(pi*1/2) q[60];
sx q[60];
rz(pi*1/2) q[60];
rz(pi*1/2) q[61];
sx q[61];
rz(pi*1/2) q[61];
rz(pi*1/2) q[61];
sx q[61];
rz(pi*1/2) q[61];
cz q[54], q[61];
rz(pi*1/2) q[54];
sx q[54];
rz(pi*1/2) q[54];
rz(pi*1/2) q[61];
sx q[61];
rz(pi*1/2) q[61];
cz q[61], q[60];
rz(pi*1/2) q[60];
sx q[60];
rz(pi*1/2) q[60];
rz(pi*-1/4) q[60];
rz(pi*1/2) q[60];
sx q[60];
rz(pi*1/2) q[60];
cz q[61], q[54];
rz(pi*1/2) q[54];
sx q[54];
rz(pi*1/2) q[54];
rz(pi*-1/4) q[54];
rz(pi*1/2) q[54];
sx q[54];
rz(pi*1/2) q[54];
rz(pi*1/4) q[61];
cz q[61], q[60];
rz(pi*1/2) q[60];
sx q[60];
rz(pi*1/2) q[60];
cz q[61], q[54];
rz(pi*1/2) q[54];
sx q[54];
rz(pi*1/2) q[54];
rz(pi*1/2) q[61];
sx q[61];
rz(pi*1/2) q[61];
rz(pi*1/2) q[61];
rz(pi*1) q[61];
rz(pi*1/2) q[61];
sx q[61];
rz(pi*1/2) q[61];
c[0] = measure q[61];
if (c[0]) {
  rz(pi*1/2) q[60];
}
if (c[0]) {
  sx q[60];
}
if (c[0]) {
  rz(pi*1/2) q[60];
}
if (c[0]) {
  cz q[61], q[60];
}
if (c[0]) {
  rz(pi*1/2) q[60];
}
if (c[0]) {
  sx q[60];
}
if (c[0]) {
  rz(pi*1/2) q[60];
}
if (c[0]) {
  rz(pi*1/2) q[61];
}
if (c[0]) {
  sx q[61];
}
if (c[0]) {
  rz(pi*1/2) q[61];
}
if (c[0]) {
  cz q[60], q[61];
}
if (c[0]) {
  rz(pi*1/2) q[61];
}
if (c[0]) {
  sx q[61];
}
if (c[0]) {
  rz(pi*1/2) q[61];
}
if (c[0]) {
  rz(pi*1/2) q[60];
}
if (c[0]) {
  sx q[60];
}
if (c[0]) {
  rz(pi*1/2) q[60];
}
if (c[0]) {
  cz q[61], q[60];
}
if (c[0]) {
  rz(pi*1/2) q[60];
}
if (c[0]) {
  sx q[60];
}
if (c[0]) {
  rz(pi*1/2) q[60];
}
if (c[0]) {
  cz q[61], q[54];
}
if (c[0]) {
  rz(pi*1/2) q[60];
}
if (c[0]) {
  sx q[60];
}
if (c[0]) {
  rz(pi*1/2) q[60];
}
if (c[0]) {
  cz q[61], q[60];
}
if (c[0]) {
  rz(pi*1/2) q[60];
}
if (c[0]) {
  sx q[60];
}
if (c[0]) {
  rz(pi*1/2) q[60];
}
if (c[0]) {
  rz(pi*1/2) q[61];
}
if (c[0]) {
  sx q[61];
}
if (c[0]) {
  rz(pi*1/2) q[61];
}
if (c[0]) {
  cz q[60], q[61];
}
if (c[0]) {
  rz(pi*1/2) q[61];
}
if (c[0]) {
  sx q[61];
}
if (c[0]) {
  rz(pi*1/2) q[61];
}
if (c[0]) {
  rz(pi*1/2) q[60];
}
if (c[0]) {
  sx q[60];
}
if (c[0]) {
  rz(pi*1/2) q[60];
}
if (c[0]) {
  cz q[61], q[60];
}
if (c[0]) {
  rz(pi*1/2) q[60];
}
if (c[0]) {
  sx q[60];
}
if (c[0]) {
  rz(pi*1/2) q[60];
}
if (c[0]) {
  x q[61];
}
