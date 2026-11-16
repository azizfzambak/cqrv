OPENQASM 3.0;
include "stdgates.inc";
bit[18] c;
qubit[133] q;
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
x q[35];
rz(pi*1/2) q[42];
sx q[42];
rz(pi*1/2) q[42];
rz(pi*1/2) q[42];
sx q[42];
rz(pi*1/2) q[42];
x q[42];
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
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
cz q[44], q[35];
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
cz q[35], q[44];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
cz q[44], q[35];
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
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
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
cz q[44], q[35];
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
cz q[35], q[44];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
cz q[44], q[35];
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
cz q[43], q[44];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
x q[45];
rz(pi*1/2) q[46];
sx q[46];
rz(pi*1/2) q[46];
rz(pi*1/4) q[46];
rz(pi*1/2) q[46];
sx q[46];
rz(pi*1/2) q[46];
cz q[45], q[46];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
rz(pi*1/2) q[46];
sx q[46];
rz(pi*1/2) q[46];
rz(pi*1/2) q[46];
sx q[46];
rz(pi*1/2) q[46];
rz(pi*1/2) q[54];
sx q[54];
rz(pi*1/2) q[54];
rz(pi*1/4) q[54];
rz(pi*1/2) q[54];
sx q[54];
rz(pi*1/2) q[54];
rz(pi*1/2) q[55];
sx q[55];
rz(pi*1/2) q[55];
rz(pi*1/4) q[55];
rz(pi*1/2) q[55];
sx q[55];
rz(pi*1/2) q[55];
rz(pi*1/2) q[62];
sx q[62];
rz(pi*1/2) q[62];
rz(pi*1/4) q[62];
rz(pi*1/2) q[62];
sx q[62];
rz(pi*1/2) q[62];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
x q[63];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
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
cz q[67], q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
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
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
cz q[66], q[67];
cz q[66], q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*-1/4) q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/4) q[66];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
rz(pi*-1/4) q[67];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
cz q[66], q[67];
cz q[66], q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[55];
sx q[55];
rz(pi*1/2) q[55];
cz q[65], q[55];
rz(pi*1/2) q[55];
sx q[55];
rz(pi*1/2) q[55];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
cz q[55], q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[55];
sx q[55];
rz(pi*1/2) q[55];
cz q[65], q[55];
rz(pi*1/2) q[55];
sx q[55];
rz(pi*1/2) q[55];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/2) q[66];
cz q[66], q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
cz q[64], q[65];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
cz q[65], q[66];
cz q[65], q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*-1/4) q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/4) q[65];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*-1/4) q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
cz q[65], q[66];
cz q[65], q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[65];
rz(pi*1) q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
rz(pi*1/2) q[68];
sx q[68];
rz(pi*1/2) q[68];
rz(pi*1/2) q[68];
sx q[68];
rz(pi*1/2) q[68];
x q[68];
c[0] = measure q[65];
if (c[0]) {
  rz(pi*1/2) q[64];
}
if (c[0]) {
  sx q[64];
}
if (c[0]) {
  rz(pi*1/2) q[64];
}
if (c[0]) {
  cz q[65], q[64];
}
if (c[0]) {
  rz(pi*1/2) q[64];
}
if (c[0]) {
  sx q[64];
}
if (c[0]) {
  rz(pi*1/2) q[64];
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
  cz q[64], q[65];
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
  rz(pi*1/2) q[64];
}
if (c[0]) {
  sx q[64];
}
if (c[0]) {
  rz(pi*1/2) q[64];
}
if (c[0]) {
  cz q[65], q[64];
}
if (c[0]) {
  rz(pi*1/2) q[64];
}
if (c[0]) {
  sx q[64];
}
if (c[0]) {
  rz(pi*1/2) q[64];
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
  cz q[64], q[65];
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
  rz(pi*1/2) q[64];
}
if (c[0]) {
  sx q[64];
}
if (c[0]) {
  rz(pi*1/2) q[64];
}
if (c[0]) {
  cz q[65], q[64];
}
if (c[0]) {
  rz(pi*1/2) q[64];
}
if (c[0]) {
  sx q[64];
}
if (c[0]) {
  rz(pi*1/2) q[64];
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
  cz q[64], q[65];
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
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
x q[64];
if (c[0]) {
  x q[65];
}
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/4) q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
c[1] = measure q[66];
if (c[1]) {
  rz(pi*1/2) q[55];
}
if (c[1]) {
  sx q[55];
}
if (c[1]) {
  rz(pi*1/2) q[55];
}
if (c[1]) {
  cz q[65], q[55];
}
if (c[1]) {
  rz(pi*1/2) q[55];
}
if (c[1]) {
  sx q[55];
}
if (c[1]) {
  rz(pi*1/2) q[55];
}
if (c[1]) {
  rz(pi*1/2) q[65];
}
if (c[1]) {
  sx q[65];
}
if (c[1]) {
  rz(pi*1/2) q[65];
}
if (c[1]) {
  cz q[55], q[65];
}
if (c[1]) {
  rz(pi*1/2) q[65];
}
if (c[1]) {
  sx q[65];
}
if (c[1]) {
  rz(pi*1/2) q[65];
}
if (c[1]) {
  rz(pi*1/2) q[55];
}
if (c[1]) {
  sx q[55];
}
if (c[1]) {
  rz(pi*1/2) q[55];
}
if (c[1]) {
  cz q[65], q[55];
}
if (c[1]) {
  rz(pi*1/2) q[55];
}
if (c[1]) {
  sx q[55];
}
if (c[1]) {
  rz(pi*1/2) q[55];
}
if (c[1]) {
  rz(pi*1/2) q[67];
}
if (c[1]) {
  sx q[67];
}
if (c[1]) {
  rz(pi*1/2) q[67];
}
if (c[1]) {
  cz q[66], q[67];
}
if (c[1]) {
  rz(pi*1/2) q[67];
}
if (c[1]) {
  sx q[67];
}
if (c[1]) {
  rz(pi*1/2) q[67];
}
if (c[1]) {
  rz(pi*1/2) q[66];
}
if (c[1]) {
  sx q[66];
}
if (c[1]) {
  rz(pi*1/2) q[66];
}
if (c[1]) {
  cz q[67], q[66];
}
if (c[1]) {
  rz(pi*1/2) q[66];
}
if (c[1]) {
  sx q[66];
}
if (c[1]) {
  rz(pi*1/2) q[66];
}
if (c[1]) {
  rz(pi*1/2) q[67];
}
if (c[1]) {
  sx q[67];
}
if (c[1]) {
  rz(pi*1/2) q[67];
}
if (c[1]) {
  cz q[66], q[67];
}
if (c[1]) {
  rz(pi*1/2) q[67];
}
if (c[1]) {
  sx q[67];
}
if (c[1]) {
  rz(pi*1/2) q[67];
}
if (c[1]) {
  cz q[66], q[65];
}
if (c[1]) {
  rz(pi*1/2) q[55];
}
if (c[1]) {
  sx q[55];
}
if (c[1]) {
  rz(pi*1/2) q[55];
}
if (c[1]) {
  cz q[65], q[55];
}
if (c[1]) {
  rz(pi*1/2) q[55];
}
if (c[1]) {
  sx q[55];
}
if (c[1]) {
  rz(pi*1/2) q[55];
}
if (c[1]) {
  rz(pi*1/2) q[65];
}
if (c[1]) {
  sx q[65];
}
if (c[1]) {
  rz(pi*1/2) q[65];
}
if (c[1]) {
  cz q[55], q[65];
}
if (c[1]) {
  rz(pi*1/2) q[65];
}
if (c[1]) {
  sx q[65];
}
if (c[1]) {
  rz(pi*1/2) q[65];
}
if (c[1]) {
  rz(pi*1/2) q[55];
}
if (c[1]) {
  sx q[55];
}
if (c[1]) {
  rz(pi*1/2) q[55];
}
if (c[1]) {
  cz q[65], q[55];
}
if (c[1]) {
  rz(pi*1/2) q[55];
}
if (c[1]) {
  sx q[55];
}
if (c[1]) {
  rz(pi*1/2) q[55];
}
if (c[1]) {
  rz(pi*1/2) q[67];
}
if (c[1]) {
  sx q[67];
}
if (c[1]) {
  rz(pi*1/2) q[67];
}
if (c[1]) {
  cz q[66], q[67];
}
if (c[1]) {
  rz(pi*1/2) q[67];
}
if (c[1]) {
  sx q[67];
}
if (c[1]) {
  rz(pi*1/2) q[67];
}
if (c[1]) {
  rz(pi*1/2) q[66];
}
if (c[1]) {
  sx q[66];
}
if (c[1]) {
  rz(pi*1/2) q[66];
}
if (c[1]) {
  cz q[67], q[66];
}
if (c[1]) {
  rz(pi*1/2) q[66];
}
if (c[1]) {
  sx q[66];
}
if (c[1]) {
  rz(pi*1/2) q[66];
}
if (c[1]) {
  rz(pi*1/2) q[67];
}
if (c[1]) {
  sx q[67];
}
if (c[1]) {
  rz(pi*1/2) q[67];
}
if (c[1]) {
  cz q[66], q[67];
}
if (c[1]) {
  rz(pi*1/2) q[67];
}
if (c[1]) {
  sx q[67];
}
if (c[1]) {
  rz(pi*1/2) q[67];
}
rz(pi*1/2) q[55];
sx q[55];
rz(pi*1/2) q[55];
x q[55];
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
rz(pi*1/2) q[55];
sx q[55];
rz(pi*1/2) q[55];
cz q[65], q[55];
rz(pi*1/2) q[55];
sx q[55];
rz(pi*1/2) q[55];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
cz q[55], q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[55];
sx q[55];
rz(pi*1/2) q[55];
cz q[65], q[55];
rz(pi*1/2) q[55];
sx q[55];
rz(pi*1/2) q[55];
cz q[55], q[46];
rz(pi*1/2) q[46];
sx q[46];
rz(pi*1/2) q[46];
cz q[46], q[45];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
rz(pi*-1/4) q[45];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
rz(pi*1/2) q[55];
sx q[55];
rz(pi*1/2) q[55];
cz q[46], q[55];
rz(pi*1/4) q[46];
cz q[46], q[45];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
rz(pi*1/2) q[55];
sx q[55];
rz(pi*1/2) q[55];
rz(pi*-1/4) q[55];
rz(pi*1/2) q[55];
sx q[55];
rz(pi*1/2) q[55];
cz q[46], q[55];
rz(pi*1/2) q[46];
sx q[46];
rz(pi*1/2) q[46];
rz(pi*1/2) q[46];
rz(pi*1/2) q[46];
sx q[46];
rz(pi*1/2) q[46];
cz q[45], q[46];
rz(pi*1/2) q[46];
sx q[46];
rz(pi*1/2) q[46];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
cz q[46], q[45];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
rz(pi*1/2) q[46];
sx q[46];
rz(pi*1/2) q[46];
cz q[45], q[46];
rz(pi*1/2) q[46];
sx q[46];
rz(pi*1/2) q[46];
cz q[45], q[44];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
cz q[44], q[43];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
rz(pi*-1/4) q[43];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
cz q[44], q[45];
rz(pi*1/4) q[44];
cz q[44], q[43];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
rz(pi*-1/4) q[45];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
cz q[44], q[45];
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
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
cz q[42], q[43];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
rz(pi*1/2) q[55];
sx q[55];
rz(pi*1/2) q[55];
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
rz(pi*1/2) q[62];
sx q[62];
rz(pi*1/2) q[62];
cz q[63], q[62];
rz(pi*1/2) q[62];
sx q[62];
rz(pi*1/2) q[62];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
cz q[62], q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*1/2) q[62];
sx q[62];
rz(pi*1/2) q[62];
cz q[63], q[62];
rz(pi*1/2) q[62];
sx q[62];
rz(pi*1/2) q[62];
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
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
cz q[64], q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
cz q[63], q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
cz q[64], q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
if (c[1]) {
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
cz q[67], q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
cz q[67], q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
cz q[66], q[67];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
cz q[67], q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
cz q[68], q[67];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
cz q[67], q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*-1/4) q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/2) q[68];
sx q[68];
rz(pi*1/2) q[68];
cz q[67], q[68];
rz(pi*1/4) q[67];
cz q[67], q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/2) q[68];
sx q[68];
rz(pi*1/2) q[68];
rz(pi*-1/4) q[68];
rz(pi*1/2) q[68];
sx q[68];
rz(pi*1/2) q[68];
cz q[67], q[68];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
rz(pi*1/2) q[67];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
cz q[66], q[67];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
cz q[67], q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
cz q[66], q[67];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
cz q[65], q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
cz q[66], q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
cz q[65], q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
cz q[65], q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
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
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
cz q[64], q[65];
cz q[64], q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*-1/4) q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*1/4) q[64];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*-1/4) q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
cz q[64], q[65];
cz q[64], q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
cz q[63], q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
cz q[64], q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
cz q[63], q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
cz q[62], q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*1/2) q[62];
sx q[62];
rz(pi*1/2) q[62];
cz q[63], q[62];
rz(pi*1/2) q[62];
sx q[62];
rz(pi*1/2) q[62];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
cz q[62], q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*1/2) q[62];
sx q[62];
rz(pi*1/2) q[62];
cz q[61], q[62];
rz(pi*1/2) q[62];
sx q[62];
rz(pi*1/2) q[62];
rz(pi*1/2) q[61];
sx q[61];
rz(pi*1/2) q[61];
cz q[62], q[61];
rz(pi*1/2) q[61];
sx q[61];
rz(pi*1/2) q[61];
rz(pi*1/2) q[62];
sx q[62];
rz(pi*1/2) q[62];
cz q[61], q[62];
rz(pi*1/2) q[62];
sx q[62];
rz(pi*1/2) q[62];
cz q[61], q[54];
rz(pi*1/2) q[54];
sx q[54];
rz(pi*1/2) q[54];
rz(pi*1/2) q[54];
sx q[54];
rz(pi*1/2) q[54];
cz q[42], q[54];
rz(pi*1/2) q[42];
sx q[42];
rz(pi*1/2) q[42];
rz(pi*1/2) q[54];
sx q[54];
rz(pi*1/2) q[54];
rz(pi*1/2) q[61];
sx q[61];
rz(pi*1/2) q[61];
cz q[54], q[61];
cz q[54], q[42];
rz(pi*1/2) q[42];
sx q[42];
rz(pi*1/2) q[42];
rz(pi*-1/4) q[42];
rz(pi*1/2) q[42];
sx q[42];
rz(pi*1/2) q[42];
rz(pi*1/4) q[54];
rz(pi*1/2) q[61];
sx q[61];
rz(pi*1/2) q[61];
rz(pi*-1/4) q[61];
rz(pi*1/2) q[61];
sx q[61];
rz(pi*1/2) q[61];
cz q[54], q[61];
cz q[54], q[42];
rz(pi*1/2) q[42];
sx q[42];
rz(pi*1/2) q[42];
rz(pi*1/2) q[54];
sx q[54];
rz(pi*1/2) q[54];
rz(pi*1/2) q[54];
rz(pi*1) q[54];
rz(pi*1/2) q[54];
sx q[54];
rz(pi*1/2) q[54];
rz(pi*1/2) q[61];
sx q[61];
rz(pi*1/2) q[61];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[68];
sx q[68];
rz(pi*1/2) q[68];
c[2] = measure q[54];
if (c[2]) {
  rz(pi*1/2) q[42];
}
if (c[2]) {
  sx q[42];
}
if (c[2]) {
  rz(pi*1/2) q[42];
}
if (c[2]) {
  cz q[54], q[42];
}
if (c[2]) {
  rz(pi*1/2) q[42];
}
if (c[2]) {
  sx q[42];
}
if (c[2]) {
  rz(pi*1/2) q[42];
}
if (c[2]) {
  rz(pi*1/2) q[54];
}
if (c[2]) {
  sx q[54];
}
if (c[2]) {
  rz(pi*1/2) q[54];
}
if (c[2]) {
  cz q[42], q[54];
}
if (c[2]) {
  rz(pi*1/2) q[54];
}
if (c[2]) {
  sx q[54];
}
if (c[2]) {
  rz(pi*1/2) q[54];
}
if (c[2]) {
  rz(pi*1/2) q[42];
}
if (c[2]) {
  sx q[42];
}
if (c[2]) {
  rz(pi*1/2) q[42];
}
if (c[2]) {
  cz q[54], q[42];
}
if (c[2]) {
  rz(pi*1/2) q[42];
}
if (c[2]) {
  sx q[42];
}
if (c[2]) {
  rz(pi*1/2) q[42];
}
if (c[2]) {
  cz q[61], q[54];
}
if (c[2]) {
  rz(pi*1/2) q[54];
}
if (c[2]) {
  sx q[54];
}
if (c[2]) {
  rz(pi*1/2) q[54];
}
if (c[2]) {
  cz q[42], q[54];
}
if (c[2]) {
  rz(pi*1/2) q[54];
}
if (c[2]) {
  sx q[54];
}
if (c[2]) {
  rz(pi*1/2) q[54];
}
if (c[2]) {
  rz(pi*1/2) q[42];
}
if (c[2]) {
  sx q[42];
}
if (c[2]) {
  rz(pi*1/2) q[42];
}
if (c[2]) {
  cz q[54], q[42];
}
if (c[2]) {
  rz(pi*1/2) q[42];
}
if (c[2]) {
  sx q[42];
}
if (c[2]) {
  rz(pi*1/2) q[42];
}
if (c[2]) {
  rz(pi*1/2) q[54];
}
if (c[2]) {
  sx q[54];
}
if (c[2]) {
  rz(pi*1/2) q[54];
}
if (c[2]) {
  cz q[42], q[54];
}
if (c[2]) {
  rz(pi*1/2) q[54];
}
if (c[2]) {
  sx q[54];
}
if (c[2]) {
  rz(pi*1/2) q[54];
}
rz(pi*1/2) q[42];
sx q[42];
rz(pi*1/2) q[42];
if (c[2]) {
  x q[54];
}
rz(pi*1/2) q[54];
sx q[54];
rz(pi*1/2) q[54];
rz(pi*1/4) q[54];
rz(pi*1/2) q[54];
sx q[54];
rz(pi*1/2) q[54];
rz(pi*1/2) q[61];
sx q[61];
rz(pi*1/2) q[61];
c[3] = measure q[42];
if (c[3]) {
  cz q[44], q[45];
}
if (c[3]) {
  x q[42];
}
rz(pi*1/2) q[42];
sx q[42];
rz(pi*1/2) q[42];
rz(pi*1/4) q[42];
rz(pi*1/2) q[42];
sx q[42];
rz(pi*1/2) q[42];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
c[4] = measure q[61];
if (c[4]) {
  cz q[65], q[64];
}
if (c[4]) {
  x q[61];
}
rz(pi*1/2) q[61];
sx q[61];
rz(pi*1/2) q[61];
rz(pi*1/4) q[61];
rz(pi*1/2) q[61];
sx q[61];
rz(pi*1/2) q[61];
rz(pi*1/2) q[61];
sx q[61];
rz(pi*1/2) q[61];
cz q[62], q[61];
rz(pi*1/2) q[61];
sx q[61];
rz(pi*1/2) q[61];
rz(pi*1/2) q[62];
sx q[62];
rz(pi*1/2) q[62];
cz q[61], q[62];
rz(pi*1/2) q[62];
sx q[62];
rz(pi*1/2) q[62];
rz(pi*1/2) q[61];
sx q[61];
rz(pi*1/2) q[61];
cz q[62], q[61];
rz(pi*1/2) q[61];
sx q[61];
rz(pi*1/2) q[61];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
c[5] = measure q[45];
if (c[5]) {
  cz q[46], q[55];
}
if (c[5]) {
  x q[45];
}
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
rz(pi*1/4) q[45];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
x q[46];
rz(pi*1/2) q[46];
sx q[46];
rz(pi*1/2) q[46];
rz(pi*1/2) q[46];
sx q[46];
rz(pi*1/2) q[46];
x q[46];
cz q[46], q[45];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
rz(pi*1/2) q[46];
sx q[46];
rz(pi*1/2) q[46];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
cz q[46], q[45];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
rz(pi*1/2) q[46];
sx q[46];
rz(pi*1/2) q[46];
cz q[45], q[46];
rz(pi*1/2) q[46];
sx q[46];
rz(pi*1/2) q[46];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
cz q[46], q[45];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
x q[55];
rz(pi*1/2) q[55];
sx q[55];
rz(pi*1/2) q[55];
c[6] = measure q[44];
if (c[6]) {
  rz(pi*1/2) q[43];
}
if (c[6]) {
  sx q[43];
}
if (c[6]) {
  rz(pi*1/2) q[43];
}
if (c[6]) {
  cz q[44], q[43];
}
if (c[6]) {
  rz(pi*1/2) q[43];
}
if (c[6]) {
  sx q[43];
}
if (c[6]) {
  rz(pi*1/2) q[43];
}
if (c[6]) {
  rz(pi*1/2) q[44];
}
if (c[6]) {
  sx q[44];
}
if (c[6]) {
  rz(pi*1/2) q[44];
}
if (c[6]) {
  cz q[43], q[44];
}
if (c[6]) {
  rz(pi*1/2) q[44];
}
if (c[6]) {
  sx q[44];
}
if (c[6]) {
  rz(pi*1/2) q[44];
}
if (c[6]) {
  rz(pi*1/2) q[43];
}
if (c[6]) {
  sx q[43];
}
if (c[6]) {
  rz(pi*1/2) q[43];
}
if (c[6]) {
  cz q[44], q[43];
}
if (c[6]) {
  rz(pi*1/2) q[43];
}
if (c[6]) {
  sx q[43];
}
if (c[6]) {
  rz(pi*1/2) q[43];
}
if (c[6]) {
  cz q[35], q[44];
}
if (c[6]) {
  rz(pi*1/2) q[44];
}
if (c[6]) {
  sx q[44];
}
if (c[6]) {
  rz(pi*1/2) q[44];
}
if (c[6]) {
  cz q[43], q[44];
}
if (c[6]) {
  rz(pi*1/2) q[44];
}
if (c[6]) {
  sx q[44];
}
if (c[6]) {
  rz(pi*1/2) q[44];
}
if (c[6]) {
  rz(pi*1/2) q[43];
}
if (c[6]) {
  sx q[43];
}
if (c[6]) {
  rz(pi*1/2) q[43];
}
if (c[6]) {
  cz q[44], q[43];
}
if (c[6]) {
  rz(pi*1/2) q[43];
}
if (c[6]) {
  sx q[43];
}
if (c[6]) {
  rz(pi*1/2) q[43];
}
if (c[6]) {
  rz(pi*1/2) q[44];
}
if (c[6]) {
  sx q[44];
}
if (c[6]) {
  rz(pi*1/2) q[44];
}
if (c[6]) {
  cz q[43], q[44];
}
if (c[6]) {
  rz(pi*1/2) q[44];
}
if (c[6]) {
  sx q[44];
}
if (c[6]) {
  rz(pi*1/2) q[44];
}
x q[35];
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
x q[35];
x q[43];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
x q[43];
if (c[6]) {
  x q[44];
}
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
rz(pi*1/4) q[44];
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
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
cz q[43], q[44];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
cz q[44], q[35];
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
rz(pi*-1/4) q[35];
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
cz q[44], q[43];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
rz(pi*-1/4) q[43];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
rz(pi*1/4) q[44];
cz q[44], q[35];
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
cz q[44], q[43];
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
rz(pi*1/2) q[44];
cz q[44], q[43];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
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
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
cz q[44], q[43];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
c[7] = measure q[64];
c[8] = measure q[65];
if (c[7]) {
  rz(pi*1/2) q[63];
}
if (c[7]) {
  sx q[63];
}
if (c[7]) {
  rz(pi*1/2) q[63];
}
if (c[7]) {
  cz q[64], q[63];
}
if (c[7]) {
  rz(pi*1/2) q[63];
}
if (c[7]) {
  sx q[63];
}
if (c[7]) {
  rz(pi*1/2) q[63];
}
if (c[7]) {
  rz(pi*1/2) q[64];
}
if (c[7]) {
  sx q[64];
}
if (c[7]) {
  rz(pi*1/2) q[64];
}
if (c[7]) {
  cz q[63], q[64];
}
if (c[7]) {
  rz(pi*1/2) q[64];
}
if (c[7]) {
  sx q[64];
}
if (c[7]) {
  rz(pi*1/2) q[64];
}
if (c[7]) {
  rz(pi*1/2) q[63];
}
if (c[7]) {
  sx q[63];
}
if (c[7]) {
  rz(pi*1/2) q[63];
}
if (c[7]) {
  cz q[64], q[63];
}
if (c[7]) {
  rz(pi*1/2) q[63];
}
if (c[7]) {
  sx q[63];
}
if (c[7]) {
  rz(pi*1/2) q[63];
}
if (c[7]) {
  rz(pi*1/2) q[66];
}
if (c[7]) {
  sx q[66];
}
if (c[7]) {
  rz(pi*1/2) q[66];
}
if (c[7]) {
  cz q[65], q[66];
}
if (c[7]) {
  rz(pi*1/2) q[66];
}
if (c[7]) {
  sx q[66];
}
if (c[7]) {
  rz(pi*1/2) q[66];
}
if (c[7]) {
  rz(pi*1/2) q[65];
}
if (c[7]) {
  sx q[65];
}
if (c[7]) {
  rz(pi*1/2) q[65];
}
if (c[7]) {
  cz q[66], q[65];
}
if (c[7]) {
  rz(pi*1/2) q[65];
}
if (c[7]) {
  sx q[65];
}
if (c[7]) {
  rz(pi*1/2) q[65];
}
if (c[7]) {
  rz(pi*1/2) q[66];
}
if (c[7]) {
  sx q[66];
}
if (c[7]) {
  rz(pi*1/2) q[66];
}
if (c[7]) {
  cz q[65], q[66];
}
if (c[7]) {
  rz(pi*1/2) q[66];
}
if (c[7]) {
  sx q[66];
}
if (c[7]) {
  rz(pi*1/2) q[66];
}
if (c[7]) {
  cz q[64], q[65];
}
if (c[7]) {
  rz(pi*1/2) q[63];
}
if (c[7]) {
  sx q[63];
}
if (c[7]) {
  rz(pi*1/2) q[63];
}
if (c[7]) {
  cz q[64], q[63];
}
if (c[7]) {
  rz(pi*1/2) q[63];
}
if (c[7]) {
  sx q[63];
}
if (c[7]) {
  rz(pi*1/2) q[63];
}
if (c[7]) {
  rz(pi*1/2) q[64];
}
if (c[7]) {
  sx q[64];
}
if (c[7]) {
  rz(pi*1/2) q[64];
}
if (c[7]) {
  cz q[63], q[64];
}
if (c[7]) {
  rz(pi*1/2) q[64];
}
if (c[7]) {
  sx q[64];
}
if (c[7]) {
  rz(pi*1/2) q[64];
}
if (c[7]) {
  rz(pi*1/2) q[63];
}
if (c[7]) {
  sx q[63];
}
if (c[7]) {
  rz(pi*1/2) q[63];
}
if (c[7]) {
  cz q[64], q[63];
}
if (c[7]) {
  rz(pi*1/2) q[63];
}
if (c[7]) {
  sx q[63];
}
if (c[7]) {
  rz(pi*1/2) q[63];
}
if (c[7]) {
  rz(pi*1/2) q[66];
}
if (c[7]) {
  sx q[66];
}
if (c[7]) {
  rz(pi*1/2) q[66];
}
if (c[7]) {
  cz q[65], q[66];
}
if (c[7]) {
  rz(pi*1/2) q[66];
}
if (c[7]) {
  sx q[66];
}
if (c[7]) {
  rz(pi*1/2) q[66];
}
if (c[7]) {
  rz(pi*1/2) q[65];
}
if (c[7]) {
  sx q[65];
}
if (c[7]) {
  rz(pi*1/2) q[65];
}
if (c[7]) {
  cz q[66], q[65];
}
if (c[7]) {
  rz(pi*1/2) q[65];
}
if (c[7]) {
  sx q[65];
}
if (c[7]) {
  rz(pi*1/2) q[65];
}
if (c[7]) {
  rz(pi*1/2) q[66];
}
if (c[7]) {
  sx q[66];
}
if (c[7]) {
  rz(pi*1/2) q[66];
}
if (c[7]) {
  cz q[65], q[66];
}
if (c[7]) {
  rz(pi*1/2) q[66];
}
if (c[7]) {
  sx q[66];
}
if (c[7]) {
  rz(pi*1/2) q[66];
}
x q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
x q[63];
if (c[7]) {
  x q[64];
}
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/4) q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
x q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
if (c[8]) {
  cz q[67], q[68];
}
if (c[8]) {
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
cz q[66], q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
cz q[65], q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
cz q[66], q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
x q[67];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
cz q[67], q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
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
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
cz q[66], q[67];
cz q[66], q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*-1/4) q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/4) q[66];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
rz(pi*-1/4) q[67];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
cz q[66], q[67];
cz q[66], q[65];
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
rz(pi*1/2) q[66];
cz q[66], q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
cz q[55], q[65];
rz(pi*1/2) q[55];
sx q[55];
rz(pi*1/2) q[55];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
cz q[65], q[66];
cz q[65], q[55];
rz(pi*1/2) q[55];
sx q[55];
rz(pi*1/2) q[55];
rz(pi*-1/4) q[55];
rz(pi*1/2) q[55];
sx q[55];
rz(pi*1/2) q[55];
rz(pi*1/4) q[65];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*-1/4) q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
cz q[65], q[66];
cz q[65], q[55];
rz(pi*1/2) q[55];
sx q[55];
rz(pi*1/2) q[55];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[65];
rz(pi*1) q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
x q[68];
rz(pi*1/2) q[68];
sx q[68];
rz(pi*1/2) q[68];
rz(pi*1/2) q[68];
sx q[68];
rz(pi*1/2) q[68];
x q[68];
c[9] = measure q[65];
if (c[9]) {
  rz(pi*1/2) q[55];
}
if (c[9]) {
  sx q[55];
}
if (c[9]) {
  rz(pi*1/2) q[55];
}
if (c[9]) {
  cz q[65], q[55];
}
if (c[9]) {
  rz(pi*1/2) q[55];
}
if (c[9]) {
  sx q[55];
}
if (c[9]) {
  rz(pi*1/2) q[55];
}
if (c[9]) {
  rz(pi*1/2) q[65];
}
if (c[9]) {
  sx q[65];
}
if (c[9]) {
  rz(pi*1/2) q[65];
}
if (c[9]) {
  cz q[55], q[65];
}
if (c[9]) {
  rz(pi*1/2) q[65];
}
if (c[9]) {
  sx q[65];
}
if (c[9]) {
  rz(pi*1/2) q[65];
}
if (c[9]) {
  rz(pi*1/2) q[55];
}
if (c[9]) {
  sx q[55];
}
if (c[9]) {
  rz(pi*1/2) q[55];
}
if (c[9]) {
  cz q[65], q[55];
}
if (c[9]) {
  rz(pi*1/2) q[55];
}
if (c[9]) {
  sx q[55];
}
if (c[9]) {
  rz(pi*1/2) q[55];
}
if (c[9]) {
  cz q[66], q[65];
}
if (c[9]) {
  rz(pi*1/2) q[65];
}
if (c[9]) {
  sx q[65];
}
if (c[9]) {
  rz(pi*1/2) q[65];
}
if (c[9]) {
  cz q[55], q[65];
}
if (c[9]) {
  rz(pi*1/2) q[65];
}
if (c[9]) {
  sx q[65];
}
if (c[9]) {
  rz(pi*1/2) q[65];
}
if (c[9]) {
  rz(pi*1/2) q[55];
}
if (c[9]) {
  sx q[55];
}
if (c[9]) {
  rz(pi*1/2) q[55];
}
if (c[9]) {
  cz q[65], q[55];
}
if (c[9]) {
  rz(pi*1/2) q[55];
}
if (c[9]) {
  sx q[55];
}
if (c[9]) {
  rz(pi*1/2) q[55];
}
if (c[9]) {
  rz(pi*1/2) q[65];
}
if (c[9]) {
  sx q[65];
}
if (c[9]) {
  rz(pi*1/2) q[65];
}
if (c[9]) {
  cz q[55], q[65];
}
if (c[9]) {
  rz(pi*1/2) q[65];
}
if (c[9]) {
  sx q[65];
}
if (c[9]) {
  rz(pi*1/2) q[65];
}
rz(pi*1/2) q[55];
sx q[55];
rz(pi*1/2) q[55];
x q[55];
cz q[55], q[46];
rz(pi*1/2) q[46];
sx q[46];
rz(pi*1/2) q[46];
cz q[46], q[45];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
rz(pi*-1/4) q[45];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
rz(pi*1/2) q[55];
sx q[55];
rz(pi*1/2) q[55];
cz q[46], q[55];
rz(pi*1/4) q[46];
cz q[46], q[45];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
rz(pi*1/2) q[55];
sx q[55];
rz(pi*1/2) q[55];
rz(pi*-1/4) q[55];
rz(pi*1/2) q[55];
sx q[55];
rz(pi*1/2) q[55];
cz q[46], q[55];
rz(pi*1/2) q[46];
sx q[46];
rz(pi*1/2) q[46];
rz(pi*1/2) q[46];
rz(pi*1/2) q[46];
sx q[46];
rz(pi*1/2) q[46];
cz q[45], q[46];
rz(pi*1/2) q[46];
sx q[46];
rz(pi*1/2) q[46];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
cz q[46], q[45];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
rz(pi*1/2) q[46];
sx q[46];
rz(pi*1/2) q[46];
cz q[45], q[46];
rz(pi*1/2) q[46];
sx q[46];
rz(pi*1/2) q[46];
cz q[45], q[44];
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
cz q[44], q[43];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
rz(pi*-1/4) q[43];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
cz q[44], q[45];
rz(pi*1/4) q[44];
cz q[44], q[43];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
rz(pi*-1/4) q[45];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
cz q[44], q[45];
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
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
cz q[42], q[43];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
rz(pi*1/2) q[55];
sx q[55];
rz(pi*1/2) q[55];
if (c[9]) {
  x q[65];
}
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/4) q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
c[10] = measure q[66];
if (c[10]) {
  rz(pi*1/2) q[64];
}
if (c[10]) {
  sx q[64];
}
if (c[10]) {
  rz(pi*1/2) q[64];
}
if (c[10]) {
  cz q[65], q[64];
}
if (c[10]) {
  rz(pi*1/2) q[64];
}
if (c[10]) {
  sx q[64];
}
if (c[10]) {
  rz(pi*1/2) q[64];
}
if (c[10]) {
  rz(pi*1/2) q[65];
}
if (c[10]) {
  sx q[65];
}
if (c[10]) {
  rz(pi*1/2) q[65];
}
if (c[10]) {
  cz q[64], q[65];
}
if (c[10]) {
  rz(pi*1/2) q[65];
}
if (c[10]) {
  sx q[65];
}
if (c[10]) {
  rz(pi*1/2) q[65];
}
if (c[10]) {
  rz(pi*1/2) q[64];
}
if (c[10]) {
  sx q[64];
}
if (c[10]) {
  rz(pi*1/2) q[64];
}
if (c[10]) {
  cz q[65], q[64];
}
if (c[10]) {
  rz(pi*1/2) q[64];
}
if (c[10]) {
  sx q[64];
}
if (c[10]) {
  rz(pi*1/2) q[64];
}
if (c[10]) {
  rz(pi*1/2) q[67];
}
if (c[10]) {
  sx q[67];
}
if (c[10]) {
  rz(pi*1/2) q[67];
}
if (c[10]) {
  cz q[66], q[67];
}
if (c[10]) {
  rz(pi*1/2) q[67];
}
if (c[10]) {
  sx q[67];
}
if (c[10]) {
  rz(pi*1/2) q[67];
}
if (c[10]) {
  rz(pi*1/2) q[66];
}
if (c[10]) {
  sx q[66];
}
if (c[10]) {
  rz(pi*1/2) q[66];
}
if (c[10]) {
  cz q[67], q[66];
}
if (c[10]) {
  rz(pi*1/2) q[66];
}
if (c[10]) {
  sx q[66];
}
if (c[10]) {
  rz(pi*1/2) q[66];
}
if (c[10]) {
  rz(pi*1/2) q[67];
}
if (c[10]) {
  sx q[67];
}
if (c[10]) {
  rz(pi*1/2) q[67];
}
if (c[10]) {
  cz q[66], q[67];
}
if (c[10]) {
  rz(pi*1/2) q[67];
}
if (c[10]) {
  sx q[67];
}
if (c[10]) {
  rz(pi*1/2) q[67];
}
if (c[10]) {
  cz q[66], q[65];
}
if (c[10]) {
  rz(pi*1/2) q[64];
}
if (c[10]) {
  sx q[64];
}
if (c[10]) {
  rz(pi*1/2) q[64];
}
if (c[10]) {
  cz q[65], q[64];
}
if (c[10]) {
  rz(pi*1/2) q[64];
}
if (c[10]) {
  sx q[64];
}
if (c[10]) {
  rz(pi*1/2) q[64];
}
if (c[10]) {
  rz(pi*1/2) q[65];
}
if (c[10]) {
  sx q[65];
}
if (c[10]) {
  rz(pi*1/2) q[65];
}
if (c[10]) {
  cz q[64], q[65];
}
if (c[10]) {
  rz(pi*1/2) q[65];
}
if (c[10]) {
  sx q[65];
}
if (c[10]) {
  rz(pi*1/2) q[65];
}
if (c[10]) {
  rz(pi*1/2) q[64];
}
if (c[10]) {
  sx q[64];
}
if (c[10]) {
  rz(pi*1/2) q[64];
}
if (c[10]) {
  cz q[65], q[64];
}
if (c[10]) {
  rz(pi*1/2) q[64];
}
if (c[10]) {
  sx q[64];
}
if (c[10]) {
  rz(pi*1/2) q[64];
}
if (c[10]) {
  rz(pi*1/2) q[67];
}
if (c[10]) {
  sx q[67];
}
if (c[10]) {
  rz(pi*1/2) q[67];
}
if (c[10]) {
  cz q[66], q[67];
}
if (c[10]) {
  rz(pi*1/2) q[67];
}
if (c[10]) {
  sx q[67];
}
if (c[10]) {
  rz(pi*1/2) q[67];
}
if (c[10]) {
  rz(pi*1/2) q[66];
}
if (c[10]) {
  sx q[66];
}
if (c[10]) {
  rz(pi*1/2) q[66];
}
if (c[10]) {
  cz q[67], q[66];
}
if (c[10]) {
  rz(pi*1/2) q[66];
}
if (c[10]) {
  sx q[66];
}
if (c[10]) {
  rz(pi*1/2) q[66];
}
if (c[10]) {
  rz(pi*1/2) q[67];
}
if (c[10]) {
  sx q[67];
}
if (c[10]) {
  rz(pi*1/2) q[67];
}
if (c[10]) {
  cz q[66], q[67];
}
if (c[10]) {
  rz(pi*1/2) q[67];
}
if (c[10]) {
  sx q[67];
}
if (c[10]) {
  rz(pi*1/2) q[67];
}
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
x q[64];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
cz q[64], q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
cz q[63], q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
cz q[64], q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
cz q[64], q[65];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
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
cz q[64], q[65];
cz q[64], q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*-1/4) q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*1/4) q[64];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*-1/4) q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
cz q[64], q[65];
cz q[64], q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*1/2) q[62];
sx q[62];
rz(pi*1/2) q[62];
cz q[63], q[62];
rz(pi*1/2) q[62];
sx q[62];
rz(pi*1/2) q[62];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
cz q[62], q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*1/2) q[62];
sx q[62];
rz(pi*1/2) q[62];
cz q[63], q[62];
rz(pi*1/2) q[62];
sx q[62];
rz(pi*1/2) q[62];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
cz q[64], q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
cz q[63], q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
cz q[64], q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
if (c[10]) {
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
cz q[67], q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
cz q[67], q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
cz q[66], q[67];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
cz q[67], q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
cz q[68], q[67];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
cz q[67], q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*-1/4) q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/2) q[68];
sx q[68];
rz(pi*1/2) q[68];
cz q[67], q[68];
rz(pi*1/4) q[67];
cz q[67], q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/2) q[68];
sx q[68];
rz(pi*1/2) q[68];
rz(pi*-1/4) q[68];
rz(pi*1/2) q[68];
sx q[68];
rz(pi*1/2) q[68];
cz q[67], q[68];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
rz(pi*1/2) q[67];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
cz q[66], q[67];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
cz q[67], q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
cz q[66], q[67];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
cz q[65], q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
cz q[66], q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
cz q[65], q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
cz q[65], q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
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
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
cz q[64], q[65];
cz q[64], q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*-1/4) q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*1/4) q[64];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*-1/4) q[65];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
cz q[64], q[65];
cz q[64], q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
cz q[63], q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
cz q[64], q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
cz q[63], q[64];
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
cz q[62], q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*1/2) q[62];
sx q[62];
rz(pi*1/2) q[62];
cz q[63], q[62];
rz(pi*1/2) q[62];
sx q[62];
rz(pi*1/2) q[62];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
cz q[62], q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
rz(pi*1/2) q[62];
sx q[62];
rz(pi*1/2) q[62];
cz q[61], q[62];
rz(pi*1/2) q[62];
sx q[62];
rz(pi*1/2) q[62];
rz(pi*1/2) q[61];
sx q[61];
rz(pi*1/2) q[61];
cz q[62], q[61];
rz(pi*1/2) q[61];
sx q[61];
rz(pi*1/2) q[61];
rz(pi*1/2) q[62];
sx q[62];
rz(pi*1/2) q[62];
cz q[61], q[62];
rz(pi*1/2) q[62];
sx q[62];
rz(pi*1/2) q[62];
cz q[61], q[54];
rz(pi*1/2) q[54];
sx q[54];
rz(pi*1/2) q[54];
rz(pi*1/2) q[54];
sx q[54];
rz(pi*1/2) q[54];
cz q[42], q[54];
rz(pi*1/2) q[42];
sx q[42];
rz(pi*1/2) q[42];
rz(pi*1/2) q[54];
sx q[54];
rz(pi*1/2) q[54];
rz(pi*1/2) q[61];
sx q[61];
rz(pi*1/2) q[61];
cz q[54], q[61];
cz q[54], q[42];
rz(pi*1/2) q[42];
sx q[42];
rz(pi*1/2) q[42];
rz(pi*-1/4) q[42];
rz(pi*1/2) q[42];
sx q[42];
rz(pi*1/2) q[42];
rz(pi*1/4) q[54];
rz(pi*1/2) q[61];
sx q[61];
rz(pi*1/2) q[61];
rz(pi*-1/4) q[61];
rz(pi*1/2) q[61];
sx q[61];
rz(pi*1/2) q[61];
cz q[54], q[61];
cz q[54], q[42];
rz(pi*1/2) q[42];
sx q[42];
rz(pi*1/2) q[42];
rz(pi*1/2) q[54];
sx q[54];
rz(pi*1/2) q[54];
rz(pi*1/2) q[54];
rz(pi*1) q[54];
rz(pi*1/2) q[54];
sx q[54];
rz(pi*1/2) q[54];
rz(pi*1/2) q[61];
sx q[61];
rz(pi*1/2) q[61];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
rz(pi*1/2) q[68];
sx q[68];
rz(pi*1/2) q[68];
c[11] = measure q[54];
if (c[11]) {
  rz(pi*1/2) q[42];
}
if (c[11]) {
  sx q[42];
}
if (c[11]) {
  rz(pi*1/2) q[42];
}
if (c[11]) {
  cz q[54], q[42];
}
if (c[11]) {
  rz(pi*1/2) q[42];
}
if (c[11]) {
  sx q[42];
}
if (c[11]) {
  rz(pi*1/2) q[42];
}
if (c[11]) {
  rz(pi*1/2) q[54];
}
if (c[11]) {
  sx q[54];
}
if (c[11]) {
  rz(pi*1/2) q[54];
}
if (c[11]) {
  cz q[42], q[54];
}
if (c[11]) {
  rz(pi*1/2) q[54];
}
if (c[11]) {
  sx q[54];
}
if (c[11]) {
  rz(pi*1/2) q[54];
}
if (c[11]) {
  rz(pi*1/2) q[42];
}
if (c[11]) {
  sx q[42];
}
if (c[11]) {
  rz(pi*1/2) q[42];
}
if (c[11]) {
  cz q[54], q[42];
}
if (c[11]) {
  rz(pi*1/2) q[42];
}
if (c[11]) {
  sx q[42];
}
if (c[11]) {
  rz(pi*1/2) q[42];
}
if (c[11]) {
  cz q[61], q[54];
}
if (c[11]) {
  rz(pi*1/2) q[54];
}
if (c[11]) {
  sx q[54];
}
if (c[11]) {
  rz(pi*1/2) q[54];
}
if (c[11]) {
  cz q[42], q[54];
}
if (c[11]) {
  rz(pi*1/2) q[54];
}
if (c[11]) {
  sx q[54];
}
if (c[11]) {
  rz(pi*1/2) q[54];
}
if (c[11]) {
  rz(pi*1/2) q[42];
}
if (c[11]) {
  sx q[42];
}
if (c[11]) {
  rz(pi*1/2) q[42];
}
if (c[11]) {
  cz q[54], q[42];
}
if (c[11]) {
  rz(pi*1/2) q[42];
}
if (c[11]) {
  sx q[42];
}
if (c[11]) {
  rz(pi*1/2) q[42];
}
if (c[11]) {
  rz(pi*1/2) q[54];
}
if (c[11]) {
  sx q[54];
}
if (c[11]) {
  rz(pi*1/2) q[54];
}
if (c[11]) {
  cz q[42], q[54];
}
if (c[11]) {
  rz(pi*1/2) q[54];
}
if (c[11]) {
  sx q[54];
}
if (c[11]) {
  rz(pi*1/2) q[54];
}
rz(pi*1/2) q[42];
sx q[42];
rz(pi*1/2) q[42];
if (c[11]) {
  x q[54];
}
rz(pi*1/2) q[61];
sx q[61];
rz(pi*1/2) q[61];
c[12] = measure q[42];
if (c[12]) {
  cz q[44], q[45];
}
if (c[12]) {
  x q[42];
}
rz(pi*1/2) q[44];
sx q[44];
rz(pi*1/2) q[44];
rz(pi*1/2) q[45];
sx q[45];
rz(pi*1/2) q[45];
c[13] = measure q[61];
if (c[13]) {
  cz q[65], q[64];
}
if (c[13]) {
  x q[61];
}
rz(pi*1/2) q[64];
sx q[64];
rz(pi*1/2) q[64];
rz(pi*1/2) q[65];
sx q[65];
rz(pi*1/2) q[65];
c[14] = measure q[45];
if (c[14]) {
  cz q[46], q[55];
}
if (c[14]) {
  x q[45];
}
x q[46];
rz(pi*1/2) q[46];
sx q[46];
rz(pi*1/2) q[46];
x q[55];
rz(pi*1/2) q[55];
sx q[55];
rz(pi*1/2) q[55];
c[15] = measure q[44];
if (c[15]) {
  rz(pi*1/2) q[43];
}
if (c[15]) {
  sx q[43];
}
if (c[15]) {
  rz(pi*1/2) q[43];
}
if (c[15]) {
  cz q[44], q[43];
}
if (c[15]) {
  rz(pi*1/2) q[43];
}
if (c[15]) {
  sx q[43];
}
if (c[15]) {
  rz(pi*1/2) q[43];
}
if (c[15]) {
  rz(pi*1/2) q[44];
}
if (c[15]) {
  sx q[44];
}
if (c[15]) {
  rz(pi*1/2) q[44];
}
if (c[15]) {
  cz q[43], q[44];
}
if (c[15]) {
  rz(pi*1/2) q[44];
}
if (c[15]) {
  sx q[44];
}
if (c[15]) {
  rz(pi*1/2) q[44];
}
if (c[15]) {
  rz(pi*1/2) q[43];
}
if (c[15]) {
  sx q[43];
}
if (c[15]) {
  rz(pi*1/2) q[43];
}
if (c[15]) {
  cz q[44], q[43];
}
if (c[15]) {
  rz(pi*1/2) q[43];
}
if (c[15]) {
  sx q[43];
}
if (c[15]) {
  rz(pi*1/2) q[43];
}
if (c[15]) {
  cz q[35], q[44];
}
if (c[15]) {
  rz(pi*1/2) q[44];
}
if (c[15]) {
  sx q[44];
}
if (c[15]) {
  rz(pi*1/2) q[44];
}
if (c[15]) {
  cz q[43], q[44];
}
if (c[15]) {
  rz(pi*1/2) q[44];
}
if (c[15]) {
  sx q[44];
}
if (c[15]) {
  rz(pi*1/2) q[44];
}
if (c[15]) {
  rz(pi*1/2) q[43];
}
if (c[15]) {
  sx q[43];
}
if (c[15]) {
  rz(pi*1/2) q[43];
}
if (c[15]) {
  cz q[44], q[43];
}
if (c[15]) {
  rz(pi*1/2) q[43];
}
if (c[15]) {
  sx q[43];
}
if (c[15]) {
  rz(pi*1/2) q[43];
}
if (c[15]) {
  rz(pi*1/2) q[44];
}
if (c[15]) {
  sx q[44];
}
if (c[15]) {
  rz(pi*1/2) q[44];
}
if (c[15]) {
  cz q[43], q[44];
}
if (c[15]) {
  rz(pi*1/2) q[44];
}
if (c[15]) {
  sx q[44];
}
if (c[15]) {
  rz(pi*1/2) q[44];
}
x q[35];
rz(pi*1/2) q[35];
sx q[35];
rz(pi*1/2) q[35];
x q[43];
rz(pi*1/2) q[43];
sx q[43];
rz(pi*1/2) q[43];
if (c[15]) {
  x q[44];
}
c[16] = measure q[64];
c[17] = measure q[65];
if (c[16]) {
  rz(pi*1/2) q[63];
}
if (c[16]) {
  sx q[63];
}
if (c[16]) {
  rz(pi*1/2) q[63];
}
if (c[16]) {
  cz q[64], q[63];
}
if (c[16]) {
  rz(pi*1/2) q[63];
}
if (c[16]) {
  sx q[63];
}
if (c[16]) {
  rz(pi*1/2) q[63];
}
if (c[16]) {
  rz(pi*1/2) q[64];
}
if (c[16]) {
  sx q[64];
}
if (c[16]) {
  rz(pi*1/2) q[64];
}
if (c[16]) {
  cz q[63], q[64];
}
if (c[16]) {
  rz(pi*1/2) q[64];
}
if (c[16]) {
  sx q[64];
}
if (c[16]) {
  rz(pi*1/2) q[64];
}
if (c[16]) {
  rz(pi*1/2) q[63];
}
if (c[16]) {
  sx q[63];
}
if (c[16]) {
  rz(pi*1/2) q[63];
}
if (c[16]) {
  cz q[64], q[63];
}
if (c[16]) {
  rz(pi*1/2) q[63];
}
if (c[16]) {
  sx q[63];
}
if (c[16]) {
  rz(pi*1/2) q[63];
}
if (c[16]) {
  rz(pi*1/2) q[66];
}
if (c[16]) {
  sx q[66];
}
if (c[16]) {
  rz(pi*1/2) q[66];
}
if (c[16]) {
  cz q[65], q[66];
}
if (c[16]) {
  rz(pi*1/2) q[66];
}
if (c[16]) {
  sx q[66];
}
if (c[16]) {
  rz(pi*1/2) q[66];
}
if (c[16]) {
  rz(pi*1/2) q[65];
}
if (c[16]) {
  sx q[65];
}
if (c[16]) {
  rz(pi*1/2) q[65];
}
if (c[16]) {
  cz q[66], q[65];
}
if (c[16]) {
  rz(pi*1/2) q[65];
}
if (c[16]) {
  sx q[65];
}
if (c[16]) {
  rz(pi*1/2) q[65];
}
if (c[16]) {
  rz(pi*1/2) q[66];
}
if (c[16]) {
  sx q[66];
}
if (c[16]) {
  rz(pi*1/2) q[66];
}
if (c[16]) {
  cz q[65], q[66];
}
if (c[16]) {
  rz(pi*1/2) q[66];
}
if (c[16]) {
  sx q[66];
}
if (c[16]) {
  rz(pi*1/2) q[66];
}
if (c[16]) {
  cz q[65], q[64];
}
if (c[16]) {
  rz(pi*1/2) q[63];
}
if (c[16]) {
  sx q[63];
}
if (c[16]) {
  rz(pi*1/2) q[63];
}
if (c[16]) {
  cz q[64], q[63];
}
if (c[16]) {
  rz(pi*1/2) q[63];
}
if (c[16]) {
  sx q[63];
}
if (c[16]) {
  rz(pi*1/2) q[63];
}
if (c[16]) {
  rz(pi*1/2) q[64];
}
if (c[16]) {
  sx q[64];
}
if (c[16]) {
  rz(pi*1/2) q[64];
}
if (c[16]) {
  cz q[63], q[64];
}
if (c[16]) {
  rz(pi*1/2) q[64];
}
if (c[16]) {
  sx q[64];
}
if (c[16]) {
  rz(pi*1/2) q[64];
}
if (c[16]) {
  rz(pi*1/2) q[63];
}
if (c[16]) {
  sx q[63];
}
if (c[16]) {
  rz(pi*1/2) q[63];
}
if (c[16]) {
  cz q[64], q[63];
}
if (c[16]) {
  rz(pi*1/2) q[63];
}
if (c[16]) {
  sx q[63];
}
if (c[16]) {
  rz(pi*1/2) q[63];
}
if (c[16]) {
  rz(pi*1/2) q[66];
}
if (c[16]) {
  sx q[66];
}
if (c[16]) {
  rz(pi*1/2) q[66];
}
if (c[16]) {
  cz q[65], q[66];
}
if (c[16]) {
  rz(pi*1/2) q[66];
}
if (c[16]) {
  sx q[66];
}
if (c[16]) {
  rz(pi*1/2) q[66];
}
if (c[16]) {
  rz(pi*1/2) q[65];
}
if (c[16]) {
  sx q[65];
}
if (c[16]) {
  rz(pi*1/2) q[65];
}
if (c[16]) {
  cz q[66], q[65];
}
if (c[16]) {
  rz(pi*1/2) q[65];
}
if (c[16]) {
  sx q[65];
}
if (c[16]) {
  rz(pi*1/2) q[65];
}
if (c[16]) {
  rz(pi*1/2) q[66];
}
if (c[16]) {
  sx q[66];
}
if (c[16]) {
  rz(pi*1/2) q[66];
}
if (c[16]) {
  cz q[65], q[66];
}
if (c[16]) {
  rz(pi*1/2) q[66];
}
if (c[16]) {
  sx q[66];
}
if (c[16]) {
  rz(pi*1/2) q[66];
}
x q[63];
rz(pi*1/2) q[63];
sx q[63];
rz(pi*1/2) q[63];
if (c[16]) {
  x q[64];
}
x q[66];
rz(pi*1/2) q[66];
sx q[66];
rz(pi*1/2) q[66];
if (c[17]) {
  cz q[67], q[68];
}
if (c[17]) {
  x q[65];
}
x q[67];
rz(pi*1/2) q[67];
sx q[67];
rz(pi*1/2) q[67];
x q[68];
rz(pi*1/2) q[68];
sx q[68];
rz(pi*1/2) q[68];
