module

/-!
# CQRV.Certify.SHA3

Report §8.4.2, §9.5.3 (certificate hashes) — SHA3-256 (FIPS 202) in Lean, so that hashing stays
inside the single-language trusted base (DECISIONS.md 2026-10-21, planning decision (3); Stage 8a
reviewer decision 1): Keccak-f[1600] on 25 little-endian 64-bit lanes, sponge with rate
136 bytes, SHA3 domain padding `0x06 … 0x80` (`0x86` when only one pad byte fits), 32-byte
output. Python `hashlib.sha3_256` is only a test oracle (`tests/diff/sha3_diff.py`).
-/

@[expose] public section

namespace CQRV.Certify.SHA3

/-- FIPS 202 §3.2.5 — the 24 round constants of ι. -/
def roundConstants : Array UInt64 := #[
  0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
  0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
  0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
  0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
  0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
  0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- FIPS 202 §3.2.2 — the ρ rotation offsets, indexed by lane `x + 5y`. -/
def rotations : Array UInt64 := #[
  0, 1, 62, 28, 27,
  36, 44, 6, 55, 20,
  3, 10, 43, 25, 39,
  41, 45, 15, 21, 8,
  18, 2, 61, 56, 14]

/-- Left rotation of a lane (`n < 64`; `n = 0` gives `v`). -/
def rotl (v n : UInt64) : UInt64 := (v <<< n) ||| (v >>> (64 - n))

/-- FIPS 202 §3.3 — one round θ, ρ, π, χ, ι on the state `a` (25 lanes, index `x + 5y`). -/
def round (a : Array UInt64) (rc : UInt64) : Array UInt64 := Id.run do
  -- θ
  let c : Array UInt64 := Array.ofFn fun (x : Fin 5) =>
    a[x.val]! ^^^ a[x.val + 5]! ^^^ a[x.val + 10]! ^^^ a[x.val + 15]! ^^^ a[x.val + 20]!
  let d : Array UInt64 := Array.ofFn fun (x : Fin 5) =>
    c[(x.val + 4) % 5]! ^^^ rotl c[(x.val + 1) % 5]! 1
  let a := Array.ofFn fun (i : Fin 25) => a[i.val]! ^^^ d[i.val % 5]!
  -- ρ and π: B[y, 2x + 3y] = rot(A[x, y], r[x, y])
  let mut b : Array UInt64 := Array.replicate 25 0
  for i in [0:25] do
    let x := i % 5
    let y := i / 5
    b := b.set! (y + 5 * ((2 * x + 3 * y) % 5)) (rotl a[i]! rotations[i]!)
  -- χ, then ι
  let a := Array.ofFn fun (i : Fin 25) =>
    let x := i.val % 5
    let y := i.val / 5
    b[i.val]! ^^^ (~~~ b[(x + 1) % 5 + 5 * y]! &&& b[(x + 2) % 5 + 5 * y]!)
  return a.set! 0 (a[0]! ^^^ rc)

/-- FIPS 202 §3.4 — Keccak-f[1600]: 24 rounds. -/
def keccakF (a : Array UInt64) : Array UInt64 :=
  roundConstants.foldl round a

/-- The sponge rate of SHA3-256 in bytes (`1600 − 2·256` bits). -/
def rate : Nat := 136

/-- FIPS 202 §6.1, B.2 — SHA3 padding: append `0x06`, zeros, and set the high bit of the last
byte of the block (`0x86` when the message needs a single pad byte). The result's size is a
positive multiple of `rate`. -/
def pad (m : ByteArray) : ByteArray := Id.run do
  let k := rate - m.size % rate
  let mut out := m.push 0x06
  for _ in [1:k] do out := out.push 0
  return out.set! (out.size - 1) (out.get! (out.size - 1) ||| 0x80)

/-- The little-endian 64-bit lane `j` of a block starting at byte `off`. -/
def lane (m : ByteArray) (off j : Nat) : UInt64 :=
  (List.range 8).foldl (fun v k => v ||| ((m.get! (off + 8 * j + k)).toUInt64 <<< (8 * k).toUInt64)) 0

/-- Report §9.5.3 — SHA3-256 of a byte string (32 bytes). -/
def sha3_256 (m : ByteArray) : ByteArray := Id.run do
  let p := pad m
  let mut s : Array UInt64 := Array.replicate 25 0
  for blk in [0:p.size / rate] do
    for j in [0:rate / 8] do
      s := s.set! j (s[j]! ^^^ lane p (blk * rate) j)
    s := keccakF s
  let mut out := ByteArray.empty
  for j in [0:4] do
    for k in [0:8] do
      out := out.push ((s[j]! >>> (8 * k).toUInt64).toUInt8)
  return out

/-- Lower-case hexadecimal rendering of a byte string. -/
def toHex (b : ByteArray) : String :=
  let digit (n : UInt8) : Char := "0123456789abcdef".toList[n.toNat]!
  String.ofList (b.toList.flatMap fun (x : UInt8) => [digit (x >>> 4), digit (x &&& 0x0f)])

/-- Report §9.5.3 — SHA3-256 of a byte string, as 64 lower-case hex digits. -/
def sha3_256Hex (m : ByteArray) : String := toHex (sha3_256 m)

/-- SHA3-256 of the UTF-8 encoding of a string, as hex. -/
def sha3String (s : String) : String := sha3_256Hex s.toUTF8

end CQRV.Certify.SHA3

end
