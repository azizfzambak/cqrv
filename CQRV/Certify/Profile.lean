module

public import Lean.Data.Json
public import CQRV.Grades.Profile
public import CQRV.Certify.Certificate

/-!
# CQRV.Certify.Profile

Report §3.3.2–3.3.3, §9.5.3 — reading a hardware profile file `profiles/<name>.json`
(`docs/profile.schema.json` v1.0.0; Stage 11b, DECISIONS.md 2026-10-26) for
`cqr certify --profile <name|path>`.

The reader enforces the schema's rules itself (the CLI has no JSON Schema validator): exactly
the keys of the schema; `schema_version` "1.0.0"; every number a natural number or `null`; `p_bar`
a decimal string in `[0, 1]` or `null`; and a non-empty `source` entry for every numeric field,
so that no figure enters without saying where it comes from. The profile hash is SHA3-256 of
the file text with LF line endings (as `predicate_hash`).
-/

@[expose] public section

namespace CQRV.Certify

open Lean

/-- The schema version of profile files. -/
def profileSchemaVersion : String := "1.0.0"

/-- The numeric fields of a profile; each needs a `source` entry. -/
def profileNumericFields : List String :=
  ["w", "d", "t", "a", "t_gate_ns", "t_T_ns", "t1_ns", "p_bar"]

/-- The keys of a profile object (`note` is optional). -/
def profileKeys : List String :=
  ["schema_version", "name", "note", "source", "budget", "t_gate_ns", "t_T_ns", "t1_ns", "p_bar"]

/-- The keys of a JSON object. -/
def objKeys (j : Json) : Except String (List String) := do
  let o ← j.getObj?
  return o.toList.map (·.1)

/-- A natural number or `null`. -/
def optNat (field : String) : Json → Except String (Option Nat)
  | .null => pure none
  | j => match j.getNat? with
    | .ok n => pure (some n)
    | .error _ => throw s!"profile: `{field}` must be a natural number or null"

/-- Report §3.3.3 — a profile from its JSON object (decision 1 of Stage 11b). -/
def profileOfJson (j : Json) : Except String Profile := do
  let keys ← objKeys j
  for k in keys do
    unless profileKeys.contains k do throw s!"profile: unknown key `{k}`"
  let field (k : String) : Except String Json :=
    (j.getObjVal? k).mapError fun _ => s!"profile: missing key `{k}`"
  let v ← (← field "schema_version").getStr?
  unless v == profileSchemaVersion do
    throw s!"profile: schema_version {v}, expected {profileSchemaVersion}"
  let name ← (← field "name").getStr?
  if name.isEmpty then throw "profile: empty name"
  let src ← field "source"
  for k in profileNumericFields do
    match src.getObjValAs? String k with
    | .ok s => if s.isEmpty then throw s!"profile: empty source for `{k}`"
    | .error _ => throw s!"profile: no source for `{k}` (every figure needs one)"
  for k in ← objKeys src do
    unless profileNumericFields.contains k do throw s!"profile: unknown source key `{k}`"
  let b ← field "budget"
  for k in ← objKeys b do
    unless ["w", "d", "t", "a"].contains k do throw s!"profile: unknown budget key `{k}`"
  let comp (k : String) : Except String (Option Nat) := do
    optNat s!"budget.{k}" (← (b.getObjVal? k).mapError fun _ => s!"profile: missing budget.{k}")
  let pBar ← match ← field "p_bar" with
    | .null => pure none
    | .str s => match parseDecimal s with
      | some p => if p ≤ 1 then pure (some p) else throw s!"profile: p_bar {s} > 1"
      | none => throw s!"profile: p_bar `{s}` is not a decimal string"
    | _ => throw "profile: p_bar must be a decimal string or null"
  return { name, budget := ⟨← comp "w", ← comp "d", ← comp "t", ← comp "a"⟩,
           tGateNs := ← optNat "t_gate_ns" (← field "t_gate_ns"),
           tTNs := ← optNat "t_T_ns" (← field "t_T_ns"),
           t1Ns := ← optNat "t1_ns" (← field "t1_ns"), pBar }

/-- `--profile <name|path>`: a path if it contains `/` or `\` or ends in `.json`, otherwise
`profiles/<name>.json` (relative to the project root, as `lean-toolchain`). -/
def profilePath (arg : String) : String :=
  if arg.contains '/' || arg.contains '\\' || arg.endsWith ".json" then arg
  else s!"profiles/{arg}.json"

/-- Report §9.5.3 — `profile_hash`: SHA3-256 of the profile file, line endings LF. -/
def profileHash (text : String) : String :=
  SHA3.sha3String (normalizeLF text)

/-- Read and check a profile; returns it with its hash. -/
def loadProfile (arg : String) : IO (Except String (Profile × String)) := do
  let path := profilePath arg
  unless ← System.FilePath.pathExists path do return .error s!"profile file {path} not found"
  let text ← IO.FS.readFile path
  return do
    let j ← (Json.parse text).mapError (s!"{path}: " ++ ·)
    let p ← (profileOfJson j).mapError (s!"{path}: " ++ ·)
    return (p, profileHash text)

end CQRV.Certify

end
