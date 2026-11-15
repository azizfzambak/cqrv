module

public import CQRV.Hardware.Decomp
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# CQRV.Hardware.Relabel

Report §5.3, §9.1.1; PHASE2_SPEC §C.3 step 2 (Stage 26b1, Track C) — renaming the qubits of gates
and circuits, Physlib-free: the data side of routing. A *qubit map* `f : Qubit → Qubit` is applied
to every operand (`Gate.map`, `Circuit.map`, `BasisGate.map`); two maps matter:

* **a permutation of the data qubits** of a register of width `N` (`Qubit.relabel N σ` for
  `σ : Equiv.Perm (Fin N)`, acting on `data i` with `i < N` and fixing everything else; the
  routing SWAP is `swapPerm N p q = Equiv.swap p q`);
* **the canonical placement** of the logical register on a flat physical register
  (`Qubit.place n`: `data i ↦ data i`, `anc j ↦ data (n + j)`), which lets a logical circuit on
  `Reg n × Reg a'` run on `Reg (n + a') × Reg 0`.

The physical register of Stage 26 is the compact register of the used qubits, with `nAnc = 0`:
a physical circuit is `⟨N, gates⟩` whose qubits are all `data i`, `i < N`. The proofs
(`gateU_map`, `channelDenote_map`, …) are in `CQRV.Hardware.Route`.
-/

@[expose] public section

namespace CQRV.Hardware

open CQRV

/-- Rename the operands of a gate (`ifBit` structurally). -/
def _root_.CQRV.Gate.map (f : Qubit → Qubit) : Gate → Gate
  | .h q => .h (f q)
  | .s q => .s (f q)
  | .sdg q => .sdg (f q)
  | .t q => .t (f q)
  | .tdg q => .tdg (f q)
  | .x q => .x (f q)
  | .z q => .z (f q)
  | .cnot c t => .cnot (f c) (f t)
  | .cz a b => .cz (f a) (f b)
  | .measure q j => .measure (f q) j
  | .ifBit j g => .ifBit j (g.map f)
  | .alloc q => .alloc (f q)
  | .free q => .free (f q)
  | .p a k q => .p a k (f q)
  | .cp a k c t => .cp a k (f c) (f t)

/-- Rename the operands of a basis gate. -/
def BasisGate.map (f : Qubit → Qubit) : BasisGate → BasisGate
  | .rz a k q => .rz a k (f q)
  | .sx q => .sx (f q)
  | .x q => .x (f q)
  | .cz a b => .cz (f a) (f b)
  | .cx c t => .cx (f c) (f t)
  | .measure q j => .measure (f q) j
  | .ifBit j g => .ifBit j (g.map f)

/-- The circuit with renamed operands on a register of `nData` data qubits. -/
def _root_.CQRV.Circuit.map (f : Qubit → Qubit) (nData : ℕ) (C : Circuit) : Circuit :=
  ⟨nData, C.gates.map (Gate.map f)⟩

theorem _root_.CQRV.Gate.map_qubits (f : Qubit → Qubit) (g : Gate) : (g.map f).qubits = g.qubits.map f := by
  induction g with
  | ifBit j g ih => simpa [Gate.map, Gate.qubits] using ih
  | _ => simp [Gate.map, Gate.qubits]

theorem _root_.CQRV.Gate.map_writes (f : Qubit → Qubit) (g : Gate) : (g.map f).writes = g.writes := by
  cases g <;> rfl

theorem _root_.CQRV.Gate.map_isClifford (f : Qubit → Qubit) (g : Gate) : (g.map f).isClifford = g.isClifford := by
  cases g <;> rfl

theorem BasisGate.expand_map (f : Qubit → Qubit) (bg : BasisGate) :
    (bg.map f).expand = bg.expand.map (Gate.map f) := by
  induction bg with
  | ifBit j g ih => simp [BasisGate.map, BasisGate.expand, ih, List.map_map, Function.comp_def, Gate.map]
  | _ => simp [BasisGate.map, BasisGate.expand, Gate.map]

/-! ## Permutations of the data qubits -/

/-- A permutation of `Fin N` as a function on `ℕ`, fixing `i ≥ N`. -/
def permFn (N : ℕ) (σ : Equiv.Perm (Fin N)) (i : ℕ) : ℕ :=
  if h : i < N then (σ ⟨i, h⟩).val else i

/-- The data qubits permuted by `σ`; the ancilla qubits fixed. -/
def _root_.CQRV.Qubit.relabel (N : ℕ) (σ : Equiv.Perm (Fin N)) : Qubit → Qubit
  | .data i => .data (permFn N σ i)
  | .anc i => .anc i

def _root_.CQRV.Gate.relabel (N : ℕ) (σ : Equiv.Perm (Fin N)) : Gate → Gate := Gate.map (Qubit.relabel N σ)

/-- The circuit with its data qubits permuted (the register unchanged). -/
def _root_.CQRV.Circuit.relabel (N : ℕ) (σ : Equiv.Perm (Fin N)) (C : Circuit) : Circuit :=
  ⟨C.nData, C.gates.map (Gate.relabel N σ)⟩

/-- The routing SWAP of data qubits `p` and `q`, as a permutation. -/
def swapPerm (N : ℕ) (p q : Fin N) : Equiv.Perm (Fin N) := Equiv.swap p q

/-! ## The canonical placement -/

/-- The logical register placed on a flat register: data qubit `i` stays, ancilla `j` becomes data
qubit `n + j`. -/
def _root_.CQRV.Qubit.place (n : ℕ) : Qubit → Qubit
  | .data i => .data i
  | .anc j => .data (n + j)

/-- A logical circuit on `n` data qubits and `a'` ancillae as a physical circuit on `n + a'` data
qubits and no ancilla. -/
def _root_.CQRV.Circuit.place (n a' : ℕ) (C : Circuit) : Circuit := Circuit.map (Qubit.place n) (n + a') C

/-! ## The ancilla count of the translation (the 26a open item)

`(translateCircuit b C).nAnc = C.nAnc` is **false in general**: `alloc` and `free` vanish in the
translation, so an ancilla that is only allocated and freed is lost — `⟨1, [alloc (anc 3)]⟩` has
`nAnc = 4` and its translation `⟨1, []⟩` has `nAnc = 0`. The corrected statement: the equality holds
when every ancilla of an `alloc` / `free` also occurs in a gate that is not bookkeeping
(`Circuit.ancCovered`, decidable), which is the case for every synthesized circuit (an allocated
ancilla is used). -/

/-- The contribution of a qubit to `nAnc`: `i + 1` for `anc i`, `0` for a data qubit. -/
def ancIdx : Qubit → ℕ
  | .anc i => i + 1
  | .data _ => 0

/-- `alloc` and `free`: the bookkeeping gates, which the translation drops (`ifBit` looks inside:
a conditioned bookkeeping gate never occurs in a well-formed circuit). -/
def _root_.CQRV.Gate.isBookkeeping : Gate → Bool
  | .alloc _ | .free _ => true
  | .ifBit _ g => g.isBookkeeping
  | _ => false

/-- The qubit of a bookkeeping gate (`ifBit` looks inside). -/
def _root_.CQRV.Gate.bookkeepingQubit : Gate → Option Qubit
  | .alloc q | .free q => some q
  | .ifBit _ g => g.bookkeepingQubit
  | _ => none

theorem bookkeepingQubit_of {g : Gate} (hb : g.isBookkeeping = true) :
    ∃ q₀, g.bookkeepingQubit = some q₀ ∧ g.qubits = [q₀] := by
  induction g with
  | ifBit j g ih =>
    obtain ⟨q₀, h1, h2⟩ := ih hb
    exact ⟨q₀, by simpa [Gate.bookkeepingQubit] using h1, by simpa [Gate.qubits] using h2⟩
  | alloc q => exact ⟨q, rfl, rfl⟩
  | free q => exact ⟨q, rfl, rfl⟩
  | _ => simp [Gate.isBookkeeping] at hb

theorem expansion_bookkeeping (b : TargetBasis) {g : Gate} (hb : g.isBookkeeping = true) :
    expansion b g = [] := by
  induction g with
  | ifBit j g ih => rw [expansion_ifBit, ih hb]; rfl
  | alloc q => rfl
  | free q => rfl
  | _ => simp [Gate.isBookkeeping] at hb

/-- Every ancilla of a bookkeeping gate occurs in a gate that is not bookkeeping. -/
def _root_.CQRV.Circuit.ancCovered (C : Circuit) : Bool :=
  C.gates.all fun g => match g.bookkeepingQubit with
    | some q => C.gates.any fun g' => !g'.isBookkeeping && decide (q ∈ g'.qubits)
    | none => true

theorem nAnc_eq_foldl (C : Circuit) :
    C.nAnc = (C.gates.flatMap Gate.qubits).foldl (fun m q => max m (ancIdx q)) 0 := by
  simp only [Circuit.nAnc]
  have step : ∀ (gs : List Gate) (m : ℕ),
      gs.foldl (fun m g => g.qubits.foldl (fun m q => match q with | .anc i => Nat.max m (i + 1) | .data _ => m) m) m =
        (gs.flatMap Gate.qubits).foldl (fun m q => max m (ancIdx q)) m := by
    intro gs
    induction gs with
    | nil => intro m; rfl
    | cons g gs ih =>
      intro m
      simp only [List.foldl_cons, List.flatMap_cons, List.foldl_append, ih]
      congr 1
      induction g.qubits generalizing m with
      | nil => rfl
      | cons q qs ihq => cases q <;> simp [List.foldl_cons, ancIdx, ihq]
  exact step C.gates 0

theorem foldl_max_eq_sup (l : List ℕ) (m : ℕ) : l.foldl max m = max m (l.toFinset.sup id) := by
  induction l generalizing m with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldl_cons, ih, List.toFinset_cons, Finset.sup_insert, id]
    omega

/-- `nAnc` depends only on the set of qubits that occur. -/
theorem nAnc_eq_sup (C : Circuit) :
    C.nAnc = ((C.gates.flatMap Gate.qubits).map ancIdx).toFinset.sup id := by
  rw [nAnc_eq_foldl]
  have : ∀ (l : List Qubit) (m : ℕ), l.foldl (fun m q => max m (ancIdx q)) m = (l.map ancIdx).foldl max m := by
    intro l; induction l with
    | nil => intro m; rfl
    | cons q l ih => intro m; simp [List.foldl_cons, ih]
  rw [this, foldl_max_eq_sup]
  simp

/-- The qubits of a non-bookkeeping gate's expansion are the gate's qubits (as sets). -/
theorem mem_qubits_expansion (b : TargetBasis) (g : Gate) (hg : g.isBookkeeping = false) (q : Qubit) :
    q ∈ (expansion b g).flatMap Gate.qubits ↔ q ∈ g.qubits := by
  induction g with
  | ifBit j g' ih =>
    have hg' : g'.isBookkeeping = false := hg
    rw [expansion_ifBit]
    simp only [Gate.qubits, List.flatMap_map]
    exact ih hg'
  | alloc _ => simp [Gate.isBookkeeping] at hg
  | free _ => simp [Gate.isBookkeeping] at hg
  | _ => cases b <;> simp [expansion, decompTable, hGates, cnotEntry, czEntry, pEntry, cpEntry,
      BasisGate.expand, Gate.qubits] <;> tauto

theorem mem_qubits_expansion_of_mem (b : TargetBasis) (g : Gate) (q : Qubit)
    (h : q ∈ (expansion b g).flatMap Gate.qubits) : q ∈ g.qubits := by
  cases hb : g.isBookkeeping
  · exact (mem_qubits_expansion b g hb q).mp h
  · rw [expansion_bookkeeping b hb] at h
    simp at h

/-- **The corrected ancilla count**: when every bookkeeping ancilla is covered, the translation has
the circuit's `nAnc`. -/
theorem nAnc_translate (b : TargetBasis) (C : Circuit) (h : C.ancCovered = true) :
    (translateCircuit b C).nAnc = C.nAnc := by
  rw [nAnc_eq_sup, nAnc_eq_sup]
  congr 1
  ext i
  simp only [List.mem_toFinset, List.mem_map, List.mem_flatMap, translateCircuit]
  constructor
  · rintro ⟨q, ⟨g', ⟨g, hg, hg'⟩, hq⟩, rfl⟩
    exact ⟨q, ⟨g, hg, mem_qubits_expansion_of_mem b g q (List.mem_flatMap.mpr ⟨g', hg', hq⟩)⟩, rfl⟩
  · rintro ⟨q, ⟨g, hg, hq⟩, rfl⟩
    cases hb : g.isBookkeeping
    · obtain ⟨g', hg', hq'⟩ := List.mem_flatMap.mp ((mem_qubits_expansion b g hb q).mpr hq)
      exact ⟨q, ⟨g', ⟨g, hg, hg'⟩, hq'⟩, rfl⟩
    · -- a bookkeeping gate: its qubit occurs in a covering gate
      have hc : ∃ g₂ ∈ C.gates, g₂.isBookkeeping = false ∧ q ∈ g₂.qubits := by
        simp only [Circuit.ancCovered, List.all_eq_true] at h
        have hg0 := h g hg
        obtain ⟨q₀, hq₀, hqs⟩ := bookkeepingQubit_of hb
        rw [hq₀] at hg0
        rw [hqs, List.mem_singleton] at hq
        subst hq
        simp only [List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hg0
        obtain ⟨g₂, hg₂, hb₂, hq₂⟩ := hg0
        exact ⟨g₂, hg₂, hb₂, hq₂⟩
      obtain ⟨g₂, hg₂, hb₂, hq₂⟩ := hc
      obtain ⟨g', hg', hq'⟩ := List.mem_flatMap.mp ((mem_qubits_expansion b g₂ hb₂ q).mpr hq₂)
      exact ⟨q, ⟨g', ⟨g₂, hg₂, hg'⟩, hq'⟩, rfl⟩

end CQRV.Hardware
