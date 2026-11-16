module

public import CQRV.Hardware.Reorder

/-!
# CQRV.Hardware.WitnessSound

Report §5.3, §9.1.1; PHASE2_SPEC §C.3 step 3 (Stage 26b3, Track C) — the soundness of the
reconstruction `applyWitness` (`CQRV.Hardware.Witness`), Physlib-side.

* **Step lists.** `runSteps` (data side) produces basis gates from a layout list; here the same
  steps are read at the IR level under a permutation `τ` of the physical register (`irRun`): the
  layout list `layOf N k τ` is `τ` on the first `k` canonical positions, and `swapLay` against a
  SWAP is `swapPermN N p q * τ` (`swapLay_layOf`, `runSteps_snd`, `runSteps_fst`).
* **`irRun_kraus`**, the migration: the Kraus operators of a run equal, up to a unit scalar per
  branch, those of the logical gates relabeled by the initial layout followed by all the SWAPs
  (`krausOps_swap_migrate` step by step, the blocks through their own soundness).
* **`applyBlock_sound`**: a block's physical gates are, up to a unit scalar per branch, the
  members relabeled by the layout at the block (the SWAPs composing to the identity collapse to a
  scalar; the member order undone by `krausOps_reorder`); the conditioned form through the bit.
* **`applyWitness_sound`**: `channelDenote N 0 (physCircuit N G) (embed b σ₀ ρ) =
  embed b σ_f (channelDenote n a C ρ)` with `σ_f = irPerm steps * σ₀`, by the five steps of
  PHASE2_SPEC "26b2 done"; then `AncRestore.phys` and `realizes_phys`.
-/

@[expose] public section

open CQRV Matrix
open scoped MState

namespace CQRV.Hardware

noncomputable section

/-! ## Permutations of the physical register -/

section Perms

variable {N : ℕ}

theorem permFn_one (i : ℕ) : permFn N (1 : Equiv.Perm (Fin N)) i = i := by
  unfold permFn; split_ifs <;> rfl

theorem permFn_mul (σ τ : Equiv.Perm (Fin N)) (i : ℕ) :
    permFn N (σ * τ) i = permFn N σ (permFn N τ i) := by
  unfold permFn
  by_cases hi : i < N
  · simp [hi]
  · simp [hi]

theorem permFn_lt_of_lt (σ : Equiv.Perm (Fin N)) {i : ℕ} (hi : i < N) : permFn N σ i < N := by
  rw [permFn_lt σ hi]; exact (σ ⟨i, hi⟩).isLt

theorem qubitRelabel_mul (σ τ : Equiv.Perm (Fin N)) (q : Qubit) :
    Qubit.relabel N (σ * τ) q = Qubit.relabel N σ (Qubit.relabel N τ q) := by
  cases q <;> simp [Qubit.relabel, permFn_mul]

theorem gateMap_map (f g : Qubit → Qubit) (x : Gate) : Gate.map f (Gate.map g x) = Gate.map (f ∘ g) x := by
  induction x with
  | ifBit j x ih => simp [Gate.map, ih]
  | _ => simp [Gate.map]

theorem gateMap_congr {f g : Qubit → Qubit} (x : Gate) (h : ∀ q ∈ x.qubits, f q = g q) :
    Gate.map f x = Gate.map g x := by
  induction x with
  | ifBit j x ih => simp only [Gate.map]; rw [ih (by simpa [Gate.qubits] using h)]
  | _ => simp_all [Gate.map, Gate.qubits]

theorem gateRelabel_mul (σ τ : Equiv.Perm (Fin N)) (g : Gate) :
    Gate.relabel N (σ * τ) g = Gate.relabel N σ (Gate.relabel N τ g) := by
  simp only [Gate.relabel, gateMap_map]
  exact gateMap_congr g fun q _ => qubitRelabel_mul σ τ q

theorem gateMap_isUnitary (f : Qubit → Qubit) (g : Gate) : (g.map f).isUnitary = g.isUnitary := by
  cases g <;> rfl

theorem gateMap_ifBit (f : Qubit → Qubit) (j : ℕ) (g : Gate) :
    Gate.map f (.ifBit j g) = .ifBit j (Gate.map f g) := rfl

/-- The SWAP of two physical positions as a permutation (`1` outside the register). -/
def swapPermN (N p q : ℕ) : Equiv.Perm (Fin N) :=
  if h : p < N ∧ q < N then swapPerm N ⟨p, h.1⟩ ⟨q, h.2⟩ else 1

theorem swapPermN_eq {p q : ℕ} (hp : p < N) (hq : q < N) :
    swapPermN N p q = swapPerm N ⟨p, hp⟩ ⟨q, hq⟩ := by
  simp [swapPermN, hp, hq]

theorem permFn_swapPermN {p q : ℕ} (hp : p < N) (hq : q < N) (x : ℕ) :
    permFn N (swapPermN N p q) x = if x = p then q else if x = q then p else x := by
  rw [swapPermN_eq hp hq]
  unfold permFn
  by_cases hx : x < N
  · simp only [hx, ↓reduceDIte, swapPerm, Equiv.swap_apply_def]
    by_cases hxp : x = p
    · subst hxp; simp
    · by_cases hxq : x = q
      · subst hxq; simp [hxp]
      · have h1 : (⟨x, hx⟩ : Fin N) ≠ ⟨p, hp⟩ := fun h => hxp (Fin.mk.inj_iff.mp h)
        have h2 : (⟨x, hx⟩ : Fin N) ≠ ⟨q, hq⟩ := fun h => hxq (Fin.mk.inj_iff.mp h)
        simp [h1, h2, hxp, hxq]
  · have hxp : x ≠ p := fun h => hx (h ▸ hp)
    have hxq : x ≠ q := fun h => hx (h ▸ hq)
    simp [hx, hxp, hxq]

theorem permMat_one : permMat (N := N) (A := 0) (1 : Equiv.Perm (Fin N)) = 1 := by
  rw [permMat, ← monoMat_id_one]; rfl

theorem stateEquiv_mul (σ τ : Equiv.Perm (Fin N)) :
    stateEquiv (A := 0) (σ * τ) = (stateEquiv σ).trans (stateEquiv τ) := by
  ext u <;> rfl

theorem permMat_mul (σ τ : Equiv.Perm (Fin N)) :
    permMat (A := 0) (σ * τ) = permMat σ * permMat τ := by
  rw [permMat, permMat, permMat, monoMat_mul]
  congr 1
  funext u; simp

end Perms

/-! ## Layouts as permutations -/

section Layouts

variable {N : ℕ}

/-- The layout list of the first `k` canonical positions under `τ`. -/
def layOf (N k : ℕ) (τ : Equiv.Perm (Fin N)) : List ℕ := (List.range k).map (permFn N τ)

theorem layOf_getD (k : ℕ) (τ : Equiv.Perm (Fin N)) {i : ℕ} (hi : i < k) (d : ℕ) :
    (layOf N k τ).getD i d = permFn N τ i := by
  simp [layOf, List.getD_eq_getElem?_getD, hi]

theorem layOf_length (k : ℕ) (τ : Equiv.Perm (Fin N)) : (layOf N k τ).length = k := by
  simp [layOf]

theorem layOf_one (N : ℕ) : layOf N N 1 = List.range N := by
  simp only [layOf]
  rw [List.map_congr_left (fun i _ => permFn_one i)]
  simp

theorem swapLay_layOf (k : ℕ) (τ : Equiv.Perm (Fin N)) {p q : ℕ} (hp : p < N) (hq : q < N) :
    swapLay (layOf N k τ) p q = layOf N k (swapPermN N p q * τ) := by
  simp only [swapLay, layOf, List.map_map]
  congr 1
  funext i
  simp only [Function.comp]
  rw [permFn_mul, permFn_swapPermN hp hq]

theorem layoutQ_layOf (n a : ℕ) (τ : Equiv.Perm (Fin N)) {q : Qubit} (hq : q.inRange n a = true) :
    layoutQ n (layOf N (n + a) τ) q = Qubit.relabel N τ (Qubit.place n q) := by
  cases q with
  | data i =>
    have hi : i < n := by simpa [Qubit.inRange] using hq
    simp only [layoutQ, canonPos]
    rw [layOf_getD _ _ (show i < n + a by omega)]
    rfl
  | anc j =>
    have hj : j < a := by simpa [Qubit.inRange] using hq
    simp only [layoutQ, canonPos]
    rw [layOf_getD _ _ (show n + j < n + a by omega)]
    rfl

theorem mem_qubits_expand {bg : BasisGate} {q : Qubit} (h : q ∈ bg.expand.flatMap Gate.qubits) :
    q ∈ bg.qubits := by
  induction bg with
  | ifBit j g ih =>
    simp only [BasisGate.expand, List.flatMap_map, Gate.qubits] at h
    exact ih h
  | _ => simp_all [BasisGate.expand, BasisGate.qubits, Gate.qubits]

theorem expand_flatMap_map (f : Qubit → Qubit) (gs : List BasisGate) :
    (gs.map (BasisGate.map f)).flatMap BasisGate.expand = (gs.flatMap BasisGate.expand).map (Gate.map f) := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [List.flatMap_cons, BasisGate.expand_map, ih]

theorem expand_flatMap_ifBit (j : ℕ) (gs : List BasisGate) :
    (gs.map (BasisGate.ifBit j)).flatMap BasisGate.expand = (gs.flatMap BasisGate.expand).map (Gate.ifBit j) := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [List.flatMap_cons, BasisGate.expand, ih]

end Layouts

/-! ## Step lists at the IR level -/

section Steps

variable (b : TargetBasis) (n : ℕ) {N : ℕ}

/-- The IR gates of the table's SWAP entry on the physical positions `p`, `q`. -/
def swapIR (p q : ℕ) : List Gate := (swapEntry b (.data p) (.data q)).gates.flatMap BasisGate.expand

/-- Logical basis gates as IR gates on the flat register, at the canonical positions. -/
def placedIR (gs : List BasisGate) : List Gate :=
  (gs.flatMap BasisGate.expand).map (Gate.map (Qubit.place n))

theorem placedIR_append (gs gs' : List BasisGate) :
    placedIR n (gs ++ gs') = placedIR n gs ++ placedIR n gs' := by
  simp [placedIR, List.flatMap_append]

/-- The physical IR gates of a step list under the layout permutation `τ`. -/
def irRun (N : ℕ) : List PStep → Equiv.Perm (Fin N) → List Gate
  | [], _ => []
  | .swap p q :: rest, τ => swapIR b p q ++ irRun N rest (swapPermN N p q * τ)
  | .place gs :: rest, τ => (placedIR n gs).map (Gate.relabel N τ) ++ irRun N rest τ
  | .block _ P :: rest, τ => P.flatMap BasisGate.expand ++ irRun N rest τ

/-- The logical basis gates of a step list, in order. -/
def irLogB : List PStep → List BasisGate
  | [] => []
  | .swap _ _ :: rest => irLogB rest
  | .place gs :: rest => gs ++ irLogB rest
  | .block L _ :: rest => L ++ irLogB rest

/-- The SWAP gates of a step list, in order. -/
def irSwaps : List PStep → List Gate
  | [] => []
  | .swap p q :: rest => swapIR b p q ++ irSwaps rest
  | .place _ :: rest => irSwaps rest
  | .block _ _ :: rest => irSwaps rest

/-- The permutation the SWAPs of a step list compose to (applied in order). -/
def irPerm (N : ℕ) : List PStep → Equiv.Perm (Fin N)
  | [] => 1
  | .swap p q :: rest => irPerm N rest * swapPermN N p q
  | .place _ :: rest => irPerm N rest
  | .block _ _ :: rest => irPerm N rest

/-- Kraus equality up to a unit scalar per branch, on the physical register. -/
def KEq (N m : ℕ) (X Y : List Gate) : Prop :=
  ∀ c : Fin m → Bool, ∃ z : ℂ, star z * z = 1 ∧ krausOps N 0 m X c = z • krausOps N 0 m Y c

theorem KEq.refl (N m : ℕ) (X : List Gate) : KEq N m X X := fun _ => ⟨1, by simp, by simp⟩

/-- The side conditions of a step list under the layout `τ`: SWAPs of distinct positions inside the
register; placed gates on the logical register; blocks sound at their layouts. -/
def StepsOk (N n a : ℕ) : List PStep → Equiv.Perm (Fin N) → Prop
  | [], _ => True
  | .swap p q :: rest, τ => p ≠ q ∧ p < N ∧ q < N ∧ StepsOk N n a rest (swapPermN N p q * τ)
  | .place gs :: rest, τ => (∀ bg ∈ gs, ∀ q ∈ bg.qubits, q.inRange n a = true) ∧ StepsOk N n a rest τ
  | .block L P :: rest, τ =>
    (∀ m, KEq N m (P.flatMap BasisGate.expand) ((placedIR n L).map (Gate.relabel N τ))) ∧
      StepsOk N n a rest τ

theorem StepsOk_append (a : ℕ) (s₁ s₂ : List PStep) (τ : Equiv.Perm (Fin N)) :
    StepsOk N n a (s₁ ++ s₂) τ ↔ StepsOk N n a s₁ τ ∧ StepsOk N n a s₂ (irPerm N s₁ * τ) := by
  induction s₁ generalizing τ with
  | nil => simp [StepsOk, irPerm]
  | cons s rest ih =>
    cases s with
    | swap p q => simp only [List.cons_append, StepsOk, irPerm, ih, mul_assoc]; tauto
    | place gs => simp only [List.cons_append, StepsOk, irPerm, ih]; tauto
    | block L P => simp only [List.cons_append, StepsOk, irPerm, ih]; tauto

theorem irPerm_append (s₁ s₂ : List PStep) : irPerm N (s₁ ++ s₂) = irPerm N s₂ * irPerm N s₁ := by
  induction s₁ with
  | nil => simp [irPerm]
  | cons s rest ih => cases s <;> simp [irPerm, ih, mul_assoc]

theorem irLogB_append (s₁ s₂ : List PStep) : irLogB (s₁ ++ s₂) = irLogB s₁ ++ irLogB s₂ := by
  induction s₁ with
  | nil => rfl
  | cons s rest ih => cases s <;> simp [irLogB, ih]

/-- The layout after a run is the initial one permuted by the SWAPs. -/
theorem runSteps_snd (a : ℕ) (steps : List PStep) (k : ℕ) (τ : Equiv.Perm (Fin N))
    (h : StepsOk N n a steps τ) :
    (runSteps b n steps (layOf N k τ)).2 = layOf N k (irPerm N steps * τ) := by
  induction steps generalizing τ with
  | nil => simp [runSteps, irPerm]
  | cons s rest ih =>
    cases s with
    | swap p q =>
      obtain ⟨_, hp, hq, hrest⟩ := h
      simp only [runSteps, irPerm, swapLay_layOf k τ hp hq, ih _ hrest, mul_assoc]
    | place gs => simp only [runSteps, irPerm, ih _ h.2]
    | block L P => simp only [runSteps, irPerm, ih _ h.2]

/-- The gates of a run, expanded, are the IR run. -/
theorem runSteps_fst (a : ℕ) (steps : List PStep) (τ : Equiv.Perm (Fin N))
    (h : StepsOk N n a steps τ) :
    (runSteps b n steps (layOf N (n + a) τ)).1.flatMap BasisGate.expand = irRun b n N steps τ := by
  induction steps generalizing τ with
  | nil => rfl
  | cons s rest ih =>
    cases s with
    | swap p q =>
      obtain ⟨_, hp, hq, hrest⟩ := h
      simp only [runSteps, irRun, List.flatMap_append, swapLay_layOf _ τ hp hq, ih _ hrest, swapIR]
    | place gs =>
      obtain ⟨hgs, hrest⟩ := h
      simp only [runSteps, irRun, List.flatMap_append, ih _ hrest, expand_flatMap_map, placedIR,
        List.map_map]
      congr 1
      apply List.map_congr_left
      intro g hg
      simp only [Function.comp]
      rw [Gate.relabel, gateMap_map]
      apply gateMap_congr
      intro q hq
      obtain ⟨bg, hbg, hgbg⟩ := List.mem_flatMap.mp hg
      exact layoutQ_layOf n a τ (hgs bg hbg q (mem_qubits_expand (List.mem_flatMap.mpr ⟨g, hgbg, hq⟩)))
    | block L P =>
      obtain ⟨_, hrest⟩ := h
      simp only [runSteps, irRun, List.flatMap_append, ih _ hrest]

theorem swapIR_eq (p q : ℕ) (hp : p < N) (hq : q < N) :
    swapIR b p q = (swapEntry b (.data (⟨p, hp⟩ : Fin N).val) (.data (⟨q, hq⟩ : Fin N).val)).gates.flatMap
      BasisGate.expand := rfl

/-- **The migration over a step list**: the Kraus operators of a run are, up to a unit scalar per
branch, those of the logical gates relabeled by the initial layout, followed by all the SWAPs. -/
theorem irRun_kraus (a m : ℕ) (steps : List PStep) (τ : Equiv.Perm (Fin N))
    (h : StepsOk N n a steps τ) :
    KEq N m (irRun b n N steps τ) ((placedIR n (irLogB steps)).map (Gate.relabel N τ) ++ irSwaps b steps) := by
  induction steps generalizing τ with
  | nil => simpa [irRun, irLogB, irSwaps, placedIR] using KEq.refl N m []
  | cons s rest ih =>
    cases s with
    | swap p q =>
      obtain ⟨hpq, hp, hq, hrest⟩ := h
      intro c
      obtain ⟨z, hz, hk⟩ := ih _ hrest c
      refine ⟨z, hz, ?_⟩
      simp only [irRun, irLogB, irSwaps]
      rw [krausOps_append_list, hk, Matrix.smul_mul, ← krausOps_append_list]
      congr 1
      -- the relabeling by `swapPermN * τ` is the relabeling by `τ` then by the SWAP
      have hL : (placedIR n (irLogB rest)).map (Gate.relabel N (swapPermN N p q * τ)) =
          ((placedIR n (irLogB rest)).map (Gate.relabel N τ)).map (Gate.relabel N (swapPermN N p q)) := by
        rw [List.map_map]; apply List.map_congr_left; intro g _; exact gateRelabel_mul _ _ g
      rw [hL, ← List.append_assoc, krausOps_append_list, swapPermN_eq hp hq, swapIR_eq b p q hp hq,
        krausOps_swap_migrate (A := 0) b ⟨p, hp⟩ ⟨q, hq⟩ (fun h => hpq (Fin.mk.inj_iff.mp h)),
        ← krausOps_append_list, List.append_assoc]
    | place gs =>
      obtain ⟨_, hrest⟩ := h
      intro c
      obtain ⟨z, hz, hk⟩ := ih _ hrest c
      refine ⟨z, hz, ?_⟩
      simp only [irRun, irLogB, irSwaps, placedIR_append, List.map_append, List.append_assoc]
      rw [krausOps_append_list, hk, Matrix.smul_mul, ← krausOps_append_list]
    | block L P =>
      obtain ⟨hblk, hrest⟩ := h
      intro c
      obtain ⟨z, hz, hk⟩ := ih _ hrest c
      obtain ⟨y, hy, hky⟩ := hblk m c
      refine ⟨z * y, ?_, ?_⟩
      · calc star (z * y) * (z * y) = (star z * z) * (star y * y) := by rw [star_mul]; ring
          _ = 1 := by rw [hz, hy, one_mul]
      · simp only [irRun, irLogB, irSwaps, placedIR_append, List.map_append, List.append_assoc]
        rw [krausOps_append_list, hk, hky, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
          ← krausOps_append_list]

end Steps

/-! ## Monadic plumbing -/

section Plumbing

theorem exceptBind_ok {α β : Type} {x : Except String α} {f : α → Except String β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => simp [bind, Except.bind] at h
  | ok a => exact ⟨a, rfl, h⟩

theorem ensure_ok {c : Bool} {msg : String} {u : Unit} (h : ensure c msg = .ok u) : c = true := by
  cases c <;> simp [ensure] at h ⊢

theorem exceptPure_ok {α : Type} {a y : α} (h : (pure a : Except String α) = .ok y) : a = y := by
  simpa [pure, Except.pure] using h

end Plumbing

/-! ## Conditioned lists, unitary runs, the SWAP product -/

section Cond

variable {N : ℕ}

theorem krausOps_map_ifBit_false {m : ℕ} (c : Fin m → Bool) (j : ℕ) (hb : bitVal c j = false)
    (X : List Gate) : krausOps N 0 m (X.map (Gate.ifBit j)) c = 1 := by
  induction X with
  | nil => rfl
  | cons g X ih => simp [krausOps, gateK, hb, ih]

theorem krausOps_map_ifBit_true {m : ℕ} (c : Fin m → Bool) (j : ℕ) (hb : bitVal c j = true)
    (X : List Gate) (hX : X.all Gate.isUnitary = true) :
    krausOps N 0 m (X.map (Gate.ifBit j)) c = krausOps N 0 m X c := by
  induction X with
  | nil => rfl
  | cons g X ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hX
    simp only [List.map_cons, krausOps, ih hX.2]
    rw [gateK_of_unitary N 0 c g hX.1]
    simp [gateK, hb]

theorem swapIR_unitary (b : TargetBasis) (p q : ℕ) : (swapIR b p q).all Gate.isUnitary = true := by
  cases b <;> simp [swapIR, swapEntry, cnotEntry, hGates, BasisGate.expand, Gate.isUnitary]

/-- The SWAP conditions alone. -/
def SwapsOk (N : ℕ) : List PStep → Prop
  | [] => True
  | .swap p q :: rest => p ≠ q ∧ p < N ∧ q < N ∧ SwapsOk N rest
  | .place _ :: rest => SwapsOk N rest
  | .block _ _ :: rest => SwapsOk N rest

theorem StepsOk.swapsOk {n a : ℕ} {steps : List PStep} {τ : Equiv.Perm (Fin N)}
    (h : StepsOk N n a steps τ) : SwapsOk N steps := by
  induction steps generalizing τ with
  | nil => trivial
  | cons s rest ih =>
    cases s with
    | swap p q => exact ⟨h.1, h.2.1, h.2.2.1, ih h.2.2.2⟩
    | place gs => exact ih h.2
    | block L P => exact ih h.2

theorem irSwaps_unitary (b : TargetBasis) (steps : List PStep) :
    (irSwaps b steps).all Gate.isUnitary = true := by
  induction steps with
  | nil => rfl
  | cons s rest ih =>
    cases s with
    | swap p q => simp only [irSwaps, List.all_append, Bool.and_eq_true]; exact ⟨swapIR_unitary b p q, ih⟩
    | place gs => exact ih
    | block L P => exact ih

/-- The SWAPs of a step list compose, as a unitary, to a unit scalar times the permutation matrix
of `irPerm`. -/
theorem ud_irSwaps (b : TargetBasis) (steps : List PStep) (h : SwapsOk N steps) :
    ∃ ν : ℂ, star ν * ν = 1 ∧ unitaryDenote N 0 (irSwaps b steps) = ν • permMat (irPerm N steps) := by
  induction steps with
  | nil => exact ⟨1, by simp, by simp [irSwaps, unitaryDenote, irPerm, permMat_one]⟩
  | cons s rest ih =>
    cases s with
    | swap p q =>
      obtain ⟨hpq, hp, hq, hrest⟩ := h
      obtain ⟨ν, hν, hud⟩ := ih hrest
      have hne : (⟨p, hp⟩ : Fin N) ≠ ⟨q, hq⟩ := fun h => hpq (Fin.mk.inj_iff.mp h)
      refine ⟨ν * phaseQ (swapEntry b (.data p) (.data q)).irPhase, ?_, ?_⟩
      · calc star (ν * phaseQ (swapEntry b (.data p) (.data q)).irPhase) *
              (ν * phaseQ (swapEntry b (.data p) (.data q)).irPhase)
            = (star ν * ν) * (star (phaseQ (swapEntry b (.data p) (.data q)).irPhase) *
                phaseQ (swapEntry b (.data p) (.data q)).irPhase) := by rw [star_mul]; ring
          _ = 1 := by rw [hν, star_phaseQ_mul, one_mul]
      · simp only [irSwaps, irPerm]
        rw [unitaryDenote_append, hud, swapIR_eq b p q hp hq, ud_swapEntry N 0 b ⟨p, hp⟩ ⟨q, hq⟩ hne,
          Matrix.smul_mul, Matrix.mul_smul, smul_smul, permMat_mul, swapPermN_eq hp hq]
    | place gs => simpa [irSwaps, irPerm] using ih h
    | block L P => simpa [irSwaps, irPerm] using ih h

/-- A step list of SWAPs and placed gates whose expansions are Clifford (no blocks). -/
def PlacedClifford : List PStep → Prop
  | [] => True
  | .swap _ _ :: rest => PlacedClifford rest
  | .place gs :: rest => (∀ bg ∈ gs, bg.expand.all Gate.isClifford = true) ∧ PlacedClifford rest
  | .block _ _ :: _ => False

theorem irRun_unitary (b : TargetBasis) (n : ℕ) (steps : List PStep) (τ : Equiv.Perm (Fin N))
    (h : PlacedClifford steps) : (irRun b n N steps τ).all Gate.isUnitary = true := by
  induction steps generalizing τ with
  | nil => rfl
  | cons s rest ih =>
    cases s with
    | swap p q =>
      simp only [irRun, List.all_append, Bool.and_eq_true]
      exact ⟨swapIR_unitary b p q, ih _ h⟩
    | place gs =>
      obtain ⟨hgs, hrest⟩ := h
      simp only [irRun, List.all_append, Bool.and_eq_true]
      refine ⟨?_, ih _ hrest⟩
      simp only [placedIR, List.map_map, List.all_map, List.all_eq_true, Function.comp]
      intro g hg
      obtain ⟨bg, hbg, hgbg⟩ := List.mem_flatMap.mp hg
      rw [Gate.relabel, gateMap_map, gateMap_isUnitary]
      exact isUnitary_of_isClifford g (List.all_eq_true.mp (hgs bg hbg) g hgbg)
    | block L P => exact h.elim

/-- From the layout check on the whole register: the SWAPs compose to the identity. -/
theorem irPerm_eq_one (b : TargetBasis) (n a : ℕ) (steps : List PStep) (h : StepsOk N n a steps 1)
    (hr : (runSteps b n steps (List.range N)).2 = List.range N) : irPerm N steps = 1 := by
  rw [← layOf_one N, runSteps_snd b n a steps N 1 h, mul_one] at hr
  ext x
  have := congrArg (fun l => l.getD x.val 0) hr
  simp only [layOf_getD _ _ x.isLt, permFn_lt _ x.isLt] at this
  simpa using this

end Cond

/-! ## The reordering with an interpretation -/

section ReorderInterp

variable {n a : ℕ}

/-- `krausOps_reorder` for elements of any type read through `interp`: independent elements have
Kraus operators on disjoint qubits. -/
theorem krausOps_reorder_interp {α : Type} [DecidableEq α] (qs : α → List Qubit) (bs : α → List ℕ)
    (interp : α → List Gate) {m : ℕ} (l l' : List α)
    (hind : ∀ x ∈ l, ∀ y ∈ l, indep qs bs x y = true →
      ∀ q ∈ (interp x).flatMap Gate.qubits, q ∉ (interp y).flatMap Gate.qubits)
    (h : validReorder qs bs l l' = true) (c : Fin m → Bool) :
    krausOps n a m (l'.flatMap interp) c = krausOps n a m (l.flatMap interp) c := by
  induction l' generalizing l with
  | nil =>
    simp only [validReorder, List.isEmpty_iff] at h
    subst h
    rfl
  | cons x rest ih =>
    simp only [validReorder] at h
    cases hs : splitFirst x l with
    | none => rw [hs] at h; simp at h
    | some p =>
      obtain ⟨pre, post⟩ := p
      rw [hs] at h
      simp only [Bool.and_eq_true] at h
      have hl := splitFirst_spec hs
      have hind' : ∀ x ∈ pre ++ post, ∀ y ∈ pre ++ post, indep qs bs x y = true →
          ∀ q ∈ (interp x).flatMap Gate.qubits, q ∉ (interp y).flatMap Gate.qubits := by
        intro x' hx' y hy
        apply hind
        · rw [hl]; simp only [List.mem_append, List.mem_cons] at hx' ⊢; tauto
        · rw [hl]; simp only [List.mem_append, List.mem_cons] at hy ⊢; tauto
      rw [hl, List.flatMap_cons, List.flatMap_append, List.flatMap_cons,
        krausOps_append_list, krausOps_append_list, krausOps_append_list, ih (pre ++ post) hind' h.2,
        List.flatMap_append, krausOps_append_list]
      have hcomm : krausOps n a m (pre.flatMap interp) c * krausOps n a m (interp x) c =
          krausOps n a m (interp x) c * krausOps n a m (pre.flatMap interp) c := by
        apply krausOps_comm_of_disjoint
        intro q hq hq'
        obtain ⟨g, hg, hqg⟩ := List.mem_flatMap.mp hq
        obtain ⟨y, hy, hgy⟩ := List.mem_flatMap.mp hg
        have hx : x ∈ l := by rw [hl]; simp
        have hy' : y ∈ l := by rw [hl]; simp [hy]
        exact hind x hx y hy' (List.all_eq_true.mp h.1 y hy) q hq' (List.mem_flatMap.mpr ⟨g, hgy, hqg⟩)
      rw [Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc]

end ReorderInterp

/-! ## The block -/

section Block

variable (b : TargetBasis) (n a : ℕ) {N : ℕ}

theorem stripIf_qubits (bg : BasisGate) : bg.stripIf.qubits = bg.qubits := by
  cases bg <;> rfl

theorem stripIf_ifBit (j : ℕ) (bg : BasisGate) : (BasisGate.ifBit j bg).stripIf = bg := rfl

/-- The IR gates of a member, stripped of its condition, placed and laid out. -/
def memberIR (τ : Equiv.Perm (Fin N)) (T : List BasisGate) (k : ℕ) : List Gate :=
  (((T.getD k default).stripIf.expand).map (Gate.map (Qubit.place n))).map (Gate.relabel N τ)

theorem placedIR_map_relabel (τ : Equiv.Perm (Fin N)) (T : List BasisGate) (ks : List ℕ) :
    (placedIR n (ks.map fun k => (T.getD k default).stripIf)).map (Gate.relabel N τ) =
      ks.flatMap (memberIR n τ T) := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    rw [List.map_cons, List.flatMap_cons, ← ih, ← List.singleton_append, placedIR_append,
      List.map_append]
    congr 1
    simp [placedIR, memberIR]

/-- The members of a conditioned block, placed and laid out, are the stripped members under the
condition. -/
theorem placedIR_members (τ : Equiv.Perm (Fin N)) (T : List BasisGate) (j : ℕ) (ks : List ℕ)
    (hks : ∀ k ∈ ks, ∃ bg, T[k]? = some (.ifBit j bg)) :
    (placedIR n (ks.map fun k => T.getD k default)).map (Gate.relabel N τ) =
      (ks.flatMap (memberIR n τ T)).map (Gate.ifBit j) := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    obtain ⟨bg, hbg⟩ := hks k (List.mem_cons_self ..)
    have hT : T.getD k default = .ifBit j bg := by simp [List.getD_eq_getElem?_getD, hbg]
    rw [List.map_cons, List.flatMap_cons, ← List.singleton_append, placedIR_append, List.map_append,
      ih fun k hk => hks k (List.mem_cons_of_mem _ hk), List.map_append]
    congr 1
    simp only [placedIR, memberIR, hT, stripIf_ifBit, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, BasisGate.expand, List.map_map]
    apply List.map_congr_left
    intro g _
    simp [Function.comp, Gate.relabel, gateMap_ifBit]

theorem memberIR_unitary (τ : Equiv.Perm (Fin N)) (T : List BasisGate) (ks : List ℕ)
    (hcl : ∀ k ∈ ks, (T.getD k default).stripIf.expand.all Gate.isClifford = true) :
    (ks.flatMap (memberIR n τ T)).all Gate.isUnitary = true := by
  simp only [List.all_eq_true, List.mem_flatMap, memberIR, List.mem_map, forall_exists_index, and_imp]
  rintro g k hk g₁ g₀ hg₀ rfl rfl
  rw [Gate.relabel, gateMap_isUnitary, gateMap_isUnitary]
  exact isUnitary_of_isClifford g₀ (List.all_eq_true.mp (hcl k hk) g₀ hg₀)

/-- The steps of a block body satisfy the side conditions at every layout, and their logical gates
are the stripped members in the body's order. -/
theorem blockSteps_ok (T : List BasisGate) (members : List ℕ) (body : List BlockEntry)
    (steps : List PStep) (h : blockSteps N T members body = .ok steps)
    (hT : ∀ bg ∈ T, ∀ q ∈ bg.qubits, q.inRange n a = true)
    (hcl : ∀ k ∈ members, (T.getD k default).stripIf.expand.all Gate.isClifford = true) :
    (∀ τ : Equiv.Perm (Fin N), StepsOk N n a steps τ) ∧ PlacedClifford steps ∧
      irLogB steps = (body.filterMap fun e => match e with | .gate k => some k | .swap _ _ => none).map
        fun k => (T.getD k default).stripIf := by
  induction body generalizing steps with
  | nil =>
    simp only [blockSteps] at h
    rw [← exceptPure_ok h]
    exact ⟨fun _ => trivial, trivial, rfl⟩
  | cons e es ih =>
    simp only [blockSteps] at h
    obtain ⟨s, he, h⟩ := exceptBind_ok h
    obtain ⟨ss, hes, h⟩ := exceptBind_ok h
    rw [← exceptPure_ok h]
    obtain ⟨ih1, ih2, ih3⟩ := ih ss hes
    cases e with
    | gate k =>
      simp only [blockEntryStep] at he
      by_cases hk : members.contains k = true
      · simp only [hk, ↓reduceIte] at he
        cases hTk : T[k]? with
        | none => rw [hTk] at he; simp at he
        | some bg =>
          rw [hTk] at he
          rw [← exceptPure_ok he]
          have hmem : k ∈ members := by simpa using hk
          have hbg : T.getD k default = bg := by simp [List.getD_eq_getElem?_getD, hTk]
          refine ⟨fun τ => ⟨?_, ih1 τ⟩, ⟨?_, ih2⟩, ?_⟩
          · intro bg' hbg' q hq
            simp only [List.mem_singleton] at hbg'
            subst hbg'
            rw [stripIf_qubits] at hq
            exact hT bg (List.mem_of_getElem? hTk) q hq
          · intro bg' hbg'
            simp only [List.mem_singleton] at hbg'
            subst hbg'
            have := hcl k hmem
            rwa [hbg] at this
          · simp [irLogB, ih3, List.getD_eq_getElem?_getD, hTk]
      · simp only [hk] at he; simp at he
    | swap p q =>
      simp only [blockEntryStep] at he
      by_cases hpq : p = q
      · simp only [hpq, ↓reduceIte] at he; simp at he
      · simp only [hpq, ↓reduceIte] at he
        by_cases hr : p < N ∧ q < N
        · simp only [hr, and_self, ↓reduceIte] at he
          rw [← exceptPure_ok he]
          exact ⟨fun τ => ⟨hpq, hr.1, hr.2, ih1 _⟩, ih2, by simpa [irLogB, List.filterMap_cons] using ih3⟩
        · simp only [hr, ↓reduceIte] at he; simp at he

/-- **The block is sound**: its physical gates are, up to a unit scalar per branch, the members
(conditioned, in the circuit's order) placed and relabeled by the layout at the block. -/
theorem applyBlock_sound (τ : Equiv.Perm (Fin N)) (T : List BasisGate) (j : ℕ) (members : List ℕ)
    (body : List BlockEntry) (L P : List BasisGate)
    (h : applyBlock b n N T j members body (layOf N (n + a) τ) = .ok (L, P))
    (hT : ∀ bg ∈ T, ∀ q ∈ bg.qubits, q.inRange n a = true)
    (hmem : ∀ k ∈ members, ∃ bg, T[k]? = some (.ifBit j bg) ∧ bg.expand.all Gate.isClifford = true) :
    L = members.map (fun k => T.getD k default) ∧
      ∀ m, KEq N m (P.flatMap BasisGate.expand) ((placedIR n L).map (Gate.relabel N τ)) := by
  simp only [applyBlock] at h
  obtain ⟨steps, hs, h⟩ := exceptBind_ok h
  obtain ⟨_, hlay, h⟩ := exceptBind_ok h
  obtain ⟨_, hrange, h⟩ := exceptBind_ok h
  obtain ⟨_, hvalid, h⟩ := exceptBind_ok h
  have hLP := exceptPure_ok h
  simp only [Prod.mk.injEq] at hLP
  obtain ⟨rfl, rfl⟩ := hLP
  have hrange' : (runSteps b n steps (List.range N)).2 = List.range N := beq_iff_eq.mp (ensure_ok hrange)
  have hcl : ∀ k ∈ members, (T.getD k default).stripIf.expand.all Gate.isClifford = true := by
    intro k hk
    obtain ⟨bg, hbg, hc⟩ := hmem k hk
    simp [List.getD_eq_getElem?_getD, hbg, stripIf_ifBit, hc]
  obtain ⟨hok, hpc, hlog⟩ := blockSteps_ok n a T members body steps hs hT hcl
  have hperm : irPerm N steps = 1 := irPerm_eq_one b n a steps (hok 1) hrange'
  refine ⟨rfl, fun m c => ?_⟩
  -- the physical gates: the run under the condition
  have hP : ((runSteps b n steps (layOf N (n + a) τ)).1.map (BasisGate.ifBit j)).flatMap BasisGate.expand =
      (irRun b n N steps τ).map (Gate.ifBit j) := by
    rw [expand_flatMap_ifBit, runSteps_fst b n a steps τ (hok τ)]
  -- the logical gates: the members under the condition
  have hL : (placedIR n (members.map fun k => T.getD k default)).map (Gate.relabel N τ) =
      (members.flatMap (memberIR n τ T)).map (Gate.ifBit j) :=
    placedIR_members n τ T j members fun k hk => (hmem k hk).imp fun _ h => h.1
  rw [hP, hL]
  have hmemT : ∀ k ∈ members, T.getD k default ∈ T := by
    intro k hk
    obtain ⟨bg, hbg, _⟩ := hmem k hk
    have : T.getD k default = .ifBit j bg := by simp [List.getD_eq_getElem?_getD, hbg]
    rw [this]; exact List.mem_of_getElem? hbg
  -- independence of members transfers to their placed and laid-out gates
  have hind : ∀ x ∈ members, ∀ y ∈ members,
      indep (fun k => (T.getD k default).qubits) (fun _ => ([] : List ℕ)) x y = true →
      ∀ q ∈ (memberIR n τ T x).flatMap Gate.qubits, q ∉ (memberIR n τ T y).flatMap Gate.qubits := by
    intro x hx y hy hxy q hqx hqy
    simp only [indep, disjointL, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not] at hxy
    simp only [memberIR, List.flatMap_map, List.mem_flatMap, Gate.relabel, Gate.map_qubits,
      List.mem_map] at hqx hqy
    obtain ⟨g, hg, q₀, ⟨a₀, ha₀, rfl⟩, rfl⟩ := hqx
    obtain ⟨g', hg', q₁, ⟨a₁, ha₁, rfl⟩, hq⟩ := hqy
    have hx0 : a₀ ∈ (T.getD x default).qubits := by
      rw [← stripIf_qubits]; exact mem_qubits_expand (List.mem_flatMap.mpr ⟨g, hg, ha₀⟩)
    have hy1 : a₁ ∈ (T.getD y default).qubits := by
      rw [← stripIf_qubits]; exact mem_qubits_expand (List.mem_flatMap.mpr ⟨g', hg', ha₁⟩)
    have hr0 : a₀.inRange n a = true := hT _ (hmemT x hx) a₀ hx0
    have hr1 : a₁.inRange n a = true := hT _ (hmemT y hy) a₁ hy1
    have : a₁ = a₀ := place_inj n a hr1 hr0 (relabel_injective τ hq)
    subst this
    exact hxy.1 a₁ hx0 hy1
  -- the taken members are a valid reordering of all members
  have hvalid' := ensure_ok hvalid
  have hreord : krausOps N 0 m ((body.filterMap fun e => match e with | .gate k => some k | .swap _ _ => none).flatMap
      (memberIR n τ T)) c = krausOps N 0 m (members.flatMap (memberIR n τ T)) c :=
    krausOps_reorder_interp (n := N) (a := 0) _ _ (memberIR n τ T) members _ hind hvalid' c
  by_cases hb : bitVal c j = true
  · rw [krausOps_map_ifBit_true c j hb _ (irRun_unitary b n steps τ hpc),
      krausOps_map_ifBit_true c j hb _ (memberIR_unitary n τ T members hcl)]
    obtain ⟨z, hz, hk⟩ := irRun_kraus b n a m steps τ (hok τ) c
    obtain ⟨ν, hν, hud⟩ := ud_irSwaps b steps (hok τ).swapsOk
    refine ⟨z * ν, ?_, ?_⟩
    · calc star (z * ν) * (z * ν) = (star z * z) * (star ν * ν) := by rw [star_mul]; ring
        _ = 1 := by rw [hz, hν, one_mul]
    · rw [hk, krausOps_append_list, krausOps_of_unitary N 0 m _ (irSwaps_unitary b steps), hud, hperm,
        permMat_one, hlog, placedIR_map_relabel, hreord, Matrix.smul_mul, one_mul, smul_smul]
  · rw [Bool.not_eq_true] at hb
    exact ⟨1, by simp, by rw [krausOps_map_ifBit_false c j hb, krausOps_map_ifBit_false c j hb, one_smul]⟩

end Block

/-! ## The elements of the translated circuit -/

section Elements

variable (b : TargetBasis)

/-- The logical basis gates of an element. -/
def Elem.gates (T : List BasisGate) : Elem → List BasisGate
  | .plain k => [T.getD k default]
  | .block _ ms => ms.map fun k => T.getD k default

theorem Elem.qubits_eq (T : List BasisGate) (e : Elem) :
    Elem.qubits T e = (Elem.gates T e).flatMap BasisGate.qubits := by
  cases e <;> simp [Elem.qubits, Elem.gates, List.flatMap_map]

theorem map_getD_range {α : Type} [Inhabited α] (E : List α) :
    (List.range E.length).map (fun i => E.getD i default) = E := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem flatMap_singleton_map {α β : Type} (l : List α) (f : α → β) :
    l.flatMap (fun x => [f x]) = l.map f := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, ih]

theorem getD_append_offset {α : Type} (T₀ X : List α) {k : ℕ} (hk : T₀.length = k) (i : ℕ) (d : α) :
    (T₀ ++ X).getD (i + k) d = X.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (show T₀.length ≤ i + k by omega), hk]

theorem getElem?_append_offset {α : Type} (T₀ X : List α) {k : ℕ} (hk : T₀.length = k) (i : ℕ) :
    (T₀ ++ X)[i + k]? = X[i]? := by
  simp [List.getElem?_append_right (show T₀.length ≤ i + k by omega), hk]

/-- The elements of one gate at the offset `k`. -/
def elemsOf (g : Gate) (k : ℕ) : List Elem :=
  match g with
  | .ifBit j _ => [.block j (List.range (decompTable b g).gates.length |>.map (· + k))]
  | _ => List.range (decompTable b g).gates.length |>.map fun i => Elem.plain (i + k)

theorem elements_go_cons (g : Gate) (gs : List Gate) (k : ℕ) :
    elements.go b (g :: gs) k = elemsOf b g k ++ elements.go b gs (k + (decompTable b g).gates.length) := by
  cases g <;> rfl

theorem qubits_subset_expand {bg : BasisGate} {q : Qubit} (h : q ∈ bg.qubits) :
    q ∈ bg.expand.flatMap Gate.qubits := by
  induction bg with
  | ifBit j g ih => simp only [BasisGate.expand, BasisGate.qubits, List.flatMap_map, Gate.qubits] at h ⊢; exact ih h
  | _ => simp_all [BasisGate.expand, BasisGate.qubits, Gate.qubits]

/-- The specification of `elements.go`: the elements enumerate the translated gates in order, their
gates are translated gates, and a block's members are the conditioned Clifford gates of its
source. -/
theorem elements_go_spec (gs : List Gate) (k : ℕ) (T₀ : List BasisGate) (hk : T₀.length = k)
    (hcl : ∀ g ∈ gs, ∀ j g', g = .ifBit j g' → g'.isClifford = true) :
    ((elements.go b gs k).flatMap (Elem.gates (T₀ ++ gs.flatMap fun g => (decompTable b g).gates)) =
        gs.flatMap fun g => (decompTable b g).gates) ∧
      (∀ e ∈ elements.go b gs k, ∀ bg ∈ Elem.gates (T₀ ++ gs.flatMap fun g => (decompTable b g).gates) e,
        bg ∈ T₀ ++ gs.flatMap fun g => (decompTable b g).gates) ∧
      (∀ e ∈ elements.go b gs k, ∀ j ms, e = .block j ms → ∀ k' ∈ ms,
        ∃ bg, (T₀ ++ gs.flatMap fun g => (decompTable b g).gates)[k']? = some (.ifBit j bg) ∧
          bg.expand.all Gate.isClifford = true) := by
  induction gs generalizing k T₀ with
  | nil => simp [elements.go]
  | cons g gs ih =>
    rw [elements_go_cons]
    set E := (decompTable b g).gates with hE
    have hlen : (T₀ ++ E).length = k + E.length := by simp [hk]
    obtain ⟨ih1, ih2, ih3⟩ := ih (k + E.length) (T₀ ++ E) hlen
      (fun g' hg' => hcl g' (List.mem_cons_of_mem _ hg'))
    simp only [List.flatMap_cons, List.append_assoc] at ih1 ih2 ih3 ⊢
    -- the gates of the elements of `g` are `E`
    have hgetD : ∀ i, i < E.length → (T₀ ++ (E ++ gs.flatMap fun g => (decompTable b g).gates)).getD (i + k) default =
        E.getD i default := by
      intro i hi
      rw [getD_append_offset T₀ _ hk, List.getD_eq_getElem?_getD, List.getElem?_append_left hi,
        ← List.getD_eq_getElem?_getD]
    have hgates : (elemsOf b g k).flatMap
        (Elem.gates (T₀ ++ (E ++ gs.flatMap fun g => (decompTable b g).gates))) = E := by
      have key : (List.range E.length).map (fun i =>
          (T₀ ++ (E ++ gs.flatMap fun g => (decompTable b g).gates)).getD (i + k) default) = E := by
        rw [List.map_congr_left (fun i hi => hgetD i (List.mem_range.mp hi)), map_getD_range]
      cases g <;> simp only [elemsOf, hE, List.flatMap_cons, List.flatMap_nil, List.append_nil, Elem.gates,
        List.map_map, Function.comp_def, List.flatMap_map] <;>
        first | exact key | (rw [flatMap_singleton_map]; exact key)
    refine ⟨?_, ?_, ?_⟩
    · rw [List.flatMap_append, hgates, ih1]
    · intro e he bg hbg
      rcases List.mem_append.mp he with he | he
      · have : bg ∈ (elemsOf b g k).flatMap
            (Elem.gates (T₀ ++ (E ++ gs.flatMap fun g => (decompTable b g).gates))) :=
          List.mem_flatMap.mpr ⟨e, he, hbg⟩
        rw [hgates] at this
        exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl this)))
      · exact ih2 e he bg hbg
    · intro e he j ms hems k' hk'
      rcases List.mem_append.mp he with he | he
      · -- an element of `g`: a block only when `g` is conditioned
        cases g with
        | ifBit j' g' =>
          simp only [elemsOf, List.mem_singleton] at he
          subst he
          simp only [Elem.block.injEq] at hems
          obtain ⟨hj, hms⟩ := hems
          subst hms
          rw [← hj]
          simp only [List.mem_map, List.mem_range] at hk'
          obtain ⟨i, hi, rfl⟩ := hk'
          have hcl' : g'.isClifford = true := hcl _ (List.mem_cons_self ..) j' g' rfl
          have hall := isClifford_expansion b g' hcl'
          rw [getElem?_append_offset T₀ _ hk, List.getElem?_append_left hi]
          have hi' : i < (decompTable b g').gates.length := by simpa [hE, decompTable] using hi
          have hEi : E[i]? = some (.ifBit j' ((decompTable b g').gates.getD i default)) := by
            simp [hE, decompTable, List.getElem?_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
          refine ⟨_, hEi, ?_⟩
          simp only [expansion, List.all_eq_true, List.mem_flatMap] at hall ⊢
          intro x hx
          have hmemi : (decompTable b g').gates.getD i default ∈ (decompTable b g').gates := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']; exact List.getElem_mem hi'
          exact hall x ⟨_, hmemi, hx⟩
        | _ =>
          simp only [elemsOf, List.mem_map] at he
          obtain ⟨i, _, hi⟩ := he
          rw [← hi] at hems
          cases hems
      · exact ih3 e he j ms hems k' hk'

/-- The specification of `elements b C` for a well-formed circuit. -/
theorem elements_spec (C : Circuit) (hC : C.WF) :
    ((elements b C).flatMap (Elem.gates (translate b C)) = translate b C) ∧
      (∀ e ∈ elements b C, ∀ bg ∈ Elem.gates (translate b C) e, bg ∈ translate b C) ∧
      (∀ e ∈ elements b C, ∀ j ms, e = .block j ms → ∀ k ∈ ms,
        ∃ bg, (translate b C)[k]? = some (.ifBit j bg) ∧ bg.expand.all Gate.isClifford = true) := by
  have := elements_go_spec b C.gates 0 [] rfl hC.clifford
  simpa [elements, translate] using this

/-- Every qubit of the translation lies on the logical register `Reg C.nData × Reg C.nAnc`. -/
theorem translate_inRange (C : Circuit) (hC : C.WF) :
    ∀ bg ∈ translate b C, ∀ q ∈ bg.qubits, q.inRange C.nData C.nAnc = true := by
  intro bg hbg q hq
  obtain ⟨g, hg, hbgg⟩ := List.mem_flatMap.mp hbg
  have hqg : q ∈ g.qubits := by
    apply mem_qubits_expansion_of_mem b g q
    simp only [expansion, List.mem_flatMap]
    obtain ⟨x, hx, hqx⟩ := List.mem_flatMap.mp (qubits_subset_expand hq)
    exact ⟨x, ⟨bg, hbgg, hx⟩, hqx⟩
  cases q with
  | data i =>
    have := hC.qubitsOk g hg
    simp only [Gate.qubitsOk, Bool.and_eq_true, List.all_eq_true] at this
    have := this.1 _ hqg
    simpa [Qubit.inRange] using this
  | anc i =>
    simpa [Qubit.inRange] using Circuit.anc_lt_nAnc hg hqg

theorem inRange_of_WF (C : Circuit) (hC : C.WF) :
    ∀ g ∈ C.gates, ∀ q ∈ g.qubits, q.inRange C.nData C.nAnc = true := by
  intro g hg q hq
  cases q with
  | data i =>
    have := hC.qubitsOk g hg
    simp only [Gate.qubitsOk, Bool.and_eq_true, List.all_eq_true] at this
    have := this.1 _ hq
    simpa [Qubit.inRange] using this
  | anc i => simpa [Qubit.inRange] using Circuit.anc_lt_nAnc hg hq

theorem ancsBelow_translate (C : Circuit) : ancsBelow (translateCircuit b C).gates C.nAnc = true := by
  simp only [ancsBelow, translateCircuit, List.all_eq_true, List.mem_flatMap]
  rintro g' ⟨g, hg, hg'⟩ q hq
  have hqg : q ∈ g.qubits := mem_qubits_expansion_of_mem b g q (List.mem_flatMap.mpr ⟨g', hg', hq⟩)
  cases q with
  | data i => rfl
  | anc i => simpa [Qubit.ancBelow] using Circuit.anc_lt_nAnc hg hqg

end Elements

/-! ## The fold over `order` -/

section Fold

variable (b : TargetBasis) (C : Circuit) (w : Witness) {N : ℕ}

/-- The invariant of the fold: the layout is the initial permutation moved by the SWAPs so far,
the logical gates of the steps are those of the taken elements, the steps satisfy their side
conditions, and the taken elements are elements. -/
structure FoldInv (σ₀ : Equiv.Perm (Fin N)) (st : ApplyState) : Prop where
  lay : st.lay = layOf N (C.nData + C.nAnc) (irPerm N st.steps * σ₀)
  log : irLogB st.steps = st.taken.flatMap (Elem.gates (translate b C))
  ok : StepsOk N C.nData C.nAnc st.steps σ₀
  mem : ∀ e ∈ st.taken, e ∈ elements b C

theorem foldInv_init (σ₀ : Equiv.Perm (Fin N)) (h₀ : w.initial = layOf N (C.nData + C.nAnc) σ₀) :
    FoldInv b C σ₀ ⟨w.initial, [], []⟩ :=
  ⟨by simp [irPerm, h₀], rfl, trivial, fun _ h => by simp at h⟩

theorem orderStep_inv (hC : C.WF) (σ₀ : Equiv.Perm (Fin N)) (st st' : ApplyState) (e : OrderEntry)
    (hinv : FoldInv b C σ₀ st)
    (h : orderStep b C.nData N (translate b C) (elements b C) w st e = .ok st') :
    FoldInv b C σ₀ st' := by
  obtain ⟨hspec1, hspec2, hspec3⟩ := elements_spec b C hC
  have hT := translate_inRange b C hC
  cases e with
  | swap p q =>
    simp only [orderStep] at h
    by_cases hpq : p = q
    · simp only [hpq, ↓reduceIte] at h; simp at h
    · simp only [hpq, ↓reduceIte] at h
      by_cases hr : p < N ∧ q < N
      · simp only [hr, and_self, ↓reduceIte] at h
        rw [← exceptPure_ok h]
        refine ⟨?_, ?_, ?_, hinv.mem⟩
        · simp only [hinv.lay, swapLay_layOf _ _ hr.1 hr.2, irPerm_append, irPerm, one_mul, mul_assoc]
        · simp [irLogB_append, irLogB, hinv.log]
        · exact (StepsOk_append _ _ _ _ _).mpr ⟨hinv.ok, hpq, hr.1, hr.2, trivial⟩
      · simp only [hr, ↓reduceIte] at h; simp at h
  | elem i =>
    simp only [orderStep] at h
    cases hel : (elements b C)[i]? with
    | none => rw [hel] at h; simp at h
    | some el =>
      rw [hel] at h
      have hmem : el ∈ elements b C := List.mem_of_getElem? hel
      by_cases htk : st.taken.contains el = true
      · simp only [htk, ↓reduceIte] at h; simp at h
      · simp only [htk, Bool.false_eq_true, ↓reduceIte] at h
        cases el with
        | plain k =>
          dsimp only at h
          cases hTk : (translate b C)[k]? with
          | none => rw [hTk] at h; simp at h
          | some bg =>
            rw [hTk] at h
            rw [← exceptPure_ok h]
            refine ⟨?_, ?_, ?_, ?_⟩
            · simp only [hinv.lay, irPerm_append, irPerm, one_mul]
            · simp [irLogB_append, irLogB, hinv.log, Elem.gates, List.getD_eq_getElem?_getD, hTk]
            · refine (StepsOk_append _ _ _ _ _).mpr ⟨hinv.ok, ?_, trivial⟩
              intro bg' hbg' q hq
              simp only [List.mem_singleton] at hbg'
              subst hbg'
              exact hT _ (List.mem_of_getElem? hTk) q hq
            · intro e he
              rcases List.mem_append.mp he with he | he
              · exact hinv.mem e he
              · simp only [List.mem_singleton] at he; subst he; exact hmem
        | block j members =>
          dsimp only at h
          cases hbody : w.blocks.lookup i with
          | none => rw [hbody] at h; simp at h
          | some body =>
            rw [hbody] at h
            obtain ⟨LP, hLP, h⟩ := exceptBind_ok h
            rw [← exceptPure_ok h]
            have hmem' : ∀ k ∈ members, ∃ bg, (translate b C)[k]? = some (.ifBit j bg) ∧
                bg.expand.all Gate.isClifford = true := hspec3 _ hmem j members rfl
            rw [hinv.lay] at hLP
            obtain ⟨hL, hK⟩ := applyBlock_sound b C.nData C.nAnc (irPerm N st.steps * σ₀) (translate b C) j
              members body LP.1 LP.2 hLP hT hmem'
            refine ⟨?_, ?_, ?_, ?_⟩
            · simp only [hinv.lay, irPerm_append, irPerm, one_mul]
            · simp [irLogB_append, irLogB, hinv.log, Elem.gates, hL]
            · exact (StepsOk_append _ _ _ _ _).mpr ⟨hinv.ok, hK, trivial⟩
            · intro e he
              rcases List.mem_append.mp he with he | he
              · exact hinv.mem e he
              · simp only [List.mem_singleton] at he; subst he; exact hmem

theorem foldlM_inv (hC : C.WF) (σ₀ : Equiv.Perm (Fin N)) (l : List OrderEntry) (st st' : ApplyState)
    (hinv : FoldInv b C σ₀ st)
    (h : l.foldlM (orderStep b C.nData N (translate b C) (elements b C) w) st = .ok st') :
    FoldInv b C σ₀ st' := by
  induction l generalizing st with
  | nil => simp only [List.foldlM] at h; rw [← exceptPure_ok h]; exact hinv
  | cons e l ih =>
    simp only [List.foldlM] at h
    obtain ⟨st₁, h₁, h⟩ := exceptBind_ok h
    exact ih st₁ (orderStep_inv b C w hC σ₀ st st₁ e hinv h₁) h

end Fold

/-! ## The soundness theorem -/

section Sound

variable (b : TargetBasis) (C : Circuit) (w : Witness) (bb : ℕ)

theorem placedIR_flatMap (n : ℕ) {N : ℕ} (τ : Equiv.Perm (Fin N)) (T : List BasisGate) (l : List Elem) :
    (placedIR n (l.flatMap (Elem.gates T))).map (Gate.relabel N τ) =
      l.flatMap fun e => (placedIR n (Elem.gates T e)).map (Gate.relabel N τ) := by
  induction l with
  | nil => rfl
  | cons e l ih => rw [List.flatMap_cons, List.flatMap_cons, placedIR_append, List.map_append, ih]

/-- **`applyWitness_sound`** (PHASE2_SPEC §C.3): for a well-formed circuit, a reconstruction that
passes every check, and a permutation `σ₀` of the compact register extending the initial layout,
the physical circuit on the embedded input gives the embedded output of the logical circuit, laid
out by `σ_f = irPerm steps * σ₀`, which extends the witness's final layout. The well-formedness of
the physical circuit and its bit count are hypotheses decided per instance
(`CQRV.Tests.HardwareWitnessSound`). -/
theorem applyWitness_sound (hC : C.WF) (G : List BasisGate)
    (hG : applyWitness b C w (C.nData + (C.nAnc + bb)) = .ok G)
    (hWF : (physCircuit (C.nData + (C.nAnc + bb)) G).WF)
    (hM : (physCircuit (C.nData + (C.nAnc + bb)) G).nBits = C.nBits)
    (σ₀ : Equiv.Perm (Fin (C.nData + (C.nAnc + bb))))
    (h₀ : w.initial = layOf (C.nData + (C.nAnc + bb)) (C.nData + C.nAnc) σ₀) :
    ∃ σf : Equiv.Perm (Fin (C.nData + (C.nAnc + bb))),
      w.final = layOf (C.nData + (C.nAnc + bb)) (C.nData + C.nAnc) σf ∧
      ∀ ρ : MState (Reg C.nData × Reg C.nAnc),
        channelDenote (C.nData + (C.nAnc + bb)) 0 (physCircuit (C.nData + (C.nAnc + bb)) G) (embed bb σ₀ ρ) =
          embed bb σf (channelDenote C.nData C.nAnc C ρ) := by
  -- the checks
  simp only [applyWitness] at hG
  obtain ⟨_, _, hG⟩ := exceptBind_ok hG
  obtain ⟨_, _, hG⟩ := exceptBind_ok hG
  obtain ⟨_, _, hG⟩ := exceptBind_ok hG
  obtain ⟨_, _, hG⟩ := exceptBind_ok hG
  obtain ⟨st, hfold, hG⟩ := exceptBind_ok hG
  obtain ⟨_, _, hG⟩ := exceptBind_ok hG
  obtain ⟨_, hfinal, hG⟩ := exceptBind_ok hG
  obtain ⟨_, hvalid, hG⟩ := exceptBind_ok hG
  have hGeq := exceptPure_ok hG
  have hinv := foldlM_inv b C w hC σ₀ w.order _ st (foldInv_init b C w σ₀ h₀) hfold
  have hfinal' : st.lay = w.final := beq_iff_eq.mp (ensure_ok hfinal)
  have hvalid' := ensure_ok hvalid
  obtain ⟨hspec1, hspec2, hspec3⟩ := elements_spec b C hC
  have hT := translate_inRange b C hC
  refine ⟨irPerm _ st.steps * σ₀, by rw [← hfinal', hinv.lay], fun ρ => ?_⟩
  -- the physical gates: the IR run from `σ₀`
  have hgates : (physCircuit (C.nData + (C.nAnc + bb)) G).gates = irRun b C.nData _ st.steps σ₀ := by
    simp only [physCircuit, ← hGeq]
    rw [h₀]
    exact runSteps_fst b C.nData C.nAnc st.steps σ₀ hinv.ok
  -- the reference physical circuit: the translation placed and laid out by `σ₀`
  have hQgates : (physOf (n := C.nData) (a := C.nAnc) bb σ₀ (translateCircuit b C)).gates =
      (placedIR C.nData (translate b C)).map (Gate.relabel _ σ₀) := by
    simp [physOf, Circuit.relabel, Circuit.place, Circuit.map, placedIR, translateCircuit_gates]
  have hQbits : (physOf (n := C.nData) (a := C.nAnc) bb σ₀ (translateCircuit b C)).bitsOk = true :=
    relabel_bitsOk σ₀ _ (place_bitsOk C.nData (C.nAnc + bb) _ (translate_wf b C hC).bitsOk)
  have hQn : (physOf (n := C.nData) (a := C.nAnc) bb σ₀ (translateCircuit b C)).nBits = C.nBits := by
    simp only [physOf, Circuit.relabel_eq_map, nBits_map, Circuit.place, nBits_translate]
  -- independence of elements transfers to their placed and laid-out gates
  have hind : ∀ x ∈ elements b C, ∀ y ∈ elements b C,
      indep (Elem.qubits (translate b C)) (Elem.bits (translate b C)) x y = true →
      ∀ q ∈ ((placedIR C.nData (Elem.gates (translate b C) x)).map (Gate.relabel _ σ₀)).flatMap Gate.qubits,
        q ∉ ((placedIR C.nData (Elem.gates (translate b C) y)).map (Gate.relabel _ σ₀)).flatMap Gate.qubits := by
    intro x hx y hy hxy q hqx hqy
    simp only [indep, disjointL, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not] at hxy
    simp only [placedIR, List.flatMap_map, List.mem_flatMap, Gate.relabel, Gate.map_qubits,
      List.mem_map] at hqx hqy
    obtain ⟨g, hg, q₀, ⟨a₀, ha₀, rfl⟩, rfl⟩ := hqx
    obtain ⟨g', hg', q₁, ⟨a₁, ha₁, rfl⟩, hq⟩ := hqy
    obtain ⟨bg, hbg, hgbg⟩ := hg
    obtain ⟨bg', hbg', hgbg'⟩ := hg'
    have hx0 : a₀ ∈ bg.qubits := mem_qubits_expand (List.mem_flatMap.mpr ⟨g, hgbg, ha₀⟩)
    have hy1 : a₁ ∈ bg'.qubits := mem_qubits_expand (List.mem_flatMap.mpr ⟨g', hgbg', ha₁⟩)
    have hr0 : a₀.inRange C.nData C.nAnc = true := hT bg (hspec2 x hx bg hbg) a₀ hx0
    have hr1 : a₁.inRange C.nData C.nAnc = true := hT bg' (hspec2 y hy bg' hbg') a₁ hy1
    have : a₁ = a₀ := place_inj C.nData C.nAnc hr1 hr0 (relabel_injective σ₀ hq)
    subst this
    exact hxy.1 a₁ (by rw [Elem.qubits_eq]; exact List.mem_flatMap.mpr ⟨bg, hbg, hx0⟩)
      (by rw [Elem.qubits_eq]; exact List.mem_flatMap.mpr ⟨bg', hbg', hy1⟩)
  -- the Kraus operators of the physical circuit, branch by branch
  have hkraus : ∀ c : Fin C.nBits → Bool, ∃ z : ℂ, star z * z = 1 ∧
      krausOps (C.nData + (C.nAnc + bb)) 0 C.nBits (physCircuit (C.nData + (C.nAnc + bb)) G).gates c =
        z • (permMat (A := 0) (irPerm (C.nData + (C.nAnc + bb)) st.steps) *
          krausOps (C.nData + (C.nAnc + bb)) 0 C.nBits
            (physOf (n := C.nData) (a := C.nAnc) bb σ₀ (translateCircuit b C)).gates c) := by
    intro c
    obtain ⟨z, hz, hk⟩ := irRun_kraus b C.nData C.nAnc C.nBits st.steps σ₀ hinv.ok c
    obtain ⟨ν, hν, hud⟩ := ud_irSwaps b st.steps hinv.ok.swapsOk
    refine ⟨z * ν, ?_, ?_⟩
    · calc star (z * ν) * (z * ν) = (star z * z) * (star ν * ν) := by rw [star_mul]; ring
        _ = 1 := by rw [hz, hν, one_mul]
    · rw [hgates, hk, krausOps_append_list, krausOps_of_unitary _ 0 _ _ (irSwaps_unitary b st.steps), hud,
        hinv.log, placedIR_flatMap,
        krausOps_reorder_interp (n := C.nData + (C.nAnc + bb)) (a := 0) _ _ _ (elements b C) st.taken hind hvalid' c,
        ← placedIR_flatMap, hspec1, ← hQgates, Matrix.smul_mul, smul_smul]
  -- the channel: `Ad(permMat σ_f)` of the embedded translation
  have hembed : embed bb (irPerm _ st.steps * σ₀) (channelDenote C.nData C.nAnc C ρ) =
      (channelDenote _ 0 (physOf (n := C.nData) (a := C.nAnc) bb σ₀ (translateCircuit b C)) (embed bb σ₀ ρ)).relabel
        (stateEquiv (irPerm _ st.steps)) := by
    rw [channelDenote_embed bb σ₀ (translateCircuit b C) (translate_wf b C hC) (ancsBelow_translate b C)
      (translate_wf b C hC).qubitsOk, translate_channel C.nData C.nAnc b C hC hC.qubitsOk (inRange_of_WF C hC)]
    simp only [embed, MState.relabel_relabel, stateEquiv_mul, Equiv.trans_assoc]
  rw [hembed]
  apply MState.ext_m
  rw [relabel_m_eq_permMat, channelDenote_m_gen _ 0 hWF.bitsOk hM, channelDenote_m_gen _ 0 hQbits hQn,
    Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨z, hz, hk⟩ := hkraus c
  have hz' : z * star z = 1 := by rw [mul_comm]; exact hz
  rw [hk, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, hz', one_smul]
  simp only [Matrix.mul_assoc]

end Sound

/-! ## The bit count of the physical circuit -/

section Bits

variable (b : TargetBasis) (n : ℕ) {N : ℕ}

theorem validReorder_perm {α : Type} [DecidableEq α] (qs : α → List Qubit) (bs : α → List ℕ)
    (l l' : List α) (h : validReorder qs bs l l' = true) : l'.Perm l := by
  induction l' generalizing l with
  | nil =>
    simp only [validReorder, List.isEmpty_iff] at h
    subst h
    exact List.Perm.refl _
  | cons x rest ih =>
    simp only [validReorder] at h
    cases hs : splitFirst x l with
    | none => rw [hs] at h; simp at h
    | some p =>
      obtain ⟨pre, post⟩ := p
      rw [hs] at h
      simp only [Bool.and_eq_true] at h
      rw [splitFirst_spec hs]
      exact ((ih (pre ++ post) h.2).cons x).trans List.perm_middle.symm

theorem written_map_ifBit' (j : ℕ) (gs : List Gate) : Circuit.written (gs.map (Gate.ifBit j)) = [] := by
  induction gs with
  | nil => rfl
  | cons g gs _ => simp [Circuit.written, List.flatMap_cons, Gate.writes]

theorem written_swapIR (p q : ℕ) : Circuit.written (swapIR b p q) = [] := by
  cases b <;> simp [swapIR, swapEntry, cnotEntry, hGates, BasisGate.expand, Circuit.written, Gate.writes]

/-- The classical bits written by a run are those of its logical gates, in the run's order (the
SWAPs and the conditioned blocks write none). -/
theorem written_irRun (steps : List PStep) (τ : Equiv.Perm (Fin N)) (hblk : ∀ L P, PStep.block L P ∈ steps →
      Circuit.written (P.flatMap BasisGate.expand) = [] ∧ Circuit.written (L.flatMap BasisGate.expand) = []) :
    Circuit.written (irRun b n N steps τ) = Circuit.written (placedIR n (irLogB steps)) := by
  induction steps generalizing τ with
  | nil => rfl
  | cons s rest ih =>
    have hrest : ∀ L P, PStep.block L P ∈ rest → _ := fun L P h => hblk L P (List.mem_cons_of_mem _ h)
    cases s with
    | swap p q =>
      simp only [irRun, irLogB, written_append_list, written_swapIR, List.nil_append]
      exact ih _ hrest
    | place gs =>
      simp only [irRun, irLogB, written_append_list, placedIR_append, Gate.relabel_eq_map, written_map,
        ih _ hrest]
    | block L P =>
      obtain ⟨hP, hL⟩ := hblk L P (List.mem_cons_self ..)
      rw [irRun, irLogB, written_append_list, hP, List.nil_append, ih _ hrest, placedIR_append,
        written_append_list]
      simp only [placedIR, written_map, hL, List.nil_append]

end Bits

/-! ## The transfers -/

section Transfer

variable (b : TargetBasis) (C : Circuit) (w : Witness) (bb : ℕ)

/-- Report §6.3.2 — **`AncRestore.phys`**: the restoration transfers to the physical circuit: on
the embedded `ρ ⊗ |0⟩`, laid out by `σ₀`, it gives the embedded `U ρ U† ⊗ |0⟩`, laid out by `σ_f`
(the ancillae and the idle qubits are back in |0⟩, at the final layout). -/
theorem AncRestore.phys (hC : C.WF) (G : List BasisGate)
    (hG : applyWitness b C w (C.nData + (C.nAnc + bb)) = .ok G)
    (hWF : (physCircuit (C.nData + (C.nAnc + bb)) G).WF)
    (hM : (physCircuit (C.nData + (C.nAnc + bb)) G).nBits = C.nBits)
    (σ₀ : Equiv.Perm (Fin (C.nData + (C.nAnc + bb))))
    (h₀ : w.initial = layOf (C.nData + (C.nAnc + bb)) (C.nData + C.nAnc) σ₀)
    {U : 𝐔[Reg C.nData]} (hR : AncRestore C.nData C.nAnc C U) :
    ∃ σf : Equiv.Perm (Fin (C.nData + (C.nAnc + bb))),
      w.final = layOf (C.nData + (C.nAnc + bb)) (C.nData + C.nAnc) σf ∧
      ∀ ρ : MState (Reg C.nData),
        channelDenote (C.nData + (C.nAnc + bb)) 0 (physCircuit (C.nData + (C.nAnc + bb)) G)
            (embed bb σ₀ (ρ ⊗ᴹ ancZero C.nAnc)) =
          embed bb σf ((U ◃ ρ) ⊗ᴹ ancZero C.nAnc) := by
  obtain ⟨σf, hf, h⟩ := applyWitness_sound b C w bb hC G hG hWF hM σ₀ h₀
  exact ⟨σf, hf, fun ρ => by rw [h, hR ρ]⟩

variable {n a : ℕ}

/-- The embedding as one relabeling. -/
def embedEquiv (σ : Equiv.Perm (Fin (n + (a + bb)))) :
    Reg (n + (a + bb)) × Reg 0 ≃ (Reg n × Reg a) × Reg bb :=
  (stateEquiv σ).trans ((placeEquiv n (a + bb)).trans (wEquiv n a bb))

theorem embed_eq_relabel (σ : Equiv.Perm (Fin (n + (a + bb)))) (ρ : MState (Reg n × Reg a)) :
    embed bb σ ρ = (ρ ⊗ᴹ ancZero bb).relabel (embedEquiv bb σ) := by
  simp [embed, embedState, embedEquiv, MState.relabel_relabel]

/-- The un-embedding: undo the layout and the placement, trace out the idle qubits and the
ancillae. -/
def unembed (σ : Equiv.Perm (Fin (n + (a + bb)))) : CPTPMap (Reg (n + (a + bb)) × Reg 0) (Reg n) :=
  CPTPMap.traceRight ∘ₘ CPTPMap.traceRight ∘ₘ CPTPMap.ofEquiv (embedEquiv bb σ)

theorem unembed_embed (σ : Equiv.Perm (Fin (n + (a + bb)))) (ρ : MState (Reg n × Reg a)) :
    unembed bb σ (embed bb σ ρ) = ρ.traceRight := by
  simp only [unembed, CPTPMap.compose_eq, CPTPMap.ofEquiv_apply, embed_eq_relabel, MState.relabel_relabel,
    Equiv.symm_trans_self, MState.relabel_refl, CPTPMap.traceRight_eq_MState_traceRight,
    MState.traceRight_prod_eq]

/-- PHASE2_SPEC §C.3 — the physical Grover channel of a physical circuit `P` on the compact
register: prepare the embedded |0⟩ (the all-zero physical state), run `P`, undo the final layout and
trace out everything but the data register. The grade is the circuit's own (26c: `PhysGrade`). -/
def physGroverChannel (σ₀ σf : Equiv.Perm (Fin (n + (a + bb)))) (P : Circuit) : GradedChannel Unit (Reg n) :=
  ⟨unembed bb σf ∘ₘ channelDenote (n + (a + bb)) 0 P ∘ₘ CPTPMap.replacement (embed bb σ₀ (ancZero n ⊗ᴹ ancZero a)),
    Synthesis.grade P⟩

/-- Report §2.1.2 — **`realizes_phys`**: `Realizes` transfers to the physical circuit, with the
same decoding, at the physical circuit's own grade. -/
theorem realizes_phys (hC : C.WF) (G : List BasisGate)
    (hG : applyWitness b C w (C.nData + (C.nAnc + bb)) = .ok G)
    (hWF : (physCircuit (C.nData + (C.nAnc + bb)) G).WF)
    (hM : (physCircuit (C.nData + (C.nAnc + bb)) G).nBits = C.nBits)
    (σ₀ : Equiv.Perm (Fin (C.nData + (C.nAnc + bb))))
    (h₀ : w.initial = layOf (C.nData + (C.nAnc + bb)) (C.nData + C.nAnc) σ₀)
    {Y : Type} [Fintype Y] [DecidableEq Y] [PseudoMetricSpace Y] (S : Spec Unit Y)
    (dec : POVM Y (Reg C.nData)) (ε δ : ℝ) (r : Grade)
    (h : Realizes S dec (Grover.groverChannel C.nData C) ε δ r) :
    ∃ σf : Equiv.Perm (Fin (C.nData + (C.nAnc + bb))),
      w.final = layOf (C.nData + (C.nAnc + bb)) (C.nData + C.nAnc) σf ∧
      Realizes S dec (physGroverChannel bb σ₀ σf (physCircuit (C.nData + (C.nAnc + bb)) G)) ε δ
        (Synthesis.grade (physCircuit (C.nData + (C.nAnc + bb)) G)) := by
  obtain ⟨σf, hf, hch⟩ := applyWitness_sound b C w bb hC G hG hWF hM σ₀ h₀
  refine ⟨σf, hf, le_rfl, fun x hx => ?_⟩
  have hchan : (physGroverChannel bb σ₀ σf (physCircuit (C.nData + (C.nAnc + bb)) G)).chan (encode x) =
      (Grover.groverChannel C.nData C).chan (encode x) := by
    simp only [physGroverChannel, Grover.groverChannel, GradedChannel.traceAnc, CPTPMap.compose_eq,
      CPTPMap.replacement_apply, hch, unembed_embed, CPTPMap.traceRight_eq_MState_traceRight]
  rw [hchan]
  exact h.2 x hx

end Transfer

end

end CQRV.Hardware
