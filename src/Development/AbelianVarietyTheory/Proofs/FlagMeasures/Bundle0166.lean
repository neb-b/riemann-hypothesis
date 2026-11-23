module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0137
public import Formalism.FormalDegreeBessel.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormPosOfIsUnit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LieAlgebraBesselModelMiddleUnitaryEntries
section
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CellLieAlg

theorem mem_lieE_iff {m : ℕ} {S : Set (Matrix (Fin m) (Fin m) ℂ)} (P : Submodule ℝ (Matrix (Fin m) (Fin m) ℂ))
    (hP : ∀ X, X ∈ lieOf S ↔ X ∈ P) (x : EuclideanSpace ℝ (Fin m × Fin m × Bool)) :
    x ∈ lieE S ↔ unrealify x ∈ P := by
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨X, hX, rfl⟩ := hy
      have e : unrealify ((WithLp.equiv 2 _).symm (realifyFun X)) = X := by
        ext i j; rfl
      show unrealify ((WithLp.equiv 2 _).symm (realifyFun X)) ∈ P
      rw [e]; exact (hP X).1 hX
    | zero =>
      have e : unrealify (0 : EuclideanSpace ℝ (Fin m × Fin m × Bool)) = 0 := by
        ext i j; apply Complex.ext <;> simp [unrealify]
      rw [e]; exact P.zero_mem
    | add x y _ _ hx hy =>
      have e : unrealify (x + y) = unrealify x + unrealify y := by
        ext i j; apply Complex.ext <;> simp [unrealify]
      rw [e]; exact P.add_mem hx hy
    | smul c x _ hx =>
      have e : unrealify (c • x) = c • unrealify x := by
        ext i j; apply Complex.ext <;> simp [unrealify]
      rw [e]; exact P.smul_mem c hx
  · intro hx
    refine Submodule.subset_span ⟨unrealify x, (hP _).2 hx, ?_⟩
    ext ⟨i, j, b⟩
    cases b <;> rfl

open scoped Matrix.Norms.Operator in
theorem mem_lieOf_UH {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) (hH : H * H = 1) (X : Matrix (Fin N) (Fin N) ℂ) :
    X ∈ lieOf (UH H) ↔ Xᴴ * H + H * X = 0 := by
  constructor
  · intro h
    have hc : (fun t : ℝ => NormedSpace.exp (t • Xᴴ) * H * NormedSpace.exp (t • X)) = fun _ => H := by
      funext t
      have h1 : (NormedSpace.exp ((t : ℂ) • X))ᴴ * H * NormedSpace.exp ((t : ℂ) • X) = H := h t
      rw [← Matrix.exp_conjTranspose, Complex.coe_smul, Matrix.conjTranspose_smul, star_trivial] at h1
      exact h1
    have hd : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Xᴴ) * H * NormedSpace.exp (t • X)) _ 0 :=
      ((hasDerivAt_exp_smul_const (𝕂 := ℝ) Xᴴ 0).mul_const H).mul (hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0)
    rw [hc] at hd
    have := hd.unique (hasDerivAt_const _ _)
    simpa using this
  · intro hX t
    set Y : Matrix (Fin N) (Fin N) ℂ := (t : ℂ) • X with hYdef
    have hY : Yᴴ * H + H * Y = 0 := by
      rw [hYdef, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
        Matrix.mul_smul, ← smul_add, hX, smul_zero]
    have hinv : H⁻¹ = H := Matrix.inv_eq_right_inv hH
    have hu : IsUnit H := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_left_inverse hH)
    have hYh : Yᴴ = H * (-Y) * H⁻¹ := by
      have e : Yᴴ * H = -(H * Y) := eq_neg_of_add_eq_zero_left hY
      calc Yᴴ = Yᴴ * (H * H) := by rw [hH, Matrix.mul_one]
        _ = (Yᴴ * H) * H := by rw [Matrix.mul_assoc]
        _ = _ := by rw [e, hinv, Matrix.mul_neg]
    have hexp : (NormedSpace.exp Y)ᴴ = H * NormedSpace.exp (-Y) * H := by
      rw [← Matrix.exp_conjTranspose, hYh, Matrix.exp_conj _ _ hu, hinv]
    have hc : NormedSpace.exp (-Y) * NormedSpace.exp Y = 1 := by
      rw [← Matrix.exp_add_of_commute _ _ (Commute.neg_left (Commute.refl Y)), neg_add_cancel,
        NormedSpace.exp_zero]
    show (NormedSpace.exp Y)ᴴ * H * NormedSpace.exp Y = H
    rw [hexp, Matrix.mul_assoc (H * NormedSpace.exp (-Y)) H H, hH,
      Matrix.mul_one, Matrix.mul_assoc, hc, Matrix.mul_one]

open scoped Matrix.Norms.Operator in
theorem exp_mul_eq_iff {N : ℕ} (X E : Matrix (Fin N) (Fin N) ℂ) :
    (∀ t : ℝ, NormedSpace.exp (t • X) * E = E) ↔ X * E = 0 := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => NormedSpace.exp (t • X) * E)
      (NormedSpace.exp (t • X) * X * E) t := fun t =>
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) X t).mul_const E
  constructor
  · intro h
    have h0 := hd 0
    rw [show (fun t : ℝ => NormedSpace.exp (t • X) * E) = fun _ => E from funext h] at h0
    simpa using h0.unique (hasDerivAt_const _ _)
  · intro h t
    have := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
      (fun t => by rw [(hd t).deriv, Matrix.mul_assoc, h, Matrix.mul_zero]) t 0
    simpa using this

theorem mul_single_eq_iff {N : ℕ} (g h : Matrix (Fin N) (Fin N) ℂ) (j : Fin N) :
    g * Matrix.single j j (1 : ℂ) = h * Matrix.single j j (1 : ℂ) ↔ g *ᵥ bvec j = h *ᵥ bvec j := by
  simp only [bvec, Matrix.mulVec_single_one]
  constructor
  · intro e
    funext i
    simpa using congrFun (congrFun e i) j
  · intro e
    ext i l
    by_cases hl : l = j
    · subst hl
      simpa using congrFun e i
    · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hl, Matrix.mul_single_apply_of_ne _ _ _ _ _ hl]

theorem exp_fix_iff {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (j : Fin N) :
    (∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) *ᵥ bvec j = bvec j) ↔ ∀ i, X i j = 0 := by
  have h1 := exp_mul_eq_iff X (Matrix.single j j (1 : ℂ))
  have h2 := mul_single_eq_iff X 0 j
  rw [Matrix.zero_mul] at h2
  rw [h2] at h1
  have h3 : X *ᵥ bvec j = (0 : Matrix (Fin N) (Fin N) ℂ) *ᵥ bvec j ↔ ∀ i, X i j = 0 := by
    simp [bvec, funext_iff]
  rw [← h3, ← h1]
  refine forall_congr' fun t => ?_
  have h4 := mul_single_eq_iff (NormedSpace.exp (t • X)) 1 j
  rw [Matrix.one_mul, Matrix.one_mulVec] at h4
  rw [h4, Complex.coe_smul]

theorem rows_zero {k r : ℕ} {X : Mat k r} (hX : Xᴴ * Hpk k r + Hpk k r * X = 0)
    (hc : ∀ j : Fin (2 * r + k + 1), ¬ (r ≤ j.val ∧ j.val ≤ r + k) → ∀ i, X i j = 0)
    (i : Fin (2 * r + k + 1)) (hi : ¬ (r ≤ i.val ∧ i.val ≤ r + k)) (j : Fin (2 * r + k + 1)) : X i j = 0 := by
  have hil := i.isLt
  let i' : Fin (2 * r + k + 1) := ⟨2 * r + k - i.val, by omega⟩
  have hv : i'.val = 2 * r + k - i.val := rfl
  have h := congrFun (congrFun hX i') j
  have h1 : (Xᴴ * Hpk k r) i' j = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [Matrix.conjTranspose_apply, hc i' (by omega) l, star_zero, zero_mul]
  have h2 : (Hpk k r * X) i' j = X i j := by
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · have : Hpk k r i' i = 1 := by
        unfold Hpk
        split_ifs with a b c d <;> first | rfl | (exfalso; omega)
      rw [this, one_mul]
    · intro l _ hl
      have hl' : l.val ≠ i.val := fun e => hl (Fin.ext e)
      have : Hpk k r i' l = 0 := by
        unfold Hpk
        split_ifs with a b c d <;> first | rfl | (exfalso; omega)
      rw [this, zero_mul]
    · simp
  rw [Matrix.add_apply, h1, h2, zero_add] at h
  exact h

theorem mem_lieOf_UWb (k r : ℕ) (X : Mat k r) :
    X ∈ lieOf (Formalism.FourierDecayAlt.B2.UWb k r) ↔ (Xᴴ * Hpk k r + Hpk k r * X = 0 ∧ ∀ i j : Fin (2 * r + k + 1),
      ¬ ((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)) → X i j = 0) := by
  have hH := (hpkFacts k r).2.1
  constructor
  · intro h
    have hX := (mem_lieOf_UH _ hH X).1 fun t => (h t).1
    have hc : ∀ j : Fin (2 * r + k + 1), ¬ (r ≤ j.val ∧ j.val ≤ r + k) → ∀ i, X i j = 0 := by
      intro j hj
      have hjl := j.isLt
      by_cases hr : j.val < r
      · exact (exp_fix_iff X j).1 fun t => ((h t).2 ⟨j.val, hr⟩).1
      · have e : esI k r ⟨2 * r + k - j.val, by omega⟩ = j := by
          apply Fin.ext; simp only [esI]; omega
        rw [← e]
        exact (exp_fix_iff X _).1 fun t => ((h t).2 _).2
    refine ⟨hX, fun i j hij => ?_⟩
    by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
    · exact hc j (fun hj => hij ⟨hi, hj⟩) i
    · exact rows_zero hX hc i hi j
  · rintro ⟨hX, h0⟩ t
    refine ⟨(mem_lieOf_UH _ hH X).2 hX t, fun a => ⟨?_, ?_⟩⟩
    · refine (exp_fix_iff X _).2 (fun i => h0 i _ fun h => ?_) t
      have := h.2.1; have := a.isLt
      simp only [eI] at *; omega
    · refine (exp_fix_iff X _).2 (fun i => h0 i _ fun h => ?_) t
      have := h.2.2; have := a.isLt
      simp only [esI] at *; omega

def skewSub {N : ℕ} (H : Matrix (Fin N) (Fin N) ℂ) : Submodule ℝ (Matrix (Fin N) (Fin N) ℂ) where
  carrier := {X | Xᴴ * H + H * X = 0}
  zero_mem' := by simp
  add_mem' {a b} ha hb := by
    have ha' : aᴴ * H + H * a = 0 := ha
    have hb' : bᴴ * H + H * b = 0 := hb
    show (a + b)ᴴ * H + H * (a + b) = 0
    rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, ha', hb', add_zero]
  smul_mem' c a ha := by
    have ha' : aᴴ * H + H * a = 0 := ha
    show (c • a)ᴴ * H + H * (c • a) = 0
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, ha', smul_zero]

def midSub (k r : ℕ) : Submodule ℝ (Mat k r) where
  carrier := {X | ∀ i j : Fin (2 * r + k + 1),
      ¬ ((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)) → X i j = 0}
  zero_mem' := fun _ _ _ => rfl
  add_mem' {a b} ha hb := fun i j h => by rw [Matrix.add_apply, ha i j h, hb i j h, add_zero]
  smul_mem' c a ha := fun i j h => by rw [Matrix.smul_apply, ha i j h, smul_zero]

theorem lie_entries : ∀ (k r : ℕ) (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)), (x ∈ lieE (GG k r) ↔ (unrealify x)ᴴ * Hpk k r + Hpk k r * unrealify x = 0) ∧ (x ∈ lieE (Formalism.FourierDecayAlt.B2.UWb k r) ↔ ((unrealify x)ᴴ * Hpk k r + Hpk k r * unrealify x = 0 ∧ ∀ i j : Fin (2 * r + k + 1), ¬ ((r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k)) → unrealify x i j = 0)) ∧ (x ∈ lieE (Formalism.FourierDecayAlt.B2.UWb k r) → NormedSpace.exp (unrealify x) ∈ Formalism.FourierDecayAlt.B2.UWb k r) := by
  intro k r x
  have h2 := mem_lieE_iff (S := Formalism.FourierDecayAlt.B2.UWb k r) (skewSub (Hpk k r) ⊓ midSub k r) (mem_lieOf_UWb k r) x
  refine ⟨mem_lieE_iff (skewSub (Hpk k r)) (mem_lieOf_UH _ (hpkFacts k r).2.1) x, h2, fun hx => ?_⟩
  have h := (mem_lieOf_UWb k r _).2 (h2.1 hx) 1
  simpa using h

end GlobalTheory.CellLieAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralRadicalEqTopSectionSplit
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.PSplit

theorem mp_merge {ι α : Type} [Fintype ι] [MeasureSpace α] [SigmaFinite (volume : Measure α)]
    (p q : ι → Prop) [DecidablePred p] [Fintype {i // p i}] [Fintype {i // q i}]
    (hq : ∀ i, q i ↔ ¬ p i) :
    MeasurePreserving (fun x : ({i // p i} → α) × ({i // q i} → α) =>
      fun i => if h : p i then x.1 ⟨i, h⟩ else x.2 ⟨i, (hq i).2 h⟩) volume volume := by
  obtain rfl : q = fun i => ¬ p i := funext fun i => propext (hq i)
  have := (volume_preserving_piEquivPiSubtypeProd (fun _ : ι => α) p).symm
  convert this using 1
  all_goals first | rfl | (congr <;> exact Subsingleton.elim _ _)

theorem mp_comm {A B C D : Type} [MeasureSpace A] [MeasureSpace B] [MeasureSpace C]
    [MeasureSpace D] [SFinite (volume : Measure A)] [SFinite (volume : Measure B)]
    [SFinite (volume : Measure C)] [SFinite (volume : Measure D)] :
    MeasurePreserving (fun x : (A × B) × (C × D) => ((x.1.1, x.2.1), (x.1.2, x.2.2)))
      volume volume := by
  have h1 := measurePreserving_prodAssoc (volume : Measure A) (volume : Measure B)
    (volume : Measure (C × D))
  have h2 := (MeasurePreserving.id (volume : Measure A)).prod
    (measurePreserving_prodAssoc (volume : Measure B) (volume : Measure C)
      (volume : Measure D)).symm
  have h3 := (MeasurePreserving.id (volume : Measure A)).prod
    ((Measure.measurePreserving_swap (μ := (volume : Measure B)) (ν := (volume : Measure C))).prod
      (MeasurePreserving.id (volume : Measure D)))
  have h4 := (MeasurePreserving.id (volume : Measure A)).prod
    (measurePreserving_prodAssoc (volume : Measure C) (volume : Measure B)
      (volume : Measure D))
  have h5 := (measurePreserving_prodAssoc (volume : Measure A) (volume : Measure C)
    (volume : Measure (B × D))).symm
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

theorem lintegral_shift {A C T : Type} [MeasureSpace A] [MeasureSpace C] [MeasureSpace T]
    [SFinite (volume : Measure A)] [SFinite (volume : Measure C)] [SFinite (volume : Measure T)]
    [AddGroup C] [MeasurableAdd₂ C] [Measure.IsAddRightInvariant (volume : Measure C)]
    (F : (A × C) × T → ℝ≥0∞) (hF : Measurable F) (c : A × T → C) (hc : Measurable c) :
    ∫⁻ x, F x = ∫⁻ y : A × C, ∫⁻ t : T, F ((y.1, y.2 + c (y.1, t)), t) := by
  have hG : Measurable (fun x : (A × C) × T => F ((x.1.1, x.1.2 + c (x.1.1, x.2)), x.2)) := by
    apply hF.comp
    fun_prop
  rw [lintegral_lintegral_swap (f := fun (y : A × C) (t : T) => F ((y.1, y.2 + c (y.1, t)), t))
    hG.aemeasurable, Measure.volume_eq_prod, lintegral_prod_symm _ hF.aemeasurable]
  refine lintegral_congr fun t => ?_
  rw [Measure.volume_eq_prod, lintegral_prod _ (Measurable.aemeasurable (by fun_prop)),
    lintegral_prod (fun y : A × C => F ((y.1, y.2 + c (y.1, t)), t))
      (Measurable.aemeasurable (hG.comp (f := fun y : A × C => (y, t)) (by fun_prop)))]
  refine lintegral_congr fun a => ?_
  exact (lintegral_add_right_eq_self (fun s => F ((a, s), t)) (c (a, t))).symm

theorem sf_pair (ι κ : Type) [Fintype ι] [Fintype κ] :
    SFinite (volume : Measure ((ι → ℂ) × (κ → ℝ))) := inferInstance

theorem sf_rows (ι κ : Type) [Fintype ι] [Fintype κ] :
    SFinite (volume : Measure (ι → κ → ℂ)) := inferInstance

theorem sf_triple (ι ι' κ κ' : Type) [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ'] :
    SFinite (volume : Measure ((ι → ι' → ℂ) × (κ → ℂ) × (κ' → ℝ))) := by
  have := sf_pair κ κ'
  have := sf_rows ι ι'
  exact Measure.prod.instSFinite

theorem inv_pair (ι κ : Type) [Fintype ι] [Fintype κ] :
    Measure.IsAddRightInvariant (volume : Measure ((ι → ℂ) × (κ → ℝ))) :=
  Measure.prod.instIsAddRightInvariant

def merge (k r j : ℕ) (x : PSec k r j × PTop k r j) : PPar k r :=
  (fun a => if h : (a : ℕ) < j then x.1.1 ⟨a, h⟩ else x.2.1 ⟨a, not_lt.1 h⟩,
   fun p => if h : (p.1.1 : ℕ) < j then x.1.2.1 ⟨p, h⟩ else x.2.2.1 ⟨p, not_lt.1 h⟩,
   fun a => if h : (a : ℕ) < j then x.1.2.2 ⟨a, h⟩ else x.2.2.2 ⟨a, not_lt.1 h⟩)

theorem mp_mergeP (k r j : ℕ) : MeasurePreserving (merge k r j) volume volume := by
  have h1 := mp_merge (α := Fin (k + 1) → ℂ) (fun a : Fin r => (a : ℕ) < j)
    (fun a : Fin r => j ≤ (a : ℕ)) (fun _ => not_lt.symm)
  have h2 := mp_merge (α := ℂ) (fun p : UT r => (p.1.1 : ℕ) < j)
    (fun p : UT r => j ≤ (p.1.1 : ℕ)) (fun _ => not_lt.symm)
  have h3 := mp_merge (α := ℝ) (fun a : Fin r => (a : ℕ) < j)
    (fun a : Fin r => j ≤ (a : ℕ)) (fun _ => not_lt.symm)
  have := sf_pair {p : UT r // (p.1.1 : ℕ) < j} {a : Fin r // (a : ℕ) < j}
  have := sf_pair {p : UT r // j ≤ (p.1.1 : ℕ)} {a : Fin r // j ≤ (a : ℕ)}
  have := sf_pair (UT r) (Fin r)
  have h4 := (h2.prod h3).comp mp_comm
  have h5 := @MeasurePreserving.prod _ _ _ _ _ _ _ _ _ _ _ _ Measure.prod.instSFinite
    Measure.prod.instSFinite _ _ h1 h4
  exact h5.comp mp_comm

theorem cont_pOf (k r : ℕ) : Continuous (fun q : PPar k r => (fun a b => pOf k r q a b : Mt k r)) := by
  refine continuous_pi fun i => continuous_pi fun i' => ?_
  simp only [pOf, pEl, skewM, Rad.herm_Hb]
  split_ifs <;> fun_prop

noncomputable def shift (k r j : ℕ)
    (x : ({a : Fin r // (a : ℕ) < j} → Fin (k + 1) → ℂ) × PTop k r j) :
    ({p : UT r // (p.1.1 : ℕ) < j} → ℂ) × ({a : Fin r // (a : ℕ) < j} → ℝ) :=
  (fun p => if h : j ≤ (p.1.1.2 : ℕ) then
      herm (Hb k) (x.2.1 ⟨p.1.1.2, h⟩) (x.1 ⟨p.1.1.1, p.2⟩) / 2 else 0, 0)

theorem meas_shift (k r j : ℕ) : Measurable (shift k r j) := by
  refine Measurable.prodMk (Measurable.of_eval fun p => ?_) measurable_const
  simp only [Rad.herm_Hb]
  split_ifs <;> fun_prop

theorem herm_zero_left {k : ℕ} (w : Fin (k + 1) → ℂ) : herm (Hb k) 0 w = 0 := by
  simp [Rad.herm_Hb]

theorem herm_zero_right {k : ℕ} (w : Fin (k + 1) → ℂ) : herm (Hb k) w 0 = 0 := by
  simp [Rad.herm_Hb]

theorem mul_eq (k r j : ℕ) (q' : PSec k r j) (q : PTop k r j) :
    pTop k r j q * pSec k r j q' =
      pOf k r (merge k r j ((q'.1, q'.2 + shift k r j (q'.1, q)), q)) := by
  simp only [pTop, pSec, pOf, Rad.pEl_mul, merge]
  congr 1
  · funext a
    by_cases h : (a : ℕ) < j
    · simp [h, not_le.2 h]
    · simp [h, not_lt.1 h]
  · ext a b
    simp only [Matrix.add_apply, Matrix.of_apply, skewM, shift]
    by_cases ha : (a : ℕ) < j <;> by_cases hb : (b : ℕ) < j
    · have ha' := not_le.2 ha
      have hb' := not_le.2 hb
      simp [ha, hb, ha', hb', herm_zero_left, herm_zero_right]
    · have ha' := not_le.2 ha
      have hb' := not_lt.1 hb
      have hab : a < b := by rw [Fin.lt_def]; omega
      simp [ha, hb, ha', hb', hab, herm_zero_left]
    · have ha' := not_lt.1 ha
      have hb' := not_le.2 hb
      have hab : b < a := by rw [Fin.lt_def]; omega
      simp [ha, hb, ha', hb', hab, hab.not_gt, herm_zero_left]
      rw [← Rad.herm_star]
      simp only [Complex.star_def]
      ring
    · have ha' := not_lt.1 ha
      have hb' := not_lt.1 hb
      simp [ha, hb, ha', hb', herm_zero_left, herm_zero_right]

theorem lintegral_split (k r j : ℕ) (f : Mat k r → ℝ≥0∞)
    (hf : Measurable (fun x : Mt k r => f (Matrix.of x))) :
    ∫⁻ q : PPar k r, f (pOf k r q) =
      ∫⁻ q' : PSec k r j, ∫⁻ q : PTop k r j, f (pTop k r j q * pSec k r j q') := by
  have hg : Measurable (fun q : PPar k r => f (pOf k r q)) :=
    hf.comp (f := fun q : PPar k r => (fun a b => pOf k r q a b : Mt k r))
      (cont_pOf k r).measurable
  have := sf_pair {p : UT r // (p.1.1 : ℕ) < j} {a : Fin r // (a : ℕ) < j}
  have := sf_triple {a : Fin r // j ≤ (a : ℕ)} (Fin (k + 1)) {p : UT r // j ≤ (p.1.1 : ℕ)}
    {a : Fin r // j ≤ (a : ℕ)}
  have := inv_pair {p : UT r // (p.1.1 : ℕ) < j} {a : Fin r // (a : ℕ) < j}
  rw [← (mp_mergeP k r j).lintegral_comp hg,
    lintegral_shift (fun x => f (pOf k r (merge k r j x))) (hg.comp (mp_mergeP k r j).measurable) _ (meas_shift k r j)]
  simp only [mul_eq]

end GlobalTheory.Amp.PSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantIntegrable
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count
open scoped InnerProductSpace

namespace GlobalTheory.Count.Majorant

theorem decE_le_exp (q : ℕ) (hq : 1 ≤ q) (h d : ℝ) (hh : 0 ≤ h) (hd : 0 ≤ d) :
    decE q h d ≤ Real.exp (h / 8) * Real.exp (-(h / (8 * Real.sqrt q) * d)) := by
  have hs : (1 : ℝ) ≤ Real.sqrt q := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hq)
  have hm : d / Real.sqrt q - 1 ≤ min (2 * d ^ 2) (d / Real.sqrt q) := by
    have h1 : d / Real.sqrt q ≤ d := div_le_self hd hs
    exact le_min (by nlinarith [sq_nonneg (d - 1 / 4)]) (by linarith)
  have key : h / (8 * Real.sqrt q) * d = h / 8 * (d / Real.sqrt q) := by
    rw [div_mul_eq_mul_div, div_mul_div_comm]
  have hmul := mul_le_mul_of_nonneg_left hm (by linarith : (0 : ℝ) ≤ h / 8)
  unfold GlobalTheory.Count.decE
  rw [← Real.exp_add, Real.exp_le_exp, key]
  nlinarith [hmul]

theorem dOp_eq_zero {n : ℕ} (ε : Fin n → Bool) (h0 : rkR ε = 0) (g : UJ ε) : dOp (uMat g) = 0 := by
  have hall : (∀ a, ε a = false) ∨ (∀ a, ε a = true) := by
    unfold GlobalTheory.Count.rkR at h0
    rcases Nat.min_eq_zero_iff.mp h0 with h1 | h1
    · left
      intro a
      have ha : a ∉ univ.filter (fun a => ε a = true) := by
        rw [Finset.card_eq_zero.mp h1]; simp
      simpa using ha
    · right
      intro a
      have ha : a ∉ univ.filter (fun a => ε a = false) := by
        rw [Finset.card_eq_zero.mp h1]; simp
      simpa using ha
  have hJ : Jm ε = 1 ∨ Jm ε = -1 := by
    rcases hall with hf | ht
    · right
      ext i j
      by_cases hij : i = j <;> simp [Jm, Matrix.diagonal_apply, Matrix.one_apply, hf, hij]
    · left
      ext i j
      by_cases hij : i = j <;> simp [Jm, Matrix.diagonal_apply, Matrix.one_apply, ht, hij]
  have hg : inUJ ε (uMat g) := g.2
  have hu : uMat g ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
    unfold inUJ at hg
    rcases hJ with hJ | hJ <;> rw [hJ] at hg <;> simpa using hg
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    unfold GlobalTheory.Count.dOp
    have hle : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (uMat g))‖ ≤ 0 :=
      ContinuousLinearMap.opNorm_le_bound _ le_rfl fun x => by simp [EuclideanSpace.norm_eq]
    rw [le_antisymm hle (norm_nonneg _), Real.log_zero]
  · have hP0 : inP ε (0 : Matrix (Fin n) (Fin n) ℂ) := by simp [inP, inG]
    obtain ⟨hb0, hb1, -⟩ := GlobalTheory.Count.Cartan.dOp_bounds hn hu hP0
    rw [NormedSpace.exp_zero, mul_one] at hb0 hb1
    have hs0 : hs (0 : Matrix (Fin n) (Fin n) ℂ) = 0 := by simp [hs]
    rw [hs0, Real.sqrt_zero] at hb1
    nlinarith [Real.sqrt_pos.mpr (two_pos : (0 : ℝ) < 2)]

theorem majorant_integrable : ∀ (n : ℕ) (ε : Fin n → Bool) (h s : ℝ), 0 ≤ h → (rkR ε = 0 ∨ 8 * Real.sqrt (rkR ε) * (s + 4 * n * rkR ε) < h) → Integrable (fun g : UJ ε => decE (rkR ε) h (dOp (uMat g)) * Real.exp (s * dOp (uMat g))) (muG ε) := by
  intro n ε h s hh hcase
  obtain ⟨C, -, hC⟩ := _root_.GlobalTheory.BallVol.ballVol n ε
  have hcont : Continuous (fun g : UJ ε => dOp (uMat g)) :=
    (GlobalTheory.Count.Cartan.cartan_distances n ε).2.2.2.2
  have hmeas : Measurable (fun g : UJ ε => dOp (uMat g)) := hcont.measurable
  have hdec : Continuous (decE (rkR ε) h) := by
    unfold GlobalTheory.Count.decE
    fun_prop
  have hint_meas : AEStronglyMeasurable
      (fun g : UJ ε => decE (rkR ε) h (dOp (uMat g)) * Real.exp (s * dOp (uMat g))) (muG ε) :=
    ((hdec.comp hcont).mul (Real.continuous_exp.comp (continuous_const.mul hcont))).aestronglyMeasurable
  by_cases hq : rkR ε = 0
  · have hz : ∀ g : UJ ε, dOp (uMat g) = 0 := fun g => dOp_eq_zero ε hq g
    have hI := _root_.GlobalTheory.integrable_exp_neg_mul_of_sublevel_growth (UJ ε) (muG ε) (fun g => dOp (uMat g)) (4 * n * rkR ε)
      (4 * n * rkR ε + 1) C hmeas (fun g => by simp [hz g]) hC (by linarith)
    refine hI.congr (ae_of_all _ fun g => ?_)
    simp [hz g, GlobalTheory.Count.decE]
  · have hq1 : 1 ≤ rkR ε := Nat.one_le_iff_ne_zero.mpr hq
    have hlt : 8 * Real.sqrt (rkR ε) * (s + 4 * n * rkR ε) < h := hcase.resolve_left hq
    have hrk : rkR ε ≤ n := by
      unfold GlobalTheory.Count.rkR
      exact (min_le_left _ _).trans ((Finset.card_le_univ _).trans (Fintype.card_fin n).le)
    have hn : 1 ≤ n := hq1.trans hrk
    have hpos : ∀ g : UJ ε, 0 ≤ dOp (uMat g) := fun g =>
      ((GlobalTheory.Count.Cartan.cartan_distances n ε).2.1 g g hn).1
    have hsq : 0 < Real.sqrt (rkR ε) := Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hq)
    have hab : (4 * n * rkR ε : ℝ) < h / (8 * Real.sqrt (rkR ε)) - s := by
      have : s + 4 * n * rkR ε < h / (8 * Real.sqrt (rkR ε)) :=
        (lt_div_iff₀ (by linarith : (0 : ℝ) < 8 * Real.sqrt (rkR ε))).mpr (by linarith)
      linarith
    have hI := (_root_.GlobalTheory.integrable_exp_neg_mul_of_sublevel_growth (UJ ε) (muG ε) (fun g => dOp (uMat g)) (4 * n * rkR ε)
      (h / (8 * Real.sqrt (rkR ε)) - s) C hmeas hpos hC hab).const_mul (Real.exp (h / 8))
    refine hI.mono' hint_meas (ae_of_all _ fun g => ?_)
    have hd := hpos g
    have hE := decE_le_exp (rkR ε) hq1 h (dOp (uMat g)) hh hd
    have hnn : 0 ≤ decE (rkR ε) h (dOp (uMat g)) * Real.exp (s * dOp (uMat g)) := by
      unfold GlobalTheory.Count.decE
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    calc decE (rkR ε) h (dOp (uMat g)) * Real.exp (s * dOp (uMat g))
        ≤ Real.exp (h / 8) * Real.exp (-(h / (8 * Real.sqrt (rkR ε)) * dOp (uMat g))) *
            Real.exp (s * dOp (uMat g)) := mul_le_mul_of_nonneg_right hE (Real.exp_pos _).le
      _ = Real.exp (h / 8) * Real.exp (-((h / (8 * Real.sqrt (rkR ε)) - s) * dOp (uMat g))) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring

end GlobalTheory.Count.Majorant
end

