module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.DerivExistsAllPosStatement
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle0002

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.Stable
section
noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem KRep.op_curve {ε : Fin n → Bool} (R : KRep ε)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inK ε X) (γ : ℝ → KG ε)
    (hγ : ∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) (t : ℝ) :
    R.op (γ t) = NormedSpace.exp ((t : ℂ) • R.dτ X) := by
  set A := R.dτ X with hA
  have hmulK : ∀ a b : KG ε, toMK (a * b) = toMK a * toMK b := fun a b => rfl
  have honeK : toMK (1 : KG ε) = 1 := rfl
  have hγadd : ∀ s u : ℝ, γ (s + u) = γ s * γ u := by
    intro s u
    apply onep_KG_ext
    rw [hmulK, hγ, hγ, hγ, Complex.ofReal_add, add_smul]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)
  have hop : ∀ a b : KG ε, R.op (a * b) = R.op a * R.op b := by
    intro a b
    simp [KRep.op]
  have hγ0 : γ 0 = 1 := by
    apply onep_KG_ext
    rw [hγ, honeK]
    simp
  have hd0 : HasDerivAt (fun t => R.op (γ t)) A 0 := R.hasDeriv X hX γ hγ
  have hd : ∀ s : ℝ, HasDerivAt (fun t => R.op (γ t)) (R.op (γ s) * A) s := by
    intro s
    have h1 : HasDerivAt (fun t => R.op (γ (t - s))) A s :=
      HasDerivAt.comp_sub_const (f := fun t => R.op (γ t)) s s (by rwa [sub_self])
    refine (h1.const_mul (R.op (γ s))).congr_of_eventuallyEq ?_
    filter_upwards with u
    rw [← hop, ← hγadd, add_sub_cancel]
  have hE : ∀ s : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp (u • -A))
      (NormedSpace.exp (s • -A) * -A) s := fun s => hasDerivAt_exp_smul_const (-A) s
  have hcomm : ∀ s : ℝ, Commute A (NormedSpace.exp (s • -A)) := fun s =>
    (((Commute.refl A).neg_right).smul_right s).exp_right
  have hh : ∀ s : ℝ, HasDerivAt (fun u => R.op (γ u) * NormedSpace.exp (u • -A)) 0 s := by
    intro s
    have := (hd s).mul (hE s)
    have key : R.op (γ s) * A * NormedSpace.exp (s • -A) +
        R.op (γ s) * (NormedSpace.exp (s • -A) * -A) = 0 := by
      rw [mul_assoc, (hcomm s).eq, mul_neg, mul_neg, add_neg_cancel]
    rw [key] at this
    exact this
  have hconst : ∀ u : ℝ, R.op (γ u) * NormedSpace.exp (u • -A) = 1 := by
    intro u
    have := is_const_of_deriv_eq_zero (f := fun u => R.op (γ u) * NormedSpace.exp (u • -A))
      (fun s => (hh s).differentiableAt) (fun s => (hh s).deriv) u 0
    rw [this]
    simp [hγ0, KRep.op]
  have hinv : NormedSpace.exp (t • -A) * NormedSpace.exp (t • A) = 1 := by
    have hk : ∀ s : ℝ, HasDerivAt (fun u : ℝ => NormedSpace.exp (u • -A) * NormedSpace.exp (u • A))
        0 s := by
      intro s
      have := (hE s).mul (hasDerivAt_exp_smul_const A s)
      have hcF : Commute (NormedSpace.exp (s • A)) A := ((Commute.refl A).smul_left s).exp_left
      have key : NormedSpace.exp (s • -A) * -A * NormedSpace.exp (s • A) +
          NormedSpace.exp (s • -A) * (NormedSpace.exp (s • A) * A) = 0 := by
        rw [mul_assoc, neg_mul, mul_neg, hcF.eq, neg_add_cancel]
      rw [key] at this
      exact this
    have := is_const_of_deriv_eq_zero
      (f := fun u : ℝ => NormedSpace.exp (u • -A) * NormedSpace.exp (u • A))
      (fun s => (hk s).differentiableAt) (fun s => (hk s).deriv) t 0
    rw [this]
    simp
  calc R.op (γ t) = R.op (γ t) * (NormedSpace.exp (t • -A) * NormedSpace.exp (t • A)) := by
        rw [hinv, mul_one]
    _ = NormedSpace.exp (t • A) := by rw [← mul_assoc, hconst, one_mul]
    _ = NormedSpace.exp ((t : ℂ) • A) := by rw [Complex.coe_smul]

theorem KRep.op_eq_exp {ε : Fin n → Bool} (R : KRep ε) (k : KG ε) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, inK ε Y ∧ R.op k = NormedSpace.exp (R.dτ Y) := by
  obtain ⟨Y, hY, hk⟩ := exists_log ε k
  obtain ⟨γ, hγ⟩ := exists_curve ε hY
  have h1 : γ 1 = k := by
    apply onep_KG_ext
    rw [hγ 1, hk, Complex.ofReal_one, one_smul]
  refine ⟨Y, hY, ?_⟩
  rw [← h1, R.op_curve hY γ hγ 1, Complex.ofReal_one, one_smul]

theorem KRep.dτ_stable_of_stable {ε : Fin n → Bool} (R : KRep ε)
    (W : Submodule ℂ R.V) (hW : ∀ k : KG ε, ∀ v ∈ W, R.op k v ∈ W) :
    ∀ a b, ε a = ε b → ∀ v ∈ W, R.dτ (Matrix.single a b 1) v ∈ W := by
  have hK : ∀ X, inK ε X → ∀ v ∈ W, R.dτ X v ∈ W := by
    intro X hX v hv
    obtain ⟨γ, hγ⟩ := exists_curve ε hX
    have hd := R.hasDeriv X hX γ hγ
    let L : (R.V →L[ℂ] R.V) →L[ℝ] R.V := (ContinuousLinearMap.apply ℂ R.V v).restrictScalars ℝ
    have hdv : HasDerivAt (fun t => R.op (γ t) v) (R.dτ X v) 0 :=
      L.hasFDerivAt.comp_hasDerivAt 0 hd
    have hclosed : IsClosed (W : Set R.V) := W.closed_of_finiteDimensional
    refine hclosed.mem_of_tendsto hdv.tendsto_slope_zero (Filter.Eventually.of_forall fun t => ?_)
    exact W.smul_of_tower_mem _ (W.sub_mem (hW _ v hv) (hW _ v hv))
  intro a b hab v hv
  have hX1 : inK ε (Matrix.single a b (1 : ℂ) - Matrix.single b a 1) := by
    apply inK_of_skew_comm
    · simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_single]
    · rw [sub_mul, mul_sub, single_mul_Jm_comm hab, single_mul_Jm_comm hab.symm]
  have hX2 : inK ε (Complex.I • (Matrix.single a b (1 : ℂ) + Matrix.single b a 1)) := by
    apply inK_of_skew_comm
    · simp [Matrix.conjTranspose_add, Matrix.conjTranspose_single, add_comm,
        Matrix.single_neg]
    · rw [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, single_mul_Jm_comm hab,
        single_mul_Jm_comm hab.symm]
  have hI : -Complex.I / 2 * Complex.I = 1 / 2 := by
    rw [div_mul_eq_mul_div, neg_mul, Complex.I_mul_I]
    norm_num
  have hdec : Matrix.single a b (1 : ℂ) =
      (1 / 2 : ℂ) • (Matrix.single a b (1 : ℂ) - Matrix.single b a 1) +
        (-Complex.I / 2) • (Complex.I • (Matrix.single a b (1 : ℂ) + Matrix.single b a 1)) := by
    rw [smul_smul, hI]
    module
  rw [hdec, map_add (f := _), map_smul, map_smul, _root_.add_apply,
    _root_.smul_apply, _root_.smul_apply]
  exact W.add_mem (W.smul_mem _ (hK _ hX1 v hv)) (W.smul_mem _ (hK _ hX2 v hv))

theorem KRep.stable_of_dτ_stable {ε : Fin n → Bool} (R : KRep ε) (W : Submodule ℂ R.V)
    (hW : ∀ a b, ε a = ε b → ∀ v ∈ W, R.dτ (Matrix.single a b 1) v ∈ W) :
    ∀ k : KG ε, ∀ v ∈ W, R.op k v ∈ W := by
  intro k v hv
  obtain ⟨Y, hY, hk⟩ := R.op_eq_exp k
  rw [hk]
  refine exp_mem_of_stable W (R.dτ Y) ?_ v hv
  intro w hw
  rw [Matrix.matrix_eq_sum_single Y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, FunLike.coe_sum, Finset.sum_apply]
  refine W.sum_mem fun a _ => W.sum_mem fun b _ => ?_
  by_cases hab : ε a = ε b
  · rw [show Matrix.single a b (Y a b) = Y a b • Matrix.single a b 1 by
        rw [Matrix.smul_single, smul_eq_mul, mul_one],
      map_smul, _root_.smul_apply]
    exact W.smul_mem _ (hW a b hab w hw)
  · rw [inK_entry_eq_zero hY hab, Matrix.single_zero, map_zero]
    exact W.zero_mem

theorem kRepStable : KRepStableStatement := by
  intro n ε R W
  constructor
  · intro h a b hab x hx
    exact R.dτ_stable_of_stable W h a b hab x hx
  · intro h
    exact R.stable_of_dτ_stable W (fun a b hab x hx => h a b hab x hx)

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ContinuousRepresentations.URepCompRedOf
section
noncomputable section

open Matrix Filter Topology
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.HW

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

lemma inUJ_of_mem_K (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) : inUJ ε g := by
  simp only [Kset, inUJ, Set.mem_setOf_eq] at *
  obtain ⟨hu, hc⟩ := hg
  have h1 : star g * g = 1 := Matrix.mem_unitaryGroup_iff'.mp hu
  rw [Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose, h1, Matrix.one_mul]

def cr2K (ε : Fin n → Bool) {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) : KG ε :=
  ⟨⟨⟨g, star g, Unitary.mul_star_self_of_mem hg.1, Unitary.star_mul_self_of_mem hg.1⟩,
    inUJ_of_mem_K ε hg⟩, hg⟩

lemma KRep.actM_units {ε : Fin n → Bool} (R : KRep ε) (X : Matrix (Fin n) (Fin n) ℂ) (v : R.V) :
    actM R.units X v = R.dτ X v := by
  simp only [KRep.units, actM]
  conv_rhs => rw [Matrix.matrix_eq_sum_single X]
  have h : ∀ a b, Matrix.single a b (X a b) = X a b • Matrix.single a b (1 : ℂ) := by
    intro a b; rw [Matrix.smul_single, smul_eq_mul, mul_one]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [h, map_sum, map_smul]
  simp [LinearMap.sum_apply, ContinuousLinearMap.sum_apply]

def compactRepOfUnitaryDifferential (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] (τ : KG ε →* unitary (H →L[ℂ] H)) (hτ : Continuous τ)
    (dτ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] (H →L[ℂ] H))
    (hd : ∀ X, inK ε X → ∀ γ : ℝ → KG ε,
      (∀ t : ℝ, toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
        HasDerivAt (fun t => ((τ (γ t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H)) (dτ X) 0) : KRep ε :=
  haveI : CompleteSpace H := FiniteDimensional.complete ℂ H
  { V := H, τ := τ, cont := hτ, dτ := dτ, hasDeriv := hd }

theorem uRepCompRed_of (hU : URepHomStatement) (hD : DerivExistsStatement)
    (hR : KRepRelStatement) (hC : CompRedStatement) : URepCompRedStatement := by
  intro n ε H _ _ _ σ hσ
  obtain ⟨τ, hτc, hτ⟩ := hU n ε H σ hσ
  obtain ⟨dτ, hd⟩ := hD n ε H τ hτc
  obtain ⟨hRel, hUnit⟩ := hR n ε (compactRepOfUnitaryDifferential ε H τ hτc dτ hd)
  obtain ⟨m, x, μ, h1, h2, h3, h4, h5, h6⟩ := hC n ε (compactRepOfUnitaryDifferential ε H τ hτc dτ hd)
  refine ⟨(compactRepOfUnitaryDifferential ε H τ hτc dτ hd).units, hRel, hUnit, ?_, m, x, μ, h1, h2, h3, ?_⟩
  · intro X hX v
    have hK : ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Kset ε := fun t =>
      (Formalism.REAL.maximal_compact_facts n ε).2.2.2.1 _ (Formalism.REAL.inK_smul_real ε hX t)
    have hγ : ∀ t : ℝ, toMK (cr2K ε (hK t)) = NormedSpace.exp ((t : ℂ) • X) := fun t => rfl
    have hder := hd X hX (fun t => cr2K ε (hK t)) hγ
    erw [KRep.actM_units (compactRepOfUnitaryDifferential ε H τ hτc dτ hd) X v]
    have hfun : (fun t : ℝ => (σ (NormedSpace.exp ((t : ℂ) • X))) v) =
        fun t : ℝ => (((τ (cr2K ε (hK t)) : unitary (H →L[ℂ] H)) : H →L[ℂ] H)) v := by
      funext t; rw [hτ, hγ]
    rw [hfun]
    have h2 := ((ContinuousLinearMap.apply ℂ H v).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hder
    exact h2
  · refine ⟨?_, ?_⟩
    · intro i g hg v hv
      have := h5 i (cr2K ε hg) v hv
      simp only [KRep.op, compactRepOfUnitaryDifferential] at this
      have e : σ g = ((τ (cr2K ε hg) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) := by
        rw [hτ]; rfl
      rw [e]; exact this
    · intro i
      obtain ⟨T, φ, -, hop, hdτ, hw⟩ := h6 i
      refine ⟨T, φ, ?_, ?_, hw⟩
      · intro k v
        have e : σ (toMK k) = ((τ k : unitary (H →L[ℂ] H)) : H →L[ℂ] H) := (hτ k).symm
        rw [e]; exact hop k v
      · intro a b hab v
        have hc : Matrix.single a b (1 : ℂ) * Jm ε = Jm ε * Matrix.single a b 1 := by
          show Matrix.single a b (1 : ℂ) * Matrix.diagonal _ = Matrix.diagonal _ * Matrix.single a b 1
          ext i j
          rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.single_apply]
          by_cases h : a = i ∧ b = j
          · obtain ⟨rfl, rfl⟩ := h; simp [hab]
          · simp [h]
        exact hdτ _ hc v

end ReciprocityTheory.ChartRestriction.DS.HW
end
end

