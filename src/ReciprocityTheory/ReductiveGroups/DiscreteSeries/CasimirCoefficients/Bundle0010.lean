module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.IsClosedKset
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ContinuousOnFderivPhiP
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0008
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.CasPsB
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ContinuousConjProjection
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0003
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0004
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0009
public import Formalism.FormalDegreeBessel.StatementIO
public import Formalism.FormalDegreeBessel.StatementDS

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.CasLPsM
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

theorem casL_psM (T : KType ε Λ) (μ : Fin n → ℤ) (lam : Fin n → ℝ) (hμ : IsMu lam μ) :
    ∃ U : Set (Matrix (Fin n) (Fin n) ℂ), IsOpen U ∧ posSet n ⊆ U ∧ DifferentiableOn ℂ (psM T μ) U ∧
      (∀ X : Matrix (Fin n) (Fin n) ℂ, DifferentiableOn ℂ (Lhol X (psM T μ)) U) ∧
      ∀ z ∈ U, casL (psM T μ) z = ((casVal lam : ℝ) : ℂ) • psM T μ z := by
  have := compactSpace_KG ε
  have hh := psM_holo T μ
  rcases hh with ⟨U, hUo, hpos, hΩ, hdiff, hfd⟩
  refine ⟨U, hUo, hpos, hdiff, fun X => CasPsB.differentiableOn_lhol T μ hUo hΩ hfd X, fun z hz => ?_⟩
  have hint : ∀ a b : Fin n, Integrable (fun k =>
      CasPsB.FY' T μ (Matrix.single b a 1) z k (Matrix.of.symm (Matrix.single a b 1 * z))) (muK ε) := fun a b =>
    (CasPsB.integrable_K (CasPsB.continuous_FY' T μ hUo hΩ hfd _ hz)).apply_continuousLinearMap _
  calc casL (psM T μ) z
      = ∑ a, ∑ b, ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
          ∫ k, CasPsB.FY' T μ (Matrix.single b a 1) z k (Matrix.of.symm (Matrix.single a b 1 * z)) ∂(muK ε) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          CasPsB.lhol_lhol_psM T μ hUo hΩ hfd _ _ hz
    _ = ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
          ∫ k, ∑ a, ∑ b, CasPsB.FY' T μ (Matrix.single b a 1) z k (Matrix.of.symm (Matrix.single a b 1 * z)) ∂(muK ε) := by
        rw [integral_finsetSum Finset.univ
          (fun a _ => integrable_finsetSum Finset.univ (fun b _ => hint a b)), Finset.smul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [integral_finsetSum Finset.univ (fun b _ => hint a b), Finset.smul_sum]
    _ = ((Module.finrank ℂ T.V : ℂ) / ((muK ε Set.univ).toReal : ℂ)) •
          ∫ k, ((casVal lam : ℝ) : ℂ) • (PhiM μ (toMK k⁻¹ * z * toMK k) •
            (T.op k * projW T * T.op k⁻¹)) ∂(muK ε) := by
        congr 1
        exact integral_congr_ae (Filter.Eventually.of_forall fun k =>
          CasPsB.sum_FY' T μ lam hμ k (hΩ z hz k))
    _ = ((casVal lam : ℝ) : ℂ) • psM T μ z := by
        rw [integral_smul, smul_comm]
        rfl

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.DecPos
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {ε : Fin n → Bool} {Λ : Fin n → ℝ}

private abbrev dpP (T : KType ε Λ) (k : KG ε) : T.V →L[ℂ] T.V := T.op k * projW T * T.op k⁻¹

private lemma dp_op_inv (T : KType ε Λ) (k : KG ε) :
    T.op k⁻¹ = ContinuousLinearMap.adjoint (T.op k) := by
  exact op_inv_eq_adjoint T k

private lemma dpP_apply (T : KType ε Λ) (k : KG ε) (v : T.V) :
    dpP T k v = ⟪T.op k T.w, v⟫_ℂ • T.op k T.w := by
  show T.op k (projW T (T.op k⁻¹ v)) = _
  unfold projW
  rw [ContinuousLinearMap.smulRight_apply, map_smul, dp_op_inv]
  congr 1
  exact ContinuousLinearMap.adjoint_inner_right _ _ _

private lemma dp_inner_P (T : KType ε Λ) (k : KG ε) (v : T.V) :
    ⟪v, dpP T k v⟫_ℂ = ((‖⟪T.op k T.w, v⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
  rw [dpP_apply, inner_smul_right, ← inner_conj_symm v (T.op k T.w)]
  first
  | (rw [RCLike.mul_conj]; rfl)
  | (rw [RCLike.mul_conj]; norm_cast)
  | (rw [RCLike.mul_conj]; push_cast; ring)
  | (rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring)
  | simp [RCLike.mul_conj]

private lemma dp_cont_P (T : KType ε Λ) : Continuous (dpP T) := by
  have hop : Continuous fun k : KG ε => T.op k := continuous_subtype_val.comp T.cont
  have hinv : Continuous fun k : KG ε => T.op k⁻¹ := hop.comp continuous_inv
  exact (hop.mul continuous_const).mul hinv

private lemma dp_integrable (T : KType ε Λ) {g : KG ε → ℝ} (hg : Continuous g) :
    Integrable (fun k => ((g k : ℝ) : ℂ) • dpP T k) (muK ε) := by
  haveI := compactSpace_KG ε
  have hf : Continuous (fun k => ((g k : ℝ) : ℂ) • dpP T k) :=
    (Complex.continuous_ofReal.comp hg).smul (dp_cont_P T)
  exact integrableOn_univ.mp (ContinuousOn.integrableOn_compact isCompact_univ hf.continuousOn)

private lemma dp_isPositive (T : KType ε Λ) {c : ℝ} (hc : 0 ≤ c) {g : KG ε → ℝ} (hg : Continuous g)
    (hg0 : ∀ k, 0 ≤ g k) :
    ((c : ℂ) • ∫ k, ((g k : ℝ) : ℂ) • dpP T k ∂(muK ε)).IsPositive := by
  have hI := dp_integrable T hg

  have key : ∀ u v : T.V, ⟪u, (∫ k, ((g k : ℝ) : ℂ) • dpP T k ∂(muK ε)) v⟫_ℂ =
      ∫ k, ((g k : ℝ) : ℂ) * ⟪u, dpP T k v⟫_ℂ ∂(muK ε) := by
    intro u v
    have hIv : Integrable (fun k => (((g k : ℝ) : ℂ) • dpP T k) v) (muK ε) :=
      (ContinuousLinearMap.apply ℂ T.V v).integrable_comp hI
    rw [ContinuousLinearMap.integral_apply hI, ← integral_inner hIv]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [ContinuousLinearMap.smul_apply, inner_smul_right]

  have hsym : ∀ k (u v : T.V), ⟪dpP T k u, v⟫_ℂ = ⟪u, dpP T k v⟫_ℂ := by
    intro k u v
    rw [dpP_apply, dpP_apply, inner_smul_left, inner_smul_right, inner_conj_symm]
    ring
  refine ⟨?_, ?_⟩
  · intro u v
    change ⟪(((c : ℝ) : ℂ) • ∫ k, ((g k : ℝ) : ℂ) • dpP T k ∂(muK ε)) u, v⟫_ℂ =
      ⟪u, (((c : ℝ) : ℂ) • ∫ k, ((g k : ℝ) : ℂ) • dpP T k ∂(muK ε)) v⟫_ℂ
    rw [ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right,
      ← inner_conj_symm _ v, key, key, ← integral_conj, Complex.conj_ofReal]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only
    rw [map_mul, Complex.conj_ofReal, inner_conj_symm, hsym]
  · intro v
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm, ContinuousLinearMap.smul_apply,
      inner_smul_right, key]
    have e : ∫ k, ((g k : ℝ) : ℂ) * ⟪v, dpP T k v⟫_ℂ ∂(muK ε) =
        ((∫ k, g k * ‖⟪T.op k T.w, v⟫_ℂ‖ ^ 2 ∂(muK ε) : ℝ) : ℂ) := by
      first
      | rw [← integral_complex_ofReal]
      | rw [← integral_ofReal]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      simp only [dp_inner_P]
      push_cast
      ring
    rw [e, ← Complex.ofReal_mul]
    simp only [RCLike.re_to_complex, Complex.ofReal_re]
    exact mul_nonneg hc (integral_nonneg fun k => mul_nonneg (hg0 k) (sq_nonneg _))

private lemma dp_posDef_conj (k : KG ε) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    (toMK k⁻¹ * x * toMK k).PosDef := by
  have hinj : Function.Injective (toMK k).mulVec := by
    intro a b h
    have h2 := congrArg ((toMK k)ᴴ).mulVec h
    simpa [Matrix.mulVec_mulVec, (toMK_facts k).1] using h2
  rw [toMK_inv]
  exact hx.conjTranspose_mul_mul_same hinj

private lemma dp_cont_phi (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    Continuous (fun k : KG ε => (PhiM μ (toMK k⁻¹ * x * toMK k)).re) := by
  have htoMK : Continuous (toMK : KG ε → Matrix (Fin n) (Fin n) ℂ) := by
    unfold toMK toM
    first
    | fun_prop
    | continuity
    | exact continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hcont : Continuous fun k : KG ε => toMK k⁻¹ * x * toMK k :=
    ((htoMK.comp continuous_inv).mul continuous_const).mul htoMK
  have hmem : ∀ k : KG ε, toMK k⁻¹ * x * toMK k ∈ OmegaSet n := by
    intro k
    first
    | exact posSet_subset_omega (dp_posDef_conj k hx)
    | exact posSet_subset_omega (by simpa [posSet] using dp_posDef_conj k hx)
  exact Complex.continuous_re.comp
    ((phiM_differentiableOn μ).continuousOn.comp_continuous hcont hmem)

theorem psM_norm_le (T : KType ε Λ) (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) {B : ℝ}
    (hB : ∀ k : KG ε, (PhiM μ (toMK k⁻¹ * x * toMK k)).re ≤ B) : ‖psM T μ x‖ ≤ B := by
  set c : ℝ := (Module.finrank ℂ T.V : ℝ) / (muK ε Set.univ).toReal with hc_def
  have hc : 0 ≤ c := div_nonneg (Nat.cast_nonneg _) (muK_univ_pos ε).le
  set g : KG ε → ℝ := fun k => (PhiM μ (toMK k⁻¹ * x * toMK k)).re with hg_def
  have hgc : Continuous g := dp_cont_phi μ hx
  have hg0 : ∀ k, 0 ≤ g k := fun k => (phiM_posDef μ (dp_posDef_conj k hx)).1.le
  have hPhi : ∀ k, PhiM μ (toMK k⁻¹ * x * toMK k) = ((g k : ℝ) : ℂ) := by
    intro k
    apply Complex.ext
    · simp [hg_def]
    · simp [(phiM_posDef μ (dp_posDef_conj k hx)).2]
  have hA : psM T μ x = ((c : ℝ) : ℂ) • ∫ k, ((g k : ℝ) : ℂ) • dpP T k ∂(muK ε) := by
    unfold psM
    rw [hc_def]
    push_cast
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [hPhi, dpP]
  have hone : (1 : T.V →L[ℂ] T.V) = ((c : ℝ) : ℂ) • ∫ k, (((fun _ => (1 : ℝ)) k : ℝ) : ℂ) • dpP T k ∂(muK ε) := by
    rw [← psM_one T μ]
    unfold psM
    rw [hc_def]
    push_cast
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    have h1 : toMK k⁻¹ * 1 * toMK k = 1 := by rw [Matrix.mul_one, toMK_inv, (toMK_facts k).1]
    simp only [h1, phiM_one, one_smul, dpP]
  have i1 := dp_integrable T (g := fun _ => (1 : ℝ)) continuous_const
  have i2 := dp_integrable T hgc
  have hlin : ∫ k, (((fun k => B - g k) k : ℝ) : ℂ) • dpP T k ∂(muK ε) =
      (B : ℂ) • (∫ k, (((fun _ => (1 : ℝ)) k : ℝ) : ℂ) • dpP T k ∂(muK ε)) -
        ∫ k, ((g k : ℝ) : ℂ) • dpP T k ∂(muK ε) := by
    have i1' : Integrable (fun k => (B : ℂ) • ((((fun _ => (1 : ℝ)) k : ℝ) : ℂ) • dpP T k)) (muK ε) :=
      i1.smul (B : ℂ)
    have e1 := integral_sub i1' i2
    rw [integral_smul] at e1
    refine (integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)).trans e1
    beta_reduce
    rw [smul_smul, ← sub_smul]
    congr 1
    push_cast
    ring
  have hdiff : (B : ℂ) • (1 : T.V →L[ℂ] T.V) - psM T μ x =
      ((c : ℝ) : ℂ) • ∫ k, (((fun k => B - g k) k : ℝ) : ℂ) • dpP T k ∂(muK ε) := by
    rw [hlin, smul_sub, smul_comm ((c : ℝ) : ℂ) (B : ℂ), ← hone, ← hA]
  have hpos1 := dp_isPositive T hc hgc hg0
  have hpos2 := dp_isPositive T hc (g := fun k => B - g k) (continuous_const.sub hgc)
    (fun k => sub_nonneg.mpr (hB k))
  have h0 : 0 ≤ psM T μ x := by
    rw [ContinuousLinearMap.nonneg_iff_isPositive, hA]
    exact hpos1
  have hle : psM T μ x ≤ (B : ℂ) • (1 : T.V →L[ℂ] T.V) := by
    rw [ContinuousLinearMap.le_def, hdiff]
    exact hpos2
  have hB0 : 0 ≤ B := (hg0 1).trans (hB 1)
  calc ‖psM T μ x‖ ≤ ‖(B : ℂ) • (1 : T.V →L[ℂ] T.V)‖ :=
      CStarAlgebra.norm_le_norm_of_le_of_nonneg hle h0
    _ ≤ ‖(B : ℂ)‖ * ‖(1 : T.V →L[ℂ] T.V)‖ := norm_smul_le _ _
    _ ≤ B * 1 := by
        rw [Complex.norm_real, Real.norm_of_nonneg hB0]
        exact mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le hB0
    _ = B := mul_one B

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.GelfandPhi
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem single_mul_single_one (i j k l : Fin n) :
    Matrix.single i j (1 : ℂ) * Matrix.single k l 1 = if j = k then Matrix.single i l 1 else 0 := by
  split_ifs with h
  · subst h
    rw [Matrix.single_mul_single_same, mul_one]
  · exact Matrix.single_mul_single_of_ne _ _ _ _ h _

theorem lhol_neg (X : Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (z : Matrix (Fin n) (Fin n) ℂ) : Lhol (-X) F z = -Lhol X F z := by
  simp [Lhol, Matrix.neg_mul]

theorem phiM_contDiffOn (μ : Fin n → ℤ) : ContDiffOn ℂ ∞ (PhiM μ) (OmegaSet n) :=
  fun _ hz => (contDiffAt_phiM μ hz).contDiffWithinAt

def phiT (μ : Fin n → ℤ) : smoothS n :=
  ⟨(OmegaSet n).indicator (PhiM μ), (phiM_contDiffOn μ).congr fun _ hz => Set.indicator_of_mem hz _⟩

theorem phiT_eqOn (μ : Fin n → ℤ) :
    Set.EqOn (PhiM μ) ((phiT μ : smoothS n) : Matrix (Fin n) (Fin n) ℂ → ℂ) (OmegaSet n) :=
  fun _ hz => (Set.indicator_of_mem hz _).symm

theorem eOp_phiT (μ : Fin n → ℤ) (X : Matrix (Fin n) (Fin n) ℂ) (c : ℂ)
    (h : ∀ z ∈ OmegaSet n, Lhol X (PhiM μ) z = c * PhiM μ z) : eOp X (phiT μ) = c • phiT μ := by
  apply Subtype.ext
  funext z
  rw [eOp_apply]
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  by_cases hz : z ∈ OmegaSet n
  · rw [ltOp_of_mem _ hz, lhol_congr (phiT_eqOn μ).symm hz, h z hz, ← phiT_eqOn μ hz]
  · rw [ltOp_of_not_mem _ hz]
    simp [phiT, Set.indicator_apply, hz]

def xRev (n : ℕ) : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ :=
  fun a b => -Matrix.single (Fin.rev a) (Fin.rev b) 1

def xTr (n : ℕ) : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ :=
  fun a b => Matrix.single b a 1

theorem xRev_rel (a b c d : Fin n) : xRev n c d * xRev n a b - xRev n a b * xRev n c d =
    (if b = c then xRev n a d else 0) - (if d = a then xRev n c b else 0) := by
  unfold xRev
  rw [neg_mul_neg, neg_mul_neg, single_mul_single_one, single_mul_single_one]
  by_cases h1 : b = c
  · subst h1
    by_cases h2 : d = a
    · subst h2
      simp <;> abel
    · simp [h2, Ne.symm h2]
  · by_cases h2 : d = a
    · subst h2
      simp [h1, Ne.symm h1]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

theorem xTr_rel (a b c d : Fin n) : xTr n c d * xTr n a b - xTr n a b * xTr n c d =
    (if b = c then xTr n a d else 0) - (if d = a then xTr n c b else 0) := by
  unfold xTr
  rw [single_mul_single_one, single_mul_single_one]
  by_cases h1 : b = c
  · subst h1
    by_cases h2 : d = a
    · subst h2
      simp <;> abel
    · simp [h2, Ne.symm h2]
  · by_cases h2 : d = a
    · subst h2
      simp [h1, Ne.symm h1]
    · simp [h1, h2, Ne.symm h1, Ne.symm h2]

theorem hw_rev (μ : Fin n → ℤ) :
    IsHWVec (fun a b => eOp (xRev n a b)) (fun a => ((μ (Fin.rev a) : ℤ) : ℝ)) (phiT μ) := by
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · refine eOp_phiT μ _ _ fun z hz => ?_
    unfold xRev
    rw [lhol_neg, lhol_phiM_diag μ _ hz]
    push_cast
    ring
  · have h0 : eOp (xRev n a b) (phiT μ) = (0 : ℂ) • phiT μ := by
      refine eOp_phiT μ _ _ fun z hz => ?_
      unfold xRev
      rw [lhol_neg, lhol_phiM_lower μ (Fin.rev_lt_rev.2 hab) hz]
      simp
    rw [h0, zero_smul]

theorem hw_tr (μ : Fin n → ℤ) :
    IsHWVec (fun a b => eOp (xTr n a b)) (fun a => -((μ a : ℤ) : ℝ)) (phiT μ) := by
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · refine eOp_phiT μ _ _ fun z hz => ?_
    unfold xTr
    rw [lhol_phiM_diag μ _ hz]
    push_cast
    ring
  · have h0 : eOp (xTr n a b) (phiT μ) = (0 : ℂ) • phiT μ := by
      refine eOp_phiT μ _ _ fun z hz => ?_
      unfold xTr
      rw [lhol_phiM_lower μ hab hz]
      simp
    rw [h0, zero_smul]

theorem rho_rev_add (a : Fin n) : rho n (Fin.rev a) + rho n a = 0 := by
  have ha := a.isLt
  unfold rho
  rw [Fin.val_rev, Nat.cast_sub (by omega : a.val + 1 ≤ n)]
  push_cast
  ring

private theorem gval_comp_perm (l : Fin n → ℂ) (σ : Equiv.Perm (Fin n)) (k : ℕ) :
    gval (fun r => l (σ r)) k = gval l k := by
  have h : (∏ r, (1 - PowerSeries.X * (1 - PowerSeries.C (l (σ r)) * PowerSeries.X)⁻¹)) =
      ∏ r, (1 - PowerSeries.X * (1 - PowerSeries.C (l r) * PowerSeries.X)⁻¹) :=
    Equiv.prod_comp σ (fun r => 1 - PowerSeries.X * (1 - PowerSeries.C (l r) * PowerSeries.X)⁻¹)
  unfold gval gelfandSeries
  beta_reduce
  rw [h]

theorem gelfand_phiM (μ : Fin n → ℤ) (lam : Fin n → ℝ) (hμ : IsMu lam μ) (k : ℕ) {z : Matrix (Fin n) (Fin n) ℂ}
    (hz : z ∈ OmegaSet n) :
    opGelfand (fun a b => Lhol (Matrix.single a b (1 : ℂ))) k (PhiM μ) z =
        ((-1 : ℂ) ^ k * gval (icShift lam) k) * PhiM μ z ∧
      opGelfand (fun a b => Lhol (Matrix.single (Fin.rev b) (Fin.rev a) (1 : ℂ))) k (PhiM μ) z =
        gval (icShift (-lam)) k * PhiM μ z := by
  constructor
  · have hY : ∀ a b, Matrix.single a b (1 : ℂ) = (-1 : ℂ) • xRev n (Fin.revPerm a) (Fin.revPerm b) := by
      intro a b
      simp [xRev]
    have hν : ((fun a => ((μ (Fin.rev a) : ℤ) : ℝ)) + rho n) = fun a => lam (Fin.revPerm a) := by
      funext a
      simp only [Pi.add_apply, Fin.revPerm_apply, hμ (Fin.rev a)]
      have := rho_rev_add (n := n) a
      linarith
    refine (opGelfand_eq (xRev n) _ Fin.revPerm (-1) hY (PhiM μ) (phiT μ) (phiT_eqOn μ) k hz).trans ?_
    rw [gelfand_hw (isGlRep_eOp (xRev n) xRev_rel) (hw_rev μ) k, hν, Submodule.coe_smul, Pi.smul_apply,
      smul_eq_mul, ← phiT_eqOn μ hz]
    rw [show icShift (fun a => lam (Fin.revPerm a)) = fun a => icShift lam (Fin.revPerm a) from rfl,
      gval_comp_perm]
    ring
  · have hY : ∀ a b, Matrix.single (Fin.rev b) (Fin.rev a) (1 : ℂ) =
        (1 : ℂ) • xTr n (Fin.revPerm a) (Fin.revPerm b) := by
      intro a b
      simp [xTr]
    have hν : ((fun a => -((μ a : ℤ) : ℝ)) + rho n) = -lam := by
      funext a
      simp only [Pi.add_apply, Pi.neg_apply, hμ a]
      ring
    refine (opGelfand_eq (xTr n) _ Fin.revPerm 1 hY (PhiM μ) (phiT μ) (phiT_eqOn μ) k hz).trans ?_
    rw [gelfand_hw (isGlRep_eOp (xTr n) xTr_rel) (hw_tr μ) k, hν, Submodule.coe_smul, Pi.smul_apply,
      smul_eq_mul, ← phiT_eqOn μ hz, one_pow, one_mul]

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiCapelliStatement
section
noncomputable section

open Finset MeasureTheory Matrix
open scoped ComplexOrder ContDiff ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.S7

open ReciprocityTheory.ChartRestriction.DS

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def negL (a b : Fin n) (F : Matrix (Fin n) (Fin n) ℂ → E) : Matrix (Fin n) (Fin n) ℂ → E :=
  fun z => -Lhol (Matrix.single a b 1) F z

def PsiCapelliStatement (n : ℕ) : Prop :=
  ∀ (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ), IsMu lam μ →
    ∀ (Y : ℂ) (g : Matrix (Fin n) (Fin n) ℂ), inUJ ε g →
      Formalism.QuantumDeterminants.capelli ε (Y + ((n : ℂ) - 1) / 2) (PsiM T μ) g =
        Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • PsiM T μ g

end ReciprocityTheory.ChartRestriction.DS.S7
end
end

