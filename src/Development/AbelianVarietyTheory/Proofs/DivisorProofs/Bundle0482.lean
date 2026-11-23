module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0462
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0466
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0467
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFDerivAtWeightTwoDerivativeEisensteinTerm
section
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory.WeightTwoSum

theorem norm_cpow_eq_mul_conj_cpow (u s : ℂ) :
    ((‖u‖ : ℝ) : ℂ) ^ (-2 * s) = (u * starRingEnd ℂ u) ^ (-s) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  rw [sq, Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _)]
  rw [show -2 * s = ((2:ℕ):ℂ) * (-s) by push_cast; ring, Complex.cpow_nat_mul, sq]

theorem hasFDerivAt_factor_norm_cpow {I : Type} [Fintype I] (j : I) (a c K σ : ℂ) (n : ℕ) (z : I → ℂ)
    (hu : a + z j * c ≠ 0) :
    HasFDerivAt (𝕜 := ℝ) (fun w : I → ℂ => K * (a + w j * c)⁻¹ ^ n * ((‖a + w j * c‖ : ℝ) : ℂ) ^ (-2 * σ))
      ((K * (a + z j * c)⁻¹ ^ n * ((‖a + z j * c‖ : ℝ) : ℂ) ^ (-2 * σ) * (-((n : ℂ) + σ) * c / (a + z j * c))) • dz j +
       (K * (a + z j * c)⁻¹ ^ n * ((‖a + z j * c‖ : ℝ) : ℂ) ^ (-2 * σ) *
         (-σ * starRingEnd ℂ c / starRingEnd ℂ (a + z j * c))) • dzbar j) z := by
  simp_rw [norm_cpow_eq_mul_conj_cpow]
  set u := a + z j * c with hu_def
  have hU : HasFDerivAt (𝕜 := ℝ) (fun w : I → ℂ => a + w j * c) (c • dz j) z :=
    ((dz j).hasFDerivAt.mul_const c).const_add a
  have hC : HasFDerivAt (𝕜 := ℝ) (fun w : I → ℂ => starRingEnd ℂ (a + w j * c))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (c • dz j)) z :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp z hU
  have hP := hU.mul hC
  have hcu : starRingEnd ℂ u ≠ 0 := (map_ne_zero _).2 hu
  have hne : u * starRingEnd ℂ u ≠ 0 := mul_ne_zero hu hcu
  have hslit : u * starRingEnd ℂ u ∈ Complex.slitPlane := by
    rw [Complex.mul_conj]
    exact Complex.ofReal_mem_slitPlane.2 (Complex.normSq_pos.2 hu)
  have hpow := ((hasDerivAt_id (u * starRingEnd ℂ u)).cpow_const (c := -σ) hslit).comp_hasFDerivAt z hP
  have hinv := (((hasDerivAt_id u).inv hu).pow n).comp_hasFDerivAt z hU
  have h := (hinv.const_mul K).mul hpow
  refine h.congr_fderiv ?_
  ext v
  clear h hinv hpow hP hC hU hslit
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    dz_apply, dzbar_apply, smul_eq_mul, ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_mul,
    Function.comp_apply, id, Pi.inv_apply, Pi.pow_apply, Pi.mul_apply, ← hu_def]
  rw [Complex.cpow_sub _ _ hne, Complex.cpow_one]
  rcases n with _ | n
  · simp
    field_simp
    ring
  · simp only [Nat.add_sub_cancel, inv_pow]
    field_simp
    push_cast
    ring

theorem hasFDerivAt_eTerm : ∀ (E : Type) [Field E] [NumberField E] (I : Type) [Fintype I] [DecidableEq I]
    (φ : I → E →+* ℂ) (m : I → ℕ) (σ : ℂ) (x : E), x ≠ 0 → ∀ z ∈ polydisc I,
    HasFDerivAt (𝕜 := ℝ) (fun w : I → ℂ => eTerm φ m σ w x)
      (∑ j, (eTerm φ (m + Pi.single j 1) σ z x • dz j +
        (eTerm φ m σ z x * (-σ * φ j x / starRingEnd ℂ (defCoord φ z x j))) • dzbar j)) z := by
  intro E _ _ I _ _ φ m σ x hx z hz
  let C : ℕ → ℂ := fun n => (-1 : ℂ) ^ n * ∏ j ∈ Finset.range n, (2 + σ + j)
  let c : I → ℂ := fun i => starRingEnd ℂ (φ i x)
  let F : I → (I → ℂ) → ℂ := fun i w => C (m i) * c i ^ m i * (φ i x + w i * c i)⁻¹ ^ (2 + m i) *
    ((‖φ i x + w i * c i‖ : ℝ) : ℂ) ^ (-2 * σ)
  let α : I → ℂ := fun i => -(((2 + m i : ℕ) : ℂ) + σ) * c i / (φ i x + z i * c i)
  let β : I → ℂ := fun i => -σ * starRingEnd ℂ (c i) / starRingEnd ℂ (φ i x + z i * c i)
  have hF : ∀ i, HasFDerivAt (𝕜 := ℝ) (F i) ((F i z * α i) • dz i + (F i z * β i) • dzbar i) z := fun i =>
    hasFDerivAt_factor_norm_cpow i (φ i x) (c i) (C (m i) * c i ^ m i) σ (2 + m i) z
      (GlobalTheory.DeformedSum.defCoord_ne_zero φ z hz x hx i)
  have hprod := HasFDerivAt.finsetProd (u := Finset.univ) (g := F) (x := z) (fun i _ => hF i)
  have hfun : (fun w : I → ℂ => eTerm φ m σ w x) = fun w => ∏ i ∈ Finset.univ, F i w := rfl
  have hval : eTerm φ m σ z x = ∏ i ∈ Finset.univ, F i z := rfl
  rw [hfun]
  refine hprod.congr_fderiv ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  have key : ∀ (f g : I → ℂ), (∀ i, i ≠ j → g i = f i) →
      ∏ i, g i = (∏ i ∈ Finset.univ.erase j, f i) * g j := by
    intro f g h
    rw [← Finset.prod_erase_mul Finset.univ g (Finset.mem_univ j)]
    congr 1
    exact Finset.prod_congr rfl fun i hi => h i (Finset.ne_of_mem_erase hi)
  rw [smul_add, smul_smul, smul_smul]
  congr 1
  · congr 1
    unfold eTerm
    rw [key (fun i => F i z) _ ?_]
    · congr 1
      simp only [Pi.add_apply, Pi.single_eq_same, F, α, C, c, defCoord, Finset.prod_range_succ, pow_succ]
      push_cast
      ring
    · intro i hij
      simp only [Pi.add_apply, Pi.single_eq_of_ne hij, add_zero]
      rfl
  · congr 1
    rw [hval, ← Finset.prod_erase_mul Finset.univ (fun i => F i z) (Finset.mem_univ j)]
    simp only [β, c, defCoord, Complex.conj_conj]
    ring

end GlobalTheory.WeightTwoSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasStrictFDerivAtMulCurvesMatrixGroupIdentity
section
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal

theorem GlobalTheory.hasStrictFDerivAt_mul_curves_at_identity : ∀ (ι : Type) [Fintype ι] (r : ℕ) (H : Subgroup (ι → GL (Fin r) ℂ)) (W₁ W₂ : Type) [NormedAddCommGroup W₁] [NormedSpace ℝ W₁] [NormedAddCommGroup W₂] [NormedSpace ℝ W₂] (σ : W₁ → H) (t : W₂ → H) (D₁ : W₁ →L[ℝ] (ι → Fin r → Fin r → ℂ)) (D₂ : W₂ →L[ℝ] (ι → Fin r → Fin r → ℂ)), σ 0 = 1 → t 0 = 1 → HasStrictFDerivAt (fun w => fun τ i j => ((((σ w : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j) D₁ 0 → HasStrictFDerivAt (fun w => fun τ i j => ((((t w : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j) D₂ 0 → HasStrictFDerivAt (fun w : W₁ × W₂ => fun τ i j => ((((σ w.1 * t w.2 : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j) (D₁.comp (ContinuousLinearMap.fst ℝ W₁ W₂) + D₂.comp (ContinuousLinearMap.snd ℝ W₁ W₂)) 0 := by
  intro ι _ r H W₁ W₂ _ _ _ _ σ t D₁ D₂ hσ ht h₁ h₂
  set f₁ : W₁ → ι → Fin r → Fin r → ℂ := fun w τ i j =>
    ((((σ w : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j with hf₁
  set f₂ : W₂ → ι → Fin r → Fin r → ℂ := fun w τ i j =>
    ((((t w : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j with hf₂
  have e : (fun w : W₁ × W₂ => fun τ i j =>
      ((((σ w.1 * t w.2 : H) : ι → GL (Fin r) ℂ) τ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ) i j) =
      fun w τ i j => ∑ c, f₁ w.1 τ i c * f₂ w.2 τ c j := by
    funext w τ i j
    simp [hf₁, hf₂, Matrix.mul_apply]
  have z₁ : ∀ τ i c, f₁ 0 τ i c = (1 : Matrix (Fin r) (Fin r) ℂ) i c := by
    intro τ i c; simp [hf₁, hσ]
  have z₂ : ∀ τ c j, f₂ 0 τ c j = (1 : Matrix (Fin r) (Fin r) ℂ) c j := by
    intro τ c j; simp [hf₂, ht]
  have g₁ : HasStrictFDerivAt (fun w : W₁ × W₂ => f₁ w.1)
      (D₁.comp (ContinuousLinearMap.fst ℝ W₁ W₂)) (0 : W₁ × W₂) :=
    h₁.comp (0 : W₁ × W₂) (hasStrictFDerivAt_fst (p := (0 : W₁ × W₂)))
  have g₂ : HasStrictFDerivAt (fun w : W₁ × W₂ => f₂ w.2)
      (D₂.comp (ContinuousLinearMap.snd ℝ W₁ W₂)) (0 : W₁ × W₂) :=
    h₂.comp (0 : W₁ × W₂) (hasStrictFDerivAt_snd (p := (0 : W₁ × W₂)))
  rw [e]
  refine hasStrictFDerivAt_pi'.2 fun τ => hasStrictFDerivAt_pi'.2 fun i =>
    hasStrictFDerivAt_pi'.2 fun j => ?_
  have a₁ : ∀ c, HasStrictFDerivAt (fun w : W₁ × W₂ => f₁ w.1 τ i c)
      ((ContinuousLinearMap.proj c).comp ((ContinuousLinearMap.proj i).comp
        ((ContinuousLinearMap.proj τ).comp (D₁.comp (ContinuousLinearMap.fst ℝ W₁ W₂))))) 0 :=
    fun c => hasStrictFDerivAt_pi'.1 (hasStrictFDerivAt_pi'.1 (hasStrictFDerivAt_pi'.1 g₁ τ) i) c
  have a₂ : ∀ c, HasStrictFDerivAt (fun w : W₁ × W₂ => f₂ w.2 τ c j)
      ((ContinuousLinearMap.proj j).comp ((ContinuousLinearMap.proj c).comp
        ((ContinuousLinearMap.proj τ).comp (D₂.comp (ContinuousLinearMap.snd ℝ W₁ W₂))))) 0 :=
    fun c => hasStrictFDerivAt_pi'.1 (hasStrictFDerivAt_pi'.1 (hasStrictFDerivAt_pi'.1 g₂ τ) c) j
  have hs0 := HasStrictFDerivAt.sum (u := Finset.univ) (A := fun c (w : W₁ × W₂) => f₁ w.1 τ i c * f₂ w.2 τ c j)
    (fun c _ => (a₁ c).mul (a₂ c))
  have ef : (fun w : W₁ × W₂ => ∑ c, f₁ w.1 τ i c * f₂ w.2 τ c j) =
      ∑ c, (fun (w : W₁ × W₂) => f₁ w.1 τ i c * f₂ w.2 τ c j) := by
    funext w
    simp [Finset.sum_apply]
  rw [ef]
  refine hs0.congr_fderiv ?_
  clear ef hs0 a₁ a₂ g₁ g₂ e
  clear_value f₁ f₂
  clear hf₁ hf₂ h₁ h₂ hσ ht σ t
  refine ContinuousLinearMap.ext fun w => ?_
  simp [z₁, z₂, Matrix.one_apply, Finset.sum_add_distrib, ite_mul]
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumDeformedLatticeEisensteinSummandWeightTwo
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory.WeightTwoCompare

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

theorem prodCpow {J : Type} (t : Finset J) (f : J → ℝ) (hf : ∀ j, 0 ≤ f j) (w : ℂ) :
    ∏ j ∈ t, ((f j : ℝ) : ℂ) ^ w = (((∏ j ∈ t, f j : ℝ)) : ℂ) ^ w := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf a) (Finset.prod_nonneg fun j _ => hf j)]

theorem norm_cpow_eq_exp {h : ℂ} (hh : h ≠ 0) (σ : ℂ) :
    ((‖h‖ : ℝ) : ℂ) ^ (-2 * σ) = Complex.exp (-σ * ((Real.log (Complex.normSq h) : ℝ) : ℂ)) := by
  have hn : ((‖h‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hh
  rw [Complex.cpow_def_of_ne_zero hn, ← Complex.ofReal_log (norm_nonneg _), Complex.normSq_eq_norm_sq,
    Real.log_pow]
  congr 1
  push_cast
  ring

variable [IsCMField E]

theorem defCoord_eq (φ : I → E →+* ℂ) (e : I ≃ Emb (maximalRealSubfield E))
    (he : ∀ (i : I) (a : maximalRealSubfield E), φ i (a : E) = ((e i a : ℝ) : ℂ)) (θ : E) {z : I → ℂ}
    (hz : z ∈ polydisc I) (a b : maximalRealSubfield E) (i : I) :
    defCoord φ z ((a : E) + (b : E) * θ) i =
      (1 + z i) / (2 * (Real.pi : ℂ) * Complex.I) * latPt (modPt φ e θ z) (a, b) (e i) := by
  have h1 := one_add_ne_zero hz i
  have hπ : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    exact mul_ne_zero (mul_ne_zero two_ne_zero this) Complex.I_ne_zero
  simp only [defCoord, latPt, modPt, Equiv.symm_apply_apply, map_add (f := _), map_mul, he, Complex.conj_ofReal]
  field_simp
  ring

theorem defTerm_eq (φ : I → E →+* ℂ) (e : I ≃ Emb (maximalRealSubfield E))
    (he : ∀ (i : I) (a : maximalRealSubfield E), φ i (a : E) = ((e i a : ℝ) : ℂ)) (θ : E) {z : I → ℂ}
    (hz : z ∈ polydisc I) (σ : ℂ) (a b : maximalRealSubfield E) :
    defTerm φ 2 z σ ((a : E) + (b : E) * θ) =
      (homFac z)⁻¹ ^ 2 * Complex.exp (-σ * logFac z) * eisTerm 2 σ (modPt φ e θ z) (a, b) := by
  set w := latPt (modPt φ e θ z) (a, b)
  set c : I → ℂ := fun i => (1 + z i) / (2 * (Real.pi : ℂ) * Complex.I)
  have hc : homFac z = ∏ i, c i := rfl
  have hw : ∏ τ, w τ = ∏ i, w (e i) := (Equiv.prod_comp e w).symm
  unfold defTerm eisTerm logFac
  simp only [defCoord_eq φ e he θ hz a b]
  rw [Finset.prod_mul_distrib]
  have h1 : ∏ i, (c i * w (e i))⁻¹ ^ 2 = (homFac z)⁻¹ ^ 2 * (∏ τ, w τ)⁻¹ ^ 2 := by
    rw [hc, hw, ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib, ← Finset.prod_pow, ← Finset.prod_pow,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [mul_inv, mul_pow]
  have h2 : ∏ i, ((‖c i * w (e i)‖ : ℝ) : ℂ) ^ (-2 * σ) =
      ((‖homFac z‖ : ℝ) : ℂ) ^ (-2 * σ) * ((‖∏ τ, w τ‖ : ℝ) : ℂ) ^ (-2 * σ) := by
    rw [prodCpow _ _ (fun i => norm_nonneg _), hc, hw, norm_prod, norm_prod,
      ← Complex.mul_cpow_ofReal_nonneg (Finset.prod_nonneg fun i _ => norm_nonneg _)
        (Finset.prod_nonneg fun i _ => norm_nonneg _), ← Complex.ofReal_mul, ← Finset.prod_mul_distrib]
    simp only [norm_mul]
  rw [h1, h2, norm_cpow_eq_exp (homFac_ne_zero hz)]
  ring

end GlobalTheory.WeightTwoCompare

namespace GlobalTheory.WeightTwoCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem eq_of_add_mul {θ : E} (hθ : θ ∉ maximalRealSubfield E) {a b a' b' : maximalRealSubfield E}
    (h : (a : E) + (b : E) * θ = (a' : E) + (b' : E) * θ) : a = a' ∧ b = b' := by
  by_cases hb : b = b'
  · subst hb
    refine ⟨Subtype.ext ?_, rfl⟩
    simpa using h
  · exfalso
    apply hθ
    have hb' : ((b : E) - (b' : E)) ≠ 0 := by
      intro h0; apply hb; exact Subtype.ext (sub_eq_zero.1 h0)
    have : θ = ((a' : E) - (a : E)) / ((b : E) - (b' : E)) := by
      field_simp
      linear_combination h
    rw [this]
    exact div_mem (sub_mem a'.2 a.2) (sub_mem b.2 b'.2)

end GlobalTheory.WeightTwoCompare

namespace GlobalTheory.WeightTwoCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem algebraMap_unit (u : (OF E)ˣ) :
    algebraMap (OF E) E (u : OF E) = (((u : 𝓞 (maximalRealSubfield E)) : maximalRealSubfield E) : E) := rfl

noncomputable def classMap (𝔞 𝔟 : Frac (maximalRealSubfield E)) (θ : E) (L : Set E) (hθ : θ ∉ maximalRealSubfield E)
    (hL : ∀ x : E, x ∈ L ↔ ∃ a ∈ latM 𝔞, ∃ b ∈ (𝔟 : FractionalIdeal (𝓞 (maximalRealSubfield E))⁰ (maximalRealSubfield E)),
      x = (a : E) + (b : E) * θ)
    (c : Quotient (latRel 𝔞 𝔟)) : modUnits L :=
  ⟨Quotient.mk _ ((c.out.1.1 : E) + (c.out.1.2 : E) * θ),
    (c.out.1.1 : E) + (c.out.1.2 : E) * θ, (hL _).2 ⟨_, c.out.2.1, _, c.out.2.2.1, rfl⟩, fun h0 => c.out.2.2.2 (by
      have h := eq_of_add_mul hθ (a := c.out.1.1) (b := c.out.1.2) (a' := 0) (b' := 0) (by simpa using h0)
      exact Prod.ext h.1 h.2), rfl⟩

end GlobalTheory.WeightTwoCompare

namespace GlobalTheory.WeightTwoCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem classMap_bijective (𝔞 𝔟 : Frac (maximalRealSubfield E)) (θ : E) (L : Set E) (hθ : θ ∉ maximalRealSubfield E)
    (hL : ∀ x : E, x ∈ L ↔ ∃ a ∈ latM 𝔞, ∃ b ∈ (𝔟 : FractionalIdeal (𝓞 (maximalRealSubfield E))⁰ (maximalRealSubfield E)),
      x = (a : E) + (b : E) * θ) :
    Function.Bijective (classMap 𝔞 𝔟 θ L hθ hL) := by
  constructor
  · intro c c' h
    have h1 := Quotient.exact (congrArg Subtype.val h)
    obtain ⟨u, hu⟩ := h1
    rw [algebraMap_unit, mul_add, ← mul_assoc, ← Subfield.coe_mul, ← Subfield.coe_mul] at hu
    obtain ⟨ha, hb⟩ := eq_of_add_mul hθ hu
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    exact Quotient.sound ⟨u, ha, hb⟩
  · rintro ⟨q, x, hxL, hx0, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := (hL x).1 hxL
    have hp : ((a, b) : maximalRealSubfield E × maximalRealSubfield E) ≠ 0 := by
      intro h0
      apply hx0
      have h1 : a = 0 := congrArg Prod.fst h0
      have h2 : b = 0 := congrArg Prod.snd h0
      simp [h1, h2]
    let p : LatPair 𝔞 𝔟 := ⟨(a, b), ha, hb, hp⟩
    refine ⟨Quotient.mk _ p, Subtype.ext ?_⟩
    obtain ⟨ε, h1, h2⟩ : (latRel 𝔞 𝔟).r (Quotient.mk (latRel 𝔞 𝔟) p).out p := Quotient.exact (Quotient.out_eq _)
    show Quotient.mk _ _ = Quotient.mk _ _
    refine Quotient.sound ⟨ε, ?_⟩
    rw [algebraMap_unit]
    have e1 : a = p.1.1 := rfl
    have e2 : b = p.1.2 := rfl
    rw [e1, e2, h1, h2, Subfield.coe_mul, Subfield.coe_mul]
    ring

end GlobalTheory.WeightTwoCompare

namespace GlobalTheory.WeightTwoCompare

theorem hasSum_defTerm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (e : I ≃ Emb (maximalRealSubfield E)), (∀ (i : I) (a : maximalRealSubfield E), φ i (a : E) = ((e i a : ℝ) : ℂ)) →
    ∀ (𝔞 𝔟 : Frac (maximalRealSubfield E)) (θ : E) (L : Set E), θ ∉ maximalRealSubfield E →
    (∀ x : E, x ∈ L ↔ ∃ a ∈ latM 𝔞, ∃ b ∈ (𝔟 : FractionalIdeal (𝓞 (maximalRealSubfield E))⁰ (maximalRealSubfield E)),
      x = (a : E) + (b : E) * θ) →
    ∀ z ∈ polydisc I, ∀ (σ S : ℂ), HasSum (eisClass 𝔞 𝔟 2 σ (modPt φ e θ z)) S →
      HasSum (fun q : modUnits L => defTerm φ 2 z σ q.1.out) ((homFac z)⁻¹ ^ 2 * Complex.exp (-σ * logFac z) * S) := by
  intro E _ _ _ I _ φ e he 𝔞 𝔟 θ L hθ hL z hz σ S hS
  let g := Equiv.ofBijective _ (classMap_bijective 𝔞 𝔟 θ L hθ hL)
  rw [← g.hasSum_iff]
  have key1 : ∀ c, defTerm φ 2 z σ (g c).1.out =
      (homFac z)⁻¹ ^ 2 * Complex.exp (-σ * logFac z) * eisClass 𝔞 𝔟 2 σ (modPt φ e θ z) c := by
    intro c
    set x : E := (c.out.1.1 : E) + (c.out.1.2 : E) * θ with hx
    have hg : (g c).1 = Quotient.mk _ x := rfl
    obtain ⟨u, hu⟩ : unitRel.r x (g c).1.out := Quotient.exact (by rw [hg, Quotient.out_eq])
    rw [hu, hx, algebraMap_unit, mul_add, ← mul_assoc, ← Subfield.coe_mul, ← Subfield.coe_mul,
      defTerm_eq φ e he θ hz, eisTerm_unit (by decide)]
    rfl
  have key : (fun q : modUnits L => defTerm φ 2 z σ q.1.out) ∘ g =
      fun c => (homFac z)⁻¹ ^ 2 * Complex.exp (-σ * logFac z) * eisClass 𝔞 𝔟 2 σ (modPt φ e θ z) c := by
    funext c
    simp only [Function.comp_apply]
    exact key1 c
  rw [key]
  exact hS.mul_left _

end GlobalTheory.WeightTwoCompare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HatKMConjImp
section
noncomputable section
namespace GlobalTheory.UCls.KGrp
open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat GlobalTheory.UCls

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem isUA_mul (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) {g h : Matrix (Fin n) (Fin n) (RA F E)}
    (hg : IsUA c G g) (hh : IsUA c G h) : IsUA c G (g * h) :=
  ⟨by rw [det_mul]; exact hg.1.mul hh.1, fun x y => by rw [← mulVec_mulVec, ← mulVec_mulVec, hg.2, hh.2]⟩

theorem isUA_inv (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) {g : Matrix (Fin n) (Fin n) (RA F E)}
    (hg : IsUA c G g) : IsUA c G g⁻¹ := by
  refine ⟨isUnit_nonsing_inv_det g hg.1, fun x y => ?_⟩
  rw [← hg.2, mulVec_mulVec, mulVec_mulVec, mul_nonsing_inv g hg.1, one_mulVec, one_mulVec]

theorem isKM_mul (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ)
    {k k' : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) (hk' : IsKM c G L M k') :
    IsKM c G L M (k * k') := by
  refine ⟨isUA_mul c G hk.1 hk'.1, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y', hy', e'⟩ := hk'.2.1 x hx
    have hkx : k' *ᵥ x ∈ hat F L := by
      have : k' *ᵥ x = x + M • y' := by rw [← e']; abel
      rw [this]; exact add_mem hx (nsmul_mem hy' M)
    obtain ⟨y, hy, e⟩ := hk.2.1 _ hkx
    refine ⟨y + y', add_mem hy hy', ?_⟩
    rw [← mulVec_mulVec, smul_add, ← e, ← e']; abel
  · obtain ⟨y, hy, e⟩ := hk.2.2 x hx
    obtain ⟨z, hz, e'⟩ := hk'.2.2 y hy
    exact ⟨z, hz, by rw [← mulVec_mulVec, e', e]⟩

theorem isKM_inv (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ)
    {k : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) : IsKM c G L M k⁻¹ := by
  have h1 : k * k⁻¹ = 1 := mul_nonsing_inv k hk.1.1
  have h2 : k⁻¹ * k = 1 := nonsing_inv_mul k hk.1.1
  refine ⟨isUA_inv c G hk.1, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy, rfl⟩ := hk.2.2 x hx
    obtain ⟨z, hz, e⟩ := hk.2.1 y hy
    refine ⟨-z, neg_mem hz, ?_⟩
    rw [mulVec_mulVec, h2, one_mulVec, smul_neg, ← e]; abel
  · obtain ⟨z, hz, e⟩ := hk.2.1 x hx
    refine ⟨k *ᵥ x, ?_, by rw [mulVec_mulVec, h2, one_mulVec]⟩
    have : k *ᵥ x = x + M • z := by rw [← e]; abel
    rw [this]; exact add_mem hx (nsmul_mem hz M)

theorem isKM_conj (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L Λ : Set (Fin n → E)) (M : ℕ)
    {g0 κ : Matrix (Fin n) (Fin n) (RA F E)} (hg0 : IsUA c G g0)
    (hL : (hat F L : Set (Fin n → RA F E)) = g0.mulVec '' (hat F Λ : Set (Fin n → RA F E)))
    (hκ : IsKM c G L M κ) : IsKM c G Λ M (g0⁻¹ * κ * g0) := by
  have h1 : g0 * g0⁻¹ = 1 := mul_nonsing_inv g0 hg0.1
  have h2 : g0⁻¹ * g0 = 1 := nonsing_inv_mul g0 hg0.1
  have mem : ∀ x, x ∈ hat F Λ → g0 *ᵥ x ∈ hat F L := fun x hx => by
    have : g0 *ᵥ x ∈ (hat F L : Set (Fin n → RA F E)) := by rw [hL]; exact ⟨x, hx, rfl⟩
    exact this
  have back : ∀ z, z ∈ hat F L → g0⁻¹ *ᵥ z ∈ hat F Λ := fun z hz => by
    have : z ∈ (hat F L : Set (Fin n → RA F E)) := hz
    rw [hL] at this
    obtain ⟨x, hx, rfl⟩ := this
    rw [mulVec_mulVec, h2, one_mulVec]; exact hx
  refine ⟨isUA_mul c G (isUA_mul c G (isUA_inv c G hg0) hκ.1) hg0, fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy, e⟩ := hκ.2.1 _ (mem x hx)
    refine ⟨g0⁻¹ *ᵥ y, back y hy, ?_⟩
    have hx' : g0⁻¹ *ᵥ (g0 *ᵥ x) = x := by rw [mulVec_mulVec, h2, one_mulVec]
    rw [← mulVec_smul, ← e, mulVec_sub, hx', ← mulVec_mulVec, ← mulVec_mulVec]
  · obtain ⟨y, hy, e⟩ := hκ.2.2 _ (mem x hx)
    refine ⟨g0⁻¹ *ᵥ y, back y hy, ?_⟩
    have hy' : g0 *ᵥ (g0⁻¹ *ᵥ y) = y := by rw [mulVec_mulVec, h1, one_mulVec]
    rw [← mulVec_mulVec, ← mulVec_mulVec, hy', e, mulVec_mulVec, h2, one_mulVec]

theorem hatKM_conj_imp {X Y : Set (Fin n → RA F E)} (M : ℕ) {A A' P : Matrix (Fin n) (Fin n) (RA F E)}
    (h2 : A' * A = 1) (hXY : X = A.mulVec '' Y)
    (hP : (∀ x ∈ X, ∃ y ∈ X, P *ᵥ x - x = M • y) ∧ ∀ x ∈ X, ∃ y ∈ X, P *ᵥ y = x) :
    (∀ x ∈ Y, ∃ y ∈ Y, (A' * P * A) *ᵥ x - x = M • y) ∧ ∀ x ∈ Y, ∃ y ∈ Y, (A' * P * A) *ᵥ y = x := by
  have back : ∀ y ∈ X, A' *ᵥ y ∈ Y := fun y hy => by
    rw [hXY] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [mulVec_mulVec, h2, one_mulVec]; exact hz
  have fwd : ∀ y ∈ Y, A *ᵥ y ∈ X := fun y hy => by rw [hXY]; exact ⟨y, hy, rfl⟩
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · obtain ⟨y, hy, e⟩ := hP.1 _ (fwd x hx)
    refine ⟨A' *ᵥ y, back y hy, ?_⟩
    have hx' : A' *ᵥ (A *ᵥ x) = x := by rw [mulVec_mulVec, h2, one_mulVec]
    rw [← mulVec_smul, ← e, mulVec_sub, hx', ← mulVec_mulVec, ← mulVec_mulVec]
  · obtain ⟨y, hy, e⟩ := hP.2 _ (fwd x hx)
    have hy2 := hy
    rw [hXY] at hy2
    obtain ⟨z, hz, rfl⟩ := hy2
    refine ⟨z, hz, ?_⟩
    rw [← mulVec_mulVec, ← mulVec_mulVec, e, mulVec_mulVec, h2, one_mulVec]

theorem hatKM_conj {X Y : Set (Fin n → RA F E)} (M : ℕ) {A A' P : Matrix (Fin n) (Fin n) (RA F E)}
    (h1 : A * A' = 1) (h2 : A' * A = 1) (hXY : X = A.mulVec '' Y) :
    ((∀ x ∈ X, ∃ y ∈ X, P *ᵥ x - x = M • y) ∧ ∀ x ∈ X, ∃ y ∈ X, P *ᵥ y = x) ↔
    ((∀ x ∈ Y, ∃ y ∈ Y, (A' * P * A) *ᵥ x - x = M • y) ∧ ∀ x ∈ Y, ∃ y ∈ Y, (A' * P * A) *ᵥ y = x) := by
  refine ⟨hatKM_conj_imp M h2 hXY, fun h => ?_⟩
  have hYX : Y = A'.mulVec '' X := by
    ext y
    constructor
    · intro hy
      refine ⟨A *ᵥ y, by rw [hXY]; exact ⟨y, hy, rfl⟩, by rw [mulVec_mulVec, h2, one_mulVec]⟩
    · rintro ⟨x, hx, rfl⟩
      rw [hXY] at hx
      obtain ⟨z, hz, rfl⟩ := hx
      rw [mulVec_mulVec, h2, one_mulVec]; exact hz
  have := hatKM_conj_imp (P := A' * P * A) M h1 hYX h
  have e : A * (A' * P * A) * A' = P := by
    simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  rwa [e] at this

theorem isKM_image (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ)
    {k : Matrix (Fin n) (Fin n) (RA F E)} (hk : IsKM c G L M k) :
    k.mulVec '' (hat F L : Set (Fin n → RA F E)) = (hat F L : Set (Fin n → RA F E)) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz, e⟩ := hk.2.1 y hy
    have : k *ᵥ y = y + M • z := by rw [← e]; abel
    show k *ᵥ y ∈ hat F L
    rw [this]; exact add_mem hy (nsmul_mem hz M)
  · intro hx
    obtain ⟨y, hy, e⟩ := hk.2.2 x hx
    exact ⟨y, hy, e⟩

end GlobalTheory.UCls.KGrp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureProjectiveOverStandardOpenRingStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralClosure_projective_over_standardOpenRing : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x → ∀ i, Module.Projective (rA k x {i}) (integralClosure (rA k x {i}) K) := by
  first | (exact @GlobalTheory.integralClosure_projective_rA) | (exact GlobalTheory.integralClosure_projective_rA) | (intros; apply GlobalTheory.integralClosure_projective_rA  <;> assumption)
end

