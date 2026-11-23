module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionUnitaryGroupHermitian
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0034
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdicIntegersCompact.IsCompactAdicCompletionIntegers

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsQuadOfNormal
section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil GlobalTheory.Mem.Lift
open scoped RealInnerProductSpace ContDiff Real ComplexOrder Topology

noncomputable section

namespace GlobalTheory.Mem.Lift.Normal

variable {ι : Type}

theorem real_lin_smul (l : (ι → ℂ) →ₗ[ℝ] ℂ) (c : ℂ) (z : ι → ℂ) :
    l (c • z) = c.re * l z + c.im * l (I • z) := by
  have hc : c • z = c.re • z + c.im • (I • z) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im c]
    ring
  rw [hc, map_add (f := _), map_smul, map_smul, Complex.real_smul, Complex.real_smul]

theorem real_lin_I_I (l : (ι → ℂ) →ₗ[ℝ] ℂ) (z : ι → ℂ) : l (I • I • z) = - l z := by
  rw [smul_smul, I_mul_I, neg_one_smul, map_neg]

def linPart (l : (ι → ℂ) →ₗ[ℝ] ℂ) : (ι → ℂ) →ₗ[ℂ] ℂ where
  toFun z := l z - I * l (I • z)
  map_add' x y := by simp only [smul_add, map_add (f := _)]; ring
  map_smul' c z := by
    rw [smul_comm I c z, real_lin_smul l c z, real_lin_smul l c (I • z), real_lin_I_I, RingHom.id_apply, smul_eq_mul]
    conv_rhs => rw [← Complex.re_add_im c]
    linear_combination (c.im * l (I • z)) * I_mul_I

def antiPart (l : (ι → ℂ) →ₗ[ℝ] ℂ) : (ι → ℂ) →ₗ⋆[ℂ] ℂ where
  toFun z := l z + I * l (I • z)
  map_add' x y := by simp only [smul_add, map_add (f := _)]; ring
  map_smul' c z := by
    rw [smul_comm I c z, real_lin_smul l c z, real_lin_smul l c (I • z), real_lin_I_I, smul_eq_mul]
    have : (starRingEnd ℂ) c = c.re - c.im * I := by
      apply Complex.ext <;> simp
    rw [this]
    linear_combination (c.im * l (I • z)) * I_mul_I

theorem im_add_I_re (h : ℂ) : ((h.im : ℂ) + I * ((I * h).im : ℂ)) = I * (starRingEnd ℂ) h := by
  apply Complex.ext <;> simp

theorem im_sub_I_re (h : ℂ) : ((h.im : ℂ) - I * ((I * h).im : ℂ)) = - I * h := by
  apply Complex.ext <;> simp

variable [Fintype ι] [DecidableEq ι]

def nC (X : Matrix ι ι ℂ) (i : ι × ι × Bool × Bool) : ℂ :=
  X i.1 i.2.1 * (-(1 / (4 * π))) * (if i.2.2.1 then -I else 1) * (if i.2.2.2 then I else 1)

def nP (i : ι × ι × Bool × Bool) : ι → ℂ :=
  if i.2.2.1 then I • Pi.single i.1 1 else Pi.single i.1 1

def nQ (H : Matrix ι ι ℂ) (i : ι × ι × Bool × Bool) : ι → ℂ :=
  if i.2.2.2 then I • H⁻¹ *ᵥ Pi.single i.2.1 1 else H⁻¹ *ᵥ Pi.single i.2.1 1

theorem sum_lin (X : Matrix ι ι ℂ) (A : (ι → ℂ) →ₗ[ℂ] ℂ) (v : ι → ℂ) :
    ∑ k, ∑ j, X k j * (v j * A (Pi.single k 1)) = A (X *ᵥ v) := by
  have hx : X *ᵥ v = ∑ k, (∑ j, X k j * v j) • (Pi.single k (1 : ℂ) : ι → ℂ) := by
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hx, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem sum_anti {H X : Matrix ι ι ℂ} (hH : Hᴴ = H) (hd : H.det ≠ 0) (hX : Xᴴ * H + H * X = 0)
    (A : (ι → ℂ) →ₗ⋆[ℂ] ℂ) (v : ι → ℂ) :
    ∑ k, ∑ j, X k j * ((star v ⬝ᵥ H *ᵥ Pi.single k 1) * A (H⁻¹ *ᵥ Pi.single j 1)) = - A (X *ᵥ v) := by
  have hinv' : H⁻¹ * H = 1 := Matrix.nonsing_inv_mul H (isUnit_iff_ne_zero.mpr hd)
  set w := X *ᵥ v with hw

  have hexp : w = ∑ j, (H *ᵥ w) j • (H⁻¹ *ᵥ Pi.single j 1) := by
    have h1 : H *ᵥ w = ∑ j, (H *ᵥ w) j • (Pi.single j (1 : ℂ) : ι → ℂ) := by
      ext i
      simp [Finset.sum_apply, Pi.single_apply]
    calc w = H⁻¹ *ᵥ (H *ᵥ w) := by rw [Matrix.mulVec_mulVec, hinv', Matrix.one_mulVec]
      _ = H⁻¹ *ᵥ ∑ j, (H *ᵥ w) j • (Pi.single j (1 : ℂ) : ι → ℂ) := by rw [← h1]
      _ = _ := by
        rw [Matrix.mulVec_sum]
        simp only [Matrix.mulVec_smul]
  have hA : A w = ∑ j, (starRingEnd ℂ) ((H *ᵥ w) j) * A (H⁻¹ *ᵥ Pi.single j 1) := by
    conv_lhs => rw [hexp]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LinearMap.map_smulₛₗ, smul_eq_mul]

  have hcoef : ∀ j, ∑ k, X k j * (star v ⬝ᵥ H *ᵥ Pi.single k 1) = -(starRingEnd ℂ) ((H *ᵥ w) j) := by
    intro j
    have hs : ∀ k, star v ⬝ᵥ H *ᵥ Pi.single k 1 = (star v ᵥ* H) k := by
      intro k
      rw [Matrix.dotProduct_mulVec]
      simp [dotProduct, Pi.single_apply]
    have hXH : (H * X)ᴴ = -(H * X) := by
      rw [Matrix.conjTranspose_mul, hH]
      exact eq_neg_of_add_eq_zero_left hX
    have hstar : (starRingEnd ℂ) ((H *ᵥ w) j) = (star v ᵥ* (H * X)ᴴ) j := by
      rw [hw, Matrix.mulVec_mulVec, ← Matrix.star_mulVec]
      rfl
    simp_rw [hs]
    rw [hstar, hXH, Matrix.vecMul_neg, Pi.neg_apply, neg_neg, ← Matrix.vecMul_vecMul]
    simp [vecMul, dotProduct, mul_comm]
  rw [hA, Finset.sum_comm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  calc ∑ k, X k j * ((star v ⬝ᵥ H *ᵥ Pi.single k 1) * A (H⁻¹ *ᵥ Pi.single j 1))
      = (∑ k, X k j * (star v ⬝ᵥ H *ᵥ Pi.single k 1)) * A (H⁻¹ *ᵥ Pi.single j 1) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = _ := by
        rw [hcoef j]
        ring

theorem isQuadOf_normal {H X : Matrix ι ι ℂ} (hH : Hᴴ = H) (hd : H.det ≠ 0) (hX : Xᴴ * H + H * X = 0) :
    IsQuadOf (fun x y => (star y ⬝ᵥ H *ᵥ x).im) (fun v => X *ᵥ v) (nC X) nP (nQ H) := by
  intro l v
  beta_reduce
  have hinv : H * H⁻¹ = 1 := Matrix.mul_nonsing_inv H (isUnit_iff_ne_zero.mpr hd)

  have hkj : ∀ k j, (∑ b1 : Bool, ∑ b2 : Bool, nC X (k, j, b1, b2) *
      (((star v ⬝ᵥ H *ᵥ nQ H (k, j, b1, b2)).im : ℂ) * l (nP (k, j, b1, b2)) +
        ((star v ⬝ᵥ H *ᵥ nP (k, j, b1, b2)).im : ℂ) * l (nQ H (k, j, b1, b2)))) =
      X k j * (-(1 / (4 * π))) * (I * (v j * linPart l (Pi.single k 1)) +
        (-I) * ((star v ⬝ᵥ H *ᵥ Pi.single k 1) * antiPart l (H⁻¹ *ᵥ Pi.single j 1))) := by
    intro k j
    have ha : ((star v ⬝ᵥ H *ᵥ (H⁻¹ *ᵥ Pi.single j 1)).im : ℂ) +
        I * ((star v ⬝ᵥ H *ᵥ (I • H⁻¹ *ᵥ Pi.single j 1)).im : ℂ) = I * v j := by
      rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, im_add_I_re, Matrix.mulVec_mulVec, hinv,
        Matrix.one_mulVec, dotProduct_single, mul_one, Pi.star_apply, starRingEnd_apply, star_star]
    have hp : ((star v ⬝ᵥ H *ᵥ Pi.single k 1).im : ℂ) -
        I * ((star v ⬝ᵥ H *ᵥ (I • Pi.single k 1)).im : ℂ) = -I * (star v ⬝ᵥ H *ᵥ Pi.single k 1) := by
      rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, im_sub_I_re]
    simp only [Fintype.sum_bool, nC, nP, nQ, Bool.false_eq_true, ↓reduceIte, linPart, antiPart, LinearMap.coe_mk, AddHom.coe_mk]
    linear_combination (X k j * (-(1 / (4 * π))) * (l (Pi.single k 1) - I * l (I • Pi.single k 1))) * ha +
      (X k j * (-(1 / (4 * π))) * (l (H⁻¹ *ᵥ Pi.single j 1) + I * l (I • H⁻¹ *ᵥ Pi.single j 1))) * hp
  have hsum : ∀ F : ι × ι × Bool × Bool → ℂ, ∑ i, F i = ∑ k, ∑ j, ∑ b1, ∑ b2, F (k, j, b1, b2) :=
    fun F => by simp only [Fintype.sum_prod_type]
  rw [hsum, Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => hkj k j]
  have hsplit : (∑ k, ∑ j, X k j * (-(1 / (4 * π))) * (I * (v j * linPart l (Pi.single k 1)) +
      (-I) * ((star v ⬝ᵥ H *ᵥ Pi.single k 1) * antiPart l (H⁻¹ *ᵥ Pi.single j 1)))) =
      (-(1 / (4 * π)) * I : ℂ) * ((∑ k, ∑ j, X k j * (v j * linPart l (Pi.single k 1))) -
        ∑ k, ∑ j, X k j * ((star v ⬝ᵥ H *ᵥ Pi.single k 1) * antiPart l (H⁻¹ *ᵥ Pi.single j 1))) := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hLA : linPart l (X *ᵥ v) + antiPart l (X *ᵥ v) = 2 * l (X *ᵥ v) := by
    simp only [linPart, antiPart, LinearMap.coe_mk, AddHom.coe_mk]
    ring
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hfin : ∀ z : ℂ, 2 * (π : ℂ) * I * (-(1 / (4 * (π : ℂ))) * I * (2 * z)) = z := by
    intro z
    rw [show 2 * (π : ℂ) * I * (-(1 / (4 * (π : ℂ))) * I * (2 * z)) = -(I * I) * ((π : ℂ) * (π : ℂ)⁻¹) * z by ring,
      I_mul_I, mul_inv_cancel₀ hπ]
    ring
  rw [hsplit, sum_lin, sum_anti hH hd hX, sub_neg_eq_add, hLA]
  exact hfin _

private theorem sm_add' {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    {ρ : (ι → ℂ) → B →L[ℂ] B} {f g : B} (hf : Sm ρ f) (hg : Sm ρ g) : Sm ρ (f + g) := by
  unfold Sm at *
  simp only [map_add (f := _)]
  exact hf.add hg

private theorem sm_smul' {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    {ρ : (ι → ℂ) → B →L[ℂ] B} {f : B} (a : ℂ) (hf : Sm ρ f) : Sm ρ (a • f) := by
  unfold Sm at *
  simp only [map_smul]
  exact hf.const_smul a

theorem quad_normal (H X : Matrix ι ι ℂ) {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B]
    (ρ : (ι → ℂ) → B →L[ℂ] B) (f : B) (hs : ∀ v, Sm ρ (dH ρ v f)) :
    quad ρ (nC X) nP (nQ H) f = nOp ρ H X f := by
  have hy : ∀ j : ι, Sm ρ (dH ρ (H⁻¹ *ᵥ Pi.single j 1) f) := fun j => hs _
  have hIy : ∀ j : ι, Sm ρ (dH ρ (I • H⁻¹ *ᵥ Pi.single j 1) f) := fun j => hs _

  have hexp : ∀ (u : ι → ℂ) (j : ι), dH ρ u (dOp ρ H j f) = (-(1 / (4 * π)) : ℂ) •
      (dH ρ u (dH ρ (H⁻¹ *ᵥ Pi.single j 1) f) + I • dH ρ u (dH ρ (I • H⁻¹ *ᵥ Pi.single j 1) f)) := by
    intro u j
    unfold dOp
    rw [dH_smul u _ (sm_add' (hy j) (sm_smul' I (hIy j))),
      dH_add u (hy j) (sm_smul' I (hIy j)), dH_smul u I (hIy j)]
  unfold quad nOp xOp
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [nC, nP, nQ, Bool.false_eq_true, ↓reduceIte, hexp]
  module

def omH (H : Matrix ι ι ℂ) : (ι → ℂ) →L[ℝ] (ι → ℂ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : ((ι → ℂ) →ₗ[ℝ] ℝ) ≃ₗ[ℝ] _).toLinearMap ∘ₗ
      LinearMap.mk₂ ℝ (fun x y : ι → ℂ => (star y ⬝ᵥ H *ᵥ x).im)
        (fun x x' y => by simp [mulVec_add])
        (fun r x y => by simp [mulVec_smul])
        (fun x y y' => by simp)
        (fun r x y => by simp))

theorem normal_quad : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H X : Matrix ι ι ℂ), Hᴴ = H → H.det ≠ 0 → Xᴴ * H + H * X = 0 → ∃ (κ : Type) (_ : Fintype κ) (c : κ → ℂ) (p q : κ → ι → ℂ), IsQuadOf (fun x y => (star y ⬝ᵥ H *ᵥ x).im) (fun v => X *ᵥ v) c p q ∧ ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] (ρ : (ι → ℂ) → B →L[ℂ] B), IsHeis (fun x y => (star y ⬝ᵥ H *ᵥ x).im) ρ → ∀ f, Sm ρ f → quad ρ c p q f = nOp ρ H X f := by
  intro ι _ _ H X hH hd hX
  refine ⟨ι × ι × Bool × Bool, inferInstance, nC X, nP, nQ H, isQuadOf_normal hH hd hX, ?_⟩
  intro B _ _ ρ hρ f hf
  exact quad_normal H X ρ f fun v => DCalc.sm_dH (om := omH H) hρ hf v

end GlobalTheory.Mem.Lift.Normal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormEmbeddingIntegerLeOne
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.LadicPlace

theorem norm_embedding_integer_le_one {E : Type} [Field E] [NumberField E] {l : ℕ} [Fact l.Prime]
    (τ : E →+* PadicAlgCl l) (a : 𝓞 E) : ‖τ (a : E)‖ ≤ 1 := by
  have h : IsIntegral ℤ (τ (a : E)) := by
    have := (RingOfIntegers.isIntegral_coe a).map τ.toIntAlgHom
    simpa using this
  obtain ⟨p, hp, hp0⟩ := h
  by_contra hlt
  push_neg at hlt
  set y := τ (a : E)
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, map_one,
    one_mul] at hp0
  have h1 : y ^ p.natDegree =
      - ∑ i ∈ Finset.range p.natDegree, algebraMap ℤ (PadicAlgCl l) (p.coeff i) * y ^ i := by
    linear_combination hp0
  have hpos : 0 < ‖y‖ ^ p.natDegree := pow_pos (by linarith) _
  have h2 : ‖∑ i ∈ Finset.range p.natDegree, algebraMap ℤ (PadicAlgCl l) (p.coeff i) * y ^ i‖
      < ‖y‖ ^ p.natDegree := by
    refine Finset.sum_induction _ (fun z => ‖z‖ < ‖y‖ ^ p.natDegree) ?_ (by simpa using hpos) ?_
    · intro u v hu hv
      exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max u v) (max_lt hu hv)
    · intro i hi
      rw [norm_mul, norm_pow]
      have h3 : ‖algebraMap ℤ (PadicAlgCl l) (p.coeff i)‖ ≤ 1 := by
        simpa using IsUltrametricDist.norm_intCast_le_one (PadicAlgCl l) (p.coeff i)
      calc _ ≤ 1 * ‖y‖ ^ i := by gcongr
        _ = ‖y‖ ^ i := one_mul _
        _ < _ := pow_lt_pow_right₀ hlt (Finset.mem_range.mp hi)
  rw [← norm_neg, ← h1, norm_pow] at h2
  exact lt_irrefl _ h2

theorem exists_place_of_embedding :
    ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (τ : E →+* Qbar l),
      ∃ v : HeightOneSpectrum (𝓞 E), ∀ x : E, v.valuation E x < 1 ↔ ‖τ x‖ < 1 := by
  intro E _ _ l hl τ
  have hle : ∀ a : 𝓞 E, ‖τ (a : E)‖ ≤ 1 := norm_embedding_integer_le_one τ
  let P : Ideal (𝓞 E) :=
    { carrier := {a | ‖τ (a : E)‖ < 1}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [RingOfIntegers.coe_eq_algebraMap, map_add (f := _), map_add (f := _)]
        exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [RingOfIntegers.coe_eq_algebraMap, smul_eq_mul, map_mul, map_mul, norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (hle c) (norm_nonneg _) ha }
  have hP : ∀ a : 𝓞 E, a ∈ P ↔ ‖τ (algebraMap (𝓞 E) E a)‖ < 1 := fun a => Iff.rfl
  have hone : ∀ a : 𝓞 E, a ∉ P → ‖τ (algebraMap (𝓞 E) E a)‖ = 1 := fun a ha =>
    le_antisymm (hle a) (not_lt.mp (fun h => ha ((hP a).mpr h)))
  have hprime : P.IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ne, Ideal.eq_top_iff_one, hP]; simp
    · intro a b hab
      by_contra hn
      rw [not_or] at hn
      rw [hP, map_mul, map_mul, norm_mul, hone a hn.1, hone b hn.2] at hab
      simp at hab
  have hlP : (l : 𝓞 E) ∈ P := by
    rw [hP, map_natCast, map_natCast]
    have h1 : ((l : ℕ) : PadicAlgCl l) = ((l : ℚ_[l]) : PadicAlgCl l) := by
      simp
    rw [h1, PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  have hne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hlP
    exact hl.out.ne_zero (by exact_mod_cast hlP)
  let v : HeightOneSpectrum (𝓞 E) := ⟨P, hprime, hne⟩
  have key : ∀ x : E, v.valuation E x ≤ 1 → ∃ a s : 𝓞 E, s ∉ P ∧
      x * algebraMap (𝓞 E) E s = algebraMap (𝓞 E) E a := by
    intro x hx
    obtain ⟨a, s, h⟩ := v.exists_primeCompl_mul_eq_of_integer x hx
    exact ⟨a, s, s.2, h⟩
  refine ⟨v, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · obtain ⟨a, s, hs, h⟩ := key x hx.le
    have ha : a ∈ P := by
      have : v.valuation E (algebraMap (𝓞 E) E a) < 1 := by
        rw [← h, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_right' (v.valuation_le_one s)) hx
      exact (v.valuation_lt_one_iff_mem a).mp this
    rw [hP, ← h, map_mul, norm_mul, hone s hs, mul_one] at ha
    exact ha
  · by_contra hn
    have hn' : 1 ≤ v.valuation E x := not_lt.mp hn
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hn'
    have hinv : v.valuation E x⁻¹ ≤ 1 := by
      rw [map_inv₀]; exact inv_le_one_of_one_le₀ hn'
    obtain ⟨a, s, hs, h⟩ := key _ hinv
    have h2 : algebraMap (𝓞 E) E s = x * algebraMap (𝓞 E) E a := by
      rw [← h, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
    have h3 := hone s hs
    rw [h2, map_mul, norm_mul] at h3
    have h4 := mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hx (hle a)
    exact absurd h3 h4.ne

end GlobalTheory.LadicPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalCongInvMul
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

namespace GlobalTheory

theorem principalCong_inv_mul :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n N : ℕ) (x y : GAf L n),
    NG.Cong L n N x → NG.Cong L n N y → NG.Cong L n N (x⁻¹ * y) := by
  intro L _ _ _ n N x y hx hy
  have hxi : x⁻¹ ∈ Umax L n := (Umax L n).inv_mem hx.1
  refine ⟨(Umax L n).mul_mem hxi hy.1, fun i j => ?_⟩
  choose A hA eA using hx.2
  choose B hB eB using hy.2
  have hint : ∀ i j, ((x⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := hxi
  have key : ((x⁻¹ * y).1 : Matrix (Fin n) (Fin n) (AL L)) - 1 =
      ((x⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) *
        (((y.1 : Matrix (Fin n) (Fin n) (AL L)) - 1) - ((x.1 : Matrix (Fin n) (Fin n) (AL L)) - 1)) := by
    have h1 : ((x⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) * (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
    rw [sub_sub_sub_cancel_right, mul_sub, h1, Subgroup.coe_mul, Units.val_mul]
  refine ⟨∑ k, ((x⁻¹).1 : Matrix (Fin n) (Fin n) (AL L)) i k * (B k j - A k j),
    Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hint i k) (Subring.sub_mem _ (hB k j) (hA k j)), ?_⟩
  rw [← Matrix.sub_apply, key, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.sub_apply, eA, eB]
  ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassGroupIdelicFiniteIndex
section
open IsDedekindDomain NumberField

namespace GlobalTheory.LevelChars

theorem exists_finset_close (L : Type) [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) (N : ℕ) :
    ∃ F : Finset (v.adicCompletion L), ∀ x : v.adicCompletion L, Valued.v x ≤ 1 →
      ∃ f ∈ F, Valued.v (x - f) ≤ WithZero.exp (-(N : ℤ)) := by
  classical
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer L v
  set s : v.adicCompletion L := ((π ^ N : L) : v.adicCompletion L) with hsdef
  have hs : Valued.v s = WithZero.exp (-(N : ℤ)) := by
    rw [hsdef, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_pow, hπ, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hball : IsOpen {y : v.adicCompletion L | Valued.v y < Valued.v s} := by
    have h := Valued.isOpen_ball (v.adicCompletion L) (Valued.v.restrict s)
    simpa [Valuation.restrict_lt_iff] using h
  obtain ⟨t, -, ht⟩ := (PI.IntAdCpctOpenWork.isCompact_adicCompletionIntegers (F := L) v).elim_nhds_subcover
    (fun x => {y | Valued.v (y - x) < Valued.v s})
    (fun x _ => (hball.preimage (continuous_id.sub continuous_const)).mem_nhds (by
      show Valued.v (x - x) < Valued.v s
      rw [sub_self, map_zero, hs]
      exact zero_lt_iff.2 WithZero.exp_ne_zero))
  refine ⟨t, fun x hx => ?_⟩
  have hxO : x ∈ (v.adicCompletionIntegers L : Set (v.adicCompletion L)) :=
    by rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]; exact hx
  obtain ⟨f, hf, hxf⟩ := Set.mem_iUnion₂.1 (ht hxO)
  exact ⟨f, hf, le_of_lt (hs ▸ hxf)⟩

end GlobalTheory.LevelChars

namespace GlobalTheory.LevelChars

theorem relIndex_levSub_ne_zero (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ)
    (hS : S.Finite) : (levSub L S N).relIndex (levSub L ∅ 0) ≠ 0 := by
  classical
  haveI : Finite S := hS.to_subtype
  choose F hF using fun v : S => exists_finset_close L v.1 N
  have hint : ∀ a : levSub L ∅ 0, ∀ v, Valued.v (compAt L v (a : (AdeleRing (𝓞 L) L)ˣ)) ≤ 1 :=
    fun a v => le_of_eq (a.2 v).1
  choose g hg hg' using fun (a : levSub L ∅ 0) (v : S) => hF v (compAt L v.1 a) (hint a v.1)
  let φ : levSub L ∅ 0 ⧸ (levSub L S N).subgroupOf (levSub L ∅ 0) → ((v : S) → (F v : Set (v.1.adicCompletion L))) :=
    fun q v => ⟨g q.out v, hg q.out v⟩
  have hφ : Function.Injective φ := by
    intro q q' hqq
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq, Subgroup.mem_subgroupOf]
    intro w
    refine ⟨((q.out⁻¹ * q'.out).2 w).1, fun hw => ?_⟩
    have e1 : g q.out ⟨w, hw⟩ = g q'.out ⟨w, hw⟩ := congrArg Subtype.val (congrFun hqq ⟨w, hw⟩)
    have h1 := hg' q.out ⟨w, hw⟩
    have h2 := hg' q'.out ⟨w, hw⟩
    rw [e1] at h1
    set a : (AdeleRing (𝓞 L) L)ˣ := (q.out : (AdeleRing (𝓞 L) L)ˣ)
    set b : (AdeleRing (𝓞 L) L)ˣ := (q'.out : (AdeleRing (𝓞 L) L)ˣ)
    have hinv : Valued.v (compAt L w a⁻¹) = 1 := ((q.out⁻¹).2 w).1
    have hc : compAt L w a⁻¹ * compAt L w a = 1 := by rw [← compAt_mul, inv_mul_cancel, compAt_one]
    have e2 : compAt L w ((q.out⁻¹ * q'.out : levSub L ∅ 0) : (AdeleRing (𝓞 L) L)ˣ) - 1 =
        compAt L w a⁻¹ * ((compAt L w b - g q'.out ⟨w, hw⟩) - (compAt L w a - g q'.out ⟨w, hw⟩)) := by
      have : ((q.out⁻¹ * q'.out : levSub L ∅ 0) : (AdeleRing (𝓞 L) L)ˣ) = a⁻¹ * b := rfl
      rw [this, compAt_mul]
      linear_combination hc
    rw [e2, map_mul, hinv, one_mul]
    exact (Valuation.map_sub _ _ _).trans (max_le h2 h1)
  haveI : Finite (levSub L ∅ 0 ⧸ (levSub L S N).subgroupOf (levSub L ∅ 0)) := Finite.of_injective φ hφ
  exact Subgroup.index_ne_zero_of_finite

end GlobalTheory.LevelChars

namespace GlobalTheory.LevelChars

theorem levSub_le_levSub_empty (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ) :
    levSub L S N ≤ levSub L ∅ 0 := fun a ha v => ⟨(ha v).1, fun h => absurd h (Set.notMem_empty v)⟩

theorem finiteIndex_range_sup_levSub_empty (L : Type) [Field L] [NumberField L] :
    ((Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range ⊔ levSub L ∅ 0).FiniteIndex := by
  classical
  haveI : Finite (ReciprocityTheory.Neutral.Bridge.HCFR.classOf L).range := inferInstance
  haveI := Subgroup.finiteIndex_ker (ReciprocityTheory.Neutral.Bridge.HCFR.classOf L)
  refine Subgroup.finiteIndex_of_le (H := (ReciprocityTheory.Neutral.Bridge.HCFR.classOf L).ker) ?_
  intro a ha
  obtain ⟨k, u, hu, rfl⟩ := (ReciprocityTheory.Neutral.Bridge.HCFR.classOf_eq_one_iff L a).1 ha
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨k, rfl⟩) (Subgroup.mem_sup_right ?_)
  exact fun v => ⟨(ReciprocityTheory.Neutral.Bridge.HCFR.rayUnits_top_iff L u).1 hu v, fun h => absurd h (Set.notMem_empty v)⟩

theorem finiteIndex_range_sup_levSub (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ)
    (hS : S.Finite) :
    ((Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range ⊔ levSub L S N).FiniteIndex := by
  set R := (Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range
  have hle := levSub_le_levSub_empty L S N
  haveI := finiteIndex_range_sup_levSub_empty L
  have hT : R ⊔ levSub L S N ≤ R ⊔ levSub L ∅ 0 := sup_le_sup_left hle _
  have h1 : (R ⊔ levSub L S N).relIndex (levSub L ∅ 0) ≠ 0 := by
    intro h0
    have hd : (R ⊔ levSub L S N).relIndex (levSub L ∅ 0) ∣ (levSub L S N).relIndex (levSub L ∅ 0) :=
      Subgroup.relIndex_dvd_of_le_left (levSub L ∅ 0) le_sup_right
    rw [h0] at hd
    exact relIndex_levSub_ne_zero L S N hS (Nat.eq_zero_of_zero_dvd hd)
  have h2 : R ⊔ levSub L S N ⊔ levSub L ∅ 0 = R ⊔ levSub L ∅ 0 := by
    rw [sup_assoc, sup_eq_right.2 hle]
  have h3 : (R ⊔ levSub L S N).relIndex (R ⊔ levSub L ∅ 0) ≠ 0 := by
    rw [← h2, Subgroup.relIndex_sup_left]; exact h1
  rw [Subgroup.finiteIndex_iff, ← Subgroup.relIndex_mul_index hT]
  exact mul_ne_zero h3 (Subgroup.FiniteIndex.index_ne_zero)

theorem rayClass_finite : ∀ (L : Type) [Field L] [NumberField L] (S : Set (HeightOneSpectrum (𝓞 L))) (N : ℕ), S.Finite →
    ((Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom).range ⊔ GlobalTheory.LevelChars.levSub L S N).FiniteIndex :=
  fun L _ _ S N hS => finiteIndex_range_sup_levSub L S N hS

end GlobalTheory.LevelChars
end

