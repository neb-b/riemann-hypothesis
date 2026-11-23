module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0074

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSLTwoPermutedModularFamilyAlgebraClosure
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam

variable {ι : Type} {act : ι → SL(2, ℤ) → ι}

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm in
variable {ι : Type} {act : ι → SL(2, ℤ) → ι} in
private lemma isFam_apply_smul_mul_denom_zpow {w : ℤ} {f : ι → ℍ → ℂ}
    (hf : _root_.GlobalTheory.QFam.IsFam act w f) (i : ι) (γ : SL(2, ℤ)) (τ : ℍ) :
    f i (γ • τ) * UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) ↑τ ^ (-w) = f (act i γ) τ := by
  rw [← SL_slash_apply, hf i γ]


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm in
variable {ι : Type} {act : ι → SL(2, ℤ) → ι} in
theorem _root_.GlobalTheory.QFam.IsFam.const_mul_fun {w : ℤ} {f : ι → ℍ → ℂ} (c : ℂ)
    (hf : _root_.GlobalTheory.QFam.IsFam act w f) :
    _root_.GlobalTheory.QFam.IsFam act w fun i τ => c * f i τ := by
  intro i γ
  funext τ
  simp only [SL_slash_apply]
  rw [← isFam_apply_smul_mul_denom_zpow hf i γ τ]
  ring


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm in
variable {ι : Type} {act : ι → SL(2, ℤ) → ι} in
theorem _root_.GlobalTheory.QFam.IsFam.mul_fun {w w' : ℤ} {f g : ι → ℍ → ℂ}
    (hf : _root_.GlobalTheory.QFam.IsFam act w f) (hg : _root_.GlobalTheory.QFam.IsFam act w' g) :
    _root_.GlobalTheory.QFam.IsFam act (w + w') fun i τ => f i τ * g i τ := by
  intro i γ
  funext τ
  simp only [SL_slash_apply]
  rw [← isFam_apply_smul_mul_denom_zpow hf i γ τ, ← isFam_apply_smul_mul_denom_zpow hg i γ τ, neg_add,
    zpow_add₀ (UpperHalfPlane.denom_ne_zero _ _)]
  ring


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm in
variable {ι : Type} {act : ι → SL(2, ℤ) → ι} in
theorem _root_.GlobalTheory.QFam.IsFam.pow_fun {w : ℤ} {f : ι → ℍ → ℂ} (k : ℕ)
    (hf : _root_.GlobalTheory.QFam.IsFam act w f) :
    _root_.GlobalTheory.QFam.IsFam act (k * w) fun i τ => f i τ ^ k := by
  intro i γ
  funext τ
  simp only [SL_slash_apply]
  rw [← isFam_apply_smul_mul_denom_zpow hf i γ τ, mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul,
    show -((k : ℤ) * w) = -w * k by ring]


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm in
variable {ι : Type} {act : ι → SL(2, ℤ) → ι} in
theorem _root_.GlobalTheory.QFam.IsFam.sum_fun {κ : Type} (t : Finset κ) {w : ℤ}
    {f : κ → ι → ℍ → ℂ} (hf : ∀ k ∈ t, _root_.GlobalTheory.QFam.IsFam act w (f k)) :
    _root_.GlobalTheory.QFam.IsFam act w fun i τ => ∑ k ∈ t, f k i τ := by
  intro i γ
  funext τ
  simp only [SL_slash_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k hk => isFam_apply_smul_mul_denom_zpow (hf k hk) i γ τ


open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
open ModularForm in
variable {ι : Type} {act : ι → SL(2, ℤ) → ι} in
theorem _root_.GlobalTheory.QFam.isFam_algebra : ∀ (ι : Type) (act : ι → SL(2, ℤ) → ι),
    (∀ c : ℂ, _root_.GlobalTheory.QFam.IsFam act 0 fun _ _ => c) ∧
    (∀ w f g, _root_.GlobalTheory.QFam.IsFam act w f → _root_.GlobalTheory.QFam.IsFam act w g →
      (_root_.GlobalTheory.QFam.IsFam act w fun i τ => f i τ + g i τ) ∧
        _root_.GlobalTheory.QFam.IsFam act w fun i τ => f i τ - g i τ) ∧
    (∀ w (c : ℂ) f, _root_.GlobalTheory.QFam.IsFam act w f →
      _root_.GlobalTheory.QFam.IsFam act w fun i τ => c * f i τ) ∧
    (∀ w w' f g, _root_.GlobalTheory.QFam.IsFam act w f → _root_.GlobalTheory.QFam.IsFam act w' g →
      _root_.GlobalTheory.QFam.IsFam act (w + w') fun i τ => f i τ * g i τ) ∧
    (∀ w f (k : ℕ), _root_.GlobalTheory.QFam.IsFam act w f →
      _root_.GlobalTheory.QFam.IsFam act (k * w) fun i τ => f i τ ^ k) ∧
    (∀ (κ : Type) (t : Finset κ) w (f : κ → ι → ℍ → ℂ),
      (∀ k ∈ t, _root_.GlobalTheory.QFam.IsFam act w (f k)) →
        _root_.GlobalTheory.QFam.IsFam act w fun i τ => ∑ k ∈ t, f k i τ) ∧
    (∀ (κ : Type) (t : Finset κ) (w : κ → ℤ) (f : κ → ι → ℍ → ℂ),
      (∀ k ∈ t, _root_.GlobalTheory.QFam.IsFam act (w k) (f k)) →
        _root_.GlobalTheory.QFam.IsFam act (∑ k ∈ t, w k) fun i τ => ∏ k ∈ t, f k i τ) ∧
    (∀ (κ : Type) (act' : κ → SL(2, ℤ) → κ) (φ : κ → ι) w f,
      (∀ k γ, φ (act' k γ) = act (φ k) γ) → _root_.GlobalTheory.QFam.IsFam act w f →
        _root_.GlobalTheory.QFam.IsFam act' w fun k => f (φ k)) := by
  intro ι act
  have hconst : ∀ c : ℂ, _root_.GlobalTheory.QFam.IsFam act 0 fun _ _ => c := by
    intro c i γ
    funext τ
    simp [SL_slash_apply]
  refine ⟨hconst, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w f g hf hg
    constructor
    · intro i γ
      funext τ
      simp only [SL_slash_apply]
      rw [← isFam_apply_smul_mul_denom_zpow hf i γ τ, ← isFam_apply_smul_mul_denom_zpow hg i γ τ]
      ring
    · intro i γ
      funext τ
      simp only [SL_slash_apply]
      rw [← isFam_apply_smul_mul_denom_zpow hf i γ τ, ← isFam_apply_smul_mul_denom_zpow hg i γ τ]
      ring
  · intro w c f hf
    exact hf.const_mul_fun c
  · intro w w' f g hf hg
    exact hf.mul_fun hg
  · intro w f k hf
    exact hf.pow_fun k
  · intro κ t w f hf
    exact _root_.GlobalTheory.QFam.IsFam.sum_fun t hf
  · intro κ t w f hf
    classical
    induction t using Finset.induction_on with
    | empty => simpa using hconst 1
    | insert a s ha ih =>
      have hmul := (hf a (Finset.mem_insert_self a s)).mul_fun
        (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))
      simpa [Finset.sum_insert ha, Finset.prod_insert ha] using hmul
  · intro κ act' φ w f hφ hf k γ
    show f (φ k) ∣[w] γ = f (φ (act' k γ))
    rw [hf (φ k) γ, hφ k γ]

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmoothEventuallyZeroCutoffIntervalIntegralDeri
section
noncomputable section
open scoped ContDiff
open Set MeasureTheory

namespace GlobalTheory.ParamIntCut

theorem hasDerivAt_snd {F : ℝ → ℝ → ℝ} (hF : ContDiff ℝ 1 (Function.uncurry F)) (s y : ℝ) :
    HasDerivAt (F s) (fderiv ℝ (Function.uncurry F) (s, y) (0, 1)) y := by
  have h1 : HasFDerivAt (Function.uncurry F) (fderiv ℝ (Function.uncurry F) (s, y)) (s, y) :=
    (hF.differentiable one_ne_zero (s, y)).hasFDerivAt
  have h2 : HasDerivAt (fun t : ℝ => ((s, t) : ℝ × ℝ)) ((0, 1) : ℝ × ℝ) y :=
    (hasDerivAt_const y s).prodMk (hasDerivAt_id y)
  exact h1.comp_hasDerivAt y h2

theorem hasDerivAt_intervalIntegral {F : ℝ → ℝ → ℝ} (a b : ℝ)
    (hF : ContDiff ℝ 1 (Function.uncurry F)) (y₀ : ℝ) :
    HasDerivAt (fun y => ∫ s in a..b, F s y)
      (∫ s in a..b, fderiv ℝ (Function.uncurry F) (s, y₀) (0, 1)) y₀ := by
  set P : ℝ → ℝ → ℝ := fun s y => fderiv ℝ (Function.uncurry F) (s, y) (0, 1) with hP
  have hPc : Continuous (Function.uncurry P) :=
    (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hFc : Continuous (Function.uncurry F) := hF.continuous
  have hsec : ∀ (G : ℝ → ℝ → ℝ), Continuous (Function.uncurry G) → ∀ y, Continuous (fun s => G s y) :=
    fun G hG y => hG.comp (continuous_id.prodMk continuous_const)
  obtain ⟨C, hC⟩ : ∃ C, ∀ p ∈ (uIcc a b) ×ˢ (Metric.closedBall y₀ 1), ‖Function.uncurry P p‖ ≤ C :=
    (isCompact_uIcc.prod (isCompact_closedBall y₀ 1)).exists_bound_of_continuousOn hPc.continuousOn
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ) (μ := volume)
    (a := a) (b := b) (F := fun y s => F s y) (F' := fun y s => P s y) (x₀ := y₀)
    (bound := fun _ => C) (s := Metric.ball y₀ 1) (Metric.ball_mem_nhds y₀ one_pos)
    (Filter.Eventually.of_forall fun y => (hsec F hFc y).aestronglyMeasurable)
    ((hsec F hFc y₀).intervalIntegrable _ _)
    ((hsec P hPc y₀).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t ht y hy =>
      hC (t, y) ⟨uIoc_subset_uIcc ht, Metric.ball_subset_closedBall hy⟩)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun t _ y _ => hasDerivAt_snd hF t y)
  exact key.2

theorem contDiff_nat_intervalIntegral (a b : ℝ) :
    ∀ (n : ℕ) (F : ℝ → ℝ → ℝ), ContDiff ℝ ∞ (Function.uncurry F) →
      ContDiff ℝ n (fun y => ∫ s in a..b, F s y)
  | 0, F, hF => by
    have h1 : ContDiff ℝ 1 (Function.uncurry F) := hF.of_le (by exact_mod_cast le_top)
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 fun y => (hasDerivAt_intervalIntegral a b h1 y).continuousAt
  | n + 1, F, hF => by
    have h1 : ContDiff ℝ 1 (Function.uncurry F) := hF.of_le (by exact_mod_cast le_top)
    set P : ℝ → ℝ → ℝ := fun s y => fderiv ℝ (Function.uncurry F) (s, y) (0, 1) with hP
    have hPs : ContDiff ℝ ∞ (Function.uncurry P) :=
      (hF.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
    have hc : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by norm_cast
    rw [hc, contDiff_succ_iff_deriv]
    refine ⟨fun y => (hasDerivAt_intervalIntegral a b h1 y).differentiableAt, by simp, ?_⟩
    have hd : deriv (fun y => ∫ s in a..b, F s y) = fun y => ∫ s in a..b, P s y :=
      funext fun y => (hasDerivAt_intervalIntegral a b h1 y).deriv
    rw [hd]
    exact contDiff_nat_intervalIntegral a b n P hPs

end GlobalTheory.ParamIntCut

namespace GlobalTheory.PsCo.Pc1

theorem isCutFn_intervalIntegral_and_deriv :
    ∀ (F : ℝ → ℝ → ℝ) (a b : ℝ), ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry F) →
      (∃ R : ℝ, ∀ s ∈ Set.uIcc a b, ∀ y, R ≤ y → F s y = 0) →
      GlobalTheory.PsCo.Pc1.IsCutFn (fun y => ∫ s in a..b, F s y) ∧
        ∀ y, deriv (fun y => ∫ s in a..b, F s y) y = ∫ s in a..b, deriv (F s) y := by
  intro F a b hF ⟨R, hR⟩
  have h1 : ContDiff ℝ 1 (Function.uncurry F) := hF.of_le (by exact_mod_cast le_top)
  refine ⟨⟨contDiff_infty.2 fun n => GlobalTheory.ParamIntCut.contDiff_nat_intervalIntegral a b n F hF, R, fun y hy => ?_⟩,
    fun y => ?_⟩
  · show ∫ s in a..b, F s y = 0
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun s hs => hR s hs y hy)]
    simp
  · rw [(GlobalTheory.ParamIntCut.hasDerivAt_intervalIntegral a b h1 y).deriv]
    refine intervalIntegral.integral_congr fun s _ => ?_
    exact ((GlobalTheory.ParamIntCut.hasDerivAt_snd h1 s y).deriv).symm

end GlobalTheory.PsCo.Pc1
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
section
noncomputable section

open NumberField Complex MeasureTheory
open scoped nonZeroDivisors ContDiff

namespace GlobalTheory.HeckeTwo

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

variable {F : Type} [Field F] [NumberField F]

def NZ (I : FractionalIdeal (𝓞 F)⁰ F) : Type := {b : F // b ∈ I ∧ b ≠ 0}

def unitRel (I : FractionalIdeal (𝓞 F)⁰ F) : Setoid (NZ I) where
  r p q := ∃ ε : (𝓞 F)ˣ, q.1 = ((ε : 𝓞 F) : F) * p.1
  iseqv :=
    { refl := fun _ => ⟨1, by simp⟩
      symm := fun {p q} ⟨ε, h⟩ => ⟨ε⁻¹, by rw [h, ← mul_assoc, unit_inv_mul, one_mul]⟩
      trans := fun {p q r} ⟨ε, h⟩ ⟨ε', h'⟩ => ⟨ε' * ε, by rw [h', h, ← mul_assoc]; simp⟩ }

def phi (σ w : ℂ) : ℂ := w⁻¹ ^ 2 * ((‖w‖ : ℝ) : ℂ) ^ (-2 * σ)

def hTrans (σ : ℂ) (ν y : ℝ) : ℂ :=
  ∫ t : ℝ, phi σ ((t : ℂ) + (y : ℂ) * I) * Complex.exp (-(2 * (Real.pi : ℂ) * I * (ν : ℂ) * (t : ℂ)))

def cConst (σ : ℂ) : ℂ := hTrans σ 0 1


variable (F) in
def kFac (σ : ℂ) : ℂ :=
  ∏ _τ : Emb F, ((2 * (Real.pi : ℂ) * I)⁻¹ ^ 2 * ((2 * Real.pi : ℝ) : ℂ) ^ (-2 * σ))

def fTerm (σ : ℂ) (z : Emb F → ℂ) (b ν : F) : ℂ :=
  ∏ τ : Emb F, (Complex.exp (2 * (Real.pi : ℂ) * I * ((τ ν * τ b * (z τ).re : ℝ) : ℂ)) *
    hTrans σ (τ ν) (τ b * (z τ).im))

def aPart (𝔞 : Frac F) (σ : ℂ) : ℂ :=
  ∑' c : Quotient (unitRel (latM 𝔞)), eisTerm 2 σ 0 (c.out.1, 0)

def bOne (𝔞 𝔟 : Frac F) (σ : ℂ) (z : Emb F → ℂ) : ℂ :=
  ∑' c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)),
    ∑' ν : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F), fTerm σ z c.out.1 ν.1

def bZero (Zb : ℂ → ℂ) (𝔞 𝔟 : Frac F) (σ : ℂ) (z : Emb F → ℂ) : ℂ :=
  if σ = 0 then 0 else
    kFac (F := F) σ * ((omegaFactor (F := F) 𝔞) : ℂ) * (((nrm (F := F) 𝔟) : ℝ) : ℂ) ^ (-1 - 2 * σ) * Zb (1 + 2 * σ) *
      ∏ τ : Emb F, (cConst σ * (((z τ).im : ℝ) : ℂ) ^ (-1 - 2 * σ))

def gFun (Zb : ℂ → ℂ) (𝔞 𝔟 : Frac F) (σ : ℂ) (z : Emb F → ℂ) : ℂ :=
  aPart 𝔞 σ + bZero Zb 𝔞 𝔟 σ z + kFac (F := F) σ * ((omegaFactor (F := F) 𝔞) : ℂ) * bOne 𝔞 𝔟 σ z

def IsGood (P : ℂ → (Emb F → ℂ) → ℂ) : Prop :=
  (∀ σ ∈ halfPlane, ContDiffOn ℝ ∞ (P σ) (upperHalf F)) ∧
  (∀ w : List (Emb F × Bool), ∀ z ∈ upperHalf F, DifferentiableOn ℂ (fun σ => wirtWord w (P σ) z) halfPlane)

theorem kFac_differentiable : Differentiable ℂ (kFac (F := F)) := by
  intro σ
  unfold kFac
  rw [show (fun σ : ℂ => ∏ _τ : Emb F, ((2 * (Real.pi : ℂ) * I)⁻¹ ^ 2 * ((2 * Real.pi : ℝ) : ℂ) ^ (-2 * σ))) =
      fun σ => ((2 * (Real.pi : ℂ) * I)⁻¹ ^ 2 * ((2 * Real.pi : ℝ) : ℂ) ^ (-2 * σ)) ^ Fintype.card (Emb F) from
    funext fun σ => Finset.prod_const _]
  refine DifferentiableAt.pow (DifferentiableAt.const_mul ?_ _) _
  refine DifferentiableAt.const_cpow (differentiableAt_id.const_mul _) (Or.inl ?_)
  exact_mod_cast (mul_pos two_pos Real.pi_pos).ne'

end GlobalTheory.HeckeTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullIntersectionIdealLocalFormStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.krull_intersection_ideal_local_form : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (I a a' : Ideal B), (∀ e : ℕ, a ≤ a' ⊔ I ^ (e + 1)) → ∃ r ∈ I, ∀ x ∈ a, (1 - r) * x ∈ a' := by
  first | exact @GlobalTheory.krull_inter_ideal_local | exact GlobalTheory.krull_inter_ideal_local | (intros; apply GlobalTheory.krull_inter_ideal_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrylovMatrixConjEqOfCharpolyEq
section
open Matrix Polynomial

noncomputable section

namespace GlobalTheory.LeviDesc.Krylov

theorem pow_dim_eq_neg_sum_charpoly_coeff {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F) :
    y ^ r = - ∑ k : Fin r, y.charpoly.coeff k • y ^ (k : ℕ) := by
  have h := Matrix.aeval_self_charpoly y
  have hm := (Matrix.charpoly_monic y).as_sum
  have hd : y.charpoly.natDegree = r := by simpa using Matrix.charpoly_natDegree_eq_dim y
  rw [hd] at hm
  rw [hm] at h
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, Algebra.smul_def] at h
  rw [Fin.sum_univ_eq_sum_range (fun k => y.charpoly.coeff k • y ^ k)]
  simp only [Algebra.smul_def]
  exact eq_neg_of_add_eq_zero_left h

def companion {F : Type} [Field F] (r : ℕ) (p : F[X]) : Matrix (Fin r) (Fin r) F :=
  Matrix.of fun i j => if (j : ℕ) + 1 < r then (if (i : ℕ) = (j : ℕ) + 1 then 1 else 0) else - p.coeff i

theorem mul_krylov_eq {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F) (e : Fin r → F) :
    y * krylov y e = krylov y e * companion r y.charpoly := by
  ext i j
  have hl : (y * krylov y e) i j = (y ^ ((j : ℕ) + 1) *ᵥ e) i := by
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    simp [Matrix.mul_apply, krylov_apply, Matrix.mulVec, dotProduct]
  rw [hl, Matrix.mul_apply]
  by_cases hj : (j : ℕ) + 1 < r
  · simp only [companion, Matrix.of_apply, hj, if_true]
    rw [Finset.sum_eq_single (⟨(j : ℕ) + 1, hj⟩ : Fin r)]
    · simp [krylov_apply]
    · intro k _ hk
      have : (k : ℕ) ≠ (j : ℕ) + 1 := fun h => hk (Fin.ext h)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hr : (j : ℕ) + 1 = r := by omega
    simp only [companion, Matrix.of_apply, hj, if_false]
    rw [hr, pow_dim_eq_neg_sum_charpoly_coeff y, Matrix.neg_mulVec, Matrix.sum_mulVec]
    simp [krylov_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring

theorem krylov_inv_mul_mul_krylov {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F)
    (e : Fin r → F) (h : IsUnit (krylov y e).det) :
    (krylov y e)⁻¹ * y * krylov y e = companion r y.charpoly := by
  rw [Matrix.mul_assoc, mul_krylov_eq, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h, Matrix.one_mul]

theorem krylov_conj_eq_of_charpoly_eq {F : Type} [Field F] {r : ℕ} (y y' : Matrix (Fin r) (Fin r) F)
    (e e' : Fin r → F) (hχ : y.charpoly = y'.charpoly) (h : IsUnit (krylov y e).det)
    (h' : IsUnit (krylov y' e').det) :
    (krylov y e)⁻¹ * y * krylov y e = (krylov y' e')⁻¹ * y' * krylov y' e' := by
  rw [krylov_inv_mul_mul_krylov y e h, krylov_inv_mul_mul_krylov y' e' h', hχ]

end GlobalTheory.LeviDesc.Krylov
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerAevalValuationDvrStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_aeval_valuation_dvr : ∀ (T V : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Algebra T V] [IsLocalHom (algebraMap T V)],
    Function.Injective (algebraMap T V) →
    ∀ (γ : V) (ϖ u : T) (k : ℕ), Irreducible ϖ → IsUnit u → IsUnit (k : T) → 0 < k →
    γ ^ k = algebraMap T V u →
    ∀ h : Polynomial T, Polynomial.aeval γ h = 0 ∨
      ∃ (a : ℕ) (h' c : Polynomial T), IsUnit (Polynomial.aeval γ c) ∧ IsUnit (Polynomial.aeval γ h') ∧
        Polynomial.aeval γ c * Polynomial.aeval γ h = algebraMap T V ϖ ^ a * Polynomial.aeval γ h' := by
  first | (exact @GlobalTheory.kummer_valuation) | (exact GlobalTheory.kummer_valuation) | (intros; apply GlobalTheory.kummer_valuation  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerResidueMemAdjoinUnitStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_residue_mem_adjoin_unit : ∀ (T V : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Algebra T V] [IsLocalHom (algebraMap T V)],
    Function.Injective (algebraMap T V) →
    ∀ (α γ : V) (ϖ : T) (m : ℕ), Irreducible ϖ → 0 < m → IsUnit γ →
    α ^ m = γ * algebraMap T V ϖ →
    (∀ h : Polynomial T, Polynomial.aeval γ h = 0 ∨
      ∃ (a : ℕ) (h' c : Polynomial T), IsUnit (Polynomial.aeval γ c) ∧ IsUnit (Polynomial.aeval γ h') ∧
        Polynomial.aeval γ c * Polynomial.aeval γ h = algebraMap T V ϖ ^ a * Polynomial.aeval γ h') →
    (∀ v : V, ∃ f g : Polynomial T, Polynomial.aeval α g ≠ 0 ∧ Polynomial.aeval α g * v = Polynomial.aeval α f) →
    ∀ v : V, IsLocalRing.residue V v ∈
      IntermediateField.adjoin (IsLocalRing.ResidueField T) {IsLocalRing.residue V γ} := by
  first | (exact @GlobalTheory.kummer_residue_mem_adjoin) | (exact GlobalTheory.kummer_residue_mem_adjoin) | (intros; apply GlobalTheory.kummer_residue_mem_adjoin  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerUniformiserAdjoinRootTensorIsReducedStatement
section
open IsLocalRing
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_uniformiser_adjoinRoot_tensor_isReduced : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D],
    Nonempty (D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) → Irreducible π → IsUnit (e : S) →
    IsReduced (TensorProduct S D L) := by
  first | (exact @GlobalTheory.kummer_uniformiser_tensor_isReduced) | (exact GlobalTheory.kummer_uniformiser_tensor_isReduced) | (intros; apply GlobalTheory.kummer_uniformiser_tensor_isReduced  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LambdaCoeffCommutesModeDerivation
section
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Cw2a

theorem exL_dL_holds : GlobalTheory.PsCo.Cw2a.T_exL_dL := by
  intro n L ε x b
  have h := _root_.GlobalTheory.coeff_allOnes_sumAlgEquiv_mkDerivation (σ := EntIdx n) (L := L) (dM ε x) b
  simpa [exL, dL, inL, allOnes] using h

end GlobalTheory.PsCo.Cw2a
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LambdaMonomialCoeffDualNumberProductEq
section
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Cw2a

theorem t_exL_dual : T_exL_dual := by
  intro n L m a
  exact GlobalTheory.coeff_allOnes_prod_one_add_mul (σ := EntIdx n) m a

end GlobalTheory.PsCo.Cw2a
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeTranslatesCutoffSummableStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_translates_cutoff_summable : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (h f : SchwartzMap V ℂ), HasCompactSupport h →
    ∀ u : Λ → SchwartzMap V ℂ, (∀ (l : Λ) (x : V), u l x = h (x + l) * f x) →
    ∀ k n : ℕ, Summable (fun l => SchwartzMap.seminorm ℂ k n (u l)) := by
  first | exact @GlobalTheory.SchwartzTranslateSum.summable_seminorm_mul_translate | exact GlobalTheory.SchwartzTranslateSum.summable_seminorm_mul_translate | (intros; apply GlobalTheory.SchwartzTranslateSum.summable_seminorm_mul_translate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeMulSetIntegralImage2OfForallLeStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.le_mul_setIntegral_image2_of_forall_le_alt : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (N : ℕ) (Θ : (Fin N → ℝ) → G) (Q : Set (Fin N → ℝ)) (B : Set G) (K : ℝ), Continuous Θ → IsCompact Q → IsCompact B → B ∈ nhds (1 : G) → 0 ≤ K → ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : G → ℝ) (a : ℝ), Continuous F → (∀ g, 0 ≤ F g) → (∀ x ∈ B, a ≤ K * ∫ t in Q, F (Θ t * x)) → a ≤ C * ∫ x in Set.image2 (fun t b => Θ t * b) Q B, F x ∂μ := by
  first | exact @GlobalTheory.le_mul_setIntegral_image2_of_forall_le | exact GlobalTheory.le_mul_setIntegral_image2_of_forall_le | (intros; apply GlobalTheory.le_mul_setIntegral_image2_of_forall_le <;> assumption)
end

