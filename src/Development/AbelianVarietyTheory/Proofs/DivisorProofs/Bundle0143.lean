module

public import Mathlib
public import GroundTheory.GlobalFields.TateThesis.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0046

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzGaussWidth
section
open FourierTransform MeasureTheory Filter Topology

noncomputable section
namespace GlobalTheory.GaussWidths

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem exists_schwartz_gauss_width (c : ℝ) (hc : 0 < c) :
    ∃ g : SchwartzMap E ℂ, ∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) := by
  set t : ℝ := Real.sqrt (c / Real.pi) with ht_def
  have ht : t ≠ 0 := (Real.sqrt_pos.2 (div_pos hc Real.pi_pos)).ne'
  have ht2 : t ^ 2 = c / Real.pi := Real.sq_sqrt (div_pos hc Real.pi_pos).le
  let e : E ≃L[ℝ] E := (LinearEquiv.smulOfNeZero ℝ E t ht).toContinuousLinearEquiv
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (GroundTheory.Global.gaussianSchwartz E), fun y => ?_⟩
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    GroundTheory.Global.gaussianSchwartz_apply, Complex.ofReal_exp]
  congr 1
  have hey : e y = t • y := rfl
  rw [hey, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ht2]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  push_cast
  field_simp

theorem mem_of_smul {M : Submodule ℂ (SchwartzMap E ℂ)} (c : ℝ) (K : ℂ) (hK : K ≠ 0)
    (u : SchwartzMap E ℂ) (hu : ∀ y, u y = K * Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)))
    (huM : u ∈ M) :
    ∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M := by
  intro g hg
  have : g = K⁻¹ • u := by
    ext y
    rw [SchwartzMap.smul_apply, hu, hg, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hK, one_mul]
  rw [this]
  exact M.smul_mem _ huM

variable [MeasurableSpace E] [BorelSpace E]

theorem integral_gauss_mul_gauss (s c : ℝ) (hs : 0 < s) (hc : 0 < c) (y : E) :
    ∫ a : E, Complex.exp (-((s * ‖a‖ ^ 2 : ℝ) : ℂ)) * Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ)) =
      ((Real.pi : ℂ) / ((s + c : ℝ) : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ) *
        Complex.exp (-(((s * c / (s + c)) * ‖y‖ ^ 2 : ℝ) : ℂ)) := by
  have hsc : 0 < s + c := by linarith
  have key : ∀ a : E, Complex.exp (-((s * ‖a‖ ^ 2 : ℝ) : ℂ)) *
      Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ)) =
      Complex.exp (-((s + c : ℝ) : ℂ) * (‖a‖ : ℂ) ^ 2 + ((2 * c : ℝ) : ℂ) * ((inner ℝ y a : ℝ) : ℂ)) *
        Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ)) := by
    intro a
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    rw [norm_sub_sq_real]
    push_cast
    ring
  simp_rw [key]
  rw [integral_mul_const, GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (by simpa using hsc) _ y, mul_assoc, ← Complex.exp_add]
  congr 2
  have h1 : ((s + c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsc.ne'
  push_cast at h1 ⊢
  field_simp
  ring

end GlobalTheory.GaussWidths

namespace GlobalTheory.GaussWidths

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

def HasWidth (M : Submodule ℂ (SchwartzMap E ℂ)) (c : ℝ) : Prop :=
  ∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M

def ConvStable (M : Submodule ℂ (SchwartzMap E ℂ)) : Prop :=
  ∀ (b c : ℝ), 0 < b → 0 < c →
    (∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M) →
    ∀ (h u : SchwartzMap E ℂ),
      (∀ y, u y = ∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a *
        Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))) → u ∈ M

theorem cpow_ne_zero_of_pos (r : ℝ) (hr : 0 < r) (z : ℂ) : ((r : ℂ)) ^ z ≠ 0 := by
  intro h
  rw [Complex.cpow_eq_zero_iff] at h
  exact (Complex.ofReal_ne_zero.2 hr.ne') h.1

theorem hasWidth_of_lt {M : Submodule ℂ (SchwartzMap E ℂ)} (hconv : ConvStable M) (c : ℝ)
    (hc : 0 < c) (hP : HasWidth M c) (c' : ℝ) (hc' : 0 < c') (hlt : c' < c) : HasWidth M c' := by
  set s : ℝ := c * c' / (c - c') with hs_def
  have hcc : 0 < c - c' := by linarith
  have hs : 0 < s := div_pos (mul_pos hc hc') hcc
  have hsc : s * c / (s + c) = c' := by
    rw [hs_def]; field_simp; ring
  obtain ⟨h, hh⟩ := exists_schwartz_gauss_width (E := E) (s / 2) (by linarith)
  obtain ⟨g', hg'⟩ := exists_schwartz_gauss_width (E := E) c' hc'
  set K : ℂ := ((Real.pi : ℂ) / ((s + c : ℝ) : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ)
  have hK : K ≠ 0 := by
    have : (Real.pi : ℂ) / ((s + c : ℝ) : ℂ) = ((Real.pi / (s + c) : ℝ) : ℂ) := by push_cast; rfl
    simp only [K, this]
    exact cpow_ne_zero_of_pos _ (div_pos Real.pi_pos (by linarith)) _
  have huM : K • g' ∈ M := hconv (s / 2) c (by linarith) hc hP h (K • g') (fun y => by
    rw [SchwartzMap.smul_apply, smul_eq_mul, hg', ← hsc, ← integral_gauss_mul_gauss s c hs hc y]
    congr 1
    funext a
    rw [hh]
    simp only [← Complex.exp_add]
    congr 1
    push_cast
    ring)
  exact mem_of_smul c' K hK (K • g') (fun y => by rw [SchwartzMap.smul_apply, smul_eq_mul, hg']) huM

theorem hasWidth_fourier {M : Submodule ℂ (SchwartzMap E ℂ)} (hF : ∀ f ∈ M, 𝓕 f ∈ M) (c : ℝ)
    (hc : 0 < c) (hP : HasWidth M c) : HasWidth M (Real.pi ^ 2 / c) := by
  obtain ⟨g, hg⟩ := exists_schwartz_gauss_width (E := E) c hc
  set K : ℂ := ((Real.pi : ℂ) / (c : ℂ)) ^ (Module.finrank ℝ E / 2 : ℂ)
  have hK : K ≠ 0 := by
    have : (Real.pi : ℂ) / (c : ℂ) = ((Real.pi / c : ℝ) : ℂ) := by push_cast; rfl
    simp only [K, this]
    exact cpow_ne_zero_of_pos _ (div_pos Real.pi_pos hc) _
  refine mem_of_smul (Real.pi ^ 2 / c) K hK (𝓕 g) (fun w => ?_) (hF g (hP g hg))
  have hfun : (g : E → ℂ) = fun v => Complex.exp (-(c : ℂ) * (‖v‖ : ℂ) ^ 2) := by
    funext v; rw [hg]; push_cast; ring_nf
  rw [SchwartzMap.fourier_coe, hfun, fourier_gaussian_innerProductSpace (by simpa using hc)]
  congr 2
  have : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  push_cast
  field_simp

theorem hasWidth_all {M : Submodule ℂ (SchwartzMap E ℂ)} (hconv : ConvStable M)
    (hF : ∀ f ∈ M, 𝓕 f ∈ M) (hπ : HasWidth M Real.pi) (c : ℝ) (hc : 0 < c) : HasWidth M c := by
  rcases lt_trichotomy c Real.pi with hlt | heq | hgt
  · exact hasWidth_of_lt hconv Real.pi Real.pi_pos hπ c hc hlt
  · exact heq ▸ hπ
  · have hc' : 0 < Real.pi ^ 2 / c := by positivity
    have hlt : Real.pi ^ 2 / c < Real.pi := by
      rw [div_lt_iff₀ hc]; nlinarith [Real.pi_pos]
    have h1 := hasWidth_fourier hF _ hc' (hasWidth_of_lt hconv Real.pi Real.pi_pos hπ _ hc' hlt)
    have : Real.pi ^ 2 / (Real.pi ^ 2 / c) = c := by
      have := Real.pi_pos.ne'; field_simp
    rwa [this] at h1

theorem hasWidth_pi {M : Submodule ℂ (SchwartzMap E ℂ)} (G : SchwartzMap E ℂ)
    (hG : ∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) (hGM : G ∈ M) :
    HasWidth M Real.pi := by
  intro g hg
  have : g = G := by ext y; rw [hg, hG]
  rwa [this]

end GlobalTheory.GaussWidths

namespace GlobalTheory.GaussWidths

theorem all_widths_of_conv
    (hconvAll : ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
      [MeasurableSpace E] [BorelSpace E]
      (M : Submodule ℂ (SchwartzMap E ℂ)), IsClosed (M : Set (SchwartzMap E ℂ)) →
      (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M) →
      ∀ (b c : ℝ), 0 < b → 0 < c →
      (∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M) →
      ∀ (h u : SchwartzMap E ℂ),
        (∀ y, u y = ∫ a, Complex.exp (-((b * ‖a‖ ^ 2 : ℝ) : ℂ)) * h a *
          Complex.exp (-((c * ‖y - a‖ ^ 2 : ℝ) : ℂ))) →
        u ∈ M) :
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (M : Submodule ℂ (SchwartzMap E ℂ)), IsClosed (M : Set (SchwartzMap E ℂ)) →
    (∀ (ℓ : E →L[ℝ] ℝ) (f f₁ : SchwartzMap E ℂ), f ∈ M → (∀ x, f₁ x = (ℓ x : ℂ) * f x) → f₁ ∈ M) →
    (∀ f ∈ M, 𝓕 f ∈ M) →
    ∀ G : SchwartzMap E ℂ, (∀ y, G y = Complex.exp (-((Real.pi * ‖y‖ ^ 2 : ℝ) : ℂ))) → G ∈ M →
    ∀ (c : ℝ), 0 < c → ∀ g : SchwartzMap E ℂ, (∀ y, g y = Complex.exp (-((c * ‖y‖ ^ 2 : ℝ) : ℂ))) → g ∈ M := by
  intro E _ _ _ _ _ M hM hℓ hF G hG hGM c hc g hg
  exact hasWidth_all (fun b c' hb hc' hP h u hu => hconvAll E M hM hℓ b c' hb hc' hP h u hu) hF
    (hasWidth_pi G hG hGM) c hc g hg

end GlobalTheory.GaussWidths
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionLiftingResidueValues
section
open IsLocalRing

namespace GlobalTheory.DenseSec

theorem factorₐ_comp_factorₐ {P R : Type} [CommRing P] [CommRing R] [Algebra P R] {I J K : Ideal R}
    (hIJ : I ≤ J) (hJK : J ≤ K) :
    (Ideal.Quotient.factorₐ P hJK).comp (Ideal.Quotient.factorₐ P hIJ) =
      Ideal.Quotient.factorₐ P (hIJ.trans hJK) := by
  apply AlgHom.ext
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem hensel_etChart : ∀ (R : Type) [CommRing R] [IsLocalRing R], IsAdicComplete (maximalIdeal R) R →
    ∀ (A : Type) [CommRing A] [Algebra R A] (g : ℕ) (t : Fin g → A) (h : A), GlobalTheory.DenseSec.EtChart R A t h →
    ∀ (ε : A →ₐ[R] R), IsUnit (ε h) → ∀ c : Fin g → R, (∀ i, c i - ε (t i) ∈ maximalIdeal R) →
    ∃ a : A →ₐ[R] R, IsUnit (a h) ∧ ∀ i, a (t i) = c i := by
  intro R _ _ hc A _ _ g t h hE ε hε c hcε
  classical
  haveI := hc
  letI iPB : Algebra (MvPolynomial (Fin g) R) (Localization.Away h) :=
    ((algebraMap A (Localization.Away h)).comp (MvPolynomial.aeval t).toRingHom).toAlgebra
  haveI hEt : Algebra.Etale (MvPolynomial (Fin g) R) (Localization.Away h) := hE
  letI iPR : Algebra (MvPolynomial (Fin g) R) R := (MvPolynomial.aeval c).toRingHom.toAlgebra
  have hPB : ∀ p, algebraMap (MvPolynomial (Fin g) R) (Localization.Away h) p =
      algebraMap A (Localization.Away h) (MvPolynomial.aeval t p) := fun _ => rfl
  have hPR : ∀ p, algebraMap (MvPolynomial (Fin g) R) R p = MvPolynomial.aeval c p := fun _ => rfl
  let m := maximalIdeal R

  let e' : Localization.Away h →+* R := IsLocalization.Away.lift h (g := (ε : A →+* R)) hε
  have he' : ∀ x : A, e' (algebraMap A (Localization.Away h) x) = ε x := fun x =>
    IsLocalization.Away.lift_eq h (g := (ε : A →+* R)) hε x
  have hmod : (Ideal.Quotient.mk m).comp ((ε : A →+* R).comp (MvPolynomial.aeval (R := R) t).toRingHom) =
      (Ideal.Quotient.mk m).comp (MvPolynomial.aeval c).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.aeval_X]
      exact (Ideal.Quotient.eq.2 (by
        have := hcε i
        rw [← neg_mem_iff, neg_sub] at this
        exact this))
  let f₁ : Localization.Away h →ₐ[MvPolynomial (Fin g) R] R ⧸ m :=
    { toRingHom := (Ideal.Quotient.mk m).comp e'
      commutes' := fun p => by
        show Ideal.Quotient.mk m (e' (algebraMap (MvPolynomial (Fin g) R) (Localization.Away h) p)) =
          algebraMap (MvPolynomial (Fin g) R) (R ⧸ m) p
        rw [hPB, he']
        show Ideal.Quotient.mk m (ε (MvPolynomial.aeval t p)) = Ideal.Quotient.mk m (MvPolynomial.aeval c p)
        exact congrArg (fun φ : MvPolynomial (Fin g) R →+* R ⧸ m => φ p) hmod }

  have hle : ∀ n : ℕ, m ^ (n + 1) ≤ m := fun n => Ideal.pow_le_self n.succ_ne_zero
  let q : ∀ n : ℕ, R ⧸ m ^ (n + 1) →ₐ[MvPolynomial (Fin g) R] R ⧸ m := fun n =>
    Ideal.Quotient.factorₐ _ (hle n)
  have hqs : ∀ n, Function.Surjective (q n) := fun n x => by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk _ y, rfl⟩
  have hqn : ∀ n, IsNilpotent (RingHom.ker (q n : R ⧸ m ^ (n + 1) →+* R ⧸ m)) := fun n => by
    refine ⟨n + 1, le_bot_iff.1 ?_⟩
    have hk : RingHom.ker (q n : R ⧸ m ^ (n + 1) →+* R ⧸ m) = Ideal.map (Ideal.Quotient.mk (m ^ (n + 1))) m :=
      Ideal.Quotient.factor_ker (hle n)
    rw [hk, ← Ideal.map_pow, Ideal.map_quotient_self]
  let F : ∀ n : ℕ, Localization.Away h →ₐ[MvPolynomial (Fin g) R] R ⧸ m ^ (n + 1) := fun n =>
    Algebra.FormallySmooth.liftOfSurjective f₁ (q n) (hqs n) (hqn n)
  have hF : ∀ n, (q n).comp (F n) = f₁ := fun n => Algebra.FormallySmooth.comp_liftOfSurjective _ _ _ _
  have hFc : ∀ {k n : ℕ} (hkn : k ≤ n),
      (Ideal.Quotient.factorₐ (MvPolynomial (Fin g) R) (Ideal.pow_le_pow_right (Nat.succ_le_succ hkn))).comp (F n) = F k := by
    intro k n hkn
    refine Algebra.FormallyUnramified.ext' (q k : R ⧸ m ^ (k + 1) →+* R ⧸ m) (hqn k) _ _ fun x => ?_
    have h1 := congrArg (fun φ => φ x) (hF n)
    have h2 := congrArg (fun φ => φ x) (hF k)
    simp only [AlgHom.comp_apply] at h1 h2
    show (q k) ((Ideal.Quotient.factorₐ (MvPolynomial (Fin g) R) (Ideal.pow_le_pow_right (Nat.succ_le_succ hkn) : m ^ (n + 1) ≤ m ^ (k + 1))) (F n x)) = q k (F k x)
    rw [h2, ← h1]
    have := congrArg (fun φ => φ (F n x)) (factorₐ_comp_factorₐ (P := MvPolynomial (Fin g) R)
      (Ideal.pow_le_pow_right (Nat.succ_le_succ hkn) : m ^ (n + 1) ≤ m ^ (k + 1)) (hle k))
    simpa only [AlgHom.comp_apply] using this
  let f : ∀ n : ℕ, Localization.Away h →ₐ[MvPolynomial (Fin g) R] R ⧸ m ^ n := fun n =>
    (Ideal.Quotient.factorₐ _ (Ideal.pow_le_pow_right (Nat.le_succ n))).comp (F n)
  have hf : ∀ {k n : ℕ} (hkn : k ≤ n),
      (Ideal.Quotient.factorₐ (MvPolynomial (Fin g) R) (Ideal.pow_le_pow_right hkn)).comp (f n) = f k := by
    intro k n hkn
    simp only [f]
    rw [← AlgHom.comp_assoc, factorₐ_comp_factorₐ, ← hFc hkn, ← AlgHom.comp_assoc, factorₐ_comp_factorₐ]
  let Φ : Localization.Away h →ₐ[MvPolynomial (Fin g) R] R := IsAdicComplete.liftAlgHom m f hf
  let a : A →ₐ[R] R :=
    { toRingHom := (Φ : Localization.Away h →+* R).comp (algebraMap A (Localization.Away h))
      commutes' := fun r => by
        show Φ (algebraMap A (Localization.Away h) (algebraMap R A r)) = algebraMap R R r
        have : algebraMap A (Localization.Away h) (algebraMap R A r) =
            algebraMap (MvPolynomial (Fin g) R) (Localization.Away h) (MvPolynomial.C r) := by
          rw [hPB, MvPolynomial.aeval_C]
        rw [this, Φ.commutes, hPR, MvPolynomial.aeval_C] }
  refine ⟨a, ?_, fun i => ?_⟩
  · exact (IsLocalization.Away.algebraMap_isUnit h).map Φ
  · show Φ (algebraMap A (Localization.Away h) (t i)) = c i
    have : algebraMap A (Localization.Away h) (t i) =
        algebraMap (MvPolynomial (Fin g) R) (Localization.Away h) (MvPolynomial.X i) := by
      rw [hPB, MvPolynomial.aeval_X]
    rw [this, Φ.commutes, hPR, MvPolynomial.aeval_X]

end GlobalTheory.DenseSec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfReciprocalInvAlgWithPoly
section
open Polynomial

namespace GlobalTheory.UnitLemma

noncomputable section

namespace InertUnit

variable {K : UQ} {P : K.E[X]}

theorem coeff_mul (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    K.c (P.coeff 0) * P.coeff 0 = 1 := by
  have h := congrArg (fun Q => Q.coeff 0) hr
  simp only [coeff_C_mul, coeff_zero_reverse] at h
  rw [h, leadingCoeff_map_of_leadingCoeff_ne_zero _ (by simp [hP.leadingCoeff]), hP.leadingCoeff, map_one]

def rootInv (P : K.E[X]) : AdjoinRoot P :=
  -(algebraMap K.E (AdjoinRoot P) (K.c (P.coeff 0))) * aeval (AdjoinRoot.root P) P.divX

theorem root_mul_rootInv (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    AdjoinRoot.root P * rootInv P = 1 := by
  have h0 : aeval (AdjoinRoot.root P) P = 0 := AdjoinRoot.aeval_eq P ▸ AdjoinRoot.mk_self
  have h1 := congrArg (aeval (AdjoinRoot.root P)) (X_mul_divX_add P)
  rw [h0, map_add (f := _), map_mul, aeval_X, aeval_C] at h1
  have h2 : AdjoinRoot.root P * aeval (AdjoinRoot.root P) P.divX = -algebraMap K.E (AdjoinRoot P) (P.coeff 0) :=
    eq_neg_of_add_eq_zero_left h1
  unfold rootInv
  rw [mul_left_comm, h2, neg_mul_neg, ← map_mul, coeff_mul hP hr, map_one]

theorem eval_rootInv (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    P.eval₂ ((algebraMap K.E (AdjoinRoot P)).comp (K.c : K.E →+* K.E)) (rootInv P) = 0 := by
  have hu := root_mul_rootInv hP hr
  letI : Invertible (rootInv P) := ⟨AdjoinRoot.root P, hu, by rw [mul_comm]; exact hu⟩
  rw [← eval₂_map, ← eval₂_reverse_mul_pow]
  have : ⅟(rootInv P) = AdjoinRoot.root P := rfl
  rw [this, ← hr, eval₂_mul, eval₂_C]
  have h0 : P.eval₂ (algebraMap K.E (AdjoinRoot P)) (AdjoinRoot.root P) = 0 := AdjoinRoot.eval₂_root P
  rw [h0, mul_zero, zero_mul]

def sig (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    AdjoinRoot P →+* AdjoinRoot P :=
  AdjoinRoot.lift ((algebraMap K.E (AdjoinRoot P)).comp (K.c : K.E →+* K.E)) (rootInv P) (eval_rootInv hP hr)

theorem sig_alg (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) (e : K.E) :
    sig hP hr (algebraMap K.E (AdjoinRoot P) e) = algebraMap K.E (AdjoinRoot P) (K.c e) := by
  rw [AdjoinRoot.algebraMap_eq, sig, AdjoinRoot.lift_of]
  rfl

theorem sig_root (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    sig hP hr (AdjoinRoot.root P) = rootInv P := AdjoinRoot.lift_root _

theorem sig_sig (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    (sig hP hr).comp (sig hP hr) = RingHom.id _ := by
  refine AdjoinRoot.ringHom_ext (RingHom.ext fun e => ?_) ?_
  · simp only [RingHom.comp_apply, RingHom.id_apply]
    rw [← AdjoinRoot.algebraMap_eq, sig_alg, sig_alg, K.c_c]
  · simp only [RingHom.comp_apply, RingHom.id_apply, sig_root]
    have hu := root_mul_rootInv hP hr
    have h1 : sig hP hr (AdjoinRoot.root P) * sig hP hr (rootInv P) = 1 := by rw [← map_mul, hu, map_one]
    rw [sig_root] at h1
    calc sig hP hr (rootInv P) = (AdjoinRoot.root P * rootInv P) * sig hP hr (rootInv P) := by rw [hu, one_mul]
      _ = AdjoinRoot.root P * (rootInv P * sig hP hr (rootInv P)) := by ring
      _ = AdjoinRoot.root P := by rw [h1, mul_one]

def invAlg (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) : InvAlg K where
  A := AdjoinRoot P
  fd := (AdjoinRoot.powerBasis hP.ne_zero).finite
  σ := RingEquiv.ofRingHom (sig hP hr) (sig hP hr) (sig_sig hP hr) (sig_sig hP hr)
  σ_σ := fun y => congrArg (fun f : AdjoinRoot P →+* AdjoinRoot P => f y) (sig_sig hP hr)
  σ_alg := sig_alg hP hr
  g := AdjoinRoot.root P

theorem charpoly_root (hP : P.Monic) (hr : C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse) :
    (invAlg hP hr).P = P := by
  haveI : Module.Finite K.E (AdjoinRoot P) := (AdjoinRoot.powerBasis hP.ne_zero).finite
  have h := charpoly_leftMulMatrix (AdjoinRoot.powerBasis hP.ne_zero)
  rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix, AdjoinRoot.powerBasis_gen,
    AdjoinRoot.minpoly_root hP.ne_zero, hP.leadingCoeff, inv_one, C_1, mul_one] at h
  exact h

end InertUnit

open InertUnit in
theorem exists_invAlg_root : ∀ (K : GlobalTheory.UnitLemma.UQ) (P : K.E[X]), P.Monic →
    C (K.c (P.coeff 0)) * P = (P.map (K.c : K.E →+* K.E)).reverse →
    ∃ B : GlobalTheory.UnitLemma.InvAlg K, B.g * B.σ B.g = 1 ∧ B.P = P := by
  intro K P hP hr
  refine ⟨invAlg hP hr, ?_, charpoly_root hP hr⟩
  show AdjoinRoot.root P * sig hP hr (AdjoinRoot.root P) = 1
  rw [sig_root]
  exact root_mul_rootInv hP hr
end
end GlobalTheory.UnitLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSkewHermitianMulAddDetNeZeroOfPair
section
open scoped Matrix

namespace GlobalTheory

theorem exists_skewHermitian_mul_add_det_ne_zero_of_pair :
    ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → ∀ ε : k, ε ≠ 0 → σ ε = -ε →
    ∀ (n : ℕ) (C D : Matrix (Fin n) (Fin n) k), C * (D.map σ)ᵀ + D * (C.map σ)ᵀ = 0 →
    (∀ a : Fin n → k, a ᵥ* C = 0 → a ᵥ* D = 0 → a = 0) →
      ∃ V : Matrix (Fin n) (Fin n) k, (V.map σ)ᵀ = -V ∧ (C * V + D).det ≠ 0 := by
  intro k _ σ hσ ε hε hσε n C D hCD hrk
  obtain ⟨U, P, e, hU, hP, he, hE⟩ := _root_.GlobalTheory.rank_normal_form_field k n C
  have hmul : ∀ A B : Matrix (Fin n) (Fin n) k,
      ((A * B).map σ)ᵀ = (B.map σ)ᵀ * (A.map σ)ᵀ := by
    intro A B
    rw [Matrix.map_mul, Matrix.transpose_mul]
  have hinv : ∀ A : Matrix (Fin n) (Fin n) k, (((A.map σ)ᵀ).map σ)ᵀ = A := by
    intro A
    ext i j
    simp [hσ]
  have hone : (((1 : Matrix (Fin n) (Fin n) k).map σ)ᵀ) = 1 := by
    rw [Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  have hUu : IsUnit U.det := isUnit_iff_ne_zero.mpr hU
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hPu
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hPu
  have h3 : U * U⁻¹ = 1 := Matrix.mul_nonsing_inv U hUu
  set E : Matrix (Fin n) (Fin n) k := Matrix.diagonal e with hEdef
  have hEE : E * E = E := by
    rw [hEdef, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rcases he i with h | h <;> simp [h]
  have hEs : (E.map σ)ᵀ = E := by
    rw [hEdef, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose]
    congr 1
    funext i
    rcases he i with h | h <;> simp [h]
  set Q : Matrix (Fin n) (Fin n) k := (P⁻¹.map σ)ᵀ with hQ
  set Ps : Matrix (Fin n) (Fin n) k := (P.map σ)ᵀ with hPs
  have hPQ : Ps * Q = 1 := by rw [hPs, hQ, ← hmul, h2, hone]
  have hQP : Q * Ps = 1 := by rw [hPs, hQ, ← hmul, h1, hone]
  have hQs : (Q.map σ)ᵀ = P⁻¹ := hinv _
  have hE' : E = Ps * ((C.map σ)ᵀ * (U.map σ)ᵀ) := by
    rw [← hEs, ← hE, hmul, hmul]
  have hA : E * ((U * D * Q).map σ)ᵀ = U * (C * (D.map σ)ᵀ) * (U.map σ)ᵀ := by
    rw [hmul, hmul, hQs, ← hE]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P, h1, Matrix.one_mul]
  have hB : U * D * Q * E = U * (D * (C.map σ)ᵀ) * (U.map σ)ᵀ := by
    rw [hE']
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q, hQP, Matrix.one_mul]
  have hsum : E * ((U * D * Q).map σ)ᵀ + U * D * Q * E = 0 := by
    rw [hA, hB, ← Matrix.add_mul, ← Matrix.mul_add, hCD, Matrix.mul_zero, Matrix.zero_mul]
  have hrk' : ∀ a : Fin n → k, a ᵥ* E = 0 → a ᵥ* (U * D * Q) = 0 → a = 0 := by
    intro a ha hb
    have e1 : U * C = E * P⁻¹ := by
      rw [← hE, Matrix.mul_assoc, h1, Matrix.mul_one]
    have e2 : U * D = (U * D * Q) * Ps := by
      rw [Matrix.mul_assoc, hQP, Matrix.mul_one]
    have h0 : a ᵥ* U = 0 := by
      apply hrk
      · rw [Matrix.vecMul_vecMul, e1, ← Matrix.vecMul_vecMul, ha, Matrix.zero_vecMul]
      · rw [Matrix.vecMul_vecMul, e2, ← Matrix.vecMul_vecMul, hb, Matrix.zero_vecMul]
    have : a ᵥ* (U * U⁻¹) = 0 := by
      rw [← Matrix.vecMul_vecMul, h0, Matrix.zero_vecMul]
    rwa [h3, Matrix.vecMul_one] at this
  obtain ⟨V', hV', hdet⟩ := _root_.GlobalTheory.skewHermitian_perturb_idempotent_det_ne_zero k σ hσ ε hε hσε n E (U * D * Q) hEE hEs hsum hrk'
  refine ⟨P * V' * Ps, ?_, ?_⟩
  · have hPss : (Ps.map σ)ᵀ = P := hinv _
    rw [hmul, hmul, hV', hPss, ← hPs]
    simp [Matrix.mul_assoc]
  · intro h
    apply hdet
    have : E * V' + U * D * Q = U * (C * (P * V' * Ps) + D) * Q := by
      rw [← hE, Matrix.mul_add, Matrix.add_mul]
      simp only [Matrix.mul_assoc]
      rw [hPQ, Matrix.mul_one]
    rw [this, Matrix.det_mul, Matrix.det_mul, h, mul_zero, zero_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationRingDominatingSpecializationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuationRing_dominating_specialization : ∀ (X : Scheme.{0}) (x' x : X), x' ⤳ x → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : ValuationRing V) (g : Spec (CommRingCat.of V) ⟶ X), g (IsLocalRing.closedPoint V) = x ∧ g (⊥ : PrimeSpectrum V) = x' := by
  first | exact @GlobalTheory.exists_valuationRing_of_specializes | exact GlobalTheory.exists_valuationRing_of_specializes | (intros; apply GlobalTheory.exists_valuationRing_of_specializes <;> assumption)
end

