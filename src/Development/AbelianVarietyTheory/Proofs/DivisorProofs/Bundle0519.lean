module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0506
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0472
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0498
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0476
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0496
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0493
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumHilbertEisensteinMovedPoint
section
set_option autoImplicit false

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem hasSum_movedPoint : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (τ c t : ℂ) (z : Emb F → ℂ), Even k → IsCoef k 𝔞 𝔟 a₀ a → (∀ i, 1 + z i * c ≠ 0 ∧ 0 < (τ + t * z i / (1 + z i * c)).im) → HasSum (fun ξ : F ↦ a ξ * eTr (ξ * x) * Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) * ∏ i : Emb F, ((1 + z i * c)⁻¹ ^ k * Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c)))) ((cK F k : ℂ) * gval k (split 𝔞 𝔟 x) (fun i ↦ τ + z i * (c * τ + t)) (fun i ↦ 1 + z i * c) / ((2 * Real.pi * Complex.I) ^ Module.finrank ℚ F * (omegaFactor 𝔞 : ℂ)) ^ k) := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x τ c t z hk ha hz
  have hw : (fun i : Emb F ↦ τ + t * z i / (1 + z i * c)) ∈ upperHalf F := fun i ↦ (hz i).2
  have h1 := _root_.GlobalTheory.HilbFam.hasSum_split_shift F k 𝔞 𝔟 a₀ a x _ hk ha hw
  have h2 := _root_.GlobalTheory.HilbFam.gval_linear_change F k (split 𝔞 𝔟 x) (split 𝔞 𝔟 x) (LinearEquiv.refl F _)
    (fun i ↦ τ + z i * (c * τ + t)) (fun i ↦ 1 + z i * c) (fun i ↦ τ + t * z i / (1 + z i * c)) 1
    (fun i ↦ 1 + z i * c) hk (fun _ ↦ Iff.rfl) (fun i ↦ (hz i).1) (fun v i ↦ by
      have := (hz i).1
      simp only [coord, LinearEquiv.refl_apply, Pi.one_apply]
      field_simp
      ring)
  have h3 := h1.mul_left ((∏ i, (1 + z i * c))⁻¹ ^ k)
  rw [h2]
  convert (preTransparency := .reducible) h3 using 1
  · rfl
  · funext ξ
    have hq : qPow ξ (fun i : Emb F ↦ τ + t * z i / (1 + z i * c)) =
        Complex.exp ((2 * Real.pi * Complex.I) * ((Algebra.trace ℚ F ξ : ℚ) : ℂ) * τ) *
          ∏ i : Emb F, Complex.exp ((2 * Real.pi * Complex.I) * (i ξ : ℂ) * t * z i / (1 + z i * c)) := by
      rw [← Complex.exp_sum, ← Complex.exp_add, ← _root_.GlobalTheory.HilbFam.sum_realEmb_eq_trace F ξ]
      unfold qPow
      congr 1
      simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      ring
    rw [hq, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_inv_distrib]
    ring
  · ring

end GlobalTheory.HilbFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeMellinGaussIntegralNonzeroInteger
section
noncomputable section

open NumberField MeasureTheory

namespace GlobalTheory.HeckeMellinOne

theorem hmon_eq_mul (n : ℤ) {z : ℂ} (hz : z ≠ 0) :
    GlobalTheory.HeckeTheta.hmon n z = ((‖z‖ : ℝ) : ℂ) ^ n.natAbs * (z / ((‖z‖ : ℝ) : ℂ)) ^ (-n) := by
  have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
  have hc : starRingEnd ℂ z * z = ((‖z‖ : ℝ) : ℂ) ^ 2 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  unfold GlobalTheory.HeckeTheta.hmon
  split_ifs with h
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    simp only [Int.toNat_natCast, Int.natAbs_natCast, zpow_neg, zpow_natCast]
    rw [← inv_pow, ← mul_pow]
    congr 1
    field_simp
    linear_combination hc
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, -n = m := ⟨(-n).toNat, by omega⟩
    have hm' : n.natAbs = m := by omega
    rw [hm, hm', Int.toNat_natCast, zpow_natCast, ← mul_pow]
    congr 1
    field_simp

theorem ofReal_prod_cpow {J : Type} (t : Finset J) (f : J → ℝ) (hf : ∀ j, 0 ≤ f j) (w : ℂ) :
    (((∏ j ∈ t, f j : ℝ)) : ℂ) ^ w = ∏ j ∈ t, ((f j : ℝ) : ℂ) ^ w := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf a) (Finset.prod_nonneg fun j _ => hf j), ih]

theorem real_factor (r σ a G : ℝ) (k : ℕ) (hr : 0 < r) (hk : (k : ℝ) = a) :
    r ^ k * G * (2 * Real.pi * r ^ 2) ^ (-(σ + a / 2)) =
      (2 * Real.pi) ^ (-(σ + a / 2)) * G * (r ^ 2) ^ (-σ) := by
  subst hk
  have h2π : 0 < 2 * Real.pi := by positivity
  rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos h2π, Real.rpow_def_of_pos (by positivity),
    Real.log_mul h2π.ne' (by positivity), Real.log_pow, ← Real.exp_log (pow_pos hr k), Real.log_pow]
  have key : Real.exp (k * Real.log r) * Real.exp ((Real.log (2 * Real.pi) + (2 : ℕ) * Real.log r) * -(σ + k / 2)) =
      Real.exp (Real.log (2 * Real.pi) * -(σ + k / 2)) * Real.exp ((2 : ℕ) * Real.log r * -σ) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; push_cast; ring
  linear_combination G * key

theorem complex_factor (z : ℂ) (hz : z ≠ 0) (n : ℤ) (s G : ℂ) :
    2 * (GlobalTheory.HeckeTheta.hmon n z * G *
      ((2 * Real.pi * ‖z‖ ^ 2 : ℝ) : ℂ) ^ (-(s + ((|n| : ℤ) : ℂ) / 2))) =
      2 * (2 * (Real.pi : ℂ)) ^ (-(s + ((|n| : ℤ) : ℂ) / 2)) * G *
        ((z / ((‖z‖ : ℝ) : ℂ)) ^ (-n) * ((‖z‖ ^ 2 : ℝ) : ℂ) ^ (-s)) := by
  have hr : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h2π : 0 < 2 * Real.pi := by positivity
  have e2 : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  have hk : ((n.natAbs : ℕ) : ℂ) = ((|n| : ℤ) : ℂ) := by
    rw [← Int.cast_natCast, Int.natCast_natAbs]
  rw [hmon_eq_mul n hz, e2, ← Complex.cpow_natCast,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (by positivity : (0:ℝ) < 2 * Real.pi * ‖z‖ ^ 2).ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast h2π.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (by positivity : (0:ℝ) < ‖z‖ ^ 2).ne'),
    ← Complex.ofReal_log hr.le, ← Complex.ofReal_log (by positivity), ← Complex.ofReal_log h2π.le,
    ← Complex.ofReal_log (by positivity), Real.log_mul h2π.ne' (by positivity), Real.log_pow, hk]
  have key : Complex.exp (((Real.log ‖z‖ : ℝ) : ℂ) * ((|n| : ℤ) : ℂ)) *
      Complex.exp (((Real.log (2 * Real.pi) + (2 : ℕ) * Real.log ‖z‖ : ℝ) : ℂ) * -(s + ((|n| : ℤ) : ℂ) / 2)) =
      Complex.exp (((Real.log (2 * Real.pi) : ℝ) : ℂ) * -(s + ((|n| : ℤ) : ℂ) / 2)) *
      Complex.exp ((((2 : ℕ) * Real.log ‖z‖ : ℝ) : ℂ) * -s) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
  linear_combination (2 * (z / ((‖z‖ : ℝ) : ℂ)) ^ (-n) * G) * key

end GlobalTheory.HeckeMellinOne

namespace GlobalTheory.HeckeMellinOne

theorem real_prod_rpow {J : Type} (t : Finset J) (f : J → ℝ) (hf : ∀ j, 0 ≤ f j) (w : ℝ) :
    (∏ j ∈ t, f j) ^ w = ∏ j ∈ t, f j ^ w := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      Real.mul_rpow (hf a) (Finset.prod_nonneg fun j _ => hf j), ih]

theorem mellin_term : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ) (s : ℂ), 0 < s.re → ∀ α : 𝓞 K, α ≠ 0 → Integrable (GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (α : K))) ∧ 2 ^ Fintype.card I * ∫ y, GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (α : K)) y = GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor n s * GlobalTheory.HeckeStrip.wt φ n (α : K) * ((Ideal.absNorm (Ideal.span {α}) : ℕ) : ℂ) ^ (-s) ∧ ∫ y, ‖GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (α : K)) y‖ = (∏ i, (2 * Real.pi) ^ (-(s.re + (|n i| : ℝ) / 2)) * Real.Gamma (s.re + (|n i| : ℝ) / 2)) * ((Ideal.absNorm (Ideal.span {α}) : ℕ) : ℝ) ^ (-s.re) := by
  intro K _ _ _ I _ φ hφ n s hs α hα
  have hαK : (α : K) ≠ 0 := by exact_mod_cast hα
  have hv : ∀ i, GlobalTheory.HeckeTheta.emb φ (α : K) i ≠ 0 := fun i => (map_ne_zero (φ i)).2 hαK
  obtain ⟨hint, hI, hN⟩ := _root_.GlobalTheory.HeckeMellinProd.mellin_prod I n s hs _ hv
  have hnorm := _root_.GlobalTheory.CMTypeNorm.prod_norm_sq_eq_absNorm K I φ hφ α
  refine ⟨hint, ?_, ?_⟩
  · rw [hI, ← Complex.ofReal_natCast, ← hnorm, ofReal_prod_cpow _ _ (fun i => by positivity),
      ← Finset.card_univ, Finset.pow_card_mul_prod]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor GlobalTheory.HeckeStrip.wt
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [complex_factor _ (hv i)]
    simp only [GlobalTheory.HeckeTheta.emb]
    ring
  · rw [hN, ← hnorm, real_prod_rpow _ _ (fun i => by positivity), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    exact real_factor _ _ _ _ _ (norm_pos_iff.2 (hv i)) (by rw [Nat.cast_natAbs, Int.cast_abs])

end GlobalTheory.HeckeMellinOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInCharacterIsotypicPartIffConvolution
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

noncomputable section

namespace GlobalTheory.Shin

theorem isChar_conj_eq {G : Type} [Group G] {Y : G → ℂ} (hY : IsChar ℂ ℂ Y) (g z : G) :
    Y (z * g * z⁻¹) = Y g := by
  obtain ⟨n, ρ, h⟩ := hY
  rw [h, h, Representation.char_conj]

theorem conv_op_eq {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (Y h : G → ℂ) :
    ∑ x, star (∑ y, Y y * h (y⁻¹ * x)) • ρ x =
      (∑ y, star (Y y) • ρ y) * (∑ z, star (h z) • ρ z) := by
  rw [Finset.sum_mul_sum]
  simp_rw [star_sum, star_mul', Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Equiv.sum_comp (Equiv.mulLeft y)]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp [map_mul, smul_mul_smul_comm, smul_smul, mul_comm]

def convL {G : Type} [Group G] [Fintype G] (Y : G → ℂ) : (G → ℂ) →ₗ[ℂ] (G → ℂ) :=
  ∑ g, star (Y g) • LinearMap.funLeft ℂ ℂ (fun z => g * z)

theorem convL_apply {G : Type} [Group G] [Fintype G] (Y : G → ℂ) (a : G → ℂ) (z : G) :
    convL Y a z = ∑ g, star (Y g) * a (g * z) := by
  simp [convL, LinearMap.funLeft, Finset.sum_apply]

def regKer {G : Type} [Group G] [Fintype G] (Y : G → ℂ) :
    Representation ℂ G (LinearMap.ker (convL Y)) where
  toFun g := (LinearMap.funLeft ℂ ℂ (fun z => z * g)).restrict (p := LinearMap.ker (convL Y))
      (q := LinearMap.ker (convL Y)) (by
        intro a ha
        rw [LinearMap.mem_ker] at ha ⊢
        funext z
        have := congrFun ha (z * g)
        simp only [convL_apply, Pi.zero_apply] at this ⊢
        simpa [LinearMap.funLeft, mul_assoc] using this)
  map_one' := by ext a z; simp [LinearMap.funLeft]
  map_mul' g h := by ext a z; simp [LinearMap.funLeft, mul_assoc]

theorem regKer_apply {G : Type} [Group G] [Fintype G] (Y : G → ℂ) (g : G) (a : LinearMap.ker (convL Y))
    (z : G) : ((regKer Y g a : LinearMap.ker (convL Y)) : G → ℂ) z = (a : G → ℂ) (z * g) := rfl

theorem kills_iff_conv : ∀ (G : Type) [Group G] [Finite G] (φ Y : G → ℂ), IsChar ℂ ℂ Y →
    (Kills φ Y ↔ ∃ h : G → ℂ, ∀ x, φ x = ∑ᶠ y, Y y * h (y⁻¹ * x)) := by
  intro G _ _ φ Y hY
  have := Fintype.ofFinite G
  constructor
  · intro hK
    set K := LinearMap.ker (convL Y)

    have hT : ∑ g, star (Y g) • regKer Y g = 0 := by
      ext a z
      have ha := congrFun (LinearMap.mem_ker.1 a.2) z
      rw [convL_apply, Pi.zero_apply] at ha
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
        Finset.sum_apply, Pi.smul_apply, regKer_apply, smul_eq_mul, LinearMap.zero_apply,
        Submodule.coe_zero, Pi.zero_apply]
      rw [← ha, ← Equiv.sum_comp (MulAut.conj z⁻¹).toEquiv]
      refine Finset.sum_congr rfl fun g _ => ?_
      have hc := isChar_conj_eq hY g z⁻¹
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, inv_inv] at hc ⊢
      rw [hc]
      congr 2
      group
    have hK' := hK K (regKer Y) (by
      rw [finsum_eq_sum_of_fintype]
      have := congrArg (LinearMap.trace ℂ K) hT
      set_option synthInstance.maxHeartbeats 100000 in
        simpa [map_sum, smul_eq_mul] using this)
    rw [finsum_eq_sum_of_fintype] at hK'

    let ℓ : Module.Dual ℂ (G → ℂ) := ∑ x, star (φ x) • (LinearMap.proj x : (G → ℂ) →ₗ[ℂ] ℂ)
    have hℓ : ∀ a, ℓ a = ∑ x, star (φ x) * a x := fun a => by simp [ℓ]
    have hmem : ℓ ∈ K.dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro a ha
      have := congrFun (congrArg Subtype.val (LinearMap.congr_fun hK' ⟨a, ha⟩)) 1
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, Submodule.coe_sum, Submodule.coe_smul,
        Finset.sum_apply, Pi.smul_apply, regKer_apply, smul_eq_mul, LinearMap.zero_apply,
        Submodule.coe_zero, Pi.zero_apply] at this
      have e : ∀ x, ((regKer Y x ⟨a, ha⟩ : LinearMap.ker (convL Y)) : G → ℂ) 1 = a x := fun x => by
        show a (1 * x) = a x
        rw [one_mul]
      simp only [e] at this
      rw [hℓ, this]
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hmem
    obtain ⟨μ, hμ⟩ := hmem
    refine ⟨fun w => star (μ (Pi.single w 1)), fun x => ?_⟩
    have hδ : convL Y (Pi.single x 1) = ∑ g, star (Y g) • Pi.single (g⁻¹ * x) 1 := by
      funext z
      rw [convL_apply, Finset.sum_apply]
      refine Finset.sum_congr rfl fun g _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      congr 1
      simp only [Pi.single_apply, eq_inv_mul_iff_mul_eq]
    have h1 := LinearMap.congr_fun hμ (Pi.single x 1)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearMap.dualMap_apply, hδ, map_sum, hℓ] at h1
    simp only [map_smul, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    rw [finsum_eq_sum_of_fintype]
    have h2 := congrArg star h1
    simp only [star_sum, star_mul', star_star] at h2
    rw [← h2]
  · rintro ⟨h, hφ⟩ V _ _ _ ρ hV
    have hY0 := GlobalTheory.T.isInCharacterIsotypicPart_self G Y hY V ρ hV
    rw [finsum_eq_sum_of_fintype] at hY0 ⊢
    simp_rw [hφ, finsum_eq_sum_of_fintype]
    rw [conv_op_eq, hY0, zero_mul]

end GlobalTheory.Shin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JointShapeUniqueAndDegWEq
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.JointShapeUniq

theorem length_pad {x y : List ℤ} {n : ℕ} (h : x.length + y.length ≤ n) :
    (pad x (n - x.length - y.length) y).length = n := by
  simp [pad]; omega

theorem ofFn_getD {L : List ℚ} {n : ℕ} (h : L.length = n) :
    List.ofFn (fun i : Fin n => L.getD i 0) = L := by
  subst h
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp [List.getElem?_eq_getElem h2]

theorem filter_pos {x y : List ℤ} (hx : ∀ v ∈ x, 0 < v) (hy : ∀ v ∈ y, v < 0) (k : ℕ) :
    (x ++ List.replicate k 0 ++ y).filter (fun v => decide (0 < v)) = x := by
  rw [List.filter_append, List.filter_append, List.filter_eq_self.2 (by simpa using hx),
    List.filter_eq_nil_iff.2 (by simp),
    List.filter_eq_nil_iff.2 (fun v hv => by have := hy v hv; simp; omega)]
  simp

theorem filter_neg {x y : List ℤ} (hx : ∀ v ∈ x, 0 < v) (hy : ∀ v ∈ y, v < 0) (k : ℕ) :
    (x ++ List.replicate k 0 ++ y).filter (fun v => decide (v < 0)) = y := by
  rw [List.filter_append, List.filter_append,
    List.filter_eq_nil_iff.2 (fun v hv => by have := hx v hv; simp; omega),
    List.filter_eq_nil_iff.2 (by simp), List.filter_eq_self.2 (by simpa using hy)]
  simp

theorem pad_inj {x y x' y' : List ℤ} (hx : ∀ v ∈ x, 0 < v) (hy : ∀ v ∈ y, v < 0)
    (hx' : ∀ v ∈ x', 0 < v) (hy' : ∀ v ∈ y', v < 0) {n : ℕ}
    (h : x.length + y.length ≤ n) (h' : x'.length + y'.length ≤ n)
    (e : ∀ i : Fin n, (pad x (n - x.length - y.length) y).getD i 0 =
      (pad x' (n - x'.length - y'.length) y').getD i 0) : x = x' ∧ y = y' := by
  have e1 : pad x (n - x.length - y.length) y = pad x' (n - x'.length - y'.length) y' := by
    rw [← ofFn_getD (length_pad h), ← ofFn_getD (length_pad h'), funext e]
  have e2 := List.map_injective_iff.2 (Int.cast_injective (α := ℚ)) e1
  exact ⟨by rw [← filter_pos hx hy, e2, filter_pos hx' hy'],
    by rw [← filter_neg hx hy, e2, filter_neg hx' hy']⟩

def absSum (x : List ℤ) : ℚ := (x.map fun v : ℤ => |(v : ℚ)|).sum

theorem sum_abs_pad {x y : List ℤ} {n : ℕ} (h : x.length + y.length ≤ n) :
    ∑ i : Fin n, |(pad x (n - x.length - y.length) y).getD i 0| = absSum x + absSum y := by
  have : ∑ i : Fin n, |(pad x (n - x.length - y.length) y).getD i 0| =
      ((pad x (n - x.length - y.length) y).map fun v => |v|).sum := by
    conv_rhs => rw [← ofFn_getD (length_pad h), List.map_ofFn, List.sum_ofFn]
    rfl
  rw [this]
  simp [pad, absSum, Function.comp_def]

theorem shiftNu_injective {p q : ℕ} (c : ℚ) :
    Function.Injective (shiftNu (p := p) (q := q) c) := by
  intro μ μ₁ h
  funext a
  have := congrFun h a
  rcases a with a | a <;> simpa [shiftNu] using this

theorem jointShape_unique_deg : ∀ (p q r s : ℕ) (μ μ₁ : Ix p q → ℚ) (μ' μ₁' : Ix r s → ℚ),
    JointShape p q r s μ μ' → JointShape p q r s μ₁ μ₁' →
      (μ = μ₁ ↔ μ' = μ₁') ∧ degW (cPair r s) μ = degW (cPair p q) μ' := by
  intro p q r s μ μ₁ μ' μ₁' h h₁
  obtain ⟨a, b, c, d, ha, hc, hb, hd, -, -, -, -, l1, l2, l3, l4, e1, e2⟩ := h
  obtain ⟨a', b', c', d', ha', hc', hb', hd', -, -, -, -, l1', l2', l3', l4', e1', e2'⟩ := h₁
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ?_⟩
  · subst h
    have e := e1.symm.trans e1'
    obtain ⟨rfl, rfl⟩ := pad_inj ha hb ha' hb' l1 l1' fun i => congrFun e (.inl i)
    obtain ⟨rfl, rfl⟩ := pad_inj hc hd hc' hd' l2 l2' fun i => congrFun e (.inr i)
    exact shiftNu_injective _ (e2.trans e2'.symm)
  · subst h
    have e := e2.symm.trans e2'
    obtain ⟨rfl, rfl⟩ := pad_inj ha hd ha' hd' l3 l3' fun i => congrFun e (.inl i)
    obtain ⟨rfl, rfl⟩ := pad_inj hc hb hc' hb' l4 l4' fun i => congrFun e (.inr i)
    exact shiftNu_injective _ (e1.trans e1'.symm)
  · simp only [degW, e1, e2, Fintype.sum_sum_type, ofBlocks]
    rw [sum_abs_pad l1, sum_abs_pad l2, sum_abs_pad l3, sum_abs_pad l4]
    ring

end GlobalTheory.JointShapeUniq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerReductionChernDefectEqOfPowEq
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedChern

theorem defect_mul_prim (Q q : ℕ) [NeZero Q] (hqQ : q ∣ Q) (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤))
    (v w : (Γ(U, ⊤))ˣ) (h : (w : Γ(U, ⊤)) = ζ.1 * v) : defect Q q U w = defect Q q U v := by
  have hq0 : q ≠ 0 := fun h0 => NeZero.ne Q (Nat.eq_zero_of_zero_dvd (h0 ▸ hqQ))
  haveI : NeZero q := ⟨hq0⟩
  obtain ⟨ξ, hξ⟩ := (GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties Q Γ(U, ⊤)).2.2.2.2.2 q hqQ ζ
  have h1 : kumT Q U w = kumT Q U v + resGen 1 ζ := (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting Q).2 U ζ v w h
  have h2 : (redMap Q q 1).app U 0 (resGen 1 ζ) = resGen 1 ξ := GlobalTheory.T.tateTwistReductionResolutionMap_generator Q q hqQ 1 U ζ ξ hξ
  have h3 : ((w ^ (Q / q) : (Γ(U, ⊤))ˣ) : Γ(U, ⊤)) = ξ.1 * ((v ^ (Q / q) : (Γ(U, ⊤))ˣ) : Γ(U, ⊤)) := by
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, h, hξ, mul_pow]
  have h4 : kumT q U (w ^ (Q / q)) = kumT q U (v ^ (Q / q)) + resGen 1 ξ :=
    (GlobalTheory.T.isKummerTorsorSplitting_kummerTorsorSplitting q).2 U ξ _ _ h3
  unfold defect
  rw [h1, h4, map_add (f := _), h2]
  abel

theorem defect_mul_prim_pow (Q q : ℕ) [NeZero Q] (hqQ : q ∣ Q) (U : Scheme.{0}) (ζ : Prim Q Γ(U, ⊤))
    (v : (Γ(U, ⊤))ˣ) (a : ℕ) : ∀ w : (Γ(U, ⊤))ˣ, (w : Γ(U, ⊤)) = ζ.1 ^ a * v →
      defect Q q U w = defect Q q U v := by
  have hζ : IsUnit ζ.1 := IsUnit.of_pow_eq_one ((GlobalTheory.T.primitiveRoot_pow_unit_sub_prod_properties Q Γ(U, ⊤)).1 ζ) (NeZero.ne Q)
  induction a with
  | zero =>
    intro w hw
    rw [pow_zero, one_mul] at hw
    exact congrArg (defect Q q U) (Units.ext hw)
  | succ a ih =>
    intro w hw
    have e : ((hζ.unit ^ a * v : (Γ(U, ⊤))ˣ) : Γ(U, ⊤)) = ζ.1 ^ a * v := by simp
    rw [defect_mul_prim Q q hqQ U ζ (hζ.unit ^ a * v) w (by rw [hw, e, pow_succ]; ring)]
    exact ih _ e

end GlobalTheory.EtC.RedChern

namespace GlobalTheory.EtC.RedChern

theorem defect_eq_of_pow_eq (Q q : ℕ) [NeZero Q] (hqQ : q ∣ Q) (U : Scheme.{0}) (v w : (Γ(U, ⊤))ˣ)
    (hQ : IsUnit (Q : Γ(U, ⊤))) (hvw : v ^ Q = w ^ Q) : defect Q q U v = defect Q q U w := by
  refine (_root_.GlobalTheory.EtC.sec_ext_glue (ZMod q) ((res _ (tw q 1)).X 0) U).1 _ _ ?_
  refine loc_bind ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q U).1 hQ) fun V g hV => ?_
  obtain ⟨ζ⟩ := hV
  set v' : (Γ(V, ⊤))ˣ := Units.map g.appTop.hom.toMonoidHom v
  set w' : (Γ(V, ⊤))ˣ := Units.map g.appTop.hom.toMonoidHom w
  have hx : (((w' * v'⁻¹ : (Γ(V, ⊤))ˣ) : Γ(V, ⊤))) ^ Q = 1 := by
    rw [← Units.val_pow_eq_pow_val, mul_pow, inv_pow, ← map_pow, ← map_pow, ← hvw, mul_inv_cancel, Units.val_one]
  refine loc_mono ((GlobalTheory.T.etaleLocal_primitiveRoot_and_roots_of_unity Q V).2.2.1 ζ _ hx) fun W k ⟨a, ha⟩ => ?_
  rw [GlobalTheory.T.kummerReductionChernDefect_restriction Q q hqQ W U (k ≫ g) v hQ, GlobalTheory.T.kummerReductionChernDefect_restriction Q q hqQ W U (k ≫ g) w hQ]
  symm
  refine defect_mul_prim_pow Q q hqQ W (ζ.map k.appTop.hom) _ a _ ?_
  have e1 : ∀ u : (Γ(U, ⊤))ˣ, ((Units.map (k ≫ g).appTop.hom.toMonoidHom u : (Γ(W, ⊤))ˣ) : Γ(W, ⊤)) =
      k.appTop.hom ((Units.map g.appTop.hom.toMonoidHom u : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) := fun u => rfl
  rw [e1, e1]
  change k.appTop.hom (w' : Γ(V, ⊤)) = (k.appTop.hom ζ.1) ^ a * k.appTop.hom (v' : Γ(V, ⊤))
  rw [← ha, ← map_mul, Units.val_mul, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

end GlobalTheory.EtC.RedChern
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ObjMapCompBis
section
noncomputable section

namespace GlobalTheory.UPel.HT.ObjMapComp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' S'' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {s'' : S'' ⟶ Sp R}
  {o : Obj b N s} {o' : Obj b N s'} {o'' : Obj b N s''} {f : S' ⟶ S} {g : S'' ⟶ S'}

def comp (m₁ : ObjMap o'' o' g) (m₂ : ObjMap o' o f) : ObjMap o'' o (g ≫ f) where
  φ := m₁.φ ≫ m₂.φ
  φ₂ := m₁.φ₂ ≫ m₂.φ₂
  cart := IsGrpPullback.comp m₁.cart m₂.cart
  sq := ⟨by rw [Category.assoc, m₂.sq.1, ← Category.assoc, m₁.sq.1, Category.assoc],
         by rw [Category.assoc, m₂.sq.2, ← Category.assoc, m₁.sq.2, Category.assoc]⟩
  act c := by rw [← Category.assoc, m₁.act, Category.assoc, m₂.act, Category.assoc]
  pol := LBIso.trans o''.isLB (pull_isLB o'.isLB m₁.φ₂) (pull_isLB o.isLB _) m₁.pol
    (LBIso.chartPull (chartPullPull o'.P m₁.φ₂ m₁.φ₂ rfl)
      (chartPullSame o.P (fun _ : PUnit => m₁.φ₂ ≫ m₂.φ₂) (fun _ => m₂.φ₂) (fun _ => 1) m₁.φ₂ (fun _ => rfl))
      m₂.pol)
  eta y := by rw [← Category.assoc, m₁.eta, Category.assoc, m₂.eta, Category.assoc]

end GlobalTheory.UPel.HT.ObjMapComp
end
end

