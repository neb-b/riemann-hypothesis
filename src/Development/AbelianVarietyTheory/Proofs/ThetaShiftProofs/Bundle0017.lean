module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.BoundedOnFramesIffIntegralOnFrames
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLetterRingOverDVRPolynomialDenominators
section
noncomputable section

namespace GlobalTheory.LetterDenom

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

section General

variable {σ R L : Type*} [CommRing R] [CommRing L]

theorem exists_map_eq_of_constantCoeff (φ : R →+* L) (A G : MvPolynomial σ R) (P : MvPolynomial σ L)
    (hA : MvPolynomial.constantCoeff A = 1)
    (h : MvPolynomial.map φ A * P = MvPolynomial.map φ G) : ∃ Q, MvPolynomial.map φ Q = P := by
  classical
  have hcoe : ∀ B : MvPolynomial σ R, ((MvPolynomial.map φ B : MvPolynomial σ L) : MvPowerSeries σ L) =
      MvPowerSeries.map φ (B : MvPowerSeries σ R) := by
    intro B
    ext m
    simp [MvPolynomial.coeff_map]
  have hu : (A : MvPowerSeries σ R) * MvPowerSeries.invOfUnit (A : MvPowerSeries σ R) 1 = 1 := by
    apply MvPowerSeries.mul_invOfUnit
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPolynomial.coeff_coe]
    simpa [MvPolynomial.constantCoeff_eq] using hA
  have hP : (P : MvPowerSeries σ L) =
      MvPowerSeries.map φ (MvPowerSeries.invOfUnit (A : MvPowerSeries σ R) 1 * (G : MvPowerSeries σ R)) := by
    rw [map_mul, ← hcoe G, ← h, MvPolynomial.coe_mul, hcoe A, ← mul_assoc, ← map_mul, mul_comm _ (A : MvPowerSeries σ R), hu,
      map_one, one_mul]
  have hc : ∀ m, ∃ r, φ r = P.coeff m := by
    intro m
    rw [← MvPolynomial.coeff_coe, hP, MvPowerSeries.coeff_map]
    exact ⟨_, rfl⟩
  choose r hr using hc
  refine ⟨∑ m ∈ P.support, MvPolynomial.monomial m (r m), ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  conv_rhs => rw [P.as_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.map_monomial, hr]

theorem exists_map_eq_of_eval (φ : R →+* L) (a : σ → R) (A G : MvPolynomial σ R) (P : MvPolynomial σ L)
    (hA : MvPolynomial.eval a A = 1)
    (h : MvPolynomial.map φ A * P = MvPolynomial.map φ G) : ∃ Q, MvPolynomial.map φ Q = P := by
  let s : σ → MvPolynomial σ R := fun x => MvPolynomial.X x + MvPolynomial.C (a x)
  let t : σ → MvPolynomial σ R := fun x => MvPolynomial.X x - MvPolynomial.C (a x)
  have h1 : MvPolynomial.constantCoeff (MvPolynomial.bind₁ s A) = 1 := by
    rw [← hA]
    have : (MvPolynomial.constantCoeff : MvPolynomial σ R →+* R).comp (MvPolynomial.bind₁ s).toRingHom =
        MvPolynomial.eval a := by
      apply MvPolynomial.ringHom_ext
      · intro r; simp
      · intro x; simp [s]
    exact RingHom.congr_fun this A
  have h2 := congrArg (MvPolynomial.bind₁ fun x => MvPolynomial.map φ (s x)) h
  rw [map_mul, ← MvPolynomial.map_bind₁, ← MvPolynomial.map_bind₁] at h2
  obtain ⟨Q, hQ⟩ := exists_map_eq_of_constantCoeff φ _ _ _ h1 h2
  refine ⟨MvPolynomial.bind₁ t Q, ?_⟩
  rw [MvPolynomial.map_bind₁, hQ, MvPolynomial.bind₁_bind₁]
  have : (fun x => MvPolynomial.bind₁ (fun i => MvPolynomial.map φ (t i)) (MvPolynomial.map φ (s x))) =
      MvPolynomial.X := by
    funext x
    simp [s, t]
  rw [this, MvPolynomial.bind₁_X_left]
  rfl

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem eval_arcDetR (Dw : Datum H) (V : Type) [CommRing V] :
    MvPolynomial.eval (fun x : ArcLt Dw => if x.2.1 = x.2.2 then (1 : PowerSeries V) else 0)
      (arcDetR Dw V) = 1 := by
  classical
  unfold arcDetR
  rw [map_prod]
  refine Finset.prod_eq_one fun τ _ => ?_
  rw [RingHom.map_det]
  convert Matrix.det_one (n := Fin (Dw.mult τ)) (R := PowerSeries V)
  ext i k : 2
  simp [Matrix.one_apply]

theorem map_arcDetR (Dw : Datum H) (V K : Type) [CommRing V] [Field K] (φ : PowerSeries V →+* LaurentSeries K) :
    MvPolynomial.map φ (arcDetR Dw V) = arcDet Dw K := by
  unfold arcDetR arcDet
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [RingHom.map_det]
  congr 1
  ext i k : 2
  simp

theorem arcDetR_ne_zero (Dw : Datum H) (V : Type) [CommRing V] [Nontrivial V] : arcDetR Dw V ≠ 0 := by
  intro h0
  have h1 := eval_arcDetR Dw V
  rw [h0, map_zero] at h1
  exact zero_ne_one h1

theorem den_ne_zero (Dw : Datum H) (V : Type) [CommRing V] [IsDomain V] {ϖ : V} (hϖ : ϖ ≠ 0) :
    MvPolynomial.C (PowerSeries.C ϖ * PowerSeries.X) * arcDetR Dw V ≠ 0 := by
  refine mul_ne_zero ?_ (arcDetR_ne_zero Dw V)
  rw [Ne, MvPolynomial.C_eq_zero]
  refine mul_ne_zero ?_ PowerSeries.X_ne_zero
  intro h
  exact hϖ (PowerSeries.C_injective (h.trans (map_zero _).symm))

section Parts

variable (Dw : Datum H) (V K : Type) [CommRing V] [IsDomain V] [Field K] {ϖ : V}

theorem isDomain_letter (hϖ : ϖ ≠ 0) : IsDomain (ArcSR Dw V ϖ) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors (den_ne_zero Dw V hϖ))

theorem algebraMap_letter_injective (hϖ : ϖ ≠ 0) :
    Function.Injective (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ)) :=
  IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors (den_ne_zero Dw V hϖ))

theorem flat_of_injective {A B : Type} [CommRing A] [IsDomain A] [IsBezout A] [CommRing B] [IsDomain B]
    (j : A →+* B) (hi : Function.Injective j) : j.Flat := by
  letI : Algebra A B := j.toAlgebra
  change Module.Flat A B
  rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
  rintro x ⟨⟨a, ha⟩, hx⟩
  have hx' : j a * x = 0 := hx
  have ha' : j a ≠ 0 := fun h => nonZeroDivisors.ne_zero ha (hi (h.trans (map_zero _).symm))
  exact (mul_eq_zero.mp hx').resolve_left ha'

theorem exists_lift (hϖ : ϖ ≠ 0) (φ : PowerSeries V →+* LaurentSeries K) (hφ : Function.Injective φ) :
    ∃ ψ : ArcSR Dw V ϖ →+* ArcS Dw K,
      ψ.comp (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ)) =
        (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) (ArcS Dw K)).comp (MvPolynomial.map φ) := by
  have hu : IsUnit (((algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) (ArcS Dw K)).comp
      (MvPolynomial.map φ)) (MvPolynomial.C (PowerSeries.C ϖ * PowerSeries.X) * arcDetR Dw V)) := by
    rw [map_mul]
    refine IsUnit.mul ?_ ?_
    · have hne : φ (PowerSeries.C ϖ * PowerSeries.X) ≠ 0 := by
        intro h
        apply den_ne_zero Dw V hϖ
        rw [hφ (h.trans (map_zero _).symm), map_zero, zero_mul]
      rw [RingHom.comp_apply, MvPolynomial.map_C]
      exact (hne.isUnit.map MvPolynomial.C).map _
    · rw [RingHom.comp_apply, map_arcDetR]
      exact IsLocalization.Away.algebraMap_isUnit _
  exact ⟨IsLocalization.Away.lift _ hu, IsLocalization.Away.lift_comp _ hu⟩

theorem denominators_gen {σ R L S S' : Type} [CommRing R] [CommRing L] [CommRing S] [CommRing S'] [IsDomain S]
    [Algebra (MvPolynomial σ R) S] (c Δ : MvPolynomial σ R) [IsLocalization.Away (c * Δ) S]
    (hinj : Function.Injective (algebraMap (MvPolynomial σ R) S))
    (j : MvPolynomial σ L →+* S') (hj : Function.Injective j) (a : σ → R) (ha : MvPolynomial.eval a Δ = 1)
    (φ : R →+* L) (hφ : Function.Injective φ) (ψ : S →+* S')
    (hψ : ∀ B, ψ (algebraMap (MvPolynomial σ R) S B) = j (MvPolynomial.map φ B))
    (f : S) (P : MvPolynomial σ L) (hP : j P = ψ f) :
    ∃ (N : ℕ) (G : MvPolynomial σ R), f * algebraMap (MvPolynomial σ R) S c ^ N = algebraMap _ S G := by
  obtain ⟨N, G₀, hf⟩ := IsLocalization.Away.surj (c * Δ) f
  have h3 := congrArg ψ hf
  rw [map_mul ψ, ← map_pow, ← hP, hψ, hψ, ← map_mul] at h3
  have h4 := hj h3
  have h5 : MvPolynomial.map φ (Δ ^ N) * (P * MvPolynomial.map φ (c ^ N)) = MvPolynomial.map φ G₀ := by
    rw [← h4, mul_pow, map_mul]; ring
  obtain ⟨Q, hQ⟩ := exists_map_eq_of_eval φ a _ _ _ (by rw [map_pow, ha, one_pow]) h5
  rw [← hQ, ← map_mul] at h5
  have h6 := MvPolynomial.map_injective φ hφ h5
  refine ⟨N, Q, ?_⟩
  have hu : IsUnit (algebraMap _ S (c * Δ)) := IsLocalization.Away.algebraMap_isUnit _
  rw [map_mul] at hu
  have hu' : IsUnit (algebraMap _ S (Δ ^ N)) := by
    rw [map_pow]
    exact (isUnit_of_mul_isUnit_right hu).pow N
  apply hu'.mul_left_cancel
  rw [← map_mul, h6, ← hf, map_mul, map_pow, mul_pow]
  ring

theorem denominators (hϖ : ϖ ≠ 0) (φ : PowerSeries V →+* LaurentSeries K) (hφ : Function.Injective φ)
    (ψ : ArcSR Dw V ϖ →+* ArcS Dw K)
    (hψ : ψ.comp (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ)) =
        (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) (ArcS Dw K)).comp (MvPolynomial.map φ))
    (f : ArcSR Dw V ϖ) (P : MvPolynomial (ArcLt Dw) (LaurentSeries K))
    (hP : algebraMap _ (ArcS Dw K) P = ψ f) :
    ∃ (N : ℕ) (G : MvPolynomial (ArcLt Dw) (PowerSeries V)),
      f * arcιR Dw V ϖ (PowerSeries.C (R := V) ϖ * PowerSeries.X) ^ N = algebraMap _ (ArcSR Dw V ϖ) G := by
  haveI := isDomain_letter Dw V hϖ
  have hinj := algebraMap_letter_injective Dw V hϖ
  have hD : arcDet Dw K ≠ 0 := by
    rw [← map_arcDetR Dw V K φ]
    exact fun h => arcDetR_ne_zero Dw V (MvPolynomial.map_injective φ hφ (h.trans (map_zero _).symm))
  have hinjL : Function.Injective (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) (ArcS Dw K)) :=
    IsLocalization.injective (M := Submonoid.powers (arcDet Dw K)) _
      (powers_le_nonZeroDivisors_of_noZeroDivisors hD)
  exact denominators_gen (MvPolynomial.C (PowerSeries.C ϖ * PowerSeries.X)) (arcDetR Dw V) hinj _ hinjL _
    (eval_arcDetR Dw V) φ hφ ψ (fun B => RingHom.congr_fun hψ B) f P hP

theorem comp_eq_of_letters (φ : PowerSeries V →+* PowerSeries K) (ψ : ArcSR Dw V ϖ →+* ArcS Dw K) :
    ψ.comp (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries V)) (ArcSR Dw V ϖ)) =
        (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) (ArcS Dw K)).comp
          (MvPolynomial.map ((HahnSeries.ofPowerSeries ℤ K).comp φ)) ↔
      ψ.comp (arcιR Dw V ϖ) = (arcι Dw K).comp φ ∧ ∀ x : ArcLt Dw, ψ (arcXR Dw V ϖ x) = arcX Dw K x.1 x.2.1 x.2.2 := by
  constructor
  · intro hψ
    refine ⟨RingHom.ext fun p => ?_, fun x => ?_⟩
    · have := RingHom.congr_fun hψ (MvPolynomial.C p)
      simp only [RingHom.comp_apply, MvPolynomial.map_C] at this
      simp only [RingHom.comp_apply, arcιR, arcι, this]
    · have := RingHom.congr_fun hψ (MvPolynomial.X x)
      simp only [RingHom.comp_apply, MvPolynomial.map_X] at this
      simp only [arcXR, arcX, this]
  · rintro ⟨h1, h2⟩
    apply MvPolynomial.ringHom_ext
    · intro p
      have := RingHom.congr_fun h1 p
      simp only [RingHom.comp_apply, arcιR, arcι] at this
      simp only [RingHom.comp_apply, MvPolynomial.map_C, this]
    · intro x
      have := h2 x
      simp only [arcXR, arcX] at this
      simp only [RingHom.comp_apply, MvPolynomial.map_X, this]

theorem flat_letter [IsBezout V] (hϖ : ϖ ≠ 0) : ((arcιR Dw V ϖ).comp (PowerSeries.C (R := V))).Flat := by
  haveI := isDomain_letter Dw V hϖ
  refine flat_of_injective _ ?_
  rw [arcιR, RingHom.coe_comp, RingHom.coe_comp]
  exact ((algebraMap_letter_injective Dw V hϖ).comp (MvPolynomial.C_injective _ _)).comp PowerSeries.C_injective

omit [IsDomain V] in
theorem toLaurent_injective (i : V →+* K) (hi : Function.Injective i) :
    Function.Injective ((HahnSeries.ofPowerSeries ℤ K).comp (PowerSeries.map i)) := by
  rw [RingHom.coe_comp]
  exact HahnSeries.ofPowerSeries_injective.comp (PowerSeries.map_injective _ hi)

end Parts

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Tv : CDVR) (ϖ : Tv.V), ϖ ≠ 0 → IsDomain (ArcSR Dw Tv.V ϖ) ∧ Function.Injective (algebraMap (MvPolynomial (ArcLt Dw) (PowerSeries Tv.V)) (ArcSR Dw Tv.V ϖ)) ∧ ((arcιR Dw Tv.V ϖ).comp (PowerSeries.C (R := Tv.V))).Flat ∧ (∃ ψ : ArcSR Dw Tv.V ϖ →+* ArcS Dw Tv.Fr, ψ.comp (arcιR Dw Tv.V ϖ) = (arcι Dw Tv.Fr).comp (PowerSeries.map (algebraMap Tv.V Tv.Fr)) ∧ ∀ x : ArcLt Dw, ψ (arcXR Dw Tv.V ϖ x) = arcX Dw Tv.Fr x.1 x.2.1 x.2.2) ∧ ∀ ψ : ArcSR Dw Tv.V ϖ →+* ArcS Dw Tv.Fr, ψ.comp (arcιR Dw Tv.V ϖ) = (arcι Dw Tv.Fr).comp (PowerSeries.map (algebraMap Tv.V Tv.Fr)) → (∀ x : ArcLt Dw, ψ (arcXR Dw Tv.V ϖ x) = arcX Dw Tv.Fr x.1 x.2.1 x.2.2) → ∀ f : ArcSR Dw Tv.V ϖ, (∃ P : MvPolynomial (ArcLt Dw) (LaurentSeries Tv.Fr), algebraMap _ (ArcS Dw Tv.Fr) P = ψ f) → ∃ (N : ℕ) (G : MvPolynomial (ArcLt Dw) (PowerSeries Tv.V)), f * arcιR Dw Tv.V ϖ (PowerSeries.C (R := Tv.V) ϖ * PowerSeries.X) ^ N = algebraMap _ (ArcSR Dw Tv.V ϖ) G := by
  intro E _ _ _ H Dw Tv ϖ hϖ
  have hφ := toLaurent_injective Tv.V Tv.Fr (algebraMap Tv.V Tv.Fr) (IsFractionRing.injective Tv.V Tv.Fr)
  refine ⟨isDomain_letter Dw Tv.V hϖ, algebraMap_letter_injective Dw Tv.V hϖ, flat_letter Dw Tv.V hϖ, ?_, ?_⟩
  · obtain ⟨ψ, hψ⟩ := exists_lift Dw Tv.V Tv.Fr hϖ _ hφ
    exact ⟨ψ, (comp_eq_of_letters Dw Tv.V Tv.Fr _ ψ).1 hψ⟩
  · rintro ψ h1 h2 f ⟨P, hP⟩
    exact denominators Dw Tv.V Tv.Fr hϖ _ hφ ψ ((comp_eq_of_letters Dw Tv.V Tv.Fr _ ψ).2 ⟨h1, h2⟩) f P hP

end GlobalTheory.LetterDenom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.DegenerationDataBaseChangesExistPidStatement
section
alias GlobalTheory.T.degenerationData_baseChanges_exist_pid := GlobalTheory.ArcQBC.baseChanges
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsEvalArcLetterRingOverDVRDisc
section
namespace GlobalTheory.LetterEval

open GlobalTheory.DiscEval

section General

variable {K : Type} [NormedField K] [CompleteSpace K] {V F : Type} [CommRing V] [Field F]
  (a : V →+* F) (ι : F →+* K) (hi : ∀ v, ‖(ι.comp a) v‖ ≤ 1) {ϖ : V} (hϖ : a ϖ ≠ 0)
  {t : K} (ht0 : t ≠ 0) (ht : ‖t‖ < 1)


include hϖ ht0 in
theorem hasSum_laurent_of_mul_eq {q : LaurentSeries F} {g : PowerSeries V} {N : ℕ}
    (h : q * (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C (R := F) (a ϖ) * PowerSeries.X)) ^ N =
      HahnSeries.ofPowerSeries ℤ F (PowerSeries.map a g)) :
    HasSum (fun k : ℤ => ι (q.coeff k) * t ^ k)
      (((ι (a ϖ) * t) ^ N)⁻¹ * discEval (ι.comp a) hi ht g) := by
  have h2 : (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C (R := F) (a ϖ) * PowerSeries.X)) ^ N =
      HahnSeries.single (N : ℤ) (a ϖ ^ N) := by
    rw [← map_pow, mul_pow, ← map_pow PowerSeries.C, map_mul, HahnSeries.ofPowerSeries_C,
      HahnSeries.ofPowerSeries_X_pow, HahnSeries.C_apply, HahnSeries.single_mul_single]
    simp
  have h4 : a ϖ ^ N ≠ 0 := pow_ne_zero _ hϖ
  have hc : ∀ n : ℤ, q.coeff n = if n + N < 0 then 0 else
      (a ϖ ^ N)⁻¹ * a (PowerSeries.coeff (n + N).natAbs g) := fun n => by
    have h3 := congrArg (fun g : LaurentSeries F => g.coeff (n + N)) h
    simp only [h2, HahnSeries.coeff_mul_single_add] at h3
    rw [PowerSeries.coeff_coe, PowerSeries.coeff_map] at h3
    split_ifs at h3 ⊢
    · exact (mul_eq_zero.1 h3).resolve_right h4
    · rw [← h3]
      field_simp
  have hinj : Function.Injective fun k : ℕ => (k : ℤ) - N := fun k l hkl => by simpa using hkl
  rw [← hinj.hasSum_iff]
  · refine Eq.mpr (congrArg (HasSum · _) (funext fun k => ?_))
      ((hasSum_discEval (ι.comp a) hi ht g).mul_left (((ι (a ϖ) * t) ^ N)⁻¹))
    rw [Function.comp_apply, hc, sub_add_cancel, if_neg (by omega), Int.natAbs_natCast,
      zpow_sub₀ ht0, zpow_natCast, zpow_natCast, map_mul, map_inv₀, map_pow, RingHom.comp_apply,
      mul_pow, mul_inv]
    ring
  · intro n hn
    rw [hc, if_pos, map_zero, zero_mul]
    by_contra h0
    exact hn ⟨(n + N).toNat, by simp only; omega⟩


include hϖ ht0 in
theorem hasSum_lcoeffPoly {σ : Type} (Y : σ → K) {P : MvPolynomial σ (LaurentSeries F)}
    {G : MvPolynomial σ (PowerSeries V)} {N : ℕ}
    (h : P * MvPolynomial.C
        (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C (R := F) (a ϖ) * PowerSeries.X)) ^ N =
      MvPolynomial.map ((HahnSeries.ofPowerSeries ℤ F).comp (PowerSeries.map a)) G) :
    HasSum (fun k : ℤ => MvPolynomial.eval Y (MvPolynomial.map ι (GlobalTheory.ArcQ.lcoeffPoly P k)) * t ^ k)
      (((ι (a ϖ) * t) ^ N)⁻¹ * MvPolynomial.eval₂ (discEval (ι.comp a) hi ht) Y G) := by
  classical
  have hμ : ∀ μ, P.coeff μ *
      (HahnSeries.ofPowerSeries ℤ F (PowerSeries.C (R := F) (a ϖ) * PowerSeries.X)) ^ N =
      HahnSeries.ofPowerSeries ℤ F (PowerSeries.map a (G.coeff μ)) := fun μ => by
    have := congrArg (AddMonoidAlgebra.coeff · μ) h
    rwa [← map_pow, mul_comm, MvPolynomial.coeff_C_mul, mul_comm, MvPolynomial.coeff_map] at this
  set s := P.support ∪ G.support
  have hP : ∀ k : ℤ, GlobalTheory.ArcQ.lcoeffPoly P k =
      ∑ μ ∈ s, MvPolynomial.monomial μ ((P.coeff μ).coeff k) := fun k =>
    Finset.sum_subset Finset.subset_union_left fun μ _ hμ => by
      simp [MvPolynomial.notMem_support_iff.1 hμ]
  have hG : MvPolynomial.eval₂ (discEval (ι.comp a) hi ht) Y G =
      ∑ μ ∈ s, discEval (ι.comp a) hi ht (G.coeff μ) * ∏ k ∈ μ.support, Y k ^ μ k := by
    rw [MvPolynomial.eval₂_eq]
    exact Finset.sum_subset Finset.subset_union_right fun μ _ hμ => by
      simp [MvPolynomial.notMem_support_iff.1 hμ]
  rw [hG, Finset.mul_sum]
  simp_rw [← mul_assoc]
  refine Eq.mpr (congrArg (HasSum · _) (funext fun m => ?_))
    (hasSum_sum fun μ (_ : μ ∈ s) =>
      (hasSum_laurent_of_mul_eq a ι hi hϖ ht0 ht (hμ μ)).mul_right (∏ k ∈ μ.support, Y k ^ μ k))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hP, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MvPolynomial.map_monomial, MvPolynomial.eval_monomial, Finsupp.prod]
  ring

end General

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem exists_eval : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (Tv : CDVR) (ϖ : Tv.V) (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (ιT : Tv.Fr →+* K), ϖ ≠ 0 → (∀ v : Tv.V, ‖ιT (algebraMap Tv.V Tv.Fr v)‖ ≤ 1) → ∀ (t : K) (Y : ArcLt Dw → K), 0 < ‖t‖ → ‖t‖ < 1 → (∏ τ : E →+* ℂ, (Matrix.of fun i k : Fin (Dw.mult τ) => Y ⟨τ, i, k⟩).det) ≠ 0 → ∃ ev : ArcSR Dw Tv.V ϖ →+* K, (∀ p : PowerSeries Tv.V, ev (arcιR Dw Tv.V ϖ p) = ∑' k : ℕ, ιT (algebraMap Tv.V Tv.Fr (PowerSeries.coeff k p)) * t ^ k) ∧ (∀ x, ev (arcXR Dw Tv.V ϖ x) = Y x) ∧ ∀ (f : ArcSR Dw Tv.V ϖ) (N : ℕ) (G : MvPolynomial (ArcLt Dw) (PowerSeries Tv.V)) (P : MvPolynomial (ArcLt Dw) (LaurentSeries Tv.Fr)), f * arcιR Dw Tv.V ϖ (PowerSeries.C (R := Tv.V) ϖ * PowerSeries.X) ^ N = algebraMap _ (ArcSR Dw Tv.V ϖ) G → P * MvPolynomial.C (HahnSeries.ofPowerSeries ℤ Tv.Fr (PowerSeries.C (R := Tv.Fr) (algebraMap Tv.V Tv.Fr ϖ) * PowerSeries.X)) ^ N = MvPolynomial.map ((HahnSeries.ofPowerSeries ℤ Tv.Fr).comp (PowerSeries.map (algebraMap Tv.V Tv.Fr))) G → Filter.Tendsto (fun k : ℤ => ‖MvPolynomial.eval Y (MvPolynomial.map ιT (lcoeffPoly P k)) * t ^ k‖) Filter.cofinite (nhds 0) ∧ ev f = ∑' k : ℤ, MvPolynomial.eval Y (MvPolynomial.map ιT (lcoeffPoly P k)) * t ^ k := by
  intro E _ _ _ H Dw Tv ϖ K _ _ _ ιT hϖ hi t Y ht0 ht hY
  have ht0' : t ≠ 0 := norm_pos_iff.1 ht0
  have hϖ' : algebraMap Tv.V Tv.Fr ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective Tv.V Tv.Fr)).2 hϖ
  have hϖ'' : ιT (algebraMap Tv.V Tv.Fr ϖ) ≠ 0 := (map_ne_zero ιT).2 hϖ'
  have hi' : ∀ v, ‖(ιT.comp (algebraMap Tv.V Tv.Fr)) v‖ ≤ 1 := hi
  let g : MvPolynomial (ArcLt Dw) (PowerSeries Tv.V) →+* K :=
    MvPolynomial.eval₂Hom (discEval _ hi' ht) Y
  have hgC : ∀ p, g (MvPolynomial.C p) = discEval _ hi' ht p := fun p =>
    MvPolynomial.eval₂Hom_C _ _ _
  have hgX : ∀ x, g (MvPolynomial.X x) = Y x := fun x => MvPolynomial.eval₂Hom_X' _ _ _
  have hϖX : discEval _ hi' ht (PowerSeries.C (R := Tv.V) ϖ * PowerSeries.X) =
      ιT (algebraMap Tv.V Tv.Fr ϖ) * t := by
    rw [map_mul, discEval_C, discEval_X, RingHom.comp_apply]
  have hu : IsUnit (g (MvPolynomial.C (PowerSeries.C ϖ * PowerSeries.X) * arcDetR Dw Tv.V)) := by
    rw [isUnit_iff_ne_zero, map_mul, hgC, hϖX]
    refine mul_ne_zero (mul_ne_zero hϖ'' ht0') ?_
    convert hY using 1
    rw [arcDetR, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [RingHom.map_det]
    congr 1
    ext i k
    exact hgX _
  let ev : ArcSR Dw Tv.V ϖ →+* K := IsLocalization.Away.lift _ hu
  have hev : ∀ G, ev (algebraMap _ (ArcSR Dw Tv.V ϖ) G) = g G := fun G =>
    IsLocalization.Away.lift_eq _ hu G
  have hevι : ∀ p, ev (arcιR Dw Tv.V ϖ p) = discEval _ hi' ht p := fun p =>
    (hev _).trans (hgC p)
  refine ⟨ev, fun p => ?_, fun x => (hev _).trans (hgX x), fun f N G P hf hP => ?_⟩
  · rw [hevι, ← (hasSum_discEval _ hi' ht p).tsum_eq]
    rfl
  · have hs := hasSum_lcoeffPoly _ ιT hi' hϖ' ht0' ht Y hP
    refine ⟨by simpa using hs.summable.tendsto_cofinite_zero.norm, ?_⟩
    rw [hs.tsum_eq]
    have h1 := congrArg ev hf
    rw [map_mul, map_pow, hevι, hϖX, hev] at h1
    have h2 : (ιT (algebraMap Tv.V Tv.Fr ϖ) * t) ^ N ≠ 0 := pow_ne_zero _ (mul_ne_zero hϖ'' ht0')
    rw [eq_inv_mul_iff_mul_eq₀ h2, mul_comm]
    exact h1

end GlobalTheory.LetterEval
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramedPointEvalNaturalWeightScaling
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.ArcQ

theorem evR_frBor_of_isDomain {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (hL : GlobalTheory.Reg.EvLaws Xo c) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {F : Rul Xo c} (hF : F ∈ sec Xo c a n) {S : Type} [CommRing S] [Algebra c.F S] [IsDomain S]
    (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S) (h : FrBor t y y') :
    evR Xo c F y' = wchar (ex Dw a n) t * evR Xo c F y := by
  let φ : S →ₐ[c.F] FractionRing S := IsScalarTower.toAlgHom c.F S (FractionRing S)
  have hφ : Function.Injective φ := IsFractionRing.injective S (FractionRing S)
  obtain ⟨z, hz⟩ := hL.bc _ _ φ y
  obtain ⟨z', hz'⟩ := hL.bc _ _ φ y'
  obtain ⟨g, hg1, hg2, hg⟩ := ((_root_.GlobalTheory.Frames.frChg_calculus E H Dw l Xo c S).2.2.2 t y y').1 h
  have hc := ((_root_.GlobalTheory.Frames.frChg_calculus E H Dw l Xo c S).2.2.1 _ φ g _ y y' z z' hg hz).1 hz'
  let t' : Ix Dw → (FractionRing S)ˣ := fun i => Units.map (φ : S →* FractionRing S) (t i)
  have hb : FrBor t' z z' :=
    ((_root_.GlobalTheory.Frames.frChg_calculus E H Dw l Xo c (FractionRing S)).2.2.2 t' z z').2
      ⟨fun τ => (g τ).map φ, fun τ i => by simp [t', hg1], fun τ i j hij => by simp [hg2 τ i j hij], hc⟩
  have hw := hL.wt a n F hF _ t' z z' (hL.test _ _) (hL.test _ _) hb
  rw [GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n F hF S _ φ y z hz,
    GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n F hF S _ φ y' z' hz'] at hw
  apply hφ
  rw [hw, map_mul]
  congr 1
  simp [wchar, t']

theorem evR_natural_weight_scaling : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), GlobalTheory.Reg.EvLaws Xo c → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (F : Rul Xo c), F ∈ sec Xo c a n → ∀ (S : Type) [CommRing S] [Algebra c.F S] [IsReduced S], (∀ (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (y : FrPt Xo c S) (z : FrPt Xo c T), FrMap φ y z → evR Xo c F z = φ (evR Xo c F y)) ∧ (IsDomain S → (∀ (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' → evR Xo c F y' = wchar (ex Dw a n) t * evR Xo c F y) ∧ ∀ (s : S) (y y' : FrPt Xo c S), FrChg (fun _ => 1) s y y' → evR Xo c F y' = s ^ n * evR Xo c F y) := by
  intro E _ _ _ H Dw l Xo c hL a n F hF S _ _ _
  refine ⟨fun T _ _ φ y z h => GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hL a n F hF S T φ y z h,
    fun hD => ⟨fun t y y' h => evR_frBor_of_isDomain hL hF t y y' h, fun s y y' h => ?_⟩⟩
  obtain ⟨u, rfl⟩ := ((_root_.GlobalTheory.ArcQ.frChg_exists_unique_units E H Dw l Xo c S _ s y).2.2.1 y' h).2
  let t : Ix Dw → Sˣ := fun i => i.elim u fun _ => 1
  have hb : FrBor t y y' :=
    ((_root_.GlobalTheory.Frames.frChg_calculus E H Dw l Xo c S).2.2.2 t y y').2
      ⟨fun _ => 1, fun τ i => by simp [t], fun τ i j hij => Matrix.one_apply_ne hij.ne, h⟩
  rw [evR_frBor_of_isDomain hL hF t y y' hb]
  congr 1
  simp [wchar, t, ex, Fintype.prod_option]

end GlobalTheory.ArcQ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyUnifWitnessDataOfIsUnf
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.ArcQ

theorem nonempty_unfWit_of_isUnf : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), IsUnf U → Nonempty (UnfWit U) := by
  intro E _ _ _ H Dw l Xo c σ r U h
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, hiso, hP⟩ := h
  choose Pm h1 h2 h3 h4 h5 using hP
  exact ⟨⟨g, e, F, ik, φ, hiso, Pm, h1, h2, fun k x => ⟨h3 k x, h4 k x⟩, h5⟩⟩

end GlobalTheory.ArcQ
end

