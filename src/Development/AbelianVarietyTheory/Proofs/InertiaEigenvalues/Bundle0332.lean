module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0277
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0228
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0318
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfUnitBoundedTeichmullerFlatDenominators
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP.BddDen

variable {l : ℕ} [hl : Fact l.Prime]

abbrev redMap {K : FinExt l} (bk : BK K) : bk.S →+* (OC l ⧸ Ideal.span {((l : ℕ) : OC l)}) :=
  (Ideal.Quotient.mk _).comp ((Per.θ l).comp bk.ev)

theorem redMap_coe {K : FinExt l} (bk : BK K) (p : Polynomial (Wq l bk.a)) :
    redMap bk (p : bk.S) = p.eval₂ ((redMap bk).comp PowerSeries.C) (redMap bk X) := by
  have h : (redMap bk).comp (Polynomial.coeToPowerSeries.ringHom) =
      Polynomial.eval₂RingHom ((redMap bk).comp PowerSeries.C) (redMap bk X) :=
    Polynomial.ringHom_ext (fun a => by simp) (by simp)
  exact congrArg (fun f => f p) h

theorem redMap_E {K : FinExt l} (bk : BK K) : redMap bk bk.E = redMap bk X ^ bk.Ep.natDegree := by
  rw [BK.E, redMap_coe, Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, bk.monic.coeff_natDegree,
    map_one, one_mul, add_eq_right]
  refine Finset.sum_eq_zero fun i hi => ?_
  obtain ⟨c, hc⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
  have hl0 : ((l : ℕ) : OC l ⧸ Ideal.span {((l : ℕ) : OC l)}) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {((l : ℕ) : OC l)})), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  rw [RingHom.comp_apply, hc, map_mul, map_mul, map_natCast, map_natCast, hl0, zero_mul, zero_mul]

theorem flat_not_isUnit {K : FinExt l} (bk : BK K) : ¬ IsUnit bk.flat := by
  intro hu
  have h0 : redMap bk bk.E = 0 := by
    have hk : bk.ev bk.E ∈ RingHom.ker (Per.θ l) := bk.span_ev ▸ Ideal.mem_span_singleton_self _
    rw [RingHom.mem_ker] at hk
    simp only [redMap, RingHom.comp_apply, hk, map_zero]
  rw [redMap_E, redMap, RingHom.comp_apply, RingHom.comp_apply, ← map_pow, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton] at h0
  have hX : IsUnit (bk.ev X) := bk.ev_X ▸ hu.map (WittVector.teichmuller l)
  exact PI.ArtSch.OC_l_not_unit l (isUnit_of_dvd_unit h0 ((hX.map (Per.θ l)).pow _))

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (a : Ainf l), IsUnit (inclW l a) →
    ∀ n : ℕ, ∃ (m : ℕ) (t : Ainf l), (l : Ainf l) ^ n ∣ t * a - bk.ev X ^ m := by
  intro l _ K bk a ha n
  have ha0 : a.coeff 0 ≠ 0 := by
    intro h
    have h1 := ha.map (WittVector.constantCoeff (p := l) (R := Cb l))
    rw [WittVector.constantCoeff_apply, inclW, WittVector.map_coeff, h, map_zero] at h1
    exact not_isUnit_zero h1
  have hv1 : PI.ArtSch.valb l bk.flat < 1 := by
    by_contra h
    push_neg at h
    exact flat_not_isUnit bk (isUnit_of_dvd_one
      (GlobalTheory.ArtinSchreierTilt.tiltDiv l 1 bk.flat (by rw [map_one]; exact h)))
  have hv0 : 0 < PI.ArtSch.valb l (a.coeff 0) := by
    rw [pos_iff_ne_zero]
    exact fun h => ha0 ((PreTilt.map_eq_zero (PadicComplexInt.integers l)).1 h)
  obtain ⟨m₀, hm₀⟩ := exists_pow_lt_of_lt_one hv0 hv1
  obtain ⟨c, hc⟩ := GlobalTheory.ArtinSchreierTilt.tiltDiv l (bk.flat ^ m₀) (a.coeff 0) (by rw [map_pow]; exact hm₀.le)
  obtain ⟨b, hb⟩ : (l : Ainf l) ∣ a - WittVector.teichmuller l (a.coeff 0) := by
    rw [← Ideal.mem_span_singleton, ← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub]
    simp [WittVector.constantCoeff_apply]
  have hxy : WittVector.teichmuller l c * a =
      bk.ev X ^ m₀ + (l : Ainf l) * (WittVector.teichmuller l c * b) := by
    have ha' : a = WittVector.teichmuller l (a.coeff 0) + (l : Ainf l) * b := by linear_combination hb
    have ht : WittVector.teichmuller l c * WittVector.teichmuller l (a.coeff 0) = bk.ev X ^ m₀ := by
      rw [bk.ev_X, ← map_pow, hc, map_mul, mul_comm]
    rw [ha', mul_add, ht]
    ring
  have h2 := geom_sum₂_mul (bk.ev X ^ m₀) (-((l : Ainf l) * (WittVector.teichmuller l c * b))) n
  refine ⟨m₀ * n, WittVector.teichmuller l c * ∑ i ∈ Finset.range n,
    (bk.ev X ^ m₀) ^ i * (-((l : Ainf l) * (WittVector.teichmuller l c * b))) ^ (n - 1 - i),
    -((-(WittVector.teichmuller l c * b)) ^ n), ?_⟩
  rw [pow_mul]
  linear_combination (∑ i ∈ Finset.range n,
    (bk.ev X ^ m₀) ^ i * (-((l : Ainf l) * (WittVector.teichmuller l c * b))) ^ (n - 1 - i)) * hxy + h2

end GlobalTheory.BSP.BddDen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRFiltrationKerThetaGeneratorFacts
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.MemLoc.FilSeed

variable {l : ℕ} [Fact l.Prime]

theorem mem_filtration_zero' (y : Per.BdRp l) : y ∈ Per.FilP l 0 := by
  obtain ⟨-, hone, -, -, -, -, hlast⟩ := filD_laws l
  have h1 : (1 : Per.BdRp l) ∈ Per.FilP l 0 := (hlast 0 1).1 (by rw [map_one, Nat.cast_zero]; exact hone)
  simpa using Ideal.mul_mem_left _ y h1

theorem exists_unit (C : Core l) (ξ : Ainf l) (hξ : Ideal.span {ξ} = RingHom.ker (Per.θ l)) :
    ∃ c : (Per.BdRp l)ˣ, aDp l ξ = (c : Per.BdRp l) * aDp l (xi C.ε) := by
  have hreg := (filtration_eq_xi_pow l C.ε (core_isEps l C)).2.1
  rw [C.ker_theta] at hξ
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 (hξ ▸ Ideal.mem_span_singleton_self ξ :
    ξ ∈ Ideal.span {xi C.ε})
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (hξ.symm ▸ Ideal.mem_span_singleton_self (xi C.ε) :
    xi C.ε ∈ Ideal.span {ξ})
  have h1 : aDp l a * aDp l b = 1 := by
    have : aDp l (xi C.ε) * (aDp l a * aDp l b - 1) = 0 := by
      have e : aDp l (xi C.ε) = aDp l b * (aDp l a * aDp l (xi C.ε)) := by
        rw [← map_mul, ← map_mul, ha, hb]
      linear_combination -e
    exact sub_eq_zero.1 (hreg _ this)
  refine ⟨⟨aDp l a, aDp l b, h1, by rw [mul_comm, h1]⟩, ?_⟩
  rw [← ha, map_mul]

end GlobalTheory.MemLoc.FilSeed


open GlobalTheory.MemLoc.FilSeed in
theorem GlobalTheory.MemLoc.seed_fil : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → (∀ n : ℕ, Per.FilP l n = Ideal.span {aDp l ξ ^ n}) ∧ (∀ (a b : ℤ) (x y : Per.BdR l), x ∈ Per.FilD l a → y ∈ Per.FilD l b → x * y ∈ Per.FilD l (a + b)) ∧ (∀ (a b : ℤ), a ≤ b → Per.FilD l b ≤ Per.FilD l a) ∧ (∀ (n : ℕ) (z : Per.BdRp l), algebraMap (Per.BdRp l) (Per.BdR l) z ∈ Per.FilD l n ↔ z ∈ Per.FilP l n) ∧ (∀ x : Per.BdR l, ∃ n : ℕ, x ∈ Per.FilD l (-(n : ℤ))) ∧ (∀ (a : ℤ) (n : ℕ) (x : Per.BdR l), algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) ^ n * x ∈ Per.FilD l (a + n) ↔ x ∈ Per.FilD l a) ∧ Function.Injective (algebraMap (Per.Acris l) (Per.Bcris l)) := by
  intro l _ C ξ hξ
  obtain ⟨hstep, hone, hmul, hex, -, -, hlast⟩ := filD_laws l
  obtain ⟨hP, hreg, -, -⟩ := filtration_eq_xi_pow l C.ε (core_isEps l C)
  obtain ⟨c, hc⟩ := exists_unit C ξ hξ
  have h1 : ∀ n : ℕ, Per.FilP l n = Ideal.span {aDp l ξ ^ n} := by
    intro n
    ext y
    rw [hP, Ideal.mem_span_singleton, hc, mul_pow, ← Units.val_pow_eq_pow_val,
      Units.mul_left_dvd]
  have hanti : ∀ (a b : ℤ), a ≤ b → Per.FilD l b ≤ Per.FilD l a := by
    intro a b hab
    induction b, hab using Int.leInduction with
    | base => exact le_rfl
    | succ b _ ih => exact (hstep b).trans ih
  refine ⟨h1, hmul, hanti, hlast, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨a, ha⟩ := hex x
    exact ⟨(-a).toNat, hanti _ _ (by omega) ha⟩
  · intro a n x
    set w := algebraMap (Per.BdRp l) (Per.BdR l) (aDp l ξ) with hw
    have hwn : w ^ n ∈ Per.FilD l n := by
      rw [hw, ← map_pow, hlast, h1]
      exact Ideal.mem_span_singleton_self _

    have hdvr := GlobalTheory.MemLoc.BdRDVR.core_dvr l C
    obtain ⟨_, _, -, -, -, -, hfr⟩ := hdvr
    have hinj : Function.Injective (algebraMap (Per.BdRp l) (Per.BdR l)) := IsFractionRing.injective _ _
    have hw0 : w ≠ 0 := by
      intro h
      have h0 : aDp l ξ = 0 := hinj (by rw [← hw, h, map_zero])
      rw [hc] at h0
      have h2 : aDp l (xi C.ε) = 0 := (Units.mul_right_eq_zero c).1 h0
      exact one_ne_zero (hreg 1 (by rw [h2, zero_mul]))
    haveI := hfr
    have hne : aDp l ξ ≠ 0 := fun h => hw0 (by rw [hw, h, map_zero])
    obtain ⟨u, hu⟩ : IsUnit w :=
      IsLocalization.map_units (Per.BdR l) (⟨aDp l ξ, mem_nonZeroDivisors_of_ne_zero hne⟩ : nonZeroDivisors _)
    have hv : ((u⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) ∈ Per.FilD l (-1) := by
      rw [mem_FilD_iff_xi_pow l C.ε (core_isEps l C)]
      refine ⟨((c⁻¹ : (Per.BdRp l)ˣ) : Per.BdRp l), ?_⟩
      have e1 : (- (-1 : ℤ)).toNat = 1 := by norm_num
      have e2 : (-1 : ℤ).toNat = 0 := by norm_num
      have e3 : aDp l (xi C.ε) = aDp l ξ * ((c⁻¹ : (Per.BdRp l)ˣ) : Per.BdRp l) := by
        rw [hc, mul_comm (c : Per.BdRp l), mul_assoc, Units.mul_inv, mul_one]
      rw [e1, e2, pow_one, pow_zero, e3, map_mul (algebraMap (Per.BdRp l) (Per.BdR l)) (aDp l ξ), ← hw, ← hu,
        ← mul_assoc, Units.inv_mul, one_mul]
      simp
    have hvn : ∀ k : ℕ, ((u⁻¹ : (Per.BdR l)ˣ) : Per.BdR l) ^ k ∈ Per.FilD l (-(k : ℤ)) := by
      intro k
      induction k with
      | zero => simpa using hone
      | succ k ih =>
        rw [pow_succ]
        have := hmul _ _ _ _ ih hv
        rwa [show -(k : ℤ) + -1 = -((k + 1 : ℕ) : ℤ) by push_cast; ring] at this
    constructor
    · intro h
      have := hmul _ _ _ _ (hvn n) h
      rwa [← mul_assoc, ← mul_pow, ← hu, Units.inv_mul, one_pow, one_mul,
        show -(n : ℤ) + (a + n) = a by ring] at this
    · intro h
      have := hmul _ _ _ _ hwn h
      rwa [add_comm] at this
  · have hdvr := GlobalTheory.MemLoc.BdRDVR.core_dvr l C
    obtain ⟨_, _, -, -, -, -, hfr⟩ := hdvr
    haveI := hfr
    have hinjD : Function.Injective (algebraMap (Per.BdRp l) (Per.BdR l)) := IsFractionRing.injective _ _
    have hplus : Function.Injective C.jP := (GlobalTheory.MemLoc.AwayT.away_and_inj l C).2.2
    have hloc : Function.Injective (algebraMap (Per.Acris l) (BcrisP l)) := by
      refine IsLocalization.injective (M := Submonoid.powers ((l : ℕ) : Per.Acris l)) (BcrisP l) ?_
      rw [Submonoid.powers_le, mem_nonZeroDivisors_iff]
      have ht := (acris_torsionFree_complete l).1
      exact ⟨ht, fun x hx => ht x (by rw [mul_comm]; exact hx)⟩
    intro x y hxy
    apply hloc
    apply hplus
    apply hinjD
    rw [C.jP_alg, C.jP_alg, ← C.ι_j, ← C.ι_j, hxy]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BezoutEisensteinDerivativePrimePow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem bezout_Ep_derivative : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), ∃ (c : ℕ) (a b : Polynomial (Wq l bk.a)),
    a * bk.Ep + b * Polynomial.derivative bk.Ep = Polynomial.C ((l : Wq l bk.a) ^ c) := by
  intro l _ K bk
  haveI : CharZero (Wq l bk.a) := GlobalTheory.charZero_wittVector_of_field l (Fq l bk.a)
  have hirr : Irreducible (l : Wq l bk.a) := WittVector.irreducible l (k := Fq l bk.a)
  have hprime : Prime (l : Wq l bk.a) := hirr.prime
  have hP : (Ideal.span {(l : Wq l bk.a)}).IsPrime := (Ideal.span_singleton_prime hprime.ne_zero).2 hprime
  have hE : bk.Ep.IsEisensteinAt (Ideal.span {(l : Wq l bk.a)}) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [bk.monic.leadingCoeff, Ideal.mem_span_singleton]
      exact fun h => hirr.not_isUnit (isUnit_of_dvd_one h)
    · intro n hn
      exact Ideal.mem_span_singleton.2 (bk.dvd_coeff n hn)
    · obtain ⟨w, hw⟩ := bk.coeff_zero
      rw [hw, Ideal.span_singleton_pow, Ideal.mem_span_singleton, pow_two]
      intro h
      have h2 : (l : Wq l bk.a) ∣ (w : Wq l bk.a) := (mul_dvd_mul_iff_left hprime.ne_zero).1 h
      exact hirr.not_isUnit (isUnit_of_dvd_unit h2 w.isUnit)
  have hirrE : Irreducible bk.Ep := hE.irreducible hP bk.monic.isPrimitive bk.deg_pos
  let F := FractionRing (Wq l bk.a)
  haveI : CharZero F := charZero_of_injective_algebraMap (IsFractionRing.injective (Wq l bk.a) F)
  have hirrF : Irreducible (bk.Ep.map (algebraMap (Wq l bk.a) F)) :=
    (bk.monic.irreducible_iff_irreducible_map_fraction_map).1 hirrE
  obtain ⟨a, b, hab⟩ := hirrF.separable
  rw [Polynomial.derivative_map] at hab
  obtain ⟨d₁, hd₁, hA⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors (Wq l bk.a)) a
  obtain ⟨d₂, hd₂, hB⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors (Wq l bk.a)) b
  set A := IsLocalization.integerNormalization (nonZeroDivisors (Wq l bk.a)) a
  set B := IsLocalization.integerNormalization (nonZeroDivisors (Wq l bk.a)) b
  have hd : d₁ * d₂ ≠ 0 := mul_ne_zero (nonZeroDivisors.ne_zero hd₁) (nonZeroDivisors.ne_zero hd₂)
  have key : Polynomial.C d₂ * A * bk.Ep + Polynomial.C d₁ * B * Polynomial.derivative bk.Ep =
      Polynomial.C (d₁ * d₂) := by
    apply Polynomial.map_injective (algebraMap (Wq l bk.a) F) (IsFractionRing.injective (Wq l bk.a) F)
    simp only [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_C, hA, hB, Polynomial.derivative_map]
    simp only [Algebra.smul_def, Polynomial.algebraMap_apply, map_mul, Polynomial.C_mul]
    linear_combination (Polynomial.C (algebraMap (Wq l bk.a) F d₁) * Polynomial.C (algebraMap (Wq l bk.a) F d₂)) * hab
  obtain ⟨m, u, hu⟩ := WittVector.exists_eq_pow_p_mul' (p := l) (k := Fq l bk.a) (d₁ * d₂) hd
  refine ⟨m, Polynomial.C ((↑u⁻¹ : Wq l bk.a) * d₂) * A, Polynomial.C ((↑u⁻¹ : Wq l bk.a) * d₁) * B, ?_⟩
  have : Polynomial.C ((l : Wq l bk.a) ^ m) = Polynomial.C (↑u⁻¹ : Wq l bk.a) * Polynomial.C (d₁ * d₂) := by
    rw [hu, ← Polynomial.C_mul]
    congr 1
    rw [mul_comm, mul_assoc, Units.mul_inv, mul_one]
  rw [this, ← key]
  simp only [Polynomial.C_mul]
  ring

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BhattScholzeCoefficientsOfPadicIntLattices
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.LocalSituation TensorProduct Module GlobalTheory.Per GlobalTheory.Prism

noncomputable section
namespace GlobalTheory.BSCoeff

open GlobalTheory.PstCoeff GlobalTheory.BkCoeff

section Dcris

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l}
  {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
  (ρ : Representation LL ↥(GK K) V)

theorem Dcris_resQ : Dcris (P.PD K) (resQ ρ) = (Dcris (P.PD K) ρ).restrictScalars ℚ_[l] := by
  ext x
  simp [Dcris, sub_eq_zero, actVB_resQ]

theorem isCrys_resQ_iff [FiniteDimensional ℚ_[l] LL] : IsCrys (P.PD K) (resQ ρ) ↔ IsCrys (P.PD K) ρ := by
  have e : finrank ℚ_[l] ↥(Dcris (P.PD K) (resQ ρ)) = finrank ℚ_[l] LL * finrank LL ↥(Dcris (P.PD K) ρ) := by
    rw [Dcris_resQ, finrank_mul_finrank]
    rfl
  rw [IsCrys, IsCrys, e, ← finrank_mul_finrank ℚ_[l] LL V, mul_left_comm]
  exact Nat.mul_right_inj finrank_pos.ne'

end Dcris

variable {l : ℕ} [Fact l.Prime]

set_option synthInstance.maxHeartbeats 400000

theorem algebraMap_OL (LL : FinExt l) (z : ℤ_[l]) :
    algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) z) = algebraMap ℚ_[l] ↥LL.1 (z : ℚ_[l]) := by
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1]; rfl

theorem finite_OL (LL : FinExt l) : Module.Finite ℤ_[l] ↥(OL LL) :=
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)

variable {G : Type} [Group G] [TopologicalSpace G]

@[reducible] def zlV (LL : FinExt l) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) : Module ℤ_[l] T.V :=
  Module.compHom T.V (algebraMap ℤ_[l] ↥(OL LL))

theorem modO_smul (LL : FinExt l) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) (o : ↥(OL LL)) (w : T.V) :
    @HSMul.hSMul _ _ _ (@instHSMul _ _ T.modO.toSMul) o w = algebraMap ↥(OL LL) ↥LL.1 o • w := by
  letI := T.modO
  haveI := T.towO
  exact (algebraMap_smul ↥LL.1 o w).symm

theorem zlV_smul (LL : FinExt l) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) (z : ℤ_[l]) (w : T.V) :
    (zlV LL T).toSMul.smul z w = (z : ℚ_[l]) • w := by
  change @HSMul.hSMul _ _ _ (@instHSMul _ _ T.modO.toSMul) (algebraMap ℤ_[l] ↥(OL LL) z) w = _
  rw [modO_smul, algebraMap_OL, algebraMap_smul]

theorem zlV_tower (LL : FinExt l) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) :
    letI := zlV LL T
    IsScalarTower ℤ_[l] ℚ_[l] T.V := by
  letI := zlV LL T
  refine ⟨fun z q v => ?_⟩
  change (z • q) • v = (zlV LL T).toSMul.smul z (q • v)
  rw [zlV_smul, smul_smul]
  rfl

theorem finite_compHom {O M : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [AddCommGroup M]
    [Module O M] [Module.Finite O M] :
    letI := Module.compHom M (algebraMap ℤ_[l] O)
    Module.Finite ℤ_[l] M := by
  letI := Module.compHom M (algebraMap ℤ_[l] O)
  haveI : IsScalarTower ℤ_[l] O M := ⟨fun c a x => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  exact Module.Finite.trans O M

theorem denom (LL : FinExt l) (c : ↥LL.1) :
    ∃ (z : ℚ_[l]) (a : ↥(OL LL)), c = z • algebraMap ↥(OL LL) ↥LL.1 a := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have halg : IsAlgebraic ℤ_[l] c :=
    (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).mpr (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨z, hz, hint⟩ := halg.exists_integral_multiple
  have hz' : (z : ℚ_[l]) ≠ 0 := fun h => hz (Subtype.ext h)
  refine ⟨(z : ℚ_[l])⁻¹, ⟨z • c, hint⟩, ?_⟩
  change c = (z : ℚ_[l])⁻¹ • ((z : ℚ_[l]) • c)
  rw [smul_smul, inv_mul_cancel₀ hz', one_smul]

end GlobalTheory.BSCoeff

namespace GlobalTheory

open GlobalTheory.PstCoeff GlobalTheory.BkCoeff GlobalTheory.BSCoeff


set_option maxHeartbeats 1600000 in
theorem bhattScholze_coeff : GlobalTheory.Published.BhattScholzeIntegral → GlobalTheory.Published.BhattScholzeCrystallineLattices := by
  intro h l _ K P₀ e hA
  obtain ⟨h1, h2⟩ := h l K P₀ e hA
  refine ⟨fun P AI hS LL T hC => ?_, h2⟩
  letI := zlV LL T
  haveI := zlV_tower LL T
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI : FiniteDimensional ℚ_[l] T.V := Module.Finite.trans ↥LL.1 T.V
  haveI : IsModuleTopology ℚ_[l] ↥LL.1 := isModuleTopologyOfFiniteDimensional
  haveI : IsModuleTopology ℚ_[l] T.V := isModuleTopology_of_tower ℚ_[l] ↥LL.1 T.V
  let TZ : Submodule ℤ_[l] T.V :=
    { carrier := (T.L.T : Set T.V)
      add_mem' := fun ha hb => T.L.T.add_mem ha hb
      zero_mem' := T.L.T.zero_mem
      smul_mem' := fun z v hv => T.L.T.smul_mem (algebraMap ℤ_[l] ↥(OL LL) z) hv }
  haveI := finite_OL LL
  haveI : Module.Finite ↥(OL LL) ↥T.L.T := Module.Finite.iff_fg.mpr T.L.fg
  have hfin' := finite_compHom (l := l) (O := ↥(OL LL)) (M := ↥T.L.T)
  haveI hfin : Module.Finite ℤ_[l] ↥TZ := hfin'
  have hz : ∀ (z : ℤ_[l]) (v : T.V), z • v = (z : ℚ_[l]) • v := fun z v => zlV_smul LL T z v
  have htf : Module.IsTorsionFree ℤ_[l] ↥TZ := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro z x hx
    by_cases hz0 : z = 0
    · exact Or.inl hz0
    right
    have h' : (z : ℚ_[l]) • (x : T.V) = 0 := by
      rw [← hz]; exact congrArg Subtype.val hx
    have hq : (z : ℚ_[l]) ≠ 0 := fun h0 => hz0 (PadicInt.coe_eq_zero.1 h0)
    exact Subtype.ext ((smul_eq_zero.1 h').resolve_left hq)
  have hspan : Submodule.span ℚ_[l] (TZ : Set T.V) = ⊤ := by
    let W : Submodule ↥LL.1 T.V :=
      { carrier := (Submodule.span ℚ_[l] (TZ : Set T.V) : Set T.V)
        add_mem' := fun ha hb => Submodule.add_mem _ ha hb
        zero_mem' := Submodule.zero_mem _
        smul_mem' := by
          intro a x hx
          induction hx using Submodule.span_induction with
          | mem t ht =>
            obtain ⟨q, o, rfl⟩ := denom LL a
            show (q • algebraMap ↥(OL LL) ↥LL.1 o) • t ∈ Submodule.span ℚ_[l] (TZ : Set T.V)
            rw [smul_assoc, ← modO_smul]
            exact Submodule.smul_mem _ q (Submodule.subset_span (T.L.T.smul_mem o ht))
          | zero => simp
          | add x y _ _ hx hy =>
            show a • (x + y) ∈ Submodule.span ℚ_[l] (TZ : Set T.V)
            rw [smul_add]; exact Submodule.add_mem _ hx hy
          | smul q x _ hx =>
            show a • (q • x) ∈ Submodule.span ℚ_[l] (TZ : Set T.V)
            rw [← algebraMap_smul ↥LL.1 q x, smul_smul, mul_comm, ← smul_smul, algebraMap_smul]
            exact Submodule.smul_mem _ q hx }
    have hW : W = ⊤ := by
      rw [eq_top_iff, ← T.L.span, Submodule.span_le]
      intro t ht
      exact Submodule.subset_span ht
    rw [eq_top_iff]
    intro v _
    have : v ∈ W := hW ▸ Submodule.mem_top
    exact this
  let L : Lattice (O := ℤ_[l]) (resQ T.ρ) :=
    { T := TZ
      stable := fun g x hx => T.L.stable g x hx
      fg := Module.Finite.iff_fg.mp hfin
      free := Module.free_of_finite_type_torsion_free'
      span := hspan }
  obtain ⟨E, j, hR⟩ := h1 P AI hS T.V (resQ T.ρ) L (fun x => T.cont x) ((isCrys_resQ_iff P T.ρ).mpr hC)
  exact ⟨E, j, hR⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryModIffForallTraceFormCoboundaryStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundaryMod_iff_forall_traceForm_coboundary : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    (O : Type) [CommRing O] [Algebra O LL] (lam : LL →ₗ[ℚ_[l]] ℚ_[l]) (n : ℕ) (e f : Fin n → O),
    (∀ z : ℤ_[l], ∃ o : O, algebraMap O LL o = algebraMap ℚ_[l] LL (z : ℚ_[l])) →
    (∀ o : O, ∃ z : ℤ_[l], lam (algebraMap O LL o) = (z : ℚ_[l])) →
    (∀ x : LL, x = ∑ i, lam (algebraMap O LL (f i) * x) • algebraMap O LL (e i)) →
    ∀ (L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL))),
    L1.T = LinearMap.range (Algebra.linearMap O LL) →
    ∀ (L1Z : Lattice (O := ℤ_[l]) (charRep (cycLL (P.PD K) ℚ_[l]))),
    L1Z.T = LinearMap.range (Algebra.linearMap ℤ_[l] ℚ_[l]) →
    ∀ (z : ↥(GK K) × ↥(GK K) → LL),
    (CobO (P.PD K) L1 z ↔ ∀ o : O, CobO (P.PD K) L1Z (fun x => lam (algebraMap O LL o * z x))) := by
  first | exact @GlobalTheory.cobO_iff_forall_lam | exact GlobalTheory.cobO_iff_forall_lam | (intros; apply GlobalTheory.cobO_iff_forall_lam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGaloisOrbitWittTensorLatticeWeakTopoloStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_galois_orbit_wittTensorLatticeWeakTopology : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) {K LL : FinExt l} (T : Lt K LL) {d : ℕ} (b : LatB T d) (y : TW (RW LL) T), letI := twTop T b; Continuous fun g : ↥(GK K) => TWact (AI.gRW LL (g : GQ l)) T g y := by
  first | exact @GlobalTheory.WeakClosed.continuous_orbit_twTop | exact GlobalTheory.WeakClosed.continuous_orbit_twTop | (intros; apply GlobalTheory.WeakClosed.continuous_orbit_twTop <;> assumption)
end

