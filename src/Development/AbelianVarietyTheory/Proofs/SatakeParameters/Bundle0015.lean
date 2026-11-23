module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqTransposeMulMapOfIdempotent
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0014
public import GroundTheory.Brauer.IsBrauerEquivalentIffNonemptyAlgEquiv
public import GroundTheory.Brauer.BaseChangeCSA
public import GroundTheory.Brauer.DoubleCentralizer
public import GroundTheory.Brauer.Degree
public import GroundTheory.Brauer.SkolemNoether
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0023

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCongruenceKernelTraceCharacterStatement
section
open GlobalTheory.Cong
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_congruenceKernel_trace_character : ∀ (R A : Type) [CommRing R] [IsDomain R] [AddCommGroup A] (a : ℕ) (c : R), c ≠ 0 → ∀ (φ : R →+ A), (∀ x, φ (c * x) = 0) → ∀ B : Matrix (Fin a) (Fin a) R, ∃ lam : (Matrix.GeneralLinearGroup.map (n := Fin a) (Ideal.Quotient.mk (Ideal.span {c}))).ker →* Multiplicative A, ∀ g (x : Matrix (Fin a) (Fin a) R), (g.1 : Matrix (Fin a) (Fin a) R) = 1 + c • x → lam g = Multiplicative.ofAdd (φ (B * x).trace) := by
  first | exact @GlobalTheory.congChar_exists | exact GlobalTheory.congChar_exists | (intros; apply GlobalTheory.congChar_exists; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalSubringMonicRootsResidue
section
noncomputable section

open GlobalTheory.EtC

namespace GlobalTheory.LocInField

variable {K : Type} [Field K]

def locAt (R : Subring K) (𝔪 : Ideal R) [𝔪.IsPrime] : Subring K where
  carrier := {x | ∃ a s : R, s ∉ 𝔪 ∧ x * s = a}
  zero_mem' := ⟨0, 1, fun h => Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  one_mem' := ⟨1, 1, fun h => Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  add_mem' := by
    rintro x y ⟨a, s, hs, hx⟩ ⟨b, t, ht, hy⟩
    refine ⟨a * t + b * s, s * t, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hs ht, ?_⟩
    push_cast; rw [← hx, ← hy]; ring
  mul_mem' := by
    rintro x y ⟨a, s, hs, hx⟩ ⟨b, t, ht, hy⟩
    refine ⟨a * b, s * t, fun h => (Ideal.IsPrime.mem_or_mem ‹_› h).elim hs ht, ?_⟩
    push_cast; rw [← hx, ← hy]; ring
  neg_mem' := by
    rintro x ⟨a, s, hs, hx⟩
    refine ⟨-a, s, hs, ?_⟩
    push_cast; rw [← hx]; ring

theorem le_locAt (R : Subring K) (𝔪 : Ideal R) [𝔪.IsPrime] : R ≤ locAt R 𝔪 := fun x hx =>
  ⟨⟨x, hx⟩, 1, fun h => Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).2 h), by simp⟩

theorem exists_local_subring : ∀ (k K : Type) [Field k] [Field K] [IsAlgClosed K] (φ : k →+* K) (R : Subring K) (𝔪 : Ideal R),
    φ.range ≤ R → 𝔪.IsMaximal → (∀ r : R, ∃ c : k, ∃ h : φ c ∈ R, r - ⟨φ c, h⟩ ∈ 𝔪) →
    (∀ x : K, ∃ d : R, d ≠ 0 ∧ (d : K) * x ∈ R) → (∀ x : K, IsIntegral R x → x ∈ R) →
    ∃ T : Subring K, φ.range ≤ T ∧ (∃ _ : IsLocalRing T, AIC T ∧
      ∀ t : T, ∃ c : k, ∃ h : φ c ∈ T, t - ⟨φ c, h⟩ ∈ IsLocalRing.maximalIdeal T) ∧ IsFractionRing T K := by
  intro k K _ _ _ φ R 𝔪 hφ hmax hres hden hic
  haveI : 𝔪.IsPrime := hmax.isPrime
  have hRT := le_locAt R 𝔪
  letI : Algebra R (locAt R 𝔪) := (Subring.inclusion hRT).toAlgebra
  haveI : IsScalarTower R (locAt R 𝔪) K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hunit : ∀ s : R, s ∉ 𝔪 → IsUnit (algebraMap R (locAt R 𝔪) s) := by
    intro s hs
    have hs0 : (s : K) ≠ 0 := fun h => hs (by rw [show s = 0 from Subtype.ext h]; exact zero_mem _)
    refine isUnit_iff_exists_inv.2 ⟨⟨(s : K)⁻¹, 1, s, hs, by simp [hs0]⟩, Subtype.ext ?_⟩
    change (s : K) * (s : K)⁻¹ = 1
    exact mul_inv_cancel₀ hs0
  haveI hloc : IsLocalization 𝔪.primeCompl (locAt R 𝔪) :=
    { map_units := fun s => hunit s s.2
      surj := fun t => by
        obtain ⟨a, s, hs, h⟩ := t.2
        exact ⟨(a, ⟨s, hs⟩), Subtype.ext h⟩
      exists_of_eq := fun {x y} h => by
        have h' := congrArg Subtype.val h
        have hxy : x = y := Subtype.ext h'
        exact ⟨1, by rw [hxy]⟩ }
  haveI : IsLocalRing (locAt R 𝔪) := IsLocalization.AtPrime.isLocalRing (locAt R 𝔪) 𝔪
  refine ⟨locAt R 𝔪, fun x hx => hRT (hφ hx), ⟨inferInstance, ?_, ?_⟩, ?_⟩
  · intro p hp hdeg
    have hdeg' : (p.map (algebraMap (locAt R 𝔪) K)).degree ≠ 0 := by
      rw [hp.degree_map, Polynomial.degree_eq_natDegree hp.ne_zero]
      exact_mod_cast hdeg.ne'
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hdeg'
    have hyT : IsIntegral (locAt R 𝔪) y := ⟨p, hp, by rw [← Polynomial.eval_map]; exact hy⟩
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization 𝔪.primeCompl y hyT
    have hmR : m • y ∈ R := hic _ hm
    have hmy : m • y = y * ((m : R) : K) := by
      rw [Submonoid.smul_def, Algebra.smul_def, mul_comm]; rfl
    have hyT' : y ∈ locAt R 𝔪 := ⟨⟨m • y, hmR⟩, m, m.2, hmy.symm⟩
    refine ⟨⟨y, hyT'⟩, Subtype.ext ?_⟩
    change algebraMap (locAt R 𝔪) K (p.eval ⟨y, hyT'⟩) = 0
    rw [← Polynomial.eval₂_at_apply (algebraMap (locAt R 𝔪) K), ← Polynomial.eval_map]
    exact hy
  · intro t
    obtain ⟨a, s, hs, hts⟩ := t.2
    obtain ⟨c, hc, hac⟩ := hres a
    obtain ⟨e, he, hse⟩ := hres s
    have he0 : e ≠ 0 := by
      rintro rfl
      apply hs
      have h0 : s - ⟨φ 0, he⟩ = s := by
        rw [sub_eq_self]; exact Subtype.ext (by simp)
      rwa [h0] at hse
    have hg : φ (c / e) ∈ R := hφ ⟨c / e, rfl⟩
    have hge : φ (c / e) * φ e = φ c := by rw [← map_mul, div_mul_cancel₀ c he0]
    refine ⟨c / e, hRT hg, ?_⟩
    have hb : (a - ⟨φ c, hc⟩) - ⟨φ (c / e), hg⟩ * (s - ⟨φ e, he⟩) ∈ 𝔪 :=
      sub_mem hac (Ideal.mul_mem_left _ _ hse)
    have key : (t - ⟨φ (c / e), hRT hg⟩) * algebraMap R (locAt R 𝔪) s =
        algebraMap R (locAt R 𝔪) ((a - ⟨φ c, hc⟩) - ⟨φ (c / e), hg⟩ * (s - ⟨φ e, he⟩)) := by
      apply Subtype.ext
      change ((t : K) - φ (c / e)) * (s : K) = ((a : K) - φ c) - φ (c / e) * ((s : K) - φ e)
      linear_combination hts - hge
    have hb' := (IsLocalization.AtPrime.to_map_mem_maximal_iff (locAt R 𝔪) 𝔪 _).2 hb
    rw [← key] at hb'
    exact (Ideal.IsPrime.mem_or_mem inferInstance hb').resolve_right
      fun h => (IsLocalRing.mem_maximalIdeal _).1 h (hunit s hs)
  · haveI : FaithfulSMul (locAt R 𝔪) K := inferInstance
    refine IsFractionRing.of_field _ K fun z => ?_
    obtain ⟨d, hd, hdz⟩ := hden z
    have hd0 : (d : K) ≠ 0 := fun h => hd (Subtype.ext h)
    refine ⟨⟨(d : K) * z, hRT hdz⟩, ⟨d, hRT d.2⟩, ?_⟩
    change z = (d : K) * z / d
    field_simp

end GlobalTheory.LocInField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsNormEqXModMonicOfAdicCompleteInvolution
section
open Polynomial

namespace GlobalTheory.InertNorm

theorem isAdicComplete_map_of_finite {O : Type} [CommRing O] [IsNoetherianRing O] (I : Ideal O)
    [IsAdicComplete I O] (R : Type) [CommRing R] [Algebra O R] [Module.Finite O R] :
    IsAdicComplete (I.map (algebraMap O R)) R := by
  rw [IsAdicComplete.map_algebraMap_iff]
  have : IsHausdorff I R := IsHausdorff.of_le_jacobson I R (IsAdicComplete.le_jacobson I)
  have : IsPrecomplete I R := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isPrecomplete_finite_module I R
  exact ⟨⟩

theorem finite_quotient_map_of_finite {O : Type} [CommRing O] (I : Ideal O) [Finite (O ⧸ I)]
    (R : Type) [CommRing R] [Algebra O R] [Module.Finite O R] :
    Finite (R ⧸ I.map (algebraMap O R)) := by
  have : Module.Finite O (R ⧸ I.map (algebraMap O R)) := inferInstance
  have : Module.Finite (O ⧸ I) (R ⧸ I.map (algebraMap O R)) :=
    Module.Finite.of_restrictScalars_finite O (O ⧸ I) _
  exact Module.finite_of_finite (O ⧸ I)

theorem exists_dvd_mul_map_sub_X : ∀ (O : Type) [CommRing O] [IsNoetherianRing O] (I : Ideal O) [IsAdicComplete I O] [Finite (O ⧸ I)] (c : O →+* O), (∀ x, c (c x) = x) → (∀ x ∈ I, c x ∈ I) → (∃ ω, IsUnit (ω - c ω)) → ∀ f : Polynomial O, f.Monic → f.map c = f → IsUnit (f.coeff 0) → ∃ p : Polynomial O, f ∣ p * p.map c - Polynomial.X := by
  intro O _ _ I _ _ c hcc hcI hω f hf hfc hf0
  have : Module.Finite O (AdjoinRoot f) := (AdjoinRoot.powerBasis' hf).finite
  let J : Ideal (AdjoinRoot f) := I.map (algebraMap O (AdjoinRoot f))
  have : IsAdicComplete J (AdjoinRoot f) := isAdicComplete_map_of_finite I (AdjoinRoot f)
  have : Finite (AdjoinRoot f ⧸ J) := finite_quotient_map_of_finite I (AdjoinRoot f)

  have hev : f.eval₂ ((AdjoinRoot.of f).comp c) (AdjoinRoot.root f) = 0 := by
    rw [← Polynomial.eval₂_map, hfc, AdjoinRoot.eval₂_root]
  let c' : AdjoinRoot f →+* AdjoinRoot f :=
    AdjoinRoot.lift ((AdjoinRoot.of f).comp c) (AdjoinRoot.root f) hev
  have hc'mk : ∀ p : Polynomial O, c' (AdjoinRoot.mk f p) = AdjoinRoot.mk f (p.map c) := by
    intro p
    simp only [c', AdjoinRoot.lift_mk]
    rw [← Polynomial.eval₂_map, ← AdjoinRoot.aeval_eq, Polynomial.aeval_def, AdjoinRoot.algebraMap_eq]
  have hc'of : ∀ x : O, c' (algebraMap O (AdjoinRoot f) x) = algebraMap O (AdjoinRoot f) (c x) := by
    intro x
    simp only [AdjoinRoot.algebraMap_eq, c', AdjoinRoot.lift_of, RingHom.comp_apply]
  have hcomp : c.comp c = RingHom.id O := RingHom.ext hcc
  have hinv : ∀ y, c' (c' y) = y := by
    intro y
    induction y using AdjoinRoot.induction_on with
    | ih p => rw [hc'mk, hc'mk, Polynomial.map_map, hcomp, Polynomial.map_id]
  have hJ : ∀ y ∈ J, c' y ∈ J := by
    have : J ≤ J.comap c' := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      simp only [Ideal.mem_comap, hc'of]
      exact Ideal.mem_map_of_mem _ (hcI x hx)
    exact fun y hy => this hy
  have hω' : ∃ ω, IsUnit (ω - c' ω) := by
    obtain ⟨ω, hu⟩ := hω
    refine ⟨algebraMap O (AdjoinRoot f) ω, ?_⟩
    rw [hc'of, ← map_sub]
    exact hu.map _
  have hroot : c' (AdjoinRoot.root f) = AdjoinRoot.root f := AdjoinRoot.lift_root _

  have hunit : IsUnit (AdjoinRoot.root f) := by
    have h0 : (f - Polynomial.C (f.coeff 0)).coeff 0 = 0 := by simp
    obtain ⟨q, hq⟩ := Polynomial.X_dvd_iff.mpr h0
    have hm : AdjoinRoot.root f * AdjoinRoot.mk f q = -AdjoinRoot.of f (f.coeff 0) := by
      have := congrArg (AdjoinRoot.mk f) hq
      rw [map_sub, AdjoinRoot.mk_self, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C, zero_sub] at this
      exact this.symm
    exact isUnit_of_mul_isUnit_left (hm ▸ (hf0.map (AdjoinRoot.of f)).neg)
  obtain ⟨x, hx⟩ := _root_.GlobalTheory.HenselianNorm.exists_norm_eq (AdjoinRoot f) J c' hinv hJ hω' (AdjoinRoot.root f) hroot hunit
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
  refine ⟨p, ?_⟩
  rw [← AdjoinRoot.mk_eq_zero, map_sub, map_mul, ← hc'mk, hx, AdjoinRoot.mk_X, sub_self]

end GlobalTheory.InertNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPolynomialSubringMaximalIntegral
section
open GlobalTheory.EtC

namespace GlobalTheory

theorem exists_polySubring_maximal_integral (k K : Type) [Field k] [Field K] (φ : k →+* K) :
    ∃ (D : Subring K) (m₀ : Ideal D), φ.range ≤ D ∧ m₀.IsMaximal ∧
    (∀ r : D, ∃ c : k, ∃ h : φ c ∈ D, r - ⟨φ c, h⟩ ∈ m₀) ∧
      ∀ x : K, ∃ d : D, d ≠ 0 ∧ IsIntegral D ((d : K) * x) := by
  letI : Algebra k K := φ.toAlgebra
  haveI : FaithfulSMul k K := (faithfulSMul_iff_algebraMap_injective k K).2 φ.injective
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k K
  set A : Subalgebra k K := Algebra.adjoin k (Set.range ((↑) : s → K)) with hA
  let ε : A →ₐ[k] k := (MvPolynomial.aeval (fun _ : s => (0 : k))).comp hs.1.aevalEquiv.symm.toAlgHom
  have hε : ∀ c : k, ε (algebraMap k A c) = c := fun c => ε.commutes c
  let D : Subring K := A.toSubring
  let εD : D →+* k := (ε : A →+* k)
  have hεs : Function.Surjective εD := fun c => ⟨algebraMap k A c, hε c⟩
  refine ⟨D, RingHom.ker εD, ?_, RingHom.ker_isMaximal_of_surjective εD hεs, ?_, ?_⟩
  · rintro _ ⟨c, rfl⟩
    exact A.algebraMap_mem c
  · intro r
    refine ⟨εD r, A.algebraMap_mem _, ?_⟩
    rw [RingHom.mem_ker, map_sub]
    have : εD ⟨φ (εD r), A.algebraMap_mem _⟩ = εD r := hε (εD r)
    rw [this, sub_self]
  · intro x
    haveI : Algebra.IsAlgebraic A K := hs.isAlgebraic
    haveI : Algebra.IsAlgebraic D K := ‹Algebra.IsAlgebraic A K›
    obtain ⟨y, hy, hint⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := D) x).exists_integral_multiple
    exact ⟨y, hy, by rwa [Algebra.smul_def] at hint⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralClosureMaximalResidueOfAlgClosed
section
open GlobalTheory.EtC

namespace GlobalTheory

theorem integralClosure_maximal_residue_algClosed : ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] (φ : k →+* K) (D : Subring K) (m₀ : Ideal D),
    φ.range ≤ D → m₀.IsMaximal → (∀ r : D, ∃ c : k, ∃ h : φ c ∈ D, r - ⟨φ c, h⟩ ∈ m₀) →
    (∀ x : K, ∃ d : D, d ≠ 0 ∧ IsIntegral D ((d : K) * x)) →
    ∃ (R : Subring K) (𝔪 : Ideal R), φ.range ≤ R ∧ 𝔪.IsMaximal ∧ (∀ r : R, ∃ c : k, ∃ h : φ c ∈ R, r - ⟨φ c, h⟩ ∈ 𝔪) ∧
      (∀ x : K, ∃ d : R, d ≠ 0 ∧ (d : K) * x ∈ R) ∧ ∀ x : K, IsIntegral R x → x ∈ R := by
  intro k K _ _ _ φ D m₀ hφD hm₀ hres hfrac
  let A := integralClosure D K
  have hφA : ∀ c : k, φ c ∈ A := fun c =>
    isIntegral_algebraMap (R := D) (x := (⟨φ c, hφD ⟨c, rfl⟩⟩ : D))
  have hker : RingHom.ker (algebraMap D A) ≤ m₀ := by
    intro d hd
    have h0 : (algebraMap D A d : K) = 0 := by rw [RingHom.mem_ker.mp hd]; rfl
    have : d = 0 := Subtype.ext h0
    simp [this]
  obtain ⟨𝔪, h𝔪max, h𝔪comap⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := A) m₀ hker
  let φA : k →+* A := φ.codRestrict A hφA
  let ψ : k →+* A ⧸ 𝔪 := (Ideal.Quotient.mk 𝔪).comp φA
  have hcoef : ∀ d : D, algebraMap D (A ⧸ 𝔪) d ∈ Set.range ψ := by
    intro d
    obtain ⟨c, hc, hdc⟩ := hres d
    refine ⟨c, ?_⟩
    have hmem : algebraMap D A (d - ⟨φ c, hc⟩) ∈ 𝔪 := by
      rw [← Ideal.mem_comap]
      change d - ⟨φ c, hc⟩ ∈ Ideal.under D 𝔪
      rw [h𝔪comap]
      exact hdc
    change Ideal.Quotient.mk 𝔪 (φA c) = Ideal.Quotient.mk 𝔪 (algebraMap D A d)
    symm
    rw [map_sub] at hmem
    exact Ideal.Quotient.eq.mpr hmem
  have hres' : ∀ r : A, ∃ c : k, r - φA c ∈ 𝔪 := by
    intro r
    letI : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    letI : Algebra k (A ⧸ 𝔪) := ψ.toAlgebra
    have hr : IsIntegral D (Ideal.Quotient.mkₐ D 𝔪 r) :=
      (Algebra.IsIntegral.isIntegral (R := D) r).map (Ideal.Quotient.mkₐ D 𝔪)
    obtain ⟨f, hfm, hf⟩ := hr
    have hlift : f.map (algebraMap D (A ⧸ 𝔪)) ∈ Polynomial.lifts ψ := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n; rw [Polynomial.coeff_map]; exact hcoef _
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift (hfm.map _)
    have hint : IsIntegral k (Ideal.Quotient.mk 𝔪 r) := by
      refine ⟨q, hqm, ?_⟩
      rw [Polynomial.eval₂_eq_eval_map]
      change Polynomial.eval _ (q.map ψ) = 0
      rw [hq, ← Polynomial.eval₂_eq_eval_map]
      exact hf
    have h1 := IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible hint)
    obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one k _ h1
    exact ⟨c, Ideal.Quotient.eq.mp hc.symm⟩
  refine ⟨A.toSubring, 𝔪, ?_, h𝔪max, ?_, ?_, ?_⟩
  · rintro _ ⟨c, rfl⟩; exact hφA c
  · intro r
    obtain ⟨c, hc⟩ := hres' r
    exact ⟨c, hφA c, hc⟩
  · intro x
    obtain ⟨d, hd, hint⟩ := hfrac x
    refine ⟨⟨(d : K), Subalgebra.algebraMap_mem A d⟩, ?_, hint⟩
    intro h
    apply hd
    exact Subtype.ext (by simpa using congrArg Subtype.val h)
  · intro x hx
    have hx' : IsIntegral A x := hx
    exact isIntegral_trans x hx'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIndEtaleOverEtaleOfIsIndEtaleStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIndEtale_over_etale_of_isIndEtale : ∀ (A W O : Type) [CommRing A] [CommRing W] [CommRing O] [Algebra A W] [Algebra A O] [Algebra W O] [IsScalarTower A W O] [Algebra.Etale A W], GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap A O) → GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap W O) := by
  first | (exact @GlobalTheory.IndEtaleCancel.isIndEtale_of_etale_of_isIndEtale) | (exact GlobalTheory.IndEtaleCancel.isIndEtale_of_etale_of_isIndEtale) | (intros; apply GlobalTheory.IndEtaleCancel.isIndEtale_of_etale_of_isIndEtale  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsNoetherianRingOfDirectedPureUnionStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNoetherianRing_of_directed_pure_union' : ∀ (S : Type) [CommRing S] [IsLocalRing S] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι] (R : ι → Subring S), Monotone R → (∀ x : S, ∃ i, x ∈ R i) → (∀ i, IsNoetherianRing (R i)) → (∀ i, ((maximalIdeal S).comap (R i).subtype).map (R i).subtype = maximalIdeal S) → (∀ i (J : Ideal (R i)), (J.map (R i).subtype).comap (R i).subtype = J) → IsNoetherianRing S := by
  first | (exact @GlobalTheory.isNoetherianRing_of_directed_pure_union) | (exact GlobalTheory.isNoetherianRing_of_directed_pure_union) | (intros; apply GlobalTheory.isNoetherianRing_of_directed_pure_union  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsReducedTensorIntNumberField
section
open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem isReduced_tensor_int_numberField (F K : Type) [Field F] [NumberField F] [Field K] :
    IsReduced (K ⊗[ℤ] F) := by
  haveI : Algebra.FormallyUnramified ℤ ℚ := Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors ℤ)
  haveI : Algebra.FormallyUnramified ℚ F := Algebra.FormallyUnramified.of_isSeparable ℚ F
  haveI : Algebra.FormallyUnramified ℤ F := Algebra.FormallyUnramified.comp ℤ ℚ F
  haveI : Algebra.EssFiniteType ℤ ℚ := Algebra.EssFiniteType.of_isLocalization ℚ (nonZeroDivisors ℤ)
  haveI : Algebra.EssFiniteType ℤ F := Algebra.EssFiniteType.comp ℤ ℚ F
  haveI : Algebra.FormallyUnramified K (K ⊗[ℤ] F) := inferInstance
  haveI : Algebra.EssFiniteType K (K ⊗[ℤ] F) := inferInstance
  exact Algebra.FormallyUnramified.isReduced_of_field K (K ⊗[ℤ] F)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemPowHeightOneIdealIffDvdEmbedding
section
open NumberField IsDedekindDomain WithZero

namespace GlobalTheory

theorem ordIdeal_of_ringHom {R W : Type} [CommRing R] [IsDedekindDomain R]
    [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (P : HeightOneSpectrum R) (p : W) (hp : Irreducible p) (f : R →+* W)
    (hP : ∀ x : R, x ∈ P.asIdeal ↔ p ∣ f x)
    (hd : ∀ (y : W) (n : ℕ), ∃ (x : R) (z : W), f x = y + p ^ n * z)
    (x : R) (k : ℕ) : x ∈ P.asIdeal ^ k ↔ p ^ k ∣ f x := by

  have hpp : Prime p := hp.prime
  have hp0 : p ≠ 0 := hp.ne_zero
  obtain ⟨π, z, hπ⟩ := hd p 2
  have hπP : π ∈ P.asIdeal := (hP π).2 ⟨1 + p * z, by rw [hπ]; ring⟩
  set Q : Ideal R := Ideal.comap f (Ideal.span {p ^ k}) with hQdef
  have hQ : ∀ y : R, y ∈ Q ↔ p ^ k ∣ f y := fun y => by
    rw [hQdef, Ideal.mem_comap, Ideal.mem_span_singleton]
  have hle : P.asIdeal ^ k ≤ Q := by
    have h1 : P.asIdeal ≤ Ideal.comap f (Ideal.span {p}) := fun y hy => by
      rw [Ideal.mem_comap, Ideal.mem_span_singleton]
      exact (hP y).1 hy
    calc P.asIdeal ^ k ≤ (Ideal.comap f (Ideal.span {p})) ^ k := Ideal.pow_right_mono h1 k
      _ ≤ Ideal.comap f ((Ideal.span {p}) ^ k) := Ideal.le_comap_pow f k
      _ = Q := by rw [Ideal.span_singleton_pow]
  obtain ⟨j, hj, hassoc⟩ := (dvd_prime_pow P.prime k).1 (Ideal.dvd_iff_le.2 hle)
  have hQj : Q = P.asIdeal ^ j := associated_iff_eq.1 hassoc
  have hjk : j = k := by
    by_contra hne
    have hjk' : j ≤ k - 1 := by omega
    have hmem : π ^ (k - 1) ∈ Q := by
      rw [hQj]
      exact Ideal.pow_le_pow_right hjk' (Ideal.pow_mem_pow hπP _)
    rw [hQ, map_pow, hπ] at hmem
    have hfac : (p + p ^ 2 * z) ^ (k - 1) = p ^ (k - 1) * (1 + p * z) ^ (k - 1) := by
      rw [← mul_pow]; ring
    have hk' : p ^ k = p ^ (k - 1) * p := by
      rw [← pow_succ]; congr 1; omega
    rw [hfac, hk'] at hmem
    have hdiv := (mul_dvd_mul_iff_left (pow_ne_zero (k - 1) hp0)).1 hmem
    have hdiv' := hpp.dvd_of_dvd_pow hdiv
    have hone : p ∣ 1 := (dvd_add_left (dvd_mul_right p z)).1 hdiv'
    exact hp.not_isUnit (isUnit_of_dvd_one hone)
  rw [← hQ, hQj, hjk]

theorem ordIdeal_of_embedding {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p : ℕ) (hp : Irreducible (p : W)) (ρ : E →+* Qq) (h1 : ∀ x : 𝓞 E, ∃ y : W, ρ x = algebraMap W Qq y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y)) (h2 : ∀ (y : W) (n : ℕ), ∃ (x : 𝓞 E) (z : W), ρ x = algebraMap W Qq (y + (p : W) ^ n * z)) (x : 𝓞 E) (y : W) (k : ℕ) : ρ x = algebraMap W Qq y → (x ∈ P.asIdeal ^ k ↔ (p : W) ^ k ∣ y) := by

  intro hxy
  have hinj : Function.Injective (algebraMap W Qq) := IsFractionRing.injective W Qq
  choose F hF using h1
  let f : 𝓞 E →+* W :=
    { toFun := F
      map_one' := hinj (by rw [← (hF 1).1]; simp)
      map_mul' := fun a b => hinj (by
        rw [map_mul, ← (hF (a * b)).1, ← (hF a).1, ← (hF b).1]; simp)
      map_zero' := hinj (by rw [← (hF 0).1]; simp)
      map_add' := fun a b => hinj (by
        rw [map_add (f := _), ← (hF (a + b)).1, ← (hF a).1, ← (hF b).1]; simp) }
  have hfx : ∀ a : 𝓞 E, algebraMap W Qq (f a) = ρ a := fun a => ((hF a).1).symm
  have hP : ∀ a : 𝓞 E, a ∈ P.asIdeal ↔ (p : W) ∣ f a := fun a => (hF a).2
  have hd : ∀ (b : W) (n : ℕ), ∃ (a : 𝓞 E) (c : W), f a = b + (p : W) ^ n * c := by
    intro b n
    obtain ⟨a, c, hac⟩ := h2 b n
    exact ⟨a, c, hinj (by rw [hfx, hac])⟩
  have hy : f x = y := hinj (by rw [hfx, hxy])
  rw [ordIdeal_of_ringHom P (p : W) hp f hP hd x k, hy]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.QBinomialSumCardQuotientSubspaces
section
namespace GlobalTheory

theorem qBinomial_subspaces : ∀ (k V : Type) [Field k] [Finite k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (X : ℂ),
    ∑ j ∈ Finset.range (Module.finrank k V + 1),
        (-1 : ℂ) ^ j * (Nat.card k : ℂ) ^ (j * (j - 1) / 2) *
          (Nat.card {W : Submodule k V // Module.finrank k (V ⧸ W) = j} : ℂ) * X ^ j =
      ∏ i ∈ Finset.range (Module.finrank k V), (1 - (Nat.card k : ℂ) ^ i * X) := by
  intro k V _ _ _ _ _ X
  simp only [GlobalTheory.GaussCount.card_codim]
  exact GlobalTheory.GaussCount.gauss_formula (Nat.card k) ℂ X (Module.finrank k V)

end GlobalTheory
end

