module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0001
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0003
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0039
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0035
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0031
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0033
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0050
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0040
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0037
public import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0041
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0005

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.AlgSatPow
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RealGal.AttResProof

theorem algSat_pow (a q f : ℕ) (B : Multiset ℂˣ) :
    algSat a (q ^ f) (B.map (· ^ f)) = (algSat a q B).map (· ^ f) := by
  unfold algSat
  simp only [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, Multiset.map_map]
  refine Multiset.map_congr rfl fun α _ => ?_
  simp only [Function.comp_apply, Units.val_pow_eq_pow_val, mul_pow]
  congr 1
  push_cast
  rw [← Complex.ofReal_pow, Real.rpow_pow_comm (Nat.cast_nonneg q)]

end GlobalTheory.RealGal.AttResProof
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.BcDualOfPolarized
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.PolarBc

theorem normV_under_eq {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  simp only [normV, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

theorem bcDual_of_polarized : Cr.BcDual := by
  intro js gk F K _ _ _ _ _ _ _ h2 n hn π χ P hpol hBC
  obtain ⟨χ', hs, hv⟩ := UpperTheory.heckeChar_realTransport F K h2 χ
  refine ⟨χ', fun v v' => ?_, UpperTheory.polOfSat_of_thetaSat UpperTheory.theta_satake_parameters_inverse js gk K n hn P _ ?_⟩
  · obtain ⟨u, e⟩ := hs v
    obtain ⟨u', e'⟩ := hs v'
    rw [e, e', hpol.sign u u']
  have hu : ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite, χ.UnrAt (w.under (𝓞 F)) := by
    rw [Filter.eventually_cofinite]
    refine ((GlobalTheory.Mem.UnrAe.finite_ramified χ).preimage' (f := fun w : HeightOneSpectrum (𝓞 K) => w.under (𝓞 F))
      fun v _ => ?_).subset fun w hw => hw
    haveI := v.isMaximal
    refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 K)).preimage
      (f := fun w : HeightOneSpectrum (𝓞 K) => w.asIdeal) fun _ _ _ _ e => HeightOneSpectrum.ext e).subset fun w hw => ?_
    exact ⟨w.isPrime, ⟨congrArg HeightOneSpectrum.asIdeal (Eq.symm hw)⟩⟩
  filter_upwards [hu, hBC.unr, UpperTheory.baseChange_complexConj_invariance F K n π P hBC] with w hw h3 ⟨B₁, hB₁, hB₂⟩
  obtain ⟨B, hB, hB'⟩ := h3 (w.under (𝓞 F)) rfl _ (normV_under_eq w)
  obtain rfl := hB'.unique hB₁
  obtain ⟨e1, e2⟩ := hv w
  obtain ⟨e3, e4⟩ := UpperTheory.ideleNorm_valuation_of_local_compatibility UpperTheory.ideleNorm_local_compatibility K χ' w _ (e1.symm ▸ normV_under_eq (K := F) w) (e2 hw).1
  refine ⟨e3, _, _, hB', hB₂, ?_⟩
  obtain ⟨β, d, hl, -, -, hβ, -⟩ := hpol.dual
  have e5 := UpperTheory.satake_inv_mul_char_eq_of_similitude_pairing F n _ _ _ (π.isSmooth_locRep _) χ hw β hl (fun g x y => by
    have := hβ (GlobalTheory.CuspRep.locGL F n _ g) x y
    rwa [TR.CuspSub.chiDet_locGL] at this) B hB
  rw [e4, (e2 hw).2]
  conv_rhs => rw [← e5]
  simp only [Multiset.map_map]
  exact Multiset.map_congr rfl fun b _ => by simp [mul_pow]

end GlobalTheory.PolarBc
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.ExistsInfiniteQcmSplitRam
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ExSplitCM

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]

theorem exists_prime_mem (v : HeightOneSpectrum (𝓞 F)) :
    ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 F) ∈ v.asIdeal := by
  have hmax := v.isMaximal
  letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field v.asIdeal
  have hfin : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  obtain ⟨p, hp⟩ := CharP.exists (𝓞 F ⧸ v.asIdeal)
  refine ⟨p, CharP.char_is_prime (𝓞 F ⧸ v.asIdeal) p, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact CharP.cast_eq_zero _ p

theorem prime_eq_of_mem (u : HeightOneSpectrum (𝓞 F)) {p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime)
    (h : ((p : ℕ) : 𝓞 F) ∈ u.asIdeal) (h' : ((p' : ℕ) : 𝓞 F) ∈ u.asIdeal) : p = p' := by
  by_contra hne
  have hc : Nat.gcd p p' = 1 := (Nat.coprime_primes hp hp').2 hne
  have hm : (((Nat.gcd p p' : ℕ) : ℤ) : 𝓞 F) ∈ u.asIdeal := by
    rw [Nat.gcd_eq_gcd_ab p p']
    push_cast
    exact u.asIdeal.add_mem (u.asIdeal.mul_mem_right _ h) (u.asIdeal.mul_mem_right _ h')
  rw [hc] at hm
  simp only [Nat.cast_one, Int.cast_one] at hm
  exact u.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hm)

theorem finite_primes_of_finite {B : Set (HeightOneSpectrum (𝓞 F))} (hB : B.Finite) :
    {p : ℕ | p.Prime ∧ ∃ u ∈ B, ((p : ℕ) : 𝓞 F) ∈ u.asIdeal}.Finite := by
  refine (hB.biUnion (t := fun u => {p : ℕ | p.Prime ∧ ((p : ℕ) : 𝓞 F) ∈ u.asIdeal})
    fun u _ => Set.Subsingleton.finite fun p hp p' hp' => prime_eq_of_mem u hp.1 hp'.1 hp.2 hp'.2).subset ?_
  rintro p ⟨hp, u, hu, h⟩
  exact Set.mem_biUnion hu ⟨hp, h⟩

theorem exists_mem_of_prime {p : ℕ} (hp : p.Prime) :
    ∃ u : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ u.asIdeal := by
  have hnu : ¬ IsUnit ((p : ℕ) : 𝓞 F) := by
    intro h
    have h2 := h.map (Algebra.norm ℤ (S := 𝓞 F))
    rw [show ((p : ℕ) : 𝓞 F) = algebraMap ℤ (𝓞 F) (p : ℤ) by simp, Algebra.norm_algebraMap,
      isUnit_pow_iff Module.finrank_pos.ne', Int.isUnit_iff] at h2
    have := hp.two_le
    omega
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {((p : ℕ) : 𝓞 F)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hne : M ≠ ⊥ := by
    intro h
    rw [h] at hle
    have h0 := hle (Ideal.mem_span_singleton_self _)
    rw [Ideal.mem_bot] at h0
    exact hp.ne_zero (by exact_mod_cast h0)
  exact ⟨⟨M, hM.isPrime, hne⟩, hle (Ideal.mem_span_singleton_self _)⟩

theorem mem_range_res_iff (K : IntermediateField F Ω) (σ : G F Ω) :
    σ ∈ (res F Ω ↥K).range ↔ ∀ x ∈ K, σ x = x := by
  constructor
  · rintro ⟨τ, rfl⟩ x hx
    exact τ.commutes (⟨x, hx⟩ : K)
  · intro h
    exact ⟨AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) fun x => h _ x.2, rfl⟩

theorem fix_adjoin {δ : Ω} (hint : IsIntegral F δ) (s : G F Ω) (h : s δ = δ) :
    ∀ x ∈ IntermediateField.adjoin F {δ}, s x = x := by
  intro x hx
  rw [← IntermediateField.mem_toSubalgebra,
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic] at hx
  have := (AlgHom.eqOn_adjoin_iff (φ := (s : Ω →ₐ[F] Ω)) (ψ := AlgHom.id F Ω)).2
    (by simpa [Set.EqOn] using h) hx
  simpa using this

theorem exists_qcm [IsTotallyReal F] [IsAlgClosure F Ω] (d : F) (δ : Ω) (hδ : δ ^ 2 = algebraMap F Ω d)
    (hd : ∀ φ : F →+* ℝ, φ d < 0) : ∃ Q : QCM F Ω, Q.K = IntermediateField.adjoin F {δ} := by
  have halg : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  have hint : IsIntegral F δ := (halg.isAlgebraic δ).isIntegral
  let K : IntermediateField F Ω := IntermediateField.adjoin F {δ}
  haveI : FiniteDimensional F K := IntermediateField.adjoin.finiteDimensional hint
  haveI : NumberField K := NumberField.of_module_finite F K
  let y : K := IntermediateField.AdjoinSimple.gen F δ
  have hy : algebraMap K Ω y = δ := rfl
  have hy2 : y ^ 2 = algebraMap F K d := by
    apply (algebraMap K Ω).injective
    rw [map_pow, hy, hδ, ← IsScalarTower.algebraMap_apply]
  have hle : (minpoly F δ).natDegree ≤ 2 := by
    have hm : (Polynomial.X ^ 2 - Polynomial.C d : Polynomial F).Monic :=
      Polynomial.monic_X_pow_sub_C d (by norm_num)
    have h1 := minpoly.min F δ hm (by simp [hδ])
    have h2 := Polynomial.natDegree_le_natDegree h1
    rwa [Polynomial.natDegree_X_pow_sub_C _] at h2
  have hne : (minpoly F δ).natDegree ≠ 1 := by
    intro h
    obtain ⟨c, hc⟩ := (minpoly.natDegree_eq_one_iff).1 h
    have hcd : c ^ 2 = d := by
      apply (algebraMap F Ω).injective
      rw [map_pow, hc, hδ]
    let w : InfinitePlace F := Classical.arbitrary _
    have h3 := hd (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w))
    rw [← hcd, map_pow] at h3
    exact absurd h3 (not_lt.2 (sq_nonneg _))
  have hpos := minpoly.natDegree_pos hint
  have hdeg : (minpoly F δ).natDegree = 2 := by omega
  have hrk : Module.finrank F K = 2 := by
    rw [← hdeg]; exact IntermediateField.adjoin.finrank hint
  haveI : IsTotallyComplex K := by
    refine ⟨fun w => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex]
    intro hw
    have h3 := hd ((InfinitePlace.embedding_of_isReal hw).comp (algebraMap F K))
    rw [RingHom.comp_apply, ← hy2, map_pow] at h3
    exact absurd h3 (not_lt.2 (sq_nonneg _))
  haveI : Algebra.IsQuadraticExtension F K := { finrank_eq_two' := hrk }
  exact ⟨⟨K, inferInstance, IsCMField.ofCMExtension F K, hrk⟩, rfl⟩

end GlobalTheory.ExSplitCM

open GlobalTheory.ExSplitCM in
theorem GlobalTheory.RealGal.exists_infinite_qcm_split_ram : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (T : HeightOneSpectrum (𝓞 F) → Prop), (∀ᶠ u in Filter.cofinite, T u) → ∀ (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), IsPlaceOver A v → {Q : QCM F Ω | Dec (F := F) A ≤ (res F Ω ↥Q.K).range ∧ ∃ (u : HeightOneSpectrum (𝓞 F)) (A' : ValuationSubring Ω), T u ∧ IsPlaceOver A' u ∧ ¬ Ine (F := F) A' ≤ (res F Ω ↥Q.K).range}.Infinite := by
  intro F Ω _ _ _ _ _ _ T hT v A hA
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have halg : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  obtain ⟨q, hq, hqv⟩ := exists_prime_mem v
  haveI : Fact q.Prime := ⟨hq⟩
  have hsq : ∀ p : ℕ, ∃ δ : Ω, δ ^ 2 = -(p : Ω) := fun p =>
    IsAlgClosed.exists_pow_nat_eq (-(p : Ω)) two_pos
  choose δ hδ using hsq
  let Good : Set ℕ := {p | p.Prime ∧ IsSquare (-(p : ℚ_[q])) ∧ p ≠ 2 ∧ ¬ (p : ℤ) ∣ discr F ∧
    ∀ u : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ u.asIdeal → T u}
  have hGood : Good.Infinite := by
    have hbad : ({2} ∪ {p : ℕ | p ∣ (discr F).natAbs} ∪
        {p : ℕ | p.Prime ∧ ∃ u ∈ {u : HeightOneSpectrum (𝓞 F) | ¬ T u}, ((p : ℕ) : 𝓞 F) ∈ u.asIdeal}).Finite := by
      refine ((Set.finite_singleton 2).union ?_).union (finite_primes_of_finite (Filter.eventually_cofinite.1 hT))
      exact (Nat.divisors (discr F).natAbs).finite_toSet.subset fun p hp =>
        Nat.mem_divisors.2 ⟨hp, Int.natAbs_ne_zero.2 (discr_ne_zero F)⟩
    refine ((_root_.GlobalTheory.RealGal.PrimesNegSquare.infinite_primes_neg_isSquare q).diff hbad).mono ?_
    rintro p ⟨⟨hp, hs⟩, hn⟩
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, not_or, not_and, not_exists] at hn
    refine ⟨hp, hs, hn.1.1, fun h => hn.1.2 (Int.natCast_dvd.1 h), fun u hu => ?_⟩
    by_contra hTu
    exact hn.2 hp u hTu hu
  have hQ : ∀ p ∈ Good, ∃ Q : QCM F Ω, Q.K = IntermediateField.adjoin F {δ p} := by
    intro p hp
    refine exists_qcm (-(p : F)) (δ p) (by simp [hδ p]) fun φ => ?_
    simp only [map_neg, map_natCast, neg_lt_zero]
    exact_mod_cast hp.1.pos
  have hmove : ∀ p ∈ Good, ∀ Q : QCM F Ω, Q.K = IntermediateField.adjoin F {δ p} →
      ∀ (u : HeightOneSpectrum (𝓞 F)) (A' : ValuationSubring Ω), ((p : ℕ) : 𝓞 F) ∈ u.asIdeal →
        IsPlaceOver A' u → ¬ Ine (F := F) A' ≤ (res F Ω ↥Q.K).range := by
    intro p hp Q hQK u A' hu hA' hle
    obtain ⟨s, hs, hne⟩ := GlobalTheory.T.inertia_moves_square_root F Ω p hp.1 hp.2.2.1 hp.2.2.2.1 (δ p) (hδ p) u A' hu hA'
    refine hne ((mem_range_res_iff Q.K s).1 (hle hs) (δ p) ?_)
    rw [hQK]
    exact IntermediateField.mem_adjoin_simple_self F (δ p)
  have hmem : ∀ p ∈ Good, ∀ Q : QCM F Ω, Q.K = IntermediateField.adjoin F {δ p} →
      Q ∈ {Q : QCM F Ω | Dec (F := F) A ≤ (res F Ω ↥Q.K).range ∧ ∃ (u : HeightOneSpectrum (𝓞 F)) (A' : ValuationSubring Ω), T u ∧ IsPlaceOver A' u ∧ ¬ Ine (F := F) A' ≤ (res F Ω ↥Q.K).range} := by
    intro p hp Q hQK
    refine ⟨fun s hs => ?_, ?_⟩
    · rw [mem_range_res_iff, hQK]
      refine fix_adjoin (halg.isAlgebraic (δ p)).isIntegral s ?_
      exact GlobalTheory.T.decomposition_fixes_square_root F Ω v A hA q hqv (-(p : ℤ)) (δ p) (by push_cast; exact hδ p)
        (by push_cast; exact hp.2.1) s hs
    · obtain ⟨u, hu⟩ := exists_mem_of_prime (F := F) hp.1
      obtain ⟨A', hA'⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω u
      exact ⟨u, A', hp.2.2.2.2 u hu, hA', hmove p hp Q hQK u A' hu hA'⟩
  intro hfin
  apply hGood
  refine (hfin.biUnion (t := fun Q : QCM F Ω => {p : ℕ | p.Prime ∧ ∃ u ∈ {u : HeightOneSpectrum (𝓞 F) |
      ¬ ∀ A' : ValuationSubring Ω, IsPlaceOver A' u → Ine (F := F) A' ≤ (res F Ω ↥Q.K).range},
      ((p : ℕ) : 𝓞 F) ∈ u.asIdeal})
    fun Q _ => finite_primes_of_finite (Filter.eventually_cofinite.1 (UpperTheory.cm_inertia_restriction_holds F ↥Q.K Ω))).subset ?_
  intro p hp
  obtain ⟨Q, hQK⟩ := hQ p hp
  refine Set.mem_biUnion (hmem p hp Q hQK) ⟨hp.1, ?_⟩
  obtain ⟨u, hu⟩ := exists_mem_of_prime (F := F) hp.1
  obtain ⟨A', hA'⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω u
  exact ⟨u, fun hall => hmove p hp Q hQK u A' hu hA' (hall A' hA'), hu⟩
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.MemRangeResIff
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RealGalCompat

theorem mem_range_res_iff {K M Ω : Type} [Field K] [Field M] [Field Ω] [Algebra K M] [Algebra K Ω] [Algebra M Ω]
    [IsScalarTower K M Ω] (x : G K Ω) :
    x ∈ (res K Ω M).range ↔ ∀ m : M, x (algebraMap M Ω m) = algebraMap M Ω m := by
  constructor
  · rintro ⟨y, rfl⟩ m
    exact y.commutes m
  · intro h
    refine ⟨{ x.toRingEquiv with commutes' := fun m => h m }, ?_⟩
    ext z
    rfl

theorem range_res_normal {F K M Ω : Type} [Field F] [Field K] [Field M] [Field Ω] [Algebra F K] [Algebra F M]
    [Algebra F Ω] [Algebra K M] [Algebra K Ω] [Algebra M Ω] [IsScalarTower F K Ω] [IsScalarTower F M Ω]
    [IsScalarTower K M Ω] [Normal F M] : (res K Ω M).range.Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_range_res_iff] at hn ⊢
  intro m
  obtain ⟨m', hm'⟩ : ∃ m' : M, algebraMap M Ω m' = g⁻¹ (algebraMap M Ω m) :=
    ⟨((AlgEquiv.restrictScalars F (g⁻¹ : G K Ω)).toAlgHom).restrictNormal M m,
      AlgHom.restrictNormal_commutes _ _ _⟩
  show g (n (g⁻¹ (algebraMap M Ω m))) = algebraMap M Ω m
  rw [← hm', hn m', hm', ← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

end GlobalTheory.RealGalCompat

open GlobalTheory.RealGalCompat in
theorem GlobalTheory.RealGalCompat.trace_eq : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (Q Q' : QCM F Ω) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : TR.CuspSub F a) (r : G ↥Q.K Ω →* GL (Fin a) (Qbar l)) (r' : G ↥Q'.K Ω →* GL (Fin a) (Qbar l)), Continuous r → Continuous r' → IsSSRep r → IsSSRep r' → AttRes π ι ↥Q.K r → AttRes π ι ↥Q'.K r' → ∀ (s : G ↥Q.K Ω) (s' : G ↥Q'.K Ω), res F Ω ↥Q.K s = res F Ω ↥Q'.K s' → ((r s : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace = ((r' s' : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace := by
  intro F Ω _ _ _ _ _ _ Q Q' l _ ι a π r r' hr hr' hs hs' ha ha' s s' hss
  let M : IntermediateField F Ω := Q.K ⊔ Q'.K
  haveI : FiniteDimensional F Q.K := Module.finite_of_finrank_pos (by rw [Q.two]; norm_num)
  haveI : FiniteDimensional F Q'.K := Module.finite_of_finrank_pos (by rw [Q'.two]; norm_num)
  haveI : NumberField M := NumberField.of_module_finite F M
  haveI : IsAlgClosure M Ω := ⟨IsAlgClosure.isAlgClosed F,
    haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic; Algebra.IsAlgebraic.tower_top (K := F) _⟩
  haveI : Algebra.IsQuadraticExtension F Q.K := { finrank_eq_two' := Q.two }
  haveI : Algebra.IsQuadraticExtension F Q'.K := { finrank_eq_two' := Q'.two }
  haveI : Normal F M := IntermediateField.normal_sup F Ω Q.K Q'.K
  letI : Algebra Q.K M := (IntermediateField.inclusion (le_sup_left : Q.K ≤ M)).toRingHom.toAlgebra
  letI : Algebra Q'.K M := (IntermediateField.inclusion (le_sup_right : Q'.K ≤ M)).toRingHom.toAlgebra
  haveI : IsScalarTower F Q.K M := IsScalarTower.of_algebraMap_eq fun x => ((IntermediateField.inclusion _).commutes x).symm
  haveI : IsScalarTower F Q'.K M := IsScalarTower.of_algebraMap_eq fun x => ((IntermediateField.inclusion _).commutes x).symm
  haveI : IsScalarTower Q.K M Ω := IsScalarTower.of_algebraMap_eq fun x => rfl
  haveI : IsScalarTower Q'.K M Ω := IsScalarTower.of_algebraMap_eq fun x => rfl

  have hA := _root_.GlobalTheory.AttResTower.attRes_comp_res F Ω Q.K M l ι a π r ha
  have hA' := _root_.GlobalTheory.AttResTower.attRes_comp_res F Ω Q'.K M l ι a π r' ha'
  have hS := UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ a r (res Q.K Ω M) (range_res_normal (F := F)) hs
  have hS' := UpperTheory.semisimple_restriction_to_normal_subgroup _ _ _ a r' (res Q'.K Ω M) (range_res_normal (F := F)) hs'
  have hC := hr.comp (UpperTheory.V.Af.continuous_restrictScalarsHom Q.K M Ω)
  have hC' := hr'.comp (UpperTheory.V.Af.continuous_restrictScalarsHom Q'.K M Ω)
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.AttUniq.attRes_repIso F Ω M l ι a π _ _ hC hC' hS hS' hA hA'

  set σ : G F Ω := res F Ω Q.K s with hσ
  have hfix : σ ∈ M.fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup, Subgroup.mem_inf]
    refine ⟨fun x => ?_, fun x => ?_⟩
    · exact s.commutes x
    · rw [hss]; exact s'.commutes x
  let t : G M Ω := IntermediateField.fixingSubgroupEquiv M ⟨σ, hfix⟩
  have ht : res Q.K Ω M t = s := by ext z; rfl
  have ht' : res Q'.K Ω M t = s' := by
    ext z
    exact congrArg (fun u : G F Ω => u z) hss
  have e := hg t
  simp only [MonoidHom.comp_apply, ht, ht'] at e
  rw [e, Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mul]
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.RestrictGaloisConjugate
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RealGal.TrInv

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (K : Type) [Field K] [Algebra F K] [Algebra K Ω]
  [IsScalarTower F K Ω] [Normal F K]

def galoisConjugate (g : G F Ω) (t : G K Ω) : G K Ω :=
  AlgEquiv.ofRingEquiv (f := ((g * res F Ω K t * g⁻¹ : G F Ω) : Ω ≃+* Ω)) (fun x => by
    obtain ⟨y, hy⟩ : ∃ y : K, (g⁻¹ : G F Ω) (algebraMap K Ω x) = algebraMap K Ω y :=
      ⟨(g⁻¹ : G F Ω).restrictNormal K x, (AlgEquiv.restrictNormal_commutes _ K x).symm⟩
    change g ((res F Ω K t) ((g⁻¹ : G F Ω) (algebraMap K Ω x))) = algebraMap K Ω x
    rw [hy]
    change g (t (algebraMap K Ω y)) = algebraMap K Ω x
    rw [t.commutes, ← hy]
    change (g * g⁻¹) (algebraMap K Ω x) = _
    simp)

theorem restrict_galois_conjugate (g : G F Ω) (t : G K Ω) : res F Ω K (galoisConjugate K g t) = g * res F Ω K t * g⁻¹ := by
  ext z; rfl

theorem galois_conjugate_apply (g : G F Ω) (t : G K Ω) (z : Ω) : galoisConjugate K g t z = g (t (g⁻¹ z)) := rfl

def conj (g : G F Ω) : G K Ω →* G K Ω where
  toFun := galoisConjugate K g
  map_one' := by ext z; simp [galois_conjugate_apply]
  map_mul' s t := by ext z; simp [galois_conjugate_apply, AlgEquiv.mul_apply]

theorem res_conj (g : G F Ω) (t : G K Ω) : res F Ω K (conj K g t) = g * res F Ω K t * g⁻¹ := restrict_galois_conjugate K g t

theorem conj_surjective (g : G F Ω) : Function.Surjective (conj K g) := by
  intro u
  refine ⟨conj K g⁻¹ u, ?_⟩
  ext z
  simp [conj, galois_conjugate_apply]

theorem res_injective : Function.Injective (res F Ω K) := AlgEquiv.restrictScalars_injective F

end GlobalTheory.RealGal.TrInv

end

noncomputable section

namespace GlobalTheory.RealGal.TrInv

theorem continuous_conj {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [CharZero F] [Algebra F K] [Algebra K Ω]
    [IsScalarTower F K Ω] [IsAlgClosure K Ω] [Normal F K] (g : G F Ω) : Continuous (conj K g) := by
  haveI : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap F K).injective
  haveI : Algebra.IsAlgebraic K Ω := IsAlgClosure.isAlgebraic
  haveI : IsGalois K Ω := inferInstance
  haveI : T2Space (G F Ω) := krullTopology_t2
  have hc : Continuous (res F Ω K) := UpperTheory.V.Af.continuous_restrictScalarsHom F K Ω
  have he := hc.isClosedEmbedding (res_injective (F := F) (Ω := Ω) K)
  rw [he.isEmbedding.continuous_iff]
  have : (res F Ω K) ∘ (conj K g) = fun t => g * res F Ω K t * g⁻¹ := funext (res_conj K g)
  rw [this]
  exact (continuous_const.mul hc).mul continuous_const

theorem isSSRep_comp {Γ k : Type} [Group Γ] [Field k] {a : ℕ} (r : Γ →* GL (Fin a) k) (c : Γ →* Γ)
    (hc : Function.Surjective c) (hr : IsSSRep r) : IsSSRep (r.comp c) := by
  intro W hW
  have hW' : IsInv r W := by
    intro s v hv
    obtain ⟨t, rfl⟩ := hc s
    exact hW t v hv
  obtain ⟨W', h1, h2⟩ := hr W hW'
  exact ⟨W', fun t v hv => h1 (c t) v hv, h2⟩

end GlobalTheory.RealGal.TrInv

namespace GlobalTheory.RealGal


open TrInv in
theorem trace_conj_of_attRes : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω], Module.finrank F K = 2 → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : TR.CuspSub F a) (r : G K Ω →* GL (Fin a) (Qbar l)), Continuous r → IsSSRep r → AttRes π ι K r → ∀ (g : G F Ω) (s s' : G K Ω), res F Ω K s' = g * res F Ω K s * g⁻¹ → ((r s' : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace = ((r s : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace := by
  intro F Ω _ _ _ _ _ _ K _ _ _ _ _ _ h2 l _ ι a π r hr hss hatt g s s' hs
  haveI : Algebra.IsQuadraticExtension F K := ⟨h2⟩
  haveI : Normal F K := Algebra.IsQuadraticExtension.normal F K
  have hsur := conj_surjective (F := F) (Ω := Ω) K g
  have hatt' : AttRes π ι K (r.comp (conj K g)) :=
    GlobalTheory.T.attached_rep_conjugate_invariant F Ω K l ι a π r g (conj K g) (res_conj K g) hsur hatt
  obtain ⟨h, hh⟩ := _root_.GlobalTheory.AttUniq.attRes_repIso F Ω K l ι a π r (r.comp (conj K g)) hr (hr.comp (continuous_conj K g)) hss
    (isSSRep_comp r _ hsur hss) hatt hatt'
  have hs' : s' = conj K g s := res_injective (F := F) (Ω := Ω) K (by rw [hs, res_conj])
  subst hs'
  rw [← MonoidHom.comp_apply, hh s]
  simp only [Units.val_mul]
  rw [Matrix.trace_mul_cycle]
  simp

end GlobalTheory.RealGal

end
end

