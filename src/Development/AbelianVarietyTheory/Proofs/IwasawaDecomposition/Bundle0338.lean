module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0296
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0287
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0174
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0327
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapSplit
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.FiniteIntertwining
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0320

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AevalWeightedHomogeneousChernMemChernCoefficient
section
set_option autoImplicit false

open MvPolynomial GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.GoodMetric.ChernSpan GlobalTheory.GoodMetric.PolyRep
open scoped Matrix

namespace GlobalTheory.GoodMetric.ChernSpan

theorem one_mem_trSpan_zero {ι : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S] :
    (1 : Mat m S → S) ∈ TrSpan m 0 S := by
  unfold TrSpan
  exact Submodule.subset_span ⟨[], by simp, by simp, by funext A; simp [trProd]⟩

theorem pow_mem_trSpan {ι : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (w : ℕ)
    (f : Mat m S → S) (hf : f ∈ TrSpan m w S) (e : ℕ) : f ^ e ∈ TrSpan m (e * w) S := by
  induction e with
  | zero => simpa using one_mem_trSpan_zero m S
  | succ k ih =>
    rw [pow_succ, Nat.succ_mul]
    exact _root_.GlobalTheory.GoodMetric.ChernSpan.trSpan_mul m S (k * w) w _ _ ih hf

theorem prod_mem_trSpan {ι κ : Type} (m : ι → ℕ) (S : Type) [CommRing S] [Algebra ℝ S] (s : Finset κ)
    (w : κ → ℕ) (f : κ → Mat m S → S) (hf : ∀ x ∈ s, f x ∈ TrSpan m (w x) S) :
    ∏ x ∈ s, f x ∈ TrSpan m (∑ x ∈ s, w x) S := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using one_mem_trSpan_zero m S
  · intro a t ha ih hf
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact _root_.GlobalTheory.GoodMetric.ChernSpan.trSpan_mul m S _ _ _ _ (hf a (Finset.mem_insert_self a t))
      (ih fun x hx => hf x (Finset.mem_insert_of_mem hx))

theorem trSpan_le_reach {ι : Type} [Fintype ι] (m : ι → ℕ) (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S] :
    TrSpan m n S ≤ Reach m n S := by
  unfold TrSpan
  rw [Submodule.span_le]
  rintro f ⟨l, hl, hs, rfl⟩
  exact GlobalTheory.T.tracePowerListProduct_mem_chernCoefficientRealSpan m n S l hl hs

theorem aeval_chern_mem_reach {ι : Type} [Fintype ι] (m : ι → ℕ) (n : ℕ) (S : Type) [CommRing S] [Algebra ℝ S]
    (R : MvPolynomial (ι × ℕ) ℝ) (hR : R.IsWeightedHomogeneous (Prod.snd : ι × ℕ → ℕ) n) :
    (fun A : Mat m S => aeval (fun x : ι × ℕ => (Matrix.charpolyRev (-(A x.1))).coeff x.2) R) ∈ Reach m n S := by
  refine trSpan_le_reach m n S ?_

  have key : ∀ d ∈ R.support, (fun A : Mat m S =>
      aeval (fun x : ι × ℕ => (Matrix.charpolyRev (-(A x.1))).coeff x.2) (monomial d (R.coeff d)))
        ∈ TrSpan m n S := by
    intro d hd
    have hdeg : Finsupp.weight Prod.snd d = n := hR (mem_support_iff.mp hd)
    have hprod := prod_mem_trSpan m S d.support (fun x => d x * x.2)
      (fun x (A : Mat m S) => (Matrix.charpolyRev (-(A x.1))).coeff x.2 ^ d x)
      (fun x _ => pow_mem_trSpan m S x.2 _ (_root_.GlobalTheory.GoodMetric.ChernSpan.coeff_charpolyRev_mem_trSpan m S x.1 x.2) (d x))
    have hw : ∑ x ∈ d.support, d x * x.2 = n := by
      rw [← hdeg, Finsupp.weight_apply, Finsupp.sum]
      simp [smul_eq_mul]
    rw [hw] at hprod
    convert Submodule.smul_mem _ (R.coeff d) hprod using 1
    funext A
    simp [aeval_monomial, Finsupp.prod, Finset.prod_apply, Algebra.smul_def]
  have hsum : (fun A : Mat m S => aeval (fun x : ι × ℕ => (Matrix.charpolyRev (-(A x.1))).coeff x.2) R) =
      ∑ d ∈ R.support, fun A : Mat m S =>
        aeval (fun x : ι × ℕ => (Matrix.charpolyRev (-(A x.1))).coeff x.2) (monomial d (R.coeff d)) := by
    funext A
    conv_lhs => rw [R.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Finset.sum_apply]
  rw [hsum]
  exact Submodule.sum_mem _ key

end GlobalTheory.GoodMetric.ChernSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharZeroFractionRingCoefficientRing
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.HeightCounting.FracCharZero

theorem injective_of_finite_dvr {A B : Type} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B] :
    Function.Injective (algebraMap A B) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  by_contra hne
  push_neg at hne
  obtain ⟨a, ha, ha0⟩ := hne
  have hker : (⊥ : Ideal B).comap (algebraMap A B) ≠ ⊥ := by
    intro h
    apply ha0
    have : a ∈ (⊥ : Ideal B).comap (algebraMap A B) := by simp [Ideal.mem_comap, ha]
    rw [h] at this
    simpa using this
  have hmax : ((⊥ : Ideal B).comap (algebraMap A B)).IsMaximal :=
    Ideal.IsPrime.isMaximal inferInstance hker
  have hbot : (⊥ : Ideal B).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := A) ⊥ hmax
  exact IsDiscreteValuationRing.not_a_field B (IsLocalRing.eq_maximalIdeal hbot).symm

theorem charZero_of_injective {R S : Type*} [NonAssocSemiring R] [NonAssocSemiring S] [CharZero R]
    (f : R →+* S) (hf : Function.Injective f) : CharZero S :=
  ⟨fun m n h => by
    have : f (m : R) = f (n : R) := by simpa [map_natCast] using h
    exact Nat.cast_injective (hf this)⟩

end GlobalTheory.HeightCounting.FracCharZero

namespace GlobalTheory.HeightCounting

theorem TwR.charZero_fractionRing_O : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw),
    CharZero (FractionRing (T.O i)) := by
  intro D T i
  have h1 : Function.Injective (algebraMap ℤ_[T.l i] (T.O0 i)) :=
    FracCharZero.injective_of_finite_dvr
  have h2 := T.O_inj i
  have h3 := IsFractionRing.injective (T.O i) (FractionRing (T.O i))
  exact FracCharZero.charZero_of_injective
    (((algebraMap (T.O i) (FractionRing (T.O i))).comp (algebraMap (T.O0 i) (T.O i))).comp
      (algebraMap ℤ_[T.l i] (T.O0 i))) (h3.comp (h2.comp h1))

end GlobalTheory.HeightCounting
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChosenHalfSplitPlacesMeetsConjugatePairOnce
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ChosenHalf

theorem isConjPl_unique (D : D7) {P w w' : PlE D.host} (h : IsConjPl D.host P w) (h' : IsConjPl D.host P w') :
    w = w' := by
  apply HeightOneSpectrum.ext
  ext y
  obtain ⟨x, hx⟩ := (RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv).surjective y
  have hy : (y : D.host.E) = D.host.conj (x : D.host.E) := by
    rw [← hx]; rfl
  rw [← h x y hy, ← h' x y hy]

theorem not_isConjPl_self (D : D7) {P : PlE D.host} (hs : IsSplitPl D.host P) : ¬ IsConjPl D.host P P := by
  intro hc
  obtain ⟨x, hx, hy⟩ := hs
  have hyx : ((RingOfIntegers.mapRingEquiv D.host.conj.toRingEquiv x : 𝓞 D.host.E) : D.host.E) =
      D.host.conj (x : D.host.E) := rfl
  exact hy _ hyx ((hc x _ hyx).1 hx)

theorem overPl_unique (D : D7) {P : PlE D.host} {v v' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))}
    (h : NG.OverPl P v) (h' : NG.OverPl P v') : v = v' :=
  HeightOneSpectrum.ext (h.symm.trans h')

theorem qpOf_half : ∀ (D : D7) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host), (∀ v, NG.OverPl (Pq v) v) →
    ∀ S : Finset (PlE D.host), (∀ P ∈ S, IsSplitPl D.host P) →
    (∀ P ∈ S, ∃ P' ∈ qpOf D Pq S, P' = P ∨ IsConjPl D.host P P') ∧ ∀ P ∈ qpOf D Pq S, ∀ P' ∈ qpOf D Pq S, ¬ IsConjPl D.host P P' := by
  classical
  intro D Pq hPq S hS
  have pair := _root_.GlobalTheory.PlacePair.comap_eq_iff D
  have memq : ∀ P, P ∈ qpOf D Pq S ↔ P ∈ S ∧ ∀ v, NG.OverPl P v → P = Pq v ∨ Pq v ∉ S := by
    intro P
    unfold qpOf
    rw [Finset.mem_filter]
  refine ⟨fun P hP => ?_, fun P hP P' hP' hc => ?_⟩
  · by_cases hq : P ∈ qpOf D Pq S
    · exact ⟨P, hq, Or.inl rfl⟩
    · have hn : ¬ ∀ v, NG.OverPl P v → P = Pq v ∨ Pq v ∉ S := fun h => hq ((memq P).2 ⟨hP, h⟩)
      push_neg at hn
      obtain ⟨v, hv, -, hin⟩ := hn
      refine ⟨Pq v, (memq _).2 ⟨hin, fun v' hv' => Or.inl ?_⟩, ?_⟩
      · rw [overPl_unique D (hPq v) hv']
      · rcases (pair P (Pq v)).1 (hv.trans (hPq v).symm) with h | h
        · exact Or.inl h.symm
        · exact Or.inr h
  · have hPS := ((memq P).1 hP).1
    have hP'S := ((memq P').1 hP').1
    let v := HeightOneSpectrum.under (𝓞 (maximalRealSubfield D.host.E)) P
    have hv : NG.OverPl P v := rfl
    have hv' : NG.OverPl P' v := ((pair P P').2 (Or.inr hc)).symm.trans hv
    have hqS : Pq v ∈ S := by
      rcases (pair P (Pq v)).1 (hv.trans (hPq v).symm) with h | h
      · rw [← h]; exact hPS
      · rw [← isConjPl_unique D hc h]; exact hP'S
    have e1 := qpOf_eq D Pq S hP hv hqS
    have e2 := qpOf_eq D Pq S hP' hv' hqS
    have e : P' = P := e2.trans e1.symm
    rw [e] at hc
    exact not_isConjPl_self D (hS P hPS) hc

end GlobalTheory.ChosenHalf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmTypeEmbeddingAtSideDistinctNonconjugate
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.HeightCounting.FormsStep

theorem complexConj_eq_hostConj (D : D7) (x : D.host.E) : IsCMField.complexConj D.host.E x = D.host.conj x := by
  apply D.host.φ₀.injective
  rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]

theorem kEmbT_cmDist : ∀ (D : D7) (T : TwR D.LL0 D.nd) (i : T.Tw) (b : Bool), GlobalTheory.AlgWtF.CMDist (kEmbT D T i b) := by
  intro D T i b
  have hR : Function.Injective ((readT D T i b).comp (Formalism.L2.NX.embEL0 D)) := RingHom.injective _
  have hS : ∀ g h : D.R.GG, (∀ x : D.host.E, D.host.sigmaOf g x = D.host.sigmaOf h x) → g = h := by
    intro g h e
    exact Formalism.MainNotions.Gaps.LevGap.sigmaOf_injective D.host (AlgEquiv.ext e)
  have hk : ∀ t x, kEmbT D T i b t x =
      ((readT D T i b).comp (Formalism.L2.NX.embEL0 D)) (D.host.sigmaOf ((D.eTau t : D.R.Psi) : D.R.GG) x) :=
    fun _ _ => rfl
  refine ⟨?_, ?_⟩
  · intro t t' e
    apply D.eTau.injective
    apply Subtype.ext
    apply hS
    intro x
    apply hR
    rw [← hk, ← hk, e]
  · intro t t' e
    have h1 : ((D.eTau t : D.R.Psi) : D.R.GG) =
        ((D.eTau t' : D.R.Psi) : D.R.GG) * D.R.cc := by
      apply hS
      intro x
      apply hR
      rw [← hk, Formalism.MainNotions.Gaps.LevGap.sigmaOf_mul, AlgEquiv.mul_apply, ← Formalism.MainNotions.Gaps.LevGap.conj_eq_sigmaOf,
        ← complexConj_eq_hostConj D x]
      exact DFunLike.congr_fun e x
    have ht : ((D.eTau t : D.R.Psi) : D.R.GG).1.2 = 1 := (Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau t).2
    have ht' : ((D.eTau t' : D.R.Psi) : D.R.GG).1.2 = 1 := (Formalism.HC.Frame.mem_Psi_iff _).1 (D.eTau t').2
    have h2 : ((D.eTau t : D.R.Psi) : D.R.GG).1.2 =
        ((D.eTau t' : D.R.Psi) : D.R.GG).1.2 * (-1) := by rw [h1]; rfl
    rw [ht, ht'] at h2
    exact absurd h2 (by decide)

end GlobalTheory.HeightCounting.FormsStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientSpaceStableEqBotOrTop
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX
  GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.TensorIrr

open Formalism.L2.DIV

section General

variable {K : Type} [Field K] {n : ℕ}

def bSq (lam : DomWeight n) : Module.Basis (Formalism.GradedWeylDivisibility.ssIdx n n lam.natW) K (nablaSq K n lam) :=
  (Module.Basis.span (Formalism.GradedWeylDivisibility.sSBasis K n n lam.natW).choose_spec.1.1).map
    (LinearEquiv.ofEq _ _ (Formalism.GradedWeylDivisibility.sSBasis K n n lam.natW).choose_spec.1.2.1)

theorem bSq_coe (lam : DomWeight n) (k : Formalism.GradedWeylDivisibility.ssIdx n n lam.natW) :
    ((bSq (K := K) lam k : nablaSq K n lam) : MvPolynomial (Fin n × Fin n) K) = ssB K lam.natW k := by
  simp [bSq, Module.Basis.span_apply, ssB]
  rfl

theorem ssB_mem (lam : DomWeight n) (k : Formalism.GradedWeylDivisibility.ssIdx n n lam.natW) : ssB K lam.natW k ∈ nablaSq K n lam :=
  bSq_coe (K := K) lam k ▸ (bSq (K := K) lam k).2

theorem sqAct_one_of_mem (lam : DomWeight n) {f : MvPolynomial (Fin n × Fin n) K} (hf : f ∈ nablaSq K n lam) :
    sqAct K n lam 1 f = f :=
  congrArg Subtype.val (LinearMap.congr_fun (GlobalTheory.Branching.sqRep K n lam).map_one ⟨f, hf⟩)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

def tenAt (f : ι → MvPolynomial (Fin n × Fin n) K) (τ₀ : ι) : MvPolynomial (Fin n × Fin n) K →ₗ[K] Pol K ι n :=
  LinearMap.mulLeft K (∏ τ ∈ Finset.univ.erase τ₀, Formalism.GradedWeylDivisibility.blockEmb K τ (f τ)) ∘ₗ
    (Formalism.GradedWeylDivisibility.blockEmb K (k := n) (n := n) τ₀).toLinearMap

theorem tenAt_apply (f : ι → MvPolynomial (Fin n × Fin n) K) (τ₀ : ι) (x : MvPolynomial (Fin n × Fin n) K) :
    tenAt f τ₀ x = ten (Function.update f τ₀ x) := by
  simp only [tenAt, ten, LinearMap.comp_apply, LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ τ₀), Function.update_self, mul_comm]
  congr 1
  refine Finset.prod_congr rfl fun τ hτ => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hτ)]

theorem ten_update_ssB (lam : ι → DomWeight n) (τ₀ : ι) (k : VVIdx lam) (l : Formalism.GradedWeylDivisibility.ssIdx n n (lam τ₀).natW) :
    ten (Function.update (fun τ => ssB K (lam τ).natW (k τ)) τ₀ (ssB K (lam τ₀).natW l)) =
      ((bVV K lam (Function.update k τ₀ l) : VV K lam) : Pol K ι n) := by
  rw [bVV_coe, bVVfun]
  congr 1
  funext τ
  exact (Function.apply_update (fun τ k => ssB K (lam τ).natW k) k τ₀ l τ).symm

theorem exists_op (lam : ι → DomWeight n) (τ₀ : ι) (φ : nablaSq K n (lam τ₀) →ₗ[K] nablaSq K n (lam τ₀))
    (hφ : ∃ (s : Finset (GL (Fin n) K)) (c : GL (Fin n) K → K), ∀ f : nablaSq K n (lam τ₀),
      (φ f : MvPolynomial (Fin n × Fin n) K) = ∑ g ∈ s, c g • sqAct K n (lam τ₀) g f)
    (W : Submodule K (VV K lam)) (hW : ∀ g : ι → GL (Fin n) K, ∀ w ∈ W, rhoK lam g w ∈ W) :
    ∃ T : VV K lam →ₗ[K] VV K lam, (∀ w ∈ W, T w ∈ W) ∧ ∀ k : VVIdx lam,
      ((T (bVV K lam k) : VV K lam) : Pol K ι n) =
        ten (Function.update (fun τ => ssB K (lam τ).natW (k τ)) τ₀
          (φ (bSq (lam τ₀) (k τ₀)) : MvPolynomial (Fin n × Fin n) K)) := by
  obtain ⟨s, c, hc⟩ := hφ
  refine ⟨∑ g ∈ s, c g • rhoK lam (Function.update 1 τ₀ g), ?_, ?_⟩
  · intro w hw
    rw [LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun g _ => by
      rw [LinearMap.smul_apply]
      exact W.smul_mem _ (hW _ _ hw)
  · intro k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hc, bSq_coe, ← tenAt_apply, map_sum, LinearMap.sum_apply, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, Submodule.coe_smul, map_smul]
    congr 1
    rw [rhoK_coe, bVV_coe, bVVfun, actTen K ι n lam _ _, tenAt_apply]
    congr 1
    funext τ
    by_cases h : τ = τ₀
    · subst h; simp
    · rw [Function.update_of_ne h, Function.update_of_ne h, Pi.one_apply, sqAct_one_of_mem _ (ssB_mem _ _)]

def elemOp (lam : DomWeight n) (a b : Formalism.GradedWeylDivisibility.ssIdx n n lam.natW) : nablaSq K n lam →ₗ[K] nablaSq K n lam :=
  ((bSq lam).coord a).smulRight (bSq lam b)

theorem exists_elem (lam : ι → DomWeight n)
    (H : ∀ τ, ∀ φ : nablaSq K n (lam τ) →ₗ[K] nablaSq K n (lam τ), ∃ (s : Finset (GL (Fin n) K)) (c : GL (Fin n) K → K),
      ∀ f : nablaSq K n (lam τ), (φ f : MvPolynomial (Fin n × Fin n) K) = ∑ g ∈ s, c g • sqAct K n (lam τ) g f)
    (W : Submodule K (VV K lam)) (hW : ∀ g : ι → GL (Fin n) K, ∀ w ∈ W, rhoK lam g w ∈ W)
    (τ₀ : ι) (a b : Formalism.GradedWeylDivisibility.ssIdx n n (lam τ₀).natW) :
    ∃ T : VV K lam →ₗ[K] VV K lam, (∀ w ∈ W, T w ∈ W) ∧ ∀ k : VVIdx lam,
      T (bVV K lam k) = if k τ₀ = a then bVV K lam (Function.update k τ₀ b) else 0 := by
  obtain ⟨T, hTW, hT⟩ := exists_op lam τ₀ (elemOp (lam τ₀) a b) (H τ₀ _) W hW
  refine ⟨T, hTW, fun k => Subtype.ext ?_⟩
  rw [hT k]
  have e : (elemOp (K := K) (lam τ₀) a b (bSq (lam τ₀) (k τ₀)) : MvPolynomial (Fin n × Fin n) K) =
      (if k τ₀ = a then (1 : K) else 0) • ssB K (lam τ₀).natW b := by
    simp only [elemOp, LinearMap.smulRight_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply, Submodule.coe_smul, bSq_coe]
  rw [e, ← tenAt_apply, map_smul, tenAt_apply, ten_update_ssB]
  split_ifs <;> simp

end General

theorem eq_bot_or_eq_top : ∀ (K : Type) [Field K] (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n),
    (∀ τ, ∀ φ : nablaSq K n (lam τ) →ₗ[K] nablaSq K n (lam τ), ∃ (s : Finset (GL (Fin n) K)) (c : GL (Fin n) K → K),
      ∀ f : nablaSq K n (lam τ), (φ f : MvPolynomial (Fin n × Fin n) K) = ∑ g ∈ s, c g • sqAct K n (lam τ) g f) →
    ∀ W : Submodule K (Formalism.L2.DIV.VV K lam), (∀ g : ι → GL (Fin n) K, ∀ w ∈ W, Formalism.L2.DIV.rhoK lam g w ∈ W) →
      W = ⊥ ∨ W = ⊤ := by
  intro K _ ι _ n lam H W hW
  classical
  by_cases hW0 : W = ⊥
  · exact Or.inl hW0
  right
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  obtain ⟨i, hi⟩ : ∃ i, (bVV K lam).repr w i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hw0 ((bVV K lam).ext_elem fun k => by simp [h k])
  have hproj : ∀ S : Finset ι, (∑ k ∈ Finset.univ.filter (fun k : VVIdx lam => ∀ τ ∈ S, k τ = i τ),
      (bVV K lam).repr w k • bVV K lam k) ∈ W := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · have hf : Finset.univ.filter (fun k : VVIdx lam => ∀ τ ∈ (∅ : Finset ι), k τ = i τ) = Finset.univ := by
        ext k; simp
      rw [hf, (bVV K lam).sum_repr w]
      exact hw
    · intro a S ha ih
      obtain ⟨T, hTW, hT⟩ := exists_elem lam H W hW a (i a) (i a)
      have h1 := hTW _ ih
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at h1
      convert h1 using 1
      simp only [map_smul, hT]
      rw [Finset.sum_filter, Finset.sum_filter]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : k a = i a
      · have hu : Function.update k a (i a) = k := by rw [← hk, Function.update_eq_self]
        simp [hk, hu, Finset.forall_mem_insert]
      · simp [hk, Finset.forall_mem_insert]
  have hi' : bVV K lam i ∈ W := by
    have h := hproj Finset.univ
    have hf : Finset.univ.filter (fun k : VVIdx lam => ∀ τ ∈ (Finset.univ : Finset ι), k τ = i τ) = {i} := by
      ext k; simp [funext_iff]
    rw [hf, Finset.sum_singleton] at h
    have := W.smul_mem ((bVV K lam).repr w i)⁻¹ h
    rwa [smul_smul, inv_mul_cancel₀ hi, one_smul] at this
  have hall : ∀ j, bVV K lam j ∈ W := by
    intro j
    have key : ∀ S : Finset ι, bVV K lam (fun τ => if τ ∈ S then j τ else i τ) ∈ W := by
      intro S
      refine Finset.induction_on S ?_ ?_
      · simpa using hi'
      · intro a S ha ih
        obtain ⟨T, hTW, hT⟩ := exists_elem lam H W hW a (i a) (j a)
        have h1 := hTW _ ih
        rw [hT, if_pos (by simp [ha])] at h1
        convert h1 using 2
        funext τ
        by_cases h : τ = a
        · subst h; simp
        · simp [h, Function.update_of_ne h]
    simpa using key Finset.univ
  rw [eq_top_iff]
  intro x _
  rw [← (bVV K lam).sum_repr x]
  exact W.sum_mem fun k _ => W.smul_mem _ (hall k)

end GlobalTheory.TensorIrr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContragredientIsIrreducibleFiniteDimensional
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem contragredient_isIrreducible : ∀ (k : Type) [Field k] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V), ρ.IsIrreducible → ρ.dual.IsIrreducible := by
  intro k _ G _ V _ _ _ ρ hρ
  haveI : Nontrivial V := by
    by_contra hV
    rw [not_nontrivial_iff_subsingleton] at hV
    exact (bot_ne_top (α := Subrepresentation ρ))
      (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))
  have hdualNT : Nontrivial (Module.Dual k V) := inferInstance
  refine { toNontrivial := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · have h' := congrArg Subrepresentation.toSubmodule h
    obtain ⟨x, y, hxy⟩ := hdualNT
    have hx : x ∈ (⊤ : Subrepresentation ρ.dual).toSubmodule := Submodule.mem_top
    have hy : y ∈ (⊤ : Subrepresentation ρ.dual).toSubmodule := Submodule.mem_top
    rw [← h'] at hx hy
    exact hxy (((Submodule.mem_bot k).1 hx).trans ((Submodule.mem_bot k).1 hy).symm)
  · let T : Subrepresentation ρ := ⟨S.toSubmodule.dualCoannihilator, fun g v hv => by
      rw [Submodule.mem_dualCoannihilator] at hv ⊢
      intro φ hφ
      have h1 := hv _ (S.apply_mem_toSubmodule g⁻¹ hφ)
      simpa [Representation.dual_apply, Module.Dual.transpose_apply] using h1⟩
    have hST : S.toSubmodule = T.toSubmodule.dualAnnihilator :=
      (Subspace.dualCoannihilator_dualAnnihilator_eq (W := S.toSubmodule)).symm
    rcases hρ.eq_bot_or_eq_top T with hT | hT
    · right
      apply Subrepresentation.toSubmodule_injective
      rw [hST, hT]
      exact Submodule.dualAnnihilator_bot
    · left
      apply Subrepresentation.toSubmodule_injective
      rw [hST, hT]
      exact Submodule.dualAnnihilator_top

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertSatakeParametersEqOfIsoStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial Formalism.UG GlobalTheory.SatInd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertSatakeParameters_eq_of_iso : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (π π' : NG.AutRep L n), π.Iso π' → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), (∀ (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ h ∈ Hecke ℂ (KU Dv.σw n), Set.Finite {c : GAf L n ⧸ U | ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x ∧ Dv.hval h (Dv.loc x) ≠ 0}) → NG.SatAt π Dv α → NG.SatAt π' Dv α := by
  first | exact @GlobalTheory.SatIso.satAt_of_iso | exact GlobalTheory.SatIso.satAt_of_iso | (intros; apply GlobalTheory.SatIso.satAt_of_iso <;> assumption)
end

