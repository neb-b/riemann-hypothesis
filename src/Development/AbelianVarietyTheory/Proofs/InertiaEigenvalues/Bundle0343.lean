module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0322
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0324
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsDualDualRep
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0073
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverEta
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0323
public import Development.AbelianVarietyTheory.Definitions.Foundations.AbsCharNotUnitary
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
public import GroundTheory.GlobalFields.TateThesis.GlobalZetaFinite
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteH1PeriodDatum
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.TateFiniteH1

theorem tate_finH1 (hT : Formalism.GaloisCohomology.LocalTateDualityK) :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), TateFiniteness (P.PD K) := by
  intro l _ P K LL _ _ _ O _ _ hO A LA
  obtain ⟨hR, hRs⟩ := GlobalTheory.T.goodCoefficients_explicit_sums l LL O hO
  haveI : Module.Free O ↥LA.T := LA.free
  haveI : Module.Finite O ↥LA.T := Module.Finite.iff_fg.2 LA.fg
  obtain ⟨hTc, hTs⟩ := _root_.GlobalTheory.freeModule_adicComplete_separated ((l : ℕ) : O) hR hRs ↥LA.T
  have hmemT : ∀ c : ↥(latticeCocycles LA), ∀ g, (c : ↥(GK K) → A.V) g ∈ LA.T := fun c g =>
    (Submodule.mem_pi.1 (Submodule.mem_inf.1 c.2).2) g (Set.mem_univ g)
  have hd : ∀ t : ↥LA.T, ((cob A.ρ).restrictScalars O) (t : A.V) ∈ latticeCocycles LA := fun t => by
    refine Submodule.mem_inf.2 ⟨⟨?_, fun g h => ?_⟩, Submodule.mem_pi.2 fun g _ => ?_⟩
    · change Continuous fun g => A.ρ g (t : A.V) - (t : A.V)
      simp only [sub_eq_add_neg]
      exact (A.cont _).add continuous_const
    · change A.ρ (g * h) (t : A.V) - (t : A.V) = (A.ρ g (t : A.V) - (t : A.V)) + A.ρ g (A.ρ h (t : A.V) - (t : A.V))
      rw [map_mul, Module.End.mul_apply, map_sub]
      abel
    · change A.ρ g (t : A.V) - (t : A.V) ∈ LA.T
      exact LA.T.sub_mem (LA.stable g _ t.2) t.2
  let d : ↥LA.T →ₗ[O] ↥(latticeCocycles LA) :=
    LinearMap.codRestrict (latticeCocycles LA) (((cob A.ρ).restrictScalars O).comp LA.T.subtype) hd
  have hdN : LinearMap.range d ≤ (latticeCoboundaries LA).comap (latticeCocycles LA).subtype := by
    rintro _ ⟨t, rfl⟩
    exact ⟨t, t.2, rfl⟩
  have hZ : ∀ c : ↥(latticeCocycles LA), (∀ n : ℕ, ∃ z : ↥(latticeCocycles LA), c = ((l : ℕ) : O) ^ n • z) → c = 0 := by
    intro c hc
    apply Subtype.ext
    funext g
    have h0 := hTs ⟨_, hmemT c g⟩ fun n => by
      obtain ⟨z, hz⟩ := hc n
      refine ⟨⟨_, hmemT z g⟩, Subtype.ext ?_⟩
      change (c : ↥(GK K) → A.V) g = ((l : ℕ) : O) ^ n • (z : ↥(GK K) → A.V) g
      rw [hz]
      rfl
    exact congrArg Subtype.val h0
  obtain ⟨s, hs⟩ := GlobalTheory.T.latticeCocycles_finitelyGenerated_mod_prime hT l K LL O hO A LA
  refine _root_.GlobalTheory.finite_quotient_of_complete_nakayama ((l : ℕ) : O) hR hTc hZ d _ hdN s fun c => ?_
  obtain ⟨a, c', hm⟩ := hs c
  obtain ⟨x, hx, hxe⟩ := hm
  refine ⟨a, c', ⟨x, hx⟩, Subtype.ext ?_⟩
  have e : ((d ⟨x, hx⟩ : ↥(latticeCocycles LA)) : ↥(GK K) → A.V) = ((cob A.ρ).restrictScalars O) x := rfl
  simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, e, hxe]
  abel

end GlobalTheory.TateFiniteH1
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisActionExtendsToAinfDiscRings
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem dvd_σF_self {l : ℕ} [Fact l.Prime] (g : GQ l) (x : Per.Fl l) : x ∣ Per.σF g x := by
  apply GlobalTheory.TiltAlgClosed.dvd_of_untilt_dvd
  rw [GlobalTheory.RingBasics.untilt_σF]
  generalize x.untilt = y
  by_cases hy : (y : ℂ_[l]) = 0
  · obtain rfl : y = 0 := Subtype.ext hy
    simp
  · refine ⟨⟨Per.σC g y / y, (GlobalTheory.RingBasics.mem_OC _).2 ?_⟩, Subtype.ext ?_⟩
    · rw [norm_div, GlobalTheory.RingBasics.norm_σC, div_self (norm_ne_zero_iff.2 hy)]
    · rw [GlobalTheory.RingIface.sigO_coe]
      change Per.σC g y = (y : ℂ_[l]) * (Per.σC g y / y)
      field_simp

theorem galois_discMap : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K),
    (∀ g : GQ l, bk.ev X ∣ Per.σA g (bk.ev X)) ∧ ∀ (ρ : ℝ≥0), 0 < ρ → ∀ g : GQ l,
      ∃ G : bk.DA ρ →+* bk.DA ρ, IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA g) G := by
  intro l _ K bk
  have h : ∀ g : GQ l, bk.ev X ∣ Per.σA g (bk.ev X) := fun g => by
    rw [bk.ev_X, GlobalTheory.RingIface.sigA_teich]
    exact map_dvd (WittVector.teichmuller l) (dvd_σF_self g bk.flat)
  refine ⟨h, fun ρ hρ g => ⟨_, isDiscMap_map (Per.σA g) ?_⟩⟩
  obtain ⟨c, hc⟩ := h g
  have h1 := norm_toDisc_pow_le (l := l) (u := bk.ev X) 1 hρ
  rw [pow_one, pow_one] at h1
  rw [hc, map_mul]
  exact (norm_mul_le _ _).trans ((mul_le_mul h1 (norm_toDisc_le c) (norm_nonneg _) ρ.2).trans (mul_one _).le)

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisTransitiveOnRootsOfPrime
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem galois_transitive_on_roots_of_prime (l : ℕ) [Fact l.Prime] (K : FinExt l) (π : ↥(OL K))
    (hπ : Prime π) (n : ℕ) (y z : Om l) (hy : y ^ n = ((π : ↥K.1) : Om l))
    (hz : z ^ n = ((π : ↥K.1) : Om l)) (hn : 0 < n) : ∃ g : ↥(GK K), (g : GQ l) y = z := by
  classical

  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have : IsFractionRing ↥(OL K) ↥K.1 :=
    integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥K.1
  have : IsIntegrallyClosed ↥(OL K) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension ℚ_[l]
  have hn0 : n ≠ 0 := hn.ne'
  have hmon : (Polynomial.X ^ n - Polynomial.C π).Monic := Polynomial.monic_X_pow_sub_C π hn0

  have hirr : Irreducible (Polynomial.X ^ n - Polynomial.C π) := by
    refine Polynomial.irreducible_of_eisenstein_criterion
      ((Ideal.span_singleton_prime hπ.ne_zero).2 hπ) ?_ ?_ ?_ ?_ hmon.isPrimitive
    · rw [hmon.leadingCoeff]
      intro h
      exact hπ.not_isUnit (Ideal.span_singleton_eq_top.1 ((Ideal.eq_top_iff_one _).2 h))
    · intro m hm
      rw [Polynomial.degree_X_pow_sub_C hn π, Nat.cast_lt] at hm
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C, if_neg hm.ne]
      split_ifs
      · exact Ideal.sub_mem _ (Ideal.zero_mem _) (Ideal.mem_span_singleton_self π)
      · simp
    · rw [Polynomial.degree_X_pow_sub_C hn π]
      exact_mod_cast hn
    · rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C, if_neg hn0.symm,
        if_pos rfl, zero_sub, Ideal.span_singleton_pow, Ideal.neg_mem_iff, Ideal.mem_span_singleton]
      rintro ⟨c, hc⟩
      apply hπ.not_isUnit
      have h1 : π * 1 = π * (π * c) := by
        rw [mul_one, ← mul_assoc, ← pow_two]
        exact hc
      exact isUnit_of_dvd_one ⟨c, mul_left_cancel₀ hπ.ne_zero h1⟩

  have hirrF : Irreducible (Polynomial.X ^ n - Polynomial.C ((π : ↥K.1))) := by
    have h := (hmon.irreducible_iff_irreducible_map_fraction_map (K := ↥K.1)).1 hirr
    rwa [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C] at h
  have hmin : ∀ w : Om l, w ^ n = ((π : ↥K.1) : Om l) →
      minpoly (↥K.1) w = Polynomial.X ^ n - Polynomial.C ((π : ↥K.1)) := by
    intro w hw
    refine (minpoly.eq_of_irreducible_of_monic hirrF ?_ (Polynomial.monic_X_pow_sub_C _ hn0)).symm
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      IntermediateField.algebraMap_apply, hw, sub_self]

  have : Normal (↥K.1) (Om l) := Normal.tower_top_of_normal ℚ_[l] (↥K.1) (Om l)
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ↥K.1) (E := Om l)).1
    ((hmin z hz).trans (hmin y hy).symm)
  refine ⟨⟨σ.restrictScalars ℚ_[l], ?_⟩, hσ⟩
  show σ.restrictScalars ℚ_[l] ∈ IntermediateField.fixingSubgroup K.1
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  exact σ.commutes ⟨x, hx⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GreenbergWilesTotallyComplex
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel

namespace GlobalTheory.GWComplex

section Count

variable {R : Type*} [CommRing R] {A B C D E : Type*} [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] [AddCommGroup D] [Module R D]
  [AddCommGroup E] [Module R E]

theorem card_eq_ker_mul_range (f : A →ₗ[R] B) :
    Nat.card A = Nat.card (LinearMap.ker f) * Nat.card (LinearMap.range f) := by
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f),
    Nat.card_congr f.quotKerEquivRange.toEquiv]

theorem card_five {f : A →ₗ[R] B} {g : B →ₗ[R] C} {h : C →ₗ[R] D} {k : D →ₗ[R] E}
    (hf : Function.Injective f) (h1 : Function.Exact f g) (h2 : Function.Exact g h)
    (h3 : Function.Exact h k) :
    Nat.card (LinearMap.ker k) * Nat.card B = Nat.card C * Nat.card A := by
  rw [card_eq_ker_mul_range g, card_eq_ker_mul_range h, h1.linearMap_ker_eq,
    h2.linearMap_ker_eq, h3.linearMap_ker_eq,
    ← Nat.card_congr (LinearEquiv.ofInjective f hf).toEquiv]
  ring

theorem card_comap {f : A →ₗ[R] B} {g : B →ₗ[R] C} (h : Function.Exact f g) (L : Submodule R B) :
    Nat.card (L.comap f) =
      Nat.card (LinearMap.ker f) * Nat.card (LinearMap.ker (g.domRestrict L)) := by
  let u : L.comap f →ₗ[R] L := f.restrict (fun _ hx => hx)
  rw [card_eq_ker_mul_range u]
  have e1 : LinearMap.range u = LinearMap.ker (g.domRestrict L) := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.domRestrict_apply, h x]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, hy⟩
      exact ⟨⟨y, by rw [Submodule.mem_comap, hy]; exact x.2⟩, Subtype.ext hy⟩
  have e2 : Nat.card (LinearMap.ker u) = Nat.card (LinearMap.ker f) :=
    Nat.card_congr
      { toFun := fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩
        invFun := fun x => ⟨⟨x.1, by
          rw [Submodule.mem_comap, LinearMap.mem_ker.1 x.2]; exact L.zero_mem⟩, Subtype.ext x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [e1, e2]

theorem card_pi {I : Type*} [Fintype I] {P : I → Type*} [∀ i, AddCommGroup (P i)]
    [∀ i, Module R (P i)] (L : ∀ i, Submodule R (P i)) :
    Nat.card (Submodule.pi Set.univ L) = ∏ i, Nat.card (L i) := by
  rw [← Nat.card_pi]
  exact Nat.card_congr
    { toFun := fun x i => ⟨x.1 i, x.2 i trivial⟩
      invFun := fun x => ⟨fun i => (x i).1, fun i _ => (x i).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end Count

theorem arith {k p h2 h0 s i h1 s' q h0' m : ℕ} (a1 : k * p = h2 * h0) (a2 : s = k * i)
    (a3 : i * h1 = s' * q) (a4 : h0' * h2 * m = h1) : s * h0' * p * m = s' * h0 * q := by
  calc s * h0' * p * m = (k * p) * i * h0' * m := by rw [a2]; ring
    _ = i * (h0' * h2 * m) * h0 := by rw [a1]; ring
    _ = s' * h0 * q := by rw [a4, a3]; ring


open PoitouTate in
theorem ker_flip_eq {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {r : ℕ} {S : Finset (HeightOneSpectrum (𝓞 F))}
    {Av : S → ValuationSubring Ω}
    {μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ}
    {j : ∀ v : S, H2 ((charRep μ).comp (locFam S Av v)) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)}
    (hj : ∀ v, Function.Injective (j v))
    {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M]
    [DiscreteTopology M]
    {ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M}
    (hρ : ContAction ρ) (L : LocCond ρ (locFam S Av)) :
    LinearMap.ker ((tr1 S Av μ j ρ hρ).domRestrict (Submodule.pi Set.univ L)).flip =
      Sel (twDual μ ρ) (locFam S Av) (continuous_locFam S Av)
        (perpCond μ ρ (locFam S Av) (fun v => hρ.comp' (continuous_locFam S Av v)) L) := by
  classical
  ext y
  rw [mem_Sel, LinearMap.mem_ker, LinearMap.ext_iff]
  simp only [mem_perpCond, LinearMap.flip_apply, LinearMap.domRestrict_apply, poitouTateNineTerm_transgressionOne_apply,
    LinearMap.zero_apply]
  constructor
  · intro h v x hx
    have hm : Pi.single v x ∈ Submodule.pi Set.univ L := fun w _ => by
      by_cases hw : w = v
      · subst hw; rw [Pi.single_eq_same]; exact hx
      · rw [Pi.single_eq_of_ne hw]; exact zero_mem _
    have e := h ⟨_, hm⟩
    rw [Finset.sum_eq_single v (fun w _ hw => by
      rw [Subtype.coe_mk, Pi.single_eq_of_ne hw, map_zero, map_zero]) (by simp),
      Subtype.coe_mk, Pi.single_eq_same] at e
    exact hj v (e.trans (map_zero _).symm)
  · intro h x
    exact Finset.sum_eq_zero fun v _ => by rw [h v _ (x.2 v trivial), map_zero]


open PoitouTate in
theorem greenbergWiles_totallyComplex : PoitouTateTotallyComplex → LocalFiniteness → GlobalFiniteness → GlobalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [TopologicalSpace M] [DiscreteTopology M] [Finite M] (S : Finset (HeightOneSpectrum (𝓞 F))) (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M), 0 < r → ContainsAbove S l → ∀ (hrho : ContAction rhoS) (muS : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ), muS.comp (toGS Ω _) = cycMod F Ω l r → ∀ Av : S → ValuationSubring Ω, (∀ v, IsPlaceOver (Av v) v.1) → ∀ L : LocCond rhoS (locFam S Av), Finite (Sel rhoS (locFam S Av) (continuous_locFam S Av) L) ∧ Finite (Sel (twDual muS rhoS) (locFam S Av) (continuous_locFam S Av) (perpCond muS rhoS (locFam S Av) (fun v => hrho.comp' (continuous_locFam S Av v)) L)) ∧ Nat.card (Sel rhoS (locFam S Av) (continuous_locFam S Av) L) * Nat.card (H0 (twDual muS rhoS)) * (∏ v : S, Nat.card (H0 (rhoS.comp (locFam S Av v)))) * Nat.card M ^ InfinitePlace.nrComplexPlaces F = Nat.card (Sel (twDual muS rhoS) (locFam S Av) (continuous_locFam S Av) (perpCond muS rhoS (locFam S Av) (fun v => hrho.comp' (continuous_locFam S Av v)) L)) * Nat.card (H0 rhoS) * ∏ v : S, Nat.card (L v) := by
  intro hPT hLF hGF hEC F Ω _ _ _ _ _ _ l _ r M _ _ _ _ _ S ρ hr hS hρ μ hμ Av hA L
  classical
  have : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ r)
  obtain ⟨inv, hinv, h⟩ := hPT F Ω l r hr ζ hζ
  obtain ⟨⟨δ₁, -, h0, h1, h2, h3, h4, -⟩, -⟩ := h S hS Av hA μ hμ M ρ hρ
  have := GlobalTheory.DualSide.finite_TDual_pow (l := l) (r := r) (M := M)
  have hρ' := GlobalTheory.DualSide.contAction_twDual (contAction_charRep hμ) hρ
  obtain ⟨-, f1, -⟩ := hGF F Ω l r M S ρ hr hS hρ
  obtain ⟨-, f1', f2', -⟩ := hGF F Ω l r _ S (twDual μ ρ) hr hS hρ'
  have fl : ∀ v : S, Finite (H1 (ρ.comp (locFam S Av v))) := fun v =>
    (hLF F Ω l r M (Av v) _ v.1 hr (hA v) (hρ.comp' (continuous_locFam S Av v))).2.1
  refine ⟨inferInstance, inferInstance, ?_⟩
  have a1 := card_five h0 h1 h2 h3
  rw [GlobalTheory.ZModDual.card_dual_eq, Nat.card_pi] at a1
  have a2 := card_comap h4 (Submodule.pi Set.univ L)
  have e2 : (Submodule.pi Set.univ L).comap (loc1 S Av ρ) =
      Sel ρ (locFam S Av) (continuous_locFam S Av) L := by
    ext x
    rw [mem_Sel]
    exact ⟨fun h v => h v trivial, fun h v _ => h v⟩
  rw [e2] at a2
  have a3 := GlobalTheory.ZModDual.card_ker_mul_card_eq (l ^ r) _ _
    ((tr1 S Av μ (invAt S Av μ hμ inv) ρ hρ).domRestrict (Submodule.pi Set.univ L))
  rw [ker_flip_eq (fun v => (invAt_bijective S Av μ hμ hinv v (hA v)).1), card_pi] at a3
  have a4 := hEC F Ω l r _ S (twDual μ ρ) hr hS hρ' (fun _ => 1)
    (fun w hw => absurd hw (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)))
  have hM : Nat.card (TDual (ZMod (l ^ r)) M) = Nat.card M := GlobalTheory.ZModDual.card_dual_eq _ _
  rw [archH0Card, Finset.filter_false_of_mem (fun w _ =>
    InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)), Finset.prod_empty,
    one_mul, hM, IsTotallyComplex.finrank, two_mul, pow_add, ← mul_assoc] at a4
  have a5 := Nat.eq_of_mul_eq_mul_right (pow_pos Nat.card_pos _) a4
  exact arith a1 a2 a3 a5

end GlobalTheory.GWComplex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeEigenspaceSumDisjointCompl
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

namespace GlobalTheory.EtaJoin

theorem eigSum_disjoint_compl : ∀ (D : D7) (i : D.nd.Loc) (Y : Set (D.nd.X i)),
    Disjoint (D.nd.eigSum i Y) (D.nd.eigSum i Yᶜ) := by
  intro D i Y
  exact (Formalism.MainNotions.PairedCharacterCondition.CongruenceModules.heckeEig_indep (D.nd.T i) (D.nd.act i) (D.nd.T_sep i)).disjoint_biSup_biSup
    disjoint_compl_right

end GlobalTheory.EtaJoin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdealSpanPrimeVariableBasis
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem exists_residue_basis_of_isMaximal {R A : Type} [CommRing R] [CommRing A] (f : R →+* A) (m : Ideal R)
    [hm : m.IsMaximal] (h : m.map f ≠ ⊤) :
    ∃ (ι : Type) (b : ι → A) (i₀ : ι), b i₀ = 1 ∧
      (∀ x : A, ∃ a : ι →₀ R, x - a.sum (fun i y => f y * b i) ∈ m.map f) ∧
      ∀ a : ι →₀ R, a.sum (fun i y => f y * b i) ∈ m.map f → ∀ i, a i ∈ m := by
  first
  | exact @_root_.GlobalTheory.ClosedStatement.main
  | exact _root_.GlobalTheory.ClosedStatement.main
  | (apply _root_.GlobalTheory.ClosedStatement.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClosedStatement.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClosedStatement.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClosedStatement.main ..)

theorem isMaximal_span_l_sup_span_X (l a : ℕ) [Fact l.Prime] [NeZero a] :
    (Ideal.span {(l : (Wq l a)⟦X⟧)} ⊔ Ideal.span {(X : (Wq l a)⟦X⟧)}).IsMaximal := by
  have hmax : (Ideal.span {(l : Wq l a)}).IsMaximal := by
    rw [← (WittVector.irreducible l (k := Fq l a)).maximalIdeal_eq]
    infer_instance
  have hsurj : Function.Surjective (constantCoeff (R := Wq l a)) := fun w => ⟨C w, by simp⟩
  have heq : Ideal.span {(l : (Wq l a)⟦X⟧)} ⊔ Ideal.span {(X : (Wq l a)⟦X⟧)} =
      (Ideal.span {(l : Wq l a)}).comap (constantCoeff (R := Wq l a)) := by
    apply le_antisymm
    · refine sup_le ?_ ?_ <;> rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
      · rw [map_natCast]
        exact Ideal.mem_span_singleton_self _
      · simp
    · intro x hx
      obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (Ideal.mem_comap.1 hx)
      have hX : (X : (Wq l a)⟦X⟧) ∣ x - C w * l := by
        rw [X_dvd_iff, map_sub, map_mul, map_natCast, constantCoeff_C, hw, sub_self]
      have : x = C w * l + (x - C w * l) := by ring
      rw [this]
      exact Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
        (Ideal.mem_span_singleton.2 hX)
  rw [heq]
  exact Ideal.comap_isMaximal_of_surjective _ hsurj

theorem BK.map_span_l_sup_span_X_ne_top {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) :
    (Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)}).map bk.ev ≠ ⊤ := by
  let M : Ideal (Ainf l) := (IsLocalRing.maximalIdeal (OC l)).comap (Per.θ l)
  haveI hM : M.IsPrime := Ideal.comap_isPrime _ _
  let N : Ideal bk.S := M.comap bk.ev
  haveI hN : N.IsPrime := Ideal.comap_isPrime _ _
  have hl : (l : bk.S) ∈ N := by
    change Per.θ l (bk.ev l) ∈ IsLocalRing.maximalIdeal (OC l)
    rw [map_natCast, map_natCast]
    exact (Fact.out : ¬ IsUnit (l : OC l))
  have hE : bk.E ∈ N := by
    change Per.θ l (bk.ev bk.E) ∈ IsLocalRing.maximalIdeal (OC l)
    have : bk.ev bk.E ∈ RingHom.ker (Per.θ l) := bk.span_ev ▸ Ideal.mem_span_singleton_self _
    rw [RingHom.mem_ker.1 this]
    exact Ideal.zero_mem _
  have hX : (X : bk.S) ∈ N := by
    apply hN.mem_of_pow_mem bk.Ep.natDegree
    have h1 := congrArg (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) bk.monic.as_sum
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), map_pow, map_sum] at h1
    have hs : ∑ i ∈ Finset.range bk.Ep.natDegree, Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)
        (Polynomial.C (bk.Ep.coeff i) * Polynomial.X ^ i) ∈ N := by
      refine Ideal.sum_mem _ fun i hi => ?_
      obtain ⟨w, hw⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
      rw [hw, map_mul, map_mul, map_mul, map_natCast, map_natCast]
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hl)
    have h2 := N.sub_mem hE hs
    simp only [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X] at h1 h2
    have h3 := sub_eq_of_eq_add h1
    rwa [h3] at h2
  intro htop
  apply hM.ne_top
  rw [eq_top_iff, ← htop, Ideal.map_le_iff_le_comap]
  exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 hl) ((Ideal.span_singleton_le_iff_mem _).2 hX)

theorem BK.exists_residue_basis : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K),
    ∃ (ι : Type) (b : ι → Ainf l) (i₀ : ι), b i₀ = 1 ∧
      (∀ x : Ainf l, ∃ a : ι →₀ bk.S, x - a.sum (fun i y => bk.ev y * b i) ∈
        (Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)}).map bk.ev) ∧
      ∀ a : ι →₀ bk.S, a.sum (fun i y => bk.ev y * b i) ∈
        (Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)}).map bk.ev →
        ∀ i, a i ∈ Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)} := by
  intro l _ K bk
  haveI := isMaximal_span_l_sup_span_X l bk.a
  exact exists_residue_basis_of_isMaximal bk.ev _ bk.map_span_l_sup_span_X_ne_top

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdeleLogAbsoluteValueEqLogIdeleModuleStatement
section
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideleLogAbsoluteValue_eq_log_ideleModule : ∀ (E : Type) [Field E] [NumberField E] (d : (AdeleRing (𝓞 E) E)ˣ), GlobalTheory.Mem.Chr.CharModel.logNorm E d = Real.log (GroundTheory.Global.IdeleGroup.ideleModule E d : ℝ) := by
  first | (exact @GlobalTheory.IdeleLogNormCompare.logNorm_eq_log_ideleModule) | (exact GlobalTheory.IdeleLogNormCompare.logNorm_eq_log_ideleModule) | (intros; apply GlobalTheory.IdeleLogNormCompare.logNorm_eq_log_ideleModule  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralLocalDualityOfLocalTateDualityStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_localDuality_of_localTateDuality : Formalism.GaloisCohomology.LocalTateDualityK → ReciprocityTheory.ChartRestriction.T2.IntIso := by
  first | exact @GlobalTheory.LocDualInt.int_iso_of_localTateDuality | exact GlobalTheory.LocDualInt.int_iso_of_localTateDuality | (intros; apply GlobalTheory.LocDualInt.int_iso_of_localTateDuality <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralTatePairingLatticeDualStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_tate_pairing_lattice_dual : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ L1 : Lattice (O := O) (charRep (cycLL (P.PD K) LL)), L1.T = LinearMap.range (Algebra.linearMap O LL) → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (m : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 (P.PD K) LA LA' m → ∃ β : ↥(latticeCocycles LA) →ₗ[O] ↥(divisibleCocycles LA') →ₗ[O] (LL ⧸ L1.T), (∀ d c, β d c = 0 ↔ CobO (P.PD K) L1 (cupLD LA' m d.1 c.1)) ∧ (∀ d c, d.1 ∈ latticeCoboundaries LA → β d c = 0) ∧ ∀ d c, c.1 ∈ BD LA' → β d c = 0 := by
  first | exact @GlobalTheory.TatePair.integral_pairing | exact GlobalTheory.TatePair.integral_pairing | (intros; apply GlobalTheory.TatePair.integral_pairing <;> assumption)
end

