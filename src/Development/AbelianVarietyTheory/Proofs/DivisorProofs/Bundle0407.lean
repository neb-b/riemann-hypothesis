module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0384
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0376
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0385
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0388

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisActionFinitarySheafSectionLocallyConstantStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

open GlobalTheory.EtC.GalSmooth in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisAction_finitarySheafSection_locallyConstant :
    ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F →
      ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
        (x : Sec F (Spec (CommRingCat.of Ω))),
        IsLocallyConstant (fun τ : Ω ≃ₐ[K] Ω =>
          Sec.res (Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω))) x) := by
  intro R _ F hF K Ω _ _ _ _ x
  classical
  have elements :=
    (GlobalTheory.T.preservesFilteredColimits_moduleCat_iff_forget_iff_elements
      (ULift.{1} R) (onRings F)).2.mp hF
  obtain ⟨s, y, hy⟩ := (elements (Finset Ω) (diag Ω) (cocone Ω) (coconeIsColimit Ω)).1 x
  have restrict_eq (τ : Ω ≃ₐ[K] Ω) :
      Sec.res (Spec.map (CommRingCat.ofHom (τ : Ω →+* Ω))) x =
        ((onRings F).map (CommRingCat.ofHom ((τ : Ω →+* Ω).comp (sr Ω s).subtype))).hom y := by
    rw [← hy, cocone_ι]
    show _ = ((onRings F).map (CommRingCat.ofHom (sr Ω s).subtype ≫
      CommRingCat.ofHom (τ : Ω →+* Ω))).hom y
    rw [Functor.map_comp]
    rfl
  rw [IsLocallyConstant.iff_eventually_eq]
  intro τ₀
  have : FiniteDimensional K (IntermediateField.adjoin K (s : Set Ω)) :=
    IntermediateField.finiteDimensional_adjoin (fun a _ => Algebra.IsIntegral.isIntegral a)
  have hopen : IsOpen {σ : Ω ≃ₐ[K] Ω |
      τ₀⁻¹ * σ ∈ (IntermediateField.adjoin K (s : Set Ω)).fixingSubgroup} :=
    (IntermediateField.fixingSubgroup_isOpen _).preimage (continuous_const.mul continuous_id)
  filter_upwards [hopen.mem_nhds (by simp)] with τ hτ
  have hs : Set.EqOn (τ : Ω →+* Ω) (τ₀ : Ω →+* Ω) (s : Set Ω) := fun b hb => by
    have hfix := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ b
      (IntermediateField.subset_adjoin K _ hb)
    simpa [AlgEquiv.mul_apply] using congrArg τ₀ hfix
  have hc : (τ : Ω →+* Ω).comp (sr Ω s).subtype =
      (τ₀ : Ω →+* Ω).comp (sr Ω s).subtype := by
    ext a
    exact RingHom.eqOn_set_closure hs a.2
  rw [restrict_eq τ, restrict_eq τ₀, hc]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointNormalCoords
section
open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginBCEt

open GlobalTheory.LocAcyc GlobalTheory.KeyOriginNoeth GlobalTheory.KeyOriginBC

theorem closureEtaleAt_bc : ∀ (A R A₁ R₁ : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R]
    [CommRing A₁] [IsDomain A₁] [CommRing R₁] [IsDomain R₁] [IsIntegrallyClosed R₁] [Algebra A₁ R₁]
    (f : A →+* A₁), Function.Injective f → Function.Injective (algebraMap A₁ R₁) →
    ∀ (κ : R →+* R₁), κ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp f →
    ∀ (β : GenFib A R →+* GenFib A₁ R₁),
    β.comp (algebraMap R (GenFib A R)) = (algebraMap R₁ (GenFib A₁ R₁)).comp κ →
    ∀ (DA : Type) [CommRing DA] [Algebra (GenFib A R) DA] [Algebra.IsIntegral (GenFib A R) DA]
    (P₁ : Ideal R₁) [P₁.IsPrime],
    GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A R DA (P₁.comap κ) →
    GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A₁ R₁ (BC β DA) P₁ := by
  intro A R A₁ R₁ _ _ _ _ _ _ _ _ _ _ f hf hA₁ κ hκ β hβ DA _ _ _ P₁ _ hP
  letI := closureAlg A R DA
  letI : Algebra R (Localization.AtPrime P₁) :=
    ((algebraMap R₁ (Localization.AtPrime P₁)).comp κ).toAlgebra
  letI : Algebra R₁ (BC β DA) := (baseHom A₁ R₁ (BC β DA)).toAlgebra
  haveI hE : Algebra.Etale (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R] closure A R DA) :=
    GlobalTheory.T.etale_atPrime_baseChange_of_integralClosureEtale A R R₁ DA κ P₁ hP
  haveI : IsDomain (Localization.AtPrime P₁) :=
    IsLocalization.isDomain_localization P₁.primeCompl_le_nonZeroDivisors
  haveI : IsIntegrallyClosed (Localization.AtPrime P₁) :=
    isIntegrallyClosed_of_isLocalization _ P₁.primeCompl P₁.primeCompl_le_nonZeroDivisors
  have hinjS : Function.Injective (algebraMap R₁ (Localization.AtPrime P₁)) :=
    IsLocalization.injective _ P₁.primeCompl_le_nonZeroDivisors
  have hM : (nonZeroDivisors A₁).map ((algebraMap R₁ (Localization.AtPrime P₁)).comp (algebraMap A₁ R₁))
      ≤ nonZeroDivisors (Localization.AtPrime P₁) := by
    rintro _ ⟨a, ha, rfl⟩
    apply mem_nonZeroDivisors_of_ne_zero
    intro h
    have h1 : algebraMap A₁ R₁ a = 0 := hinjS (by simpa using h)
    exact nonZeroDivisors.ne_zero ha (hA₁ (by simpa using h1))
  obtain ⟨hinj, hint⟩ := GlobalTheory.T.etale_integrallyClosed_in_localization (Localization.AtPrime P₁)
    (Localization.AtPrime P₁ ⊗[R] closure A R DA) _ hM
  obtain ⟨φ, ψ, hψφ, hunit, hsurj⟩ := GlobalTheory.T.exists_closureBaseChange_maps_and_retraction A R A₁ R₁ f hf κ hκ β hβ DA (Localization.AtPrime P₁)
  have hψφ' : ∀ e, ψ (φ e) = algebraMap _ _ e := fun e => by
    rw [← AlgHom.comp_apply, hψφ]; rfl
  have hφinj : Function.Injective φ := by
    intro x y hxy
    apply hinj
    rw [← hψφ', ← hψφ', hxy]
  have hφint : ∀ x : Localization.AtPrime P₁ ⊗[R₁] BC β DA, IsIntegral (Localization.AtPrime P₁) x →
      x ∈ φ.range := by
    intro x hx
    obtain ⟨e, he⟩ := hint (ψ x) (hx.map ψ)
    obtain ⟨m, hm, e', he'⟩ := hsurj x
    have he'' : φ e' = x * algebraMap _ _ m := he'
    have h2 : e * algebraMap _ _ m = e' := by
      apply hinj
      rw [map_mul, he, ← hψφ' e', he'', map_mul, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
    refine ⟨e, ?_⟩
    show φ e = x
    apply (hunit m hm).mul_right_cancel
    calc φ e * algebraMap _ _ m = φ (e * algebraMap _ _ m) := by rw [map_mul, AlgHom.commutes]
      _ = x * _ := by rw [h2, he'']
  haveI : Algebra.IsIntegral R (closure A R DA) := by
    letI := (baseHom A R DA).toAlgebra
    let ι : closure A R DA →ₐ[R] DA := { (closure A R DA).subtype with commutes' := fun _ => rfl }
    exact ⟨fun x => (isIntegral_algHom_iff ι Subtype.val_injective).1 x.2⟩
  haveI : Algebra.IsIntegral (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R] closure A R DA) :=
    inferInstance
  let φ' : Localization.AtPrime P₁ ⊗[R] closure A R DA →ₐ[Localization.AtPrime P₁]
      integralClosure (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R₁] BC β DA) :=
    φ.codRestrict _ (fun e => (Algebra.IsIntegral.isIntegral e).map φ)
  have hφ' : Function.Bijective φ' := by
    refine ⟨fun x y h => hφinj (congrArg Subtype.val h), fun ⟨x, hx⟩ => ?_⟩
    obtain ⟨e, he⟩ := hφint x hx
    exact ⟨e, Subtype.ext he⟩
  haveI : Algebra.Etale (Localization.AtPrime P₁)
      (integralClosure (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R₁] BC β DA)) :=
    Algebra.Etale.of_equiv (AlgEquiv.ofBijective φ' hφ')
  have hloc := TensorProduct.toIntegralClosure_bijective_of_isLocalization (R := R₁)
    (S := Localization.AtPrime P₁) (B := BC β DA) P₁.primeCompl
  haveI : Algebra.Etale (Localization.AtPrime P₁)
      (Localization.AtPrime P₁ ⊗[R₁] integralClosure R₁ (BC β DA)) :=
    Algebra.Etale.of_equiv (AlgEquiv.ofBijective _ hloc).symm
  unfold GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt
  letI := closureAlg A₁ R₁ (BC β DA)
  let eC : closure A₁ R₁ (BC β DA) ≃ₐ[R₁] integralClosure R₁ (BC β DA) :=
    { toFun := fun x => ⟨x.1, x.2⟩, invFun := fun x => ⟨x.1, x.2⟩, left_inv := fun _ => rfl,
      right_inv := fun _ => rfl, map_mul' := fun _ _ => rfl, map_add' := fun _ _ => rfl,
      commutes' := fun _ => rfl }
  exact Algebra.Etale.of_equiv (Algebra.TensorProduct.congr AlgEquiv.refl eC).symm

theorem closureEtaleAt_baseChange : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra T[X] O]
    [IsScalarTower T T[X] O]
    (A A₁ : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Algebra.EssFiniteType ℤ A] [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] [IsNoetherianRing A₁]
    [IsIntegrallyClosed A₁] [Algebra.EssFiniteType ℤ A₁] (f : A →+* A₁) (i : A →+* T)
    (i₁ : A₁ →+* T) (hf : Function.Injective f)
    (EA : Type) [CommRing EA] [Algebra A[X] EA] [Algebra A EA] [IsScalarTower A A[X] EA]
    [Algebra.Etale A[X] EA]
    (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O) (hcomp : i₁.comp f = i)
    (hj : jA.comp (algebraMap A[X] (Localization.AtPrime QA)) =
      (algebraMap T[X] O).comp (Polynomial.mapRingHom i))
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA] (q : ℕ)
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    0 < q → IsUnit (q : A) →
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∀ a : A, a ≠ 0 →
    (∀ (P : Ideal (Localization.AtPrime QA)) [P.IsPrime],
      algebraMap A (Localization.AtPrime QA) a ∉ P →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A (Localization.AtPrime QA) DA P) →
    ∀ (P₁ : Ideal (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj)) [P₁.IsPrime], algebraMap A₁ (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) (f a) ∉ P₁ →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A₁ (GlobalTheory.KeyOriginBC.Loc₁ f i i₁ EA QA jA hcomp hj) (GlobalTheory.KeyOriginBC.BC (GlobalTheory.KeyOriginBC.fibBC f i i₁ EA QA jA hcomp hj hf) DA) P₁ := by
  intro T O _ _ _ _ _ _ A A₁ _ _ _ _ _ _ _ _ _ _ _ _ f i i₁ hf EA _ _ _ _ _ QA _ jA hcomp hj DA _ _ q actA
    _ _ htors a _ hyp P₁ _ haP₁
  obtain ⟨hd, hn⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_etale (Polynomial A₁)
    (ideal₁ f i i₁ EA QA jA hcomp hj) (Loc₁ f i i₁ EA QA jA hcomp hj)
  haveI := hd
  haveI := hn
  haveI : Module.Flat (Polynomial A₁) (Loc₁ f i i₁ EA QA jA hcomp hj) :=
    Module.Flat.trans (Polynomial A₁) (Ext f EA) (Loc₁ f i i₁ EA QA jA hcomp hj)
  have hA₁ : Function.Injective (algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj)) := by
    have h1 : Function.Injective (algebraMap (Polynomial A₁) (Loc₁ f i i₁ EA QA jA hcomp hj)) := by
      set_option synthInstance.maxHeartbeats 400000 in
      exact FaithfulSMul.algebraMap_injective (Polynomial A₁) (Loc₁ f i i₁ EA QA jA hcomp hj)
    rw [IsScalarTower.algebraMap_eq A₁ (Polynomial A₁) (Loc₁ f i i₁ EA QA jA hcomp hj)]
    exact h1.comp Polynomial.C_injective
  haveI : Module.Finite (GenFib A (Localization.AtPrime QA)) DA := htors.1
  haveI : Algebra.IsIntegral (GenFib A (Localization.AtPrime QA)) DA := inferInstance
  have hκ : (locBC f i i₁ EA QA jA hcomp hj).comp (algebraMap A (Localization.AtPrime QA)) =
      (algebraMap A₁ (Loc₁ f i i₁ EA QA jA hcomp hj)).comp f :=
    RingHom.ext (locBC_algebraMap_base f i i₁ EA QA jA hcomp hj)
  have hβ : (fibBC f i i₁ EA QA jA hcomp hj hf).comp
      (algebraMap (Localization.AtPrime QA) (GenFib A (Localization.AtPrime QA))) =
      (algebraMap (Loc₁ f i i₁ EA QA jA hcomp hj) (GenFib A₁ (Loc₁ f i i₁ EA QA jA hcomp hj))).comp
        (locBC f i i₁ EA QA jA hcomp hj) :=
    RingHom.ext (fibBC_algebraMap f i i₁ EA QA jA hcomp hj hf)
  refine closureEtaleAt_bc A (Localization.AtPrime QA) A₁ (Loc₁ f i i₁ EA QA jA hcomp hj) f hf hA₁
    (locBC f i i₁ EA QA jA hcomp hj) hκ (fibBC f i i₁ EA QA jA hcomp hj hf) hβ DA P₁ ?_
  apply hyp
  rw [Ideal.mem_comap, ← RingHom.comp_apply, hκ, RingHom.comp_apply]
  exact haP₁

end GlobalTheory.KeyOriginBCEt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueCommaOfBasis
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

namespace GlobalTheory.CatCoh.Desc

theorem glue_comma_of_basis : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp F (G.map a) (s t u)) → ∃ x : F.obj T, ∀ t u, mp F u x = s t u) := by
  intro R _ C _ C' _ F G _ _ H hcov hdir T s hs
  have key : ∀ (t₁ t₂ : C') (u₁ : T ⟶ G.obj t₁) (u₂ : T ⟶ G.obj t₂) (S : C)
      (w₁ : G.obj t₁ ⟶ S) (w₂ : G.obj t₂ ⟶ S), mp F w₁ (s t₁ u₁) = mp F w₂ (s t₂ u₂) := by
    intro t₁ t₂ u₁ u₂ S w₁ w₂
    obtain ⟨n, b, hb, hb'⟩ := hdir t₁ t₂ S w₁ w₂
    refine sub_eq_zero.1 (GlobalTheory.CatCoh.Desc.sep_std H hb _ fun S' u' ⟨i, hi⟩ ↦ ?_)
    obtain ⟨t₃, ⟨a₁⟩, ⟨a₂⟩, ⟨g⟩⟩ := hb' i S' u' hi
    have e1 : mp F u' (mp F w₁ (s t₁ u₁)) = mp F g (s t₃ (u₁ ≫ G.map a₁)) := by
      rw [hs, ← mp_comp, ← mp_comp, Subsingleton.elim (G.map a₁ ≫ g) (w₁ ≫ u')]
    have e2 : mp F u' (mp F w₂ (s t₂ u₂)) = mp F g (s t₃ (u₂ ≫ G.map a₂)) := by
      rw [hs, ← mp_comp, ← mp_comp, Subsingleton.elim (G.map a₂ ≫ g) (w₂ ≫ u')]
    have e3 : u₁ ≫ G.map a₁ = u₂ ≫ G.map a₂ := Subsingleton.elim _ _
    rw [map_sub, e1, e2, e3, sub_self]
  obtain ⟨n, b, hb, hb'⟩ := hcov T
  have hex : ∀ S (u : T ⟶ S), ∃ y : F.obj S, (∃ i, IsUnit (mp F u (b i))) →
      ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), mp F w (s t v) = y := by
    intro S u
    by_cases h : ∃ i, IsUnit (mp F u (b i))
    · obtain ⟨i, hi⟩ := h
      obtain ⟨t, v, w, -⟩ := hb' i S u hi
      exact ⟨mp F w (s t v), fun _ ↦ ⟨t, v, w, rfl⟩⟩
    · exact ⟨0, fun h' ↦ absurd h' h⟩
  choose σ hσ using hex
  obtain ⟨x, hx⟩ := GlobalTheory.CatCoh.Desc.glue_std H hb σ fun S S' u ψ hp ↦ by
    obtain ⟨t, v, w, e⟩ := hσ S u hp
    obtain ⟨i, hi⟩ := hp
    obtain ⟨t', v', w', e'⟩ := hσ S' (u ≫ ψ) ⟨i, isUnit_comp ψ hi⟩
    rw [← e, ← e', ← mp_comp]
    exact key _ _ _ _ _ _ _
  refine ⟨x, fun t u ↦ ?_⟩
  have hb2 : Ideal.span (Set.range fun i ↦ mp F u (b i)) = ⊤ := by
    have := congrArg (Ideal.map (mp F u)) hb
    rwa [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
  refine sub_eq_zero.1 (GlobalTheory.CatCoh.Desc.sep_std H hb2 _ fun S' ψ ⟨i, hi⟩ ↦ ?_)
  have hi' : IsUnit (mp F (u ≫ ψ) (b i)) := by rw [mp_comp]; exact hi
  obtain ⟨t', v', w', e'⟩ := hσ S' (u ≫ ψ) ⟨i, hi'⟩
  rw [map_sub, ← mp_comp, hx _ _ ⟨i, hi'⟩, ← e', key t' t v' u S' w' ψ, sub_self]

end GlobalTheory.CatCoh.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueMeasUnivNeTopOfCompact
section
open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ENNReal

namespace GlobalTheory

theorem glueMeas_univ_ne_top_of_compact {M : Type} [TopologicalSpace M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] {n : ℕ} {ι : Type}
    (e : ι → OpenPartialHomeomorph M (V n)) (hcov : ∀ y, ∃ i, y ∈ (e i).source)
    (hd : ∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm)
      ((e i).target ∩ (e i).symm ⁻¹' (e j).source))
    (r : ι → V n → ℝ) (hr : ∀ i, ContinuousOn (r i) (e i).target)
    (hc : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      r i (e i y) = ‖GlobalTheory.ChartGlue.transDet (e i) (e j) y‖ ^ 2 * r j (e j y)) :
    GlobalTheory.ChartGlue.glueMeas e (fun i y => ENNReal.ofReal (r i (e i y))) univ ≠ ∞ := by
  classical
  set μ := GlobalTheory.ChartGlue.glueMeas e (fun i y => ENNReal.ofReal (r i (e i y))) with hμ
  have hρ : ∀ i j y, y ∈ (e i).source → y ∈ (e j).source →
      ENNReal.ofReal (r i (e i y)) =
        ENNReal.ofReal (‖GlobalTheory.ChartGlue.transDet (e i) (e j) y‖ ^ 2) * ENNReal.ofReal (r j (e j y)) := by
    intro i j y hi hj
    rw [← ENNReal.ofReal_mul (sq_nonneg _), hc i j y hi hj]
  have hloc : ∀ y : M, ∃ U : Set M, IsOpen U ∧ y ∈ U ∧ μ U < ∞ := by
    intro y
    obtain ⟨i, hi⟩ := hcov y
    have hT : (e i).target ∈ nhds ((e i) y) := (e i).open_target.mem_nhds ((e i).map_source hi)
    obtain ⟨δ, hδ, hδs⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hT
    set U := (e i).source ∩ (e i) ⁻¹' Metric.ball ((e i) y) δ with hUdef
    have hUo : IsOpen U :=
      (e i).continuousOn.isOpen_inter_preimage (e i).open_source Metric.isOpen_ball
    have hUs : U ⊆ (e i).source := inter_subset_left
    have himg : (e i) '' U ⊆ Metric.closedBall ((e i) y) δ := by
      rintro _ ⟨z, hz, rfl⟩
      exact Metric.ball_subset_closedBall hz.2
    obtain ⟨C, hC⟩ :=
      (isCompact_closedBall ((e i) y) δ).exists_bound_of_continuousOn ((hr i).mono hδs)
    refine ⟨U, hUo, ⟨hi, Set.mem_preimage.mpr (Metric.mem_ball_self hδ)⟩, ?_⟩
    have hm := GlobalTheory.ChartGlue.measurableSet_image (e i) hUo.measurableSet hUs
    rw [hμ, GlobalTheory.ChartGlue.glueMeas_apply e _ hd hρ i hUo.measurableSet hUs,
      GlobalTheory.ChartGlue.chartMeas_apply_of_subset _ _ hUo.measurableSet hUs]
    calc ∫⁻ v in (e i) '' U, ENNReal.ofReal (r i ((e i) ((e i).symm v)))
        ≤ ∫⁻ _ in (e i) '' U, ENNReal.ofReal C := by
          refine setLIntegral_mono' hm fun v hv => ENNReal.ofReal_le_ofReal ?_
          rw [(e i).right_inv (hδs (himg hv))]
          have := hC v (himg hv)
          rw [Real.norm_eq_abs] at this
          exact (le_abs_self _).trans this
      _ = ENNReal.ofReal C * volume ((e i) '' U) := setLIntegral_const _ _
      _ ≤ ENNReal.ofReal C * volume (Metric.closedBall ((e i) y) δ) := by
          gcongr
      _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top
  choose U hUo hyU hUf using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hUo
    (fun y _ => mem_iUnion.2 ⟨y, hyU y⟩)
  refine ne_of_lt (lt_of_le_of_lt (measure_mono ht) ?_)
  exact (measure_biUnion_finset_le t U).trans_lt (ENNReal.sum_lt_top.2 fun y _ => hUf y)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjEqOneOfPowEqOneOfSqZeroTrivialStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grpObj_eq_one_of_pow_eq_one_of_sqZero_trivial : ∀ (C C₀ : Type) [CommRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → RingHom.ker π ^ 2 = 0 → ∀ (G : Over (Sp C)) [GrpObj G] (n : ℕ), IsUnit (n : C) → ∀ (T : Over (Sp C)) (z : T ⟶ G), (∀ (T₀ : Over (Sp C₀)) (j : Over.mk (T₀.hom ≫ spMap π) ⟶ T), j ≫ z = 1) → z ^ n = 1 → z = 1 := by
  first | (exact @GlobalTheory.MulUnramified.eq_one_of_pow_eq_one_thick) | (exact GlobalTheory.MulUnramified.eq_one_of_pow_eq_one_thick) | (intros; apply GlobalTheory.MulUnramified.eq_one_of_pow_eq_one_thick  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjTangentVectorAddAtPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grpObj_tangentVector_add_at_point : ∀ {S : Scheme.{0}} (G : Over S) [GrpObj G] {R' : Type} [CommRing R'] (x : Sp R' ⟶ S) (w : epsPtR x ⟶ G), spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ w.left = (1 : Over.mk x ⟶ G).left → ∀ (a b : R') (wa wb : epsPtR x ⟶ G), wa.left = spMap (epsScaleR a) ≫ w.left → wb.left = spMap (epsScaleR b) ≫ w.left → (wa * wb).left = spMap (epsScaleR (a + b)) ≫ w.left := by
  first | (exact @GlobalTheory.GrpTangentPt.tanadd) | (exact GlobalTheory.GrpTangentPt.tanadd) | (intros; apply GlobalTheory.GrpTangentPt.tanadd  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLocOAff
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR

theorem hasLoc_OAff : ∀ {R' : Type} [CommRing R'] {X' : Scheme.{0}} (s' : X' ⟶ Sp R'),
    Desc.HasLoc (OAff s') := by
  intro R' _ X' s' T b
  let U := T.unop
  let b' : Γ(X', U.1) := b
  let V : X'.affineOpens := ⟨X'.basicOpen b', U.2.basicOpen b'⟩
  have hVU : V ≤ U := X'.basicOpen_le b'
  let l : T ⟶ Opposite.op V := (homOfLE hVU).op
  haveI := U.2.isLocalization_basicOpen b'
  refine ⟨Opposite.op V, l, ?_, ?_, ?_, ?_⟩
  · exact IsLocalization.Away.algebraMap_isUnit (S := Γ(X', X'.basicOpen b')) b'
  · intro y
    let y' : Γ(X', X'.basicOpen b') := y
    obtain ⟨⟨x, ⟨_, n, rfl⟩⟩, e⟩ := IsLocalization.surj (Submonoid.powers b') y'
    refine ⟨n, x, ?_⟩
    show y' * (algebraMap Γ(X', U.1) Γ(X', X'.basicOpen b') b') ^ n =
      algebraMap Γ(X', U.1) Γ(X', X'.basicOpen b') x
    rw [← map_pow]
    exact e
  · intro x hx
    let x' : Γ(X', U.1) := x
    have hx : algebraMap Γ(X', U.1) Γ(X', X'.basicOpen b') x' = 0 := hx
    obtain ⟨⟨_, n, rfl⟩, e⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers b') _ x').1 hx
    exact ⟨n, e⟩
  · intro S u hu
    have hSU : S.unop.1 ≤ U.1 := leOfHom u.unop
    have hu' : IsUnit ((X'.presheaf.map (homOfLE hSU).op).hom b') := hu
    have h1 := X'.basicOpen_res b' (homOfLE hSU).op
    rw [Scheme.basicOpen_of_isUnit _ hu'] at h1
    have hSV : S.unop ≤ V := by
      change S.unop.1 ≤ X'.basicOpen b'
      rw [h1]; exact inf_le_right
    refine ⟨(homOfLE hSV).op, Subsingleton.elim _ _, fun _ _ ↦ Subsingleton.elim _ _⟩

end GlobalTheory.CechDR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormsIntegrallyEquivalentAlmostAll
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.ProdStep

theorem mem_span_prod {A₁ A₂ : Type} [CommRing A₁] [CommRing A₂] (a₁ : A₁) (a₂ : A₂) (x : A₁ × A₂) :
    x ∈ Ideal.span {((a₁, a₂) : A₁ × A₂)} ↔ x.1 ∈ Ideal.span {a₁} ∧ x.2 ∈ Ideal.span {a₂} := by
  simp only [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨⟨c.1, rfl⟩, ⟨c.2, rfl⟩⟩
  · rintro ⟨⟨c₁, h₁⟩, ⟨c₂, h₂⟩⟩
    exact ⟨(c₁, c₂), Prod.ext h₁ h₂⟩

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, ← Functor.map_comp, ← Spec.map_comp]

theorem prodStep : ∀ (q : ℕ) (B A₁ A₂ : Type) [CommRing B] [CommRing A₁] [CommRing A₂] [Algebra B A₁] [Algebra B A₂] (f : B) (I J : Ideal B) (n i : ℤ) (y : Ht q (sp B) n i), IsCoprime I J → (∀ a : A₁, ∃ b : B, a - algebraMap B A₁ b ∈ Ideal.span {algebraMap B A₁ f}) → (∀ b : B, algebraMap B A₁ b ∈ Ideal.span {algebraMap B A₁ f} ↔ b ∈ I) → (∀ a : A₂, ∃ b : B, a - algebraMap B A₂ b ∈ Ideal.span {algebraMap B A₂ f}) → (∀ b : B, algebraMap B A₂ b ∈ Ideal.span {algebraMap B A₂ f} ↔ b ∈ J) → pull _ (spMap (algebraMap B A₁)) _ _ y = 0 → pull _ (spMap (algebraMap B A₂)) _ _ y = 0 → (∀ a : A₁ × A₂, ∃ b : B, a - algebraMap B (A₁ × A₂) b ∈ Ideal.span {algebraMap B (A₁ × A₂) f}) ∧ (∀ b : B, algebraMap B (A₁ × A₂) b ∈ Ideal.span {algebraMap B (A₁ × A₂) f} ↔ b ∈ I ⊓ J) ∧ pull _ (spMap (algebraMap B (A₁ × A₂))) _ _ y = 0 := by
  intro q B A₁ A₂ _ _ _ _ _ f I J n i y hIJ hs₁ hk₁ hs₂ hk₂ hy₁ hy₂
  have hf : algebraMap B (A₁ × A₂) f = (algebraMap B A₁ f, algebraMap B A₂ f) := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro a
    obtain ⟨u, hu, v, hv, huv⟩ := Ideal.isCoprime_iff_exists.1 hIJ
    obtain ⟨b₁, hb₁⟩ := hs₁ a.1
    obtain ⟨b₂, hb₂⟩ := hs₂ a.2
    refine ⟨b₁ * v + b₂ * u, ?_⟩
    rw [hf, mem_span_prod]
    constructor
    · have e : a.1 - algebraMap B A₁ (b₁ * v + b₂ * u) = (a.1 - algebraMap B A₁ b₁) + algebraMap B A₁ ((b₁ - b₂) * u) := by
        have : b₁ * v + b₂ * u = b₁ - (b₁ - b₂) * u := by linear_combination b₁ * huv
        rw [this, map_sub]; ring
      show a.1 - algebraMap B A₁ (b₁ * v + b₂ * u) ∈ _
      rw [e]
      exact Ideal.add_mem _ hb₁ ((hk₁ _).2 (I.mul_mem_left _ hu))
    · have e : a.2 - algebraMap B A₂ (b₁ * v + b₂ * u) = (a.2 - algebraMap B A₂ b₂) + algebraMap B A₂ ((b₂ - b₁) * v) := by
        have : b₁ * v + b₂ * u = b₂ - (b₂ - b₁) * v := by linear_combination b₂ * huv
        rw [this, map_sub]; ring
      show a.2 - algebraMap B A₂ (b₁ * v + b₂ * u) ∈ _
      rw [e]
      exact Ideal.add_mem _ hb₂ ((hk₂ _).2 (J.mul_mem_left _ hv))
  · intro b
    rw [hf, mem_span_prod, Ideal.mem_inf]
    exact and_congr (hk₁ b) (hk₂ b)
  · have hbij := GlobalTheory.EtC.ProdCoh.ht_prod_bijective q A₁ A₂ n i
    apply hbij.1
    have e₁ : (RingHom.fst A₁ A₂).comp (algebraMap B (A₁ × A₂)) = algebraMap B A₁ := by ext; rfl
    have e₂ : (RingHom.snd A₁ A₂).comp (algebraMap B (A₁ × A₂)) = algebraMap B A₂ := by ext; rfl
    simp only [map_zero]
    rw [← pull_comp, ← pull_comp, ← spMap_comp, ← spMap_comp, e₁, e₂, hy₁, hy₂]

end GlobalTheory.EtC.ProdStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyCoefficientMapFunctorialAdditiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hypercohomologyCoefficientMap_functorial_additive : ∀ (R : Type) [CommRing R] (K : Cx R) (n : ℤ), (∀ (F : Shv R) x, HK.post R K (𝟙 F) n x = x) ∧ (∀ {F G M : Shv R} (φ : F ⟶ G) (ψ : G ⟶ M) x, HK.post R K (φ ≫ ψ) n x = HK.post R K ψ n (HK.post R K φ n x)) ∧ (∀ {F G : Shv R} (φ ψ : F ⟶ G), HK.post R K (φ + ψ) n = HK.post R K φ n + HK.post R K ψ n) ∧ (∀ {F G : Shv R} (φ : F ⟶ G) (c : ℤ) x, HK.post R K (c • φ) n x = c • HK.post R K φ n x) ∧ ∀ {L : Cx R} (f : L ⟶ K) {F G : Shv R} (φ : F ⟶ G) x, HK.pull R f G n (HK.post R K φ n x) = HK.post R L φ n (HK.pull R f F n x) := by
  first | (exact @GlobalTheory.EtC.PostFun.main) | (exact GlobalTheory.EtC.PostFun.main) | (intros; apply GlobalTheory.EtC.PostFun.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenIsIrreducibleComponentOfRationalPointSmootStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_isIrreducible_componentOfRationalPoint_smooth : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)) (e : Spec (CommRingCat.of k) ⟶ X), Smooth f → e ≫ f = 𝟙 _ → IsOpen {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} ∧ IsIrreducible {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by
  first | exact @GlobalTheory.isOpen_and_isIrreducible_sectionComponent_of_smooth_field | exact GlobalTheory.isOpen_and_isIrreducible_sectionComponent_of_smooth_field | (intros; apply GlobalTheory.isOpen_and_isIrreducible_sectionComponent_of_smooth_field <;> assumption)
end

