module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1942
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetAbelianLocusOfGoodReduction
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1971
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.DivSheafA
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0815

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegPreDataDescendsFg
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegelDataDescent

theorem exists_isSquare {S' S : Scheme.{0}} {A' : Over S'} {A : Over S} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (w : φ ≫ A.hom = A'.hom ≫ f) :
    ∃ φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left, Geo.Tor.IsSquare φ φ₂ := by
  have v₁ : (fst A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  have v₂ : (snd A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  exact ⟨pullback.lift ((fst A' A').left ≫ φ) ((snd A' A').left ≫ φ)
    (by rw [Category.assoc, Category.assoc, w, reassoc_of% v₁, reassoc_of% v₂]),
    pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩

theorem isSquare_w {S' S : Scheme.{0}} {A' : Over S'} {A : Over S} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (w : φ ≫ A.hom = A'.hom ≫ f) {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left} (h : Geo.Tor.IsSquare φ φ₂) :
    φ₂ ≫ (A ⊗ A).hom = (A' ⊗ A').hom ≫ f := by
  have w₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have v₁ : (fst A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  have h₁ := h.1
  rw [← w₁, reassoc_of% h₁, w, reassoc_of% v₁]

theorem isSquare_comp {S'' S' S : Scheme.{0}} {A'' : Over S''} {A' : Over S'} {A : Over S}
    {ψ : A''.left ⟶ A'.left} {φ : A'.left ⟶ A.left} {χ : A''.left ⟶ A.left} (e : ψ ≫ φ = χ)
    {ψ₂ : (A'' ⊗ A'').left ⟶ (A' ⊗ A').left} {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}
    {χ₂ : (A'' ⊗ A'').left ⟶ (A ⊗ A).left} (hψ : Geo.Tor.IsSquare ψ ψ₂) (hφ : Geo.Tor.IsSquare φ φ₂)
    (hχ : Geo.Tor.IsSquare χ χ₂) : ψ₂ ≫ φ₂ = χ₂ := by
  have a₁ := hψ.1
  have a₂ := hψ.2
  apply pullback.hom_ext
  · change _ ≫ (fst A A).left = _ ≫ (fst A A).left
    rw [Category.assoc, hφ.1, reassoc_of% a₁, hχ.1, e]
  · change _ ≫ (snd A A).left = _ ≫ (snd A A).left
    rw [Category.assoc, hφ.2, reassoc_of% a₂, hχ.2, e]

theorem isPullback_of_isSquare {S' S : Scheme.{0}} {A' : Over S'} {A : Over S} {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (hA : IsPullback φ A'.hom A.hom f) {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}
    (h : Geo.Tor.IsSquare φ φ₂) : IsPullback φ₂ (A' ⊗ A').hom (A ⊗ A).hom f := by
  have w₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have w₂ : (snd A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have v₁ : (fst A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  have v₂ : (snd A' A').left ≫ A'.hom = (A' ⊗ A').hom := Over.w _
  have h₁ := h.1
  have h₂ := h.2
  refine ⟨⟨isSquare_w hA.w h⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => pullback.lift
      (hA.lift (s.fst ≫ (fst A A).left) s.snd (by rw [Category.assoc, w₁, s.condition]))
      (hA.lift (s.fst ≫ (snd A A).left) s.snd (by rw [Category.assoc, w₂, s.condition]))
      (by rw [IsPullback.lift_snd, IsPullback.lift_snd])) (fun s => ?_) (fun s => ?_)
    (fun s m h1 h2 => ?_)⟩⟩
  · apply pullback.hom_ext
    · change _ ≫ (fst A A).left = _ ≫ (fst A A).left
      rw [Category.assoc, h₁, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
    · change _ ≫ (snd A A).left = _ ≫ (snd A A).left
      rw [Category.assoc, h₂, ← Category.assoc]
      exact (congrArg (· ≫ φ) (pullback.lift_snd _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
  · rw [← v₁, ← Category.assoc]
    exact (congrArg (· ≫ A'.hom) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_snd _ _ _ _)
  · apply pullback.hom_ext
    · refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
      change _ ≫ (fst A' A').left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₁]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₁]
    · refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      change _ ≫ (snd A' A').left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₂]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₂]

end GlobalTheory.SiegelDataDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAffineOpenFinitePresentationStalkKaehlerFr
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory.SmoothStalk

theorem finitePresentation_algX {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [LocallyOfFinitePresentation p]
    (U : X.affineOpens) : (algX p U.1).FinitePresentation := by
  have h := HasRingHomProperty.appLE @LocallyOfFinitePresentation p inferInstance ⟨⊤, isAffineOpen_top _⟩ U le_top
  refine RingHom.FinitePresentation.comp h ?_
  refine RingHom.FinitePresentation.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.surjective ?_
  have : RingHom.ker (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).1 (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.injective
  rw [this]; exact Submodule.fg_bot

theorem smooth_stalk : ∀ (k : Type) [Field k] (X : Scheme.{0}) (p : X ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n p] (U : X.affineOpens) (x : X) (hx : x ∈ U.1), letI := (algX p U.1).toAlgebra; letI := ((X.presheaf.germ U.1 x hx).hom.comp (algX p U.1)).toAlgebra; Algebra.FinitePresentation k Γ(X, U.1) ∧ Module.Free (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] ∧ Module.Finite (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] ∧ Module.finrank (X.presheaf.stalk x) Ω[X.presheaf.stalk x⁄k] = n := by
  intro k _ X p n _ U x hx
  haveI : Smooth p := SmoothOfRelativeDimension.smooth n p
  refine ⟨?_, ?_⟩
  · exact finitePresentation_algX p U
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension n) p ‹_› ⟨⊤, isAffineOpen_top _⟩ U le_top
  obtain ⟨s, hs, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  obtain ⟨t, hxt⟩ : ∃ t : (s : Set Γ(X, U.1)), x ∈ X.basicOpen (t : Γ(X, U.1)) :=
    Opens.mem_iSup.1 (((IsAffineOpen.iSup_basicOpen_eq_self_iff U.2).2 hs).ge hx)
  have := IsAffineOpen.isLocalization_basicOpen U.2 (t : Γ(X, U.1))
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    (h t t.2 Γ(X, X.basicOpen (t : Γ(X, U.1))))
  set V := X.basicOpen (t : Γ(X, U.1))
  have hVU : V ≤ U.1 := X.basicOpen_le _
  have h₂ : (algX p V).IsStandardSmoothOfRelativeDimension n := by
    rw [← GlobalTheory.TopForm.resG_comp_algX p hVU]
    exact h₁
  have hV : IsAffineOpen V := U.2.basicOpen _
  letI iA : Algebra k Γ(X, V) := (algX p V).toAlgebra
  letI iS : Algebra Γ(X, V) (X.presheaf.stalk x) := (X.presheaf.germ V x hxt).hom.toAlgebra
  letI iK : Algebra k (X.presheaf.stalk x) := ((X.presheaf.germ U.1 x hx).hom.comp (algX p U.1)).toAlgebra
  have hcomp : ((X.presheaf.germ U.1 x hx).hom.comp (algX p U.1)) = (X.presheaf.germ V x hxt).hom.comp (algX p V) := by
    rw [← GlobalTheory.TopForm.resG_comp_algX p hVU, ← RingHom.comp_assoc]
    congr 1
    rw [← X.presheaf.germ_res (homOfLE hVU) x hxt]
    rfl
  haveI : IsScalarTower k Γ(X, V) (X.presheaf.stalk x) := IsScalarTower.of_algebraMap_eq' hcomp
  haveI : Algebra.IsStandardSmoothOfRelativeDimension n k Γ(X, V) := h₂
  haveI hloc : IsLocalization.AtPrime (X.presheaf.stalk x) (hV.primeIdealOf ⟨x, hxt⟩).asIdeal :=
    hV.isLocalization_stalk ⟨x, hxt⟩
  haveI : Algebra.FormallyEtale Γ(X, V) (X.presheaf.stalk x) :=
    Algebra.FormallyEtale.of_isLocalization (hV.primeIdealOf ⟨x, hxt⟩).asIdeal.primeCompl
  have hbc := KaehlerDifferential.isBaseChange_of_formallyEtale k Γ(X, V) (X.presheaf.stalk x)
  haveI : Nontrivial Γ(X, V) := (X.presheaf.germ V x hxt).hom.domain_nontrivial
  haveI : Module.Free Γ(X, V) Ω[Γ(X, V)⁄k] := by
    obtain ⟨ι, σ, _, _, P, -⟩ := ‹Algebra.IsStandardSmoothOfRelativeDimension n k Γ(X, V)›.out
    exact P.free_kaehlerDifferential
  have hr := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (R := k) (S := Γ(X, V)) n
  haveI : Module.Finite Γ(X, V) Ω[Γ(X, V)⁄k] := Module.finite_of_rank_eq_nat hr
  have hfr : Module.finrank Γ(X, V) Ω[Γ(X, V)⁄k] = n := Module.finrank_eq_of_rank_eq hr
  let b := Module.Free.chooseBasis Γ(X, V) Ω[Γ(X, V)⁄k]
  let b' := IsBaseChange.basis b hbc
  refine ⟨Module.Free.of_basis b', Module.Finite.of_basis b', ?_⟩
  rw [Module.finrank_eq_card_basis b', ← hfr, Module.finrank_eq_card_basis b]

end GlobalTheory.SmoothStalk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothExistsPointLiftSquareZeroLocalRing
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmoothPtLift

set_option autoImplicit false

theorem exists_lift (U S : Scheme.{0}) (p : U ⟶ S) [Smooth p] (C : Type) [CommRing C] [IsLocalRing C]
    (I : Ideal C) (hI : I ^ 2 = ⊥) (s : Sp C ⟶ S) (u₀ : Sp (C ⧸ I) ⟶ U)
    (hw : u₀ ≫ p = spMap (Ideal.Quotient.mk I) ≫ s) :
    ∃ u : Sp C ⟶ U, spMap (Ideal.Quotient.mk I) ≫ u = u₀ ∧ u ≫ p = s := by
  have hItop : I ≠ ⊤ := by
    rintro rfl
    have h1 : (1 : C) ∈ (⊤ : Ideal C) ^ 2 := by rw [Ideal.top_pow]; exact Submodule.mem_top
    rw [hI, Ideal.mem_bot] at h1
    exact one_ne_zero h1
  haveI : Nontrivial (C ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
  haveI : IsLocalRing (C ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk I) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let t₀ : Sp (C ⧸ I) := IsLocalRing.closedPoint (C ⧸ I)
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (p (u₀ t₀))) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
    U.isBasis_affineOpens.exists_subset_of_mem_open (a := u₀ t₀) hxW (W.2.preimage p.continuous)
  haveI : IsOpenImmersion hW.fromSpec := hW.isOpenImmersion_fromSpec
  haveI : IsOpenImmersion hV.fromSpec := hV.isOpenImmersion_fromSpec
  have hmap : (spMap (Ideal.Quotient.mk I)) t₀ = IsLocalRing.closedPoint C :=
    IsLocalRing.comap_closedPoint (Ideal.Quotient.mk I)
  have hsW : Set.range s ⊆ Set.range hW.fromSpec := by
    rw [hW.range_fromSpec]
    rintro _ ⟨z, rfl⟩
    have h1 : s (IsLocalRing.closedPoint C) ∈ W := by
      rw [← hmap, ← Scheme.Hom.comp_apply, ← hw, Scheme.Hom.comp_apply]
      exact hxW
    exact ((IsLocalRing.specializes_closedPoint z).map s.continuous).mem_open W.2 h1
  have hu₀V : Set.range u₀ ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec]
    rintro _ ⟨z, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint z).map u₀.continuous).mem_open V.2 hxV
  obtain ⟨a, ha⟩ : ∃ a, Spec.map a = IsOpenImmersion.lift hW.fromSpec s hsW := ⟨_, Spec.map_preimage _⟩
  obtain ⟨b₀, hb₀⟩ : ∃ b, Spec.map b = IsOpenImmersion.lift hV.fromSpec u₀ hu₀V :=
    ⟨_, Spec.map_preimage _⟩
  have key : p.appLE W V hVW ≫ b₀ = a ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) := by
    apply Spec.map_injective
    rw [← cancel_mono hW.fromSpec, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      IsAffineOpen.SpecMap_appLE_fromSpec p hW hV hVW, hb₀, ha, IsOpenImmersion.lift_fac_assoc,
      IsOpenImmersion.lift_fac, hw]
  have hsm := p.smooth_appLE hW hV hVW
  algebraize [(p.appLE W V hVW).hom, a.hom]
  let g : Γ(U, V) →ₐ[Γ(S, W)] C ⧸ I :=
    { b₀.hom with
      commutes' := fun r => by
        have := congrArg (fun f => f.hom r) key
        exact this }
  let b := Algebra.FormallySmooth.lift I ⟨2, hI⟩ g
  refine ⟨Spec.map (CommRingCat.ofHom b.toRingHom) ≫ hV.fromSpec, ?_, ?_⟩
  · have e : CommRingCat.ofHom b.toRingHom ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) = b₀ := by
      ext x
      exact Algebra.FormallySmooth.mk_lift I ⟨2, hI⟩ g x
    rw [← Category.assoc, ← Spec.map_comp, e, hb₀, IsOpenImmersion.lift_fac]
  · have e : p.appLE W V hVW ≫ CommRingCat.ofHom b.toRingHom = a := by
      ext r
      exact b.commutes r
    rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec p hW hV hVW, ← Category.assoc,
      ← Spec.map_comp, e, ha, IsOpenImmersion.lift_fac]

end GlobalTheory.SmoothPtLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncStalkRegularParametersFromAffineOpen
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

namespace GlobalTheory.SncStalk

theorem rsp_of_units {R : Type} [CommRing R] [IsLocalRing R] {n : ℕ} (y z : Fin n → R) (u : Fin n → Rˣ)
    (h : ∀ i, z i = (u i : R) * y i) (hy : ReciprocityTheory.AnForm.R.FinalTheorems.Rsp R n y) :
    ReciprocityTheory.AnForm.R.FinalTheorems.Rsp R n z := by
  refine ⟨?_, hy.2⟩
  rw [← hy.1]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [h i]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have : y i = ((u i)⁻¹ : Rˣ) * z i := by rw [h i, ← mul_assoc, Units.inv_mul, one_mul]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem stalk_snc : ∀ (X : Scheme.{0}) (I : X.IdealSheafData), ReciprocityTheory.AnForm.R.FinalTheorems.Snc I →
    ∀ (U : X.affineOpens) (x : X) (hx : x ∈ U.1), IsRegularLocalRing (X.presheaf.stalk x) ∧
      ∃ (m : ℕ) (a : Fin m → Γ(X, U.1)) (J : Finset (Fin m)),
        ReciprocityTheory.AnForm.R.FinalTheorems.Rsp (X.presheaf.stalk x) m (fun i => (X.presheaf.germ U.1 x hx).hom (a i)) ∧
        (I.ideal U).map (X.presheaf.germ U.1 x hx).hom =
          Ideal.span {(X.presheaf.germ U.1 x hx).hom (∏ i ∈ J, a i)} := by
  intro X I hI U x hx
  obtain ⟨hreg, U₁, hx₁, n, f, J, hR, hI₁⟩ := hI x
  refine ⟨hreg, ?_⟩
  letI : Algebra Γ(X, U.1) (X.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  haveI hloc := U.2.isLocalization_stalk ⟨x, hx⟩
  have halg : ∀ r : Γ(X, U.1), algebraMap Γ(X, U.1) (X.presheaf.stalk x) r =
      (X.presheaf.germ U.1 x hx).hom r := fun r => rfl
  have key : ∀ i : Fin n, ∃ (a : Γ(X, U.1)) (t : Γ(X, U.1)),
      IsUnit ((X.presheaf.germ U.1 x hx).hom t) ∧
      (X.presheaf.germ U.1 x hx).hom a = (X.presheaf.germ U₁.1 x hx₁).hom (f i) * (X.presheaf.germ U.1 x hx).hom t := by
    intro i
    obtain ⟨⟨a, t⟩, hat⟩ := IsLocalization.mk'_surjective (U.2.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
      ((X.presheaf.germ U₁.1 x hx₁).hom (f i))
    refine ⟨a, t, ?_, ?_⟩
    · rw [← halg]; exact IsLocalization.map_units _ t
    · rw [← halg, ← halg, ← hat]
      exact (IsLocalization.mk'_spec _ a t).symm
  choose a t ht hat using key
  refine ⟨n, a, J, ?_, ?_⟩
  · refine rsp_of_units _ _ (fun i => (ht i).unit) ?_ hR
    intro i
    rw [hat i, IsUnit.unit_spec, mul_comm]
  · rw [← ReciprocityTheory.AnForm.R.ds_stalkId_eq_map I U x hx, ReciprocityTheory.AnForm.R.ds_stalkId_eq_map I U₁ x hx₁, hI₁,
      Ideal.map_span, Set.image_singleton, map_prod, map_prod]
    have : ∏ i ∈ J, (X.presheaf.germ U.1 x hx).hom (a i) =
        (∏ i ∈ J, (X.presheaf.germ U.1 x hx).hom (t i)) * ∏ i ∈ J, (X.presheaf.germ U₁.1 x hx₁).hom (f i) := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hat i, mul_comm]
    rw [this, Ideal.span_singleton_mul_left_unit]
    exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun i _ => ht i

end GlobalTheory.SncStalk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapFromSpecStalkTopLeIff
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory

theorem spMap_fromSpecStalk_le_preimage_iff (X : Scheme.{0}) (x : X) (Ω : Type) [CommRing Ω] [IsLocalRing Ω]
    (ψ : X.presheaf.stalk x →+* Ω) (hψ : IsLocalHom ψ) (O : X.Opens) :
    ⊤ ≤ (spMap ψ ≫ X.fromSpecStalk x) ⁻¹ᵁ O ↔ x ∈ O := by
  constructor
  · intro h
    let p : ↥(Sp Ω) := closedPoint Ω
    have hm : (spMap ψ ≫ X.fromSpecStalk x) p ∈ O := h (x := p) trivial
    rw [Scheme.Hom.comp_apply] at hm
    have e : (spMap ψ) p = (closedPoint (X.presheaf.stalk x) : ↥(Spec (X.presheaf.stalk x))) := by
      show PrimeSpectrum.comap ψ (closedPoint Ω) = _
      exact IsLocalRing.comap_closedPoint ψ
    rw [e, Scheme.fromSpecStalk_closedPoint] at hm
    exact hm
  · intro hx w _
    have : X.fromSpecStalk x (spMap ψ w) ∈ Set.range (X.fromSpecStalk x) := ⟨_, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    show (spMap ψ ≫ X.fromSpecStalk x) w ∈ O
    rw [Scheme.Hom.comp_apply]
    exact Specializes.mem_open (x := X.fromSpecStalk x (spMap ψ w)) this O.isOpen hx

theorem spMap_fromSpecStalk_top_le_iff : ∀ (X : Scheme.{0}) (x : X) (Ω : Type) [CommRing Ω] [IsLocalRing Ω]
    (ψ : X.presheaf.stalk x →+* Ω), IsLocalHom ψ → ∀ O : X.Opens,
    ⊤ ≤ (spMap ψ ≫ X.fromSpecStalk x) ⁻¹ᵁ O ↔ x ∈ O :=
  fun X x Ω _ _ ψ hψ O => spMap_fromSpecStalk_le_preimage_iff X x Ω ψ hψ O

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecFibreProductLocalArtinianGlueExistsUnique
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem spec_localArtinian_point_eq (P : CommRingCat.{0}) [IsLocalRing P] [IsArtinianRing P]
    (x y : Spec P) : x = y := by
  apply PrimeSpectrum.ext
  haveI := x.isPrime
  haveI := y.isPrime
  rw [IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime x.asIdeal),
    IsLocalRing.eq_maximalIdeal (IsArtinianRing.isMaximal_of_isPrime y.asIdeal)]

theorem spec_map_injective_of_surjective {R S : CommRingCat.{0}} (f : R ⟶ S) (hf : Function.Surjective f) :
    Function.Injective (Spec.map f) := fun x y h =>
  PrimeSpectrum.comap_injective_of_surjective f.hom hf h

theorem spec_pullback_localArtinian_glue_existsUnique : ∀ (P B₁ B₂ B₀ : CommRingCat.{0}) (f₁ : P ⟶ B₁) (f₂ : P ⟶ B₂) (g₁ : B₁ ⟶ B₀) (g₂ : B₂ ⟶ B₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective f₁ → Function.Surjective f₂ → Nontrivial B₀ → ∀ (Z : Scheme.{0}) (a : Spec B₁ ⟶ Z) (b : Spec B₂ ⟶ Z), Spec.map g₁ ≫ a = Spec.map g₂ ≫ b → ∃! w : Spec P ⟶ Z, Spec.map f₁ ≫ w = a ∧ Spec.map f₂ ≫ w = b := by
  intro P B₁ B₂ B₀ f₁ f₂ g₁ g₂ hP hloc hart hs₁ hs₂ hnt Z a b hab
  have hnt₁ : Nontrivial B₁ := RingHom.domain_nontrivial g₁.hom
  have hnt₂ : Nontrivial B₂ := RingHom.domain_nontrivial g₂.hom
  obtain ⟨y₀⟩ : Nonempty (Spec B₀) := inferInstanceAs (Nonempty (PrimeSpectrum B₀))
  have hone₁ : ∀ y y' : Spec B₁, y = y' := fun y y' =>
    spec_map_injective_of_surjective f₁ hs₁ (spec_localArtinian_point_eq P _ _)
  have hone₂ : ∀ y y' : Spec B₂, y = y' := fun y y' =>
    spec_map_injective_of_surjective f₂ hs₂ (spec_localArtinian_point_eq P _ _)
  obtain ⟨V, hV, hzV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤)
    (x := a (Spec.map g₁ y₀)) trivial
  have hza : Set.range a ⊆ Set.range hV.fromSpec := by
    rintro _ ⟨y, rfl⟩; rw [hV.range_fromSpec, hone₁ y (Spec.map g₁ y₀)]; exact hzV
  have hzb : Set.range b ⊆ Set.range hV.fromSpec := by
    rintro _ ⟨y, rfl⟩
    rw [hV.range_fromSpec, hone₂ y (Spec.map g₂ y₀)]
    have : b (Spec.map g₂ y₀) = a (Spec.map g₁ y₀) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hab]
    rw [this]; exact hzV
  haveI := hV.isOpenImmersion_fromSpec
  set φ₁ := Spec.preimage (IsOpenImmersion.lift hV.fromSpec a hza) with hφ₁
  set φ₂ := Spec.preimage (IsOpenImmersion.lift hV.fromSpec b hzb) with hφ₂
  have ha : Spec.map φ₁ ≫ hV.fromSpec = a := by
    rw [hφ₁, Spec.map_preimage, IsOpenImmersion.lift_fac]
  have hb : Spec.map φ₂ ≫ hV.fromSpec = b := by
    rw [hφ₂, Spec.map_preimage, IsOpenImmersion.lift_fac]
  have hφ : φ₁ ≫ g₁ = φ₂ ≫ g₂ := by
    apply Spec.map_injective
    rw [← cancel_mono hV.fromSpec, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc,
      ha, hb, hab]
  have key : ∀ w : Spec P ⟶ Z, Spec.map f₁ ≫ w = a → Spec.map f₂ ≫ w = b →
      w = Spec.map (hP.lift φ₁ φ₂ hφ) ≫ hV.fromSpec := by
    intro w hw₁ hw₂
    have hr : Set.range w ⊆ Set.range hV.fromSpec := by
      rintro _ ⟨x, rfl⟩
      rw [spec_localArtinian_point_eq P x (Spec.map f₁ (Spec.map g₁ y₀)), ← Scheme.Hom.comp_apply, hw₁]
      exact hza ⟨_, rfl⟩
    rw [← IsOpenImmersion.lift_fac hV.fromSpec w hr, ← Spec.map_preimage (IsOpenImmersion.lift hV.fromSpec w hr)]
    congr 2
    apply hP.hom_ext
    · rw [IsPullback.lift_fst]
      apply Spec.map_injective
      rw [← cancel_mono hV.fromSpec, Spec.map_comp, Category.assoc, Spec.map_preimage,
        IsOpenImmersion.lift_fac, hw₁, ha]
    · rw [IsPullback.lift_snd]
      apply Spec.map_injective
      rw [← cancel_mono hV.fromSpec, Spec.map_comp, Category.assoc, Spec.map_preimage,
        IsOpenImmersion.lift_fac, hw₂, hb]
  refine ⟨Spec.map (hP.lift φ₁ φ₂ hφ) ≫ hV.fromSpec, ⟨?_, ?_⟩, fun w hw => key w hw.1 hw.2⟩
  · rw [← Category.assoc, ← Spec.map_comp, IsPullback.lift_fst, ha]
  · rw [← Category.assoc, ← Spec.map_comp, IsPullback.lift_snd, hb]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecMapFromSpecStalkOriginCompStructureEq
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FormalOrigin

theorem spMap_fromSpecStalk_origin_hom (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] (Ω : Type)
    [CommRing Ω] (ψ : G.left.presheaf.stalk (origin G) →+* Ω) :
    spMap ψ ≫ G.left.fromSpecStalk (origin G) ≫ G.hom = spMap (ψ.comp (constO G)) := by
  have e : G.left.fromSpecStalk (origin G) ≫ G.hom = spMap (constO G) := by
    have e' : CommRingCat.ofHom (constO G) =
        (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ G.hom.appTop ≫ G.left.presheaf.germ ⊤ (origin G) trivial := by
      change (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ G.hom.appLE ⊤ ⊤ (fun _ _ => trivial) ≫
        G.left.presheaf.germ ⊤ (origin G) trivial = _
      have h : G.hom.appLE ⊤ ⊤ (fun _ _ => trivial) = G.hom.appTop := Scheme.Hom.appLE_eq_app _
      rw [h]
    simp only [spMap]
    rw [e', Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ_assoc, Category.assoc, Category.assoc,
      ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rw [e]
  simp only [spMap]
  rw [← Spec.map_comp]
  rfl

end GlobalTheory.FormalOrigin
end

