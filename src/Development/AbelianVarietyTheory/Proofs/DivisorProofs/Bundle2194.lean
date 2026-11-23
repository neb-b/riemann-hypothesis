module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2095
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2123
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0740
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0755
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0526
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1298
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2071
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2098
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2099
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelStableIffPulledBackIdentity
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.TrStab

theorem one_left' {S : Scheme.{0}} (G : Over S) [GrpObj G] (T : Over S) : (1 : T ⟶ G).left = T.hom ≫ η[G].left := by
  rw [Hom.one_def, Over.comp_left, ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.toUnit_left']

theorem eq_one_of_push {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {θ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f θ) {T : Over S'} (x : T ⟶ G')
    (hx : x.left ≫ θ = T.hom ≫ f ≫ η[G].left) : x = 1 := by
  ext
  apply h.1.hom_ext
  · rw [hx, one_left', Category.assoc, ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left h]
  · rw [Over.w x, Over.w (1 : T ⟶ G')]

theorem push_one {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {θ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f θ) (T : Over S') :
    (1 : T ⟶ G').left ≫ θ = T.hom ≫ f ≫ η[G].left := by
  rw [one_left', Category.assoc, ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left h]

end GlobalTheory.UPel.HT.ES.TrStab

namespace GlobalTheory.UPel.HT.ES

open TrStab

theorem kerStableAt_iff_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (T Y : Scheme.{0}) (s₁ : T ⟶ Sp R) (s : Y ⟶ Sp R) (t : T ⟶ Y) (o₁ : Obj b N s₁) (o : Obj b N s) (m : ObjMap o₁ o t) (B₁ : Over T) [GrpObj B₁] [IsCommMonObj B₁] (B : Over Y) [GrpObj B] [IsCommMonObj B] (θ : B₁.left ⟶ B.left) (ψ₁ : o₁.A ⟶ B₁) (ψ : o.A ⟶ B), IsGrpPullback B₁ B t θ → m.φ ≫ ψ.left = ψ₁.left ≫ θ → (KerStableAt o ψ t ↔ KerStableAt o₁ ψ₁ (𝟙 T)) := by
  intro p _ D R _ b N T Y s₁ s t o₁ o m B₁ _ _ B _ _ θ ψ₁ ψ hB hψ
  constructor
  · intro h T' σ hσ g hg a
    rw [Category.comp_id] at hσ
    subst hσ
    have hG : pushPt m.cart.1.w g ≫ ψ = 1 := by
      ext
      rw [one_left', Over.comp_left]
      show (g.left ≫ m.φ) ≫ ψ.left = _
      rw [Category.assoc, hψ, ← Category.assoc, ← Over.comp_left, hg, push_one hB]
      rfl
    have h2 := h (Over.mk (T'.hom ≫ t)) T'.hom rfl (pushPt m.cart.1.w g) hG a
    apply eq_one_of_push hB
    have e := congrArg Over.Hom.left h2
    rw [one_left', Over.comp_left, Over.comp_left] at e
    simp only [Over.comp_left, Category.assoc]
    rw [← hψ, ← Category.assoc (o₁.act.act a).left, m.act a, Category.assoc]
    exact e
  · intro h T0 σ hσ g hg a
    have w : g.left ≫ o.A.hom = σ ≫ t := by rw [Over.w g, hσ]
    let g₁ : Over.mk σ ⟶ o₁.A := Over.homMk (m.cart.1.lift g.left σ w) (m.cart.1.lift_snd _ _ _)
    have hg₁ : g₁.left ≫ m.φ = g.left := m.cart.1.lift_fst _ _ _
    have h1 : g₁ ≫ ψ₁ = 1 := by
      apply eq_one_of_push hB
      rw [Over.comp_left, Category.assoc, ← hψ, ← Category.assoc, hg₁, ← Over.comp_left, hg, one_left', ← hσ, Category.assoc]
      rfl
    have h2 := h (Over.mk σ) σ (Category.comp_id σ) g₁ h1 a
    ext
    rw [one_left', Over.comp_left, Over.comp_left, ← hg₁, Category.assoc, ← Category.assoc m.φ (o.act.act a).left,
      ← m.act a]
    simp only [Category.assoc]
    rw [hψ]
    have e : (g₁ ≫ o₁.act.act a ≫ ψ₁).left ≫ θ = (1 : Over.mk σ ⟶ B₁).left ≫ θ := by rw [h2]
    rw [push_one hB] at e
    simp only [Over.comp_left, Category.assoc] at e
    rw [e, ← hσ, Category.assoc]
    rfl

end GlobalTheory.UPel.HT.ES
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyValueUnitTraitsOfUniformisedTraits
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyEven

theorem dualMapR_eq_of_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (F : DualNumber R →+* DualNumber R')
    (h1 : ∀ a, F (algebraMap R _ a) = algebraMap R' _ (f a)) (h2 : F DualNumber.eps = DualNumber.eps) :
    F = Chart.dualMapR f := by
  refine RingHom.ext fun a => ?_
  have hx : ∀ (S : Type) [CommRing S] (b : DualNumber S),
      b = algebraMap S (DualNumber S) (TrivSqZeroExt.fst b) + algebraMap S (DualNumber S) (TrivSqZeroExt.snd b) * DualNumber.eps := by
    intro S _ b
    rw [← Algebra.smul_def, ← DualNumber.inr_eq_smul_eps, TrivSqZeroExt.algebraMap_eq_inl,
      TrivSqZeroExt.inl_fst_add_inr_snd_eq]
  have hF : F a = algebraMap R' (DualNumber R') (f (TrivSqZeroExt.fst a)) +
      algebraMap R' (DualNumber R') (f (TrivSqZeroExt.snd a)) * DualNumber.eps := by
    conv_lhs => rw [hx R a]
    rw [map_add (f := _), map_mul, h1, h1, h2]
  rw [hF, ← Algebra.smul_def, ← DualNumber.inr_eq_smul_eps, TrivSqZeroExt.algebraMap_eq_inl]
  rfl

theorem keyTrait_of_keyTraitU : ∀ κ : Rule, KeyTraitU κ → KeyTrait κ := by
  intro κ hU V _ _ _ _ hA hF G _ _ L σ x y hSA hUn hLie hNz hKey
  obtain ⟨D, A, U, e, he⟩ := hUn
  obtain ⟨φ, hφe, ψ, F, hPB, hψ, hRig, hTh, hF1, hF2, hv⟩ := hKey
  obtain ⟨θ, hθm, hθφ⟩ := grpPullback_iso (isGrpPullback_pullback G (jK V)) hPB

  obtain ⟨e', he', heR⟩ := GlobalTheory.T.exists_rescaled_iso_preserving_rigidification G U.LG L e he
  obtain ⟨σ', hσ', hnz⟩ := _root_.GlobalTheory.SecTransport.main e' he' U.LG.isLB L.isLB σ
  obtain ⟨w₀, hw₀, hPW⟩ := _root_.GlobalTheory.IsoComp.isoCancelGerm θ.hom.left φ (pullback.fst G.hom (jK V)) hθφ x.P.L L.L U.LG.L x.P.isLB L.isLB U.LG.isLB ψ e' hψ he'
  let U' : Unif (IsLocalRing.maximalIdeal V) D x.P G :=
    { toUnifPre := { U.toUnifPre with gen := θ, gen_hom := hθm, ext := ⟨w₀, hw₀⟩ }, expand := U.expand }
  have hinv : U'.gen.inv.left ≫ pullback.fst G.hom (jK V) = φ := by
    show θ.inv.left ≫ pullback.fst G.hom (jK V) = φ
    rw [← hθφ, ← Category.assoc, ← Over.comp_left, θ.inv_hom_id, Over.id_left, Category.id_comp]
  have hFd := dualMapR_eq_of_map _ F hF1 hF2
  haveI : IsMonHom θ.hom := hθm
  refine hU V hA hF D x G hSA U' w₀ ⟨hw₀, x.rig_gen, ?_⟩ y hLie (fun i => ?_) σ' ?_ ?_
  · exact GlobalTheory.T.iso_preserves_rigidification_at_origin V G x.P.A θ.hom φ hθφ hφe x.P.L L.L U.LG.L x.P.isLB L.isLB U.LG.isLB x.rig L.rig U.LG.rig ψ e' w₀ hPW hRig heR
  · show (x.v i).left ≫ (U'.gen.inv.left ≫ pullback.fst G.hom (jK V)) = _
    rw [hinv, hv i, hFd]
  · intro s
    obtain ⟨z, hz, hz'⟩ := hNz s
    exact ⟨z, hz, hnz hz'⟩
  · exact _root_.GlobalTheory.secMaps_secPull_of_pointwise θ.hom.left φ _ hθφ x.P.L L.L U.LG.L L.isLB ψ e' w₀ hPW x.th σ σ' hTh hσ'

end GlobalTheory.KeyEven

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerTangentDifference
section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.FlagTan

theorem exists_dir_eq_of_smooth : ∀ (k₀ : Type) [Field k₀] (X : Scheme.{0}) (s : X ⟶ Spec (CommRingCat.of k₀)) (n : ℕ),
    SmoothOfRelativeDimension n s → ∀ (K : Type) [Field K] (κ : k₀ →+* K) (ι : Type) [Fintype ι],
    Fintype.card ι = n → ∀ Xι : Spec (CommRingCat.of (TrivSqZeroExt K (ι → K))) ⟶ X,
    Xι ≫ s = Spec.map (CommRingCat.ofHom ((TrivSqZeroExt.inlHom K (ι → K)).comp κ)) →
    (∀ M M' : ι → K,
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (Fintype.linearCombination K M)).toRingHom) ≫ Xι =
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (Fintype.linearCombination K M')).toRingHom) ≫ Xι → M = M') →
    ∀ x' : Spec (CommRingCat.of (DualNumber K)) ⟶ X,
    x' ≫ s = Spec.map (CommRingCat.ofHom ((TrivSqZeroExt.inlHom K K).comp κ)) →
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) ≫ x' =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom) ≫ Xι →
    ∃ M : ι → K, x' = Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map (Fintype.linearCombination K M)).toRingHom) ≫ Xι := by
  intro k₀ _ X s n hs K _ κ ι _ hι Xι hXs hinj x' hx's hred
  have hloc : ∀ (M : Type) [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M],
      IsLocalHom (TrivSqZeroExt.fstHom K K M).toRingHom :=
    fun M _ _ _ _ => ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ha⟩
  have cp : ∀ (M : Type) [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M],
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K M).toRingHom) (IsLocalRing.closedPoint K) =
        IsLocalRing.closedPoint (TrivSqZeroExt K M) := fun M _ _ _ _ => by
    haveI := hloc M
    exact IsLocalRing.comap_closedPoint _
  obtain ⟨U, hU, V, hV, hxV, e, hstd⟩ := hs.exists_isStandardSmoothOfRelativeDimension
    ((Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K (ι → K)).toRingHom) ≫ Xι) (IsLocalRing.closedPoint K))
  have h1 : Xι (IsLocalRing.closedPoint (TrivSqZeroExt K (ι → K))) ∈ V := by
    rw [← cp]; exact hxV
  have h2 : x' (IsLocalRing.closedPoint (DualNumber K)) ∈ V := by
    rw [← cp]; have := hxV; rw [← hred] at this; exact this
  obtain ⟨R, rfl⟩ := _root_.GlobalTheory.spec_local_hom_factors_affineOpen X V hV _ Xι h1
  obtain ⟨g, rfl⟩ := _root_.GlobalTheory.spec_local_hom_factors_affineOpen X V hV _ x' h2
  letI := (s.appLE U V e).hom.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension n Γ(Spec (CommRingCat.of k₀), U) Γ(X, V) := hstd
  have key := IsAffineOpen.SpecMap_appLE_fromSpec s hU hV e
  have mono : ∀ {Y : Scheme.{0}} {W : Y.Opens} (hW : IsAffineOpen W) {A : Type} [CommRing A] (φ ψ : Γ(Y, W) →+* A),
      Spec.map (CommRingCat.ofHom φ) ≫ hW.fromSpec = Spec.map (CommRingCat.ofHom ψ) ≫ hW.fromSpec → φ = ψ := by
    intro Y W hW A _ φ ψ h
    have := Spec.map_injective ((cancel_mono hW.fromSpec).1 h)
    exact congrArg CommRingCat.Hom.hom this
  have hsp : ∀ {A : Type} [CommRing A] (φ : Γ(X, V) →+* A),
      (Spec.map (CommRingCat.ofHom φ) ≫ hV.fromSpec) ≫ s =
        Spec.map (CommRingCat.ofHom (φ.comp (s.appLE U V e).hom)) ≫ hU.fromSpec := by
    intro A _ φ
    rw [Category.assoc, ← key, ← Category.assoc, ← Spec.map_comp]
    rfl
  have hc : ∀ (M : Type) [AddCommGroup M] [Module K M] [Module Kᵐᵒᵖ M] [IsCentralScalar K M]
      (φ : Γ(X, V) →+* TrivSqZeroExt K M),
      (Spec.map (CommRingCat.ofHom φ) ≫ hV.fromSpec) ≫ s =
        Spec.map (CommRingCat.ofHom ((TrivSqZeroExt.inlHom K M).comp κ)) →
      ∀ a, φ (s.appLE U V e a) = TrivSqZeroExt.inl (φ (s.appLE U V e a)).fst := by
    intro M _ _ _ _ φ hφ a
    have e1 := hsp φ
    have e2 : Spec.map (CommRingCat.ofHom (((TrivSqZeroExt.inlHom K M).comp (TrivSqZeroExt.fstHom K K M).toRingHom).comp
        (φ.comp (s.appLE U V e).hom))) ≫ hU.fromSpec =
        Spec.map (CommRingCat.ofHom ((TrivSqZeroExt.inlHom K M).comp κ)) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, ← e1, hφ, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
    have := mono hU _ _ (e2.trans (hφ.symm.trans e1))
    exact (RingHom.congr_fun this a).symm
  obtain ⟨M, hM⟩ := _root_.GlobalTheory.FirstOrderPoints.exists_linearCombination_eq Γ(Spec (CommRingCat.of k₀), U) Γ(X, V) K n hstd ι hι R (hc _ R hXs)
    (fun M M' h => hinj M M' (by
      rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp, h]))
    g (fun b => by
      have := mono hV ((TrivSqZeroExt.fstHom K K K).toRingHom.comp g) ((TrivSqZeroExt.fstHom K K (ι → K)).toRingHom.comp R) (by
        rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp, Category.assoc, Category.assoc]
        exact hred)
      exact RingHom.congr_fun this b)
    (hc _ g hx's)
  refine ⟨M, ?_⟩
  rw [hM, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

theorem eq_of_isKS_eq : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' x'' : Sp (DualNumber K) ⟶ Xo.X) (M : GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → GlobalTheory.FlagTan.IsTanX y x'' → GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' M → GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x'' M → x' = x'' := by
  intro hP hG E _ _ _ H Dw l Xo c K _ _ y x' x'' M hpq h' h'' k' k''
  obtain ⟨X, hX, hXy, hXM⟩ : ∃ X : Sp (TrivSqZeroExt K (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K)) ⟶ Xo.X, X ≫ Xo.s = sOf c _ ∧
      spMap (TrivSqZeroExt.fstHom c.F K (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K)).toRingHom ≫ X = y.x ∧
      ∀ M : GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K,
        GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y (spMap (GlobalTheory.FlagTan.dir c M).toRingHom ≫ X) M := by
    first
    | exact _root_.GlobalTheory.FlagTan.KSUniv.ksUniv hP hG E H Dw l Xo c K y hpq
    | exact _root_.GlobalTheory.FlagTan.KSUniv.ksUniv hP E H Dw l Xo c K y hpq
    | exact (_root_.GlobalTheory.FlagTan.KSUniv.ksUniv hP hG E H Dw l Xo c K y hpq)
  have htan : ∀ N, GlobalTheory.FlagTan.IsTanX y (spMap (GlobalTheory.FlagTan.dir c N).toRingHom ≫ X) := fun N => by
    refine ⟨?_, ?_⟩
    · rw [Category.assoc, hX, sOf, sOf, ← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      exact (GlobalTheory.FlagTan.dir c N).commutes _
    · rw [← Category.assoc, ← Spec.map_comp, ← hXy]
      congr 2
      ext z
      simp
  have uniq := fun x hx => _root_.GlobalTheory.FlagTan.isKS_unique hP E H Dw l Xo c K y x hpq hx
  have key := exists_dir_eq_of_smooth (KA l) Xo.X Xo.s Dw.dim Xo.smooth K ((algebraMap c.F K).comp (IntermediateField.inclusion c.le).toRingHom)
    (GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H)) (GlobalTheory.FlagTan.card_HIx (GlobalTheory.FlagTan.isHalf_psiSet H)) X
    (by rw [hX, sOf])
    (fun N N' e => uniq _ (htan N) N N' (hXM N) (e ▸ hXM N'))
  have hk : ∀ x, GlobalTheory.FlagTan.IsTanX y x → ∃ N, x = spMap (GlobalTheory.FlagTan.dir c N).toRingHom ≫ X := fun x hx =>
    key x (by rw [hx.1, sOf]) (hx.2.trans hXy.symm)
  obtain ⟨N', rfl⟩ := hk x' h'
  obtain ⟨N'', rfl⟩ := hk x'' h''
  rw [uniq _ (htan N') N' M (hXM N') k', uniq _ (htan N'') N'' M (hXM N'') k'']

end GlobalTheory.FlagTan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KunnethCupTensorInjective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Kunneth

section Pairs

variable {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R}
  {s' : X' ⟶ Sp R'} {σ : R →+* R'} {φ : X' ⟶ X}
  {C : Type} [Category.{0} C] (A : C ⥤ AffOp X') (B : C ⥤ AffOp X)
  (hle : ∀ T, (A.obj T).unop.1 ≤ φ ⁻¹ᵁ (B.obj T).unop.1)

def toPair : C ⥤ (Pair φ)ᵒᵖ where
  obj T := Opposite.op ⟨((A.obj T).unop, (B.obj T).unop), hle T⟩
  map {T T'} a := (homOfLE (Subtype.coe_le_coe.1
    (Prod.mk_le_mk.2 ⟨leOfHom (A.map a).unop, leOfHom (B.map a).unop⟩) :
      (⟨((A.obj T').unop, (B.obj T').unop), hle T'⟩ : Pair φ) ≤ ⟨((A.obj T).unop, (B.obj T).unop), hle T⟩)).op
  map_id _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  map_comp _ _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)

theorem restrict_pullHO1 (h : φ ≫ s = s' ≫ spMap σ) (c : HO1 s) :
    (CoefMap.restrict (OAff s') A).pull1 (pullHO1 h c) =
      ((pairPull h).comp (CoefMap.restrict (OPair φ s') (toPair A B hle))).pull1 c := by
  rw [CoefMap.pullCohomologyOne_comp, (isPullO_pullHO1 h c : (pairPull h).pull1 c = (pairRes φ s').pull1 (pullHO1 h c))]
  exact CoefMap.pullCohomologyOne_comp (pairRes φ s') (CoefMap.restrict (OPair φ s') (toPair A B hle)) (pullHO1 h c)

end Pairs

end GlobalTheory.Kunneth

namespace GlobalTheory.Kunneth

def prodFun {J J' : Type} [Preorder J] [Preorder J'] {Z : Scheme.{0}} (W : J × J' → Z.affineOpens)
    (hW : Monotone W) : Jᵒᵖ × J'ᵒᵖ ⥤ AffOp Z where
  obj T := Opposite.op (W (T.1.unop, T.2.unop))
  map a := (homOfLE (hW (Prod.mk_le_mk.2 ⟨leOfHom a.1.unop, leOfHom a.2.unop⟩))).op
  map_id _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  map_comp _ _ := Quiver.Hom.unop_inj (Subsingleton.elim _ _)

theorem cup_tmul_injective : ∀ (K : Type) [Field K] (X Y : Over (Sp K)), IsSeparated X.hom → QuasiCompact X.hom →
    IsSeparated Y.hom → QuasiCompact Y.hom → ∀ (n : ℕ) (x : Fin n → HO1 X.hom) (y : Fin n → HO1 Y.hom),
    ∑ i, cup (OAff (X ⊗ Y).hom) (pO1 (fst X Y) (x i)) (pO1 (snd X Y) (y i)) = 0 →
    ∑ i, x i ⊗ₜ[K] y i = 0 := by
  intro K _ X Y hXs hXq hYs hYq n x y hsum
  obtain ⟨J, _, _, U, hU, hUi, hUc⟩ := GlobalTheory.exists_finite_affine_cover_infClosed K X.left X.hom hXs hXq
  obtain ⟨J', _, _, V, hV, hVi, hVc⟩ := GlobalTheory.exists_finite_affine_cover_infClosed K Y.left Y.hom hYs hYq
  choose Wf h1 h2 i1 i2 hWe hi1 hi2 hbij using fun p : J × J' ↦ _root_.GlobalTheory.functions_on_product_of_affine_opens K X Y (U p.1) (V p.2)
  have hWm : Monotone Wf := fun p q hpq ↦ by
    show (Wf p).1 ≤ (Wf q).1
    rw [hWe p, hWe q]
    exact inf_le_inf (Scheme.Hom.preimage_mono _ (hU hpq.1)) (Scheme.Hom.preimage_mono _ (hV hpq.2))
  haveI : Finite J'ᵒᵖ := Finite.of_equiv J' Opposite.equivToOpposite
  let Ψ := prodFun Wf hWm
  let F := hU.functor.op ⋙ OAff X.hom
  let G := hV.functor.op ⋙ OAff Y.hom
  let E := Ψ ⋙ OAff (X ⊗ Y).hom
  let B₁ : Jᵒᵖ × J'ᵒᵖ ⥤ AffOp X.left := CategoryTheory.Prod.fst Jᵒᵖ J'ᵒᵖ ⋙ hU.functor.op
  let B₂ : Jᵒᵖ × J'ᵒᵖ ⥤ AffOp Y.left := CategoryTheory.Prod.snd Jᵒᵖ J'ᵒᵖ ⋙ hV.functor.op
  have hle₁ : ∀ T, (Ψ.obj T).unop.1 ≤ (fst X Y).left ⁻¹ᵁ (B₁.obj T).unop.1 := fun T ↦ h1 (T.1.unop, T.2.unop)
  have hle₂ : ∀ T, (Ψ.obj T).unop.1 ≤ (snd X Y).left ⁻¹ᵁ (B₂.obj T).unop.1 := fun T ↦ h2 (T.1.unop, T.2.unop)
  let m₁ := (pairPull (ovw (fst X Y))).comp (CoefMap.restrict (OPair (fst X Y).left (X ⊗ Y).hom) (toPair Ψ B₁ hle₁))
  let m₂ := (pairPull (ovw (snd X Y))).comp (CoefMap.restrict (OPair (snd X Y).left (X ⊗ Y).hom) (toPair Ψ B₂ hle₂))
  let j₁ : ∀ T : Jᵒᵖ × J'ᵒᵖ, F.obj T.1 →ₐ[K] E.obj T := fun T ↦ i1 (T.1.unop, T.2.unop)
  let j₂ : ∀ T : Jᵒᵖ × J'ᵒᵖ, G.obj T.2 →ₐ[K] E.obj T := fun T ↦ i2 (T.1.unop, T.2.unop)
  have nat₁ : ∀ (T T' : Jᵒᵖ × J'ᵒᵖ) (a : T ⟶ T') (b : F.obj T.1), j₁ T' (mp F a.1 b) = mp E a (j₁ T b) := by
    intro T T' a b
    refine (hi1 _ _).trans (Eq.trans ?_ (congrArg (mp E a) (hi1 (T.1.unop, T.2.unop) b).symm))
    exact m₁.naturality a b
  have nat₂ : ∀ (T T' : Jᵒᵖ × J'ᵒᵖ) (a : T ⟶ T') (b : G.obj T.2), j₂ T' (mp G a.2 b) = mp E a (j₂ T b) := by
    intro T T' a b
    refine (hi2 _ _).trans (Eq.trans ?_ (congrArg (mp E a) (hi2 (T.1.unop, T.2.unop) b).symm))
    exact m₂.naturality a b
  let n₁ : CoefMap (RingHom.id K) F E :=
    { G := CategoryTheory.Prod.fst Jᵒᵖ J'ᵒᵖ
      α := fun T ↦ (j₁ T).toRingHom
      naturality := fun {T T'} a b ↦ nat₁ T T' a b
      smul := fun T r b ↦ map_smul (j₁ T) r b }
  let n₂ : CoefMap (RingHom.id K) G E :=
    { G := CategoryTheory.Prod.snd Jᵒᵖ J'ᵒᵖ
      α := fun T ↦ (j₂ T).toRingHom
      naturality := fun {T T'} a b ↦ nat₂ T T' a b
      smul := fun T r b ↦ map_smul (j₂ T) r b }
  let rU := CoefMap.restrict (OAff X.hom) hU.functor.op
  let rV := CoefMap.restrict (OAff Y.hom) hV.functor.op
  let rE := CoefMap.restrict (OAff (X ⊗ Y).hom) Ψ
  have key₁ : ∀ a, rE.pull1 (pO1 (fst X Y) a) = n₁.pull1 (rU.pull1 a) := fun a ↦ by
    refine (restrict_pullHO1 Ψ B₁ hle₁ (ovw (fst X Y)) a).trans ?_
    refine (CoefMap.pullCohomologyOne_eq_of_natTrans m₁ (rU.comp n₁) (𝟙 B₁) (fun T b ↦ ?_) a).trans
      (CoefMap.pullCohomologyOne_comp rU n₁ a)
    refine (congrArg ((rU.comp n₁).α T) (mp_id (OAff X.hom) _ b)).trans ?_
    exact hi1 (T.1.unop, T.2.unop) b
  have key₂ : ∀ a, rE.pull1 (pO1 (snd X Y) a) = n₂.pull1 (rV.pull1 a) := fun a ↦ by
    refine (restrict_pullHO1 Ψ B₂ hle₂ (ovw (snd X Y)) a).trans ?_
    refine (CoefMap.pullCohomologyOne_eq_of_natTrans m₂ (rV.comp n₂) (𝟙 B₂) (fun T b ↦ ?_) a).trans
      (CoefMap.pullCohomologyOne_comp rV n₂ a)
    refine (congrArg ((rV.comp n₂).α T) (mp_id (OAff Y.hom) _ b)).trans ?_
    exact hi2 (T.1.unop, T.2.unop) b
  have hbU : Function.Bijective rU.pull1 := _root_.GlobalTheory.CoverO.restrict_bijective K X.left X.hom J U hU hUi hUc
  have hbV : Function.Bijective rV.pull1 := _root_.GlobalTheory.CoverO.restrict_bijective K Y.left Y.hom J' V hV hVi hVc
  choose x' hx' using fun i ↦ H1.mk_surjective F (rU.pull1 (x i))
  choose y' hy' using fun i ↦ H1.mk_surjective G (rV.pull1 (y i))
  have hz : H2.mk E (∑ i, cupZ E (n₁.pullbackOneCocycle (x' i)) (n₂.pullbackOneCocycle (y' i))) = 0 := by
    have h0 := congrArg rE.pull2 hsum
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, map_sum] at h0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_) h0
    rw [CoefMap.pullCohomologyTwo_cup, key₁, key₂, ← hx', ← hy']
    rfl
  obtain ⟨f, hf⟩ := H2.mk_eq_zero.1 hz
  have e := _root_.GlobalTheory.CatCoh.KunnethOne.sum_tmul_eq_zero_of_cup K Jᵒᵖ J'ᵒᵖ F G E j₁ j₂ nat₁ nat₂ (fun T ↦ hbij (T.1.unop, T.2.unop)) n x' y' f
    (fun T T' T'' a b ↦ by
      rw [hf]
      simp only [Submodule.coe_sum, Finset.sum_apply]
      rfl)
  simp only [hx', hy'] at e
  let eU := LinearEquiv.ofBijective rU.pull1 hbU
  let eV := LinearEquiv.ofBijective rV.pull1 hbV
  apply (TensorProduct.congr eU eV).injective
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero]
  exact e

end GlobalTheory.Kunneth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticePreservingMapGivesEndomorphism
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RealMult.Obj

theorem holUnif_dim_eq_of_linear {A : Over (Sp ℂ)} [GrpObj A] {L L' : LB A.left} {g g' : ℕ} (u : HolUnif A L g)
    (u' : HolUnif A L' g') (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hF : ∀ z, u'.ex (F z) = u.ex z) : g = g' := by
  haveI := u.discrete
  haveI := u'.discrete
  have hinj := AnyUnif.injective_of_ker_le_discrete u.Λ F fun z hz => by
    rw [← u.ker, ← hF, hz]
    exact (u'.ker 0).2 u'.Λ.zero_mem
  have hsurj : LinearMap.range F = ⊤ := GlobalTheory.AHWeil.eq_top_of_add_discrete u'.Λ _ fun w => by
    obtain ⟨z, hz⟩ := u.ex_onto (u'.ex w)
    refine ⟨⟨w - F z, (u'.ker _).1 ?_⟩, z, by simp⟩
    have h := u'.ex_add (w - F z) (F z)
    rw [sub_add_cancel, hF, hz] at h
    exact (mul_eq_right.1 h.symm)
  simpa using (LinearEquiv.ofBijective F ⟨hinj, LinearMap.range_eq_top.1 hsurj⟩).finrank_eq

end GlobalTheory.RealMult.Obj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullbackOfLocalUnitGeneratorsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundle_iso_pullback_of_local_unit_generators : ∀ (X Y : Scheme.{0}) (f : Y ⟶ X) (L : LB Y) (J : Type) (W : J → X.Opens) (g : ∀ x y, Γ(X, W x ⊓ W y)ˣ) (s : ∀ x k, Γ(Y, L.U k ⊓ f ⁻¹ᵁ W x)ˣ), (∀ x, GlobalTheory.PinchLift.GenOn L (f ⁻¹ᵁ W x) (s x)) → (∀ x y (t : Y) (k : L.ι), f t ∈ W x → f t ∈ W y → t ∈ L.U k → gm f t (W x ⊓ W y) (g x y) = gm (𝟙 Y) t (L.U k ⊓ f ⁻¹ᵁ W y) (s y k) * (gm (𝟙 Y) t (L.U k ⊓ f ⁻¹ᵁ W x) (s x k))⁻¹) → LBIso L ((⟨J, W, g⟩ : LB X).pull f) := by
  first | exact @GlobalTheory.PinchLift.lbIso_pull_of_genOn | exact GlobalTheory.PinchLift.lbIso_pull_of_genOn | (intros; apply GlobalTheory.PinchLift.lbIso_pull_of_genOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalEquationMemComapMapIdealSheafNearPointStatement
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localEquation_mem_comap_map_idealSheaf_near_point : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z), M₁.IsHom M (AlgHom.id o Ω) π → ∀ (D : EffCartierData M.Z) (V : M₁.Z.affineOpens) (g : Γ(M₁.Z, V.1)) (x : M.Z) (i : D.ι), π x ∈ V.1 → x ∈ D.U i → g ∈ (D.idealSheaf.map π).ideal V → valF M₁.pt V.1 g ≠ 0 → valF M.pt (D.U i) (D.f i) / valF M₁.pt V.1 g ∈ M.O x → ∃ (W : M.Z.affineOpens) (h : W.1 ≤ D.U i), x ∈ W.1 ∧ resG M.Z h (D.f i) ∈ ((D.idealSheaf.map π).comap π).ideal W := by
  first | exact @GlobalTheory.Poinc.resG_f_mem_comap_map_ideal | exact GlobalTheory.Poinc.resG_f_mem_comap_map_ideal | (intros; apply GlobalTheory.Poinc.resG_f_mem_comap_map_ideal <;> assumption)
end

