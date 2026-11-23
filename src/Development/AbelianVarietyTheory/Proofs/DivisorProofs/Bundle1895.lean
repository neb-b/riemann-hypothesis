module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SummableNormBoundedSeries
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsHorizontalGeneratorOfCharts
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactification
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0329

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArcPropertyLocalisationBaseChangeOfModel
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels

noncomputable section

namespace GlobalTheory.LocArc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F}

@[reducible] def arcRestrict (b : O →+* O') (hb : β'.comp b = β) {O'' : Type} [CommRing O''] [IsDomain O'']
    {b' : O' →+* O''} (a : ArcIn D l β' O'' b') : ArcIn D l β O'' (b'.comp b) where
  D₀ := a.D₀
  mod := a.mod
  oa := a.oa
  nontriv := a.nontriv
  even := a.even
  bimult := a.bimult
  gen := a.gen
  w0 := a.w0
  be := a.be
  be_symm := a.be_symm
  be_pos := a.be_pos
  be_adj := a.be_adj
  be_dvd := a.be_dvd
  eta := a.eta
  etaA := a.etaA
  geom := fun F _ _ _ r z hr hz => a.geom F (b r) (b z) (by rw [← hb] at hr; exact hr) (by rw [← hb] at hz; exact hz)

variable (Y : Model Xo c β) (b : O →+* O') (hb : β'.comp b = β) [IsPreimmersion (spMap b)] [Flat (spMap b)]

theorem mono_locMap : Mono (locMap Y b).φ :=
  (MorphismProperty.monomorphisms Scheme.{0}).of_isPullback (locMap Y b).cart.1.flip
    (show Mono (pullback.fst Y.s (spMap b)) from inferInstance)

theorem hasArcData_iff {O'' R : Type} [CommRing O''] [IsDomain O''] [CommRing R] [IsDomain R] {b' : O' →+* O''}
    (a : ArcIn D l β' O'' b') (I : Ideal R) (f : O'' →+* R) (u : R) (χ : Sp R ⟶ (locModel Y b hb).X) :
    (locModel Y b hb).HasArcData a I f u χ ↔
      Y.HasArcData (arcRestrict b hb a) I f u (χ ≫ pullback.fst Y.s (spMap b)) := by
  have ej := locModel_j Y b hb
  have em := locModel_m Y b hb
  constructor
  · rintro ⟨t, m, P, φ, he, w, e, h₁, h₂, h₃, h₄, h₅, h₆⟩
    obtain ⟨n, hn⟩ := ObjMaps.exists_sab_comp (locMap Y b) m
    refine ⟨t, n, P, φ, he, w, e, h₁, h₂, h₃, h₄, h₅, fun F _ _ _ _ uF e₁ e₂ => ⟨(h₆ F uF e₁ e₂).1,
      fun yF hy k p₀ σ hσ q₀ q x k₁ k₂ k₃ k₄ => (h₆ F uF e₁ e₂).2 yF ?_ k p₀ σ hσ q₀ q x k₁ k₂ k₃ ?_⟩⟩
    · rw [← cancel_mono (pullback.fst Y.s (spMap b)), Category.assoc, ej, hy]
      simp only [Category.assoc]
    · have := mono_locMap Y b
      rw [← cancel_mono (locMap Y b).φ]
      rw [hn, ← em] at k₄
      simp only [Category.assoc]
      exact k₄
  · rintro ⟨t, m, P, φ, he, w, e, h₁, h₂, h₃, h₄, h₅, h₆⟩
    obtain ⟨n, hn⟩ := ObjMaps.exists_sab_cancel (locMap Y b) m
    refine ⟨t, n, P, φ, he, w, e, h₁, h₂, h₃, h₄, h₅, fun F _ _ _ _ uF e₁ e₂ => ⟨(h₆ F uF e₁ e₂).1,
      fun yF hy k p₀ σ hσ q₀ q x k₁ k₂ k₃ k₄ => (h₆ F uF e₁ e₂).2 yF ?_ k p₀ σ hσ q₀ q x k₁ k₂ k₃ ?_⟩⟩
    · rw [← ej, ← Category.assoc, hy]
      simp only [Category.assoc]
    · have := congrArg (· ≫ (locMap Y b).φ) k₄
      simp only [Category.assoc] at this
      rw [hn, ← em]
      exact this

theorem mem_range_j_iff (x : (locModel Y b hb).X) :
    x ∈ Set.range (locModel Y b hb).j ↔ pullback.fst Y.s (spMap b) x ∈ Set.range Y.j := by
  rw [← locModel_j Y b hb]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u, Scheme.Hom.comp_apply _ _ _⟩
  · rintro ⟨u, hu⟩
    refine ⟨u, (pullback.fst Y.s (spMap b)).isEmbedding.injective ?_⟩
    rw [← hu, Scheme.Hom.comp_apply]

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]
  rfl

theorem locModel_arc (h : Y.N4) : (locModel Y b hb).N4 := by
  intro O'' _ _ _ b' ϖ a hO
  obtain ⟨χ₀, hu, hs⟩ := h O'' (b'.comp b) ϖ (arcRestrict b hb a) hO
  obtain ⟨c₁, c₂, c₃, c₄⟩ := (hu χ₀).1 rfl
  have hw : χ₀ ≫ Y.s = (spMap (PowerSeries.C (R := O'')) ≫ spMap b') ≫ spMap b := by
    rw [c₁, spMap_comp', Category.assoc]
  have hχ : pullback.lift χ₀ _ hw ≫ pullback.fst Y.s (spMap b) = χ₀ := pullback.lift_fst _ _ _
  refine ⟨pullback.lift χ₀ _ hw, fun χ' => ⟨?_, ?_⟩, fun hi y' ev d₁ d₂ d₃ d₄ d₅ => ?_⟩
  · rintro rfl
    refine ⟨pullback.lift_snd _ _ _, fun x => ?_, fun x hx => ?_, ?_⟩
    · rw [mem_abLocus_locModel, ← Scheme.Hom.comp_apply, hχ]
      exact c₂ x
    · rw [mem_range_j_iff, ← Scheme.Hom.comp_apply, hχ]
      exact c₃ x hx
    · rw [hasArcData_iff, hχ]
      exact c₄
  · rintro ⟨d₁, d₂, d₃, d₄⟩
    rw [← cancel_mono (pullback.fst Y.s (spMap b)), hχ]
    refine (hu _).2 ⟨?_, fun x => ?_, fun x hx => ?_, (hasArcData_iff Y b hb a _ _ _ _).1 d₄⟩
    · rw [Category.assoc, pullback.condition, ← Category.assoc, spMap_comp', ← Category.assoc]
      exact congrArg (· ≫ spMap b) d₁
    · rw [Scheme.Hom.comp_apply, ← mem_abLocus_locModel Y b hb]
      exact d₂ x
    · rw [Scheme.Hom.comp_apply, ← mem_range_j_iff Y b hb]
      exact d₃ x hx
  · rw [← cancel_mono (pullback.fst Y.s (spMap b)), Category.assoc, hχ]
    refine hs hi _ ev ?_ ?_ ((hasArcData_iff Y b hb a _ _ _ _).1 d₃) d₄ d₅
    · rw [Category.assoc, pullback.condition, ← Category.assoc, spMap_comp']
      exact congrArg (· ≫ spMap b) d₁
    · rintro _ ⟨q, rfl⟩
      rw [← Category.assoc, Scheme.Hom.comp_apply, ← mem_range_j_iff Y b hb]
      exact d₂ ⟨q, rfl⟩

end GlobalTheory.LocArc

theorem GlobalTheory.LocArc.arc_localise : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (O' : Type) [CommRing O'] (β' : O' →+* c.F) (b : O →+* O') (hb : β'.comp b = β) [IsPreimmersion (spMap b)] [Flat (spMap b)], Y.N4 → (locModel Y b hb).N4 :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ Y _ _ _ b hb _ _ h => GlobalTheory.LocArc.locModel_arc Y b hb h
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseIdealSheafOfIdealComapSpecMapSupport
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem appLE_comp_cst {R : Type} [CommRing R] {W W' : Scheme.{0}} (f : W ⟶ Spec (CommRingCat.of R))
    (π : W' ⟶ W) (U : W.Opens) (A : W'.Opens) (h : A ≤ π ⁻¹ᵁ U) :
    (π.appLE U A h).hom.comp (cst f U) = cst (π ≫ f) A := by
  have e : f.appTop ≫ W.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ π.appLE U A h =
      (π ≫ f).appTop ≫ W'.presheaf.map (homOfLE (le_top : A ≤ ⊤)).op := by
    rw [Scheme.Hom.map_appLE, Scheme.Hom.comp_appTop]
    simp [Scheme.Hom.appLE]
  ext r
  have := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) e
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
  exact this

theorem cst_comp_specMap {R C : Type} [CommRing R] [CommRing C] (φ : R →+* C) {W : Scheme.{0}}
    (p : W ⟶ Spec (CommRingCat.of C)) (U : W.Opens) :
    cst (p ≫ Spec.map (CommRingCat.ofHom φ)) U = (cst p U).comp φ := by
  ext a
  have := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  simp only [cst, RingHom.comp_apply, Scheme.Hom.comp_appTop, CommRingCat.hom_comp]
  rw [this]

theorem comap_baseIdeal {R : Type} [CommRing R] {W W' : Scheme.{0}} (f : W ⟶ Spec (CommRingCat.of R))
    (π : W' ⟶ W) (J : Ideal R) : (baseIdeal f J).comap π = baseIdeal (π ≫ f) J := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (ι := {p : W.affineOpens × W'.affineOpens // p.2.1 ≤ π ⁻¹ᵁ p.1.1}) (fun i => i.1.2) ?_ ?_
  · refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.1
      ((iSup_affineOpens_eq_top W).ge (Set.mem_univ (π x)))
    obtain ⟨A, hA, hxA, hAU⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.1 W'.isBasis_affineOpens (show x ∈ π ⁻¹ᵁ U.1 from hxU)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(U, ⟨A, hA⟩), hAU⟩, hxA⟩
  · intro i
    rw [GlobalTheory.Principalise.comapIdealAffine _ π i.1.1 i.1.2 i.2, baseIdeal_ideal, baseIdeal_ideal, Ideal.map_map,
      appLE_comp_cst]

theorem baseIdeal_comp_specMap {R C : Type} [CommRing R] [CommRing C] (φ : R →+* C) {W : Scheme.{0}}
    (p : W ⟶ Spec (CommRingCat.of C)) (J : Ideal R) :
    baseIdeal (p ≫ Spec.map (CommRingCat.ofHom φ)) J = baseIdeal p (J.map φ) := by
  rw [baseIdeal, baseIdeal, Ideal.map_map, cst_comp_specMap]

theorem mem_support_baseIdeal {R : Type} [CommRing R] {W : Scheme.{0}} (f : W ⟶ Spec (CommRingCat.of R))
    (J : Ideal R) (x : W) : x ∈ (baseIdeal f J).support ↔ J ≤ (f x).asIdeal := by
  obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.1
    ((iSup_affineOpens_eq_top W).ge (Set.mem_univ x))
  have key : ∀ r, x ∈ W.basicOpen (cst f U.1 r) ↔ r ∉ (f x).asIdeal := by
    intro r
    simp only [cst, rs, RingHom.comp_apply]
    rw [Scheme.basicOpen_res, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
    simp only [hxU, TopologicalSpace.Opens.mem_inf, true_and]
    exact PrimeSpectrum.mem_basicOpen _ _
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem hxU, baseIdeal_ideal]
  unfold Ideal.map
  rw [Scheme.zeroLocus_span, Scheme.mem_zeroLocus_iff]
  constructor
  · intro h r hr
    by_contra hn
    exact h _ ⟨r, hr, rfl⟩ ((key r).2 hn)
  · rintro h _ ⟨r, hr, rfl⟩ hx
    exact (key r).1 hx (h hr)

theorem baseIdeal_calculus :
    (∀ (R : Type) [CommRing R] (W W' : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (π : W' ⟶ W) (J : Ideal R), (baseIdeal f J).comap π = baseIdeal (π ≫ f) J) ∧ (∀ (R C : Type) [CommRing R] [CommRing C] (φ : R →+* C) (W : Scheme.{0}) (p : W ⟶ Spec (CommRingCat.of C)) (J : Ideal R), baseIdeal (p ≫ Spec.map (CommRingCat.ofHom φ)) J = baseIdeal p (J.map φ)) ∧ (∀ (R : Type) [CommRing R] (W : Scheme.{0}) (f : W ⟶ Spec (CommRingCat.of R)) (J : Ideal R) (x : W), x ∈ (baseIdeal f J).support ↔ J ≤ (f x).asIdeal) :=
  ⟨fun _ _ _ _ f π J => comap_baseIdeal f π J,
    fun _ _ _ _ φ _ p J => baseIdeal_comp_specMap φ p J,
    fun _ _ _ f J x => mem_support_baseIdeal f J x⟩

end GlobalTheory.FormalAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseIdealSheafOfIdealSpecBijectiveCalculus
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FormalAlg

theorem baseIdeal_sup {R : Type} [CommRing R] {W : Scheme.{0}} (f : W ⟶ Spec (CommRingCat.of R))
    (a b : Ideal R) : baseIdeal f (a ⊔ b) = baseIdeal f a ⊔ baseIdeal f b := by
  refine Scheme.IdealSheafData.ext (funext fun U => ?_)
  rw [Scheme.IdealSheafData.ideal_sup, Pi.sup_apply, baseIdeal_ideal, baseIdeal_ideal, baseIdeal_ideal,
    Ideal.map_sup]

theorem idealSheaf_ext_top {X : Scheme.{0}} [IsAffine X] {I J : X.IdealSheafData}
    (h : I.ideal ⟨⊤, isAffineOpen_top X⟩ = J.ideal ⟨⊤, isAffineOpen_top X⟩) : I = J :=
  Scheme.IdealSheafData.ext_of_iSup_eq_top (ι := Unit) (fun _ => ⟨⊤, isAffineOpen_top X⟩) iSup_const fun _ => h

theorem appLE_specMap_fromSpec {W : Scheme.{0}} (U : W.Opens) (hU : IsAffineOpen U) (C : Type) [CommRing C]
    (φ : Γ(W, U) →+* C) (h : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤
      (Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec) ⁻¹ᵁ U) :
    ((Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec).appLE U ⊤ h).hom =
      (cst (𝟙 (Spec (CommRingCat.of C))) ⊤).comp φ := by
  have hfs : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := by rw [hU.fromSpec_preimage_self]
  have m1 : (Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec).appLE U ⊤ h =
      hU.fromSpec.appLE U ⊤ hfs ≫ (Spec.map (CommRingCat.ofHom φ)).appTop := by
    rw [Scheme.Hom.comp_appLE]
    rfl
  have m2 : hU.fromSpec.appLE U ⊤ hfs = (Scheme.ΓSpecIso Γ(W, U)).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    convert Category.comp_id _
    exact (Spec Γ(W, U)).presheaf.map_id _
  have m3 : (Scheme.ΓSpecIso Γ(W, U)).inv ≫ (Spec.map (CommRingCat.ofHom φ)).appTop =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).inv :=
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)).symm
  rw [m1, m2, m3]
  ext x
  simp only [cst, RingHom.comp_apply, rs_self]
  rfl

theorem specIdeal :
    (∀ (C : Type) [CommRing C], Function.Bijective (fun a : Ideal C => baseIdeal (𝟙 (Spec (CommRingCat.of C))) a) ∧ (∀ a b : Ideal C, baseIdeal (𝟙 (Spec (CommRingCat.of C))) (a ⊔ b) = baseIdeal (𝟙 _) a ⊔ baseIdeal (𝟙 _) b)) ∧ (∀ (W : Scheme.{0}) (V : W.affineOpens) (C : Type) [CommRing C] (φ : Γ(W, V.1) →+* C) (J : W.IdealSheafData), J.comap (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) = baseIdeal (𝟙 (Spec (CommRingCat.of C))) ((J.ideal V).map φ)) := by
  refine ⟨fun C _ => ⟨⟨fun a b hab => ?_, fun J => ?_⟩, fun a b => baseIdeal_sup _ a b⟩, fun W V C _ φ J => ?_⟩
  · have hb := cst_bijective (𝟙 (Spec (CommRingCat.of C))) (W := ⊤) rfl
    have e := congrArg (fun I : (Spec (CommRingCat.of C)).IdealSheafData => I.ideal ⟨⊤, isAffineOpen_top _⟩) hab
    simp only [baseIdeal_ideal] at e
    rw [← Ideal.comap_map_of_bijective _ hb (I := a), e, Ideal.comap_map_of_bijective _ hb]
  · have hb := cst_bijective (𝟙 (Spec (CommRingCat.of C))) (W := ⊤) rfl
    refine ⟨(J.ideal ⟨⊤, isAffineOpen_top _⟩).comap (cst (𝟙 (Spec (CommRingCat.of C))) ⊤), idealSheaf_ext_top ?_⟩
    simp only [baseIdeal_ideal]
    exact Ideal.map_comap_of_surjective _ hb.2 _
  · have h : (⊤ : (Spec (CommRingCat.of C)).Opens) ≤ (Spec.map (CommRingCat.ofHom φ) ≫ V.2.fromSpec) ⁻¹ᵁ V.1 :=
      fun x _ => V.2.range_fromSpec.subset ⟨_, rfl⟩
    refine idealSheaf_ext_top ?_
    rw [GlobalTheory.Principalise.comapIdealAffine J _ V ⟨⊤, isAffineOpen_top _⟩ h, baseIdeal_ideal, Ideal.map_map,
      appLE_specMap_fromSpec V.1 V.2 C φ h]

end GlobalTheory.FormalAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundStatementHolds
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.EigenSplit
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel.BoundProof

section Gen

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)

theorem actV_mem_latT (a : Λ) {y : P.V} (hy : y ∈ P.latT) : P.actV a y ∈ P.latT :=
  (P.mem_latT_iff _).2 fun t => by
    obtain ⟨c, hc⟩ := (P.mem_latT_iff y).1 hy (P.actT (star a) t)
    exact ⟨c, by rw [hc, P.pairV_act]; rfl⟩

theorem pairV_inclT_mem {u : P.V} (hu : u ∈ P.latT) (y : O ⊗[ℤ_[p]] P.T) :
    P.pairV u (P.inclT y) ∈ (algebraMap O C).range := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add y z hy hz =>
    obtain ⟨a, ha⟩ := hy
    obtain ⟨b, hb⟩ := hz
    exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]⟩
  | tmul c t =>
    obtain ⟨b, hb⟩ := (P.mem_latT_iff u).1 hu t
    refine ⟨c * b, ?_⟩
    have e : (algebraMap O C c ⊗ₜ[ℤ_[p]] t : P.V) = algebraMap O C c • ((1 : C) ⊗ₜ[ℤ_[p]] t) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [P.inclT_tmul, e, map_smul, smul_eq_mul, map_mul, hb]

end Gen

section Gen2

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
  [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)

theorem pairV_bLie_inclT (x : LieG P.Gt) (y : O ⊗[ℤ_[p]] P.T) :
    P.pairV (P.bLie x) (P.inclT y) = algebraMap O C ((P.al y).1 x) := by
  rw [pairV_bLie_eq_evLie, P.alC_inclT, Point.inclOm, TensorProduct.mk_apply, evLie,
    LinearMap.liftBaseChange_tmul, one_smul]
  rfl

end Gen2

section Discr

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C]
  [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]
  {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] (P : Point p v O (𝓞 E))

end Discr

end GlobalTheory.FlatModel.BoundProof

namespace GlobalTheory.FlatModel

end GlobalTheory.FlatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedPowerSeriesEvaluationDivisibility
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MBLow.BddPS

def bdd (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] : Subring (PowerSeries C) :=
  GlobalTheory.BoundedPowerSeriesDisc.boundedSeries C

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]

noncomputable def ev [CompleteSpace C] (π : C) (h : ‖π‖ < 1) : bdd C →+* C :=
  GlobalTheory.BoundedPowerSeriesDisc.evalBounded π h

theorem main : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] (π : C), ‖π‖ < 1 → ∃ (B : Subring (PowerSeries C)) (ev : B →+* C) (t : B), (∀ Φ, Φ ∈ B ↔ ∃ b : ℝ, ∀ n, ‖PowerSeries.coeff n Φ‖ ≤ b) ∧ (∀ Φ : B, ev Φ = ∑' n, PowerSeries.coeff n (Φ : PowerSeries C) * π ^ n) ∧ t ≠ 0 ∧ (∀ Φ, ev Φ = 0 ↔ t ∣ Φ) ∧ ∀ Φ : B, Φ ≠ 0 → ∃ n : ℕ, ¬ t ^ n ∣ Φ := by
  first
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact @_root_.GlobalTheory.SummableSeriesBounds.main
  | (run_tac Lean.Elab.Tactic.liftMetaTactic (fun g => do pure [← g.revertAll])); exact _root_.GlobalTheory.SummableSeriesBounds.main
  | exact @_root_.GlobalTheory.SummableSeriesBounds.main
  | exact _root_.GlobalTheory.SummableSeriesBounds.main
  | (apply _root_.GlobalTheory.SummableSeriesBounds.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SummableSeriesBounds.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SummableSeriesBounds.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SummableSeriesBounds.main ..)

end GlobalTheory.MBLow.BddPS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardClassCartierDivisorPullbackEqPullback
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory.PullCartier

theorem fnOf_app {M W : Scheme.{0}} [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f]
    {U : W.Opens} (h : genericPoint M ∈ f ⁻¹ᵁ U) (a : Γ(W, U)) :
    fnOf (f ⁻¹ᵁ U) h ((f.app U).hom a) =
      GlobalTheory.functionFieldMap f (fnOf U (gen_mem (x := f (genericPoint M)) h) a) := by
  have hx : f (genericPoint M) ∈ U := h
  rw [← algebraMap_germ hx a, GlobalTheory.functionFieldMap_algebraMap, Scheme.Hom.germ_stalkMap_apply f U _ hx a]
  exact (algebraMap_germ (X := M) (U := f ⁻¹ᵁ U) (x := genericPoint M) h _).symm

theorem cls_toLB_pull : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f]
    (D₀ : CartierDiv W) (D₁ : CartierDiv M),
    (∀ x g, D₀.IsEqn (f x) g → D₁.IsEqn x (Units.map (GlobalTheory.functionFieldMap f).toMonoidHom g)) →
      cls (toLB D₁) (isLB_toLB D₁) = CechPic.pull f (cls (toLB D₀) (isLB_toLB D₀)) := by
  intro M W _ _ f _ D₀ D₁ hD
  have hP : Presents D₁ ((toLB D₀).pull f)
      fun J => Units.map (GlobalTheory.functionFieldMap f).toMonoidHom (J PUnit.unit).1.2 := by
    refine ⟨pull_isLB (isLB_toLB D₀) f, fun J K h => ?_,
      fun J x hx => hD x _ ((J PUnit.unit).2.2 _ (mem_pull.1 hx))⟩
    have hle : ((toLB D₀).pull f).U J ⊓ ((toLB D₀).pull f).U K ≤
        f ⁻¹ᵁ ((toLB D₀).U (J PUnit.unit) ⊓ (toLB D₀).U (K PUnit.unit)) :=
      fun y hy => ⟨mem_pull.1 hy.1, mem_pull.1 hy.2⟩
    have e0 : ((toLB D₀).pull f).g J K =
        res hle (pullU f _ ((toLB D₀).g (J PUnit.unit) (K PUnit.unit))) :=
      by dsimp only [LB.pull, LB.LinComb]; rw [Fintype.prod_unique, zpow_one]; rfl
    have e : fnOf _ h (((toLB D₀).pull f).g J K).val =
        fnOf _ (hle h) ((f.app _).hom ((toLB D₀).g (J PUnit.unit) (K PUnit.unit)).val) := by
      rw [e0, LB.val_res, fnOf_resG]
      rfl
    rw [e, fnOf_app, fnOf_toLB_g]
    simp only [Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
    rw [← map_mul, div_mul_cancel₀ _ (Units.ne_zero _)]
  rw [← cls_pull (isLB_toLB D₀) f hP.isLB, ← toPic_apply, hP.toPic_eq]

end GlobalTheory.PullCartier
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharZeroStalkCompactFlagSpaceOverComponent
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

namespace GlobalTheory.CompHS

theorem charZero_stalk_Y₀ : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (TF : TorFlag Xo c) (Z : Comp Xo c) (y : Y₀ TF.X Z), CharZero ((Y₀ TF.X Z).presheaf.stalk y) := by
  intro E _ _ _ H Dw l Xo c TF Z y
  let f : c.F →+* (Y₀ TF.X Z).presheaf.stalk y :=
    ((Y₀ TF.X Z).presheaf.germ ⊤ y trivial).hom.comp
      ((str₀ TF.X Z).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of c.F)).inv.hom)
  exact charZero_of_injective_ringHom f.injective

end GlobalTheory.CompHS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstLengthArchSectionEqSmulOfSameWeightStatement
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constLengthArchSection_eq_smul_of_same_weight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → FnAlgClosed (Xo := Xo) (c := c) → ∀ (Z : Comp Xo c) (la : GlobalTheory.AllWt.Weight Dw) (s t : ArchSec U x Z la), ∃ a : c.F, a ≠ 0 ∧ t.sig = a • s.sig := by
  first | exact @GlobalTheory.FlatCore.archSec_exists_eq_smul | exact GlobalTheory.FlatCore.archSec_exists_eq_smul | (intros; apply GlobalTheory.FlatCore.archSec_exists_eq_smul <;> assumption)
end

