module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2263
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAbelianSchemeAway
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RangeSubsetAbLocusOfIsProper
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SecMoveK
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CstDvdOfCstMulEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2320
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2234
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2286
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2322
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.BetaAtClosedPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2318
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibrePulledSemiAbelianEqAbelianVariety
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open Classical

namespace GlobalTheory.MumGen

theorem genFibre_pullback : ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [GlobalTheory.ZH.ArithBase o Ω] (S : GlobalTheory.ZH.ThetaSys o Ω) (ρS : S.Real) (M : GlobalTheory.ZH.RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.Over₀ M U₀ → ∀ (Z : GlobalTheory.ZH.ZHOut ρS M U₀ EE) (e : Ω →+* FractionRing R₁) (M' : Modif R₁) (h : M'.S ⟶ M.Z), M'.gp ≫ h = spMap e ≫ M.pt → ∀ (A₁ : PolAV (Sp (FractionRing R₁))) (φ : A₁.A.left ⟶ ρS.P.A.left), IsGrpPullback A₁.A ρS.P.A (spMap (e.comp S.R.val.toRingHom)) φ → LBIso A₁.L (ρS.P.L.pull φ) → ∃ α : A₁.A.left ⟶ ((Over.pullback h).obj Z.G).left, IsGrpPullback A₁.A ((Over.pullback h).obj Z.G) M'.gp α ∧ LBIso A₁.L ((Z.L.L.pull (pullback.fst Z.G.hom h)).pull α) := by
  intro R₁ _ _ o Ω _ _ _ _ S ρS M U₀ EE hO Z e M' h hh A₁ φ hcart hlb
  have hr : Set.range M.pt ⊆ (U₀ : Set M.Z) := (GlobalTheory.ZH.top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hO.ne)
  let x : Sp Ω ⟶ U₀.toScheme := IsOpenImmersion.lift U₀.ι M.pt (by rw [Scheme.Opens.range_ι]; exact hr)
  have hx : x ≫ U₀.ι = M.pt := IsOpenImmersion.lift_fac _ _ _
  have hy₀ : (spMap e ≫ x) ≫ Z.u₀ = spMap (e.comp S.R.val.toRingHom) := by
    rw [Category.assoc, Z.u₀_gen x hx, ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap_comp]
  have w₁ : φ ≫ ρS.P.A.hom = (A₁.A.hom ≫ (spMap e ≫ x)) ≫ Z.u₀ := by
    rw [hcart.1.w, Category.assoc, hy₀]
  let lam : A₁.A.left ⟶ pullback ρS.P.A.hom Z.u₀ := pullback.lift φ (A₁.A.hom ≫ (spMap e ≫ x)) w₁
  have hlam : IsGrpPullback A₁.A ((Over.pullback Z.u₀).obj ρS.P.A) (spMap e ≫ x) lam :=
    IsGrpPullback.cancel (isGrpPullback_pullback ρS.P.A Z.u₀)
      (hcart.congr hy₀.symm (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)
  have hcomp : IsGrpPullback A₁.A Z.G ((spMap e ≫ x) ≫ U₀.ι) (lam ≫ Z.φ) := IsGrpPullback.comp hlam Z.cart
  have hyy : (spMap e ≫ x) ≫ U₀.ι = M'.gp ≫ h := by rw [Category.assoc, hx, hh]
  have w₂ : (lam ≫ Z.φ) ≫ Z.G.hom = (A₁.A.hom ≫ M'.gp) ≫ h := by
    rw [hcomp.1.w, hyy, Category.assoc]
  let α : A₁.A.left ⟶ pullback Z.G.hom h := pullback.lift (lam ≫ Z.φ) (A₁.A.hom ≫ M'.gp) w₂
  have hα : IsGrpPullback A₁.A ((Over.pullback h).obj Z.G) M'.gp α :=
    IsGrpPullback.cancel (isGrpPullback_pullback Z.G h)
      (hcomp.congr hyy (pullback.lift_fst _ _ _).symm) (pullback.lift_snd _ _ _)
  refine ⟨α, hα, ?_⟩
  have hP := ρS.P.isLB
  have hZ := Z.L.isLB
  have i₁ : LBIso (ρS.P.L.pull φ) ((ρS.P.L.pull (pullback.fst ρS.P.A.hom Z.u₀)).pull lam) :=
    GlobalTheory.GenSpread.lbIso_pull_pull hP lam (pullback.lift_fst _ _ _).symm
  have i₂ : LBIso ((ρS.P.L.pull (pullback.fst ρS.P.A.hom Z.u₀)).pull lam) ((Z.L.L.pull Z.φ).pull lam) :=
    GlobalTheory.GenSpread.lbIso_pullback (LBIso.symm ⟨Z.w, Z.w_gen⟩) lam
  have i₃ : LBIso ((Z.L.L.pull Z.φ).pull lam) (Z.L.L.pull (lam ≫ Z.φ)) :=
    LBIso.symm (GlobalTheory.GenSpread.lbIso_pull_pull hZ lam rfl)
  have i₄ : LBIso (Z.L.L.pull (lam ≫ Z.φ)) ((Z.L.L.pull (pullback.fst Z.G.hom h)).pull α) :=
    GlobalTheory.GenSpread.lbIso_pull_pull hZ α (pullback.lift_fst _ _ _).symm
  have j₁ := LBIso.trans A₁.isLB (pull_isLB hP _) (pull_isLB (pull_isLB hP _) _) hlb i₁
  have j₂ := LBIso.trans A₁.isLB (pull_isLB (pull_isLB hP _) _) (pull_isLB (pull_isLB hZ _) _) j₁ i₂
  have j₃ := LBIso.trans A₁.isLB (pull_isLB (pull_isLB hZ _) _) (pull_isLB hZ _) j₂ i₃
  exact LBIso.trans A₁.isLB (pull_isLB hZ _) (pull_isLB (pull_isLB hZ _) _) j₃ i₄

end GlobalTheory.MumGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointFlatOfModificationOfDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem Modif.flat_gp (R : Type) [CommRing R] [IsDomain R] (M : Modif R) : Flat M.gp := by
  haveI := M.integral
  haveI := M.dominant
  refine Flat.of_stalkMap _ fun x => ?_
  have hx : M.gp.base x = genericPoint M.S := by
    have hd : DenseRange M.gp.base := M.gp.denseRange
    have hr : Set.range M.gp.base = {M.gp.base x} := by
      ext y; constructor
      · rintro ⟨z, rfl⟩; rw [Subsingleton.elim z x]; rfl
      · rintro rfl; exact ⟨x, rfl⟩
    have hg : IsGenericPoint (M.gp.base x) ⊤ := by
      rw [IsGenericPoint, ← hr]
      simpa [Set.top_eq_univ] using hd.closure_range
    exact hg.eq (genericPoint_spec M.S)
  have hF : IsField (M.S.presheaf.stalk (M.gp.base x)) := by
    rw [hx]; exact Field.toIsField _
  letI : Field (M.S.presheaf.stalk (M.gp.base x)) := hF.toField
  unfold RingHom.Flat
  exact inferInstance

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointsFiniteUnitaryModuliCoefficientField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc GlobalTheory.UCovSep
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.XScov

theorem genericPoints_XF_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), (genericPoints (Xo.XF c)).Finite := by
  intro E _ _ _ H Dw l Xo c
  obtain ⟨N, i, hi, hq, he⟩ := Xo.qproj
  have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str (KA l) N
  haveI : QuasiCompact Xo.s := he ▸ inferInstance
  haveI : LocallyOfFiniteType Xo.s := he ▸ inferInstance
  haveI : QuasiCompact (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) := inferInstance
  haveI : LocallyOfFiniteType (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) := inferInstance
  haveI : IsLocallyNoetherian (Xo.XF c) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
  haveI : CompactSpace (Xo.XF c) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
  haveI : IsNoetherian (Xo.XF c) := {}
  exact genericPoints.finite finite_irreducibleComponents_of_isNoetherian

end GlobalTheory.XScov
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueOverlapDiagonalAndTransfer
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem glue_overlap_cocycle : ∀ (B S X : Scheme.{0}) (π : S ⟶ B), Surjective π → ∀ (U : Over B) (J : Type) (e : J → (pullback U.hom π ⟶ X)), (∀ j, IsOpenImmersion (e j)) → ∀ (V : J → J → U.left.Opens) (τ : ∀ i j, (V i j).toScheme ⟶ U.left), (∀ (i j : J) (a : ↥(pullback U.hom π)), pullback.fst U.hom π a ∈ V i j ↔ e i a ∈ Set.range (e j)) → (∀ (i j : J) (T : Scheme.{0}) (a b : T ⟶ pullback U.hom π) (v : T ⟶ (V i j).toScheme), a ≫ e i = b ≫ e j → v ≫ (V i j).ι = a ≫ pullback.fst _ _ → v ≫ τ i j = b ≫ pullback.fst _ _) → (∀ i, V i i = ⊤) ∧ (∀ (i j k : J) (x : (V i j).toScheme), (V i j).ι x ∈ V i k → τ i j x ∈ V j k) := by
  intro B S X π hπ U J e he V τ hV hτ
  have hp : Function.Surjective (pullback.fst U.hom π) := (inferInstance : Surjective (pullback.fst U.hom π)).surj
  refine ⟨fun i => ?_, fun i j k x hx => ?_⟩
  · refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨a, rfl⟩ := hp y
    exact (hV i i a).mpr ⟨a, rfl⟩
  · obtain ⟨a, ha⟩ := hp ((V i j).ι x)
    have hij : e i a ∈ Set.range (e j) := (hV i j a).mp (by
      rw [ha]
      have hx' : (V i j).ι x ∈ Set.range (V i j).ι := ⟨x, rfl⟩
      rwa [Scheme.Opens.range_ι] at hx')
    obtain ⟨b, hb⟩ := hij
    have hik : e i a ∈ Set.range (e k) := (hV i k a).mp (by rw [ha]; exact hx)
    obtain ⟨t, ht1, ht2⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback (e i) (e j)) a b hb.symm
    have hrange : Set.range (pullback.fst (e i) (e j) ≫ pullback.fst U.hom π) ⊆ Set.range (V i j).ι := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      show (pullback.fst U.hom π) (pullback.fst (e i) (e j) z) ∈ V i j
      rw [hV i j]
      refine ⟨pullback.snd (e i) (e j) z, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    let v := IsOpenImmersion.lift (V i j).ι (pullback.fst (e i) (e j) ≫ pullback.fst U.hom π) hrange
    have hv : v ≫ (V i j).ι = pullback.fst (e i) (e j) ≫ pullback.fst U.hom π := IsOpenImmersion.lift_fac _ _ _
    have key := hτ i j _ (pullback.fst (e i) (e j)) (pullback.snd (e i) (e j)) v pullback.condition hv
    have hvt : v t = x := by
      apply (V i j).ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hv, Scheme.Hom.comp_apply, ht1, ha]
    have : τ i j x = pullback.fst U.hom π b := by
      rw [← hvt, ← Scheme.Hom.comp_apply, key, Scheme.Hom.comp_apply, ht2]
    rw [this, hV j k, hb]
    exact hik

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupFibreBaseChangeCommonFieldIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum.FibBC

theorem pullCompIso_hom_eq {T S' S : Scheme.{0}} (p : T ⟶ S') (f : S' ⟶ S) (G : Over S) [GrpObj G] :
    (pullCompIso p f G).hom = (Over.pullbackComp p f).hom.app G := Category.comp_id _

theorem pullCompIso_fst {T S' S : Scheme.{0}} (p : T ⟶ S') (f : S' ⟶ S) (G : Over S) [GrpObj G] :
    (pullCompIso p f G).hom.left ≫ pullback.fst _ p ≫ pullback.fst G.hom f = pullback.fst G.hom (p ≫ f) := by
  rw [pullCompIso_hom_eq]
  simp [Over.pullbackComp, Over.mapComp, pullback.lift_fst_assoc, pullback.lift_fst]

theorem pullCompIso_inv_fst {T S' S : Scheme.{0}} (p : T ⟶ S') (f : S' ⟶ S) (G : Over S) [GrpObj G] :
    (pullCompIso p f G).inv.left ≫ pullback.fst G.hom (p ≫ f) = pullback.fst _ p ≫ pullback.fst G.hom f := by
  rw [← pullCompIso_fst, ← Category.assoc, ← Over.comp_left, Iso.inv_hom_id, Over.id_left, Category.id_comp]

theorem pullback_map_fst {S S' : Scheme.{0}} (g : S' ⟶ S) {A B : Over S} (u : A ⟶ B) :
    ((Over.pullback g).map u).left ≫ pullback.fst B.hom g = pullback.fst A.hom g ≫ u.left :=
  pullback.lift_fst _ _ _

theorem fibre_baseChange : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (W' : Type) [CommRing W'] [IsLocalRing W'] (G' : Over (Sp W')) [GrpObj G'] (ξ' : Sp W' ⟶ S) (β : G'.left ⟶ G.left), IsGrpPullback G' G ξ' β → ∀ (k : Type) [Field k] (Y : Over (Sp k)) [GrpObj Y] (κ' : k →+* ResidueField W') (e' : (Over.pullback (spMap (residue W'))).obj G' ≅ (Over.pullback (spMap κ')).obj Y), IsMonHom e'.hom → ∀ (Ω : Type) [Field Ω] (x : Sp Ω ⟶ S) (κ : k →+* Ω) (Ω' : Type) [Field Ω'] (io : Ω →+* Ω') (i₂ : ResidueField W' →+* Ω'), spMap io ≫ x = spMap i₂ ≫ spMap (residue W') ≫ ξ' → io.comp κ = i₂.comp κ' → ∃ (e : (Over.pullback (spMap io ≫ x)).obj G ≅ (Over.pullback (spMap (io.comp κ))).obj Y) (τ : ((Over.pullback (spMap io ≫ x)).obj G).left ⟶ ((Over.pullback (spMap (residue W'))).obj G').left), IsMonHom e.hom ∧ τ ≫ pullback.fst G'.hom (spMap (residue W')) ≫ β = pullback.fst G.hom (spMap io ≫ x) ∧ e.hom.left ≫ pullback.fst Y.hom (spMap (io.comp κ)) = τ ≫ e'.hom.left ≫ pullback.fst Y.hom (spMap κ') := by
  intro S G _ W' _ _ G' _ ξ' β hβ k _ Y _ κ' e' he' Ω _ x κ Ω' _ io i₂ hc hκ
  have hm : spMap i₂ ≫ spMap κ' = spMap (io.comp κ) := by
    rw [hκ, ← Spec.map_comp]; rfl
  rw [← hm]

  have h₁ : IsGrpPullback ((Over.pullback (spMap i₂ ≫ spMap (residue W'))).obj G') G (spMap io ≫ x)
      (pullback.fst G'.hom (spMap i₂ ≫ spMap (residue W')) ≫ β) :=
    ((isGrpPullback_pullback G' (spMap i₂ ≫ spMap (residue W'))).comp hβ).congr
      (by rw [hc, Category.assoc]) rfl
  obtain ⟨e₁, he₁, he₁f⟩ := grpPullback_iso (isGrpPullback_pullback G (spMap io ≫ x)) h₁
  let e₂ := pullCompIso (spMap i₂) (spMap (residue W')) G'
  let e₃ := (Over.pullback (spMap i₂)).mapIso e'
  let e₄ := (pullCompIso (spMap i₂) (spMap κ') Y).symm
  have i₃ : IsMonHom e₃.hom := by show IsMonHom ((Over.pullback (spMap i₂)).map e'.hom); infer_instance
  have i₄ : IsMonHom e₄.hom := by show IsMonHom (pullCompIso (spMap i₂) (spMap κ') Y).inv; infer_instance
  have f₂ : e₂.hom.left ≫ pullback.fst _ (spMap i₂) ≫ pullback.fst G'.hom (spMap (residue W')) =
      pullback.fst G'.hom (spMap i₂ ≫ spMap (residue W')) := pullCompIso_fst _ _ _
  have f₃ : e₃.hom.left ≫ pullback.fst _ (spMap i₂) = pullback.fst _ (spMap i₂) ≫ e'.hom.left :=
    pullback_map_fst _ _
  have f₄ : e₄.hom.left ≫ pullback.fst Y.hom (spMap i₂ ≫ spMap κ') =
      pullback.fst _ (spMap i₂) ≫ pullback.fst Y.hom (spMap κ') := pullCompIso_inv_fst _ _ _
  refine ⟨e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄, e₁.hom.left ≫ e₂.hom.left ≫ pullback.fst _ (spMap i₂), ?_, ?_, ?_⟩
  · show IsMonHom (e₁.hom ≫ e₂.hom ≫ e₃.hom ≫ e₄.hom); infer_instance
  · rw [Category.assoc, Category.assoc, reassoc_of% f₂, he₁f]
  · show (e₁.hom ≫ e₂.hom ≫ e₃.hom ≫ e₄.hom).left ≫ _ = _
    simp only [Over.comp_left, Category.assoc]
    rw [f₄, reassoc_of% f₃]

end GlobalTheory.Mum.FibBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackPointsLiftMulInv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem grpPullback_points_lift_mul_inv : ∀ (T S : Scheme.{0}) (f : S ⟶ T) (G : Over T) [GrpObj G] (G' : Over S) [GrpObj G'] (β : G'.left ⟶ G.left), IsGrpPullback G' G f β → ∀ (Z' : Over S) (Z : Over T) (ζ : Z'.left ⟶ Z.left), ζ ≫ Z.hom = Z'.hom ≫ f → (∀ u : Z ⟶ G, ∃ u' : Z' ⟶ G', u'.left ≫ β = ζ ≫ u.left) ∧ ∀ (u v : Z ⟶ G) (u' v' : Z' ⟶ G'), u'.left ≫ β = ζ ≫ u.left → v'.left ≫ β = ζ ≫ v.left → (u' * v').left ≫ β = ζ ≫ (u * v).left ∧ (u'⁻¹).left ≫ β = ζ ≫ (u⁻¹).left := by
  intro T S f G _ G' _ β hpb Z' Z ζ hζ
  have hw : ∀ u : Z ⟶ G, (ζ ≫ u.left) ≫ G.hom = Z'.hom ≫ f := fun u => by
    rw [Category.assoc, Over.w u, hζ]
  refine ⟨fun u => ⟨Over.homMk (hpb.1.lift (ζ ≫ u.left) Z'.hom (hw u)) (hpb.1.lift_snd _ _ _),
    hpb.1.lift_fst _ _ _⟩, ?_⟩
  intro u v u' v' hu hv
  let ζ' : Over.mk (Z'.hom ≫ f) ⟶ Z := Over.homMk ζ hζ
  let φ : (Z' ⟶ G') → (Over.mk (Z'.hom ≫ f) ⟶ G) := fun w =>
    Over.homMk (w.left ≫ β) (by
      change (w.left ≫ β) ≫ G.hom = Z'.hom ≫ f
      rw [Category.assoc, hpb.1.w, ← Category.assoc, Over.w w])
  have hφ : ∀ a b, φ (a * b) = φ a * φ b := fun a b =>
    Over.OverMorphism.ext (hpb.2 Z' a b (φ a) (φ b) rfl rfl).symm
  let ψ := MonoidHom.mk' φ hφ
  have hu' : ψ u' = ζ' ≫ u := Over.OverMorphism.ext hu
  have hv' : ψ v' = ζ' ≫ v := Over.OverMorphism.ext hv
  constructor
  · have h : ψ (u' * v') = ζ' ≫ (u * v) := by rw [map_mul, hu', hv', MonObj.comp_mul]
    exact congrArg CommaMorphism.left h
  · have h : ψ (u'⁻¹) = ζ' ≫ (u⁻¹) := by rw [map_inv, hu', GrpObj.comp_inv]
    exact congrArg CommaMorphism.left h

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GsJKToOpenTop
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Mum.UnitValuedLeadingSection

noncomputable section

namespace GlobalTheory.Mum.UnitValuedLeadingSection

open Formalism.L2.Pj GlobalTheory.PsiCoordLocal

theorem gs_jK_toOpen_top {R : Type} [CommRing R] [IsDomain R] (z : (TK R).left) (r : R) :
    gs (jK R) z ⊤ (DegPre.toOpen (R := R) ⊤ r) = thK R z (algebraMap R (FractionRing R) r) := by
  have hz : jK R z ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) := trivial
  rw [gs_eq _ z ⊤ hz]
  have e := congrArg (fun f => f.hom r)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  have t : DegPre.toOpen (R := R) ⊤ r = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r := by
    simp [DegPre.toOpen]
  rw [t]
  simp only [thK, RingHom.comp_apply]
  rw [e]
  rfl

theorem psiIn_iff_val : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (z : (TK R).left) (J : ((TK R).left ⟶ D.P.A.left) → D.P.L.ι), TopGood D.P z J → ∀ (χ : D.X) (I : Ideal R), D.PsiIn χ I ↔ ∃ r ∈ I, ((val (D.psi χ) (𝟙 _) z J : ((TK R).left.presheaf.stalk z)ˣ) : (TK R).left.presheaf.stalk z) = thK R z (algebraMap R (FractionRing R) r) := by
  intro R _ _ _ D z J hJ χ I
  let j : PUnit → D.P.L.ι := fun _ => J (𝟙 _ ≫ D.xK χ)
  have hxK : 𝟙 _ ≫ D.xK χ = jK R ≫ (D.c χ).left := by
    rw [Category.id_comp]
    show (toUnit (TK R) ≫ D.c χ).left = _
    rw [Over.comp_left]
    congr 1 <;> simp
  have hj : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit) := by
    have := hJ.2 (D.c χ).left (Over.w (D.c χ))
    show ⊤ ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (J (𝟙 _ ≫ D.xK χ))
    rw [hxK, this]
  have h := generic_le D χ j hj
  have key : ∀ r : R, ((jK R).app ⊤).hom (DegPre.toOpen (R := R) ⊤ r) =
      ((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val ↔
      ((val (D.psi χ) (𝟙 _) z J : ((TK R).left.presheaf.stalk z)ˣ) : (TK R).left.presheaf.stalk z) =
        thK R z (algebraMap R (FractionRing R) r) := by
    intro r
    have hz : z ∈ jK R ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of R)).Opens) := trivial
    have g1 : gs (𝟙 (Spec (CommRingCat.of (FractionRing R)))) z _ (((jK R).app ⊤).hom (DegPre.toOpen (R := R) ⊤ r)) =
        thK R z (algebraMap R (FractionRing R) r) := by
      rw [gs_pull (𝟙 _) (jK R) z ⊤ trivial, Category.id_comp]
      exact gs_jK_toOpen_top z r
    have g2 : gs (𝟙 (Spec (CommRingCat.of (FractionRing R)))) z _ (((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val) =
        ((val (D.psi χ) (𝟙 _) z J : ((TK R).left.presheaf.stalk z)ˣ) : (TK R).left.presheaf.stalk z) := by
      refine (gs_res _ z h hz _).trans ((gs_unit _ _ _ (h hz) _).trans ?_)
      rfl
    constructor
    · intro e
      rw [← g1, ← g2, e]
    · intro e
      refine fn_ext fun y _ => ?_
      obtain rfl : y = z := Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) y z
      rw [g1, g2, e]
  constructor
  · intro hI
    obtain ⟨s, hs, es⟩ := hI j ⊤ (isAffineOpen_top _) hj h
    obtain ⟨r, hr, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ toOpen_top_bijective.2).1 hs
    exact ⟨r, hr, (key r).1 es⟩
  · rintro ⟨r, hr, e⟩
    exact (GlobalTheory.PeriodFormEdge.psiIn_iff ⟨j, hj, h, (key r).2 e⟩ I).2 hr

end GlobalTheory.Mum.UnitValuedLeadingSection
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GtPtAct
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Mum

def GtPtAct {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
    {O : Type} [Ring O] [StarRing O] [Module O D.X] (oa : D.OAct O) (a : O) (g g' : GtPtF D F) : Prop :=
  g'.b = g.b ≫ oa.onB.act a ∧
    ∀ u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (oa.onB.act (star a)) (oa.onB.act a)) rosatiε), u.IsGen →
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L) →
      ∀ χ, LB.Gen.Corr D.P.L _ _ _ _
        (LB.mulGen D.P.L _ _ _ _ (g.s (star a • χ))
          (LB.pullGen D.P.L _ _ u (lift (DegPre.cF D F χ) g.b).left)) (g'.s χ)

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GtRelVIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.TensRos

section Values

variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ}

def PV (W : Matrix (Fin r) (Fin r) ℤ) (e : N'.X → Fin r → N.X) (χ' : N'.X) (vs : Fin r → N.Gt) : F :=
  ((∏ i, ∏ j, ((vs j).s (e χ' i) * (vs i).s (e χ' j) /
      (N.θ (N.c (e χ' j)) (vs j).b (N.c (e χ' i)) * N.θ (N.c (e χ' j)) (vs j).b (vs i).b *
        N.θ (N.c (e χ' i)) (vs i).b (N.c (e χ' j) * (vs j).b))) ^ W i j : Fˣ) : F)

theorem gtRelV_iff (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F)
    (v' : N'.Gt) (vs : Fin r → N.Gt) :
    GtRelV W φ e wv v' vs ↔ (∀ j, φ v'.b j = (vs j).b) ∧ ∀ χ' : N'.X,
      (v'.s χ' : F) * wv (N'.c χ') * wv v'.b = PV W e χ' vs * wv (N'.c χ' * v'.b) * wv 1 := Iff.rfl

end Values

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
  {F : Type} [Field F] [Algebra (FractionRing R) F] {N N' : NumD F}

def tensJ (T : Tens D D' W) (ν : NumOf D F N) (y : Sp F ⟶ D'.P.A.left) :
    (LB.LinComb D.P.L (tensφ T.pr) (tensε W)).ι :=
  fun k => ν.J (y ≫ tensφ T.pr k)

def RosVT (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (f g : D'.P.A ⟶ D'.P.A) (ρ : N'.A → N'.A → F) :
    Prop :=
  ∃ u : LB.Gen (LB.LinComb (LB.LinComb D.P.L (tensφ T.pr) (tensε W)) (rosatiφ D'.P.A f g) rosatiε), u.IsGen ∧
    LB.Gen.Corr (LB.LinComb D.P.L (tensφ T.pr) (tensε W)) _ _ _ _
      (LB.pullGen (LB.LinComb D.P.L (tensφ T.pr) (tensε W)) _ _ u (zero2 D'.P.A))
      (LB.oneGen (LB.LinComb D.P.L (tensφ T.pr) (tensε W))) ∧
    ∀ b b', ρ b b' = vF u (lift (ν'.eA b) (ν'.eA b')).left (tensJ T ν)

theorem cmp_actV {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    (T : Tens D D' W) {F : Type} [Field F] [Algebra (FractionRing R) F] {N N' : NumD F} (ν : NumOf D F N)
    (ν' : NumOf D' F N') {O : Type} [CommRing O] [StarRing O] [Module O D'.X] (o : D'.OAct O)
    (ρ : O →+* Matrix (Fin r) (Fin r) ℤ) (hact : T.IsAct o ρ) (x : O) (b : N'.A) (j : Fin r) :
    GlobalTheory.Mum.TensTor.cmp T ν ν' (GlobalTheory.Relabel.actV ν' o.onB x b) j = ∏ k, GlobalTheory.Mum.TensTor.cmp T ν ν' b k ^ ρ x j k := by
  letI := D.P.isAb.comm
  let P : (D'.P.A ⟶ D.P.A) →* (TF (R := R) F ⟶ D.P.A) :=
    { toFun := fun f => ν'.eA b ≫ f
      map_one' := MonObj.comp_one _
      map_mul' := fun f g => MonObj.comp_mul _ _ _ }
  have e : ν'.eA (GlobalTheory.Relabel.actV ν' o.onB x b) ≫ T.pr j = P (∏ k, T.pr k ^ ρ x j k) := by
    rw [GlobalTheory.Relabel.actV, MulEquiv.apply_symm_apply, Category.assoc, hact.2 x j]; rfl
  rw [GlobalTheory.Mum.TensTor.cmp, e, map_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow, map_zpow]
  rfl

theorem c_actV {R : Type} [CommRing R] [IsDomain R] {D' : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {N' : NumD F} (ν' : NumOf D' F N') {O : Type} [CommRing O] [StarRing O]
    [Module O D'.X] (o : D'.OAct O) (a : O) (χ : N'.X) :
    GlobalTheory.Relabel.actV ν' o.onB a (N'.c χ) = N'.c (ν'.eX.symm (a • ν'.eX χ)) := by
  apply ν'.eA.injective
  rw [GlobalTheory.Relabel.actV, MulEquiv.apply_symm_apply, ν'.c_eq, ν'.c_eq, AddEquiv.apply_symm_apply]
  show (toUnit _ ≫ D'.c _) ≫ _ = toUnit _ ≫ D'.c _
  rw [o.c_lin, Category.assoc]

end GlobalTheory.Mum.TensRos
end
end

