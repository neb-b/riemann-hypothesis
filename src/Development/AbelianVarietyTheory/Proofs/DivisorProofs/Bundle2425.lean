module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedGroupsBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2223
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2401
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2131
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2372
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2306
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0759
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2374
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2149
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2353
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCancelGrpPullbackWithSquares
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.GrpCancel

theorem exists_cancel_square : ∀ (SA SB SC : Scheme.{0}) (A : Over SA) [GrpObj A] (B : Over SB) [GrpObj B] (C : Over SC) [GrpObj C] (g : SA ⟶ SB) (f : SB ⟶ SC) (a : A.left ⟶ C.left) (b : B.left ⟶ C.left) (a₂ : (G2 A).left ⟶ (G2 C).left) (b₂ : (G2 B).left ⟶ (G2 C).left), IsGrpPullback A C (g ≫ f) a → IsGrpPullback B C f b → IsSquare a a₂ → IsSquare b b₂ → ∃ (β : A.left ⟶ B.left) (β₂ : (G2 A).left ⟶ (G2 B).left), IsGrpPullback A B g β ∧ IsSquare β β₂ ∧ β ≫ b = a ∧ β₂ ≫ b₂ = a₂ := by
  intro SA SB SC A _ B _ C _ g f a b a₂ b₂ ha hb sa sb
  let β : A.left ⟶ B.left := hb.1.lift a (A.hom ≫ g) (by rw [Category.assoc]; exact ha.1.w)
  have e : β ≫ b = a := hb.1.lift_fst _ _ _
  have w : β ≫ B.hom = A.hom ≫ g := hb.1.lift_snd _ _ _
  have hβ : IsGrpPullback A B g β := IsGrpPullback.cancel hb (e.symm ▸ ha) w
  let β₂ : (G2 A).left ⟶ (G2 B).left := (lift (pushPt w (fst A A)) (pushPt w (snd A A))).left
  have s : IsSquare β β₂ :=
    ⟨congrArg (fun z => z.left) (lift_fst (pushPt w (fst A A)) (pushPt w (snd A A))),
      congrArg (fun z => z.left) (lift_snd (pushPt w (fst A A)) (pushPt w (snd A A)))⟩
  refine ⟨β, β₂, hβ, s, e, ?_⟩
  have h₁ : (β₂ ≫ b₂) ≫ (fst C C).left = a₂ ≫ (fst C C).left := by
    rw [Category.assoc, sb.1, ← Category.assoc, s.1, Category.assoc, e, sa.1]
  have h₂ : (β₂ ≫ b₂) ≫ (snd C C).left = a₂ ≫ (snd C C).left := by
    rw [Category.assoc, sb.2, ← Category.assoc, s.2, Category.assoc, e, sa.2]
  exact pullback.hom_ext h₁ h₂

end GlobalTheory.GrpCancel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCdvrDominating
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.DvrDom

theorem exists_cdvr_dominating : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R], ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (φ : R →+* V), GlobalTheory.LN.CDvr V ∧ Function.Injective φ ∧ IsLocalHom φ := by
  intro R _ _ _ _ _
  by_cases hR : IsField R
  · letI : Field R := hR.toField
    have hC : Function.Injective (PowerSeries.C (R := R)) := PowerSeries.C_injective
    have : CharZero (PowerSeries R) := charZero_of_injective_ringHom hC
    have hc : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries R)) (PowerSeries R) := by
      first
      | infer_instance
      | (rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance)
    have hl : IsLocalHom (PowerSeries.C (R := R)) := by
      constructor
      intro a ha
      by_cases h0 : a = 0
      · subst h0; simp at ha
      · exact isUnit_iff_ne_zero.mpr h0
    exact ⟨PowerSeries R, inferInstance, inferInstance, inferInstance, PowerSeries.C (R := R),
      (GlobalTheory.LN.cDvr_iff _).2 ⟨inferInstance, hc, this⟩, hC, hl⟩
  · obtain ⟨O, _, hO, hO', hO'', φ, h1, h2⟩ := GlobalTheory.exists_complete_discreteValuationRing_dominating (R := R) hR
    have : CharZero O := charZero_of_injective_ringHom h1
    exact ⟨O, inferInstance, hO, inferInstance, φ, (GlobalTheory.LN.cDvr_iff _).2 ⟨hO', hO'', this⟩, h1, h2⟩

end GlobalTheory.DvrDom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedFibrePt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.SecEmb.ThetaPt

theorem exists_trait_pt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (M : Modif R) (x : M.S),
    M.π x = closedPoint R → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W)
      (ξ : Sp W ⟶ M.S), GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ ξ ≫ M.π = spMap φ ∧
      ξ (closedPoint W) = x := by
  intro R _ _ _ hR M x hx
  obtain ⟨⟨hRn, -, -, -⟩, hR0⟩ := hR
  haveI := M.integral
  haveI := M.proper
  haveI : IsLocallyNoetherian M.S := LocallyOfFiniteType.isLocallyNoetherian M.π
  let A := M.S.presheaf.stalk x
  let ψc : CommRingCat.of R ⟶ A :=
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ M.π.appTop ≫ M.S.presheaf.germ ⊤ x trivial
  have hcomp : M.S.fromSpecStalk x ≫ M.π = Spec.map ψc := by
    simp only [ψc]
    rw [Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ, Category.assoc, Category.assoc,
      ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have hπinj : Function.Injective M.π.appTop.hom := fun a b h => GlobalTheory.Mum.jK_appTop_injective R (by
    rw [← M.appTop_comp, ← M.appTop_comp, h])
  have hψi : Function.Injective ψc.hom := by
    simp only [ψc, CommRingCat.hom_comp, RingHom.coe_comp]
    exact (germ_injective_of_isIntegral M.S (U := ⊤) x trivial).comp
      (hπinj.comp (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv.symm.injective)
  have hψl : IsLocalHom ψc.hom := by
    refine ((IsLocalRing.local_hom_tfae ψc.hom).out 1 5).2 ?_
    have e1 : (Spec.map ψc) (closedPoint A) = closedPoint R := by
      have h0 := congrArg M.π (Scheme.fromSpecStalk_closedPoint (x := x))
      rw [hx] at h0
      rw [← hcomp]
      exact h0
    exact congrArg PrimeSpectrum.asIdeal e1
  haveI : CharZero A := charZero_of_injective_ringHom hψi
  obtain ⟨V, _, _, _, φ₀, hV, hφ₀i, hφ₀l⟩ : ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V)
      (φ₀ : A →+* V), GlobalTheory.LN.CDvr V ∧ Function.Injective φ₀ ∧ IsLocalHom φ₀ := by
    by_cases h : IsField A
    · letI := h.toField
      refine ⟨PowerSeries A, inferInstance, inferInstance, inferInstance, PowerSeries.C, ⟨inferInstance, ?_, ?_⟩,
        PowerSeries.C_injective, inferInstance⟩
      · rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
      · exact charZero_of_injective_ringHom (f := PowerSeries.C (R := A)) PowerSeries.C_injective
    · obtain ⟨O, _, _, _, _, φ, h1, h2⟩ := GlobalTheory.exists_complete_discreteValuationRing_dominating A h
      exact ⟨O, inferInstance, inferInstance, inferInstance, φ,
        ⟨inferInstance, inferInstance, charZero_of_injective_ringHom h1⟩, h1, h2⟩
  refine ⟨V, inferInstance, inferInstance, inferInstance, φ₀.comp ψc.hom, spMap φ₀ ≫ M.S.fromSpecStalk x, hV,
    hφ₀i.comp hψi, RingHom.isLocalHom_comp _ _, ?_, ?_⟩
  · rw [Category.assoc, hcomp]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom]
  · exact (Scheme.Hom.comp_apply _ _ _).trans
      (Eq.trans (congrArg (M.S.fromSpecStalk x) (IsLocalRing.comap_closedPoint φ₀)) Scheme.fromSpecStalk_closedPoint)

theorem isLocalHom_of_finite {W W' : Type} [CommRing W] [IsLocalRing W] [CommRing W'] [IsLocalRing W']
    (io : W →+* W') (hf : io.Finite) : IsLocalHom io := by
  letI := io.toAlgebra
  haveI : Module.Finite W W' := hf
  have hmax : (maximalIdeal W').comap (algebraMap W W') = maximalIdeal W :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap _ _) (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) (maximalIdeal W'))
  refine ⟨fun a ha => ?_⟩
  by_contra h
  have : a ∈ (maximalIdeal W').comap (algebraMap W W') := hmax ▸ (IsLocalRing.mem_maximalIdeal a).2 h
  exact (IsLocalRing.mem_maximalIdeal _).1 (Ideal.mem_comap.1 this) ha

theorem exists_closedFibre_pt {W W' : Type} [CommRing W] [IsLocalRing W] [CommRing W'] [IsLocalRing W']
    (io : W →+* W') [IsLocalHom io] {S : Scheme.{0}} (G : Over S) (G' : Over (Sp W')) (ξ : Sp W ⟶ S)
    (β : G'.left ⟶ G.left) (h : IsPullback β G'.hom G.hom (spMap io ≫ ξ)) (g : G.left)
    (hg : G.hom g = ξ (closedPoint W)) :
    ∃ q : ((Over.pullback (spMap (residue W'))).obj G').left, (pullback.fst G'.hom (spMap (residue W')) ≫ β) q = g := by
  have h1 : (spMap io) (closedPoint W') = closedPoint W := IsLocalRing.comap_closedPoint io
  obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := spMap io ≫ ξ) g
    (closedPoint W') (by rw [hg]; exact (congrArg ξ h1).symm)
  have hg1 : β (h.isoPullback.inv z) = g := by
    rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst, hz1]
  have hg2 : G'.hom (h.isoPullback.inv z) = closedPoint W' := by
    rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_snd, hz2]
  have h2 : (spMap (residue W')) (closedPoint (ResidueField W')) = closedPoint W' :=
    IsLocalRing.comap_closedPoint (residue W')
  obtain ⟨q, hq1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := G'.hom) (g := spMap (residue W'))
    (h.isoPullback.inv z) (closedPoint _) (hg2.trans h2.symm)
  exact ⟨q, by rw [Scheme.Hom.comp_apply, hq1, hg1]⟩

theorem toProj_congr {R : Type} [CommRing R] {M : ℕ} {Y : Scheme.{0}} {L : LB Y} {f f' : Y ⟶ Sp R}
    (e : f = f') (s : Fin (M + 1) → L.Sec) (hs hs' : ⨆ i, nonzeroLocus (s i) = ⊤) :
    GlobalTheory.ProjSpace.toProj f s hs = GlobalTheory.ProjSpace.toProj f' s hs' := by
  subst e; rfl

theorem mem_basicOpen_theta : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (M : Modif R) (G : Over M.S) [GrpObj G],
    IsSemiAbelian G → ∀ (B L : LB G.left), B.IsLB → L.IsLB → ∀ (N : ℕ) (s : Fin (N + 1) → B.Sec) (θ : L.Sec)
    (Y : Over (Sp (ResidueField R))) [GrpObj Y], Smooth Y.hom → ∀ (j : Y.left ⟶ PSpace R N),
    j ≫ PSpace.str R N = Y.hom ≫ spMap (residue R) → IsImmersion j → ∀ (O : Y.left.Opens),
    GlobalTheory.Mum.SecEmb.TraitRed M G s θ Y j O →
    ∀ (g : (GlobalTheory.Mum.SecEmb.embH s).toScheme) (y : Y.left), y ∈ O →
    M.π (G.hom ((GlobalTheory.Mum.SecEmb.embH s).ι g)) = closedPoint R → GlobalTheory.Mum.SecEmb.embF (G.hom ≫ M.π) s g = j y →
    ∃ i : L.ι, (GlobalTheory.Mum.SecEmb.embH s).ι g ∈ G.left.basicOpen (θ.f i) := by
  intro R _ _ _ hR M G _ hG B L hB hL N s θ Y _ hY j hj hji O hT g y hy hgc hgj
  obtain ⟨W, _, _, _, φ, ξ, hW, hφi, hφl, hξ, hξx⟩ := exists_trait_pt R hR M _ hgc
  obtain ⟨W', _, _, _, io, G', _, β, κ, e, hW', hio, hiof, hpb, hκ, he, H⟩ := hT W hW φ ξ hφi hφl hξ
  haveI := isLocalHom_of_finite io hiof
  obtain ⟨q, hq⟩ := exists_closedFibre_pt io G G' ξ β hpb.1 _ hξx.symm
  let Ω : Type := (((Over.pullback (spMap (residue W'))).obj G').left).residueField q
  let p : Sp Ω ⟶ ((Over.pullback (spMap (residue W'))).obj G').left :=
    (((Over.pullback (spMap (residue W'))).obj G').left).fromSpecResidueField q
  haveI : Subsingleton (Sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  obtain ⟨p', hp'⟩ : ∃ p', p' = p ≫ pullback.fst G'.hom (spMap (residue W')) := ⟨_, rfl⟩
  obtain ⟨y', hy'⟩ : ∃ y', y' = p ≫ e.hom.left ≫ pullback.fst Y.hom (spMap κ) := ⟨_, rfl⟩
  obtain ⟨⟨hs, hproj⟩, hnz⟩ := H Ω p p' y' hp' hy'
  let pt : Sp Ω := closedPoint Ω
  have hpt : ∀ z : Sp Ω, z = pt := fun z => Subsingleton.elim _ _
  have hppt : p pt = q := Scheme.fromSpecResidueField_apply q pt
  have hg' : (p' ≫ β) pt = (embH s).ι g := by
    rw [hp', Category.assoc, Scheme.Hom.comp_apply, hppt]
    exact hq
  have hrange : Set.range (p' ≫ β) ⊆ Set.range (embH s).ι := by
    rintro _ ⟨z, rfl⟩
    rw [hpt z, hg']
    exact ⟨g, rfl⟩
  obtain ⟨l₀, hl₀⟩ : ∃ l₀ : Sp Ω ⟶ (embH s).toScheme, l₀ ≫ (embH s).ι = p' ≫ β :=
    ⟨_, IsOpenImmersion.lift_fac _ _ hrange⟩
  have hl₀pt : l₀ pt = g := by
    apply (embH s).ι.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hl₀, hg']
  obtain ⟨-, hs2, e2⟩ := GlobalTheory.Mum.toProj_secPull_of_gs (Z := Sp Ω) s (fun i => GlobalTheory.secPull (s i) (embH s).ι)
    ((embH s).ι ≫ G.hom ≫ M.π) (iSup_nonzeroLocus_embH s) (p' ≫ β) l₀ (fun z => by
      obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 (hB.cover.ge (Set.mem_univ ((p' ≫ β) z)))
      have hla : l₀ z ∈ (B.pull (embH s).ι).U (fun _ => a) := Set.mem_iInter.2 fun _ => by
        show (embH s).ι (l₀ z) ∈ B.U a
        rw [← Scheme.Hom.comp_apply, hl₀]; exact ha
      refine ⟨a, fun _ => a, 1, ha, hla, fun i => ?_⟩
      rw [Units.val_one, _root_.one_mul]
      refine Eq.trans ?_ (GlobalTheory.gs_chartSec (GlobalTheory.chartPullPull B (embH s).ι) (s i) l₀ z (fun _ => a) hla).symm
      rw [hl₀]; rfl)
  have hstr : p' ≫ G'.hom ≫ spMap (io.comp φ) = l₀ ≫ (embH s).ι ≫ G.hom ≫ M.π := by
    have hw : β ≫ G.hom ≫ M.π = G'.hom ≫ spMap io ≫ ξ ≫ M.π := by
      rw [← Category.assoc, hpb.1.w]; simp only [Category.assoc]
    have hc : spMap (io.comp φ) = spMap io ≫ spMap φ := by
      simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    rw [reassoc_of% hl₀, hw, hξ, hc]
  have key : y' ≫ j = l₀ ≫ embF (G.hom ≫ M.π) s := by
    rw [← hproj, toProj_congr hstr _ hs hs2]
    exact e2
  have hyy : y' pt = y := by
    apply hji.isEmbedding.injective
    rw [← Scheme.Hom.comp_apply, key, Scheme.Hom.comp_apply, hl₀pt, hgj]
  have hθ := hnz pt (hyy ▸ hy)
  rw [hg'] at hθ
  exact TopologicalSpace.Opens.mem_iSup.1 hθ

end GlobalTheory.Mum.SecEmb.ThetaPt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonExtensionDvrFractionFields
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.FieldTraitExt

theorem exists_normalization (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R)
    (K' : Type) [Field K'] (io : FractionRing R →+* K') (hio : io.Finite) :
    ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ : R →+* R₂) (i : K' ≃+* FractionRing R₂)
      (e : R₂ →+* K'), FinExt ρ ∧ Function.Injective e ∧ (∀ r, e (ρ r) = io (algebraMap R _ r)) ∧
      ∀ y, i (e y) = algebraMap R₂ _ y := by
  obtain ⟨⟨hnoeth, -, hic, hcomp⟩, hchar⟩ := hR
  letI : Algebra (FractionRing R) K' := io.toAlgebra
  letI : Algebra R K' := (io.comp (algebraMap R (FractionRing R))).toAlgebra
  haveI : IsScalarTower R (FractionRing R) K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional (FractionRing R) K' := hio
  haveI : CharZero (FractionRing R) := IsFractionRing.charZero_of_isFractionRing R
  let R₂ := integralClosure R K'
  haveI hfin : Module.Finite R R₂ := IsIntegralClosure.finite R (FractionRing R) K' R₂
  haveI : IsLocalRing R₂ := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := R) R₂
  haveI : IsFractionRing R₂ K' := IsIntegralClosure.isFractionRing_of_finite_extension R (FractionRing R) K' R₂
  have hRK : Function.Injective (algebraMap R K') := io.injective.comp (IsFractionRing.injective R _)
  have hinj : Function.Injective (algebraMap R R₂) := fun x y h => hRK (congrArg Subtype.val h)
  haveI : IsNoetherianRing R₂ := IsNoetherianRing.of_finite R R₂
  refine ⟨R₂, inferInstance, inferInstance, inferInstance, algebraMap R R₂,
    (IsLocalization.algEquiv (nonZeroDivisors R₂) K' (FractionRing R₂)).toRingEquiv, algebraMap R₂ K',
    ⟨⟨inferInstance, inferInstance, integralClosure.isIntegrallyClosedOfFiniteExtension (FractionRing R),
      GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local R R₂⟩, hinj, RingHom.finite_algebraMap.2 hfin⟩,
    Subtype.val_injective, fun r => rfl, fun y => ?_⟩
  exact (IsLocalization.algEquiv (nonZeroDivisors R₂) K' (FractionRing R₂)).commutes y

theorem exists_trait (R R₂ W : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R₂] [IsDomain R₂]
    [IsLocalRing R₂] [CommRing W] [IsDomain W] [IsLocalRing W] (hW : GlobalTheory.LN.CDvr W) (φ : R →+* W)
    (hφ : IsLocalHom φ) (ρ : R →+* R₂) (hρ : ρ.Finite) (Ω : Type) [Field Ω] (j : FractionRing W →+* Ω)
    (m : R₂ →+* Ω) (hm : Function.Injective m) (hc : ∀ r, m (ρ r) = j (algebraMap W _ (φ r))) :
    ∃ (W₂ : Type) (_ : CommRing W₂) (_ : IsDomain W₂) (_ : IsLocalRing W₂) (σ : W →+* W₂) (φ₂ : R₂ →+* W₂)
      (j₂ : FractionRing W₂ →+* Ω), GlobalTheory.LN.CDvr W₂ ∧ FinExt σ ∧ IsLocalHom σ ∧ Function.Injective φ₂ ∧
      IsLocalHom φ₂ ∧ φ₂.comp ρ = σ.comp φ ∧ (∀ w, j₂ (algebraMap W₂ _ (σ w)) = j (algebraMap W _ w)) ∧
      ∀ r, j₂ (algebraMap W₂ _ (φ₂ r)) = m r := by
  first
  | exact @_root_.GlobalTheory.FiniteCompletionLocalHom.exists_extension
  | exact _root_.GlobalTheory.FiniteCompletionLocalHom.exists_extension
  | (apply _root_.GlobalTheory.FiniteCompletionLocalHom.exists_extension <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteCompletionLocalHom.exists_extension <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteCompletionLocalHom.exists_extension <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteCompletionLocalHom.exists_extension ..)

end GlobalTheory.FieldTraitExt

namespace GlobalTheory.FieldTraitExt

theorem exists_finite_extension_of_trait : ∀ (R W : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing W] [IsDomain W] [IsLocalRing W], Base R → GlobalTheory.LN.CDvr W → ∀ φ : R →+* W, Function.Injective φ → IsLocalHom φ → ∀ (K' Ω : Type) [Field K'] [Field Ω] (io : FractionRing R →+* K') (j : FractionRing W →+* Ω) (l : K' →+* Ω), io.Finite → (∀ r, l (io (algebraMap R _ r)) = j (algebraMap W _ (φ r))) → ∃ (R₂ : Type) (_ : CommRing R₂) (_ : IsDomain R₂) (_ : IsLocalRing R₂) (ρ : R →+* R₂) (i : K' ≃+* FractionRing R₂) (W₂ : Type) (_ : CommRing W₂) (_ : IsDomain W₂) (_ : IsLocalRing W₂) (σ : W →+* W₂) (φ₂ : R₂ →+* W₂) (j₂ : FractionRing W₂ →+* Ω), FinExt ρ ∧ GlobalTheory.LN.CDvr W₂ ∧ FinExt σ ∧ IsLocalHom σ ∧ Function.Injective φ₂ ∧ IsLocalHom φ₂ ∧ φ₂.comp ρ = σ.comp φ ∧ (∀ r, i (io (algebraMap R _ r)) = algebraMap R₂ _ (ρ r)) ∧ (∀ w, j₂ (algebraMap W₂ _ (σ w)) = j (algebraMap W _ w)) ∧ ∀ r, j₂ (algebraMap W₂ _ (φ₂ r)) = l (i.symm (algebraMap R₂ _ r)) := by
  intro R W _ _ _ _ _ _ hR hW φ _ hφ K' Ω _ _ io j l hio hc
  obtain ⟨R₂, _, _, _, ρ, i, e, hfe, he, heρ, hie⟩ := exists_normalization R hR K' io hio
  obtain ⟨W₂, _, _, _, σ, φ₂, j₂, hW₂, hσ, hσl, hφ₂i, hφ₂l, hcomm, hj₁, hj₂⟩ :=
    exists_trait R R₂ W hW φ hφ ρ hfe.2.2 Ω j (l.comp e) (l.injective.comp he)
      (fun r => by rw [RingHom.comp_apply, heρ, hc])
  refine ⟨R₂, _, _, _, ρ, i, W₂, _, _, _, σ, φ₂, j₂, hfe, hW₂, hσ, hσl, hφ₂i, hφ₂l, hcomm, fun r => ?_, hj₁,
    fun r => ?_⟩
  · rw [← heρ, hie]
  · rw [hj₂, RingHom.comp_apply]
    congr 1
    rw [RingEquiv.eq_symm_apply, hie]

end GlobalTheory.FieldTraitExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommutingCoordinateDerivationsRegularFunct
section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
open Filter Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem exists_commuting_derivations_of_values {R : Type} [CommRing R] [Algebra ℂ R] {g : ℕ} (P : Set (Fin g → ℂ))
    (v : R → (Fin g → ℂ) → ℂ) (hP : IsOpen P) (hd : ∀ x, DifferentiableOn ℂ (v x) P)
    (he : ∀ z ∈ P, ∃ e : R →ₐ[ℂ] ℂ, ∀ b, v b z = e b) (hinj : ∀ x, (∀ z ∈ P, v x z = 0) → x = 0)
    (hder : ∀ x w, ∃ y, ∀ z ∈ P, fderiv ℂ (v x) z w = v y z) :
    ∃ d : Fin g → Derivation ℂ R R, (∀ a b x, d a (d b x) = d b (d a x)) ∧
      ∀ a x, ∀ z ∈ P, v (d a x) z = fderiv ℂ (v x) z (Pi.single a 1) := by
  choose D hD using hder
  have hext : ∀ x y, (∀ z ∈ P, v x z = v y z) → x = y := fun x y h ↦ by
    refine sub_eq_zero.1 (hinj _ fun z hz ↦ ?_)
    obtain ⟨e, he⟩ := he z hz
    rw [he, map_sub, ← he, ← he, h z hz, sub_self]
  have hadd : ∀ x y, ∀ z ∈ P, v (x + y) z = v x z + v y z := fun x y z hz ↦ by
    obtain ⟨e, he⟩ := he z hz
    simp only [he, map_add (f := _)]
  have hmul : ∀ x y, ∀ z ∈ P, v (x * y) z = v x z * v y z := fun x y z hz ↦ by
    obtain ⟨e, he⟩ := he z hz
    simp only [he, map_mul]
  have hsmul : ∀ (c : ℂ) x, ∀ z ∈ P, v (c • x) z = c • v x z := fun c x z hz ↦ by
    obtain ⟨e, he⟩ := he z hz
    simp only [he, map_smul]
  have hat : ∀ x, ∀ z ∈ P, DifferentiableAt ℂ (v x) z := fun x z hz ↦ (hd x).differentiableAt (hP.mem_nhds hz)
  have hcongr : ∀ (f k : (Fin g → ℂ) → ℂ), (∀ z ∈ P, f z = k z) → ∀ z ∈ P, fderiv ℂ f z = fderiv ℂ k z :=
    fun f k h z hz ↦ Filter.EventuallyEq.fderiv_eq (Filter.eventually_of_mem (hP.mem_nhds hz) h)
  let Dl : (Fin g → ℂ) → R →ₗ[ℂ] R := fun w ↦
    { toFun := fun x ↦ D x w
      map_add' := fun x y ↦ hext _ _ fun z hz ↦ by
        rw [hadd _ _ z hz, ← hD _ _ z hz, ← hD _ _ z hz, ← hD _ _ z hz,
          hcongr _ (v x + v y) (hadd x y) z hz, fderiv_add (hat x z hz) (hat y z hz)]
        rfl
      map_smul' := fun c x ↦ hext _ _ fun z hz ↦ by
        rw [RingHom.id_apply, hsmul _ _ z hz, ← hD _ _ z hz, ← hD _ _ z hz,
          hcongr _ (c • v x) (hsmul c x) z hz, fderiv_const_smul (hat x z hz)]
        rfl }
  have hL : ∀ w x y, Dl w (x * y) = x • Dl w y + y • Dl w x := fun w x y ↦ hext _ _ fun z hz ↦ by
    change v (D (x * y) w) z = v (x * D y w + y * D x w) z
    rw [hadd _ _ z hz, hmul _ _ z hz, hmul _ _ z hz, ← hD _ _ z hz, ← hD _ _ z hz, ← hD _ _ z hz,
      hcongr _ (v x * v y) (hmul x y) z hz, fderiv_mul (hat x z hz) (hat y z hz)]
    rfl
  have h2 : ∀ x w w', ∀ z ∈ P, v (D (D x w) w') z = fderiv ℂ (fderiv ℂ (v x)) z w' w := fun x w w' z hz ↦ by
    have ha : AnalyticAt ℂ (v x) z := ReciprocityTheory.AnForm.Osgood.osgood g P (v x) hP (hd x) z hz
    rw [← hD _ _ z hz, ← hcongr _ _ (hD x w) z hz,
      fderiv_clm_apply ha.fderiv.differentiableAt (differentiableAt_const w)]
    simp
  refine ⟨fun a ↦ Derivation.mk' (Dl (Pi.single a 1)) (hL _), fun a b x ↦ hext _ _ fun z hz ↦ ?_,
    fun a x z hz ↦ (hD x _ z hz).symm⟩
  have ha : AnalyticAt ℂ (v x) z := ReciprocityTheory.AnForm.Osgood.osgood g P (v x) hP (hd x) z hz
  change v (D (D x _) _) z = v (D (D x _) _) z
  rw [h2 _ _ _ z hz, h2 _ _ _ z hz]
  exact (ha.contDiffAt (n := ⊤)).isSymmSndFDerivAt le_top _ _

theorem exists_commuting_coordinate_derivations : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens), ∃ d : Fin g → Derivation ℂ (Sec (str A) U) (Sec (str A) U), (∀ a b x, d a (d b x) = d b (d a x)) ∧ ∀ a x, ∀ z ∈ pre u.ex U, val u.ex U (d a x) z = fderiv ℂ (val u.ex U x) z (Pi.single a 1) := by
  intro A _ g L u hA U
  obtain ⟨h1, h2, -, -, -, -, -, -, -, h10, -⟩ := _root_.GlobalTheory.CechPer.pre_val_rules A g L u
  exact exists_commuting_derivations_of_values (R := Sec (str A) U) (pre u.ex U) (val u.ex U) (h1 U) (h2 U) (h10 U)
    (_root_.GlobalTheory.ValInj.eq_zero_of_val_eq_zero A g L u hA U) (_root_.GlobalTheory.CechPer.isReg_fderiv_val A g L u hA U)

end GlobalTheory.CechPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrValuesUnitary
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.UPoinc

theorem exists_complete_dvr_values_unitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X₁ : USetup C) (D : UDeep X₁) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (ct : UCTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra (FractionRing V) (PadicAlgCl p)], IsAdicComplete (IsLocalRing.maximalIdeal V) V → (∀ x : FractionRing V, ‖algebraMap (FractionRing V) (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) →
  ∃ (V₂ : Type) (_ : CommRing V₂) (_ : IsDomain V₂) (_ : IsDiscreteValuationRing V₂) (_ : Algebra (FractionRing V₂) (PadicAlgCl p)), IsAdicComplete (IsLocalRing.maximalIdeal V₂) V₂ ∧ (∀ x : FractionRing V₂, ‖algebraMap (FractionRing V₂) (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V₂ (FractionRing V₂))) ∧
    ∃ σ : FractionRing V →+* FractionRing V₂, (algebraMap (FractionRing V₂) (PadicAlgCl p)).comp σ = algebraMap (FractionRing V) (PadicAlgCl p) ∧
      ∀ a ∈ D.X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))), D.X.M.val (gPt p ≫ y) a ∈ (algebraMap (FractionRing V₂) (PadicAlgCl p)).range := by
  intro E _ _ _ H Dw l Xo cf C X₁ D p _ z₁ c y h V _ _ _ _ hc hV
  obtain ⟨R, _, hR, y₀, hval⟩ := GlobalTheory.ValField.exists_fg_values D.X.M (gPt p ≫ y)
  let κ : FractionRing V →+* PadicAlgCl p := algebraMap (FractionRing V) (PadicAlgCl p)
  haveI : CharZero V := RingHom.charZero (κ.comp (algebraMap V (FractionRing V)))
  have hQ := GlobalTheory.PadicUnitBall.padic_mem_range p V hc κ hV
  obtain ⟨W₂, i₁, i₂, i₃, hcW, -, fV, fK, κ', -, -, -, -, hκ', hunit, hy⟩ :=
    GlobalTheory.DvrFinExt.exists_finite_extension p V hc κ hV hQ R y₀
  letI : Algebra (FractionRing W₂) (PadicAlgCl p) := κ'.toAlgebra
  refine ⟨W₂, i₁, i₂, i₃, κ'.toAlgebra, hcW, hunit, fK, hκ', fun a ha => ?_⟩
  have hm := hval κ'.fieldRange (fun r => by obtain ⟨x, hx⟩ := hy r; exact ⟨x, hx⟩) a ha
  obtain ⟨x, hx⟩ := hm
  exact ⟨x, hx⟩

end GlobalTheory.UPoinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompletedLocalRingEndomorphismCharacterAct
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.UPoinc

theorem exists_endChar_pull : ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE) (x : M.Z) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (f : FinalForm.G ⟶ FinalForm.G), IsMonHom f → ∃ (fR : G ⟶ G) (m : D.toPre.X →+ D.toPre.X), IsMonHom fR ∧ fR.left ≫ gm = gm ≫ f.left ∧ EndChar U fR m := by
  intro o' Ω _ _ _ _ S ρ M U₀ EE FinalForm x R _ _ _ j hR G _ _ gm hpb D A U f hf
  have hG : IsSemiAbelian G := GlobalTheory.Mum.isSemiAbelian_of_isGrpPullback_square _ _ _ FinalForm.G G gm hpb FinalForm.semi
  let fR : G ⟶ G :=
    Over.homMk (hpb.1.lift (gm ≫ f.left) G.hom (by rw [Category.assoc, Over.w f, hpb.1.w])) (hpb.1.lift_snd _ _ _)
  have e : fR.left ≫ gm = gm ≫ f.left := hpb.1.lift_fst _ _ _
  have hfR : IsMonHom fR := Out.PullGtPf.isMonHom_of_grpPullback hpb hpb f fR e
  obtain ⟨m, hm⟩ := GlobalTheory.Poinc.Eq8.endChar_exists_of_isMonHom R hR G hG D A U fR hfR
  exact ⟨fR, m, hfR, e, hm⟩

end GlobalTheory.UPoinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearisationInvariantRigidifiedBundleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.GenDesc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearisation_invariant_rigidified_bundle : ∀ (T X : Scheme.{0}) (π : X ⟶ T) (e : T ⟶ X), e ≫ π = 𝟙 T → Function.Surjective π.appTop.hom → ∀ (L : LB X), L.IsLB → (∃ r : LB.Gen (L.pull e), r.IsGen) → ∀ (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (θ : Ga → (T ⟶ T)), (∀ a c, ρ (a * c) = ρ a ≫ ρ c) → (∀ a c, θ (a * c) = θ a ≫ θ c) → (∀ a, e ≫ ρ a = θ a ≫ e) → (∀ a, LBIso L (L.pull (ρ a))) → ∃ u : ∀ a, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, ρ a] ![1, -1]), (∀ a, (u a).IsGen) ∧ ∀ a c, LB.Gen.Corr L _ _ _ _ (u (a * c)) (LB.mulGen L _ _ _ _ (u a) (LB.pullGen L _ _ (u c) (ρ a))) := by
  first | exact @GlobalTheory.MumLin.exists_linearisation | exact GlobalTheory.MumLin.exists_linearisation | (intros; apply GlobalTheory.MumLin.exists_linearisation <;> assumption)
end

