module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericIsoExtendsSemiAbelianDvrInducingFormal
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0146
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1293
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniquePoint
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0200
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0705
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2123
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1997
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2045
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2055

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationDeterminedByDegenerationDataNormal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.DataDetNormal

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G G' : Over (Spec (CommRingCat.of R))}
  [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {U : Unif I D A G} {U' : Unif I D' A' G'}
  {hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre} {j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G}
  {Φ : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G}
  {w : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R))) (U.LG.L.pull (Φ.hom.left ≫ pullback.fst G.hom (jK R)))}

theorem isMonHom_generic (hL : Laws) (hR : AdmBase R I) (hI : I ≠ ⊤) (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (hj : GlobalTheory.GenericIso.LevelIso U.toUnifPre U'.toUnifPre hD j)
    (hE : GlobalTheory.GenericIso.Enough U.toUnifPre U'.toUnifPre hD j)
    (hw : GlobalTheory.GenericIso.GenericRel U.toUnifPre U'.toUnifPre hD j Φ w) : IsMonHom Φ.hom := by
  let ψ : A'.A ≅ A.A := U'.gen.symm ≪≫ Φ ≪≫ U.gen
  have hψ : Φ.hom ≫ U.gen.hom = U'.gen.hom ≫ ψ.hom := by simp [ψ]
  have := U.gen_hom
  have := U'.gen_hom
  have hm : IsMonHom ψ.hom := hL.rigidity _ _ _ A'.isAb A.isAb _ (by
    rw [← IsMonHom.one_hom U'.gen.hom, Category.assoc, ← hψ, ← Category.assoc, hw.one hL hR hI hG hG' hj hE,
      IsMonHom.one_hom])
  have e : Φ.hom = U'.gen.hom ≫ ψ.hom ≫ U.gen.inv := by simp [ψ]
  rw [e]
  infer_instance

end GlobalTheory.DataDetNormal

namespace GlobalTheory.DataDetNormal

theorem exists_iso_extending {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [GrpObj G'] (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (Φ : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G) [IsMonHom Φ.hom] :
    ∃ ψ : G' ≅ G, IsMonHom ψ.hom ∧ (Over.pullback (jK R)).map ψ.hom = Φ.hom := by
  have h := GlobalTheory.semiAbelianHomExtension_holds
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := h.fractionField R (FractionRing R) G' G hG' hG Φ.hom
  obtain ⟨F₁, ⟨hF₁, hF₁'⟩, -⟩ := h.fractionField R (FractionRing R) G G' hG hG' Φ.inv
  obtain ⟨E₁, -, u₁⟩ := h.fractionField R (FractionRing R) G' G' hG' hG' (𝟙 _)
  obtain ⟨E₂, -, u₂⟩ := h.fractionField R (FractionRing R) G G hG hG (𝟙 _)
  have c₁ : F ≫ F₁ = 𝟙 G' := (u₁ _ ⟨inferInstance, by rw [Functor.map_comp, hF', hF₁', Iso.hom_inv_id]⟩).trans
    (u₁ _ ⟨inferInstance, (Over.pullback _).map_id _⟩).symm
  have c₂ : F₁ ≫ F = 𝟙 G := (u₂ _ ⟨inferInstance, by rw [Functor.map_comp, hF', hF₁', Iso.inv_hom_id]⟩).trans
    (u₂ _ ⟨inferInstance, (Over.pullback _).map_id _⟩).symm
  exact ⟨⟨F, F₁, c₁, c₂⟩, hF, hF'⟩

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegData R I}
  {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G G' : Over (Spec (CommRingCat.of R))}
  [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {U : Unif I D A G} {U' : Unif I D' A' G'}
  {hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre} {j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G}
  {Φ : (Over.pullback (jK R)).obj G' ≅ (Over.pullback (jK R)).obj G}
  {w : LB.Iso (U'.LG.L.pull (pullback.fst G'.hom (jK R))) (U.LG.L.pull (Φ.hom.left ≫ pullback.fst G.hom (jK R)))}

theorem thick_compat (hL : Laws) (hR : AdmBase R I) (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (hj : GlobalTheory.GenericIso.LevelIso U.toUnifPre U'.toUnifPre hD j)
    (hE : GlobalTheory.GenericIso.Enough U.toUnifPre U'.toUnifPre hD j)
    (hw : GlobalTheory.GenericIso.GenericRel U.toUnifPre U'.toUnifPre hD j Φ w) (ψ : G' ⟶ G)
    (hψ : (Over.pullback (jK R)).map ψ = Φ.hom) (e : ℕ) :
    (fstG I e G').left ≫ ψ.left = (j e).hom.left ≫ (fstG I e G).left := by
  have := hR.1
  have := hG.smooth
  have := hG.separated
  have := hG'.smooth
  have := GlobalTheory.schemeTheoreticallyDominant_fractionField R (FractionRing R)
  have eψ : Φ.hom.left ≫ pullback.fst G.hom (jK R) = pullback.fst G'.hom (jK R) ≫ ψ.left := by
    rw [← hψ]; exact pullback.lift_fst _ _ _
  have hx0 : ∀ x : G'.left, I ≤ (G'.hom x).asIdeal → x ∈ Set.range (fstG I 0 G').left := fun x hx => by
    show x ∈ Set.range (pullback.fst G'.hom (thick R I 0))
    rw [Scheme.Pullback.range_fst]
    exact (GlobalTheory.FormalExt.range_thick I 0 _).2 hx
  refine GlobalTheory.FormalExt.hom_ext_of_flat_family _ _ fun y => ?_
  obtain ⟨x, hx⟩ := hx0 ((fstG I e G').left y) ((GlobalTheory.FormalExt.range_thick I e _).1 (by
    have : (fstG I e G').left y ∈ Set.range (pullback.fst G'.hom (thick R I e)) := ⟨y, rfl⟩
    rw [Scheme.Pullback.range_fst] at this
    exact this))
  obtain ⟨jL, hjL⟩ : ∃ i, (fstG I 0 G).left ((j 0).hom.left x) ∈ U.LG.L.U i :=
    TopologicalSpace.Opens.mem_iSup.1 (U.LG.isLB.cover.ge trivial)
  obtain ⟨jL', hjL'⟩ : ∃ i, (fstG I 0 G').left x ∈ U'.LG.L.U i :=
    TopologicalSpace.Opens.mem_iSup.1 (U'.LG.isLB.cover.ge trivial)
  obtain ⟨B, _, _, g', g, hB, -, hg'f, hxr, h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.CompletedPoint.exists_completed_point I G G'
    (fun e => (j e).hom) (fun e => (hj e).2.1) x _ _ hjL hjL'
  have hpt : ∀ {Z : Scheme.{0}} (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ ((Over.pullback (jK R)).obj G').left),
      r ≫ pullback.fst G'.hom (jK R) = ρ ≫ g' → r ≫ Φ.hom.left ≫ pullback.fst G.hom (jK R) = ρ ≫ g :=
    fun ρ r hr => hw.point hL hR hG hG' hE hB h₁ h₂ h₃ h₄ h₅ ρ r hr
  have hg : g' ≫ ψ.left = g := by
    let a : Over.mk (g' ≫ G'.hom) ⟶ G := Over.homMk (g' ≫ ψ.left) (by simp)
    let b : Over.mk (g' ≫ G'.hom) ⟶ G := Over.homMk g (h₂.trans h₁.symm)
    have : IsSchemeTheoreticallyDominant (pullback.fst G'.hom (jK R)) := inferInstance
    have : IsSchemeTheoreticallyDominant (pullback.fst g' (pullback.fst G'.hom (jK R))) := inferInstance
    have := GlobalTheory.over_ext_of_schemeTheoreticallyDominant (a := a) (b := b)
      (pullback.fst g' (pullback.fst G'.hom (jK R))) (by
        have := hpt _ (pullback.snd g' (pullback.fst G'.hom (jK R))) pullback.condition.symm
        rw [eψ] at this
        exact (pullback.condition_assoc _).trans this)
    exact congr(($this).left)
  refine ⟨_, pullback.snd g' (fstG I e G').left, inferInstance, ?_, ?_⟩
  · rw [Scheme.Pullback.range_snd]
    show (fstG I e G').left y ∈ Set.range g'
    rw [← hx]; exact hxr
  · rw [h₅ e _ _ _ pullback.condition.symm, ← pullback.condition_assoc, hg]

end GlobalTheory.DataDetNormal

theorem GlobalTheory.unif_determined_by_data_normal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, GlobalTheory.UT.Cl.Determined U := by
  intro R _ _ _ hR D A G _ _ hG U D' A' G' _ _ hG' U' hD
  have hL := GlobalTheory.firstFiveLaws.1
  have hI : maximalIdeal R ≠ ⊤ := (maximalIdeal.isMaximal R).ne_top
  have := hR.1
  have := hR.2.2.1
  obtain ⟨j, hj⟩ := GlobalTheory.GenericIso.exists_levelIso U.toUnifPre U'.toUnifPre hD hL.globalFns
  have hE := hj.enough hL.globalFns U.expand U'.expand
  obtain ⟨Φ, w, hw⟩ := GlobalTheory.GenericIso.exists_genericRel hL R _ hR D D' A A' G G' hG hG' U U' hD j hj hE
  have hΦ : IsMonHom Φ.hom := GlobalTheory.DataDetNormal.isMonHom_generic hL hR hI hG hG' hj hE hw
  obtain ⟨ψ, hψm, hψK⟩ := GlobalTheory.DataDetNormal.exists_iso_extending hG hG' Φ
  have hth := GlobalTheory.DataDetNormal.thick_compat hL hR hG hG' hj hE hw ψ.hom hψK
  obtain ⟨wL, hwL, H⟩ := _root_.GlobalTheory.exists_bundleIso_extending_generic_normal R hR D D' A A' G G' hG hG' U U' hD j hj Φ w hw ψ hψm hψK hth
  have hs := Geo.Tor.specOf_id R
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso ((isGrpPullback_of_iso ψ).congr hs.symm rfl)
    (isGrpPullback_pullback G (specOf (RingHom.id R)))
  have hbc' : bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = ψ.hom.left := hbc
  have he₀ : eSec G' ≫ ψ.hom.left = eSec G := congrArg Over.Hom.left hψm.one_hom
  have he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) =
      specOf (RingHom.id R) ≫ eSec G :=
    (congrArg (_ ≫ ·) hbc').trans (he₀.trans ((congrArg (· ≫ _) hs).trans (Category.id_comp _)).symm)
  have hr := GlobalTheory.pmaps_rig_of_thick_compat hI U.toUnifPre U'.toUnifPre hD (fun e => (j e).hom) (fun e => (hj e).1)
    he₀ wL hwL H
  have hP : IsPullUnif (RingHom.id R) hD bc U U' := (isPullUnif_iff_stalks R R _ _ _ D D' hD A A' G G' bc U U').2
    ⟨pullCongr hbc'.symm wL, (isGen_iff _).2 (pgen_pullCongr _ ((isGen_iff _).1 hwL)), he, ?_, fun e =>
      ⟨(j e).hom.left, (hth e).symm.trans (congrArg (_ ≫ ·) hbc'.symm), (hj e).2.2,
        fun Z r z jM jM' jL jL' h₁ h₂ h₃ h₄ => ?_⟩⟩
  · obtain ⟨φ, h1, h2, h3⟩ := GlobalTheory.UT.exists_genericFibre_iso_of_model_iso R _ D D' A A' G G' U.toUnifPre
      U'.toUnifPre ψ hψm ⟨wL, hwL⟩
    exact ⟨ψ, bc, φ, hψm, mbc, hbc', hP, h1, h2, h3⟩
  · exact (Geo.Tor.maps_iff _ _ (fun _ => eSec G) _ U'.LG.rig U.LG.rig (specOf (RingHom.id R)) _
      (rigPull_le _ _ he U.LG.L) (fun _ => rfl)).2 (pmaps_pullCongr _
        ((congrArg (PMaps wL (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) U'.LG.rig U.LG.rig)
          hs).mpr hr))
  · rw [gw_pullCongr]
    refine H e Z r z jM jM' jL jL' h₁ h₂ ?_ h₄
    rw [hbc'] at h₃
    exact (congrArg (fun g => g (r z) ∈ U.LG.L.U jL) (hth e)).mp h₃
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationRingActionAdjointCubeBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.UnifAdjoint

open GlobalTheory.CechPic GlobalTheory.ZH.EndoExtend

theorem lbIso_cubeLB_star : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (o : D.toPre.OAct O) (oA : A.OAct O) (oG : RingAct G O), U.toUnifPre.OLinear O o oA oG → ∀ a : O, LBIso (cubeLB G ![fst G G ≫ oG.act a, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ oG.act (star a)] U.LG.L) := by
  intro R _ _ _ hR D A G _ _ hG U O _ _ _ o oA oG hlin a
  obtain ⟨hno, -, hic, -⟩ := hR
  have hS : IsSemiAbelian G := hG
  have := hS.smooth
  have := hS.geomConnected
  have := geometricallyIntegral_of_smooth G.hom
  have := smooth_tensorObj_hom G G
  have := geometricallyIntegral_tensorObj_hom G G
  have ha := oG.hom a
  have hsa := oG.hom (star a)
  have hgen := U.gen_hom
  have hL := U.LG.isLB
  have hA := A.isLB
  have h₁ : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have h₂ : Flat (jK R) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  have h₃ : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have hn : Geo.Tor.IsNormalScheme (Sp R) := (GlobalTheory.isNormalScheme_iff_pred _).1 inferInstance
  have h0 : CechPic.pull (eSec G) (cls U.LG.L hL) = 0 :=
    (cls_eq_zero_iff (pull_isLB hL _)).2 ⟨U.LG.rig, U.LG.rigGen⟩

  have eA : cubeCls A.A ![fst A.A A.A ≫ oA.act a, snd A.A A.A] (cls A.L hA) =
      cubeCls A.A ![fst A.A A.A, snd A.A A.A ≫ oA.act (star a)] (cls A.L hA) :=
    (cls_cubeLB A.A _ hA).symm.trans (((cls_eq_iff (LB.isLB_linComb hA _ _) (LB.isLB_linComb hA _ _)).2
      (GlobalTheory.FullPoint.lbIso_of_rosatiAdj hA (oA.rosati a))).trans (cls_cubeLB A.A _ hA))
  have hc' : CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L hL) =
      CechPic.pull U.gen.hom.left (cls A.L hA) := by
    obtain ⟨w, hw⟩ := U.ext
    rw [← cls_pull hL _ (pull_isLB hL _), ← cls_pull hA _ (pull_isLB hA _)]
    exact ((cls_eq_iff _ _).2 ⟨w, hw⟩).symm

  have hgK : cubeCls ((Over.pullback (jK R)).obj G)
        ![fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ (Over.pullback (jK R)).map (oG.act a),
          snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)]
        (CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L hL)) =
      cubeCls ((Over.pullback (jK R)).obj G)
        ![fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G),
          snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ (Over.pullback (jK R)).map (oG.act (star a))]
        (CechPic.pull (pullback.fst G.hom (jK R)) (cls U.LG.L hL)) := by
    rw [hc']
    let u := lift (fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ U.gen.hom)
      (snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G) ≫ U.gen.hom)
    have hu : u.left ≫ (A.A ⊗ A.A).hom = ((Over.pullback (jK R)).obj G ⊗ (Over.pullback (jK R)).obj G).hom ≫ 𝟙 _ := by
      rw [Category.comp_id]; exact Over.w u
    have e₁ := hlin.ext a
    have e₂ := hlin.ext (star a)
    rw [← push_cubeCls (isGrpPullback_of_iso U.gen) _ ![fst A.A A.A ≫ oA.act a, snd A.A A.A] u.left hu (fun i => ?_),
      ← push_cubeCls (isGrpPullback_of_iso U.gen) _ ![fst A.A A.A, snd A.A A.A ≫ oA.act (star a)] u.left hu
        (fun i => ?_), eA]
    · fin_cases i
      · show (fst _ _ ≫ U.gen.hom).left = (u ≫ fst A.A A.A).left
        congr 1; simp [u]
      · show ((snd _ _ ≫ (Over.pullback (jK R)).map (oG.act (star a))) ≫ U.gen.hom).left = (u ≫ snd A.A A.A ≫ oA.act (star a)).left
        congr 1; simp [u, e₂]
    · fin_cases i
      · show ((fst _ _ ≫ (Over.pullback (jK R)).map (oG.act a)) ≫ U.gen.hom).left = (u ≫ fst A.A A.A ≫ oA.act a).left
        congr 1; simp [u, e₁]
      · show (snd _ _ ≫ U.gen.hom).left = (u ≫ snd A.A A.A).left
        congr 1; simp [u]
  refine (cls_eq_iff (LB.isLB_linComb hL _ _) (LB.isLB_linComb hL _ _)).1
    ((cls_cubeLB G _ hL).trans (Eq.trans ?_ (cls_cubeLB G _ hL).symm))
  refine pic_ext (jK R) hn (G ⊗ G) (lift η[G] η[G]).left (Over.w _) ?_ ?_
  · refine (pull_cubeCls G _ (fun _ => η[G]) (lift η[G] η[G]) (fun i => ?_) _).trans
      (pull_cubeCls G _ (fun _ => η[G]) (lift η[G] η[G]) (fun i => ?_) _).symm <;>
    fin_cases i <;> simp
  · have hGp := isGrpPullback_pullback G (jK R)
    have Aw : ∀ {Y Z : Over (Sp R)} (q : Y ⟶ Z),
        ((Over.pullback (jK R)).map q).left ≫ pullback.fst Z.hom (jK R) = pullback.fst Y.hom (jK R) ≫ q.left :=
      fun q => pullback.lift_fst _ _ _
    let δ := lift ((Over.pullback (jK R)).map (fst G G)) ((Over.pullback (jK R)).map (snd G G))
    have e := congrArg (CechPic.pull δ.left) hgK
    have e' := fun x : Fin 2 → (G ⊗ G ⟶ G) => push_cubeCls hGp (T' := (Over.pullback (jK R)).obj (G ⊗ G)) (T := G ⊗ G)
      (fun i => (Over.pullback (jK R)).map (x i)) x (pullback.fst (G ⊗ G).hom (jK R)) pullback.condition
      (fun i => Aw _) (cls U.LG.L hL)
    rw [pull_cubeCls _ _ (fun i => (Over.pullback (jK R)).map (![fst G G ≫ oG.act a, snd G G] i)) δ
        (fun i => by fin_cases i <;> simp [δ]),
      pull_cubeCls _ _ (fun i => (Over.pullback (jK R)).map (![fst G G, snd G G ≫ oG.act (star a)] i)) δ
        (fun i => by fin_cases i <;> simp [δ])] at e
    exact (e' _).trans (e.trans (e' _).symm)

end GlobalTheory.Mum.UnifAdjoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationTransferIsPullDegId
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.UnifMove

theorem g_eq_of_isPullDeg_id {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R}
    (hD : IsPullDeg (RingHom.id R) D D') : D'.P.g = D.P.g :=
  H1.dim_unique _ D'.P.smoothDim
    ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (pull_grp hD).1 D.P.smoothDim)
    (eSec D'.P.A (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R))

theorem nonempty_isPullDeg_id_symm {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R}
    (hD : IsPullDeg (RingHom.id R) D D') : Nonempty (IsPullDeg (RingHom.id R) D' D) :=
  _root_.GlobalTheory.PullDegSymm.isPullDeg_symm R D D' hD

theorem exists_unif_of_isPullDeg_id {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (hR : AdmBase R I)
    {D D' : DegData R I} (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) {A : PolAV (Sp (FractionRing R))}
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (hsa : IsSemiAbelian G) (U : Unif I D A G) :
    ∃ U' : Unif I D' A G, U'.LG = U.LG ∧ U'.gen = U.gen := by
  have hs := specOf_id R
  let ε : G ≅ G := Iso.refl G
  haveI hε : IsMonHom ε.hom := show IsMonHom (𝟙 G) from inferInstance
  have gp₁ : IsGrpPullback G G (specOf (RingHom.id R)) ε.hom.left :=
    (isGrpPullback_of_iso ε).congr hs.symm rfl
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso gp₁ (isGrpPullback_pullback G (specOf (RingHom.id R)))
  have := U.gen_hom
  let eA : (Over.pullback (jK R)).obj G ≅ A.A := (Over.pullback (jK R)).mapIso ε ≪≫ U.gen
  have mE : IsMonHom eA.hom := by
    show IsMonHom ((Over.pullback (jK R)).map (𝟙 G) ≫ U.gen.hom)
    rw [CategoryTheory.Functor.map_id, Category.id_comp]
    infer_instance
  have wA : LBIso (A.L.pull eA.hom.left) (U.LG.L.pull (pullback.fst G.hom (jK R) ≫ bc.hom.left ≫
      pullback.fst G.hom (specOf (RingHom.id R)))) :=
    LBIso.chartPull (h := ((Over.pullback (jK R)).map ε.hom).left)
      (chartPullSame A.L (fun _ => eA.hom.left) (fun _ => U.gen.hom.left) _ _ fun _ => rfl)
      (chartPullSame U.LG.L _ (fun _ => pullback.fst G.hom (jK R)) _ _ fun _ => by
        rw [hbc]; exact (pullback.lift_fst _ _ _).symm) U.ext
  obtain ⟨wL, he, gL, rL⟩ := (GlobalTheory.TorsionFormCompare.rigAlong_id U.LG).read (ε := 𝟙 G) hbc hs
  obtain ⟨U', hL, hgen, -⟩ := GlobalTheory.TorsionFormCompare.exists_unif_pull_of_deg
    GlobalTheory.abelianSchemeLaws_all.1.polBaseChange GlobalTheory.abelianSchemeLaws_all.1.globalFns
    GlobalTheory.abelianSchemeLaws_all.1.secBaseChange GlobalTheory.twistBaseChange
    R R I I hR hR (RingHom.id R) (by rw [Ideal.map_id]) D A G hsa U D' hD (g_eq_of_isPullDeg_id hD) G bc mbc A rfl
    eA mE wA U.LG wL he gL rL
  refine ⟨U', hL, ?_⟩
  rw [hgen]
  ext : 1
  simp [eA, ε]

theorem unif_move : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I),
    Nonempty (IsPullDeg (RingHom.id R) D.toPre D'.toPre) → ∀ (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R))
    [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    (∀ U' : Unif I D' A G, ∃ U : Unif I D A G, U.LG = U'.LG ∧ U.gen = U'.gen) ∧
      ∀ U : Unif I D A G, ∃ U' : Unif I D' A G, U'.LG = U.LG ∧ U'.gen = U.gen := by
  intro R _ _ I hR D D' ⟨hD⟩ A G _ _ hsa
  obtain ⟨hD'⟩ := nonempty_isPullDeg_id_symm hD
  exact ⟨fun U' => exists_unif_of_isPullDeg_id hR hD' hsa U', fun U => exists_unif_of_isPullDeg_id hR hD hsa U⟩

end GlobalTheory.Mum.UnifMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformiserZpowMulUnitExponentUnique
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory

theorem exponent_uniformiser_unique {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {ϖ : V} (hϖ : Irreducible ϖ) (a b : ℤ) (w w' : Vˣ)
    (h : algebraMap V (FractionRing V) ϖ ^ a * algebraMap V (FractionRing V) (w : V) =
      algebraMap V (FractionRing V) ϖ ^ b * algebraMap V (FractionRing V) (w' : V)) : a = b := by
  have hinj : Function.Injective (algebraMap V (FractionRing V)) :=
    IsFractionRing.injective V (FractionRing V)
  have hx : algebraMap V (FractionRing V) ϖ ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]; exact hϖ.ne_zero
  have hw : algebraMap V (FractionRing V) (w : V) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]; exact w.ne_zero
  have key : ∀ (n : ℕ) (u : Vˣ), algebraMap V (FractionRing V) ϖ ^ n =
      algebraMap V (FractionRing V) (u : V) → n = 0 := by
    intro n u hn
    rw [← map_pow] at hn
    have h1 := hinj hn
    by_contra hne
    apply hϖ.not_isUnit
    rw [← isUnit_pow_iff hne, h1]; exact u.isUnit
  have hab : algebraMap V (FractionRing V) ϖ ^ (a - b) =
      algebraMap V (FractionRing V) ((w' * w⁻¹ : Vˣ) : V) := by
    rw [zpow_sub₀ hx, Units.val_mul, map_mul, map_units_inv, div_eq_iff (zpow_ne_zero _ hx)]
    field_simp
    linear_combination h
  rcases Int.eq_nat_or_neg (a - b) with ⟨n, hn | hn⟩
  · rw [hn, zpow_natCast] at hab
    have := key n _ hab
    omega
  · rw [hn, zpow_neg, zpow_natCast] at hab
    have h2 : algebraMap V (FractionRing V) ϖ ^ n =
        algebraMap V (FractionRing V) (((w' * w⁻¹)⁻¹ : Vˣ) : V) := by
      rw [map_units_inv, ← hab, inv_inv]
    have := key n _ h2
    omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitCocycleDescendsOnTripleOverlapsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LBDescent
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_cocycle_descends_on_triple_overlaps : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f] (V V₀ : Y.Opens), IsAffineOpen V₀ →
    ∀ (h : pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ ≤ pullback.snd f f ⁻¹ᵁ f ⁻¹ᵁ V₀)
      (hle : pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀ ≤ pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V) (c : Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V)ˣ),
    (∀ w : ↥(Triple f), f (pullback.fst f f (pullback.fst (pullback.snd f f) (pullback.fst f f) w)) ∈ V →
        gm (pullback.fst (pullback.snd f f) (pullback.fst f f)) w _ c *
          gm (pullback.snd (pullback.snd f f) (pullback.fst f f)) w _ c = gm (pr13 f) w _ c) →
    letI : Algebra Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀) := (f.app V₀).hom.toAlgebra
    ∀ e : Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀) ≃+* Γ(pullback f f, pullback.fst f f ⁻¹ᵁ f ⁻¹ᵁ V₀),
      (∀ a b : Γ(X, f ⁻¹ᵁ V₀), e (a ⊗ₜ b) =
        ((pullback.fst f f).app (f ⁻¹ᵁ V₀)).hom a * ((pullback.snd f f).appLE (f ⁻¹ᵁ V₀) _ h).hom b) →
      Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀) ⊗[Γ(Y, V₀)] Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀)) (e.symm (res hle c).val) *
          Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀)) (e.symm (res hle c).val) =
        Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (R := Γ(Y, V₀)) (S := Γ(Y, V₀)) (A := Γ(X, f ⁻¹ᵁ V₀)) (B := Γ(X, f ⁻¹ᵁ V₀))) (AlgHom.id Γ(Y, V₀) Γ(X, f ⁻¹ᵁ V₀)) (e.symm (res hle c).val) := by
  first | exact @GlobalTheory.LBDescent.CocycleTensor.cocycle_tensor_of_pointwise | exact GlobalTheory.LBDescent.CocycleTensor.cocycle_tensor_of_pointwise | (intros; apply GlobalTheory.LBDescent.CocycleTensor.cocycle_tensor_of_pointwise <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitCocycleLiftObstructionPullbackNaturality
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.LBObs

theorem isObU_pull : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R₀) (L : Pre I π F) (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) F F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T) (u : ∀ (T T' : C) (_ : T ⟶ T'), (F.obj T')ˣ) (u' : ∀ (T T' : C') (_ : T ⟶ T'), (F'.obj T')ˣ) (c : GlobalTheory.CatCoh.H2 (ext R₁ F)), L.IsLift L' n l → L.IsNat L' n l → (∀ T T' a, (u' T T' a : F'.obj T') = n.α T' (u _ _ (n.G.map a) : F.obj (n.G.obj T'))) → IsObU L α u c → IsObU L' α u' ((extMap R₁ n).pull2 c) := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α C _ F L C' _ F' L' n l u u' c hL hN hu hob
  obtain ⟨v, σ, z, hv, hσ, hc, hz⟩ := hob
  have hex : ∀ T, ∃ s : R₁ ⊗[R₀] F'.obj T →+ L'.B T, α.IsSig (L'.p T) s := fun T =>
    GlobalTheory.Obs.exists_isSig R R₀ I hI π hπ hk R₁ α (L'.B T) (F'.obj T) (L'.p T) (L'.semi T) (L'.surj T) (L'.ker T)
  choose σ' hσ' using hex
  have hnat : ∀ T : C', (∀ y, l T (σ (n.G.obj T) y) = σ' T (extHom R₁ (coefHom n T) y)) ∧
      ∀ y, α.KerQ y → α.KerQ (extHom R₁ (coefHom n T) y) := fun T =>
    GlobalTheory.Obs.sig_natural R R₀ I hI π hπ hk R₁ α _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _)
      _ _ (L'.p T) (L'.semi T) (L'.surj T) (L'.ker T) (l T) (coefHom n T) (fun b => hL T b) _ _ (hσ _) (hσ' T)
  refine ⟨fun T T' a => Units.map (l T').toRingHom.toMonoidHom (v _ _ (n.G.map a)), σ', (extMap R₁ n).pullbackTwoCocycle z,
    ?_, hσ', ?_, ?_⟩
  · intro T T' a
    change L'.p T' (l T' _) = _
    rw [hL, hv, hu]
  · rw [hc]; rfl
  · intro T T' T'' a b
    obtain ⟨hk1, hk2⟩ := hz _ _ _ (n.G.map a) (n.G.map b)
    refine ⟨(hnat T'').2 _ hk1, ?_⟩
    change L'.ρ b (l T' _) * l T'' _ = (1 + σ' T'' (extHom R₁ (coefHom n T'') _)) * l T'' _
    rw [hN, ← map_mul, hk2, map_mul, map_add (f := _), map_one, (hnat T'').1, Functor.map_comp]
    rfl

end GlobalTheory.LBObs
end

