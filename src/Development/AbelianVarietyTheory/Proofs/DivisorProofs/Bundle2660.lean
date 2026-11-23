module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0660
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0583
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0121
public import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.MapPowLeOfIsPullUnif
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Laws5
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0115
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationDegenerationDataUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0578
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2268
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2580
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2555
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2548
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2605
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2539
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2489
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2452
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2517
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2473
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2594
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2610
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2540
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2621
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2579
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2613

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastMore
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.TwoUnifTors


set_option maxHeartbeats 1600000 in
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorRef in
theorem main : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (A : PolAV (Sp (FractionRing V))) (G G' : Over (Sp V)) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (D D' : DegData V (maximalIdeal V)) (U : Unif (maximalIdeal V) D A G) (U' : Unif (maximalIdeal V) D' A G'), ∃ ε : D.toPre.X ≃+ D'.toPre.X, (∀ y r r', PsiCoord D.toPre y r → PsiCoord D'.toPre (ε y) r' → Associated r r') ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing V) K] (k : ℕ) (q : QkPt D.toPre K k) (q' : QkPt D'.toPre K k) (x : TFK (R := V) K ⟶ A.A), 1 ≤ k → QkToAkU U.toUnifPre K k q x → QkToAkU U'.toUnifPre K k q' x → CongMod k q'.y (ε q.y) := by
  intro V _ _ _ _ hc A G G' _ _ _ _ hG hG' D D' U U'
  have hCN : IsCN V := ⟨inferInstance, inferInstance, hc, inferInstance⟩
  have aV := admissibleBase_of_completeNormalLocalCharZero hCN

  have hext := GlobalTheory.homExtDvr_and_laws.1
  have m₁ : IsMonHom (U.gen.hom ≫ U'.gen.inv) := by
    haveI := U.gen_hom; haveI := U'.gen_hom; infer_instance
  have m₂ : IsMonHom (U'.gen.hom ≫ U.gen.inv) := by
    haveI := U.gen_hom; haveI := U'.gen_hom; infer_instance
  obtain ⟨f, ⟨hfm, hfK⟩, -⟩ := hext V G G' hG hG' (U.gen.hom ≫ U'.gen.inv) m₁
  obtain ⟨g, ⟨hgm, hgK⟩, -⟩ := hext V G' G hG' hG (U'.gen.hom ≫ U.gen.inv) m₂
  have fg : f ≫ g = 𝟙 G := by
    have u := hext V G G hG hG (𝟙 _) inferInstance
    refine u.unique ⟨inferInstance, ?_⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩
    rw [Functor.map_comp, hfK, hgK]; simp
  have gf : g ≫ f = 𝟙 G' := by
    have u := hext V G' G' hG' hG' (𝟙 _) inferInstance
    refine u.unique ⟨inferInstance, ?_⟩ ⟨inferInstance, CategoryTheory.Functor.map_id _ _⟩
    rw [Functor.map_comp, hfK, hgK]; simp
  let ψ : G ≅ G' := ⟨f, g, fg, gf⟩
  haveI : IsMonHom ψ.hom := hfm
  have hψK : (Over.pullback (jK V)).map ψ.hom ≫ U'.gen.hom = U.gen.hom := by
    change (Over.pullback (jK V)).map f ≫ U'.gen.hom = U.gen.hom
    rw [hfK]; simp

  have hid : spMap (RingHom.id V) = 𝟙 (Sp V) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.specOf_id V
  have hpb : IsGrpPullback G G' (spMap (RingHom.id V)) ψ.hom.left := by
    rw [hid]; exact isGrpPullback_of_iso ψ
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso hpb (isGrpPullback_pullback G' (spMap (RingHom.id V)))
  have he : eSec G ≫ bc.hom.left ≫ pullback.fst G'.hom (spMap (RingHom.id V)) =
      spMap (RingHom.id V) ≫ eSec G' := by
    rw [hbc]; exact GlobalTheory.PolBaseChange.eSec_comm hpb
  let L' : RigLB G := ⟨U'.LG.L.pull (bc.hom.left ≫ pullback.fst G'.hom (spMap (RingHom.id V))),
    rigPullOf (G' := G) (G := G') (bc.hom.left ≫ pullback.fst G'.hom (spMap (RingHom.id V))) (spMap (RingHom.id V))
      he U'.LG.L U'.LG.rig, pull_isLB U'.LG.isLB _,
    GlobalTheory.Proof.TautologicalModel.rigPullOf_isGen (G' := G) (G := G') (bc.hom.left ≫ pullback.fst G'.hom (spMap (RingHom.id V)))
      (spMap (RingHom.id V)) he U'.LG.L U'.LG.rig U'.LG.rigGen⟩
  obtain ⟨wL, gL, rL⟩ := GlobalTheory.Unif.RigidifyIso.exists_rigidified_iso _ _ (spMap (RingHom.id V)) G' G _ he U'.LG L'
    (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB U'.LG.isLB _))

  have wA : LBIso (A.L.pull U.gen.hom.left)
      (U'.LG.L.pull (pullback.fst G.hom (jK V) ≫ bc.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id V)))) := by
    have k₁ : pullback.fst G.hom (jK V) ≫ bc.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id V)) =
        ((Over.pullback (jK V)).map ψ.hom).left ≫ pullback.fst G'.hom (jK V) := by
      rw [hbc]; exact (pullback.lift_fst _ _ _).symm
    have k₂ : U.gen.hom.left = ((Over.pullback (jK V)).map ψ.hom).left ≫ U'.gen.hom.left := by
      rw [← Over.comp_left, hψK]
    rw [k₁, k₂]
    have t₁ : LBIso (A.L.pull (((Over.pullback (jK V)).map ψ.hom).left ≫ U'.gen.hom.left))
        ((A.L.pull U'.gen.hom.left).pull ((Over.pullback (jK V)).map ψ.hom).left) :=
      LBIso.symm ⟨GlobalTheory.Proof.TautologicalModel.taut _ _ _, GlobalTheory.Proof.TautologicalModel.taut_isGen A.isLB _ _⟩
    have t₂ : LBIso ((A.L.pull U'.gen.hom.left).pull ((Over.pullback (jK V)).map ψ.hom).left)
        ((U'.LG.L.pull (pullback.fst G'.hom (jK V))).pull ((Over.pullback (jK V)).map ψ.hom).left) :=
      GlobalTheory.RigidBundleGlue.LBIso.pull U'.ext _
    have t₃ : LBIso ((U'.LG.L.pull (pullback.fst G'.hom (jK V))).pull ((Over.pullback (jK V)).map ψ.hom).left)
        (U'.LG.L.pull (((Over.pullback (jK V)).map ψ.hom).left ≫ pullback.fst G'.hom (jK V))) :=
      ⟨GlobalTheory.Proof.TautologicalModel.taut _ _ _, GlobalTheory.Proof.TautologicalModel.taut_isGen U'.LG.isLB _ _⟩
    exact (t₁.trans (pull_isLB A.isLB _) (pull_isLB (pull_isLB A.isLB _) _)
      (pull_isLB (pull_isLB U'.LG.isLB _) _) t₂).trans (pull_isLB A.isLB _)
      (pull_isLB (pull_isLB U'.LG.isLB _) _) (pull_isLB U'.LG.isLB _) t₃

  obtain ⟨W, hW, hWψ⟩ := GlobalTheory.psiOnExists V (maximalIdeal V) aV D'
  have hWg : (specOf (RingHom.id V)).base (genericPoint (Spec (CommRingCat.of V))) ∈ W := by
    rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.specOf_id]; exact hW
  have hI : (maximalIdeal V).map (RingHom.id V) ≤ maximalIdeal V := by rw [Ideal.map_id]
  obtain ⟨D'', hD, U'', -, hgen, hPU⟩ := GlobalTheory.UnifPullGuards.unifBaseChange_holds V V _ _ aV aV (RingHom.id V) hI D' A G'
    hG' U' W hWψ hWg G bc mbc A rfl U.gen U.gen_hom wA L' wL he gL rL

  have h5 : Laws5 := GlobalTheory.allSixLaws.2.2.2.2.1
  have hUq : UnifUniqSt := GlobalTheory.allSixLaws.2.2.2.2.2.unifUniq
  have hQ : QkPullExistsSt := qkPullExists GlobalTheory.allSixLaws.1.globalFns

  have hLG : LBIso U''.LG.L U.LG.L := by
    refine GlobalTheory.FewAtTest.lbIso_of_generic hG U''.LG U.LG ?_
    have e1 := U''.ext
    rw [hgen] at e1
    exact LBIso.trans (pull_isLB U''.LG.isLB _) (pull_isLB A.isLB _) (pull_isLB U.LG.isLB _) (LBIso.symm e1) U.ext
  obtain ⟨wL₀, hwg₀, hwm₀⟩ := GlobalTheory.RigLBIso.exists_rig_iso_of_iso _ G U''.LG U.LG hLG
  obtain ⟨hD₀, hlev₀, -⟩ := hUq V (maximalIdeal V) aV D D'' A A G hG U U'' wL₀ hwg₀ hwm₀
  have hpb₀ : IsGrpPullback G G (spMap (RingHom.id V)) (Iso.refl G).hom.left := by
    haveI : IsMonHom (Iso.refl G).hom := by show IsMonHom (𝟙 G); infer_instance
    rw [hid]; exact isGrpPullback_of_iso (Iso.refl G)
  obtain ⟨bc₀, mbc₀, hbc₀⟩ := grpPullback_iso hpb₀ (isGrpPullback_pullback G (spMap (RingHom.id V)))
  have hbc₀' : bc₀.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id V)) = 𝟙 _ := hbc₀
  have hPU₀ : IsPullUnif (RingHom.id V) hD₀ bc₀ U U'' :=
    isPullUnif_of_uniq U U'' hD₀ wL₀ hwg₀ hwm₀ hlev₀ bc₀ hbc₀'
  have hbc' : bc.hom.left ≫ pullback.fst G'.hom (specOf (RingHom.id V)) = ψ.hom.left := hbc

  have k₁ : U.gen.inv ≫ (Over.pullback (jK V)).map ψ.hom = U'.gen.inv := by
    rw [Iso.inv_comp_eq, ← hψK, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have k₂ : ((Over.pullback (jK V)).map ψ.hom).left ≫ pullback.fst G'.hom (jK V) =
      pullback.fst G.hom (jK V) ≫ ψ.hom.left := pullback.lift_fst _ _ _
  refine ⟨hD₀.xe.symm.trans hD.xe, fun y r r' hr hr' => ?_, ?_⟩
  · obtain ⟨u, hu⟩ := GlobalTheory.SameCoord.psiCoord_of_isPullDeg_id hD₀ (hD₀.xe.symm y) r
      (by rw [AddEquiv.apply_symm_apply]; exact hr)
    obtain ⟨u', hu'⟩ := GlobalTheory.SameCoord.psiCoord_of_isPullDeg_id hD (hD₀.xe.symm y) r' hr'
    have h1 : Associated (u * r) (u' * r') := GlobalTheory.TorRef.psiCoord_associated hu hu'
    exact ((associated_unit_mul_left r u u.isUnit).symm.trans h1).trans (associated_unit_mul_left r' u' u'.isUnit)
  · intro K _ _ _ k q q' x hk hq hq'
    obtain ⟨f, hf, -, hinj, -, -⟩ := GlobalTheory.ZH.uTors_closed V hc A G D U K k hk
    obtain ⟨f', hf', -, hinj', -, -⟩ := GlobalTheory.ZH.uTors_closed V hc A G' D' U' K k hk
    obtain ⟨f'', hf'', hsurj'', -, -, -⟩ := GlobalTheory.ZH.uTors_closed V hc A G D'' U'' K k hk
    obtain ⟨w, hw⟩ := U.ext
    have hxk := (hq w hw).1
    obtain ⟨q'', hq''⟩ := hsurj'' x hxk
    have hF : ∀ r : V, algebraMap (FractionRing V) K (algebraMap V (FractionRing V) r) =
        algebraMap (FractionRing V) K (algebraMap V (FractionRing V) ((RingHom.id V) r)) := fun _ => rfl

    obtain ⟨p, hp₁, hp₂⟩ := hQ V V (RingHom.id V) D.toPre D''.toPre hD₀ K hF k q''
    have A₁ : QkToAkU U''.toUnifPre K k q'' (f p) :=
      h5.qkBaseChange V V _ _ aV aV (RingHom.id V) D A G U G bc₀ mbc₀ A D'' hD₀ U'' hPU₀ K hF k hk p (f p) q''
        (f p) hp₁ hp₂ (by rw [hbc₀', Category.comp_id, hgen]) ((hf p (f p)).2 rfl)
    have hpx : f p = x := ((hf'' q'' (f p)).1 A₁).trans hq''
    obtain ⟨z, hz, -⟩ := (hinj p q).1 (hpx.trans ((hf q x).1 hq))

    obtain ⟨p', hp₁', hp₂'⟩ := hQ V V (RingHom.id V) D'.toPre D''.toPre hD K hF k q''
    have B₁ : QkToAkU U''.toUnifPre K k q'' (f' p') :=
      h5.qkBaseChange V V _ _ aV aV (RingHom.id V) D' A G' U' G bc mbc A D'' hD U'' hPU K hF k hk p' (f' p') q''
        (f' p') hp₁' hp₂' (by rw [hgen, hbc', ← k₂, ← k₁, Over.comp_left]; simp only [Category.assoc])
        ((hf' p' (f' p')).2 rfl)
    have hpx' : f' p' = x := ((hf'' q'' (f' p')).1 B₁).trans hq''
    obtain ⟨z', hz', -⟩ := (hinj' p' q').1 (hpx'.trans ((hf' q' x).1 hq'))
    refine ⟨z' - hD.xe (hD₀.xe.symm z), ?_⟩
    show q'.y = hD.xe (hD₀.xe.symm q.y) + k • (z' - hD.xe (hD₀.xe.symm z))
    rw [hz', hz]
    simp only [map_add (f := _), map_nsmul]
    rw [← hp₁, hp₁', AddEquiv.apply_symm_apply, smul_sub]
    abel

end GlobalTheory.TwoUnifTors
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveHeightFormulaRhsTransportIso
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.MixHt
open GlobalTheory.TrueGeo.SmallSec GlobalTheory.FrameGlue.Pull GlobalTheory.MultPull GlobalTheory.Points

variable {k : Type} [CommRing k]

theorem isEmpty_cxPts_of_map {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} (g : Y ⟶ X) (hg : g ≫ p = q)
    (h : ∀ σ : k →+* ℂ, IsEmpty (CxPts p σ)) (σ : k →+* ℂ) : IsEmpty (CxPts q σ) :=

  isEmpty_iff.2 fun y => isEmpty_iff.1 (h σ) (PtsOver.map g hg (spMap σ) y)

theorem mixArch_pull_iso {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k)
    (hp : IsAmb p) (hq : IsAmb q) (g : Y ⟶ X) (hg : g ≫ p = q) (hη : g (genericPoint Y) = genericPoint X) [IsIso g]
    (e : ℕ) (hX : topologicalKrullDim X = (e + 1 : ℕ)) (L : Fin e → HermLB p) (M : HermLB p)
    (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r) :
    mixArch (fun a => (L a).pull g hg) (M.pull g hg)
      (MultPull.isRatSec_pull_map g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr) =
      mixArch L M hr := by
  have hY : topologicalKrullDim Y = (e + 1 : ℕ) :=
    (IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso (asIso g)).isHomeomorph).trans hX
  have hg' : inv g ≫ q = p := by rw [← hg, IsIso.inv_hom_id_assoc]
  by_cases hp0 : ∀ σ : k →+* ℂ, IsEmpty (CxPts p σ)
  · rw [(_root_.GlobalTheory.MixHt.mixArch_resArch_eq_zero_of_noCxPts k X p hp0 e L M).1 r hr]
    exact (_root_.GlobalTheory.MixHt.mixArch_resArch_eq_zero_of_noCxPts k Y q (isEmpty_cxPts_of_map g hg hp0) e _ _).1 _ _
  by_cases hq0 : ∀ σ : k →+* ℂ, IsEmpty (CxPts q σ)
  · exact absurd (isEmpty_cxPts_of_map (inv g) hg' hq0) hp0
  obtain ⟨e₁, he₁, hXa⟩ := (_root_.GlobalTheory.MixHt.amb_vertical_or_arithVar k X p hp (e + 1) hX).resolve_left fun ⟨_, _, _, h⟩ => hp0 h
  obtain ⟨e₂, he₂, hYa⟩ := (_root_.GlobalTheory.MixHt.amb_vertical_or_arithVar k Y q hq (e + 1) hY).resolve_left fun ⟨_, _, _, h⟩ => hq0 h
  obtain rfl : e₁ = e := by omega
  obtain rfl : e₂ = e₁ := by omega
  unfold mixArch
  congr 2
  funext n
  have h₁ : (comb (fun a => (L a).pull g hg) n).archInt (M.pull g hg) e₂
      (MultPull.isRatSec_pull_map g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr) =
      ((comb L n).pull g hg).archInt (M.pull g hg) e₂
      (MultPull.isRatSec_pull_map g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr) := by
    simp only [HermLB.archInt, (isometric_comb_pull L n g hg).chernInt_eq]
  rw [h₁, _root_.GlobalTheory.ArchPull.archInt_pull k X Y p q e₂ hXa hYa g hg hη (by rw [Published.residueDegree_of_isClosedImmersion]; exact one_ne_zero),
    Published.residueDegree_of_isClosedImmersion, Nat.cast_one, one_mul]

theorem mult_pull_iso {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    {p : X ⟶ Sp k} {q : Y ⟶ Sp k} (g : Y ⟶ X) (hg : g ≫ p = q) (hη : g (genericPoint Y) ⤳ genericPoint X) [IsIso g]
    (M : HermLB p) {r : M.B.ι → X.functionFieldˣ} (hr : IsRatSec M.B r) (y : Y) :
    ((M.pull g hg).div (MultPull.isRatSec_pull_map g hη hr)).mult y = (M.div hr).mult (g y) := by
  change (divOfRatSec (LB.isLB_pull M.isLB g) (MultPull.isRatSec_pull_map g hη hr)).mult y =
    (divOfRatSec M.isLB hr).mult (g y)
  obtain ⟨c, hc⟩ := exists_chart (LB.isLB_pull M.isLB g) y
  have hc' : g y ∈ M.B.U (c PUnit.unit) := Set.mem_iInter.1 hc PUnit.unit
  rw [((presents_divOfRatSec _ _).isEqn c y hc).mult_eq,
    ((presents_divOfRatSec M.isLB hr).isEqn _ _ hc').mult_eq]
  exact ord_fnMap g hη y _

theorem transport : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsAmb p → IsAmb q → ∀ (g : Y ⟶ X) (hg : g ≫ p = q) (hη : g (genericPoint Y) = genericPoint X), IsIso g → ∀ e : ℕ, topologicalKrullDim X = (e + 1 : ℕ) → ∀ (h : X → ℝ) (L : Fin e → HermLB p) (M : HermLB p) (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), recVal (fun w => h (g w)) (fun a => (L a).pull g hg) (M.pull g hg) (MultPull.isRatSec_pull_map g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr) = recVal h L M hr := by
  intro k _ X Y _ _ _ _ p q hp hq g hg hη _ e hX h L M r hr
  unfold recVal
  rw [mixArch_pull_iso p q hp hq g hg hη e hX L M r hr]
  congr 1
  refine (finsum_congr fun z => ?_).trans
    (finsum_comp_equiv (Scheme.homeoOfIso (asIso g)).toEquiv (f := fun x => ((M.div hr).mult x : ℝ) * h x))
  exact congrArg (fun n : ℤ => (n : ℝ) * h (g z)) (mult_pull_iso g hg _ M hr z)

end GlobalTheory.MixHt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceIntegralUnitaryPointsFixVacuum
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertBridge

theorem fix_vac : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σL : L →+* L) (q : ℕ) (δ : L)
      (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L) (ψL : AddChar L ℂ)
      (κ : Matrix (Fin (a + a')) (Fin a') L →+ Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      GlobalTheory.InertBridge.Chart σ B G v ϖ σL q δ JS JT ψL κ ιS ιT →
    ∀ ω : (Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) × Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →*
        Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v))),
      (∀ g h (m : SB (Fin a' × Fin (a + a') → Fv F v)) (φ₁ : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
        φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v) →
        (Acts (evFin F v) (om' (ιS g, ιT h)) (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) φ₁ ↔
          ((ω (g, h) m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = φ₁)) →
    ∀ s : SB (Fin a' × Fin (a + a') → Fv F v), (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = G.M'.vac v →
    ∀ (g : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L)) (h : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L)),
      (g : GL (Fin a') L) ∈ Formalism.UG.GLint (Fin a') (Formalism.UG.intL L) →
      (h : GL (Fin (a + a')) L) ∈ Formalism.UG.GLint (Fin (a + a')) (Formalism.UG.intL L) → ω (g, h) s = s := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hI hT L _ _ ϖ σL q δ JS JT ψL κ ιS ιT hC ω hω s hs g h hg hh
  obtain ⟨unr, odd, intS, intT, hermS, hermT, hδ, psiInt, psiNe, hAt, hSurj, hLat, hPsi, hEq, hιS, hιT, hKS, hKT⟩ := hC
  have hvac : G.M'.vac v ∈ SB (Fin a' × Fin (a + a') → Fv F v) := hs ▸ s.2
  have h1 : ω (1, h) s = s := by
    have hA : Acts (evFin F v) (om' (ιS 1, ιT h)) (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ) (G.M'.vac v) := by
      rw [map_one, hs]
      exact GlobalTheory.T.inertPlace_latticeStabilizer_fixes_vacuum F E σ B a a' G X om om' hTr v w hI hT (ιT h) (hKT h hh)
    exact Subtype.ext (((hω 1 h s _ hvac).mp hA).trans hs.symm)
  have h2 : ω (g, 1) s = s := by
    have hA : Acts (evFin F v) (om' (ιS g, ιT 1)) (s : (Fin a' × Fin (a + a') → Fv F v) → ℂ) (G.M'.vac v) := by
      rw [map_one, hs]
      exact GlobalTheory.T.inertPlace_stabilizer_fixes_vacuum_left F E σ B a a' G X om om' hTr v w hI hT (ιS g) (hKS g hg)
    exact Subtype.ext (((hω g 1 s _ hvac).mp hA).trans hs.symm)
  have hgh : ((g, h) : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) × Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L)) = (g, 1) * (1, h) := by
    simp
  rw [hgh, map_mul, Module.End.mul_apply, h1, h2]

end GlobalTheory.InertBridge

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRelationUniformisedHomConvolutionExpansi
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange
open GlobalTheory.Mum.Two.Mix

noncomputable section
namespace GlobalTheory.Mum.Two.Mix

theorem core : LL → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), Lin U₁ U₂ a b h → Coord U₁ U₂ a b h → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (j j' : ℕ) (N : Type) [Fintype N] (ρ : N → R) (σ : N → H0 U₂.LG.L j) (σ' : N → H0 U₁.LG.L j') (f : N → ∀ α : D₂.toPre.X, D₂.toPre.SecB j α) (f' : N → ∀ α : D₁.toPre.X, D₁.toPre.SecB j' α), (∀ ν e, U₂.ExpandsAt e j (σ ν) (f ν)) → (∀ ν e, U₁.ExpandsAt e j' (σ' ν) (f' ν)) → (∀ (Z : Scheme.{0}) (r : Z ⟶ G₁.left) (z : Z) (J₁ J₂), Good U₁.LG.L z J₁ → Good U₂.LG.L z J₂ → ∑ ν, constVal (r ≫ G₁.hom) z (ρ ν) * (sval (σ ν) (r ≫ a.left) z J₂ * sval (σ' ν) r z J₁) = 0) → ∀ (g : GtPtF D₁.toPre F) (g' : GtPtF D₂.toPre F), Act D₁.toPre D₂.toPre b h g g' → ∀ (w : Frm D₂.toPre F j g'.b) (w' : Frm D₁.toPre F j' g.b), w.IsGen → w'.IsGen → ∀ (x : N → D₂.toPre.X → F) (x' : N → D₁.toPre.X → F), (∀ ν χ, MixedConv.IsCoefB j g' w χ (f ν χ) (x ν χ)) → (∀ ν χ, MixedConv.IsCoefB j' g w' χ (f' ν χ) (x' ν χ)) → ∀ α : D₁.toPre.X, SumF I F (fun p : {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α} => ∑ ν, algebraMap (FractionRing R) F (algebraMap R (FractionRing R) (ρ ν)) * (x ν p.1.1 * x' ν p.1.2)) 0 := by
  intro hL R _ _ _ I hR D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ a b h hLin hCo F _ _ _ j j' N _ ρ σ σ' f f' hE hE' hrel
    g g' hg w w' hw hw' x x' hx hx' α
  choose u hu using hCo
  choose n hn using fun (ν : N) (α : D₁.toPre.X) (p : {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α}) =>
    _root_.GlobalTheory.Mum.Two.Mix.exists_mix_hom R D₁.toPre D₂.toPre b j j' p.1.1 (h p.1.1) p.1.2 α p.2 (u p.1.1) (hu p.1.1).1.1 (f ν p.1.1) (f' ν p.1.2)
  let m : ∀ α, {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α} →
      SecOver D₁.toPre.P.A.hom (LB.LinComb (JN D₁.toPre D₂.toPre) (mixφ D₁.toPre D₂.toPre b α) (MixedConv.mixε j j')) :=
    fun α p => ∑ ν, ρ ν • (show SecOver D₁.toPre.P.A.hom _ from n ν α p)
  have hm : ∀ α p (Z : Scheme.{0}) (r : Z ⟶ D₁.toPre.P.A.left) (z : Z) (J), Good (JN D₁.toPre D₂.toPre) z J →
      sval (m α p) r z J = ∑ ν, constVal (r ≫ D₁.toPre.P.A.hom) z (ρ ν) *
        (sval (f ν p.1.1) (r ≫ b.left) z (rr J) * sval (f' ν p.1.2) r z (rl J) *
          (val (u p.1.1) r z J * val (MixedConv.cubB D₁.toPre (h p.1.1) p.1.2) r z (rl J)).val) :=
    fun α p Z r z J hJ =>
      (sval_sum' (π := D₁.toPre.P.A.hom) hJ _ _ _).trans (Finset.sum_congr rfl fun ν _ =>
        (sval_smul' (π := D₁.toPre.P.A.hom) hJ _ _ _).trans (congrArg _ (hn ν α p Z r z J hJ)))
  obtain ⟨τ, hτ, hv⟩ := GlobalTheory.T.exists_mixed_bundle_frame_from_part_frames R D₁.toPre D₂.toPre F b α j j' g _ hg.1 w w' hw hw'
  refine GlobalTheory.T.adicSum_sections_pullbacks_value_abelianPart R I hR D₁ F _ (JN D₁.toPre D₂.toPre) (jn_isLB D₁.toPre D₂.toPre) _ (mixφ D₁.toPre D₂.toPre b α)
    (MixedConv.mixε j j') _ (m α) (0 : SecOver D₁.toPre.P.A.hom _) (fun e => ?_) g.b τ hτ _ 0 fun z J hJ => ⟨fun p => ?_, ?_⟩
  · obtain ⟨S, hS⟩ := _root_.GlobalTheory.Mum.Two.Mix.level R I D₁ D₂ A₁ A₂ G₁ G₂ U₁ U₂ a b h hLin.2.2.1 u (fun χ => (hu χ).2) j j' e N ρ σ σ' f f' (fun ν => hE ν e)
      (fun ν => hE' ν e) hrel m hm α
    exact ⟨S, fun Z r z J hJ => ⟨(hS Z r z J hJ).1,
      (sval_zero' (π := D₁.toPre.P.A.hom) hJ _).trans (hS Z r z J hJ).2.symm⟩⟩
  · obtain ⟨⟨χ, δ⟩, hp⟩ := p
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hm _ _ _ _ z J hJ, CoefBasic.cst_eq, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ν _ => ?_
    have c₁ : constVal (g.b.left ≫ D₁.toPre.P.A.hom) z (ρ ν) =
        CoefBasic.cstH z (algebraMap (FractionRing R) F (algebraMap R (FractionRing R) (ρ ν))) := by
      refine Eq.trans ?_ (CoefBasic.cst_eq z _)
      rw [Over.w g.b]
      refine (constVal_specMap (jFK (R := R) F) _ z _).trans ?_
      exact (congrArg (fun q => constVal q z _) (Category.id_comp _).symm).trans (constVal_specMap (𝟙 _) _ z _)
    have e₁ := GlobalTheory.T.mixed_section_value_product_expansion_terms R D₁.toPre D₂.toPre F b h g g' hg j j' w w' χ δ (u χ) (hu χ).1 (f ν χ) (f' ν δ) _ _ (hx ν χ) (hx' ν δ) z J hJ
    have e₂ := hv z J hJ
    dsimp only at hp
    subst hp
    rw [c₁, e₁, e₂, CoefBasic.cst_eq]
    simp only [map_mul]
    ring
  · rw [CoefBasic.cst_eq, map_zero, zero_mul]
    exact sval_zero' (π := D₁.toPre.P.A.hom) hJ _

end GlobalTheory.Mum.Two.Mix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberMultilinearSymm
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AV.AbVar

theorem diffVanish_chiPic_structureModule {K : Type} [Field K] (A : AbVar K) :
    letI := A.algΓ
    DiffVanish (A.dim + 1) (chiPic K (QCoh.structureModule A.X.left)) := by
  letI := A.algΓ
  refine diffVanish_chiPic_of_isProjOver (f := A.X.hom) (fun r => rfl) _
    (GlobalTheory.AV.AbVarProj.strHom_eq_and_isProjOver K A).2 ?_
  refine (QCoh.suppDim_le _).trans ?_
  rw [GlobalTheory.AV.AbVar.topologicalKrullDim_eq_dim K A]

theorem inter_update_add {K : Type} [Field K] (A : AbVar K) {J : Type} [Fintype J] [DecidableEq J]
    (hJ : Fintype.card J = A.dim) (c : J → Pic A.X.left) (i : J) (a b : Pic A.X.left) :
    inter A (Function.update c i (a + b)) = inter A (Function.update c i a) + inter A (Function.update c i b) := by
  letI := A.algΓ
  exact congrFun ((diffVanish_chiPic_structureModule A).multiDiff_update_add_of_le_card hJ.ge c i a b) 0

def interAdd {K : Type} [Field K] (A : AbVar K) {J : Type} [Fintype J] [DecidableEq J]
    (hJ : Fintype.card J = A.dim) (c : J → Pic A.X.left) (i : J) : Pic A.X.left →+ ℤ :=
  AddMonoidHom.mk' (fun a => inter A (Function.update c i a)) (inter_update_add A hJ c i)

theorem inter_comp_equiv {K : Type} [Field K] (A : AbVar K) {J J' : Type} [Fintype J] [Fintype J']
    (e : J' ≃ J) (c : J → Pic A.X.left) : inter A (c ∘ e) = inter A c := by
  letI := A.algΓ
  exact congrFun (multiDiff_comp_equiv e c _) 0

theorem inter_multilinear_and_symm :
    ∀ (K : Type) [Field K] (A : AbVar K) (J : Type) [Fintype J], Fintype.card J = A.dim →
      (∃ M : (J → Pic A.X.left) →ₘₗ[ℤ] ℤ, ∀ c, M c = inter A c) ∧
      ∀ (J' : Type) [Fintype J'] (e : J' ≃ J) (c : J → Pic A.X.left), inter A (c ∘ e) = inter A c := by
  intro K _ A J _ hJ
  classical
  refine ⟨⟨MultilinearMap.mk' (fun c => inter A c) (fun c i a b => inter_update_add A hJ c i a b)
    (fun c i n a => map_zsmul (interAdd A hJ c i) n a), fun c => rfl⟩, fun J' _ e c => inter_comp_equiv A e c⟩

end GlobalTheory.AV.AbVar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianVarietyAmpleClassAdd
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV

theorem isAmpleCls_add : ∀ (K : Type) [Field K] (A : AbVar K) (c d : Pic A.X.left),
    IsAmpleCls c → IsAmpleCls d → IsAmpleCls (c + d) := by
  intro K _ A c d hc hd
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  obtain ⟨M, hM, rfl⟩ := cls_surj d
  have hA : IsAmpleLB L := (_root_.GlobalTheory.AmpleClsIff.isAmpleCls_cls_iff K A L hL).1 hc
  have hB : IsAmpleLB M := (_root_.GlobalTheory.AmpleClsIff.isAmpleCls_cls_iff K A M hM).1 hd
  have hN : (tens L M).IsLB := isLB_tens hL hM
  have hT : IsAmpleLB (tens L M) := by
    refine hA.tensor hB hN ((cls_eq_zero_iff (LB.isLB_div (LB.isLB_div hN hL) hM)).1 ?_)
    rw [cls_div (LB.isLB_div hN hL) hM, cls_div hN hL, cls_tens hL hM]
    abel
  rw [← cls_tens hL hM hN]
  exact (_root_.GlobalTheory.AmpleClsIff.isAmpleCls_cls_iff K A (tens L M) hN).2 hT

end GlobalTheory.AV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativePolynomialFunctionEqNormFormStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicative_polynomialFunction_eq_normForm : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℚ Ω] (d : ℕ) (δ : Polynomial ℤ → ℚ) (P : Polynomial ℚ), (∀ F G, δ (F * G) = δ F * δ G) → (∀ (n : ℕ) (u : Fin n → Polynomial ℤ), ∃ Φ : MvPolynomial (Fin n) ℚ, Φ.IsHomogeneous (2 * d) ∧ ∀ m : Fin n → ℤ, MvPolynomial.eval (fun i => (m i : ℚ)) Φ = δ (∑ i, m i • u i)) → P.Monic → P.natDegree = 2 * d → (∀ n : ℤ, P.eval (n : ℚ) = δ (Polynomial.C n - Polynomial.X)) → ∀ F : Polynomial ℤ, algebraMap ℚ Ω (δ F) = ((P.aroots Ω).map (fun a => Polynomial.aeval a F)).prod := by
  first | (exact @GlobalTheory.MulPolyNorm.eq_prod_aroots) | (exact GlobalTheory.MulPolyNorm.eq_prod_aroots) | (intros; apply GlobalTheory.MulPolyNorm.eq_prod_aroots  <;> assumption)
end

