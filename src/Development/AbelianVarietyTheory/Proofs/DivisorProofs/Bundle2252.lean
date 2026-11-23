module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformizationEndomorphismCalculus
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2095
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2164
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2153
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1852
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1129
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2154
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2155
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2167
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2078

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationEndomorphismOfAdmissibleBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.UT

set_option maxHeartbeats 1000000

namespace GlobalTheory.UT


open GlobalTheory.EndData in
theorem exists_degenerationEndomorphism_of_admissibleBase : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif I D A G, ∀ (aG : G ⟶ G) (aA : A.A ⟶ A.A), IsMonHom aG → IsMonHom aA → (Over.pullback (jK R)).map aG ≫ U.gen.hom = U.gen.hom ≫ aA → ∃ E : EndU U.toUnifPre, E.aG = aG ∧ E.aA = aA := by
  intro R _ _ I hR D A G _ _ _ U aG aA hG hA hext
  have hL := GlobalTheory.firstFiveLaws
  have hC := hR.2.2.2
  have hB := D.toPre.P.isLB
  obtain ⟨aB, haB, hq⟩ := exists_abelian hL hR U.toUnifPre aG
  obtain ⟨h, hh⟩ := _root_.GlobalTheory.unifPre_end_character_const hL R I hR D A G U.toUnifPre aG hG
  choose t ht hi using hh
  choose v hv vv using fun χ e => T.exists_gen_of_torusEnd_compat R I D.toPre e G (U.gt e) ((Over.pullback (thick R I e)).map aG) aB h (t e)
    inferInstance (ht e) (hi e) (hq e) χ
  have down : ∀ χ e (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.toPre.P.L z J →
      val ((U.gt (e + 1)).t χ) (r ≫ thickMap R I e G) z J = val ((U.gt e).t χ) r z J :=
    fun χ e Z r z J hJ => (val_pull hJ _ _ _).symm.trans (val_corr hJ (U.gt_t e χ) r)
  choose u hu uv using fun χ => _root_.GlobalTheory.Unif.exists_gen_of_thick R I hC D.toPre.P.A D.toPre.P.isAb.smooth
    (AbProj.isProjBy_of_isPullback D.toPre.P (IsPullback.id_horiz _)) _ D.toPre.P.L _ _ _ _ hB (fun _ _ => rfl)
    (v χ) (hv χ) (fun e z J hJ => by
      have := (U.gt e).q_flat
      have := (U.gt e).q_surj
      refine val_eq_of_flat hB _ _ _ _ (fun k => ?_) (U.gt e).q.left (fun x J hJ => ?_) z J hJ
      · rw [← Category.assoc, trans_fst, Category.id_comp]
      · have k₁ := vv χ (e + 1) _ (𝟙 _ ≫ thickMap R I e G) x J hJ
        have k₀ := vv χ e _ (𝟙 _) x J hJ
        rw [down _ _ _ _ _ _ hJ, Category.assoc, trans_map, ← Category.assoc, down _ _ _ _ _ _ hJ, k₀,
          Category.id_comp, Category.id_comp, UnifCompare.trans_comp_q] at k₁
        rw [Category.comp_id]
        exact (mul_left_cancel k₁).symm)
  refine ⟨⟨aG, aA, aB, hG, hA, haB, h, hext, hq, fun e => ⟨t e, ht e, hi e⟩, u, fun χ => ⟨hu χ, ?_⟩,
    fun e χ Z x z J hJ => ?_⟩, rfl, rfl⟩
  · refine corr_of_val hB fun y J hJ => Eq.trans ?_ (val_one _).symm
    refine val_eq_one I hB (fun V _ k => ?_) _ (pullGen_isGen _ _ _ _ (hu χ) _) (fun e z J hJ => ?_) y J hJ
    · refine (Fintype.prod_sum_type _).trans ((congrArg₂ (· * ·) (prod_unit D.toPre (𝟙 _) (h χ) k).1
        (prod_unit D.toPre aB χ k).2).trans ((_root_.mul_one _).trans (Fintype.prod_empty _).symm))
    · have := (U.gt e).q_hom
      have k := vv χ e _ (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left z J hJ
      rw [← Over.comp_left, ← Over.comp_left, MonObj.one_comp, MonObj.one_comp, TorusCoord.val_unit _ _ hJ,
        TorusCoord.val_unit _ _ hJ, _root_.one_mul, ← uv χ e _ _ z J hJ] at k
      have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e D.toPre.P.A) =
        η[thickObj R I e D.toPre.P.A] := by simp [Hom.one_def]
      rw [o] at k
      exact (val_pull hJ _ _ _).trans ((congrArg (fun p => val (u χ) p z J)
        (UnitValue.eSec_pullback_fst (thick R I e) D.toPre.P.A).symm).trans k.symm)
  · refine (vv χ e Z x z J hJ).trans (congrArg (_ * ·) ((uv χ e Z _ z J hJ).symm.trans ?_))
    exact congrArg (fun p => val (u χ) p z J) (Category.assoc _ _ _)


open GlobalTheory.EndRosati GlobalTheory.CechPic in
theorem rosatiAdjoint_and_linear_of_admissibleBase : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif I D A G, ∀ E E' : EndU U.toUnifPre, LBIso (cubeLB G ![fst G G ≫ E.aG, snd G G] U.LG.L) (cubeLB G ![fst G G, snd G G ≫ E'.aG] U.LG.L) → RosatiAdj A.A A.L E.aA E'.aA ∧ RosatiAdj D.toPre.P.A D.toPre.P.L E.aB E'.aB ∧ (∀ χ, D.toPre.c (E.h χ) = D.toPre.c χ ≫ E'.aB) ∧ ∀ χ, D.toPre.c (E'.h χ) = D.toPre.c χ ≫ E.aB := by
  intro R _ _ I hR D A G _ _ hG U E E' H
  have hLL := GlobalTheory.firstFiveLaws
  have hGF := hLL.1.globalFns
  obtain ⟨-, -, -, hC⟩ := hR
  have := E.homG
  have := E'.homG
  have := E.homB
  have := E'.homB
  have := hG.geomConnected
  obtain ⟨u, hu, h₀⟩ := (NormRos.normRos_of_lbIso _ G U.LG.L U.LG.isLB E.aG E'.aG H).1
  have hP : AbLaw.IsProjBy D.toPre.P.A.hom := AbProj.isProjBy_of_isPullback D.toPre.P (IsPullback.id_horiz _)
  have hB : RosatiAdj D.toPre.P.A D.toPre.P.L E.aB E'.aB :=
    loc_gen_of_thickenings hGF I _ (AbelianSchemeGerms.isAbelianScheme_tensor _ _ D.toPre.P.isAb D.toPre.P.isAb)
      (AbLaw.isProjBy_tensor R _ _ hP hP) D.toPre.P.isLB _ _ fun e => by
      have := EndTorus.connectedSpace_thickening I e
      have : GeometricallyConnected (thickObj R I e G).hom :=
        inferInstanceAs (GeometricallyConnected (pullback.snd G.hom (thick R I e)))
      have : ConnectedSpace (thickObj R I e G).left :=
        GroupConn.connectedSpace_of_section (thickObj R I e G).hom (η : 𝟙_ _ ⟶ thickObj R I e G).left (Over.w _)
      exact exists_gen_thick U.toUnifPre e (E.q_lin e) (E'.q_lin e)
        (FamGerm.surjective_appTop_sq_cube U.toUnifPre).2 u hu h₀
  obtain ⟨r, hr, -⟩ := exists_ros hGF D.toPre.P.isAb D.toPre.P.isLB E.aB E'.aB hB
  refine ⟨rosatiAdj_generic U.toUnifPre E.ext E'.ext u hu, hB, fun χ => ?_, fun χ => ?_⟩
  · have h₁ := cls_of_gen D.toPre E.aB χ _ (E.u χ) (E.u_norm χ).1
    have h₂ := cls_of_rosati D.toPre.P.isLB r hr (𝟙 _) (toUnit _ ≫ D.toPre.c χ)
    rw [Category.id_comp, Category.assoc] at h₂
    refine eq_of_translate_cls D.toPre.P.isLB D.toPre.P.ktriv _ _ ?_
    linear_combination (norm := abel) h₁ + h₂
  · have h₁ := cls_of_gen D.toPre E'.aB χ _ (E'.u χ) (E'.u_norm χ).1
    have h₂ := cls_of_rosati D.toPre.P.isLB r hr (toUnit _ ≫ D.toPre.c χ) (𝟙 _)
    rw [Category.id_comp, Category.assoc, mul_comm _ (𝟙 D.toPre.P.A), mul_comm _ E'.aB] at h₂
    refine eq_of_translate_cls D.toPre.P.isLB D.toPre.P.ktriv _ _ ?_
    linear_combination (norm := abel) h₁ - h₂

end GlobalTheory.UT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescendedLineBundleEquivariantGenerator
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CharKer

theorem pmap_eq_whiskerRight {S : Scheme.{0}} {A A' : Over S} (q : A ⟶ A') (T : Over S) : pmap q T = q ▷ T := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [pmap]

theorem isPullback_over_left {S : Scheme.{0}} {P X Y Z : Over S} {f : P ⟶ X} {g : P ⟶ Y} {h : X ⟶ Z} {k : Y ⟶ Z}
    (H : IsPullback f g h k) : IsPullback f.left g.left h.left k.left :=
  H.map (Over.forget S)

theorem res_res_units {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)ˣ) :
    res h₂ (res h₁ x) = res (h₂.trans h₁) x := by
  apply Units.ext
  change _ = (X.presheaf.map ((homOfLE h₁).op ≫ (homOfLE h₂).op)).hom x.val
  rw [Functor.map_comp, CommRingCat.hom_comp, RingHom.comp_apply]; rfl

theorem res_pullU_units {X Y : Scheme.{0}} (f : Y ⟶ X) {U V : X.Opens} (h : V ≤ U) (x : Γ(X, U)ˣ) :
    pullU f V (res h x) = res (f.preimage_mono h) (pullU f U x) := by
  apply Units.ext
  have := f.naturality (homOfLE h).op
  change (X.presheaf.map (homOfLE h).op ≫ f.app V).hom x.val = _
  rw [this]; rfl

theorem mul_mul_inv_mul_inv_cancel {G : Type*} [CommGroup G] (c x y : G) : (c * x) * (c * y)⁻¹ = x * y⁻¹ := by
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_left_eq_div]

theorem exists_equivGen : ∀ (S : Scheme.{0}) (A A' N T : Over S) [GrpObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A') (χ : Γ((N ⊗ T).left, ⊤)ˣ), IsMonHom i → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → IsPullback i (toUnit N) q η[A'] → IsCharacter χ → ∃ (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ), M.IsLB ∧ IsEquivGen i q χ M e := by
  intro S A A' N T _ _ _ i q χ hi hq hfin hflat hsurj hker hχ
  have hloc := _root_.GlobalTheory.CharKer.exists_nhds_charUnit S A A' N T i q χ hi hq hfin hflat hsurj hker hχ
  have : Flat (pmap q T).left := by rw [pmap_eq_whiskerRight]; infer_instance
  have : Surjective (pmap q T).left := by rw [pmap_eq_whiskerRight]; infer_instance
  have : QuasiCompact (pmap q T).left := by rw [pmap_eq_whiskerRight]; infer_instance
  have hpb : IsPullback (prMap A N T).left (actMap i T).left (pmap q T).left (pmap q T).left :=
    isPullback_over_left (_root_.GlobalTheory.CharKer.pmap_isPullback_actMap S A A' N T i q hi hq hker)
  have hw : ∀ z, (pmap q T).left ((actMap i T).left z) = (pmap q T).left ((prMap A N T).left z) := fun z => by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hpb.w]
  have inj : ∀ U : (A' ⊗ T).left.Opens, Function.Injective (pullU (pmap q T).left U) := fun U x y hxy =>
    Units.ext (ReciprocityTheory.ChartRestriction.G.DVR.TG.app_injective_of_flat_surj (pmap q T).left U (congrArg Units.val hxy))
  have desc : ∀ (U : (A' ⊗ T).left.Opens) (u : Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ U)ˣ),
      (∀ (W : (A ⊗ (N ⊗ T)).left.Opens) (h₁ : W ≤ (actMap i T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ U))
        (h₂ : W ≤ (prMap A N T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ U)),
        res h₁ (pullU (actMap i T).left _ u) = res h₂ (pullU (prMap A N T).left _ u)) →
      ∃ g : Γ((A' ⊗ T).left, U)ˣ, pullU (pmap q T).left U g = u := by
    intro U u hu
    have hg : (prMap A N T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ U) ≤ (actMap i T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ U) :=
      fun z hz => show (pmap q T).left ((actMap i T).left z) ∈ U from (hw z) ▸ hz
    have key := GlobalTheory.FlatDescent.existsUnique_app_eq_iff (pmap q T).left hpb U _ rfl le_rfl hg u.val
    obtain ⟨a, ha, -⟩ := key.2 (congrArg Units.val (hu _ hg le_rfl)).symm
    obtain ⟨a, rfl⟩ := (GlobalTheory.FlatDescent.isUnit_app_iff (pmap q T).left U a).1 (ha ▸ u.isUnit)
    exact ⟨a, Units.ext ha⟩
  choose V hyV e he using hloc
  have hu : ∀ k l, ∃ g : Γ((A' ⊗ T).left, V k ⊓ V l)ˣ, pullU (pmap q T).left _ g =
      res ((pmap q T).left.preimage_mono inf_le_left) (e k) *
        (res ((pmap q T).left.preimage_mono inf_le_right) (e l))⁻¹ := fun k l => desc _ _ (by
    intro W h₁ h₂
    simp only [map_mul, map_inv, res_pullU_units, res_res_units]
    rw [he k W _ (h₂.trans ((prMap A N T).left.preimage_mono ((pmap q T).left.preimage_mono inf_le_left))),
      he l W _ (h₂.trans ((prMap A N T).left.preimage_mono ((pmap q T).left.preimage_mono inf_le_right))),
      mul_mul_inv_mul_inv_cancel])
  choose g hg using hu
  refine ⟨⟨(A' ⊗ T).left, V, g⟩, e, ⟨?_, ?_, ?_⟩, ?_, fun k W h₁ h₂ => he k W h₁ h₂⟩
  · exact eq_top_iff.2 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hyV y⟩
  · intro k
    apply inj
    simp only [res_pullU_units, hg, map_mul, map_inv, res_res_units, map_one, mul_inv_cancel]
  · intro a b c
    apply inj
    simp only [res_pullU_units, hg, map_mul, map_inv, res_res_units, _root_.mul_assoc, inv_mul_cancel_left]
  · intro k l W h₁ h₂ h₃
    simp only [res_pullU_units, hg, map_mul, map_inv, res_res_units, _root_.mul_assoc, inv_mul_cancel, _root_.mul_one]

end GlobalTheory.CharKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentDatumOfDescendedMultiplicationImpor
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.Desc

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}

def UT (N : Near π G) : Over (pullback π π) := Over.mk (pullback.snd N.U.hom (pullback.fst π π ≫ π))

def toS (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    pullback N.U.hom (pullback.fst π π ≫ π) ⟶ pullback N.U.hom π :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ p) (by
    rw [Category.assoc, hp]; exact pullback.condition)

def embL (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    pullback N.U.hom (pullback.fst π π ≫ π) ⟶ pullback G.hom p :=
  pullback.lift (toS N p hp ≫ N.u) (pullback.snd _ _) (by
    rw [Category.assoc, N.u_over, toS, pullback.lift_snd])

def emb (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    UT N ⟶ (Over.pullback p).obj G :=
  Over.homMk (embL N p hp) (pullback.lift_snd _ _ _)

def sum [GrpObj G] (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    UT N ⊗ UT N ⟶ (Over.pullback p).obj G :=
  (fst (UT N) (UT N) ≫ emb N p hp) * (snd (UT N) (UT N) ≫ emb N p hp)

end GlobalTheory.Mum.Desc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisorsDoubleFlagSpaceStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_divisors_doubleFlagSpace : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (gr : Root m → Y.Dv), ∀ B ∈ E'.S (genericPoint Y.X), (∀ (y : Y.X) (x : Root m), ∃ A ∈ E'.S y, ∃ t : Y.Fnˣ, (B * A⁻¹) x.1 x.2 x.2 = t ∧ (gr x).IsEqn y t) → ∀ W : Dbl Y, (∀ u : X.Fn, W.α₁ (φ u) = W.α₂ (φ u)) → ∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → AlmostLow τ a b (B.map W.α₁ * (B.map W.α₂)⁻¹) → ∃ (D₁ D₂ : Root m → CartierDiv W.Z) (Θ : CartierDiv W.Z), (∀ x, IsPull W.p₁ (D₁ x) (gr x)) ∧ (∀ x, IsPull W.p₂ (D₂ x) (gr x)) ∧ (∀ x, x ≠ ⟨τ, a⟩ → x ≠ ⟨τ, b⟩ → toPic (D₁ x) = toPic (D₂ x)) ∧ toPic (D₁ ⟨τ, a⟩) + toPic (D₁ ⟨τ, b⟩) = toPic (D₂ ⟨τ, a⟩) + toPic (D₂ ⟨τ, b⟩) ∧ toPic Θ = toPic (D₂ ⟨τ, b⟩) - toPic (D₁ ⟨τ, a⟩) ∧ Θ.Eff ∧ (Θ.supp : Set W.Z) = Set.range W.δ := by
  intro F _ X Y ι _ m E E' φ f hf gr B hB hgr W hα τ a b hab hC
  choose D₁ hD₁ using fun x => _root_.GlobalTheory.FlagPush.exists_isPull W.Z Y.X W.p₁ (gr x)
  choose D₂ hD₂ using fun x => _root_.GlobalTheory.FlagPush.exists_isPull W.Z Y.X W.p₂ (gr x)
  have hC0 : Par 0 ⊤ (B.map W.α₁ * (B.map W.α₂)⁻¹) := fun σ =>
    ⟨fun _ _ => trivial, hC.1 σ, trivial, fun i j hi => absurd hi (by simp)⟩
  obtain ⟨hCd, hCm, -⟩ := _root_.GlobalTheory.FlagPush.almostLow_units ι m τ a b hab _ ⊤ _ hC hC0
  have K := fun (z : W.Z) {A₁ A₂ : Mat m Y.Fn} (hA₁ : A₁ ∈ E'.S (W.p₁ z)) (hA₂ : A₂ ∈ E'.S (W.p₂ z)) =>
    GlobalTheory.FlagPush.DivOn.key hf hB hgr W hα hab hC hD₁ hD₂ z hA₁ hA₂
  have hne : a ≠ b := fun h => by rw [h] at hab; omega
  have hΘ : ∀ (z : W.Z) {A₁ A₂ : Mat m Y.Fn} (hA₁ : A₁ ∈ E'.S (W.p₁ z)) (hA₂ : A₂ ∈ E'.S (W.p₂ z)),
      ∃ g : W.Z.functionFieldˣ, (g : W.Z.functionField) = (A₁.map W.α₁ * (A₂.map W.α₂)⁻¹) τ a b ∧
        (D₂ ⟨τ, b⟩ - D₁ ⟨τ, a⟩ + CartierDiv.principal (Units.mk0 _ hC.2.1)).IsEqn z g := fun z A₁ A₂ hA₁ hA₂ => by
    obtain ⟨t₁, t₂, q₁, q₂, -, -, -, e, -⟩ := K z hA₁ hA₂
    refine ⟨_, ?_, ((q₂ ⟨τ, b⟩).sub (q₁ ⟨τ, a⟩)).add (CartierDiv.isEqn_principal _ z)⟩
    rw [e, Units.val_mul, Units.val_div_eq_div_val, Units.val_mk0]
    ring
  refine ⟨D₁, D₂, D₂ ⟨τ, b⟩ - D₁ ⟨τ, a⟩ + CartierDiv.principal (Units.mk0 _ hC.2.1), hD₁, hD₂, fun x hxa hxb => ?_,
    ?_, ?_, fun z => ?_, ?_⟩
  · have e : D₂ x + CartierDiv.principal (Units.mk0 _ (hCd x hxa hxb).1) = D₁ x :=
      CartierDiv.ext_of_isEqn fun z => by
        obtain ⟨A₁, hA₁⟩ := E'.nonempty (W.p₁ z)
        obtain ⟨A₂, hA₂⟩ := E'.nonempty (W.p₂ z)
        obtain ⟨t₁, t₂, q₁, q₂, -, hu, -⟩ := K z hA₁ hA₂
        refine ⟨_, (q₂ x).add (CartierDiv.isEqn_principal _ z), (q₁ x).iff_unitAt.2 ?_⟩
        convert hu x hxa hxb using 1
        rw [Units.val_mul, Units.val_mk0]
        ring
    rw [← e, map_add (f := _), toPic_principal, add_zero]
  · have e : D₂ ⟨τ, a⟩ + D₂ ⟨τ, b⟩ + CartierDiv.principal (Units.mk0 _ hCm) = D₁ ⟨τ, a⟩ + D₁ ⟨τ, b⟩ :=
      CartierDiv.ext_of_isEqn fun z => by
        obtain ⟨A₁, hA₁⟩ := E'.nonempty (W.p₁ z)
        obtain ⟨A₂, hA₂⟩ := E'.nonempty (W.p₂ z)
        obtain ⟨t₁, t₂, q₁, q₂, -, -, hu, -⟩ := K z hA₁ hA₂
        refine ⟨_, ((q₂ _).add (q₂ _)).add (CartierDiv.isEqn_principal _ z), ((q₁ _).add (q₁ _)).iff_unitAt.2 ?_⟩
        convert hu using 1
        simp only [Units.val_mul, Units.val_mk0]
        ring
    rw [← map_add (f := _), ← map_add (f := _), ← e, map_add _ (_ + _), toPic_principal, add_zero]
  · rw [map_add (f := _), toPic_principal, add_zero, map_sub]
  · obtain ⟨A₁, hA₁⟩ := E'.nonempty (W.p₁ z)
    obtain ⟨A₂, hA₂⟩ := E'.nonempty (W.p₂ z)
    obtain ⟨g, e, hg⟩ := hΘ z hA₁ hA₂
    obtain ⟨t₁, t₂, -, -, -, -, -, -, hr⟩ := K z hA₁ hA₂
    exact ⟨g, hg, by rw [one_mul, e]; exact hr⟩
  · ext z
    constructor
    · intro hz
      obtain ⟨A₁, hA₁⟩ := E'.nonempty (W.p₁ z)
      obtain ⟨A₂, hA₂⟩ := E'.nonempty (W.p₂ z)
      obtain ⟨g, e, hg⟩ := hΘ z hA₁ hA₂
      obtain ⟨t₁, t₂, -, -, hal, -⟩ := K z hA₁ hA₂
      refine _root_.GlobalTheory.FlagPush.mem_range_section_of_not_unitAt F X Y ι m E E' φ f hf W hα τ a b z A₁ hA₁ A₂ hA₂ hal ?_
      rw [← e]
      exact hg.mem_supp_iff.1 hz
    · rintro ⟨y, rfl⟩
      obtain ⟨A, hA⟩ := E'.nonempty y
      have e₁ : W.p₁ (W.δ y) = y := by rw [← Scheme.Hom.comp_apply, W.δ₁]; rfl
      have e₂ : W.p₂ (W.δ y) = y := by rw [← Scheme.Hom.comp_apply, W.δ₂]; rfl
      obtain ⟨g, e, hg⟩ := hΘ (W.δ y) (A₁ := A) (A₂ := A) (by rw [e₁]; exact hA) (by rw [e₂]; exact hA)
      refine hg.mem_supp_iff.2 ?_
      rw [e]
      exact _root_.GlobalTheory.FlagPush.not_unitAt_section F X Y ι m E E' φ f hf W hα τ a b hne y A hA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffectiveQDivisorOffPointAmpleClass
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair

set_option autoImplicit false

namespace GlobalTheory

theorem exists_common_den_nonneg (q₁ q₂ : ℚ) (h₁ : 0 ≤ q₁) (h₂ : 0 ≤ q₂) :
    ∃ a b M : ℕ, 0 < M ∧ q₁ = a / M ∧ q₂ = b / M := by
  refine ⟨q₁.num.toNat * q₂.den, q₂.num.toNat * q₁.den, q₁.den * q₂.den,
    Nat.mul_pos q₁.den_pos q₂.den_pos, ?_, ?_⟩
  · have e : ((q₁.num.toNat : ℕ) : ℚ) = q₁.num := by
      exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.2 h₁)
    have hd : (q₂.den : ℚ) ≠ 0 := by exact_mod_cast q₂.den_ne_zero
    push_cast
    rw [e, mul_div_mul_right _ _ hd, Rat.num_div_den]
  · have e : ((q₂.num.toNat : ℕ) : ℚ) = q₂.num := by
      exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.2 h₂)
    have hd : (q₁.den : ℚ) ≠ 0 := by exact_mod_cast q₁.den_ne_zero
    push_cast
    rw [e, mul_comm (q₁.den : ℚ) (q₂.den : ℚ), mul_div_mul_right _ _ hd, Rat.num_div_den]

theorem exists_eff_off_pt_ample_class : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → letI := algebraΓOfHom p; ∀ (N₀ : LB X) (A : CartierDiv X) (x : X) (r : ℕ) (lam μ : ℚ), N₀.IsLB → IsNef ℂ N₀ → IsAmpleLB (toLB A) → 0 < r → lam ≤ 1 → 0 < μ → ∃ (M : ℕ) (E : CartierDiv X), 0 < M ∧ E.Eff ∧ x ∉ E.supp ∧ ∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB E] : ℚ) / M = (1 - lam) * interNumRed ℂ C ![N₀] / r + μ * interNumRed ℂ C ![toLB A] := by
  intro X _ _ p hp
  letI := algebraΓOfHom p
  intro N₀ A x r lam μ hN₀ hNef hA hr hlam hμ
  have hr' : (0 : ℚ) < r := by exact_mod_cast hr
  obtain ⟨a, b, M, hM, ha, hb⟩ :=
    exists_common_den_nonneg ((1 - lam) / r) μ (div_nonneg (by linarith) hr'.le) hμ.le
  have hb1 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · rw [h] at hb; simp at hb; linarith
    · exact h
  have hAb : IsAmpleLB (lbPow (toLB A) b) := (isAmpleLB_pow_iff hA.isLB hb1).2 hA
  have hNa : IsNef ℂ (lbPow N₀ a) := hNef.pow hA a
  have hP : (tens (lbPow (toLB A) b) (lbPow N₀ a)).IsLB := isLB_tens hAb.isLB hNa.isLB
  have hPa : IsAmpleLB (tens (lbPow (toLB A) b) (lbPow N₀ a)) :=
    isAmpleLB_of_cls_eq_ample_add_nef ℂ X p hp _ _ _ hAb hNa hP
      (cls_tens hAb.isLB hNa.isLB hP)
  obtain ⟨n, hn, s, hx, -, -⟩ := hPa.exists_affine_le (x := x) (U := ⊤) trivial
  have hgen : genericPoint X ∈ nonzeroLocus s :=
    (genericPoint_specializes x).mem_open (nonzeroLocus s).isOpen hx
  have hLn := isLB_lbPow hPa.isLB n
  refine ⟨M * n, divOfSec hLn s hgen, Nat.mul_pos hM hn, eff_divOfSec_of_sec hLn s hgen,
    notMem_supp_divOfSec.2 hx, fun C hC => ?_⟩
  have hcls : toPic (divOfSec hLn s hgen) = cls _ hLn :=
    (presents_divOfRatSec hLn (isRatSec_ratOfSec s hgen)).toPic_eq
  have e : cls (toLB (divOfSec hLn s hgen)) (isLB_toLB _) =
      (n * a) • cls N₀ hN₀ + (n * b) • cls (toLB A) (isLB_toLB A) := by
    change toPic (divOfSec hLn s hgen) = _
    rw [hcls, cls_lbPow hPa.isLB, cls_tens hAb.isLB hNa.isLB, cls_lbPow (isLB_toLB A),
      cls_lbPow hN₀]
    rw [smul_add, smul_smul, smul_smul, add_comm]
  rw [interNumRed_of_cls_eq_nsmul_add ℂ X p hp _ N₀ (toLB A) (isLB_toLB _) hN₀ (isLB_toLB A)
    (n * a) (n * b) C hC e]
  have hMn : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_of_ne_zero (by omega)).ne'
  rw [hb, mul_div_right_comm, ha]
  push_cast
  field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerEndomorphismActingByMatrix
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.Poinc.Sep.E8Fibration.exists_monHom_actsBy : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj B] (pr : Fin 8 → (A ⟶ B)),
  E8Fibration.IsProd pr → ∀ m : Matrix (Fin 8) (Fin 8) ℤ, ∃ f : A ⟶ A, IsMonHom f ∧ E8Fibration.ActsBy pr f m := by
  intro S A B _ _ _ pr hP m
  letI cG : ∀ Z : Over S, CommGroup (Z ⟶ B) := fun Z => Hom.commGroup
  have mc : ∀ {T : Over S} (u v : T ⟶ A) (e : A ⟶ B), IsMonHom e → (u * v) ≫ e = (u ≫ e) * (v ≫ e) := by
    intro T u v e he
    rw [Hom.mul_def, Hom.mul_def, Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map]
  have pc : ∀ {T : Over S} (x : T ⟶ A) (a : Fin 8),
      x ≫ (∏ b, pr b ^ m a b : A ⟶ B) = ∏ b, (x ≫ pr b) ^ m a b := by
    intro T x a
    let φ : (A ⟶ B) →* (T ⟶ B) :=
      { toFun := fun u => x ≫ u, map_one' := MonObj.comp_one x, map_mul' := fun u v => MonObj.comp_mul x u v }
    have := map_prod φ (fun b => pr b ^ m a b) Finset.univ
    simp only [map_zpow] at this
    exact this
  obtain ⟨f, hf, -⟩ := hP.2 A (fun a => ∏ b, pr b ^ m a b)
  refine ⟨f, ReciprocityTheory.ChartRestriction.G.Geo.Tor.isMonHom_of_mul f fun T x y => ?_, hf⟩
  refine (hP.2 T fun a => ((x * y) ≫ f) ≫ pr a).unique (fun a => rfl) fun a => ?_
  rw [mc _ _ _ (hP.1 a), Category.assoc, Category.assoc, Category.assoc, hf, pc, pc, pc,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [mc _ _ _ (hP.1 b), mul_zpow]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEndoImageTorsionPointUniformisedModelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_endo_image_torsion_point_uniformised_model : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (f : ρ.P.A ⟶ ρ.P.A), IsMonHom f → ∀ (m : ℕ) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), x ^ m = 1 → ∃ x₂ : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A, x₂.left ≫ u.φ = x.left ≫ u.φ ≫ f.left ∧ x₂ ^ m = 1 := by
  first | exact @GlobalTheory.EndoPt.exists_endo_point | exact GlobalTheory.EndoPt.exists_endo_point | (intros; apply GlobalTheory.EndoPt.exists_endo_point <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicalTrivialisationCompMonHomStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_even_cubicalTrivialisation_comp_monHom : ∀ (S : Scheme.{0}) (G H H' : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj H] [GrpObj H'] (P : GlobalTheory.UU.CP G) (i : H' ⟶ G) (e : H ⟶ H'), IsMonHom e → ∀ σ : GlobalTheory.UU.CubTriv P.c i, GlobalTheory.UU.CubTriv.Even (P := P) σ → ∃ σ₁ : GlobalTheory.UU.CubTriv P.c (e ≫ i), GlobalTheory.UU.CubTriv.Even (P := P) σ₁ := by
  first | exact @GlobalTheory.CubTrivComp.exists_even_comp | exact GlobalTheory.CubTrivComp.exists_even_comp | (intros; apply GlobalTheory.CubTrivComp.exists_even_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulEqLogDerivationExtendLocalizationAwStatement
section
open GlobalTheory.LogDerProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_smul_eq_logDerivation_extend_localizationAway : ∀ {k R S : Type} [Field k] [CommRing R] [CommRing S] [Algebra R S] (f : R) [IsLocalization.Away f S] (φ : k →+* R), φ.FiniteType → ∀ (J : Ideal R) (n : (logSub ((algebraMap R S).comp φ) (J.map (algebraMap R S))).restrictScalars R), ∃ x : logSub φ J × Submonoid.powers f, x.2 • n = res (S := S) f φ J x.1 := by
  first | exact @GlobalTheory.LogDerProj.exists_pow_smul_eq_res | exact GlobalTheory.LogDerProj.exists_pow_smul_eq_res | (intros; apply GlobalTheory.LogDerProj.exists_pow_smul_eq_res <;> assumption)
end

