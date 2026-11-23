module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidifiedCubicalSymmetricExtensionNormalB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0189
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0173
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.TripleExt

namespace PositivityTheory.Member.SiegelModularCharts.K6

theorem pic_ext {X U : Scheme.{0}} [IsLocallyNoetherian X] (hX : Geo.Tor.IsNormalScheme X) (j : U ⟶ X)
    [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] (P : Over X) (e : X ⟶ P.left) {HU : Scheme.{0}}
    (jH : HU ⟶ P.left) (pU : HU ⟶ U) (hp : Smooth P.hom) (hg : GeometricallyIntegral P.hom) (he : e ≫ P.hom = 𝟙 _)
    (hj : IsPullback jH pU P.hom j) (α β : Pic P.left) (h₁ : pull jH α = pull jH β) (h₂ : pull e α = pull e β) :
    α = β := by
  obtain ⟨N, hN, hc⟩ := cls_surj (α - β)
  refine sub_eq_zero.1 (hc ▸ (cls_eq_zero_iff hN).2 ?_)
  refine _root_.GlobalTheory.GenericExtend.exists_isGen_of_densePart X U j hX inferInstance inferInstance inferInstance inferInstance P e N he hp hg hN
    ((cls_eq_zero_iff (pull_isLB hN _)).1 ?_) ((cls_eq_zero_iff (pull_isLB hN _)).1 ?_)
  · rw [cls_pull hN, hc, map_sub, h₂, sub_self]
  · rw [cls_pull hN, hc, ← hj.isoPullback_inv_fst, pull_comp, map_sub, h₁, sub_self, map_zero]

theorem isReduced_of_normal {X : Scheme.{0}} (hX : Geo.Tor.IsNormalScheme X) : IsReduced X := by
  have : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    have := (hX x).1
    infer_instance
  exact isReduced_of_isReduced_stalk X

theorem isReduced_source {X U : Scheme.{0}} (hX : Geo.Tor.IsNormalScheme X) (j : U ⟶ X)
    (h : ∀ u : U, IsIso (j.stalkMap u)) : IsReduced U := by
  have : ∀ x : U, _root_.IsReduced (U.presheaf.stalk x) := fun x => by
    have := (hX (j x)).1
    have := h x
    exact isReduced_of_injective (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv.symm
      (asIso (j.stalkMap x)).commRingCatIsoToRingEquiv.symm.injective
  exact isReduced_of_isReduced_stalk U

theorem exists_sab_extension {X U : Scheme.{0}} [IsLocallyNoetherian X] (hX : Geo.Tor.IsNormalScheme X) (j : U ⟶ X)
    [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] {E : Type} [Field E] [NumberField E] [IsCMField E]
    (H : Host E) (G : Over X) [GrpObj G] [IsCommMonObj G] (semi : IsSemiAbelian G) (act : OAct (𝓞 E) G)
    (t₀ : SAB H U) (a : t₀.G.left ⟶ G.left) [IsProper t₀.G.hom] (h : IsGrpPullback t₀.G G j a)
    (hact : ∀ x, (t₀.act.act x).left ≫ a = a ≫ (act.act x).left) (M : LB G.left) (hM : M.IsLB)
    (hMa : LBIso (M.pull a) t₀.PP.L) :
    ∃ (PP : RigLB G) (cub : CubicalStr G PP) (h₁ : _) (h₂ : _) (h₃ : _)
      (m : SABMap t₀ (SAB.mk G semi act PP cub h₁ h₂ h₃) j), m.φ = a := by
  have := semi.smooth
  have := semi.geomConnected
  obtain ⟨hgen, hst, -, -⟩ := densePart_basic X U j inferInstance inferInstance inferInstance inferInstance
  obtain ⟨PP, hPP⟩ := NormalCubeExt.exists_rigidified h t₀.PP hM hMa
  have hc₀ : cls t₀.PP.L t₀.PP.isLB = pull a (cls PP.L PP.isLB) :=
    (cls_eq_iff t₀.PP.isLB (pull_isLB PP.isLB _)).2 hPP
  have hrig : pull (eSec G) (cls PP.L PP.isLB) = 0 :=
    (cls_eq_zero_iff (pull_isLB PP.isLB _)).2 ⟨PP.rig, PP.rigGen⟩
  have pa : ∀ {T : Over U} (x : T ⟶ t₀.G) b,
      pushPt h.1.w (x ≫ t₀.act.act b) = pushPt h.1.w x ≫ act.act b := fun x b =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  have ha1 : ∀ b, η[G] ≫ act.act b = η[G] := fun b => by have := act.hom b; exact IsMonHom.one_hom _
  have s₂ := CubeExtension.smooth_tensor G G
  have s₃ := CubeExtension.smooth_tensor G (G ⊗ G)
  have c₂ := CubeExtension.geometricallyConnected_tensor G G
  have c₃ := CubeExtension.geometricallyConnected_tensor G (G ⊗ G)
  have hy : ∀ (T : Over X) (y : T ⟶ G), ∃ y' : Over.mk (pullback.snd T.hom j) ⟶ t₀.G, pushPt h.1.w y' =
      (Over.homMk (pullback.fst T.hom j) pullback.condition :
        Over.mk ((Over.mk (pullback.snd T.hom j)).hom ≫ j) ⟶ T) ≫ y := fun T y =>
    ⟨Over.homMk (h.1.lift (pullback.fst T.hom j ≫ y.left) (pullback.snd T.hom j)
      (by rw [Category.assoc, Over.w]; exact pullback.condition)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩
  obtain ⟨hcub, hsym⟩ := GlobalTheory.T.cubicalStructure_and_symmetric_of_cube_gen X G PP semi
    ⟨isReduced_of_normal hX, hgen.trans (range_subset_abLocus_of_isProper semi h.1)⟩
  obtain ⟨cub⟩ : Nonempty (CubicalStr G PP) := by
    refine hcub ((cls_eq_zero_iff (isLB_cube (x3 G) PP.isLB)).1 ?_)
    rw [cls_cube _ PP.isLB]
    let T' : Over U := Over.mk (pullback.snd (G3 G).hom j)
    let u : Over.mk (T'.hom ≫ j) ⟶ G3 G := Over.homMk (pullback.fst (G3 G).hom j) pullback.condition
    choose y hy' using fun i => hy (G3 G) (x3 G i)
    let e : 𝟙_ (Over X) ⟶ G3 G := lift η[G] (lift η[G] η[G])
    refine pic_ext hX j (G3 G) e.left u.left T'.hom s₃
      (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _) (Over.w e)
      (IsPullback.of_hasPullback _ _) _ _ ?_ ?_
    · have h₀ := (cls_eq_zero_iff (isLB_cube (x3 t₀.G) t₀.PP.isLB)).2 ⟨t₀.cub.t, t₀.cub.isGen⟩
      rw [cls_cube _ t₀.PP.isLB, hc₀] at h₀
      have h₁ := congrArg (pull (lift (y 0) (lift (y 1) (y 2))).left) h₀
      rw [pull_cubeCls_pre, map_zero] at h₁
      refine (pull_cubeCls_push h _ _ u (fun i => ?_) _).trans (h₁.trans (map_zero _).symm)
      refine Eq.trans ?_ (hy' i)
      congr 1
      fin_cases i <;> simp [x3]
    · refine (pull_cubeCls_pre e _ _).trans (Eq.trans ?_ (map_zero _).symm)
      refine Eq.trans ?_ (cubeCls_one (n := 3) _ hrig)
      congr 1
      funext i
      fin_cases i <;> simp [e, x3]
  have hs : PP.IsSymmetric := by
    refine hsym ((cls_eq_iff PP.isLB (pull_isLB PP.isLB _)).1 ?_)
    have hι : (ι[t₀.G]).left ≫ a = a ≫ (ι[G]).left := by
      have e := congrArg (fun q => q.left) (map_inv (pushHom h t₀.G) (𝟙 t₀.G))
      simp only [Hom.inv_def, Category.id_comp] at e
      refine e.trans ?_
      show (𝟙 _ ≫ a) ≫ _ = _
      rw [Category.id_comp]
    have e₂ : eSec G ≫ (ι[G]).left = eSec G := by
      rw [eSec, ← Over.comp_left, GrpObj.one_inv]
    rw [cls_pull PP.isLB]
    refine pic_ext hX j G (eSec G) a t₀.G.hom inferInstance
      (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _) (Over.w η[G]) h.1 _ _ ?_ ?_
    · obtain ⟨-, w, hw, -⟩ := t₀.sym
      have h₀ := (cls_eq_iff t₀.PP.isLB (pull_isLB t₀.PP.isLB _)).2 ⟨w, hw⟩
      rw [cls_pull t₀.PP.isLB, hc₀, ← pull_comp, hι, pull_comp] at h₀
      exact h₀
    · rw [← pull_comp, e₂]
  have hadj : ∀ b, LBIso (cubeLB G ![fst G G ≫ act.act b, snd G G] PP.L)
      (cubeLB G ![fst G G, snd G G ≫ act.act (H.bar b)] PP.L) := fun b => by
    refine (cls_eq_iff (isLB_cube _ PP.isLB) (isLB_cube _ PP.isLB)).1 ?_
    rw [cls_cube _ PP.isLB, cls_cube _ PP.isLB]
    let T' : Over U := Over.mk (pullback.snd (G ⊗ G).hom j)
    let u : Over.mk (T'.hom ≫ j) ⟶ G ⊗ G := Over.homMk (pullback.fst (G ⊗ G).hom j) pullback.condition
    obtain ⟨y₁, hy₁⟩ : ∃ y' : T' ⟶ t₀.G, pushPt h.1.w y' = u ≫ fst G G := hy _ (fst G G)
    obtain ⟨y₂, hy₂⟩ : ∃ y' : T' ⟶ t₀.G, pushPt h.1.w y' = u ≫ snd G G := hy _ (snd G G)
    let e : 𝟙_ (Over X) ⟶ G ⊗ G := lift η[G] η[G]
    refine pic_ext hX j (G ⊗ G) e.left u.left T'.hom s₂
      (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _) (Over.w e)
      (IsPullback.of_hasPullback _ _) _ _ ?_ ?_
    · have h₀ := (cls_eq_iff (isLB_cube _ t₀.PP.isLB) (isLB_cube _ t₀.PP.isLB)).2 (t₀.adj b)
      rw [cls_cube _ t₀.PP.isLB, cls_cube _ t₀.PP.isLB, hc₀] at h₀
      have h₁ := congrArg (pull (lift y₁ y₂).left) h₀
      rw [pull_cubeCls_pre, pull_cubeCls_pre] at h₁
      refine (pull_cubeCls_push h _ _ u (fun i => ?_) _).trans
        (h₁.trans (pull_cubeCls_push h _ _ u (fun i => ?_) _).symm)
      · fin_cases i
        · simp [pa, hy₁]
        · simp [hy₂]
      · fin_cases i
        · simp [hy₁]
        · simp [pa, hy₂]
    · refine (pull_cubeCls_pre e _ _).trans (Eq.trans ?_ (pull_cubeCls_pre e _ _).symm)
      congr 1
      funext i
      fin_cases i <;> simp [e, ha1]
  have hprim : LBIso PP.L (cubeLB G ![𝟙 G, act.act H.w0] PP.L) := by
    refine (cls_eq_iff PP.isLB (isLB_cube _ PP.isLB)).1 ?_
    rw [cls_cube _ PP.isLB]
    refine pic_ext hX j G (eSec G) a t₀.G.hom inferInstance
      (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres _) (Over.w η[G]) h.1 _ _ ?_ ?_
    · have h₀ := (cls_eq_iff t₀.PP.isLB (isLB_cube _ t₀.PP.isLB)).2 t₀.prim
      rw [cls_cube _ t₀.PP.isLB, hc₀] at h₀
      have h₁ := pull_cubeCls_push h ![𝟙 t₀.G, t₀.act.act H.w0] ![𝟙 G, act.act H.w0] (pushPt h.1.w (𝟙 t₀.G))
        (fun i => by
          fin_cases i
          · simp
          · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)) (cls PP.L PP.isLB)
      have e : (pushPt h.1.w (𝟙 t₀.G)).left = a := Category.id_comp _
      rw [e] at h₁
      exact h₀.trans h₁.symm
    · refine hrig.trans (Eq.trans ?_ (pull_cubeCls_pre η[G] _ _).symm)
      refine (cubeCls_one (n := 2) _ hrig).symm.trans ?_
      congr 1
      funext i
      fin_cases i <;> simp [ha1]
  obtain ⟨m, hm⟩ := exists_sabMap_of_lbIso E H X U (SAB.mk G semi act PP cub hs hadj hprim) t₀ j a
    ⟨isReduced_source hX j hst, fun x _ => range_subset_abLocus_of_isProper t₀.semi
      (ObjRebase.isGrpPullback_id t₀.G).1 ⟨x, rfl⟩⟩ h hact hPP
  exact ⟨PP, cub, hs, hadj, hprim, m, hm⟩

end PositivityTheory.Member.SiegelModularCharts.K6

namespace PositivityTheory.Member.SiegelModularCharts

end PositivityTheory.Member.SiegelModularCharts
