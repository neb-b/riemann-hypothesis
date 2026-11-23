module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
public import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsFiniteEtaleCoverConstantTorsion
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSymmetricLinearisationSquareDiagonalBundleStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0015

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPolAVFiniteTypeSubring
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory.KeyTf

private theorem spMap_subtype_comp_inclusion' {S : Type} [CommRing S] {R R' : Subring S} (h : R ≤ R') :
    spMap R'.subtype ≫ spMap (Subring.inclusion h) = spMap R.subtype := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

private theorem exists_lift_to_pullback_grpPullback {S : Type} [CommRing S] {R R' : Subring S} (h : R ≤ R') (A : Over (Sp S))
    [GrpObj A] (A₀ : Over (Sp R)) [GrpObj A₀] (φ : A.left ⟶ A₀.left) (H : IsGrpPullback A A₀ (spMap R.subtype) φ) :
    ∃ φ₁ : A.left ⟶ ((Over.pullback (spMap (Subring.inclusion h))).obj A₀).left,
      φ₁ ≫ pullback.fst A₀.hom (spMap (Subring.inclusion h)) = φ ∧
      IsGrpPullback A ((Over.pullback (spMap (Subring.inclusion h))).obj A₀) (spMap R'.subtype) φ₁ := by
  have w : φ ≫ A₀.hom = (A.hom ≫ spMap R'.subtype) ≫ spMap (Subring.inclusion h) := by
    rw [Category.assoc, spMap_subtype_comp_inclusion' h]
    exact H.1.w
  refine ⟨pullback.lift φ (A.hom ≫ spMap R'.subtype) w, pullback.lift_fst _ _ _, ?_⟩
  refine IsGrpPullback.cancel (isGrpPullback_pullback A₀ (spMap (Subring.inclusion h))) ?_ ?_
  · exact H.congr (spMap_subtype_comp_inclusion' h).symm (pullback.lift_fst _ _ _).symm
  · exact pullback.lift_snd _ _ _

theorem exists_model_of_le {S : Type} [CommRing S] {R R' : Subring S} (h : R ≤ R') (A : Over (Sp S)) [GrpObj A]
    (A₀ : Over (Sp R)) [GrpObj A₀] (φ : A.left ⟶ A₀.left) (H : IsGrpPullback A A₀ (spMap R.subtype) φ) :
    ∃ (A₁ : Over (Sp R')) (_ : GrpObj A₁) (φ₁ : A.left ⟶ A₁.left) (π : A₁.left ⟶ A₀.left), φ₁ ≫ π = φ ∧
      IsGrpPullback A₁ A₀ (spMap (Subring.inclusion h)) π ∧ IsGrpPullback A A₁ (spMap R'.subtype) φ₁ := by
  obtain ⟨φ₁, e, H₁⟩ := exists_lift_to_pullback_grpPullback h A A₀ φ H
  exact ⟨_, inferInstance, φ₁, _, e, isGrpPullback_pullback A₀ _, H₁⟩

private theorem lbIso_pull_comp_theta_law {X Y Z : Scheme.{0}} {L : LB Z} (hL : L.IsLB) (φ₁ : X ⟶ Y) (π : Y ⟶ Z) :
    LBIso (L.pull (φ₁ ≫ π)) ((L.pull π).pull φ₁) := by
  refine LBLimit.lbIso_of_refinement _ _ (LB.isLB_pull hL _) (fun a _ => a ⟨⟩ ⟨⟩) ?_ ?_
  · intro a y hy
    have h1 := (mem_pull (L := L.pull π)).1 hy
    have h2 := (mem_pull (L := L)).1 h1
    exact (mem_pull (L := L)).2 h2
  · intro a b y ha hb
    have ha' := (mem_pull (L := L)).1 ((mem_pull (L := L.pull π)).1 ha)
    have hb' := (mem_pull (L := L)).1 ((mem_pull (L := L.pull π)).1 hb)
    rw [gm_pull_g (L.pull π) φ₁ (𝟙 X) y a b ha hb, gm_pull_g L π (𝟙 X ≫ φ₁) y (a ⟨⟩) (b ⟨⟩)
      ((mem_pull (L := L.pull π)).1 ha) ((mem_pull (L := L.pull π)).1 hb),
      gm_pull_g L (φ₁ ≫ π) (𝟙 X) y (fun _ => a ⟨⟩ ⟨⟩) (fun _ => b ⟨⟩ ⟨⟩) ((mem_pull (L := L)).2 ha')
      ((mem_pull (L := L)).2 hb')]
    simp only [Category.assoc]

theorem lbIso_pull_pull_of_comp {X Y Z : Scheme.{0}} {M : LB X} {L : LB Z} (hM : M.IsLB) (hL : L.IsLB)
    {φ : X ⟶ Z} {φ₁ : X ⟶ Y} {π : Y ⟶ Z} (e : φ₁ ≫ π = φ) (H : LBIso M (L.pull φ)) :
    LBIso M ((L.pull π).pull φ₁) := by
  subst e
  exact LBIso.trans hM (LB.isLB_pull hL _) (LB.isLB_pull (LB.isLB_pull hL _) _) H (lbIso_pull_comp_theta_law hL φ₁ π)

private theorem exists_intermediate_abelian_model_factorization {S : Type} [CommRing S] {g : ℕ} {R R' : Subring S} (h : R ≤ R') (A : Over (Sp S))
    [GrpObj A] (A₀ : Over (Sp R)) [GrpObj A₀] (φ : A.left ⟶ A₀.left) (H : IsGrpPullback A A₀ (spMap R.subtype) φ)
    (hab : IsAbelianScheme A₀) (hpr : IsProjOver A₀.hom) (hsm : SmoothOfRelativeDimension g A₀.hom) :
    ∃ (A₁ : Over (Sp R')) (_ : GrpObj A₁) (φ₁ : A.left ⟶ A₁.left) (π : A₁.left ⟶ A₀.left), φ₁ ≫ π = φ ∧
      IsGrpPullback A₁ A₀ (spMap (Subring.inclusion h)) π ∧ IsGrpPullback A A₁ (spMap R'.subtype) φ₁ ∧
      IsAbelianScheme A₁ ∧ IsProjOver A₁.hom ∧ SmoothOfRelativeDimension g A₁.hom := by
  obtain ⟨φ₁, e, H₁⟩ := exists_lift_to_pullback_grpPullback h A A₀ φ H
  have hp := isGrpPullback_pullback A₀ (spMap (Subring.inclusion h))
  refine ⟨_, inferInstance, φ₁, _, e, hp, H₁, ?_, ?_, ?_⟩
  · exact Out.TLinPf.isAb_pullback _ A₀ hab
  · exact ProjSpace.isProjOver_of_isPullback_spMap (Subring.inclusion h) hp.1 hpr
  · exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hp.1 hsm

theorem exists_polAV_finiteType_subring :
    ∀ (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] (P : Out.PolAV (Sp S)), ∃ (R : Subring S) (P₀ : Out.PolAV (Sp R)) (φ : P.A.left ⟶ P₀.A.left), Algebra.FiniteType ℤ R ∧ P₀.g = P.g ∧ IsGrpPullback P.A P₀.A (spMap R.subtype) φ ∧ LBIso P.L (P₀.L.pull φ) := by
  classical
  intro S _ _ _ P
  obtain ⟨R₀, A₀, _, φ₀, hR₀, hab₀, hsm₀, hpr₀, H₀⟩ := exists_projective_abelian_model S P
  have := hab₀.proper
  obtain ⟨F₁, hF₁⟩ := LBLimit.lb_descends_to_fg_subring S R₀ P.A.left A₀.left P.A.hom A₀.hom φ₀ P.L H₀.1 P.isLB
  obtain ⟨R₁, hle₁, hsub₁, hR₁⟩ := exists_finiteType_subring_adjoin S R₀ F₁ hR₀
  obtain ⟨A₁, _, φ₁, π₁, e₁, Hπ₁, H₁, hab₁, hpr₁, hsm₁⟩ := exists_intermediate_abelian_model_factorization hle₁ P.A A₀ φ₀ H₀ hab₀ hpr₀ hsm₀
  obtain ⟨L₁, hL₁, hiso₁⟩ := hF₁ R₁ hle₁ hsub₁ A₁.left A₁.hom π₁ φ₁ Hπ₁.1 e₁ H₁.1.w
  have : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing ℤ R₁
  obtain ⟨F₂, hF₂⟩ := AmpleSubring.relAmple_subring S R₁ P A₁ φ₁ L₁ hab₁ hpr₁ hL₁ H₁ hiso₁
  obtain ⟨F₃, hF₃⟩ := rigidified_sym_descend_to_subring S R₁ P A₁ φ₁ L₁ hab₁ hL₁ H₁ hiso₁
  obtain ⟨R₂, hle₂, hsub₂, hR₂⟩ := exists_finiteType_subring_adjoin S R₁ (F₂ ∪ F₃) hR₁
  rw [Finset.coe_union, Set.union_subset_iff] at hsub₂
  obtain ⟨A₂, _, φ₂, π₂, e₂, Hπ₂, H₂, hab₂, hpr₂, hsm₂⟩ := exists_intermediate_abelian_model_factorization hle₂ P.A A₁ φ₁ H₁ hab₁ hpr₁ hsm₁
  have ha₂ := hF₂ R₂ hle₂ hsub₂.1 A₂ π₂ Hπ₂
  have hrs₂ := hF₃ R₂ hle₂ hsub₂.2 A₂ π₂ Hπ₂
  have hL₂ := LB.isLB_pull hL₁ π₂
  have hiso₂ := lbIso_pull_pull_of_comp P.isLB hL₁ e₂ hiso₁
  have : IsNoetherianRing R₂ := Algebra.FiniteType.isNoetherianRing ℤ R₂
  obtain ⟨F₄, hF₄⟩ := exists_finset_kTriv_of_subring S R₂ P A₂ φ₂ (L₁.pull π₂) hab₂ hL₂ ha₂ H₂ hiso₂
  obtain ⟨R₃, hle₃, hsub₃, hR₃⟩ := exists_finiteType_subring_adjoin S R₂ F₄ hR₂
  obtain ⟨A₃, _, φ₃, π₃, e₃, Hπ₃, H₃, hab₃, hpr₃, hsm₃⟩ := exists_intermediate_abelian_model_factorization hle₃ P.A A₂ φ₂ H₂ hab₂ hpr₂ hsm₂
  have hk₃ := hF₄ R₃ hle₃ hsub₃ A₃ π₃ Hπ₃
  have hL₃ := LB.isLB_pull hL₂ π₃
  have hpol := pol_pull _ _ A₂ A₃ _ π₃ _ _ hL₂ hL₃ hab₂ Hπ₃ (PolBaseChange.lbIso_refl hL₃)
  have hiso₃ := lbIso_pull_pull_of_comp P.isLB hL₂ e₃ hiso₂
  refine ⟨R₃,
    { A := A₃
      isAb := hab₃
      g := P.g
      smoothDim := hsm₃
      L := (L₁.pull π₂).pull π₃
      isLB := hL₃
      rigid := PolBaseChange.rigidified_pull Hπ₃ hrs₂.1
      sym := PolBaseChange.sym_pull Hπ₃ hrs₂.2
      ample := hpol.2.1 ha₂
      ktriv := hk₃ }, φ₃, hR₃, rfl, H₃, hiso₃⟩

end GlobalTheory.KeyTf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSymmetricSqrtPrincipalSiegelFiniteEtale
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.SiegelSqrt
open GlobalTheory.SiegelPullComp GlobalTheory.SiegelRingChange

section Transfer
variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}

def Labels {C : Type} [Group C] (A : Over S) [GrpObj A] (n : ℕ) (i : C →* (𝟙_ (Over S) ⟶ A)) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S),
    (∀ x : Over.mk t ⟶ A, x ^ n = 1 ↔ ∃ c, x = toUnit _ ≫ i c) ∧ ∀ c, toUnit (Over.mk t) ≫ i c = 1 → c = 1

theorem exists_pull_labels (h : IsGrpPullback A' A f φ) {C : Type} [Group C] (n : ℕ)
    (i : C →* (𝟙_ (Over S) ⟶ A)) (hi : Labels A n i) :
    ∃ i' : C →* (𝟙_ (Over S') ⟶ A'), (∀ c, (i' c).left ≫ φ = f ≫ (i c).left) ∧ Labels A' n i' := by
  have hmul : ∀ x y : 𝟙_ (Over S) ⟶ A, GlobalTheory.SiegelPull.secPull h (x * y) =
      GlobalTheory.SiegelPull.secPull h x * GlobalTheory.SiegelPull.secPull h y := by
    intro x y
    apply GlobalTheory.SiegelPull.push_injective h (𝟙_ (Over S'))
    rw [map_mul, GlobalTheory.SiegelPull.push_secPull', GlobalTheory.SiegelPull.push_secPull', GlobalTheory.SiegelPull.push_secPull',
      MonObj.comp_mul]
  refine ⟨MonoidHom.mk' (fun c => GlobalTheory.SiegelPull.secPull h (i c)) (fun a b => by rw [map_mul]; exact hmul _ _),
    fun c => GlobalTheory.SiegelPull.secPull_left h (i c), ?_⟩
  intro k _ _ t
  have hp := hi k (t ≫ f)
  have hinj := GlobalTheory.SiegelPull.push_injective h (Over.mk t)
  have key : ∀ c, pushHom h (Over.mk t) (toUnit (Over.mk t) ≫ GlobalTheory.SiegelPull.secPull h (i c)) =
      toUnit (Over.mk (t ≫ f)) ≫ i c := fun c => GlobalTheory.SiegelPull.push_secPull h (i c) (Over.mk t)
  refine ⟨fun x => ⟨fun hx => ?_, ?_⟩, fun c hc => hp.2 c ?_⟩
  · have hpx : pushHom h (Over.mk t) x ^ n = 1 := by rw [← map_pow, hx, map_one]
    obtain ⟨c, hc⟩ := (hp.1 (pushHom h (Over.mk t) x)).1 hpx
    exact ⟨c, hinj ((key c).symm ▸ hc)⟩
  · rintro ⟨c, rfl⟩
    apply hinj
    rw [map_pow, map_one]
    exact (hp.1 _).2 ⟨c, key c⟩
  · rw [← key c]
    have hc' : toUnit (Over.mk t) ≫ GlobalTheory.SiegelPull.secPull h (i c) = 1 := hc
    rw [hc', map_one]

end Transfer

section Sieg
variable {h k : ℕ} {o o' : Type} [CommRing o] [CommRing o'] {ζ : o} {ζ' : o'} {S S' S'' : Scheme.{0}}
  {s : S ⟶ Sp o} {s' : S' ⟶ Sp o'}

theorem diag_isLB (c : SiegPre h k ζ s) : c.diag.IsLB := by
  have pull_isLB {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : Y ⟶ X) : (L.pull F).IsLB := by
    refine { cover := top_le_iff.1 ?_, g_self := ?_, cocycle := ?_ }
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hL (F y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 Y) y _ hy, map_one, gm_pull_g L F (𝟙 Y) y J J hy hy]
      exact gm_self hL _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_pull_g L F (𝟙 Y) y I J hy.1.1 hy.1.2,
        gm_pull_g L F (𝟙 Y) y J K hy.1.2 hy.2, gm_pull_g L F (𝟙 Y) y I K hy.1.1 hy.2]
      exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  unfold SiegPre.diag
  exact pull_isLB c.isLB _

theorem diag_iso {c : SiegPre h k ζ s} {c' : SiegPre h k ζ' s'} {φ : c'.A.left ⟶ c.A.left}
    {φ₂ : (G2 c'.A).left ⟶ (G2 c.A).left} (hs : IsSquare φ φ₂) (hw : LBIso c'.P (c.P.pull φ₂)) :
    LBIso c'.diag (c.diag.pull φ) := by
  unfold SiegPre.diag
  exact GlobalTheory.SiegelPull.diag_iso hs hw

theorem sqOf_of_pb {o₁ : Type} [CommRing o₁] {ζ₁ : o₁} {s₁ : S' ⟶ Sp o₁} {c₁ : SiegPre h k ζ₁ s₁}
    {c : SiegPre h k ζ s} {f : S' ⟶ S} {g : S'' ⟶ S'} {P : Out.PolAV S''} {φ : P.A.left ⟶ c₁.A.left}
    (hP : SqOf P c₁ g φ) (hc : SiegPB c₁ c f) : ∃ ψ, SqOf P c (g ≫ f) ψ := by
  have pull_isLB {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : Y ⟶ X) : (L.pull F).IsLB := by
    refine { cover := top_le_iff.1 ?_, g_self := ?_, cocycle := ?_ }
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hL (F y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 Y) y _ hy, map_one, gm_pull_g L F (𝟙 Y) y J J hy hy]
      exact gm_self hL _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_pull_g L F (𝟙 Y) y I J hy.1.1 hy.1.2,
        gm_pull_g L F (𝟙 Y) y J K hy.1.2 hy.2, gm_pull_g L F (𝟙 Y) y I K hy.1.1 hy.2]
      exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  have hLam : (abelian₂ P.A P.L).IsLB := by
    unfold abelian₂ cubeLB
    exact ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ P.isLB _ _
  obtain ⟨hPb, hg, φ₂', hsq', hiso'⟩ := hP
  obtain ⟨φ₁, φ₂, hpb₁, hsq₁, hiso₁, -⟩ := hc
  refine ⟨φ ≫ φ₁, hPb.comp hpb₁, hg, φ₂' ≫ φ₂, ⟨?_, ?_⟩, ?_⟩
  · rw [Category.assoc, hsq₁.1, ← Category.assoc, hsq'.1, Category.assoc]
  · rw [Category.assoc, hsq₁.2, ← Category.assoc, hsq'.2, Category.assoc]
  · exact LBIso.trans hLam (pull_isLB c₁.isLB _) (pull_isLB c.isLB _) hiso'
      (LBIso.trans (pull_isLB c₁.isLB _) (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _)
        (GlobalTheory.SiegelPullComp.iso_pull φ₂' hiso₁) (GlobalTheory.SiegelPullComp.iso_pull_pull c.isLB φ₂ φ₂'))

end Sieg

theorem pull_sieg {h k : ℕ} {o : Type} [CommRing o] {ζ : o} {S S' : Scheme.{0}} {s : S ⟶ Sp o} (s' : S' ⟶ Sp o)
    (f : S' ⟶ S) (hf : f ≫ s = s') (c : SiegPre h k ζ s) (hc : c.Principal) :
    ∃ c' : SiegPre h k ζ s', SiegPB c' c f ∧ c'.Principal := by
  obtain ⟨⟨c', hc'⟩, hpr⟩ := GlobalTheory.siegPre_pullback h k o ζ S S' s s' f c hf
  exact ⟨c', hc', hpr c' hc' hc⟩

theorem isUnit_two_sections (R : Type) [CommRing R] [Algebra ℚ R] : IsUnit ((2 : ℕ) : Γ(Sp R, ⊤)) := by
  have h2 : IsUnit ((2 : ℕ) : R) := by
    have hq : IsUnit ((2 : ℕ) : ℚ) := isUnit_iff_ne_zero.mpr (by norm_num)
    have := hq.map (algebraMap ℚ R)
    rwa [map_natCast] at this
  have := h2.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  rwa [map_natCast] at this

private theorem exists_ringHom_spMap_eq {R o : Type} [CommRing R] [CommRing o] (g : Sp R ⟶ Sp o) :
    ∃ β : o →+* R, spMap β = g :=
  ⟨(Spec.preimage g).hom, by unfold spMap; simp⟩

private theorem spMap_comp_var {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

theorem exists_sqrt : Out.Laws → ∀ (h k : ℕ) (o : Type) [CommRing o] (ζ : o) (R : Type) [CommRing R] [Algebra ℚ R] [IsNoetherianRing R] (S : Scheme.{0}) (s : S ⟶ Sp o) (c : SiegPre h k ζ s) (f : Sp R ⟶ S), 2 ≤ k → IsUnit ζ → c.Principal → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (P : Out.PolAV (Sp R₁)) (φ : P.A.left ⟶ c.A.left), (Module.Finite R R₁ ∧ Algebra.Etale R R₁ ∧ Module.FaithfullyFlat R R₁) ∧ SqOf P c (spMap (algebraMap R R₁) ≫ f) φ ∧ TorsConst P.A 2 := by
  intro hL h k o _ ζ R _ _ _ S s c f hk hζ hc
  have pull_isLB {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (F : Y ⟶ X) : (L.pull F).IsLB := by
    refine { cover := top_le_iff.1 ?_, g_self := ?_, cocycle := ?_ }
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hL (F y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 Y) y _ hy, map_one, gm_pull_g L F (𝟙 Y) y J J hy hy]
      exact gm_self hL _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_pull_g L F (𝟙 Y) y I J hy.1.1 hy.1.2,
        gm_pull_g L F (𝟙 Y) y J K hy.1.2 hy.2, gm_pull_g L F (𝟙 Y) y I K hy.1.1 hy.2]
      exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  have two : ∀ (T : Type) [CommRing T] [Algebra ℚ T], IsUnit ((2 : ℕ) : T) := fun T _ _ => by
    have hq : IsUnit ((2 : ℕ) : ℚ) := isUnit_iff_ne_zero.mpr (by norm_num)
    have := hq.map (algebraMap ℚ T)
    rwa [map_natCast] at this
  have sq2 : ∀ x : Multiplicative (Fin (2 * h) → ZMod 2), x ^ 2 = 1 := fun x => by
    apply Multiplicative.toAdd.injective
    funext j
    rw [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, Nat.cast_ofNat,
      show (2 : ZMod 2) = 0 from rfl, zero_mul]

  obtain ⟨β, hβ⟩ := exists_ringHom_spMap_eq (f ≫ s)
  obtain ⟨c₁, hpb₁, hc₁⟩ := pull_sieg (spMap β) f hβ.symm c hc
  have sm₁ := _root_.GlobalTheory.SiegDim.smoothOfRelativeDimension hL h k o ζ R β c₁ hk hζ

  obtain ⟨R₁, _, _, ⟨fin₁, et₁, ff₁⟩, lab₁⟩ := _root_.GlobalTheory.TorsionCover.exists_torsion_basis_cover R c₁.A h 2 c₁.ab sm₁ (two R)
  haveI : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing R R₁
  letI : Algebra ℚ R₁ := ((algebraMap R R₁).comp (algebraMap ℚ R)).toAlgebra
  obtain ⟨c₂, hpb₂, hc₂⟩ := pull_sieg (spMap ((algebraMap R R₁).comp β)) (spMap (algebraMap R R₁))
    (spMap_comp_var β (algebraMap R R₁)).symm c₁ hc₁
  obtain ⟨φ₂, φ₂₂, hg₂, hsq₂, hiso₂, hlev₂⟩ := hpb₂
  obtain ⟨i, hi⟩ := lab₁ c₂.A φ₂ hg₂

  obtain ⟨R₂, _, _, ⟨fin₂, et₂, ff₂⟩, H91⟩ := GlobalTheory.T.exists_symmetric_linearisation_square_diagonalBundle hL h k o ζ R₁ ((algebraMap R R₁).comp β) c₂ h i hc₂
  haveI : IsNoetherianRing R₂ := Algebra.FiniteType.isNoetherianRing R₁ R₂
  letI : Algebra ℚ R₂ := ((algebraMap R₁ R₂).comp (algebraMap ℚ R₁)).toAlgebra
  obtain ⟨c₃, hpb₃, hc₃⟩ := pull_sieg (spMap ((algebraMap R₁ R₂).comp ((algebraMap R R₁).comp β)))
    (spMap (algebraMap R₁ R₂))
    (spMap_comp_var ((algebraMap R R₁).comp β) (algebraMap R₁ R₂)).symm c₂ hc₂
  obtain ⟨φ₃, φ₃₂, hg₃, hsq₃, hiso₃, hlev₃⟩ := hpb₃
  obtain ⟨i₃, hi₃l, hi₃⟩ := exists_pull_labels hg₃ 2 i hi
  have hLlb : (lbPow (c₂.diag.pull φ₃) 2).IsLB := isLB_lbPow (pull_isLB (diag_isLB c₂) _) 2
  obtain ⟨u, j, hu⟩ := H91 c₃.A φ₃ i₃ _ hg₃ hi₃l rfl

  obtain ⟨hmon, hfin, het, hsurj⟩ :=
    GlobalTheory.abelianScheme_id_pow_finite_etale_surjective (Sp R₂) c₃.A 2 c₃.ab (isUnit_two_sections R₂)
  obtain ⟨M, hM, hLM, hMinv⟩ := GlobalTheory.T.exists_descent_symmetric_linearised_bundle (Sp R₂) c₃.A c₃.A ((𝟙 c₃.A) ^ 2) _ i₃ _ hLlb hmon hfin het hsurj
    (fun x => by rw [MonObj.comp_pow, Category.comp_id, ← map_pow, sq2, map_one])
    (fun k _ _ t => ⟨fun x => by rw [MonObj.comp_pow, Category.comp_id]; exact (hi₃ k t).1 x, (hi₃ k t).2⟩) u j hu
  have hLam := _root_.GlobalTheory.LamOfDouble.lam_iso_of_pull_two hL h k o ζ R₂ _ c₃ M hc₃ hM
    (LBIso.trans (isLB_lbPow (diag_isLB c₃) 2) hLlb (pull_isLB hM _) (lbIso_lbPow (diag_iso hsq₃ hiso₃) 2) hLM)
  obtain ⟨P, φP, hP⟩ := _root_.GlobalTheory.SymRoot.exists_polAV_sqOf hL h k o ζ R₂ _ c₃ M hc₃ (_root_.GlobalTheory.SiegDim.smoothOfRelativeDimension hL h k o ζ R₂ _ c₃ hk hζ) hM hLam hMinv

  obtain ⟨ψ₂, hψ₂⟩ := sqOf_of_pb hP ⟨φ₃, φ₃₂, hg₃, hsq₃, hiso₃, hlev₃⟩
  obtain ⟨ψ₁, hψ₁⟩ := sqOf_of_pb hψ₂ ⟨φ₂, φ₂₂, hg₂, hsq₂, hiso₂, hlev₂⟩
  obtain ⟨ψ₀, hψ₀⟩ := sqOf_of_pb hψ₁ hpb₁
  obtain ⟨iP, -, hiP⟩ := exists_pull_labels hP.1 2 i₃ hi₃
  letI : Algebra R R₂ := ((algebraMap R₁ R₂).comp (algebraMap R R₁)).toAlgebra
  haveI : IsScalarTower R R₁ R₂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  refine ⟨R₂, inferInstance, inferInstance, P, ψ₀, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · first | exact Module.Finite.trans R₁ R₂ | infer_instance
  · first | exact Algebra.Etale.comp R R₁ R₂ | infer_instance
  · first | exact Module.FaithfullyFlat.trans R R₁ R₂ | infer_instance
  · have e : spMap (algebraMap R R₂) ≫ f =
        ((𝟙 _ ≫ spMap (algebraMap R₁ R₂)) ≫ spMap (algebraMap R R₁)) ≫ f := by
      rw [Category.id_comp, ← spMap_comp_var]
    rw [e]
    exact hψ₀
  · intro K _ _ x y hy
    obtain ⟨a, rfl⟩ := ((hiP K x).1 y).1 hy
    exact ⟨iP a, by rw [← map_pow, sq2, map_one], rfl⟩

end GlobalTheory.SiegelSqrt
end
end

