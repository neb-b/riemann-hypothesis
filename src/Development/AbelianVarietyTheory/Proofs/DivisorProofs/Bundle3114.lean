module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2133
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3109
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3084
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3107
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2110
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2470
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0126
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3076
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2579
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2803
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3110
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2277
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2164
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsPolarisationBundleLift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UPel.HT.PolLift
open GlobalTheory.AbDual GlobalTheory.CechPic

theorem lbIso_symm {X : Scheme.{0}} {P Q : LB X} (hP : P.IsLB) (hQ : Q.IsLB) (e : LBIso P Q) : LBIso Q P :=
  (cls_eq_iff hQ hP).1 ((cls_eq_iff hP hQ).2 e).symm

theorem gen_comp {X Y Z : Scheme.{0}} {P : LB X} (hP : P.IsLB) (f : Y ⟶ X) (g : Z ⟶ Y)
    (h : ∃ t : (P.pull f).Gen, t.IsGen) : ∃ t : (P.pull (g ≫ f)).Gen, t.IsGen := by
  refine (cls_eq_zero_iff (pull_isLB hP _)).1 ?_
  rw [cls_pull hP, pull_comp, ← cls_pull hP _ (pull_isLB hP _), (cls_eq_zero_iff (pull_isLB hP _)).2 h, map_zero]

theorem gen_pull_pull {X Y Z : Scheme.{0}} {P : LB X} (hP : P.IsLB) (a : Y ⟶ X) (x : Z ⟶ Y)
    (h : ∃ t : (P.pull (x ≫ a)).Gen, t.IsGen) : ∃ t : ((P.pull a).pull x).Gen, t.IsGen := by
  refine (cls_eq_zero_iff (pull_isLB (pull_isLB hP _) _)).1 ?_
  rw [cls_pull (pull_isLB hP _), cls_pull hP, ← pull_comp, ← cls_pull hP _ (pull_isLB hP _)]
  exact (cls_eq_zero_iff (pull_isLB hP _)).2 h

theorem gen_left {S : Scheme.{0}} {A : Over S} [GrpObj A] (P : LB (A ⊗ A).left) (hP : P.IsLB) (u : A ⟶ A) [IsMonHom u]
    (h₁ : ∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen)
    (h₂ : ∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) :
    (∃ t : ((P.pull (lift (fst A A ≫ u) (snd A A)).left).pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧
    (∃ t : ((P.pull (lift (fst A A ≫ u) (snd A A)).left).pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) := by
  refine ⟨gen_pull_pull hP _ _ ?_, gen_pull_pull hP _ _ ?_⟩
  · rw [← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd, MonObj.one_comp]
    exact h₁
  · have e : lift (𝟙 A) (1 : A ⟶ A) ≫ lift (fst A A ≫ u) (snd A A) = u ≫ lift (𝟙 A) (1 : A ⟶ A) := by
      rw [comp_lift, lift_fst_assoc, lift_snd, comp_lift, Category.id_comp, Category.comp_id, MonObj.comp_one]
    rw [← Over.comp_left, e, Over.comp_left]
    exact gen_comp hP _ _ h₂

theorem sq_left {S S' : Scheme.{0}} {A₀ : Over S'} {A : Over S} [GrpObj A₀] [GrpObj A] {i : A₀.left ⟶ A.left}
    {l : (A₀ ⊗ A₀).left ⟶ (A ⊗ A).left} (l₁ : l ≫ (fst A A).left = (fst A₀ A₀).left ≫ i)
    (l₂ : l ≫ (snd A A).left = (snd A₀ A₀).left ≫ i) (u₀ : A₀ ⟶ A₀) (u : A ⟶ A) (w : u₀.left ≫ i = i ≫ u.left) :
    (lift (fst A₀ A₀ ≫ u₀) (snd A₀ A₀)).left ≫ l = l ≫ (lift (fst A A ≫ u) (snd A A)).left := by
  apply GlobalTheory.AbDual.left_ext
  · rw [Category.assoc, l₁, Category.assoc, GlobalTheory.AbDual.lift_left_fst, ← Category.assoc, GlobalTheory.AbDual.lift_left_fst,
      Over.comp_left, Over.comp_left, Category.assoc, w, ← Category.assoc, ← l₁, Category.assoc]
  · rw [Category.assoc, l₂, Category.assoc, GlobalTheory.AbDual.lift_left_snd, ← Category.assoc, GlobalTheory.AbDual.lift_left_snd, l₂]

theorem exists_pol_lift : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∀ (A : Over (Sp C)) [GrpObj A] [IsCommMonObj A] (i : o₀.A.left ⟶ A.left) (h : IsGrpPullback o₀.A A (spMap π) i), IsAbelianScheme A → ∀ (act : GlobalTheory.UPel.HT.OActN D.O A), (∀ c, (o₀.act.act c).left ≫ i = i ≫ (act.act c).left) → (∀ φ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ → ∀ x ∈ liftFil (divided₂ hsq) h, ∀ y ∈ liftFil (divided₂ hsq) h, φ x y = 0) → ∃ (P : LB (G2 A).left) (φ₂ : (G2 o₀.A).left ⟶ (G2 A).left), P.IsLB ∧ (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) ∧ LBIso P (P.pull (lift (snd A A) (fst A A)).left) ∧ Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) ∧ (∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over (Sp C)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1) ∧ (∀ c : D.O, LBIso (P.pull (lift (fst A A ≫ act.act c) (snd A A)).left) (P.pull (lift (fst A A) (snd A A ≫ act.act (D.star c).unop)).left)) ∧ IsSquare i φ₂ ∧ LBIso o₀.P (P.pull φ₂) := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR o₀ A _ _ i h hA act hact hiso
  haveI : Nontrivial C₀ := by
    refine ⟨⟨0, 1, fun h ↦ ?_⟩⟩
    have h1 : (1 : C) ∈ RingHom.ker π := by rw [RingHom.mem_ker, map_one]; exact h.symm
    have h2 : (1 : C) ∈ RingHom.ker π ^ 2 := by
      rw [pow_two]; simpa using Ideal.mul_mem_mul h1 h1
    rw [hsq] at h2
    exact one_ne_zero ((Submodule.mem_bot C).1 h2)
  let κ := divided₂ hsq
  have hκ : IsNilDP κ := isDPNilpotent_squareZero hsq
  have ADR : GlobalTheory.Published.AbelianDeRham := GlobalTheory.abelianDeRham
  have ADC : GlobalTheory.Published.AbelianDualCrystal := GlobalTheory.abelianDualCrystal
  have GD : GlobalTheory.Published.GrothendieckDeformation :=
    GlobalTheory.Published.grothendieckDeformation_of_lifting GlobalTheory.abelianDeRham GlobalTheory.abelianScheme_hom_lifting_nilpotent_dividedPowers
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim C A hA
  obtain ⟨l, l₁, l₂⟩ := exists_prod_pullback h h
  have hsq2 : Geo.Tor.IsSquare i l := ⟨l₁, l₂⟩
  have C' := GlobalTheory.Published.AbelianDualCrystal.cupSquare_crys_prod ADR.1 ADC.2 hκ hπ rfl hA hg hA hg h h
  obtain ⟨φ₀, hφ₀⟩ := exists_isCorrForm C' o₀.isLB o₀.rig₁ o₀.rig₂
  have hΔ₀ : (o₀.P.pull (lift (𝟙 o₀.A) (𝟙 o₀.A)).left).IsLB := pull_isLB o₀.isLB _
  obtain ⟨P, hP, t₁, t₂, -, -, eP⟩ := GlobalTheory.BirigidLift.exists_lift GD ADR ADC hκ hπ rfl hA hg hA hg h h l₁ l₂
    hΔ₀ o₀.ample hΔ₀ o₀.ample o₀.isLB o₀.rig₁ o₀.rig₂ hφ₀ (hiso φ₀ hφ₀)
  have wΔ : (lift (𝟙 o₀.A) (𝟙 o₀.A)).left ≫ l = i ≫ (lift (𝟙 A) (𝟙 A)).left := by
    apply GlobalTheory.AbDual.left_ext
    · rw [Category.assoc, l₁, Category.assoc, GlobalTheory.AbDual.lift_left_fst, ← Category.assoc, GlobalTheory.AbDual.lift_left_fst]
      simp
    · rw [Category.assoc, l₂, Category.assoc, GlobalTheory.AbDual.lift_left_snd, ← Category.assoc, GlobalTheory.AbDual.lift_left_snd]
      simp
  have hL : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have aL : Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) := by
    haveI := hA.smooth
    exact _root_.GlobalTheory.AmpleNilThickening.relAmple_of_isNilDP C C₀ (RingHom.ker π) κ hκ π hπ rfl A o₀.A i h.1 inferInstance _ _
      hL hΔ₀ (GlobalTheory.RMDeform.lbIso_pull_square hP o₀.isLB eP _ _ i wΔ) o₀.ample
  have symm := _root_.GlobalTheory.BirigidLift.symm_of_lift GD ADC C C₀ (RingHom.ker π) κ hκ π hπ rfl g o₀.A A i h hA hg l hsq2
    _ hL aL o₀.P o₀.isLB o₀.symm P hP t₁ t₂ eP
  have ros : ∀ c : D.O, LBIso (P.pull (lift (fst A A ≫ act.act c) (snd A A)).left)
      (P.pull (lift (fst A A) (snd A A ≫ act.act (D.star c).unop)).left) := by
    intro c
    haveI := o₀.act.hom c
    haveI := act.hom c
    haveI := o₀.act.hom (D.star c).unop
    haveI := act.hom (D.star c).unop
    have hQ := pull_isLB hP (lift (fst A A ≫ act.act c) (snd A A)).left
    have hQ₀ := pull_isLB o₀.isLB (lift (fst o₀.A o₀.A ≫ o₀.act.act c) (snd o₀.A o₀.A)).left
    obtain ⟨q₁, q₂⟩ := gen_left P hP (act.act c) t₁ t₂
    have eQ : LBIso ((P.pull (lift (fst A A ≫ act.act c) (snd A A)).left).pull l)
        (o₀.P.pull (lift (fst o₀.A o₀.A ≫ o₀.act.act c) (snd o₀.A o₀.A)).left) :=
      lbIso_symm hQ₀ (pull_isLB hQ _) (GlobalTheory.RMDeform.lbIso_pull_square hP o₀.isLB eP _ _ l
        (sq_left l₁ l₂ _ _ (hact c)))
    exact _root_.GlobalTheory.BirigidLift.pull_one_prod_of_lift GD ADC C C₀ (RingHom.ker π) κ hκ π hπ rfl g o₀.A A i h hA hg l hsq2 _ hL aL
      (o₀.act.act (D.star c).unop) (act.act (D.star c).unop) (hact _) o₀.P _ o₀.isLB hQ₀ (o₀.rosati c)
      P _ hP hQ t₁ t₂ q₁ q₂ eP eQ
  have ker : ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over (Sp C)) (x : T ⟶ A),
      (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x ^ e = 1 := by
    obtain ⟨e, he, H⟩ := o₀.kerP
    have hu : IsUnit (e : C) := by
      have := (b.unit e he).map tR
      simpa using this
    exact ⟨e, he, _root_.GlobalTheory.KerLiftUnit.ker_pow_eq_one_of_lift C C₀ π hπ hsq o₀.A A i h hA l hsq2 o₀.P P o₀.isLB hP t₁ t₂ symm aL eP e hu H⟩
  exact ⟨P, l, hP, t₁, t₂, symm, aL, ker, ros, hsq2, lbIso_symm (pull_isLB hP l) o₀.isLB eP⟩

end GlobalTheory.UPel.HT.PolLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFirstOrderHodgeEqKodairaSpencerGraph
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section
namespace GlobalTheory.HTNecessary

variable {k : Type} [Field k] {A₀ : Over (Sp k)} [GrpObj A₀] {A' : Over (Sp (DualNumber k))} [GrpObj A']
  {i : A₀.left ⟶ A'.left} {h : IsGrpPullback A₀ A' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) i}

theorem isFilLift_add {x y x' y' : HdR A₀} (e : IsFilLift h x y) (e' : IsFilLift h x' y') :
    IsFilLift h (x + x') (y + y') := by
  obtain ⟨d, hd, e⟩ := e
  obtain ⟨d', hd', e'⟩ := e'
  refine ⟨d + d', add_mem hd hd', fun c ↦ ?_⟩
  rw [LinearMap.add_apply, e, e']
  ext <;> simp

theorem isFilLift_smul {x y : HdR A₀} (e : IsFilLift h x y) (r : k) :
    IsFilLift h (r • x) (r • y) := by
  obtain ⟨d, hd, e⟩ := e
  refine ⟨algebraMap k (DualNumber k) r • d, Submodule.smul_mem _ _ hd, fun c ↦ ?_⟩
  rw [LinearMap.smul_apply, e]
  ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem isFilLift_zero : IsFilLift h (0 : HdR A₀) 0 :=
  ⟨0, zero_mem _, fun c ↦ by
    simp only [LinearMap.zero_apply, TrivSqZeroExt.inl_zero, TrivSqZeroExt.inr_zero, add_zero]⟩

theorem isFilLift_push (f₀ : A₀ ⟶ A₀) (f : A' ⟶ A') [IsMonHom f₀] [IsMonHom f] (e : i ≫ f.left = f₀.left ≫ i)
    {x y : HdR A₀} (hxy : IsFilLift h x y) :
    IsFilLift h (push (dp0 k) (𝟙 _) f₀ x) (push (dp0 k) (𝟙 _) f₀ y) := by
  obtain ⟨d, hd, e'⟩ := hxy
  have hmem := push_mem_liftFil (epsDP k) h h f₀ f e hd
  refine ⟨_, hmem, fun c ↦ ?_⟩
  have k1 : GrpMor (dp0 k) (𝟙 _) A₀ (epsDP k) (DeRham.epsRed k) A₀
      (algebraMap k (DualNumber k)) (𝟙 _) f₀.left :=
    ⟨(constMor A₀).dp, (constMor A₀).base, (homMor (dp0 k) (𝟙 _) f₀).w,
      (homMor (dp0 k) (𝟙 _) f₀).mul⟩
  have e1 := GrpMor.pull_pull (constMor A₀) (homMor (epsDP k) _ f₀) k1 (fun _ ↦ rfl) (by simp) c
  have e2 := GrpMor.pull_pull (homMor (dp0 k) (𝟙 _) f₀) (constMor A₀) k1 (fun _ ↦ rfl) rfl c
  rw [push_apply]
  show d (primPull _ _ f₀ _) = _
  erw [primPull, e1, ← e2, e']
  rfl

theorem exists_isFilLift (hA' : IsAbelianScheme A') {x : HdR A₀} (hx : x ∈ Fil A₀) : ∃ y, IsFilLift h x y := by
  obtain ⟨g, hg⟩ := GlobalTheory.KSGraph.exists_dim A' hA'
  obtain ⟨v, ⟨y, hy, -⟩, -⟩ := GlobalTheory.DeRham.ksRegular_of_isAbelianScheme _root_.GlobalTheory.abelianDeRham h hA' hg x hx
  exact ⟨y, hy⟩

theorem main : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∃ g : HdR o₀.A →ₗ[k] HdR o₀.A, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) g ∧ ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (g x) := by
  intro p _ D R _ b N _ _ k _ _ t o₀ β hβ φ hφ o' m'
  have hab₀ := o₀.ab
  have hab' := o'.ab
  have hL1 : ∀ x ∈ Fil o₀.A, ∃ y, IsFilLift m'.cart x y := fun x hx ↦ exists_isFilLift hab' hx
  have hG := GlobalTheory.KSGraph.isFilLift_iff_sub_mem k o₀.A o'.A m'.φ m'.cart hab'
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (Fil o₀.A)
  let bs := Module.Basis.ofVectorSpace k (Fil o₀.A)
  let f : Fil o₀.A →ₗ[k] HdR o₀.A := bs.constr k fun j ↦ (hL1 _ (bs j).2).choose
  have hf : ∀ x : Fil o₀.A, IsFilLift m'.cart x.1 (f x) := by
    intro x
    have hx : x ∈ Submodule.span k (Set.range bs) := by rw [bs.span_eq]; trivial
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      rw [Module.Basis.constr_basis]
      exact (hL1 _ (bs j).2).choose_spec
    | zero => simpa using isFilLift_zero
    | add x y _ _ hx hy => simpa using isFilLift_add hx hy
    | smul r x _ hx => simpa using isFilLift_smul hx r
  let g : HdR o₀.A →ₗ[k] HdR o₀.A := f ∘ₗ Submodule.linearProjOfIsCompl _ _ hC
  have hg : ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (g x) := fun x hx ↦ by
    have : Submodule.linearProjOfIsCompl _ _ hC x = ⟨x, hx⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hC ⟨x, hx⟩
    simpa [g, this] using hf ⟨x, hx⟩
  refine ⟨g, ⟨fun a x hx ↦ ?_, fun z hz ↦ ?_, fun x hx y hy ↦ ?_⟩, hg⟩
  · haveI := o₀.act.hom a
    haveI := o'.act.hom a
    have hax : GlobalTheory.HTCount.crysAct o₀ a x ∈ Fil o₀.A := by
      rw [GlobalTheory.HTCount.crysAct_apply]; exact push_mem_Fil _ hx
    have e1 : IsFilLift m'.cart (GlobalTheory.HTCount.crysAct o₀ a x) (GlobalTheory.HTCount.crysAct o₀ a (g x)) := by
      rw [GlobalTheory.HTCount.crysAct_apply]
      exact isFilLift_push (o₀.act.act a) (o'.act.act a) (m'.act a).symm (hg x hx)
    exact (hG _ hax _ _ e1).1 (hg _ hax)
  · obtain ⟨hz₀, hz⟩ := GlobalTheory.T.lieConditionHodgeSubspace_constant_lift_mem_fil p D R b N k t o₀ β hβ o' m' z hz
    simpa using (hG _ hz₀ _ _ hz).1 (hg _ hz₀)
  · exact GlobalTheory.T.harrisTaylor_firstOrder_deformation_skew p D R b N k t o₀ φ hφ o' m' x hx y hy _ _ (hg x hx) (hg y hy)

end GlobalTheory.HTNecessary
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorStructuresRepresentableSiegelBaseCha
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.UPel.HT

open GlobalTheory.SiegelPull GlobalTheory.SiegelPullComp

theorem relRep_siegel : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M e : ℕ), 3 ≤ N → N.Coprime p → 3 ≤ M → Odd M → M.Coprime p → e.Coprime p → ∀ (Y : Scheme.{0}) (s : Y ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) s), SiegKerBy c e → IsLocallyNoetherian (pullback (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R))) → ∃ (Z : Scheme.{0}) (π : Z ⟶ pullback (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R))) (u : Obj b N (π ≫ pullback.snd _ _)) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Z) ⟶ u.A)), IsSympLev u.P h M (zetaAway M) (π ≫ pullback.fst _ _ ≫ s) lev ∧ IsFinite π ∧ (∀ (T : Scheme.{0}) (g : T ⟶ Z) (t : T ⟶ Sp R) (t₁ : T ⟶ Sp (cycAway M)) (o : Obj b N t) (l : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over T) ⟶ o.A)) (hl : IsSympLev o.P h M (zetaAway M) t₁ l), (∃ m : ObjMap o u g, ∀ a, (l a).left ≫ m.φ = g ≫ (lev a).left) → SiegPB (o.toSieg hl) c (g ≫ π ≫ pullback.fst _ _)) ∧ ∀ (T : Scheme.{0}) (t₀ : T ⟶ Y) (t : T ⟶ Sp R) (t₁ : T ⟶ Sp (cycAway M)) (o : Obj b N t) (l : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over T) ⟶ o.A)) (hl : IsSympLev o.P h M (zetaAway M) t₁ l), SiegPB (o.toSieg hl) c t₀ → ∃! g : T ⟶ Z, g ≫ π ≫ pullback.fst _ _ = t₀ ∧ g ≫ π ≫ pullback.snd _ _ = t ∧ ∃ m : ObjMap o u g, ∀ a, (l a).left ≫ m.φ = g ≫ (lev a).left := by
  intro p _ D R _ b N h M e hN hNp hM hMo hMp hep Y s c hker hY
  haveI := hY
  obtain ⟨⟨c', hc'⟩, -⟩ := GlobalTheory.siegPre_pullback h M (cycAway M) (zetaAway M) Y _ s
    (pullback.fst (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R)) ≫ s) (pullback.fst _ _) c rfl
  have hker' : SiegKerBy c' e := siegKerBy_pull hc' hker
  obtain ⟨Z, π, u, φu, φ₂u, hpb, hsq, hiso, hfin, hrep⟩ :=
    GlobalTheory.T.harrisTaylor_structures_relatively_representable p D R b N hN hNp h M (cycAway M) (zetaAway M) _ _ (pullback.snd _ _) c' e hep hker'
  let lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Z) ⟶ u.A) := fun a => GlobalTheory.SiegelPull.secPull hpb (c'.lev a)
  have hlev : ∀ a, (lev a).left ≫ φu = π ≫ (c'.lev a).left := fun a => GlobalTheory.SiegelPull.secPull_left hpb _
  have hsl : IsSympLev u.P h M (zetaAway M) (π ≫ pullback.fst _ _ ≫ s) lev :=
    isSympLev_pull hpb hsq c'.isLB u.isLB hiso hlev (GlobalTheory.UPel.HT.SiegPre.isSympLev c')
  have hlevw : ∀ a, (lev a).left ≫ u.A.hom = 𝟙 Z := fun a => Over.w (lev a)
  refine ⟨Z, π, u, lev, hsl, hfin, ?_, ?_⟩
  · rintro T g t t₁ o l hl ⟨m, hm⟩
    have h1 : SiegPB (o.toSieg hl) (u.toSieg hsl) g := ⟨m.φ, m.φ₂, m.cart, m.sq, m.pol, hm⟩
    have h2 : SiegPB (u.toSieg hsl) c' π := ⟨φu, φ₂u, hpb, hsq, hiso, hlev⟩
    exact pb_comp (pb_comp hc' h2) h1
  · intro T t₀ t t₁ o l hl hS
    have hw : t₀ ≫ s ≫ spMap (Int.castRingHom (cycAway M)) = t ≫ spMap (Int.castRingHom R) :=
      specZIsTerminal.hom_ext _ _
    let g₀ : T ⟶ pullback (s ≫ spMap (Int.castRingHom (cycAway M))) (spMap (Int.castRingHom R)) :=
      pullback.lift t₀ t hw
    have hg₁ : g₀ ≫ pullback.fst _ _ = t₀ := pullback.lift_fst _ _ _
    have hg₂ : g₀ ≫ pullback.snd _ _ = t := pullback.lift_snd _ _ _
    have hS' : SiegPB (o.toSieg hl) c' g₀ := pb_cancel hc' (by rw [hg₁]; exact hS)
    obtain ⟨φ, φ₂, hφ, hsqφ, hisoφ, hlφ⟩ := hS'
    obtain ⟨z, ⟨hz, m, hm⟩, huniq⟩ := hrep T g₀ t o φ φ₂ hg₂ hφ hsqφ hisoφ
    have hlw : ∀ a, (l a).left ≫ o.A.hom = 𝟙 T := fun a => Over.w (l a)
    refine ⟨z, ⟨by rw [← Category.assoc, hz, hg₁], by rw [← Category.assoc, hz, hg₂], m, fun a => ?_⟩, ?_⟩
    · apply hpb.1.hom_ext
      · rw [Category.assoc, hm, Category.assoc, hlev, ← Category.assoc, hz]
        exact hlφ a
      · rw [Category.assoc, m.cart.1.w, ← Category.assoc, hlw, Category.assoc, hlevw]
        simp
    · rintro z' ⟨h1', h2', m', hm'⟩
      have hzπ : z' ≫ π = g₀ := pullback.hom_ext (by rw [Category.assoc, h1', hg₁])
        (by rw [Category.assoc, h2', hg₂])
      refine huniq z' ⟨hzπ, m', ?_⟩
      refine GlobalTheory.T.siegelObject_rigidity_identifications_eq h M hM _ T _ t₁ c' (o.toSieg hl) g₀ hker'.1 (m'.φ ≫ φu) φ (m'.φ₂ ≫ φ₂u) φ₂
        (by rw [← hzπ]; exact m'.cart.comp hpb) ⟨?_, ?_⟩ ?_ (fun a => ?_) hφ hsqφ hisoφ hlφ
      · exact (Category.assoc _ _ _).trans ((congrArg (m'.φ₂ ≫ ·) hsq.1).trans ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ φu) m'.sq.1).trans (Category.assoc _ _ _))))
      · exact (Category.assoc _ _ _).trans ((congrArg (m'.φ₂ ≫ ·) hsq.2).trans ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ φu) m'.sq.2).trans (Category.assoc _ _ _))))
      · exact (m'.pol.trans o.isLB (pull_isLB u.isLB _) (pull_isLB (pull_isLB c'.isLB _) _)
          (iso_pull m'.φ₂ hiso)).trans o.isLB (pull_isLB (pull_isLB c'.isLB _) _) (pull_isLB c'.isLB _)
          (iso_pull_pull c'.isLB φ₂u m'.φ₂)
      · show (l a).left ≫ m'.φ ≫ φu = g₀ ≫ (c'.lev a).left
        rw [← Category.assoc, hm' a, Category.assoc, hlev, ← Category.assoc, hzπ]

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicConjugatePullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct
open GlobalTheory.AV GlobalTheory.AV.AbVar
open scoped CategoryTheory.Obj CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FibreAV

section

variable {S : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ S) (A : Over S) [GrpObj A]

theorem pull_map_left_fst {B : Over S} (f : A ⟶ B) :
    ((Over.pullback x).map f).left ≫ pullback.fst B.hom x = pullback.fst A.hom x ≫ f.left := by
  simp only [Over.pullback_map_left, pullback.lift_fst]

theorem push_comp_map {T : Over (Sp k)} {g : T.left ⟶ S} (f : A ⟶ A)
    (e : (T ⟶ (Over.pullback x).obj A) → (Over.mk g ⟶ A)) (he : ∀ z, (e z).left = z.left ≫ pullback.fst A.hom x)
    (z : T ⟶ (Over.pullback x).obj A) : e (z ≫ (Over.pullback x).map f) = e z ≫ f := by
  apply Over.OverMorphism.ext
  rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, pull_map_left_fst, Category.assoc]

end

open GlobalTheory.AV.AbVar in
theorem fibre_av : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F] (act : OAct (𝓞 F) A) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), ∃ (B : AbVar k) (e : (Over.mk x ⟶ A) ≃* B.Pt) (ψ : 𝓞 F →+* End B), (∀ (c : 𝓞 F) (g : Over.mk x ⟶ A), e (g ≫ act.act c) = e g ≫ Hom.hom (ψ c).asHom) ∧ ∀ c : 𝓞 F, (∀ v : epsPtR x ⟶ A, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ v.left = (1 : Over.mk x ⟶ A).left → v ≫ act.act c = 1 → v = 1) → ∀ w : epsPtR (𝟙 (Sp k)) ⟶ B.X, spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ w.left = (1 : Over.mk (𝟙 (Sp k)) ⟶ B.X).left → w ≫ Hom.hom (ψ c).asHom = 1 → w = 1 := by
  intro S A _ _ hA F _ _ act k _ _ x
  letI : GrpObj ((Over.pullback x).obj A) := Functor.grpObjObj
  have h : IsGrpPullback ((Over.pullback x).obj A) A x (pullback.fst A.hom x) := isGrpPullback_pullback A x
  have hab : IsAbelianScheme ((Over.pullback x).obj A) := GlobalTheory.isAbelianScheme_pullback_obj x A hA
  obtain ⟨g, hg⟩ := GlobalTheory.AV.exists_smoothOfRelativeDimension_of_isAbelianScheme k _ hab
  let B : AbVar k := { X := (Over.pullback x).obj A, ab := hab, dim := g, smooth := hg }
  obtain ⟨e₀, he₀⟩ := GlobalTheory.LiePull.exists_pushEquiv h (𝟙_ (Over (Sp k))) x (by simp)
  have i : ptOver k (AlgebraicClosure k) ≅ 𝟙_ (Over (Sp k)) := by
    let σ : k ≃+* AlgebraicClosure k :=
      RingEquiv.ofBijective (algebraMap k (AlgebraicClosure k))
        IsAlgClosed.algebraMap_bijective_of_isIntegral
    have : IsIso (spMap (algebraMap k (AlgebraicClosure k))) := by
      change IsIso (Spec.map σ.toCommRingCatIso.hom)
      infer_instance
    exact Over.isoMk (asIso (spMap (algebraMap k (AlgebraicClosure k)))) (by
      change spMap _ ≫ 𝟙 _ = spMap _
      exact Category.comp_id _)
  let ptEquiv : (𝟙_ (Over (Sp k)) ⟶ B.X) ≃* B.Pt :=
    { toFun := fun t => i.hom ≫ t
      invFun := fun t => i.inv ≫ t
      left_inv := fun t => by simp
      right_inv := fun t => by simp
      map_mul' := fun t u => MonObj.comp_mul _ t u }
  let e : (Over.mk x ⟶ A) ≃* B.Pt := e₀.symm.trans ptEquiv
  have hm : ∀ c, IsMonHom ((Over.pullback x).map (act.act c)) := fun c => by
    have := act.hom c; infer_instance
  let ψf : 𝓞 F → (B ⟶ B) := fun c => Hom.mk (A := B) (B := B)
    ((Over.pullback x).map (act.act c)) (h := hm c)
  have hψ : ∀ c, Hom.hom (ψf c) = (Over.pullback x).map (act.act c) := fun c => rfl
  have hom_ext {f g : B ⟶ B} (hfg : Hom.hom f = Hom.hom g) : f = g := Subtype.ext hfg
  have act0 : act.act 0 = 1 := by
    have := act.add 0 0
    rw [add_zero] at this
    exact (mul_eq_left.mp this.symm)
  let ψ : 𝓞 F →+* End B :=
    { toFun := fun c => End.of (ψf c)
      map_one' := by
        apply End.ext
        change ψf 1 = 𝟙 B
        apply hom_ext
        rw [hψ, act.one, CategoryTheory.Functor.map_id, id_hom]
      map_mul' := fun a b => by
        apply End.ext
        change ψf (a * b) = ψf b ≫ ψf a
        apply hom_ext
        rw [comp_hom, hψ, hψ, hψ, mul_comm, act.mul, CategoryTheory.Functor.map_comp]
      map_zero' := by
        apply End.ext
        change ψf 0 = 0
        apply hom_ext
        rw [hψ, act0, zero_hom]
        exact CategoryTheory.Functor.map_one _
      map_add' := fun a b => by
        apply End.ext
        change ψf (a + b) = ψf a + ψf b
        apply hom_ext
        rw [add_hom, hψ, hψ, hψ, act.add]
        exact CategoryTheory.Functor.map_mul _ _ _ }
  refine ⟨B, e, ψ, fun c z => ?_, fun c H w hw1 hw2 => ?_⟩
  · show ptEquiv (e₀.symm (z ≫ act.act c)) =
      ptEquiv (e₀.symm z) ≫ (Over.pullback x).map (act.act c)
    have : e₀.symm (z ≫ act.act c) = e₀.symm z ≫ (Over.pullback x).map (act.act c) := by
      apply e₀.injective
      rw [MulEquiv.apply_symm_apply, push_comp_map x A (act.act c) e₀ he₀, MulEquiv.apply_symm_apply]
    rw [this]
    rfl
  · obtain ⟨e₁, he₁⟩ := GlobalTheory.LiePull.exists_pushEquiv h (epsPtR (𝟙 (Sp k)))
      (spMap (algebraMap k (DualNumber k)) ≫ x) (by simp)
    obtain ⟨e₂, he₂⟩ := GlobalTheory.LiePull.exists_pushEquiv h (Over.mk (𝟙 (Sp k))) x (by simp)
    have one : (1 : Over.mk x ⟶ A).left = (1 : Over.mk (𝟙 (Sp k)) ⟶ (Over.pullback x).obj A).left ≫
        pullback.fst A.hom x := by
      rw [← he₂, map_one]
    have r1 : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ (e₁ w).left = (1 : Over.mk x ⟶ A).left := by
      rw [he₁, one, ← Category.assoc, hw1]
    have r2 : e₁ w ≫ act.act c = 1 := by
      rw [← push_comp_map x A (act.act c) e₁ he₁]
      have hw2' : w ≫ Hom.hom (ψf c) = 1 := hw2
      change e₁ (w ≫ Hom.hom (ψf c)) = 1
      rw [hw2', map_one]
    exact e₁.injective ((H (e₁ w) r1 r2).trans (map_one e₁).symm)

end GlobalTheory.FibreAV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentFactorUniformisedOfDegDataFactor
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem factor_unif : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (D₁ : DegData R₁ (maximalIdeal R₁)) (G₁ : Over (Sp R₁)) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R₁))) (U₁ : Unif (maximalIdeal R₁) D₁ A₁ G₁), FinExt ρ ∧ Nonempty (IsPullDeg ρ D.toPre D₁.toPre) ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ LBIso (abelian₂ G₁ U₁.LG.L) ((abelian₂ G' U'.LG.L).pull (β₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) := by
  intro R _ _ _ hB D D' F hA A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hinc hpr hip hpi
  obtain ⟨R₀, _, _, _, ρ₀, D₀, G₀, _, _, β₀, β₀₂, P, W, _, _, _, φ, GW, _, _, β, DW, AW, UW,
    hF₀, hD₀, hβ₀, hsq₀, hG₀, hW, hφi, hφl, hβ, hL, hDW, hLam⟩ :=
    _root_.GlobalTheory.Mum.FactorTrait.factor_unif_at_trait R hB D D' F hA A' G' hG' U' oA oG hlin G hG inc pr hinc hpr hip hpi
  haveI := hB.2
  have hB₀ : Base R₀ := ⟨hF₀.1, charZero_of_injective_ringHom hF₀.2.1⟩
  obtain ⟨R₁, _, _, _, ρ₁, D₁, G₁, _, _, β₁, A₁, U₁, hF₁, hD₁, hβ₁, hL₁⟩ :=
    _root_.GlobalTheory.Mum.Ident.exists_finExt_unif R₀ hB₀ D₀ G₀ P hG₀ W hW φ hφi hφl GW β DW AW UW hβ hL hDW
  obtain ⟨hF, hD⟩ := GlobalTheory.Mum.FinExtComp.finExt_comp_isPullDeg R R₀ R₁ ρ₀ ρ₁ D.toPre D₀.toPre D₁.toPre hF₀ hF₁ hD₀ hD₁
  obtain ⟨β₁₂, hsq₁, hlam⟩ := GlobalTheory.Mum.lbIso_lam_pull_of_isGrpPullback _ _ (spMap ρ₁) G₀ G₁ β₁ hβ₁
  have hQ : (abelian₂ G' U'.LG.L).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ U'.LG.isLB _ _
  have key := hlam P.L.L U₁.LG.L _ (abelian₂ G' U'.LG.L) _ P.L.isLB U₁.LG.isLB hQ hL₁ hLam
  have hsp : spMap (ρ₁.comp ρ₀) = spMap ρ₁ ≫ spMap ρ₀ := by
    simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  refine ⟨R₁, inferInstance, inferInstance, inferInstance, ρ₁.comp ρ₀, D₁, G₁, inferInstance, inferInstance,
    β₁ ≫ β₀, β₁₂ ≫ β₀₂, A₁, U₁, hF, hD, ?_, ?_, ?_⟩
  · rw [hsp]; exact hβ₁.comp hβ₀
  · refine ⟨?_, ?_⟩
    · rw [Category.assoc, hsq₀.1, ← Category.assoc, hsq₁.1, Category.assoc]
    · rw [Category.assoc, hsq₀.2, ← Category.assoc, hsq₁.2, Category.assoc]
  · simpa only [Category.assoc] using key
end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagRootPullbackQuasiInverseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_diag_root_pullback_quasiInverse : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) [IsLocallyNoetherian Y] (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ P' : LB (G2 B).left, IsAxesTriv B P' → LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) → LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) → Out.RelAmple B (P'.pull (lift (𝟙 B) (𝟙 B)).left) := by
  first | (exact @GlobalTheory.UPel.HT.ES.relAmple_diag_root_pull) | (exact GlobalTheory.UPel.HT.ES.relAmple_diag_root_pull) | (intros; apply GlobalTheory.UPel.HT.ES.relAmple_diag_root_pull  <;> assumption)
end

