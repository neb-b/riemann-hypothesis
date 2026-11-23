module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2392
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1955
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1973
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1991
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1963
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2318
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2368
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0157
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThValAtAndNotIsThValue
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SabMapOfIsoOfExtendGen
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiBalanceFormalSumMemSpanCubicalTheta
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TensBal.SpanPf

variable {r : ℕ}

abbrev S (r : ℕ) : Submodule ℤ (Vec r →₀ ℤ) :=
  Submodule.span ℤ (Set.range fun p : Vec r × Vec r × Vec r => theta p.1 p.2.1 p.2.2)

lemma lam_comm (u v : Vec r) : lam u v = lam v u := by
  unfold lam; rw [add_comm u v]; abel

lemma theta_eq (u u' v : Vec r) : theta u u' v = lam (u + u') v - lam u v - lam u' v := by
  unfold lam theta; abel

lemma theta_mem (a b c : Vec r) : theta a b c ∈ S r := Submodule.subset_span ⟨(a, b, c), rfl⟩

def f (u v : Vec r) : (Vec r →₀ ℤ) ⧸ S r := Submodule.Quotient.mk (lam u v)

lemma f_comm (u v : Vec r) : f u v = f v u := by unfold f; rw [lam_comm]

lemma f_add_left (u u' v : Vec r) : f (u + u') v = f u v + f u' v := by
  unfold f
  rw [← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
  have h := theta_mem u u' v
  rw [theta_eq] at h
  convert h using 1; abel

lemma f_add_right (u v v' : Vec r) : f u (v + v') = f u v + f u v' := by
  rw [f_comm, f_add_left, f_comm v, f_comm v']

lemma f_smul_left (c : ℤ) (u v : Vec r) : f (c • u) v = c • f u v :=
  map_zsmul (AddMonoidHom.mk' (fun u => f u v) (fun a b => f_add_left a b v)) c u

lemma f_smul_right (c : ℤ) (u v : Vec r) : f u (c • v) = c • f u v := by
  rw [f_comm, f_smul_left, f_comm]

def B (r : ℕ) : Vec r →ₗ[ℤ] Vec r →ₗ[ℤ] (Vec r →₀ ℤ) ⧸ S r :=
  LinearMap.mk₂ ℤ f f_add_left f_smul_left f_add_right f_smul_right

lemma B_apply (u v : Vec r) : B r u v = Submodule.Quotient.mk (lam u v) := rfl

lemma B_comm (u v : Vec r) : B r u v = B r v u := f_comm u v

lemma axv_eq (A : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) : axv A i = ∑ l, A i l • xv l := by
  funext s
  cases s <;> simp [axv, xv, Finset.sum_apply, Pi.single_apply]

lemma azv_eq (A' : Matrix (Fin r) (Fin r) ℤ) (i : Fin r) : azv A' i = ∑ l, A' i l • zv l := by
  funext s
  cases s <;> simp [azv, zv, Finset.sum_apply, Pi.single_apply]

def P (C : Matrix (Fin r) (Fin r) ℤ) : (Vec r →₀ ℤ) ⧸ S r := ∑ l, ∑ m, C l m • B r (xv l) (zv m)

lemma P_add (C D : Matrix (Fin r) (Fin r) ℤ) : P (C + D) = P C + P D := by
  simp [P, add_smul, Finset.sum_add_distrib]

lemma T1 (A V : Matrix (Fin r) (Fin r) ℤ) :
    ∑ i, ∑ j, V i j • B r (axv A i) (zv j) = P (A.transpose * V) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [P, axv_eq, map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun j _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]

lemma T3 (A' V : Matrix (Fin r) (Fin r) ℤ) :
    ∑ i, ∑ j, V i j • B r (xv i) (azv A' j) = P (V * A') := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [P, azv_eq, map_sum, map_zsmul, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

lemma swapW (V : Matrix (Fin r) (Fin r) ℤ) (g : Fin r → Fin r → (Vec r →₀ ℤ) ⧸ S r) :
    ∑ i, ∑ j, V i j • g j i = ∑ i, ∑ j, V.transpose i j • g i j := by
  rw [Finset.sum_comm]; rfl

lemma per (A A' : Matrix (Fin r) (Fin r) ℤ) (i j : Fin r) :
    ∑ a : Fin 6, rosatiε a • B r (rosVec A A' a i) (rosVec A A' a j) =
      B r (axv A i) (zv j) + B r (zv i) (axv A j) - B r (xv i) (azv A' j) - B r (azv A' i) (xv j) := by
  simp [Fin.sum_univ_six, rosVec, rosatiε, map_add (f := _), LinearMap.add_apply]
  abel

theorem main {r : ℕ} (W A A' : Matrix (Fin r) (Fin r) ℤ)
    (h : A.transpose * (W + W.transpose) = (W + W.transpose) * A') :
    GlobalTheory.TensBal.sig W A A' ∈ Submodule.span ℤ
      (Set.range fun p : GlobalTheory.TensBal.Vec r × GlobalTheory.TensBal.Vec r × GlobalTheory.TensBal.Vec r =>
        GlobalTheory.TensBal.theta p.1 p.2.1 p.2.2) := by
  rw [← Submodule.Quotient.mk_eq_zero]
  have e : (Submodule.Quotient.mk (sig W A A') : (Vec r →₀ ℤ) ⧸ S r) =
      ∑ i, ∑ j, W i j • ∑ a : Fin 6, rosatiε a • B r (rosVec A A' a i) (rosVec A A' a j) := by
    rw [sig, ← Submodule.mkQ_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zsmul, Submodule.mkQ_apply, ← B_apply, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ => ?_
    rw [mul_comm]
  show (Submodule.Quotient.mk (sig W A A') : (Vec r →₀ ℤ) ⧸ S r) = 0
  rw [e]
  simp only [per, smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have h2 : ∑ i, ∑ j, W i j • B r (zv i) (axv A j) = P (A.transpose * W.transpose) := by
    rw [← T1]; simp only [B_comm (zv _)]; exact swapW W (fun a b => B r (axv A a) (zv b))
  have h4 : ∑ i, ∑ j, W i j • B r (azv A' i) (xv j) = P (W.transpose * A') := by
    rw [← T3]; simp only [B_comm (azv A' _)]; exact swapW W (fun a b => B r (xv a) (azv A' b))
  rw [T1, h2, T3, h4, ← P_add, sub_sub, ← P_add, ← Matrix.add_mul, ← Matrix.mul_add, h, sub_self]

end GlobalTheory.TensBal.SpanPf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiConditionDescendsGaloisCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.RosatiDescent

open GlobalTheory.CechPic

theorem lift_left_fst {S : Scheme.{0}} {A T : Over S} (f g : T ⟶ A) :
    (lift f g).left ≫ (fst A A).left = f.left :=
  congrArg (fun q => q.left) (lift_fst f g)

theorem lift_left_snd {S : Scheme.{0}} {A T : Over S} (f g : T ⟶ A) :
    (lift f g).left ≫ (snd A A).left = g.left :=
  congrArg (fun q => q.left) (lift_snd f g)

theorem eSec_comp_of_isMonHom {S : Scheme.{0}} {A : Over S} [GrpObj A] (u : A ⟶ A) [IsMonHom u] :
    eSec A ≫ u.left = eSec A := by
  show (η[A] ≫ u).left = η[A].left
  rw [IsMonHom.one_hom]

theorem lbIso_act_descent : ∀ (O : Type) [Ring O] (star : O → O) (X Y : Scheme.{0}) (π : X ⟶ Y) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (φ₂ : (G2 A).left ⟶ (G2 A₀).left) (P : LB (G2 A).left) (P₀ : LB (G2 A₀).left) (act : OActN O A) (act₀ : OActN O A₀), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → (∃ t : (P₀.pull (eSec (G2 A₀))).Gen, t.IsGen) → (∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left) → (∀ c, LBIso (P.pull (lift (fst A A ≫ act.act c) (snd A A)).left) (P.pull (lift (fst A A) (snd A A ≫ act.act (star c))).left)) → ∀ c, LBIso (P₀.pull (lift (fst A₀ A₀ ≫ act₀.act c) (snd A₀ A₀)).left) (P₀.pull (lift (fst A₀ A₀) (snd A₀ A₀ ≫ act₀.act (star c))).left) := by
  intro O _ star X Y π Ga _ ρ A _ _ A₀ _ _ φ φ₂ P P₀ act act₀ hG hA hA₀ gp hsq hP hP₀ iP _ hact hros c
  have := hG.fin
  have := hG.etale
  have := hG.onto
  have hB : IsAbelianScheme (G2 A₀) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA₀ hA₀
  have h₁ := pull_isLB hP₀ (lift (fst A₀ A₀ ≫ act₀.act c) (snd A₀ A₀)).left
  have h₂ := pull_isLB hP₀ (lift (fst A₀ A₀) (snd A₀ A₀ ≫ act₀.act (star c))).left
  have hN := LB.isLB_div h₂ h₁
  have cN := cls_div h₂ h₁ hN
  rw [cls_pull hP₀, cls_pull hP₀] at cN
  have m₀ := act₀.hom c
  have m₀' := act₀.hom (star c)
  have c₁ : φ₂ ≫ (lift (fst A₀ A₀ ≫ act₀.act c) (snd A₀ A₀)).left =
      (lift (fst A A ≫ act.act c) (snd A A)).left ≫ φ₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst A₀ A₀).left = (_ ≫ _) ≫ (fst A₀ A₀).left
      rw [Category.assoc, lift_left_fst, Category.assoc, hsq.1, ← Category.assoc, lift_left_fst]
      show φ₂ ≫ (fst A₀ A₀).left ≫ (act₀.act c).left = (fst A A).left ≫ (act.act c).left ≫ φ
      rw [reassoc_of% hsq.1, hact]
    · show (_ ≫ _) ≫ (snd A₀ A₀).left = (_ ≫ _) ≫ (snd A₀ A₀).left
      rw [Category.assoc, lift_left_snd, Category.assoc, hsq.2, ← Category.assoc, lift_left_snd]
  have c₂ : φ₂ ≫ (lift (fst A₀ A₀) (snd A₀ A₀ ≫ act₀.act (star c))).left =
      (lift (fst A A) (snd A A ≫ act.act (star c))).left ≫ φ₂ := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst A₀ A₀).left = (_ ≫ _) ≫ (fst A₀ A₀).left
      rw [Category.assoc, lift_left_fst, Category.assoc, hsq.1, ← Category.assoc, lift_left_fst]
    · show (_ ≫ _) ≫ (snd A₀ A₀).left = (_ ≫ _) ≫ (snd A₀ A₀).left
      rw [Category.assoc, lift_left_snd, Category.assoc, hsq.2, ← Category.assoc, lift_left_snd]
      show φ₂ ≫ (snd A₀ A₀).left ≫ (act₀.act (star c)).left = (snd A A).left ≫ (act.act (star c)).left ≫ φ
      rw [reassoc_of% hsq.2, hact]
  have e₁ : eSec (G2 A₀) ≫ (lift (fst A₀ A₀ ≫ act₀.act c) (snd A₀ A₀)).left = eSec (G2 A₀) := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst A₀ A₀).left = _ ≫ (fst A₀ A₀).left
      rw [Category.assoc, lift_left_fst, GlobalTheory.SquareDescent.eSec_fst]
      show eSec (G2 A₀) ≫ (fst A₀ A₀).left ≫ (act₀.act c).left = _
      rw [reassoc_of% GlobalTheory.SquareDescent.eSec_fst, eSec_comp_of_isMonHom]
    · show (_ ≫ _) ≫ (snd A₀ A₀).left = _ ≫ (snd A₀ A₀).left
      rw [Category.assoc, lift_left_snd]
  have e₂ : eSec (G2 A₀) ≫ (lift (fst A₀ A₀) (snd A₀ A₀ ≫ act₀.act (star c))).left = eSec (G2 A₀) := by
    apply pullback.hom_ext
    · show (_ ≫ _) ≫ (fst A₀ A₀).left = _ ≫ (fst A₀ A₀).left
      rw [Category.assoc, lift_left_fst]
    · show (_ ≫ _) ≫ (snd A₀ A₀).left = _ ≫ (snd A₀ A₀).left
      rw [Category.assoc, lift_left_snd, GlobalTheory.SquareDescent.eSec_snd]
      show eSec (G2 A₀) ≫ (snd A₀ A₀).left ≫ (act₀.act (star c)).left = _
      rw [reassoc_of% GlobalTheory.SquareDescent.eSec_snd, eSec_comp_of_isMonHom]
  have hPφ : pull φ₂ (cls _ hP₀) = cls _ hP := ((cls_eq_iff hP (pull_isLB hP₀ φ₂)).2 iP).symm
  have hR : pull (lift (fst A A ≫ act.act c) (snd A A)).left (cls _ hP) =
      pull (lift (fst A A) (snd A A ≫ act.act (star c))).left (cls _ hP) :=
    (cls_eq_iff (pull_isLB hP _) (pull_isLB hP _)).2 (hros c)
  have hpb := GlobalTheory.SiegelDescent.isPullback_square gp.1 φ₂ hsq
  have z₁ : pull (eSec (G2 A₀)) (cls _ hN) = 0 := by
    rw [cN, map_sub, ← pull_comp, ← pull_comp, e₁, e₂, sub_self]
  have z₂ : pull (pullback.fst (G2 A₀).hom π) (cls _ hN) = 0 := by
    rw [cN, ← hpb.isoPullback_inv_fst, pull_comp, map_sub, ← pull_comp φ₂, ← pull_comp φ₂, c₁, c₂,
      pull_comp, pull_comp, hPφ, hR, sub_self, map_zero]
  obtain ⟨t, ht⟩ := GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange GlobalTheory.SemiRigid.globalFns Y X π (G2 A₀) _ hB hN
    inferInstance inferInstance inferInstance
    ((cls_eq_zero_iff (pull_isLB hN _)).1 ((cls_pull hN _ _).trans z₁))
    ((cls_eq_zero_iff (pull_isLB hN _)).1 ((cls_pull hN _ _).trans z₂))
  have h0 : cls _ hN = 0 := (cls_eq_zero_iff hN).2 ⟨t, ht⟩
  rw [cN, sub_eq_zero, ← cls_pull hP₀ _ h₁, ← cls_pull hP₀ _ h₂] at h0
  exact (cls_eq_iff h₁ h₂).1 h0.symm

end GlobalTheory.RosatiDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiGeneratorValueOneZeroFirstFactor
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RosZeroLeft

theorem val_lift_one_left : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), L.IsLB →
    IsAbelianScheme A → ∀ (f g : A ⟶ A) [IsMonHom f] [IsMonHom g]
    (u : LB.Gen (LB.LinComb L (rosatiφ A f g) rosatiε)), u.IsGen →
    LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u (zero2 A)) (LB.oneGen L) →
    ∀ (T : Over S) (y : T ⟶ A) (z : T.left) (J : (T.left ⟶ A.left) → L.ι), Good L z J →
      val u (lift (1 : T ⟶ A) y).left z J = 1 := by
  intro S A _ _ L hL hA f g _ _ u hu h₀ T y z J hJ
  have one_isGen : (LB.oneGen L (Y := A.left)).IsGen :=
    isGen_of_gm _ fun _ _ _ _ _ =>
      (map_one _).trans (Eq.symm ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
        (_root_.mul_one _)))
  have key := gen_unique' hL (u := LB.pullGen L _ _ u (lift (1 : A ⟶ A) (𝟙 A)).left)
    (u' := LB.oneGen L) (fun U _ h => by
      refine (Fintype.prod_empty _).trans (Eq.symm ((prod_ros f g 1 (𝟙 A) h).trans ?_))
      rw [MonObj.one_comp, _root_.one_mul, _root_.one_mul, Category.id_comp]
      simp)
    A.hom η[A].left (Over.w η[A]) (GlobalTheory.globalFns_holds _ _ hA).2 (DVR.pullGen_isGen _ _ _ _ hu _)
    one_isGen (fun y I hI => by
      have := val_corr hI h₀ (𝟙 _)
      rw [val_pull hI, Category.id_comp, val_one] at this
      rw [val_pull hI, val_one, ← Over.comp_left]
      have e : η[A] ≫ lift (1 : A ⟶ A) (𝟙 A) = lift η[A] η[A] := by simp [Hom.one_def]
      rw [e]; exact this) _ y.left z J hJ
  rw [val_pull hJ, val_one, ← Over.comp_left, comp_lift, Category.comp_id, MonObj.comp_one] at key
  exact key

end GlobalTheory.RosZeroLeft
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiValueTensorDataTransportLambdaBundle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.TensRosMove

theorem rosati_alg {U : Type} [CommGroup U] (g : Fin 6 → U) (u : U) :
    (∏ k, g k ^ rosatiε k) * u * (g 1 * g 2 * g 3) = u * (g 0 * g 4 * g 5) := by
  rw [Fin.prod_univ_six]
  show g 0 ^ (1 : ℤ) * g 1 ^ (-1 : ℤ) * g 2 ^ (-1 : ℤ) * g 3 ^ (-1 : ℤ) * g 4 ^ (1 : ℤ) * g 5 ^ (1 : ℤ) * u *
    (g 1 * g 2 * g 3) = u * (g 0 * g 4 * g 5)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  abel

theorem rosVT_move : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (O : Type) [CommRing O] [StarRing O] (oa : D'.toPre.P.OAct O) (x : O) (ρ' : N'.A → N'.A → F), GlobalTheory.Relabel.RosV ν' oa x ρ' → ∃ ρ'' : N'.A → N'.A → F, GlobalTheory.Mum.TensRos.RosVT T ν ν' (oa.act (star x)) (oa.act x) ρ'' ∧ ∀ a b, ρ'' a b * (wv T ν ν' (GlobalTheory.Relabel.actV ν' oa (star x) a) * wv T ν ν' b * wv T ν ν' (a * GlobalTheory.Relabel.actV ν' oa x b)) = ρ' a b * (wv T ν ν' (GlobalTheory.Relabel.actV ν' oa (star x) a * b) * wv T ν ν' a * wv T ν ν' (GlobalTheory.Relabel.actV ν' oa x b)) := by
  intro R _ _ _ _ D D' n W T F _ _ _ N N' ν ν' O _ _ oa x ρ' hR
  obtain ⟨u, hu, u₀, hρ⟩ := hR
  have := oa.hom x
  have := oa.hom (star x)
  have hL₁ : (LB.LinComb D.toPre.P.L (tensφ T.pr) (tensε W)).IsLB := LB.isLB_linComb D.toPre.P.isLB _ _
  obtain ⟨u'', hu'', hv⟩ := GlobalTheory.WtTower.exists_gen_of_iso (LB.isLB_linComb D'.toPre.P.isLB _ rosatiε)
    (LB.isLB_linComb hL₁ (rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x)) rosatiε)
    (LB.linCombIso T.w _ rosatiε) (DVR.linCombIso_isGen T.w T.w_gen _ _) u hu
  refine ⟨fun a b => vF u'' (lift (ν'.eA a) (ν'.eA b)).left (GlobalTheory.Mum.TensRos.tensJ T ν), ⟨u'', hu'', ?_, fun _ _ => rfl⟩, ?_⟩
  · refine corr_of_val hL₁ fun y J hJ => ?_
    rw [val_pull hJ, val_one]
    have h1 : (η[D'.toPre.P.A] : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.toPre.P.A) = 1 := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    have hz : ∀ k, (𝟙 _ ≫ zero2 D'.toPre.P.A) ≫ rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x) k =
        (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.toPre.P.A).left := fun k => by
      rw [Category.id_comp, zero2, h1, ← GlobalTheory.RosMove.rosO_left, ← Over.comp_left, GlobalTheory.RosMove.lift_rosO]
      fin_cases k <;> simp [MonObj.one_comp]
    choose I hI using fun χ : _ ⟶ D'.toPre.P.A.left => exists_chart D'.toPre.P.isLB (χ y)
    have hI' : Good D'.toPre.P.L y I := hI
    have e₀ : val u (𝟙 _ ≫ zero2 D'.toPre.P.A) y I = 1 := by
      have := val_corr hI' u₀ (𝟙 _)
      rwa [val_pull hI', val_one] at this
    have m₁ := hJ.mem (rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x)) (𝟙 _ ≫ zero2 D'.toPre.P.A)
    have m₂ := hI'.mem (rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x)) (𝟙 _ ≫ zero2 D'.toPre.P.A)
    have H := hv _ (𝟙 _ ≫ zero2 D'.toPre.P.A) y _ _ m₁ m₂
    have G := GlobalTheory.WtTower.gm_linCombIso T.w (rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x)) rosatiε (_, _)
      (𝟙 _ ≫ zero2 D'.toPre.P.A) y ⟨m₁, m₂⟩
    refine H.trans (Eq.trans (congrArg₂ (· * ·) G e₀) ?_)
    rw [_root_.mul_one]
    have key : ∀ Fn : (_ ⟶ D'.toPre.P.A.left) → ((𝟙_ (Over (Spec (CommRingCat.of R)))).left.presheaf.stalk y)ˣ,
        ∏ a, Fn ((𝟙 _ ≫ zero2 D'.toPre.P.A) ≫ rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x) a) ^ rosatiε a = 1 := by
      intro Fn
      simp only [hz]
      simp [Fin.prod_univ_succ, rosatiε]
    exact key (fun ψ => gm ψ y (((LB.LinComb D.toPre.P.L (tensφ T.pr) (tensε W)).div D'.toPre.P.L).U (J ψ, I ψ))
      (T.w.s (J ψ, I ψ)))
  · intro a b
    let z : Sp F := IsLocalRing.closedPoint F
    have hN : Good D.toPre.P.L z ν.J := fun q => ν.good q trivial
    have hJ' : Good D'.toPre.P.L z ν'.J := fun q => ν'.good q trivial
    have mT : ∀ y : Sp F ⟶ D'.toPre.P.A.left,
        y z ∈ (LB.LinComb D.toPre.P.L (tensφ T.pr) (tensε W)).U (GlobalTheory.Mum.TensRos.tensJ T ν y) :=
      fun y => Set.mem_iInter.2 fun k => hN (y ≫ tensφ T.pr k)
    have m₁ : (lift (ν'.eA a) (ν'.eA b)).left z ∈ LB.wchart (LB.LinComb D.toPre.P.L (tensφ T.pr) (tensε W))
        (rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x))
        (fun k => GlobalTheory.Mum.TensRos.tensJ T ν ((lift (ν'.eA a) (ν'.eA b)).left ≫
          rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x) k)) := Set.mem_iInter.2 fun k => mT _
    have m₂ := hJ'.mem (rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x)) (lift (ν'.eA a) (ν'.eA b)).left
    have H := hv _ (lift (ν'.eA a) (ν'.eA b)).left z _ _ m₁ m₂
    have G := GlobalTheory.WtTower.gm_linCombIso T.w (rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x)) rosatiε (_, _)
      (lift (ν'.eA a) (ν'.eA b)).left z ⟨m₁, m₂⟩
    let Gp : N'.A → ((Sp F).presheaf.stalk z)ˣ := fun p => gm (ν'.eA p).left z
      (((LB.LinComb D.toPre.P.L (tensφ T.pr) (tensε W)).div D'.toPre.P.L).U
        (GlobalTheory.Mum.TensRos.tensJ T ν (ν'.eA p).left, ν'.J (ν'.eA p).left))
      (T.w.s (GlobalTheory.Mum.TensRos.tensJ T ν (ν'.eA p).left, ν'.J (ν'.eA p).left))
    have hW : ∀ p, toStk z (wv T ν ν' p) = (Gp p).val := fun p => by
      have hm : (ν'.eA p).left z ∈ (((LB.LinComb D.toPre.P.L (tensφ T.pr) (tensε W)).div D'.toPre.P.L).U
          (GlobalTheory.Mum.TensRos.tensJ T ν (ν'.eA p).left, ν'.J (ν'.eA p).left)) := ⟨mT _, hJ' _⟩
      exact toStk_valF _ _ z hm _
    have ea : ∀ y c, ν'.eA (GlobalTheory.Relabel.actV ν' oa y c) = ν'.eA c ≫ oa.act y := fun y c => ν'.eA.apply_symm_apply _
    let pts : Fin 6 → N'.A := ![GlobalTheory.Relabel.actV ν' oa (star x) a * b, GlobalTheory.Relabel.actV ν' oa (star x) a, b,
      a * GlobalTheory.Relabel.actV ν' oa x b, a, GlobalTheory.Relabel.actV ν' oa x b]
    have hp : ∀ k, (lift (ν'.eA a) (ν'.eA b)).left ≫ rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x) k =
        (ν'.eA (pts k)).left := fun k => by
      rw [← GlobalTheory.RosMove.rosO_left, ← Over.comp_left, GlobalTheory.RosMove.lift_rosO]
      fin_cases k <;> simp [pts, ea]
    have key : ∀ Fn : (Sp F ⟶ D'.toPre.P.A.left) → ((Sp F).presheaf.stalk z)ˣ,
        ∏ k, Fn ((lift (ν'.eA a) (ν'.eA b)).left ≫ rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x) k) ^ rosatiε k =
          ∏ k, Fn (ν'.eA (pts k)).left ^ rosatiε k := fun Fn => by simp only [hp]
    have G' := G.trans (key (fun ψ => gm ψ z
      (((LB.LinComb D.toPre.P.L (tensφ T.pr) (tensε W)).div D'.toPre.P.L).U (GlobalTheory.Mum.TensRos.tensJ T ν ψ, ν'.J ψ))
      (T.w.s (GlobalTheory.Mum.TensRos.tensJ T ν ψ, ν'.J ψ))))
    have v'' := toStk_valF _ _ z m₁ (u''.s _)
    have v' : toStk z (ρ' a b) = (gm (lift (ν'.eA a) (ν'.eA b)).left z _ (u.s fun k => ν'.J
        ((lift (ν'.eA a) (ν'.eA b)).left ≫ rosatiφ D'.toPre.P.A (oa.act (star x)) (oa.act x) k))).val := by
      rw [hρ]; exact toStk_valF _ _ z m₂ _
    have HH := H.trans (congrArg₂ (· * ·) G' rfl)
    apply (toStk z).injective
    show toStk z (vF u'' (lift (ν'.eA a) (ν'.eA b)).left (GlobalTheory.Mum.TensRos.tensJ T ν) * _) = _
    simp only [map_mul, hW, v']
    erw [v'', HH]
    simp only [← Units.val_mul]
    congr 1
    exact rosati_alg (fun k => Gp (pts k)) _

end GlobalTheory.Mum.TensRosMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecTw
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

def SecTw {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Sp (FractionRing R))} {N : ℕ}
    (σ : Kb R →ₐ[FractionRing R] Kb R) (t t' : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N) : Prop :=
  ∀ (Z : Scheme.{0}) (p p' : Z ⟶ (TFK (R := R) (Kb R) ⊗ A.A).left),
    p' ≫ (snd (TFK (R := R) (Kb R)) A.A).left = p ≫ (snd (TFK (R := R) (Kb R)) A.A).left →
    p' ≫ (fst (TFK (R := R) (Kb R)) A.A).left = p ≫ (fst (TFK (R := R) (Kb R)) A.A).left ≫ spMap σ.toRingHom →
    ∀ z J, Good A.L z J → sval t' p z J = sval t p' z J
end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianBaseChangeNormalDomainGenericFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemiAbGenericFibre

theorem baseChange_normal_generic : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], IsSemiAbelian G → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (χ : Sp R ⟶ S), IsLocallyNoetherian (Over.mk χ ⊗ G).left ∧ GlobalTheory.IsNormalScheme (Over.mk χ ⊗ G).left ∧ IsPreimmersion ((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left ∧ ∀ W : (Over.mk χ ⊗ G).left.Opens, Function.Injective ((((Over.homMk (spMap (algebraMap R (FractionRing R))) rfl : Over.mk (spMap (algebraMap R (FractionRing R)) ≫ χ) ⟶ Over.mk χ) ▷ G).left.app W).hom) := by
  intro S G _ hG R _ _ _ _ χ
  set K := FractionRing R
  set T : Over S := Over.mk χ
  set TK : Over S := Over.mk (spMap (algebraMap R K) ≫ χ)
  set h : TK ⟶ T := Over.homMk (spMap (algebraMap R K)) rfl
  have hpb : IsPullback (h ▷ G).left (CartesianMonoidalCategory.fst TK G).left
      (CartesianMonoidalCategory.fst T G).left (spMap (algebraMap R K)) :=
    GlobalTheory.ThetaRuleCompare.isPullback_whisker h
  have hsm : Smooth G.hom := hG.smooth
  have h1 : IsPullback (CartesianMonoidalCategory.snd T G).left (CartesianMonoidalCategory.fst T G).left G.hom T.hom :=
    (IsPullback.of_hasPullback T.hom G.hom).flip
  have hsf : Smooth (CartesianMonoidalCategory.fst T G).left := MorphismProperty.of_isPullback h1 hsm
  have : IsLocallyNoetherian T.left := (inferInstance : IsLocallyNoetherian (Sp R))
  have : IsLocallyNoetherian (T ⊗ G).left := LocallyOfFiniteType.isLocallyNoetherian (CartesianMonoidalCategory.fst T G).left
  have : GlobalTheory.IsNormalScheme T.left := (inferInstance : GlobalTheory.IsNormalScheme (Sp R))
  have : IsPreimmersion (spMap (algebraMap R K)) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  refine ⟨inferInstance, GlobalTheory.isNormalScheme_of_smooth (CartesianMonoidalCategory.fst T G).left,
    MorphismProperty.of_isPullback hpb.flip ‹_›, fun W => ?_⟩
  have : IsDominant (spMap (algebraMap R K)) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)).le.trans bot_le)⟩
  have : QuasiCompact (spMap (algebraMap R K)) := by
    set_option backward.isDefEq.respectTransparency.types false in
      exact (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr (by infer_instance)
  have : IsSchemeTheoreticallyDominant (spMap (algebraMap R K)) :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  have : IsSchemeTheoreticallyDominant (h ▷ G).left :=
    IsSchemeTheoreticallyDominant.of_isPullback hpb.flip
  have : QuasiCompact (h ▷ G).left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hpb.flip inferInstance
  exact (h ▷ G).left.app_injective W

end GlobalTheory.SemiAbGenericFibre
end

