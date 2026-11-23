module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2188
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0141
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0483
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ProductTorsionSectionBound
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.Sep.E8Fibration.Lab

def postHom {S : Scheme.{0}} (T : Over S) {A B : Over S} [GrpObj A] [GrpObj B] (f : A ⟶ B) [IsMonHom f] :
    (T ⟶ A) →* (T ⟶ B) where
  toFun x := x ≫ f
  map_one' := by simp
  map_mul' x y := by simp [MonObj.mul_comp]

def preHom {S : Scheme.{0}} {T A : Over S} (x : T ⟶ A) (B : Over S) [GrpObj B] :
    (A ⟶ B) →* (T ⟶ B) where
  toFun y := x ≫ y
  map_one' := by simp
  map_mul' y z := by simp [MonObj.comp_mul]

theorem zpow_finset_sum {G J : Type} [CommGroup G] (g : G) (s : Finset J) (e : J → ℤ) :
    g ^ (∑ i ∈ s, e i) = ∏ i ∈ s, g ^ e i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add, ih]

theorem prod_prod_zpow {G C J : Type} [CommGroup G] [Fintype C] [Fintype J] (b : C → G) (x : J → C → ℤ) (k : J → ℤ) :
    ∏ i, (∏ c, b c ^ x i c) ^ k i = ∏ c, b c ^ (∑ i, k i * x i c) := by
  simp only [← Finset.prod_zpow, ← zpow_mul, zpow_finset_sum]
  rw [Finset.prod_comm]
  simp only [mul_comm]

theorem pow_val_intCast {G : Type} [Group G] {N : ℕ} (hN : 0 < N) {g : G} (hg : g ^ N = 1) (k : ℤ) :
    g ^ ((k : ZMod N)).val = g ^ k := by
  haveI : NeZero N := ⟨hN.ne'⟩
  rw [← zpow_natCast, ZMod.val_intCast]
  exact (zpow_eq_zpow_emod' k hg).symm

theorem prod_zpow_pow_eq_one {G C : Type} [CommGroup G] [Fintype C] {N : ℕ} {b : C → G} (hb : ∀ c, b c ^ N = 1)
    (x : C → ℤ) : (∏ c, b c ^ x c) ^ N = 1 := by
  rw [← Finset.prod_pow]
  refine Finset.prod_eq_one fun c _ => ?_
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb, one_zpow]

theorem sum_labMat_mul (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : (e8 W).det = 1) (h : ℕ) (a : Fin 2)
    (i : Fin (2 * (8 * h))) (u : Fin 8) (c : Fin h ⊕ Fin h) :
    ∑ i', labMat W hW h a i' i * sharpBasis W hW h (Pi.single i' 1) u c =
      ∑ v, actMat W a u v * sharpBasis W hW h (Pi.single i 1) v c := by
  have key : ∀ y : Fin (2 * (8 * h)) → ℤ,
      ∑ i', y i' * sharpBasis W hW h (Pi.single i' 1) u c = sharpBasis W hW h y u c := by
    intro y
    conv_rhs => rw [pi_eq_sum_univ' y]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact (key _).trans (congrFun (congrFun ((sharpBasis W hW h).apply_symm_apply _) u) c)

theorem ptOf_torsion_and_act : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (hW : IsE8 W) (gQ : ℕ) {S : Scheme.{0}} (A B : Over S) [GrpObj A] [IsCommMonObj A]
  [GrpObj B] [IsCommMonObj B] (pr : Fin 8 → (A ⟶ B)) (hP : E8Fibration.IsProd pr) (N : ℕ) {T : Over S}
  (b : Fin gQ ⊕ Fin gQ → (T ⟶ B)), (∀ c, b c ^ N = 1) → 0 < N →
  (∀ i, E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i 1)) ^ N = 1) ∧
  ∀ (act : Fin 2 → (A ⟶ A)), (∀ i, E8Fibration.ActsBy pr (act i) (E8Fibration.actMat W i)) → ∀ (a : Fin 2) (i : Fin (2 * (8 * gQ))),
    E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i 1)) ≫ act a =
      Out.linComb (fun i' => E8Fibration.Lab.ptOf hP b (E8Fibration.Lab.sharpBasis W hW.2 gQ (Pi.single i' 1)))
        (fun i' => ((E8Fibration.Lab.labMat W hW.2 gQ a i' i : ZMod N)).val) := by
  intro W hW gQ S A B _ _ _ _ pr hP N T b hb hN
  have ext : ∀ x y : T ⟶ A, (∀ u, x ≫ pr u = y ≫ pr u) → x = y := fun x y h =>
    (hP.2 T fun u => y ≫ pr u).unique h fun _ => rfl
  refine ⟨fun i => ext _ _ fun u => ?_, fun act hact a i => ext _ _ fun u => ?_⟩
  · haveI := hP.1 u
    have := map_pow (postHom T (pr u)) (ptOf hP b (sharpBasis W hW.2 gQ (Pi.single i 1))) N
    refine this.trans ?_
    change (ptOf hP b _ ≫ pr u) ^ N = _
    rw [ptOf_pr, prod_zpow_pow_eq_one hb]
    exact (map_one (postHom T (pr u))).symm
  · haveI := hP.1 u
    have h1 : (ptOf hP b (sharpBasis W hW.2 gQ (Pi.single i 1)) ≫ act a) ≫ pr u =
        ∏ c, b c ^ (∑ v, actMat W a u v * sharpBasis W hW.2 gQ (Pi.single i 1) v c) := by
      rw [Category.assoc, hact a u, ← prod_prod_zpow]
      refine (map_prod (preHom (ptOf hP b (sharpBasis W hW.2 gQ (Pi.single i 1))) B) _ _).trans ?_
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [map_zpow, ← ptOf_pr hP]
      rfl
    rw [h1, Out.linComb, List.prod_ofFn]
    refine Eq.trans ?_ (map_prod (postHom T (pr u)) _ _).symm
    simp only [← sum_labMat_mul W hW.2 gQ a i u]
    rw [← prod_prod_zpow]
    refine Finset.prod_congr rfl fun i' _ => ?_
    rw [map_pow, ← pow_val_intCast hN (prod_zpow_pow_eq_one hb _), ← ptOf_pr hP]
    rfl

end GlobalTheory.Poinc.Sep.E8Fibration.Lab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerFormBundleMatricesAdjoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.E8AdjointPairing

open GlobalTheory.CechPic

section Pairing

variable {S : Scheme.{0}} {G G' T : Over S} [GrpObj G] [GrpObj G']

def lamC (x y : T ⟶ G) : Pic G.left →+ Pic T.left where
  toFun c := lam c x y
  map_zero' := by simp only [lam, map_zero]; abel
  map_add' c d := by simp only [lam, map_add (f := _)]; abel

theorem lamC_apply (c : Pic G.left) (x y : T ⟶ G) : lamC x y c = lam c x y := rfl

theorem lam_pull_of (g : G' ⟶ G) (c : Pic G.left) (u v : T ⟶ G')
    (hm : (u * v) ≫ g = (u ≫ g) * (v ≫ g)) (h1 : (1 : T ⟶ G') ≫ g = 1) :
    lam (pull g.left c) u v = lam c (u ≫ g) (v ≫ g) := by
  simp only [lam, ← pull_comp, ← Over.comp_left, hm, h1]

end Pairing

end GlobalTheory.E8AdjointPairing

namespace GlobalTheory.E8AdjointPairing

open GlobalTheory.CechPic

section Bilinear

variable {S : Scheme.{0}} {G G' T : Over S} [GrpObj G] [GrpObj G'] [IsCommMonObj G]
  {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen)
include hΘ

theorem lam_mul_right' (x y z : T ⟶ G) :
    lam (cls L hL) x (y * z) = lam (cls L hL) x y + lam (cls L hL) x z := by
  rw [lam_comm, lam_mul_left hL hΘ, lam_comm, lam_comm _ z]

def lamHom (z : T ⟶ G) : (T ⟶ G) →* Multiplicative (Pic T.left) where
  toFun x := Multiplicative.ofAdd (lam (cls L hL) x z)
  map_one' := by rw [lam_one_left]; rfl
  map_mul' x y := by rw [lam_mul_left hL hΘ]; rfl

theorem lam_zpow_left (x z : T ⟶ G) (k : ℤ) :
    lam (cls L hL) (x ^ k) z = k • lam (cls L hL) x z := by
  have h := map_zpow (lamHom hL hΘ z) x k
  exact congrArg Multiplicative.toAdd h

theorem lam_prod_left : ∀ (n : ℕ) (x : Fin n → (T ⟶ G)) (e : Fin n → ℤ) (z : T ⟶ G),
    lam (cls L hL) (List.ofFn fun v => x v ^ e v).prod z = ∑ v, e v • lam (cls L hL) (x v) z
  | 0, x, e, z => by simp [lam_one_left]
  | n + 1, x, e, z => by
    rw [List.ofFn_succ, List.prod_cons, lam_mul_left hL hΘ, lam_zpow_left hL hΘ,
      lam_prod_left n (fun v => x v.succ) (fun v => e v.succ) z, Fin.sum_univ_succ]

theorem lam_prod_right (n : ℕ) (x : Fin n → (T ⟶ G)) (e : Fin n → ℤ) (z : T ⟶ G) :
    lam (cls L hL) z (List.ofFn fun v => x v ^ e v).prod = ∑ v, e v • lam (cls L hL) z (x v) := by
  rw [lam_comm, lam_prod_left hL hΘ]
  simp only [lam_comm _ z]

theorem lam_lam (p q : G' ⟶ G) [IsMonHom p] [IsMonHom q] (u v : T ⟶ G') :
    lam (lam (cls L hL) p q) u v = lam (cls L hL) (u ≫ p) (v ≫ q) + lam (cls L hL) (u ≫ q) (v ≫ p) := by
  have e : lam (lam (cls L hL) p q) u v = lamC u v (lam (cls L hL) p q) := rfl
  rw [e, show lam (cls L hL) p q = pull (p * q).left (cls L hL) - pull p.left (cls L hL) - pull q.left (cls L hL)
      + pull (1 : G' ⟶ G).left (cls L hL) from rfl, map_add, map_sub, map_sub]
  simp only [lamC_apply]
  rw [lam_pull_of (p * q) _ u v (by rw [MonObj.comp_mul, MonObj.mul_comp, MonObj.mul_comp, MonObj.comp_mul,
      MonObj.comp_mul, _root_.mul_mul_mul_comm]) (by rw [MonObj.comp_mul, MonObj.one_comp, MonObj.one_comp, _root_.mul_one]),
    lam_pull_of p _ u v (MonObj.mul_comp _ _ _) (MonObj.one_comp _),
    lam_pull_of q _ u v (MonObj.mul_comp _ _ _) (MonObj.one_comp _),
    lam_pull_of (1 : G' ⟶ G) _ u v (by rw [MonObj.comp_one, MonObj.comp_one, MonObj.comp_one, _root_.mul_one])
      (MonObj.comp_one _)]
  rw [MonObj.comp_mul, MonObj.comp_mul, MonObj.comp_one, MonObj.comp_one, lam_one_left,
    lam_mul_left hL hΘ, lam_mul_right' hL hΘ, lam_mul_right' hL hΘ]
  abel

end Bilinear

end GlobalTheory.E8AdjointPairing

namespace GlobalTheory.E8AdjointPairing

open GlobalTheory.CechPic

theorem alg_left {M : Type*} [AddCommGroup M] (S a : Matrix (Fin 8) (Fin 8) ℤ) (B : Fin 8 → Fin 8 → M) :
    ∑ i, ∑ j, S i j • ∑ v, a i v • B v j = ∑ v, ∑ j, (a.transpose * S) v j • B v j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
  simp_rw [smul_comm (S _ _) (a _ _)]
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun j _ => Finset.sum_comm).trans ?_
  exact Finset.sum_comm

theorem alg_right {M : Type*} [AddCommGroup M] (S a' : Matrix (Fin 8) (Fin 8) ℤ) (B : Fin 8 → Fin 8 → M) :
    ∑ i, ∑ j, S i j • ∑ v, a' j v • B i v = ∑ i, ∑ v, (S * a') i v • B i v := by
  simp only [Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_comm

def precomp {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] (h : T ⟶ T') : (T' ⟶ G) →* (T ⟶ G) where
  toFun y := h ≫ y
  map_one' := MonObj.comp_one h
  map_mul' := MonObj.comp_mul h

theorem comp_prod {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] (h : T ⟶ T') :
    ∀ (n : ℕ) (x : Fin n → (T' ⟶ G)) (e : Fin n → ℤ),
      h ≫ (List.ofFn fun v => x v ^ e v).prod = (List.ofFn fun v => (h ≫ x v) ^ e v).prod
  | 0, x, e => by simp [MonObj.comp_one]
  | n + 1, x, e => by
    rw [List.ofFn_succ, List.prod_cons, MonObj.comp_mul, comp_prod h n, List.ofFn_succ, List.prod_cons]
    congr 1
    exact map_zpow (precomp (G := G) h) (x 0) (e 0)

theorem lbIso_cubeLB_adjoint : ∀ (K : Type) [Field K] (A A' : PolAV (Sp K)) (W : Matrix (Fin 8) (Fin 8) ℤ) (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (a a' : Matrix (Fin 8) (Fin 8) ℤ), (W + W.transpose) * a' = a.transpose * (W + W.transpose) → ∀ (f f' : A'.A ⟶ A'.A), (∀ u, f ≫ pr u = (List.ofFn fun v => pr v ^ a u v).prod) → (∀ u, f' ≫ pr u = (List.ofFn fun v => pr v ^ a' u v).prod) → LBIso (cubeLB A'.A ![fst A'.A A'.A ≫ f, snd A'.A A'.A] A'.L) (cubeLB A'.A ![fst A'.A A'.A, snd A'.A A'.A ≫ f'] A'.L) := by
  intro K _ A A' W pr hpr hiso a a' hS f f' hf hf'
  have := A.isAb.comm
  obtain ⟨r, hr⟩ := A.rigid
  obtain ⟨cs⟩ := (GlobalTheory.firstFiveLaws.1.cube (Sp K) A ⟨A.L, r, A.isLB, hr⟩ rfl).1
  have hΘ : ∃ t : LB.Gen (Theta A.A A.L), t.IsGen := ⟨cs.t, cs.isGen⟩
  have hL := A.isLB
  have hL' := A'.isLB
  have hLam : (abelian₂ A.A A.L).IsLB := LB.isLB_linComb hL _ _
  have hLC := LB.isLB_linComb hLam (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left)
    (fun ab => W ab.1 ab.2)
  have hcA : cls A'.L hL' = ∑ ab : Fin 8 × Fin 8, W ab.1 ab.2 • lam (cls A.L hL) (pr ab.1) (pr ab.2) := by
    rw [(cls_eq_iff hL' hLC).2 hiso, cls_linComb hLam]
    refine Finset.sum_congr rfl fun ab _ => ?_
    congr 1
    rw [show cls (abelian₂ A.A A.L) hLam = lam (cls A.L hL) (fst A.A A.A) (snd A.A A.A) from cls_cube_two hL _ _ _,
      pull_lam, lift_fst, lift_snd]
  have key : ∀ {T : Over (Sp K)} (u v : T ⟶ A'.A), lam (cls A'.L hL') u v =
      ∑ i, ∑ j, (W + W.transpose) i j • lam (cls A.L hL) (u ≫ pr i) (v ≫ pr j) := by
    intro T u v
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← lamC_apply, hcA, map_sum]
    simp only [map_zsmul, lamC_apply, lam_lam hL hΘ, smul_add, Finset.sum_add_distrib, Matrix.add_apply,
      Matrix.transpose_apply, add_smul]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
    congr 1
    exact Finset.sum_comm
  have h₁ : (cubeLB A'.A ![fst A'.A A'.A ≫ f, snd A'.A A'.A] A'.L).IsLB := LB.isLB_linComb hL' _ _
  have h₂ : (cubeLB A'.A ![fst A'.A A'.A, snd A'.A A'.A ≫ f'] A'.L).IsLB := LB.isLB_linComb hL' _ _
  refine (cls_eq_iff h₁ h₂).1 ?_
  rw [cls_cube_two hL', cls_cube_two hL', key, key]
  simp only [Category.assoc, hf, hf', comp_prod, lam_prod_left hL hΘ, lam_prod_right hL hΘ]
  refine (alg_left (W + W.transpose) a
    (fun v j => lam (cls A.L hL) (fst A'.A A'.A ≫ pr v) (snd A'.A A'.A ≫ pr j))).trans ?_
  rw [← hS]
  exact (alg_right (W + W.transpose) a'
    (fun i v => lam (cls A.L hL) (fst A'.A A'.A ≫ pr i) (snd A'.A A'.A ≫ pr v))).symm

end GlobalTheory.E8AdjointPairing
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerProjectionsGroupPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.GrpPullPow

theorem isMonHom_of_mul_pts {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H)
    (h : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) : IsMonHom f := by
  refine ⟨?_, ?_⟩
  · rw [MonObj.one_eq_one, MonObj.one_eq_one]
    exact map_one (MonoidHom.mk' (fun x : 𝟙_ (Over S) ⟶ G ↦ x ≫ f) (h _))
  · rw [MonObj.mul_eq_mul G, MonObj.mul_eq_mul H, MonObj.comp_mul,
      tensorHom_fst, tensorHom_snd]
    exact h (G ⊗ G) (fst G G) (snd G G)

theorem pr_pull : ∀ {T T' : Scheme.{0}} {t : T' ⟶ T} {B C : Over T} [GrpObj B] [GrpObj C] {B' C' : Over T'} [GrpObj B'] [GrpObj C'] {φB : B'.left ⟶ B.left} {χ : C'.left ⟶ C.left} (pr : Fin 8 → (B ⟶ C)), IsGrpPullback B' B t φB → IsGrpPullback C' C t χ → (∀ a, IsMonHom (pr a)) → (∀ (T₁ : Over T) (y : Fin 8 → (T₁ ⟶ C)), ∃! x : T₁ ⟶ B, ∀ a, x ≫ pr a = y a) → ∃ pr' : Fin 8 → (B' ⟶ C'), (∀ a, (pr' a).left ≫ χ = φB ≫ (pr a).left) ∧ (∀ a, IsMonHom (pr' a)) ∧ ∀ (T₁ : Over T') (y : Fin 8 → (T₁ ⟶ C')), ∃! x : T₁ ⟶ B', ∀ a, x ≫ pr' a = y a := by
  intro T T' t B C _ _ B' C' _ _ φB χ pr hB hC hpr huniv
  have hw : ∀ a, (φB ≫ (pr a).left) ≫ C.hom = B'.hom ≫ t := fun a => by
    rw [Category.assoc, Over.w (pr a), hB.1.w]
  let pr' : Fin 8 → (B' ⟶ C') := fun a =>
    Over.homMk (hC.1.lift (φB ≫ (pr a).left) B'.hom (hw a)) (hC.1.lift_snd _ _ _)
  have h1 : ∀ a, (pr' a).left ≫ χ = φB ≫ (pr a).left := fun a => hC.1.lift_fst _ _ _
  have hpush : ∀ (T₁ : Over T') (x : T₁ ⟶ B') a,
      pushPt hC.1.w (x ≫ pr' a) = pushPt hB.1.w x ≫ pr a := by
    intro T₁ x a
    apply Over.OverMorphism.ext
    show (x.left ≫ (pr' a).left) ≫ χ = (x.left ≫ φB) ≫ (pr a).left
    rw [Category.assoc, h1, Category.assoc]
  refine ⟨pr', h1, fun a => ?_, fun T₁ y => ?_⟩
  · haveI := hpr a
    refine isMonHom_of_mul_pts _ fun T₁ x y => ?_
    apply Over.OverMorphism.ext
    apply hC.1.hom_ext
    · have e1 := hC.2 T₁ (x ≫ pr' a) (y ≫ pr' a) (pushPt hC.1.w (x ≫ pr' a))
        (pushPt hC.1.w (y ≫ pr' a)) rfl rfl
      have e2 := hB.2 T₁ x y (pushPt hB.1.w x) (pushPt hB.1.w y) rfl rfl
      rw [← e1, hpush, hpush, ← MonObj.mul_comp, Over.comp_left, Over.comp_left, Category.assoc, h1,
        ← Category.assoc, ← e2]
    · rw [Over.w, Over.w]
  · let T₀ : Over T := Over.mk (T₁.hom ≫ t)
    obtain ⟨x₀, hx₀, hu⟩ := huniv T₀ (fun a => pushPt hC.1.w (y a))
    have wx : x₀.left ≫ B.hom = T₁.hom ≫ t := Over.w x₀
    let X : T₁ ⟶ B' := Over.homMk (hB.1.lift x₀.left T₁.hom wx) (hB.1.lift_snd _ _ _)
    have hX : X.left ≫ φB = x₀.left := hB.1.lift_fst _ _ _
    refine ⟨X, fun a => ?_, fun x' hx' => ?_⟩
    · apply Over.OverMorphism.ext
      apply hC.1.hom_ext
      · show (X.left ≫ (pr' a).left) ≫ χ = (y a).left ≫ χ
        rw [Category.assoc, h1, ← Category.assoc, hX]
        exact congrArg (fun q => q.left) (hx₀ a)
      · rw [Over.w, Over.w]
    · have e : pushPt hB.1.w x' = x₀ := hu _ fun a => by
        rw [← hpush, hx' a]
      apply Over.OverMorphism.ext
      apply hB.1.hom_ext
      · rw [hX]; exact congrArg (fun q => q.left) e
      · rw [Over.w, Over.w]

end GlobalTheory.GrpPullPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ElementaryMatrixEndomorphismGroupPullbackTranspo
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.MatEndPull

theorem ext_of_pb {T T' : Scheme.{0}} {t : T' ⟶ T} {G : Over T} {G' : Over T'} [GrpObj G] [GrpObj G']
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G t φ) {X : Over T'} {x y : X ⟶ G'}
    (e : x.left ≫ φ = y.left ≫ φ) : x = y := by
  apply Over.OverMorphism.ext
  apply h.1.hom_ext e
  rw [Over.w x, Over.w y]

theorem one_left_eq {T : Scheme.{0}} {X M : Over T} [GrpObj M] : (1 : X ⟶ M).left = X.hom ≫ η[M].left := by
  rw [Hom.one_def, Over.comp_left]
  congr 1

theorem mul_comp_lift {T T' : Scheme.{0}} {t : T' ⟶ T} {B : Over T} {B' : Over T'} [GrpObj B] [GrpObj B']
    {φ : B'.left ⟶ B.left} (h : IsGrpPullback B' B t φ) {f : B ⟶ B} [IsMonHom f] {f' : B' ⟶ B'}
    (e : f'.left ≫ φ = φ ≫ f.left) {X : Over T'} (x y : X ⟶ B') :
    (x * y) ≫ f' = (x ≫ f') * (y ≫ f') := by
  apply ext_of_pb h
  have e₁ := h.2 X x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl
  have e₂ := h.2 X (x ≫ f') (y ≫ f') (pushPt h.1.w x ≫ f) (pushPt h.1.w y ≫ f)
    (by simp [pushPt, e]) (by simp [pushPt, e])
  rw [← e₂, Over.comp_left, Category.assoc, e, ← Category.assoc, ← e₁, ← Over.comp_left, mul_comp]

theorem isMonHom_lift {T T' : Scheme.{0}} {t : T' ⟶ T} {B : Over T} {B' : Over T'} [GrpObj B] [GrpObj B']
    {φ : B'.left ⟶ B.left} (h : IsGrpPullback B' B t φ) {f : B ⟶ B} [IsMonHom f] {f' : B' ⟶ B'}
    (e : f'.left ≫ φ = φ ≫ f.left) : IsMonHom f' := by
  have h1 : ∀ (X : Over T'), (1 : X ⟶ B') ≫ f' = 1 := fun X => by
    have := mul_comp_lift h e (1 : X ⟶ B') 1
    rw [_root_.mul_one] at this
    exact mul_eq_left.1 this.symm
  refine ⟨?_, ?_⟩
  · have := h1 (𝟙_ _)
    simpa [Hom.one_def] using this
  · have := mul_comp_lift h e (fst B' B') (snd B' B')
    simpa [Hom.mul_def] using this

theorem unit_pull {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'}
    [GrpObj G'] {φ : G'.left ⟶ G.left} (hG : IsGrpPullback G' G f φ) :
    η[G'].left ≫ φ = f ≫ η[G].left := by
  have h := hG.2 (𝟙_ _) 1 1 (pushPt hG.1.w 1) (pushPt hG.1.w 1) rfl rfl
  rw [_root_.mul_one] at h
  have h3 : pushPt hG.1.w (1 : 𝟙_ (Over S') ⟶ G') * pushPt hG.1.w 1 = pushPt hG.1.w 1 :=
    Over.OverMorphism.ext h
  have h4 : (1 : 𝟙_ (Over S') ⟶ G').left ≫ φ = (1 : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G).left :=
    congrArg Over.Hom.left (mul_eq_left.1 h3)
  rw [one_left_eq, one_left_eq] at h4
  simpa using h4

theorem matEnd_pull : ∀ {T T' : Scheme.{0}} {t : T' ⟶ T} {B C : Over T} [GrpObj B] [GrpObj C] {B' C' : Over T'} [GrpObj B'] [GrpObj C'] {φB : B'.left ⟶ B.left} {χ : C'.left ⟶ C.left} (pr : Fin 8 → (B ⟶ C)) (pr' : Fin 8 → (B' ⟶ C')) (a b : Fin 8) (f₁ : B ⟶ B) (f₁' : B' ⟶ B'), IsGrpPullback B' B t φB → IsGrpPullback C' C t χ → (∀ w, (pr' w).left ≫ χ = φB ≫ (pr w).left) → f₁'.left ≫ φB = φB ≫ f₁.left → MatEnd pr a b f₁ → MatEnd pr' a b f₁' := by
  intro T T' t B C _ _ B' C' _ _ φB χ pr pr' a b f₁ f₁' hB hC hpr e hf
  obtain ⟨hm, hw⟩ := hf
  haveI := hm
  refine ⟨isMonHom_lift hB e, fun w => ?_⟩
  apply ext_of_pb hC
  have key : (f₁' ≫ pr' w).left ≫ χ = φB ≫ (f₁ ≫ pr w).left := by
    rw [Over.comp_left, Category.assoc, hpr, ← Category.assoc, e, Category.assoc, ← Over.comp_left]
  rw [key, hw w]
  split_ifs
  · exact (hpr b).symm
  · rw [one_left_eq, one_left_eq, ← Category.assoc, hB.1.w, Category.assoc, Category.assoc,
      unit_pull hC]

end GlobalTheory.MatEndPull

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndCharExistsOfIsMonHom
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Eq8

theorem endChar_exists_of_isMonHom (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (_hB : GlobalTheory.Mum.Base R)
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (_hG : IsSemiAbelian G) (D : DegData R (maximalIdeal R))
    (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (f : G ⟶ G) (hfm : IsMonHom f) :
    ∃ m, EndChar U f m := by
  have hr : ∀ x ∈ maximalIdeal R ^ (0 + 1), residue R x = 0 := fun x hx =>
    (residue_eq_zero_iff x).2 (Ideal.pow_le_self (Nat.succ_ne_zero 0) hx)
  have hp := isGrpPullback_pullback G (spMap (residue R))
  have e : ((Over.pullback (spMap (residue R))).map f).left ≫ pullback.fst G.hom (spMap (residue R)) =
      pullback.fst G.hom (spMap (residue R)) ≫ f.left := pullback.lift_fst _ _ _
  have hf₁ : IsMonHom ((Over.pullback (spMap (residue R))).map f) :=
    Out.PullGtPf.isMonHom_of_grpPullback hp hp f _ e
  obtain ⟨m, hm⟩ := (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U.gt 0) hr hp).2 _
    (GlobalTheory.TorusPart.gtTorus (U.gt 0) hr hp ≫ (Over.pullback (spMap (residue R))).map f) inferInstance
  refine ⟨m, fun κ _ a ha G₀ _ φ h f₀ hf => ?_⟩
  let σ : ResidueField R →+* κ := Ideal.Quotient.lift _ a fun x hx => ha x (by simpa using hx)
  have ea : a = σ.comp (residue R) := RingHom.ext fun _ => rfl
  have es : spMap a = spMap σ ≫ spMap (residue R) := by rw [← Spec.map_comp]; rfl
  let ψ : G₀.left ⟶ ((Over.pullback (spMap (residue R))).obj G).left :=
    pullback.lift φ (G₀.hom ≫ spMap σ) (by rw [Category.assoc, ← es, h.1.w])
  have hψ : ψ ≫ pullback.fst G.hom (spMap (residue R)) = φ := pullback.lift_fst _ _ _
  have k : IsGrpPullback G₀ ((Over.pullback (spMap (residue R))).obj G) (spMap σ) ψ :=
    hp.cancel (h.congr es hψ.symm) (pullback.lift_snd _ _ _)
  have e₀ : f₀.left ≫ ψ = ψ ≫ ((Over.pullback (spMap (residue R))).map f).left := hp.1.hom_ext
    (by rw [Category.assoc, hψ, hf, Category.assoc, e, ← Category.assoc, hψ])
    (by rw [Category.assoc, k.1.w, ← Category.assoc, Over.w, Category.assoc, Over.w, k.1.w])
  rw [← GlobalTheory.TorusPart.pullTorus_gtTorus (U.gt 0) hr ha hp h k ea hψ.symm,
    ← GlobalTheory.TorusPart.pullTorus_comp k k _ f₀ e₀, hm, GlobalTheory.TorusPart.pullTorus_torusMap_comp]

end GlobalTheory.Poinc.Eq8
end
end

