module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.ZzMinusSecondProjTranspose
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.DetSmulMk

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.DuForm
section
noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

theorem map_inv_of {K L : Type} [CommRing K] [CommRing L] {n : Type} [Fintype n] [DecidableEq n]
    (f : K →+* L) (A : Matrix n n K) (hA : IsUnit A.det) : (A⁻¹).map f = (A.map f)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul A hA, Matrix.map_one f f.map_zero f.map_one]

theorem splitFirstProj_conj (x : E) : ph1 g (M.L.cj x) = ph2 g x := by
  change (g.e (M.L.cj x)).1 = (g.e x).2
  rw [g.e_cj]
  rfl

theorem splitFirstProj_algebraMap (a : F) : ph1 g (algebraMap F E a) = a := by
  change (g.e (algebraMap F E a)).1 = a
  rw [AlgEquiv.commutes]
  rfl

def gHat (g : SplitG M.L) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) : Matrix (Ix r) (Ix r) F :=
  Matrix.fromBlocks (Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then -T else 0)
    (Zh.map (ph2 g)) (Zh.map (ph1 g)).transpose
    (Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then -T' else 0)

def pM (r : ℕ) (x : F) : Matrix (Ix r) (Ix r) F := Matrix.fromBlocks 1 (-x • 1) 0 (x • 1)

theorem map_gramG (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    (gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) Zh (algebraMap F E T) (algebraMap F E T')).map
        (ph1 g) = (pM r (g.q : F)⁻¹).transpose * gHat g Zh T T' * pM r (g.q : F)⁻¹ := by
  simp only [gramG, gHat, pM, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.transpose_one, Matrix.transpose_zero, Matrix.transpose_smul,
    Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, Matrix.smul_mul, Matrix.mul_smul,
    add_zero, zero_add]
  congr 1 <;> ext a b <;>
    by_cases h : a = Fin.last r ∧ b = Fin.last r <;>
    simp [cor, h, splitFirstProj_conj, splitFirstProj_algebraMap, map_mul, map_add (f := _), map_neg, map_sub, Matrix.add_apply, Matrix.smul_apply, Matrix.neg_apply] <;>
    ring

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.FormInverseCounting.LamSMulVec
section
noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (O : Subring E) (cj : E →+* E) {r : ℕ}

theorem bRaw_e (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (y : Fin (r + 1) → O) :
    bRaw O cj Z y (Pi.single (Fin.last r) 1) = lamL O Z y := by
  unfold bRaw
  rw [Finset.sum_eq_single (Fin.last r)]
  · simp [lamL, lamC]
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · simp

theorem bRaw_b_mem (hcj : ∀ x, cj (cj x) = x) (hO : ∀ x ∈ O, cj x ∈ O)
    (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hu : IsUnit (Z.map O.subtype).det)
    (y : Fin (r + 1) → O) : bRaw O cj Z y (fun i => cjT O cj hO Z i (Fin.last r)) ∈ O := by
  unfold bRaw
  have hinv : (Z.map O.subtype) * (Z.map O.subtype)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have e : ∀ j, cj ((cjT O cj hO Z j (Fin.last r) : O) : E) = (Z.map O.subtype) (Fin.last r) j := fun j => hcj _
  simp only [e]
  rw [show ∑ j, (Z.map O.subtype) (Fin.last r) j * ((Z.map O.subtype)⁻¹.mulVec (fun i => (y i : E))) j =
      ((Z.map O.subtype).mulVec ((Z.map O.subtype)⁻¹.mulVec (fun i => (y i : E)))) (Fin.last r) from rfl,
    Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  exact (y _).2

theorem lamS_mulVec (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hO : ∀ x ∈ O, cj x ∈ O)
    (hu : IsUnit (Z.map O.subtype).det) (w : Fin (r + 1) → O) :
    lamS O cj Z ((cjT O cj hO Z).mulVec w) = (w (Fin.last r) : E) := by
  unfold lamS lamStarC
  have hinv : (Z.map O.subtype) * (Z.map O.subtype)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hcoe : ∀ b, (((cjT O cj hO Z).mulVec w b : O) : E) = ∑ c, cj ((Z c b : O) : E) * (w c : E) := by
    intro b
    simp [Matrix.mulVec, dotProduct, cjT]
  simp only [hcoe, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hrow : ∀ c, ∑ b, cj ((Z.map O.subtype)⁻¹ b (Fin.last r)) * (cj ((Z c b : O) : E) * (w c : E)) =
      cj (if c = Fin.last r then 1 else 0) * (w c : E) := by
    intro c
    have h1 := congrFun (congrFun hinv c) (Fin.last r)
    rw [Matrix.mul_apply, Matrix.one_apply] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h1, map_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    rw [map_mul]
    simp only [Matrix.map_apply, Subring.coe_subtype]
    ring
  rw [Finset.sum_congr rfl (fun c _ => hrow c)]
  simp [apply_ite cj]

theorem lamS_K (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hO : ∀ x ∈ O, cj x ∈ O)
    (hu : IsUnit (Z.map O.subtype).det) (k : Fin (r + 1) → O)
    (hk : k ∈ headCols (cjT O cj hO Z)) : lamS O cj Z k = 0 := by
  unfold headCols at hk
  have hinv : (Z.map O.subtype) * (Z.map O.subtype)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  induction hk using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    unfold lamS lamStarC
    have h1 := congrFun (congrFun hinv a.castSucc) (Fin.last r)
    rw [Matrix.mul_apply, Matrix.one_apply_ne (Fin.castSucc_lt_last a).ne] at h1
    have key : ∑ b, cj ((Z.map O.subtype)⁻¹ b (Fin.last r)) * ((cjT O cj hO Z b a.castSucc : O) : E) =
        cj (∑ b, (Z.map O.subtype) a.castSucc b * (Z.map O.subtype)⁻¹ b (Fin.last r)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      apply Finset.sum_congr rfl
      intro b _
      rw [map_mul, mul_comm]
      rfl
    rw [key, h1, map_zero]
  | zero =>
    unfold lamS lamStarC
    simp
  | add x y _ _ hx hy =>
    unfold lamS lamStarC at hx hy ⊢
    simp only [Pi.add_apply, Subring.coe_add, mul_add, Finset.sum_add_distrib, hx, hy, add_zero]
  | smul c x _ hx =>
    unfold lamS lamStarC at hx ⊢
    calc ∑ b, cj ((Z.map O.subtype)⁻¹ b (Fin.last r)) * (((c • x) b : O) : E) =
          (c : E) * ∑ b, cj ((Z.map O.subtype)⁻¹ b (Fin.last r)) * ((x b : O) : E) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          simp only [Pi.smul_apply, smul_eq_mul, Subring.coe_mul]
          ring
      _ = 0 := by rw [hx, mul_zero]

theorem lamS_b (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O) (hO : ∀ x ∈ O, cj x ∈ O)
    (hu : IsUnit (Z.map O.subtype).det) :
    lamS O cj Z (fun i => cjT O cj hO Z i (Fin.last r)) = 1 := by
  unfold lamS lamStarC
  have hinv : (Z.map O.subtype) * (Z.map O.subtype)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have h1 := congrFun (congrFun hinv (Fin.last r)) (Fin.last r)
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at h1
  have key : ∑ b, cj ((Z.map O.subtype)⁻¹ b (Fin.last r)) * ((cjT O cj hO Z b (Fin.last r) : O) : E) =
      cj (∑ b, (Z.map O.subtype) (Fin.last r) b * (Z.map O.subtype)⁻¹ b (Fin.last r)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [map_mul, mul_comm]
    rfl
  rw [key, h1, map_one]

theorem lamS_e (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) O)
    (hκ : (Z.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0) :
    lamS O cj Z (Pi.single (Fin.last r) 1) = 0 := by
  unfold lamS lamStarC
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [hκ, map_zero, zero_mul]
  · intro b _ hb
    simp [Pi.single_apply, hb]
  · simp

variable (hcj : ∀ x, cj (cj x) = x) (hO : ∀ x ∈ O, cj x ∈ O)
variable {Z₁ Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) O}
include hcj

theorem pair_e (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (hκ₁ : (Z₁.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0)
    (hκ₂ : (Z₂.map O.subtype)⁻¹ (Fin.last r) (Fin.last r) = 0)
    (p : PairSet O cj hO Z₁ Z₂) : p.1.2 (eCl (cjT O cj hO Z₁)) = eCl (cjT O cj hO Z₂) := by
  obtain ⟨y₂', hy⟩ := Submodule.Quotient.mk_surjective _ (p.1.2 (eCl (cjT O cj hO Z₁)))
  rw [← hy, eCl, ← sub_eq_zero, ← Submodule.Quotient.mk_sub]
  apply mk_eq_zero_of O cj hcj hO Z₂ hu₂
  · intro y
    obtain ⟨y₁, hy₁⟩ := Submodule.Quotient.mk_surjective _ (p.1.1.symm (Submodule.Quotient.mk y))
    have e1 : p.1.1 (Submodule.Quotient.mk y₁) = Submodule.Quotient.mk y := by
      rw [hy₁]; exact p.1.1.apply_symm_apply _
    have A := p.2.2.2 y₁ (Pi.single (Fin.last r) 1) y y₂' e1 hy.symm
    rw [bRaw_e O cj Z₁, ← lam_keep O hu₁ hu₂ p.1.1.toLinearMap p.2.1.1 y₁ y e1] at A
    rw [bRaw_sub_right, bRaw_e]
    exact A
  · rw [lamS_sub, p.2.2.1 _ y₂' hy.symm, lamS_e O cj Z₁ hκ₁, lamS_e O cj Z₂ hκ₂, sub_zero]

theorem pair_b (hu₁ : IsUnit (Z₁.map O.subtype).det) (hu₂ : IsUnit (Z₂.map O.subtype).det)
    (p : PairSet O cj hO Z₁ Z₂) : p.1.2 (bCls (cjT O cj hO Z₁)) = bCls (cjT O cj hO Z₂) := by
  obtain ⟨y₂', hy⟩ := Submodule.Quotient.mk_surjective _ (p.1.2 (bCls (cjT O cj hO Z₁)))
  rw [← hy, bCls, ← sub_eq_zero, ← Submodule.Quotient.mk_sub]
  apply mk_eq_zero_of O cj hcj hO Z₂ hu₂
  · intro y
    obtain ⟨y₁, hy₁⟩ := Submodule.Quotient.mk_surjective _ (p.1.1.symm (Submodule.Quotient.mk y))
    have e1 : p.1.1 (Submodule.Quotient.mk y₁) = Submodule.Quotient.mk y := by
      rw [hy₁]; exact p.1.1.apply_symm_apply _
    have A := p.2.2.2 y₁ _ y y₂' e1 hy.symm
    rw [bRaw_sub_right]
    have B := O.add_mem A (bRaw_b_mem O cj hcj hO Z₁ hu₁ y₁)
    rw [sub_add_cancel] at B
    exact O.sub_mem B (bRaw_b_mem O cj hcj hO Z₂ hu₂ y)
  · rw [lamS_sub, p.2.2.1 _ y₂' hy.symm, lamS_b O cj Z₁ hO hu₁, lamS_b O cj Z₂ hO hu₂, sub_self]

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
end
end

