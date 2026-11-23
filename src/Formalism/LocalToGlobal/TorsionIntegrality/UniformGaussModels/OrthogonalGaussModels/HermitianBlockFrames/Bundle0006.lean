module

public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.Bundle0005
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.Bundle0003
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.Bundle0002

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.BlockDiagMulBlockShift
section
noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
open Formalism.L2.Th1.Top.FrP

section Blocks
variable {n : Type} [Fintype n] [DecidableEq n]

def mv {R : Type*} [Zero R] [One R] (a : Fin 4) : Matrix (Fin 4 × n) (Fin 4 × n) R :=
  fun x y => if x.1 = a ∧ y.1 = 0 ∧ x.2 = y.2 then 1 else 0

theorem mv_mul_apply {R : Type*} [CommRing R] (a : Fin 4) (G : Matrix (Fin 4 × n) (Fin 4 × n) R)
    (z w : Fin 4 × n) : ((mv a : Matrix (Fin 4 × n) (Fin 4 × n) R) * G) z w = if z.1 = a then G (0, z.2) w else 0 := by
  simp only [Matrix.mul_apply, mv]
  by_cases h : z.1 = a
  · rw [Fintype.sum_eq_single (0, z.2)]
    · simp [h]
    · intro y hy
      rw [if_neg, zero_mul]
      rintro ⟨-, h0, h2⟩
      exact hy (Prod.ext h0 h2.symm)
  · simp [h]

theorem blockShift_mul_apply {R : Type*} [CommRing R] (k : Fin 4) (G : Matrix (Fin 4 × n) (Fin 4 × n) R)
    (z w : Fin 4 × n) : ((bmv0 k : Matrix (Fin 4 × n) (Fin 4 × n) R) * G) z w = if z.1 = 0 then G (k, z.2) w else 0 := by
  simp only [Matrix.mul_apply, bmv0]
  by_cases h : z.1 = 0
  · rw [Fintype.sum_eq_single (k, z.2)]
    · simp [h]
    · intro y hy
      rw [if_neg, zero_mul]
      rintro ⟨-, h0, h2⟩
      exact hy (Prod.ext h0 h2.symm)
  · simp [h]

theorem mv_mulVec (a : Fin 4) (y : Fin 4 × n → ℂ) :
    (mv a : Matrix _ _ ℂ).mulVec y = fun x => if x.1 = a then y (0, x.2) else 0 := by
  funext x
  simp only [Matrix.mulVec, dotProduct, mv]
  by_cases h : x.1 = a
  · rw [Fintype.sum_eq_single (0, x.2)]
    · simp [h]
    · intro z hz
      rw [if_neg, zero_mul]
      rintro ⟨-, h0, h2⟩
      exact hz (Prod.ext h0 h2.symm)
  · simp [h]

theorem blockShift_mulVec (k : Fin 4) (y : Fin 4 × n → ℂ) :
    (bmv0 k : Matrix _ _ ℂ).mulVec y = fun x => if x.1 = 0 then y (k, x.2) else 0 := by
  funext x
  simp only [Matrix.mulVec, dotProduct, bmv0]
  by_cases h : x.1 = 0
  · rw [Fintype.sum_eq_single (k, x.2)]
    · simp [h]
    · intro z hz
      rw [if_neg, zero_mul]
      rintro ⟨-, h0, h2⟩
      exact hz (Prod.ext h0 h2.symm)
  · simp [h]

theorem mv_pres (Λ : AddSubgroup (n → ℂ)) (a : Fin 4) :
    ∀ y ∈ pow4 Λ, Matrix.toLin' (mv a : Matrix _ _ ℂ) y ∈ pow4 Λ := by
  intro y hy
  have hy' : ∀ b, slice b y ∈ Λ := hy
  show ∀ b, slice b _ ∈ Λ
  intro b
  rw [Matrix.toLin'_apply, mv_mulVec]
  by_cases h : b = a
  · subst h
    convert hy' 0 using 1
    funext i
    simp [slice]
  · convert Λ.zero_mem using 1
    funext i
    simp [slice, h]

theorem blockShift_mapsTo (Λ : AddSubgroup (n → ℂ)) (k : Fin 4) :
    ∀ y ∈ pow4 Λ, Matrix.toLin' (bmv0 k : Matrix _ _ ℂ) y ∈ pow4 Λ := by
  intro y hy
  have hy' : ∀ b, slice b y ∈ Λ := hy
  show ∀ b, slice b _ ∈ Λ
  intro b
  rw [Matrix.toLin'_apply, blockShift_mulVec]
  by_cases h : b = 0
  · subst h
    convert hy' k using 1
    funext i
    simp [slice]
  · convert Λ.zero_mem using 1
    funext i
    simp [slice, h]

theorem bd4_transpose {R : Type*} [Zero R] (P : Matrix n n R) : (bd4 P).transpose = bd4 P.transpose := by
  ext x y
  by_cases h : x.1 = y.1
  · simp [bd4, Matrix.transpose_apply, h]
  · simp [bd4, Matrix.transpose_apply, h, Ne.symm h]

theorem bd4_smul {R : Type*} [CommRing R] (c : R) (P : Matrix n n R) : bd4 (c • P) = c • bd4 P := by
  ext x y
  by_cases h : x.1 = y.1 <;> simp [bd4, h]

theorem bd4_one {R : Type*} [CommRing R] : bd4 (1 : Matrix n n R) = 1 := by
  ext x y
  by_cases h1 : x.1 = y.1 <;> by_cases h2 : x.2 = y.2 <;>
    simp [bd4, Matrix.one_apply, Prod.ext_iff, h1, h2]

theorem blockDiag_mul_blockShift {R : Type*} [CommRing R] (P : Matrix n n R) (k : Fin 4) :
    bd4 P * bmv0 k = bmv0 k * bd4 P := by
  ext x y
  rw [blockShift_mul_apply]
  simp only [Matrix.mul_apply, bd4, bmv0]
  rw [Fintype.sum_eq_single (0, y.2)]
  · by_cases h1 : x.1 = 0 <;> by_cases h2 : y.1 = k
    · simp [h1, h2]
    · have h2' : k ≠ y.1 := fun h => h2 h.symm
      simp [h1, h2, h2']
    · simp [h1, h2]
    · simp [h1, h2]
  · intro z hz
    by_cases hc : z.1 = 0 ∧ y.1 = k ∧ z.2 = y.2
    · exact absurd (Prod.ext hc.1 hc.2.2 : z = (0, y.2)) hz
    · rw [if_neg hc, mul_zero]

theorem exists_cols (G Gi : Matrix (Fin 4 × n) (Fin 4 × n) ℂ) (hG : G * Gi = 1) :
    ∃ w : n → Fin 4 × n, IsUnit (Matrix.of fun i j => G (0, i) (w j)) := by
  classical
  set v : Fin 4 × n → (n → ℂ) := fun j i => G (0, i) j with hv
  have hspan : Submodule.span ℂ (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x = ∑ j, (∑ k, Gi j (0, k) * x k) • v j := by
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hv]
      have h : ∀ k, ∑ j, G (0, i) j * Gi j (0, k) = if i = k then 1 else 0 := fun k => by
        have := congrFun (congrFun hG (0, i)) (0, k)
        simpa [Matrix.mul_apply, Matrix.one_apply] using this
      symm
      calc ∑ j, (∑ k, Gi j (0, k) * x k) * G (0, i) j
          = ∑ k, (∑ j, G (0, i) j * Gi j (0, k)) * x k := by
            simp_rw [Finset.sum_mul]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
        _ = x i := by simp [h]
    rw [hx]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨b, hbs, hbspan, hbli⟩ := exists_linearIndependent ℂ (Set.range v)
  rw [hspan] at hbspan
  let B := Module.Basis.mk hbli (le_of_eq (by rw [Subtype.range_coe, hbspan]))
  let e := B.indexEquiv (Pi.basisFun ℂ n)
  have hmem : ∀ i : n, ∃ j, v j = ((e.symm i : b) : n → ℂ) := fun i => hbs (e.symm i).2
  choose w hw using hmem
  refine ⟨w, ?_⟩
  rw [← Matrix.linearIndependent_cols_iff_isUnit]
  have hfun : (Matrix.of fun i j => G (0, i) (w j)).col =
      (fun x : b => (x : n → ℂ)) ∘ e.symm := by
    funext j i
    simp [Matrix.col, Matrix.transpose_apply, ← hw j, hv]
  rw [hfun]
  exact hbli.comp _ e.symm.injective

end Blocks

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.TransposeMulBlockDiagMul
section
noncomputable section
open scoped BigOperators
open Matrix

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Loc
open Formalism.L2.Th1.Top.FrP

section Blocks
variable {K : Type*} [CommRing K] {n : Type} [Fintype n] [DecidableEq n]

def what₂ {m : Type*} (X : Matrix (Fin 4 × n) m K) (b : Fin 4) : Matrix n m K := fun i w => X (b, i) w

theorem blockDiag_mul_apply' {m : Type*} [Fintype m] (P : Matrix n n K) (Q : Matrix (Fin 4 × n) m K)
    (a : Fin 4) (i : n) (w : m) : (bd4 P * Q) (a, i) w = ∑ j, P i j * Q (a, j) w := by
  simp only [bd4, Matrix.mul_apply, Fintype.sum_prod_type, ite_mul, zero_mul]
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

theorem mul_bd4_apply {m : Type*} [Fintype m] (X : Matrix m (Fin 4 × n) K) (P : Matrix n n K)
    (x : m) (a : Fin 4) (j : n) : (X * bd4 P) x (a, j) = ∑ k, X x (a, k) * P k j := by
  simp only [bd4, Matrix.mul_apply, Fintype.sum_prod_type, mul_ite, mul_zero]
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [hb]) (by simp)]
  simp

theorem transpose_mul_blockDiag_mul {m m' : Type*} [Fintype m] [Fintype m'] (X : Matrix (Fin 4 × n) m K)
    (Y : Matrix (Fin 4 × n) m' K) (H : Matrix n n K) :
    Xᵀ * bd4 H * Y = ∑ b : Fin 4, (what₂ X b)ᵀ * H * what₂ Y b := by
  ext w w'
  rw [Matrix.sum_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_bd4_apply]
  simp only [what₂, Matrix.mul_apply, transpose_apply]

theorem blockShift_mul_apply {m : Type*} [Fintype m] (c : Fin 4) (X : Matrix (Fin 4 × n) m K) (b : Fin 4) (i : n)
    (w : m) : ((bmv0 c : Matrix (Fin 4 × n) (Fin 4 × n) K) * X) (b, i) w = if b = 0 then X (c, i) w else 0 := by
  simp only [bmv0, Matrix.mul_apply, ite_mul, one_mul, zero_mul]
  by_cases hb : b = 0
  · rw [if_pos hb, Finset.sum_eq_single (c, i)]
    · simp [hb]
    · rintro ⟨b', j⟩ _ hne
      rw [if_neg]
      rintro ⟨-, h1, h2⟩
      exact hne (Prod.ext h1 h2.symm)
    · simp
  · rw [if_neg hb]
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [if_neg]
    rintro ⟨h, -⟩
    exact hb h

theorem blockDiag_map' {L : Type*} [CommRing L] (f : K →+* L) (P : Matrix n n K) : (bd4 P).map f = bd4 (P.map f) := by
  ext x y
  simp only [bd4, Matrix.map_apply]
  split_ifs <;> simp

theorem bd4_transpose (P : Matrix n n K) : (bd4 P)ᵀ = bd4 Pᵀ := by
  ext x y
  simp only [bd4, transpose_apply]
  split_ifs with h1 h2 h2 <;> first | rfl | exact absurd h1.symm h2 | exact absurd h2.symm h1

theorem blockDiag_mul' (P Q : Matrix n n K) : bd4 P * bd4 Q = bd4 (P * Q) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  rw [blockDiag_mul_apply']
  simp only [bd4, Matrix.mul_apply]
  split_ifs with h <;> simp

theorem bd4_smul (r : K) (P : Matrix n n K) : bd4 (r • P) = r • bd4 P := by
  ext x y
  simp only [bd4, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

end Blocks

section Lmat
variable {l : ℕ} [Fact l.Prime] {m m' : Type}

theorem lmat_apply (δ : MaximalUnramifiedExtension l) (A B : Matrix m m' ℚ) (x : m) (y : m') :
    lmat δ A B x y = (A x y : MaximalUnramifiedExtension l) + δ * (B x y : MaximalUnramifiedExtension l) := by
  simp [lmat]

theorem lmat_map_σ (σ : MaximalUnramifiedExtension l →+* MaximalUnramifiedExtension l) (δ : MaximalUnramifiedExtension l) (hσδ : σ δ = -δ) (A B : Matrix m m' ℚ) :
    (lmat δ A B).map σ = lmat δ A (-B) := by
  ext x y
  simp only [Matrix.map_apply, lmat_apply, map_add (f := _), map_mul, map_ratCast, hσδ, Matrix.neg_apply, Rat.cast_neg]
  ring

theorem lmat_mem {dK : ℕ} {δ : MaximalUnramifiedExtension l} {hδ : δ ^ 2 = -(dK : MaximalUnramifiedExtension l)} (U₁ U₂ : Matrix m m' ℚ)
    (hU : ∀ x y, padicNorm l (U₁ x y) ≤ 1 ∧ padicNorm l (U₂ x y) ≤ 1) (x : m) (y : m') :
    lmat δ U₁ U₂ x y ∈ OO dK δ hδ := by
  rw [lmat_apply]
  exact (OO dK δ hδ).add_mem (ratCast_mem _ (hU x y).1) ((OO dK δ hδ).mul_mem δ_mem (ratCast_mem _ (hU x y).2))

end Lmat

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame.Loc
end
end

