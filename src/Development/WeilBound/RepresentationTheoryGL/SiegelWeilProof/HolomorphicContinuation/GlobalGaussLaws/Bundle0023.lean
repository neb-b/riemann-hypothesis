module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0020
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0018
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0009
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0019

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.LevFUnitary
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.VacH

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.Glob PositivityTheory.Rg.Sw.Glob.VacS PositivityTheory.Rg.Sw.Glob.VacB PositivityTheory.Rg.Sw.Glob.VacC
  PositivityTheory.Rg.Sw.Glob.VacD PositivityTheory.Rg.Sw.Glob.VacE PositivityTheory.Rg.Sw.Glob.VacF PositivityTheory.Rg.Sw.Glob.VacG

theorem row_norm {n : ℕ} (u : Matrix (Fin n) (Fin n) ℂ) (hu : u * uᴴ = 1) (x : Fin n → ℂ) :
    ∑ j, ((‖∑ k, x k * u k j‖ ^ 2 : ℝ) : ℂ) = ∑ k, ((‖x k‖ ^ 2 : ℝ) : ℂ) := by
  have h1 : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
    intro z
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp only [h1]
  have hu2 : ∀ k l, ∑ j, u k j * star (u l j) = if k = l then 1 else 0 := by
    intro k l
    have h := congrFun (congrFun hu k) l
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] using h
  calc ∑ j, (∑ k, x k * u k j) * star (∑ k, x k * u k j)
      = ∑ j, ∑ k, ∑ l, x k * star (x l) * (u k j * star (u l j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [star_sum, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
        rw [star_mul']
        ring
    _ = ∑ k, ∑ l, x k * star (x l) * ∑ j, u k j * star (u l j) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ k, x k * star (x k) := by
        simp only [hu2, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem levF_unitary {m n : ℕ} (e : ℤ) (u : Matrix (Fin n) (Fin n) ℂ) (hu : uᴴ * u = 1) (K γ0 : ℂ) :
    levF e u (DG (m := m) (n := n) K (fun _ _ => γ0)) =
      DG (K * (u.det ^ e * (star u.det) ^ ((m : ℤ) - e))) (fun _ _ => γ0) := by
  funext v
  have hu' : u * uᴴ = 1 := mul_eq_one_comm.mp hu
  have key : ∀ a : Fin m, ∏ j : Fin n, Complex.exp (-γ0 * ((‖(Matrix.of v * u) a j‖ ^ 2 : ℝ) : ℂ))
      = ∏ j : Fin n, Complex.exp (-γ0 * ((‖v a j‖ ^ 2 : ℝ) : ℂ)) := by
    intro a
    rw [← Complex.exp_sum, ← Complex.exp_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    congr 2
    simpa [Matrix.mul_apply] using row_norm u hu' (v a)
  simp only [levF, DG, key]
  ring

theorem dbl_angle (ρ x : ℝ) (hρ : ρ ^ 2 = 1) :
    ((Real.cos (x / 2) : ℂ) + Complex.I * (ρ : ℂ) * (Real.sin (x / 2) : ℂ)) *
      ((Real.cos (x / 2) : ℂ) + Complex.I * (ρ : ℂ) * (Real.sin (x / 2) : ℂ)) =
    (Real.cos x : ℂ) + Complex.I * (ρ : ℂ) * (Real.sin x : ℂ) := by
  have hc := Real.cos_two_mul (x / 2)
  have hs := Real.sin_two_mul (x / 2)
  have hp := Real.sin_sq_add_cos_sq (x / 2)
  rw [show 2 * (x / 2) = x by ring] at hc hs
  rw [hc, hs]
  generalize Real.cos (x / 2) = c at *
  generalize Real.sin (x / 2) = s at *
  push_cast
  have hp' : (s : ℂ) ^ 2 + (c : ℂ) ^ 2 = 1 := by exact_mod_cast hp
  have hρ' : (ρ : ℂ) ^ 2 = 1 := by exact_mod_cast hρ
  linear_combination (-1 : ℂ) * hp' + (s : ℂ) ^ 2 * (ρ : ℂ) ^ 2 * Complex.I_sq - (s : ℂ) ^ 2 * hρ'

end PositivityTheory.Rg.Sw.Glob.VacH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.PIn
section
noncomputable section

open GlobalTheory.StdUnn

namespace PositivityTheory.Rg.Sw.Glob

theorem pIn : PIn := by
  intro D n p hp
  obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hp
  obtain ⟨m, u, b, e, hm, hu⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_levi_unip hp a ha
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inr (Or.inl ⟨_, _, hm⟩)))
    (Subgroup.subset_closure (Or.inl ⟨b, hu⟩))

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.SiegelParabolicUnnMatrixBlockUpperTriangular
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.GlobalGaussBlockRelations

variable {D : D7} {n : ℕ}

def bA (M : Mx D (n + n) (n + n)) : Mx D n n := (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁

def bB (M : Mx D (n + n) (n + n)) : Mx D n n := (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂

def bC (M : Mx D (n + n) (n + n)) : Mx D n n := (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁

theorem siegelParabolicUnn_matrix_blockUpperTriangular (M : Mx D (n + n) (n + n)) : M = blk4 (bA M) (bB M) (bC M) (blkDm M) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j <;> rfl

theorem rel1 (g : G D n) : adj (mat g) * blk4 0 1 (-1) 0 * mat g = blk4 0 1 (-1) 0 := by
  have h : adj (mat g) * JR (AF D.host.F) (Jst D n) * mat g = JR (AF D.host.F) (Jst D n) := g.2
  rwa [JR_Jst] at h

theorem JJ_sq : (blk4 0 1 (-1) 0 : Mx D (n + n) (n + n)) * blk4 0 1 (-1) 0 = -1 := by
  rw [submatrix_fromBlocks_mul]
  simp only [mul_one, zero_add, add_zero, mul_neg, mul_zero, neg_zero]
  rw [← block_matrix_one (R := AE D) (n := n)]
  unfold blk4
  rw [show Matrix.fromBlocks (-1 : Mx D n n) 0 0 (-1) = -Matrix.fromBlocks 1 0 0 1 by
    rw [Matrix.fromBlocks_neg]; simp, Matrix.submatrix_neg]
  rfl

set_option maxHeartbeats 1000000 in
theorem rel2 (g : G D n) : mat g * blk4 0 1 (-1) 0 * adj (mat g) = blk4 0 1 (-1) 0 := by
  have hMN : mat g * mat g⁻¹ = 1 := by
    rw [show mat g * mat g⁻¹ = mat (g * g⁻¹) from rfl, mul_inv_cancel]; rfl
  have h1 := rel1 g
  have hJ : (blk4 0 1 (-1) 0 : Mx D (n + n) (n + n)) * blk4 0 1 (-1) 0 = -1 := JJ_sq
  generalize (blk4 0 1 (-1) 0 : Mx D (n + n) (n + n)) = J at h1 hJ ⊢
  generalize mat g⁻¹ = N at hMN
  generalize mat g = M at hMN h1 ⊢
  have h2 : adj M * J = J * N := by
    calc adj M * J = adj M * J * (M * N) := by rw [hMN, mul_one]
      _ = (adj M * J * M) * N := by simp only [mul_assoc]
      _ = J * N := by rw [h1]
  have h3 : N = -(J * adj M * J) := by
    have : J * (adj M * J) = J * (J * N) := by rw [h2]
    rw [← mul_assoc, ← mul_assoc, hJ] at this
    rw [this, neg_mul, one_mul, neg_neg]
  have h4 : M * (J * adj M * J) = -1 := by
    have : M * N = 1 := hMN
    rw [h3, mul_neg] at this
    rw [← neg_neg (M * (J * adj M * J)), this]
  have h5 : M * J * adj M * J = -1 := by rw [← h4]; simp only [mul_assoc]
  calc M * J * adj M = -(M * J * adj M * (J * J)) := by rw [hJ, mul_neg, mul_one, neg_neg]
    _ = -((M * J * adj M * J) * J) := by rw [mul_assoc (M * J * adj M) J J]
    _ = J := by rw [h5, neg_mul, one_mul, neg_neg]

set_option maxHeartbeats 1000000 in
theorem blockRels (g : G D n) :
    adj (bB (mat g)) * blkDm (mat g) = adj (blkDm (mat g)) * bB (mat g) ∧
    adj (bA (mat g)) * blkDm (mat g) - adj (bC (mat g)) * bB (mat g) = 1 ∧
    blkDm (mat g) * adj (bC (mat g)) = bC (mat g) * adj (blkDm (mat g)) ∧
    bA (mat g) * adj (blkDm (mat g)) - bB (mat g) * adj (bC (mat g)) = 1 := by
  have h1 := rel1 g
  have h2 := rel2 g
  rw [siegelParabolicUnn_matrix_blockUpperTriangular (mat g)] at h1 h2
  generalize bA (mat g) = A at h1 h2 ⊢
  generalize bB (mat g) = B at h1 h2 ⊢
  generalize bC (mat g) = C at h1 h2 ⊢
  generalize blkDm (mat g) = Dd at h1 h2 ⊢
  rw [adelicConjTranspose_blockMatrixTwoByTwoFin, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul] at h1 h2
  simp only [mul_zero, mul_one, add_zero, zero_add, mul_neg, neg_mul] at h1 h2
  obtain ⟨-, e12, -, e22⟩ := blockMatrixTwoByTwoFin_injective h1
  obtain ⟨-, f12, -, f22⟩ := blockMatrixTwoByTwoFin_injective h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (neg_add_eq_zero.1 e22).symm
  · rw [← e12]; abel
  · exact neg_add_eq_zero.1 f22
  · rw [← f12]; abel

end PositivityTheory.Rg.Sw.Glob.GlobalGaussBlockRelations

namespace PositivityTheory.Rg.Sw.Glob

open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model GlobalTheory.MixModel

set_option maxHeartbeats 2000000 in
theorem unitD : UnitD := by
  intro D n g hD
  obtain ⟨r1, r2, r3, r4⟩ := GlobalGaussBlockRelations.blockRels g
  have hM := GlobalGaussBlockRelations.siegelParabolicUnn_matrix_blockUpperTriangular (mat g)
  generalize GlobalGaussBlockRelations.bA (mat g) = A at r1 r2 r3 r4 hM
  generalize GlobalGaussBlockRelations.bB (mat g) = B at r1 r2 r3 r4 hM
  generalize GlobalGaussBlockRelations.bC (mat g) = C at r1 r2 r3 r4 hM
  generalize blkDm (mat g) = Dd at r1 r2 r3 r4 hM hD
  obtain ⟨Di, hDi1, hDi2⟩ : ∃ Di : Mx D n n, Dd * Di = 1 ∧ Di * Dd = 1 :=
    ⟨Dd⁻¹, Matrix.mul_nonsing_inv Dd hD, Matrix.nonsing_inv_mul Dd hD⟩
  have hA1 : adj Di * adj Dd = 1 := by rw [← adj_mul, hDi1, adj_one]
  have hA2 : adj Dd * adj Di = 1 := by rw [← adj_mul, hDi2, adj_one]
  have hb : adj (B * Di) = B * Di := by
    rw [adj_mul]
    calc adj Di * adj B = adj Di * (adj B * Dd) * Di := by simp only [mul_assoc, hDi1, mul_one]
      _ = adj Di * (adj Dd * B) * Di := by rw [r1]
      _ = B * Di := by rw [← mul_assoc (adj Di), hA1, one_mul]
  have hc : adj (Di * C) = Di * C := by
    rw [adj_mul]
    calc adj C * adj Di = Di * (Dd * adj C) * adj Di := by simp only [← mul_assoc, hDi2, one_mul]
      _ = Di * (C * adj Dd) * adj Di := by rw [r3]
      _ = Di * C := by simp only [mul_assoc, hA2, mul_one]
  have ha1 : (A - B * Di * C) * adj Dd = 1 := by
    rw [sub_mul, mul_assoc (B * Di) C (adj Dd), ← r3, ← mul_assoc (B * Di) Dd (adj C), mul_assoc B Di Dd, hDi2,
      mul_one, r4]
  have ha2 : adj Dd * (A - B * Di * C) = 1 := mul_eq_one_comm.mp ha1
  let aG : GL (Fin n) (AE D) := ⟨A - B * Di * C, adj Dd, ha1, ha2⟩
  obtain ⟨m, hm⟩ := exists_levi aG
  have hm' : mat m = blk4 (A - B * Di * C) 0 0 Dd := by
    rw [hm]
    show blk4 (A - B * Di * C) 0 0 (adj (adj Dd)) = _
    rw [adj_adj]
  obtain ⟨u, hu⟩ := (exists_unip (B * Di)).2 hb
  obtain ⟨v, hv⟩ : ∃ v : G D n, mat v = blk4 1 0 (Di * C) 1 := by
    refine exists_mat _ (blk4 1 0 (-(Di * C)) 1) ?_ ?_ ?_
    · rw [submatrix_fromBlocks_mul]
      simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, add_zero, zero_add, add_neg_cancel]
      exact block_matrix_one
    · rw [submatrix_fromBlocks_mul]
      simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, add_zero, zero_add, neg_add_cancel]
      exact block_matrix_one
    · rw [adelicConjTranspose_blockMatrixTwoByTwoFin, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, hc]
      simp only [adj_one, adj_zero, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul, add_zero, zero_add,
        Matrix.mul_neg, neg_add_cancel]
  have hg : g = u * m * v := by
    apply Subtype.ext
    apply Units.ext
    show mat g = mat u * mat m * mat v
    rw [hM, hu, hm', hv, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
    simp only [one_mul, mul_one, mul_zero, zero_mul, add_zero, zero_add]
    have e1 : B * Di * Dd = B := by rw [mul_assoc, hDi2, mul_one]
    have e2 : Dd * (Di * C) = C := by rw [← mul_assoc, hDi1, one_mul]
    rw [e1, e2, mul_assoc B Di C, sub_add_cancel]
  rw [hg]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl ⟨_, hu⟩))
    (Subgroup.subset_closure (Or.inr (Or.inl ⟨_, _, hm'⟩)))) (Subgroup.subset_closure (Or.inr (Or.inr ⟨_, hv⟩)))

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.TraceGramBReal
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob.DilAH

variable {D : D7} {n : ℕ}

theorem cLoc_pos {l : D.what₂.Tau → ℝ} {τ : D.what₂.Tau} (h : l τ ≠ 0) : 0 < cLoc l τ := by
  unfold cLoc; have := abs_pos.2 h; positivity

theorem abs_tLoc (l : D.what₂.Tau → ℝ) (τ : D.what₂.Tau) : |tLoc l τ| = cLoc l τ := by
  unfold tLoc cLoc; rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]

theorem trace_gramB_real {m : ℕ} (ε : Fin m → Bool) (b : Bool) (u : Fin m → Fin n → ℂ) :
    (gramB ε b u).trace = ((∑ a ∈ Finset.univ.filter (fun a => ε a = b), ∑ j, ‖u a j‖ ^ 2 : ℝ) : ℂ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gramB, evX, Qb, map_sum, map_mul, MvPolynomial.eval_X, if_true, Bool.false_eq_true, if_false,
    Matrix.trace, Matrix.diag]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.conj_mul', Complex.star_def]

theorem sum_filter_bool {m : ℕ} (ε : Fin m → Bool) (f : Fin m → ℝ) :
    ∑ a ∈ Finset.univ.filter (fun a => ε a = true), f a + ∑ a ∈ Finset.univ.filter (fun a => ε a = false), f a =
      ∑ a, f a := by
  rw [← Finset.sum_union]
  · congr 1; ext a; cases ε a <;> simp
  · rw [Finset.disjoint_filter]; intro a _ h; simp [h]

theorem gC_gauss {m : ℕ} (ε : Fin m → Bool) (t c : ℝ) (hc : 0 < c) (δ : ℝ) (u : Fin m → Fin n → ℂ) :
    gC ε t c ((Complex.I * (δ / c : ℝ)) • 1) ((-(Complex.I * (δ / c : ℝ))) • 1) u =
      Complex.exp (-((δ * ∑ a, ∑ j, ‖u a j‖ ^ 2 : ℝ) : ℂ)) := by
  unfold gC
  congr 1
  simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul, trace_gramB_real]
  have h := sum_filter_bool (epsT t ε) (fun a => ∑ j, ‖u a j‖ ^ 2)
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [← h]
  push_cast
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

theorem fP_one {m : ℕ} (ε : Fin m → Bool) (t c : ℝ) (hc : 0 < c) :
    fP c (1 : PX m n) = gZf ε t c (Complex.I • 1) := by
  funext u
  have e1 : gZf ε t c (Complex.I • 1) u = gC ε t c ((Complex.I * (c / c : ℝ)) • 1) ((-(Complex.I * (c / c : ℝ))) • 1) u := by
    unfold gZf gC
    rw [div_self hc.ne', Complex.ofReal_one, mul_one, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
      Complex.star_def, Complex.conj_I]
  rw [e1, gC_gauss ε t c hc c u]
  simp [fP, evX, gs]

end PositivityTheory.Rg.Sw.Glob.DilAH
end
end

