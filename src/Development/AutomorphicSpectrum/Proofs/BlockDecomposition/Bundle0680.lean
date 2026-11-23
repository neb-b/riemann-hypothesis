module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0657
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0655
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0595
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0557
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0437
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KFiniteVectorsDense
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0298
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0282
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0674

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeTranslationPreserved
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE.Transport

open GlobalTheory.StdUnn.Model (submatrix_fromBlocks_mul)
open GlobalTheory.CompanionTheory.ThTw (block_mul₂ bl_add mat_nzx_sh block_matrix_injective adj_sub')
open GlobalTheory.CompanionTheory.PcB (mat_mul' rational_map_block_matrix rat_one' rat_zero' rat_neg')
open GlobalTheory.CompanionTheory.FourierN (mat_injective)

variable {D : D7} {n ρ p : ℕ} {hn : ρ + p = n}

theorem adelicConjTranspose_blockMatrixTwoByTwoFin {k : ℕ} (a b c d : Mx D k k) :
    adj (blk4 a b c d) = blk4 (adj a) (adj c) (adj b) (adj d) := by
  simp only [adj, blk4]
  rw [← Matrix.submatrix_map, Matrix.transpose_submatrix, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]

theorem block_matrix_diagonal_one_eq_one {k : ℕ} : blk4 (1 : Mx D k k) 0 0 1 = 1 := by
  simp only [blk4, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem jr_eq {k : ℕ} : JR (AF D.host.F) (Jst D k) = (blk4 0 1 (-1) 0 : Mx D (k + k) (k + k)) := by
  show rat (blk4 0 1 (-1) 0) = _
  rw [rational_map_block_matrix, rat_one', rat_zero', rat_neg', rat_one']

theorem rel_left {k : ℕ} (g : G D k) {a b c d : Mx D k k} (h : mat g = blk4 a b c d) :
    adj d ⬝ a - adj b ⬝ c = 1 ∧ adj a ⬝ c = adj c ⬝ a ∧ adj b ⬝ d = adj d ⬝ b ∧ adj a ⬝ d - adj c ⬝ b = 1 := by
  have h2 : adj (mat g) * JR (AF D.host.F) (Jst D k) * mat g = JR (AF D.host.F) (Jst D k) := g.2
  rw [jr_eq, h, adelicConjTranspose_blockMatrixTwoByTwoFin, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul] at h2
  obtain ⟨e1, e2, e3, e4⟩ := block_matrix_injective h2
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_neg, add_zero, zero_add, Matrix.neg_mul] at e1 e2 e3 e4
  refine ⟨?_, (neg_add_eq_zero.1 e1).symm, (neg_add_eq_zero.1 e4).symm, ?_⟩
  · have : adj d ⬝ a - adj b ⬝ c = -(-(adj d ⬝ a) + adj b ⬝ c) := by abel
    rw [this, e3, neg_neg]
  · rw [sub_eq_neg_add, e2]

theorem rel_right {k : ℕ} (g : G D k) {a b c d : Mx D k k} (h : mat g = blk4 a b c d) :
    a ⬝ adj d - b ⬝ adj c = 1 ∧ c ⬝ adj d = d ⬝ adj c ∧ b ⬝ adj a = a ⬝ adj b ∧ d ⬝ adj a - c ⬝ adj b = 1 := by
  obtain ⟨l1, l2, l3, l4⟩ := rel_left g h
  have hL : (blk4 (adj d) (-adj b) (-adj c) (adj a) : Mx D (k + k) (k + k)) * blk4 a b c d = 1 := by
    rw [submatrix_fromBlocks_mul, ← block_matrix_diagonal_one_eq_one]
    congr 1
    · rw [Matrix.neg_mul, ← sub_eq_add_neg, l1]
    · rw [Matrix.neg_mul, ← sub_eq_add_neg, l3, sub_self]
    · rw [Matrix.neg_mul, l2, neg_add_cancel]
    · rw [Matrix.neg_mul, ← sub_eq_neg_add, l4]
  have hR := mul_eq_one_comm.1 hL
  rw [submatrix_fromBlocks_mul, ← block_matrix_diagonal_one_eq_one] at hR
  obtain ⟨e1, e2, e3, e4⟩ := block_matrix_injective hR
  simp only [Matrix.mul_neg] at e1 e2 e3 e4
  refine ⟨by rw [sub_eq_add_neg, e1], sub_eq_zero.1 (by rw [sub_eq_add_neg, e3]),
    (neg_add_eq_zero.1 e2).symm, by rw [sub_eq_neg_add, e4]⟩

theorem exists_rat_blocks {k : ℕ} (γ : G D k) (h : γ ∈ GF D k) :
    ∃ a b c d : Matrix (Fin k) (Fin k) D.host.E, mat γ = blk4 (rat a) (rat b) (rat c) (rat d) := by
  obtain ⟨x, -, hxe⟩ := h
  have hm : mat γ = rat x.1 := (congrArg Units.val hxe).symm
  refine ⟨(x.1.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁,
    (x.1.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂,
    (x.1.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁,
    (x.1.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂, ?_⟩
  rw [hm, ← rational_map_block_matrix]
  congr 1
  simp only [blk4, Matrix.fromBlocks_toBlocks, Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id]

theorem comb_sub (a b : Mx D ρ p) (P Q R S U V : Mx D p p) :
    (a ⬝ P - b ⬝ Q) ⬝ R + (b ⬝ S - a ⬝ U) ⬝ V = a ⬝ (P ⬝ R - U ⬝ V) + b ⬝ (S ⬝ V - Q ⬝ R) := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

theorem comb_add (a b : Mx D ρ p) (P Q R S U V : Mx D p p) :
    (a ⬝ P + b ⬝ Q) ⬝ R - (a ⬝ S + b ⬝ U) ⬝ V = a ⬝ (P ⬝ R - S ⬝ V) + b ⬝ (Q ⬝ R - U ⬝ V) := by
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

theorem cont_rmul (c : Mx D p p) : Continuous fun v : Mx D ρ p => v ⬝ c :=
  continuous_id.matrix_mul continuous_const

theorem cont_sub {X : Type*} [TopologicalSpace X] {f g : X → Mx D ρ p} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun v => f v - g v := by
  have h₁ : IsTopologicalRing (AE D) := inferInstance
  have h₂ : IsTopologicalAddGroup (AE D) := inferInstance
  have h₃ : ContinuousSub (AE D) := IsTopologicalAddGroup.to_continuousSub
  exact continuous_matrix fun i j => (hf.matrix_elem i j).sub (hg.matrix_elem i j)

theorem cont_add {X : Type*} [TopologicalSpace X] {f g : X → Mx D ρ p} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun v => f v + g v :=
  continuous_matrix fun i j => (hf.matrix_elem i j).add (hg.matrix_elem i j)

def tEquiv (a b c d : Mx D p p)
    (l1 : adj d ⬝ a - adj b ⬝ c = 1) (l2 : adj a ⬝ c = adj c ⬝ a) (l3 : adj b ⬝ d = adj d ⬝ b)
    (l4 : adj a ⬝ d - adj c ⬝ b = 1)
    (r1 : a ⬝ adj d - b ⬝ adj c = 1) (r2 : c ⬝ adj d = d ⬝ adj c) (r3 : b ⬝ adj a = a ⬝ adj b)
    (r4 : d ⬝ adj a - c ⬝ adj b = 1) :
    (Mx D ρ p × Mx D ρ p) ≃ₜ+ (Mx D ρ p × Mx D ρ p) where
  toFun v := (v.1 ⬝ adj d - v.2 ⬝ adj c, v.2 ⬝ adj a - v.1 ⬝ adj b)
  invFun v := (v.1 ⬝ a + v.2 ⬝ c, v.1 ⬝ b + v.2 ⬝ d)
  left_inv v := by
    refine Prod.ext ?_ ?_
    · show (v.1 ⬝ adj d - v.2 ⬝ adj c) ⬝ a + (v.2 ⬝ adj a - v.1 ⬝ adj b) ⬝ c = v.1
      rw [comb_sub, l1, l2, sub_self, Matrix.mul_one, Matrix.mul_zero, add_zero]
    · show (v.1 ⬝ adj d - v.2 ⬝ adj c) ⬝ b + (v.2 ⬝ adj a - v.1 ⬝ adj b) ⬝ d = v.2
      rw [comb_sub, l4, l3, sub_self, Matrix.mul_one, Matrix.mul_zero, zero_add]
  right_inv v := by
    refine Prod.ext ?_ ?_
    · show (v.1 ⬝ a + v.2 ⬝ c) ⬝ adj d - (v.1 ⬝ b + v.2 ⬝ d) ⬝ adj c = v.1
      rw [comb_add, r1, r2, sub_self, Matrix.mul_one, Matrix.mul_zero, add_zero]
    · show (v.1 ⬝ b + v.2 ⬝ d) ⬝ adj a - (v.1 ⬝ a + v.2 ⬝ c) ⬝ adj b = v.2
      rw [comb_add, r3, r4, sub_self, Matrix.mul_one, Matrix.mul_zero, zero_add]
  map_add' u v := by
    refine Prod.ext ?_ ?_
    · show (u.1 + v.1) ⬝ adj d - (u.2 + v.2) ⬝ adj c = (u.1 ⬝ adj d - u.2 ⬝ adj c) + (v.1 ⬝ adj d - v.2 ⬝ adj c)
      simp only [Matrix.add_mul]
      abel
    · show (u.2 + v.2) ⬝ adj a - (u.1 + v.1) ⬝ adj b = (u.2 ⬝ adj a - u.1 ⬝ adj b) + (v.2 ⬝ adj a - v.1 ⬝ adj b)
      simp only [Matrix.add_mul]
      abel
  continuous_toFun := by
    refine Continuous.prodMk ?_ ?_
    · exact cont_sub ((cont_rmul _).comp continuous_fst) ((cont_rmul _).comp continuous_snd)
    · exact cont_sub ((cont_rmul _).comp continuous_snd) ((cont_rmul _).comp continuous_fst)
  continuous_invFun := by
    refine Continuous.prodMk ?_ ?_
    · exact cont_add ((cont_rmul _).comp continuous_fst) ((cont_rmul _).comp continuous_snd)
    · exact cont_add ((cont_rmul _).comp continuous_fst) ((cont_rmul _).comp continuous_snd)


set_option maxHeartbeats 1000000 in
theorem emb_conj (M : Maps D hn) (g : G D p) {a b c d : Mx D p p} (hg : mat g = blk4 a b c d)
    (z' : hermA D ρ) (x y x' y' : Mx D ρ p)
    (h1 : y' ⬝ a + x' ⬝ c = y) (h2 : y' ⬝ b + x' ⬝ d = x)
    (h3 : adj x' = a ⬝ adj x - b ⬝ adj y) (h4 : adj y' = d ⬝ adj y - c ⬝ adj x)
    (h5 : z'.1 - x' ⬝ (d ⬝ adj y - c ⬝ adj x) = -(x ⬝ adj y)) :
    M.emb g * (M.nzx 0 x * M.sh y) = M.nzx z' x' * M.sh y' * M.emb g := by
  have hE := M.emb_mat g _ _ _ _ hg
  apply mat_injective
  rw [mat_mul' (M.emb g), mat_mul' _ (M.emb g), mat_nzx_sh, mat_nzx_sh, hE, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, block_mul₂, bl_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_neg, Matrix.neg_mul, neg_zero, h1, h2, h3, h4, h5, neg_sub, AddSubgroup.coe_zero, zero_sub,
    sub_eq_add_neg (a ⬝ adj x), sub_eq_add_neg (c ⬝ adj x)]

def zTv (a b c d : Mx D p p) (x y : Mx D ρ p) : Mx D ρ ρ :=
  x ⬝ ((adj c ⬝ b) ⬝ adj y) + y ⬝ ((adj b ⬝ c) ⬝ adj x) - x ⬝ ((adj a ⬝ c) ⬝ adj x) - y ⬝ ((adj b ⬝ d) ⬝ adj y)

theorem zTv_herm {a b c d : Mx D p p} (l2 : adj a ⬝ c = adj c ⬝ a) (l3 : adj b ⬝ d = adj d ⬝ b) (x y : Mx D ρ p) :
    adj (zTv a b c d x y) = zTv a b c d x y := by
  simp only [zTv, adj_sub', adj_add, adj_mul, adj_adj, ← l2, ← l3]
  simp only [Matrix.mul_assoc]
  abel

theorem zTv_eq {a b c d : Mx D p p} (l4 : adj a ⬝ d - adj c ⬝ b = 1) (x y : Mx D ρ p) :
    zTv a b c d x y - (x ⬝ adj a - y ⬝ adj b) ⬝ (d ⬝ adj y - c ⬝ adj x) = -(x ⬝ adj y) := by
  have e : ∀ w : Mx D p ρ, adj a ⬝ (d ⬝ w) = w + adj c ⬝ (b ⬝ w) := fun w => by
    rw [← Matrix.mul_assoc, sub_eq_iff_eq_add.1 l4, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc]
  simp only [zTv, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, e, Matrix.mul_add]
  abel

theorem rational_map_sub {k l : ℕ} (u v : Matrix (Fin k) (Fin l) D.host.E) : rat (D := D) (u - v) = rat u - rat v := by
  ext i j
  exact map_sub (incA D) _ _

theorem rational_map_add {k l : ℕ} (u v : Matrix (Fin k) (Fin l) D.host.E) : rat (D := D) (u + v) = rat u + rat v := by
  ext i j
  exact map_add (incA D) _ _

theorem transport {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (γ : G D p) (hγ : γ ∈ GF D p) :
    ∃ T : (Mx D ρ p × Mx D ρ p) ≃ₜ+ (Mx D ρ p × Mx D ρ p),
      (∀ ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E, ∃ ξ₁' ξ₂' : Matrix (Fin ρ) (Fin p) D.host.E,
        T (GlobalTheory.CompanionTheory.FJE.rt ξ₁, GlobalTheory.CompanionTheory.FJE.rt ξ₂) = (GlobalTheory.CompanionTheory.FJE.rt ξ₁', GlobalTheory.CompanionTheory.FJE.rt ξ₂')) ∧
      (∀ ξ₁ ξ₂ : Matrix (Fin ρ) (Fin p) D.host.E, ∃ ξ₁' ξ₂' : Matrix (Fin ρ) (Fin p) D.host.E,
        T.symm (GlobalTheory.CompanionTheory.FJE.rt ξ₁, GlobalTheory.CompanionTheory.FJE.rt ξ₂) = (GlobalTheory.CompanionTheory.FJE.rt ξ₁', GlobalTheory.CompanionTheory.FJE.rt ξ₂')) ∧
      ∀ y x : Mx D ρ p, ∃ z' : hermA D ρ,
        M.emb γ * (M.nzx 0 x * M.sh y) = M.nzx z' (T (y, x)).2 * M.sh (T (y, x)).1 * M.emb γ := by
  obtain ⟨a, b, c, d, hm⟩ := exists_rat_blocks γ hγ
  obtain ⟨l1, l2, l3, l4⟩ := rel_left γ hm
  obtain ⟨r1, r2, r3, r4⟩ := rel_right γ hm
  refine ⟨tEquiv (ρ := ρ) _ _ _ _ l1 l2 l3 l4 r1 r2 r3 r4, ?_, ?_, ?_⟩
  · intro ξ₁ ξ₂
    refine ⟨ξ₁ * dᴴ - ξ₂ * cᴴ, ξ₂ * aᴴ - ξ₁ * bᴴ, ?_⟩
    show (rat ξ₁ ⬝ adj (rat d) - rat ξ₂ ⬝ adj (rat c), rat ξ₂ ⬝ adj (rat a) - rat ξ₁ ⬝ adj (rat b)) =
      (rat (ξ₁ * dᴴ - ξ₂ * cᴴ), rat (ξ₂ * aᴴ - ξ₁ * bᴴ))
    simp only [rational_map_sub, rat_mul, rat_conjTranspose]
  · intro ξ₁ ξ₂
    refine ⟨ξ₁ * a + ξ₂ * c, ξ₁ * b + ξ₂ * d, ?_⟩
    show (rat ξ₁ ⬝ rat a + rat ξ₂ ⬝ rat c, rat ξ₁ ⬝ rat b + rat ξ₂ ⬝ rat d) =
      (rat (ξ₁ * a + ξ₂ * c), rat (ξ₁ * b + ξ₂ * d))
    simp only [rational_map_add, rat_mul]
  · intro y x
    refine ⟨⟨zTv (rat a) (rat b) (rat c) (rat d) x y, zTv_herm l2 l3 x y⟩, ?_⟩
    refine emb_conj M γ hm _ x y _ _ ?_ ?_ ?_ ?_ (zTv_eq l4 x y)
    · show (y ⬝ adj (rat d) - x ⬝ adj (rat c)) ⬝ rat a + (x ⬝ adj (rat a) - y ⬝ adj (rat b)) ⬝ rat c = y
      rw [comb_sub, l1, l2, sub_self, Matrix.mul_one, Matrix.mul_zero, add_zero]
    · show (y ⬝ adj (rat d) - x ⬝ adj (rat c)) ⬝ rat b + (x ⬝ adj (rat a) - y ⬝ adj (rat b)) ⬝ rat d = x
      rw [comb_sub, l4, l3, sub_self, Matrix.mul_one, Matrix.mul_zero, zero_add]
    · show adj (x ⬝ adj (rat a) - y ⬝ adj (rat b)) = _
      rw [adj_sub', adj_mul, adj_mul, adj_adj, adj_adj]
    · show adj (y ⬝ adj (rat d) - x ⬝ adj (rat c)) = _
      rw [adj_sub', adj_mul, adj_mul, adj_adj, adj_adj]

end GlobalTheory.CompanionTheory.FJE.Transport
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemL2OfBoundedContinuousInvariant
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC PositivityTheory.Affgl

noncomputable section

namespace GlobalTheory.CompanionTheory.CuspInvariant

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem memL2_of_bounded_continuous_invariant (μ : Measure (GA E a)) [μ.IsHaarMeasure] {φ : GA E a → ℂ} (hc : Continuous φ)
    (hl : LeftInv (latticeGL E a) φ) {C : ℝ} (hC : ∀ g, ‖φ g‖ ≤ C) : MemL2Quotient (latticeGL E a) μ φ := by
  have hfin := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  refine ⟨hl, MemLp.of_bound ?_ C (.of_forall fun q => hC _)⟩
  refine aestronglyMeasurable_quotMeasure_iff_lift.2 ?_
  rw [hl.lift_descend]
  exact hc.aestronglyMeasurable

theorem repOp_toL2cusp (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {f φ : GA E a → ℂ}
    (hf : Continuous f) (hs : HasCompactSupport f) (h : MemL2Quotient (latticeGL E a) μ φ) (hm : φ ∈ cuspCont E a)
    (hφ : ∀ x, convR μ f φ x = φ x) :
    repOp (Rcusp μ) μ f ⟨h.toL2, toL2_mem_cuspidal h hm⟩ = ⟨h.toL2, toL2_mem_cuspidal h hm⟩ := by
  have hi : Integrable f μ := hf.integrable_of_hasCompactSupport hs
  have hT : IsRepOp (R (latticeGL E a) μ) μ f (Rop (latticeGL E a) μ f) := isRepOp_Rop hi
  refine Subtype.ext (((isSubrep_L2cusp μ).coe_repOp_rep hT).2 _ |>.trans ?_)
  refine l2DiscreteQuotient_ext_iff_lift_ae_eq.2 ?_
  have e := h.lift_toL2_ae_eq
  refine (GlobalTheory.AutomorphicL2Pointwise.lift_Rop_eq_convR _ _ μ f hi h.toL2).2.trans
    (Filter.EventuallyEq.trans (.of_forall fun x => ?_) e.symm)
  rw [← hφ x]
  refine integral_congr_ae ?_
  filter_upwards [(measurePreserving_mul_left μ x).quasiMeasurePreserving.ae e] with y hy
  rw [hy]

theorem finiteDimensional_span (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {f : GA E a → ℂ}
    (hf : Continuous f) (hs : HasCompactSupport f) (S : Set (GA E a → ℂ))
    (hS : ∀ φ ∈ S, φ ∈ cuspCont E a ∧ (∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C) ∧ ∀ x, convR μ f φ x = φ x) :
    FiniteDimensional ℂ (Submodule.span ℂ S) := by
  have hA := GlobalTheory.CompanionTheory.CuspidalCompact.isCompactOperator_repOp_Rcusp E a μ f hf hs
  have hK := GlobalTheory.CompanionTheory.CompactFix.finiteDimensional_ker_sub_id _ hA
  set K := LinearMap.ker (((repOp (Rcusp μ) μ f : L2cusp μ →L[ℂ] L2cusp μ) : L2cusp μ →ₗ[ℂ] L2cusp μ) - LinearMap.id)
  let t := GlobalTheory.CompanionTheory.CuspTransfer.toL2cusp μ
  have ht : Function.Injective t := (injective_iff_map_eq_zero _).2 fun φ e => Subtype.ext (by
    by_contra h0
    exact toL2_ne_zero φ.2.2 φ.2.1.1 h0 (congrArg Subtype.val e))
  let Q := K.comap t
  have hQ : FiniteDimensional ℂ Q := FiniteDimensional.of_injective (t.restrict (q := K) fun x hx => hx)
    fun x y e => Subtype.ext (ht (congrArg Subtype.val e))
  have hle : Submodule.span ℂ S ≤ Q.map (GlobalTheory.CompanionTheory.CuspTransfer.cuspidalL2Functions μ).subtype := Submodule.span_le.2 fun φ hφ => by
    obtain ⟨h1, ⟨C, hC⟩, h3⟩ := hS φ hφ
    have hm := memL2_of_bounded_continuous_invariant μ h1.1 (leftInv_of_mem_cuspCont h1) hC
    refine ⟨⟨φ, h1, hm⟩, ?_, rfl⟩
    change _ ∈ K
    simp only [K, LinearMap.mem_ker, LinearMap.sub_apply, ContinuousLinearMap.coe_coe, LinearMap.id_apply]
    exact sub_eq_zero.2 (repOp_toL2cusp μ hf hs hm h1 h3)
  exact Submodule.finiteDimensional_of_le hle

theorem exists_compact_open {L : Subgroup (GL (Fin a) (Af E))} (hL : IsOpen (L : Set (GL (Fin a) (Af E)))) :
    ∃ U : Subgroup (GL (Fin a) (Af E)), U ≤ L ∧ IsOpen (U : Set (GL (Fin a) (Af E))) ∧
      IsCompact (U : Set (GL (Fin a) (Af E))) := by
  obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : GA E a)
  have hc := ContAut.continuous_map_pFin E a
  have hW : (GeneralLinearGroup.map (pFin E) '' C : Set (GL (Fin a) (Af E))) ∈ 𝓝 (1 : GL (Fin a) (Af E)) := by
    set_option synthInstance.maxHeartbeats 200000 in
      have h1 : finGL E a ⁻¹' C ∈ 𝓝 (1 : GL (Fin a) (Af E)) :=
        (GlobalTheory.CompanionTheory.DenseKFin.continuous_finGL (E := E) (a := a)).continuousAt.preimage_mem_nhds (by simpa using hC1)
    exact Filter.mem_of_superset h1 fun k hk => ⟨_, hk, pFin_finGL k⟩
  obtain ⟨U, hU, hUW⟩ := GlobalTheory.CompanionTheory.DenseKFin.exists_openSubgroup_GLAf (Filter.inter_mem hW (hL.mem_nhds (one_mem L)))
  exact ⟨U, fun k hk => (hUW hk).2, hU, (hC.image hc).of_isClosed_subset (Subgroup.isClosed_of_isOpen U hU)
    fun k hk => (hUW hk).1⟩

abbrev pI (g : GA E a) : GL (Fin a) (Cinf E) := GeneralLinearGroup.map (pInf E) g

def levelSet (U : Subgroup (GL (Fin a) (Af E))) : Set (GA E a) := {g | GeneralLinearGroup.map (pFin E) g ∈ U}

theorem isClopen_levelSet {U : Subgroup (GL (Fin a) (Af E))} (hU : IsOpen (U : Set (GL (Fin a) (Af E)))) :
    IsClopen (levelSet U : Set (GA E a)) :=
  ⟨(Subgroup.isClosed_of_isOpen U hU).preimage (ContAut.continuous_map_pFin E a),
    hU.preimage (ContAut.continuous_map_pFin E a)⟩

theorem isCompact_levelSet_inter {U : Subgroup (GL (Fin a) (Af E))} (hU : IsCompact (U : Set (GL (Fin a) (Af E))))
    {K : Set (GL (Fin a) (Cinf E))} (hK : IsCompact K) : IsCompact ((levelSet U : Set (GA E a)) ∩ pI ⁻¹' K) := by
  have e : (levelSet U : Set (GA E a)) ∩ pI ⁻¹' K =
      (GASplit.splitEquiv E a).toHomeomorph ⁻¹' (K ×ˢ (U : Set (GL (Fin a) (Af E)))) := by
    ext g
    exact and_comm
  rw [e]
  exact (Homeomorph.isCompact_preimage _).2 (hK.prod hU)

section Measure

variable [MeasurableSpace (GL (Fin a) (Cinf E))] [BorelSpace (GL (Fin a) (Cinf E))]

def levelMeasure (μ : Measure (GA E a)) (U : Subgroup (GL (Fin a) (Af E))) : Measure (GL (Fin a) (Cinf E)) :=
  (μ.restrict (levelSet U)).map pI

theorem measurable_pI : Measurable (pI : GA E a → GL (Fin a) (Cinf E)) :=
  (ContAut.continuous_map_pInf E a).measurable

theorem isHaarMeasure_levelMeasure (μ : Measure (GA E a)) [μ.IsHaarMeasure] {U : Subgroup (GL (Fin a) (Af E))}
    (hU : IsOpen (U : Set (GL (Fin a) (Af E)))) (hUc : IsCompact (U : Set (GL (Fin a) (Af E)))) :
    (levelMeasure μ U).IsHaarMeasure := by
  haveI : T2Space (GL (Fin a) (Cinf E)) := Units.isEmbedding_embedProduct.t2Space
  have hH := (isClopen_levelSet hU).isOpen.measurableSet
  have hp := measurable_pI (E := E) (a := a)
  have hmeas : ∀ {K : Set (GL (Fin a) (Cinf E))}, MeasurableSet K →
      levelMeasure μ U K = μ (pI ⁻¹' K ∩ levelSet U) := fun hK => by
    rw [levelMeasure, Measure.map_apply hp hK, Measure.restrict_apply (hp hK)]
  refine { lt_top_of_isCompact := ?_, map_mul_left_eq_self := ?_, open_pos := ?_ }
  · intro K hK
    rw [hmeas hK.measurableSet, Set.inter_comm]
    exact (isCompact_levelSet_inter hUc hK).measure_lt_top
  · intro y
    have hpre : (fun g : GA E a => infGL E a y * g) ⁻¹' levelSet U = levelSet U := by
      ext g
      simp [levelSet]
    have hmp := (measurePreserving_mul_left μ (infGL E a y)).restrict_preimage hH
    rw [hpre] at hmp
    rw [levelMeasure, Measure.map_map (measurable_const_mul y) hp]
    have e : ((fun x => y * x) ∘ pI : GA E a → _) = pI ∘ fun g => infGL E a y * g := by
      funext g
      simp
    rw [e, ← Measure.map_map hp (measurable_const_mul _), hmp.map_eq]
  · intro V hV hne
    obtain ⟨y, hy⟩ := hne
    rw [hmeas hV.measurableSet]
    refine ((hV.preimage (ContAut.continuous_map_pInf E a)).inter (isClopen_levelSet hU).isOpen).measure_ne_zero μ
      ⟨infGL E a y, by simpa using hy, ?_⟩
    simp [levelSet, one_mem]

theorem integral_levelMeasure (μ : Measure (GA E a)) {U : Subgroup (GL (Fin a) (Af E))}
    (hU : IsOpen (U : Set (GL (Fin a) (Af E)))) {α : GL (Fin a) (Cinf E) → ℂ} (hα : Continuous α) {φ : GA E a → ℂ}
    (hφ : Continuous φ) (hfix : ∀ k ∈ U, ∀ x, φ (x * finGL E a k) = φ x) (g : GA E a) :
    ∫ y, φ (g * infGL E a y) * α y ∂levelMeasure μ U = convR μ ((levelSet U).indicator (α ∘ pI)) φ g := by
  have hH := (isClopen_levelSet (E := E) hU).isOpen.measurableSet
  have hc : Continuous fun y => φ (g * infGL E a y) * α y :=
    (hφ.comp (continuous_const.mul GlobalTheory.CompanionTheory.DenseKFin.continuous_infGL)).mul hα
  rw [levelMeasure, integral_map measurable_pI.aemeasurable hc.aestronglyMeasurable]
  have e : (fun y => (levelSet U).indicator (α ∘ pI) y * φ (g * y)) =
      (levelSet U).indicator fun y => α (pI y) * φ (g * y) := by
    funext y
    by_cases h : y ∈ levelSet U <;> simp [h]
  rw [convR, e, integral_indicator hH]
  refine setIntegral_congr_fun hH fun y hy => ?_
  have h := hfix _ hy (g * infGL E a (pI y))
  rw [mul_assoc, infGL_mul_finGL] at h
  simp only [h, mul_comm]

end Measure

theorem continuous_test {U : Subgroup (GL (Fin a) (Af E))} (hU : IsOpen (U : Set (GL (Fin a) (Af E))))
    {α : GL (Fin a) (Cinf E) → ℂ} (hα : Continuous α) :
    Continuous ((levelSet U : Set (GA E a)).indicator (α ∘ pI)) :=
  (hα.comp (ContAut.continuous_map_pInf E a)).indicator fun x hx => by
    rw [(isClopen_levelSet hU).frontier_eq] at hx
    exact absurd hx (Set.notMem_empty x)

theorem hasCompactSupport_test {U : Subgroup (GL (Fin a) (Af E))} (hU : IsCompact (U : Set (GL (Fin a) (Af E))))
    {α : GL (Fin a) (Cinf E) → ℂ} (hα : HasCompactSupport α) :
    HasCompactSupport ((levelSet U : Set (GA E a)).indicator (α ∘ pI)) := by
  set_option synthInstance.maxHeartbeats 200000 in
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_levelSet_inter hU hα) fun g hg => ?_
  rw [Function.mem_support] at hg
  have h1 : g ∈ levelSet U := by
    by_contra h
    exact hg (Set.indicator_of_notMem h _)
  refine ⟨h1, subset_tsupport _ ?_⟩
  rw [Function.mem_support]
  rwa [Set.indicator_of_mem h1] at hg

theorem cuspInvFin (hb : GlobalTheory.Published.CuspFormsBoundedGL)
    (hu : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), UnifAlpha E a) :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), CuspInvFin E a := by
  intro E _ _ _ a L hL W _ _ _ ρ hρ J hJ
  obtain ⟨U, hUL, hUo, hUc⟩ := exists_compact_open hL
  letI : MeasurableSpace (GL (Fin a) (Cinf E)) := borel _
  haveI : BorelSpace (GL (Fin a) (Cinf E)) := ⟨rfl⟩
  let μ : Measure (GA E a) := Measure.haar
  haveI := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  obtain ⟨α, hαc, hαs, hα⟩ := hu E a W ρ hρ J hJ (levelMeasure μ U) (isHaarMeasure_levelMeasure μ hUo hUc)
  set S : Set (Sm E a) := {φ | φ ∈ genSpace L ρ J ∧ IsCuspidal φ.1 ∧
    ∀ t g, φ.1 (GlobalTheory.UnitaryBC.splitCentre E a t * g) = φ.1 g} with hSdef
  have key := finiteDimensional_span μ (continuous_test hUo hαc) (hasCompactSupport_test hUc hαs)
    ((Sm E a).subtype '' S) (by
      rintro _ ⟨φ, ⟨hφ, hcusp, hz⟩, rfl⟩
      have hcf : IsCuspForm φ := ⟨hφ.1, hcusp⟩
      have hm := mem_cuspCont_of_isCuspForm hcf hz
      refine ⟨hm, hb.of_invariant hcf hz, fun x => ?_⟩
      refine (integral_levelMeasure μ hUo hαc hm.1 (fun k hk y => ?_) x).symm.trans (hα L φ hφ x).symm
      exact congrFun (congrArg Subtype.val (hφ.2.1 k (hUL hk))) y)
  rw [← Submodule.map_span] at key
  exact (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) _).symm.finiteDimensional

end GlobalTheory.CompanionTheory.CuspInvariant

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankDirectSumHermitianLt
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn GlobalTheory.StdUnn.Model PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw GlobalTheory.CompanionTheory.PcFc

namespace GlobalTheory.CompanionTheory.PcFc

theorem rank_fromBlocks_ge {K : Type*} [Field K] {ρ p : ℕ} (a : Matrix (Fin ρ) (Fin ρ) K)
    (ha : a.det ≠ 0) (c : Matrix (Fin p) (Fin p) K) (hc : c ≠ 0) :
    ρ + 1 ≤ (Matrix.fromBlocks a 0 0 c).rank := by
  classical
  obtain ⟨i, j, hij⟩ : ∃ i j, c i j ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (Matrix.ext h)
  have hsub : (Matrix.fromBlocks a 0 0 c).submatrix
      (Sum.map id fun _ : Unit => i) (Sum.map id fun _ : Unit => j) =
      Matrix.fromBlocks a 0 0 (Matrix.of fun _ _ : Unit => c i j) := by
    ext x y
    rcases x with x | x <;> rcases y with y | y <;> rfl
  have hdet : (Matrix.fromBlocks a 0 0
      (Matrix.of fun _ _ : Unit => c i j)).det ≠ 0 := by
    rw [Matrix.det_fromBlocks_zero₂₁]
    simpa using ⟨ha, hij⟩
  have hrank := Matrix.rank_of_isUnit _
    ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))
  have hle := Matrix.rank_submatrix_le (Matrix.fromBlocks a 0 0 c)
    (Sum.map id fun _ : Unit => i) (Sum.map id fun _ : Unit => j)
  rw [hsub, hrank] at hle
  simpa using hle

theorem rank_dsum_ge : ∀ {D : D7} {n ρ p : ℕ} (hn : ρ + p = n) (b₀ : HermE D ρ), b₀.1.det ≠ 0 → ∀ β' : HermE D p, β'.1 ≠ 0 → ρ + 1 ≤ (dsum hn b₀ β').1.rank := by
  intro D n ρ p hn b₀ hb β' hβ
  have h := rank_fromBlocks_ge b₀.1 hb β'.1 hβ
  have e : (dsum hn b₀ β').1.rank = (Matrix.fromBlocks b₀.1 0 0 β'.1).rank :=
    Matrix.rank_submatrix _ (finSumFinEquiv.trans (finCongr hn)).symm
      (finSumFinEquiv.trans (finCongr hn)).symm
  rw [e]
  exact h

end GlobalTheory.CompanionTheory.PcFc
end

