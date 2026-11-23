module

public import Mathlib
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0633
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SummableCell
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0495
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0464
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0625
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0428
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0416
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0451
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0404
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0711
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0410
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0426
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0408
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0708
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0701
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0697
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.WhitNDgOfLocalOfSteps
public import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0464
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0229
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0416
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0160
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0166
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0710

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCellInvariantUnipotent
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf

namespace GlobalTheory.CompanionTheory.SwUnf

open PositivityTheory.GramSchwartzFunctions.EC

section Blocks

variable {K : Type} [Field K] {n : ℕ}

theorem lowerC_apply' (M : Matrix (Fin (n + n)) (Fin (n + n)) K) (i j : Fin n) :
    lowerC M i j = M (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) := rfl

theorem lowerC_siegel_mul {y : Matrix (Fin (n + n)) (Fin (n + n)) K} (hy : IsSiegelP y)
    (W : Matrix (Fin (n + n)) (Fin (n + n)) K) :
    lowerC (y * W) = GlobalTheory.CompanionTheory.RatPtsUnn.blkD y * lowerC W := by
  have hy' : ∀ i j : Fin n, y (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0 := hy
  ext i j
  simp only [lowerC_apply', Matrix.mul_apply]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [hy', zero_mul, Finset.sum_const_zero, zero_add, GlobalTheory.CompanionTheory.RatPtsUnn.blkD]

theorem lowerC_mul_unip (X : Matrix (Fin (n + n)) (Fin (n + n)) K) (b : Matrix (Fin n) (Fin n) K) :
    lowerC (X * blk4 1 b 0 1) = lowerC X := by
  ext i j
  simp only [lowerC_apply', Matrix.mul_apply]
  rw [← finSumFinEquiv.sum_comp, Fintype.sum_sum_type]
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₂₁, Matrix.one_apply, Matrix.zero_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const_zero, add_zero]

end Blocks

variable {D : D7} {n : ℕ}

private theorem incA_injective' (D : D7) : Function.Injective (incA D) := by
  haveI : Nontrivial (AF D.host.F) :=
    inferInstanceAs (Nontrivial (NumberField.InfiniteAdeleRing D.host.F ×
      IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers D.host.F) D.host.F))
  haveI : Nontrivial (AF D.host.F ⊗[D.host.F] D.host.E) :=
    Function.Injective.nontrivial
      (Algebra.TensorProduct.includeRight_injective (algebraMap D.host.F (AF D.host.F)).injective)
  exact (incA D).injective

theorem isUnit_det_of_mat (x : GF D n) {g : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E}
    (h : mat (x : G D n) = g.map (incA D)) : IsUnit g.det := by
  obtain ⟨g', hg', -, hg'm⟩ := GlobalTheory.CompanionTheory.RatPtsUnn.clause1 (x : G D n) x.2
  have hgg : g = g' := Matrix.map_injective (incA_injective' D) (h.symm.trans hg'm)
  rw [hgg]
  exact hg'

private theorem mat_mul_eq_ite_of_hasMult {D : D7} {n : ℕ} (a b : G D n) : mat (a * b) = mat a * mat b := by
  simp only [mat, map_mul, Units.val_mul]

theorem cosetCell_rmulEquiv : ∀ {D : D7} {n : ℕ} (q : Cosets (P D n) (GF D n)) (γ : GF D n) (b : Matrix (Fin n) (Fin n) D.host.E), mat (γ : G D n) = blk4 1 (b.map (incA D)) 0 1 → cosetCell (rmulEquiv (P D n) (GF D n) γ q) = cosetCell q := by
  intro D n q γ b h
  set q' := rmulEquiv (P D n) (GF D n) γ q with hq'
  have e3 : GlobalTheory.AutomorphicL2Unitary.mk _ q'.out = GlobalTheory.AutomorphicL2Unitary.mk _ (q.out * γ) :=
    calc GlobalTheory.AutomorphicL2Unitary.mk _ q'.out = q' := Quotient.out_eq q'
      _ = GlobalTheory.AutomorphicL2Unitary.rmul _ γ q := rfl
      _ = GlobalTheory.AutomorphicL2Unitary.rmul _ γ (GlobalTheory.AutomorphicL2Unitary.mk _ q.out) :=
        congrArg (GlobalTheory.AutomorphicL2Unitary.rmul _ γ) (Quotient.out_eq q).symm
      _ = GlobalTheory.AutomorphicL2Unitary.mk _ (q.out * γ) := GlobalTheory.AutomorphicL2Unitary.rmul_mk _ _
  obtain ⟨p, hp⟩ := GlobalTheory.AutomorphicL2Unitary.mk_eq_iff.mp e3
  have hp' : ((p : GF D n) : G D n) * (q'.out : G D n) = (q.out : G D n) * (γ : G D n) :=
    congrArg Subtype.val hp
  have hb : blk4 1 (b.map (incA D)) 0 1 = (blk4 1 b 0 1).map (incA D) := by
    have h1 : (1 : Matrix (Fin n) (Fin n) D.host.E).map (incA D) = 1 := (incA D).mapMatrix.map_one
    have h0 : (0 : Matrix (Fin n) (Fin n) D.host.E).map (incA D) = 0 := (incA D).mapMatrix.map_zero
    unfold blk4
    rw [← Matrix.submatrix_map, Matrix.fromBlocks_map, h1, h0]
  have hm := congrArg mat hp'
  rw [mat_mul_eq_ite_of_hasMult, mat_mul_eq_ite_of_hasMult, h, mat_ratOf, mat_ratOf, mat_ratOf, hb, ← Matrix.map_mul,
    ← Matrix.map_mul] at hm
  have hm2 : ratOf (p : GF D n) * ratOf q'.out = ratOf q.out * blk4 1 b 0 1 :=
    Matrix.map_injective (incA_injective' D) hm
  have hpP : ((p : GF D n) : G D n) ∈ P D n := Subgroup.mem_subgroupOf.mp p.2
  have hS : IsSiegelP (ratOf (p : GF D n)) :=
    (GlobalTheory.CompanionTheory.RatPtsUnn.clause3 _ (p : GF D n).2 _ (mat_ratOf (p : GF D n))).mp hpP
  have hC : lowerC (ratOf q.out) = GlobalTheory.CompanionTheory.RatPtsUnn.blkD (ratOf (p : GF D n)) * lowerC (ratOf q'.out) := by
    rw [← lowerC_mul_unip (ratOf q.out) b, ← hm2, lowerC_siegel_mul hS]
  have hU : IsUnit (GlobalTheory.CompanionTheory.RatPtsUnn.blkD (ratOf (p : GF D n))).det := by
    have hd := isUnit_det_of_mat (p : GF D n) (mat_ratOf (p : GF D n))
    rw [GlobalTheory.CompanionTheory.RatPtsUnn.det_eq_of_lowerLeft_zero _ hS] at hd
    exact isUnit_of_mul_isUnit_right hd
  have hinj : ∀ w, GlobalTheory.CompanionTheory.RatPtsUnn.blkD (ratOf (p : GF D n)) *ᵥ w = 0 → w = 0 := by
    intro w hw
    rw [← Matrix.one_mulVec w, ← Matrix.nonsing_inv_mul _ hU, ← Matrix.mulVec_mulVec, hw,
      Matrix.mulVec_zero]
  simp only [cosetCell, cellKer]
  ext v
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  rw [hC, ← Matrix.mulVec_mulVec]
  constructor
  · intro h0
    rw [h0, Matrix.mulVec_zero]
  · intro h0
    exact hinj _ h0

end GlobalTheory.CompanionTheory.SwUnf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreFunctionLocallyConstantCompact
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibCompact

theorem exists_right_invariant {G Z : Type} [Group G] [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) (ρ : Representation ℂ H Z) (f : cIndSpace H ρ) :
    ∃ S : Set G, IsOpen S ∧ (1 : G) ∈ S ∧ ∀ s ∈ S, ∀ p : G, f.1.1.1 (p * s) = f.1.1.1 p := by
  have hopen : IsOpen {s : G | GlobalTheory.PRep.ind H ρ s f.1.1 = f.1.1} := f.1.2
  refine ⟨_, hopen, ?_, fun s hs p => ?_⟩
  · show GlobalTheory.PRep.ind H ρ 1 f.1.1 = f.1.1
    simp
  · have hs' : GlobalTheory.PRep.ind H ρ s f.1.1 = f.1.1 := hs
    exact congrFun (congrArg Subtype.val hs') p

theorem exists_compact_support {G Z : Type} [Group G] [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : Subgroup G) (ρ : Representation ℂ H Z) (f : cIndSpace H ρ) :
    ∃ C : Set G, IsCompact C ∧ ∀ p : G, f.1.1.1 p ≠ 0 → ∃ h ∈ H, ∃ c ∈ C, p = h * c :=
  f.2

section Column

variable (k : Type) [Field k]

def col (n : ℕ) (p : Mir k n) : Fin n → k :=
  fun j => ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc j) (Fin.last n)

theorem last_last (n : ℕ) (p : Mir k n) :
    ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.last n) = 1 := by
  have h := congrFun ((GlobalTheory.BZMir.mem_Mir_iff k (p : GL (Fin (n + 1)) k)).1 p.2) (Fin.last n)
  simpa [GlobalTheory.BZMir.eLast] using h

theorem last_column_entry_product_formula (n : ℕ) (a : Fin n → k) (A : Matrix (Fin n) (Fin n) k)
    (P : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (hP : P (Fin.last n) (Fin.last n) = 1) (j : Fin n) :
    ((1 + colMat k n a) * glEmbMat k n A * P) (Fin.castSucc j) (Fin.last n) =
      a j + (A.mulVec (fun l => P (Fin.castSucc l) (Fin.last n))) j := by
  rw [add_mul, one_mul, GlobalTheory.BZMir.colMat_mul_glEmbMat, add_mul, Matrix.add_apply]
  simp [Matrix.mul_apply, Fin.sum_univ_castSucc, GlobalTheory.BZMir.glEmbMat, GlobalTheory.BZMir.colMat, Matrix.mulVec,
    dotProduct, hP, Fin.castSucc_ne_last]
  all_goals ring

theorem col_uM_levi_mul (n : ℕ) (a : Fin n → k) (g : GL (Fin n) k) (p : Mir k n) :
    col k n (uM k n a * levi k n g * p) = a + (g : Matrix (Fin n) (Fin n) k).mulVec (col k n p) := by
  funext j
  exact GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.last_column_entry_product_formula k n a (g : Matrix (Fin n) (Fin n) k)
    ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.last_last k n p) j

theorem col_one (n : ℕ) : col k n 1 = 0 := by
  funext j
  simp [GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col, Matrix.one_apply, Fin.castSucc_ne_last]

theorem col_uM_levi (n : ℕ) (a : Fin n → k) (g : GL (Fin n) k) :
    col k n (uM k n a * levi k n g) = a := by
  have h := GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col_uM_levi_mul k n a g 1
  rwa [mul_one, GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col_one, Matrix.mulVec_zero, add_zero] at h

end Column

section Top

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_midV (i t : ℕ) : Continuous (midV k i t) := by
  refine continuous_pi fun j => ?_
  induction j using Fin.addCases with
  | left l =>
    show Continuous fun v : Fin t → k => Fin.append (0 : Fin i → k) v (Fin.castAdd t l)
    simp only [Fin.append_left, Pi.zero_apply]
    exact continuous_const
  | right l =>
    show Continuous fun v : Fin t → k => Fin.append (0 : Fin i → k) v (Fin.natAdd i l)
    simp only [Fin.append_right]
    exact continuous_apply l

theorem continuous_col_inv (n : ℕ) : Continuous (fun c : Mir k n => col k n c⁻¹) :=
  continuous_pi fun j =>
    (Units.continuous_coe_inv.comp continuous_subtype_val).matrix_elem (Fin.castSucc j) (Fin.last n)

theorem isLocallyConstant_uM {Z : Type} (n : ℕ) (F : Mir k n → Z) (S : Set (Mir k n)) (hS : IsOpen S)
    (h1 : (1 : Mir k n) ∈ S) (hF : ∀ s ∈ S, ∀ p, F (p * s) = F p) (g : GL (Fin n) k) :
    IsLocallyConstant (fun y : Fin n → k => F (uM k n y * levi k n g)) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro y₀
  have hu := GlobalTheory.CompanionTheory.BZPsiPG.Cont.continuous_uM k n
  set L := GlobalTheory.BZMir.levi k n g
  let φ : (Fin n → k) → GlobalTheory.BZMir.Mir k n := fun y => L⁻¹ * GlobalTheory.CompanionTheory.BZPsiPG.uM k n (y - y₀) * L
  have hφ : Continuous φ :=
    (continuous_const.mul (hu.comp (continuous_id.sub continuous_const))).mul continuous_const
  refine ⟨φ ⁻¹' S, hS.preimage hφ, ?_, fun y hy => ?_⟩
  · show L⁻¹ * GlobalTheory.CompanionTheory.BZPsiPG.uM k n (y₀ - y₀) * L ∈ S
    rw [sub_self, GlobalTheory.CompanionTheory.BZPsiPG.uM_zero, mul_one, inv_mul_cancel]
    exact h1
  · have hadd : GlobalTheory.CompanionTheory.BZPsiPG.uM k n y =
        GlobalTheory.CompanionTheory.BZPsiPG.uM k n y₀ * GlobalTheory.CompanionTheory.BZPsiPG.uM k n (y - y₀) := by
      rw [← GlobalTheory.CompanionTheory.BZPsiPG.uM_add]
      congr 1
      abel
    have hy' : GlobalTheory.CompanionTheory.BZPsiPG.uM k n y * L = GlobalTheory.CompanionTheory.BZPsiPG.uM k n y₀ * L * φ y := by
      rw [hadd]
      simp only [φ]
      group
    show F (GlobalTheory.CompanionTheory.BZPsiPG.uM k n y * L) = F (GlobalTheory.CompanionTheory.BZPsiPG.uM k n y₀ * L)
    rw [hy']
    exact hF _ hy _

end Top

theorem fibV_main : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ (f : cIndSpace (HPG k i t) (hRep τ σ)) (g : GL (Fin (i + t)) k), IsLocallyConstant (fibV f g) ∧ HasCompactSupport (fibV f g) := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ _ _ f g
  constructor
  · obtain ⟨S, hS, h1, hSf⟩ := GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.exists_right_invariant _ _ f
    exact (GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.isLocallyConstant_uM k (i + t) _ S hS h1 hSf g).comp_continuous
      (GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.continuous_midV k i t)
  · obtain ⟨C, hC, hCf⟩ := GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.exists_compact_support _ _ f
    let proj : GlobalTheory.BZMir.Mir k (i + t) → Fin t → k := fun c j =>
      -(((g : Matrix (Fin (i + t)) (Fin (i + t)) k) *ᵥ GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col k (i + t) c⁻¹) (Fin.natAdd i j))
    have hproj : Continuous proj := continuous_pi fun j =>
      ((continuous_apply (Fin.natAdd i j)).comp
        (continuous_const.matrix_mulVec (GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.continuous_col_inv k (i + t)))).neg
    refine HasCompactSupport.of_support_subset_isCompact (hC.image hproj) ?_
    intro v hv
    obtain ⟨h, hh, c, hc, hp⟩ := hCf (GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.midV k i t v) *
      GlobalTheory.BZMir.levi k (i + t) g) hv
    refine ⟨c, hc, ?_⟩
    obtain ⟨x, q, hxq⟩ := _root_.GlobalTheory.CompanionTheory.BZPsiPG.HpgMem.main k i t ⟨h, hh⟩
    have hxq' : h = GlobalTheory.CompanionTheory.BZPsiPG.uM k (i + t) (GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x) *
        GlobalTheory.BZMir.levi k (i + t) q := hxq
    have key : GlobalTheory.CompanionTheory.BZPsiPG.topV k i t x = GlobalTheory.CompanionTheory.BZPsiPG.midV k i t v +
        (g : Matrix (Fin (i + t)) (Fin (i + t)) k) *ᵥ GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col k (i + t) c⁻¹ := by
      rw [← GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col_uM_levi_mul, hp, mul_inv_cancel_right, hxq',
        GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col_uM_levi]
    funext j
    have hj := congrFun key (Fin.natAdd i j)
    simp only [GlobalTheory.CompanionTheory.BZPsiPG.topV, GlobalTheory.CompanionTheory.BZPsiPG.midV, Fin.append_right, Pi.add_apply, Pi.zero_apply] at hj
    show -(((g : Matrix (Fin (i + t)) (Fin (i + t)) k) *ᵥ GlobalTheory.CompanionTheory.BZPsiPG.FibCompact.col k (i + t) c⁻¹) (Fin.natAdd i j)) = v j
    rw [neg_eq_iff_add_eq_zero, add_comm]
    exact hj.symm

end GlobalTheory.CompanionTheory.BZPsiPG.FibCompact

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalTypedExtension
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV

theorem typed_tw_finite {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}
    (U : Submodule ℂ (Sm E N)) (z : ℂ)
    (H : ∀ (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)),
      IsOpen (K : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed U K W))
    (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ))
    (hK : IsOpen (K : Set (GL (Fin N) (Af E)))) (hW : FiniteDimensional ℂ W) :
    FiniteDimensional ℂ (typed (tw U z) K W) := by
  have hK₀ : IsOpen ((K ⊓ KO E N : Subgroup (GL (Fin N) (Af E))) : Set (GL (Fin N) (Af E))) := by
    rw [Subgroup.coe_inf]
    exact hK.inter (GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E N)
  have hfin := H (K ⊓ KO E N) W hK₀ hW
  have hflat : FlatFn (absFn (E := E) N (-z)) := GlobalTheory.T.flat_absolute_character N (-z)
  have hval : ∀ (φ : Sm E N) x, (mulChi N (GlobalTheory.CuspRep.Model.absC E (-z)) φ).1 x =
      absFn N (-z) x * φ.1 x := fun φ x => by
    simp only [mulChi_apply, absFn]
    exact mul_comm _ _
  have hfinv : ∀ (g : GA E N), ∀ u ∈ KO E N, absFn (E := E) N (-z) (g * finGL E N u) = absFn N (-z) g := by
    intro g u hu
    have := hflat.rinv g 1 u hu
    simpa [cf] using this
  have hkinv : ∀ (g : GA E N) (k : Kinf E N),
      absFn (E := E) N (-z) (g * infGL E N (Unitary.toUnits k)) = absFn N (-z) g := by
    intro g k
    have := hflat.rinv g k 1 (one_mem _)
    simpa [cf] using this
  let L : Sm E N ≃ₗ[ℂ] Sm E N := mulChi N (GlobalTheory.CuspRep.Model.absC E (-z))
  have hle : (typed (tw U z) K W).map (L : Sm E N →ₗ[ℂ] Sm E N) ≤ typed U (K ⊓ KO E N) W := by
    rintro _ ⟨φ, ⟨⟨ψ, hψ, rfl⟩, hlev, htype⟩, rfl⟩
    set φ : Sm E N := mulChi N (GlobalTheory.CuspRep.Model.absC E z) ψ with hφ
    have hL : ∀ x, (L φ).1 x = absFn N (-z) x * φ.1 x := hval φ
    refine ⟨?_, ?_, ?_⟩
    · have hback : L φ = ψ := by
        refine Subtype.ext (funext fun x => ?_)
        have e : ∀ s : ℂ, ((chiDet N (GlobalTheory.CuspRep.Model.absC E s) x : ℂˣ) : ℂ) =
            Complex.exp (s * GlobalTheory.Mem.Chr.CharModel.logNorm E (GeneralLinearGroup.det x)) := fun _ => rfl
        rw [hL, hφ, mulChi_apply, absFn, e, e, mul_left_comm, ← Complex.exp_add]
        simp
      show L φ ∈ U
      rw [hback]
      exact hψ
    · intro u hu g
      have h2 : φ.1 (g * finGL E N u) = φ.1 g := hlev u hu.1 g
      show (L φ).1 (g * finGL E N u) = (L φ).1 g
      rw [hL, hL, hfinv g u hu.2, h2]
    · intro g
      have h3 : (fun k : Kinf E N => φ.1 (g * infGL E N (Unitary.toUnits k))) ∈ W := htype g
      have h4 : (fun k : Kinf E N => (L φ).1 (g * infGL E N (Unitary.toUnits k))) =
          absFn N (-z) g • (fun k : Kinf E N => φ.1 (g * infGL E N (Unitary.toUnits k))) := by
        funext k
        rw [hL, hkinv g k]
        rfl
      show (fun k : Kinf E N => (L φ).1 (g * infGL E N (Unitary.toUnits k))) ∈ W
      rw [h4]
      exact W.smul_mem _ h3
  have h1 : FiniteDimensional ℂ ((typed (tw U z) K W).map (L : Sm E N →ₗ[ℂ] Sm E N)) :=
    Submodule.finiteDimensional_of_le hle
  exact LinearEquiv.finiteDimensional (L.submoduleMap (typed (tw U z) K W)).symm

end GlobalTheory.CompanionTheory.LimV
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockKStable
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PfSWUS

theorem fockKStable : PositivityTheory.PfSWUS.FockKStable := by
  intro D n V ψ χ θ μ ω H l s ν Φ hStd k hk
  obtain ⟨𝓕, hμ⟩ := hStd.hμ
  have hψ := hStd.hψ
  have hχ := hStd.hχ
  have hr := hStd.hη
  have hθ := hStd.hθ
  have hω := hStd.hω
  have hl := hStd.hl
  have hs := hStd.hs
  have hΦ := hStd.hΦ
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, hlam, hψeq, hchart, hdat, htr⟩ :=
    _root_.GlobalTheory.StdUnn.SchDatum.exists_datum D A V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω
  obtain ⟨lam', hlam', -, l', hl', habs⟩ := GlobalTheory.StdUnn.shift_char_realPar D ψ₀ hstd θ hθ μ' hsk
  have hll : lam' = lam := (algebraMap D.host.F D.host.E).injective (hlam'.trans hlam.symm)
  subst hll
  have hl'' : HasRealPar ψ θ l' := hψeq ▸ hl'
  have hleq : l = l' := _root_.GlobalTheory.StdUnn.RealPar.realPar_unique D ψ θ hθ l l' hl hl''
  subst hleq
  obtain ⟨-, hsurj, -⟩ := _root_.GlobalTheory.SchSchwartzAll.schSchwartz D ψ₀ hstd θ hθ A V μ 𝓕 hμ
  obtain ⟨f, hf, hfΦ⟩ := hsurj Φ.1 Φ.2
  obtain ⟨s', hstd', hcomm⟩ := _root_.GlobalTheory.StdUnn.KComm.exists_stdInv_comm_K D A μ' hsk κ hchart θ hθ
  have hfock : IsFockVec ψ₀ θ (dblSp A) V s' s f :=
    _root_.GlobalTheory.StdUnnFockRev.isFockVec_of_sch_mem_fockA D ψ₀ hstd θ hθ A V μ 𝓕 hμ μ' hsk s' s hstd' hs l habs f hf (hfΦ ▸ hΦ)
  obtain ⟨hth, N, hN⟩ := hfock
  have hk' : κ (κ.symm k) ∈ K D A.rank := by
    rw [show κ (κ.symm k) = k from κ.apply_symm_apply k]
    exact hk
  have hfock' : IsFockVec ψ₀ θ (dblSp A) V s' s (omh (κ.symm k, 1) f) :=
    ⟨hdat.om_pres _ f hth, N,
      _root_.GlobalTheory.CartanFockDeg.om_keeps_fockDeg D ψ₀ θ (dblSp A) V 1 χ⁻¹ omh s' s hdat hθ (κ.symm k) (hcomm _ hk') N f hth hN⟩
  have hmem := _root_.GlobalTheory.StdUnn.sch_mem_fockA D ψ₀ hstd θ hθ A V μ 𝓕 hμ μ' hsk s' s hstd' hs l habs _ hfock'
  have htrk := htr (κ.symm k) f hf Φ hfΦ.symm
  rw [show κ (κ.symm k) = k from κ.apply_symm_apply k] at htrk
  exact Eq.mpr (congrArg (fun φ : Mx D V.rank n → ℂ => φ ∈ fockA θ V n l s) htrk) hmem

end GlobalTheory.CompanionTheory.PfSWUS

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NodeFunctionLeviDecomposition
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.LimV.NodeApply

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ}

theorem levi_eq_mul_cf (u u' : BlockIx (r + s) r → Ad E) (m m' : GA E r × GA E s) (k k' : Kinf E (r + s))
    (c c' : GL (Fin (r + s)) (Af E)) (hc : c ∈ KO E (r + s)) (hc' : c' ∈ KO E (r + s))
    (h : unip u * lev (Ad E) r s m * cf (r + s) k c = unip u' * lev (Ad E) r s m' * cf (r + s) k' c') :
    ∃ (k₁ : Kinf E r) (c₁ : GL (Fin r) (Af E)) (k₂ : Kinf E s) (c₂ : GL (Fin s) (Af E)),
      c₁ ∈ KO E r ∧ c₂ ∈ KO E s ∧ m' = (m.1 * cf r k₁ c₁, m.2 * cf s k₂ c₂) := by
  obtain ⟨v, hv⟩ := lev_mul_unip (m⁻¹) (-u + u')
  have hu : (unip u : GA E (r + s))⁻¹ = unip (-u) := by
    rw [inv_eq_iff_mul_eq_one, ← D.unip_add', add_neg_cancel, unip_zero]
  have key : unip v * lev (Ad E) r s (m⁻¹ * m') = cf (r + s) (k * k'⁻¹) (c * c'⁻¹) := by
    rw [← cf_mul, ← cf_inv, map_mul, ← mul_assoc, ← hv, D.unip_add', map_inv, ← hu]
    have h2 : unip u' * lev (Ad E) r s m' =
        unip u * lev (Ad E) r s m * cf (r + s) k c * (cf (r + s) k' c')⁻¹ := by
      rw [h]; group
    rw [mul_assoc (lev (Ad E) r s m)⁻¹, mul_assoc (unip u)⁻¹, h2]
    group
  obtain ⟨k₁, c₁, k₂, c₂, h₁, h₂, hm⟩ := GlobalTheory.T.levi_factor_of_unipotent_decomp v (m⁻¹ * m') _ _
    (mul_mem hc (inv_mem hc')) key
  refine ⟨k₁, c₁, k₂, c₂, h₁, h₂, ?_⟩
  calc m' = m * (m⁻¹ * m') := (mul_inv_cancel_left m m').symm
    _ = _ := by rw [hm]; rfl

theorem nodeFn_apply : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {r s : ℕ} (e₁ : GA E r → ℂ) (e₂ : GA E s → ℂ), FlatFn e₁ → FlatFn e₂ → ∀ (u : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s)) (c : GL (Fin (r + s)) (Af E)), c ∈ KO E (r + s) → nodeFn e₁ e₂ (unip u * lev (Ad E) r s m * cf (r + s) k c) = e₁ m.1 * e₂ m.2 := by
  intro E _ _ _ r s e₁ e₂ f₁ f₂ u m k c hc
  obtain ⟨k', c', hc', hx'⟩ :=
    (exists_iw (unip u * lev (Ad E) r s m * cf (r + s) k c)).choose_spec.choose_spec
  obtain ⟨k₁, c₁, k₂, c₂, h₁, h₂, hm⟩ := levi_eq_mul_cf u _ m _ k k' c c' hc hc' hx'
  have hl : leviOf (unip u * lev (Ad E) r s m * cf (r + s) k c) =
      (m.1 * cf r k₁ c₁, m.2 * cf s k₂ c₂) := hm
  rw [nodeFn, hl, f₁.rinv _ _ _ h₁, f₂.rinv _ _ _ h₂]

end GlobalTheory.CompanionTheory.LimV.NodeApply

end
end

