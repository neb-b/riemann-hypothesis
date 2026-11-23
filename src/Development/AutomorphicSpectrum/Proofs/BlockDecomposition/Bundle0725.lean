module

public import Mathlib
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
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0714
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0721
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0456
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0362
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0561
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0677
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0674
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0710
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0706
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0658
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolarPartIdentity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0672
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1830
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0723
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0414
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0454
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TypedSpaceApproximation
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreSubgroupOpenCompact
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

open GlobalTheory.SplitWeil

namespace GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

variable {k : Type} [Field k]

theorem colv_uM_mul_levi (n : ℕ) (y : Fin n → k) (b : GL (Fin n) k) :
    GlobalTheory.CompanionTheory.MirLevi.colv (uM k n y * levi k n b) = y := by
  have hu : ((GlobalTheory.CompanionTheory.BZPsiPG.uM k n y : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      1 + GlobalTheory.BZMir.colMat k n y := by
    first
    | rfl
    | (ext a c; simp [GlobalTheory.CompanionTheory.BZPsiPG.uM, GlobalTheory.BZMir.unip])
  have hL : ((GlobalTheory.BZMir.levi k n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      GlobalTheory.BZMir.glEmbMat k n (b : Matrix (Fin n) (Fin n) k) := rfl
  funext i
  simp only [GlobalTheory.CompanionTheory.MirLevi.colv, Subgroup.coe_mul, Units.val_mul, hu, hL]
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp [GlobalTheory.BZMir.glEmbMat, GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last]

theorem eq_uM_colv_mul_levi (n : ℕ) (p : Mir k n) :
    p = uM k n (GlobalTheory.CompanionTheory.MirLevi.colv p) * levi k n (mirabolicProjection k n p) := by
  have hl (g : GL (Fin n) k) : mirabolicProjection k n (levi k n g) = g := by
    apply Units.ext
    ext i j
    change GlobalTheory.BZMir.blockMat k n (GlobalTheory.BZMir.glEmbMat k n (g : Matrix (Fin n) (Fin n) k)) i j = (g : Matrix (Fin n) (Fin n) k) i j
    simp [GlobalTheory.BZMir.blockMat, GlobalTheory.BZMir.glEmbMat]
  have h1 : GlobalTheory.BZMir.mirabolicProjection k n
      (p * (GlobalTheory.BZMir.levi k n (GlobalTheory.BZMir.mirabolicProjection k n p))⁻¹) = 1 := by
    rw [map_mul, map_inv, hl, mul_inv_cancel]
  have hm : p * (levi k n (mirabolicProjection k n p))⁻¹ ∈ MirUin k n := by
    let q := p * (levi k n (mirabolicProjection k n p))⁻¹
    have hrow : ∀ j, ((q : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j =
        GlobalTheory.BZMir.eLast k n j :=
      fun j => congrFun ((GlobalTheory.BZMir.mem_Mir_iff k (q : GL (Fin (n + 1)) k)).1 q.2) j
    have hblock : ∀ i j : Fin n,
        ((q : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.castSucc j) =
          (1 : Matrix (Fin n) (Fin n) k) i j :=
      fun i j => congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i j) h1
    change q ∈ MirUin k n
    rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU, MonoidHom.mem_range]
    refine ⟨Multiplicative.ofAdd fun i =>
      ((q : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n), ?_⟩
    apply Units.ext
    ext i j
    change ((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) + GlobalTheory.BZMir.colMat k n (fun i =>
      ((q : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n))) i j =
      ((q : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j
    rw [Matrix.add_apply, GlobalTheory.BZMir.colMat]
    rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last j with ⟨j, rfl⟩ | rfl
    · simp [Matrix.one_apply, Fin.castSucc_ne_last, hblock]
    · simp [Matrix.one_apply, Fin.castSucc_ne_last]
    · simp [Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm, hrow, GlobalTheory.BZMir.eLast]
    · simp [hrow, GlobalTheory.BZMir.eLast]
  obtain ⟨y, hy⟩ := GlobalTheory.CompanionTheory.BZPsiPG.exists_uM_of_mem k n hm
  have hp : p = GlobalTheory.CompanionTheory.BZPsiPG.uM k n y *
      GlobalTheory.BZMir.levi k n (GlobalTheory.BZMir.mirabolicProjection k n p) := by
    rw [← hy, inv_mul_cancel_right]
  have hy' : GlobalTheory.CompanionTheory.MirLevi.colv p = y := by
    rw [hp]
    exact GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.colv_uM_mul_levi n y _
  rw [hy']
  exact hp

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem continuous_colv (n : ℕ) : Continuous (GlobalTheory.CompanionTheory.MirLevi.colv : Mir k n → Fin n → k) := by
  show Continuous fun p : GlobalTheory.BZMir.Mir k n => fun i : Fin n =>
    ((p : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc i) (Fin.last n)
  first
  | exact continuous_pi fun i =>
      (Units.continuous_val.comp continuous_subtype_val).matrix_elem (Fin.castSucc i) (Fin.last n)
  | exact continuous_pi fun i => (continuous_apply (Fin.last n)).comp
      ((continuous_apply (Fin.castSucc i)).comp (Units.continuous_val.comp continuous_subtype_val))
  | fun_prop

theorem coe_Bgrp_eq (n : ℕ) (c : kˣ) (K₁ : Subgroup (GL (Fin n) k)) (h : K₁ ≤ KO k (Fin n)) :
    (Bgrp n c K₁ h : Set (Mir k n)) =
      GlobalTheory.CompanionTheory.MirLevi.colv ⁻¹' (latt n c : Set (Fin n → k)) ∩ mirabolicProjection k n ⁻¹' (K₁ : Set (GL (Fin n) k)) := by
  have hl (g : GL (Fin n) k) : mirabolicProjection k n (levi k n g) = g := by
    apply Units.ext
    ext i j
    change GlobalTheory.BZMir.blockMat k n (GlobalTheory.BZMir.glEmbMat k n (g : Matrix (Fin n) (Fin n) k)) i j = (g : Matrix (Fin n) (Fin n) k) i j
    simp [GlobalTheory.BZMir.blockMat, GlobalTheory.BZMir.glEmbMat]
  have hu (y : Fin n → k) : mirabolicProjection k n (uM k n y) = 1 := by
    apply Units.ext
    ext i j
    change GlobalTheory.BZMir.blockMat k n (1 + GlobalTheory.BZMir.colMat k n y) i j = (1 : Matrix (Fin n) (Fin n) k) i j
    simp [GlobalTheory.BZMir.blockMat, GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last]
  ext p
  change (∃ y ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt n c, ∃ b ∈ K₁,
      p = GlobalTheory.CompanionTheory.BZPsiPG.uM k n y * GlobalTheory.BZMir.levi k n b) ↔
    (GlobalTheory.CompanionTheory.MirLevi.colv p ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt n c ∧ GlobalTheory.BZMir.mirabolicProjection k n p ∈ K₁)
  constructor
  · rintro ⟨y, hy, b, hb, rfl⟩
    refine ⟨?_, ?_⟩
    · rwa [GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.colv_uM_mul_levi]
    · rwa [map_mul, hu, hl, one_mul]
  · rintro ⟨hy, hb⟩
    exact ⟨_, hy, _, hb, GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.eq_uM_colv_mul_levi n p⟩

theorem coe_Bgrp_eq_image (n : ℕ) (c : kˣ) (K₁ : Subgroup (GL (Fin n) k)) (h : K₁ ≤ KO k (Fin n)) :
    (Bgrp n c K₁ h : Set (Mir k n)) =
      (fun q : (Fin n → k) × GL (Fin n) k => uM k n q.1 * levi k n q.2) ''
        ((latt n c : Set (Fin n → k)) ×ˢ (K₁ : Set (GL (Fin n) k))) := by
  ext p
  change (∃ y ∈ GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.latt n c, ∃ b ∈ K₁,
      p = GlobalTheory.CompanionTheory.BZPsiPG.uM k n y * GlobalTheory.BZMir.levi k n b) ↔ _
  constructor
  · rintro ⟨y, hy, b, hb, rfl⟩
    exact ⟨(y, b), ⟨hy, hb⟩, rfl⟩
  · rintro ⟨⟨y, b⟩, ⟨hy, hb⟩, rfl⟩
    exact ⟨y, hy, b, hb, rfl⟩

theorem isOpen_isCompact_Bgrp : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) (c : kˣ) (K₁ : Subgroup (GL (Fin n) k))
    (h : K₁ ≤ GlobalTheory.SplitWeil.KO k (Fin n)), IsOpen (K₁ : Set (GL (Fin n) k)) →
    IsOpen (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp n c K₁ h : Set (Mir k n)) ∧
      IsCompact (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.Bgrp n c K₁ h : Set (Mir k n)) := by
  intro k _ _ _ _ n c K₁ h hK
  have hc : Continuous (levi k n) ∧ Continuous (uM k n) ∧ Continuous (mirabolicProjection k n) := by
    refine ⟨GlobalTheory.CompanionTheory.BZMirFun.continuous_levi k n, GlobalTheory.CompanionTheory.BZPsiPG.Cont.continuous_uM k n, ?_⟩
    have hval : Continuous fun g : Mir k n =>
        ((g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
      Units.continuous_val.comp continuous_subtype_val
    have hblock : Continuous fun g : Mir k n =>
        ((mirabolicProjection k n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
      refine continuous_pi fun i => continuous_pi fun j => ?_
      exact (continuous_apply (Fin.castSucc j)).comp ((continuous_apply (Fin.castSucc i)).comp hval)
    refine Units.continuous_iff.2 ⟨hblock, ?_⟩
    have heq : (fun g : Mir k n => (((mirabolicProjection k n g)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) =
        fun g => ((mirabolicProjection k n g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
      funext g
      rw [map_inv]
    show Continuous (fun g : Mir k n => (((mirabolicProjection k n g)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))
    rw [heq]
    exact hblock.comp continuous_inv
  refine ⟨?_, ?_⟩
  · rw [GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.coe_Bgrp_eq]
    exact ((GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.isOpen_latt n c).preimage (GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.continuous_colv n)).inter
      (hK.preimage hc.2.2)
  · rw [GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.coe_Bgrp_eq_image]
    have hK₁ : IsCompact (K₁ : Set (GL (Fin n) k)) :=
      (GlobalTheory.SplitFlip.isCompact_KO (k := k) (n := Fin n)).of_isClosed_subset
        (K₁.isClosed_of_isOpen hK) (SetLike.coe_subset_coe.mpr h)
    exact ((GlobalTheory.CompanionTheory.BZPsiPG.FibOnto.isCompact_latt n c).prod hK₁).image
      ((hc.2.1.comp continuous_fst).mul (hc.1.comp continuous_snd))

end GlobalTheory.CompanionTheory.BZPsiPG.FibOnto

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightPowerIntegrableWeylOrbit
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HermConv

theorem integrable_height_rpow : ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) (H : G D n → ℝ≥0), IsHt H →
  (∃ C : Set (G D n), IsCompact C ∧ ∀ g, ∃ q ∈ P D n, ∃ c ∈ C, g = q * c) → ∀ τ : ℝ, (ρ : ℝ) < τ →
    Integrable (fun ζ : hermA D ρ => (H (M.w * M.nzx ζ 0) : ℝ) ^ τ) m.lz := by
  intro D n ρ p hn M m H hH hC τ hτ
  have hτ0 : 0 ≤ τ := le_of_lt (lt_of_le_of_lt (Nat.cast_nonneg ρ) hτ)
  have hadj0 : ∀ k l : ℕ, GlobalTheory.MixModel.adj (0 : Mx D k l) = 0 := by
    intro k l
    show ((0 : Mx D k l).map (cA D)).transpose = 0
    ext i j
    simp
  have hadj1 : GlobalTheory.MixModel.adj (1 : Mx D ρ ρ) = 1 := by
    show ((1 : Mx D ρ ρ).map (cA D)).transpose = 1
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  have hadjn1 : GlobalTheory.MixModel.adj (-1 : Mx D ρ ρ) = -1 := by
    show ((-1 : Mx D ρ ρ).map (cA D)).transpose = -1
    rw [Matrix.map_neg _ (fun a => map_neg (cA D) a), Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.transpose_neg, Matrix.transpose_one]
  have hone : GlobalTheory.StdUnn.blk4 (1 : Mx D ρ ρ) 0 0 1 = 1 := by
    show (Matrix.fromBlocks (1 : Mx D ρ ρ) 0 0 1).submatrix ⇑finSumFinEquiv.symm ⇑finSumFinEquiv.symm = 1
    rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
  have hJ1 : GlobalTheory.StdUnn.blk4 (0 : Mx D ρ ρ) 1 (-1) 0 * GlobalTheory.StdUnn.blk4 0 (-1) 1 0 = 1 := by
    rw [GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul]
    simp only [zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero, neg_mul, mul_neg, neg_neg, neg_zero]
    exact hone
  have hJ2 : GlobalTheory.StdUnn.blk4 (0 : Mx D ρ ρ) (-1) 1 0 * GlobalTheory.StdUnn.blk4 0 1 (-1) 0 = 1 := by
    rw [GlobalTheory.StdUnn.Model.submatrix_fromBlocks_mul]
    simp only [zero_mul, mul_zero, one_mul, mul_one, zero_add, add_zero, neg_mul, mul_neg, neg_neg, neg_zero]
    exact hone
  let u : GL (Fin (ρ + ρ)) (AE D) := ⟨GlobalTheory.StdUnn.blk4 0 1 (-1) 0, GlobalTheory.StdUnn.blk4 0 (-1) 1 0, hJ1, hJ2⟩
  have hu : GlobalTheory.MixModel.adj (u : Mx D (ρ + ρ) (ρ + ρ)) * GlobalTheory.StdUnn.blk4 0 1 (-1) 0 * (u : Mx D (ρ + ρ) (ρ + ρ)) =
      GlobalTheory.StdUnn.blk4 0 1 (-1) 0 := by
    show GlobalTheory.MixModel.adj (GlobalTheory.StdUnn.blk4 (0 : Mx D ρ ρ) 1 (-1) 0) * GlobalTheory.StdUnn.blk4 0 1 (-1) 0 *
      GlobalTheory.StdUnn.blk4 0 1 (-1) 0 = GlobalTheory.StdUnn.blk4 0 1 (-1) 0
    rw [GlobalTheory.CompanionTheory.JacobiMaps.adjoint_symplectic_block_product, hadj0, hadj1, hadjn1]
    simp only [zero_mul, mul_zero, one_mul, mul_one, sub_zero, zero_sub, neg_neg, mul_neg, neg_mul, sub_self, neg_zero]
  obtain ⟨ι, hιc, hιm⟩ := _root_.GlobalTheory.CompanionTheory.FirstBlockEmb.exists_first_emb D n ρ p hn
  have hH' := _root_.GlobalTheory.CompanionTheory.HtPull.isHt_blockPull D n ρ p hn ι hιc hιm H hH
  let w' : G D ρ := GlobalTheory.CompanionTheory.JacobiMaps.mkG u hu
  have hw' : GlobalTheory.StdUnn.mat w' = GlobalTheory.StdUnn.blk4 0 1 (-1) 0 := GlobalTheory.CompanionTheory.JacobiMaps.mat_mkG u hu
  let nb : hermA D ρ → G D ρ := fun z => GlobalTheory.CompanionTheory.JacobiMaps.nAt (z : Mx D ρ ρ) z.2
  have hnb : ∀ z : hermA D ρ, GlobalTheory.StdUnn.mat (nb z) = GlobalTheory.StdUnn.blk4 1 (z : Mx D ρ ρ) 0 1 :=
    fun z => GlobalTheory.CompanionTheory.JacobiMaps.mat_nAt _ _
  have hS := _root_.GlobalTheory.CompanionTheory.HermSum.summable_height_rpow D ρ (fun h => H (ι h)) hH' w' nb hw' hnb τ hτ
  have hιw : ι w' = M.w := by
    apply GlobalTheory.CompanionTheory.FourierN.mat_injective
    rw [hιm w' 0 1 (-1) 0 hw', M.w_mat]
  have hιn : ∀ z : hermA D ρ, ι (nb z) = M.nzx z 0 := by
    intro z
    apply GlobalTheory.CompanionTheory.FourierN.mat_injective
    rw [hιm (nb z) 1 (z : Mx D ρ ρ) 0 1 (hnb z), M.nzx_mat, hadj0, GlobalTheory.CompanionTheory.PcB.blockMatrix_one, GlobalTheory.CompanionTheory.JacobiMaps.blockMatrix_zero]
  have hf_eq : ∀ z : hermA D ρ, (H (M.w * M.nzx z 0) : ℝ) ^ τ = (H (ι (w' * nb z)) : ℝ) ^ τ := by
    intro z
    rw [map_mul, hιw, hιn]
  have hSum : Summable (fun ζ : ratHerm D ρ => (H (M.w * M.nzx (ζ : hermA D ρ) 0) : ℝ) ^ τ) := by
    simpa only [hf_eq] using hS
  obtain ⟨K, hK, hKc⟩ := GlobalTheory.CompanionTheory.FourierN.exists_compact_cover (D := D) (n := ρ)
  have hNc : Continuous fun z : hermA D ρ => M.nzx z 0 := GlobalTheory.CompanionTheory.PcB.continuous_nz M
  obtain ⟨κ, hκ1, hκ⟩ := GlobalTheory.CompanionTheory.HtRightTranslate.height_mul_le D n H hH hC
    ((fun z => M.nzx z 0) '' K) (hK.image hNc)
  refine _root_.GlobalTheory.CompanionTheory.HermFD.integrable_of_periodisation_bound D ρ m.lz m.𝓖 m.hz (fun ζ => (H (M.w * M.nzx ζ 0) : ℝ) ^ τ) ?_ ?_ hSum K hKc (κ ^ τ)
    (Real.rpow_nonneg (by linarith) τ) ?_
  · exact (NNReal.continuous_coe.comp (hH.1.comp (continuous_const.mul hNc))).rpow_const fun _ => Or.inr hτ0
  · exact fun z => Real.rpow_nonneg (NNReal.coe_nonneg _) τ
  · intro ζ _ z hz
    have h1 : M.nzx (ζ + z) 0 = M.nzx ζ 0 * M.nzx z 0 := by
      rw [GlobalTheory.CompanionTheory.PcB.nzx_mul, add_zero]
    have h2 := hκ (M.nzx z 0) ⟨z, hz, rfl⟩ (M.w * M.nzx ζ 0)
    show (H (M.w * M.nzx (ζ + z) 0) : ℝ) ^ τ ≤ κ ^ τ * (H (M.w * M.nzx ζ 0) : ℝ) ^ τ
    rw [h1, ← mul_assoc, ← Real.mul_rpow (by linarith) (NNReal.coe_nonneg _)]
    exact Real.rpow_le_rpow (NNReal.coe_nonneg _) h2 hτ0

end GlobalTheory.CompanionTheory.HermConv

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTensorPower
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.PowRep

open GlobalTheory.CuspDim.IsoPow
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet (powLine powLine_a constLine)

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem h_powLine {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : Geo.HermLine ι) (r : ℕ)
    (z : (Σ k, ι k) → ℂ) : (powLine A r).h z = A.h z ^ r := by
  induction r with
  | zero => simp [powLine, constLine]
  | succ r ih => simp [powLine, Geo.HermLine.tensor, ih, pow_succ]

theorem frame_pow {Z : Scheme.{0}} (B : LB Z) (r : ℕ) (V : Z.Opens) (u : ∀ i, Γ(Z, B.U i ⊓ V)ˣ)
    (h : ∀ i j, Semi.res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
          B.U i ⊓ B.U j ⊓ V ≤ B.U j ⊓ V) (u j) =
        Semi.res (inf_le_left : B.U i ⊓ B.U j ⊓ V ≤ B.U i ⊓ B.U j) (B.g i j) *
          Semi.res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
            B.U i ⊓ B.U j ⊓ V ≤ B.U i ⊓ V) (u i))
    (j j' : PUnit.{1} → B.ι) :
    Semi.res (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
        (lbPow B r).U j ⊓ (lbPow B r).U j' ⊓ V ≤ (lbPow B r).U j' ⊓ V)
        (Semi.res (inf_le_inf_right V (pow_le r j')) (u (j' PUnit.unit)) ^ r) =
      Semi.res (inf_le_left : (lbPow B r).U j ⊓ (lbPow B r).U j' ⊓ V ≤ (lbPow B r).U j ⊓ (lbPow B r).U j')
          ((lbPow B r).g j j') *
        Semi.res (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
          (lbPow B r).U j ⊓ (lbPow B r).U j' ⊓ V ≤ (lbPow B r).U j ⊓ V)
          (Semi.res (inf_le_inf_right V (pow_le r j)) (u (j PUnit.unit)) ^ r) := by
  have hW : (lbPow B r).U j ⊓ (lbPow B r).U j' ⊓ V ≤
      B.U (j PUnit.unit) ⊓ B.U (j' PUnit.unit) ⊓ V :=
    inf_le_inf_right V (inf_le_inf (pow_le r j) (pow_le r j'))
  have e := congrArg (fun t => Semi.res hW t ^ r) (h (j PUnit.unit) (j' PUnit.unit))
  simp only [map_mul, mul_pow, GlobalTheory.CuspDim.IsoPow.res_res] at e
  rw [res_pow_g]
  simp only [map_pow, GlobalTheory.CuspDim.IsoPow.res_res]
  exact e

theorem res_blockUnit {k : Fin (m + 1)} (i j : Bk n k) {W W' : (MP ℤ m n).Opens}
    (h : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) (h' : W' ≤ W) :
    Semi.res h' (blockUnit i j h) = blockUnit i j (h'.trans h) :=
  GlobalTheory.CuspDim.IsoPow.res_res _ _ _

theorem ev_res_pow {p : (MP ℤ m n) ⟶ Sp ℤ} {W U : (MP ℤ m n).Opens} (h : W ≤ U) (v : Γ(MP ℤ m n, U)ˣ) (r : ℕ)
    {y : CxPts p σ₀} (hy : y ∈ ptsIn p σ₀ W) :
    CxPts.ev p σ₀ W ((Semi.res h v ^ r : Γ(MP ℤ m n, W)ˣ) : Γ(MP ℤ m n, W)) y =
      CxPts.ev p σ₀ U (v : Γ(MP ℤ m n, U)) y ^ r := by
  rw [Units.val_pow_eq_pow_val, CxPts.ev_eq hy, map_pow, ← CxPts.ev_eq hy]
  exact congrArg (· ^ r) (CxPts.ev_res h hy _)

theorem chart_pow {B : LB (MP ℤ m n)} (A : Geo.HermLine (Bk n)) (r : ℕ) (j : PUnit.{1} → B.ι) (c c' : ∀ k, Bk n k)
    (v : Γ(MP ℤ m n, B.U (j PUnit.unit) ⊓ mchart c)ˣ) (v' : Γ(MP ℤ m n, B.U (j PUnit.unit) ⊓ mchart c')ˣ)
    (h : Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
          B.U (j PUnit.unit) ⊓ (mchart c ⊓ mchart c') ≤ B.U (j PUnit.unit) ⊓ mchart c) v =
        Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
          B.U (j PUnit.unit) ⊓ (mchart c ⊓ mchart c') ≤ B.U (j PUnit.unit) ⊓ mchart c') v' *
        ∏ k, blockUnit (c k) (c' k) (fun _ hx =>
          ⟨mchart_le c k hx.2.1, mchart_le c' k hx.2.2⟩ :
            B.U (j PUnit.unit) ⊓ (mchart c ⊓ mchart c') ≤
              prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))) ^ A.a k) :
    Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_left) :
        (lbPow B r).U j ⊓ (mchart c ⊓ mchart c') ≤ (lbPow B r).U j ⊓ mchart c)
        (Semi.res (inf_le_inf_right _ (pow_le r j)) v ^ r) =
      Semi.res (le_inf inf_le_left (inf_le_right.trans inf_le_right) :
        (lbPow B r).U j ⊓ (mchart c ⊓ mchart c') ≤ (lbPow B r).U j ⊓ mchart c')
        (Semi.res (inf_le_inf_right _ (pow_le r j)) v' ^ r) *
      ∏ k, blockUnit (c k) (c' k) (fun _ hx =>
        ⟨mchart_le c k hx.2.1, mchart_le c' k hx.2.2⟩ :
          (lbPow B r).U j ⊓ (mchart c ⊓ mchart c') ≤
            prB n k ⁻¹ᵁ (chart ℤ (n k) (c k) ⊓ chart ℤ (n k) (c' k))) ^ (powLine A r).a k := by
  have hW : (lbPow B r).U j ⊓ (mchart c ⊓ mchart c') ≤ B.U (j PUnit.unit) ⊓ (mchart c ⊓ mchart c') :=
    inf_le_inf_right _ (pow_le r j)
  have e := congrArg (fun t => Semi.res hW t ^ r) h
  simp only [map_mul, mul_pow, map_prod, map_zpow, res_blockUnit, GlobalTheory.CuspDim.IsoPow.res_res] at e
  simp only [map_pow, GlobalTheory.CuspDim.IsoPow.res_res]
  refine e.trans (congrArg _ ?_)
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [powLine_a, mul_comm, zpow_mul, zpow_natCast]
  exact congrArg (fun t => (t ^ A.a k) ^ r) (res_blockUnit _ _ _ _)

theorem isHermRep_pow (m : ℕ) (n : Fin (m + 1) → ℕ) (M : HermLB (mpStr ℤ m n)) (A : Geo.HermLine (Bk n)) (r : ℕ)
    (hM : IsHermRep M A) : IsHermRep (M.pow r) (powLine A r) := by
  obtain ⟨u, h₁, h₂, h₃⟩ := hM
  refine ⟨fun (j : PUnit.{1} → M.B.ι) c =>
    Semi.res (inf_le_inf_right _ (pow_le (B := M.B) r j)) (u (j PUnit.unit) c) ^ r, ?_, ?_, ?_⟩
  · intro j j' c
    exact frame_pow M.B r (mchart c) (fun i => u i c) (fun i j => h₁ i j c) j j'
  · intro j c c'
    exact chart_pow A r j c c' _ _ (h₂ (j PUnit.unit) c c')
  · intro (j : PUnit.{1} → M.B.ι) c y z hz hy
    have hy' : y ∈ ptsIn (mpStr ℤ m n) σ₀ (M.B.U (j PUnit.unit) ⊓ mchart c) :=
      CxPts.ptsIn_mono (inf_le_inf_right _ (pow_le (B := M.B) r j)) hy
    have e := h₃ (j PUnit.unit) c y z hz hy'
    have eφ : ((M.pow r).φ σ₀).φ j y = r * (M.φ σ₀).φ (j PUnit.unit) y := by
      exact ((M.φ σ₀).zpow_φ r j y).trans (by simp)
    have ev := ev_res_pow (p := mpStr ℤ m n) (inf_le_inf_right (mchart c) (pow_le (B := M.B) r j))
      (u (j PUnit.unit) c) r hy
    beta_reduce
    rw [h_powLine, e, eφ, show CxPts.ev (mpStr ℤ m n) σ₀ ((M.pow r).B.U j ⊓ mchart c) _ y = _ from ev, norm_pow, mul_pow, mul_pow, ← Finset.prod_pow,
      ← Real.exp_nat_mul, mul_div_assoc]
    congr 2
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [powLine_a, mul_comm, zpow_mul, zpow_natCast]

end GlobalTheory.CompanionTheory.MPDict.PowRep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothFibreActionStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG GlobalTheory.CompanionTheory.BZPsiPG.FibKer
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_fibre_action : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {Z : Type} [AddCommGroup Z] [Module ℂ Z] (ρ₀ : Representation ℂ (Multiplicative (Fin i → k)) Z), IsSmooth ρ₀ → IsSmooth (fibAct t ρ₀) := by
  first | exact @GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmFib.isSmooth_fibAct | exact GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmFib.isSmooth_fibAct | (intros; apply GlobalTheory.CompanionTheory.BZPsiPG.FibKer.SmFib.isSmooth_fibAct <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothTensorFixedParabolicNearOne
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.Stab

theorem hRep_fix : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ z : V ⊗[ℂ] W, ∃ U ∈ nhds (1 : Mir k (i + t)), ∀ h : HPG k i t, (h : Mir k (i + t)) ∈ U → hRep τ σ h z = z := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ hτ hσ z
  have hs : IsSmooth (hRep τ σ) :=
    isSmooth_comp (isSmooth_extTensor hτ hσ) _ (GlobalTheory.CompanionTheory.BZPhiPG.Onto.continuous_pgProj k i t)
  obtain ⟨O, hO, e⟩ := isOpen_induced_iff.1 (hs z)
  have hmem : ∀ h : HPG k i t, (h : Mir k (i + t)) ∈ O ↔ hRep τ σ h z = z := fun h =>
    Set.ext_iff.1 e h
  have h1 : (1 : Mir k (i + t)) ∈ O := (hmem 1).2 (by simp)
  exact ⟨O, hO.mem_nhds h1, fun h hh => (hmem h).1 hh⟩

end GlobalTheory.CompanionTheory.BZPsiPG.Stab
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TypedSpaceApproximationStatement
section
open scoped Classical
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typed_space_approximation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)]
  (μ : Measure (GA E N)) [μ.IsHaarMeasure] (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ))
  (R ε δ : ℝ) (α : GA E N → ℂ) (F : Set (GA E N)), IsOpen (K : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W → 0 < ε →
  Continuous α → HasCompactSupport α → 0 < δ → IsFundamentalDomain (latticeGL E N) F μ →
  ∃ Ω : Set (GA E N), IsCompact Ω ∧ ∀ (V : Submodule ℂ (Sm E N)) (ψ : Sm E N), IsDiscrete V → ψ ∈ V → TypeB K W ψ →
    InfBdd R V → (∀ r, 0 < r → r < N → ∀ c ∈ ExpV r V, pE E N r c ≤ -ε * (r * ((N : ℝ) - r))) →
    (∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ.1 (x * y) ∂μ = s * ψ.1 x) →
    (∫⁻ x in F, ‖ψ.1 x‖ₑ ^ 2 ∂μ) = 1 → 1 ≤ 2 * ∫⁻ x in Ω, ‖ψ.1 x‖ₑ ^ 2 ∂μ := by
  first | exact @GlobalTheory.CompanionTheory.Conc.conc | exact GlobalTheory.CompanionTheory.Conc.conc | (intros; apply GlobalTheory.CompanionTheory.Conc.conc <;> assumption)
end

