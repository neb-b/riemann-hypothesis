module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AbelianVarietyTheory.Definitions.Divisors.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1479
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1599

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.AbsHcExponentLeAndAbsCenterLeOfSizeRows
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

theorem UpperTheory.abs_hc_exponent_le_and_abs_center_le_of_sizeRows :
    ∀ (D : D7) (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → HostHyp D → (∀ τ l, |(((D.hc τ).e l : ℚ) : ℝ)| ≤ 4 * large₂.sc.b) ∧ ∀ τ i, 1 ≤ i → i ≤ D.R.m → |((cen D 1 τ i : ℤ) : ℝ)| ≤ 2 * large₂.sc.b := by
  intro D large₂ hS hH
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hb, he, -⟩ := hS
  have hbpos : 0 < large₂.sc.b := by
    have := large₂.Sc_pos
    have : (0 : ℝ) ≤ (↑D.R.m + 1) * ↑(gap D 1) := by positivity
    linarith
  refine ⟨fun τ l => ?_, fun τ i hi him => ?_⟩
  · obtain ⟨hb0, he0⟩ := he τ l
    have hg := ((hH.gap τ l).1)
    have ht : (0 : ℚ) ≤ ((D.R.t : ℚ) + 3) / 2 := by positivity
    have hepos : (0 : ℚ) ≤ (D.hc τ).e l := by linarith
    have hepos' : (0 : ℝ) ≤ (((D.hc τ).e l : ℚ) : ℝ) := by exact_mod_cast hepos
    rw [abs_of_nonneg hepos']
    exact he0
  · set G := GlobalTheory.SignedHC.GridData.ofHCParam (D.hc τ) (sLen D) (gap D 1) 0 with hG
    have hcen : cen D 1 τ i = ⌊G.mid i⌋ := rfl
    have hmid : G.mid i = G.a i + (G.ga : ℚ) / 2 := G.mid_eq hi
    have ha : G.a i = (G.v 2 : ℚ) + 1 / 2 + ((G.m : ℚ) + 1 - i) * G.ga := rfl
    have hm : G.m = D.R.m := rfl
    have hga : G.ga = gap D 1 := rfl
    have hv : 0 ≤ G.v 2 ∧ ((G.v 2 : ℚ) : ℝ) ≤ large₂.Sc := by
      by_cases hk : 0 < D.R.k - 1
      · have hv2 : G.v 2 = ⌊(D.hc τ).v ⟨0, hk⟩⌋ := by
          simp [hG, GlobalTheory.SignedHC.GridData.ofHCParam, GlobalTheory.SignedHC.GridData.extend, hk]
        obtain ⟨h0, h1⟩ := large₂.cloud_v τ ⟨0, hk⟩
        have h0' : (0 : ℚ) ≤ (D.hc τ).v ⟨0, hk⟩ := by exact_mod_cast h0
        refine ⟨?_, ?_⟩
        · rw [hv2]
          exact Int.floor_nonneg.mpr h0'
        · rw [hv2]
          have hfl : ((⌊(D.hc τ).v ⟨0, hk⟩⌋ : ℤ) : ℚ) ≤ (D.hc τ).v ⟨0, hk⟩ := Int.floor_le _
          have hfl' : ((((⌊(D.hc τ).v ⟨0, hk⟩⌋ : ℤ) : ℚ)) : ℝ) ≤ (((D.hc τ).v ⟨0, hk⟩ : ℚ) : ℝ) := by
            exact_mod_cast hfl
          linarith
      · have hv2 : G.v 2 = 0 := by
          simp [hG, GlobalTheory.SignedHC.GridData.ofHCParam, GlobalTheory.SignedHC.GridData.extend, hk]
        rw [hv2]
        refine ⟨le_rfl, ?_⟩
        simpa using large₂.Sc_pos.le
    obtain ⟨hv0, hv1⟩ := hv
    have hi' : (1 : ℚ) ≤ i := by exact_mod_cast hi
    have him' : (i : ℚ) ≤ D.R.m := by exact_mod_cast him
    have hga0 : (0 : ℚ) ≤ G.ga := by positivity
    have hv0' : (0 : ℚ) ≤ G.v 2 := by exact_mod_cast hv0
    have hmid0 : 0 ≤ G.mid i := by
      rw [hmid, ha, hm]
      have : (0 : ℚ) ≤ ((D.R.m : ℚ) + 1 - i) * G.ga := mul_nonneg (by linarith) hga0
      linarith
    have hmid1 : ((G.mid i : ℚ) : ℝ) ≤ large₂.sc.b := by
      have e1 : ((G.mid i : ℚ) : ℝ) = ((G.v 2 : ℚ) : ℝ) + 1 / 2 + (((D.R.m : ℝ) + 1 - i) * (gap D 1 : ℝ)) + (gap D 1 : ℝ) / 2 := by
        rw [hmid, ha, hm, hga]
        push_cast
        ring
      have hgr : (0 : ℝ) ≤ (gap D 1 : ℝ) := by positivity
      have hir : (1 : ℝ) ≤ i := by exact_mod_cast hi
      have : ((D.R.m : ℝ) + 1 - i) * (gap D 1 : ℝ) + (gap D 1 : ℝ) / 2 ≤ ((D.R.m : ℝ) + 1) * (gap D 1 : ℝ) := by
        nlinarith
      linarith
    have hf0 : 0 ≤ cen D 1 τ i := by
      rw [hcen]
      exact Int.floor_nonneg.mpr hmid0
    have hf1 : ((cen D 1 τ i : ℤ) : ℝ) ≤ large₂.sc.b := by
      rw [hcen]
      have hfl : ((⌊G.mid i⌋ : ℤ) : ℚ) ≤ G.mid i := Int.floor_le _
      have hfl' : ((((⌊G.mid i⌋ : ℤ) : ℚ)) : ℝ) ≤ ((G.mid i : ℚ) : ℝ) := by exact_mod_cast hfl
      have : (((⌊G.mid i⌋ : ℤ)) : ℝ) = ((((⌊G.mid i⌋ : ℤ) : ℚ)) : ℝ) := by push_cast; rfl
      linarith
    have hf0' : (0 : ℝ) ≤ ((cen D 1 τ i : ℤ) : ℝ) := by exact_mod_cast hf0
    rw [abs_of_nonneg hf0']
    linarith
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.ExistsMemKOEqStdFrameMulOfIsPrimFrameFin
section
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel

open Matrix in
theorem UpperTheory.exists_mem_KO_eq_stdFrame_mul_of_isPrimFrame_fin :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] {a' : ℕ} (σ : A ⊕ Fin a' ≃ D) (X : Matrix A D k), IsPrimFrame (GlobalTheory.SplitFlip.stdLat k D) X → ∃ κ ∈ GlobalTheory.SplitWeil.KO k D, X = X0 k σ * (invT κ).val := by
  intro k _ _ _ _ A D _ _ _ _ a' σ X hX
  have hXint : ∀ i j, X i j ∈ 𝒪[k] := mem_matLat_stdLat.1 hX.2.1
  obtain ⟨R, hRint, hXR⟩ := GlobalTheory.PrimFrameMove.exists_rightInverse hX
  obtain ⟨h, hh⟩ := (rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ X).1 hX.1
  set Y : Matrix (Fin a') D k := Y0 k σ * (h : Matrix D D k) with hYeq
  have hYX : Y * X.transpose = 0 := by
    rw [hh]
    exact frameSecondBlock_mul_frameFirstBlock_transpose_eq_zero σ h
  have hYrank : Y.rank = a' := by
    have hY0 : Y0 k σ * (Y0 k σ).transpose = 1 := by
      ext i j
      simp [Y0, Matrix.mul_apply, Matrix.one_apply, Finset.sum_ite_eq']
    have hW : Y * (((h⁻¹ : GL D k) : Matrix D D k) * (Y0 k σ).transpose) = 1 := by
      rw [hYeq, Matrix.mul_assoc, ← Matrix.mul_assoc (h : Matrix D D k), ← Units.val_mul,
        mul_inv_cancel, Units.val_one, Matrix.one_mul, hY0]
    have h1 := Matrix.rank_mul_le_left Y (((h⁻¹ : GL D k) : Matrix D D k) * (Y0 k σ).transpose)
    rw [hW, Matrix.rank_one, Fintype.card_fin] at h1
    have h2 := Matrix.rank_le_card_height Y
    rw [Fintype.card_fin] at h2
    omega
  obtain ⟨g₀, hg₀⟩ := GlobalTheory.PrimFrameExist.exists_gl_mul_isPrimFrame k a' D (fun _ => 1) Y hYrank
  set Y' : Matrix (Fin a') D k := (g₀ : Matrix (Fin a') (Fin a') k) * Y with hY'eq
  have hY'prim : IsPrimFrame (stdLat k D) Y' := hg₀
  have hY'int : ∀ i j, Y' i j ∈ 𝒪[k] := mem_matLat_stdLat.1 hY'prim.2.1
  obtain ⟨S, hSint, hY'S⟩ := GlobalTheory.PrimFrameMove.exists_rightInverse hY'prim
  have hY'X : Y' * X.transpose = 0 := by
    rw [hY'eq, Matrix.mul_assoc, hYX, Matrix.mul_zero]
  have hRX : R.transpose * X.transpose = 1 := by
    rw [← Matrix.transpose_mul, hXR, Matrix.transpose_one]
  set S' : Matrix D (Fin a') k := S - X.transpose * (R.transpose * S) with hS'eq
  have hRS' : R.transpose * S' = 0 := by
    rw [hS'eq, Matrix.mul_sub, ← Matrix.mul_assoc, hRX, Matrix.one_mul, sub_self]
  have hY'S' : Y' * S' = 1 := by
    rw [hS'eq, Matrix.mul_sub, ← Matrix.mul_assoc, hY'X, Matrix.zero_mul, sub_zero, hY'S]
  have mulInt : ∀ {m n o : Type} [Fintype n] (P : Matrix m n k) (Q : Matrix n o k),
      (∀ i j, P i j ∈ 𝒪[k]) → (∀ i j, Q i j ∈ 𝒪[k]) → ∀ i j, (P * Q) i j ∈ 𝒪[k] := by
    intro m n o _ P Q hP hQ i j
    rw [Matrix.mul_apply]
    exact sum_mem fun x _ => mul_mem (hP _ _) (hQ _ _)
  have hS'int : ∀ i j, S' i j ∈ 𝒪[k] := by
    intro i j
    rw [hS'eq, Matrix.sub_apply]
    refine sub_mem (hSint i j) ?_
    exact mulInt _ _ (fun a b => hXint b a) (mulInt _ _ (fun a b => hRint b a) hSint) i j
  let K : Matrix D D k := (Matrix.fromRows R.transpose Y').submatrix σ.symm (Equiv.refl D)
  let N : Matrix D D k := (Matrix.fromCols X.transpose S').submatrix (Equiv.refl D) σ.symm
  have hKN : K * N = 1 := by
    simp only [K, N]
    rw [Matrix.submatrix_mul_equiv, Matrix.fromRows_mul_fromCols, hRX, hRS', hY'X, hY'S',
      Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
  have hNK : N * K = 1 := mul_eq_one_comm.1 hKN
  let κ : GL D k := ⟨K, N, hKN, hNK⟩
  refine ⟨κ, ?_, ?_⟩
  · rw [mem_KO_iff]
    constructor
    · intro e d
      show K e d ∈ 𝒪[k]
      simp only [K, Matrix.submatrix_apply, Equiv.refl_apply]
      rcases σ.symm e with i | j
      · simpa using hRint d i
      · simpa using hY'int j d
    · intro d e
      show N d e ∈ 𝒪[k]
      simp only [N, Matrix.submatrix_apply, Equiv.refl_apply]
      rcases σ.symm e with i | j
      · simpa using hXint i d
      · simpa using hS'int d j
  · ext i d
    rw [frameMatrixFirstColumnBlock_mul_apply]
    show X i d = N d (σ (Sum.inl i))
    simp [N]
end

