module

public import Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH
public import Development.AutomorphicArithmetic.PrimitiveCosets.charsA
public import Development.AutomorphicArithmetic.PrimitiveCosets.Bundle0003
public import Development.AutomorphicArithmetic.PrimitiveCosets.Bundle0002
public import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ChTop
public import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ChCore
public import Development.AutomorphicArithmetic.DedekindLFunctions.LandauTheorems.ZeroFreeOfRpowWindow

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.PrimitiveCosets.CoreGm
section
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

theorem UpperTheory.Comparison₂.core_gm :
    ∀ (Λ : Level) (eD eL K cHH eK C eps : ℝ), 0 < eps → ∃ x1 : ℝ, ∀ x ≥ x1, ∀ (φ : Frame) (H : HostAx φ) (TT : Finset φ.A),
      EAtH Λ H.toHostRaw TT x eps C → CoreAtH H.toHostRaw TT eD eL K cHH eK eps x →
        Λ.Gm x ≤ x ^ ((1 : ℝ) / 2 + (eD + eL + 7) * eps) := by
  intro Λ eD eL K cHH eK C eps heps
  have ho : (0 : ℝ) ≤ Λ.o := Nat.cast_nonneg _
  have hc : |(3 * (Λ.o : ℝ) + 1)⁻¹| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact inv_le_one_of_one_le₀ (by linarith)
  obtain ⟨x₁, hx₁⟩ := Deduction.ch_core (max (eD + eL) 0 + 3) eps C (koOf Λ) (3 * (Λ.o : ℝ) + 1)⁻¹ (4 * (Λ.o : ℝ))
    (by positivity) heps hc
  obtain ⟨x₂, hx₂⟩ := large_x_eventually eps K cHH eK heps
  obtain ⟨x₃, hx₃⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop heps).eventually_ge_atTop (1 + 4 * (Λ.o : ℝ)))
  refine ⟨max x₁ (max x₂ x₃), fun x hx φ H TT hE hCore => ?_⟩
  have g1 : x₁ ≤ x := le_trans (le_max_left _ _) hx
  have g2 : x₂ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have g3 : x₃ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨U0, i0, tr, W, i4, i5, Top, i6, m, f, Dd, Cc, Xpp, ell, N, T2, a, w, eT, eP, η, X', θ,
    hell, hxx, hε, heD, heL, hcHH, hcov, hId, hLed, hWin, hBN, hSz, hThin, hCost, hRest, hT2⟩ := hCore
  subst hxx hε
  have hLX := hx₂ _ g2
  have hWin' := hWin
  obtain ⟨⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22,
    w23, w24, w25, w26, w27, wC⟩, wEta⟩ := hWin'
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17⟩ := wC
  have hLX' : LargeX Dd.x Dd.ε K Cc.cHH eK := by
    refine ⟨hLX.1, le_trans ?_ hLX.2⟩
    unfold KBig
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) (by linarith)
  have hb : 0 < Dd.b := by linarith
  have hx0 : 0 < Dd.x := by linarith
  have hk : 0 < Dd.k := by linarith
  have ha : 0 ≤ Dd.a := le_trans (by positivity) w5
  have hE0 : 0 ≤ eD + eL := by linarith
  rw [max_eq_left hE0] at hx₁
  have hBr : 0 ≤ errorBracketSizeWindows Dd.x Dd.ε (Fintype.card φ.A) TT.card T2.card m Dd.b Dd.k Dd.a := by
    unfold errorBracketSizeWindows
    positivity
  have hExp : Dd.x ^ (CErr Cc * Dd.ε) ≤ Dd.x ^ ((eD + eL + 3) * Dd.ε) := by
    refine Real.rpow_le_rpow_of_exponent_le w1 (mul_le_mul_of_nonneg_right ?_ w2.le)
    unfold CErr
    linarith
  have hmain := hx₁ _ g1 φ.A m (arith H.toHostRaw) _ ell N TT T2 a w Dd.b Dd.b' Dd.k Dd.a η X' θ φ.A0
    (keptA Λ H.toHostRaw) (hostFactsS φ H) hb ha hk w7 w8 hSz hThin hCost hRest hT2
    (charsA Λ φ H TT _ _ C ell hx0 hE hell) (fun u hu => by
      obtain ⟨v, rfl⟩ := hcov u hu
      exact le_trans (Deduction.ch_top Dd tr Cc Xpp eK K _ ell N TT T2 a w eT eP hId hLed hWin hBN hLX' v)
        (mul_le_mul_of_nonneg_right hExp hBr))
  rw [gmA_eq Λ φ H TT _ _ C ell hE hell] at hmain
  have hs := sigA_le Λ φ H TT _ _ C ell hx0 hE hell
  have h1 : Dd.x ^ ((1 : ℝ) / 2 + Dd.ε) ≤ Dd.x ^ ((1 : ℝ) / 2 + (eD + eL + 3 + 3) * Dd.ε) :=
    Real.rpow_le_rpow_of_exponent_le w1 (by nlinarith)
  have h2 : Dd.x ^ ((1 : ℝ) / 2 + (eD + eL + 7) * Dd.ε)
      = Dd.x ^ Dd.ε * Dd.x ^ ((1 : ℝ) / 2 + (eD + eL + 3 + 3) * Dd.ε) := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  have h3 := mul_le_mul_of_nonneg_right (hx₃ _ g3)
    (Real.rpow_nonneg hx0.le ((1 : ℝ) / 2 + (eD + eL + 3 + 3) * Dd.ε))
  have h4 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 4 * (Λ.o : ℝ) by positivity)
  rw [h2]
  linarith
end

-- bundled from Development.AutomorphicArithmetic.PrimitiveCosets.Imports
section
open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

theorem UpperTheory.Comparison₂.formB :
    ∀ Λ : Level, Λ.FormB := by
  intro Λ la hla θ hθ0 hθ1 hW
  classical
  let weight (ψ : PChar) : ℝ := if ψ = PChar.one then 1 else Λ.wt ψ
  have weight_pos (ψ : PChar) : 0 < weight ψ := by
    unfold weight Level.wt
    split_ifs
    · exact one_pos
    · exact one_pos
    · positivity
  have admissible (ψ : PChar) : ψ.N = 1 ∨ ψ.χ ≠ 1 := by
    by_cases h : ψ.χ = 1
    · left
      have hp := ψ.prim
      rw [DirichletCharacter.IsPrimitive, h, DirichletCharacter.conductor_one] at hp
      exact hp.symm
    · exact Or.inr h
  let F : Deduction.CharFamily :=
    @Deduction.CharFamily.mk Λ.KEPT _ (fun i => i.1.N) (fun i => i.1.ne)
      (fun i => i.1.χ) (fun i => weight i.1) (fun i => weight_pos i.1)
      (fun i => admissible i.1)
  have hG (y : ℝ) : Deduction.Gm F y = Λ.Gm y := by
    change (∑ i : Λ.KEPT, weight i.1 * (Deduction.Gchi i.1.χ y).re) = Λ.Gm y
    rw [Finset.sum_coe_sort Λ.KEPT (fun ψ => weight ψ * (Deduction.Gchi ψ.χ y).re),
      ← Finset.add_sum_erase _ _ Λ.one_mem, Level.Gm, Level.Nt]
    congr 1
    · have hGz : Formalism.Gz y = An.G y := by
        unfold Formalism.Gz Formalism.Sz An.G
        have hsum : (∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n * (y / n - 1)) =
            ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, An.abelian₂ n * max (y / n - 1) 0 := by
          apply Finset.sum_congr rfl
          intro n hn
          obtain ⟨hn₁, hn₂⟩ := Finset.mem_Icc.mp hn
          have hn_pos : 0 < n := Nat.zero_lt_of_lt hn₁
          have hny : (n : ℝ) ≤ y := (Nat.le_floor_iff' hn_pos.ne').mp hn₂
          have hnonneg : 0 ≤ y / (n : ℝ) - 1 := by
            rw [sub_nonneg, le_div_iff₀ (Nat.cast_pos.mpr hn_pos), one_mul]
            exact hny
          rw [max_eq_left hnonneg]
        rw [hsum]
        ring
      rw [show weight PChar.one = 1 by simp [weight], one_mul, ← gChi_eq, hGz]
      simp only [An.gChi, PChar.one]
      exact (congrArg Complex.re (ite_eq_left rfl)).trans (Complex.ofReal_re _)
    · refine Finset.sum_congr rfl fun ψ hψ => ?_
      have hne : ψ ≠ PChar.one := Finset.ne_of_mem_erase hψ
      simp only [weight, ite_eq_right hne, gChi_eq]
  have hZ (h : Deduction.ZeroFree F θ) : Λ.ZeroFreeAbove θ := by
    intro ψ hψ s hs
    exact h ⟨ψ, hψ⟩ s hs
  apply hZ
  refine Deduction.zeroFree_of_rpow_window F (δ := la - 1) (C := 1) hθ0 hθ1 (by linarith) fun Y₀ => ?_
  obtain ⟨Y, hY, hx⟩ := hW Y₀
  refine ⟨Y, hY, fun y hy => ?_⟩
  have h1 : (1 : ℝ) + (la - 1) = la := by ring
  rw [h1] at hy
  rw [hG, one_mul]
  exact hx y hy.1 hy.2
end

