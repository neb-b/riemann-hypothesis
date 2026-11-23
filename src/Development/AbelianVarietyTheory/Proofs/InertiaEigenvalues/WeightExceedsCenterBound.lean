module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NodeYPredEqChainVertexAtRowZeroLast

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

open GlobalTheory.SignedHC

theorem e_add_v_two_pos {R : Ranks} (P : HCParam R) (s ga : ℕ) (c : ℕ → ℤ) (j : Fin R.m) :
    0 < P.e j + ((GridData.ofHCParam P s ga c).v 2 : ℚ) := by
  obtain ⟨hv, hb, -⟩ := GridData.ofHCParam_spec P s ga c
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  have h1 : (GridData.ofHCParam P s ga c).v (R.k - 2 + 2) < (GridData.ofHCParam P s ga c).v 2 :=
    (GridData.ofHCParam P s ga c).v_anti 2 _ le_rfl (by omega) (show R.k - 2 + 2 ≤ R.k by omega)
  have h2 : (GridData.ofHCParam P s ga c).b (0 + 1) ≤ (GridData.ofHCParam P s ga c).b (j.1 + 1) := by
    rcases Nat.eq_zero_or_pos j.1 with h | h
    · rw [h]
    · exact ((GridData.ofHCParam P s ga c).b_mono _ _ le_rfl (by omega) (show j.1 + 1 ≤ R.m from j.2)).le
  have h1' : P.v ⟨R.k - 2, by omega⟩ < ((GridData.ofHCParam P s ga c).v 2 : ℚ) := by
    rw [hv]; exact_mod_cast h1
  have h2' : P.b ⟨0, by omega⟩ ≤ P.b j := by
    rw [hb, hb]; exact_mod_cast h2
  have h3 := P.v_gt_u ⟨R.k - 2, by omega⟩
  have h4 := P.u_last_gt (by omega) (by omega)
  have h5 : P.u ⟨R.k - 2 + 1, by omega⟩ = P.u ⟨R.k - 1, by omega⟩ := by
    congr 2; omega
  have h6 := P.gap_be j
  have h7 : (0 : ℚ) ≤ R.t := by positivity
  simp only at h3
  linarith

theorem nFun_eq_bigN (D : D7) : BlochKatoReduction.Gen.NFun D.R = GlobalTheory.Grid.bigN D := by
  have hk := D.R.m_add_three_le_k
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have h : Odd (D.R.r + 6) := by
    rw [Nat.odd_iff]; unfold Ranks.r; omega
  simp only [BlochKatoReduction.Gen.NFun, BlochKatoReduction.Gen.sFun, if_pos h, GlobalTheory.Grid.bigN, GlobalTheory.Grid.sLen]

end GlobalTheory.LamTie
