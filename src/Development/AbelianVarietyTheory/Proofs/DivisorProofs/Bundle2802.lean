module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1856
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2045
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1687
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1873
public import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2769
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulMemOfMemSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1450
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0086
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1916
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1913
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2767
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1299
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1312
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2124
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1763
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1843
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2785
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1992
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1861
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1221
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2779

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeBasisPeterssonSecond
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option maxHeartbeats 1000000

namespace GlobalTheory.HSShortRoad

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem antitone_of_gapGe {g : ℤ} (hg : 0 ≤ g) {la : AllWt.Weight Dw} (h : GapGe g la) (τ : Psi H) :
    Antitone (la τ) := by
  intro a i hai
  have h0 : ∀ k, 0 ≤ gap (la τ) k := fun k => by
    by_cases hk : k + 1 < Dw.p + Dw.q
    · exact hg.trans (h τ k hk)
    · rw [gap, dite_eq_right hk]
  have e := ofGaps_gap (la τ) a i
  have := Finset.sum_le_sum_of_subset_of_nonneg (f := gap (la τ)) (Finset.range_mono (show (a : ℕ) ≤ i from hai))
    fun k _ _ => h0 k
  rw [ofGaps] at e
  linarith

theorem gapGe_wt {P : WtPar Dw} (h : WtBig P) (j : ℕ) : GapGe (FlagTan.dimFlag Dw + 1) (P.wt j) := by
  have h₁ : GapGe (FlagTan.dimFlag Dw + 3) P.u₁ := h.gaps.mono (by
    push_cast
    exact le_mul_of_one_le_right (by positivity) (by omega))
  intro τ k hk
  have a := h₁ τ k hk
  have b := (P.gap_rem τ k).1
  have c : -2 ≤ gap (FlagTan.kap Dw τ) k := by rw [gap_kap τ hk]; split_ifs <;> omega
  have d : 0 ≤ gap (P.u₁ τ) k := le_trans (by positivity) a
  simp only [WtPar.wt, WtPar.uc, WtPar.u₂, Pi.add_apply, Pi.smul_apply, gap_add, gap_nsmul]
  nlinarith [mul_nonneg (Int.natCast_nonneg j) d, mul_nonneg (Int.natCast_nonneg (FlagTan.dimFlag Dw)) d]

noncomputable abbrev sz (la : AllWt.Weight Dw) : ℝ := ∑ τ, ∑ k, |(la τ k : ℝ)|

theorem one_le_sz {la : AllWt.Weight Dw} (h : 0 < sz la) : 1 ≤ sz la := by
  have e : sz la = ((∑ τ, ∑ k, |la τ k| : ℤ) : ℝ) := by push_cast; rfl
  rw [e] at h ⊢
  exact_mod_cast (show (0 : ℤ) < _ by exact_mod_cast h)

end Weights

theorem log_le_of_le_exp {s y : ℝ} (h0 : 0 ≤ s) (hy : 0 ≤ y) (h : s ≤ Real.exp y) : Real.log s ≤ y := by
  rcases h0.eq_or_lt with rfl | h0
  · simpa using hy
  · exact (Real.log_le_iff_le_exp h0).2 h

theorem log_size_le {a L κ s : ℝ} (ha : 0 < a) (hL : 1 ≤ L) (h₁ : Real.log a ≤ L) (hκ : 1 ≤ κ)
    (h₂ : Real.log κ ≤ 2 * L) (h0 : 0 ≤ s) (h : s ≤ 2 * ((a * L) ^ 2 * κ)) : Real.log s ≤ 10 * L := by
  have hp : 0 < 2 * ((a * L) ^ 2 * κ) := by positivity
  refine log_le_of_le_exp h0 (by linarith) (h.trans ((Real.log_le_iff_le_exp hp).1 ?_))
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_mul ha.ne' (by positivity)]
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < L by linarith)
  push_cast
  linarith

theorem span_of_shortGen {F V κ : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
    {Nm : κ → V → ℝ} {M : Submodule (𝓞 F) V} {n : ℕ} {w : Fin n → V} {Λ : ℝ} (h : CompHt.IsShortGen Nm M w Λ)
    (hM : Submodule.span F (M : Set V) = ⊤) : (∀ i, w i ∈ M) ∧ Submodule.span F (Set.range w) = ⊤ :=
  ⟨fun i => (h.gen _).2 (Submodule.subset_span ⟨i, rfl⟩), top_le_iff.1 (hM.ge.trans (Submodule.span_le.2 fun x hx =>
    Submodule.span_subset_span ℤ F _ ((h.gen x).1 hx)))⟩

theorem sum_univ_inst {α : Type} {i1 i2 : Fintype α} (f : α → ℝ) :
    @Finset.sum α ℝ _ (@Finset.univ α i1) f = @Finset.sum α ℝ _ (@Finset.univ α i2) f := by
  obtain rfl : i1 = i2 := Subsingleton.elim _ _
  rfl

theorem bound_le {C Z PP κ : ℝ} (hC : 0 ≤ C) (hZ : 1 ≤ Z) (hCZ : 6 * C ≤ Z) (hP : Z ^ 12 ≤ PP) (hκ : 1 ≤ κ) :
    C * (Z ^ 3 * (Z ^ 2 * κ) + Z ^ 5) ≤ PP * κ := by
  have h5 : 0 ≤ Z ^ 5 := by positivity
  have e : C * (Z ^ 3 * (Z ^ 2 * κ) + Z ^ 5) = C * Z ^ 5 * (κ + 1) := by ring
  have a1 : C * Z ^ 5 * (κ + 1) ≤ C * Z ^ 5 * (2 * κ) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have a2 : 2 * C * Z ^ 5 ≤ Z * Z ^ 5 := mul_le_mul_of_nonneg_right (by linarith) h5
  have a3 : Z * Z ^ 5 ≤ Z ^ 12 := by
    rw [← pow_succ']
    exact pow_le_pow_right₀ hZ (by norm_num)
  have a4 : 2 * C * Z ^ 5 ≤ PP := a2.trans (a3.trans hP)
  rw [e]
  calc C * Z ^ 5 * (κ + 1) ≤ C * Z ^ 5 * (2 * κ) := a1
    _ = (2 * C * Z ^ 5) * κ := by ring
    _ ≤ PP * κ := mul_le_mul_of_nonneg_right a4 (by linarith)

end GlobalTheory.HSShortRoad
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCmConstantAddLogDerivativeLeSquareTopBound
section
open GlobalTheory.SqTop GlobalTheory.FunObj.SqNum GlobalTheory.CMVal

noncomputable section

namespace GlobalTheory.SizesArch

open Formalism.BasicNotions NumberField

theorem log_gamma_nat_le (n : ℕ) (hn : 1 ≤ n) : Real.log (Real.Gamma n) ≤ n * Real.log n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hg : Real.Gamma ((m + 1 : ℕ) : ℝ) = (m.factorial : ℝ) := by
    rw [Nat.cast_succ, Real.Gamma_nat_eq_factorial]
  have hf : (m.factorial : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ (m + 1) := by
    have h1 : m.factorial ≤ (m + 1) ^ (m + 1) :=
      (Nat.factorial_le_pow m).trans ((Nat.pow_le_pow_left (Nat.le_succ m) m).trans
        (Nat.pow_le_pow_right (Nat.succ_pos m) (Nat.le_succ m)))
    exact_mod_cast h1
  rw [hg, ← Real.log_pow]
  exact Real.log_le_log (by exact_mod_cast Nat.factorial_pos m) hf

theorem log_cmConst_le {Φ : Type} [Fintype Φ] (dF d : ℝ) (k : ℕ) (κ : Φ → ℕ) (hdF : 0 < dF) (hd : 1 ≤ d)
    (hk : 1 ≤ k) :
    Real.log (Formalism.PairingDivisionLocalBalance.cmConst dF d k κ) ≤ (((k : ℝ) - 1) / 2) * Real.log dF +
      ∑ τ, Real.log (Real.Gamma ((k : ℝ) + κ τ)) + (Formalism.PairingDivisionLocalBalance.absK κ : ℝ) * 8 := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hG : ∀ τ, 0 < Real.Gamma ((k : ℝ) + κ τ) := fun τ =>
    Real.Gamma_pos_of_pos (by have : (0 : ℝ) ≤ κ τ := Nat.cast_nonneg _; linarith)
  have hsd : 1 ≤ Real.sqrt d := by rw [Real.one_le_sqrt]; exact hd
  have hq : 0 < 2 * Real.pi / Real.sqrt d := div_pos (by positivity) (by linarith)
  unfold Formalism.PairingDivisionLocalBalance.cmConst
  rw [Real.log_mul (mul_ne_zero (Real.rpow_pos_of_pos hdF _).ne' (Finset.prod_ne_zero_iff.2 fun τ _ => (hG τ).ne'))
      (pow_ne_zero _ hq.ne'),
    Real.log_mul (Real.rpow_pos_of_pos hdF _).ne' (Finset.prod_ne_zero_iff.2 fun τ _ => (hG τ).ne'),
    Real.log_rpow hdF, Real.log_prod (fun τ _ => (hG τ).ne'), Real.log_pow]
  have h1 : Real.log (2 * Real.pi / Real.sqrt d) ≤ 8 := by
    have h3 := Real.log_le_sub_one_of_pos hq
    have h2 : 2 * Real.pi / Real.sqrt d ≤ 2 * Real.pi := div_le_self (by positivity) hsd
    linarith [Real.pi_le_four]
  have h0 : (0 : ℝ) ≤ Formalism.PairingDivisionLocalBalance.absK κ := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left h1 h0
  linarith

end GlobalTheory.SizesArch

namespace GlobalTheory.SizesArch

open Formalism.BasicNotions NumberField GlobalTheory.ChiGrid

theorem sizes : ∀ ε : ℝ, ∃ Cx x₁ : ℝ, ∀ (D : Formalism.BasicNotions.D7) (large₂ : Formalism.BasicNotions.SizeData₂ D), large₂.sc.eps = ε → x₁ ≤ large₂.sc.x →
    Rec large₂ → ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j →
      Real.log (C0 D.host.E D.host.d (2 * s) (kap D 1 i j s)) +
        (Formalism.PairingDivisionLocalBalance.wtM (2 * s) (kap D 1 i j s) : ℝ) * ((Real.log D.host.d + |large₂.logDerivativeAtOne|) / 2) ≤
        bTH D Cx large₂.sc.x large₂.sc.b := by
  intro ε
  refine ⟨200, 0, fun D large₂ _ _ hR i j s hs1 hs2 => ?_⟩
  obtain ⟨-, -, hm4, hm, -, hmfNd, -, -, -, hrd1, hrd2, -, -, -⟩ := hR.size
  obtain ⟨hgb, hb675⟩ := GlobalTheory.BigTop.Fun.gap_le_b hR.size
  have hbL : Real.log large₂.sc.b = large₂.sc.L := by unfold Scale.b; exact Real.log_exp _
  have hL1 : 1 ≤ large₂.sc.L := by
    rw [← hbL, Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hx1 : 1 < large₂.sc.x := large₂.sc.one_lt_alt
  have hlogx : 0 ≤ Real.log large₂.sc.x := Real.log_nonneg hx1.le
  have hcard : Fintype.card D.what₂.Tau = D.R.f := Formalism.MainNotions.Lnk.card_Tau D
  have hf1n : 1 ≤ D.R.f := by
    have : 1 ≤ D.R.m ^ 4 := Nat.one_le_pow _ _ (by omega)
    omega
  have hf1 : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf1n

  have hsb : (s : ℝ) ≤ large₂.sc.b := by
    have h1 := GlobalTheory.BigTop.Fun.rankV_lt_gap (D := D) i.2 j.2
    have e := (ranks_exact D i j).2.2
    have h3 : rankV D i j ≤ rankV D (i + 1) (j + 1) := by unfold rankV; gcongr <;> omega
    have : s ≤ gap D 1 := by omega
    exact (by exact_mod_cast this : (s : ℝ) ≤ gap D 1).trans hgb

  have hκ : ∀ τ, (kap D 1 i j s τ : ℝ) ≤ 5 * large₂.sc.b := by
    intro τ
    obtain ⟨e0, e1⟩ := GlobalTheory.BigTop.Fun.numE_bounds hR.size τ j.2
    obtain ⟨c0, c1⟩ := GlobalTheory.BigTop.Fun.cen_bounds hR.size τ (i := D.R.m - i) (by omega) (by omega)
    have h : (kap D 1 i j s τ : ℤ) ≤ (num D 1 τ).e (j + 1) + cen D 1 τ (D.R.m - i) := by
      unfold kap; omega
    have h' : ((kap D 1 i j s τ : ℤ) : ℝ) ≤ ((num D 1 τ).e (j + 1) : ℝ) + (cen D 1 τ (D.R.m - i) : ℝ) := by
      exact_mod_cast h
    push_cast at h'
    linarith

  have hN1 : 1 ≤ D.R.N D.R.m := by unfold Ranks.N; have := D.R.m_add_three_le_k; omega
  have hd1 : (1 : ℝ) ≤ D.host.d := by exact_mod_cast D.host.hyp.2.1.one_lt.le
  have hdb : (D.host.d : ℝ) ≤ large₂.sc.b := by
    have hm1 : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (show 1 ≤ D.R.m by omega)
    have hN : (1 : ℝ) ≤ (D.R.N D.R.m : ℝ) := by exact_mod_cast hN1
    have h1 : (1 : ℝ) ≤ (D.R.m : ℝ) * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hm1 hf1) (one_le_pow₀ hN)
    exact (le_mul_of_one_le_left (by linarith) h1).trans hmfNd
  have hlogd : Real.log D.host.d ≤ large₂.sc.L := hbL ▸ Real.log_le_log (by linarith) hdb
  have hlogd0 : 0 ≤ Real.log D.host.d := Real.log_nonneg hd1
  have hdl : |large₂.logDerivativeAtOne| ≤ large₂.sc.L := hR.dlog

  have hdF : |(discr (maximalRealSubfield D.host.E) : ℝ)| = (2 * D.host.v) ^ D.R.f := by
    rw [← hR.hF]; exact GlobalTheory.CovDom.NormConst.abs_discr_F D
  have h2v : 2 * D.host.v = D.host.rdE := by show 2 * (D.host.rdE / 2) = D.host.rdE; ring
  have hdF0 : 0 < |(discr (maximalRealSubfield D.host.E) : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero _)
  have hlogdF : Real.log |(discr (maximalRealSubfield D.host.E) : ℝ)| ≤ (D.R.f : ℝ) * large₂.sc.L := by
    rw [hdF, Real.log_pow, h2v]
    have : Real.log D.host.rdE ≤ large₂.sc.L := by linarith
    exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)

  have hC := log_cmConst_le |(discr (maximalRealSubfield D.host.E) : ℝ)| (D.host.d : ℝ) (2 * s) (kap D 1 i j s) hdF0 hd1
    (by omega)
  have hC0 : C0 D.host.E D.host.d (2 * s) (kap D 1 i j s) =
      Formalism.PairingDivisionLocalBalance.cmConst |(discr (maximalRealSubfield D.host.E) : ℝ)| (D.host.d : ℝ) (2 * s) (kap D 1 i j s) := rfl
  rw [hC0]
  set b := large₂.sc.b
  set L := large₂.sc.L
  set F : ℝ := (D.R.f : ℝ) with hF
  have hb0 : 0 ≤ b := by linarith
  have hk : ((2 * s : ℕ) : ℝ) ≤ 2 * b := by push_cast; linarith
  have hk1 : (1 : ℝ) ≤ ((2 * s : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ 2 * s by omega)

  have T1 : (((2 * s : ℕ) : ℝ) - 1) / 2 * Real.log |(discr (maximalRealSubfield D.host.E) : ℝ)| ≤ 2 * (F * b * L) := by
    have a1 : 0 ≤ (((2 * s : ℕ) : ℝ) - 1) / 2 := by linarith
    have a2 := mul_le_mul_of_nonneg_left hlogdF a1
    have a3 : (((2 * s : ℕ) : ℝ) - 1) / 2 ≤ b := by linarith
    have a4 : 0 ≤ F * L := by positivity
    have a5 := mul_le_mul_of_nonneg_right a3 a4
    nlinarith

  have T2 : ∑ τ, Real.log (Real.Gamma (((2 * s : ℕ) : ℝ) + kap D 1 i j s τ)) ≤ 49 * (F * b * L) := by
    have each : ∀ τ, Real.log (Real.Gamma (((2 * s : ℕ) : ℝ) + kap D 1 i j s τ)) ≤ 49 * (b * L) := by
      intro τ
      have e : ((2 * s : ℕ) : ℝ) + kap D 1 i j s τ = ((2 * s + kap D 1 i j s τ : ℕ) : ℝ) := by push_cast; ring
      rw [e]
      have hn1 : 1 ≤ 2 * s + kap D 1 i j s τ := by omega
      refine (log_gamma_nat_le _ hn1).trans ?_
      have hn : ((2 * s + kap D 1 i j s τ : ℕ) : ℝ) ≤ 7 * b := by push_cast; linarith [hκ τ]
      have hn0 : (1 : ℝ) ≤ ((2 * s + kap D 1 i j s τ : ℕ) : ℝ) := by exact_mod_cast hn1
      have hl0 : 0 ≤ Real.log ((2 * s + kap D 1 i j s τ : ℕ) : ℝ) := Real.log_nonneg hn0
      have hl : Real.log ((2 * s + kap D 1 i j s τ : ℕ) : ℝ) ≤ 7 * L := by
        have l1 := Real.log_le_log (by linarith) hn
        rw [Real.log_mul (by norm_num) (by linarith), hbL] at l1
        have l2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 7 by norm_num)
        linarith
      have := mul_le_mul hn hl hl0 (by linarith)
      linarith
    refine (Finset.sum_le_sum fun τ _ => each τ).trans ?_
    rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    linarith

  have hsumκ : (Formalism.PairingDivisionLocalBalance.absK (kap D 1 i j s) : ℝ) ≤ 5 * (F * b) := by
    unfold Formalism.PairingDivisionLocalBalance.absK
    push_cast
    refine (Finset.sum_le_sum fun τ _ => hκ τ).trans ?_
    rw [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
    linarith
  have hsumκ0 : (0 : ℝ) ≤ Formalism.PairingDivisionLocalBalance.absK (kap D 1 i j s) := Nat.cast_nonneg _
  have T3 : (Formalism.PairingDivisionLocalBalance.absK (kap D 1 i j s) : ℝ) * 8 ≤ 40 * (F * b * L) := by
    have : F * b ≤ F * b * L := le_mul_of_one_le_right (by positivity) hL1
    linarith

  have hM : (Formalism.PairingDivisionLocalBalance.wtM (2 * s) (kap D 1 i j s) : ℝ) ≤ 12 * (F * b) := by
    unfold Formalism.PairingDivisionLocalBalance.wtM
    push_cast
    rw [hcard]
    have : (2 * (s : ℝ)) * F ≤ 2 * b * F := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    push_cast at hsumκ
    linarith
  have T4 : (Formalism.PairingDivisionLocalBalance.wtM (2 * s) (kap D 1 i j s) : ℝ) * ((Real.log D.host.d + |large₂.logDerivativeAtOne|) / 2) ≤ 12 * (F * b * L) := by
    have a1 : (Real.log D.host.d + |large₂.logDerivativeAtOne|) / 2 ≤ L := by linarith
    have a2 : 0 ≤ (Real.log D.host.d + |large₂.logDerivativeAtOne|) / 2 := by positivity
    have := mul_le_mul hM a1 a2 (by positivity)
    linarith
  have hfin : 0 ≤ F * b * Real.log large₂.sc.x := by positivity
  unfold bTH
  rw [hbL]
  have e : 200 * (D.R.f : ℝ) * b * (L + Real.log large₂.sc.x) = 200 * (F * b * L) + 200 * (F * b * Real.log large₂.sc.x) := by
    rw [hF]; ring
  rw [e]
  have hP : 0 ≤ F * b * L := by positivity
  linarith

end GlobalTheory.SizesArch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFinrankCuspFormsLe
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovTop.DimLogTop

theorem log_size_le (f r L kap S : ℝ) (hf : 1 ≤ f) (hr : 1 ≤ r) (hL : 1 ≤ L) (hk0 : 0 ≤ kap)
    (hk : Real.log kap ≤ 2 * L) (hfr : Real.log (f * r) ≤ L) (hS0 : 0 ≤ S)
    (hS : S ≤ (f * r * L) ^ 2 * kap + 6 * f * r ^ 2) : Real.log S ≤ 20 * L := by
  rcases hS0.eq_or_lt with h | h
  · rw [← h, Real.log_zero]; linarith
  have hfr0 : 0 < f * r := by positivity
  have e1 : f * r ≤ Real.exp L := (Real.log_le_iff_le_exp hfr0).1 hfr
  have e2 : L ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have e3 : kap ≤ Real.exp (2 * L) := by
    rcases hk0.eq_or_lt with h0 | h0
    · rw [← h0]; exact (Real.exp_pos _).le
    · exact (Real.log_le_iff_le_exp h0).1 hk
  have e4 : (7 : ℝ) ≤ Real.exp (6 * L) := by linarith [Real.add_one_le_exp (6 * L)]
  have hE : Real.exp (6 * L) = Real.exp L ^ 2 * Real.exp L ^ 2 * Real.exp (2 * L) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; push_cast; ring
  have hE2 : Real.exp L ^ 2 ≤ Real.exp (6 * L) := by
    rw [← Real.exp_nat_mul]; exact Real.exp_le_exp.2 (by push_cast; linarith)
  have a1 : (f * r * L) ^ 2 * kap ≤ Real.exp (6 * L) := by
    rw [hE, mul_pow]
    have : (f * r) ^ 2 ≤ Real.exp L ^ 2 := pow_le_pow_left₀ hfr0.le e1 2
    have : L ^ 2 ≤ Real.exp L ^ 2 := pow_le_pow_left₀ (by linarith) e2 2
    gcongr
  have a2 : 6 * f * r ^ 2 ≤ 6 * Real.exp (6 * L) := by
    have : f * r ^ 2 ≤ (f * r) ^ 2 := by nlinarith
    have : (f * r) ^ 2 ≤ Real.exp L ^ 2 := pow_le_pow_left₀ hfr0.le e1 2
    nlinarith
  have a3 : S ≤ Real.exp (12 * L) := by
    have : Real.exp (12 * L) = Real.exp (6 * L) * Real.exp (6 * L) := by rw [← Real.exp_add]; ring_nf
    rw [this]
    have := Real.exp_pos (6 * L)
    nlinarith
  have := (Real.log_le_iff_le_exp h).2 a3
  linarith

theorem cube_le (Cb L Zb : ℝ) (hL : Cb ≤ L) (hL1 : 1 ≤ L) (hZ : L ≤ Zb) : Cb * Zb ^ 3 ≤ Zb ^ 12 := by
  have h1 : 1 ≤ Zb := hL1.trans hZ
  have h9 : Zb ≤ Zb ^ 9 := le_self_pow₀ h1 (by norm_num)
  have h3 : 0 ≤ Zb ^ 3 := by positivity
  calc Cb * Zb ^ 3 ≤ Zb ^ 9 * Zb ^ 3 := mul_le_mul_of_nonneg_right (by linarith) h3
    _ = Zb ^ 12 := by ring

theorem rkK_eq_finrank_of_span_top {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] (L : Submodule (𝓞 K) V) (h : Submodule.span K (L : Set V) = ⊤) :
    Formalism.HN.rkK L = Module.finrank K V := by
  unfold Formalism.HN.rkK
  rw [h, finrank_top]

end GlobalTheory.CovTop.DimLogTop

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeFubiniStudyBoxFamily
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef

theorem fs_box_rank_le : GlobalTheory.Published.ArCalc → AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0})
    [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (J : Type) [Fintype J]
    (e : J → X.functionField) (x : Fin D → X.functionField) (w : J × Finset (Fin D) → ℝ),
    LinearIndependent ℤ e → AlgebraicIndependent ℤ x → (∀ c, 0 ≤ w c) →
    IsFS M (boxFam e x) w → (D.factorial : ℝ) * Fintype.card J ≤ gdeg M D := by
  intro hAr hHS k _ X _ p D hD M J _ e x w he hx hw hFS
  have hNef : M.IsNef D := _root_.GlobalTheory.HSNef.FSNef.isNef_of_isFS hAr k X p D hD M _ (boxFam e x) w hFS hw
  obtain ⟨P, hPL, hmem⟩ := _root_.GlobalTheory.HSNef.isFS_mem_pair k X p M _ (boxFam e x) w hFS
  subst hPL
  exact _root_.GlobalTheory.HSNef.RankNef.rank_le_gdeg_of_isNef hAr hHS k X p D hD P hNef J e x he hx hmem

end GlobalTheory.HSNef
end

