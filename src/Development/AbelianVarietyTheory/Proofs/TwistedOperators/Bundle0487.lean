module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0474
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierInversionZeroCompactQuotientSummable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AeZeroOfSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0029
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
public import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.StatementOfTied
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0467
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0472
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairwiseFlatMapBand
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries

namespace GlobalTheory.RowReal

theorem block_bounds {x y : ℚ} {n : ℕ} (h : y ∈ GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block x n) :
    x - ((n : ℚ) - 1) / 2 ≤ y ∧ y ≤ x + ((n : ℚ) - 1) / 2 := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h
  have hi' : (i : ℚ) + 1 ≤ n := by exact_mod_cast (List.mem_range.1 hi)
  have h0 : (0 : ℚ) ≤ i := by positivity
  constructor <;> linarith

theorem block_pairwise (x : ℚ) (n : ℕ) : (GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block x n).Pairwise (· > ·) := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block
  rw [List.pairwise_map]
  refine List.pairwise_lt_range.imp fun {i j} h => ?_
  have : (i : ℚ) < j := by exact_mod_cast h
  show _ < _
  linarith

theorem pairwise_flatMap_band {n : ℕ} (f : Fin n → List ℚ) (lo hi : Fin n → ℚ)
    (hp : ∀ i, (f i).Pairwise (· > ·)) (hb : ∀ i, ∀ x ∈ f i, lo i ≤ x ∧ x ≤ hi i)
    (hs : ∀ i j : Fin n, i < j → hi j < lo i) : ((List.finRange n).flatMap f).Pairwise (· > ·) := by
  rw [List.pairwise_flatMap]
  refine ⟨fun i _ => hp i, (List.pairwise_lt_finRange n).imp fun {i j} hij x hx y hy => ?_⟩
  linarith [(hb i x hx).1, (hb j y hy).2, hs i j hij]

theorem rowEntries_good (D : D7) (C : ℝ) (τ : D.what₂.Tau) : (rowEntries D C τ).Good := by
  set G := num D C τ with hG
  set P := rowEntries D C τ with hPdef
  have hGm : G.m = D.R.m := rfl
  have hGk : G.k = D.R.k := rfl
  have hGs : G.s = sLen D := rfl
  have hGt : G.t = D.R.t := rfl
  have hGg : G.ga = gap D C := rfl
  have hSm : (rowSizes D).m = D.R.m := rfl
  have hSk : (rowSizes D).k = D.R.k := rfl
  have hSs : (rowSizes D).s = sLen D := rfl
  have hSt : (rowSizes D).t = D.R.t := rfl
  have hPa : ∀ l, P.a l = G.a l := fun _ => rfl
  have hPc : ∀ i, P.c i = G.cen (i + 1) := fun _ => rfl
  have hPv : ∀ i, P.v i = G.v (i + 2) := fun _ => rfl
  have hPu : ∀ i, P.u i = G.vHalf (i + 2) := fun _ => rfl
  have hPb : ∀ j, P.b j = G.b (j + 1) := fun _ => rfl
  have hPe : ∀ j, P.e j = G.e (j + 1) := fun _ => rfl
  have hm2 := D.R.two_le_m
  have hk3 := D.R.m_add_three_le_k
  have hgap : sLen D + 2 < gap D C := by have := (isLeast_gap D C).1.2.1; omega
  have hgQ : (sLen D : ℚ) + 2 < G.ga := by rw [hGg]; exact_mod_cast hgap
  have ht1 : (1 : ℚ) ≤ D.R.t := by exact_mod_cast D.R.t_odd.pos
  have hle : ∀ {i j : ℕ}, i ≤ j → G.a j ≤ G.a i := fun h => by
    rcases h.eq_or_lt with rfl | h
    · exact le_rfl
    · linarith [a_add_le (G := G) h]
  have hcen : ∀ i : ℕ, 1 ≤ i → i ≤ D.R.m → |(G.cen i : ℚ) - (G.a i + G.ga / 2)| ≤ 1 := fun i h1 h2 => by
    rw [← G.mid_eq h1]; exact num_nearMid D C τ i (Finset.mem_Icc.2 ⟨h1, h2⟩)
  have hC : ∀ i : ℕ, 1 ≤ i → i ≤ D.R.m → ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (G.cen i : ℚ) (sLen D),
      G.a i + G.ga / 2 - ((sLen D : ℚ) + 1) / 2 ≤ x ∧ x ≤ G.a i + G.ga / 2 + ((sLen D : ℚ) + 1) / 2 := by
    intro i h1 h2 x hx
    have e1 := block_bounds hx
    have e2 := abs_le.1 (hcen i h1 h2)
    constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]
  have hspec := GlobalTheory.SignedHC.GridData.ofHCParam_spec (D.hc τ) (sLen D) (gap D C) (cen D C τ)
  have hbe : ∀ j (h : j < D.R.m), ((D.R.t : ℚ) + 3) / 2 ≤ G.e (j + 1) - G.b (j + 1) := fun j h => by
    have := (D.hc τ).gap_be ⟨j, h⟩
    rw [hspec.2.1 ⟨j, h⟩, hspec.2.2 ⟨j, h⟩] at this
    exact this
  have heb : ∀ j (h : j + 1 < D.R.m), ((D.R.t : ℚ) + 3) / 2 ≤ G.b (j + 2) - G.e (j + 1) := fun j h => by
    have := (D.hc τ).gap_eb ⟨j, by omega⟩ h
    rw [hspec.2.1 ⟨j + 1, h⟩, hspec.2.2 ⟨j, by omega⟩] at this
    exact this
  have hvle : ∀ i j, 2 ≤ i → i ≤ j → j ≤ D.R.k → G.v j ≤ G.v i := fun i j h1 h2 h3 => by
    rcases h2.eq_or_lt with rfl | h
    · exact le_rfl
    · exact (G.v_anti i j h1 h h3).le
  have hble : ∀ i j, 1 ≤ i → i ≤ j → j ≤ D.R.m → G.b i ≤ G.b j := fun i j h1 h2 h3 => by
    rcases h2.eq_or_lt with rfl | h
    · exact le_rfl
    · exact (G.b_mono i j h1 h h3).le
  have hvk : (-(G.b 1 : ℚ)) < G.v D.R.k - 1 / 2 := by
    have h1 := (D.hc τ).v_gt_u ⟨D.R.k - 2, by omega⟩
    have h2 := (D.hc τ).u_last_gt (by omega) (by omega)
    have h3 : -(D.hc τ).b ⟨0, by omega⟩ < (D.hc τ).v ⟨D.R.k - 2, by omega⟩ := by
      refine h2.trans (lt_of_eq_of_lt ?_ h1)
      congr 1
      ext
      simp only
      omega
    rw [hspec.2.1 ⟨0, by omega⟩, hspec.1 ⟨D.R.k - 2, by omega⟩] at h3
    have h4 : -(G.b 1) < G.v D.R.k := by
      rw [show D.R.k - 2 + 2 = D.R.k by omega] at h3
      exact_mod_cast h3
    have h5 : ((-(G.b 1) + 1 : ℤ) : ℚ) ≤ G.v D.R.k := by exact_mod_cast h4
    push_cast at h5
    linarith
  refine ⟨fun l => ⟨G.v 2 + ((G.m : ℤ) + 1 - ((l : ℕ) : ℤ)) * G.ga, ?_⟩, fun i => ⟨G.v (i + 2) - 1, ?_⟩, ?_⟩
  · rw [hPa]; unfold GlobalTheory.SignedHC.GridData.a; push_cast; ring
  · rw [hPu]; unfold GlobalTheory.SignedHC.GridData.vHalf; push_cast; ring

  have bX : ∀ (i : Fin (rowSizes D).m), ∀ x ∈ GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (P.c i) (rowSizes D).s ++ [P.a i.succ],
      G.a (i + 1) ≤ x ∧ x ≤ G.a (i + 1) + G.ga / 2 + ((sLen D : ℚ) + 1) / 2 := by
    intro i x hx
    have hi := i.2
    rw [List.mem_append, List.mem_singleton, hPc, hPa, hSs, Fin.val_succ] at hx
    rcases hx with hx | rfl
    · have := hC (i + 1) (by omega) (by omega) x hx
      constructor <;> linarith [this.1, this.2]
    · constructor
      · exact le_rfl
      · have : (0 : ℚ) ≤ G.ga := by positivity
        linarith
  have pX : (P.a 0 :: (List.finRange (rowSizes D).m).flatMap fun i =>
      GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (P.c i) (rowSizes D).s ++ [P.a i.succ]).Pairwise (· > ·) := by
    rw [List.pairwise_cons]
    constructor
    · intro x hx
      obtain ⟨i, -, hx⟩ := List.mem_flatMap.1 hx
      have h1 := (bX i x hx).2
      have h2 := a_add_le (G := G) (show 0 < (i : ℕ) + 1 by omega)
      rw [hPa]
      show x < G.a 0
      linarith
    · refine pairwise_flatMap_band _ (fun i => G.a (i + 1)) (fun i => G.a (i + 1) + G.ga / 2 + ((sLen D : ℚ) + 1) / 2)
        (fun i => ?_) bX (fun i j hij => ?_)
      · rw [List.pairwise_append]
        refine ⟨block_pairwise _ _, List.pairwise_singleton _ _, fun x hx y hy => ?_⟩
        rw [List.mem_singleton] at hy
        subst hy
        rw [hPc, hSs] at hx
        have := hC (i + 1) (by omega) (by omega) x hx
        rw [hPa, Fin.val_succ]
        show _ < _
        linarith [this.1]
      · have h := a_add_le (G := G) (show (i : ℕ) + 1 < j + 1 by have : (i : ℕ) < j := hij; omega)
        show _ < _
        linarith
  have tX : ∀ x ∈ (P.a 0 :: (List.finRange (rowSizes D).m).flatMap fun i =>
      GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (P.c i) (rowSizes D).s ++ [P.a i.succ]), G.a G.m ≤ x := by
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · rw [hPa]; exact hle (by simp)
    · obtain ⟨i, -, hx⟩ := List.mem_flatMap.1 hx
      have := i.2
      exact (hle (show (i : ℕ) + 1 ≤ G.m by rw [hGm]; omega)).trans (bX i x hx).1

  have bY : ∀ (i : Fin ((rowSizes D).k - 1)), ∀ y ∈ [(P.v i : ℚ), P.u i],
      (G.v (i + 2) : ℚ) - 1 / 2 ≤ y ∧ y ≤ G.v (i + 2) := by
    intro i y hy
    rw [hPv, hPu] at hy
    unfold GlobalTheory.SignedHC.GridData.vHalf at hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl <;> constructor <;> linarith
  have pY : ((List.finRange ((rowSizes D).k - 1)).flatMap fun i => [(P.v i : ℚ), P.u i]).Pairwise (· > ·) := by
    refine pairwise_flatMap_band _ (fun i => (G.v (i + 2) : ℚ) - 1 / 2) (fun i => (G.v (i + 2) : ℚ)) (fun i => ?_) bY
      (fun i j hij => ?_)
    · refine List.Pairwise.cons (fun y hy => ?_) (List.pairwise_singleton _ _)
      rw [List.mem_singleton] at hy
      subst hy
      rw [hPv, hPu]
      unfold GlobalTheory.SignedHC.GridData.vHalf
      show _ < _
      linarith
    · have hj : (j : ℕ) < D.R.k - 1 := j.2
      have hij' : (i : ℕ) < j := hij
      have h := G.v_anti (i + 2) (j + 2) (by omega) (by omega) (by rw [hGk]; omega)
      have h' : ((G.v (j + 2) + 1 : ℤ) : ℚ) ≤ G.v (i + 2) := by exact_mod_cast h
      push_cast at h'
      show _ < _
      linarith
  have tY : ∀ y ∈ ((List.finRange ((rowSizes D).k - 1)).flatMap fun i => [(P.v i : ℚ), P.u i]),
      (G.v D.R.k : ℚ) - 1 / 2 ≤ y ∧ y ≤ G.v 2 := by
    intro y hy
    obtain ⟨i, -, hy⟩ := List.mem_flatMap.1 hy
    have hi : (i : ℕ) < D.R.k - 1 := i.2
    have h1 : ((G.v D.R.k : ℤ) : ℚ) ≤ G.v (i + 2) := by exact_mod_cast hvle (i + 2) D.R.k (by omega) (by omega) le_rfl
    have h2 : ((G.v (i + 2) : ℤ) : ℚ) ≤ G.v 2 := by exact_mod_cast hvle 2 (i + 2) le_rfl (by omega) (by omega)
    have := bY i y hy
    constructor <;> linarith [this.1, this.2]

  have bZ : ∀ (j : Fin (rowSizes D).m), ∀ z ∈ ((-P.b j : ℚ) :: GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (-P.e j) (rowSizes D).t),
      -(G.e (j + 1) : ℚ) - ((D.R.t : ℚ) - 1) / 2 ≤ z ∧ z ≤ -(G.b (j + 1) : ℚ) := by
    intro j z hz
    have hj : (j : ℕ) < D.R.m := j.2
    have h1 := hbe j hj
    rw [List.mem_cons, hPb, hPe, hSt] at hz
    rcases hz with rfl | hz
    · constructor <;> linarith
    · have := block_bounds hz
      constructor <;> linarith [this.1, this.2]
  have pZ : ((List.finRange (rowSizes D).m).flatMap fun j =>
      (-P.b j : ℚ) :: GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (-P.e j) (rowSizes D).t).Pairwise (· > ·) := by
    refine pairwise_flatMap_band _ (fun j => -(G.e (j + 1) : ℚ) - ((D.R.t : ℚ) - 1) / 2) (fun j => -(G.b (j + 1) : ℚ))
      (fun j => ?_) bZ (fun i j hij => ?_)
    · have hj : (j : ℕ) < D.R.m := j.2
      have h1 := hbe j hj
      rw [List.pairwise_cons]
      refine ⟨fun z hz => ?_, block_pairwise _ _⟩
      rw [hPb, hPe, hSt] at *
      have := block_bounds hz
      show _ < _
      linarith [this.2]
    · have hj : (j : ℕ) < D.R.m := j.2
      have hij' : (i : ℕ) < j := hij
      have h1 := heb i (by omega)
      have h2 : ((G.b (i + 2) : ℤ) : ℚ) ≤ G.b (j + 1) := by exact_mod_cast hble (i + 2) (j + 1) (by omega) (by omega) (by omega)
      show _ < _
      linarith
  have tZ : ∀ z ∈ ((List.finRange (rowSizes D).m).flatMap fun j =>
      (-P.b j : ℚ) :: GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.block (-P.e j) (rowSizes D).t), z ≤ -(G.b 1 : ℚ) := by
    intro z hz
    obtain ⟨j, -, hz⟩ := List.mem_flatMap.1 hz
    have hj : (j : ℕ) < D.R.m := j.2
    have h1 : ((G.b 1 : ℤ) : ℚ) ≤ G.b (j + 1) := by exact_mod_cast hble 1 (j + 1) le_rfl (by omega) (by omega)
    linarith [(bZ j z hz).2]

  have hv2 : (G.v 2 : ℚ) < G.a G.m := by
    rw [G.a_m]
    have : (0 : ℚ) ≤ G.ga := by positivity
    linarith
  show (Entries.orderList P).Pairwise (· > ·)
  rw [Entries.orderList, List.pairwise_append, List.pairwise_append]
  refine ⟨⟨pX, pY, fun x hx y hy => ?_⟩, pZ, fun x hx z hz => ?_⟩
  · have h1 := tX x hx
    have h2 := (tY y hy).2
    show _ < _
    linarith
  · have h3 := tZ z hz
    show _ < _
    rcases List.mem_append.1 hx with hx | hx
    · have h1 := tX x hx
      have h2 := tY _ (List.mem_flatMap.2 ⟨⟨0, by rw [hSk]; omega⟩, List.mem_finRange _, List.mem_cons_self⟩)
      linarith [h2.1, h2.2]
    · have h1 := (tY x hx).1
      linarith

end GlobalTheory.RowReal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalTranslateSumBoundedRapidDecay
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.LatticeTranslateSum

theorem sum_pow_le {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i) (N : ℕ) :
    (∑ i, f i) ^ N ≤ (Fintype.card ι : ℝ) ^ N * ∑ i, f i ^ N := by
  set k : ℝ := (Fintype.card ι : ℝ) with hk_def
  have hk1 : (1 : ℝ) ≤ k := Nat.one_le_cast.mpr Fintype.card_pos
  have hk : (0 : ℝ) < k := by linarith
  have hw : ∑ _i : ι, (1 / k) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hk_def]
    field_simp
  have h := Real.pow_arith_mean_le_arith_mean_pow Finset.univ (fun _ => 1 / k) f
    (fun _ _ => by positivity) hw (fun i _ => hf i) N
  rw [← Finset.mul_sum, ← Finset.mul_sum, mul_pow] at h
  have hs : 0 ≤ ∑ i, f i ^ N := Finset.sum_nonneg fun i _ => pow_nonneg (hf i) _
  calc (∑ i, f i) ^ N = k ^ N * ((1 / k) ^ N * (∑ i, f i) ^ N) := by
        rw [← mul_assoc, ← mul_pow, mul_one_div_cancel hk.ne', one_pow, one_mul]
    _ ≤ k ^ N * (1 / k * ∑ i, f i ^ N) := mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ k ^ N * ∑ i, f i ^ N := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have : 1 / k ≤ 1 := by rw [div_le_one hk]; exact hk1
        nlinarith

theorem decay (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (θ : InfFam D) (hθ : IsInfFam θ)
    (S T : HSp D) (c : WO S T → ℂ)
    (hder : ∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (k : ℕ), ∃ C : ℝ, ∀ w : WO S T,
      ‖deriv (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0‖ ^ k * ‖c w‖ ≤ C) (N : ℕ) :
    ∃ C : ℝ, ∀ w : WO S T, (1 + GlobalTheory.Unf.realSize θ w) ^ N * ‖c w‖ ≤ C := by
  classical
  choose n zs κ hκ using fun τ => _root_.GlobalTheory.SymplBound.bound D S T τ
  choose Cf hCf using hder
  obtain ⟨τ₀⟩ := (GlobalTheory.DataRowsCounterexample.places_nonempty D).1
  let dv : (Σ τ : D.what₂.Tau, Fin (n τ)) → WO S T → ℝ := fun p w =>
    ‖deriv (fun t : ℝ => ψ (symplO S T (lineAt θ p.1 (zs p.1 p.2) t) w)) 0‖
  let r : (Σ τ : D.what₂.Tau, Fin (n τ)) → ℝ := fun p => |κ p.1| / (2 * Real.pi)
  let f : WO S T → Option (Σ τ : D.what₂.Tau, Fin (n τ)) → ℝ := fun w o =>
    match o with
    | none => 1
    | some p => r p * dv p w
  have hf0 : ∀ w o, 0 ≤ f w o := by
    intro w o
    cases o with
    | none => simp [f]
    | some p => exact mul_nonneg (div_nonneg (abs_nonneg _) (by positivity)) (norm_nonneg _)
  have hdv : ∀ p w, r p * dv p w = |κ p.1| * |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt S T p.1 (zs p.1 p.2) (compAt θ p.1 w)| := by
    intro p w
    simp only [r, dv]
    rw [_root_.GlobalTheory.LatSum.norm_deriv_psi_symplO_lineAt D ψ hψ θ hθ S T p.1 (zs p.1 p.2) w]
    field_simp
  have hsize : ∀ w, 1 + GlobalTheory.Unf.realSize θ w ≤ ∑ o, f w o := by
    intro w
    rw [Fintype.sum_option]
    simp only [f]
    refine add_le_add le_rfl ?_
    rw [Fintype.sum_sigma]
    unfold GlobalTheory.Unf.realSize
    refine Finset.sum_le_sum fun τ _ => ?_
    simp only [hdv]
    rw [← Finset.mul_sum]
    have hs : 0 ≤ ∑ l, |GlobalTheory.IndefiniteRowSideFullHecke.HermitianSymplecticScalars.symplAt S T τ (zs τ l) (compAt θ τ w)| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    exact (hκ τ (compAt θ τ w)).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hs)
  refine ⟨(Fintype.card (Option (Σ τ : D.what₂.Tau, Fin (n τ))) : ℝ) ^ N *
    (Cf τ₀ 0 0 + ∑ p, r p ^ N * Cf p.1 (zs p.1 p.2) N), fun w => ?_⟩
  have hrs : 0 ≤ GlobalTheory.Unf.realSize θ w := by
    unfold GlobalTheory.Unf.realSize
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have h1 : (1 + GlobalTheory.Unf.realSize θ w) ^ N ≤ (∑ o, f w o) ^ N := pow_le_pow_left₀ (by positivity) (hsize w) N
  have h2 := sum_pow_le (f w) (hf0 w) N
  calc (1 + GlobalTheory.Unf.realSize θ w) ^ N * ‖c w‖ ≤ (∑ o, f w o) ^ N * ‖c w‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ ≤ (Fintype.card (Option (Σ τ : D.what₂.Tau, Fin (n τ))) : ℝ) ^ N * (∑ o, f w o ^ N) * ‖c w‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ ≤ _ := by
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [Fintype.sum_option, add_mul, Finset.sum_mul]
        refine add_le_add ?_ (Finset.sum_le_sum fun p _ => ?_)
        · simp only [f, one_pow, one_mul]
          simpa using hCf τ₀ 0 0 w
        · simp only [f]
          rw [mul_pow, mul_assoc]
          exact mul_le_mul_of_nonneg_left (hCf p.1 (zs p.1 p.2) N w)
            (pow_nonneg (div_nonneg (abs_nonneg _) (by positivity)) _)

end GlobalTheory.LatticeTranslateSum


open GlobalTheory.LatticeTranslateSum in
theorem GlobalTheory.LatticeTranslateSum.sum_translates_bounded : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (c : WO S T → ℂ), (∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ w : WO S T, c w ≠ 0 → ∀ u ∈ U, u.map (infPart D) = 0 → ψ (symplO S T w u) = 1) → (∀ (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (k : ℕ), ∃ C : ℝ, ∀ w : WO S T, ‖deriv (fun t : ℝ => ψ (symplO S T (lineAt θ τ z t) w)) 0‖ ^ k * ‖c w‖ ≤ C) → ∃ C : ℝ, ∀ w : WO S T, Summable (fun γ : ratL T S => ‖c ((γ : WO S T) + w)‖) ∧ ∑' γ : ratL T S, ‖c ((γ : WO S T) + w)‖ ≤ C := by
  intro D ψ hψ θ hθ S T c ⟨U, hU, hUc⟩ hder
  obtain ⟨Q, hQ, hQc⟩ := _root_.GlobalTheory.AnnihMat.annihilator_inBox_full D ψ hψ S T U hU
  have hbox : ∀ x, c x ≠ 0 → GlobalTheory.Unf.InBox Q x := fun x hx => hQc x (hUc x hx)
  obtain ⟨-, -, -, -, -, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  obtain ⟨N, hN⟩ := GlobalTheory.Unf.MajLoc.summable_bound D θ hθ T.rank S.rank
  obtain ⟨b, hb, hbb⟩ := hN Q K hQ hK
  obtain ⟨C, hC⟩ := decay D ψ hψ θ hθ S T c hder N
  have hmaj : ∀ x : WO S T, ‖c x‖ ≤ max C 0 * GlobalTheory.Unf.maj θ Q N x := by
    intro x
    by_cases hx : c x = 0
    · rw [hx, norm_zero]
      refine mul_nonneg (le_max_right _ _) ?_
      unfold GlobalTheory.Unf.maj
      split_ifs
      · have hrs : 0 ≤ GlobalTheory.Unf.realSize θ x := by
          unfold GlobalTheory.Unf.realSize
          exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
        positivity
      · exact le_rfl
    · have hrs : 0 ≤ GlobalTheory.Unf.realSize θ x := by
        unfold GlobalTheory.Unf.realSize
        exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
      have hp : 0 < (1 + GlobalTheory.Unf.realSize θ x) ^ N := by positivity
      unfold GlobalTheory.Unf.maj
      rw [if_pos (hbox x hx), ← div_eq_mul_inv, le_div_iff₀ hp, mul_comm]
      exact (hC x).trans (le_max_left _ _)
  have hinj : Function.Injective (incA D) := GlobalTheory.MixModel.incA_injective
  let e0 : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ratL T S := fun ξ => ⟨rat ξ, ⟨ξ, rfl⟩⟩
  have he0 : Function.Bijective e0 := by
    refine ⟨fun ξ ξ' h => ?_, fun γ => ?_⟩
    · have h' : rat ξ = rat ξ' := congrArg Subtype.val h
      exact Matrix.map_injective hinj h'
    · obtain ⟨x, ξ, hξ⟩ := γ
      exact ⟨ξ, Subtype.ext hξ⟩
  refine ⟨max C 0 * ∑' ξ, b ξ, fun w => ?_⟩
  obtain ⟨g0, hg0, hg0K⟩ := hcov w
  let e : Matrix (Fin T.rank) (Fin S.rank) D.host.E ≃ ratL T S :=
    (Equiv.ofBijective e0 he0).trans (Equiv.addRight ⟨g0, hg0⟩)
  have hterm : ∀ ξ, ‖c (((e ξ : ratL T S) : WO S T) + w)‖ ≤ max C 0 * b ξ := by
    intro ξ
    have he : ((e ξ : ratL T S) : WO S T) + w = (g0 + w) + rat ξ := by
      show rat ξ + g0 + w = (g0 + w) + rat ξ
      abel
    rw [he]
    exact (hmaj _).trans (mul_le_mul_of_nonneg_left (hbb _ hg0K ξ) (le_max_right _ _))
  have hs : Summable (fun ξ => ‖c (((e ξ : ratL T S) : WO S T) + w)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hb.mul_left _)
  refine ⟨e.summable_iff.mp hs, ?_⟩
  rw [← e.tsum_eq, ← tsum_mul_left]
  exact hs.tsum_le_tsum hterm (hb.mul_left _)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SquareNuHeckeCharacterNotUnramifiedAtChosenPlace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri FieldCond)

namespace GlobalTheory.RowTest

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem squareNuHeckeCharacter_not_unramified_at_chosenPlace {μ₀ : T} (hL : L.Is μ₀) (G : GridData L sc) (t : T) (i j : Fin D.R.m) :
    ¬ (SqNum.nuH G t i j).UnrAt (G.pl.w G.pl.v0) := by
  intro hnu

  have hunder : (G.pl.w G.pl.v0).under (𝓞 D.host.F) = G.pl.v0 :=
    G.pl.under_w (G.pl.mem_S0_of_sum_eq.2 (Or.inl rfl))
  have hnotS1 : G.pl.v0 ∉ S1 D := G.ch.basePlace_not_mem_chiGridBadPlaces

  have hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q t →
      (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ≠ (G.pl.w G.pl.v0).under (𝓞 D.host.F) := by
    intro PP hPP
    rw [hunder]
    rcases hPP with hP | hP
    · intro heq
      apply hnotS1
      obtain ⟨k, hk⟩ := (hL.Pg PP).1 hP
      have hmem := GlobalTheory.LevelPlaces.mem_of_div L.C.P k PP hk
      have hF : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal := by
        simpa using hmem
      rw [← heq, S1_mem_OmF]
      fin_cases k
      · exact Or.inl hF
      · exact Or.inr (Or.inl hF)
    · exact G.pl.levelPlace_ne_basePlace t PP hP
  obtain ⟨hxi, hmu⟩ := (GlobalTheory.levCh_unramified_places D T L μ₀ hL t).2.2.2 _ hoff

  have hchi := (G.ch.lev0 (D.R.m - i) (by omega) (by omega) _ hunder).2
  apply hchi
  intro x hx
  have h := hnu x hx
  change (L.C.mu0 j * L.xiH t / G.ch.chiH (D.R.m - i)).loc (G.pl.w G.pl.v0) x = 1 at h
  change (L.C.mu0 j).loc (G.pl.w G.pl.v0) x * (L.xiH t).loc (G.pl.w G.pl.v0) x * ((G.ch.chiH (D.R.m - i)).loc (G.pl.w G.pl.v0) x)⁻¹ = 1 at h
  rw [hmu j x hx, hxi x hx, one_mul, one_mul] at h
  exact inv_eq_one.mp h

end GlobalTheory.RowTest

end
end

