module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1615
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1610
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Bundle0007
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.Bundle0003
public import Development.AutomorphicArithmetic.CyclotomicBounds.WildJets.LogSum
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0518
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlBlockFiniteDimModuleStructure
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HighestWeightTensor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1221
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0513
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1219
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJointShapeGenerated
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0689
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinFirst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0713
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1232
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1215
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1498
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1461
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLines
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1247
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1734
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1216
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1725
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationDarbouxCoordinates

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumEqualSignKernelLossesBounded
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat GlobalTheory.SumSize
open Formalism.DivisionValues (vw lw)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem GlobalTheory.SumSize.TopSize.depSum {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) :
    ∃ S : Finset ℕ, GlobalTheory.NormSum.Exponents S (fun l => if l.Prime then (depL G l : ℝ) else 0) (sig G) := by
  classical
  let c : HeightOneSpectrum (𝓞 D.host.F) → ℕ := fun v => ringChar (𝓞 D.host.F ⧸ v.asIdeal)
  have key : ∀ l : ℕ, l.Prime → depL G l = 0 ∨ ∃ v ∈ G.pl.S0, c v = l ∧ l ≤ Ideal.absNorm v.asIdeal ∧
      depL G l = G.pl.depth sc v := by
    intro l hl
    rcases (G.pl.W0.filter fun PP => (l : 𝓞 D.host.E) ∈ PP.asIdeal).eq_empty_or_nonempty with h | h
    · left; unfold depL; rw [h]; rfl
    · right
      obtain ⟨PP, hPP, e⟩ := Finset.exists_mem_eq_sup _ h (depthAt G)
      obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hPP
      have h1' : ∃ v ∈ G.pl.S0, G.pl.w v = PP := by
        unfold Places.W0 at h1; simpa only [Finset.mem_image] using h1
      obtain ⟨v, hv, rfl⟩ := h1'
      have hlv : (l : 𝓞 D.host.F) ∈ v.asIdeal := by
        rw [← G.pl.under_w hv]
        change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) l ∈ (G.pl.w v).asIdeal
        rwa [map_natCast]
      haveI := v.isPrime
      haveI : Finite (𝓞 D.host.F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
      have h0 : ((l : ℕ) : 𝓞 D.host.F ⧸ v.asIdeal) = 0 := by
        rw [← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]; exact hlv
      have hc : c v = l := CharP.ringChar_of_prime_eq_zero hl h0
      refine ⟨v, hv, hc, ?_, ?_⟩
      · have h3 : ((Nat.card (𝓞 D.host.F ⧸ v.asIdeal) : ℕ) : 𝓞 D.host.F ⧸ v.asIdeal) = 0 := by
          haveI := Fintype.ofFinite (𝓞 D.host.F ⧸ v.asIdeal)
          rw [Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero _
        rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← hc]
        exact Nat.le_of_dvd Nat.card_pos (ringChar.dvd h3)
      · rw [← (depthAt_w G hv).2, ← e]; unfold depL; congr
  refine ⟨(G.pl.S0.image c).filter Nat.Prime, fun l hl => (Finset.mem_filter.1 hl).2,
    fun l => by dsimp only; split_ifs <;> positivity, fun l hl => ?_, ?_⟩
  · dsimp only
    split_ifs with hp
    · rcases key l hp with h | ⟨v, hv, h, -⟩
      · rw [h, Nat.cast_zero]
      · exact absurd (Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨v, hv, h⟩, hp⟩) hl
    · rfl
  have hnn : ∀ v, 0 ≤ (G.pl.depth sc v : ℝ) * Real.log (Ideal.absNorm v.asIdeal) :=
    fun v => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  unfold sig
  rw [← Finset.sum_fiberwise_of_maps_to (g := c) (t := G.pl.S0.image c) (fun w hw => Finset.mem_image_of_mem _ hw)]
  refine le_trans (Finset.sum_le_sum fun l hl => ?_) (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset Nat.Prime _)
    fun l _ _ => Finset.sum_nonneg fun v _ => hnn v)
  have hp := (Finset.mem_filter.1 hl).2
  dsimp only
  rw [if_pos hp]
  rcases key l hp with h | ⟨v, hv, h, h1, h2⟩
  · rw [h, Nat.cast_zero, zero_mul]; exact Finset.sum_nonneg fun v _ => hnn v
  · refine le_trans ?_ (Finset.single_le_sum (f := fun v => (G.pl.depth sc v : ℝ) * Real.log (Ideal.absNorm v.asIdeal))
      (fun v _ => hnn v) (Finset.mem_filter.2 ⟨hv, h⟩))
    rw [h2]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (by exact_mod_cast hp.pos) (by exact_mod_cast h1)) (Nat.cast_nonneg _)

private theorem GlobalTheory.SumSize.TopSize.sum_le_of_exponents {S : Finset ℕ} {h : ℕ → ℝ} {B : ℝ} (hE : GlobalTheory.NormSum.Exponents S h B)
    (P : Finset ℕ) : ∑ p ∈ P, h p * Real.log p ≤ B := by
  obtain ⟨-, h0, hS, hB⟩ := hE
  calc ∑ p ∈ P, h p * Real.log p ≤ ∑ p ∈ P ∪ S, h p * Real.log p :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
          (fun p _ _ => mul_nonneg (h0 p) (Real.log_natCast_nonneg p))
    _ = ∑ p ∈ S, h p * Real.log p :=
        (Finset.sum_subset Finset.subset_union_right (fun x _ hxS => by rw [hS x hxS, zero_mul])).symm
    _ ≤ _ := hB

private theorem GlobalTheory.SumSize.TopSize.sum_nab_le (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) {X : ℝ} (hX : 0 ≤ X) :
    ∑ p ∈ P, (if (p : ℝ) ≤ X then Real.logb p X else 0) * Real.log p ≤ X * max (Real.log X) 0 := by
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  rcases lt_or_ge X 1 with h1 | h1
  · rw [Finset.filter_false_of_mem, Finset.sum_empty]
    · positivity
    · intro p hp hle
      have : (1 : ℝ) < p := by exact_mod_cast (hP p hp).one_lt
      linarith
  · rw [max_eq_left (Real.log_nonneg h1)]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p hp _ => ?_) (UpperTheory.WildA.logSum X h1)
    · obtain ⟨hp1, hp2⟩ := Finset.mem_filter.1 hp
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor hp2)), hP p hp1⟩
    · have hp' := (Finset.mem_filter.1 hp).2
      exact mul_nonneg (Real.logb_nonneg (by exact_mod_cast hp'.one_lt) h1) (Real.log_natCast_nonneg p)

private theorem GlobalTheory.SumSize.TopSize.d_le {D : D7} (large₂ : SizeData₂ D) (h : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) :
    (D.host.d : ℝ) ≤ large₂.sc.b := by
  obtain ⟨-, -, -, hf, hm, -⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ h
  obtain ⟨-, -, -, -, -, hb, -⟩ := h
  have hk : D.R.m + 3 ≤ D.R.k := D.R.m_add_three_le_k
  have hN1 : 1 ≤ D.R.N D.R.m := by simp only [Formalism.BasicNotions.Ranks.N]; omega
  have h1 : 1 ≤ D.R.m * D.R.f * D.R.N D.R.m ^ 2 := Nat.mul_pos (Nat.mul_pos (by omega) hf) (by positivity)
  have h2 : (1 : ℝ) ≤ (D.R.m : ℝ) * D.R.f * (D.R.N D.R.m : ℝ) ^ 2 := by exact_mod_cast h1
  exact (le_mul_of_one_le_left (Nat.cast_nonneg _) h2).trans hb

private theorem GlobalTheory.SumSize.TopSize.arith {C1 C f m N b lb sg s1 s2 s3 s4 : ℝ} (hC1 : 0 < C1)
    (hC : C1 * 26 + C1 ^ 2 * (|Real.log C1| + 1) ≤ C) (hf : 0 ≤ f) (hm : 0 ≤ m) (hN : 1 ≤ N) (hb : 0 ≤ b) (hlb : 1 ≤ lb)
    (hsg : 0 ≤ sg) (h1 : s1 ≤ lb / 100) (h2 : s2 ≤ lb) (h3 : s3 ≤ sg) (h4 : s4 ≤ C1 * b * (|Real.log C1| + lb)) :
    C1 * m * (13 * f * N * b) * s1 + C1 * m * (13 * f * N * b) * s2 + C1 * m * (13 * f * N * b) * s3 +
      C1 * m * (f * N ^ 2) * s4 ≤ C * f * m * N ^ 2 * (lb + sg) * b := by
  have hM0 : 0 ≤ f * m * N ^ 2 * b * (lb + sg) := by positivity
  have hNN : N ≤ N ^ 2 := by nlinarith
  have hT1 : C1 * m * (13 * f * N * b) * (s1 + s2 + s3) ≤ C1 * 26 * (f * m * N ^ 2 * b * (lb + sg)) := by
    calc C1 * m * (13 * f * N * b) * (s1 + s2 + s3) ≤ C1 * m * (13 * f * N * b) * (2 * (lb + sg)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ C1 * m * (13 * f * N ^ 2 * b) * (2 * (lb + sg)) := by gcongr
      _ = _ := by ring
  have h5 : |Real.log C1| + lb ≤ (|Real.log C1| + 1) * (lb + sg) := by nlinarith [abs_nonneg (Real.log C1)]
  have hT2 : C1 * m * (f * N ^ 2) * s4 ≤ C1 ^ 2 * (|Real.log C1| + 1) * (f * m * N ^ 2 * b * (lb + sg)) := by
    calc C1 * m * (f * N ^ 2) * s4 ≤ C1 * m * (f * N ^ 2) * (C1 * b * (|Real.log C1| + lb)) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ ≤ C1 * m * (f * N ^ 2) * (C1 * b * ((|Real.log C1| + 1) * (lb + sg))) := by gcongr
      _ = _ := by ring
  have hC0 := mul_le_mul_of_nonneg_right hC hM0
  calc _ = C1 * m * (13 * f * N * b) * (s1 + s2 + s3) + C1 * m * (f * N ^ 2) * s4 := by ring
    _ ≤ (C1 * 26 + C1 ^ 2 * (|Real.log C1| + 1)) * (f * m * N ^ 2 * b * (lb + sg)) := by linarith
    _ ≤ C * (f * m * N ^ 2 * b * (lb + sg)) := hC0
    _ = _ := by ring

open GlobalTheory.SumSize.TopInt GlobalTheory.SumSize.TopSize in
private theorem GlobalTheory.SumSize.TopSize.core {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T)
    (large₂ : SizeData₂ D) (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) (hH : HostHyp D) (hc : sc.cGap = 1) {C1 C : ℝ} (hC1 : 0 < C1)
    (hC : C1 * 26 + C1 ^ 2 * (|Real.log C1| + 1) ≤ C) {S : Finset ℕ} {δ : ℕ → ℝ}
    (hδ : GlobalTheory.NormSum.Exponents S δ (Real.log D.host.rdE)) :
    Loss (topDl G δ C1 large₂.sc.b) (bOne G C large₂.sc.b) := by
  classical
  obtain ⟨Sd, hSd⟩ := depSum G
  obtain ⟨-, -, hN, -, -, -, hrd, hb12⟩ := GlobalTheory.SizesOfRows.sizes_of_sizeRows large₂ hs
  have hd := d_le large₂ hs
  have hker : ∀ j, j < D.R.m → ((∑ τ, ∑ a, (wt G (.top (j + 1)) τ).natW a : ℕ) : ℝ) +
      (D.R.f : ℝ) * (G.V (.top j)).rank * (G.V (.top (j + 1))).rank ≤ 13 * D.R.f * bigN D * large₂.sc.b :=
    fun j hj => UpperTheory.WildA.kerLe (G := G) large₂ hs hH hc (.top t j) hj
  generalize large₂.sc.b = b at *
  have hδ0 := hδ.2.1
  have hlb : 1 ≤ Real.log b := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hsig : 0 ≤ sig G := Finset.sum_nonneg fun v _ => mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _)
  set h : ℕ → ℝ := fun l => if l.Prime then
    C1 * ∑ j ∈ Finset.range D.R.m, kerLoss G δ C1 b (.top j) (.top (j + 1)) l (depL G l) else 0 with hh
  set P : Finset ℕ := (S ∪ {D.host.d} ∪ Sd ∪ Finset.range (⌊C1 * b⌋₊ + 1)).filter Nat.Prime with hP
  have hPp : ∀ p ∈ P, p.Prime := fun p hp => (Finset.mem_filter.1 hp).2
  have e : topDl G δ C1 b = fun w : PlL D => (vw w ((primeUnder w : ℕ) : D.what₂.LL) : ℝ) * h (primeUnder w) := by
    funext w
    simp only [hh, if_pos (primeUnder_prime w), topDl, mul_assoc]
  rw [e]
  refine UpperTheory.WildA.expLoss D P h _ ⟨hPp, fun l => ?_, fun l hl => ?_, ?_⟩
  · simp only [hh]
    split_ifs with hl
    · exact mul_nonneg hC1.le (Finset.sum_nonneg fun j _ => kerLoss_nonneg G hδ0 C1 b _ _ hl _)
    · exact le_rfl
  · simp only [hh]
    split_ifs with hp
    · simp only [hP, Finset.mem_filter, hp, and_true, Finset.mem_union, Finset.mem_singleton, Finset.mem_range, not_or] at hl
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hl
      have e1 := hδ.2.2.1 l h1
      have e3 : (depL G l : ℝ) = 0 := by simpa only [if_pos hp] using hSd.2.2.1 l h3
      have e4 : ¬ (l : ℝ) ≤ C1 * b := fun h5 => h4 (Nat.lt_succ_of_le (Nat.le_floor h5))
      simp only [kerLoss, e1, e3, if_neg h2, if_neg e4, add_zero, mul_zero, Finset.sum_const_zero]
    · rfl
  have hKp : ∀ p ∈ P, h p * Real.log p ≤
      C1 * D.R.m * (13 * D.R.f * bigN D * b) * (δ p * Real.log p) +
        C1 * D.R.m * (13 * D.R.f * bigN D * b) * ((if p = D.host.d then (1 : ℝ) else 0) * Real.log p) +
        C1 * D.R.m * (13 * D.R.f * bigN D * b) * ((if p.Prime then (depL G p : ℝ) else 0) * Real.log p) +
        C1 * D.R.m * (D.R.f * (bigN D : ℝ) ^ 2) * ((if (p : ℝ) ≤ C1 * b then Real.logb p (C1 * b) else 0) * Real.log p) := by
    intro p hp
    have hM : 0 ≤ δ p + (if p = D.host.d then (1 : ℝ) else 0) + (depL G p : ℝ) := by
      have := hδ0 p
      have : 0 ≤ (if p = D.host.d then (1 : ℝ) else 0) := by split_ifs <;> norm_num
      positivity
    have hK := Finset.sum_le_card_nsmul (Finset.range D.R.m)
      (fun j => kerLoss G δ C1 b (.top j) (.top (j + 1)) p (depL G p))
      ((13 * D.R.f * bigN D * b) * (δ p + (if p = D.host.d then 1 else 0) + (depL G p : ℝ)) +
        D.R.f * (bigN D : ℝ) ^ 2 * (if (p : ℝ) ≤ C1 * b then Real.logb p (C1 * b) else 0)) (fun j hj => by
        unfold kerLoss
        exact add_le_add (mul_le_mul_of_nonneg_right (hker j (Finset.mem_range.1 hj)) hM) le_rfl)
    rw [Finset.card_range, nsmul_eq_mul] at hK
    have hlp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    simp only [hh, if_pos (hPp p hp)]
    refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK hC1.le) hlp).trans (le_of_eq ?_)
    ring
  have hs2 : ∑ p ∈ P, (if p = D.host.d then (1 : ℝ) else 0) * Real.log p ≤ Real.log b := by
    simp only [ite_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq']
    split_ifs with hdP
    · exact Real.log_le_log (by exact_mod_cast (hPp _ hdP).pos) hd
    · linarith
  have hs4 : ∑ p ∈ P, (if (p : ℝ) ≤ C1 * b then Real.logb p (C1 * b) else 0) * Real.log p ≤
      C1 * b * (|Real.log C1| + Real.log b) := by
    have h0 : 0 ≤ C1 * b := mul_nonneg hC1.le (by linarith)
    refine (sum_nab_le P hPp h0).trans (mul_le_mul_of_nonneg_left ?_ h0)
    rw [Real.log_mul hC1.ne' (by linarith)]
    exact max_le (by linarith [le_abs_self (Real.log C1)]) (by linarith [abs_nonneg (Real.log C1)])
  refine (Finset.sum_le_sum hKp).trans ?_
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  exact arith hC1 hC (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by exact_mod_cast hN) (by linarith) hlb hsig
    ((sum_le_of_exponents hδ P).trans hrd) hs2 (sum_le_of_exponents hSd P) hs4

theorem _root_.GlobalTheory.T.sum_equalSign_kernel_losses_bounded : ∀ C1 : ℝ, 0 < C1 → ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∃ C0 : ℝ, ∀ ε C : ℝ, C0 ≤ C → ∃ x₀ : ℝ,
      ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
      ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK → GlobalTheory.NormSum.Inp D →
      ∀ (S : Finset ℕ) (δ : ℕ → ℝ), GlobalTheory.NormSum.Letters D S δ →
        Loss (GlobalTheory.SumSize.TopInt.topDl ch.G δ C1 large₂.sc.b) (bOne ch.G C large₂.sc.b) := by
  intro C1 hC1
  refine ⟨0, fun CF _ => ⟨C1 * 26 + C1 ^ 2 * (|Real.log C1| + 1), fun ε C hC => ⟨0, ?_⟩⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hSet ch _ hAt _ _ S δ hLet
  have hc : ch.sc.cGap = 1 := by rw [hAt]
  exact GlobalTheory.SumSize.TopSize.core ch.G A.μ0 large₂ hSet.size hSet.host hc hC1 hC ⟨hLet.1, hLet.2.1, hLet.2.2.1, hLet.2.2.2.1⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelReal
section
noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.RealLift.Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_map_piInf {n m : Type} (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

theorem hasExp_div (τ : ∀ w : InfinitePlace F, EmbOver E w) {χ χ' : Chr F E} {m m' : InfinitePlace F → ℤ}
    (h : HasExp τ χ m) (h' : HasExp τ χ' m') : HasExp τ (χ / χ') (fun w => m w - m' w) := by
  intro z hz
  rw [MonoidHom.div_apply, Circle.coe_div, h z hz, h' z hz, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have : piInf (τ w) (z : AE F E) / (‖piInf (τ w) (z : AE F E)‖ : ℂ) ≠ 0 := by
    have h0 : piInf (τ w) (z : AE F E) ≠ 0 := by
      intro e
      have := congrArg (piInf (τ w)) z.mul_inv
      rw [map_mul, e, zero_mul, map_one] at this
      exact zero_ne_one this
    exact div_ne_zero h0 (by exact_mod_cast norm_ne_zero_iff.2 h0)
  rw [zpow_sub₀ this]

section Tensor
variable {ι : Type} [Fintype ι] [DecidableEq ι] {V W : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

theorem map_atPl (p : ∀ i, V i →ₗ[ℂ] W i) (w : ι) (L : Module.End ℂ (V w)) (L' : Module.End ℂ (W w))
    (h : p w ∘ₗ L = L' ∘ₗ p w) : PiTensorProduct.map p ∘ₗ atPl w L = atPl w L' ∘ₗ PiTensorProduct.map p := by
  unfold atPl
  rw [← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
  congr 1
  funext i
  by_cases hi : i = w
  · subst hi; simp [h]
  · simp [Function.update_of_ne hi]

theorem map_sumPl (p : ∀ i, V i →ₗ[ℂ] W i) (L : ∀ i, Module.End ℂ (V i)) (L' : ∀ i, Module.End ℂ (W i))
    (h : ∀ i, p i ∘ₗ L i = L' i ∘ₗ p i) : PiTensorProduct.map p ∘ₗ sumPl L = sumPl L' ∘ₗ PiTensorProduct.map p := by
  apply LinearMap.ext; intro x
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [sumPl, LinearMap.comp_apply, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun i _ => LinearMap.congr_fun (map_atPl p i (L i) (L' i) (h i)) x

end Tensor

theorem i_locfin : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (V : ι → Type) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] (L : ∀ i, Module.End ℂ (V i)), (∀ i, GlobalTheory.RealLift.LocFin (L i)) → GlobalTheory.RealLift.LocFin (GlobalTheory.RealLift.sumPl L) := _root_.GlobalTheory.RealLift.locFin_sumPl

theorem i_expact : ∀ (F : Type) [Field F] [NumberField F] (κ V : Type) [Fintype κ] [AddCommGroup V] [Module ℂ V] (Φ : V →ₗ[ℂ] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (L : Module.End ℂ V) (om : Multiplicative ℝ →* Module.End ℂ ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ)), GlobalTheory.RealLift.LocFin L → (∀ t, ∀ l ∈ (GlobalTheory.WeilM.adeleClass F).adm κ, l ∘ₗ om t ∈ (GlobalTheory.WeilM.adeleClass F).adm κ) → (∀ T, GlobalTheory.RealLift.SD (fun t => om (Multiplicative.ofAdd t)) (Φ T) (Φ (L T))) → ∃ U : Module.End ℂ V, GlobalTheory.RealLift.IsExp L U ∧ ∀ T, GlobalTheory.RealLift.SA (om (Multiplicative.ofAdd 1)) (Φ T) (Φ (U T)) := _root_.GlobalTheory.ExpAct.expAct_fock

theorem i_actslaws : GlobalTheory.RealLift.ActsLaws := _root_.GlobalTheory.RealLift.actsLaws

theorem i_derex : GlobalTheory.RealLift.DerEx := _root_.GlobalTheory.HeisDer.derEx

theorem i_fockex : GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.FockEx := _root_.GlobalTheory.FockMapEx.fockEx_of_derEx

theorem i_vacline : GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine := GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives

theorem i_polrange : GlobalTheory.RealLift.ActsLaws → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.PolRange := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws

theorem i_genex : GlobalTheory.RealLift.GenEx := _root_.GlobalTheory.RealLiftGen.genEx

theorem i_lineex : GlobalTheory.RealLift.LineEx := _root_.GlobalTheory.RealLift.exists_line_of_upq

theorem i_kline : GlobalTheory.RealLift.LineEx → GlobalTheory.RealLift.KLine := GlobalTheory.T.maximalCompact_oneParameterLines_of_lieLines

theorem i_liescalar : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.LieScalar := _root_.GlobalTheory.LieScal.lieScalar

theorem i_liesecond : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RealLift.DerEx → GlobalTheory.RealLift.FockEx → GlobalTheory.RealLift.VacLine → GlobalTheory.RealLift.LieScalar → GlobalTheory.RealLift.LieSecond := _root_.GlobalTheory.RealLift.LieSecondPf.lieSecond_of_lieScalar

theorem i_liefirst : GlobalTheory.RealLift.LieSecond → GlobalTheory.RealLift.LieFirst := GlobalTheory.T.lieFirst_of_lieSecond'

theorem i_frameex : GlobalTheory.RealLift.FrameEx := _root_.GlobalTheory.RealLift.frameEx_holds

theorem i_parity : GlobalTheory.RealLift.Parity := _root_.GlobalTheory.RealLift.even_im_hermitian_sub

section Helpers

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V W : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

theorem atPl_eq (w : ι) (L : Module.End ℂ (V w)) :
    atPl w L = PiTensorProduct.mapMultilinear ℂ V V (Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w L) := rfl

theorem atPl_add (w : ι) (L L' : Module.End ℂ (V w)) : atPl w (L + L') = atPl w L + atPl w L' := by
  simp only [atPl_eq, MultilinearMap.map_update_add]

theorem atPl_smul (w : ι) (c : ℂ) (L : Module.End ℂ (V w)) : atPl w (c • L) = c • atPl w L := by
  simp only [atPl_eq, MultilinearMap.map_update_smul, RingHom.id_apply]

theorem atPl_one (w : ι) : atPl w (1 : Module.End ℂ (V w)) = 1 := by
  rw [atPl_eq, show Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w 1 = fun i => LinearMap.id by
    funext i; by_cases h : i = w
    · subst h; simp; rfl
    · simp [Function.update_of_ne h]]
  exact PiTensorProduct.map_id

theorem atPl_zero (w : ι) : atPl w (0 : Module.End ℂ (V w)) = 0 := by
  simp only [atPl_eq, MultilinearMap.map_update_zero]

end Helpers

section Exp

variable {V V' Z : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup Z] [Module ℂ Z]

theorem pow_comm {q : V →ₗ[ℂ] Z} {L : Module.End ℂ V} {L0 : Module.End ℂ Z} (h : q ∘ₗ L = L0 ∘ₗ q) (n : ℕ) (v : V) :
    q ((L ^ n) v) = (L0 ^ n) (q v) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih, ← LinearMap.comp_apply, h,
      LinearMap.comp_apply]

theorem exp_equiv {q : V →ₗ[ℂ] Z} {q' : V' →ₗ[ℂ] Z} {L U : Module.End ℂ V} {L' U' : Module.End ℂ V'} {L0 : Module.End ℂ Z}
    (hU : IsExp L U) (hU' : IsExp L' U') (h : q ∘ₗ L = L0 ∘ₗ q) (h' : q' ∘ₗ L' = L0 ∘ₗ q') {v : V} {v' : V'}
    (e : q v = q' v') : q (U v) = q' (U' v') := by
  refine sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ (q (U v) - q' (U' v'))).1 fun l => ?_)
  rw [map_sub, sub_eq_zero]
  have a := hU v (l ∘ₗ q)
  have b := hU' v' (l ∘ₗ q')
  simp only [LinearMap.comp_apply, pow_comm h, pow_comm h', e] at a b
  exact a.unique b

end Exp

theorem locFin_fock1 (P Q R S : ℕ) (X : Mat P Q) (hX : IsKC X) (c : ℂ) :
    LocFin (fockAct1 P Q R S X + c • 1) := fun v => by
  obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).1 v
  exact ⟨W, hW, hv, fun y hy => W.add_mem (hs X hX y hy) (W.smul_mem c hy)⟩

theorem locFin_fock2 (P Q R S : ℕ) (Y : Mat R S) (hY : IsKC Y) (c : ℂ) :
    LocFin (fockAct2 P Q R S Y + c • 1) := fun v => by
  obtain ⟨⟨W, hW, hv, hs⟩, -⟩ := (GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 v
  exact ⟨W, hW, hv, fun y hy => W.add_mem (hs Y hY y hy) (W.smul_mem c hy)⟩

section Side

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d P Q R S : ℕ} {Y : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W)
  (N : InfinitePlace F → GKMod R S) (p : ∀ w, Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] (N w).V)
  (Φ : Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (Ψ : SInf F (Fin n × Fin d) →ₗ[ℂ] Tens F P Q R S)

include Φ in
theorem pol_eq (hrange : LinearMap.range Φ = M.Pol B.ψ B.emb) {f : SInf F (Fin n × Fin d)} (hf : f ∈ M.Pol B.ψ B.emb) :
    ∃ T, f = Φ T := by
  rw [← hrange] at hf
  obtain ⟨T, rfl⟩ := hf
  exact ⟨T, rfl⟩

end Side

section SideW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d P Q R S : ℕ} {Y : Spc F E n} {W : Spc F E d} (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W)
  (N : InfinitePlace F → GKMod R S) (p : ∀ w, Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] (N w).V)
  (Φ : Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)) (Ψ : SInf F (Fin n × Fin d) →ₗ[ℂ] Tens F P Q R S)

end SideW

theorem zero_mem_upq (R S : ℕ) : (0 : Mat R S) ∈ upq R S := by simp [upq]

end GlobalTheory.RealLift.Main
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportedArchHeisenbergDirectionsContinuous
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.ArchTransportHost

theorem archDir_transport_host : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (m n : ℕ) (JA : Matrix (Fin m) (Fin m) D.host.E)
    (JB : Matrix (Fin n) (Fin n) D.host.E) (ξ : AF D.host.F ⊗[D.host.F] D.host.E) (κ : Type) [Fintype κ]
    (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ)
    (om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ)),
    (∀ p w, ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
      om p (co.rho ψ w φ) = co.rho ψ (GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) p w) (om p φ)) →
    ∃ M : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
        GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) → ((κ → mixedEmbedding.mixedSpace D.host.F) × (κ → mixedEmbedding.mixedSpace D.host.F)) →ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace D.host.F) × (κ → mixedEmbedding.mixedSpace D.host.F)),
      (∀ p h, ∀ φ ∈ GlobalTheory.WeilM.schA D.host.F κ,
        om p (GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair D.host.F (M p h)) φ) =
          GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilL2Words.archPair D.host.F h) (om p φ)) ∧
      ∀ h, Continuous fun p => M p h := by
  intro D ψ m n JA JB ξ κ _ co om hom
  exact GlobalTheory.ArchTransportDir.archDir_transport D.host.F D.host.E D.sp.cm.sig ψ m n JA JB ξ κ co om hom

end GlobalTheory.ArchTransportHost

end
end

