module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1877
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2042
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchoredWeightIndefiniteLiftGaps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1992
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Formalism.LocalRingCardinality.Bundle0003
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchorBoundStatement
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.AnchorRd

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem anchor_eq (P : ParameterChoice' D L) (t : D.what₂.Tau) (τ : Psi p.T.Q.H) (hτ : τ.1 = DV.tauEmb D t) :
    (anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℤ) =
      ⌊Formalism.L2.NTheta.lamAt (D.hc t) (D.R.k - 2) + (D.hc t).e i -
        (((D.R.sigW ((i : ℕ) + 1)).1 : ℚ) - ((D.R.k - 2 : ℕ) + 1)) - ((D.R.t : ℚ) + 1) / 2⌋ +
        (((p.κ i).n / 2 : ℕ) : ℤ) := by
  have hk := D.R.m_add_three_le_k
  have hmain := GlobalTheory.CovTop.WtRead.main D p.T p.fw.laws i (p.κ i)
  have hsw : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + (i : ℕ) := by simp only [Ranks.sigW]; omega
  have hpq : (dat p i).p = (D.R.sigW ((i : ℕ) + 1)).1 := hmain.1
  have hlt : D.R.k - 1 - 1 < (dat p i).p + (dat p i).q := by omega
  have hj : D.R.k - 2 < (D.R.sigW ((i : ℕ) + 1)).1 := by omega
  obtain ⟨-, hnn⟩ := GlobalTheory.RecGaps.bigEnt p P i t (D.R.k - 2) hj
  unfold anchor
  rw [dite_eq_left hlt, GlobalTheory.CovTop.WtRead.laOf_big D p.T p.fw.laws i (p.κ i) t τ hτ _ ⟨D.R.k - 2, hj⟩ (by simp; omega),
    (p.fw.kap i t).1 ⟨D.R.k - 2, hj⟩]
  rw [GlobalTheory.RecGaps.sig_Wc]
  unfold aPl
  rw [if_pos hj, Int.toNat_of_nonneg hnn]

theorem abs_anchor_sub_le (P : ParameterChoice' D L) (t : D.what₂.Tau) (τ : Psi p.T.Q.H) (hτ : τ.1 = DV.tauEmb D t) :
    |((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℤ) : ℝ) - (((D.hc t).e i : ℚ) : ℝ)| ≤
      L.Sc + D.R.nV + D.R.m + D.R.t + 2 := by
  have hk := D.R.m_add_three_le_k
  have ha := anchor_eq p i P t τ hτ
  have hn : (p.κ i).n = D.R.nV := (p.fw.kap i t).2.2
  have hv : Formalism.L2.NTheta.lamAt (D.hc t) (D.R.k - 2) = (D.hc t).v ⟨D.R.k - 2, by omega⟩ := by
    unfold Formalism.L2.NTheta.lamAt; rw [dite_eq_left (by omega)]
  have hc := L.cloud_v t ⟨D.R.k - 2, by omega⟩
  have hsw : ((D.R.sigW ((i : ℕ) + 1)).1 : ℚ) - ((D.R.k - 2 : ℕ) + 1) = (i : ℚ) + 1 := by
    rw [show (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + (i : ℕ) by simp only [Ranks.sigW]; omega,
      Nat.cast_sub (by omega : 2 ≤ D.R.k)]
    push_cast; ring
  rw [hsw, hv] at ha
  rw [ha, hn]
  have h1 := Int.floor_le ((D.hc t).v ⟨D.R.k - 2, by omega⟩ + (D.hc t).e i - ((i : ℚ) + 1) - ((D.R.t : ℚ) + 1) / 2)
  have h2 := Int.lt_floor_add_one ((D.hc t).v ⟨D.R.k - 2, by omega⟩ + (D.hc t).e i - ((i : ℚ) + 1) - ((D.R.t : ℚ) + 1) / 2)
  have h1' : ((⌊(D.hc t).v ⟨D.R.k - 2, by omega⟩ + (D.hc t).e i - ((i : ℚ) + 1) - ((D.R.t : ℚ) + 1) / 2⌋ : ℤ) : ℝ) ≤
      (((D.hc t).v ⟨D.R.k - 2, by omega⟩ + (D.hc t).e i - ((i : ℚ) + 1) - ((D.R.t : ℚ) + 1) / 2 : ℚ) : ℝ) := by
    exact_mod_cast h1
  have h2' : (((D.hc t).v ⟨D.R.k - 2, by omega⟩ + (D.hc t).e i - ((i : ℚ) + 1) - ((D.R.t : ℚ) + 1) / 2 : ℚ) : ℝ) <
      ((⌊(D.hc t).v ⟨D.R.k - 2, by omega⟩ + (D.hc t).e i - ((i : ℚ) + 1) - ((D.R.t : ℚ) + 1) / 2⌋ : ℤ) : ℝ) + 1 := by
    exact_mod_cast h2
  have hnv : ((D.R.nV / 2 : ℕ) : ℝ) ≤ D.R.nV := by exact_mod_cast Nat.div_le_self _ _
  have hnv0 : (0 : ℝ) ≤ ((D.R.nV / 2 : ℕ) : ℝ) := by positivity
  have hi : ((i : ℕ) : ℝ) + 1 ≤ D.R.m := by exact_mod_cast i.2
  have ht : (0 : ℝ) ≤ D.R.t := by positivity
  rw [Int.cast_add, Int.cast_natCast]
  push_cast at h1' h2'
  rw [abs_le]
  constructor <;> linarith [hc.1, hc.2]


set_option maxHeartbeats 1000000 in
theorem anchorAt_of {PP A : ℝ} (P : ParameterChoice' D L) (hw : WtNum p i PP) (hh : HostNum D L PP A 1) : AnchorAt p i 100 := by
  have hk := D.R.m_add_three_le_k
  have hm2 := D.R.two_le_m
  obtain ⟨hp, hq, hcard, -, -, E, hE, -⟩ := GlobalTheory.CovTop.WtRead.main D p.T p.fw.laws i (p.κ i)
  have hL10 := hh.big.2.1
  have hLx := hh.big.2.2.1
  have hll := hh.big.2.2.2
  have hxA : 1 ≤ L.sc.x ^ A := Real.one_le_rpow (by linarith) (by linarith [hh.poly.1])
  have hb : L.sc.x ^ A ≤ L.sc.b := by simpa using hh.room
  have hb1 : 1 ≤ L.sc.b := hxA.trans hb
  have hf : (8 : ℝ) ≤ D.R.f := by exact_mod_cast hh.f8
  have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast hm2
  have hunit := hw.unit
  have hom := hw.om
  have hanc : ∀ τ, |((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℤ) : ℝ)| ≤ 4 * L.sc.b := by
    intro τ
    unfold anchor
    split_ifs with h
    · exact hw.up τ _
    · simp only [Int.cast_zero, abs_zero]; linarith

  have hpr : ((dat p i).p : ℝ) + (dat p i).q = D.R.r := by
    rw [hp, hq]; exact_mod_cast GlobalTheory.CovTop.WtRead.sigW_add D i
  have hp0 : (0 : ℝ) ≤ (dat p i).p := by positivity
  have hq0 : (0 : ℝ) ≤ (dat p i).q := by positivity
  have hcr : |((dat p i).p : ℝ) - (dat p i).q| ≤ D.R.r := abs_le.2 ⟨by linarith, by linarith⟩
  have hqm : ((dat p i).q : ℝ) ≤ D.R.m := by
    rw [hq]; exact_mod_cast (by simp only [Ranks.sigW]; omega : (D.R.sigW ((i : ℕ) + 1)).2 ≤ D.R.m)
  have hc_eq : ((D.R.k : ℝ) + (((i : ℕ) + 1 : ℕ) : ℝ) - 1) - ((D.R.m : ℝ) - (((i : ℕ) + 1 : ℕ) : ℝ)) =
      ((dat p i).p : ℝ) - (dat p i).q := by
    rw [hp, hq]
    simp only [Ranks.sigW]
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring

  have hmainS : mainT p i = ∑ t : D.what₂.Tau, (((dat p i).p : ℝ) - (dat p i).q) * (((D.hc t).e i : ℚ) : ℝ) *
      (ofRecord D L p.Del p.h0).logOm := by
    show ∑ ρ : RPl D.R, (((D.R.k : ℝ) + (((i : ℕ) + 1 : ℕ) : ℝ) - 1) - ((D.R.m : ℝ) - (((i : ℕ) + 1 : ℕ) : ℝ))) *
      (ofRecord D L p.Del p.h0).w ((i : ℕ) + 1) ρ * (ofRecord D L p.Del p.h0).logOm = _
    rw [hc_eq, ← (tauPl_bijective D).sum_comp (fun t => (((dat p i).p : ℝ) - (dat p i).q) * (((D.hc t).e i : ℚ) : ℝ) *
      (ofRecord D L p.Del p.h0).logOm)]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    congr 2
    simp only [NumDatum.w, NumDatum.eQ]
    rw [dite_eq_left ⟨by omega, by omega⟩]
    congr 3
  have hancS : ∑ τ : Psi p.T.Q.H, (((dat p i).p : ℝ) - (dat p i).q) *
      ((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℤ) : ℝ) * (ofRecord D L p.Del p.h0).logOm =
      ∑ t : D.what₂.Tau, (((dat p i).p : ℝ) - (dat p i).q) *
        ((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) (E t) : ℤ) : ℝ) * (ofRecord D L p.Del p.h0).logOm :=
    (Equiv.sum_comp E (fun τ => (((dat p i).p : ℝ) - (dat p i).q) *
      ((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℤ) : ℝ) * (ofRecord D L p.Del p.h0).logOm)).symm
  have hcardT : (Fintype.card D.what₂.Tau : ℝ) = D.R.f := by exact_mod_cast Formalism.MainNotions.Lnk.card_Tau D

  have hne : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by rw [Formalism.MainNotions.Lnk.card_Tau]; have := hh.f8; omega)
  obtain ⟨t0⟩ := hne
  have hw'' : L.sc.w'' D.R.n ≤ 8 * L.sc.b := by
    have a1 := hw.low (E t0)
    have a2 := (abs_le.1 (hanc (E t0))).2
    linarith
  have hr2k : (D.R.r : ℝ) ≤ 2 * D.R.k := by exact_mod_cast (by unfold Ranks.r; omega : D.R.r ≤ 2 * D.R.k)
  have hSc0 : 0 ≤ L.Sc := L.Sc_pos.le
  have hrS : (D.R.r : ℝ) * L.Sc ≤ 16 * L.sc.b := by
    have a1 := P.kS_le
    have a2 : (D.R.r : ℝ) * L.Sc ≤ 2 * D.R.k * L.Sc := mul_le_mul_of_nonneg_right hr2k hSc0
    linarith
  have hnV : (D.R.nV : ℝ) = D.R.r + D.R.t := by unfold Ranks.nV; push_cast; ring
  have hmr : (D.R.m : ℝ) ≤ D.R.r := by exact_mod_cast (by unfold Ranks.r; omega : D.R.m ≤ D.R.r)
  have ht0 : (0 : ℝ) ≤ D.R.t := by positivity
  have hrnV : (D.R.r : ℝ) * D.R.nV ≤ L.sc.b := by
    have a1 := hh.poly.2.2
    have e0 : (0 : ℝ) ≤ (D.R.r : ℝ) * D.R.nV := by positivity
    have a2 : (D.R.r : ℝ) * D.R.nV * 1 ≤ (D.R.r : ℝ) * D.R.nV * (D.R.f * L.sc.L) :=
      mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)) e0
    calc (D.R.r : ℝ) * D.R.nV = (D.R.r : ℝ) * D.R.nV * 1 := by ring
      _ ≤ (D.R.r : ℝ) * D.R.nV * (D.R.f * L.sc.L) := a2
      _ = D.R.f * D.R.r * D.R.nV * L.sc.L := by ring
      _ ≤ L.sc.x ^ A := a1
      _ ≤ L.sc.b := hb
  have hB : (D.R.r : ℝ) * (L.Sc + D.R.nV + D.R.m + D.R.t + 2) ≤ 20 * L.sc.b := by
    have e1 : (D.R.r : ℝ) * (D.R.nV + D.R.m + D.R.t + 2) ≤ 4 * ((D.R.r : ℝ) * D.R.nV) := by
      calc (D.R.r : ℝ) * (D.R.nV + D.R.m + D.R.t + 2) ≤ (D.R.r : ℝ) * (4 * D.R.nV) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = 4 * ((D.R.r : ℝ) * D.R.nV) := by ring
    calc (D.R.r : ℝ) * (L.Sc + D.R.nV + D.R.m + D.R.t + 2) =
          (D.R.r : ℝ) * L.Sc + (D.R.r : ℝ) * (D.R.nV + D.R.m + D.R.t + 2) := by ring
      _ ≤ 16 * L.sc.b + 4 * L.sc.b := add_le_add hrS (by linarith)
      _ = 20 * L.sc.b := by ring
  refine ⟨?_, ?_, hh.poly.2.2.trans hb⟩
  · rw [hmainS, hancS, ← Finset.sum_sub_distrib]
    have hterm : ∀ t : D.what₂.Tau, |(((dat p i).p : ℝ) - (dat p i).q) * (((D.hc t).e i : ℚ) : ℝ) *
        (ofRecord D L p.Del p.h0).logOm - (((dat p i).p : ℝ) - (dat p i).q) *
        ((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) (E t) : ℤ) : ℝ) * (ofRecord D L p.Del p.h0).logOm| ≤
        (D.R.r : ℝ) * (L.Sc + D.R.nV + D.R.m + D.R.t + 2) * (3 * L.sc.L) := by
      intro t
      have a1 := abs_anchor_sub_le p i P t (E t) (hE t)
      rw [show (((dat p i).p : ℝ) - (dat p i).q) * (((D.hc t).e i : ℚ) : ℝ) * (ofRecord D L p.Del p.h0).logOm -
          (((dat p i).p : ℝ) - (dat p i).q) * ((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) (E t) : ℤ) : ℝ) *
          (ofRecord D L p.Del p.h0).logOm = -((((dat p i).p : ℝ) - (dat p i).q) *
          (((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) (E t) : ℤ) : ℝ) - (((D.hc t).e i : ℚ) : ℝ)) *
          (ofRecord D L p.Del p.h0).logOm) by ring, abs_neg, abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul hcr a1 (abs_nonneg _) (by positivity)) hom (abs_nonneg _) (by positivity)
    calc _ ≤ ∑ t : D.what₂.Tau, (D.R.r : ℝ) * (L.Sc + D.R.nV + D.R.m + D.R.t + 2) * (3 * L.sc.L) :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun t _ => hterm t)
      _ = D.R.f * ((D.R.r : ℝ) * (L.Sc + D.R.nV + D.R.m + D.R.t + 2)) * (3 * L.sc.L) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcardT]; ring
      _ ≤ D.R.f * (20 * L.sc.b) * (3 * L.sc.L) := by gcongr
      _ ≤ 100 * unitE p := by
          rw [hunit]
          have e1 : (0 : ℝ) ≤ D.R.f * L.sc.b * L.sc.L := by positivity
          have e2 : D.R.f * L.sc.b * L.sc.L * 1 ≤ D.R.f * L.sc.b * L.sc.L * (D.R.m * Real.log (Real.log L.sc.x)) :=
            mul_le_mul_of_nonneg_left (one_le_mul_of_one_le_of_one_le (by linarith) hll) e1
          have e3 : (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x) =
              D.R.f * L.sc.b * L.sc.L * (D.R.m * Real.log (Real.log L.sc.x)) := by ring
          have e4 : (D.R.f : ℝ) * (20 * L.sc.b) * (3 * L.sc.L) = 60 * (D.R.f * L.sc.b * L.sc.L * 1) := by ring
          rw [e3, e4]
          linarith
  · have hsum : ∑ τ : Psi p.T.Q.H, |((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℤ) : ℝ)| ≤
        D.R.f * (4 * L.sc.b) := by
      calc _ ≤ ∑ τ : Psi p.T.Q.H, 4 * L.sc.b := Finset.sum_le_sum fun τ _ => hanc τ
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hcard, nsmul_eq_mul]
    calc (∑ τ : Psi p.T.Q.H, |((anchor (dat p i) (wtA (p.κ i)) (p.κ i).n (D.R.k - 1) τ : ℤ) : ℝ)|) *
          ((dat p i).q : ℝ) * L.sc.L ≤ D.R.f * (4 * L.sc.b) * D.R.m * L.sc.L := by gcongr
      _ ≤ 100 * unitE p := by
          rw [hunit]
          have e1 : (0 : ℝ) ≤ D.R.f * L.sc.b * D.R.m * L.sc.L := by positivity
          have e2 : D.R.f * L.sc.b * D.R.m * L.sc.L * 1 ≤ D.R.f * L.sc.b * D.R.m * L.sc.L * Real.log (Real.log L.sc.x) :=
            mul_le_mul_of_nonneg_left hll e1
          have e3 : (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x) =
              D.R.f * L.sc.b * D.R.m * L.sc.L * Real.log (Real.log L.sc.x) := by ring
          have e4 : (D.R.f : ℝ) * (4 * L.sc.b) * D.R.m * L.sc.L = 4 * (D.R.f * L.sc.b * D.R.m * L.sc.L * 1) := by ring
          rw [e3, e4]
          linarith

end GlobalTheory.CovTop.AnchorRd

namespace GlobalTheory.CovTop

end GlobalTheory.CovTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntitoneWeightLogBoundStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.BergRank

open ReciprocityTheory.ChartRestriction.G.FD

theorem statement_abs_wtOf_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (la : AllWt.Weight Dw) (x : (E →+* ℂ) × ℕ) :
    |(((wtOf Dw la 0).1 x : ℤ) : ℝ)| ≤ ∑ τ, ∑ i, |(la τ i : ℝ)| := by
  have key : ∀ τ i, |(la τ i : ℝ)| ≤ ∑ τ, ∑ i, |(la τ i : ℝ)| := fun τ i =>
    (Finset.single_le_sum (f := fun i => |(la τ i : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun τ => ∑ i, |(la τ i : ℝ)|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.mem_univ τ))
  have h0 : (0 : ℝ) ≤ ∑ τ, ∑ i, |(la τ i : ℝ)| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  unfold wtOf
  dsimp only
  split_ifs <;> push_cast <;> simp only [sub_zero, abs_neg, abs_zero] <;> first | exact h0 | exact key _ _

theorem statement_abs_modelWt_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r)
    (la : AllWt.Weight Dw) (k : U.Comp) (τ : (U.X k).Ψ) (i : Fin r) :
    |((AllWt.modelWt U (wtOf Dw la 0) k τ i : ℤ) : ℝ)| ≤ ∑ τ, ∑ i, |(la τ i : ℝ)| := by
  unfold AllWt.modelWt
  have h2 : (wtOf Dw la 0).2 / 2 = 0 := by rw [AllWt.wtOf_snd]; simp
  split_ifs
  · rw [h2, add_zero]; exact statement_abs_wtOf_le la _
  · rw [h2, sub_zero]; push_cast; rw [abs_neg]; exact statement_abs_wtOf_le la _

theorem statement_sum_spread_modelWt_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r)
    (la : AllWt.Weight Dw) (k : U.Comp) :
    ∑ τ, (U.X k).spread (AllWt.modelWt U (wtOf Dw la 0) k) τ ≤
      2 * (Module.finrank ℚ E : ℝ) * ∑ τ, ∑ i, |(la τ i : ℝ)| := by
  set S := ∑ τ, ∑ i, |(la τ i : ℝ)| with hS
  have h0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hsp : ∀ τ, (U.X k).spread (AllWt.modelWt U (wtOf Dw la 0) k) τ ≤ 2 * S := by
    intro τ
    unfold Data.spread
    rcases isEmpty_or_nonempty (Fin r) with hr | hr
    · simp; linarith
    · have hb := fun i => abs_le.1 (statement_abs_modelWt_le U la k τ i)
      have h1 : (⨆ i, ((AllWt.modelWt U (wtOf Dw la 0) k τ i : ℤ) : ℝ)) ≤ S := ciSup_le fun i => (hb i).2
      have h2 : -S ≤ ⨅ i, ((AllWt.modelWt U (wtOf Dw la 0) k τ i : ℤ) : ℝ) := le_ciInf fun i => (hb i).1
      linarith
  have hcard : (Fintype.card (U.X k).Ψ : ℝ) ≤ Module.finrank ℚ E := by
    have e1 : Fintype.card (U.X k).Ψ = (U.X k).Ψ.card := Fintype.card_coe _
    have e2 : (U.X k).Ψ.card ≤ Fintype.card (E →+* ℂ) := Finset.card_le_univ _
    rw [NumberField.Embeddings.card] at e2
    exact_mod_cast e1 ▸ e2
  calc ∑ τ, (U.X k).spread (AllWt.modelWt U (wtOf Dw la 0) k) τ ≤ ∑ _τ : (U.X k).Ψ, 2 * S :=
        Finset.sum_le_sum fun τ _ => hsp τ
    _ = (Fintype.card (U.X k).Ψ : ℝ) * (2 * S) := by rw [Finset.sum_const, nsmul_eq_mul]; rfl
    _ ≤ (Module.finrank ℚ E : ℝ) * (2 * S) := mul_le_mul_of_nonneg_right hcard (by linarith)
    _ = _ := by ring


end GlobalTheory.BergRank

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.antitone_weight_log_bound : Hypotheses2 → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ la : AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → Real.log (∑ τ, ∑ k, |(la τ k : ℝ)|) ≤ 20 * Lb → ∀ Z, BergLe Z Y.U (fun _ => D.sp.W j) Y.dict la (Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3)) ∧ SupBdWt Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z la (Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3)) ∧ Real.log (Y.rkC la Z) ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3 := by
  intro hP
  refine ⟨4000, by norm_num, ?_⟩
  intro D T hT j hp hq hE hj Y e o hY Lb hLb hM hsz hfr ho la hla hS Z
  have hL := (GlobalTheory.T.deepLevelCover_principalLevel_laws_galois D T j Y e o hT hj hY hY.unit hY.modelW).1
  set S : ℝ := ∑ τ, ∑ k, |(la τ k : ℝ)| with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  set n : ℝ := (Module.finrank ℚ D.host.E : ℝ) with hn
  have hn1 : 1 ≤ n := by
    have : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    rw [hn]; exact_mod_cast this
  have hnlog : Real.log n ≤ 3 * Lb := (log_finrank_le_fieldSz _).trans hsz
  set w : ℝ := 2 * n * S + 1 with hw
  have hnS : 0 ≤ n * S := mul_nonneg (by linarith) hS0
  have hw1 : 1 ≤ w := by rw [hw]; nlinarith
  have hlogw : Real.log w ≤ 25 * Lb := by
    have hint : S = (((∑ τ, ∑ k, |la τ k|) : ℤ) : ℝ) := by rw [hSdef]; push_cast; rfl
    have hz : (0 : ℤ) ≤ ∑ τ, ∑ k, |la τ k| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    rcases hz.eq_or_lt with h0 | h1
    · have : S = 0 := by rw [hint, ← h0]; simp
      rw [hw, this]; simp; linarith
    · have hS1 : 1 ≤ S := by rw [hint]; exact_mod_cast h1
      have hwle : w ≤ 3 * (n * S) := by rw [hw]; nlinarith
      have hlS : Real.log S ≤ 20 * Lb := hS
      have e1 : Real.log w ≤ Real.log (3 * (n * S)) := Real.log_le_log (by linarith) hwle
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) (by positivity)] at e1
      have h3 : Real.log 3 < 2 := by
        have := Real.log_two_lt_d9; have h4 : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
        have : Real.log 4 = 2 * Real.log 2 := by rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
        linarith
      linarith
  obtain ⟨hβ1, hβ⟩ := _root_.GlobalTheory.ConstSzRows.supConst_size_rows D Y.d.l₂.M Lb w (by have := Y.d.l₂.three_le; omega) hLb hM hsz hfr hw1 hlogw
  set β := GlobalTheory.LevGeo.supConst D.host.E D.R.r D.host.d Y.d.l₂.M w with hβdef
  have hβexp : β ≤ Real.exp (4000 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3) := by
    rw [← Real.exp_log (by linarith : 0 < β)]; exact Real.exp_le_exp.2 hβ
  have hsp : ∀ σ k, ∑ τ, ((Y.U σ).X k).spread (AllWt.modelWt (Y.U σ) (wtOf _ la 0) k) τ ≤ w := fun σ k =>
    (GlobalTheory.BergRank.statement_sum_spread_modelWt_le _ la k).trans (by rw [hw]; linarith)
  have hB : BergLe Z Y.U (fun _ => D.sp.W j) Y.dict la β := fun σ hσ y hy =>
    _root_.GlobalTheory.BergComp.bergOn_le_supConst hP.p6 D j _ _ _ _ _ Y.U Y.dict hL σ hσ (wtOf _ la 0) (AllWt.even_wtOf la 0) w (by linarith) (hsp σ) Z y hy
  have hBexp : BergLe Z Y.U (fun _ => D.sp.W j) Y.dict la (Real.exp (4000 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3)) :=
    fun σ hσ y hy => (hB σ hσ y hy).trans (ENNReal.ofReal_le_ofReal hβexp)
  refine ⟨hBexp, ?_, ?_⟩
  · refine SupBdWt.of_bergOn (Real.exp_pos _).le ?_ hBexp
    intro σ hσ g
    obtain ⟨th, hr, -, hd⟩ := hY.dictU σ hσ
    exact Formalism.L2.Pj.dict_dom_of hd g
  · have hrk := _root_.GlobalTheory.RankBergman.rkC_le_of_bergLe D T.toCore j Y e o hY la Z β (by linarith) hB
    have hpos : 0 ≤ 4000 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3 := by positivity
    rcases (show (0 : ℝ) ≤ Y.rkC la Z by unfold Deep.rkC; positivity).eq_or_lt with h0 | h0
    · rw [← h0, Real.log_zero]; exact hpos
    · exact (Real.log_le_log h0 hrk).trans hβ

end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapInjectiveOfFlat
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs.SigInj

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀}
  {R₁ : Type} [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁)

def jj (i : I) : R₁ := Classical.choose (α.surj i.1 i.2)

theorem jj_q (i : I) : α.q (jj α i) = 0 := (Classical.choose_spec (α.surj i.1 i.2)).1

theorem jj_k (i : I) : α.k (jj α i) = i := (Classical.choose_spec (α.surj i.1 i.2)).2

theorem eq_jj {y : R₁} {i : I} (hq : α.q y = 0) (hk : α.k y = i) : y = jj α i := by
  have h := α.inj (y - jj α i) (by rw [map_sub, hq, jj_q, sub_zero]) (by rw [map_sub, hk, jj_k, sub_self])
  exact sub_eq_zero.mp h

theorem jj_add (i i' : I) : jj α (i + i') = jj α i + jj α i' :=
  (eq_jj α (by rw [map_add (f := _), jj_q, jj_q, add_zero]) (by rw [map_add (f := _), jj_k, jj_k]; rfl)).symm

theorem jj_smul (r : R) (i : I) : jj α (r • i) = π r • jj α i :=
  (eq_jj α (by rw [map_smul, jj_q, smul_zero]) (by rw [α.smul, jj_k]; rfl)).symm

variable {B B₀ : Type} [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀)

def tau (hs : SemiHom π p) : I ⊗[R] B →+ R₁ ⊗[R₀] B₀ :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun i ↦ AddMonoidHom.mk' (fun b ↦ jj α i ⊗ₜ[R₀] p b)
      (fun b b' ↦ by rw [map_add (f := _), TensorProduct.tmul_add]))
      (fun i i' ↦ by ext b; simp [jj_add, TensorProduct.add_tmul]))
    (fun r i b ↦ by
      simp only [AddMonoidHom.mk'_apply]
      rw [jj_smul, hs r b, TensorProduct.smul_tmul])

theorem tau_tmul (hs : SemiHom π p) (i : I) (b : B) : tau α p hs (i ⊗ₜ b) = jj α i ⊗ₜ[R₀] p b := by
  simp [tau, TensorProduct.liftAddHom_tmul]

end GlobalTheory.Obs.SigInj

open GlobalTheory.Obs.SigInj in
theorem GlobalTheory.Obs.sig_inj_of_flat : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) [Module.Flat R B] (σ : R₁ ⊗[R₀] B₀ →+ B), α.IsSig p σ → ∀ y, α.KerQ y → σ y = 0 → y = 0 := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α B B₀ _ _ _ _ p hs hp hker _ σ hσ y hy h0
  have hrange : ∀ y : R₁ ⊗[R₀] B₀, ∃ z, tau α p hs z =
      y - (1 : R₁) ⊗ₜ[R₀] TensorProduct.lid R₀ B₀ (Algebra.TensorProduct.map α.q (AlgHom.id R₀ B₀) y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul x b₀ =>
      obtain ⟨b, rfl⟩ := hp b₀
      have hq' : α.q (x - algebraMap R₀ R₁ (α.q x)) = 0 := by simp
      refine ⟨⟨α.k (x - algebraMap R₀ R₁ (α.q x)), α.mem _⟩ ⊗ₜ b, ?_⟩
      rw [tau_tmul, ← eq_jj α hq' rfl, Algebra.TensorProduct.map_tmul, TensorProduct.lid_tmul,
        ← TensorProduct.smul_tmul, TensorProduct.sub_tmul, Algebra.algebraMap_eq_smul_one]
      rfl
    | add a c ha hc =>
      obtain ⟨za, hza⟩ := ha
      obtain ⟨zc, hzc⟩ := hc
      exact ⟨za + zc, by rw [map_add (f := _), hza, hzc, map_add (f := _), map_add (f := _), TensorProduct.tmul_add]; abel⟩
  obtain ⟨z, hz⟩ := hrange y
  rw [show Algebra.TensorProduct.map α.q (AlgHom.id R₀ B₀) y = 0 from hy, map_zero,
    TensorProduct.tmul_zero, sub_zero] at hz
  have hμ : ∀ z, σ (tau α p hs z) = TensorProduct.lid R B (LinearMap.rTensor B I.subtype z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul i b => rw [tau_tmul, hσ, jj_k]; simp
    | add a c ha hc => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), ha, hc]
  have hinj : Function.Injective (fun z ↦ TensorProduct.lid R B (LinearMap.rTensor B I.subtype z)) :=
    (TensorProduct.lid R B).injective.comp
      (Module.Flat.rTensor_preserves_injective_linearMap _ Subtype.val_injective)
  have hz0 : z = 0 := hinj (by
    show TensorProduct.lid R B (LinearMap.rTensor B I.subtype z) =
      TensorProduct.lid R B (LinearMap.rTensor B I.subtype 0)
    rw [map_zero, map_zero, ← hμ, hz, h0])
  rw [← hz, hz0, map_zero]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentationSigmaMapNatural
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem sig_natural : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) (B' B₀' : Type) [CommRing B'] [Algebra R B'] [CommRing B₀'] [Algebra R₀ B₀'] (p' : B' →+* B₀') (hs' : SemiHom π p') (hp' : Function.Surjective p') (hker' : ∀ b, p' b = 0 ↔ b ∈ I.map (algebraMap R B')) (ρ : B →ₐ[R] B') (φ : B₀ →ₐ[R₀] B₀'), (∀ b, p' (ρ b) = φ (p b)) → ∀ (σ : R₁ ⊗[R₀] B₀ →+ B) (σ' : R₁ ⊗[R₀] B₀' →+ B'), α.IsSig p σ → α.IsSig p' σ' → (∀ y, ρ (σ y) = σ' (extHom R₁ φ y)) ∧ ∀ y, α.KerQ y → α.KerQ (extHom R₁ φ y) := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α B B₀ _ _ _ _ p hs hp hker B' B₀' _ _ _ _ p' hs' hp' hker' ρ φ hρ σ σ' hσ hσ'
  refine ⟨fun y => ?_, fun y hy => ?_⟩
  · induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul r b₀ =>
      obtain ⟨b, rfl⟩ := hp b₀
      rw [hσ r b]
      simp only [extHom, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      rw [← hρ b, hσ' r (ρ b), map_smul]
    | add x z hx hz => simp only [map_add (f := _), hx, hz]
  · have key : ∀ y : R₁ ⊗[R₀] B₀,
        Algebra.TensorProduct.map α.q (AlgHom.id R₀ B₀') (extHom R₁ φ y) =
          Algebra.TensorProduct.map (AlgHom.id R₀ R₀) φ (Algebra.TensorProduct.map α.q (AlgHom.id R₀ B₀) y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul r b₀ => simp [extHom]
      | add x z hx hz => simp only [map_add (f := _), hx, hz]
    unfold Aug.KerQ at hy ⊢
    rw [key, hy, map_zero]

end GlobalTheory.Obs
end

