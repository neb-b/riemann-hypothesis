module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0024

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

theorem price_linear_combination_le (n N rr w2 η cg NM b1 jt : ℝ) (hn : 0 ≤ n) (hN : 0 ≤ N) (hr : 0 ≤ rr) (hcg : 0 ≤ cg) (hjt : jt ≤ NM) :
    n * (rr * (w2 + η + cg)) + N * (rr * (2 * b1)) + n * rr * jt ≤
      rr * (N * (2 * b1 + cg) + n * (w2 + η + cg + NM)) := by
  nlinarith [mul_nonneg (mul_nonneg hr hN) hcg, mul_nonneg (mul_nonneg hn hr) (sub_nonneg.mpr hjt)]

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

section Orbit

variable (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (hT : GatTies D) (hL : Formalism.MainNotions.G.LatTied hT X Y)
  (u : D.what₂.Word) (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
  (t0 : Formalism.MainNotions.G.HH D) (ht0 : t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w))

include hL ht0 in
theorem ne_b_top (hS : Formalism.MainNotions.SizesAt L) (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0)))
    (hs : s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0)) :
    L.sc.b' ≤ ((Y.Fl u w hg).b (Y.vOf u w hg t0) s : ℝ) ∧
      ((Y.Fl u w hg).b (Y.vOf u w hg t0) s : ℝ) ≤ 5 / 4 * L.sc.b' := by
  obtain ⟨_, h2, h3, _⟩ := ((hL u w hg).2.2.2.2.2.2 t0 ht0).2 s
  rw [(h3 hs).2]
  unfold Formalism.MainNotions.G.bL
  rw [dite_eq_left (h2.1 hs)]
  exact ⟨L.bT_ge _, ne_bT_le hS _⟩


end Orbit

def priceThreshold : ℝ := 9

theorem price_threshold_ge_nine : 9 ≤ priceThreshold := by norm_num [priceThreshold]


open Classical in
theorem price_bound_small_primes : PriceBoundSmallPrimes := by
  intro D L X Y K hK hS hT hL u w hg hp t0 ht0 j hj
  obtain ⟨hrk, hx2⟩ := hK
  have hr : (D.gat u w hg).P.r = Formalism.MainNotions.G.rG L.sc := by rw [(hL u w hg).2.2.2.1, if_pos hp]
  have ht : (Y.Fl u w hg).t = D.R.t := (hL u w hg).2.1
  have hc : ((Y.Fl u w hg).c : ℝ) ≤ Formalism.MainNotions.G.cG L := (hL u w hg).2.2.1
  have hinj := nc_iota_inj X Y hT hL u w hg t0 ht0
  have hm := nc_m_ge hT u w hg
  have hk := hT.gat_k u w hg
  have hno : ¬ ((D.gat u w hg).P.m + 1 ≤ Formalism.MainNotions.G.rG L.sc) := by omega
  have hr0 : (0 : ℝ) ≤ (Formalism.MainNotions.G.rG L.sc : ℝ) := Nat.cast_nonneg _
  have hw := ne_w''_nonneg (L := L)
  have hη := L.etaSz_pos
  have hcG := nc_cG_nonneg (L := L)
  have hb' := L.sc.b'_pos
  rw [hr]
  have h1 := ne_abs (Y.Fl u w hg).t (Formalism.MainNotions.G.rG L.sc) j ((Y.Fl u w hg).TT (Y.vOf u w hg t0))
    ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0)) ((Y.Fl u w hg).w (Y.vOf u w hg t0))
    ((Formalism.MainNotions.G.rG L.sc : ℝ) * (L.sc.w'' D.R.n + L.etaSz + Formalism.MainNotions.G.cG L))
    ((Formalism.MainNotions.G.rG L.sc : ℝ) * (2 * L.sc.b'))
    (by positivity) (by positivity)
    (fun s _ => by
      have hsum := ne_sum_le (Y.Fl u w hg) (Y.vOf u w hg t0) s (Formalism.MainNotions.G.rG L.sc) hm (fun hs => by
        have h0 := (ne_b_top X Y hT hL u w hg t0 ht0 hS s hs).1
        have : (0 : ℝ) ≤ ((Y.Fl u w hg).b (Y.vOf u w hg t0) s : ℝ) := by linarith
        exact_mod_cast this)
      rw [if_neg (fun h => hno h.2)] at hsum
      have h7 := mul_le_mul_of_nonneg_left hc hr0
      have h11 := mul_nonneg hr0 hw
      by_cases hs : s ∈ (Y.Fl u w hg).TT (Y.vOf u w hg t0)
      · rw [if_pos hs]
        have hwt := ne_w_top X Y hT hL u w hg t0 ht0 j hj s hs
        have hb := (ne_b_top X Y hT hL u w hg t0 ht0 hS s hs).2
        have hx : L.sc.b' / L.sc.x ≤ L.sc.b' / 2 := div_le_div_of_nonneg_left hb'.le (by norm_num) hx2
        have h5 := mul_le_mul_of_nonneg_left
          (show ((Y.Fl u w hg).w (Y.vOf u w hg t0) j s : ℝ) ≤ 2 * L.sc.b' + L.etaSz by linarith) hr0
        nlinarith [h5, h7, hsum, h11]
      · rw [if_neg hs]
        have hwn := ne_w_non X Y hT hL u w hg t0 ht0 j hj s hs
        have h5 := mul_le_mul_of_nonneg_left hwn hr0
        nlinarith [h5, h7, hsum])
  refine le_trans h1 ?_
  unfold Formalism.MainNotions.G.Pr Formalism.MainNotions.G.Nv
  rw [if_neg (not_le.2 hp), nc_topsOn X Y hT hL u w hg t0 ht0, Finset.card_image_of_injective _ hinj,
    ne_nP X Y hT hL u w hg t0 ht0, ht]
  have hN := ne_Nm (D := D) j hj
  have hfin := price_linear_combination_le ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) (((Y.Fl u w hg).TT (Y.vOf u w hg t0)).card : ℝ)
    (Formalism.MainNotions.G.rG L.sc : ℝ) (L.sc.w'' D.R.n) L.etaSz (Formalism.MainNotions.G.cG L) (Formalism.MainNotions.G.Nm D) L.sc.b'
    ((j : ℝ) * ((D.R.t : ℝ) + 1) / 2) (Nat.cast_nonneg _) (Nat.cast_nonneg _) hr0 hcG hN
  have e : ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) * (Formalism.MainNotions.G.rG L.sc : ℝ) * (j : ℝ) * ((D.R.t : ℝ) + 1) / 2 =
      ((D.gat u w hg).P.n' (Y.vOf u w hg t0) : ℝ) * (Formalism.MainNotions.G.rG L.sc : ℝ) * ((j : ℝ) * ((D.R.t : ℝ) + 1) / 2) := by ring
  rw [e]
  exact hfin

theorem priceBoundLargePrimes_priceThreshold : PriceBoundLargePrimes priceThreshold :=
  fun D L X Y K hK => price_bound_large_primes D L X Y K (by linarith [price_threshold_ge_nine])

theorem ne_priceThreshold : PriceBound priceThreshold :=
  priceBound_of_largePrimes_of_smallPrimes priceThreshold priceBoundLargePrimes_priceThreshold price_bound_small_primes

theorem numericalComparisonUniform_of_size (hS : nd_NeedSize) : Formalism.MainNotions.FormalGroupSystem.NumericalComparisonUniform :=
  numerical_closed_of_threshold priceThreshold price_threshold_ge_nine (nc_need3_of priceThreshold hS ne_priceThreshold)

end Formalism.MainNotions.FormalGroupSystem.Pf
