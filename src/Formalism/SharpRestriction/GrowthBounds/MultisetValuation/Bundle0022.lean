module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0020
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.TwoSumsCondition
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EaRestSExpVOf

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.PriceBoundSmallPrimes
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

def PriceBoundLargePrimes (C₀ : ℝ) : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts),
    C₀ ≤ K.Pr1 → Formalism.MainNotions.SizesAt L →
    ∀ hT : GatTies D, Formalism.MainNotions.G.LatTied hT X Y → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      L.sc.p0 D.R.k ≤ ((D.what₂.places.resChar w : ℕ) : ℝ) →
      ∀ t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w), ∀ j ∈ SizeData₂.lifts D,
        Formalism.MainNotions.FormalGroupSystem.Pr (Y.Fl u w hg).t (D.gat u w hg).P.r ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
          ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j ≤
          Formalism.MainNotions.G.Pr X K (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j t0

def PriceBoundSmallPrimes : Prop :=
  ∀ (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts),
    (Formalism.MainNotions.G.rG L.sc < D.R.k ∧ 2 ≤ L.sc.x) → Formalism.MainNotions.SizesAt L →
    ∀ hT : GatTies D, Formalism.MainNotions.G.LatTied hT X Y → ∀ (u : D.what₂.Word) (w : D.what₂.places.Pl)
      (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      ((D.what₂.places.resChar w : ℕ) : ℝ) < L.sc.p0 D.R.k →
      ∀ t0 ∈ Formalism.MainNotions.G.reps X (D.what₂.places.resChar w), ∀ j ∈ SizeData₂.lifts D,
        Formalism.MainNotions.FormalGroupSystem.Pr (Y.Fl u w hg).t (D.gat u w hg).P.r ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0))
          ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j ≤
          Formalism.MainNotions.G.Pr X K (Formalism.MainNotions.G.bL L) (D.what₂.places.resChar w) j t0

theorem priceBound_of_largePrimes_of_smallPrimes (C₀ : ℝ) (h1 : PriceBoundLargePrimes C₀) (h2 : PriceBoundSmallPrimes) : PriceBound C₀ := by
  intro D L X Y K hK1 hK2 hS hT hL u w hg _ t0 ht0 j hj
  rcases le_or_gt (L.sc.p0 D.R.k) ((D.what₂.places.resChar w : ℕ) : ℝ) with h | h
  · exact h1 D L X Y K hK1 hS hT hL u w hg h t0 ht0 j hj
  · exact h2 D L X Y K hK2 hS hT hL u w hg h t0 ht0 j hj

variable {n' k1 : ℕ}

theorem ne_abs (t r j : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ)
    (A Bt : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ Bt)
    (h : ∀ s : Fin n', IsOddPos s → (r : ℝ) * w j s + ∑ a ∈ Icc (k1 + 2 - r) (k1 + 1), (lamI lam0 s a : ℝ) ≤
      A + (if s ∈ TT then Bt else 0)) :
    Pr t r lam0 w j ≤ n' * A + TT.card * Bt + (n' : ℝ) * r * j * (t + 1) / 2 := by
  unfold Pr
  have h1 : ∑ s ∈ univ.filter (fun s : Fin n' => IsOddPos s),
      ((r : ℝ) * w j s + ∑ a ∈ Icc (k1 + 2 - r) (k1 + 1), (lamI lam0 s a : ℝ)) ≤
      ∑ s ∈ univ.filter (fun s : Fin n' => IsOddPos s), (A + (if s ∈ TT then Bt else 0)) :=
    Finset.sum_le_sum fun s hs => h s (Finset.mem_filter.1 hs).2
  have h2 : ∑ s ∈ univ.filter (fun s : Fin n' => IsOddPos s), (A + (if s ∈ TT then Bt else 0)) ≤
      ∑ s : Fin n', (A + (if s ∈ TT then Bt else 0)) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun s _ _ => by split_ifs <;> linarith)
  have h3 : ∑ s : Fin n', (A + (if s ∈ TT then Bt else 0)) = n' * A + TT.card * Bt := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  linarith

theorem price_sum_single_edge (t j : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ)
    (A : ℝ) (E : Fin n' → ℝ) (hA : 0 ≤ A)
    (h : ∀ s : Fin n', IsOddPos s → ((1 : ℕ) : ℝ) * w j s + ∑ a ∈ Icc (k1 + 2 - 1) (k1 + 1), (lamI lam0 s a : ℝ) ≤
      if s ∈ TT then E s else A) :
    Pr t 1 lam0 w j ≤ ∑ s ∈ TT.filter IsOddPos, E s + n' * A + (n' : ℝ) * ((1 : ℕ) : ℝ) * j * (t + 1) / 2 := by
  unfold Pr
  have h1 : ∑ s ∈ univ.filter (fun s : Fin n' => IsOddPos s),
      (((1 : ℕ) : ℝ) * w j s + ∑ a ∈ Icc (k1 + 2 - 1) (k1 + 1), (lamI lam0 s a : ℝ)) ≤
      ∑ s ∈ univ.filter (fun s : Fin n' => IsOddPos s), (if s ∈ TT then E s else A) :=
    Finset.sum_le_sum fun s hs => h s (Finset.mem_filter.1 hs).2
  rw [Finset.sum_ite] at h1
  have e1 : (univ.filter (fun s : Fin n' => IsOddPos s)).filter (fun s => s ∈ TT) = TT.filter IsOddPos := by
    ext s; simp [and_comm]
  rw [e1, Finset.sum_const, nsmul_eq_mul] at h1
  have h2 : (((univ.filter (fun s : Fin n' => IsOddPos s)).filter (fun s => s ∉ TT)).card : ℝ) ≤ n' := by
    have := Finset.card_le_univ ((univ.filter (fun s : Fin n' => IsOddPos s)).filter (fun s => s ∉ TT))
    rw [Fintype.card_fin] at this
    exact_mod_cast this
  have h3 := mul_le_mul_of_nonneg_right h2 hA
  exact add_le_add (le_trans h1 (add_le_add le_rfl h3)) le_rfl

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.ThRestGcVOf
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset
open Formalism.InvariantFactorPaths.G7 (lgF lamF Gser)

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [hp : Fact p.Prime] (X : Sys p)

theorem th_GtV_eq (j : ℕ) (v : X.Pl) (c c' : K0 p) :
    ea_GtV X j v c c' = ren (Sum.map (Sigma.mk v) (Sigma.mk v))
      (Gt p (Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1))) c c') := by
  unfold ea_GtV Gt
  rw [th_ren_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [th_ren_ren]
  congr 1
  funext k
  fin_cases k <;> rfl

theorem th_restGcV_of (hG : RestGc p) : ea_RestGcV X := by
  intro c hc j v K' _ _ vp hvp μ hμ0 hμ
  have hs := X.std v
  obtain ⟨u, hu, V, hV, heq⟩ := hG hs.five_le c hc (X.G.P.n' v) (NN X.G.P.m X.t j)
    (NN X.G.P.m X.t (j + 1)) hs.two_le hs.even (X.om v) K' vp hvp μ hμ0 hμ
  let ρ : Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) → X.ZA j := fun z => ⟨v, z⟩
  refine ⟨u, hu, ren ρ V, th_IntR_ren ρ hV, ?_⟩
  have hT : MvPowerSeries.HasSubst (tOf vp μ (X.coordZA K' j)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero
      (th_tOf_const vp μ hμ0 _ (coordZA_const X K' j))
  have hT' : MvPowerSeries.HasSubst
      (tOf vp μ (coordZ (r0 := NN X.G.P.m X.t j) (r1 := NN X.G.P.m X.t (j + 1)) (X.om v) K' 1)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero
      (th_tOf_const vp μ hμ0 _ (coordZ_const (X.om v) K' 1))
  have hg : MvPowerSeries.constantCoeff
      (-(MvPowerSeries.map (algebraMap (K0 p) K'))
        (Gt p (Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)))
          (wK p c) (wK p ((sigW p) c)))) = 0 := by
    simp [th_Gt_const]
  have hh : MvPowerSeries.constantCoeff
      (-(MvPowerSeries.C (vp ^ (p + 1) / (p : K')) * hhS p K' u :
        MvPowerSeries (Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1))) K')) = 0 := by
    simp [hhS_const]
  have hfun : (fun k => tOf vp μ (X.coordZA K' j) (Sum.map (Sigma.mk v) (Sigma.mk v) k)) =
      fun k => ren ρ (tOf vp μ (coordZ (X.om v) K' 1) k) := by
    funext k
    simp only [tOf]
    rw [th_coordZA_eq, th_ren_psubst ρ (coordZ_const (X.om v) K' 1 k)]
  rw [th_GtV_eq, th_map_ren, ← th_ren_neg, ← th_ren_expK _ hg, th_subst_ren _ hT, hfun,
    ← th_ren_subst ρ hT', heq, th_ren_mul, th_ren_expK ρ hh, th_ren_neg, th_ren_mul, th_ren_C,
    th_hhA_eq]

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

