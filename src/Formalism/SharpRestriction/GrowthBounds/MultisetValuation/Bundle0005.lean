module

public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.Bundle0003
public import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.TheoremOfAlternateForm

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.NcSummableMin
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Finset

theorem nc_geom (p : ℕ) (hp : 2 ≤ p) :
    HasSum (fun e : ℕ => (((p : ℝ)) ^ (2 * e + 1))⁻¹) (Formalism.MainNotions.FormalGroupSystem.gam p) := by
  have hp' : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hq : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by nlinarith
  have hr : ((p : ℝ) ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by nlinarith)
  have h0 : 0 ≤ ((p : ℝ) ^ 2)⁻¹ := by positivity
  have := (hasSum_geometric_of_lt_one h0 hr).mul_left ((p : ℝ)⁻¹)
  have e1 : (fun e : ℕ => ((p : ℝ) ^ (2 * e + 1))⁻¹) = fun i : ℕ => (p : ℝ)⁻¹ * ((p : ℝ) ^ 2)⁻¹ ^ i := by
    funext e
    rw [pow_succ, pow_mul, mul_inv, inv_pow]
    ring
  have e2 : Formalism.MainNotions.FormalGroupSystem.gam p = (p : ℝ)⁻¹ * (1 - ((p : ℝ) ^ 2)⁻¹)⁻¹ := by
    rw [Formalism.MainNotions.FormalGroupSystem.gam]
    first
      | (field_simp; ring)
      | field_simp
  rw [e1, e2]
  exact this

theorem nc_geomc (p : ℕ) (hp : 2 ≤ p) (c : ℝ) :
    HasSum (fun e : ℕ => c / ((p : ℝ)) ^ (2 * e + 1)) (c * Formalism.MainNotions.FormalGroupSystem.gam p) := by
  have := (nc_geom p hp).mul_left c
  simpa [div_eq_mul_inv] using this

theorem nc_abs_min_le (a b : ℝ) (hb : 0 ≤ b) : |min a b| ≤ |a| := by
  rcases le_total a b with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, abs_of_nonneg hb, abs_of_nonneg (hb.trans h)]
    exact h

theorem nc_summable_min (p : ℕ) (hp : 2 ≤ p) (y : ℝ) (z : ℕ → ℝ) (hz : ∀ e, 0 ≤ z e) :
    Summable fun e : ℕ => min (y / ((p : ℝ)) ^ (2 * e + 1)) (z e) := by
  have hg : Summable (fun e : ℕ => |y| / ((p : ℝ)) ^ (2 * e + 1)) := (nc_geomc p hp |y|).summable
  have hb : ∀ e : ℕ, ‖min (y / ((p : ℝ)) ^ (2 * e + 1)) (z e)‖ ≤ |y| / ((p : ℝ)) ^ (2 * e + 1) := by
    intro e
    have hq : (0 : ℝ) < ((p : ℝ)) ^ (2 * e + 1) := by
      have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
      positivity
    rw [Real.norm_eq_abs]
    calc |min (y / ((p : ℝ)) ^ (2 * e + 1)) (z e)| ≤ |y / ((p : ℝ)) ^ (2 * e + 1)| := nc_abs_min_le _ _ (hz e)
      _ = |y| / ((p : ℝ)) ^ (2 * e + 1) := by rw [abs_div, abs_of_pos hq]
  first
    | exact Summable.of_norm_bounded hg hb
    | exact Summable.of_norm_bounded _ hg hb

theorem nc_min (p : ℕ) (hp : 2 ≤ p) (y yu : ℝ) (z zu : ℕ → ℝ) (hy : y ≤ yu) (hz : ∀ e, zu e ≤ z e)
    (hz0 : ∀ e, 0 ≤ zu e) :
    Formalism.MainNotions.FormalGroupSystem.gam p * y - ∑' e : ℕ, min (y / ((p : ℝ)) ^ (2 * e + 1)) (z e) ≤
      Formalism.MainNotions.FormalGroupSystem.gam p * yu - ∑' e : ℕ, min (yu / ((p : ℝ)) ^ (2 * e + 1)) (zu e) := by
  have hs1 := nc_geomc p hp y
  have hs2 := nc_geomc p hp yu
  have m1 := nc_summable_min p hp y z (fun e => (hz0 e).trans (hz e))
  have m2 := nc_summable_min p hp yu zu hz0
  rw [mul_comm (Formalism.MainNotions.FormalGroupSystem.gam p) y, mul_comm (Formalism.MainNotions.FormalGroupSystem.gam p) yu, ← hs1.tsum_eq, ← hs2.tsum_eq]
  rw [← hs1.summable.tsum_sub m1, ← hs2.summable.tsum_sub m2]
  refine (hs1.summable.sub m1).tsum_le_tsum (fun e => ?_) (hs2.summable.sub m2)
  have hq : (0 : ℝ) < ((p : ℝ)) ^ (2 * e + 1) := by
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
    positivity
  have ha : y / ((p : ℝ)) ^ (2 * e + 1) ≤ yu / ((p : ℝ)) ^ (2 * e + 1) := div_le_div_of_nonneg_right hy hq.le
  have hze := hz e
  simp only [Pi.sub_apply, min_def]
  split_ifs <;> linarith

theorem nc_pos (p : ℕ) (hp : 2 ≤ p) (y yu : ℝ) (z zu : ℕ → ℝ) (ex exu : ℕ → Prop) [DecidablePred ex]
    [DecidablePred exu] (hy : y ≤ yu) (hyu : 0 ≤ yu) (hz : ∀ e, zu e ≤ z e) (hz0 : ∀ e, 0 ≤ zu e)
    (hex : ∀ e, exu e → ex e) :
    ∑' e : ℕ, (if ex e then 0 else max 0 (y / ((p : ℝ)) ^ (2 * e + 1) - z e)) ≤
      ∑' e : ℕ, (if exu e then 0 else max (yu / ((p : ℝ)) ^ (2 * e + 1) - zu e) 0) := by
  have hq : ∀ e : ℕ, (0 : ℝ) < ((p : ℝ)) ^ (2 * e + 1) := by
    intro e
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
    positivity
  have hS := (nc_geomc p hp yu).summable
  have hR : Summable (fun e : ℕ => if exu e then 0 else max (yu / ((p : ℝ)) ^ (2 * e + 1) - zu e) 0) := by
    refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) hS
    · split_ifs
      · exact le_rfl
      · exact le_max_right _ _
    · have h1 : 0 ≤ yu / ((p : ℝ)) ^ (2 * e + 1) := div_nonneg hyu (hq e).le
      have h2 := hz0 e
      split_ifs
      · exact h1
      · exact max_le (by linarith) h1
  have hLs : Summable (fun e : ℕ => if ex e then 0 else max 0 (y / ((p : ℝ)) ^ (2 * e + 1) - z e)) := by
    refine Summable.of_nonneg_of_le (fun e => ?_) (fun e => ?_) hS
    · split_ifs
      · exact le_rfl
      · exact le_max_left _ _
    · have h1 : 0 ≤ yu / ((p : ℝ)) ^ (2 * e + 1) := div_nonneg hyu (hq e).le
      have h3 : y / ((p : ℝ)) ^ (2 * e + 1) ≤ yu / ((p : ℝ)) ^ (2 * e + 1) := div_le_div_of_nonneg_right hy (hq e).le
      have h2 := hz0 e
      have h4 := hz e
      split_ifs
      · exact h1
      · exact max_le h1 (by linarith)
  refine hLs.tsum_le_tsum (fun e => ?_) hR
  have h3 : y / ((p : ℝ)) ^ (2 * e + 1) ≤ yu / ((p : ℝ)) ^ (2 * e + 1) := div_le_div_of_nonneg_right hy (hq e).le
  have h4 := hz e
  by_cases he : ex e
  · rw [if_pos he]
    split_ifs
    · exact le_rfl
    · exact le_max_right _ _
  · have heu : ¬ exu e := fun h => he (hex e h)
    rw [if_neg he, if_neg heu]
    exact max_le (le_max_right _ _) (le_trans (by linarith) (le_max_left _ _))

variable {n' k1 : ℕ}

theorem nc_gB_ge (p t : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (j : ℕ)
    (hp : 2 ≤ p) (ya zc : Fin n' → ℝ) (dlv : ℝ) (h1 : ∀ s ∈ TT, ya s ≤ al TT lam0 s)
    (h2 : ∀ s, (cap t TT lam0 w j s : ℝ) ≤ zc s) (h3 : ∀ s, 0 ≤ cap t TT lam0 w j s)
    (hd : de p t TT lam0 w j ≤ dlv) :
    Formalism.MainNotions.FormalGroupSystem.gam p * ∑ s ∈ TT, ya s -
              ∑ s ∈ TT.filter IsOddPos, ∑' e : ℕ,
                min (ya s / ((p : ℝ)) ^ (2 * e + 1)) (zc (Formalism.MainNotions.G.posAdd s (2 * e + 1))) - dlv ≤
      gB p t TT lam0 w j := by
  unfold gB
  have hg0 : 0 ≤ Formalism.MainNotions.FormalGroupSystem.gam p := (nc_geom p hp).nonneg fun e => by positivity
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not TT IsOddPos,
    ← Finset.sum_filter_add_sum_filter_not TT IsOddPos (fun s => Formalism.MainNotions.FormalGroupSystem.gam p * (al TT lam0 s : ℝ))]
  have hA : ∑ s ∈ TT.filter IsOddPos, (Formalism.MainNotions.FormalGroupSystem.gam p * ya s - ∑' e : ℕ,
        min (ya s / ((p : ℝ)) ^ (2 * e + 1)) (zc (Formalism.MainNotions.G.posAdd s (2 * e + 1)))) ≤
      ∑ s ∈ TT.filter IsOddPos, (Formalism.MainNotions.FormalGroupSystem.gam p * (al TT lam0 s : ℝ) - ∑' e : ℕ,
        min ((al TT lam0 s : ℝ) / ((p : ℝ)) ^ (2 * e + 1)) (cap t TT lam0 w j (Formalism.MainNotions.G.posAdd s (2 * e + 1)) : ℝ)) := by
    apply Finset.sum_le_sum
    intro s hs
    exact nc_min p hp _ _ _ _ (h1 s (Finset.mem_filter.1 hs).1) (fun e => h2 _) (fun e => by exact_mod_cast h3 _)
  have hB : ∑ s ∈ TT.filter (fun s => ¬ IsOddPos s), Formalism.MainNotions.FormalGroupSystem.gam p * ya s ≤
      ∑ s ∈ TT.filter (fun s => ¬ IsOddPos s), Formalism.MainNotions.FormalGroupSystem.gam p * (al TT lam0 s : ℝ) := by
    apply Finset.sum_le_sum
    intro s hs
    exact mul_le_mul_of_nonneg_left (h1 s (Finset.mem_filter.1 hs).1) hg0
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hA
  linarith

theorem nc_gA_ge (p t : ℕ) (TT : Finset (Fin n')) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (j : ℕ)
    (hp : 2 ≤ p) (ya zc : Fin n' → ℝ) (dlv : ℝ) (ex : Fin n' → ℕ → Prop) [∀ s, DecidablePred (ex s)]
    (h1 : ∀ s ∈ TT, ya s ≤ al TT lam0 s) (h0 : ∀ s, 0 ≤ al TT lam0 s)
    (h2 : ∀ s, (cap t TT lam0 w j s : ℝ) ≤ zc s) (h3 : ∀ s, 0 ≤ cap t TT lam0 w j s)
    (hex : ∀ s ∈ TT, ∀ e, 2 * e + 1 ∈ dSet TT s → ex s e)
    (hd : de p t TT lam0 w j ≤ dlv) :
    ∑ s ∈ TT, ∑' e : ℕ, (if ex s e then 0 else
        max 0 (ya s / ((p : ℝ)) ^ (2 * e + 1) - zc (Formalism.MainNotions.G.posAdd s (2 * e + 1)))) - dlv ≤
      gA p t TT lam0 w j := by
  unfold gA
  have hA : ∑ s ∈ TT, ∑' e : ℕ, (if ex s e then 0 else
        max 0 (ya s / ((p : ℝ)) ^ (2 * e + 1) - zc (Formalism.MainNotions.G.posAdd s (2 * e + 1)))) ≤
      ∑ s ∈ TT, ∑' e : ℕ, (if 2 * e + 1 ∈ dSet TT s then 0 else
        max ((al TT lam0 s : ℝ) / (p : ℝ) ^ (2 * e + 1) -
          (cap t TT lam0 w j (Formalism.MainNotions.G.posAdd s (2 * e + 1)) : ℝ)) 0) := by
    apply Finset.sum_le_sum
    intro s hs
    exact nc_pos p hp _ _ _ _ (ex s) (fun e => 2 * e + 1 ∈ dSet TT s) (h1 s hs) (by exact_mod_cast h0 s)
      (fun e => h2 _) (fun e => by exact_mod_cast h3 _) (hex s hs)
  linarith

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MultisetValuation.RamifiedLatticeOfChainEstimates
section
noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X)

def EntCondition : Prop :=
  ∀ j < X.mm, ∀ (i0 : X.Pl → ℕ) (gP : X.Pl → ℚ), (∀ v, PlaceB X Y j v (i0 v) (gP v)) →
    EntB X Y j i0 (∑ v, (gP v : ℝ))

def RatCondition : Prop := ∀ v j, ∃ q : ℚ, X.g0v v j = q

def HeckeIntegralLevel : Prop :=
  ∀ v, ∀ j < X.mm, ∀ i ∈ Icc 1 X.G.P.r, ∀ F ∈ X.Int (j + 1), X.Tt v i (j + 1) F ∈ X.Int (j + 1)

theorem sum_ite_single {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι) (a : ℝ) (f : ι → ℝ) :
    ∑ v', (if v' = v then a else f v') = a + ∑ v' ∈ univ.erase v, f v' := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v), if_pos rfl]
  congr 1
  refine Finset.sum_congr rfl fun v' hv' => ?_
  rw [if_neg (Finset.ne_of_mem_erase hv')]

variable {X Y}

theorem PlaceB.mono {j : ℕ} {v : X.Pl} {i : ℕ} {g g' : ℝ} (h : g' ≤ g) (hP : PlaceB X Y j v i g) :
    PlaceB X Y j v i g' := by
  unfold PlaceB at *
  rcases hP with ⟨hi, hL | hL⟩ | ⟨h1, h2, h3⟩
  · exact Or.inl ⟨hi, Or.inl (Pend.LowAt.mono Y h hL)⟩
  · exact Or.inl ⟨hi, Or.inr (h.trans hL)⟩
  · exact Or.inr ⟨h1, h2, h.trans h3⟩

theorem EntB.mono {j : ℕ} {i0 : X.Pl → ℕ} {g g' : ℝ} (h : g' ≤ g) (hB : EntB X Y j i0 g) : EntB X Y j i0 g' := by
  unfold EntB at *
  intro La La' h1 h2 φ I n
  exact Pend.geC_mono Y h (hB La La' h1 h2 φ I n)

theorem ent_strict (hE : EntCondition X Y) (j : ℕ) (hj : j < X.mm) (i0 : X.Pl → ℕ) (gP : X.Pl → ℝ)
    (hP : ∀ v, PlaceB X Y j v (i0 v) (gP v)) (g' : ℝ) (hg : g' < ∑ v, gP v) : EntB X Y j i0 g' := by
  classical
  have hD : 0 < ∑ v, gP v - g' := sub_pos.mpr hg
  have hc : (0 : ℝ) < Fintype.card X.Pl + 1 := by positivity
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (∑ v, gP v - g') / (Fintype.card X.Pl + 1) := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; exact div_pos hD hc
  have hεc : (Fintype.card X.Pl : ℝ) * ε < ∑ v, gP v - g' := by
    have h1 : ε * (Fintype.card X.Pl + 1) = ∑ v, gP v - g' := by
      rw [hε]; exact div_mul_cancel₀ _ hc.ne'
    nlinarith
  have hq : ∀ v, ∃ q : ℚ, gP v - ε < q ∧ (q : ℝ) < gP v := fun v => exists_rat_btwn (by linarith)
  choose q hq1 hq2 using hq
  have hsum : g' ≤ ∑ v, (q v : ℝ) := by
    have h1 : ∑ v, (gP v - ε) ≤ ∑ v, (q v : ℝ) := Finset.sum_le_sum fun v _ => (hq1 v).le
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
    linarith
  exact EntB.mono hsum (hE j hj i0 q fun v => PlaceB.mono (hq2 v).le (hP v))

theorem formB_lim (hF : FormB X Y) (j : ℕ) (hj : j < X.mm) (i0 : X.Pl → ℕ) (vs : List X.Pl) (g : ℝ) (hnd : vs.Nodup)
    (hr : ∀ v, i0 v ≤ X.G.P.r) (h0 : ∀ v, v ∉ vs → i0 v = 0) (hB : ∀ g' < g, EntB X Y j i0 g')
    (G : X.Fm j) (hG : G ∈ X.Int j) : X.vGe (j + 1) (TtL X (j + 1) i0 vs (X.Kz j G)) (g - X.dG j) := by
  have he0 : (0 : ℝ) ≤ (X.eO : ℝ) := Nat.cast_nonneg _
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (g - X.dG j) * (X.eO : ℝ) := ⟨_, rfl⟩
  have hc1 : (⌈x⌉ : ℝ) < x + 1 := Int.ceil_lt_add_one x
  have hc2 : x ≤ (⌈x⌉ : ℝ) := Int.le_ceil x
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (x - ⌈x⌉ + 1) / ((X.eO : ℝ) + 1) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact div_pos (by linarith) (by linarith)
  have hδe : δ * (X.eO : ℝ) < x - ⌈x⌉ + 1 := by
    have h1 : δ * ((X.eO : ℝ) + 1) = x - ⌈x⌉ + 1 := by
      rw [hδ]; exact div_mul_cancel₀ _ (by linarith)
    nlinarith
  have hlin : (g - δ - X.dG j) * (X.eO : ℝ) = x - δ * (X.eO : ℝ) := by rw [hx]; ring
  have hceil : ⌈(g - δ - X.dG j) * (X.eO : ℝ)⌉ = ⌈(g - X.dG j) * (X.eO : ℝ)⌉ := by
    rw [← hx, Int.ceil_eq_iff, hlin]
    constructor
    · linarith
    · nlinarith
  have h := hF j hj i0 vs (g - δ) hnd hr h0 (hB _ (by linarith)) G hG
  have hv : X.vsc (g - δ - X.dG j) = X.vsc (g - X.dG j) := by rw [vsc_def, vsc_def, hceil]
  unfold Sys.vGe at h ⊢
  rw [hv] at h
  exact h

theorem form_of_place (hF : FormB X Y) (hE : EntCondition X Y) (j : ℕ) (hj : j < X.mm) (i0 : X.Pl → ℕ) (vs : List X.Pl)
    (gP : X.Pl → ℝ) (hnd : vs.Nodup) (hr : ∀ v, i0 v ≤ X.G.P.r) (h0 : ∀ v, v ∉ vs → i0 v = 0)
    (hP : ∀ v, PlaceB X Y j v (i0 v) (gP v)) (G : X.Fm j) (hG : G ∈ X.Int j) :
    X.vGe (j + 1) (TtL X (j + 1) i0 vs (X.Kz j G)) (∑ v, gP v - X.dG j) :=
  formB_lim hF j hj i0 vs (∑ v, gP v) hnd hr h0 (fun g' hg' => ent_strict hE j hj i0 gP hP g' hg') G hG

theorem form_valuation_of_bound (D : Formalism.BasicNotions.D7) (hF : FormB X Y) (h3 : adm3 D X Y) : Conclusion0 D X := by
  unfold Conclusion0
  intro j hj G hG
  have h := hF j hj (fun _ => 0) [] 0 List.nodup_nil (fun _ => Nat.zero_le _) (fun _ _ => rfl)
    (fun La La' h1 h2 φ I n => h3 j hj La La' h1 h2 φ I n) G hG
  rw [zero_sub] at h
  exact h

theorem theorem_A_entries_of_corollary (D : Formalism.BasicNotions.D7) (hE : EntCondition X Y) (hQ : RatCondition X) (h2U : VolumeRatio₂ D X Y) : projection_lemma_base_level D X Y := by
  unfold projection_lemma_base_level
  intro j hj La La' h1 h2 φ I n
  choose q hq using hQ
  have hP : ∀ v, PlaceB X Y j v 0 (q v (j + 1)) := fun v =>
    Or.inl ⟨rfl, Or.inl (by rw [← hq v (j + 1)]; exact h2U v j hj)⟩
  have h := hE j hj (fun _ => 0) (fun v => q v (j + 1)) hP La La' h1 h2 φ I n
  have hs : ∑ v, X.g0v v (j + 1) = ∑ v, ((q v (j + 1) : ℚ) : ℝ) :=
    Finset.sum_congr rfl fun v _ => hq v (j + 1)
  rw [hs]
  exact h

theorem slopeEstimate_of_lemmaB_slopeLine (D : Formalism.BasicNotions.D7) (hF : FormB X Y) (hE : EntCondition X Y) (h2U : VolumeRatio₂ D X Y) : Conclusion2 D X := by
  unfold Conclusion2
  intro j hj G hG
  exact form_of_place hF hE j hj (fun _ => 0) [] (fun v => X.g0v v (j + 1)) List.nodup_nil
    (fun _ => Nat.zero_le _) (fun _ _ => rfl) (fun v => Or.inl ⟨rfl, Or.inl (h2U v j hj)⟩) G hG

theorem hecke_integral_of_forms (D : Formalism.BasicNotions.D7) (hF : FormB X Y) (hE : EntCondition X Y) (h2U : VolumeRatio₂ D X Y) : MassRatio₂ D X := by
  classical
  unfold MassRatio₂
  intro v j hj G hG
  have hP : ∀ v', PlaceB X Y j v' 0
      (if v' = v then X.gv v (j + 1) - X.alEven v else X.g0v v' (j + 1)) := by
    intro v'
    by_cases hv : v' = v
    · subst hv
      rw [if_pos rfl]
      exact Or.inl ⟨rfl, Or.inr le_rfl⟩
    · rw [if_neg hv]
      exact Or.inl ⟨rfl, Or.inl (h2U v' j hj)⟩
  have h := form_of_place hF hE j hj (fun _ => 0) []
    (fun v' => if v' = v then X.gv v (j + 1) - X.alEven v else X.g0v v' (j + 1)) List.nodup_nil
    (fun _ => Nat.zero_le _) (fun _ _ => rfl) hP G hG
  beta_reduce at h
  rw [sum_ite_single] at h
  exact h

theorem hecke_valuation_of_entries (D : Formalism.BasicNotions.D7) (hF : FormB X Y) (hE : EntCondition X Y) (h2U : VolumeRatio₂ D X Y) (v : X.Pl) (j : ℕ)
    (hj : j < X.mm) (i : ℕ) (hi : i ∈ Icc 1 X.G.P.r) (G : X.Fm j) (hG : G ∈ X.Int j) :
    X.vGe (j + 1) (X.Tt v i (j + 1) (X.Kz j G))
      (X.gv v (j + 1) + ∑ v' ∈ univ.erase v, X.g0v v' (j + 1) - X.dG j) := by
  classical
  obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
  have hP : ∀ v', PlaceB X Y j v' (if v' = v then i else 0)
      (if v' = v then X.gv v (j + 1) else X.g0v v' (j + 1)) := by
    intro v'
    by_cases hv : v' = v
    · subst hv
      rw [if_pos rfl, if_pos rfl]
      exact Or.inr ⟨hi1, hi2, le_rfl⟩
    · rw [if_neg hv, if_neg hv]
      exact Or.inl ⟨rfl, Or.inl (h2U v' j hj)⟩
  have h := form_of_place hF hE j hj (fun v' => if v' = v then i else 0) [v]
    (fun v' => if v' = v then X.gv v (j + 1) else X.g0v v' (j + 1)) (List.nodup_singleton v)
    (fun v' => by split_ifs <;> omega)
    (fun v' hv' => if_neg (by simpa using hv')) hP G hG
  beta_reduce at h
  rw [sum_ite_single] at h
  simpa only [TtL, List.foldr_cons, List.foldr_nil, eq_self_iff_true, if_true, ↓reduceIte] using h

theorem latticeChain_succ_of_partial (D : Formalism.BasicNotions.D7) (hF : FormB X Y) (hE : EntCondition X Y) (h2U : VolumeRatio₂ D X Y) (hB1 : HeckeIntegralLevel X) :
    PointsLemma D X := fun v j hj =>
  ⟨fun i hi F hF' => hB1 v j hj i hi F hF', fun i hi G hG => hecke_valuation_of_entries D hF hE h2U v j hj i hi G hG⟩

theorem ramifiedLattice_of_chain_estimates (D : Formalism.BasicNotions.D7) (h2U : VolumeRatio₂ D X Y) (h5D : LowTermBound D X Y) : Conclusion5 D X := by
  unfold Conclusion5
  refine ⟨fun v => relative_presentation_of_d7 D _ _ _ _ _ _ _ _ _ _ _ _ (X.std v), fun VV F hF => ?_⟩
  exact h5D X.gv X.g0v X.Conclusion₂ X.Svv VV (fun _ _ _ _ => le_rfl) h2U (fun _ _ _ _ => le_rfl)
    (fun _ _ => le_rfl) F hF

end Formalism.MainNotions.FormalGroupSystem.Pf
end
end

