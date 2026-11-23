module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0012

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsDyadicShellIndex
section
open Finset

namespace GlobalTheory

theorem exists_dyadic_shell_index (ep : ℝ) (hep : 0 < ep) :
    ∃ sh : ℝ → ℕ, (∀ s, s ≤ 2 ^ sh s * ep) ∧ ∀ s j, j < sh s → 2 ^ j * ep < s := by
  classical
  have hex : ∀ s : ℝ, ∃ n : ℕ, s ≤ 2 ^ n * ep := by
    intro s
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (s / ep) (by norm_num : (1 : ℝ) < 2)
    refine ⟨n, ?_⟩
    rw [div_lt_iff₀ hep] at hn
    exact hn.le
  refine ⟨fun s => Nat.find (hex s), fun s => Nat.find_spec (hex s), fun s j hj => ?_⟩
  exact not_le.mp (Nat.find_min (hex s) hj)

theorem sum_prod_box_erase_zero (ι : Type) [Fintype ι] [DecidableEq ι] (W : ℕ → ℝ) (N : ℕ) :
    ∑ k ∈ (Fintype.piFinset (fun _ : ι => range (N + 1))).erase (fun _ => 0), ∏ v, W (k v)
      = (W 0 + ∑ i ∈ range N, W (i + 1)) ^ Fintype.card ι - W 0 ^ Fintype.card ι := by
  classical
  have hz : (fun _ : ι => (0 : ℕ)) ∈ Fintype.piFinset (fun _ : ι => range (N + 1)) := by
    simp [Fintype.mem_piFinset]
  rw [Finset.sum_erase_eq_sub hz,
    ← Finset.prod_univ_sum (fun _ : ι => range (N + 1)) (fun _ j => W j),
    Finset.prod_const, Finset.prod_const, Finset.card_univ, Finset.sum_range_succ', add_comm]

theorem sum_over_dyadic_shells :
    ∀ (Γ ι : Type) [Fintype ι] (d : Γ → ι → ℝ) (w : Γ → ℝ) (A κ h ep c : ℝ), 0 ≤ A → 0 ≤ κ → 0 < ep → 0 < c → ep ≤ 1 / c → κ * ep ≤ Real.log 2 → 32 * κ ≤ h * ep → 1 ≤ h * ep ^ 2 / 16 → (∀ γ v, 0 ≤ d γ v) → (∀ r : ι → ℝ, (∀ v, 0 ≤ r v) → {γ | ∀ v, d γ v ≤ r v}.Finite ∧ (({γ | ∀ v, d γ v ≤ r v}.ncard : ℕ) : ℝ) ≤ A * Real.exp (κ * ∑ v, r v)) → (∀ γ, ∃ v, ep < d γ v) → (∀ γ, 0 ≤ w γ ∧ w γ ≤ ∏ v, Real.exp (-(h / 8) * min (d γ v ^ 2) (d γ v / c))) → Summable w ∧ ∑' γ, w γ ≤ A * (2 * Fintype.card ι * 3 ^ Fintype.card ι * Real.exp (-(h * ep ^ 2 / 16))) := by
  intro Γ ι _ d w A κ h ep c hA hκ hep hc hepc hκep hh hT hd hcount hfar hw
  classical
  obtain ⟨sh, hsh1, hsh2⟩ := exists_dyadic_shell_index ep hep
  obtain ⟨hineq, -, hpow⟩ := shell_sum_elementary_inequalities
  set T : ℝ := h * ep ^ 2 / 16 with hTdef
  have hhpos : 0 < h := by
    by_contra hneg
    replace hneg := not_lt.mp hneg
    have h1 : h * ep ^ 2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hneg (sq_nonneg ep)
    linarith
  have hκT : κ * ep ≤ T / 2 := by
    have h1 : 32 * κ * ep ≤ h * ep * ep := mul_le_mul_of_nonneg_right hh hep.le
    rw [hTdef]
    nlinarith

  let F : ℕ → ℝ := fun j => if j = 0 then 1 else Real.exp (-T * 2 ^ j)
  let W : ℕ → ℝ := fun j => Real.exp (κ * (2 ^ j * ep)) * F j
  let K : Γ → ι → ℕ := fun γ v => sh (d γ v)
  have hF0 : ∀ j, 0 ≤ F j := by
    intro j
    simp only [F]
    split_ifs
    · exact zero_le_one
    · exact (Real.exp_pos _).le
  have hW0 : ∀ j, 0 ≤ W j := fun j => mul_nonneg (Real.exp_pos _).le (hF0 j)

  have hwF : ∀ γ, w γ ≤ ∏ v, F (K γ v) := by
    intro γ
    refine (hw γ).2.trans (Finset.prod_le_prod₀ (fun v _ => (Real.exp_pos _).le) (fun v _ => ?_))
    have hmin0 : 0 ≤ min (d γ v ^ 2) (d γ v / c) := le_min (sq_nonneg _) (div_nonneg (hd γ v) hc.le)
    simp only [F, K]
    split_ifs with hk
    · rw [Real.exp_le_one_iff]
      nlinarith
    · rw [Real.exp_le_exp]
      have hlt : sh (d γ v) - 1 < sh (d γ v) := Nat.sub_lt (Nat.pos_of_ne_zero hk) one_pos
      have hbig := hsh2 (d γ v) _ hlt
      have hp1 : (1 : ℝ) ≤ 2 ^ (sh (d γ v) - 1) := one_le_pow₀ (by norm_num)
      have hge : ep ≤ d γ v := by nlinarith
      have hm := hineq (d γ v) ep c hep hge hc hepc
      have h2 : (2 : ℝ) ^ sh (d γ v) = 2 * 2 ^ (sh (d γ v) - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      have hm2 : ep ^ 2 * 2 ^ (sh (d γ v) - 1) ≤ min (d γ v ^ 2) (d γ v / c) := by
        have : ep * (2 ^ (sh (d γ v) - 1) * ep) ≤ ep * d γ v :=
          mul_le_mul_of_nonneg_left hbig.le hep.le
        nlinarith
      have hm3 := mul_le_mul_of_nonneg_left hm2 hhpos.le
      rw [h2, hTdef]
      nlinarith

  have hfib : ∀ (u : Finset Γ) (k : ι → ℕ),
      ((u.filter fun γ => K γ = k).card : ℝ) ≤ A * ∏ v, Real.exp (κ * (2 ^ k v * ep)) := by
    intro u k
    have hr : ∀ v, 0 ≤ (2 : ℝ) ^ k v * ep := fun v => mul_nonneg (pow_nonneg (by norm_num) _) hep.le
    obtain ⟨hfin, hcard⟩ := hcount (fun v => 2 ^ k v * ep) hr
    have hsub : ((u.filter fun γ => K γ = k : Finset Γ) : Set Γ) ⊆ {γ | ∀ v, d γ v ≤ 2 ^ k v * ep} := by
      intro γ hγ
      have hγ' := Finset.mem_filter.mp (Finset.mem_coe.mp hγ)
      intro v
      have := hsh1 (d γ v)
      rw [← hγ'.2]
      exact this
    have hle := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_coe_finset] at hle
    calc ((u.filter fun γ => K γ = k).card : ℝ)
        ≤ (({γ | ∀ v, d γ v ≤ 2 ^ k v * ep}.ncard : ℕ) : ℝ) := by exact_mod_cast hle
      _ ≤ A * Real.exp (κ * ∑ v, 2 ^ k v * ep) := hcard
      _ = A * ∏ v, Real.exp (κ * (2 ^ k v * ep)) := by
        rw [Finset.mul_sum, Real.exp_sum]

  have hpart : ∀ u : Finset Γ, ∑ γ ∈ u, w γ
      ≤ A * (2 * Fintype.card ι * 3 ^ Fintype.card ι * Real.exp (-(h * ep ^ 2 / 16))) := by
    intro u
    set N : ℕ := u.sup fun γ => Finset.univ.sup (K γ) with hN
    set B := (Fintype.piFinset fun _ : ι => range (N + 1)).erase (fun _ => 0) with hB
    have hmaps : ∀ γ ∈ u, K γ ∈ B := by
      intro γ hγ
      rw [hB, Finset.mem_erase, Fintype.mem_piFinset]
      refine ⟨?_, fun v => ?_⟩
      · intro h0
        obtain ⟨v, hv⟩ := hfar γ
        have h1 : K γ v = 0 := congrFun h0 v
        have h2 := hsh1 (d γ v)
        simp only [K] at h1
        rw [h1, pow_zero, one_mul] at h2
        linarith
      · rw [Finset.mem_range, Nat.lt_succ_iff]
        exact (Finset.le_sup (f := K γ) (Finset.mem_univ v)).trans
          (Finset.le_sup (f := fun γ => Finset.univ.sup (K γ)) hγ)
    have hal0 : 0 ≤ W 0 := hW0 0
    have hal2 : W 0 ≤ 2 := by
      show Real.exp (κ * (2 ^ 0 * ep)) * (if (0 : ℕ) = 0 then 1 else Real.exp (-T * 2 ^ 0)) ≤ 2
      rw [if_pos rfl, pow_zero, one_mul, mul_one]
      calc Real.exp (κ * ep) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hκep
        _ = 2 := Real.exp_log (by norm_num)
    have hT1 : 1 ≤ T := hT
    have hWs : ∀ i, W (i + 1) ≤ Real.exp (-T) * (1 / 2 : ℝ) ^ i := by
      intro i
      refine le_trans ?_ (exp_neg_mul_two_pow_le_geometric T hT1 i)
      simp only [W, F, if_neg (Nat.succ_ne_zero i)]
      rw [← Real.exp_add, Real.exp_le_exp, pow_succ]
      have hp : (0 : ℝ) ≤ 2 ^ i := pow_nonneg (by norm_num) _
      nlinarith
    have hexpT : Real.exp (-T) ≤ 1 / 2 := by
      have h1 : Real.exp (-T) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
      have h2 : (1 : ℝ) + 1 ≤ Real.exp 1 := Real.add_one_le_exp 1
      have h3 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
      have h4 : 0 < Real.exp (-1) := Real.exp_pos _
      nlinarith
    have hbe : ∑ i ∈ range N, W (i + 1) ≤ 2 * Real.exp (-T) := by
      calc ∑ i ∈ range N, W (i + 1) ≤ ∑ i ∈ range N, Real.exp (-T) * (1 / 2 : ℝ) ^ i :=
            Finset.sum_le_sum fun i _ => hWs i
        _ = Real.exp (-T) * ∑ i ∈ range N, (1 / 2 : ℝ) ^ i := by rw [Finset.mul_sum]
        _ ≤ Real.exp (-T) * 2 :=
            mul_le_mul_of_nonneg_left (sum_geometric_two_le N) (Real.exp_pos _).le
        _ = 2 * Real.exp (-T) := mul_comm _ _
    have hbe0 : 0 ≤ ∑ i ∈ range N, W (i + 1) := Finset.sum_nonneg fun i _ => hW0 _
    have hbe1 : ∑ i ∈ range N, W (i + 1) ≤ 1 := by linarith
    have hbox := sum_prod_box_erase_zero ι W N
    have key := hpow (W 0) (∑ i ∈ range N, W (i + 1)) (Fintype.card ι) hal0 hal2 hbe0 hbe1
    calc ∑ γ ∈ u, w γ ≤ ∑ γ ∈ u, ∏ v, F (K γ v) := Finset.sum_le_sum fun γ _ => hwF γ
      _ = ∑ k ∈ B, ∑ γ ∈ u with K γ = k, ∏ v, F (k v) :=
          (Finset.sum_fiberwise_of_maps_to' hmaps (fun k => ∏ v, F (k v))).symm
      _ = ∑ k ∈ B, ((u.filter fun γ => K γ = k).card : ℝ) * ∏ v, F (k v) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ k ∈ B, (A * ∏ v, Real.exp (κ * (2 ^ k v * ep))) * ∏ v, F (k v) :=
          Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_right (hfib u k) (Finset.prod_nonneg fun v _ => hF0 _)
      _ = A * ∑ k ∈ B, ∏ v, W (k v) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [mul_assoc, ← Finset.prod_mul_distrib]
      _ = A * ((W 0 + ∑ i ∈ range N, W (i + 1)) ^ Fintype.card ι - W 0 ^ Fintype.card ι) := by
          rw [hB, hbox]
      _ ≤ A * (Fintype.card ι * (2 * Real.exp (-T)) * 3 ^ Fintype.card ι) := by
          refine mul_le_mul_of_nonneg_left (key.trans ?_) hA
          have h3 : (0 : ℝ) ≤ 3 ^ Fintype.card ι := pow_nonneg (by norm_num) _
          have hn : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbe hn) h3
      _ = A * (2 * Fintype.card ι * 3 ^ Fintype.card ι * Real.exp (-(h * ep ^ 2 / 16))) := by
          rw [hTdef]
          ring
  have hw0 : 0 ≤ w := fun γ => (hw γ).1
  exact ⟨summable_of_sum_le hw0 hpart, Real.tsum_le_of_sum_le hw0 hpart⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HenselStepCardComap
section
open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory

theorem henselStep_card_comap {W T : Type} [AddCommGroup W] [AddCommGroup T]
    (T1 T2 : AddSubgroup T) (h21 : T2 ≤ T1) (d : W →+ T) (hd1 : ∀ w, d w ∈ T1)
    (hd2 : ∀ t ∈ T1, ∃ w, d w - t ∈ T2) :
    Nat.card (T2.comap d) * Nat.card T1 = Nat.card W * Nat.card T2 := by
  have hsup : d.range ⊔ T2 = T1 := by
    apply le_antisymm
    · refine sup_le ?_ h21
      rintro _ ⟨w, rfl⟩
      exact hd1 w
    · intro t ht
      obtain ⟨w, hw⟩ := hd2 t ht
      have : t = d w + -(d w - t) := by abel
      rw [this]
      exact AddSubgroup.add_mem_sup ⟨w, rfl⟩ (T2.neg_mem hw)
  have h1 : (T2.comap d).index = T2.relIndex T1 := by
    rw [AddSubgroup.index_comap, ← hsup, AddSubgroup.relIndex_sup_right]
  have h2 := AddSubgroup.card_mul_index (T2.comap d)
  have h3 := AddSubgroup.card_mul_index (T2.addSubgroupOf T1)
  have h4 : Nat.card (T2.addSubgroupOf T1) = Nat.card T2 :=
    Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe h21).toEquiv
  rw [h4] at h3
  rw [← h2, ← h3, h1]
  unfold AddSubgroup.relIndex
  ring

theorem henselStep_count {V W T : Type} [AddCommGroup V] [AddCommGroup W] [AddCommGroup T]
    [Finite V] [Finite W] [Finite T] (ι : W →+ V) (f : V → T) (P : Set V)
    (T1 T2 : AddSubgroup T) (τ : T) (h21 : T2 ≤ T1) (hP : ∀ y ∈ P, ∀ w, y + ι w ∈ P)
    (hd : ∀ y ∈ P, ∃ d : W →+ T, (∀ w, d w ∈ T1) ∧ (∀ t ∈ T1, ∃ w, d w - t ∈ T2) ∧
      ∀ w, f (y + ι w) - f y - d w ∈ T2) :
    Set.ncard {y | y ∈ P ∧ f y - τ ∈ T1} * Nat.card T2 =
      Set.ncard {y | y ∈ P ∧ f y - τ ∈ T2} * Nat.card T1 := by
  set S1 : Set V := {y | y ∈ P ∧ f y - τ ∈ T1} with hS1
  set S2 : Set V := {y | y ∈ P ∧ f y - τ ∈ T2} with hS2

  have ha : Nat.card (Σ y : S1, {w : W // (y : V) + ι w ∈ S2}) = S2.ncard * Nat.card W := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_prod]
    refine Nat.card_congr
      { toFun := fun p => (⟨p.1.1 + ι p.2.1, p.2.2⟩, p.2.1)
        invFun := fun q => ⟨⟨q.1.1 + ι (-q.2), ?_⟩, ⟨q.2, ?_⟩⟩
        left_inv := ?_
        right_inv := ?_ }
    · obtain ⟨⟨u, hu, hu2⟩, w⟩ := q
      refine ⟨hP u hu _, ?_⟩
      obtain ⟨d, h1, -, h3⟩ := hd u hu
      have : f (u + ι (-w)) - τ = (f (u + ι (-w)) - f u - d (-w)) + d (-w) + (f u - τ) := by
        abel
      simp only
      rw [this]
      exact T1.add_mem (T1.add_mem (h21 (h3 _)) (h1 _)) (h21 hu2)
    · simp
    · rintro ⟨⟨y, hy⟩, ⟨w, hw⟩⟩
      have : y + ι w + ι (-w) = y := by simp
      refine Sigma.subtype_ext ?_ rfl
      exact Subtype.ext this
    · rintro ⟨⟨u, hu⟩, w⟩
      simp
  have hb : ∀ y : S1, Nat.card {w : W // (y : V) + ι w ∈ S2} * Nat.card T1 =
      Nat.card W * Nat.card T2 := by
    rintro ⟨y, hy, hy1⟩
    obtain ⟨d, h1, h2, h3⟩ := hd y hy
    rw [← henselStep_card_comap T1 T2 h21 d h1 h2]
    congr 1
    obtain ⟨w0, hw0⟩ := h2 _ (T1.neg_mem hy1)
    refine Nat.card_congr ((Equiv.subRight w0).subtypeEquiv ?_)
    intro w
    simp only [hS2, Set.mem_setOf_eq, Equiv.subRight_apply, AddSubgroup.mem_comap, map_sub]
    have key : f (y + ι w) - τ =
        (f (y + ι w) - f y - d w) + (d w0 - -(f y - τ)) + (d w - d w0) := by abel
    rw [key]
    constructor
    · rintro ⟨-, h⟩
      exact (T2.add_mem_cancel_left (T2.add_mem (h3 w) hw0)).1 h
    · intro h
      exact ⟨hP y hy w, T2.add_mem (T2.add_mem (h3 w) hw0) h⟩
  haveI := Fintype.ofFinite S1
  rw [Nat.card_sigma] at ha
  have hc : S2.ncard * Nat.card W * Nat.card T1 = S1.ncard * (Nat.card W * Nat.card T2) := by
    rw [← ha, Finset.sum_mul, Finset.sum_congr rfl (fun y _ => hb y), Finset.sum_const,
      Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hW : 0 < Nat.card W := Nat.card_pos
  apply Nat.eq_of_mul_eq_mul_left hW
  linarith [hc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFieldOrExistsSwappedIdempotentOfQuadraticEtale
section
open GlobalTheory.SgAlg Matrix

namespace GlobalTheory.SgAlg

theorem isField_or_exists_idempotent_of_isQA {E : Type} [CommRing E] (σ : E →+* E) (h : IsQA σ) :
    IsField E ∨ ∃ e : E, e * e = e ∧ e + σ e = 1 ∧ ∀ x : E, e * x ≠ 0 → ∃ y, e * x * y = e := by
  obtain ⟨hinv, ⟨x₀, hx₀⟩, hred, -, hunit⟩ := h
  by_cases hN : ∀ y : E, y ≠ 0 → y * σ y ≠ 0
  · left
    refine ⟨⟨σ x₀, x₀, hx₀⟩, mul_comm, ?_⟩
    intro y hy
    have hfix : σ (y * σ y) = y * σ y := by
      rw [map_mul, hinv, mul_comm]
    obtain ⟨u, hu⟩ := hunit _ hfix (hN y hy)
    refine ⟨σ y * (↑u⁻¹ : E), ?_⟩
    rw [← mul_assoc, ← hu]
    exact u.mul_inv
  · right
    push Not at hN
    obtain ⟨y, hy, hyy⟩ := hN
    have hsfix : σ (y + σ y) = y + σ y := by
      rw [map_add (f := _), hinv, add_comm]
    have hs : y + σ y ≠ 0 := by
      intro h0
      have h1 : σ y = -y := eq_neg_of_add_eq_zero_right h0
      rw [h1] at hyy
      have h2 : y ^ 2 = 0 := by
        have : y * y = 0 := by simpa using hyy
        rw [pow_two, this]
      exact hy (pow_eq_zero_iff (two_ne_zero) |>.mp h2)
    obtain ⟨s, hs'⟩ := hunit _ hsfix hs
    have hsum : (↑s⁻¹ : E) * (y + σ y) = 1 := by rw [← hs', Units.inv_mul]
    have hσs : σ (↑s⁻¹ : E) * (y + σ y) = 1 := by
      have : σ ((↑s⁻¹ : E) * (y + σ y)) = 1 := by
        rw [hsum, map_one]
      rwa [map_mul, hsfix] at this
    have hσs' : σ (↑s⁻¹ : E) = ↑s⁻¹ := by
      calc σ (↑s⁻¹ : E) = σ (↑s⁻¹ : E) * ((y + σ y) * ↑s⁻¹) := by
            rw [mul_comm (y + σ y), hsum, mul_one]
        _ = ↑s⁻¹ := by rw [← mul_assoc, hσs, one_mul]
    set e : E := y * ↑s⁻¹ with he
    have hσe : σ e = σ y * ↑s⁻¹ := by rw [he, map_mul, hσs']
    have hadd : e + σ e = 1 := by
      rw [hσe, he, ← add_mul, mul_comm]; exact hsum
    have horth : e * σ e = 0 := by
      rw [hσe, he]
      calc y * ↑s⁻¹ * (σ y * ↑s⁻¹) = (y * σ y) * (↑s⁻¹ * ↑s⁻¹) := by ring
        _ = 0 := by rw [hyy, zero_mul]
    have hidem : e * e = e := by
      have : e * (e + σ e) = e := by rw [hadd, mul_one]
      rwa [mul_add, horth, add_zero] at this
    refine ⟨e, hidem, hadd, ?_⟩
    intro x hx
    have hufix : σ (e * x + σ (e * x)) = e * x + σ (e * x) := by
      rw [map_add (f := _), hinv, add_comm]
    have heu : e * (e * x + σ (e * x)) = e * x := by
      rw [map_mul, mul_add, ← mul_assoc, hidem, ← mul_assoc, horth, zero_mul, add_zero]
    have hu0 : e * x + σ (e * x) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at heu
      exact hx heu.symm
    obtain ⟨u, hu⟩ := hunit _ hufix hu0
    refine ⟨↑u⁻¹, ?_⟩
    rw [← heu, ← hu, mul_assoc, u.mul_inv, mul_one]

end GlobalTheory.SgAlg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrimitiveTupleOfLinearIndependentFiniteRing
section
open GlobalTheory.GramCount
open scoped Classical

namespace GlobalTheory.GramCount

theorem sum_char_dot_eq_zero {B : Type} [CommRing B] [Fintype B] (χ : AddChar B ℂ)
    (hχ : χ.IsPrimitive) {m : ℕ} (t : Fin m → B) (ht : t ≠ 0) :
    ∑ s : Fin m → B, χ (∑ a, s a * t a) = 0 := by
  let f : (Fin m → B) →+ B :=
    { toFun := fun s => ∑ a, s a * t a
      map_zero' := by simp
      map_add' := fun s s' => by simp [add_mul, Finset.sum_add_distrib] }
  have h : χ.compAddMonoidHom f ≠ 0 := by
    intro h0
    obtain ⟨a, ha⟩ := Function.ne_iff.1 ht
    refine hχ ha ?_
    ext r
    have h1 := DFunLike.congr_fun h0 (Pi.single a r)
    simpa [f, Pi.single_apply, mul_comm] using h1
  exact AddChar.sum_eq_zero_iff_ne_zero.2 h

theorem exists_dot_eq_of_indep {B : Type} [CommRing B] [Fintype B] (χ : AddChar B ℂ)
    (hχ : χ.IsPrimitive) {k n : ℕ} (x : Fin k → Fin n → B)
    (hx : ∀ s : Fin k → B, ∑ a, s a • x a = 0 → s = 0) (u : Fin k → B) :
    ∃ z : Fin n → B, ∀ a, ∑ i, x a i * z i = u a := by
  by_contra hne
  push_neg at hne
  have h1 : ∑ z : Fin n → B, ∑ s : Fin k → B, χ (∑ a, s a * (∑ i, x a i * z i - u a)) = 0 := by
    refine Finset.sum_eq_zero fun z _ => ?_
    refine sum_char_dot_eq_zero χ hχ (fun a => ∑ i, x a i * z i - u a) ?_
    obtain ⟨a, ha⟩ := hne z
    intro h0
    exact ha (sub_eq_zero.1 (congrFun h0 a))
  rw [Finset.sum_comm, Finset.sum_eq_single (0 : Fin k → B)] at h1
  · simp at h1
  · intro s _ hs
    have h2 : ∀ z : Fin n → B, χ (∑ a, s a * (∑ i, x a i * z i - u a)) =
        χ (∑ i, z i * (∑ a, s a • x a) i) * χ (-∑ a, s a * u a) := by
      intro z
      rw [← AddChar.map_add_eq_mul]
      congr 1
      simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum, sub_eq_add_neg, mul_add, Finset.sum_add_distrib, mul_neg,
        Finset.sum_neg_distrib]
      congr 1
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
      ring
    simp only [h2]
    rw [← Finset.sum_mul, sum_char_dot_eq_zero χ hχ _ (fun h => hs (hx s h)), zero_mul]
  · simp

theorem prim_of_indep_of_isPrimitive : ∀ {B : Type} [CommRing B] [Fintype B] (c : B →+* B),
    (∀ u, c (c u) = u) → ∀ (χ : AddChar B ℂ), χ.IsPrimitive →
    ∀ (k n : ℕ) (x : Fin k → Fin n → B),
      (∀ s : Fin k → B, ∑ a, s a • x a = 0 → s = 0) → Prim c x := by
  intro B _ _ c hc χ hχ k n x hx
  choose z hz using fun b : Fin k => exists_dot_eq_of_indep χ hχ x hx (Pi.single b 1)
  refine ⟨fun b i => c (z b i), fun a b => ?_⟩
  simp only [ip, hc]
  rw [hz, Pi.single_apply]

end GlobalTheory.GramCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureBallEqLintegralUpperMeasureDensity
section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace GlobalTheory

theorem measure_ball_eq_lintegral_upperDens : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (l ν : Measure V) [l.IsAddHaarMeasure] [IsFiniteMeasure ν] (η : ℝ) (C : ℝ≥0), (∀ x : V, ‖x‖ < η → GlobalTheory.HaarDensChart.upperDens l ν x < C) → ∀ ρ : ℝ, ρ ≤ η → ν (Metric.ball 0 ρ) = ∫⁻ x in Metric.ball 0 ρ, GlobalTheory.HaarDensChart.upperDens l ν x ∂l := by
  intro V _ _ _ _ _ l ν _ _ η C hC ρ hρ
  set U : Set V := Metric.ball (0 : V) η with hUdef
  have hUo : IsOpen U := Metric.isOpen_ball

  have key : ∀ x ∈ U, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ν (Metric.closedBall x r) ≤ ((C : ℝ≥0) • l) (Metric.closedBall x r) := by
    intro x hx
    have h0 : limsup (fun r : ℝ => ν (Metric.closedBall x r) / l (Metric.closedBall x r))
        (𝓝[>] (0 : ℝ)) < (C : ℝ≥0∞) := hC x (mem_ball_zero_iff.1 hx)
    filter_upwards [Filter.eventually_lt_of_limsup_lt h0, self_mem_nhdsWithin] with r hr hr0
    have hpos : l (Metric.closedBall x r) ≠ 0 := (Metric.measure_closedBall_pos l x hr0).ne'
    have hfin : l (Metric.closedBall x r) ≠ ⊤ := measure_closedBall_lt_top.ne
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    exact ((ENNReal.div_lt_iff (Or.inl hpos) (Or.inl hfin)).1 hr).le

  have hle : ∀ s ⊆ U, ν s ≤ ((C : ℝ≥0) • l) s := fun s hs =>
    (Besicovitch.vitaliFamily ν).measure_le_of_frequently_le ((C : ℝ≥0) • l)
      Measure.AbsolutelyContinuous.rfl s
      (fun x hx => (Besicovitch.tendsto_filterAt ν x).frequently (key x (hs hx)).frequently)
  have hac : ν.restrict U ≪ l := by
    intro s hs
    rw [Measure.restrict_apply' hUo.measurableSet]
    refine le_antisymm ?_ (by simp)
    calc ν (s ∩ U) ≤ ((C : ℝ≥0) • l) (s ∩ U) := hle _ Set.inter_subset_right
      _ ≤ ((C : ℝ≥0) • l) s := measure_mono Set.inter_subset_left
      _ = 0 := by simp [hs]

  have hae : ∀ᵐ x ∂l, x ∈ U →
      GlobalTheory.HaarDensChart.upperDens l ν x = (ν.restrict U).rnDeriv l x := by
    filter_upwards [Besicovitch.ae_tendsto_rnDeriv (ν.restrict U) l] with x hx hxU
    have hev : (fun r : ℝ => ν.restrict U (Metric.closedBall x r) / l (Metric.closedBall x r))
        =ᶠ[𝓝[>] (0 : ℝ)] (fun r : ℝ => ν (Metric.closedBall x r) / l (Metric.closedBall x r)) := by
      obtain ⟨ε, εpos, hε⟩ := Metric.isOpen_iff.1 hUo x hxU
      filter_upwards [Ioo_mem_nhdsGT εpos] with r hr
      rw [Measure.restrict_eq_self _ ((Metric.closedBall_subset_ball hr.2).trans hε)]
    show limsup (fun r : ℝ => ν (Metric.closedBall x r) / l (Metric.closedBall x r))
        (𝓝[>] (0 : ℝ)) = _
    exact (hx.congr' hev).limsup_eq
  have hsub : Metric.ball (0 : V) ρ ⊆ U := Metric.ball_subset_ball hρ
  calc ν (Metric.ball 0 ρ) = ν.restrict U (Metric.ball 0 ρ) :=
        (Measure.restrict_eq_self _ hsub).symm
    _ = l.withDensity ((ν.restrict U).rnDeriv l) (Metric.ball 0 ρ) := by
        rw [Measure.withDensity_rnDeriv_eq _ _ hac]
    _ = ∫⁻ x in Metric.ball 0 ρ, (ν.restrict U).rnDeriv l x ∂l :=
        withDensity_apply _ Metric.isOpen_ball.measurableSet
    _ = ∫⁻ x in Metric.ball 0 ρ, GlobalTheory.HaarDensChart.upperDens l ν x ∂l := by
        refine setLIntegral_congr_fun_ae Metric.isOpen_ball.measurableSet ?_
        filter_upwards [hae] with x hx hxρ
        exact (hx (hsub hxρ)).symm

end GlobalTheory
end

