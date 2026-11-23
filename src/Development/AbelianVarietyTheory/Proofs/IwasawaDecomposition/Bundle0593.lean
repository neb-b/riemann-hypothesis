module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0574
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0566

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthBoundBlocksOfBlockDiagonal
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.GoodMetric

theorem pow_le_logTwo_mul_pow {L : ℝ} {N N' k : ℕ} (hN' : N = 0 → N' = 0) (hL : N = 0 ∨ Real.log 2 ≤ L)
    (hk : k ≤ N') : L ^ k ≤ (Real.log 2)⁻¹ ^ N' * L ^ N' := by
  have h2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h2' : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hD : 1 ≤ (Real.log 2)⁻¹ ^ N' := one_le_pow₀ (one_le_inv₀ h2 |>.2 h2'.le)
  rcases hL with hN | hL
  · have : N' = 0 := hN' hN
    subst this
    have : k = 0 := by omega
    subst this
    simp
  · have hL0 : 0 < L := h2.trans_le hL
    rcases le_or_gt 1 L with h1 | h1
    · calc L ^ k ≤ L ^ N' := pow_le_pow_right₀ h1 hk
        _ = 1 * L ^ N' := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right hD (by positivity)
    · calc L ^ k ≤ 1 := pow_le_one₀ hL0.le h1.le
        _ ≤ (L * (Real.log 2)⁻¹) ^ N' := one_le_pow₀ (by rw [← div_eq_mul_inv, one_le_div h2]; exact hL)
        _ = _ := by rw [mul_pow, mul_comm]

theorem sum_abs_log_eq_zero_or_ge {n : ℕ} (S : Finset (Fin n)) (v : ReciprocityTheory.L2DbarEstimates.V n)
    (hS : ∀ a ∈ S, ‖v a‖ < 1 / 2) :
    ∑ a ∈ S, |Real.log ‖v a‖| = 0 ∨ Real.log 2 ≤ ∑ a ∈ S, |Real.log ‖v a‖| := by
  by_cases h : ∀ a ∈ S, |Real.log ‖v a‖| = 0
  · exact Or.inl (Finset.sum_eq_zero h)
  · push_neg at h
    obtain ⟨a, ha, hne⟩ := h
    right
    have hv : ‖v a‖ ≠ 0 := fun h0 => hne (by rw [h0]; simp)
    have hpos : 0 < ‖v a‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
    have hlt : Real.log ‖v a‖ < Real.log (1 / 2) := Real.log_lt_log hpos (hS a ha)
    have hl : Real.log 2 ≤ |Real.log ‖v a‖| := by
      rw [one_div, Real.log_inv] at hlt
      rw [abs_of_neg (by linarith [Real.log_pos one_lt_two])]
      linarith
    exact hl.trans (Finset.single_le_sum (f := fun a => |Real.log ‖v a‖|) (fun _ _ => abs_nonneg _) ha)

end GlobalTheory.GoodMetric

namespace GlobalTheory.GoodMetric

theorem goodBound_of_blockDiagonal' : ∀ (n : ℕ) (S : Finset (Fin n)) (ι : Type) [Fintype ι] [DecidableEq ι] (m : ι → ℕ) (G : ∀ τ : ι, ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin (m τ)) (Fin (m τ)) ℂ) (c : ℝ) (N : ℕ), ∃ (c' : ℝ) (N' : ℕ), ∀ v : ReciprocityTheory.L2DbarEstimates.V n, (∀ a ∈ S, ‖v a‖ < 1 / 2) → (Matrix.blockDiagonal' fun τ => G τ v).det ≠ 0 → (∀ p q, ContDiffAt ℝ 2 (fun u => (Matrix.blockDiagonal' fun τ => G τ u) p q) v) → GlobalTheory.GoodMetric.GoodBound S c N (fun u => Matrix.blockDiagonal' fun τ => G τ u) v → ∀ τ, GlobalTheory.GoodMetric.GoodBound S c' N' (G τ) v := by
  intro n S ι _ _ m G c N
  set K := ∑ τ, m τ
  set N' := N * (K + 1)
  set F : ℝ := ∏ τ, ((m τ).factorial : ℝ)
  set D : ℝ := (Real.log 2)⁻¹ ^ N'
  refine ⟨F * (max 1 c) ^ (K + 1) * D, N', ?_⟩
  intro v hS hdet hC hG τ
  set L := ∑ a ∈ S, |Real.log ‖v a‖| with hLdef
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hdp : 0 < ‖(Matrix.blockDiagonal' fun τ => G τ v).det‖⁻¹ := inv_pos.2 (norm_pos_iff.2 hdet)
  have hcY : 0 < c * L ^ N := hdp.trans_le hG.det
  have hY : 0 < L ^ N := by
    rcases (pow_nonneg hL0 N).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hcY; exact absurd hcY (lt_irrefl 0)
  have hc : 0 < c := pos_of_mul_pos_left hcY hY.le
  have hLN : N = 0 ∨ Real.log 2 ≤ L := by
    rcases sum_abs_log_eq_zero_or_ge S v hS with h | h
    · left
      by_contra hN
      rw [← hLdef] at h
      rw [h, zero_pow hN] at hY
      exact lt_irrefl 0 hY
    · exact Or.inr h
  have hN' : N = 0 → N' = 0 := fun h => by simp [N', h]
  have key : ∀ k ≤ N', L ^ k ≤ D * L ^ N' := fun k hk => pow_le_logTwo_mul_pow hN' hLN hk
  have hF : 1 ≤ F := by
    have : F = ((∏ τ, (m τ).factorial : ℕ) : ℝ) := by simp [F]
    rw [this]
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _)
  have hD : 1 ≤ D := one_le_pow₀ ((one_le_inv₀ (Real.log_pos one_lt_two)).2
    (by have := Real.log_two_lt_d9; linarith))
  have hM1 : 1 ≤ max 1 c := le_max_left _ _
  have hcF : c ≤ F * (max 1 c) ^ (K + 1) :=
    calc c ≤ max 1 c := le_max_right _ _
      _ ≤ (max 1 c) ^ (K + 1) := le_self_pow₀ hM1 (by omega)
      _ = 1 * (max 1 c) ^ (K + 1) := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hF (by positivity)
  have hcc' : c ≤ F * (max 1 c) ^ (K + 1) * D :=
    hcF.trans (le_mul_of_one_le_right (by positivity) hD)

  have hent : ∀ τ' (i j : Fin (m τ')), ‖G τ' v i j‖ ≤ c * L ^ N := fun τ' i j => by
    have := hG.entry ⟨τ', i⟩ ⟨τ', j⟩
    simpa [Matrix.blockDiagonal'_apply_eq] using this
  have hprod : (Matrix.blockDiagonal' fun τ => G τ v).det = ∏ τ', (G τ' v).det :=
    GlobalTheory.Div.BlockChangeDet.det_blockDiagonal'_eq_prod _
  have hunit : ∀ τ', IsUnit (G τ' v).det := fun τ' => by
    rw [hprod] at hdet
    exact (Finset.prod_ne_zero_iff.1 hdet τ' (Finset.mem_univ _)).isUnit
  have hCτ : ∀ τ', GlobalTheory.HermFrame.MContDiffAt 2 (G τ') v := fun τ' i j => by
    have := hC ⟨τ', i⟩ ⟨τ', j⟩
    simpa [Matrix.blockDiagonal'_apply_eq] using this
  have hconn : ∀ ξ, GlobalTheory.HermFrame.conn (fun u => Matrix.blockDiagonal' fun τ => G τ u) v ξ =
      Matrix.blockDiagonal' fun τ => GlobalTheory.HermFrame.conn (G τ) v ξ := fun ξ =>
    GlobalTheory.HermFrame.conn_blockDiagonal' hunit ξ
  have hcurv : ∀ ξ η, GlobalTheory.HermFrame.curv (fun u => Matrix.blockDiagonal' fun τ => G τ u) v ξ η =
      Matrix.blockDiagonal' fun τ => GlobalTheory.HermFrame.curv (G τ) v ξ η := fun ξ η =>
    GlobalTheory.HermFrame.curv_blockDiagonal' hCτ hunit ξ η
  have hdel : ∀ ξ η, GlobalTheory.HermFrame.mdel (fun u => GlobalTheory.HermFrame.conn
      (fun u => Matrix.blockDiagonal' fun τ => G τ u) u ξ) v η =
      Matrix.blockDiagonal' fun τ => GlobalTheory.HermFrame.mdel (fun u => GlobalTheory.HermFrame.conn (G τ) u ξ) v η := by
    intro ξ η
    have he : (fun u => GlobalTheory.HermFrame.conn (fun u => Matrix.blockDiagonal' fun τ => G τ u) u ξ) =ᶠ[𝓝 v]
        fun u => Matrix.blockDiagonal' fun τ => GlobalTheory.HermFrame.conn (G τ) u ξ :=
      (Filter.eventually_all.2 fun i => (hCτ i).eventually_isUnit (hunit i)).mono
        fun x hx => GlobalTheory.HermFrame.conn_blockDiagonal' hx ξ
    rw [GlobalTheory.HermFrame.mdel_congr he, GlobalTheory.HermFrame.mdel_blockDiagonal']

  set e := c * L ^ N
  set M := max 1 e
  have hM : 1 ≤ M := le_max_left _ _
  have hdetle : ∀ τ', ‖(G τ' v).det‖ ≤ ((m τ').factorial : ℝ) * M ^ m τ' := fun τ' => by
    have := Matrix.det_le (abv := NormedField.toAbsoluteValue ℂ) (A := G τ' v) (x := M)
      fun i j => (hent τ' i j).trans (le_max_right _ _)
    calc ‖(G τ' v).det‖ = (NormedField.toAbsoluteValue ℂ) (G τ' v).det := rfl
      _ ≤ _ := this
      _ = _ := by simp [Fintype.card_fin, nsmul_eq_mul]
  set P := ∏ τ' ∈ Finset.univ.erase τ, ‖(G τ' v).det‖
  have hnorm : ‖(Matrix.blockDiagonal' fun τ => G τ v).det‖ = ‖(G τ v).det‖ * P := by
    rw [hprod, norm_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
  have hP0 : 0 < P := Finset.prod_pos fun τ' _ => norm_pos_iff.2 (hunit τ').ne_zero
  have hinv : ‖(G τ v).det‖⁻¹ = ‖(Matrix.blockDiagonal' fun τ => G τ v).det‖⁻¹ * P := by
    rw [hnorm, mul_inv, mul_assoc, inv_mul_cancel₀ hP0.ne', mul_one]
  have hPle : P ≤ F * M ^ K := by
    have h1 : P ≤ ∏ τ' ∈ Finset.univ.erase τ, ((m τ').factorial : ℝ) * M ^ m τ' :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun τ' _ => hdetle τ'
    have h2 : ∏ τ' ∈ Finset.univ.erase τ, ((m τ').factorial : ℝ) * M ^ m τ' ≤
        ∏ τ', ((m τ').factorial : ℝ) * M ^ m τ' := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
      refine le_mul_of_one_le_left (Finset.prod_nonneg fun _ _ => by positivity) ?_
      exact one_le_mul_of_one_le_of_one_le
        (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)) (one_le_pow₀ hM)
    have h3 : ∏ τ', ((m τ').factorial : ℝ) * M ^ m τ' = F * M ^ K := by
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    linarith
  have hMle : M ≤ max 1 c * max 1 (L ^ N) :=
    max_le (one_le_mul_of_one_le_of_one_le hM1 (le_max_left _ _))
      (mul_le_mul (le_max_right _ _) (le_max_right _ _) hY.le (by positivity))
  have hMY : (max 1 (L ^ N)) ^ (K + 1) ≤ D * L ^ N' := by
    rcases le_total 1 (L ^ N) with h | h
    · rw [max_eq_right h, ← pow_mul]; exact key _ le_rfl
    · rw [max_eq_left h, one_pow]; simpa using key 0 (Nat.zero_le _)
  refine ⟨fun i j => ?_, ?_, fun a i j => ?_, fun a b i j => ?_, fun a b i j => ?_⟩
  · calc ‖G τ v i j‖ ≤ c * L ^ N := hent τ i j
      _ ≤ c * (D * L ^ N') := mul_le_mul_of_nonneg_left (key N (by simp [N']; exact Nat.le_mul_of_pos_right _ (by omega))) hc.le
      _ = c * D * L ^ N' := by ring
      _ ≤ F * (max 1 c) ^ (K + 1) * D * L ^ N' :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcF (by positivity)) (by positivity)
  · rw [hinv]
    calc ‖(Matrix.blockDiagonal' fun τ => G τ v).det‖⁻¹ * P ≤ e * (F * M ^ K) :=
          mul_le_mul hG.det hPle hP0.le hcY.le
      _ ≤ M * (F * M ^ K) := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
      _ = F * M ^ (K + 1) := by ring
      _ ≤ F * (max 1 c * max 1 (L ^ N)) ^ (K + 1) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hMle _) (by positivity)
      _ = F * (max 1 c) ^ (K + 1) * (max 1 (L ^ N)) ^ (K + 1) := by ring
      _ ≤ F * (max 1 c) ^ (K + 1) * (D * L ^ N') := mul_le_mul_of_nonneg_left hMY (by positivity)
      _ = _ := by ring
  · have := hG.form a ⟨τ, i⟩ ⟨τ, j⟩
    rw [hconn, Matrix.blockDiagonal'_apply_eq] at this
    exact this.trans hcc'
  · have := hG.dbar a b ⟨τ, i⟩ ⟨τ, j⟩
    rw [hcurv, Matrix.blockDiagonal'_apply_eq] at this
    exact this.trans hcc'
  · have := hG.del a b ⟨τ, i⟩ ⟨τ, j⟩
    rw [hdel, hdel, Matrix.sub_apply, Matrix.blockDiagonal'_apply_eq, Matrix.blockDiagonal'_apply_eq,
      ← Matrix.sub_apply] at this
    exact this.trans hcc'

end GlobalTheory.GoodMetric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MumfordGoodGrowthBoundCongrGermGram
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.GoodMetric

theorem goodBound_congr_nhds (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (c : ℝ) (N : ℕ)
    (G G' : ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n) :
    G =ᶠ[nhds v] G' → GlobalTheory.GoodMetric.GoodBound S c N G v → GlobalTheory.GoodMetric.GoodBound S c N G' v := by
  intro h hb
  have hv : G v = G' v := h.eq_of_nhds
  have hc : ∀ ξ, (fun u => GlobalTheory.HermFrame.conn G u ξ) =ᶠ[nhds v] (fun u => GlobalTheory.HermFrame.conn G' u ξ) :=
    fun ξ => h.eventuallyEq_nhds.mono fun x hx => GlobalTheory.HermFrame.conn_congr hx ξ
  refine ⟨fun i j => ?_, ?_, fun a i j => ?_, fun a b i j => ?_, fun a b i j => ?_⟩
  · rw [← hv]; exact hb.entry i j
  · rw [← hv]; exact hb.det
  · rw [← GlobalTheory.HermFrame.conn_congr h]; exact hb.form a i j
  · rw [← GlobalTheory.HermFrame.curv_congr h]; exact hb.dbar a b i j
  · rw [← GlobalTheory.HermFrame.mdel_congr (hc _), ← GlobalTheory.HermFrame.mdel_congr (hc _)]; exact hb.del a b i j

end GlobalTheory.GoodMetric
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PoincareNormCoordinateVectorMulLengthLeFive
section
open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.PoinLen

theorem mem_castLE_iff {n a : ℕ} (ha : a ≤ n) (k : Fin n) :
    k ∈ Finset.univ.map (Fin.castLEEmb ha) ↔ k.val < a := by
  constructor
  · intro h
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 h
    simp
  · intro h
    exact Finset.mem_map.2 ⟨⟨k.val, h⟩, Finset.mem_univ _, Fin.ext (by simp)⟩

theorem gnorm_poincareGram_single {n : ℕ} (a : ℕ) (z : Fin n → ℂ) (k : Fin n) :
    GlobalTheory.HermFrame.gnorm (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.poincareGram a z) (Pi.single k 1) =
      √(if k.val < a then 1 / (2 * (‖z k‖ ^ 2 * GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog (z k) ^ 2)) else 1 / 2) := by
  rw [GlobalTheory.HermFrame.gnorm, GlobalTheory.HermFrame.form_single, GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.poincareGram, diagonal_apply_eq]
  simp only [Complex.ofReal_re]

theorem sqrt_two_mul_pi_le : √(2 * Real.pi ^ 2) ≤ 5 := by
  rw [show (5:ℝ) = √(5 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  apply Real.sqrt_le_sqrt
  nlinarith [Real.pi_lt_d2, Real.pi_pos]

theorem gnorm_mul_poinWt_le_five : ∀ (n a : ℕ) (ha : a ≤ n) (ρ : ℝ), ρ ≤ 1 / 2 → ∀ v : ReciprocityTheory.L2DbarEstimates.V n,
    v.ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured ha ρ → ∀ k : Fin n,
    GlobalTheory.HermFrame.gnorm (GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.poincareGram a v.ofLp) (Pi.single k 1) *
      GlobalTheory.GoodMetric.poinWt (Finset.univ.map (Fin.castLEEmb ha)) v k ≤ 5 := by
  intro n a ha ρ hρ v hv k
  rw [gnorm_poincareGram_single, GlobalTheory.GoodMetric.poinWt]
  by_cases hk : k.val < a
  · rw [if_pos hk, if_pos ((mem_castLE_iff ha k).2 hk)]
    have h0 : v.ofLp k ≠ 0 := by
      have := hv.2 ⟨k.val, hk⟩
      simpa [Fin.castLE] using this
    have h1 : ‖v.ofLp k‖ < 1 := lt_of_lt_of_le (hv.1 k) (by linarith)
    have ht := GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog_pos h0 h1
    have hx : 0 < ‖v.ofLp k‖ := norm_pos_iff.2 h0
    have hlog : |Real.log ‖v.ofLp k‖| = 2 * Real.pi * GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog (v.ofLp k) := by
      rw [abs_of_neg (Real.log_neg hx h1), GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog]
      field_simp
    change √(1 / (2 * (‖v.ofLp k‖ ^ 2 * GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog (v.ofLp k) ^ 2))) *
      (‖v.ofLp k‖ * |Real.log ‖v.ofLp k‖|) ≤ 5
    rw [hlog]
    set x := ‖v.ofLp k‖
    set t := GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog (v.ofLp k)
    have hB : 0 ≤ x * (2 * Real.pi * t) := by positivity
    rw [← Real.sqrt_sq hB, ← Real.sqrt_mul (by positivity)]
    convert sqrt_two_mul_pi_le using 2
    field_simp
  · rw [if_neg hk, if_neg (fun h => hk ((mem_castLE_iff ha k).1 h)), mul_one]
    calc √(1 / 2 : ℝ) ≤ √1 := Real.sqrt_le_sqrt (by norm_num)
      _ ≤ 5 := by rw [Real.sqrt_one]; norm_num

end GlobalTheory.PoinLen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFanCarrierDimensionBounded
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem genRank_le_sq (E : Type) [Field E] [NumberField E] (q : ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X] (hX : Module.finrank (𝓞 E) X ≤ q) {m : ℕ}
    (γ : Fin m → LinearMap.BilinForm ℤ X) : genRank γ ≤ (q * Module.finrank ℚ E) ^ 2 := by
  have : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  have : Module.Free ℤ X := free_int_of_projective E
  have h1 : genRank γ ≤ Module.finrank ℤ (LinearMap.BilinForm ℤ X) :=
    Submodule.finrank_le _
  have h2 : Module.finrank ℤ (LinearMap.BilinForm ℤ X) = Module.finrank ℤ X * Module.finrank ℤ X := by
    unfold LinearMap.BilinForm
    rw [Module.finrank_linearMap, Module.finrank_linearMap_self]
  have h3 : Module.finrank ℤ X ≤ q * Module.finrank ℚ E := by
    rw [finrank_int_eq_finrank_mul E X, mul_comm]
    exact Nat.mul_le_mul_right _ hX
  calc genRank γ ≤ Module.finrank ℤ X * Module.finrank ℤ X := h2 ▸ h1
    _ ≤ (q * Module.finrank ℚ E) * (q * Module.finrank ℚ E) := Nat.mul_le_mul h3 h3
    _ = (q * Module.finrank ℚ E) ^ 2 := (sq _).symm

theorem carrierDim_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (ψ lab : InvFun (𝓞 E)), IsCarrierDim H.bar q ψ lab → ∃ N : ℕ, ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
    [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q →
    ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → lab.evalZ β ≤ N := by
  intro E _ _ _ H q ψ lab hlab
  refine ⟨(q * Module.finrank ℚ E) ^ 2, fun X _ _ _ _ hX β hβ hpos => ?_⟩
  rw [hlab X hX β hβ hpos]
  exact_mod_cast (by
    rcases Set.eq_empty_or_nonempty {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧
        InRCone γ β ∧ genRank γ = k} with he | hne
    · rw [he, Nat.sInf_empty]; exact Nat.zero_le _
    · obtain ⟨m, γ, -, -, hk⟩ := Nat.sInf_mem hne
      rw [← hk]; exact genRank_le_sq E q X hX γ :
    sInf {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ ∧ InRCone γ β ∧ genRank γ = k} ≤
      (q * Module.finrank ℚ E) ^ 2)

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimitiveBalancedFormEqOfSameRay
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem balForms_zsmul_cancel {O : Type} [CommRing O] {bar : O → O} {X : Type} [AddCommGroup X] [Module O X]
    {g : ℤ} (hg : g ≠ 0) {a b : balForms bar X} (h : g • a = g • b) : a = b := by
  apply Subtype.ext
  refine LinearMap.ext₂ fun y z => ?_
  have h2 := LinearMap.congr_fun₂ (congrArg Subtype.val h) y z
  simp only [Submodule.coe_smul, LinearMap.smul_apply, smul_eq_mul] at h2
  exact mul_left_cancel₀ hg h2

theorem isPrim_ray_eq : ∀ {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X]
    (β β' : balForms bar X) (p r : ℕ), IsPrim bar β → IsPrim bar β' → 0 < p → 0 < r → p • β = r • β' → β = β' := by
  intro O _ bar X _ _ β β' p r hβ hβ' hp hr h
  set g := Nat.gcd p r with hgdef
  have hg : 0 < g := Nat.gcd_pos_of_pos_left r hp
  obtain ⟨p₁, hp₁⟩ : g ∣ p := Nat.gcd_dvd_left p r
  obtain ⟨r₁, hr₁⟩ : g ∣ r := Nat.gcd_dvd_right p r
  have hcop : Nat.Coprime p₁ r₁ := by
    have := Nat.coprime_div_gcd_div_gcd (m := p) (n := r) hg
    rw [← hgdef] at this
    have e1 : p / g = p₁ := by rw [hp₁, Nat.mul_div_cancel_left _ hg]
    have e2 : r / g = r₁ := by rw [hr₁, Nat.mul_div_cancel_left _ hg]
    rwa [e1, e2] at this

  have h1 : (p₁ : ℤ) • β = (r₁ : ℤ) • β' := by
    apply balForms_zsmul_cancel (g := (g : ℤ)) (by exact_mod_cast hg.ne')
    rw [smul_smul, smul_smul, ← Nat.cast_mul, ← Nat.cast_mul, ← hp₁, ← hr₁, natCast_zsmul, natCast_zsmul]
    exact h

  have hbez : (p₁ : ℤ) * Nat.gcdA p₁ r₁ + (r₁ : ℤ) * Nat.gcdB p₁ r₁ = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one]; rfl
  set u := Nat.gcdA p₁ r₁
  set v := Nat.gcdB p₁ r₁
  have hr1 : r₁ = 1 := by
    apply hβ r₁ (u • β' + v • β)
    calc β = ((p₁ : ℤ) * u + (r₁ : ℤ) * v) • β := by rw [hbez, one_smul]
      _ = u • ((p₁ : ℤ) • β) + (r₁ : ℤ) • (v • β) := by
          rw [add_smul, smul_smul, smul_smul, mul_comm (p₁ : ℤ) u]
      _ = r₁ • (u • β' + v • β) := by
          rw [h1, smul_smul, mul_comm u, ← smul_smul, ← smul_add, natCast_zsmul]
  have hp1 : p₁ = 1 := by
    apply hβ' p₁ (u • β' + v • β)
    calc β' = ((p₁ : ℤ) * u + (r₁ : ℤ) * v) • β' := by rw [hbez, one_smul]
      _ = (p₁ : ℤ) • (u • β') + v • ((r₁ : ℤ) • β') := by
          rw [add_smul, smul_smul, smul_smul, mul_comm (r₁ : ℤ) v]
      _ = p₁ • (u • β' + v • β) := by
          rw [← h1, smul_smul v, mul_comm v, ← smul_smul, ← smul_add, natCast_zsmul]
  rw [hr1, hp1] at h1
  simpa using h1

end GlobalTheory.PolFan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PuncturedPolydiscSumNegLogEqAndGeLogTwo
section
open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.Proof.puncturedPolydisc_sum_negLog_eq_and_ge_logTwo

theorem tlog_sum_eq_and_log_two_le : ∀ (n a : ℕ) (ha : a ≤ n) (ρ : ℝ), ρ ≤ 1 / 2 → ∀ v : ReciprocityTheory.L2DbarEstimates.V n, v.ofLp ∈ GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.punctured ha ρ → (∑ i : Fin a, GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog (v.ofLp (Fin.castLE ha i)) = (∑ k ∈ Finset.univ.map (Fin.castLEEmb ha), |Real.log ‖v k‖|) / (2 * Real.pi)) ∧ (0 < a → Real.log 2 ≤ ∑ k ∈ Finset.univ.map (Fin.castLEEmb ha), |Real.log ‖v k‖|) := by
  intro n a ha ρ hρ v hv
  have hpos : ∀ i : Fin a, 0 < ‖v.ofLp (Fin.castLE ha i)‖ := fun i => norm_pos_iff.2 (hv.2 i)
  have hlt : ∀ i : Fin a, ‖v.ofLp (Fin.castLE ha i)‖ < 1 / 2 := fun i =>
    lt_of_lt_of_le (hv.1 (Fin.castLE ha i)) hρ
  have hneg : ∀ i : Fin a, Real.log ‖v.ofLp (Fin.castLE ha i)‖ < 0 := fun i =>
    Real.log_neg (hpos i) (by linarith [hlt i])
  refine ⟨?_, fun h0 => ?_⟩
  · rw [Finset.sum_map, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Fin.castLEEmb_apply, GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.tlog]
    rw [abs_of_neg (hneg i)]
  · rw [Finset.sum_map]
    have hs := Finset.single_le_sum (f := fun i : Fin a => |Real.log ‖v (Fin.castLEEmb ha i)‖|)
      (fun i _ => abs_nonneg _) (Finset.mem_univ (⟨0, h0⟩ : Fin a))
    refine le_trans ?_ hs
    have e : |Real.log ‖v (Fin.castLEEmb ha ⟨0, h0⟩)‖| = -Real.log ‖v.ofLp (Fin.castLE ha ⟨0, h0⟩)‖ :=
      abs_of_neg (hneg _)
    simp only [] at e ⊢
    rw [e]
    have hl : Real.log ‖v.ofLp (Fin.castLE ha ⟨0, h0⟩)‖ ≤ Real.log (1 / 2) :=
      Real.log_le_log (hpos _) (hlt _).le
    have h2 : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
    linarith

end GlobalTheory.Proof.puncturedPolydisc_sum_negLog_eq_and_ge_logTwo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RealConeCoordsIntegralOfPartOfIntBasis
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

theorem GlobalTheory.cone_coords_int_of_isPartOfBasis : ∀ (X : Type) [AddCommGroup X] (m : ℕ) (u : Fin m → LinearMap.BilinForm ℤ X) (hu : ∀ i, u i ∈ balForms (id : ℤ → ℤ) X), IsPartOfBasis (fun i => (⟨u i, hu i⟩ : balForms (id : ℤ → ℤ) X)) → ∀ (β : LinearMap.BilinForm ℤ X) (t : Fin m → ℝ), toReal β = ∑ i, t i • toReal (u i) → ∀ i, ∃ z : ℤ, t i = z := by
  intro X _ m u hu hpb β t h
  obtain ⟨n, b, hb⟩ := hpb
  have hpt : ∀ a y, (β a y : ℝ) = ∑ i, t i * (u i a y : ℝ) := fun a y => by
    have := LinearMap.congr_fun₂ h a y
    simpa [LinearMap.sum_apply, toReal_apply] using this
  have hsym : ∀ a y, β a y = β y a := fun a y => by
    have h1 := hpt a y
    have h2 := hpt y a
    have : (β a y : ℝ) = β y a := by
      rw [h1, h2]
      exact Finset.sum_congr rfl fun i _ => by rw [((mem_balForms_int).1 (hu i)) a y]
    exact_mod_cast this
  let β' : balForms (id : ℤ → ℤ) X := ⟨β, (mem_balForms_int).2 hsym⟩
  set s := b.repr β' with hs
  have hexp : ∀ a y, β a y = ∑ j, s j * ((b j : LinearMap.BilinForm ℤ X) a y) := fun a y => by
    have h0 := congrArg (fun γ : balForms (id : ℤ → ℤ) X => (γ : LinearMap.BilinForm ℤ X) a y) (b.sum_repr β')
    simp only [Submodule.coe_sum, Submodule.coe_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at h0
    exact h0.symm
  let e : Fin m ⊕ Fin n → ℝ := Sum.elim t 0
  let c : Fin m ⊕ Fin n → ℝ := fun j => (s j : ℝ) - e j
  have hc : ∑ j, c j • toReal ((balForms (id : ℤ → ℤ) X).subtype (b j)) = 0 := by
    refine LinearMap.ext₂ fun a y => ?_
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, Submodule.subtype_apply, smul_eq_mul,
      LinearMap.zero_apply, c, sub_mul, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    have e1 : (∑ j, (s j : ℝ) * ((b j : LinearMap.BilinForm ℤ X) a y : ℝ)) = β a y := by
      rw [hexp a y]; push_cast; rfl
    rw [e1, hpt a y, Fintype.sum_sum_type]
    simp [e, hb]
  intro i
  refine ⟨s (Sum.inl i), ?_⟩
  have := sum_mul_eq_zero_of_sum_toReal (X := X) (j := (balForms (id : ℤ → ℤ) X).subtype) Subtype.val_injective
    (b.coord (Sum.inl i)) hc
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply] at this
  rw [Finset.sum_eq_single (Sum.inl i)] at this
  · simp [c, e] at this
    linarith
  · intro j _ hj; simp [hj]
  · simp
end

