module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0004
public import Formalism.PeriodIntegrals.Bundle0012
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SandwichChart.SandwichOfOfCharts

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SandwichChart.SideAUnrealifyRL
section
noncomputable section

open Matrix Filter Topology Classical
open scoped ENNReal NNReal

namespace PI.SwSandwichOfWork

open PI.SwBig PI.SwSand

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

variable {k r : ℕ}

private theorem SideA_unrealify_RL (X : Mat k r) : unrealify (RL X) = X := by
  ext i j
  first
    | (apply Complex.ext <;> simp [unrealify, RL, realifyFun])
    | (apply Complex.ext <;> rfl)

private theorem SideA_rhoS_le (S : Set (Mat k r)) (X : Mat k r) (hX : RL X ∈ lieE S) (x : Mt k r)
    (hx : NormedSpace.exp X = Matrix.of x) :
    rhoS k r S x ^ 2 ≤ ENNReal.ofReal (‖RL X‖ ^ 2) := by
  have h1 : rhoS k r S x ≤ (‖(RL X : EuclideanSpace ℝ _)‖₊ : ℝ≥0∞) := by
    unfold rhoS
    refine iInf₂_le (⟨RL X, hX⟩ : lieE S) ?_
    funext i j
    simp only [SideA_unrealify_RL, hx, Matrix.of_apply]
  calc rhoS k r S x ^ 2 ≤ (‖(RL X : EuclideanSpace ℝ _)‖₊ : ℝ≥0∞) ^ 2 := by gcongr
    _ = ENNReal.ofReal (‖RL X‖ ^ 2) := by
      first
        | (rw [← ENNReal.ofReal_coe_nnreal, coe_nnnorm, ENNReal.ofReal_pow (norm_nonneg _)])
        | (rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]; rfl)
        | simp [ENNReal.ofReal_pow]

theorem sideA : SideA := by
  intro hNR hLG hLW hGU hPF hW0 hLEN hExpN hLI hCB k r ε hε hε1
  obtain ⟨δ, hδ, hCBδ⟩ := hCB k r (ε / 2) (by linarith)
  refine ⟨δ, hδ, fun ρ hρ hρδ n c m n' hn hm hn' hPsi => ?_⟩
  obtain ⟨x, hxball, hxeq⟩ := hPsi
  have hxmem : (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) ∈
      (uH k r).map RL := by
    rw [← hLG k r]
    exact x.2
  obtain ⟨Y, hY, hYx⟩ := Submodule.mem_map.mp hxmem
  have hYn : ‖Y‖ < ρ := by
    rw [← hNR k r Y, hYx]
    exact mem_ball_zero_iff.mp hxball
  have hexpY : NormedSpace.exp Y =
      w0B k r * (Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹) := by
    ext i j
    have h := congrFun (congrFun hxeq i) j
    simp only [Psi] at h
    rw [← hYx, SideA_unrealify_RL] at h
    exact h
  obtain ⟨v, hv, hPhi, hvη, hLm⟩ := hCBδ Y hY (hYn.trans hρδ)
  have hv' := hv
  rw [Vs, Submodule.mem_prod, Submodule.mem_prod, Submodule.mem_prod] at hv'
  obtain ⟨hv1, -, hv3, hv4⟩ := hv'

  have hEq : Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹ =
      NormedSpace.exp v.1 * bigCell k r (1 + v.2.1) 1 * NormedSpace.exp v.2.2.1 *
        (NormedSpace.exp v.2.2.2)⁻¹ := by
    have h := hexpY.symm.trans (hPhi.symm.trans (hPF k r _ _ _ _))
    have h2 : w0B k r * (w0B k r * (Matrix.of n * bigCell k r c 1 * Matrix.of m * (Matrix.of n')⁻¹)) =
        w0B k r * (w0B k r * (NormedSpace.exp v.1 * bigCell k r (1 + v.2.1) 1 *
          NormedSpace.exp v.2.2.1 * (NormedSpace.exp v.2.2.2)⁻¹)) := by rw [h]
    simp only [← Matrix.mul_assoc, hW0 k r, Matrix.one_mul] at h2
    exact h2
  have hc2 : ∀ a, (1 + v.2.1) a ≠ 0 := by
    intro a h0
    have hxa : ‖v.2.1 a‖ < 1 := by
      calc ‖v.2.1 a‖ ≤ ‖v.2.1‖ := norm_le_pi_norm _ a
        _ ≤ ‖v.2‖ := norm_fst_le _
        _ ≤ ‖v‖ := norm_snd_le _
        _ < ε / 2 := hvη
        _ < 1 := by linarith
    have h1 : v.2.1 a = -1 := by
      simp only [Pi.add_apply, Pi.one_apply] at h0
      linear_combination h0
    rw [h1] at hxa
    simp at hxa
  obtain ⟨hnX, hcx, hmZ, hn'X'⟩ := hGU k r _ _ _ _ _ _ c (1 + v.2.1) hn (hExpN k r _ hv1) hm
    ((hLW k r).1 _ hv3) hn' (hExpN k r _ hv4) hc2 hEq
  have hA := SideA_rhoS_le (Nset k r) v.1
    (by rw [hLEN k r]; exact Submodule.mem_map_of_mem hv1) n hnX.symm
  have hB := SideA_rhoS_le (UWb k r) v.2.2.1
    (by rw [(hLW k r).2]; exact Submodule.mem_map_of_mem hv3) m hmZ.symm
  have hC := SideA_rhoS_le (Nset k r) v.2.2.2
    (by rw [hLEN k r]; exact Submodule.mem_map_of_mem hv4) n' hn'X'.symm
  have hcs : ∑ a, ‖c a - 1‖ ^ 2 = ∑ a, ‖v.2.1 a‖ ^ 2 := by
    rw [hcx]
    simp
  have hL0 : 0 ≤ ‖Lm k r v‖ := norm_nonneg _
  have hlt : ‖Lm k r v‖ < (1 + ε) * ρ := by
    have h1 : (1 - ε / 2) * ‖Lm k r v‖ < ρ := lt_of_le_of_lt hLm hYn
    nlinarith [mul_nonneg hε.le hL0, mul_nonneg (mul_nonneg hε.le (sub_nonneg.mpr hε1.le)) hL0]
  have hsq : ‖Lm k r v‖ ^ 2 < ((1 + ε) * ρ) ^ 2 := by nlinarith
  have hsum : ‖RL v.1‖ ^ 2 + 2 * ∑ a, ‖v.2.1 a‖ ^ 2 + ‖RL v.2.2.1‖ ^ 2 + ‖RL v.2.2.2‖ ^ 2 =
      ‖Lm k r v‖ ^ 2 := by
    rw [← (hLI k r).2.2 v hv, hNR k r]
  unfold Qf
  calc rhoS k r (Nset k r) n ^ 2 + ENNReal.ofReal (2 * ∑ a, ‖c a - 1‖ ^ 2) +
        rhoS k r (UWb k r) m ^ 2 + rhoS k r (Nset k r) n' ^ 2
      ≤ ENNReal.ofReal (‖RL v.1‖ ^ 2) + ENNReal.ofReal (2 * ∑ a, ‖v.2.1 a‖ ^ 2) +
        ENNReal.ofReal (‖RL v.2.2.1‖ ^ 2) + ENNReal.ofReal (‖RL v.2.2.2‖ ^ 2) := by
        rw [hcs]
        gcongr
    _ = ENNReal.ofReal (‖RL v.1‖ ^ 2 + 2 * ∑ a, ‖v.2.1 a‖ ^ 2 + ‖RL v.2.2.1‖ ^ 2 +
        ‖RL v.2.2.2‖ ^ 2) := by
        rw [ENNReal.ofReal_add, ENNReal.ofReal_add, ENNReal.ofReal_add] <;> positivity
    _ = ENNReal.ofReal (‖Lm k r v‖ ^ 2) := by rw [hsum]
    _ < ENNReal.ofReal (((1 + ε) * ρ) ^ 2) :=
        (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hsq

end PI.SwSandwichOfWork
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SandwichChart.SideBUnrealifyRL
section
noncomputable section

open Matrix Filter Topology Classical
open scoped ENNReal NNReal

namespace PI.SwSandwichOfWork

open PI.SwBig PI.SwSand

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

variable {k r : ℕ}

private theorem SideB_unrealify_RL (X : Mat k r) : unrealify (RL X) = X := by
  ext i j
  simp [unrealify, RL]
  apply Complex.ext <;> simp [realifyFun]

private theorem SideB_le_of_sq {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]

private theorem SideB_lt_of_sq {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 < b ^ 2) : a < b := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]

private theorem SideB_below (S : Set (Mat k r)) (x : Mt k r) (t : ℝ) (ht : 0 < t)
    (hlt : rhoS k r S x < ENNReal.ofReal t) :
    ∃ Y : lieE S, (fun i j => NormedSpace.exp (unrealify (Y : EuclideanSpace ℝ _)) i j : Mt k r) = x ∧
      ‖(Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖ < t := by
  unfold rhoS at hlt
  obtain ⟨Y, hY⟩ := iInf_lt_iff.1 hlt
  obtain ⟨hex, hY2⟩ := iInf_lt_iff.1 hY
  refine ⟨Y, hex, ?_⟩
  have h3 : ENNReal.ofReal ‖(Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖ <
      ENNReal.ofReal t := by
    rw [← coe_nnnorm, ENNReal.ofReal_coe_nnreal]; exact hY2
  exact (ENNReal.ofReal_lt_ofReal_iff ht).1 h3

theorem SideB_pick (S : Set (Mat k r)) (T : Submodule ℝ (Mat k r)) (hST : lieE S = T.map RL) (x : Mt k r)
    (h : rhoS k r S x ≠ ⊤) (τ : ℝ) (hτ : 0 < τ) :
    ∃ X ∈ T, NormedSpace.exp X = Matrix.of x ∧ ‖RL X‖ ^ 2 < (rhoS k r S x).toReal ^ 2 + τ := by
  have ha : 0 ≤ (rhoS k r S x).toReal := ENNReal.toReal_nonneg
  have hs : 0 < Real.sqrt ((rhoS k r S x).toReal ^ 2 + τ) := Real.sqrt_pos.2 (by positivity)
  have hlt : rhoS k r S x < ENNReal.ofReal (Real.sqrt ((rhoS k r S x).toReal ^ 2 + τ)) := by
    have e : rhoS k r S x = ENNReal.ofReal (rhoS k r S x).toReal := (ENNReal.ofReal_toReal h).symm
    calc rhoS k r S x = ENNReal.ofReal (rhoS k r S x).toReal := e
      _ < ENNReal.ofReal (Real.sqrt ((rhoS k r S x).toReal ^ 2 + τ)) := by
        refine (ENNReal.ofReal_lt_ofReal_iff hs).2 ?_
        rw [Real.lt_sqrt ha]; linarith
  obtain ⟨Y, hex, hY⟩ := SideB_below S x _ hs hlt
  have hm : (Y : EuclideanSpace ℝ _) ∈ T.map RL := hST ▸ Y.2
  obtain ⟨X, hX, hXe⟩ := Submodule.mem_map.1 hm
  refine ⟨X, hX, ?_, ?_⟩
  · ext i j; rw [← hex, ← hXe, SideB_unrealify_RL]; rfl
  · rw [hXe]
    exact (Real.lt_sqrt (norm_nonneg _)).1 hY

private theorem SideB_Qreal (n : Mt k r) (c : Fin r → ℂ) (m n' : Mt k r) (q : ℝ) (hq : 0 < q)
    (hQ : Qf k r n c m n' < ENNReal.ofReal q) :
    rhoS k r (Nset k r) n ≠ ⊤ ∧ rhoS k r (UWb k r) m ≠ ⊤ ∧ rhoS k r (Nset k r) n' ≠ ⊤ ∧
      (rhoS k r (Nset k r) n).toReal ^ 2 + 2 * ∑ a, ‖c a - 1‖ ^ 2 + (rhoS k r (UWb k r) m).toReal ^ 2 +
        (rhoS k r (Nset k r) n').toReal ^ 2 < q := by
  have hQt : Qf k r n c m n' ≠ ⊤ := ne_top_of_lt hQ
  unfold Qf at hQt
  have hA : rhoS k r (Nset k r) n ≠ ⊤ := by
    intro h; apply hQt; rw [h]; simp
  have hB : rhoS k r (UWb k r) m ≠ ⊤ := by
    intro h; apply hQt; rw [h]; simp
  have hD : rhoS k r (Nset k r) n' ≠ ⊤ := by
    intro h; apply hQt; rw [h]; simp
  refine ⟨hA, hB, hD, ?_⟩
  have ha : 0 ≤ (rhoS k r (Nset k r) n).toReal := ENNReal.toReal_nonneg
  have hb : 0 ≤ (rhoS k r (UWb k r) m).toReal := ENNReal.toReal_nonneg
  have hd : 0 ≤ (rhoS k r (Nset k r) n').toReal := ENNReal.toReal_nonneg
  have hs0 : 0 ≤ 2 * ∑ a, ‖c a - 1‖ ^ 2 := by positivity
  have e : Qf k r n c m n' = ENNReal.ofReal ((rhoS k r (Nset k r) n).toReal ^ 2 + 2 * ∑ a, ‖c a - 1‖ ^ 2 +
      (rhoS k r (UWb k r) m).toReal ^ 2 + (rhoS k r (Nset k r) n').toReal ^ 2) := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_pow ha, ENNReal.ofReal_pow hb,
      ENNReal.ofReal_pow hd, ENNReal.ofReal_toReal hA, ENNReal.ofReal_toReal hB, ENNReal.ofReal_toReal hD]
    rfl
  rw [e] at hQ
  exact (ENNReal.ofReal_lt_ofReal_iff hq).1 hQ

private theorem SideB_vnorm (X Z X' : Mat k r) (x : Fin r → ℂ) (N : ℝ) (hN0 : 0 ≤ N) (hNR : NormRL)
    (hN2 : N ^ 2 = ‖RL X‖ ^ 2 + 2 * ∑ a, ‖x a‖ ^ 2 + ‖RL Z‖ ^ 2 + ‖RL X'‖ ^ 2) :
    ‖((X, x, Z, X') : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r)‖ ≤ N := by
  have hS : 0 ≤ ∑ a, ‖x a‖ ^ 2 := Finset.sum_nonneg (fun a _ => sq_nonneg ‖x a‖)
  have h1 := sq_nonneg ‖RL X‖
  have h2 := sq_nonneg ‖RL Z‖
  have h3 := sq_nonneg ‖RL X'‖
  have hX : ‖X‖ ≤ N := by
    rw [← hNR]
    exact SideB_le_of_sq hN0 (by nlinarith)
  have hZ : ‖Z‖ ≤ N := by
    rw [← hNR]
    exact SideB_le_of_sq hN0 (by nlinarith)
  have hX' : ‖X'‖ ≤ N := by
    rw [← hNR]
    exact SideB_le_of_sq hN0 (by nlinarith)
  have hx : ‖x‖ ≤ N := by
    refine (pi_norm_le_iff_of_nonneg hN0).2 fun a => SideB_le_of_sq hN0 ?_
    have hxa : ‖x a‖ ^ 2 ≤ ∑ a, ‖x a‖ ^ 2 :=
      Finset.single_le_sum (f := fun a => ‖x a‖ ^ 2) (fun a _ => sq_nonneg ‖x a‖)
        (Finset.mem_univ a)
    nlinarith
  first
  | exact norm_prod_le_iff.2 ⟨hX, norm_prod_le_iff.2 ⟨hx, norm_prod_le_iff.2 ⟨hZ, hX'⟩⟩⟩
  | (simp only [Prod.norm_def]; exact max_le hX (max_le hx (max_le hZ hX')))

private theorem SideB_arith (ε ρ N Y : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hρ : 0 < ρ) (hN0 : 0 ≤ N) (hY0 : 0 ≤ Y)
    (hN : N ^ 2 < ρ ^ 2 * ((1 - ε) ^ 2 + ε ^ 2 / 8)) (hY : Y ≤ (1 + ε) * N) : N < ρ ∧ Y < ρ := by
  have e2 : 0 < ε * ε := mul_pos hε0 hε0
  have e3 : 0 < ε * ε * (1 - ε) := mul_pos e2 (sub_pos.2 hε1)
  have e4 : 0 < ε * ε * ε * (1 - ε) := mul_pos (mul_pos e2 hε0) (sub_pos.2 hε1)
  have hf : (1 - ε) ^ 2 + ε ^ 2 / 8 < 1 := by nlinarith
  have hg : (1 + ε) ^ 2 * ((1 - ε) ^ 2 + ε ^ 2 / 8) < 1 := by nlinarith
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hN2 : N ^ 2 < ρ ^ 2 := by
    nlinarith [mul_lt_mul_of_pos_left hf hρ2]
  have hY2 : Y ^ 2 < ρ ^ 2 := by
    have hq : 0 < (1 + ε) ^ 2 := by positivity
    nlinarith [mul_le_mul hY hY hY0 (by positivity : (0:ℝ) ≤ (1 + ε) * N),
      mul_lt_mul_of_pos_left hN hq, mul_lt_mul_of_pos_left hg hρ2]
  exact ⟨SideB_lt_of_sq hρ.le hN2, SideB_lt_of_sq hρ.le hY2⟩

theorem sideB : SideB := by
  intro hNR hLG hLW hPF hLN hLI hCF k r ε hε0 hε1
  obtain ⟨δ, hδ, hF⟩ := hCF k r ε hε0
  refine ⟨δ, hδ, fun ρ hρ hρδ n c m n' hn hm hn' hQ => ?_⟩
  have hq : 0 < ((1 - ε) * ρ) ^ 2 := by
    have : 0 < 1 - ε := by linarith
    positivity
  obtain ⟨hA, hB, hD, hQr⟩ := SideB_Qreal n c m n' _ hq hQ
  have hτ : 0 < ρ ^ 2 * ε ^ 2 / 24 := by positivity
  obtain ⟨X, hX, e1, hX2⟩ := SideB_pick (Nset k r) (lieNS k r) (hLN k r) n hA _ hτ
  obtain ⟨Z, hZ, e2, hZ2⟩ := SideB_pick (UWb k r) (uWb k r) (hLW k r).2 m hB _ hτ
  obtain ⟨X', hX', e3, hX'2⟩ := SideB_pick (Nset k r) (lieNS k r) (hLN k r) n' hD _ hτ
  have hv : ((X, c - 1, Z, X') : Mat k r × (Fin r → ℂ) × Mat k r × Mat k r) ∈ Vs k r :=
    Submodule.mem_prod.2 ⟨hX, Submodule.mem_prod.2 ⟨Submodule.mem_top, Submodule.mem_prod.2 ⟨hZ, hX'⟩⟩⟩
  have hsum : ∑ i, ‖(c - 1) i‖ ^ 2 = ∑ i, ‖c i - 1‖ ^ 2 := by simp [Pi.sub_apply]
  have hN2 : ‖Lm k r (X, c - 1, Z, X')‖ ^ 2 =
      ‖RL X‖ ^ 2 + 2 * ∑ i, ‖(c - 1) i‖ ^ 2 + ‖RL Z‖ ^ 2 + ‖RL X'‖ ^ 2 := by
    rw [← hNR k r (Lm k r _), (hLI k r).2.2 _ hv]
  have hNlt : ‖Lm k r (X, c - 1, Z, X')‖ ^ 2 < ρ ^ 2 * ((1 - ε) ^ 2 + ε ^ 2 / 8) := by
    have e : ((1 - ε) * ρ) ^ 2 + 3 * (ρ ^ 2 * ε ^ 2 / 24) = ρ ^ 2 * ((1 - ε) ^ 2 + ε ^ 2 / 8) := by ring
    rw [hN2, hsum]; linarith
  have hvN := SideB_vnorm X Z X' (c - 1) _ (norm_nonneg _) hNR hN2
  obtain ⟨Y, hYu, hYe, hYn⟩ := hF _ hv (by
    have := (SideB_arith ε ρ _ 0 hε0 hε1 hρ (norm_nonneg _) le_rfl hNlt (by positivity)).1
    linarith)
  have hYρ := (SideB_arith ε ρ _ ‖Y‖ hε0 hε1 hρ (norm_nonneg _) (norm_nonneg _) hNlt hYn).2
  have hmem : RL Y ∈ lieE (UH (Hpk k r)) := by
    rw [hLG k r]; exact Submodule.mem_map_of_mem hYu
  unfold gBall expBall
  refine ⟨⟨RL Y, hmem⟩, ?_, ?_⟩
  · rw [mem_ball_zero_iff]
    show ‖RL Y‖ < ρ
    rw [hNR k r Y]; exact hYρ
  · have hc : (1 : Fin r → ℂ) + (c - 1) = c := by abel
    funext i j
    show NormedSpace.exp (unrealify (RL Y)) i j = Psi k r n c m n' i j
    rw [SideB_unrealify_RL, hYe, hPF]
    simp only [hc]
    unfold Psi
    rw [e1, e2, e3]

end PI.SwSandwichOfWork
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SandwichChart.UnrealifyRL
section
noncomputable section

open Matrix Filter Topology Classical
open scoped ENNReal NNReal

namespace PI.SwSandwichOfWork

open PI.SwBig PI.SwSand

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing Matrix.frobeniusNormedAlgebra

variable {k r : ℕ}

theorem normRL : NormRL := by
  intro k r X
  rw [EuclideanSpace.norm_eq, Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool, Real.rpow_two, Complex.sq_norm, Complex.normSq_apply]
  simp [RL, realifyFun]
  ring

def sgI (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if r ≤ i.val ∧ i.val ≤ r + k then i else ⟨2 * r + k - i.val, by omega⟩

theorem Log_Hpk_eq (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = sgI k r i then (if i.val = r + k then -1 else 1) else 0 := by
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  unfold Hpk sgI
  split_ifs <;> (try simp only [Fin.ext_iff, Fin.val_mk] at *) <;> first | rfl | (exfalso; omega)

theorem Log_sgI_sgI (i : Fin (2 * r + k + 1)) : sgI k r (sgI k r i) = i := by
  unfold sgI
  split_ifs <;> simp_all [Fin.ext_iff] <;> omega

theorem Log_sgI_val (i : Fin (2 * r + k + 1)) : ((sgI k r i).val = r + k ↔ i.val = r + k) := by
  unfold sgI
  split_ifs <;> simp_all <;> omega

theorem hpk_sq : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (sgI k r i)]
  · rw [Log_Hpk_eq, Log_Hpk_eq, if_pos rfl, Log_sgI_sgI, Matrix.one_apply]
    have hv := (Log_sgI_val (k := k) (r := r) i)
    by_cases h : j = i
    · subst h
      by_cases h2 : j.val = r + k
      · rw [if_pos h2, if_pos rfl, if_pos (hv.2 h2), if_pos rfl]; norm_num
      · rw [if_neg h2, if_pos rfl, if_neg (fun h' => h2 (hv.1 h')), if_pos rfl]; norm_num
    · rw [if_neg h, if_neg (Ne.symm h), mul_zero]
  · intro l _ hl; rw [Log_Hpk_eq, if_neg hl, zero_mul]
  · simp

theorem logG : LogG := by
  intro k r
  have hE : HasStrictFDerivAt (NormedSpace.exp : Mat k r → Mat k r)
      ((ContinuousLinearEquiv.refl ℝ (Mat k r) : Mat k r →L[ℝ] Mat k r)) 0 := by
    rw [ContinuousLinearEquiv.coe_refl]
    exact hasStrictFDerivAt_exp_zero
  obtain ⟨ε, hε, hleft⟩ := Metric.eventually_nhds_iff.1 hE.eventually_left_inverse
  set H := Hpk k r
  have hHH : H * H = 1 := hpk_sq
  have hHu : IsUnit H := (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hHH)
  have hHi : H⁻¹ = H := Matrix.inv_eq_right_inv hHH
  set C := ‖H‖ * ‖H‖ + 1
  have hC : 0 < C := by positivity
  refine ⟨min ε (ε / C), lt_min hε (div_pos hε hC), fun L hL hG => ?_⟩
  have hLε : ‖L‖ < ε := lt_of_lt_of_le hL (min_le_left _ _)
  have hLC : ‖L‖ < ε / C := lt_of_lt_of_le hL (min_le_right _ _)
  have hadj : ‖adjH L‖ < ε := by
    have h1 : ‖adjH L‖ ≤ ‖H‖ * ‖H‖ * ‖L‖ := by
      unfold adjH
      calc ‖H * Lᴴ * H‖ ≤ ‖H * Lᴴ‖ * ‖H‖ := norm_mul_le _ _
        _ ≤ ‖H‖ * ‖Lᴴ‖ * ‖H‖ := by gcongr; exact norm_mul_le _ _
        _ = ‖H‖ * ‖H‖ * ‖L‖ := by rw [Matrix.frobenius_norm_conjTranspose]; ring
    have h2 : ‖H‖ * ‖H‖ * ‖L‖ < ε := by
      calc ‖H‖ * ‖H‖ * ‖L‖ ≤ C * ‖L‖ := by gcongr; simp [C]
        _ < C * (ε / C) := by gcongr
        _ = ε := by field_simp
    linarith
  have hexp : NormedSpace.exp (adjH L) = NormedSpace.exp (-L) := by
    have hG' : (NormedSpace.exp L)ᴴ * H * NormedSpace.exp L = H := hG
    have h1 : NormedSpace.exp (adjH L) = H * (NormedSpace.exp L)ᴴ * H := by
      have := Matrix.exp_conj H Lᴴ hHu
      rw [hHi, Matrix.exp_conjTranspose] at this
      exact this
    have h2 : (H * (NormedSpace.exp L)ᴴ * H) * NormedSpace.exp L = 1 := by
      rw [Matrix.mul_assoc (H * _), show H * (NormedSpace.exp L)ᴴ * (H * NormedSpace.exp L)
        = H * ((NormedSpace.exp L)ᴴ * H * NormedSpace.exp L) by simp only [Matrix.mul_assoc], hG', hHH]
    rw [h1, Matrix.exp_neg, Matrix.inv_eq_left_inv h2]
  have e1 := hleft (y := adjH L) (by simpa using hadj)
  have e2 := hleft (y := -L) (by simpa using hLε)
  rw [hexp] at e1
  show adjH L + L = 0
  rw [← e1, e2, neg_add_cancel]

end PI.SwSandwichOfWork
end
end

