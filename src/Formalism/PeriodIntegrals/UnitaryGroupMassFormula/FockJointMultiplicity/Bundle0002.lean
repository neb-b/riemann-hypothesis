module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.JointMultOfSteps
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.CauchyHW
section
noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FJM

def bRow {σ : Type*} {m n : ℕ} (ι : Fin m × Fin n → σ) (a b : Fin m) : Module.End ℂ (MvPolynomial σ ℂ) :=
  ∑ k : Fin n, LinearMap.mulLeft ℂ (X (ι (a, k))) * (pderiv (ι (b, k))).toLinearMap

def bCol {σ : Type*} {m n : ℕ} (ι : Fin m × Fin n → σ) (c d : Fin n) : Module.End ℂ (MvPolynomial σ ℂ) :=
  ∑ i : Fin m, LinearMap.mulLeft ℂ (X (ι (i, c))) * (pderiv (ι (i, d))).toLinearMap

def CauchyHW : Prop := ∀ (σ : Type) (m n : ℕ) (ι : Fin m × Fin n → σ), Function.Injective ι →
  ∀ (α : Fin m → ℕ) (β : Fin n → ℕ) (P : MvPolynomial σ ℂ), P ≠ 0 →
  (∀ a b : Fin m, a < b → bRow ι a b P = 0) → (∀ c d : Fin n, c < d → bCol ι c d P = 0) →
  (∀ e ∈ P.support, (∀ i, ∑ k : Fin n, e (ι (i, k)) = α i) ∧ (∀ k, ∑ i : Fin m, e (ι (i, k)) = β k)) →
  (∀ i, 0 < α i) → (∀ k, 0 < β k) →
  m = n ∧ Antitone α ∧ (∀ (i : Fin m) (k : Fin n), (i : ℕ) = k → α i = β k) ∧
    ∃ Q : MvPolynomial σ ℂ, (∀ e ∈ Q.support, ∀ x, e (ι x) = 0) ∧
      P = shapeProd (Matrix.of fun (i : Fin m) (k : Fin n) => (X (ι (i, k)) : MvPolynomial σ ℂ)) (List.ofFn α) * Q

def MinDegJ : Prop := ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ),
  ∀ P ∈ JH p q r s μ μ', P ≠ 0 →
    (∃ d : ℕ, (d : ℚ) = degW (cPair r s) μ ∧ P ∈ homog (Ix p q × Ix r s) d) ∧
    (∃ d : ℕ, (d : ℚ) = degW (cPair p q) μ' ∧ P ∈ homog (Ix p q × Ix r s) d)

abbrev nu1 (p q r s : ℕ) (μ : Ix p q → ℚ) : Ix p q → ℚ := shiftNu (cPair r s) μ
abbrev nu2 (p q r s : ℕ) (μ' : Ix r s → ℚ) : Ix r s → ℚ := shiftNu (cPair p q) μ'

def MinHyp (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) (P : Pol p q r s) : Prop :=
  P ∈ JH p q r s μ μ' ∧ P ≠ 0 ∧ ∃ d : ℕ, (d : ℚ) = degW (cPair r s) μ ∧ (d : ℚ) = degW (cPair p q) μ' ∧
    P ∈ homog (Ix p q × Ix r s) d

def PureJ : Prop := ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) (P : Pol p q r s), MinHyp p q r s μ μ' P →
  ∀ e ∈ P.support, ∀ l : Ln p q r s, e l ≠ 0 →
    nu1 p q r s μ l.1 ≠ 0 ∧ nu2 p q r s μ' l.2 ≠ 0 ∧
    (linePos l = true ↔ 0 < nu1 p q r s μ l.1) ∧ (linePos l = true ↔ 0 < nu2 p q r s μ' l.2)

def SegJ : Prop := ∀ (p q r s : ℕ) (μ : Ix p q → ℚ) (μ' : Ix r s → ℚ) (P : Pol p q r s), MinHyp p q r s μ μ' P →
  (∀ i i' : Fin p, i < i' → 0 < nu1 p q r s μ (.inl i') → 0 < nu1 p q r s μ (.inl i)) ∧
  (∀ i i' : Fin p, i < i' → nu1 p q r s μ (.inl i) < 0 → nu1 p q r s μ (.inl i') < 0) ∧
  (∀ j j' : Fin q, j < j' → 0 < nu1 p q r s μ (.inr j') → 0 < nu1 p q r s μ (.inr j)) ∧
  (∀ j j' : Fin q, j < j' → nu1 p q r s μ (.inr j) < 0 → nu1 p q r s μ (.inr j') < 0) ∧
  (∀ k k' : Fin r, k < k' → 0 < nu2 p q r s μ' (.inl k') → 0 < nu2 p q r s μ' (.inl k)) ∧
  (∀ k k' : Fin r, k < k' → nu2 p q r s μ' (.inl k) < 0 → nu2 p q r s μ' (.inl k') < 0) ∧
  (∀ l l' : Fin s, l < l' → 0 < nu2 p q r s μ' (.inr l') → 0 < nu2 p q r s μ' (.inr l)) ∧
  (∀ l l' : Fin s, l < l' → nu2 p q r s μ' (.inr l) < 0 → nu2 p q r s μ' (.inr l') < 0)

end PI.FJM
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.ExistPad
section
open FockH1Action PI.FJM

noncomputable section

namespace PI.FJMX

theorem posPart_pw (a : List ℤ) (ha : a.Pairwise (· ≥ ·)) : (PI.FJM.posPart a).Pairwise (· ≥ ·) := by
  rw [PI.FJM.posPart, List.pairwise_map]
  exact ha.imp fun h => by omega

theorem negPart_pw (b : List ℤ) (hb : b.Pairwise (· ≥ ·)) : (PI.FJM.negPart b).Pairwise (· ≥ ·) := by
  rw [PI.FJM.negPart, List.pairwise_reverse, List.pairwise_map]
  exact hb.imp fun h => by omega

theorem posPart_getD (a : List ℤ) (ha : ∀ v ∈ a, 0 < v) (i : ℕ) :
    ((PI.FJM.posPart a).getD i 0 : ℚ) = if h : i < a.length then ((a[i] : ℤ) : ℚ) else 0 := by
  by_cases h : i < a.length
  · rw [dite_eq_left h, List.getD_eq_getElem _ _ (by simpa [PI.FJM.posPart] using h)]
    simp only [PI.FJM.posPart, List.getElem_map]
    have hpos := ha _ (List.getElem_mem h)
    have := Int.toNat_of_nonneg hpos.le
    exact_mod_cast this
  · rw [dite_eq_right h, List.getD_eq_default _ _ (by simpa [PI.FJM.posPart] using not_lt.1 h)]
    simp

theorem negPart_getD (b : List ℤ) (hb : ∀ v ∈ b, v < 0) (j : ℕ) :
    ((PI.FJM.negPart b).getD j 0 : ℚ) =
      if h : j < b.length then -((b[b.length - 1 - j]'(by omega) : ℤ) : ℚ) else 0 := by
  by_cases h : j < b.length
  · rw [dite_eq_left h, List.getD_eq_getElem _ _ (by simpa [PI.FJM.negPart] using h)]
    simp only [PI.FJM.negPart, List.getElem_reverse, List.getElem_map, List.length_map]
    have hneg := hb _ (List.getElem_mem (l := b) (n := b.length - 1 - j) (by omega))
    have := Int.toNat_of_nonneg (show 0 ≤ -b[b.length - 1 - j] by omega)
    have h2 : ((-b[b.length - 1 - j]).toNat : ℚ) = ((-b[b.length - 1 - j] : ℤ) : ℚ) := by
      exact_mod_cast this
    rw [h2]
    push_cast
    ring
  · rw [dite_eq_right h, List.getD_eq_default _ _ (by simpa [PI.FJM.negPart] using not_lt.1 h)]
    simp

theorem pad_getD (a b : List ℤ) (n : ℕ) (hn : a.length + b.length ≤ n) (ha : ∀ v ∈ a, 0 < v)
    (hb : ∀ v ∈ b, v < 0) (i : ℕ) (hi : i < n) :
    (pad a (n - a.length - b.length) b).getD i 0 =
      ((PI.FJM.posPart a).getD i 0 : ℚ) - ((PI.FJM.negPart b).getD (n - 1 - i) 0 : ℚ) := by
  rw [posPart_getD a ha, negPart_getD b hb]
  rw [pad, List.getD_eq_getElem _ _ (by simp; omega)]
  simp only [List.getElem_map]
  by_cases h1 : i < a.length
  · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left h1,
      dite_eq_left h1, dite_eq_right (by omega)]
    simp
  · by_cases h2 : i < a.length + (n - a.length - b.length)
    · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by omega),
        dite_eq_right h1, dite_eq_right (by omega)]
      simp
    · rw [List.getElem_append_right (by simp; omega), dite_eq_right h1, dite_eq_left (by omega)]
      simp only [neg_neg, sub_neg_eq_add, zero_add]
      congr 2
      simp
      omega

end PI.FJMX
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockJointMultiplicity.ExistWt
section
open MvPolynomial FockH1Action PI.FJM

noncomputable section

namespace PI.FJMX

theorem tele (g : ℕ → ℕ) (hg : ∀ t, g (t + 1) ≤ g t) (i₀ : ℕ) (n : ℕ) :
    ∑ t ∈ Finset.range n, (if i₀ ≤ t then (g t - g (t + 1)) else 0) =
      if i₀ < n then g i₀ - g n else 0 := by
  have anti : Antitone g := antitone_nat_of_succ_le hg
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 := hg n
    by_cases h : i₀ < n
    · have h2 : g n ≤ g i₀ := anti h.le
      rw [if_pos h, if_pos (by omega : i₀ ≤ n), if_pos (by omega : i₀ < n + 1)]
      omega
    · by_cases h' : i₀ = n
      · subst h'
        simp
      · rw [if_neg h, if_neg (by omega : ¬ i₀ ≤ n), if_neg (by omega : ¬ i₀ < n + 1)]

theorem getD_succ_le (α : List ℕ) (hα : α.Pairwise (· ≥ ·)) (t : ℕ) :
    α.getD (t + 1) 0 ≤ α.getD t 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  by_cases h : t + 1 < α.length
  · rw [List.getElem?_eq_getElem h, List.getElem?_eq_getElem (by omega)]
    simp only [Option.getD_some]
    exact (List.pairwise_iff_getElem.1 hα) t (t + 1) (by omega) h (by omega)
  · rw [List.getElem?_eq_none (by omega)]
    simp

theorem getD_length (α : List ℕ) : α.getD α.length 0 = 0 := by
  simp

theorem shape_sum (α : List ℕ) (hα : α.Pairwise (· ≥ ·)) (i₀ : ℕ) :
    ∑ t ∈ Finset.range α.length, (α.getD t 0 - α.getD (t + 1) 0) • (if i₀ < t + 1 then 1 else 0) =
      α.getD i₀ 0 := by
  have e : ∀ t, (α.getD t 0 - α.getD (t + 1) 0) • (if i₀ < t + 1 then 1 else 0) =
      if i₀ ≤ t then (α.getD t 0 - α.getD (t + 1) 0) else 0 := by
    intro t
    by_cases h : i₀ ≤ t
    · rw [if_pos (by omega), if_pos h]; simp
    · rw [if_neg (by omega), if_neg h]; simp
  simp only [e]
  rw [tele (fun t => α.getD t 0) (getD_succ_le α hα), getD_length]
  split_ifs with h
  · simp
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    simp

variable {p q r s m k : ℕ}

theorem leadT_hom_row (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s) (w : Ln p q r s → ℕ) (i₀ : Fin m)
    (hw : ∀ i j, w (ρ i, κ j) = if i = i₀ then 1 else 0) (t : ℕ) :
    IsWeightedHomogeneous w (leadT (varMat ρ κ) t) (if i₀.val < t then 1 else 0) := by
  classical
  unfold leadT
  split_ifs with hh hlt
  · have := minorPolynomial_isWeightedHomogeneous (R := ℂ) (fun i j : Fin t => (ρ (Fin.castLE hh.1 i), κ (Fin.castLE hh.2 j))) w
      (fun i => if Fin.castLE hh.1 i = i₀ then 1 else 0) (fun _ => 0) (fun i j => by simp [hw])
    have hs : ∑ i : Fin t, (if Fin.castLE hh.1 i = i₀ then 1 else 0) + ∑ _j : Fin t, 0 = 1 := by
      simp only [Finset.sum_const_zero, add_zero]
      rw [Finset.sum_eq_single ⟨i₀.val, hlt⟩]
      · simp [Fin.ext_iff]
      · intro i _ hi
        rw [if_neg]
        intro e
        apply hi
        ext
        simp [← e]
      · simp
    rw [hs] at this
    exact this
  · have := minorPolynomial_isWeightedHomogeneous (R := ℂ) (fun i j : Fin t => (ρ (Fin.castLE hh.1 i), κ (Fin.castLE hh.2 j))) w
      (fun i => if Fin.castLE hh.1 i = i₀ then 1 else 0) (fun _ => 0) (fun i j => by simp [hw])
    have hs : ∑ i : Fin t, (if Fin.castLE hh.1 i = i₀ then 1 else 0) + ∑ _j : Fin t, 0 = 0 := by
      simp only [Finset.sum_const_zero, add_zero]
      apply Finset.sum_eq_zero
      intro i _
      rw [if_neg]
      intro e
      apply hlt
      rw [← e]
      simp
    rw [hs] at this
    exact this
  · exact isWeightedHomogeneous_zero _ _ _
  · exact isWeightedHomogeneous_zero _ _ _

theorem leadT_hom_col (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s) (w : Ln p q r s → ℕ) (j₀ : Fin k)
    (hw : ∀ i j, w (ρ i, κ j) = if j = j₀ then 1 else 0) (t : ℕ) :
    IsWeightedHomogeneous w (leadT (varMat ρ κ) t) (if j₀.val < t then 1 else 0) := by
  classical
  unfold leadT
  split_ifs with hh hlt
  · have := minorPolynomial_isWeightedHomogeneous (R := ℂ) (fun i j : Fin t => (ρ (Fin.castLE hh.1 i), κ (Fin.castLE hh.2 j))) w
      (fun _ => 0) (fun j => if Fin.castLE hh.2 j = j₀ then 1 else 0) (fun i j => by simp [hw])
    have hs : ∑ _i : Fin t, 0 + ∑ j : Fin t, (if Fin.castLE hh.2 j = j₀ then 1 else 0) = 1 := by
      simp only [Finset.sum_const_zero, zero_add]
      rw [Finset.sum_eq_single ⟨j₀.val, hlt⟩]
      · simp [Fin.ext_iff]
      · intro j _ hj
        rw [if_neg]
        intro e
        apply hj
        ext
        simp [← e]
      · simp
    rw [hs] at this
    exact this
  · have := minorPolynomial_isWeightedHomogeneous (R := ℂ) (fun i j : Fin t => (ρ (Fin.castLE hh.1 i), κ (Fin.castLE hh.2 j))) w
      (fun _ => 0) (fun j => if Fin.castLE hh.2 j = j₀ then 1 else 0) (fun i j => by simp [hw])
    have hs : ∑ _i : Fin t, 0 + ∑ j : Fin t, (if Fin.castLE hh.2 j = j₀ then 1 else 0) = 0 := by
      simp only [Finset.sum_const_zero, zero_add]
      apply Finset.sum_eq_zero
      intro j _
      rw [if_neg]
      intro e
      apply hlt
      rw [← e]
      simp
    rw [hs] at this
    exact this
  · exact isWeightedHomogeneous_zero _ _ _
  · exact isWeightedHomogeneous_zero _ _ _

theorem leadT_hom_zero (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s) (w : Ln p q r s → ℕ)
    (hw : ∀ i j, w (ρ i, κ j) = 0) (t : ℕ) :
    IsWeightedHomogeneous w (leadT (varMat ρ κ) t) 0 := by
  unfold leadT
  split_ifs with hh
  · have := minorPolynomial_isWeightedHomogeneous (R := ℂ) (fun i j : Fin t => (ρ (Fin.castLE hh.1 i), κ (Fin.castLE hh.2 j))) w
      (fun _ => 0) (fun _ => 0) (fun i j => by simp [hw])
    simp only [Finset.sum_const_zero, add_zero] at this
    exact this
  · exact isWeightedHomogeneous_zero _ _ _

theorem shapeProd_hom_of (M : Matrix (Fin m) (Fin k) (Pol p q r s)) (w : Ln p q r s → ℕ) (α : List ℕ)
    (deg : ℕ → ℕ) (h : ∀ t, IsWeightedHomogeneous w (leadT M t) (deg t)) :
    IsWeightedHomogeneous w (shapeProd M α)
      (∑ t ∈ Finset.range α.length, (α.getD t 0 - α.getD (t + 1) 0) • deg (t + 1)) := by
  unfold shapeProd
  exact IsWeightedHomogeneous.prod _ _ _ fun t _ => (h (t + 1)).pow _

theorem shapeProd_hom_row (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s) (w : Ln p q r s → ℕ) (i₀ : Fin m)
    (hw : ∀ i j, w (ρ i, κ j) = if i = i₀ then 1 else 0) (α : List ℕ) (hα : α.Pairwise (· ≥ ·)) :
    IsWeightedHomogeneous w (shapeProd (varMat ρ κ) α) (α.getD i₀.val 0) := by
  have := shapeProd_hom_of (varMat ρ κ) w α _ (leadT_hom_row ρ κ w i₀ hw)
  rwa [shape_sum α hα] at this

theorem shapeProd_hom_col (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s) (w : Ln p q r s → ℕ) (j₀ : Fin k)
    (hw : ∀ i j, w (ρ i, κ j) = if j = j₀ then 1 else 0) (α : List ℕ) (hα : α.Pairwise (· ≥ ·)) :
    IsWeightedHomogeneous w (shapeProd (varMat ρ κ) α) (α.getD j₀.val 0) := by
  have := shapeProd_hom_of (varMat ρ κ) w α _ (leadT_hom_col ρ κ w j₀ hw)
  rwa [shape_sum α hα] at this

theorem shapeProd_hom_zero (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s) (w : Ln p q r s → ℕ)
    (hw : ∀ i j, w (ρ i, κ j) = 0) (α : List ℕ) :
    IsWeightedHomogeneous w (shapeProd (varMat ρ κ) α) 0 := by
  have := shapeProd_hom_of (varMat ρ κ) w α _ (leadT_hom_zero ρ κ w hw)
  simpa using this

end PI.FJMX
end
end

