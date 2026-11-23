module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0052

@[expose] public section

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows

namespace GlobalTheory.ColRows.LastSideProof

def ext {N : ℕ} (lam : DomWeight N) (i : ℕ) : ℤ := if h : i < N then lam.w ⟨i, h⟩ else 0

theorem ext_of {N : ℕ} (lam : DomWeight N) (i : Fin N) : ext lam i = lam.w i := by
  simp [ext, i.2]

theorem first_difference_eq_range_sum {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) :
    Br.d0 hN lam sg = ∑ i ∈ Finset.range n, (ext sg i - ext lam (i + 1)) := by
  rw [Br.d0, ← Fin.sum_univ_eq_sum_range (fun i => ext sg i - ext lam (i + 1))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Br.aBr, ← ext_of sg i, ← ext_of lam]
  rfl

theorem nBr_eq_sub {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) :
    Br.nBr lam sg = lam.w ⟨0, by omega⟩ - Br.d0 hN lam sg := by
  subst hN
  have h : ∀ i : Fin n, lam.w (Br.iS rfl i) = lam.w i.succ := fun i => rfl
  simp only [Br.nBr, Br.d0, Br.aBr, h, Finset.sum_sub_distrib, Fin.sum_univ_succ]
  have h0 : lam.w 0 = lam.w ⟨0, by omega⟩ := rfl
  rw [h0]
  ring

theorem first_difference_head_le {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) (hI : Br.Interlace hN lam sg) :
    ∀ p, 1 ≤ p → p ≤ n → ∑ i ∈ Finset.range p, (ext sg i - ext lam (i + 1)) ≤ ext sg 0 - ext lam p := by
  intro p hp1 hpn
  induction p with
  | zero => omega
  | succ p ih =>
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp
    · rw [Finset.sum_range_succ]
      have h1 := ih hp (by omega)
      have h2 := (hI ⟨p, by omega⟩).2
      rw [Br.bBr, ← ext_of sg, ← ext_of lam] at h2
      have e : ((Br.iC hN ⟨p, by omega⟩ : Fin N) : ℕ) = p := rfl
      rw [e] at h2
      simp only at h2
      linarith

theorem dOne_le {N n : ℕ} (hN : N = n + 1) (lam : DomWeight N) (sg : DomWeight n) (p : ℕ) (hp0 : 0 < p) (hpn : p < n) :
    GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne hN lam sg ≤ 2 * Br.d0 hN lam sg + (ext lam 1 - ext lam p) + (ext lam (p + 1) - ext lam n) := by
  set D := Br.d0 hN lam sg
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne hN lam sg = ∑ i ∈ Finset.range n, min (ext lam i - ext lam (i + 1)) D := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne, ← Fin.sum_univ_eq_sum_range (fun i => min (ext lam i - ext lam (i + 1)) D)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ext_of lam, ← ext_of lam]
    rfl
  rw [e1]
  calc ∑ i ∈ Finset.range n, min (ext lam i - ext lam (i + 1)) D
      ≤ ∑ i ∈ Finset.range n, ((ext lam i - ext lam (i + 1)) +
          (if i = 0 ∨ i = p then D - (ext lam i - ext lam (i + 1)) else 0)) := by
        refine Finset.sum_le_sum fun i _ => ?_
        split_ifs
        · have := min_le_right (ext lam i - ext lam (i + 1)) D; linarith
        · have := min_le_left (ext lam i - ext lam (i + 1)) D; linarith
    _ = (ext lam 0 - ext lam n) + ((D - (ext lam 0 - ext lam (0 + 1))) + (D - (ext lam p - ext lam (p + 1)))) := by
        rw [Finset.sum_add_distrib, Finset.sum_range_sub' (fun i => ext lam i)]
        congr 1
        rw [Finset.sum_eq_add (f := fun i => if i = 0 ∨ i = p then D - (ext lam i - ext lam (i + 1)) else 0)
          0 p (by omega : 0 ≠ p)]
        · simp [hp0.ne']
        · intro c _ hc; simp [hc.1, hc.2]
        · intro h; exact absurd (Finset.mem_range.2 (by omega)) h
        · intro h; exact absurd (Finset.mem_range.2 hpn) h
    _ = 2 * D + (ext lam 1 - ext lam p) + (ext lam (p + 1) - ext lam n) := by ring

end GlobalTheory.ColRows.LastSideProof

namespace GlobalTheory.ColRows.LastSideProof

theorem sum_range_mul (f : ℕ → ℚ) (c : ℕ) : ∀ m : ℕ,
    ∑ x ∈ Finset.range (m * c), f x = ∑ B ∈ Finset.range m, ∑ ρ ∈ Finset.range c, f (B * c + ρ)
  | 0 => by simp
  | m + 1 => by
    rw [Nat.succ_mul, Finset.sum_range_add, sum_range_mul f c m, Finset.sum_range_succ]

section Place

variable {X : Fields} {Word : Type} {R : Ranks} (W : Wts X Word R) (u : Word) (τ : X.Tau)

theorem ext_lam_lo (i : ℕ) (hi : i < R.k) :
    (ext (W.lamTrue u R.m τ) i : ℚ) =
      (W.hc u τ).u ⟨i, hi⟩ - ((R.k : ℚ) - 1) / 2 + (i : ℚ) - (R.m : ℚ) * (((R.t : ℚ) + 1) / 2) := by
  have hiN : i < R.N R.m := by unfold Ranks.N; omega
  rw [ext, dite_eq_left hiN]
  exact GlobalTheory.BranchMembers.lamTrue_lo W u τ ⟨i, hiN⟩ ⟨i, hi⟩ rfl

theorem ext_lam_hi (B ρ : ℕ) (hB : B < R.m) (hρ : ρ < R.t + 1) :
    (ext (W.lamTrue u R.m τ) (R.k + B * (R.t + 1) + ρ) : ℚ) =
      -(RowPar.of (W.hc u τ)).eAt B + (R.k : ℚ) / 2 + (2 * (B : ℚ) + 1) * (((R.t : ℚ) + 1) / 2) -
        (R.m : ℚ) * (((R.t : ℚ) + 1) / 2) := by
  have h1 : (B + 1) * (R.t + 1) ≤ R.m * (R.t + 1) := Nat.mul_le_mul_right _ hB
  have hiN : R.k + B * (R.t + 1) + ρ < R.N R.m := by
    unfold Ranks.N; rw [Nat.succ_mul] at h1; omega
  rw [ext, dite_eq_left hiN]
  exact GlobalTheory.BranchMembers.lamTrue_hi W u τ ⟨_, hiN⟩ B ρ hρ rfl

theorem ext_sg (hW : W.Ok) (i : ℕ) (hi : i < R.N R.m - 1) :
    (ext (W.sgTrue τ) i : ℚ) =
      (RowPar.of (W.hc u τ)).sgHC i - RowPar.sh R - ((R.k : ℚ) - 2) / 2 - (R.m : ℚ) * (((R.t : ℚ) + 1) / 2) + (i : ℚ) := by
  rw [ext, dite_eq_left hi]
  exact GlobalTheory.BranchMembers.sgTrue_entry W hW u τ ⟨i, hi⟩

end Place

end GlobalTheory.ColRows.LastSideProof

namespace GlobalTheory.ColRows.LastSideProof

section Place2

variable {X : Fields} {Word : Type} {R : Ranks} (W : Wts X Word R) (hW : W.Ok) (u : Word) (τ : X.Tau)
include hW

theorem block_sum (B : ℕ) (hB : B < R.m) :
    ∑ ρ ∈ Finset.range (R.t + 1),
        ((ext (W.sgTrue τ) (R.k - 1 + (B * (R.t + 1) + ρ)) - ext (W.lamTrue u R.m τ) (R.k - 1 + (B * (R.t + 1) + ρ) + 1) : ℤ) : ℚ) =
      (RowPar.of (W.hc u τ)).eAt B - (RowPar.of (W.hc u τ)).bAt B - ((R.t : ℚ) + 1) / 2 := by
  have hk := R.m_add_three_le_k
  have h1 : (B + 1) * (R.t + 1) ≤ R.m * (R.t + 1) := Nat.mul_le_mul_right _ hB
  rw [Nat.succ_mul] at h1
  have hn : ∀ ρ, ρ < R.t + 1 → R.k - 1 + (B * (R.t + 1) + ρ) < R.N R.m - 1 := by
    intro ρ hρ; unfold Ranks.N; omega
  have ck : ((R.k - 1 : ℕ) : ℚ) = (R.k : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [Finset.sum_range_succ']
  have e0 : R.k - 1 + (B * (R.t + 1) + 0) = R.k - 1 + B * (R.t + 1) := by omega
  have e0' : R.k - 1 + (B * (R.t + 1) + 0) + 1 = R.k + B * (R.t + 1) + 0 := by omega
  have z0 := ext_sg W u τ hW _ (hn 0 (by omega))
  rw [e0, RowPar.sgHC_b] at z0
  have l0 := ext_lam_hi W u τ B 0 hB (by omega)
  have hzero : ∀ ρ ∈ Finset.range R.t,
      ((ext (W.sgTrue τ) (R.k - 1 + (B * (R.t + 1) + (ρ + 1))) -
        ext (W.lamTrue u R.m τ) (R.k - 1 + (B * (R.t + 1) + (ρ + 1)) + 1) : ℤ) : ℚ) = 0 := by
    intro ρ hρ
    rw [Finset.mem_range] at hρ
    have e1 : R.k - 1 + (B * (R.t + 1) + (ρ + 1)) = R.k - 1 + B * (R.t + 1) + (ρ + 1) := by omega
    have e1' : R.k - 1 + (B * (R.t + 1) + (ρ + 1)) + 1 = R.k + B * (R.t + 1) + (ρ + 1) := by omega
    have z1 := ext_sg W u τ hW _ (hn (ρ + 1) (by omega))
    rw [e1, RowPar.sgHC_e _ B (ρ + 1) (by omega) (by omega)] at z1
    have l1 := ext_lam_hi W u τ B (ρ + 1) hB (by omega)
    rw [e1', e1]
    push_cast
    rw [z1, l1]
    push_cast [ck]
    ring
  rw [Finset.sum_eq_zero hzero, zero_add]
  rw [e0', e0]
  push_cast
  rw [z0, l0]
  push_cast [ck]
  unfold RowPar.sh
  ring

theorem bottomRank_sum_le_two_mul_totalRank :
    ((Br.d0 (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ) : ℤ) : ℚ) ≤
      (W.hc u τ).v ⟨0, by have := R.m_add_three_le_k; omega⟩ - (W.hc u τ).u ⟨R.k - 1, by have := R.m_add_three_le_k; omega⟩ -
        (R.k : ℚ) + 3 / 2 +
        ∑ B ∈ Finset.range R.m, ((RowPar.of (W.hc u τ)).eAt B - (RowPar.of (W.hc u τ)).bAt B - ((R.t : ℚ) + 1) / 2) := by
  have hk := R.m_add_three_le_k
  have hI := GlobalTheory.BranchMembers.interlace W hW u τ
  have hn : R.N R.m - 1 = (R.k - 1) + R.m * (R.t + 1) := by unfold Ranks.N; omega
  have hhead := first_difference_head_le (N_m_succ R) _ _ hI (R.k - 1) (by omega) (by omega)
  have hsplit : ∀ f : ℕ → ℤ, ∑ i ∈ Finset.range (R.N R.m - 1), f i =
      ∑ i ∈ Finset.range (R.k - 1), f i + ∑ x ∈ Finset.range (R.m * (R.t + 1)), f (R.k - 1 + x) := fun f => by
    rw [hn, Finset.sum_range_add]
  rw [first_difference_eq_range_sum, hsplit]
  push_cast
  have hhead' : (∑ i ∈ Finset.range (R.k - 1), ((ext (W.sgTrue τ) i : ℚ) - (ext (W.lamTrue u R.m τ) (i + 1) : ℚ))) ≤
      (ext (W.sgTrue τ) 0 : ℚ) - (ext (W.lamTrue u R.m τ) (R.k - 1) : ℚ) := by exact_mod_cast hhead
  have htail : ∑ x ∈ Finset.range (R.m * (R.t + 1)),
      ((ext (W.sgTrue τ) (R.k - 1 + x) : ℚ) - (ext (W.lamTrue u R.m τ) (R.k - 1 + x + 1) : ℚ)) =
      ∑ B ∈ Finset.range R.m, ((RowPar.of (W.hc u τ)).eAt B - (RowPar.of (W.hc u τ)).bAt B - ((R.t : ℚ) + 1) / 2) := by
    rw [sum_range_mul (fun x => (ext (W.sgTrue τ) (R.k - 1 + x) : ℚ) - (ext (W.lamTrue u R.m τ) (R.k - 1 + x + 1) : ℚ))]
    refine Finset.sum_congr rfl fun B hB => ?_
    rw [← block_sum W hW u τ B (Finset.mem_range.1 hB)]
    push_cast
    rfl
  rw [htail]
  have s0 := ext_sg W u τ hW 0 (by unfold Ranks.N; omega)
  rw [RowPar.sgHC_lo _ (by omega), RowPar.vb_lo _ (by omega)] at s0
  have l1 := ext_lam_lo W u τ (R.k - 1) (by omega)
  have ck : ((R.k - 1 : ℕ) : ℚ) = (R.k : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [s0, l1, ck] at hhead'
  unfold RowPar.sh at hhead'
  push_cast at hhead'
  linarith

end Place2

end GlobalTheory.ColRows.LastSideProof

namespace GlobalTheory.ColRows.LastSideProof

section Place3

variable {X : Fields} {Word : Type} {R : Ranks} (W : Wts X Word R) (hW : W.Ok) (u : Word) (τ : X.Tau)
include hW

theorem dOne_le_place :
    ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ) : ℤ) : ℚ) ≤
      3 * ((Br.d0 (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ) : ℤ) : ℚ) +
        ((W.hc u τ).u ⟨1, by have := R.m_add_three_le_k; omega⟩ - (W.hc u τ).v ⟨R.k - 2, by have := R.m_add_three_le_k; omega⟩ +
          5 / 2 - (R.k : ℚ)) +
        ((RowPar.of (W.hc u τ)).eAt (R.m - 1) - (RowPar.of (W.hc u τ)).eAt 0 - ((R.m : ℚ) - 1) * ((R.t : ℚ) + 1)) := by
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  have hI := GlobalTheory.BranchMembers.interlace W hW u τ
  have hNn : R.N R.m - 1 = R.k + (R.m - 1) * (R.t + 1) + R.t := by
    have e : (R.m - 1) * (R.t + 1) + (R.t + 1) = R.m * (R.t + 1) := by
      rw [← Nat.succ_mul]; congr 1; omega
    unfold Ranks.N
    generalize (R.m - 1) * (R.t + 1) = A at e ⊢
    generalize R.m * (R.t + 1) = A' at e ⊢
    omega
  have hpn : R.k - 1 < R.N R.m - 1 := by rw [hNn]; omega
  have h1 := dOne_le (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ) (R.k - 1) (by omega) hpn

  have hnonneg : ∀ i ∈ Finset.range (R.N R.m - 1), 0 ≤ ext (W.sgTrue τ) i - ext (W.lamTrue u R.m τ) (i + 1) := by
    intro i hi
    rw [Finset.mem_range] at hi
    have h2 := (hI ⟨i, hi⟩).1
    rw [Br.aBr, ← ext_of (W.sgTrue τ), ← ext_of (W.lamTrue u R.m τ)] at h2
    exact h2
  have hsingle := Finset.single_le_sum hnonneg (Finset.mem_range.2 (by omega : R.k - 2 < R.N R.m - 1))
  rw [← first_difference_eq_range_sum (N_m_succ R)] at hsingle
  have e2 : R.k - 2 + 1 = R.k - 1 := by omega
  rw [e2] at hsingle
  have e3 : R.k - 1 + 1 = R.k + 0 * (R.t + 1) + 0 := by omega
  have hext : ext (W.lamTrue u R.m τ) (R.N R.m - 1) = ext (W.lamTrue u R.m τ) (R.k + (R.m - 1) * (R.t + 1) + R.t) :=
    congrArg _ hNn
  rw [e3, hext] at h1
  have l1 := ext_lam_lo W u τ 1 (by omega)
  have lk := ext_lam_lo W u τ (R.k - 1) (by omega)
  have lh0 := ext_lam_hi W u τ 0 0 (by omega) (by omega)
  have lh1 := ext_lam_hi W u τ (R.m - 1) R.t (by omega) (by omega)
  have s2 := ext_sg W u τ hW (R.k - 2) (by omega)
  rw [RowPar.sgHC_lo _ (by omega), RowPar.vb_lo _ (by omega)] at s2
  have h1q : ((GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum.dOne (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ) : ℤ) : ℚ) ≤
      2 * ((Br.d0 (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ) : ℤ) : ℚ) +
        ((ext (W.lamTrue u R.m τ) 1 : ℚ) - (ext (W.lamTrue u R.m τ) (R.k - 1) : ℚ)) +
        ((ext (W.lamTrue u R.m τ) (R.k + 0 * (R.t + 1) + 0) : ℚ) -
          (ext (W.lamTrue u R.m τ) (R.k + (R.m - 1) * (R.t + 1) + R.t) : ℚ)) := by exact_mod_cast h1
  have hsq : (ext (W.sgTrue τ) (R.k - 2) : ℚ) - (ext (W.lamTrue u R.m τ) (R.k - 1) : ℚ) ≤
      ((Br.d0 (N_m_succ R) (W.lamTrue u R.m τ) (W.sgTrue τ) : ℤ) : ℚ) := by exact_mod_cast hsingle
  have ck1 : ((R.k - 1 : ℕ) : ℚ) = (R.k : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have ck2 : ((R.k - 2 : ℕ) : ℚ) = (R.k : ℚ) - 2 := by rw [Nat.cast_sub (by omega)]; simp
  have cm1 : ((R.m - 1 : ℕ) : ℚ) = (R.m : ℚ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [l1, lk, lh0, lh1] at h1q
  rw [s2, lk] at hsq
  simp only [ck1, ck2, cm1, Nat.cast_zero, Nat.cast_one] at h1q hsq
  unfold RowPar.sh at hsq
  have e4 : (⟨R.k - 2, by omega⟩ : Fin (R.k - 1)) = ⟨R.k - 2, by omega⟩ := rfl
  nlinarith [h1q, hsq]

end Place3

end GlobalTheory.ColRows.LastSideProof

namespace GlobalTheory.ColRows.LastSideProof

theorem uW_first (N : NumDatum) (δ : Code N) (z : RPl N.R) (h : 0 < N.R.k) : N.uW δ z ⟨0, h⟩ = (N.hc z).u ⟨0, h⟩ := by
  simp [NumDatum.uW]

theorem uW_last (N : NumDatum) (δ : Code N) (z : RPl N.R) (h : N.R.k - 1 < N.R.k) :
    N.uW δ z ⟨N.R.k - 1, h⟩ = (N.hc z).u ⟨N.R.k - 1, h⟩ := by
  unfold NumDatum.uW
  rw [dite_eq_right (by simp only; omega)]

theorem castQ {a b : ℚ} (h : a ≤ b) : (a : ℝ) ≤ (b : ℝ) := Rat.cast_le.mpr h

end GlobalTheory.ColRows.LastSideProof
