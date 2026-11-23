module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0106
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0180
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0172
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0185

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VPowLatticeLeImageAddLPowOfFiniteCokernel
section
noncomputable section

open PowerSeries GlobalTheory.BK Matrix GlobalTheory.LiftCoker

theorem GlobalTheory.LiftCoker.vPow_mem_imL_add_lPow : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (η H : ℕ) (D₁ : BKDat O K l e a ι η H) (D₂ : BKDat O K l e a κ η H) (F : BKHom D₁ D₂), IsFiniteLength (A O K) F.coker → ∀ b : ℕ, 1 ≤ b → H + η + b ≤ l → ∀ x ∈ D₂.L, ∃ y ∈ D₁.L, ∃ z ∈ D₂.L, ((X : K⟦X⟧) ^ e) ^ (H + η + b) • x = F.app y + (l : K) ^ b • z := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ η H D₁ D₂ F hfin b hb hlb x hx
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  obtain ⟨n, hn⟩ := _root_.GlobalTheory.UPow.exists_uIn_pow_smul_eq_zero O K _ hfin
  have hX : ∀ τ, (X : O⟦X⟧) ^ n ∈ colon O K (F.mat τ) := by
    intro τ w hw
    have hW : (Pi.single τ w : Vec K a κ) ∈ D₂.M := mem_tot.2 fun σ i => by
      by_cases h : σ = τ
      · subst h; simpa using hw i
      · simp [h]
    have h1 := hn (Submodule.Quotient.mk ⟨_, hW⟩)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.submoduleOf, Submodule.mem_comap] at h1
    obtain ⟨m, hm, hm'⟩ := h1
    refine ⟨m τ, fun j => mem_tot.1 hm τ j, ?_⟩
    have h2 := congrFun hm' τ
    simp only [LinearMap.restrictScalars_apply, BK.Hom.app_apply] at h2
    rw [h2]
    simp [Submodule.coe_smul, Subalgebra.smul_def]
  have key := _root_.GlobalTheory.frobenius_ideal_degree_bound (O := O) l hl2 (PowerSeries.expand l (Fact.out : l.Prime).ne_zero)
    (fun f m => PowerSeries.coeff_expand _ _ f) a e (H + η) b (fun τ => colon O K (F.mat τ)) hb hlb
    (fun τ => ⟨n, Ideal.mem_sup_left (hX τ)⟩)
    (fun τ α hα => GlobalTheory.T.colonIdeal_frobenius_le_map_expand O K l ι κ _ (_root_.GlobalTheory.LiftCoker.E_pow_mul_mem_colon_frob O K l e a ι κ η H D₁ D₂ F τ α hα))
  have comp : ∀ τ, ∀ w : κ → K⟦X⟧, (∀ i, w i ∈ A O K) → ∃ m : ι → K⟦X⟧, (∀ j, m j ∈ A O K) ∧
      ∃ w' : κ → K⟦X⟧, (∀ i, w' i ∈ A O K) ∧
        ((X : K⟦X⟧) ^ e) ^ (H + η + b) • w = (F.mat (τ - 1)).map (frob K l) *ᵥ m + (l : K⟦X⟧) ^ b • w' := by
    intro τ w hw
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.1 (key (τ - 1))
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hq
    obtain ⟨m, hm, hmeq⟩ := GlobalTheory.T.colonIdeal_map_expand_le_frobenius O K l ι κ _ hp w hw
    refine ⟨m, hm, PowerSeries.map (algebraMap O K) c • w, fun i => ?_, ?_⟩
    · rw [Pi.smul_apply, smul_eq_mul]
      exact mul_mem (map_mem_A c) (hw i)
    · have h3 := congrArg (PowerSeries.map (algebraMap O K)) hpq
      rw [map_add (f := _), map_mul, map_pow, map_pow, map_X, map_natCast] at h3
      rw [← pow_mul, ← h3, add_smul, hmeq, smul_smul, mul_comm]
  choose w hw hxw using fun τ => D₂.mem_extc.1 (mem_tot.1 hx τ)
  choose m hm w' hw' hmw using fun τ => comp τ (w τ) (hw τ)
  refine ⟨fun τ => D₁.mx τ *ᵥ m τ, mem_tot.2 fun τ => D₁.mem_extc.2 ⟨m τ, hm τ, rfl⟩,
    fun τ => D₂.mx τ *ᵥ w' τ, mem_tot.2 fun τ => D₂.mem_extc.2 ⟨w' τ, hw' τ, rfl⟩, ?_⟩
  funext τ
  have hsm : ∀ v : κ → K⟦X⟧, (l : K) ^ b • v = (l : K⟦X⟧) ^ b • v := fun v => by
    rw [← algebraMap_smul K⟦X⟧ ((l : K) ^ b) v, map_pow, map_natCast]
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, hsm, BK.Hom.app_apply, Matrix.mulVec_mulVec,
    F.comm τ, hxw τ, ← Matrix.mulVec_smul, hmw τ, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZetaSeriesHigherTermsMemLPowBreuilKisin
section
noncomputable section

namespace GlobalTheory

open PowerSeries GlobalTheory.BK

theorem nat_mul_add_le_pow {l : ℕ} (hl : 2 ≤ l) (n : ℕ) : n * l + l ≤ l ^ (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have h1 := Nat.mul_le_mul_right l ih
    have h2 := Nat.mul_le_mul_left (n * l + l) hl
    nlinarith

theorem zeta_add_lphi_conn_mem : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), ∀ (y₀ : Vec K a ι), 1 ≤ η → η < H → 14 * H < l → E K l e ^ η • y₀ ∈ D.M → ∃ r ∈ D.MM, D.zeta ((X : K⟦X⟧) ^ e • y₀) + D.lphi (D.conn ((X : K⟦X⟧) ^ e • y₀)) = (l : K) ^ (l - 14 * H) • r := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D y₀ hη hηH hHl hy₀
  set y : Vec K a ι := (X : K⟦X⟧) ^ e • y₀ with hy
  set A := l - 14 * H with hA
  have hl0 : (l : K) ≠ 0 := l_ne_zero (K := K) l
  have hlA : (l : K) ^ A ≠ 0 := pow_ne_zero _ hl0
  set c : K := ((l : K) ^ A)⁻¹ with hc
  set w : Vec K a ι := c • (D.zeta y + D.lphi (D.conn y)) with hw
  let t : ℕ → Vec K a ι := fun n => -(c • (D.lphi ^ (n + 2)) (D.conn y))
  have hterm : ∀ n, ∃ v ∈ D.MM, t n = (l : K) ^ n • v := by
    intro n
    obtain ⟨w₁, hw₁, h₁⟩ := _root_.GlobalTheory.BK.lphi_pow_conn_X_pow_smul_mem O K l e a ι η H D y₀ hη hy₀ (n + 1)
    obtain ⟨w', hw', h₂⟩ := GlobalTheory.T.exists_X_pow_smul_eq_prime_pow_smul_phiModule O K l e a ι D.toPhiMod (n + 1) w₁ hw₁
    set B := H + 2 * η + (n + 1) * (η - 1) with hB
    have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
    have hineq : B + A + n ≤ l ^ (n + 1) := by
      have h1 := nat_mul_add_le_pow hl2 n
      have h2 : (n + 1) * (η - 1) ≤ (n + 1) * H := Nat.mul_le_mul_left _ (by omega)
      have h3 : n * (H + 1) ≤ n * l := Nat.mul_le_mul_left _ (by omega)
      have h4 : (n + 1) * H = n * H + H := by ring
      have h5 : n * (H + 1) = n * H + n := by ring
      omega
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hineq
    rw [h₂, hd, show B + A + n + d = B + (A + (n + d)) by ring, pow_add (l : K) B, mul_smul] at h₁
    have h₃ := congrArg (fun v => ((l : K) ^ B)⁻¹ • v) h₁
    simp only [inv_smul_smul₀ (pow_ne_zero B hl0)] at h₃
    refine ⟨-((l : K) ^ d • w'), neg_mem (PhiMod.l_pow_smul_mem_MM _ d hw'), ?_⟩
    change -(c • (D.lphi ^ (n + 1 + 1)) (D.conn y)) = _
    rw [h₃, pow_add, mul_smul, hc, inv_smul_smul₀ hlA, pow_add, mul_smul, smul_neg]
  have hpart : ∀ m, w - ∑ n ∈ Finset.range m, t n ∈ uPow K a ι m := by
    intro m
    have key := D.zeta_add_sum_mem y (m + 1)
    rw [Finset.sum_range_succ'] at key
    have heq : w - ∑ n ∈ Finset.range m, t n = c • (D.zeta y + (∑ n ∈ Finset.range m,
        (D.lphi ^ (n + 1 + 1)) (D.conn y) + (D.lphi ^ (0 + 1)) (D.conn y))) := by
      simp only [t, hw, Finset.sum_neg_distrib, sub_neg_eq_add, zero_add, pow_one, smul_add,
        Finset.smul_sum]
      abel
    rw [heq]
    exact Submodule.smul_of_tower_mem _ c (uPow_anti (by omega) key)
  refine ⟨w, GlobalTheory.T.mem_phiModuleLattice_of_adic_series_prime_pow_terms O K l e a ι D.toPhiMod w t hterm hpart, ?_⟩
  rw [hw, hc, smul_inv_smul₀ hlA]

end GlobalTheory
end
end

