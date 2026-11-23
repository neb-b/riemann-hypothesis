module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0012
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.Bundle0007
public import Mathlib

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHBSt
section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

def DeuringHeilbronnMB : Prop :=
  ∃ (c₀ c₁ c₂ : ℝ) (B : ℕ), 0 < c₀ ∧ 0 < c₁ ∧ 0 < c₂ ∧
    ∀ (M : ℕ) [NeZero M] (χ₁ χ : DirichletCharacter ℂ M) (β₁ T : ℝ) (ρ : ℂ),
    3 ≤ M → 2 ≤ T → χ₁ ^ 2 = 1 → χ₁ ≠ 1 → DirichletCharacter.LFunction χ₁ (β₁ : ℂ) = 0 →
    1 - c₁ / Real.log ((M : ℝ) * T) < β₁ → β₁ < 1 →
    IsLZero χ ρ → 1 - c₀ ≤ ρ.re → |ρ.im| ≤ T → (χ, ρ) ≠ (χ₁, (β₁ : ℂ)) →
    c₂ * Real.log (c₁ / ((1 - β₁) * Real.log ((M : ℝ) * T) ^ B)) / Real.log ((M : ℝ) * T) ≤ 1 - ρ.re

def ZeroSumOfB : Prop := LogDensityM → DeuringHeilbronnMB → ZeroSum

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDHSt
section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

def DHTuran : Prop :=
  ∃ (c : ℝ) (A B : ℕ), 0 < c ∧ ∀ (n K : ℕ) (z : Fin n → ℂ), 1 ≤ n → B * n ≤ K →
    (∀ i, ‖z i‖ ≤ 1) → (∃ i, ‖z i‖ = 1) → (∀ i, ‖z i‖ ^ 2 ≤ 2 * (z i).re) →
    ∃ k : ℕ, K ≤ k ∧ k ≤ A * K ∧ c ^ K ≤ (∑ i, z i ^ k).re

def DHPos : Prop :=
  ∀ (M : ℕ) [NeZero M] (χ₁ χ : DirichletCharacter ℂ M) (γ σ : ℝ) (k : ℕ), χ₁ ^ 2 = 1 → 1 < σ →
    0 ≤ ((-1 : ℂ) ^ k * (iteratedDeriv k (negLD (1 : DirichletCharacter ℂ M)) (σ : ℂ)
        + iteratedDeriv k (negLD χ₁) (σ : ℂ)
        + iteratedDeriv k (negLD χ) ((σ : ℂ) + γ * I)
        + iteratedDeriv k (negLD (χ * χ₁)) ((σ : ℂ) + γ * I))).re

def DHCauchy : Prop :=
  ∀ (f : ℂ → ℂ) (z₀ : ℂ) (r B : ℝ), 0 < r → 1 ≤ B →
    DifferentiableOn ℂ f (Metric.closedBall z₀ r) → f z₀ ≠ 0 →
    (∀ z ∈ Metric.closedBall z₀ r, ‖f z‖ ≤ B * ‖f z₀‖) →
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall z₀ (r / 3) ∧ f ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ Real.log B / Real.log 2 ∧
      ∀ (k : ℕ) (s : ℂ), s ∈ Metric.closedBall z₀ (r / 12) → f s ≠ 0 →
        ‖(-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (fun z => -(deriv f z / f z)) s
            + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1)‖ ≤ 72 * Real.log B / r * (12 / r) ^ k

def DHLocal : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M) (t : ℝ), 3 ≤ M →
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (‖ρ - ((26 / 25 : ℂ) + t * I)‖ ≤ 4 / 25 ∧ IsLZero ψ ρ)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      (∀ ρ ∈ Z, ρ.re < 1) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ C * Real.log ((M : ℝ) * (|t| + 2)) ∧
      ∀ (k : ℕ) (s : ℂ), 1 < s.re → ‖s - ((26 / 25 : ℂ) + t * I)‖ ≤ 1 / 25 →
        ‖(-1 : ℂ) ^ k / (k.factorial : ℂ) * iteratedDeriv k (negLD ψ) s
            - (if ψ = 1 then 1 / (s - 1) ^ (k + 1) else 0)
            + ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) ^ (k + 1)‖ ≤ C * Real.log ((M : ℝ) * (|t| + 2)) * 25 ^ k

def DHLocalOf : Prop := DHCauchy → DHLocal

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTDensSt
section
open Complex Finset

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens

open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet

def qd (M : ℕ) (T : ℝ) : ℕ := ⌈(M : ℝ) * T⌉₊

def pYd (M : ℕ) (T : ℝ) : ℕ := qd M T ^ 3

def pJd (M : ℕ) (T : ℝ) : ℕ := 8 * (Nat.log 2 (qd M T) + 1)

def pNd (M : ℕ) (T : ℝ) : ℕ := 2 ^ pJd M T

def blkD (Y N U : ℕ) (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑ n ∈ Ioc U (2 * U), mco Y N n * f n * (n : ℂ) ^ (-s)

def DivSq : Prop :=
  ∀ x : ℕ, 1 ≤ x → ∑ n ∈ Icc 1 x, ((n.divisors.card : ℕ) : ℝ) ^ 2 ≤ (x : ℝ) * (1 + Real.log x) ^ 3

def CoefficientBlockBound : Prop :=
  ∀ (Y N U : ℕ) (σ : ℝ), 1 ≤ U → 0 ≤ σ →
    ∑ n ∈ Ioc U (2 * U), (‖mco Y N n‖ * (n : ℝ) ^ (-σ)) ^ 2 ≤
      2 * (U : ℝ) ^ (1 - 2 * σ) * (1 + Real.log (2 * U)) ^ 3

def PairCross : Prop :=
  ∀ (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M), ψ ≠ 1 → ∀ w : ℂ, 0 ≤ w.re → ∀ U : ℕ, 1 ≤ U →
    ‖∑ n ∈ Ioc U (2 * U), ψ (n : ZMod M) * (n : ℂ) ^ (-w)‖ ≤ 4 * ((M : ℝ) + 1) * (1 + ‖w‖)

def PairSame : Prop :=
  ∀ (M : ℕ) [NeZero M] (w : ℂ), 0 ≤ w.re → w.re ≤ 1 → w.im ≠ 0 → ∀ U : ℕ, 1 ≤ U →
    ‖∑ n ∈ Ioc U (2 * U), (1 : DirichletCharacter ℂ M) (n : ZMod M) * (n : ℂ) ^ (-w)‖ ≤
      4 * (U : ℝ) ^ (1 - w.re) / |w.im| + 4 * ((M : ℝ) + 1) * (1 + ‖w‖)

def Spacing : Prop :=
  ∀ (P : Finset ℝ) (T : ℝ), 0 ≤ T → (∀ x ∈ P, |x| ≤ T) → (∀ x ∈ P, ∀ y ∈ P, x ≠ y → 1 ≤ |x - y|) →
    (P.card : ℝ) ≤ 2 * T + 1 ∧ ∀ t ∈ P, ∑ x ∈ P.erase t, 1 / |t - x| ≤ 2 * (1 + Real.log (2 * T + 1))

def Triv : Prop :=
  ∀ (M : ℕ) [NeZero M] (T : ℝ) (S : Finset (DirichletCharacter ℂ M × ℂ)), 0 ≤ T →
    (∀ p ∈ S, |p.2.im| ≤ T) → (∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → p.1 = p'.1 → 1 ≤ |p.2.im - p'.2.im|) →
    (S.card : ℝ) ≤ (M : ℝ) * (2 * T + 1)

def Offdiag : Prop :=
  ∀ (M : ℕ) [NeZero M] (S : Finset (DirichletCharacter ℂ M × ℂ)) (σ T : ℝ) (U : ℕ), 1 ≤ U → 2 ≤ T →
    1 / 2 ≤ σ → (∀ p ∈ S, σ ≤ p.2.re ∧ p.2.re ≤ 1 ∧ |p.2.im| ≤ T) →
    (∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → p.1 = p'.1 → 1 ≤ |p.2.im - p'.2.im|) →
    ∀ p ∈ S, ∑ p' ∈ S, ‖∑ n ∈ Ioc U (2 * U), p.1 (n : ZMod M) * (starRingEnd ℂ) (p'.1 (n : ZMod M)) *
        (n : ℂ) ^ (-((p.2 - (σ : ℂ)) + (starRingEnd ℂ) (p'.2 - (σ : ℂ))))‖ ≤
      (U : ℝ) * (9 + 8 * Real.log (2 * T + 1)) + (S.card : ℝ) * (8 * ((M : ℝ) + 1) * (2 + 2 * T))

def BlockCnt : Prop :=
  ∀ {α : Type} (S : Finset α) (f : α → ℕ → ℂ) (ρ : α → ℂ) (Y N U : ℕ) (σ θ G K : ℝ), 1 ≤ U → 0 < θ →
    0 ≤ σ → 0 ≤ G → 0 ≤ K →
    (∀ p ∈ S, ∀ n : ℕ, ‖f p n‖ ≤ 1) → (∀ p ∈ S, σ ≤ (ρ p).re) →
    (∀ p ∈ S, ∑ p' ∈ S, ‖∑ n ∈ Ioc U (2 * U), f p n * (starRingEnd ℂ) (f p' n) *
        (n : ℂ) ^ (-((ρ p - (σ : ℂ)) + (starRingEnd ℂ) (ρ p' - (σ : ℂ))))‖ ≤ (U : ℝ) * G + (S.card : ℝ) * K) →
    (∀ p ∈ S, θ ≤ ‖blkD Y N U (f p) (ρ p)‖) →
    2 * (U : ℝ) ^ (1 - 2 * σ) * (1 + Real.log (2 * U)) ^ 3 * K ≤ θ ^ 2 / 2 →
    (S.card : ℝ) ≤ 4 * (U : ℝ) ^ (2 - 2 * σ) * (1 + Real.log (2 * U)) ^ 3 * G / θ ^ 2

def EtaPartial : Prop :=
  ∀ s : ℂ, 0 < s.re → s ≠ 1 → ∀ N : ℕ, 1 ≤ N →
    ‖(1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s -
        (∑ n ∈ Icc 1 (2 * N), (n : ℂ) ^ (-s) - (2 : ℂ) ^ (1 - s) * ∑ n ∈ Icc 1 N, (n : ℂ) ^ (-s))‖ ≤
      4 * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re)

def PrincipalZeta : Prop :=
  ∀ (M : ℕ) [NeZero M] (s : ℂ), 0 < s.re → IsLZero (1 : DirichletCharacter ℂ M) s → riemannZeta s = 0

def Detect1 : Prop :=
  ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M), χ ≠ 1 → ∀ T : ℝ, 2 ≤ T → 3 ≤ M →
    ∀ ρ : ℂ, 3 / 4 ≤ ρ.re → |ρ.im| ≤ T → DirichletCharacter.LFunction χ ρ = 0 →
      ∃ j ∈ range (pJd M T), 1 / (2 * (pJd M T : ℝ)) ≤
        ‖blkD (pYd M T) (pNd M T) (pYd M T * 2 ^ j) (fun n => χ (n : ZMod M)) ρ‖

def Detect0 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ q₀ : ℕ, ∀ (M : ℕ) [NeZero M] (T : ℝ), 2 ≤ T → 3 ≤ M → q₀ ≤ qd M T →
    ∀ ρ : ℂ, 3 / 4 ≤ ρ.re → |ρ.im| ≤ T → IsLZero (1 : DirichletCharacter ℂ M) ρ →
      ∃ i ∈ range 2, ∃ j ∈ range (pJd M T + 1),
        c / (((pJd M T : ℝ) + 1) * Real.log (qd M T)) ≤
          ‖blkD (pYd M T) (2 ^ i * pNd M T) (pYd M T * 2 ^ j)
            (fun n => (1 : DirichletCharacter ℂ 1) (n : ZMod 1)) ρ‖

def Count1 : Prop :=
  ∃ C : ℝ, ∃ q₀ : ℕ, ∀ (M : ℕ) [NeZero M] (T σ : ℝ) (S : Finset (DirichletCharacter ℂ M × ℂ)),
    3 ≤ M → 2 ≤ T → 3 / 4 ≤ σ → q₀ ≤ qd M T →
    (∀ p ∈ S, p.1 ≠ 1 ∧ σ ≤ p.2.re ∧ p.2.re < 1 ∧ |p.2.im| ≤ T ∧ DirichletCharacter.LFunction p.1 p.2 = 0) →
    (∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → p.1 = p'.1 → 1 ≤ |p.2.im - p'.2.im|) →
    (S.card : ℝ) ≤ C * ((M : ℝ) * T) ^ (24 * (1 - σ)) * Real.log ((M : ℝ) * T) ^ 10

def Count0 : Prop :=
  ∃ C : ℝ, ∃ q₀ : ℕ, ∀ (M : ℕ) [NeZero M] (T σ : ℝ) (S : Finset (DirichletCharacter ℂ M × ℂ)),
    3 ≤ M → 2 ≤ T → 3 / 4 ≤ σ → q₀ ≤ qd M T →
    (∀ p ∈ S, p.1 = 1 ∧ σ ≤ p.2.re ∧ p.2.re < 1 ∧ |p.2.im| ≤ T ∧ IsLZero p.1 p.2) →
    (∀ p ∈ S, ∀ p' ∈ S, p ≠ p' → 1 ≤ |p.2.im - p'.2.im|) →
    (S.card : ℝ) ≤ C * ((M : ℝ) * T) ^ (24 * (1 - σ)) * Real.log ((M : ℝ) * T) ^ 10

end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTEOf
section
open Finset Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet

theorem cZ_pos : 0 < cZ :=
  lt_min (Classical.choose_spec Formalism.ZeroFreeDirichlet.zFRDirichlet).1 (by norm_num)

theorem cZ_le : cZ ≤ 1 / 20 :=
  min_le_right _ _

theorem inRegion_mono {c c' : ℝ} (hc : c ≤ c') (q : ℕ) [NeZero q] (s : ℂ) (hs : InRegion c q s) :
    InRegion c' q s := by
  unfold InRegion at hs ⊢
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlog : 0 < Real.log ((q : ℝ) * (|s.im| + 2)) :=
    Real.log_pos (by nlinarith [abs_nonneg s.im])
  have h1 : c / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ c' / Real.log ((q : ℝ) * (|s.im| + 2)) :=
    div_le_div_of_nonneg_right hc hlog.le
  linarith

theorem zfr_cZ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : InRegion cZ q s)
    (hz : IsLZero χ s) :
    χ ^ 2 = 1 ∧ χ ≠ 1 ∧ s.im = 0 ∧ deriv (DirichletCharacter.LFunction χ) s ≠ 0 ∧
      ∀ (χ' : DirichletCharacter ℂ q) (s' : ℂ), InRegion cZ q s' → IsLZero χ' s' → χ' = χ ∧ s' = s := by
  have hZ := Classical.choose_spec Formalism.ZeroFreeDirichlet.zFRDirichlet
  have hle : cZ ≤ Classical.choose Formalism.ZeroFreeDirichlet.zFRDirichlet := min_le_left _ _
  obtain ⟨h1, h2, h3, h4, h5⟩ := hZ.2 q χ s (inRegion_mono hle q s hs) hz
  exact ⟨h1, h2, h3, h4, fun χ' s' hs' hz' => h5 χ' s' (inRegion_mono hle q s' hs') hz'⟩

theorem eOf_cases (M : ℕ) [NeZero M] :
    (∃ p : DirichletCharacter ℂ M × ℝ, eOf M = some p ∧ IsExcPair p.1 p.2 ∧ InRegion cZ M (p.2 : ℂ)) ∨
    (∃ p : DirichletCharacter ℂ M × ℝ, eOf M = some p ∧ IsExcPair p.1 p.2 ∧
      ∀ p' : DirichletCharacter ℂ M × ℝ, IsExcPair p'.1 p'.2 → ¬ InRegion cZ M (p'.2 : ℂ)) ∨
    (eOf M = none ∧ ∀ p' : DirichletCharacter ℂ M × ℝ, ¬ IsExcPair p'.1 p'.2) := by
  unfold eOf
  split_ifs with h h'
  · exact Or.inl ⟨h.choose, rfl, h.choose_spec.1, h.choose_spec.2⟩
  · exact Or.inr (Or.inl ⟨h'.choose, rfl, h'.choose_spec, fun p' hp' hr => h ⟨p', hp', hr⟩⟩)
  · exact Or.inr (Or.inr ⟨rfl, fun p' hp' => h' ⟨p', hp'⟩⟩)

theorem eOf_exc (M : ℕ) [NeZero M] (p : DirichletCharacter ℂ M × ℝ) (h : eOf M = some p) :
    IsExcPair p.1 p.2 := by
  rcases eOf_cases M with ⟨q, hq, hex, _⟩ | ⟨q, hq, hex, _⟩ | ⟨hn, _⟩
  · rw [h] at hq
    cases hq
    exact hex
  · rw [h] at hq
    cases hq
    exact hex
  · rw [h] at hn
    cases hn

theorem eOf_none (M : ℕ) [NeZero M] (h : eOf M = none) (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ) :
    ¬ IsExcPair χ₁ β₁ := by
  rcases eOf_cases M with ⟨q, hq, _, _⟩ | ⟨q, hq, _, _⟩ | ⟨_, hno⟩
  · rw [h] at hq
    cases hq
  · rw [h] at hq
    cases hq
  · exact hno (χ₁, β₁)

theorem inRegion_ofReal (c : ℝ) (q : ℕ) (β : ℝ) :
    InRegion c q (β : ℂ) ↔ 1 - c / Real.log ((q : ℝ) * 2) ≤ β := by
  unfold InRegion
  rw [Complex.ofReal_im, Complex.ofReal_re, abs_zero, zero_add]

theorem log_two_mul_le (M : ℕ) (hM : 2 ≤ M) : Real.log ((M : ℝ) * 2) ≤ 2 * Real.log M := by
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  rw [Real.log_mul (by positivity) (by norm_num)]
  have h1 : Real.log 2 ≤ Real.log M := Real.log_le_log (by norm_num) hM'
  linarith

theorem log_pos_of_two_le (M : ℕ) (hM : 2 ≤ M) : 0 < Real.log M := by
  apply Real.log_pos
  exact_mod_cast (show 1 < M by omega)

theorem isExcPair_of_region (M : ℕ) [NeZero M] (hM : 2 ≤ M) (χ : DirichletCharacter ℂ M) (β : ℝ)
    (h2 : χ ^ 2 = 1) (h1 : χ ≠ 1) (hz : DirichletCharacter.LFunction χ (β : ℂ) = 0)
    (hr : InRegion cZ M (β : ℂ)) : IsExcPair χ β := by
  refine ⟨h2, h1, hz, ?_, ?_⟩
  · rw [inRegion_ofReal] at hr
    have hlogM := log_pos_of_two_le M hM
    have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
    have hlogge : Real.log M ≤ Real.log ((M : ℝ) * 2) := Real.log_le_log (by positivity) (by nlinarith)
    have hcz := cZ_le
    have hcz0 := cZ_pos
    have hlog2pos : 0 < Real.log ((M : ℝ) * 2) := lt_of_lt_of_le hlogM hlogge
    have h3 : cZ / Real.log ((M : ℝ) * 2) < 1 / (8 * Real.log M) := by
      rw [div_lt_div_iff₀ hlog2pos (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right hcz hlogM.le]
    linarith
  · by_contra hge
    push_neg at hge
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl h1) (by simpa using hge) hz

theorem zero_in_region (M : ℕ) [NeZero M] (hM : 2 ≤ M) (χ : DirichletCharacter ℂ M) (s : ℂ)
    (hs : InRegion cZ M s) (hz : IsLZero χ s) :
    ∃ β₁ : ℝ, eOf M = some (χ, β₁) ∧ s = (β₁ : ℂ) ∧ deriv (DirichletCharacter.LFunction χ) s ≠ 0 := by
  obtain ⟨h2, h1, him, hder, huniq⟩ := zfr_cZ M χ s hs hz
  have hs' : s = ((s.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  have hzr : DirichletCharacter.LFunction χ ((s.re : ℝ) : ℂ) = 0 := by rw [← hs']; exact hz.2
  have hrr : InRegion cZ M ((s.re : ℝ) : ℂ) := by rw [← hs']; exact hs
  have hex : IsExcPair χ s.re := isExcPair_of_region M hM χ s.re h2 h1 hzr hrr
  rcases eOf_cases M with ⟨p, hp, hpex, hpr⟩ | ⟨p, hp, hpex, hno⟩ | ⟨hn, hno⟩
  · have hz' : IsLZero p.1 (p.2 : ℂ) := ⟨Or.inl hpex.2.1, hpex.2.2.1⟩
    obtain ⟨e1, e2⟩ := huniq p.1 (p.2 : ℂ) hpr hz'
    refine ⟨p.2, ?_, e2.symm, hder⟩
    rw [hp, ← e1]
  · exact absurd hrr (hno (χ, s.re) hex)
  · exact absurd hex (hno (χ, s.re))

theorem etaOf_some (M : ℕ) [NeZero M] (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ) (h : eOf M = some (χ₁, β₁)) :
    etaOf M = min 1 ((1 - β₁) * Real.log M) := by
  unfold etaOf
  rw [h]

theorem etaOf_none (M : ℕ) [NeZero M] (h : eOf M = none) : etaOf M = 1 := by
  unfold etaOf
  rw [h]

theorem etaOf_pos (M : ℕ) [NeZero M] (hM : 2 ≤ M) : 0 < etaOf M := by
  rcases hE : eOf M with _ | ⟨χ₁, β₁⟩
  · rw [etaOf_none M hE]
    exact one_pos
  · rw [etaOf_some M χ₁ β₁ hE]
    have hex := eOf_exc M (χ₁, β₁) hE
    exact lt_min one_pos (mul_pos (by linarith [hex.2.2.2.2]) (log_pos_of_two_le M hM))

theorem etaOf_le_one (M : ℕ) [NeZero M] : etaOf M ≤ 1 := by
  rcases hE : eOf M with _ | ⟨χ₁, β₁⟩
  · rw [etaOf_none M hE]
  · rw [etaOf_some M χ₁ β₁ hE]
    exact min_le_left _ _

theorem etaOf_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (M : ℕ) [NeZero M], 3 ≤ M → c * (M : ℝ) ^ (-ε) ≤ etaOf M := by
  obtain ⟨c, hc, hb⟩ := Formalism.ZeroFreeDirichlet.excBound ε hε
  refine ⟨min 1 (c * Real.log 3), lt_min one_pos (mul_pos hc (Real.log_pos (by norm_num))), fun M _ hM => ?_⟩
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hpow : (M : ℝ) ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hM1 (by linarith)
  have hpow0 : 0 < (M : ℝ) ^ (-ε) := Real.rpow_pos_of_pos (by linarith) _
  have hle1 : min 1 (c * Real.log 3) * (M : ℝ) ^ (-ε) ≤ 1 := by
    calc min 1 (c * Real.log 3) * (M : ℝ) ^ (-ε) ≤ 1 * 1 :=
          mul_le_mul (min_le_left _ _) hpow hpow0.le zero_le_one
      _ = 1 := one_mul 1
  rcases hE : eOf M with _ | ⟨χ₁, β₁⟩
  · rw [etaOf_none M hE]
    exact hle1
  · rw [etaOf_some M χ₁ β₁ hE]
    have hex := eOf_exc M (χ₁, β₁) hE
    have hβ := hb M χ₁ β₁ hex.1 hex.2.1 hex.2.2.1
    have hlog3 : Real.log 3 ≤ Real.log M := Real.log_le_log (by norm_num) (by exact_mod_cast hM)
    have hlogM : 0 ≤ Real.log M := le_trans (Real.log_nonneg (by norm_num)) hlog3
    have h1 : c * (M : ℝ) ^ (-ε) ≤ 1 - β₁ := by linarith
    apply le_min hle1
    calc min 1 (c * Real.log 3) * (M : ℝ) ^ (-ε) ≤ (c * Real.log 3) * (M : ℝ) ^ (-ε) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hpow0.le
      _ ≤ (c * Real.log M) * (M : ℝ) ^ (-ε) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog3 hc.le) hpow0.le
      _ = (c * (M : ℝ) ^ (-ε)) * Real.log M := by ring
      _ ≤ (1 - β₁) * Real.log M := mul_le_mul_of_nonneg_right h1 hlogM

theorem etaOf_far (M : ℕ) [NeZero M] (hM : 2 ≤ M) (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ)
    (h : eOf M = some (χ₁, β₁)) (hr : ¬ InRegion cZ M (β₁ : ℂ)) : cZ / 2 ≤ etaOf M := by
  rw [etaOf_some M χ₁ β₁ h]
  rw [inRegion_ofReal] at hr
  push_neg at hr
  have hlogM := log_pos_of_two_le M hM
  have hlog2 := log_two_mul_le M hM
  have hM' : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hlogge : Real.log M ≤ Real.log ((M : ℝ) * 2) := Real.log_le_log (by positivity) (by nlinarith)
  have hlog2pos : 0 < Real.log ((M : ℝ) * 2) := lt_of_lt_of_le hlogM hlogge
  have hcz := cZ_le
  have hcz0 := cZ_pos
  have h1 : cZ / Real.log ((M : ℝ) * 2) < 1 - β₁ := by linarith
  have hb : 0 < 1 - β₁ := lt_trans (div_pos hcz0 hlog2pos) h1
  rw [div_lt_iff₀ hlog2pos] at h1
  have h2 : cZ / 2 ≤ (1 - β₁) * Real.log M := by
    nlinarith [mul_le_mul_of_nonneg_left hlog2 hb.le]
  exact le_min (by linarith) h2

theorem eOf_char_sq (M : ℕ) [NeZero M] (χ₁ : DirichletCharacter ℂ M) (β₁ : ℝ) (h : eOf M = some (χ₁, β₁))
    (b : ZMod M) (hb : IsUnit b) : χ₁ b = 1 ∨ χ₁ b = -1 := by
  have hex := eOf_exc M (χ₁, β₁) h
  have h2 : (χ₁ ^ 2) b = 1 := by
    rw [hex.1]
    exact MulChar.one_apply hb
  rw [MulChar.pow_apply' χ₁ (by norm_num)] at h2
  exact mul_self_eq_one_iff.mp (by rw [← sq]; exact h2)

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.PNTExplDefs
section
open Complex Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

def exLF {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) : ℂ → ℂ :=
  if χ = 1 then DirichletCharacter.LFunctionTrivChar₁ M else DirichletCharacter.LFunction χ

def exOrd {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (exLF χ) ρ

def exKer (y : ℝ) (w : ℂ) : ℂ := (y : ℂ) ^ w / (w * (w - 1))

def explicitFormulaConstant {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) : ℂ := -(deriv (exLF χ) 1 / exLF χ 1)

end Formalism.HermitianLattices.Ext.PrimesInProgressions
end
end

