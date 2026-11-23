module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
public import Formalism.LocalToGlobal.Columns.Bundle0007
public import Formalism.HarderNarasimhan.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0003
public import Formalism.LocalRingCardinality.DataArith

@[expose] public section

noncomputable section

namespace GlobalTheory.Core.Ht2

open NumberField Formalism.BasicNotions

section Generic

variable {K : Type} [Field K] [NumberField K] [StarRing K]

abbrev nrm (A : HLat K) (v : InfinitePlace K) (x : A.V) : ℝ := Formalism.HermitianLatticesTheory.normAt A.b A.X v x

def IsoAll (N A : HLat K) (e : N.V →ₗ[K] A.V) : Prop := ∀ v x, nrm A v (e x) = nrm N v x

def Norming (B M : HLat K) (pr : B.V →ₗ[K] Module.Dual K M.V) : Prop :=
  ∀ (w : B.V) (v : InfinitePlace K), ∃ z, v (pr w z) = nrm B v w ^ 2 ∧ nrm M v z = nrm B v w

def Reads (N B A M : HLat K) (Ψ : N.V →ₗ[K] B.V) (Φ : A.V →ₗ[K] Module.Dual K M.V) : Prop :=
  ∃ (e : N.V →ₗ[K] A.V) (pr : B.V →ₗ[K] Module.Dual K M.V),
    IsoAll N A e ∧ Norming B M pr ∧ ∀ x, Φ (e x) = pr (Ψ x)

def PairLe (A M : HLat K) (Φ : A.V →ₗ[K] Module.Dual K M.V) (h : ℝ) : Prop :=
  ∃ c : InfinitePlace K → ℝ, (∀ v x y, v (Φ x y) ^ 2 ≤ Real.exp (c v) * nrm A v x ^ 2 * nrm M v y ^ 2) ∧
    (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, c v ≤ h

def ValLe (N B : HLat K) (Ψ : N.V →ₗ[K] B.V) (h : ℝ) : Prop :=
  ∃ c : InfinitePlace K → ℝ, (∀ v x, nrm B v (Ψ x) ^ 2 ≤ Real.exp (c v) * nrm N v x ^ 2) ∧
    (1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, c v ≤ h

theorem nrm_nonneg (A : HLat K) (v : InfinitePlace K) (x : A.V) : 0 ≤ nrm A v x :=
  Real.sqrt_nonneg _

theorem Norming.nrm_le {B M : HLat K} {pr : B.V →ₗ[K] Module.Dual K M.V} (hn : Norming B M pr) (w : B.V) (v : InfinitePlace K)
    {C : ℝ} (hC : 0 ≤ C) (h : ∀ y, v (pr w y) ≤ C * nrm M v y) : nrm B v w ≤ C := by
  obtain ⟨z, hz, hzn⟩ := hn w v
  have hw := nrm_nonneg B v w
  have hle := h z
  rw [hz, hzn] at hle
  nlinarith

theorem Reads.exists_nrm_le {N B A M : HLat K} {Ψ : N.V →ₗ[K] B.V} {Φ : A.V →ₗ[K] Module.Dual K M.V}
    (hr : Reads N B A M Ψ Φ) : ∃ e : N.V →ₗ[K] A.V, IsoAll N A e ∧ ∀ x v (C : ℝ), 0 ≤ C →
      (∀ y, v (Φ (e x) y) ≤ C * nrm M v y) → nrm B v (Ψ x) ≤ C := by
  obtain ⟨e, pr, he, hn, hΦ⟩ := hr
  refine ⟨e, he, fun x v C hC hb => hn.nrm_le (Ψ x) v hC fun y => ?_⟩
  rw [← hΦ x]
  exact hb y

theorem valLe_of_reads {N B A M : HLat K} {Ψ : N.V →ₗ[K] B.V} {Φ : A.V →ₗ[K] Module.Dual K M.V} {h : ℝ}
    (hr : Reads N B A M Ψ Φ) (hp : PairLe A M Φ h) : ValLe N B Ψ h := by
  obtain ⟨c, hc, hmean⟩ := hp
  obtain ⟨e, he, hbd⟩ := hr.exists_nrm_le
  refine ⟨c, fun v x => ?_, hmean⟩

  have hs : Real.exp (c v / 2) ^ 2 = Real.exp (c v) := by
    rw [sq, ← Real.exp_add, add_halves]
  have hE : 0 ≤ Real.exp (c v / 2) := (Real.exp_pos _).le
  have hN := nrm_nonneg N v x
  have key : nrm B v (Ψ x) ≤ Real.exp (c v / 2) * nrm N v x := by
    refine hbd x v _ (mul_nonneg hE hN) fun y => ?_
    have h1 := hc v (e x) y
    rw [he v x, ← hs] at h1
    have hM := nrm_nonneg M v y
    have hb : 0 ≤ Real.exp (c v / 2) * nrm N v x * nrm M v y := mul_nonneg (mul_nonneg hE hN) hM
    nlinarith
  have hk := nrm_nonneg B v (Ψ x)
  calc nrm B v (Ψ x) ^ 2 ≤ (Real.exp (c v / 2) * nrm N v x) ^ 2 := by nlinarith
    _ = Real.exp (c v) * nrm N v x ^ 2 := by rw [mul_pow, hs]

end Generic

namespace Std

variable (K : Type) [Field K] [NumberField K] [StarRing K] (n : ℕ)

variable {K n}

end Std

end GlobalTheory.Core.Ht2

end
