module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0003
public import Formalism.DropLevelBounds.Statement
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0007
public import ReciprocityTheory.DualLattices.DetPolyMulCayleyOmegaPow
public import ReciprocityTheory.DualLattices.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalDiscPointsValuationIntegers
section
namespace GlobalTheory.ChF

private theorem exists_pow_mem_span_of_not_isUnit {p : ℕ} [Fact p.Prime] {C : Type} [Field C]
    [CharZero C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
    (hv : v.Integers O) {x : O} (hx : ¬ IsUnit x) :
    ∃ M : ℕ, x ^ M ∈ Ideal.span {(p : O)} := by
  have h1 : v (algebraMap O C x) < 1 :=
    lt_of_le_of_ne (hv.map_le_one x) fun h => hx (hv.isUnit_of_one' h)
  have hp : (0 : NNReal) < v (algebraMap O C (p : O)) := by
    rw [map_natCast, pos_iff_ne_zero, Valuation.ne_zero_iff]
    exact Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  obtain ⟨M, hM⟩ := NNReal.exists_pow_lt_of_lt_one hp h1
  refine ⟨M, Ideal.mem_span_singleton.2 (hv.dvd_of_le ?_)⟩
  rw [map_pow, map_pow]
  exact hM.le

private theorem not_isUnit_algHom_of_constantCoeff_eq_zero {O : Type} [CommRing O] [Nontrivial O]
    {κ : Type} (Φ : MvPowerSeries κ O →ₐ[O] O) (f : MvPowerSeries κ O)
    (hf : MvPowerSeries.constantCoeff f = 0) : ¬ IsUnit (Φ f) := by
  rintro ⟨u, hu⟩
  have h1 : IsUnit (1 - ((u⁻¹ : Oˣ) : O) • f) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, map_sub, map_one, Algebra.smul_def, map_mul, hf,
      mul_zero, sub_zero]
    exact isUnit_one
  have h2 := h1.map Φ
  rw [map_sub, map_one, map_smul, ← hu, smul_eq_mul, Units.inv_mul, sub_self] at h2
  exact not_isUnit_zero h2

theorem formalDisc_points_integers : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (κ : Type) [Finite κ], (∀ c : κ → O, (∀ q, ¬ IsUnit (c q)) → ∃! Φ : MvPowerSeries κ O →ₐ[O] O, ∀ q, Φ (MvPowerSeries.X q) = c q) ∧ (∀ (Φ : MvPowerSeries κ O →ₐ[O] O) (f : MvPowerSeries κ O), MvPowerSeries.constantCoeff f = 0 → ¬ IsUnit (Φ f)) ∧ ∀ (Φ : MvPowerSeries κ O →ₐ[O] O) (n : ℕ), ∃ N : ℕ, ∀ f ∈ ((Ideal.span {(p : O)}).map (MvPowerSeries.C : O →+* MvPowerSeries κ O) ⊔ Ideal.span (Set.range (MvPowerSeries.X : κ → MvPowerSeries κ O))) ^ N, Φ f ∈ Ideal.span {(p : O) ^ n} := by
  intro p _ C _ _ _ v O _ _ hv hp hc κ _
  haveI : Nontrivial O := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hp.out (isUnit_of_subsingleton _)
  refine ⟨fun c hcu => ?_, not_isUnit_algHom_of_constantCoeff_eq_zero, fun Φ n => ?_⟩
  · obtain ⟨hex, huniq⟩ := GlobalTheory.mvPowerSeries_eval_of_pow_mem O (Ideal.span {(p : O)}) κ c
      fun j => exists_pow_mem_span_of_not_isUnit hv (hcu j)
    obtain ⟨Φ, hΦ⟩ := hex hc O
    refine ⟨Φ, hΦ, fun Ψ hΨ => ?_⟩
    have := huniq inferInstance O Ψ.toRingHom Φ.toRingHom
      (fun t => (Ψ.commutes t).trans (Φ.commutes t).symm) hΨ hΦ
    exact AlgHom.ext fun g => DFunLike.congr_fun this g
  · obtain ⟨N, hN⟩ := GlobalTheory.NilpotentEval.exists_pow_sup_span_le (Ideal.span {(p : O)})
      (fun q => Φ (MvPowerSeries.X q)) fun q => exists_pow_mem_span_of_not_isUnit hv
        (not_isUnit_algHom_of_constantCoeff_eq_zero Φ _ (MvPowerSeries.constantCoeff_X q))
    refine ⟨N * n, fun f hf => ?_⟩
    rw [← Ideal.span_singleton_pow]
    refine GlobalTheory.NilpotentEval.pow_mul_le hN n ?_
    have hf' := Ideal.mem_map_of_mem Φ.toRingHom hf
    rw [Ideal.map_pow] at hf'
    refine Ideal.pow_right_mono ?_ _ hf'
    rw [Ideal.map_sup]
    refine sup_le_sup ?_ ?_
    · rw [Ideal.map_map, Ideal.map_le_iff_le_comap]
      intro x hx
      rw [Ideal.mem_comap]
      have : (Φ.toRingHom.comp MvPowerSeries.C) x = x := Φ.commutes x
      rwa [this]
    · rw [Ideal.map_span]
      refine Ideal.span_mono ?_
      rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
      exact ⟨q, rfl⟩

end GlobalTheory.ChF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LeWeightOfCoeffPow
section
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds ReciprocityTheory.PGsh
open scoped BigOperators

noncomputable section

namespace GlobalTheory.UnitCase

variable {C : Type} [Field C] {σ κ : Type}

lemma jetAt0_eq_sum (P : MvPolynomial σ C) (G : MvPowerSeries σ C) (s : Finset (σ →₀ ℕ))
    (hs : P.support ⊆ s) :
    jetAt0 P G = ∑ m ∈ s, AddMonoidAlgebra.coeff P m * (mfact m : C) * MvPowerSeries.coeff m G := by
  unfold jetAt0
  refine Finset.sum_subset hs fun m _ hm => ?_
  rw [MvPolynomial.notMem_support_iff.1 hm]
  simp

end GlobalTheory.UnitCase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MulFlowValLe
section
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds

namespace GlobalTheory.FlowScaling

variable {l d : ℕ} [NeZero d]

lemma isFlow_zero {D : ZMod d → ℝ} (hD : ∀ a, 0 ≤ D a) : IsFlow l d D (fun _ _ => 0) :=
  ⟨fun _ _ => le_rfl, fun s => by simpa using hD s⟩

lemma mul_flowVal_le (hl : 1 ≤ l) {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} (hx : IsFlow l d D x) :
    (l : ℝ) * flowVal d x ≤ ∑ a, D a := by
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl
  unfold flowVal
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  have h2 := hx.2 a
  have h3 : 0 ≤ ∑ i ∈ oddLevels d, x (a - (i : ZMod d)) i :=
    Finset.sum_nonneg fun i _ => hx.1 _ i
  have h4 : (l : ℝ) * ∑ i ∈ oddLevels d, x a i ≤ ∑ i ∈ oddLevels d, (l : ℝ) ^ i * x a i := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact absurd (Finset.mem_filter.1 hi).2 (by decide)
    exact mul_le_mul_of_nonneg_right (le_self_pow₀ hl1 hi0) (hx.1 a i)
  linarith

lemma flowVal_le (hl : 1 ≤ l) {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} (hx : IsFlow l d D x) :
    flowVal d x ≤ (∑ a, D a) / l := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl
  rw [le_div_iff₀ hl0, mul_comm]
  exact mul_flowVal_le hl hx

lemma le_maxFlow (hl : 1 ≤ l) {D : ZMod d → ℝ} {x : ZMod d → ℕ → ℝ} (hx : IsFlow l d D x) :
    flowVal d x ≤ maxFlow l d D := by
  refine le_csSup ⟨(∑ a, D a) / l, ?_⟩ ⟨x, hx, rfl⟩
  rintro t ⟨y, hy, rfl⟩
  exact flowVal_le hl hy

lemma maxFlow_le {D : ZMod d → ℝ} (hD : ∀ a, 0 ≤ D a) {B : ℝ}
    (h : ∀ x, IsFlow l d D x → flowVal d x ≤ B) : maxFlow l d D ≤ B := by
  refine csSup_le ⟨_, _, isFlow_zero hD, rfl⟩ ?_
  rintro t ⟨y, hy, rfl⟩
  exact h y hy

lemma maxFlow_le_div (hl : 1 ≤ l) {D : ZMod d → ℝ} (hD : ∀ a, 0 ≤ D a) :
    maxFlow l d D ≤ (∑ a, D a) / l :=
  maxFlow_le hD fun _ hx => flowVal_le hl hx

lemma maxFlow_nonneg (hl : 1 ≤ l) {D : ZMod d → ℝ} (hD : ∀ a, 0 ≤ D a) :
    0 ≤ maxFlow l d D := by
  have := le_maxFlow hl (isFlow_zero (l := l) hD)
  simpa [flowVal] using this

lemma mul_maxFlow_le (hl : 1 ≤ l) {c : ℝ} {D D' : ZMod d → ℝ} (hc : 0 ≤ c) (hD : ∀ a, 0 ≤ D a)
    (h : ∀ a, c * D a ≤ D' a) : c * maxFlow l d D ≤ maxFlow l d D' := by
  rcases hc.eq_or_lt with rfl | hc0
  · rw [zero_mul]
    exact maxFlow_nonneg hl fun a => by simpa using h a
  · rw [← le_div_iff₀' hc0]
    refine maxFlow_le hD fun x hx => ?_
    rw [le_div_iff₀' hc0]
    have hf : IsFlow l d D' (fun a i => c * x a i) := by
      refine ⟨fun s i => mul_nonneg hc (hx.1 s i), fun s => le_trans (le_of_eq ?_)
        ((mul_le_mul_of_nonneg_left (hx.2 s) hc).trans (h s))⟩
      rw [mul_add, Finset.mul_sum, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    have hv : flowVal d (fun a i => c * x a i) = c * flowVal d x := by
      simp only [flowVal, Finset.mul_sum]
    rw [← hv]
    exact le_maxFlow hl hf

lemma maxFlow_mul (hl : 1 ≤ l) {c : ℝ} {D : ZMod d → ℝ} (hc : 0 ≤ c) (hD : ∀ a, 0 ≤ D a) :
    maxFlow l d (fun a => c * D a) = c * maxFlow l d D := by
  refine le_antisymm ?_ (mul_maxFlow_le hl hc hD fun _ => le_rfl)
  rcases hc.eq_or_lt with rfl | hc0
  · have := maxFlow_le_div (D := fun a => 0 * D a) hl (fun a => by simp)
    simpa using this
  · have := mul_maxFlow_le (c := c⁻¹) (D := fun a => c * D a) (D' := D) hl (inv_nonneg.2 hc)
      (fun a => mul_nonneg hc (hD a)) (fun a => by rw [inv_mul_cancel_left₀ hc0.ne'])
    rwa [inv_mul_le_iff₀ hc0] at this

end GlobalTheory.FlowScaling
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.WeightNonnegExpOfWeightGeInvPrimeSubOne
section
open ReciprocityTheory.PGsh

namespace GlobalTheory.ExpWeight

variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))
  {σ : Type} [DecidableEq σ] (ρ : σ → ℝ)


variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))
  {σ : Type} [DecidableEq σ] (ρ : σ → ℝ) in
theorem _root_.GlobalTheory.ExpWeight.weight_exp :
  (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (ρ : σ → ℝ) (h : MvPowerSeries σ C), MvPowerSeries.constantCoeff h = 0 →
    (∀ α, (((1 / (l - 1)) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (h))) → (∀ α, (((0) - α.sum (fun j e => ρ j * (e : ℝ)) : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (PowerSeries.subst (h) (PowerSeries.exp C))))) := by
  intro C _ _ v l hl hvl σ _ _ ρ h h0 hh
  set c : ℝ := 1 / ((l : ℝ) - 1) with hc
  set w : (σ →₀ ℕ) → ℝ := fun α => α.sum (fun j e => ρ j * (e : ℝ)) with hw
  have hwadd : ∀ α β : σ →₀ ℕ, w (α + β) = w α + w β := fun α β => by
    simp only [hw]
    exact Finsupp.sum_add_index' (fun j => by simp) (fun j a b => by push_cast; ring)
  have hsumle : ∀ {ι : Type} (s : Finset ι) (f : ι → C) (r : ℝ),
      (∀ i ∈ s, ((r : ℝ) : WithTop ℝ) ≤ v (f i)) → ((r : ℝ) : WithTop ℝ) ≤ v (∑ i ∈ s, f i) := by
    intro ι s f r hf
    refine Finset.sum_induction f (fun x => ((r : ℝ) : WithTop ℝ) ≤ v x) (fun a b ha hb => ?_) ?_ hf
    · exact le_trans (le_min ha hb) (v.map_add a b)
    · simp
  have hpow : ∀ (d : ℕ) (α : σ →₀ ℕ), (((d : ℝ) * c - w α : ℝ) : WithTop ℝ) ≤ v (MvPowerSeries.coeff α (h ^ d)) := by
    intro d
    induction d with
    | zero =>
      intro α
      rw [pow_zero, MvPowerSeries.coeff_one]
      split_ifs with hα
      · subst hα
        simp [hw]
      · simp
    | succ d ih =>
      intro α
      rw [pow_succ, MvPowerSeries.coeff_mul]
      refine hsumle _ _ _ fun p hp => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      rw [v.map_mul]
      have e : ((((d + 1 : ℕ) : ℝ) * c - w α : ℝ) : WithTop ℝ) =
          (((d : ℝ) * c - w p.1 : ℝ) : WithTop ℝ) + ((1 / ((l : ℝ) - 1) - w p.2 : ℝ) : WithTop ℝ) := by
        rw [← WithTop.coe_add, ← hp, hwadd, hc]
        congr 1
        push_cast
        ring
      rw [e]
      exact add_le_add (ih p.1) (hh p.2)
  intro α
  have hsub : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero h0
  rw [PowerSeries.coeff_subst hsub]
  refine finsum_induction (fun x => (((0 : ℝ) - w α : ℝ) : WithTop ℝ) ≤ v x) (by simp)
    (fun a b ha hb => le_trans (le_min ha hb) (v.map_add a b)) fun d => ?_
  simp only [PowerSeries.coeff_exp, smul_eq_mul, v.map_mul]
  have hf : (d.factorial : C) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  have hinv : algebraMap ℚ C (1 / (d.factorial : ℚ)) = ((d.factorial : C))⁻¹ := by simp
  rw [hinv]
  obtain ⟨y, hy⟩ := _root_.ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.exists_real v (inv_ne_zero hf)
  have hfact := _root_.ReciprocityTheory.ChartRestriction.G.Sh.PowerSeriesCoeffGaps.natCast_eq_factorization v hl hvl (Nat.factorial_ne_zero d)
  have hprod : v ((d.factorial : C))⁻¹ + v (d.factorial : C) = 0 := by
    rw [← v.map_mul, inv_mul_cancel₀ hf, v.map_one]
  rw [hy, hfact, ← WithTop.coe_add, WithTop.coe_eq_zero] at hprod
  have hle := _root_.GlobalTheory.LegendreBounds.upper l hl d
  have hyr : y = -((d.factorial.factorization l : ℕ) : ℝ) := by linarith
  simp only [Nat.padicValNat_def, ← Nat.factorization_def _ hl] at hle
  have hdc : (d : ℝ) / ((l : ℝ) - 1) = d * c := by rw [hc]; ring
  rw [hy]
  calc (((0 : ℝ) - w α : ℝ) : WithTop ℝ) ≤ ((y + ((d : ℝ) * c - w α) : ℝ) : WithTop ℝ) :=
        WithTop.coe_le_coe.mpr (by linarith)
    _ = ((y : ℝ) : WithTop ℝ) + (((d : ℝ) * c - w α : ℝ) : WithTop ℝ) := WithTop.coe_add _ _
    _ ≤ _ := add_le_add le_rfl (hpow d α)

end GlobalTheory.ExpWeight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.WeightedOrderGePrimePowOfSumPurePowersAddStatement
section
open ReciprocityTheory.PGsh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightedOrderGe_prime_pow_of_sum_pure_powers_add : (∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (l : ℕ), l.Prime → v (l : C) = 1 → ∀ (M N k : ℕ) (r w w₂ : ℝ) (a : Fin M → C) (ν : MvPowerSeries (Fin M) C), w ≤ w₂ → (∀ j, ((w - r * N : ℝ) : WithTop ℝ) ≤ v (a j)) →
    OrdGe v (fun _ => r) ν w₂ → OrdGe v (fun _ => r) ((∑ j, MvPowerSeries.C (R := C) (a j) * (MvPowerSeries.X j : MvPowerSeries (Fin M) C) ^ N + ν) ^ (l ^ k) -
      ∑ j, MvPowerSeries.C (R := C) (a j ^ (l ^ k)) * (MvPowerSeries.X j : MvPowerSeries (Fin M) C) ^ (N * l ^ k)) (min (1 + (l : ℝ) ^ k * w) ((l : ℝ) ^ k * w₂))) := by
  first | exact @GlobalTheory.WeightFrobenius.main | exact GlobalTheory.WeightFrobenius.main | (intros; apply GlobalTheory.WeightFrobenius.main <;> assumption)
end

