module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0330
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0327
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0072
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdGeExpOfLogSumTwoRadii
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth

namespace GlobalTheory.ExpWeightTwoRadii

variable {C : Type} [Field C] {M : ℕ}

def WtBelow (v : AddValuation C (WithTop ℝ)) (ρ : Fin M → ℝ) (D : ℕ)
    (g : MvPowerSeries (Fin M) C) (r : ℝ) : Prop :=
  ∀ α : Fin M →₀ ℕ, Finsupp.degree α < D →
    (((r - ∑ m, ρ m * (α m : ℝ) : ℝ)) : WithTop ℝ) ≤ v (coeff α g)

theorem wt_add_index (ρ : Fin M → ℝ) (β γ : Fin M →₀ ℕ) :
    ∑ m, ρ m * ((β + γ) m : ℝ) = (∑ m, ρ m * (β m : ℝ)) + ∑ m, ρ m * (γ m : ℝ) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finsupp.add_apply, Nat.cast_add, mul_add]

theorem WtBelow.mul {v : AddValuation C (WithTop ℝ)} {ρ : Fin M → ℝ} {D : ℕ}
    {g h : MvPowerSeries (Fin M) C} {r s : ℝ} (hg0 : constantCoeff g = 0)
    (hh0 : constantCoeff h = 0) (hg : WtBelow v ρ D g r) (hh : WtBelow v ρ D h s) :
    WtBelow v ρ (D + 1) (g * h) (r + s) := by
  classical
  intro α hα
  rw [coeff_mul]
  refine v.map_le_sum fun q hq => ?_
  have hq' : q.1 + q.2 = α := by simpa using hq
  by_cases h1 : q.1 = 0
  · rw [h1, coeff_zero_eq_constantCoeff_apply, hg0, zero_mul, v.map_zero]; exact le_top
  by_cases h2 : q.2 = 0
  · rw [h2, coeff_zero_eq_constantCoeff_apply, hh0, mul_zero, v.map_zero]; exact le_top
  have hd : Finsupp.degree q.1 + Finsupp.degree q.2 = Finsupp.degree α := by
    rw [← hq', map_add (f := _)]
  have d1 : Finsupp.degree q.1 ≠ 0 := fun e => h1 ((Finsupp.degree_eq_zero_iff _).1 e)
  have d2 : Finsupp.degree q.2 ≠ 0 := fun e => h2 ((Finsupp.degree_eq_zero_iff _).1 e)
  rw [v.map_mul]
  refine le_trans (le_of_eq ?_) (add_le_add (hg q.1 (by omega)) (hh q.2 (by omega)))
  rw [← WithTop.coe_add, ← hq', wt_add_index]
  congr 1
  ring

theorem WtBelow.pow_succ {v : AddValuation C (WithTop ℝ)} {ρ : Fin M → ℝ} {D : ℕ}
    {g : MvPowerSeries (Fin M) C} {r : ℝ} (hg0 : constantCoeff g = 0)
    (hg : WtBelow v ρ D g r) (k : ℕ) :
    WtBelow v ρ D (g ^ (k + 1)) (((k + 1 : ℕ) : ℝ) * r) := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
    have h := WtBelow.mul (by simp [hg0]) hg0 ih hg
    intro α hα
    have h' := h α (by omega)
    rw [_root_.pow_succ g (k + 1)]
    refine le_trans (le_of_eq ?_) h'
    congr 1
    push_cast
    ring

theorem WtBelow.pow {v : AddValuation C (WithTop ℝ)} {ρ : Fin M → ℝ} {D : ℕ}
    {g : MvPowerSeries (Fin M) C} {r : ℝ} (hg0 : constantCoeff g = 0)
    (hg : WtBelow v ρ D g r) {N : ℕ} (hN : 2 ≤ N) :
    WtBelow v ρ (D + 1) (g ^ N) ((N : ℝ) * r) := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 + 1 := ⟨N - 2, by omega⟩
  have h := WtBelow.mul (by simp [hg0]) hg0 (hg.pow_succ hg0 k) hg
  rw [_root_.pow_succ g (k + 1)]
  convert h using 1
  push_cast
  ring

theorem ordGe_of_lgSum_radii (v : AddValuation C (WithTop ℝ)) (p : ℕ) (hp : p.Prime)
    {d : ℕ} (good : Fin d → Prop) [DecidablePred good] (c : Fin d → ℕ → Fin d → C)
    (h0 : ∀ a, c a 0 = Pi.single a 1)
    (hc : ∀ a (n : ℕ) b, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b))
    (hgood : ∀ a, good a → ∀ (n : ℕ) b, 1 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b))
    (ρ : Fin M → ℝ) (z t : Fin d → MvPowerSeries (Fin M) C) (r : Fin d → ℝ)
    (hr : ∀ b, r b = if good b then 2 / ((p : ℝ) * (p - 1)) else 2 / ((p : ℝ) - 1))
    (hz : ∀ b, OrdGe v ρ (z b) (r b)) (ht : ∀ b, constantCoeff (t b) = 0)
    (hlg : ∀ b, lgSum p c t b = z b) : ∀ b, OrdGe v ρ (t b) (r b) := by
  classical
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  set g' : ℝ := 2 / ((p : ℝ) - 1) with hg'
  have hg'1 : g' * ((p : ℝ) - 1) = 2 := by rw [hg']; field_simp
  have hg'0 : 0 < g' := by rw [hg']; apply div_pos <;> linarith
  have hgp : 2 / ((p : ℝ) * (p - 1)) * p = g' := by rw [hg']; field_simp
  have hγ0 : 0 ≤ 2 / ((p : ℝ) * (p - 1)) := by
    apply div_nonneg (by norm_num); apply mul_nonneg <;> linarith
  have hγg : 2 / ((p : ℝ) * (p - 1)) ≤ g' := by
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ p by linarith) hγ0
    linarith
  have hre : ∀ e, r e ≤ g' := by
    intro e; rw [hr e]; split_ifs <;> linarith

  have hnum : ∀ (a e : Fin d) (n : ℕ) (L : ℝ), (good a → -(n : ℝ) ≤ L) →
      (-((n : ℝ) + 1) ≤ L) → r e ≤ L + (p : ℝ) ^ (n + 1) * r a := by
    intro a e n L hLg hL
    have hb := one_add_mul_sub_le_pow (a := (p : ℝ)) (by linarith) n
    have hb' := mul_le_mul_of_nonneg_left hb hg'0.le
    have hb1 := one_add_mul_sub_le_pow (a := (p : ℝ)) (by linarith) (n + 1)
    have hb1' := mul_le_mul_of_nonneg_left hb1 hg'0.le
    have e1 : g' * (1 + (n : ℝ) * ((p : ℝ) - 1)) = g' + 2 * n := by
      linear_combination (n : ℝ) * hg'1
    have e2 : g' * (1 + ((n + 1 : ℕ) : ℝ) * ((p : ℝ) - 1)) = g' + 2 * ((n : ℝ) + 1) := by
      push_cast; linear_combination ((n : ℝ) + 1) * hg'1
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hre' := hre e
    rw [hr a]
    split_ifs with hga
    · have hL' := hLg hga
      have e3 : (p : ℝ) ^ (n + 1) * (2 / ((p : ℝ) * (p - 1))) = g' * (p : ℝ) ^ n := by
        rw [_root_.pow_succ, ← hgp]; ring
      rw [e3]; linarith
    · have e4 : (p : ℝ) ^ (n + 1) * g' = g' * (p : ℝ) ^ (n + 1) := by ring
      rw [e4]; linarith
  have step : ∀ D : ℕ, ∀ a, WtBelow v ρ D (t a) (r a) := by
    intro D
    induction D with
    | zero => intro a α hα; omega
    | succ D ih =>
      intro e α hα
      have h1 : coeff α (lgSum p c t e) = coeff α (z e) := by rw [hlg e]
      have h2 : coeff α (lgSum p c t e) =
          ∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ a, c a n e * coeff α (t a ^ (p ^ n)) :=
        rfl
      rw [h2, Finset.sum_range_succ'] at h1
      have h3 : ∑ a, c a 0 e * coeff α (t a ^ (p ^ 0)) = coeff α (t e) := by
        simp [h0, Pi.single_apply]
      rw [h3] at h1
      rw [eq_sub_of_add_eq' h1]
      refine v.map_le_sub (hz e α) ?_
      refine v.map_le_sum fun n _ => v.map_le_sum fun a _ => ?_
      have hN : 2 ≤ p ^ (n + 1) := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
      have h4 := (ih a).pow (ht a) hN α hα
      rw [v.map_mul]
      by_cases hga : good a
      · have hc1 := hgood a hga (n + 1) e (by omega)
        refine le_trans ?_ (add_le_add hc1 h4)
        rw [← WithTop.coe_add, WithTop.coe_le_coe]
        have := hnum a e n (1 - ((n + 1 : ℕ) : ℝ)) (fun _ => by push_cast; linarith)
          (by push_cast; linarith)
        push_cast at this ⊢
        linarith
      · have hc1 := hc a (n + 1) e
        refine le_trans ?_ (add_le_add hc1 h4)
        rw [← WithTop.coe_add, WithTop.coe_le_coe]
        have := hnum a e n (-((n + 1 : ℕ) : ℝ)) (fun h => absurd h hga) (by push_cast; linarith)
        push_cast at this ⊢
        linarith
  intro b α
  exact step (Finsupp.degree α + 1) b α (by omega)

theorem ordGe_of_lgSum_twoRadii :
    ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (p : ℕ), p.Prime → v (p : C) = 1 → ∀ (d M : ℕ) (good : Fin d → Prop) [DecidablePred good] (c : Fin d → ℕ → Fin d → C), (∀ a, c a 0 = Pi.single a 1) → (∀ a (n : ℕ) b, ((-(n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b)) → (∀ a, good a → ∀ (n : ℕ) b, 1 ≤ n → ((1 - (n : ℝ) : ℝ) : WithTop ℝ) ≤ v (c a n b)) → ∀ (ρ : Fin M → ℝ) (z t : Fin d → MvPowerSeries (Fin M) C), (∀ b, OrdGe v ρ (z b) (if good b then 2 / ((p : ℝ) * (p - 1)) else 2 / ((p : ℝ) - 1))) → (∀ b, constantCoeff (t b) = 0) → (∀ b, lgSum p c t b = z b) → ∀ b, OrdGe v ρ (t b) (if good b then 2 / ((p : ℝ) * (p - 1)) else 2 / ((p : ℝ) - 1)) := by
  intro C _ _ v p hp _ d M good _ c h0 hc hgood ρ z t hz ht hlg
  exact ordGe_of_lgSum_radii v p hp good c h0 hc hgood ρ z t
    (fun b => if good b then 2 / ((p : ℝ) * (p - 1)) else 2 / ((p : ℝ) - 1)) (fun _ => rfl)
    hz ht hlg

end GlobalTheory.ExpWeightTwoRadii
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootFreeActionFinsuppSum
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KummerSplit

noncomputable section

namespace GlobalTheory.EtC.FreeActSum

def rootUnit {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) : Aˣ :=
  Units.ofPowEqOne ζ.1 q ((GlobalTheory.EtC.PrimBasic.prim_basic q A).1 ζ) (NeZero.ne q)

lemma rootUnit_val {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) :
    ((rootUnit ζ : Aˣ) : A) = ζ.1 := rfl

lemma orderOf_rootUnit {q : ℕ} [NeZero q] {A : Type} [CommRing A] [Nontrivial A] (ζ : Prim q A) :
    orderOf (rootUnit ζ) = q := by
  rw [orderOf_eq_iff (NeZero.pos q)]
  refine ⟨?_, ?_⟩
  · ext; simp [rootUnit_val, (GlobalTheory.EtC.PrimBasic.prim_basic q A).1 ζ]
  · intro m hmq hm0 h1
    have hne : ¬ m ≡ 0 [MOD q] := by
      intro h
      have := (Nat.modEq_zero_iff_dvd).1 h
      exact absurd (Nat.le_of_dvd hm0 this) (not_le.2 hmq)
    have hu := (GlobalTheory.EtC.PrimBasic.prim_basic q A).2.2.1 ζ m 0 hne
    have h1' : ζ.1 ^ m = 1 := by
      have := congrArg (fun u : Aˣ => (u : A)) h1
      simpa [rootUnit_val] using this
    rw [h1', pow_zero, sub_self] at hu
    exact not_isUnit_zero hu

abbrev H {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) : Subgroup Aˣ :=
  Subgroup.zpowers (rootUnit ζ)

lemma mem_H {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (u : Aˣ) :
    ((QuotientGroup.mk u : Aˣ ⧸ H ζ).out)⁻¹ * u ∈ H ζ := by
  rw [← QuotientGroup.eq]
  simp

def expo {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (u : Aˣ) : ℤ :=
  Classical.choose (Subgroup.mem_zpowers_iff.1 (mem_H ζ u))

lemma expo_spec {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (u : Aˣ) :
    rootUnit ζ ^ expo ζ u = ((QuotientGroup.mk u : Aˣ ⧸ H ζ).out)⁻¹ * u :=
  Classical.choose_spec (Subgroup.mem_zpowers_iff.1 (mem_H ζ u))

def tau {q : ℕ} [NeZero q] {A : Type} [CommRing A] (ζ : Prim q A) (u : Aˣ) : ZMod q :=
  (expo ζ u : ZMod q)

lemma tau_mul {q : ℕ} [NeZero q] {A : Type} [CommRing A] [Nontrivial A] (ζ : Prim q A) (u : Aˣ) (n : ℕ) :
    tau ζ (rootUnit ζ ^ n * u) = tau ζ u + n := by
  have hcls : (QuotientGroup.mk (rootUnit ζ ^ n * u) : Aˣ ⧸ H ζ) = QuotientGroup.mk u := by
    rw [QuotientGroup.eq]
    have : (rootUnit ζ ^ n * u)⁻¹ * u = (rootUnit ζ ^ n)⁻¹ := by
      rw [mul_inv_rev, mul_comm u⁻¹, mul_assoc, inv_mul_cancel, mul_one]
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)
  have h1 := expo_spec ζ (rootUnit ζ ^ n * u)
  have h2 := expo_spec ζ u
  rw [hcls] at h1
  set r := ((QuotientGroup.mk u : Aˣ ⧸ H ζ).out)
  have key : rootUnit ζ ^ (expo ζ (rootUnit ζ ^ n * u) - (n : ℤ) - expo ζ u) = 1 := by
    rw [zpow_sub, zpow_sub, h1, h2, zpow_natCast]
    simp [mul_comm, mul_left_comm, mul_assoc]
  rw [← orderOf_dvd_iff_zpow_eq_one, orderOf_rootUnit] at key
  unfold tau
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).2 key
  push_cast at this
  linear_combination this

end GlobalTheory.EtC.FreeActSum

namespace GlobalTheory.EtC.FreeActSum

theorem free_act_sum : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A] [Nontrivial A] (ζ : Prim q A) (ι : Type) (s : Finset ι) (c : ι → ULift.{1} (ZMod q)) (a : ι → ℕ) (v w : ι → Aˣ), (∀ i ∈ s, (w i : A) = ζ.1 ^ a i * v i) → (∑ i ∈ s, (Finsupp.single (w i) (c i) - Finsupp.single (v i) (c i))) = 0 → ∑ i ∈ s, (c i).down * (a i : ZMod q) = 0 := by
  intro q _ A _ _ ζ ι s c a v w hw hsum
  let T : (Aˣ →₀ ULift.{1} (ZMod q)) →+ ZMod q :=
    Finsupp.liftAddHom (fun u => (AddMonoidHom.mulRight (tau ζ u)).comp (AddEquiv.ulift.toAddMonoidHom))
  have hT := congrArg T hsum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_zero] at hT
  rw [← hT]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have hwu : w i = rootUnit ζ ^ a i * v i := by
    ext; simp [rootUnit_val, hw i hi]
  simp only [T, map_sub, Finsupp.liftAddHom_apply_single, AddMonoidHom.coe_comp, Function.comp_apply,
    AddMonoidHom.coe_mulRight]
  rw [hwu, tau_mul]
  show (c i).down * (a i : ZMod q) = (c i).down * (tau ζ (v i) + a i) - (c i).down * tau ζ (v i)
  ring

end GlobalTheory.EtC.FreeActSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdSubConjEqZero
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.GalSec.Tens

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]


open Classical in
def conj (θ : Ω) : Finset Ω := by
  classical
  exact ((minpoly K θ).aroots Ω).toFinset

def DependsOn (k : ℕ) (θ : Ω) (φ : LCRing K Ω k) : Prop :=
  ∀ g g' : Fin k → (Ω ≃ₐ[K] Ω), (∀ i, g i θ = g' i θ) → φ g = φ g'


open Classical in
def pick (k : ℕ) (θ : Ω) (t : Fin k → Ω) : Fin k → (Ω ≃ₐ[K] Ω) := by
  classical
  exact if h : ∃ g : Fin k → (Ω ≃ₐ[K] Ω), ∀ i, g i θ = t i then h.choose else 1

variable {K Ω}
variable {B : Type} [CommRing B]


open Classical in
def idem (g₀ : Ω →+* B) (θ : Ω) (b : B) (s : conj K Ω θ) : B := by
  classical
  exact g₀ (∏ j ∈ (Finset.univ : Finset (conj K Ω θ)).erase s, ((s : Ω) - (j : Ω)))⁻¹ *
    ∏ j ∈ (Finset.univ : Finset (conj K Ω θ)).erase s, (b - g₀ (j : Ω))

def lev (g₀ : Ω →+* B) {k : ℕ} (gs : Fin k → (Ω →+* B)) (θ : Ω) (φ : LCRing K Ω k) : B :=
  ∑ t : Fin k → conj K Ω θ, g₀ (φ (pick K Ω k θ (fun i => (t i : Ω)))) * ∏ i, idem g₀ θ (gs i θ) (t i)

end GlobalTheory.EtC.GalSec.Tens

namespace GlobalTheory.EtC.GalSec.Tens

open Polynomial

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

theorem mem_conj_iff [Algebra.IsAlgebraic K Ω] [Normal K Ω] (θ s : Ω) :
    s ∈ conj K Ω θ ↔ ∃ σ : Ω ≃ₐ[K] Ω, σ θ = s := by
  classical
  have hne : minpoly K θ ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral θ)
  simp only [conj, Multiset.mem_toFinset, mem_aroots, ne_eq, hne, not_false_eq_true, true_and]
  constructor
  · intro h
    have hm : minpoly K s = minpoly K θ :=
      (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible (Algebra.IsIntegral.isIntegral θ)) h
        (minpoly.monic (Algebra.IsIntegral.isIntegral θ))).symm
    obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit Ω).1 hm
    exact ⟨σ, hσ⟩
  · rintro ⟨σ, rfl⟩
    rw [aeval_algEquiv, AlgHom.comp_apply, minpoly.aeval, map_zero]

theorem self_mem_conj [Algebra.IsAlgebraic K Ω] [Normal K Ω] (θ : Ω) : θ ∈ conj K Ω θ :=
  (mem_conj_iff θ θ).2 ⟨1, rfl⟩

theorem prod_conj [Algebra.IsAlgebraic K Ω] [Normal K Ω] [Algebra.IsSeparable K Ω] (θ : Ω) :
    ∏ s ∈ conj K Ω θ, (X - C s) = (minpoly K θ).map (algebraMap K Ω) := by
  classical
  have hint := Algebra.IsIntegral.isIntegral (R := K) θ
  have hsp : Splits ((minpoly K θ).map (algebraMap K Ω)) := Normal.splits inferInstance θ
  have hmo : ((minpoly K θ).map (algebraMap K Ω)).Monic := (minpoly.monic hint).map _
  have hnd : ((minpoly K θ).map (algebraMap K Ω)).roots.Nodup :=
    nodup_roots (Polynomial.Separable.map (Algebra.IsSeparable.isSeparable K θ))
  conv_rhs => rw [hsp.eq_prod_roots_of_monic hmo]
  rw [conj, aroots, Finset.prod_eq_multiset_prod, Multiset.toFinset_val, hnd.dedup]

end GlobalTheory.EtC.GalSec.Tens

namespace GlobalTheory.EtC.GalSec.Tens

open Polynomial

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

theorem apply_mem_conj [Algebra.IsAlgebraic K Ω] [Normal K Ω] (θ : Ω) (σ : Ω ≃ₐ[K] Ω) :
    σ θ ∈ conj K Ω θ :=
  (mem_conj_iff θ (σ θ)).2 ⟨σ, rfl⟩

theorem prod_sub_conj_eq_zero [Algebra.IsAlgebraic K Ω] [Normal K Ω] [Algebra.IsSeparable K Ω]
    {B : Type} [CommRing B] (g₀ σ' : Ω →+* B)
    (h : σ'.comp (algebraMap K Ω) = g₀.comp (algebraMap K Ω)) (θ : Ω) :
    ∏ s ∈ conj K Ω θ, (σ' θ - g₀ s) = 0 := by
  have h1 : (∏ s ∈ conj K Ω θ, (X - C s)).eval₂ g₀ (σ' θ) = ∏ s ∈ conj K Ω θ, (σ' θ - g₀ s) := by
    rw [eval₂_finsetProd]
    simp
  rw [← h1, prod_conj, eval₂_map, ← h, ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]

theorem idem_spec [Algebra.IsAlgebraic K Ω] [Normal K Ω] {B : Type} [CommRing B] (g₀ : Ω →+* B)
    (θ : Ω) (b : B) (hb : ∏ s ∈ conj K Ω θ, (b - g₀ s) = 0) :
    CompleteOrthogonalIdempotents (idem (K := K) g₀ θ b) ∧ (∀ s : conj K Ω θ, b * idem (K := K) g₀ θ b s = g₀ s * idem (K := K) g₀ θ b s) ∧
      b = ∑ s : conj K Ω θ, g₀ s * idem (K := K) g₀ θ b s := by
  classical
  letI : Algebra Ω B := g₀.toAlgebra
  haveI : Nonempty (conj K Ω θ) := ⟨⟨θ, self_mem_conj θ⟩⟩
  have hid : idem (K := K) g₀ θ b = GlobalTheory.Pat.lagIdem b (fun j : conj K Ω θ => (j : Ω)) := by
    funext s
    rw [idem, GlobalTheory.Pat.lagIdem, Ring.inverse_eq_inv', Algebra.smul_def, map_prod]
    simp only [map_sub, aeval_X, aeval_C, RingHom.algebraMap_toAlgebra]
  have hu : ∀ i j : conj K Ω θ, i ≠ j → IsUnit ((i : Ω) - j) := fun i j h =>
    (sub_ne_zero.2 (Subtype.coe_injective.ne h)).isUnit
  have hP : aeval b (∏ j : conj K Ω θ, (X - C (j : Ω))) = 0 := by
    rw [map_prod]
    simp only [map_sub, aeval_X, aeval_C, RingHom.algebraMap_toAlgebra]
    rw [Finset.prod_coe_sort (conj K Ω θ) (fun s => b - g₀ s)]
    exact hb
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.lagIdem_spec Ω B (conj K Ω θ) b _ hu hP
  rw [hid]
  refine ⟨h1, fun s => ?_, ?_⟩
  · rw [h2 s, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  · conv_lhs => rw [h3]
    simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra]

theorem pick_spec [Algebra.IsAlgebraic K Ω] [Normal K Ω] (k : ℕ) (θ : Ω) (t : Fin k → Ω)
    (ht : ∀ i, t i ∈ conj K Ω θ) (i : Fin k) : pick K Ω k θ t i θ = t i := by
  have hex : ∃ g : Fin k → (Ω ≃ₐ[K] Ω), ∀ i, g i θ = t i := by
    choose g hg using fun i => (mem_conj_iff θ (t i)).1 (ht i)
    exact ⟨g, hg⟩
  classical
  rw [pick, dite_eq_left hex]
  exact hex.choose_spec i

end GlobalTheory.EtC.GalSec.Tens

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullSpMapComp
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

def laurentMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) : LaurentPolynomial A →+* LaurentPolynomial B :=
  AddMonoidAlgebra.mapRingHom ℤ f

namespace GmPhiNat

theorem laurentMap_C {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    (laurentMap f).comp (LaurentPolynomial.C : A →+* LaurentPolynomial A) = (LaurentPolynomial.C : B →+* LaurentPolynomial B).comp f := by
  refine RingHom.ext fun a => ?_
  change AddMonoidAlgebra.mapRingHom ℤ f (LaurentPolynomial.C a) = LaurentPolynomial.C (f a)
  rw [← LaurentPolynomial.single_eq_C, AddMonoidAlgebra.mapRingHom_single]; rfl

theorem laurentMap_T {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (n : ℤ) :
    laurentMap f (LaurentPolynomial.T n) = LaurentPolynomial.T n := by
  change AddMonoidAlgebra.mapRingHom ℤ f (AddMonoidAlgebra.single n (1 : A)) = AddMonoidAlgebra.single n (1 : B)
  rw [AddMonoidAlgebra.mapRingHom_single, map_one]

theorem laurentMap_comp {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) :
    laurentMap (g.comp f) = (laurentMap g).comp (laurentMap f) :=
  AddMonoidAlgebra.mapRingHom_comp _ _

theorem spMap_comp {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, ← Functor.map_comp, ← Spec.map_comp]
  rfl

theorem pull_spMap_comp (q : ℕ) {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) (n i : ℤ)
    (x : Ht q (sp A) n i) : pull _ (spMap (g.comp f)) _ n x = pull _ (spMap g) _ n (pull _ (spMap f) _ n x) := by
  rw [spMap_comp, pull_comp]

theorem pull_cast (q : ℕ) {E E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (hn : n = n') (hi : i = i') (x : Ht q E' n i) :
    pull _ f (tw q i') n' (Ht.cast hn hi x) = Ht.cast hn hi (pull _ f (tw q i) n x) := by
  subst hn; subst hi; rfl

theorem laurentVar_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) :
    Units.map (Spec.map (CommRingCat.ofHom (laurentMap f))).appTop.hom.toMonoidHom (laurentVar A) = laurentVar B := by
  apply Units.ext
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (laurentMap f))
  have h2 := congrArg (fun φ => φ.hom (LaurentPolynomial.T 1)) h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  simp only [laurentVar, laurentVarUnit, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  rw [← h2, laurentMap_T]

theorem isUnit_gamma (q : ℕ) (A : Type) [CommRing A] (hq : IsUnit (q : A)) :
    IsUnit (q : Γ(Spec (CommRingCat.of (LaurentPolynomial A)), ⊤)) := by
  have h := (hq.map (LaurentPolynomial.C : A →+* LaurentPolynomial A)).map
    (Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial A))).inv.hom
  simpa using h

end GmPhiNat


open GmPhiNat in
theorem gmPhi_nat (h6 : DivisorNaturality) (q : ℕ) [NeZero q] {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hq : IsUnit (q : A))
    (i : ℤ) (a : Ht q (sp A) 0 (i - 1)) :
    pull _ (spMap (laurentMap f)) _ 1 (gmPhi q A i a) = gmPhi q B i (pull _ (spMap f) _ 0 a) := by
  obtain ⟨hcup, -, -, hkum⟩ := h6 q
  simp only [gmPhi, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
  rw [pull_cast, hcup, ← pull_spMap_comp, ← pull_spMap_comp, laurentMap_C]
  congr 2
  rw [spMap, hkum _ _ (isUnit_gamma q A hq), laurentVar_map]

end GlobalTheory.EtC

end
end

