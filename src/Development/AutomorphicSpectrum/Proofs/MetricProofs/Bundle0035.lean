module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0036
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplier
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SumFundCoMulSumIic
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RootOriginWeightComparison
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.Fund

theorem sum_neg_mul_eq_sum_fundCo {Ψ : Type} [Fintype Ψ] {N : ℕ} (f : Ψ → Fin N → ℝ) (B R : Ψ × Fin N → ℝ)
    (h : ∀ τ i, R (τ, i) = -∑ k ∈ Finset.Iic i, B (τ, k)) :
    ∑ r : Ψ × Fin N, -f r.1 r.2 * B r = ∑ r : Ψ × Fin N, fundCo (f r.1) r.2 * R r := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have e := sum_fundCo_mul_sum_Iic (f τ) fun k => B (τ, k)
  simp only [h, mul_neg, Finset.sum_neg_distrib, neg_mul]
  rw [e]

theorem weight_sub_log_sing :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (lam nu : Wt (CMType H) (D.p + D.q)) (n' : Option (RootIx D) → ℤ) (s : ℝ) (x : Or.Re.R.X), (∀ j, (n' j : ℝ) = RM.coef lam 0 j) → scale s ≤ Sys.t₀ → Or.Re.π x ∈ Sys.open' → RM.weight (scale s) (lam - s • nu) s (Or.Re.R.lift x x) - Real.log (∏ r, (Or.sing r).h (Or.Re.R.lift x x) ^ n' (some r)) = s / RM.kA * Real.log (RM.A.h (Or.Re.R.lift x x)) - s * ∑ r : RootIx D, fundCo (nu r.1) r.2 * Real.log ((Or.Re.ref (some r)).h (Or.Re.R.lift x x)) + ∑ r : RootIx D, fundCo ((lam - s • nu) r.1) r.2 * Sys.phT (some r) (scale s) (Or.Re.π x) - ∑ r : RootIx D, fundCo (lam r.1) r.2 * Sys.ph (some r) (Or.Re.π x) := by
  intro E _ _ _ H D l Xo c O _ β Y S RM Sys Fx Or lam nu n' s x hn ht hop
  have hw := Or.Re.R.mem x x (Or.Re.R.mem_U x)
  have ht0 : 0 < scale s := Real.exp_pos _
  have hreg : ∀ τ i, Real.log ((Or.Re.ref (some (τ, i))).h (Or.Re.R.lift x x)) +
      Sys.phT (some (τ, i)) (scale s) (Or.Re.π x) =
      -∑ k ∈ Finset.Iic i, Real.log ((RM.x (scale s) (τ, k)).h (Or.Re.R.lift x x)) := fun τ i => by
    rw [← Or.fund_reg τ i (scale s) ht0 ht _ hw, Or.Re.line_eq (some (τ, i)) (scale s) ht0 ht x]
  have hsing : ∀ τ i, Real.log ((Or.Re.ref (some (τ, i))).h (Or.Re.R.lift x x)) +
      Sys.ph (some (τ, i)) (Or.Re.π x) =
      -∑ k ∈ Finset.Iic i, Real.log ((Or.sing (τ, k)).h (Or.Re.R.lift x x)) :=
    fun τ i => Or.fund_sing τ i x hop
  have e1 := sum_neg_mul_eq_sum_fundCo (lam - s • nu)
    (fun r => Real.log ((RM.x (scale s) r).h (Or.Re.R.lift x x)))
    (fun r => Real.log ((Or.Re.ref (some r)).h (Or.Re.R.lift x x)) +
      Sys.phT (some r) (scale s) (Or.Re.π x)) hreg
  have e2 := sum_neg_mul_eq_sum_fundCo lam
    (fun r => Real.log ((Or.sing r).h (Or.Re.R.lift x x)))
    (fun r => Real.log ((Or.Re.ref (some r)).h (Or.Re.R.lift x x)) +
      Sys.ph (some r) (Or.Re.π x)) hsing
  have hlog : Real.log (∏ r, (Or.sing r).h (Or.Re.R.lift x x) ^ n' (some r)) =
      ∑ r : RootIx D, -lam r.1 r.2 * Real.log ((Or.sing r).h (Or.Re.R.lift x x)) := by
    rw [Real.log_prod fun r _ => zpow_ne_zero _ ((Or.sing r).pos _ hw.1).ne']
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Real.log_zpow, hn (some r)]
    rfl
  have hwt : RM.weight (scale s) (lam - s • nu) s (Or.Re.R.lift x x) =
      s / RM.kA * Real.log (RM.A.h (Or.Re.R.lift x x)) +
        ∑ r : RootIx D, -(lam - s • nu) r.1 r.2 * Real.log ((RM.x (scale s) r).h (Or.Re.R.lift x x)) := by
    unfold RootModel.weight
    rw [Fintype.sum_option]
    rfl
  rw [hwt, hlog, e1, e2]
  have hco : ∀ r : RootIx D, fundCo ((lam - s • nu) r.1) r.2 = fundCo (lam r.1) r.2 - s * fundCo (nu r.1) r.2 := by
    intro r
    have : (lam - s • nu) r.1 = lam r.1 - s • nu r.1 := rfl
    rw [this, fundCo_sub, fundCo_smul]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  have hρ : ∑ r : RootIx D, fundCo ((lam - s • nu) r.1) r.2 * Real.log ((Or.Re.ref (some r)).h (Or.Re.R.lift x x)) =
      ∑ r : RootIx D, fundCo (lam r.1) r.2 * Real.log ((Or.Re.ref (some r)).h (Or.Re.R.lift x x)) -
        ∑ r : RootIx D, s * (fundCo (nu r.1) r.2 * Real.log ((Or.Re.ref (some r)).h (Or.Re.R.lift x x))) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hco]
    ring
  rw [hρ]
  ring

end GlobalTheory.CompanionTheory.Ar.Small.Fund
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RootOriginWeightComparisonShift
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.Fund.Orbit

theorem log_h_scale {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (ℓ : HermLine ι) (c : K → ℂ)
    (z : (Σ k, ι k) → ℂ) (hc : ∀ k, c k ≠ 0) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log (ℓ.h (fun p => c p.1 * z p)) = Real.log (ℓ.h z) + ∑ k, (ℓ.a k : ℝ) * Real.log ‖c k‖ := by
  have hn : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hc k)
  rw [ℓ.smul c z hc, Real.log_mul (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hn k)) (ℓ.pos z hz).ne',
    Real.log_prod (fun k _ => zpow_ne_zero _ (hn k)), add_comm]
  simp only [Real.log_zpow]

theorem coef_add_smul {Ψ : Type} [Fintype Ψ] {N : ℕ} (R : RootModel Ψ N) (lam nu : Wt Ψ N) (s : ℝ)
    (j : Option (Ψ × Fin N)) : R.coef (lam - s • nu) s j + s * R.coef nu (-1) j = R.coef lam 0 j := by
  cases j with
  | none => simp only [RootModel.coef]; ring
  | some r => simp only [RootModel.coef, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem line_a {Ψ : Type} [Fintype Ψ] {N : ℕ} (R : RootModel Ψ N) (t : ℝ) (j : Option (Ψ × Fin N)) :
    (R.line t j).a = (R.line 1 j).a := by
  cases j with
  | none => rfl
  | some r => simp only [RootModel.line, R.x_deg]

theorem torus_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (lam nu : Wt (CMType H) (D.p + D.q)) (n' n₀ : Option (RootIx D) → ℤ) (q₀ : ℕ) (s t : ℝ) (cc : RM.K → ℂ) (z : (Σ k, RM.ι k) → ℂ) (v : ℂ), 0 < q₀ → (∀ j, (n' j : ℝ) = RM.coef lam 0 j) → (∀ j, (n₀ j : ℝ) = q₀ * RM.coef nu (-1) j) → (∀ k, cc k ≠ 0) → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → v ≠ 0 → s / q₀ * Real.log ‖v * ∏ k, cc k ^ (combLine (RM.line 1) n₀).a k‖ + RM.weight t (lam - s • nu) s (fun p => cc p.1 * z p) - Real.log (∏ r, (Or.sing r).h (fun p => cc p.1 * z p) ^ n' (some r)) = s / q₀ * Real.log ‖v‖ + RM.weight t (lam - s • nu) s z - Real.log (∏ r, (Or.sing r).h z ^ n' (some r)) := by
  intro E _ _ _ H D l Xo c O _ β Y S RM Sys Fx Or lam nu n' n₀ q₀ s t cc z v hq hn' hn₀ hc hz hv
  have hq0 : (q₀ : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne'
  have hn : ∀ k, ‖cc k‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hc k)
  have hzc : ∀ k, ∃ i, (fun p : (Σ k, RM.ι k) => cc p.1 * z p) ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hz k
    exact ⟨i, mul_ne_zero (hc k) hi⟩

  have ha : ∀ k, (((combLine (RM.line 1) n₀).a k : ℤ) : ℝ) = ∑ j, (n₀ j : ℝ) * ((RM.line 1 j).a k : ℝ) := by
    intro k
    simp only [GlobalTheory.CompanionTheory.Ar.Top.combLine, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    rfl

  have h1 : Real.log ‖v * ∏ k, cc k ^ (combLine (RM.line 1) n₀).a k‖ =
      Real.log ‖v‖ + ∑ k, ((combLine (RM.line 1) n₀).a k : ℝ) * Real.log ‖cc k‖ := by
    rw [norm_mul, norm_prod, Real.log_mul (norm_ne_zero_iff.mpr hv)
      (Finset.prod_ne_zero_iff.mpr fun k _ => norm_ne_zero_iff.mpr (zpow_ne_zero _ (hc k))),
      Real.log_prod (fun k _ => norm_ne_zero_iff.mpr (zpow_ne_zero _ (hc k)))]
    simp only [norm_zpow, Real.log_zpow]

  have h2 : RM.weight t (lam - s • nu) s (fun p => cc p.1 * z p) =
      RM.weight t (lam - s • nu) s z +
        ∑ k, (∑ j, RM.coef (lam - s • nu) s j * ((RM.line 1 j).a k : ℝ)) * Real.log ‖cc k‖ := by
    simp only [RootModel.weight, log_h_scale _ cc z hc hz, line_a RM t, mul_add, Finset.sum_add_distrib]
    congr 1
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

  have hlog : ∀ w : (Σ k, RM.ι k) → ℂ, (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) →
      Real.log (∏ r, (Or.sing r).h w ^ n' (some r)) = ∑ r, (n' (some r) : ℝ) * Real.log ((Or.sing r).h w) := by
    intro w hw
    rw [Real.log_prod (fun r _ => (zpow_pos ((Or.sing r).pos w hw) _).ne')]
    simp only [Real.log_zpow]
  have h3 : Real.log (∏ r, (Or.sing r).h (fun p => cc p.1 * z p) ^ n' (some r)) =
      Real.log (∏ r, (Or.sing r).h z ^ n' (some r)) +
        ∑ k, (∑ r, (n' (some r) : ℝ) * (RM.xdeg r k : ℝ)) * Real.log ‖cc k‖ := by
    rw [hlog _ hzc, hlog z hz]
    simp only [log_h_scale _ cc z hc hz, Or.sing_deg, mul_add, Finset.sum_add_distrib]
    congr 1
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring

  have hn'none : (n' none : ℝ) = 0 := by
    rw [hn' none]
    simp [RootModel.coef]
  have h4 : ∀ k, s / q₀ * ((combLine (RM.line 1) n₀).a k : ℝ) +
      ∑ j, RM.coef (lam - s • nu) s j * ((RM.line 1 j).a k : ℝ) =
      ∑ r, (n' (some r) : ℝ) * (RM.xdeg r k : ℝ) := by
    intro k
    have e1 : ∑ r, (n' (some r) : ℝ) * (RM.xdeg r k : ℝ) = ∑ j, (n' j : ℝ) * ((RM.line 1 j).a k : ℝ) := by
      rw [Fintype.sum_option, hn'none, zero_mul, zero_add]
      exact Finset.sum_congr rfl fun r _ => by simp only [RootModel.line, RM.x_deg]
    rw [e1, ha, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hn₀ j, hn' j, ← coef_add_smul RM lam nu s j]
    field_simp
    ring
  rw [h1, h2, h3]
  have h5 : s / q₀ * ∑ k, ((combLine (RM.line 1) n₀).a k : ℝ) * Real.log ‖cc k‖ +
      ∑ k, (∑ j, RM.coef (lam - s • nu) s j * ((RM.line 1 j).a k : ℝ)) * Real.log ‖cc k‖ =
      ∑ k, (∑ r, (n' (some r) : ℝ) * (RM.xdeg r k : ℝ)) * Real.log ‖cc k‖ := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← h4 k]
    ring
  linear_combination h5

end GlobalTheory.CompanionTheory.Ar.Small.Fund.Orbit
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SameOrbitRefl
section
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Cj

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

abbrev cj (z : (Σ k, ι k) → ℂ) : (Σ k, ι k) → ℂ := fun q => starRingEnd ℂ (z q)

theorem cj_cj (z : (Σ k, ι k) → ℂ) : cj (cj z) = z := by
  funext q; simp [cj]

theorem cj_nonzero {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    ∀ k, ∃ i, cj z ⟨k, i⟩ ≠ 0 := fun k => by
  obtain ⟨i, hi⟩ := hz k
  exact ⟨i, by simpa [cj] using hi⟩

theorem sameOrbit_symm {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit z' z := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext p
  simp [← mul_assoc, inv_mul_cancel₀ (hc p.1)]

theorem sameOrbit_trans {z z' z'' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (h' : SameOrbit z' z'') :
    SameOrbit z z'' := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨c', hc', rfl⟩ := h'
  refine ⟨fun k => c k * c' k, fun k => mul_ne_zero (hc k) (hc' k), ?_⟩
  funext p
  simp [mul_assoc]

theorem sameOrbit_refl (z : (Σ k, ι k) → ℂ) : SameOrbit z z :=
  ⟨fun _ => 1, fun _ => one_ne_zero, by simp⟩

theorem sameOrbit_cj {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') : SameOrbit (cj z) (cj z') := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => starRingEnd ℂ (c k), fun k => by simpa using hc k, ?_⟩
  funext p
  simp [cj]

theorem cj_mem_mcPts {P : Ideal (MRing ι)} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P) : cj z ∈ mcPts P := by
  refine ⟨cj_nonzero hz.1, fun f hf => ?_⟩
  have h := hz.2 f hf
  have key : eval (cj z) (map (Int.castRingHom ℂ) f) =
      starRingEnd ℂ (eval z (map (Int.castRingHom ℂ) f)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [MvPolynomial.eval_map, MvPolynomial.eval_map, MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq,
      map_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp [map_mul, map_prod, map_pow]
  rw [key, h, map_zero]

theorem log_sub_orbit (A B : HermLine ι) (hab : A.a = B.a) {z z' : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) (h : SameOrbit z z') :
    Real.log (A.h z) - Real.log (B.h z) = Real.log (A.h z') - Real.log (B.h z') := by
  obtain ⟨c, hc, rfl⟩ := h
  have hP : 0 < ∏ k, ‖c k‖ ^ A.a k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hc k)) _
  rw [A.smul c z' hc, B.smul c z' hc, ← hab,
    Real.log_mul hP.ne' (A.pos z' hz).ne', Real.log_mul hP.ne' (B.pos z' hz).ne']
  ring

def conjAvg (A : HermLine ι) : HermLine ι where
  a := A.a
  h z := Real.sqrt |A.h z * A.h (cj z)|
  pos z hz := Real.sqrt_pos.2 (abs_pos.2 (mul_pos (A.pos z hz) (A.pos _ (cj_nonzero hz))).ne')
  smul c z hc := by
    have hP : 0 ≤ ∏ k, ‖c k‖ ^ A.a k :=
      Finset.prod_nonneg fun k _ => zpow_nonneg (norm_nonneg _) _
    have e1 : cj (fun p : Σ k, ι k => c p.1 * z p) =
        fun p => (starRingEnd ℂ (c p.1)) * cj z p := by
      funext p; simp [cj]
    have hc' : ∀ k, starRingEnd ℂ (c k) ≠ 0 := fun k => by simpa using hc k
    rw [e1, A.smul c z hc, A.smul _ (cj z) hc']
    simp only [RCLike.norm_conj]
    rw [show (∏ k, ‖c k‖ ^ A.a k) * A.h z * ((∏ k, ‖c k‖ ^ A.a k) * A.h (cj z)) =
      (∏ k, ‖c k‖ ^ A.a k) ^ 2 * (A.h z * A.h (cj z)) by ring, abs_mul, abs_of_nonneg (sq_nonneg _),
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hP]

theorem conjAvg_conj (A : HermLine ι) : IsConjInvariantH (conjAvg A) := fun z => by
  change Real.sqrt |A.h (cj z) * A.h (cj (cj z))| = Real.sqrt |A.h z * A.h (cj z)|
  rw [cj_cj, mul_comm]

theorem conjAvg_log (A : HermLine ι) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    Real.log ((conjAvg A).h z) = (Real.log (A.h z) + Real.log (A.h (cj z))) / 2 := by
  have h1 := A.pos z hz
  have h2 := A.pos _ (cj_nonzero hz)
  change Real.log (Real.sqrt |A.h z * A.h (cj z)|) = _
  rw [abs_of_pos (mul_pos h1 h2), Real.log_sqrt (mul_pos h1 h2).le, Real.log_mul h1.ne' h2.ne']

theorem conjAvg_smooth {A : HermLine ι} (hA : IsSmoothHerm A) : IsSmoothHerm (conjAvg A) := by
  set S : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} with hS
  have hconj : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cj : ((Σ k, ι k) → ℂ) → (Σ k, ι k) → ℂ) := by
    refine contDiff_pi.2 fun q => ?_
    exact Complex.conjCLE.contDiff.comp (contDiff_apply ℝ (fun _ => ℂ) q)
  have hmap : Set.MapsTo (cj : ((Σ k, ι k) → ℂ) → (Σ k, ι k) → ℂ) S S := fun z hz => cj_nonzero hz
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => A.h (cj z)) S :=
    hA.comp hconj.contDiffOn hmap
  have hprod := hA.mul h2
  have hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => Real.sqrt (A.h z * A.h (cj z))) S :=
    hprod.sqrt fun z hz => (mul_pos (A.pos z hz) (A.pos _ (cj_nonzero hz))).ne'
  refine hs.congr fun z hz => ?_
  change Real.sqrt |A.h z * A.h (cj z)| = _
  rw [abs_of_pos (mul_pos (A.pos z hz) (A.pos _ (cj_nonzero hz)))]

theorem holoOn_comp {e : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    {A : FinHolAtlas e X} {B : FinHolAtlas e Y} {g : X → Y} (hg : HoloMap A B g) {V : Set Y}
    {G : Y → ℂ} (hG : B.HoloOn V G) : A.HoloOn (g ⁻¹' V) (G ∘ g) := by
  intro j w hw
  obtain ⟨k, hk⟩ := B.cover (g ((A.chart j).symm w))
  have hw' : w ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' (g ⁻¹' (B.chart k).source) := ⟨hw.1, hk⟩
  have h1 := hg.2 j k w hw'
  have h2 : AnalyticAt ℂ (G ∘ (B.chart k).symm) ((B.chart k ∘ g ∘ (A.chart j).symm) w) := by
    refine hG k _ ⟨(B.chart k).map_source hk, ?_⟩
    simp only [Function.comp, Set.mem_preimage, (B.chart k).left_inv hk]
    exact hw.2
  have h3 := h2.comp h1
  refine h3.congr ?_
  have hc : ContinuousAt (g ∘ (A.chart j).symm) w :=
    hg.1.continuousAt.comp ((A.chart j).continuousAt_symm hw.1)
  filter_upwards [hc ((B.chart k).open_source.mem_nhds hk)] with w' hw''
  have hw3 : g ((A.chart j).symm w') ∈ (B.chart k).source := hw''
  simp only [Function.comp, (B.chart k).left_inv hw3]

def IsLiftSys {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (P : Ideal (MRing ι))
    (U : X → Set X) (lift : X → X → (Σ k, ι k) → ℂ) : Prop :=
  (∀ x, IsOpen (U x)) ∧ (∀ x, x ∈ U x) ∧ (∀ x p, A.HoloOn (U x) fun y => lift x y p) ∧
  (∀ x, ∀ y ∈ U x, lift x y ∈ mcPts P) ∧
  (∀ x x', ∀ y ∈ U x ∩ U x', SameOrbit (lift x y) (lift x' y)) ∧
  (∀ z ∈ mcPts P, ∃ x, SameOrbit (lift x x) z) ∧
  (∀ x x', SameOrbit (lift x x) (lift x' x') → x = x') ∧
  ∀ x, ∀ p : (k : K) → ι k, (∀ k, lift x x ⟨k, p k⟩ ≠ 0) → ∀ j, x ∈ (A.chart j).source →
    (fderiv ℂ (fun y => affCoord p (lift x ((A.chart j).symm y))) (A.chart j x)).ker = ⊥

end GlobalTheory.CompanionTheory.Ar.PB.Cj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SelM
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW

def selM {N : ℕ} (S : Finset (Fin N)) : Matrix (Fin N) (Fin S.card) ℂ :=
  Matrix.of fun a b => if a = S.orderEmbOfFin rfl b then 1 else 0

end GlobalTheory.CompanionTheory.Ar.PB.StepW
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.SncAdaptedChartSectionForm
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.LocalModel

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem continuousAt_of_chart {E : Type} [TopologicalSpace E] (A : FinHolAtlas e X) (j : Fin A.n) {p : X}
    (hp : p ∈ (A.chart j).source) (f : X → E)
    (h : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j p)) : ContinuousAt f p := by
  have h1 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ (A.chart j)) p :=
    ContinuousAt.comp (f := A.chart j) h ((A.chart j).continuousAt hp)
  refine h1.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hp] with z hz
  simp [(A.chart j).left_inv hz]

theorem continuousAt_of_holoOn (A : FinHolAtlas e X) {U : Set X} {g : X → ℂ} (hg : A.HoloOn U g)
    {p : X} (hp : p ∈ U) : ContinuousAt g p := by
  obtain ⟨j, hj⟩ := A.cover p
  refine continuousAt_of_chart A j hj g ?_
  refine (hg j _ ⟨(A.chart j).map_source hj, ?_⟩).continuousAt
  simpa [(A.chart j).left_inv hj] using hp

theorem continuousAt_of_smoothOn (A : FinHolAtlas e X) {U : Set X} (hU : IsOpen U) {f : X → ℝ}
    (hf : A.SmoothOn U f) {p : X} (hp : p ∈ U) : ContinuousAt f p := by
  obtain ⟨j, hj⟩ := A.cover p
  refine continuousAt_of_chart A j hj f ?_
  have hmem : A.chart j p ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U :=
    ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hp⟩
  exact (hf j).continuousOn.continuousAt
    (((A.chart j).isOpen_inter_preimage_symm hU).mem_nhds hmem)

theorem zero_set_and_bound : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s → ∀ (x : X) (φ : OpenPartialHomeomorph X (Fin e → ℂ)) (S : Finset (Fin e)) (μ : Fin e → ℕ) (v : X → ℂ), IsCompatChart A φ → Metric.closedBall (0 : Fin e → ℂ) 2 ⊆ φ.target → φ.source ⊆ L.U x → (∀ i ∈ S, 1 ≤ μ i) → A.HoloOn φ.source v → (∀ y ∈ φ.source, v y ≠ 0) → (∀ y ∈ φ.source, s x y = v y * ∏ i ∈ S, φ y i ^ μ i) → (∀ y ∈ φ.target, (φ.symm y ∈ bdry s ↔ ∃ i ∈ S, y i = 0)) ∧ ∃ M : ℝ, ∀ y ∈ Metric.closedBall (0 : Fin e → ℂ) 2, φ.symm y ∉ bdry s → |rW L s (φ.symm y) - rLoc S μ y| ≤ M := by
  intro e X _ A L s hL hs x φ S μ v hφ hball hsrc hμ hv hv0 hsv

  have glue : ∀ y ∈ φ.target, ‖s x (φ.symm y)‖ * Real.exp (-L.φ x (φ.symm y)) =
      ‖s (φ.symm y) (φ.symm y)‖ * Real.exp (-L.φ (φ.symm y) (φ.symm y)) := fun y hy =>
    hs.2 x (φ.symm y) (φ.symm y) ⟨hsrc (φ.map_target hy), L.mem_U _⟩
  have hform : ∀ y ∈ φ.target, s x (φ.symm y) = v (φ.symm y) * ∏ i ∈ S, y i ^ μ i := by
    intro y hy
    rw [hsv _ (φ.map_target hy)]
    simp only [φ.right_inv hy]
  have hzero : ∀ y ∈ φ.target, (φ.symm y ∈ bdry s ↔ ∃ i ∈ S, y i = 0) := by
    intro y hy
    have h1 : s (φ.symm y) (φ.symm y) = 0 ↔ s x (φ.symm y) = 0 := by
      have hg := glue y hy
      constructor
      · intro h0
        rw [h0] at hg
        simpa [Real.exp_ne_zero] using hg
      · intro h0
        rw [h0, norm_zero, zero_mul] at hg
        rcases mul_eq_zero.1 hg.symm with h | h
        · exact norm_eq_zero.1 h
        · exact absurd h (Real.exp_ne_zero _)
    change s (φ.symm y) (φ.symm y) = 0 ↔ _
    rw [h1, hform y hy, mul_eq_zero, Finset.prod_eq_zero_iff]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact absurd h (hv0 _ (φ.map_target hy))
      · exact ⟨i, hi, (pow_eq_zero_iff (Nat.one_le_iff_ne_zero.1 (hμ i hi))).1 h⟩
    · rintro ⟨i, hi, h⟩
      refine Or.inr ⟨i, hi, ?_⟩
      rw [h]
      exact zero_pow (Nat.one_le_iff_ne_zero.1 (hμ i hi))
  refine ⟨hzero, ?_⟩

  have hcont : ContinuousOn (fun y => -2 * Real.log ‖v (φ.symm y)‖ + 2 * L.φ x (φ.symm y)) φ.target := by
    intro y hy
    have hp := φ.map_target hy
    have cs : ContinuousAt φ.symm y := φ.continuousAt_symm hy
    have c1 : ContinuousAt (fun y => v (φ.symm y)) y :=
      ContinuousAt.comp (f := φ.symm) (continuousAt_of_holoOn A hv hp) cs
    have c2 : ContinuousAt (fun y => L.φ x (φ.symm y)) y :=
      ContinuousAt.comp (f := φ.symm)
        (continuousAt_of_smoothOn A (L.isOpen_U x) (hL.1 x) (hsrc hp)) cs
    have c3 : ContinuousAt (fun y => Real.log ‖v (φ.symm y)‖) y :=
      c1.norm.log (norm_ne_zero_iff.2 (hv0 _ hp))
    exact ((continuousAt_const.mul c3).add (continuousAt_const.mul c2)).continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Fin e → ℂ) 2).exists_bound_of_continuousOn
    (hcont.mono hball)
  refine ⟨C + |(∑ i ∈ S, (μ i : ℝ)) * Real.log 4|, fun y hy hnb => ?_⟩
  have hyt := hball hy
  have hnz : ∀ i ∈ S, y i ≠ 0 := fun i hi h0 => hnb ((hzero y hyt).2 ⟨i, hi, h0⟩)
  have hs0 : s (φ.symm y) (φ.symm y) ≠ 0 := hnb
  have hvn : ‖v (φ.symm y)‖ ≠ 0 := norm_ne_zero_iff.2 (hv0 _ (φ.map_target hyt))
  have hlogS : Real.log (∏ i ∈ S, ‖y i‖ ^ μ i) = ∑ i ∈ S, (μ i : ℝ) * Real.log ‖y i‖ := by
    rw [Real.log_prod (fun i hi => pow_ne_zero _ (norm_ne_zero_iff.2 (hnz i hi)))]
    exact Finset.sum_congr rfl fun i _ => Real.log_pow _ _
  have hlog : logNormSec L s (φ.symm y) = Real.log ‖v (φ.symm y)‖ +
      ∑ i ∈ S, (μ i : ℝ) * Real.log ‖y i‖ - L.φ x (φ.symm y) := by
    unfold logNormSec
    rw [← glue y hyt, hform y hyt, norm_mul, norm_prod]
    simp only [norm_pow]
    rw [Real.log_mul (mul_ne_zero hvn (Finset.prod_ne_zero_iff.2 fun i hi =>
        pow_ne_zero _ (norm_ne_zero_iff.2 (hnz i hi)))) (Real.exp_ne_zero _),
      Real.log_mul hvn (Finset.prod_ne_zero_iff.2 fun i hi =>
        pow_ne_zero _ (norm_ne_zero_iff.2 (hnz i hi))), hlogS, Real.log_exp]
    ring
  have hloc : rLoc S μ y = Real.exp 1 + (∑ i ∈ S, (μ i : ℝ)) * Real.log 4 -
      2 * ∑ i ∈ S, (μ i : ℝ) * Real.log ‖y i‖ := by
    unfold rLoc
    rw [Finset.sum_mul, Finset.mul_sum, add_sub_assoc, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hn : ‖y i‖ ≠ 0 := norm_ne_zero_iff.2 (hnz i hi)
    rw [Real.log_div (by norm_num) (pow_ne_zero _ hn), Real.log_pow]
    push_cast
    ring
  have hdiff : rW L s (φ.symm y) - rLoc S μ y =
      (-2 * Real.log ‖v (φ.symm y)‖ + 2 * L.φ x (φ.symm y)) -
        (∑ i ∈ S, (μ i : ℝ)) * Real.log 4 := by
    unfold rW
    rw [hlog, hloc]
    ring
  rw [hdiff]
  have hb := hC y hy
  rw [Real.norm_eq_abs] at hb
  exact (abs_sub _ _).trans (add_le_add hb le_rfl)

end GlobalTheory.CompanionTheory.Ar.PB.LocalModel
end
end

