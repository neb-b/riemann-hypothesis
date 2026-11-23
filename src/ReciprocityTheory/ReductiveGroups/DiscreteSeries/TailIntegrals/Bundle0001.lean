module

public import Mathlib

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.ScaleInt
section
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities

theorem scale_int {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {r : ℝ}
    (hr : (Module.finrank ℝ E : ℝ) < r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ a b : ℝ, 0 < a → 0 < b →
      ∫⁻ x, ENNReal.ofReal ((a + b * ‖x‖) ^ (-r)) ∂μ ≤
        ENNReal.ofReal (K * a ^ (-r) * (a / b) ^ (Module.finrank ℝ E : ℝ)) := by
  have hg := integrable_one_add_norm (μ := μ) hr
  refine ⟨∫ x, (1 + ‖x‖) ^ (-r) ∂μ, integral_nonneg fun x => by positivity, fun a b ha hb => ?_⟩
  have ht : 0 < a / b := div_pos ha hb
  have ha' := ha.ne'
  have hb' := hb.ne'
  have hpt : ∀ x : E, (a + b * ‖x‖) ^ (-r) = a ^ (-r) * (1 + ‖(a / b)⁻¹ • x‖) ^ (-r) := by
    intro x
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le),
      ← Real.mul_rpow ha.le (by positivity : (0 : ℝ) ≤ 1 + (a / b)⁻¹ * ‖x‖)]
    congr 1
    first | (field_simp; done) | (field_simp; ring)
  have hF : Integrable (fun x => a ^ (-r) * (1 + ‖(a / b)⁻¹ • x‖) ^ (-r)) μ :=
    (hg.comp_smul (inv_ne_zero ht.ne')).const_mul (a ^ (-r))
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal hF (Filter.Eventually.of_forall fun x =>
    mul_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg (by positivity) _))]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_const_mul, Measure.integral_comp_smul (μ := μ) (f := fun y => (1 + ‖y‖) ^ (-r)) (R := (a / b)⁻¹),
    smul_eq_mul, inv_pow, inv_inv, abs_of_pos (pow_pos ht _), Real.rpow_natCast]
  exact le_of_eq (by ring)

end ReciprocityTheory.ChartRestriction.DS.Xi.RankOneLeviIdentities
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TailIntegrals.TailInt
section
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Xi

abbrev Xp (p m : ℕ) := (Fin p → ℂ) × (Fin p → ℂ) × (Fin m → ℂ) × ℝ

def Lsq {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : ℝ :=
  1 + ∑ j : Fin p, if j.val < l.val then ‖x.1 j‖ ^ 2 else 0

def bco {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : ℂ :=
  (((-(∑ i, ‖x.2.2.1 i‖ ^ 2) / 2 : ℝ)) : ℂ) + (x.2.2.2 : ℂ) * Complex.I -
    ∑ j : Fin p, if l.val ≤ j.val then x.2.1 j * star (x.1 j) else 0

def rhoSq {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : ℝ :=
  Lsq x (Fin.last p) + ∑ i, ‖x.2.2.1 i‖ ^ 2 + ∑ j : Fin p, if l.val ≤ j.val then ‖x.2.1 j‖ ^ 2 else 0

def de {p m : ℕ} (x : Xp p m) (l : Fin (p + 1)) : ℝ :=
  Real.sqrt (Lsq x l * rhoSq x l + ‖bco x l‖ ^ 2)

def s0N (p m : ℕ) (l : Fin (p + 1)) : ℝ := if l.val < p then 2 else (m : ℝ) + 1

def CHInt (p m : ℕ) (ν : Fin (p + 1) → ℝ) : ℝ≥0∞ :=
  ∫⁻ x : Xp p m, ∏ l, ENNReal.ofReal (de x l ^ (-(s0N p m l + ν l)))

def CHCond (p : ℕ) (ν : Fin (p + 1) → ℝ) : Prop :=
  (∀ l : Fin (p + 1), 0 < ∑ j ∈ Finset.Iic l, ν j) ∧
  (∀ l : Fin (p + 1), l.val < p → 0 < ∑ j ∈ Finset.Iic l, ν j + 2 * ∑ j ∈ Finset.Ioi l, ν j)

def CH : Prop := ∀ (p m : ℕ) (ν : Fin (p + 1) → ℝ), CHCond p ν → CHInt p m ν < ∞

def tailPt {p m : ℕ} (x : (Fin (p + 1) → ℂ) × (Fin p → ℂ) × (Fin m → ℂ) × ℝ) : Xp (p + 1) m :=
  (x.1, Fin.cons 0 x.2.1, x.2.2)

def TailInt (p m : ℕ) (α : ℝ) (ν : Fin (p + 1) → ℝ) : ℝ≥0∞ :=
  ∫⁻ x : (Fin (p + 1) → ℂ) × (Fin p → ℂ) × (Fin m → ℂ) × ℝ,
    ENNReal.ofReal (Lsq (tailPt x) 1 ^ ((-2 + α) / 2)) * ENNReal.ofReal (de (tailPt x) 1 ^ (-α)) *
      ∏ i : Fin (p + 1), ENNReal.ofReal (de (tailPt x) i.succ ^ (-(s0N (p + 1) m i.succ + ν i)))

def TailFin : Prop :=
  ∀ (p m : ℕ) (α : ℝ) (ν : Fin (p + 1) → ℝ), CHCond p (Function.update ν 0 (α + ν 0)) →
    0 < α + 2 * ∑ i, ν i → TailInt p m α ν < ∞

def C1 : Prop :=
  ∀ (p m : ℕ) (x : Xp (p + 1) m),
    de x 0 ^ 2 = Lsq x 1 * ‖x.2.1 0 - x.1 0 * bco x 1 / (Lsq x 1 : ℂ)‖ ^ 2 + de x 1 ^ 2 / Lsq x 1

def SUB : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → ∃ C : ℝ, ∀ c : Fin 3 → ℂ,
    (∫⁻ t in Set.Icc (1 : ℝ) 2, ENNReal.ofReal ((1 + ‖c 0 + c 1 * t + c 2 * t ^ 2‖) ^ (-δ))) ≤
      ENNReal.ofReal (C * (1 + ‖c‖) ^ (-δ / 2))

def KER : Prop :=
  ∀ e γ : ℝ, 0 < e → e < γ → γ < 2 → ∃ C : ℝ, ∀ (c : ℂ) (D : ℝ), 0 < D →
    (∫⁻ x : ℂ, ENNReal.ofReal ((‖x - c‖ ^ 2 + D ^ 2) ^ (-1 + e / 2)) * ENNReal.ofReal (‖x‖ ^ (-γ))) ≤
      ENNReal.ofReal (C * (‖c‖ ^ 2 + D ^ 2) ^ (-(γ - e) / 2))

def slowly {n : ℕ} (t A b : Fin n → ℝ) (β : ℝ) : ℝ≥0∞ :=
  ∏ i, ENNReal.ofReal ((A i ^ 2 + (β - b i) ^ 2) ^ (-t i / 2))

def SLOW : Prop :=
  ∀ (n : ℕ) (T κ : ℝ), 0 < κ → κ < 1 → ∃ C : ℝ, ∀ (t A b : Fin n → ℝ) (R : ℝ), 0 < R → (∀ i, 0 ≤ t i) →
    ∑ i, t i ≤ T → (∀ i, R ≤ A i) →
      (∫⁻ β : ℝ, slowly t A b β * ENNReal.ofReal (|β| ^ (-κ))) ≤ ENNReal.ofReal (C * R ^ (-κ)) * ∫⁻ β : ℝ, slowly t A b β

def linF {p m : ℕ} (η η' : Fin p → ℂ) (ζ : Fin m → ℂ) (x : Xp p m) : ℂ :=
  ∑ j, (x.1 j * η j + x.2.1 j * η' j) + ∑ i, x.2.2.1 i * ζ i

def OSInt (p m : ℕ) (s : Fin (p + 2) → ℝ) (δ : ℝ) (η η' : Fin (p + 1) → ℂ) (ζ : Fin m → ℂ) (c₀ : ℝ) : ℝ≥0∞ :=
  ∫⁻ x : Xp (p + 1) m, (∏ l, ENNReal.ofReal (de x l ^ (-s l))) *
    ENNReal.ofReal ((1 + |2 * (linF η η' ζ x).im + c₀|) ^ (-δ))

def OS : Prop :=
  ∀ (p m : ℕ) (δ γ : ℝ) (e : Fin (p + 2) → ℝ), 0 < δ → δ ≤ 1 / 2 → 0 < γ → γ ≤ δ / 8 → (∀ l, 0 < e l) →
    e 0 + 2 * ∑ i : Fin (p + 1), e i.succ < γ / 2 →
    ∃ C : ℝ, ∀ (η η' : Fin (p + 1) → ℂ) (ζ : Fin m → ℂ) (c₀ : ℝ), η' 0 ≠ 0 →
      OSInt p m (fun l => s0N (p + 1) m l - e l) δ η η' ζ c₀ ≤
        ENNReal.ofReal (C * ‖η' 0‖ ^ (-γ) * (1 + |c₀|) ^ (-δ / 4))

end ReciprocityTheory.ChartRestriction.DS.Xi
end
end

