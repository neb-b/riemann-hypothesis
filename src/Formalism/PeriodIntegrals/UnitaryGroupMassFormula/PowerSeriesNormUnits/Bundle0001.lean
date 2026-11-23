module

public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0005

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.ConstantCoeffFormalSMul
section
noncomputable section

open Classical

namespace PI.PhNormUnits.UnitaryGroupMassFormula

open PI.PhNormUnits

variable {p : ℕ} [Fact p.Prime]

section One

variable {l ex : PowerSeries ℂ_[p]}

theorem l_const (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.constantCoeff l = 0 := by
  have h1 := congrArg (MvPowerSeries.constantCoeff (σ := Unit) (R := ℂ_[p])) hinv
  rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hex0)] at h1
  rw [finsum_eq_single _ 0] at h1
  · have h2 : PowerSeries.constantCoeff l =
        MvPowerSeries.constantCoeff (PowerSeries.X : PowerSeries ℂ_[p]) := by
      simpa using h1
    exact h2.trans PowerSeries.constantCoeff_X
  · intro d hd
    rw [map_pow]
    change PowerSeries.coeff d l • (PowerSeries.constantCoeff ex) ^ d = 0
    rw [hex0, zero_pow hd, smul_zero]

theorem coeff_one_l_ne (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.coeff 1 l ≠ 0 := by
  intro h1
  have hl0 := l_const hex0 hinv
  have hX2 : (PowerSeries.X : PowerSeries ℂ_[p]) ^ 2 ∣ l := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    interval_cases m
    · simpa using hl0
    · exact h1
  obtain ⟨q, hq⟩ := hX2
  obtain ⟨e', he'⟩ := PowerSeries.X_dvd_iff.mpr hex0
  have hs : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex0
  have key : PowerSeries.subst ex l = (PowerSeries.X : PowerSeries ℂ_[p]) ^ 2 *
      (e' ^ 2 * PowerSeries.subst ex q) := by
    rw [hq, PowerSeries.subst_mul hs, PowerSeries.subst_pow hs, PowerSeries.subst_X hs, he']
    ring
  rw [hinv] at key
  have h2 : (PowerSeries.X : PowerSeries ℂ_[p]) ^ 2 ∣ PowerSeries.X := ⟨_, key⟩
  rw [PowerSeries.X_pow_dvd_iff] at h2
  simpa using h2 1 (by norm_num)

theorem ex_l (hex0 : PowerSeries.constantCoeff ex = 0)
    (hinv : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.subst l ex = PowerSeries.X := by
  have hl0 := l_const hex0 hinv
  have hu : IsUnit (PowerSeries.coeff 1 l) := isUnit_iff_ne_zero.mpr (coeff_one_l_ne hex0 hinv)
  set Q := PowerSeries.substInvOfIsUnit l hu
  have hQl : PowerSeries.subst l Q = PowerSeries.X := PowerSeries.subst_substInvOfIsUnit_left l hl0 hu
  have hexQ : ex = Q := by
    have hs : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex0
    have hsl : PowerSeries.HasSubst l := PowerSeries.HasSubst.of_constantCoeff_zero' hl0
    calc ex = PowerSeries.subst ex (PowerSeries.X : PowerSeries ℂ_[p]) := (PowerSeries.subst_X hs).symm
      _ = PowerSeries.subst ex (PowerSeries.subst l Q) := by rw [hQl]
      _ = PowerSeries.subst (PowerSeries.subst ex l) Q := PowerSeries.subst_comp_subst_apply hsl hs Q
      _ = PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[p]) Q := by rw [hinv]
      _ = Q := PowerSeries.X_subst Q
  rw [hexQ]; exact hQl

end One

section Law

variable {l ex : PowerSeries ℂ_[p]} (hex0 : PowerSeries.constantCoeff ex = 0)
  (hinv : PowerSeries.subst ex l = PowerSeries.X)
variable {τ : Type*}

include hex0 hinv

theorem L_E (b : MvPowerSeries τ ℂ_[p]) (hb : MvPowerSeries.constantCoeff b = 0) :
    PowerSeries.subst (PowerSeries.subst b ex) l = b := by
  have hs : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex0
  have hb' : PowerSeries.HasSubst b := PowerSeries.HasSubst.of_constantCoeff_zero hb
  rw [← PowerSeries.subst_comp_subst_apply hs hb', hinv, PowerSeries.subst_X hb']

theorem E_L (a : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) :
    PowerSeries.subst (PowerSeries.subst a l) ex = a := by
  have hl0 := l_const hex0 hinv
  have hs : PowerSeries.HasSubst l := PowerSeries.HasSubst.of_constantCoeff_zero' hl0
  have ha' : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [← PowerSeries.subst_comp_subst_apply hs ha', ex_l hex0 hinv, PowerSeries.subst_X ha']

theorem constantCoeff_subst_log (a : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a l) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero ha l (l_const hex0 hinv)

omit hinv in
theorem z0_pt_zero_pt_one_L3 (b : MvPowerSeries τ ℂ_[p]) (hb : MvPowerSeries.constantCoeff b = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst b ex) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hb ex hex0

theorem constantCoeff_formalAdd (a b : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) : MvPowerSeries.constantCoeff (add l ex a b) = 0 := by
  unfold add
  apply z0_pt_zero_pt_one_L3 hex0
  rw [map_add (f := _), constantCoeff_subst_log hex0 hinv a ha, constantCoeff_subst_log hex0 hinv b hb, add_zero]

theorem constantCoeff_formalSMul (c : ℂ_[p]) (a : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (mulBy l ex c a) = 0 := by
  unfold mulBy
  apply z0_pt_zero_pt_one_L3 hex0
  rw [map_mul, constantCoeff_subst_log hex0 hinv a ha, mul_zero]

theorem L_add (a b : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) :
    PowerSeries.subst (add l ex a b) l = PowerSeries.subst a l + PowerSeries.subst b l := by
  unfold add
  apply L_E hex0 hinv
  rw [map_add (f := _), constantCoeff_subst_log hex0 hinv a ha, constantCoeff_subst_log hex0 hinv b hb, add_zero]

theorem L_mulBy (c : ℂ_[p]) (a : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) :
    PowerSeries.subst (mulBy l ex c a) l = MvPowerSeries.C c * PowerSeries.subst a l := by
  unfold mulBy
  apply L_E hex0 hinv
  rw [map_mul, constantCoeff_subst_log hex0 hinv a ha, mul_zero]

theorem mulBy_mulBy (c d : ℂ_[p]) (a : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) :
    mulBy l ex c (mulBy l ex d a) = mulBy l ex (c * d) a := by
  show PowerSeries.subst (MvPowerSeries.C c * PowerSeries.subst (mulBy l ex d a) l) ex = _
  rw [L_mulBy hex0 hinv d a ha, ← mul_assoc, ← map_mul]
  rfl

theorem add_mulBy (c d : ℂ_[p]) (a : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) :
    add l ex (mulBy l ex c a) (mulBy l ex d a) = mulBy l ex (c + d) a := by
  unfold add
  rw [L_mulBy hex0 hinv c a ha, L_mulBy hex0 hinv d a ha, ← add_mul, ← map_add (f := _)]
  rfl

theorem mulBy_add (c : ℂ_[p]) (a b : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) :
    mulBy l ex c (add l ex a b) = add l ex (mulBy l ex c a) (mulBy l ex c b) := by
  unfold mulBy
  rw [L_add hex0 hinv a b ha hb]
  unfold add
  rw [L_E hex0 hinv _ (by rw [map_mul, constantCoeff_subst_log hex0 hinv a ha, mul_zero]),
    L_E hex0 hinv _ (by rw [map_mul, constantCoeff_subst_log hex0 hinv b hb, mul_zero]), mul_add]

omit hex0 hinv in
theorem add_comm' (a b : MvPowerSeries τ ℂ_[p]) : add l ex a b = add l ex b a := by
  unfold add; rw [add_comm]

theorem mulBy_one (a : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) :
    mulBy l ex 1 a = a := by
  unfold mulBy; rw [map_one, one_mul]; exact E_L hex0 hinv a ha

omit hinv in
theorem mulBy_zero' (a : MvPowerSeries τ ℂ_[p]) : mulBy l ex 0 a = 0 := by
  unfold mulBy
  rw [map_zero, zero_mul, PowerSeries.subst_zero_of_constantCoeff_zero hex0]

theorem add_self (a : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) :
    add l ex a a = mulBy l ex 2 a := by
  rw [show (2 : ℂ_[p]) = 1 + 1 by norm_num, ← add_mulBy hex0 hinv 1 1 a ha, mulBy_one hex0 hinv a ha]

theorem mulBy_succ (k : ℕ) (a : MvPowerSeries τ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) :
    mulBy l ex ((k + 1 : ℕ) : ℂ_[p]) a = add l ex (mulBy l ex (k : ℂ_[p]) a) a := by
  rw [show ((k + 1 : ℕ) : ℂ_[p]) = (k : ℂ_[p]) + 1 by push_cast; ring, ← add_mulBy hex0 hinv _ _ a ha,
    mulBy_one hex0 hinv a ha]

omit hex0 hinv in
theorem be_comm (ph : PowerSeries ℂ_[p]) (a b : MvPowerSeries τ ℂ_[p]) :
    be l ex ph a b = be l ex ph b a := by
  unfold be; rw [add_comm' a b]; ring

end Law

section Subst

variable {σ τ : Type*} [Finite σ] {l ex : PowerSeries ℂ_[p]} (s : σ → MvPowerSeries τ ℂ_[p])
  (hs : ∀ i, MvPowerSeries.constantCoeff (s i) = 0)

include hs

theorem sb_psubst (a : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (f : PowerSeries ℂ_[p]) :
    MvPowerSeries.subst s (PowerSeries.subst a f) = PowerSeries.subst (MvPowerSeries.subst s a) f := by
  have hS : MvPowerSeries.HasSubst s := MvPowerSeries.hasSubst_of_constantCoeff_zero hs
  have ha' : MvPowerSeries.HasSubst (fun _ : Unit => a) :=
    (PowerSeries.HasSubst.of_constantCoeff_zero ha).const
  rw [PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply ha' hS]
  rfl

theorem sb_X (i : σ) : MvPowerSeries.subst s (Xv i : MvPowerSeries σ ℂ_[p]) = s i :=
  MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hs) i

theorem sb_add' (F G : MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries.subst s (F + G) = MvPowerSeries.subst s F + MvPowerSeries.subst s G :=
  MvPowerSeries.subst_add (MvPowerSeries.hasSubst_of_constantCoeff_zero hs) F G

theorem sb_sub' (F G : MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries.subst s (F - G) = MvPowerSeries.subst s F - MvPowerSeries.subst s G :=
  MvPowerSeries.subst_sub (MvPowerSeries.hasSubst_of_constantCoeff_zero hs) F G

theorem sb_C_mul (c : ℂ_[p]) (F : MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries.subst s (MvPowerSeries.C c * F) = MvPowerSeries.C c * MvPowerSeries.subst s F := by
  rw [MvPowerSeries.subst_mul (MvPowerSeries.hasSubst_of_constantCoeff_zero hs), MvPowerSeries.subst_C]

variable (hex0 : PowerSeries.constantCoeff ex = 0) (hinv : PowerSeries.subst ex l = PowerSeries.X)
include hex0 hinv

theorem sb_add (a b : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) :
    MvPowerSeries.subst s (add l ex a b) = add l ex (MvPowerSeries.subst s a) (MvPowerSeries.subst s b) := by
  unfold add
  rw [sb_psubst s hs _ (by rw [map_add (f := _), constantCoeff_subst_log hex0 hinv a ha, constantCoeff_subst_log hex0 hinv b hb, add_zero]),
    sb_add' s hs, sb_psubst s hs a ha, sb_psubst s hs b hb]

theorem sb_mulBy (c : ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.subst s (mulBy l ex c a) = mulBy l ex c (MvPowerSeries.subst s a) := by
  unfold mulBy
  rw [sb_psubst s hs _ (by rw [map_mul, constantCoeff_subst_log hex0 hinv a ha, mul_zero]), sb_C_mul s hs,
    sb_psubst s hs a ha]

omit hex0 hinv in
theorem sb_phAt (ph : PowerSeries ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.subst s (phAt ph a) = phAt ph (MvPowerSeries.subst s a) :=
  sb_psubst s hs a ha ph

theorem sb_be (ph : PowerSeries ℂ_[p]) (a b : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) :
    MvPowerSeries.subst s (be l ex ph a b) =
      be l ex ph (MvPowerSeries.subst s a) (MvPowerSeries.subst s b) := by
  unfold be
  rw [sb_sub' s hs, sb_sub' s hs, sb_phAt s hs ph _ (constantCoeff_formalAdd hex0 hinv a b ha hb), sb_add s hs hex0 hinv a b ha hb,
    sb_phAt s hs ph a ha, sb_phAt s hs ph b hb]

end Subst

end PI.PhNormUnits.UnitaryGroupMassFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.Development
section
noncomputable section

open Classical Filter Topology

namespace PI.PhNormUnits.UnitaryGroupMassFormula

open PI.PhNormUnits

def Hyp (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])) : Prop :=
  PowerSeries.constantCoeff ex = 0 ∧ PowerSeries.subst ex l = PowerSeries.X ∧ p ≠ 2 ∧
    ((2 : ℂ_[p]), (2 : ℂ_[p])) ∈ S ∧ (∀ α ∈ S, α.swap ∈ S) ∧ (∀ α ∈ S, ∀ β ∈ S, α + β ∈ S) ∧
    (∀ α ∈ S, ∀ β ∈ S, α * β ∈ S) ∧
    (∀ α ∈ S, IntegralMv (mulBy l ex α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p])) ∧
    IntegralMv (add l ex (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) ∧
    (∀ α ∈ S, ∃ n : ℤ_[p], α.1 + α.2 = zc n) ∧ (∀ α ∈ S, ∃ n : ℤ_[p], α.1 * α.2 = zc n) ∧
    (∀ α ∈ S, ∃ β ∈ S, ∃ γ ∈ S, ‖β.1‖ = 1 ∧ ‖β.2‖ = 1 ∧ ‖γ.1‖ = 1 ∧ ‖γ.2‖ = 1 ∧ α = β + γ) ∧
    Simeq (be l ex ph (add l ex (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (be l ex ph (Xv 0) (Xv 2) + be l ex ph (Xv 1) (Xv 2)) ∧
    (∀ α ∈ S, ‖α.1‖ = 1 → ‖α.2‖ = 1 → Simeq (phAt ph (mulBy l ex α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (α.1 * α.2) * phAt ph (Xv ())))

def NormRel (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (α : ℂ_[p] × ℂ_[p]) : Prop :=
  Simeq (phAt ph (mulBy l ex α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
    (MvPowerSeries.C (α.1 * α.2) * phAt ph (Xv ()))

def SwapRel (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (α : ℂ_[p] × ℂ_[p]) : Prop :=
  Simeq (be l ex ph (mulBy l ex α.1 (Xv 0)) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])
    (be l ex ph (Xv 0) (mulBy l ex α.2 (Xv 1)))

def TraceRel (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (δ : ℂ_[p] × ℂ_[p]) : Prop :=
  Simeq (be l ex ph (Xv ()) (mulBy l ex δ.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
    (MvPowerSeries.C (δ.1 + δ.2) * phAt ph (Xv ()))

def StepUnits : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])), Hyp p l ex ph S →
    ∀ α ∈ S, ‖α.1‖ = 1 → ‖α.2‖ = 1 → SwapRel p l ex ph α

def StepAll : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])), Hyp p l ex ph S →
    (∀ α ∈ S, ‖α.1‖ = 1 → ‖α.2‖ = 1 → SwapRel p l ex ph α) → ∀ α ∈ S, SwapRel p l ex ph α

def StepTrace : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])), Hyp p l ex ph S →
    (∀ α ∈ S, SwapRel p l ex ph α) → ∀ δ ∈ S, TraceRel p l ex ph δ

def StepSum : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])), Hyp p l ex ph S →
    (∀ α ∈ S, SwapRel p l ex ph α) → (∀ δ ∈ S, TraceRel p l ex ph δ) → ∀ α ∈ S, NormRel p l ex ph α

theorem target_of_hyp (h : ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]) (S : Set (ℂ_[p] × ℂ_[p])),
    Hyp p l ex ph S → ∀ α ∈ S, NormRel p l ex ph α) : Target := by
  intro p _ l ex ph S h0 hX h2 hS2 hswap hadd hmul hint_r hadd2 htr hnm hdec hdef hunit α hα
  exact h p l ex ph S
    ⟨h0, hX, h2, hS2, hswap, hadd, hmul, hint_r, hadd2, htr, hnm, hdec, hdef, hunit⟩ α hα

theorem target_of_steps (hU : StepUnits) (hA : StepAll) (hT : StepTrace) (hS : StepSum) : Target := by
  refine target_of_hyp ?_
  intro p _ l ex ph S hH
  have hsw : ∀ α ∈ S, SwapRel p l ex ph α := hA p l ex ph S hH (hU p l ex ph S hH)
  exact hS p l ex ph S hH hsw (hT p l ex ph S hH hsw)

def CalcEquiv : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f g h k : MvPowerSeries σ ℂ_[p]),
    Simeq f f ∧ (Simeq f g → Simeq g f) ∧ (Simeq f g → Simeq g h → Simeq f h) ∧
    (Simeq f g → Simeq h k → Simeq (f + h) (g + k)) ∧ (Simeq f g → Simeq (-f) (-g)) ∧
    (Simeq f g ↔ Simeq (f - g) 0)

def CalcSubst : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ τ : Type) [Finite σ] (a : σ → MvPowerSeries τ ℂ_[p]),
    (∀ i, MvPowerSeries.constantCoeff (a i) = 0) → (∀ i, IntegralMv (a i)) →
    (∀ f g : MvPowerSeries σ ℂ_[p], Simeq f g → Simeq (MvPowerSeries.subst a f) (MvPowerSeries.subst a g)) ∧
    (∀ f : MvPowerSeries σ ℂ_[p], IntegralMv f → IntegralMv (MvPowerSeries.subst a f))

def CalcClosed : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (F : ℕ → MvPowerSeries σ ℂ_[p]) (f : MvPowerSeries σ ℂ_[p]),
    (∀ e, Tendsto (fun k => MvPowerSeries.coeff e (F k)) atTop (𝓝 (MvPowerSeries.coeff e f))) →
    ((∀ k, Simeq (F k) 0) → Simeq f 0) ∧ ((∀ k, IntegralMv (F k)) → IntegralMv f)

def NatDense : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n : ℤ_[p]), ∃ u : ℕ → ℕ, Tendsto (fun k => ((u k : ℕ) : ℂ_[p])) atTop (𝓝 (zc n))

def CalcZpScale : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (f g : MvPowerSeries σ ℂ_[p]) (n : ℤ_[p]),
    Simeq f g → Simeq (MvPowerSeries.C (zc n) * f) (MvPowerSeries.C (zc n) * g)

end PI.PhNormUnits.UnitaryGroupMassFormula
end
end

