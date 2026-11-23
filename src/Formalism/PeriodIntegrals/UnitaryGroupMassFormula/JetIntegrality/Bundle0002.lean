module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.Bundle0001
public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.CoeffSubstOfDegreeEqOne

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.ChainSt
section
noncomputable section

namespace PI.JetsPhW.W

open PI.JetsPhW

theorem pderiv_subst_self : PdSelf := fun _ _ _ i g => Ch.pderiv_subst_X_self i g

theorem pderiv_subst_ne : PdNe := fun _ _ _ _ _ g h => Ch.pderiv_subst_X_ne h g

theorem derivative_chain_rule : DChain := by
  intro p _ σ i l v g s c hv hs hpd
  unfold Dv
  rw [Ch.pderiv_subst i hs, hpd]
  linear_combination (MvPowerSeries.C c * PowerSeries.subst s (dX g)) * Ch.subst_v_mul hv i

theorem derivative_self : DSelf := by
  intro p _ σ i v g
  unfold Dv
  rw [Ch.pderiv_subst_X_self, ← PowerSeries.subst_mul
    (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)) v (dX g)]

theorem evaluation_at_zero : Ev0 := by
  intro p _ σ s g hs
  have hsub : PowerSeries.HasSubst s := PowerSeries.HasSubst.of_constantCoeff_zero hs
  have h2 : MvPowerSeries.constantCoeff
      (PowerSeries.subst s (g - PowerSeries.C (PowerSeries.constantCoeff g))) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hs _ (by simp)
  have h4 : PowerSeries.subst s g = PowerSeries.subst s (g - PowerSeries.C (PowerSeries.constantCoeff g)) +
      MvPowerSeries.C (PowerSeries.constantCoeff g) := by
    rw [← PowerSeries.subst_C (a := s) (PowerSeries.constantCoeff g), ← PowerSeries.subst_add hsub,
      sub_add_cancel]
  rw [h4, map_add (f := _), h2, zero_add, MvPowerSeries.constantCoeff_C]

theorem jet_derivative_integrality : JetD := by
  intro p _ ex ph n
  have h : (dX (A := ℂ_[p])) = ⇑(PowerSeries.derivative (R := ℂ_[p])) := funext Ch.dX_eq
  rw [h, PowerSeries.constantCoeff_iterate_derivative]
  rfl

theorem intMv_subst_X {p : ℕ} [Fact p.Prime] {σ : Type*} {v : PowerSeries ℂ_[p]} (hv : IntP v) (i : σ) :
    IntegralMv (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) v) := by
  classical
  intro e
  rw [PowerSeries.coeff_subst_single]
  split_ifs
  · exact hv _
  · show ‖(0 : ℂ_[p])‖ ≤ 1
    simp

theorem derivative_integral : Dint := fun _ _ _ i _ _ hv hf => intMv_mul (intMv_subst_X hv i) (intMv_pderiv i hf)

theorem log_derivative_integral_jet_integrality : LogDer := fun _ _ _ i _ _ hv hf hE => L0 i hf hE (intMv_subst_X hv i)

end PI.JetsPhW.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.FirstJetIntegralGeneralHolds
section
noncomputable section

namespace PI.JetsPhW.Low

open PI.JetsPhW

theorem logOk_low {p : ℕ} [Fact p.Prime] {l ex : PowerSeries ℂ_[p]} (h : LogOk l ex) :
    PowerSeries.constantCoeff l = 0 ∧
      PowerSeries.coeff 1 l * PowerSeries.coeff 1 ex = 1 ∧ ‖PowerSeries.coeff 1 ex‖ ≤ 1 := by
  obtain ⟨hex, hsub, v, hvint, hv⟩ := h
  have hl0 : PowerSeries.constantCoeff l = 0 := by
    have hc := congrArg MvPowerSeries.constantCoeff hsub
    rw [const_subst hex] at hc
    rw [hc]
    exact PowerSeries.constantCoeff_X
  have hl1 : PowerSeries.coeff 1 l * PowerSeries.coeff 1 ex = 1 := by
    have hc := congrArg (PowerSeries.coeff 1) hsub
    rw [pcoeff1_subst hex l, PowerSeries.coeff_one_X] at hc
    exact hc
  have hv0 : PowerSeries.coeff 0 v * PowerSeries.coeff 1 l = 1 := by
    have hc := congrArg (PowerSeries.coeff 0) hv
    simpa [PowerSeries.coeff_mul, dX] using hc
  have hev : PowerSeries.coeff 1 ex = PowerSeries.coeff 0 v := by
    linear_combination PowerSeries.coeff 0 v * hl1 - PowerSeries.coeff 1 ex * hv0
  refine ⟨hl0, hl1, ?_⟩
  rw [hev]
  exact hvint 0

theorem firstJetIntegralGeneral_holds : OneG := by
  intro p _ l ex ph h hp hs
  obtain ⟨_, _, h2⟩ := logOk_low h
  have h1 := (logOk_low h).2.1
  have h0 := (logOk_low h).1
  have hex := h.1
  have hde : Finsupp.degree (Finsupp.single () 1 : Unit →₀ ℕ) = 1 := by simp
  have hX0 : MvPowerSeries.constantCoeff (Xv () : MvPowerSeries Unit ℂ_[p]) = 0 := by simp [Xv]
  have hXe : MvPowerSeries.coeff (Finsupp.single () 1) (Xv () : MvPowerSeries Unit ℂ_[p]) = 1 := by
    simp [Xv, MvPowerSeries.coeff_X]
  have hL0 : MvPowerSeries.constantCoeff (PowerSeries.subst (Xv () : MvPowerSeries Unit ℂ_[p]) l) = 0 := by
    rw [const_subst hX0]
    exact h0
  have hLe : MvPowerSeries.coeff (Finsupp.single () 1) (PowerSeries.subst (Xv () : MvPowerSeries Unit ℂ_[p]) l) =
      PowerSeries.coeff 1 l := by
    rw [coeff_subst_of_degree_eq_one hX0 l hde, hXe, mul_one]
  have hB0 : MvPowerSeries.constantCoeff
      (MvPowerSeries.C (-1 : ℂ_[p]) * PowerSeries.subst (Xv () : MvPowerSeries Unit ℂ_[p]) l) = 0 := by
    rw [map_mul, hL0, mul_zero]
  have hBe : MvPowerSeries.coeff (Finsupp.single () 1)
      (MvPowerSeries.C (-1 : ℂ_[p]) * PowerSeries.subst (Xv () : MvPowerSeries Unit ℂ_[p]) l) = -PowerSeries.coeff 1 l := by
    rw [MvPowerSeries.coeff_C_mul, hLe, neg_one_mul]
  have hA0 : MvPowerSeries.constantCoeff (mulBy l ex (-1) (Xv ()) : MvPowerSeries Unit ℂ_[p]) = 0 := by
    rw [mulBy, const_subst hB0]
    exact hex
  have hAe : MvPowerSeries.coeff (Finsupp.single () 1)
      (mulBy l ex (-1) (Xv ()) : MvPowerSeries Unit ℂ_[p]) = -1 := by
    rw [mulBy, coeff_subst_of_degree_eq_one hB0 ex hde, hBe]
    linear_combination (-1 : ℂ_[p]) * h1
  have hf : MvPowerSeries.coeff (Finsupp.single () 1)
      (phAt ph (mulBy l ex (-1) (Xv ())) : MvPowerSeries Unit ℂ_[p]) = -PowerSeries.coeff 1 ph := by
    rw [phAt, coeff_subst_of_degree_eq_one hA0 ph hde, hAe, mul_neg_one]
  have hg : MvPowerSeries.coeff (Finsupp.single () 1) (phAt ph (Xv ()) : MvPowerSeries Unit ℂ_[p]) =
      PowerSeries.coeff 1 ph := by
    rw [phAt, coeff_subst_of_degree_eq_one hX0 ph hde, hXe, mul_one]
  have hint := hs.2 (Finsupp.single () 1)
  unfold IsIntP at hint
  rw [coeff_truncatedExp_of_degree_eq_one _ hde, map_sub, hf, hg] at hint
  have hc : ‖PowerSeries.coeff 1 ph‖ ≤ 1 := by
    have h2c : -PowerSeries.coeff 1 ph - PowerSeries.coeff 1 ph = -(2 * PowerSeries.coeff 1 ph) := by
      ring
    rw [h2c, norm_neg, norm_mul, norm_two hp, one_mul] at hint
    exact hint
  show ‖((Nat.factorial 1 : ℕ) : ℂ_[p]) * PowerSeries.coeff 1 (PowerSeries.subst ex ph : PowerSeries ℂ_[p])‖ ≤ 1
  rw [pcoeff1_subst hex ph, Nat.factorial_one, Nat.cast_one, one_mul, norm_mul]
  exact mul_le_one₀ hc (norm_nonneg _) h2

end PI.JetsPhW.Low
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.GlueHoldsVar
section
noncomputable section

namespace PI.JetsPhW.W

open PI.JetsPhW

theorem glue_holds_var : Glue := by
  intro hI hH hO hT
  refine ⟨?_, ?_, ?_⟩
  · intro p _ W wq ex ph h1 h2 h3 h4 h6 hW hex hl hc i hi1 hi2
    exact hH p (PI.JetsPhW.flog W wq) ex ph ⟨hex, hl, hI p W wq h1 h2 h3 h4 h6 hW⟩ hc i hi1 hi2
  · intro p _ W wq ex ph h1 h2 h3 h4 h6 hW hex hl hp hc
    exact hO p (PI.JetsPhW.flog W wq) ex ph ⟨hex, hl, hI p W wq h1 h2 h3 h4 h6 hW⟩ hp hc
  · intro p _ W wq ex ph a b h1 h2 h3 h4 h6 hW hex hl hc
    exact hT p (PI.JetsPhW.flog W wq) ex ph a b ⟨hex, hl, hI p W wq h1 h2 h3 h4 h6 hW⟩ hc

end PI.JetsPhW.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.PolarizationDifferenceFormulaHolds
section
noncomputable section

namespace PI.JetsPhW.W

open PI.JetsPhW

namespace R

variable {K : Type*} [CommRing K]

theorem cc_l {l ex : PowerSeries K} (hex : PowerSeries.constantCoeff ex = 0)
    (hl : PowerSeries.subst ex l = PowerSeries.X) : PowerSeries.constantCoeff l = 0 := by
  have h1 := PowerSeries.constantCoeff_subst (R := K) (PowerSeries.HasSubst.of_constantCoeff_zero' hex) l
  rw [hl] at h1
  have hex' : MvPowerSeries.constantCoeff ex = 0 := hex
  rw [finsum_eq_single _ 0 (fun d hd => by rw [map_pow, hex', zero_pow hd, smul_zero])] at h1
  simp only [pow_zero, map_one, smul_eq_mul, mul_one] at h1
  have h2 : PowerSeries.coeff 0 l = 0 := by
    rw [← h1]
    exact PowerSeries.constantCoeff_X
  simpa using h2

theorem l_ex {l ex : PowerSeries K} (hex : PowerSeries.constantCoeff ex = 0)
    (hl : PowerSeries.subst ex l = PowerSeries.X) {τ : Type*} {x : MvPowerSeries τ K}
    (hx : MvPowerSeries.constantCoeff x = 0) :
    PowerSeries.subst (PowerSeries.subst x ex) l = x := by
  have ha : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero' hex
  have hb : PowerSeries.HasSubst x := PowerSeries.HasSubst.of_constantCoeff_zero hx
  rw [← PowerSeries.subst_comp_subst_apply ha hb, hl, PowerSeries.subst_X hb]

theorem ph_ex {ex ph : PowerSeries K} (hex : PowerSeries.constantCoeff ex = 0) {τ : Type*}
    {s : MvPowerSeries τ K} (hs : MvPowerSeries.constantCoeff s = 0) :
    PowerSeries.subst (PowerSeries.subst s ex) ph =
      PowerSeries.subst s (PowerSeries.subst ex ph : PowerSeries K) := (PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hex)
    (PowerSeries.HasSubst.of_constantCoeff_zero hs) ph).symm

theorem cc_sum {l : PowerSeries K} (hl0 : PowerSeries.constantCoeff l = 0) {τ : Type*}
    {a b : MvPowerSeries τ K} (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a l + PowerSeries.subst b l) = 0 := by
  rw [map_add (f := _), PowerSeries.constantCoeff_subst_eq_zero ha l hl0,
    PowerSeries.constantCoeff_subst_eq_zero hb l hl0, add_zero]

end R

section
variable {p : ℕ} [Fact p.Prime] {σ : Type*} {l ex ph : PowerSeries ℂ_[p]}

theorem phAt_add (hex : PowerSeries.constantCoeff ex = 0) (hl : PowerSeries.subst ex l = PowerSeries.X)
    {a b : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) :
    phAt ph (add l ex a b) = PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst b l) (psi ex ph) := by
  unfold PI.JetsPhW.phAt PI.JetsPhW.add psi
  exact PI.JetsPhW.W.R.ph_ex hex
    (PI.JetsPhW.W.R.cc_sum (PI.JetsPhW.W.R.cc_l hex hl) ha hb)

theorem l_add (hex : PowerSeries.constantCoeff ex = 0) (hl : PowerSeries.subst ex l = PowerSeries.X)
    {a b : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) :
    PowerSeries.subst (add l ex a b) l = PowerSeries.subst a l + PowerSeries.subst b l := by
  unfold PI.JetsPhW.add
  exact PI.JetsPhW.W.R.l_ex hex hl
    (PI.JetsPhW.W.R.cc_sum (PI.JetsPhW.W.R.cc_l hex hl) ha hb)

theorem cc_add (hex : PowerSeries.constantCoeff ex = 0) (hl : PowerSeries.subst ex l = PowerSeries.X)
    {a b : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    (hb : MvPowerSeries.constantCoeff b = 0) : MvPowerSeries.constantCoeff (add l ex a b) = 0 := by
  unfold PI.JetsPhW.add
  exact PowerSeries.constantCoeff_subst_eq_zero
    (PI.JetsPhW.W.R.cc_sum (PI.JetsPhW.W.R.cc_l hex hl) ha hb) ex hex

end

theorem cubeDefectFormula_holds : Rw3 := by
  intro p _ l ex ph h
  obtain ⟨hex, hl, -⟩ := h
  have h0 : MvPowerSeries.constantCoeff (PI.JetsPhW.Xv 0 : MvPowerSeries (Fin 3) ℂ_[p]) = 0 :=
    MvPowerSeries.constantCoeff_X _
  have h1 : MvPowerSeries.constantCoeff (PI.JetsPhW.Xv 1 : MvPowerSeries (Fin 3) ℂ_[p]) = 0 :=
    MvPowerSeries.constantCoeff_X _
  have h2 : MvPowerSeries.constantCoeff (PI.JetsPhW.Xv 2 : MvPowerSeries (Fin 3) ℂ_[p]) = 0 :=
    MvPowerSeries.constantCoeff_X _
  unfold PI.JetsPhW.cubeE
  rw [phAt_add hex hl (cc_add hex hl h0 h1) h2,
    l_add hex hl h0 h1, phAt_add hex hl h0 h1,
    phAt_add hex hl h1 h2, phAt_add hex hl h2 h0]

end PI.JetsPhW.W
end
end

