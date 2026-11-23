module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupPoints.ConstantCoeffPsubst

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupPoints.AddGenThm
section
noncomputable section

namespace PI.FglPtW.Wk

open PI.AddIntG.Wk

theorem addGen_thm : PI.FglPtW.AddGen := by
  intro K _ S l ex hex0 hinv hF σ a b ha hb
  have hcc : ∀ {τ : Type} (f : PowerSeries K) (c : MvPowerSeries τ K),
      MvPowerSeries.constantCoeff c = 0 →
      MvPowerSeries.constantCoeff (PowerSeries.subst c f) = PowerSeries.constantCoeff f := by
    intro τ f c hc
    rw [PowerSeries.constantCoeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hc)]
    rw [finsum_eq_single _ 0]
    · simp
    · intro d hd
      rw [map_pow, hc, zero_pow hd, smul_zero]
  have hl0 : PowerSeries.constantCoeff l = 0 := by
    have h := hcc l ex hex0
    rw [hinv] at h
    rw [← h]
    exact PowerSeries.constantCoeff_X
  have hP0 : ∀ s, MvPowerSeries.constantCoeff ((![a, b] : Fin 2 → MvPowerSeries σ K) s) = 0 := by
    intro s
    fin_cases s <;> simp [ha.2, hb.2]
  have hP : MvPowerSeries.HasSubst (![a, b] : Fin 2 → MvPowerSeries σ K) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hP0
  have hmix : ∀ (c : MvPowerSeries (Fin 2) K), MvPowerSeries.constantCoeff c = 0 →
      ∀ f : PowerSeries K, MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries σ K) (PowerSeries.subst c f) =
        PowerSeries.subst (MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries σ K) c) f := by
    intro c hc f
    exact MvPowerSeries.subst_comp_subst_apply
      (PowerSeries.HasSubst.const (PowerSeries.HasSubst.of_constantCoeff_zero hc)) hP f
  have hX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 :=
    MvPowerSeries.constantCoeff_X 0
  have hX1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 :=
    MvPowerSeries.constantCoeff_X 1
  have hG0 : MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) l +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) l) = 0 := by
    rw [map_add (f := _), hcc l _ hX0, hcc l _ hX1, hl0, add_zero]
  have hG : MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries σ K)
      (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) l +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) l) =
      PowerSeries.subst a l + PowerSeries.subst b l := by
    rw [MvPowerSeries.subst_add hP, hmix _ hX0, hmix _ hX1, MvPowerSeries.subst_X hP,
      MvPowerSeries.subst_X hP]
    rfl
  have heq : PowerSeries.subst (PowerSeries.subst a l + PowerSeries.subst b l) ex =
      MvPowerSeries.subst (![a, b] : Fin 2 → MvPowerSeries σ K) (PowerSeries.subst
        (PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) l +
          PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) l) ex) := by
    rw [hmix _ hG0, hG]
  refine ⟨?_, ?_⟩
  · rw [heq, serOver_iff]
    refine mvsubst_mem_SerS S hP0 (fun i => ?_) ((serOver_iff S _).mp hF)
    fin_cases i <;> simp [(serOver_iff S a).mp ha.1, (serOver_iff S b).mp hb.1]
  · rw [hcc ex _ (by rw [map_add (f := _), hcc l a ha.2, hcc l b hb.2, hl0, add_zero])]
    exact hex0

end PI.FglPtW.Wk

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalGroupPoints.MulGenThm
section
noncomputable section

namespace PI.FglPtW.Wk

open PI.AddIntG.Wk

theorem mulGen_thm : PI.FglPtW.MulGen := by
  intro K _ S l ex hex hl c hG σ a ha
  obtain ⟨haS, ha0⟩ := ha
  have hex' : MvPowerSeries.constantCoeff ex = 0 := hex
  have hsub : PowerSeries.HasSubst ex := PowerSeries.HasSubst.of_constantCoeff_zero hex'

  have hl0 : PowerSeries.constantCoeff l = 0 := by
    have h1 := congrArg MvPowerSeries.constantCoeff hl
    rw [PowerSeries.constantCoeff_subst hsub,
      finsum_eq_single _ 0 (fun d hd => by rw [map_pow, hex', zero_pow hd, smul_zero])] at h1
    simpa using h1.trans (PowerSeries.constantCoeff_X (R := K))
  have hX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X () : MvPowerSeries Unit K) = 0 := by simp
  have hXs : PowerSeries.HasSubst (MvPowerSeries.X () : MvPowerSeries Unit K) :=
    PowerSeries.HasSubst.of_constantCoeff_zero hX0
  have has : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha0
  have hA0 : MvPowerSeries.constantCoeff (MvPowerSeries.C c *
      PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit K) l) = 0 := by
    rw [map_mul, PowerSeries.constantCoeff_subst_eq_zero hX0 l hl0, mul_zero]
  have hAs := PowerSeries.HasSubst.of_constantCoeff_zero hA0

  have hinner : PowerSeries.subst a (MvPowerSeries.C c *
      PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit K) l) =
      MvPowerSeries.C c * PowerSeries.subst a l := by
    rw [← PowerSeries.coe_substAlgHom has, map_mul, PowerSeries.coe_substAlgHom,
      PowerSeries.subst_comp_subst_apply hXs has]
    congr 1
    · have h2 := (PowerSeries.substAlgHom has).commutes c
      rw [PowerSeries.coe_substAlgHom] at h2
      first
        | exact h2
        | simp
        | (simp only [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at h2
           exact h2)
    · congr 1
      exact PowerSeries.subst_X has
  have key : PowerSeries.subst (MvPowerSeries.C c * PowerSeries.subst a l) ex =
      PowerSeries.subst a (PowerSeries.subst (MvPowerSeries.C c *
        PowerSeries.subst (MvPowerSeries.X () : MvPowerSeries Unit K) l) ex) := by
    rw [PowerSeries.subst_comp_subst_apply hAs has, hinner]
  rw [key]
  refine ⟨?_, ?_⟩
  · rw [serOver_iff]
    exact subst_mem_SerS S ha0 ((serOver_iff S a).mp haS) ((serOver_iff S _).mp hG)
  · exact PowerSeries.constantCoeff_subst_eq_zero ha0 _
      (PowerSeries.constantCoeff_subst_eq_zero hA0 ex hex)

end PI.FglPtW.Wk

end
end

