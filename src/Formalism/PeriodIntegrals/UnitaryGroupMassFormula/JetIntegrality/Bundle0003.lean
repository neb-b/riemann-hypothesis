module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.Bundle0002
public import Mathlib
public import Formalism.PeriodIntegrals.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.CoeffSubstOfDegreeEqOne
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.HighGOf
section
noncomputable section

namespace PI.JetsPhW.W

open PI.JetsPhW

section
variable {p : ℕ} [Fact p.Prime] {σ : Type*}

theorem Dv_add (v : PowerSeries ℂ_[p]) (i : σ) (f g : MvPowerSeries σ ℂ_[p]) :
    Dv v i (f + g) = Dv v i f + Dv v i g := by
  simp only [Dv, map_add (f := _), mul_add]

theorem Dv_sub (v : PowerSeries ℂ_[p]) (i : σ) (f g : MvPowerSeries σ ℂ_[p]) :
    Dv v i (f - g) = Dv v i f - Dv v i g := by
  simp only [Dv, map_sub, mul_sub]

end

private theorem pderiv_lX (hP : PdSelf) (hN : PdNe) {p : ℕ} [Fact p.Prime]
    {σ : Type} [DecidableEq σ] (l : PowerSeries ℂ_[p]) (i j : σ) :
    MvPowerSeries.pderiv (R := ℂ_[p]) i (lX l j : MvPowerSeries σ ℂ_[p]) =
      if j = i then PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) (PI.JetsPhW.dX l) else 0 := by
  split_ifs with h
  · subst h
    exact hP p σ j l
  · exact hN p σ i j l h

private theorem isIntP_constantCoeff_of_integralMv {p : ℕ} [Fact p.Prime] {σ : Type*} {F : MvPowerSeries σ ℂ_[p]}
    (h : PI.JetsPhW.IntegralMv F) : PI.JetsPhW.IsIntP (MvPowerSeries.constantCoeff F) := by
  have h0 := h 0
  rwa [MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at h0

theorem highG_of (hC : DChain) (hS : DSelf) (hN : PdNe) (hP : PdSelf) (hE : Ev0) (hJ : JetD)
    (hL : LogDer) (hI : Dint) : HighG := by
  intro p hp l ex ph hpair hD i hi1 hi2
  have hDdef := cubeDefectFormula_holds p l ex ph hpair
  obtain ⟨hex, hl, v, hvint, hv⟩ := hpair
  obtain ⟨hD0, hDe⟩ := hD
  simp only [sub_zero] at hD0 hDe
  have hl0 : PowerSeries.constantCoeff l = 0 := PI.JetsPhW.W.R.cc_l hex hl
  have hX : ∀ j : Fin 3, MvPowerSeries.constantCoeff (MvPowerSeries.X j : MvPowerSeries (Fin 3) ℂ_[p]) = 0 := by
    intro j; simp
  have hLc : ∀ j : Fin 3, MvPowerSeries.constantCoeff (lX l j : MvPowerSeries (Fin 3) ℂ_[p]) = 0 :=
    fun j => (hE p (Fin 3) _ l (hX j)).trans hl0
  have hpd : ∀ i j : Fin 3, MvPowerSeries.pderiv (R := ℂ_[p]) i (lX l j : MvPowerSeries (Fin 3) ℂ_[p]) =
      if j = i then PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX l) else 0 :=
    fun i j => pderiv_lX hP hN l i j
  have hd : ∀ (i : Fin 3) (S : MvPowerSeries (Fin 3) ℂ_[p]) (c : ℂ_[p]) (g : PowerSeries ℂ_[p]),
      MvPowerSeries.constantCoeff S = 0 →
      MvPowerSeries.pderiv (R := ℂ_[p]) i S =
        MvPowerSeries.C c * PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX l) →
      Dv v i (PowerSeries.subst S g) = MvPowerSeries.C c * PowerSeries.subst S (PI.JetsPhW.dX g) :=
    fun i S c g h1 h2 => hC p (Fin 3) i l v g S c hv h1 h2
  have hXne : ∀ (i j : Fin 3) (g : PowerSeries ℂ_[p]), j ≠ i →
      Dv v i (PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin 3) ℂ_[p]) g) = 0 := by
    intro i j g h
    simp only [Dv]
    rw [hN p (Fin 3) i j g h, mul_zero]
  have hq : ∀ j : Fin 3, (PI.JetsPhW.phAt ph (PI.JetsPhW.Xv j) : MvPowerSeries (Fin 3) ℂ_[p]) =
      PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin 3) ℂ_[p]) ph := fun j => rfl
  have c012 : MvPowerSeries.constantCoeff (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) = 0 := by
    simp only [map_add (f := _), hLc, add_zero]
  have c01 : MvPowerSeries.constantCoeff (lX l 0 + lX l 1 : MvPowerSeries (Fin 3) ℂ_[p]) = 0 := by
    simp only [map_add (f := _), hLc, add_zero]
  have c12 : MvPowerSeries.constantCoeff (lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) = 0 := by
    simp only [map_add (f := _), hLc, add_zero]
  have c20 : MvPowerSeries.constantCoeff (lX l 2 + lX l 0 : MvPowerSeries (Fin 3) ℂ_[p]) = 0 := by
    simp only [map_add (f := _), hLc, add_zero]
  have p0_012 : MvPowerSeries.pderiv (R := ℂ_[p]) 0 (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) =
      MvPowerSeries.C 1 * PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX l) := by
    simp only [map_add (f := _), hpd]; simp (config := { decide := true })
  have p0_01 : MvPowerSeries.pderiv (R := ℂ_[p]) 0 (lX l 0 + lX l 1 : MvPowerSeries (Fin 3) ℂ_[p]) =
      MvPowerSeries.C 1 * PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX l) := by
    simp only [map_add (f := _), hpd]; simp (config := { decide := true })
  have p0_12 : MvPowerSeries.pderiv (R := ℂ_[p]) 0 (lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) =
      MvPowerSeries.C 0 * PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX l) := by
    simp only [map_add (f := _), hpd]; simp (config := { decide := true })
  have p0_20 : MvPowerSeries.pderiv (R := ℂ_[p]) 0 (lX l 2 + lX l 0 : MvPowerSeries (Fin 3) ℂ_[p]) =
      MvPowerSeries.C 1 * PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX l) := by
    simp only [map_add (f := _), hpd]; simp (config := { decide := true })
  have p1_012 : MvPowerSeries.pderiv (R := ℂ_[p]) 1 (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) =
      MvPowerSeries.C 1 * PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX l) := by
    simp only [map_add (f := _), hpd]; simp (config := { decide := true })
  have p1_01 : MvPowerSeries.pderiv (R := ℂ_[p]) 1 (lX l 0 + lX l 1 : MvPowerSeries (Fin 3) ℂ_[p]) =
      MvPowerSeries.C 1 * PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX l) := by
    simp only [map_add (f := _), hpd]; simp (config := { decide := true })
  have p1_20 : MvPowerSeries.pderiv (R := ℂ_[p]) 1 (lX l 2 + lX l 0 : MvPowerSeries (Fin 3) ℂ_[p]) =
      MvPowerSeries.C 0 * PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX l) := by
    simp only [map_add (f := _), hpd]; simp (config := { decide := true })
  have p2_012 : MvPowerSeries.pderiv (R := ℂ_[p]) 2 (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) =
      MvPowerSeries.C 1 * PowerSeries.subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX l) := by
    simp only [map_add (f := _), hpd]; simp (config := { decide := true })
  have p2_01 : MvPowerSeries.pderiv (R := ℂ_[p]) 2 (lX l 0 + lX l 1 : MvPowerSeries (Fin 3) ℂ_[p]) =
      MvPowerSeries.C 0 * PowerSeries.subst (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX l) := by
    simp only [map_add (f := _), hpd]; simp (config := { decide := true })
  have e1 : Dv v 0 (PI.JetsPhW.cubeE l ex ph) =
      PowerSeries.subst (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX (psi ex ph)) -
        PowerSeries.subst (lX l 0 + lX l 1 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX (psi ex ph)) -
        PowerSeries.subst (lX l 2 + lX l 0 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX (psi ex ph)) +
        PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (v * PI.JetsPhW.dX ph) := by
    rw [hDdef]
    simp only [Dv_add, Dv_sub, hq]
    rw [hd 0 _ 1 _ c012 p0_012, hd 0 _ 1 _ c01 p0_01, hd 0 _ 0 _ c12 p0_12, hd 0 _ 1 _ c20 p0_20,
      hS p (Fin 3) 0 v ph, hXne 0 1 ph (by decide), hXne 0 2 ph (by decide)]
    simp only [map_one, map_zero, one_mul, zero_mul, sub_zero, add_zero]
  have e2 : Dv v 1
      (PowerSeries.subst (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX (psi ex ph)) -
        PowerSeries.subst (lX l 0 + lX l 1 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX (psi ex ph)) -
        PowerSeries.subst (lX l 2 + lX l 0 : MvPowerSeries (Fin 3) ℂ_[p]) (PI.JetsPhW.dX (psi ex ph)) +
        PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) ℂ_[p]) (v * PI.JetsPhW.dX ph)) =
      PowerSeries.subst (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p])
          (PI.JetsPhW.dX (PI.JetsPhW.dX (psi ex ph))) -
        PowerSeries.subst (lX l 0 + lX l 1 : MvPowerSeries (Fin 3) ℂ_[p])
          (PI.JetsPhW.dX (PI.JetsPhW.dX (psi ex ph))) := by
    simp only [Dv_add, Dv_sub]
    rw [hd 1 _ 1 _ c012 p1_012, hd 1 _ 1 _ c01 p1_01, hd 1 _ 0 _ c20 p1_20, hXne 1 0 _ (by decide)]
    simp only [map_one, map_zero, one_mul, zero_mul, sub_zero, add_zero]
  have e3 : Dv v 2
      (PowerSeries.subst (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p])
          (PI.JetsPhW.dX (PI.JetsPhW.dX (psi ex ph))) -
        PowerSeries.subst (lX l 0 + lX l 1 : MvPowerSeries (Fin 3) ℂ_[p])
          (PI.JetsPhW.dX (PI.JetsPhW.dX (psi ex ph)))) =
      PowerSeries.subst (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p])
          (PI.JetsPhW.dX (PI.JetsPhW.dX (PI.JetsPhW.dX (psi ex ph)))) := by
    rw [Dv_sub, hd 2 _ 1 _ c012 p2_012, hd 2 _ 0 _ c01 p2_01]
    simp only [map_one, map_zero, one_mul, zero_mul, sub_zero]
  have h1 : PI.JetsPhW.IntegralMv (Dv v 0 (PI.JetsPhW.cubeE l ex ph)) := hL p (Fin 3) 0 v _ hvint hD0 hDe
  rw [e1] at h1
  have h2 := hI p (Fin 3) 1 v _ hvint h1
  rw [e2] at h2
  have h3 := hI p (Fin 3) 2 v _ hvint h2
  rw [e3] at h3
  have hk : ∀ k : ℕ, PI.JetsPhW.IntegralMv (PowerSeries.subst (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p])
      ((PI.JetsPhW.dX (A := ℂ_[p]))^[k + 3] (psi ex ph))) := by
    intro k
    induction k with
    | zero => exact h3
    | succ k ih =>
      have h4 := hI p (Fin 3) 0 v _ hvint ih
      rw [hd 0 _ 1 _ c012 p0_012, map_one, one_mul] at h4
      rw [show k + 1 + 3 = (k + 3) + 1 by omega, Function.iterate_succ_apply']
      exact h4
  have hψ : PowerSeries.constantCoeff (psi ex ph) = PowerSeries.constantCoeff ph := hE p Unit ex ph hex
  rcases i with _ | _ | _ | k
  ·
    have hph : PowerSeries.constantCoeff ph = 0 := by
      have h0 := hD0
      rw [hDdef] at h0
      simp only [map_add (f := _), map_sub, hq] at h0
      rw [hE p (Fin 3) _ _ c012, hE p (Fin 3) _ _ c01, hE p (Fin 3) _ _ c12, hE p (Fin 3) _ _ c20,
        hE p (Fin 3) _ _ (hX 0), hE p (Fin 3) _ _ (hX 1), hE p (Fin 3) _ _ (hX 2), hψ] at h0
      linear_combination h0
    rw [hJ p ex ph]
    show PI.JetsPhW.IsIntP (PowerSeries.constantCoeff (psi ex ph))
    rw [hψ, hph]
    simp [PI.JetsPhW.IsIntP]
  · exact absurd rfl hi1
  · exact absurd rfl hi2
  · have hc := isIntP_constantCoeff_of_integralMv (hk k)
    rw [hE p (Fin 3) _ _ c012] at hc
    rw [hJ p ex ph]
    exact hc

end PI.JetsPhW.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.SecondJetIntegralGeneralHolds
section
noncomputable section

namespace PI.JetsPhW.Low

open PI.JetsPhW

private lemma coeff_mulBy_low_degree {p : ℕ} [Fact p.Prime] {l ex : PowerSeries ℂ_[p]} (hlog : LogOk l ex) (c : ℂ_[p])
    {A : MvPowerSeries (Fin 2) ℂ_[p]} (hA : MvPowerSeries.constantCoeff A = 0) :
    MvPowerSeries.constantCoeff (mulBy l ex c A) = 0 ∧
      MvPowerSeries.coeff E0 (mulBy l ex c A) = c * MvPowerSeries.coeff E0 A ∧
      MvPowerSeries.coeff E1 (mulBy l ex c A) = c * MvPowerSeries.coeff E1 A := by
  obtain ⟨hl0, hle, -⟩ := logOk_low hlog
  have hAl : MvPowerSeries.constantCoeff (PowerSeries.subst A l : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    rw [const_subst hA]; exact hl0
  have hI : MvPowerSeries.constantCoeff
      (MvPowerSeries.C c * PowerSeries.subst A l : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    rw [map_mul, hAl, mul_zero]
  have e : mulBy l ex c A = PowerSeries.subst (MvPowerSeries.C c * PowerSeries.subst A l) ex := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [e, const_subst hI]; exact hlog.1
  · rw [e, coeff_expX_subst hI, MvPowerSeries.coeff_C_mul, coeff_expX_subst hA]
    linear_combination (c * MvPowerSeries.coeff E0 A) * hle
  · rw [e, coeff_expY_subst hI, MvPowerSeries.coeff_C_mul, coeff_expY_subst hA]
    linear_combination (c * MvPowerSeries.coeff E1 A) * hle

private lemma coeff_be_low_degree {p : ℕ} [Fact p.Prime] {l ex : PowerSeries ℂ_[p]} (ph : PowerSeries ℂ_[p])
    (hlog : LogOk l ex) {A B : MvPowerSeries (Fin 2) ℂ_[p]} (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) (hA1 : MvPowerSeries.coeff E1 A = 0)
    (hB0 : MvPowerSeries.coeff E0 B = 0) :
    MvPowerSeries.coeff E0 (be l ex ph A B) = 0 ∧ MvPowerSeries.coeff E1 (be l ex ph A B) = 0 ∧
      MvPowerSeries.coeff bivariateExponentMonomial (be l ex ph A B) =
        2 * MvPowerSeries.coeff E0 A * MvPowerSeries.coeff E1 B *
          (PowerSeries.coeff 1 ph * PowerSeries.coeff 2 ex * PowerSeries.coeff 1 l ^ 2 +
            PowerSeries.coeff 2 ph) := by
  obtain ⟨hl0, hle, -⟩ := logOk_low hlog
  have hAl : MvPowerSeries.constantCoeff (PowerSeries.subst A l : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    rw [const_subst hA]; exact hl0
  have hBl : MvPowerSeries.constantCoeff (PowerSeries.subst B l : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    rw [const_subst hB]; exact hl0
  have hS : MvPowerSeries.constantCoeff
      (PowerSeries.subst A l + PowerSeries.subst B l : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    rw [map_add (f := _), hAl, hBl, add_zero]
  have ea : add l ex A B = PowerSeries.subst (PowerSeries.subst A l + PowerSeries.subst B l) ex := rfl
  have hadd : MvPowerSeries.constantCoeff (add l ex A B) = 0 := by
    rw [ea, const_subst hS]; exact hlog.1
  have eb : be l ex ph A B = PowerSeries.subst (add l ex A B) ph - PowerSeries.subst A ph -
      PowerSeries.subst B ph := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [eb, map_sub, map_sub, coeff_expX_subst hadd, coeff_expX_subst hA, coeff_expX_subst hB, ea, coeff_expX_subst hS, map_add (f := _),
      coeff_expX_subst hA, coeff_expX_subst hB, hB0]
    linear_combination (PowerSeries.coeff 1 ph * MvPowerSeries.coeff E0 A) * hle
  · rw [eb, map_sub, map_sub, coeff_expY_subst hadd, coeff_expY_subst hA, coeff_expY_subst hB, ea, coeff_expY_subst hS, map_add (f := _),
      coeff_expY_subst hA, coeff_expY_subst hB, hA1]
    linear_combination (PowerSeries.coeff 1 ph * MvPowerSeries.coeff E1 B) * hle
  · rw [eb, map_sub, map_sub, coeff_expXY_subst hadd, coeff_expXY_subst hA, coeff_expXY_subst hB,
      ea, coeff_expXY_subst hS, coeff_expX_subst hS, coeff_expY_subst hS, map_add, map_add, map_add, coeff_expXY_subst hA, coeff_expXY_subst hB,
      coeff_expX_subst hA, coeff_expX_subst hB, coeff_expY_subst hA, coeff_expY_subst hB, hA1, hB0]
    linear_combination (PowerSeries.coeff 1 ph * (MvPowerSeries.coeff bivariateExponentMonomial A + MvPowerSeries.coeff bivariateExponentMonomial B) +
      2 * MvPowerSeries.coeff E0 A * MvPowerSeries.coeff E1 B * PowerSeries.coeff 2 ph *
        (PowerSeries.coeff 1 ex * PowerSeries.coeff 1 l + 1)) * hle

theorem secondJetIntegralGeneral_holds : TwoG := by
  intro p _ l ex ph a b hlog hsim
  obtain ⟨hl0, hle, he1⟩ := logOk_low hlog
  have hex0 : PowerSeries.constantCoeff ex = 0 := hlog.1
  have cX : ∀ i : Fin 2, MvPowerSeries.constantCoeff (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := fun i => by
    simp [Xv]
  have x00 : MvPowerSeries.coeff E0 (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) = 1 := by
    simp [Xv, MvPowerSeries.coeff_X, E0, E1, Finsupp.single_eq_single_iff]
  have x01 : MvPowerSeries.coeff E1 (Xv 0 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    simp [Xv, MvPowerSeries.coeff_X, E0, E1, Finsupp.single_eq_single_iff]
  have x10 : MvPowerSeries.coeff E0 (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    simp [Xv, MvPowerSeries.coeff_X, E0, E1, Finsupp.single_eq_single_iff]
  have x11 : MvPowerSeries.coeff E1 (Xv 1 : MvPowerSeries (Fin 2) ℂ_[p]) = 1 := by
    simp [Xv, MvPowerSeries.coeff_X, E0, E1, Finsupp.single_eq_single_iff]
  obtain ⟨ma0, ma1, ma2⟩ := coeff_mulBy_low_degree hlog a (cX 0)
  obtain ⟨mb0, mb1, mb2⟩ := coeff_mulBy_low_degree hlog b (cX 1)
  obtain ⟨u0, u1, u2⟩ := coeff_be_low_degree ph hlog ma0 (cX 1) (by rw [ma2, x01, mul_zero]) x10
  obtain ⟨v0, v1, v2⟩ := coeff_be_low_degree ph hlog (cX 0) mb0 x01 (by rw [mb1, x10, mul_zero])
  set D := (be l ex ph (mulBy l ex a (Xv 0)) (Xv 1) - be l ex ph (Xv 0) (mulBy l ex b (Xv 1)) :
    MvPowerSeries (Fin 2) ℂ_[p]) with hD
  have hD0 : MvPowerSeries.constantCoeff D = 0 := hsim.1
  have d0 : MvPowerSeries.coeff E0 D = 0 := by rw [hD, map_sub, u0, v0, sub_zero]
  have d1 : MvPowerSeries.coeff E1 D = 0 := by rw [hD, map_sub, u1, v1, sub_zero]

  have hs : (bivariateExponentMonomial.sum fun _ k => k) = 2 := degree_expXY
  have hexp : MvPowerSeries.coeff bivariateExponentMonomial (expMv D) = MvPowerSeries.coeff bivariateExponentMonomial D := by
    change (∑ n ∈ Finset.range ((bivariateExponentMonomial.sum fun _ k => k) + 1),
      MvPowerSeries.coeff bivariateExponentMonomial (D ^ n) / (n.factorial : ℂ_[p])) = _
    rw [hs, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, pow_two,
      coeff_expXY_mul hD0 hD0, d0, d1]
    simp [MvPowerSeries.coeff_one, expXY_ne_zero]
  have hint : ‖MvPowerSeries.coeff bivariateExponentMonomial D‖ ≤ 1 := by
    rw [← hexp]; exact hsim.2 bivariateExponentMonomial
  have hjet : jet ex ph 2 = 2 * (PowerSeries.coeff 1 ph * PowerSeries.coeff 2 ex +
      PowerSeries.coeff 2 ph * PowerSeries.coeff 1 ex ^ 2) := by
    unfold jet
    rw [pcoeff2_subst hex0 ph]
    norm_num
  have hval : MvPowerSeries.coeff bivariateExponentMonomial D = (a - b) * jet ex ph 2 * PowerSeries.coeff 1 l ^ 2 := by
    rw [hD, map_sub, u2, v2, ma1, mb2, x00, x11, hjet]
    linear_combination (-2 * (a - b) * PowerSeries.coeff 2 ph *
      (PowerSeries.coeff 1 ex * PowerSeries.coeff 1 l + 1)) * hle

  have hl1 : 1 ≤ ‖PowerSeries.coeff 1 l‖ := by
    have h := congrArg norm hle
    rw [norm_mul, norm_one] at h
    by_contra hlt
    push_neg at hlt
    nlinarith [norm_nonneg (PowerSeries.coeff 1 ex), norm_nonneg (PowerSeries.coeff 1 l)]
  rw [hval, norm_mul, norm_pow] at hint
  unfold IsIntP
  have hxy := norm_nonneg ((a - b) * jet ex ph 2)
  have := mul_le_mul_of_nonneg_left (one_le_pow₀ (n := 2) hl1) hxy
  linarith

end PI.JetsPhW.Low
end
end

