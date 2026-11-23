module

public import Formalism.PeriodIntegrals.Bundle0003
public import Mathlib
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0063
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0035
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.CoeffSubstOfDegreeEqOne
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0037

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.CoeffPowEqZeroOfDegreeLt
section
noncomputable section

open PI.JetsPhW

namespace PI.JetsPhW.Ch

section Chain

variable {R : Type*} [CommRing R] {σ : Type*}

private theorem coeff_dX (f : PowerSeries R) (n : ℕ) :
    PowerSeries.coeff n (PI.JetsPhW.dX f) = ((n : R) + 1) * PowerSeries.coeff (n + 1) f := by
  simp only [PI.JetsPhW.dX, PowerSeries.coeff_mk]

theorem dX_eq (f : PowerSeries R) : dX f = PowerSeries.derivative (R := R) f := by
  ext n
  rw [PowerSeries.coeff_derivative, coeff_dX]
  ring

theorem degree_le_of_le {y e : σ →₀ ℕ} (h : y ≤ e) : y.degree ≤ e.degree := by
  obtain ⟨z, rfl⟩ := exists_add_of_le h
  rw [map_add (f := _)]
  exact Nat.le_add_right _ _

theorem coeff_pow_eq_zero_of_degree_lt {a : MvPowerSeries σ R} (ha : MvPowerSeries.constantCoeff a = 0)
    {e : σ →₀ ℕ} {d : ℕ} (h : e.degree < d) : MvPowerSeries.coeff e (a ^ d) = 0 := by
  apply MvPowerSeries.coeff_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast h) (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero d ha)

theorem coeff_subst_congr {a : MvPowerSeries σ R} (ha : MvPowerSeries.constantCoeff a = 0)
    {f g : PowerSeries R} {N : ℕ} (hfg : ∀ k < N, PowerSeries.coeff k f = PowerSeries.coeff k g)
    {e : σ →₀ ℕ} (he : e.degree < N) :
    MvPowerSeries.coeff e (PowerSeries.subst a f) = MvPowerSeries.coeff e (PowerSeries.subst a g) := by
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [PowerSeries.coeff_subst hs, PowerSeries.coeff_subst hs]
  refine finsum_congr fun k => ?_
  by_cases hk : k < N
  · rw [hfg k hk]
  · rw [coeff_pow_eq_zero_of_degree_lt ha (lt_of_lt_of_le he (not_lt.mp hk)), smul_zero, smul_zero]

theorem coeff_mul_congr (u : MvPowerSeries σ R) {f g : MvPowerSeries σ R} {e : σ →₀ ℕ}
    (hfg : ∀ y ≤ e, MvPowerSeries.coeff y f = MvPowerSeries.coeff y g) :
    MvPowerSeries.coeff e (u * f) = MvPowerSeries.coeff e (u * g) := by
  classical
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [hfg p.2 (by rw [← hp]; exact le_add_self)]

theorem pderiv_subst_coe (i : σ) {a : MvPowerSeries σ R} (ha : MvPowerSeries.constantCoeff a = 0)
    (q : Polynomial R) :
    MvPowerSeries.pderiv (R := R) i (PowerSeries.subst a (q : PowerSeries R)) =
      MvPowerSeries.pderiv (R := R) i a * PowerSeries.subst a (dX (q : PowerSeries R)) := by
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [dX_eq, PowerSeries.derivative_coe, PowerSeries.subst_coe hs,
    PowerSeries.subst_coe hs, Derivation.map_aeval, smul_eq_mul]
  ring

theorem pderiv_subst (i : σ) {a : MvPowerSeries σ R} (ha : MvPowerSeries.constantCoeff a = 0)
    (g : PowerSeries R) :
    MvPowerSeries.pderiv (R := R) i (PowerSeries.subst a g) =
      MvPowerSeries.pderiv (R := R) i a * PowerSeries.subst a (dX g) := by
  ext e
  have h1 : MvPowerSeries.coeff e (MvPowerSeries.pderiv (R := R) i (PowerSeries.subst a g)) =
      MvPowerSeries.coeff e (MvPowerSeries.pderiv (R := R) i
        (PowerSeries.subst a (PowerSeries.trunc (e.degree + 2) g : PowerSeries R))) := by
    rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv]
    congr 1
    refine coeff_subst_congr ha (N := e.degree + 2) (fun k hk => ?_) ?_
    · exact (PowerSeries.coeff_coe_trunc_of_lt hk).symm
    · rw [map_add (f := _), Finsupp.degree_single]
      omega
  have h2 : MvPowerSeries.coeff e (MvPowerSeries.pderiv (R := R) i a * PowerSeries.subst a (PI.JetsPhW.dX g)) =
      MvPowerSeries.coeff e (MvPowerSeries.pderiv (R := R) i a *
        PowerSeries.subst a (PI.JetsPhW.dX (PowerSeries.trunc (e.degree + 2) g : PowerSeries R))) := by
    refine coeff_mul_congr _ fun y hy => ?_
    refine coeff_subst_congr ha (N := e.degree + 1) (fun k hk => ?_) ?_
    · rw [coeff_dX, coeff_dX, PowerSeries.coeff_coe_trunc_of_lt (n := k + 1) (m := e.degree + 2) (by omega)]
    · exact Nat.lt_succ_of_le (degree_le_of_le hy)
  rw [h1, pderiv_subst_coe i ha, h2]

theorem pderiv_subst_X_self (i : σ) (g : PowerSeries R) :
    MvPowerSeries.pderiv (R := R) i (PowerSeries.subst (MvPowerSeries.X i) g) =
      PowerSeries.subst (MvPowerSeries.X i) (dX g) := by
  rw [pderiv_subst i (a := MvPowerSeries.X i) (MvPowerSeries.constantCoeff_X i) g,
    MvPowerSeries.pderiv_X_self, one_mul]

theorem pderiv_subst_X_ne {i j : σ} (h : j ≠ i) (g : PowerSeries R) :
    MvPowerSeries.pderiv (R := R) i (PowerSeries.subst (MvPowerSeries.X j) g) = 0 := by
  rw [pderiv_subst i (a := MvPowerSeries.X j) (MvPowerSeries.constantCoeff_X j) g,
    MvPowerSeries.pderiv_X_of_ne h, zero_mul]

theorem subst_one' (a : MvPowerSeries σ R) : PowerSeries.subst a (1 : PowerSeries R) = 1 := by
  simpa using PowerSeries.subst_C (a := a) (1 : R)

private theorem powerSeries_hasSubst_mvPowerSeries_X (i : σ) : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries σ R) :=
  PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)

theorem subst_v_mul {l v : PowerSeries R} (hv : v * dX l = 1) (i : σ) :
    PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ R) v *
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ R) (dX l) = 1 := by
  rw [← PowerSeries.subst_mul (powerSeries_hasSubst_mvPowerSeries_X i), hv, subst_one']

end Chain

end PI.JetsPhW.Ch
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.ExpLog
section
noncomputable section

open Classical

namespace PI.JetsPhW.W

open PI.JetsPhW MvPowerSeries

variable {p : ℕ} [Fact p.Prime] {σ : Type*}

theorem intMv_mul {F G : MvPowerSeries σ ℂ_[p]} (hF : IntegralMv F) (hG : IntegralMv G) :
    IntegralMv (F * G) :=
  _root_.UpperTheory.Reformulated.B.IntegralPolynomialSecond.intMv_mul hF hG

theorem intMv_pderiv {F : MvPowerSeries σ ℂ_[p]} (i : σ) (hF : IntegralMv F) :
    IntegralMv (pderiv (R := ℂ_[p]) i F) :=
  _root_.UpperTheory.Reformulated.B.Gwb7.intMv_pderiv i hF

theorem intMv_inv {F : MvPowerSeries σ ℂ_[p]} (hF : IntegralMv F) (h1 : constantCoeff F = 1) :
    ∃ G : MvPowerSeries σ ℂ_[p], IntegralMv G ∧ F * G = 1 :=
  _root_.UpperTheory.Reformulated.B.UnitBallLemmas.intMv_inv hF h1

theorem coeff_pow_eq_zero {f : MvPowerSeries σ ℂ_[p]} (hf : constantCoeff f = 0) {n : ℕ}
    {α : σ →₀ ℕ} (h : Finsupp.degree α < n) : coeff α (f ^ n) = 0 := by
  apply coeff_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast h) (le_order_pow_of_constantCoeff_eq_zero n hf)

def expT (f : MvPowerSeries σ ℂ_[p]) (N : ℕ) : MvPowerSeries σ ℂ_[p] :=
  ∑ n ∈ Finset.range N, ((n.factorial : ℂ_[p])⁻¹) • f ^ n

theorem coeff_expMv (f : MvPowerSeries σ ℂ_[p]) (α : σ →₀ ℕ) :
    coeff α (expMv f) =
      ∑ n ∈ Finset.range (Finsupp.degree α + 1), coeff α (f ^ n) / (n.factorial : ℂ_[p]) := rfl

theorem coeff_expT (f : MvPowerSeries σ ℂ_[p]) (N : ℕ) (α : σ →₀ ℕ) :
    coeff α (expT f N) = ∑ n ∈ Finset.range N, coeff α (f ^ n) / (n.factorial : ℂ_[p]) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [expT, map_sum, map_smul, smul_eq_mul, div_eq_inv_mul]

theorem coeff_expMv_eq_expT {f : MvPowerSeries σ ℂ_[p]} (hf : constantCoeff f = 0) {α : σ →₀ ℕ}
    {N : ℕ} (hN : Finsupp.degree α < N) : coeff α (expMv f) = coeff α (expT f N) := by
  rw [coeff_expMv, coeff_expT]
  apply Finset.sum_subset
  · intro n hn; simp only [Finset.mem_range] at *; omega
  · intro n _ hn
    simp only [Finset.mem_range, not_lt] at hn
    rw [coeff_pow_eq_zero hf (by omega), zero_div]

theorem pderiv_expT (f : MvPowerSeries σ ℂ_[p]) (i : σ) (N : ℕ) :
    pderiv (R := ℂ_[p]) i (expT f (N + 1)) = pderiv (R := ℂ_[p]) i f * expT f N := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [expT, map_sum, Derivation.map_smul, Finset.mul_sum]
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Derivation.map_one_eq_zero, smul_zero, add_zero]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [pderiv_pow, Nat.add_sub_cancel, smul_eq_C_mul, smul_eq_C_mul]
  have hn : ((n + 1 : ℕ) : MvPowerSeries σ ℂ_[p]) = C ((n + 1 : ℕ) : ℂ_[p]) := (map_natCast C _).symm
  have key : ((n + 1).factorial : ℂ_[p])⁻¹ * ((n + 1 : ℕ) : ℂ_[p]) = (n.factorial : ℂ_[p])⁻¹ := by
    have h1 : ((n + 1 : ℕ) : ℂ_[p]) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    rw [Nat.factorial_succ, Nat.cast_mul, mul_inv, mul_comm, ← mul_assoc, mul_inv_cancel₀ h1, one_mul]
  rw [hn]
  calc C ((n + 1).factorial : ℂ_[p])⁻¹ * (C ((n + 1 : ℕ) : ℂ_[p]) * f ^ n * pderiv (R := ℂ_[p]) i f)
      = C (((n + 1).factorial : ℂ_[p])⁻¹ * ((n + 1 : ℕ) : ℂ_[p])) * (f ^ n * pderiv (R := ℂ_[p]) i f) := by
        rw [map_mul]; ring
    _ = pderiv (R := ℂ_[p]) i f * (C (n.factorial : ℂ_[p])⁻¹ * f ^ n) := by rw [key]; ring

theorem pderiv_expMv {f : MvPowerSeries σ ℂ_[p]} (hf : constantCoeff f = 0) (i : σ) :
    pderiv (R := ℂ_[p]) i (expMv f) = pderiv (R := ℂ_[p]) i f * expMv f := by
  ext α
  have h1 : coeff α (pderiv (R := ℂ_[p]) i (expMv f)) =
      coeff α (pderiv (R := ℂ_[p]) i (expT f (Finsupp.degree α + 1 + 1))) := by
    rw [coeff_pderiv, coeff_pderiv, coeff_expMv_eq_expT hf]
    rw [map_add (f := _), Finsupp.degree_single]; omega
  rw [h1, pderiv_expT, coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  congr 1
  refine (coeff_expMv_eq_expT hf ?_).symm
  have := congrArg Finsupp.degree (Finset.HasAntidiagonal.mem_antidiagonal.1 hx)
  rw [map_add (f := _)] at this; omega

theorem constantCoeff_expMv (f : MvPowerSeries σ ℂ_[p]) : constantCoeff (expMv f) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_expMv]
  simp

theorem L0 {f c : MvPowerSeries σ ℂ_[p]} (i : σ) (hf : constantCoeff f = 0)
    (hE : IntegralMv (expMv f)) (hc : IntegralMv c) : IntegralMv (c * pderiv (R := ℂ_[p]) i f) := by
  obtain ⟨G, hG, hEG⟩ := intMv_inv hE (constantCoeff_expMv f)
  have : c * pderiv (R := ℂ_[p]) i f = c * pderiv (R := ℂ_[p]) i (expMv f) * G := by
    rw [pderiv_expMv hf, mul_assoc, mul_assoc, hEG, mul_one]
  rw [this]
  exact intMv_mul (intMv_mul hc (intMv_pderiv i hE)) hG

end PI.JetsPhW.W
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.ExpLow
section
noncomputable section

namespace PI.JetsPhW.Low

open PI.JetsPhW

variable {p : ℕ} [Fact p.Prime]

theorem coeff_truncatedExp_of_degree_eq_one {σ : Type*} (F : MvPowerSeries σ ℂ_[p]) {e : σ →₀ ℕ}
    (hd : Finsupp.degree e = 1) :
    MvPowerSeries.coeff e (expMv F) = MvPowerSeries.coeff e F := by
  classical
  have he : e ≠ 0 := by
    rintro rfl
    simp at hd
  have h1 : (e.sum fun _ k => k) = 1 := by
    rw [← hd]
    rfl
  change (∑ n ∈ Finset.range ((e.sum fun _ k => k) + 1),
    MvPowerSeries.coeff e (F ^ n) / (n.factorial : ℂ_[p])) = _
  rw [h1, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one, MvPowerSeries.coeff_one, if_neg he]
  simp

theorem norm_two (hp : p ≠ 2) : ‖(2 : ℂ_[p])‖ = 1 := by
  have h : ‖((2 : ℕ) : ℚ_[p])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.2 ((Nat.coprime_primes (Fact.out) Nat.prime_two).2 hp)
  have e : (2 : ℂ_[p]) = ((algebraMap ℚ_[p] (PadicAlgCl p) ((2 : ℕ) : ℚ_[p]) : PadicAlgCl p) : ℂ_[p]) := by
    rw [map_natCast, PadicComplex.coe_natCast]
    norm_num
  rw [e, PadicComplex.norm_extends, PadicAlgCl.norm_extends, h]

end PI.JetsPhW.Low
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.InvOmega
section
noncomputable section

open Classical

namespace PI.JetsPhW.Inv

variable {p : ℕ} [Fact p.Prime]

theorem dX_eq_derivative (f : PowerSeries ℂ_[p]) : dX f = PowerSeries.derivative f := by
  ext n
  rw [PowerSeries.coeff_derivative, dX, PowerSeries.coeff_mk, mul_comm]

theorem inverse_omega_holds : InvOmega := by
  simpa only [InvOmega, IsIntP, IsWq, dX, flog, omegaW,
    UpperTheory.Reformulated.B.Gwa1.InvOmega, UpperTheory.Reformulated.B.Gwa1.IsIntP,
    UpperTheory.Reformulated.B.Gwa1.IsWq, UpperTheory.Reformulated.B.Gwa1.dX,
    UpperTheory.Reformulated.B.Gwa1.flog, UpperTheory.Reformulated.B.Gwa1.omegaW] using
    _root_.UpperTheory.Reformulated.B.Gwa1.inverse_omega_holds

end PI.JetsPhW.Inv
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.JetIntegrality.TwoUnit
section
noncomputable section

namespace PI.JetsPhW.W

open PI.JetsPhW

def Dv {p : ℕ} [Fact p.Prime] {σ : Type*} (v : PowerSeries ℂ_[p]) (i : σ)
    (f : MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) v * MvPowerSeries.pderiv (R := ℂ_[p]) i f

def psi {p : ℕ} [Fact p.Prime] (ex ph : PowerSeries ℂ_[p]) : PowerSeries ℂ_[p] :=
  PowerSeries.subst ex ph

def IntP {p : ℕ} [Fact p.Prime] (g : PowerSeries ℂ_[p]) : Prop :=
  ∀ n, IsIntP (PowerSeries.coeff n g)

def DChain : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i : σ) (l v g : PowerSeries ℂ_[p]) (s : MvPowerSeries σ ℂ_[p])
    (c : ℂ_[p]), v * dX l = 1 → MvPowerSeries.constantCoeff s = 0 →
    MvPowerSeries.pderiv (R := ℂ_[p]) i s =
      MvPowerSeries.C c * PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) (dX l) →
    Dv v i (PowerSeries.subst s g) = MvPowerSeries.C c * PowerSeries.subst s (dX g)

def PdSelf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i : σ) (g : PowerSeries ℂ_[p]),
    MvPowerSeries.pderiv (R := ℂ_[p]) i (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) g) =
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) (dX g)

def PdNe : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i j : σ) (g : PowerSeries ℂ_[p]), j ≠ i →
    MvPowerSeries.pderiv (R := ℂ_[p]) i (PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries σ ℂ_[p]) g) = 0

def DSelf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i : σ) (v g : PowerSeries ℂ_[p]),
    Dv v i (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) g) =
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) (v * dX g)

def Ev0 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (s : MvPowerSeries σ ℂ_[p]) (g : PowerSeries ℂ_[p]),
    MvPowerSeries.constantCoeff s = 0 →
    MvPowerSeries.constantCoeff (PowerSeries.subst s g) = PowerSeries.constantCoeff g

def JetD : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (ex ph : PowerSeries ℂ_[p]) (n : ℕ),
    jet ex ph n = PowerSeries.constantCoeff ((dX (A := ℂ_[p]))^[n] (psi ex ph))

def LogDer : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i : σ) (v : PowerSeries ℂ_[p]) (f : MvPowerSeries σ ℂ_[p]),
    IntP v → MvPowerSeries.constantCoeff f = 0 → IntegralMv (expMv f) → IntegralMv (Dv v i f)

def Dint : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (i : σ) (v : PowerSeries ℂ_[p]) (f : MvPowerSeries σ ℂ_[p]),
    IntP v → IntegralMv f → IntegralMv (Dv v i f)

abbrev lX {p : ℕ} [Fact p.Prime] {σ : Type*} (l : PowerSeries ℂ_[p]) (j : σ) : MvPowerSeries σ ℂ_[p] :=
  PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries σ ℂ_[p]) l

def Rw3 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (l ex ph : PowerSeries ℂ_[p]), LogOk l ex →
    cubeE l ex ph =
      PowerSeries.subst (lX l 0 + lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) (psi ex ph) -
        PowerSeries.subst (lX l 0 + lX l 1 : MvPowerSeries (Fin 3) ℂ_[p]) (psi ex ph) -
        PowerSeries.subst (lX l 1 + lX l 2 : MvPowerSeries (Fin 3) ℂ_[p]) (psi ex ph) -
        PowerSeries.subst (lX l 2 + lX l 0 : MvPowerSeries (Fin 3) ℂ_[p]) (psi ex ph) +
        phAt ph (Xv 0) + phAt ph (Xv 1) + phAt ph (Xv 2)

end PI.JetsPhW.W
end
end

