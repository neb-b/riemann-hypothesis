module

public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0009
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.GenusOneWittExistsOf
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.PadicNormTwoHundredSixteenEqOneOfFiveLe
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0005
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.EisensteinRecursion
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.Bundle0006
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.KummerThetaLogarithms.Bundle0004
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Joints
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.Bundle0006
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntBasis
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.CoeffPowEqZeroOfCc
public import Formalism.LocalToGlobal.InertKernelTheory.K2OfAgreements
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated

@[expose] public section

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMModel
section
noncomputable section

namespace Formalism.L2.KerInert.MModel

open PowerSeries
open Formalism.L2.Th1.A (shortW logSer expSer wpReg)
open Formalism.L2.KerInert.MC (phi)

variable {p : ℕ} [Fact p.Prime]

def scaleVC (e : ℂ_[p]ˣ) : WeierstrassCurve.VariableChange ℂ_[p] := ⟨e⁻¹, 0, 0, 0⟩

theorem scaleVC_smul (e : ℂ_[p]ˣ) (g2 g3 : ℂ_[p]) :
    scaleVC e • shortW g2 g3 = shortW ((e : ℂ_[p]) ^ 4 * g2) ((e : ℂ_[p]) ^ 6 * g3) := by
  ext <;>
    simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆, scaleVC, shortW, inv_inv] <;> ring

theorem norm_four (h5 : 5 ≤ p) : ‖(4 : ℂ_[p])‖ = 1 := by
  have hp : p.Prime := Fact.out
  rw [show (4 : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] ((4 : ℕ) : ℚ_[p]) by rw [map_natCast]; norm_num,
    norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  refine (Nat.Prime.coprime_iff_not_dvd hp).mpr fun hd => ?_
  have := Nat.le_of_dvd (by norm_num) hd
  omega

theorem coeffIn_short (h5 : 5 ≤ p) {g2 g3 : ℂ_[p]} (n2 : ‖g2‖ ≤ 1) (n3 : ‖g3‖ ≤ 1) :
    Formalism.L2.Th1.C.CoeffIn (Formalism.L2.KerInert.ModelP.RB p) (shortW g2 g3) := by
  have h4 := norm_four h5
  simp only [Formalism.L2.Th1.C.CoeffIn, Formalism.L2.Th1.C.mem_unitBall_iff, shortW, norm_zero, zero_le_one,
    norm_div, norm_neg, h4, div_one, true_and]
  exact ⟨n2, n3⟩

theorem param (h5 : 5 ≤ p) (g2 g3 ε : ℂ_[p]) (hε : ‖ε‖ = 1) (n2 : ‖g2‖ ≤ 1) (n3 : ‖g3‖ ≤ 1)
    (nd : ‖g2 ^ 3 - 27 * g3 ^ 2‖ = 1) (hth : ∀ n, ‖coeff n (Formalism.L2.Th1.D.thetaS p g2 g3 ε)‖ ≤ 1)
    (C : WeierstrassCurve.VariableChange ℂ_[p])
    (i1 : ‖(C • shortW (ε ^ 4 * g2) (ε ^ 6 * g3)).a₁‖ ≤ 1) (i2 : ‖(C • shortW (ε ^ 4 * g2) (ε ^ 6 * g3)).a₂‖ ≤ 1)
    (i3 : ‖(C • shortW (ε ^ 4 * g2) (ε ^ 6 * g3)).a₃‖ ≤ 1) (hΔ : ‖(C • shortW (ε ^ 4 * g2) (ε ^ 6 * g3)).Δ‖ = 1) :
    ∃ h : PowerSeries ℂ_[p], constantCoeff h = 0 ∧ (∀ n, ‖coeff n h‖ ≤ 1) ∧ ‖coeff 1 h‖ = 1 ∧
      PowerSeries.C (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])) * (logSer (C • shortW (ε ^ 4 * g2) (ε ^ 6 * g3))).subst h =
        Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p := by
  have hp2 : 2 ≤ p := by omega
  have hε0 : ε ≠ 0 := by
    intro h
    rw [h, norm_zero] at hε
    exact zero_ne_one hε
  set e : ℂ_[p]ˣ := Units.mk0 ε hε0 with he
  have hee : (e : ℂ_[p]) = ε := rfl
  have hW' : shortW (ε ^ 4 * g2) (ε ^ 6 * g3) = scaleVC e • shortW g2 g3 := by
    rw [scaleVC_smul, hee]
  set D := C * scaleVC e with hD
  have hCD : C • shortW (ε ^ 4 * g2) (ε ^ 6 * g3) = D • shortW g2 g3 := by
    rw [hW', hD, mul_smul]
  have hΔ0 : (shortW g2 g3).Δ = g2 ^ 3 - 27 * g3 ^ 2 := by
    simp only [shortW, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  have hW0int : Formalism.L2.Th1.C.CoeffIn (Formalism.L2.KerInert.ModelP.RB p) (shortW g2 g3) :=
    coeffIn_short h5 n2 n3
  obtain ⟨hu, hui, hr, hs, ht⟩ := Formalism.L2.KerInert.ModelP.vc_gen h5 (shortW g2 g3)
    (by simp [shortW]) (by simp [shortW]) (by simp [shortW]) (by rw [hΔ0, nd]) D
    (by rw [← hCD]; exact i1) (by rw [← hCD]; exact i2) (by rw [← hCD]; exact i3)
    (by rw [← hCD]; exact hΔ)
  have hsu : ((scaleVC e).u : ℂ_[p]) = ε⁻¹ := by
    show ((e⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) = ε⁻¹
    rw [Units.val_inv_eq_inv_val, hee]
  have hDu : (D.u : ℂ_[p]) = C.u * ε⁻¹ := by
    rw [← hsu]
    rfl
  have hCu : ‖(C.u : ℂ_[p])‖ = 1 := by
    rw [hDu, norm_mul, norm_inv, hε, inv_one, mul_one] at hu
    exact hu
  have hphiInt : Formalism.L2.Th1.C.IntPS (Formalism.L2.KerInert.ModelP.RB p) (phi (shortW g2 g3) D) :=
    Formalism.L2.KerInert.MC.intPS_phi (shortW g2 g3) hW0int D
      ((Formalism.L2.Th1.C.mem_unitBall_iff _).mpr hu.le) ((Formalism.L2.Th1.C.mem_unitBall_iff _).mpr hr)
      ((Formalism.L2.Th1.C.mem_unitBall_iff _).mpr hs) ((Formalism.L2.Th1.C.mem_unitBall_iff _).mpr ht)
  have hthInt : Formalism.L2.Th1.C.IntPS (Formalism.L2.KerInert.ModelP.RB p) (Formalism.L2.Th1.D.thetaS p g2 g3 ε) :=
    fun n => (Formalism.L2.Th1.C.mem_unitBall_iff _).mpr (hth n)
  have hlg0 : constantCoeff (Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p) = 0 :=
    Formalism.InvariantFactorPaths.G7.FormalGroupLaws.constantCoeff_lgF p hp2
  have hth0 : constantCoeff (Formalism.L2.Th1.D.thetaS p g2 g3 ε) = 0 := by
    simp only [Formalism.L2.Th1.D.thetaS]
    refine PowerSeries.constantCoeff_subst_eq_zero
      (by rw [map_mul]; exact mul_eq_zero_of_right _ hlg0) _ ?_
    simp [Formalism.L2.Th1.CM.uSer]
  set b : PowerSeries ℂ_[p] := PowerSeries.C (C.u : ℂ_[p]) * Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p with hbdef
  have hb0 : constantCoeff b = 0 := by simp [hbdef, hlg0]
  have hb : PowerSeries.HasSubst b := PowerSeries.HasSubst.of_constantCoeff_zero' hb0
  obtain ⟨hE0, hE1, hEL, -, -⟩ := Formalism.L2.Th1.A.expSpec ℂ_[p] (D • shortW g2 g3)
  have hE : PowerSeries.HasSubst (expSer (D • shortW g2 g3)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hE0
  have hh : PowerSeries.subst b (expSer (D • shortW g2 g3)) =
      PowerSeries.subst (Formalism.L2.Th1.D.thetaS p g2 g3 ε) (phi (shortW g2 g3) D) := by
    have hCX0 : constantCoeff (PowerSeries.C ((D.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * X : PowerSeries ℂ_[p]) = 0 := by
      simp
    have hCX : PowerSeries.HasSubst (PowerSeries.C ((D.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * X : PowerSeries ℂ_[p]) :=
      PowerSeries.HasSubst.of_constantCoeff_zero' hCX0
    obtain ⟨hE00, -, -, -, -⟩ := Formalism.L2.Th1.A.expSpec ℂ_[p] (shortW g2 g3)
    have hA : PowerSeries.HasSubst (PowerSeries.subst (PowerSeries.C ((D.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * X)
        (expSer (shortW g2 g3))) :=
      PowerSeries.HasSubst.of_constantCoeff_zero' (PowerSeries.constantCoeff_subst_eq_zero hCX0 _ hE00)
    rw [Formalism.L2.KerInert.MC.exp_eq, PowerSeries.subst_comp_subst_apply hA hb,
      PowerSeries.subst_comp_subst_apply hCX hb]
    congr 1
    have hsb : PowerSeries.subst b (PowerSeries.C ((D.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * X : PowerSeries ℂ_[p]) =
        PowerSeries.C ε * Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p := by
      rw [PowerSeries.subst_mul hb, PowerSeries.subst_X hb, PowerSeries.subst_C]
      show PowerSeries.C _ * b = _
      rw [hbdef, ← mul_assoc, ← map_mul, Units.val_inv_eq_inv_val, hDu]
      congr 2
      field_simp
    rw [hsb, Formalism.L2.Th1.D.thetaS, Formalism.L2.Th1.A.uSerEq]
  refine ⟨PowerSeries.subst b (expSer (D • shortW g2 g3)), ?_, ?_, ?_, ?_⟩
  · exact PowerSeries.constantCoeff_subst_eq_zero hb0 _ hE0
  · intro n
    rw [hh]
    exact (Formalism.L2.Th1.C.mem_unitBall_iff _).mp
      (Formalism.L2.KerInert.MC.intPS_subst' _ hphiInt hthInt hth0 n)
  · rw [Formalism.L2.G.Pend.coeff_one_subst _ _ hb0, hE1, one_mul, hbdef, PowerSeries.coeff_C_mul,
      Formalism.InvariantFactorPaths.G7.FormalGroupLaws.coeff_one_lgF p hp2, mul_one, hCu]
  · rw [hCD, ← PowerSeries.subst_comp_subst_apply hE hb, hEL, PowerSeries.subst_X hb, hbdef,
      ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]

section Exp

open Formalism.L2.Th1.B (fExp fLog sigS sigma lU fExp_add constantCoeff_fExp fExp_fLog constantCoeff_fLog)

theorem X_mul_shift (f : PowerSeries ℂ_[p]) (hf : constantCoeff f = 0) :
    f = X * PowerSeries.mk (fun n => coeff (n + 1) f) := by
  have h := PowerSeries.sub_const_eq_X_mul_shift f
  rwa [hf, map_zero, sub_zero] at h

theorem subst_fExp {a f : PowerSeries ℂ_[p]} (ha : constantCoeff a = 0) (hf : constantCoeff f = 0) :
    PowerSeries.subst a (fExp (ι := Unit) f) = fExp (ι := Unit) (PowerSeries.subst a f) := by
  simp only [fExp]
  exact PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hf)
    (PowerSeries.HasSubst.of_constantCoeff_zero' ha) _

theorem sig_at (h5 : 5 ≤ p) (g2 g3 s2 ε : ℂ_[p]) :
    (Formalism.L2.Th1.B.sgStar s2 (wpReg (shortW g2 g3))).subst (PowerSeries.C ε * Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p) =
      PowerSeries.C ε * X * fExp (-Formalism.L2.Th1.D.phFF p g2 g3 s2 ε) := by
  have hp2 : 2 ≤ p := by omega
  set L : PowerSeries ℂ_[p] := PowerSeries.C ε * Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p with hLdef
  set P := wpReg (shortW g2 g3)
  have hlg0 : constantCoeff (Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p) = 0 :=
    Formalism.InvariantFactorPaths.G7.FormalGroupLaws.constantCoeff_lgF p hp2
  have hL0 : constantCoeff L = 0 := by simp [hLdef, hlg0]
  have hL : PowerSeries.HasSubst L := PowerSeries.HasSubst.of_constantCoeff_zero' hL0
  have hS0 : constantCoeff (sigS P) = 0 := by
    simp [sigS, Formalism.L2.Th1.B.constantCoeff_prim]
  have hQ0 : constantCoeff (-(PowerSeries.C (s2 / 2) * X ^ 2 : PowerSeries ℂ_[p])) = 0 := by simp
  have hA0 : constantCoeff (PowerSeries.subst L (sigS P)) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hL0 _ hS0
  have hB0 : constantCoeff (-(PowerSeries.C (s2 / 2) * L ^ 2)) = 0 := by simp [hL0]
  have hAB : constantCoeff (PowerSeries.subst L (sigS P) + -(PowerSeries.C (s2 / 2) * L ^ 2)) = 0 := by
    rw [map_add (f := _), hA0, hB0, add_zero]
  have hU1 : constantCoeff (lU (Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p)) = 1 := by
    have h := Formalism.InvariantFactorPaths.G7.coeff_lgF_pow ℂ_[p] hp2 0
    simp only [pow_zero, inv_one] at h
    simpa [lU] using h
  have hF0 : constantCoeff (fLog (lU (Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p))) = 0 :=
    constantCoeff_fLog hU1
  have hXU : X * lU (Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p) = Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p :=
    (X_mul_shift _ hlg0).symm
  have hL' : L = PowerSeries.C ε * X * lU (Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p) := by
    rw [mul_assoc, hXU]
  have hsubQ : PowerSeries.subst L (-(PowerSeries.C (s2 / 2) * X ^ 2 : PowerSeries ℂ_[p])) =
      -(PowerSeries.C (s2 / 2) * L ^ 2) := by
    rw [← PowerSeries.coe_substAlgHom hL, map_neg, map_mul, map_pow, PowerSeries.coe_substAlgHom hL,
      PowerSeries.subst_X hL, PowerSeries.subst_C]
    rfl
  have hphi : -Formalism.L2.Th1.D.phFF p g2 g3 s2 ε =
      PowerSeries.subst L (sigS P) + -(PowerSeries.C (s2 / 2) * L ^ 2) +
        fLog (lU (Formalism.InvariantFactorPaths.G7.lgF ℂ_[p] p)) := by
    simp only [Formalism.L2.Th1.D.phFF]
    ring
  rw [hphi, fExp_add hAB hF0, fExp_add hA0 hB0, fExp_fLog hU1]
  simp only [Formalism.L2.Th1.B.sgStar, sigma]
  rw [PowerSeries.subst_mul hL, PowerSeries.subst_mul hL, PowerSeries.subst_X hL,
    subst_fExp hL0 hS0, subst_fExp hL0 hQ0, hsubQ]
  generalize fExp (PowerSeries.subst L (sigS P)) = a
  generalize fExp (-(PowerSeries.C (s2 / 2) * L ^ 2)) = b
  rw [hL']
  ring

end Exp

section EPart

open Formalism.L2.Th1.B (fExp fExp_add constantCoeff_fExp)

end EPart

section Comparison₂

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)

end Comparison₂

end Formalism.L2.KerInert.MModel
end
end

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMRead
section
noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical

namespace ParameterChangeLemmas

open IntegralOrthonormalChange

variable {p : ℕ} [Fact p.Prime]

theorem constantCoeff_inVar_eq_zero {σ : Type*} (i : σ) (f : PowerSeries ℂ_[p]) (hf : PowerSeries.constantCoeff f = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) f) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) f hf

theorem integral_subst_single_variable {σ : Type*} (i : σ) (f : PowerSeries ℂ_[p]) (hf : ∀ n, IsIntP (PowerSeries.coeff n f)) :
    IntegralMv (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) f) := by
  intro n
  rw [PowerSeries.coeff_subst_single]
  split_ifs
  · exact hf _
  · show ‖(0 : ℂ_[p])‖ ≤ 1
    simp

theorem integral_prod {σ ι : Type*} (s : Finset ι) (f : ι → MvPowerSeries σ ℂ_[p])
    (hf : ∀ i ∈ s, IntegralMv (f i)) : IntegralMv (∏ i ∈ s, f i) := by
  refine Finset.prod_induction f IntegralMv (fun a b ha hb => IntegralOrthonormalChange.integral_mul ha hb) ?_ hf
  intro n
  show ‖MvPowerSeries.coeff n (1 : MvPowerSeries σ ℂ_[p])‖ ≤ 1
  rw [MvPowerSeries.coeff_one]
  split_ifs <;> simp

theorem subst_single_var {σ τ : Type*} (S : σ → MvPowerSeries τ ℂ_[p]) (hS : MvPowerSeries.HasSubst S)
    (f : PowerSeries ℂ_[p]) (i : σ) :
    MvPowerSeries.subst S (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p]) f) =
      PowerSeries.subst (S i) f := by
  have hX : MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X i : MvPowerSeries σ ℂ_[p])) :=
    (PowerSeries.HasSubst.X i).const
  rw [PowerSeries.subst, MvPowerSeries.subst_comp_subst_apply hX hS, PowerSeries.subst]
  congr 1
  funext _
  exact MvPowerSeries.subst_X hS i

theorem subst_inv {σ : Type*} (a : MvPowerSeries σ ℂ_[p]) (ha : MvPowerSeries.constantCoeff a = 0)
    (f : PowerSeries ℂ_[p]) : PowerSeries.subst a f⁻¹ = (PowerSeries.subst a f)⁻¹ := by
  have hs : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  by_cases hf : PowerSeries.constantCoeff f = 0
  · have h1 : f⁻¹ = 0 := PowerSeries.inv_eq_zero.mpr hf
    have h2 : MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 :=
      PowerSeries.constantCoeff_subst_eq_zero ha f hf
    rw [h1, MvPowerSeries.inv_eq_zero.mpr h2, ← PowerSeries.coe_substAlgHom hs, map_zero]
  · have hm : PowerSeries.subst a f * PowerSeries.subst a f⁻¹ = 1 := by
      rw [← PowerSeries.subst_mul hs, PowerSeries.mul_inv_cancel f hf, ← PowerSeries.coe_substAlgHom hs, map_one]
    have hc : MvPowerSeries.constantCoeff (PowerSeries.subst a f) ≠ 0 := by
      intro h0
      have := congrArg MvPowerSeries.constantCoeff hm
      rw [map_mul, h0, zero_mul, map_one] at this
      exact zero_ne_one this
    rw [MvPowerSeries.eq_inv_iff_mul_eq_one hc, mul_comm, hm]

private theorem exists_integral_subst_inverse_of_unit_linear (h : PowerSeries ℂ_[p]) (h0 : PowerSeries.constantCoeff h = 0)
    (hI : ∀ n, ‖PowerSeries.coeff n h‖ ≤ 1) (h1 : ‖PowerSeries.coeff 1 h‖ = 1) :
    ∃ g : PowerSeries ℂ_[p], PowerSeries.constantCoeff g = 0 ∧ (∀ n, ‖PowerSeries.coeff n g‖ ≤ 1) ∧
      ‖PowerSeries.coeff 1 g‖ = 1 ∧ PowerSeries.subst h g = PowerSeries.X := by
  set u := PowerSeries.coeff 1 h with hudef
  have hu0 : u ≠ 0 := by
    intro hu
    rw [hu, norm_zero] at h1
    exact zero_ne_one h1
  obtain ⟨h', hh'⟩ : PowerSeries.X ∣ h := PowerSeries.X_dvd_iff.mpr h0
  have hcc : PowerSeries.constantCoeff h' = u := by
    rw [hudef, hh', PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have hpow : ∀ m k, PowerSeries.coeff k (h ^ m) =
      if m ≤ k then PowerSeries.coeff (k - m) (h' ^ m) else 0 := by
    intro m k
    rw [hh', mul_pow, PowerSeries.coeff_X_pow_mul']
  have hlow : ∀ m k, k < m → PowerSeries.coeff k (h ^ m) = 0 := by
    intro m k hk
    rw [hpow, ite_eq_right (by omega)]
  have hdiag : ∀ m, PowerSeries.coeff m (h ^ m) = u ^ m := by
    intro m
    rw [hpow, ite_eq_left le_rfl, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, hcc]
  let b : ℕ → ℂ_[p] := Nat.strongRec fun n rec =>
    (u ^ n)⁻¹ * PowerSeries.coeff n
      (PowerSeries.X - ∑ m : Fin n, PowerSeries.C (rec m m.isLt) * h ^ (m : ℕ))
  have hb : ∀ n, b n = (u ^ n)⁻¹ * PowerSeries.coeff n
      (PowerSeries.X - ∑ m ∈ Finset.range n, PowerSeries.C (b m) * h ^ m) := by
    intro n
    rw [← Fin.sum_univ_eq_sum_range (fun m => PowerSeries.C (b m) * h ^ m) n]
    exact Nat.strongRec_eq _ n
  have hcoeffP : ∀ N k, PowerSeries.coeff k (∑ m ∈ Finset.range N, PowerSeries.C (b m) * h ^ m) =
      ∑ m ∈ Finset.range N, b m * PowerSeries.coeff k (h ^ m) := by
    intro N k
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, PowerSeries.coeff_C_mul]
  have hA : ∀ N, ∀ k < N, PowerSeries.coeff k
      (PowerSeries.X - ∑ m ∈ Finset.range N, PowerSeries.C (b m) * h ^ m) = 0 := by
    intro N
    induction N with
    | zero => intro k hk; omega
    | succ N ih =>
      intro k hk
      rw [Finset.sum_range_succ, ← sub_sub, map_sub]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
      · rw [ih k hk, PowerSeries.coeff_C_mul, hlow N k hk, mul_zero, sub_zero]
      · subst hk
        rw [PowerSeries.coeff_C_mul, hdiag, hb k, mul_comm ((u ^ k)⁻¹) _, mul_assoc,
          inv_mul_cancel₀ (pow_ne_zero k hu0), mul_one, sub_self]
  have hb0 : b 0 = 0 := by
    rw [hb 0]
    simp
  have hb1 : b 1 = u⁻¹ := by
    rw [hb 1]
    simp [hb0]
  have hH : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hhI : Formalism.L2.Th1.C.IntPS (IntegralOrthonormalChange.intRing p) h := fun n => hI n
  have hpowI : ∀ m, Formalism.L2.Th1.C.IntPS (IntegralOrthonormalChange.intRing p) (h ^ m) := by
    intro m
    induction m with
    | zero => simpa using Formalism.L2.Th1.C.USideA.intPS_C (R := IntegralOrthonormalChange.intRing p) (one_mem _)
    | succ m ihm => rw [pow_succ]; exact Formalism.L2.Th1.C.USideA.intPS_mul ihm hhI
  have hint : ∀ n, b n ∈ IntegralOrthonormalChange.intRing p := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rw [hb n]
      refine Subring.mul_mem _ ?_ ?_
      · show ‖(u ^ n)⁻¹‖ ≤ 1
        rw [norm_inv, norm_pow, h1, one_pow, inv_one]
      · exact Formalism.L2.Th1.C.USideA.intPS_sub Formalism.L2.Th1.C.USideA.intPS_X
          (Formalism.L2.Th1.C.USideA.intPS_sum _ fun m hm =>
            Formalism.L2.Th1.C.USideA.intPS_mul
              (Formalism.L2.Th1.C.USideA.intPS_C (ih m (Finset.mem_range.mp hm))) (hpowI m)) n
  refine ⟨PowerSeries.mk b, ?_, ?_, ?_, ?_⟩
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk, hb0]
  · intro n
    rw [PowerSeries.coeff_mk]
    exact hint n
  · rw [PowerSeries.coeff_mk, hb1, norm_inv, h1, inv_one]
  · ext k
    rw [PowerSeries.coeff_subst' hH]
    simp only [PowerSeries.coeff_mk, smul_eq_mul]
    rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (k + 1)) ?_]
    · have := hA (k + 1) k (Nat.lt_succ_self k)
      rw [map_sub, hcoeffP, sub_eq_zero] at this
      exact this.symm
    · intro d hd
      simp only [Function.mem_support] at hd
      simp only [Finset.coe_range, Set.mem_Iio]
      by_contra hdk
      exact hd (by rw [hlow d k (by omega), mul_zero])

theorem exists_inv (h : PowerSeries ℂ_[p]) (h0 : PowerSeries.constantCoeff h = 0)
    (hI : ∀ n, IsIntP (PowerSeries.coeff n h)) (h1 : ‖PowerSeries.coeff 1 h‖ = 1) :
    ∃ g : PowerSeries ℂ_[p], PowerSeries.constantCoeff g = 0 ∧ (∀ n, IsIntP (PowerSeries.coeff n g)) ∧
      h.subst g = PowerSeries.X := by
  obtain ⟨g, g0, gI, g1, hg⟩ := exists_integral_subst_inverse_of_unit_linear h h0 hI h1
  obtain ⟨k, k0, -, -, hk⟩ := exists_integral_subst_inverse_of_unit_linear g g0 gI g1
  have hG : PowerSeries.HasSubst g := PowerSeries.HasSubst.of_constantCoeff_zero' g0
  have hH : PowerSeries.HasSubst h := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hkh : k = h := by
    have e1 : PowerSeries.subst h (PowerSeries.subst g k) = h := by
      rw [hk, PowerSeries.subst_X hH]
    rw [PowerSeries.subst_comp_subst_apply hG hH, hg, PowerSeries.X_subst] at e1
    exact e1
  refine ⟨g, g0, gI, ?_⟩
  rw [← hkh]
  exact hk

end ParameterChangeLemmas

open ParameterChangeLemmas IntegralOrthonormalChange

end Formalism.L2.KerInert
end
end

-- bundled from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SecondKernelNonzeroUnit
section
noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.K2

variable {p : ℕ} [Fact p.Prime] {X : Sys p}

theorem p_ne_zero_Kf (Y : Pend X) : (p : X.G.Kf) ≠ 0 := by
  intro h
  have h1 : algebraMap (K0 p) Y.Kc (p : K0 p) = 0 := by
    rw [map_natCast, ← map_natCast (algebraMap X.G.Kf Y.Kc), h, map_zero]
  rw [map_eq_zero_iff _ (algebraMap (K0 p) Y.Kc).injective] at h1
  exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) h1

theorem eS_ne_zero (Y : Pend X) (j : ℕ) (La : X.Lt j) : Y.eS j La ≠ 0 := by
  unfold Pend.eS
  exact Finset.prod_ne_zero_iff.mpr fun v _ => zpow_ne_zero _ (p_ne_zero_Kf Y)

theorem eT_ne_zero (Y : Pend X) (j : ℕ) (La' : X.Lt (j + 1)) : Y.eT j La' ≠ 0 := by
  unfold Pend.eT
  exact Finset.prod_ne_zero_iff.mpr fun v _ => zpow_ne_zero _ (p_ne_zero_Kf Y)

theorem kernel_of_smul : KerOfSmul := by
  intro p _ X Y j La La' f h G
  have hne : Y.eS j La * (Y.eT j La')⁻¹ ≠ 0 :=
    mul_ne_zero (eS_ne_zero Y j La) (inv_ne_zero (eT_ne_zero Y j La'))
  unfold Pend.ker Pend.kerF
  rw [h, map_smul, smul_smul, mul_inv_cancel₀ hne, one_smul]

theorem ker_zero (Y : Pend X) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) : Y.ker j La La' 0 = 0 := by
  simp only [Pend.ker, Pend.kerF, map_zero, LinearMap.zero_apply, smul_zero]

theorem ker_add (Y : Pend X) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) (G1 G2 : (X.Pj j).Xsp) :
    Y.ker j La La' (G1 + G2) = Y.ker j La La' G1 + Y.ker j La La' G2 := by
  simp only [Pend.ker, Pend.kerF, map_add (f := _), LinearMap.add_apply, smul_add]

theorem ker_smul (Y : Pend X) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)) (a : X.G.Kf) (G : (X.Pj j).Xsp) :
    Y.ker j La La' (a • G) = a • Y.ker j La La' G := by
  simp only [Pend.ker, Pend.kerF, map_smul, LinearMap.smul_apply]
  rw [smul_smul, smul_smul, mul_comm]

theorem map_smul_Kf (Y : Pend X) {σ : Type} (a : X.G.Kf) (P : MvPolynomial σ X.G.Kf) :
    MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (a • P) = a • MvPolynomial.map (algebraMap X.G.Kf Y.Kc) P := by
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul, algebraMap_smul]

theorem body_of_span (Y : Pend X) (j : ℕ) (cK : Y.Kc) (S : Set (X.Fm j))
    (hS : ∀ F ∈ S, ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
      MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (X.Kz j F c' L') =
        ∑ La ∈ Y.Rep j, (((X.stab j La : Y.Kc))⁻¹ * cK) • Y.ker j La (c', L') (F La.1 La.2))
    (F : X.Fm j) (hF : F ∈ Submodule.span X.G.Kf S) :
    ∀ (c' : X.Lv.comp (j + 1)) (L' : (X.Pj (j + 1)).Tup), (X.Pj (j + 1)).IsLatTup L' →
      MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (X.Kz j F c' L') =
        ∑ La ∈ Y.Rep j, (((X.stab j La : Y.Kc))⁻¹ * cK) • Y.ker j La (c', L') (F La.1 La.2) := by
  induction hF using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero =>
    intro c' L' _
    simp only [map_zero, Pi.zero_apply, ker_zero, smul_zero, Finset.sum_const_zero]
  | add x y _ _ hx hy =>
    intro c' L' hL
    simp only [map_add (f := _), Pi.add_apply, ker_add, smul_add, Finset.sum_add_distrib, hx c' L' hL, hy c' L' hL]
  | smul a x _ hx =>
    intro c' L' hL
    simp only [map_smul, Pi.smul_apply, ker_smul]
    rw [map_smul_Kf Y, hx c' L' hL, Finset.smul_sum]
    refine Finset.sum_congr rfl fun La _ => ?_
    rw [smul_comm]

section Rec

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc0 : G.Consts} {Dx : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc0 Dx cX}

theorem sharpQ_qOf {t : KerEntTied ex} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {i : ℕ}
    {x : ((Tw.fm u μ).lat i).V} (h : ∃ Q, SharpQ t Tw u μ i x Q) : SharpQ t Tw u μ i x (qOf t Tw u μ i x) := by
  unfold qOf
  rw [dite_eq_left h]
  exact Classical.choose_spec h

end Rec

end Formalism.L2.KerInert.K2
end
end

