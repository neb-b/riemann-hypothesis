module

public import Mathlib
public import Formalism.LocalToGlobal.InertKernelTheory.DefsBeCob
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FormalExponentialAgree
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.InVarAddInVarNeZero
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Joints
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.Bundle0006
public import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicNormTwoHundredSixteenEqOneOfFiveLe
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMulOfApprox
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhEquivShortWeierstrassModel
section
noncomputable section

namespace GlobalTheory.ShortModelTie

open Formalism.MainNotions.FormalGroupSystem Formalism.L2.Th1.D Formalism.L2.KerInert.BeCob
open Formalism.MainNotions.GL3Theta (G1)
open Formalism.L2.G.Pend (k0ToC wToC LTIso)
open Formalism.InvariantFactorPaths.G7 (lgF)
open Formalism.DworkPowerSeriesWeights (Integral)
open GlobalTheory.CurveDictionary (lgF_eq_logF cc_lgF')

theorem X_mul_lU {K : Type} [Field K] [CharZero K] (f : PowerSeries K) (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.X * Formalism.L2.Th1.B.lU f = f := by
  ext n
  cases n with
  | zero => rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply, hf]
  | succ n =>
    rw [PowerSeries.coeff_succ_X_mul]
    unfold Formalism.L2.Th1.B.lU
    rw [PowerSeries.coeff_mk]

theorem integral_ps {K : Type} [NormedField K] {f : PowerSeries K}
    (h : ∀ k, ‖PowerSeries.coeff k f‖ ≤ 1) : Integral (f : MvPowerSeries Unit K) := by
  intro n
  have e : n = Finsupp.single () (n ()) := Finsupp.ext fun u => by rcases u with ⟨⟩; simp
  rw [e]
  exact h (n ())

theorem exists_witt_series_inverse_formalGroup_iso {l : ℕ} [Fact l.Prime] {g : G1 l} (hOk : g.Ok) (hLT : LTIso g) :
    ∃ w : PowerSeries (WW l), PowerSeries.map (wToC l) w = vLT hLT := by
  have hex := hOk.2.2.1
  have hinv := hOk.2.2.2
  set e := eLT hLT with he
  have he1 : ‖e‖ = 1 := Formalism.L2.G.Pend.norm_wToC_unit l _
  have hene : e ≠ 0 := by intro h; rw [h, norm_zero] at he1; exact zero_ne_one he1
  set th0 := Formalism.L2.G.Pend.thOf hLT with hth0
  have h00 : PowerSeries.constantCoeff th0 = 0 := Formalism.L2.G.Pend.thOf_zero hLT
  have hu : IsUnit (PowerSeries.coeff 1 th0) := Formalism.L2.G.Pend.thOf_unit hLT
  set i0 := th0.substInvOfIsUnit hu with hi0
  have hi00 : PowerSeries.constantCoeff i0 = 0 := PowerSeries.constantCoeff_substInvOfIsUnit _ _
  have hR : PowerSeries.subst i0 th0 = PowerSeries.X := PowerSeries.subst_substInvOfIsUnit_right _ h00 hu
  set thC := PowerSeries.map (wToC l) th0 with hthC
  set iC := PowerSeries.map (wToC l) i0 with hiC
  have hthC0 : PowerSeries.constantCoeff thC = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hthC, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h00, map_zero]
  have hiC0 : PowerSeries.constantCoeff iC = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hiC, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hi00, map_zero]
  have hRC : PowerSeries.subst iC thC = PowerSeries.X := by
    have h := congrArg (MvPowerSeries.map (wToC l)) hR
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hi00)] at h
    exact h.trans (MvPowerSeries.map_X _ _)
  have hv0 : PowerSeries.constantCoeff (PowerSeries.C e⁻¹ * lgF ℂ_[l] l) = 0 := by
    rw [map_mul, cc_lgF', mul_zero]
  have hlog : PowerSeries.subst thC (lgF ℂ_[l] l) = PowerSeries.C e * g.l := by
    have h := Formalism.L2.G.Pend.thOf_log hLT
    rw [lgF_eq_logF] at h
    exact h
  have hVT : PowerSeries.subst thC (vLT hLT) = PowerSeries.X := by
    unfold vLT
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hv0)
      (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0),
      PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0), PowerSeries.subst_C, hlog]
    have e1 : (MvPowerSeries.C e⁻¹ : PowerSeries ℂ_[l]) * (PowerSeries.C e * g.l) = g.l := by
      rw [← mul_assoc]
      show PowerSeries.C e⁻¹ * PowerSeries.C e * g.l = g.l
      rw [← map_mul, inv_mul_cancel₀ hene, map_one, one_mul]
    rw [e1]
    exact Formalism.L2.G.Pend.ex_l g hex hinv
  refine ⟨i0, ?_⟩
  show iC = vLT hLT
  symm
  calc vLT hLT = PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[l]) (vLT hLT) := (PowerSeries.X_subst _).symm
    _ = PowerSeries.subst (PowerSeries.subst iC thC) (vLT hLT) := by rw [hRC]
    _ = PowerSeries.subst iC (PowerSeries.subst thC (vLT hLT)) :=
        (PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0)
          (PowerSeries.HasSubst.of_constantCoeff_zero' hiC0) _).symm
    _ = PowerSeries.subst iC (PowerSeries.X : PowerSeries ℂ_[l]) := by rw [hVT]
    _ = iC := PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' hiC0)

theorem v_integral {l : ℕ} [Fact l.Prime] {g : G1 l} (hOk : g.Ok) (hLT : LTIso g) (n : ℕ) :
    ‖PowerSeries.coeff n (vLT hLT)‖ ≤ 1 := by
  obtain ⟨w, hw⟩ := exists_witt_series_inverse_formalGroup_iso hOk hLT
  rw [← hw, PowerSeries.coeff_map]
  have := Formalism.L2.G.Pend.norm_wToC_pow_mul l 0 (PowerSeries.coeff n w)
  simpa using this

theorem phTie : Formalism.L2.KerInert.BeCob.PhTie := by
  intro l _ g hLT hOk s2 hph
  have hp : l.Prime := Fact.out
  have hex := hOk.2.2.1
  have hinv := hOk.2.2.2
  set e := eLT hLT with he
  have he1 : ‖e‖ = 1 := Formalism.L2.G.Pend.norm_wToC_unit l _
  have hene : e ≠ 0 := by intro h; rw [h, norm_zero] at he1; exact zero_ne_one he1
  set Lc : PowerSeries ℂ_[l] := lgF ℂ_[l] l with hLc
  have hL0 : PowerSeries.constantCoeff Lc = 0 := cc_lgF' _ _
  have hv0 : PowerSeries.constantCoeff (PowerSeries.C e⁻¹ * Lc) = 0 := by
    rw [map_mul, hL0, mul_zero]
  set v := vLT hLT with hvdef
  have hvcc : PowerSeries.constantCoeff v = 0 := PowerSeries.constantCoeff_subst_eq_zero hv0 _ hex
  have hvS : PowerSeries.HasSubst v := PowerSeries.HasSubst.of_constantCoeff_zero' hvcc
  set lW := Formalism.L2.Th1.A.logSer g.W with hlWdef
  have hgl : g.l = lW := Formalism.L2.KerInert.Dict.formal_logarithm_agree l g.W g.wq hOk.2.1
  have hlW0 : PowerSeries.constantCoeff lW = 0 := by rw [← hgl]; exact Formalism.MainNotions.J.cc_l g
  have hlW1 : PowerSeries.coeff 1 lW = 1 := (Formalism.L2.Th1.A.logSpec ℂ_[l] g.W).2.1
  have hvl : PowerSeries.subst v lW = PowerSeries.C e⁻¹ * Lc := by
    rw [← hgl]; exact Formalism.L2.G.Pend.lg_pt g hex hinv hv0
  set P := Formalism.L2.Th1.A.wpReg g.W with hPdef
  have hP : Formalism.L2.Th1.A.wpReg (Formalism.L2.Th1.A.shortW (Formalism.L2.Th1.A.g₂ g.W) (Formalism.L2.Th1.A.g₃ g.W)) = P := by
    rw [GlobalTheory.CurveDictionary.wpReg_eq, hPdef, GlobalTheory.CurveDictionary.wpReg_eq g.W, (Formalism.L2.Th1.A.shortInv ℂ_[l] _ _).2.1,
      (Formalism.L2.Th1.A.shortInv ℂ_[l] _ _).2.2.1]
  have hneg : ∀ f : PowerSeries ℂ_[l], PowerSeries.subst v (-f) = -PowerSeries.subst v f := fun f => by
    rw [← PowerSeries.coe_substAlgHom hvS, map_neg]
  have hlU1 : MvPowerSeries.constantCoeff (Formalism.L2.Th1.B.lU lW : MvPowerSeries Unit ℂ_[l]) = 1 := by
    show PowerSeries.constantCoeff (Formalism.L2.Th1.B.lU lW) = 1
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    unfold Formalism.L2.Th1.B.lU
    rw [PowerSeries.coeff_mk, zero_add, hlW1]
  set U := PowerSeries.subst v (Formalism.L2.Th1.B.lU lW) with hU
  have hψ : psiLT hLT = -PowerSeries.subst (PowerSeries.C e⁻¹ * Lc) (Formalism.L2.Th1.B.sigS P) +
      PowerSeries.C (s2 / 2) * (PowerSeries.C e⁻¹ * Lc) ^ 2 - Formalism.L2.Th1.B.fLog U := by
    unfold psiLT
    rw [hph]
    unfold Formalism.L2.Th1.B.phW Formalism.L2.Th1.B.phO
    rw [PowerSeries.subst_sub hvS, PowerSeries.subst_add hvS, hneg, PowerSeries.subst_mul hvS,
      PowerSeries.subst_pow hvS, PowerSeries.subst_C, hvl,
      PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hlW0) hvS, hvl]
    have hfl : PowerSeries.subst v (Formalism.L2.Th1.B.fLog (Formalism.L2.Th1.B.lU lW)) = Formalism.L2.Th1.B.fLog U := by
      rw [hU, PowerSeries.subst_def, PowerSeries.subst_def]
      exact Formalism.L2.Th1.B.subst_fLog (fun _ => hvcc) hlU1
    rw [← hfl]
    rfl
  have hFF : phFF l (Formalism.L2.Th1.A.g₂ g.W) (Formalism.L2.Th1.A.g₃ g.W) s2 e⁻¹ =
      -PowerSeries.subst (PowerSeries.C e⁻¹ * Lc) (Formalism.L2.Th1.B.sigS P) +
      PowerSeries.C (s2 / 2) * (PowerSeries.C e⁻¹ * Lc) ^ 2 - Formalism.L2.Th1.B.fLog (Formalism.L2.Th1.B.lU Lc) := by
    unfold phFF
    rw [hP]

  have hvU : v * U = PowerSeries.C e⁻¹ * Lc := by
    have h1 : PowerSeries.subst v (PowerSeries.X * Formalism.L2.Th1.B.lU lW) = v * U := by
      rw [PowerSeries.subst_mul hvS, PowerSeries.subst_X hvS]
    rw [← h1, X_mul_lU lW hlW0, hvl]
  have hprod : Formalism.L2.Th1.B.lU Lc = (PowerSeries.C e * Formalism.L2.Th1.B.lU v) * U := by
    apply mul_left_cancel₀ (PowerSeries.X_ne_zero (R := ℂ_[l]))
    rw [X_mul_lU Lc hL0]
    calc Lc = PowerSeries.C e * (PowerSeries.C e⁻¹ * Lc) := by
          rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hene, map_one, one_mul]
      _ = PowerSeries.C e * (v * U) := by rw [hvU]
      _ = PowerSeries.X * (PowerSeries.C e * Formalism.L2.Th1.B.lU v * U) := by
          rw [show PowerSeries.C e * (v * U) = PowerSeries.C e * ((PowerSeries.X * Formalism.L2.Th1.B.lU v) * U) by
            rw [X_mul_lU v hvcc]]
          ring

  have hex1 : PowerSeries.coeff 1 g.ex = 1 := by
    have h := congrArg (PowerSeries.coeff 1) hinv
    rw [Formalism.L2.G.Pend.coeff_one_subst _ _ hex, Formalism.L2.G.Pend.coeff_one_l g hOk.2.1, one_mul,
      PowerSeries.coeff_one_X] at h
    exact h
  have hv1 : PowerSeries.coeff 1 v = e⁻¹ := by
    rw [hvdef]
    unfold vLT
    rw [Formalism.L2.G.Pend.coeff_one_subst _ _ hv0, hex1, one_mul, PowerSeries.coeff_C_mul,
      Formalism.InvariantFactorPaths.G7.FormalGroupLaws.coeff_one_lgF l hp.two_le, mul_one]
  have hA : MvPowerSeries.constantCoeff (PowerSeries.C e * Formalism.L2.Th1.B.lU v : MvPowerSeries Unit ℂ_[l]) = 1 := by
    show PowerSeries.constantCoeff (PowerSeries.C e * Formalism.L2.Th1.B.lU v) = 1
    rw [map_mul, PowerSeries.constantCoeff_C, ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    unfold Formalism.L2.Th1.B.lU
    rw [PowerSeries.coeff_mk, zero_add, hv1, mul_inv_cancel₀ hene]
  have hLU : PowerSeries.constantCoeff (Formalism.L2.Th1.B.lU Lc) = 1 := Formalism.L2.Th1.E.Joints.cc_lU hp.two_le
  have hUc : MvPowerSeries.constantCoeff (U : MvPowerSeries Unit ℂ_[l]) = 1 := by
    have h := congrArg PowerSeries.constantCoeff hprod
    rw [hLU, map_mul] at h
    have hA' : PowerSeries.constantCoeff (PowerSeries.C e * Formalism.L2.Th1.B.lU v) = 1 := hA
    rw [hA', one_mul] at h
    exact h.symm
  have hdiff : (psiLT hLT : MvPowerSeries Unit ℂ_[l]) -
      phFF l (Formalism.L2.Th1.A.g₂ g.W) (Formalism.L2.Th1.A.g₃ g.W) s2 e⁻¹ =
      Formalism.L2.Th1.B.fLog (PowerSeries.C e * Formalism.L2.Th1.B.lU v : MvPowerSeries Unit ℂ_[l]) := by
    rw [hψ, hFF, hprod, Formalism.L2.Th1.B.ParO.fLog_mul hA hUc]
    ring
  refine ⟨?_, ?_⟩
  · rw [hdiff]; exact Formalism.L2.Th1.B.constantCoeff_fLog hA
  · rw [hdiff]
    show Integral (Formalism.L2.Th1.B.fExp (Formalism.L2.Th1.B.fLog _))
    rw [Formalism.L2.Th1.B.fExp_fLog hA]
    apply integral_ps
    intro k
    rw [PowerSeries.coeff_C_mul, norm_mul, he1, one_mul]
    unfold Formalism.L2.Th1.B.lU
    rw [PowerSeries.coeff_mk]
    exact v_integral hOk hLT (k + 1)

end GlobalTheory.ShortModelTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmulMemLocPOfVal
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint

noncomputable section

namespace GlobalTheory.JetOpWeylLat

open GlobalTheory.JetPoint GlobalTheory.LiftTypePrime Formalism.GradedWeylDivisibility

section Expand

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ}

omit [Fintype ι] in
theorem jetLin_mul_monomial (J : (DVar ι a b →₀ ℕ) → K) (P : Pol K ι b) (m : DVar ι a b →₀ ℕ) :
    jetLin J (rename Sum.inl P * rename Sum.inr (monomial m (1 : K))) = J m • P := by
  induction P using MvPolynomial.induction_on' with
  | monomial p c =>
    rw [rename_monomial, rename_monomial, monomial_mul, mul_one, jetLin, constr_monomial]
    have h1 : (p.mapDomain Sum.inl + m.mapDomain Sum.inr).comapDomain Sum.inl Sum.inl_injective.injOn = p := by
      ext x
      rw [Finsupp.comapDomain_apply, Finsupp.add_apply, Finsupp.mapDomain_apply_of_injective Sum.inl_injective,
        Finsupp.mapDomain_notin_range _ _ (by simp), add_zero]
    have h2 : (p.mapDomain Sum.inl + m.mapDomain Sum.inr).comapDomain Sum.inr Sum.inr_injective.injOn = m := by
      ext x
      rw [Finsupp.comapDomain_apply, Finsupp.add_apply, Finsupp.mapDomain_apply_of_injective Sum.inr_injective,
        Finsupp.mapDomain_notin_range _ _ (by simp), zero_add]
    rw [h1, h2, smul_monomial, smul_monomial, smul_eq_mul, smul_eq_mul, mul_comm]
  | add p q hp hq => rw [map_add (f := _), add_mul, map_add (f := _), hp, hq, smul_add]

def joinExp (α : ι → (Fin b × Fin a →₀ ℕ)) : DVar ι a b →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun k => α k.1 k.2

theorem subD_ten [DecidableEq ι] (h : a ≤ b) (F : ι → MvPolynomial (Fin a × Fin a) ℤ) :
    subD K ι a b (ten fun τ => map (Int.castRingHom K) (F τ)) =
      ∑ α ∈ Fintype.piFinset fun τ => (subGen h (F τ)).support,
        rename Sum.inl (ten fun τ => map (Int.castRingHom K) ((subGen h (F τ)).coeff (α τ))) *
          rename Sum.inr (monomial (joinExp α) (1 : K)) := by
  have e1 : subD K ι a b (ten fun τ => map (Int.castRingHom K) (F τ)) =
      ∏ τ, aeval (fun v : Fin a × Fin a => ∑ β : Fin b,
        (X (Sum.inl (τ, β, Fin.castLE h v.2)) : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) *
          X (Sum.inr (τ, β, v.1))) (F τ) := by
    unfold subD ten blockEmb
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [aeval_rename]
    refine (aeval_map_algebraMap K _ (F τ)).trans ?_
    congr 2
    funext v
    have hv : (v.2 : ℕ) < b := lt_of_lt_of_le v.2.2 h
    simp only [Function.comp_apply, dif_pos hv]
    rfl
  rw [e1]
  refine (Finset.prod_congr rfl fun τ _ => aeval_subGen h
    (fun v : Fin b × Fin a => (X (Sum.inr (τ, v)) : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K))
    (fun v : Fin b × Fin b => X (Sum.inl (τ, v))) (F τ)).trans ?_
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.prod_mul_distrib]
  congr 1
  · unfold ten blockEmb
    rw [map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [rename_rename, rename_eq_aeval]
    exact (aeval_map_algebraMap K _ _).symm
  · rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp), map_prod, Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun τ _ => ?_
    refine (Finsupp.prod_fintype (α τ)
      (fun v e => (X (Sum.inr (τ, v)) : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) ^ e) (by simp)).trans ?_
    simp [joinExp]

theorem jetMap_ten [DecidableEq ι] (h : a ≤ b) (J : (DVar ι a b →₀ ℕ) → K) (n : ι → ℕ)
    (f : ι → MvPolynomial (Fin a × Fin a) ℤ) :
    jetMap J n (ten fun τ => map (Int.castRingHom K) (f τ)) =
      ∑ α ∈ Fintype.piFinset fun τ => (subGen h (f τ * GlobalTheory.WeylMinorDual.gdet ℤ a ^ n τ)).support,
        J (joinExp α) • ten fun τ =>
          map (Int.castRingHom K) ((subGen h (f τ * GlobalTheory.WeylMinorDual.gdet ℤ a ^ n τ)).coeff (α τ)) := by
  have e : (ten fun τ => map (Int.castRingHom K) (f τ)) * ∏ τ, frDet K a τ ^ n τ =
      ten fun τ => map (Int.castRingHom K) (f τ * GlobalTheory.WeylMinorDual.gdet ℤ a ^ n τ) := by
    rw [← GlobalTheory.WeylMinorDual.ten_gdet]
    simp only [ten, map_mul, map_pow, GlobalTheory.WeylMinorDual.map_gdet, Finset.prod_mul_distrib]
  change jetLin J (subD K ι a b (_ * _)) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, subD_ten h, map_sum]
  exact Finset.sum_congr rfl fun α _ => jetLin_mul_monomial _ _ _

end Expand

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {a b : ℕ}

theorem toK_map_int {σ : Type} (f : MvPolynomial σ ℤ) :
    toK K σ (map (Int.castRingHom (𝓞 K)) f) = map (Int.castRingHom K) f := by
  change map (algebraMap (𝓞 K) K) _ = _
  rw [map_map]
  congr 1

theorem ten_mem_delStd (lam : ι → DomWeight a) {f : ι → MvPolynomial (Fin a × Fin a) ℤ}
    (hf : ∀ τ, f τ ∈ delSq ℤ a (lam τ)) : (ten fun τ => map (Int.castRingHom K) (f τ)) ∈ delStd K lam :=
  Submodule.subset_span ⟨_, fun τ => ⟨_, GlobalTheory.WeylRowAll.map_mem_weyl (Int.castRingHom (𝓞 K)) _ _ _ (hf τ),
    toK_map_int _⟩, rfl⟩

theorem delStd_le_span (lam : ι → DomWeight a) :
    delStd K lam ≤ Submodule.span (𝓞 K) {P | ∃ f : ι → MvPolynomial (Fin a × Fin a) ℤ,
      (∀ τ, f τ ∈ delSq ℤ a (lam τ)) ∧ P = ten fun τ => map (Int.castRingHom K) (f τ)} := by
  have h : ∀ τ, (delSq (𝓞 K) a (lam τ)).map (toK K _) = Submodule.span (𝓞 K) (Set.range fun u =>
      map (Int.castRingHom K) (applyWord ℤ u (hw ℤ (le_refl a) (lam τ).natW))) := fun τ => by
    rw [delSq, weyl, Submodule.map_span, ← Set.range_comp]
    congr 2
    funext u
    rw [← toK_map_int, ← lclosedeq_applyWord_map, lclosedeq_hw_map]
    rfl
  unfold delStd
  simp only [h]
  rw [GlobalTheory.WeylMinorDual.tensorLat_span]
  refine Submodule.span_mono ?_
  rintro _ ⟨u, rfl⟩
  exact ⟨_, fun τ => Submodule.subset_span ⟨u τ, rfl⟩, rfl⟩

theorem mem_localization_weylLattice_iff (w : HeightOneSpectrum (𝓞 K)) (lam : ι → DomWeight a)
    {M : ι → Submodule (𝓞 K) (Fin a → K)} (hM : LatWithBasis w M 1) (F : Formalism.L2.DIV.VV K lam) :
    F ∈ localization₂ w.asIdeal (delK lam fun τ => dualFr (M τ)) ↔ (F : Pol K ι a) ∈ localization₂ w.asIdeal (delStd K lam) := by
  have h1 : F ∈ localization₂ w.asIdeal (delK lam fun τ => dualFr (M τ)) ↔
      (F : Pol K ι a) ∈ localization₂ w.asIdeal (delP lam fun τ => dualFr (M τ)) := Iff.rfl
  have h2 := (GlobalTheory.TransLoc.nabDelLoc_free_leVV.1 K ι a lam (fun τ => dualFr (M τ))
    (fun τ => GlobalTheory.DualLat.isLattice_dualFr _ (GlobalTheory.HAtBasis.isLattice_of_basisAt w (hM τ).1 (hM τ).2)) w
    (fun τ => inside₂ K a ((1 : ι → GL (Fin a) K) τ))
    (fun τ => GlobalTheory.DualWeylDual.isBasisAt_dualFr w (hM τ).1 (hM τ).2)).2
  rw [h1, h2, GlobalTheory.TransLoc.mem_map_actP, GlobalTheory.HAtBasis.polyAction_invTranspose_inv]
  simp only [Pi.one_apply, Units.val_one, Matrix.det_one, one_zpow, Finset.prod_const_one, one_smul, blockAct_one,
    AlgHom.id_apply]

theorem smul_mem_localizationAt_of_valuation (w : HeightOneSpectrum (𝓞 K)) {Z : Type} [AddCommGroup Z] [Module K Z] [Module (𝓞 K) Z]
    [IsScalarTower (𝓞 K) K Z] {T : Submodule (𝓞 K) Z} {x : K}
    (hx : w.valuation K x ≤ 1) {P : Z} (hP : P ∈ T) : x • P ∈ localization₂ w.asIdeal T := by
  obtain ⟨r, ⟨d, hd⟩, h⟩ := w.exists_primeCompl_mul_eq_of_integer x hx
  have h' : algebraMap (𝓞 K) K d * x = algebraMap (𝓞 K) K r := (mul_comm _ _).trans h
  have e : d • x • P = r • P := by
    rw [← algebraMap_smul K d (x • P), smul_smul, h', algebraMap_smul]
  exact ⟨d, hd, e ▸ T.smul_mem r hP⟩

theorem jetMap_ten_mem (w : HeightOneSpectrum (𝓞 K)) {hab : a < b} {lam : ι → DomWeight a} {lam' : ι → DomWeight b}
    {s s' : ι → ℤ} {n : ι → ℕ} (hw : WtCompat hab lam lam' s s' n) {c : K} {J : (DVar ι a b →₀ ℕ) → K}
    (hJ : ∀ m, InDeg lam s' m → w.valuation K (c * J m) ≤ 1) {f : ι → MvPolynomial (Fin a × Fin a) ℤ}
    (hf : ∀ τ, f τ ∈ delSq ℤ a (lam τ)) :
    c • jetMap J n (ten fun τ => map (Int.castRingHom K) (f τ)) ∈ localization₂ w.asIdeal (delStd K lam') := by
  classical
  have hF : ∀ τ, f τ * GlobalTheory.WeylMinorDual.gdet ℤ a ^ n τ ∈ weyl ℤ a a le_rfl fun r => (lam τ).natW r + n τ := fun τ => by
    rw [GlobalTheory.WeylMinorDual.weyl_add]
    exact ⟨f τ, hf τ, rfl⟩
  have hν : ∀ τ (j : Fin b), (lam' τ).natW j = if h : (j : ℕ) < a then (lam τ).natW ⟨j, h⟩ + n τ else 0 := by
    intro τ j
    have e0 := GlobalTheory.WeylMinorDual.natW_cast (lam' τ) j
    have e5 := detShift_eq hw τ
    split_ifs with h
    · have e1 : (lam' τ).w j + s τ = _ := hw.1 τ ⟨j, h⟩
      have e2 := GlobalTheory.WeylMinorDual.natW_cast (lam τ) ⟨j, h⟩
      have e3 := hw.2.2 τ
      omega
    · have e1 := hw.2.1 τ j (not_lt.1 h)
      omega
  rw [jetMap_ten hab.le, Finset.smul_sum]
  refine Submodule.sum_mem _ fun α hα => ?_
  rw [smul_smul]
  refine smul_mem_localizationAt_of_valuation w (hJ _ fun τ => ?_)
    (ten_mem_delStd lam' fun τ => coeff_subGen_mem hab.le (natW_anti _) (hν τ) (hF τ) _)
  have h1 := subGen_isHomogeneous hab.le (isHomogeneous_of_mem_weyl
    (fun _ _ h => Nat.add_le_add_right (natW_anti _ h) _) (hF τ)) (mem_support_iff.1 (Fintype.mem_piFinset.1 hα τ))
  have h2 : (∑ β : Fin b, ∑ γ : Fin a, joinExp α (τ, β, γ)) = ∑ r, ((lam τ).natW r + n τ) := by
    rw [← h1, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type]
    simp [joinExp]
  rw [h2, Nat.cast_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Nat.cast_add, GlobalTheory.WeylMinorDual.natW_cast, hw.2.2 τ]
  ring

theorem jetOpWeyl : GlobalTheory.ColPeriod.JetOpWeyl := by
  intro K _ _ w ι _ a b hab lam lam' s s' n hw M MW _ _ hM hMW c J hJ F hF
  have hmem : jetMap J n (F : Pol K ι a) ∈ Formalism.L2.DIV.VV K lam' :=
    jetMap_mem hab.le n _ _ (fun ap => GlobalTheory.SubstMem.substAdj_sharp_mem K ι a b hab lam lam' s s' n hw ap _ F.2) J
  rw [mem_localization_weylLattice_iff w lam hM] at hF
  rw [mem_localization_weylLattice_iff w lam' hMW, Submodule.coe_smul, coe_jetOp _ _ _ _ _ hmem]
  have key : delStd K lam ≤ (localization₂ w.asIdeal (delStd K lam')).comap ((c • jetMap J n).restrictScalars (𝓞 K)) := by
    refine (delStd_le_span lam).trans (Submodule.span_le.2 ?_)
    rintro _ ⟨f, hf, rfl⟩
    exact jetMap_ten_mem w hw hJ hf
  obtain ⟨t, ht, hF⟩ := hF
  obtain ⟨u, hu, h⟩ := key hF
  refine ⟨u * t, mul_mem hu ht, ?_⟩
  rw [map_smul] at h
  rw [mul_smul]
  exact h

end GlobalTheory.JetOpWeylLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaIntertwinesMatchedOperators
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SysW


set_option maxHeartbeats 1000000 in
theorem matched_operators_theta_intertwine : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ SF, IsSF R SF → ∀ i t P, Good R t P → ∀ cV cW, MatchW R i t P cV cW → ∀ hV, IsOpsV R i t hV → (∀ h, IsOpsW R i h → ∀ y, R.thG i t (hV P cV y) = h P cW (R.thG i t y)) ∧ ∀ c, ∀ w ∈ Wcc R SF i c, hV P cV (LinearMap.adjoint (R.thG i t) w) = evC (Wc D i) P (c P) cW • LinearMap.adjoint (R.thG i t) w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS hX SF hSF i t P hP cV cW hM hV hhV
  have hP0 : Good R A.μ0 P := ((GlobalTheory.GoodPrimes.good_primes R F hC.lev).2.1 t P hP).2.2
  have hWinj : Function.Injective (R.HW i (sg0 D A)).e := (hC.models.HW i (sg0 D A)).1
  have key : ∀ h, IsOpsW R i h → ∀ y, R.thG i t (hV P cV y) = h P cW (R.thG i t y) := by
    intro h hh y
    have h1 := hM y (hV P cV y) (hhV P hP cV y)
    have h2 := hh P hP0 cW (R.thG i t y)
    exact hWinj (h1.trans h2.symm)
  refine ⟨key, ?_⟩
  intro c w hw
  have XW := _root_.GlobalTheory.SphOpsModel.sphericalOperators_forms_on_rank_space_normal_alt R F hC hS hX SF hSF i
  obtain ⟨hW, hWo, hWn, -, -, -, hWe, -⟩ := XW
  have XV := (GlobalTheory.T.realization_family_normal_operators R F hC.lev hC.fam hC.models).2 i t
  obtain ⟨hV', hV'o, hV'n⟩ := XV
  have hVinj : Function.Injective (R.HV i t).e := (hC.models.HV i t).1
  have heq : ∀ c, hV P c = hV' P c := fun c => LinearMap.ext fun x => hVinj (by rw [hhV P hP, hV'o P hP])
  have nV' : Commute (hV' P cV) (LinearMap.adjoint (hV' P cV)) :=
    Eq.mpr (congrArg (Commute (hV' P cV)) (hV'n.2 P hP cV)) (hV'n.1 P P hP hP _ _)
  have nV : Commute (hV P cV) (LinearMap.adjoint (hV P cV)) :=
    Eq.mpr (congrArg (fun L => Commute L (LinearMap.adjoint L)) (heq cV)) nV'
  have nW : Commute (hW P cW) (LinearMap.adjoint (hW P cW)) :=
    Eq.mpr (congrArg (Commute (hW P cW)) (hWn.2 P hP0 cW)) (hWn.1 P P hP0 hP0 _ _)
  exact _root_.GlobalTheory.HkUp.eigen_up_along_adjoint (R.thG i t) (fun _ : Unit => hV P cV) (fun _ : Unit => hW P cW) (fun _ u => key hW hWo u)
    (fun _ => nV) (fun _ => nW) () _ w (hWe c P hP0 cW w hw)

end GlobalTheory.SysW
end

