module

public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0004
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Bundle0003
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.LogarithmicSubstitution.OneAddMulDerivLogSubst
public import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.BinomialSeriesCoefficients.CoeffPowEqZeroOfCc

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Taylor
section
noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.F

namespace Taylor

open PowerSeries

theorem coeff_taylor0 (f : ℂ → ℂ) (n : ℕ) :
    coeff n (taylor0 f) = iteratedDeriv n f 0 / (n.factorial : ℂ) := by
  simp [taylor0]

theorem taylor0_add {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylor0 (fun z => f z + g z) = taylor0 f + taylor0 g := by
  ext n
  rw [map_add (f := _), coeff_taylor0, coeff_taylor0, coeff_taylor0,
    iteratedDeriv_fun_add hf.contDiffAt hg.contDiffAt, add_div]

theorem taylor0_mul {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) :
    taylor0 (fun z => f z * g z) = taylor0 f * taylor0 g := by
  ext n
  rw [coeff_mul, coeff_taylor0, iteratedDeriv_fun_mul hf.contDiffAt hg.contDiffAt,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_div]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  simp only [coeff_taylor0]
  have h1 : (n.factorial : ℂ) = (n.choose i : ℂ) * (i.factorial : ℂ) * ((n - i).factorial : ℂ) := by
    exact_mod_cast (Nat.choose_mul_factorial_mul_factorial hi').symm
  have h2 : (n.choose i : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hi').ne'
  have h3 : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have h4 : ((n - i).factorial : ℂ) ≠ 0 := by exact_mod_cast (n - i).factorial_ne_zero
  rw [h1]
  field_simp

theorem taylor0_const (c : ℂ) : taylor0 (fun _ => c) = C c := by
  ext n
  rw [coeff_taylor0, iteratedDeriv_const, coeff_C]
  split_ifs with h
  · simp [h]
  · simp

theorem taylor0_id : taylor0 (fun z => z) = X := by
  ext n
  rw [coeff_taylor0, iteratedDeriv_fun_id_zero, coeff_X]
  split_ifs with h
  · simp [h]
  · simp

theorem taylor0_congr {f g : ℂ → ℂ} (h : f =ᶠ[nhds 0] g) : taylor0 f = taylor0 g := by
  ext n
  rw [coeff_taylor0, coeff_taylor0, h.iteratedDeriv_eq]

theorem taylor0_deriv (f : ℂ → ℂ) : taylor0 (deriv f) = derivative (taylor0 f) := by
  ext n
  rw [coeff_derivative, coeff_taylor0, coeff_taylor0, ← iteratedDeriv_succ', Nat.factorial_succ]
  have h3 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h4 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
  push_cast
  field_simp

theorem iteratedDeriv_comp_mul (a : ℂ) (n : ℕ) : ∀ f : ℂ → ℂ, AnalyticAt ℂ f 0 →
    iteratedDeriv n (fun z => f (a * z)) 0 = a ^ n * iteratedDeriv n f 0 := by
  induction n with
  | zero => intro f _; simp
  | succ n ih =>
    intro f hf
    have hc : Filter.Tendsto (fun z : ℂ => a * z) (nhds 0) (nhds 0) := by
      have : Continuous fun z : ℂ => a * z := by fun_prop
      simpa using this.tendsto 0
    have he : deriv (fun z => f (a * z)) =ᶠ[nhds 0] fun z => a * deriv f (a * z) := by
      filter_upwards [hc.eventually hf.eventually_analyticAt] with z hz
      have h1 : HasDerivAt f (deriv f (a * z)) (a * z) := hz.differentiableAt.hasDerivAt
      have h2 : HasDerivAt (fun z : ℂ => a * z) a z := by
        simpa using (hasDerivAt_id z).const_mul a
      have := (h1.comp z h2).deriv
      rw [mul_comm] at this
      exact this
    rw [iteratedDeriv_succ', he.iteratedDeriv_eq, iteratedDeriv_const_mul_field, ih _ hf.deriv,
      iteratedDeriv_succ', pow_succ]
    ring

theorem taylor0_rescale {f : ℂ → ℂ} (a : ℂ) (hf : AnalyticAt ℂ f 0) :
    taylor0 (fun z => f (a * z)) = rescale a (taylor0 f) := by
  ext n
  rw [coeff_rescale, coeff_taylor0, coeff_taylor0, iteratedDeriv_comp_mul a n f hf, mul_div_assoc]

theorem taylor0_inj {f g : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0)
    (h : taylor0 f = taylor0 g) : f =ᶠ[nhds 0] g := by
  have hd : AnalyticAt ℂ (fun z => f z - g z) 0 := hf.fun_sub hg
  have h0 : ∀ n, iteratedDeriv n (fun z => f z - g z) 0 = 0 := by
    intro n
    have h1 := congrArg (coeff n) h
    rw [coeff_taylor0, coeff_taylor0] at h1
    have h3 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have h2 : iteratedDeriv n f 0 = iteratedDeriv n g 0 := by
      field_simp at h1
      exact h1
    rw [iteratedDeriv_fun_sub hf.contDiffAt hg.contDiffAt, h2, sub_self]
  have ht : analyticOrderAt (fun z => f z - g z) 0 = ⊤ := by
    rw [ENat.eq_top_iff_forall_ge]
    intro n
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hd).mpr fun i _ => h0 i
  rw [analyticOrderAt_eq_top] at ht
  filter_upwards [ht] with z hz
  exact sub_eq_zero.mp hz

theorem ode_zero {a Y : PowerSeries ℂ} (h : derivative Y = a * Y) (h0 : constantCoeff Y = 0) :
    Y = 0 := by
  have key : ∀ n, coeff n Y = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      cases n with
      | zero => simpa using h0
      | succ n =>
        have h1 := congrArg (coeff n) h
        rw [coeff_derivative, coeff_mul] at h1
        have h2 : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, coeff p.1 a * coeff p.2 Y = 0 := by
          refine Finset.sum_eq_zero fun p hp => ?_
          have : p.2 < n + 1 := by
            have := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
            omega
          rw [ih _ this, mul_zero]
        rw [h2] at h1
        have h4 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast n.succ_ne_zero
        exact (mul_eq_zero.mp h1).resolve_right h4
  ext n
  simpa using key n

theorem taylor0_exp {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (h0 : f 0 = 0) :
    taylor0 (fun z => Complex.exp (f z)) = Formalism.L2.Th1.B.fExp (taylor0 f) := by
  have hE : AnalyticAt ℂ (fun z => Complex.exp (f z)) 0 := hf.cexp
  have hc : constantCoeff (taylor0 f) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_taylor0]
    simp [h0]
  have hS : HasSubst (taylor0 f) := HasSubst.of_constantCoeff_zero' hc
  have he : deriv (fun z => Complex.exp (f z)) =ᶠ[nhds 0] fun z => deriv f z * Complex.exp (f z) := by
    filter_upwards [hf.eventually_analyticAt] with z hz
    have := (hz.differentiableAt.hasDerivAt.cexp).deriv
    rw [mul_comm] at this
    exact this
  have h1 : derivative (taylor0 fun z => Complex.exp (f z))
      = derivative (taylor0 f) * taylor0 fun z => Complex.exp (f z) := by
    rw [← taylor0_deriv, taylor0_congr he, taylor0_mul hf.deriv hE, taylor0_deriv]
  have h2 : derivative (Formalism.L2.Th1.B.fExp (taylor0 f))
      = derivative (taylor0 f) * Formalism.L2.Th1.B.fExp (taylor0 f) := by
    unfold Formalism.L2.Th1.B.fExp
    rw [derivative_subst hS, derivative_exp, mul_comm]
  have h3 : constantCoeff (taylor0 fun z => Complex.exp (f z)) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_taylor0]
    simp [h0]
  have h4 : constantCoeff (Formalism.L2.Th1.B.fExp (taylor0 f)) = 1 := by
    unfold Formalism.L2.Th1.B.fExp
    have h5 : exp ℂ = 1 + (exp ℂ - 1) := by ring
    have h6 : (1 : PowerSeries ℂ).subst (taylor0 f) = (1 : PowerSeries ℂ) := by
      rw [← coe_substAlgHom hS, map_one]
    have h7 : constantCoeff ((exp ℂ - 1).subst (taylor0 f) : PowerSeries ℂ) = 0 :=
      constantCoeff_subst_eq_zero hc _ (by simp)
    rw [h5, subst_add hS, h6, map_add (f := _), map_one, h7, add_zero]
  refine sub_eq_zero.mp (ode_zero (a := derivative (taylor0 f)) ?_ ?_)
  · rw [map_sub, h1, h2, mul_sub]
  · rw [map_sub, h3, h4, sub_self]

end Taylor

theorem taylor_ring : TaylorRing :=
  ⟨fun _ _ hf hg => ⟨Taylor.taylor0_add hf hg, Taylor.taylor0_mul hf hg⟩, Taylor.taylor0_const,
    Taylor.taylor0_id, fun _ _ h => Taylor.taylor0_congr h⟩

theorem taylor_deriv : TaylorDeriv :=
  ⟨fun f _ => Taylor.taylor0_deriv f, fun _ a hf => Taylor.taylor0_rescale a hf,
    fun _ _ hf hg h => Taylor.taylor0_inj hf hg h⟩

theorem taylor_exp : TaylorExp := fun _ hf h0 => Taylor.taylor0_exp hf h0

end Formalism.L2.Th1.F
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.TaylorSigma
section
noncomputable section
open Filter Topology

namespace Formalism.L2.Th1.F

namespace TaylorSigmaUniqueness


open PowerSeries in
lemma formal_unique (P U V : PowerSeries ℂ) (hV : X * derivative V = -(X * P))
    (hV0 : constantCoeff V = 0) (hU : X * derivative U = X * (V * U))
    (hU0 : constantCoeff U = 1) : U = B.fExp (B.sigS P) := by
  have hV' : derivative V = -P := by
    apply mul_left_cancel₀ (X_ne_zero (R := ℂ))
    rw [hV, mul_neg]
  have hU' : derivative U = V * U := mul_left_cancel₀ (X_ne_zero (R := ℂ)) hU
  have hVp : V = -B.prim P := by
    refine derivative.ext ?_ ?_
    · rw [hV', map_neg]
      exact congrArg Neg.neg (B.dz_prim P).symm
    · rw [hV0, map_neg, B.constantCoeff_prim, neg_zero]
  have hS0 : constantCoeff (B.sigS P) = 0 := by
    rw [B.sigS, map_neg, B.constantCoeff_prim, neg_zero]
  have hS0' : constantCoeff (-B.sigS P) = 0 := by rw [map_neg, hS0, neg_zero]
  have hSd : derivative (B.sigS P) = V := by
    rw [B.sigS, map_neg, hVp]
    exact congrArg Neg.neg (B.dz_prim _)
  have key : U * (C.mvExp (-B.sigS P) : PowerSeries ℂ) = 1 := by
    refine derivative.ext ?_ ?_
    · rw [Derivation.leibniz, C.derivative_mvExp hS0', map_neg, hSd, hU', Derivation.map_one_eq_zero]
      simp only [smul_eq_mul]
      ring
    · rw [map_mul, hU0, map_one, one_mul]
      exact C.constantCoeff_mvExp hS0'
  have h2 : (C.mvExp (-B.sigS P) : PowerSeries ℂ) * C.mvExp (B.sigS P) = 1 := C.mvExp_neg hS0
  calc U = U * ((C.mvExp (-B.sigS P) : PowerSeries ℂ) * C.mvExp (B.sigS P)) := by rw [h2, mul_one]
    _ = C.mvExp (B.sigS P) := by rw [← mul_assoc, key, one_mul]
    _ = B.fExp (B.sigS P) := rfl

lemma constantCoeff_taylor0 (f : ℂ → ℂ) : PowerSeries.constantCoeff (taylor0 f) = f 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, taylor0, PowerSeries.coeff_mk]
  simp

def u (L : PeriodPair) (z : ℂ) : ℂ := ∏' l : L.lattice, wFactor (l : ℂ) z

lemma differentiable_u (L : PeriodPair) : Differentiable ℂ (u L) :=
  SigmaBasic.differentiable_tprod sigma_product_locally_uniform L

lemma u_zero (L : PeriodPair) : u L 0 = 1 := by
  simp [u, SigmaBasic.wFactor_zero_right]

lemma analyticAt_v (L : PeriodPair) : AnalyticAt ℂ (AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0) 0 :=
  (AnalyticIdentityTheoremsZetaFacts.differentiableOn_zetaExcept L 0).analyticAt (L.compl_lattice_sdiff_singleton_mem_nhds 0)

lemma analyticAt_pExcept (L : PeriodPair) : AnalyticAt ℂ (L.weierstrassPExcept 0) 0 :=
  (L.differentiableOn_weierstrassPExcept 0).analyticAt (L.compl_lattice_sdiff_singleton_mem_nhds 0)

lemma ode_u (L : PeriodPair) :
    ∀ᶠ z in 𝓝 (0 : ℂ), z * deriv (u L) z = z * (AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0 z * u L z) := by
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0] with z hz
  by_cases h0 : z = 0
  · simp [h0]
  have hzl : z ∉ L.lattice := fun h => hz ⟨h, h0⟩
  have h1 : HasDerivAt (wSigma L) (wZeta L z * wSigma L z) z :=
    sigmaLogDeriv_of sigma_product_locally_uniform sigma_summable zeta_summable L z hzl
  have h2 : HasDerivAt (wSigma L) (1 * u L z + z * deriv (u L) z) z :=
    (hasDerivAt_id z).mul (differentiable_u L z).hasDerivAt
  have h3 := h1.unique h2
  rw [← AnalyticIdentityTheoremsZetaFacts.zetaExcept_zero_add L z] at h3
  have h4 : wSigma L z = z * u L z := rfl
  rw [h4] at h3
  have h5 : (1 / z) * z = 1 := by field_simp
  linear_combination -h3 + u L z * h5

lemma ode_v (L : PeriodPair) :
    ∀ᶠ z in 𝓝 (0 : ℂ), z * deriv (AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0) z = -(z * L.weierstrassPExcept 0 z) := by
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0] with z hz
  by_cases h0 : z = 0
  · simp [h0]
  have hzl : z ∉ L.lattice := fun h => hz ⟨h, h0⟩
  have h1 : HasDerivAt (wZeta L) (-(L.weierstrassP z)) z := zeta_has_deriv L z hzl
  have h2 : HasDerivAt (fun w : ℂ => 1 / w) (-(1 / z ^ 2)) z := by
    simpa only [one_div] using hasDerivAt_inv h0
  have h3 : AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0 = fun w => wZeta L w - 1 / w := by
    funext w
    rw [← AnalyticIdentityTheoremsZetaFacts.zetaExcept_zero_add L w]
    ring
  have h4 : deriv (fun w => wZeta L w - 1 / w) z = -(L.weierstrassP z) - -(1 / z ^ 2) :=
    (h1.sub h2).deriv
  rw [h3, h4]
  have h5 := L.weierstrassPExcept_add 0 z
  simp only [ZeroMemClass.coe_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, div_zero] at h5
  rw [← h5]
  ring

end TaylorSigmaUniqueness


open TaylorSigmaUniqueness in
theorem taylorSigma_of (hr : TaylorRing) (hd : TaylorDeriv) : TaylorSigma := by
  intro L
  obtain ⟨hadd, hC, hX, hgerm⟩ := hr
  have hid : AnalyticAt ℂ (fun z : ℂ => z) 0 := analyticAt_id
  have hu : AnalyticAt ℂ (u L) 0 := (differentiable_u L).analyticAt 0
  have hv := analyticAt_v L
  have hp := analyticAt_pExcept L
  have e1 : taylor0 (wSigma L) = PowerSeries.X * taylor0 (u L) := by
    have := (hadd (fun z => z) (u L) hid hu).2
    rw [hX] at this
    exact this
  have eU : PowerSeries.X * PowerSeries.derivative (R := ℂ) (taylor0 (u L))
      = PowerSeries.X * (taylor0 (AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0) * taylor0 (u L)) := by
    have hvu : AnalyticAt ℂ (fun z => AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0 z * u L z) 0 := hv.mul hu
    rw [← hd.1 _ hu, ← hX, ← (hadd _ _ hid hu.deriv).2, ← (hadd _ _ hv hu).2,
      ← (hadd _ _ hid hvu).2]
    exact hgerm _ _ (ode_u L)
  have eV : PowerSeries.X * PowerSeries.derivative (R := ℂ) (taylor0 (AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0))
      = -(PowerSeries.X * pSeries L) := by
    have hneg : taylor0 (fun z => (-1 : ℂ) * (z * L.weierstrassPExcept 0 z))
        = -(PowerSeries.X * pSeries L) := by
      have hzp : AnalyticAt ℂ (fun z => z * L.weierstrassPExcept 0 z) 0 := hid.mul hp
      rw [(hadd (fun _ => (-1 : ℂ)) _ analyticAt_const hzp).2, hC,
        (hadd _ _ hid hp).2, hX, pSeries]
      simp
    rw [← hd.1 _ hv, ← hneg, ← hX, ← (hadd _ _ hid hv.deriv).2]
    refine hgerm _ _ ((ode_v L).mono fun z hz => ?_)
    show z * deriv (AnalyticIdentityTheoremsZetaFacts.zetaExcept L 0) z = -1 * (z * L.weierstrassPExcept 0 z)
    rw [hz]; ring
  rw [e1, B.sigma]
  congr 1
  refine formal_unique (pSeries L) _ _ eV ?_ eU ?_
  · rw [constantCoeff_taylor0, AnalyticIdentityTheoremsZetaFacts.zetaExcept_zero_zero]
  · rw [constantCoeff_taylor0, u_zero]

theorem taylorSgStar_of (h : TaylorSigma) (hr : TaylorRing) (he : TaylorExp) (hent : SigmaEntire) :
    TaylorSgStar := by
  intro L
  obtain ⟨hadd, hC, hX, -⟩ := hr
  have hid : AnalyticAt ℂ (fun z : ℂ => z) 0 := analyticAt_id
  have hzz : AnalyticAt ℂ (fun z : ℂ => z * z) 0 := hid.mul hid
  have hf : AnalyticAt ℂ (fun z : ℂ => -(s2 L / 2) * (z * z)) 0 := analyticAt_const.mul hzz
  have hef : AnalyticAt ℂ (fun z : ℂ => Complex.exp (-(s2 L / 2) * (z * z))) 0 := hf.cexp
  have hTf : taylor0 (fun z : ℂ => -(s2 L / 2) * (z * z))
      = -(PowerSeries.C (s2 L / 2) * PowerSeries.X ^ 2) := by
    rw [(hadd (fun _ => -(s2 L / 2)) _ analyticAt_const hzz).2, hC,
      (hadd _ _ hid hid).2, hX, map_neg]
    ring
  have hfun : sgStar L = fun z => wSigma L z * Complex.exp (-(s2 L / 2) * (z * z)) := by
    funext z
    rw [sgStar]
    congr 2
    ring
  rw [hfun, (hadd _ _ ((hent L).analyticAt 0) hef).2, h L, he _ hf (by simp), hTf, B.sgStar]

namespace TaylorSigmaUniqueness

lemma dblInt_eq (e : PowerSeries ℂ) : C.dblInt e = B.prim (B.prim e) := by
  ext n
  simp only [C.dblInt, B.prim, PowerSeries.coeff_mk]
  rcases n with _ | _ | n
  · simp
  · simp
  · have h1 : ((n : ℂ) + 1 + 1) ≠ 0 := by
      have : ((n + 2 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      push_cast at this
      intro h; apply this; linear_combination h
    have h2 : ((n : ℂ) + 1) ≠ 0 := by
      have : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      push_cast at this
      exact this
    simp
    field_simp

end TaylorSigmaUniqueness


open TaylorSigmaUniqueness in
theorem taylorSgStar'_of (h : TaylorSgStar) : TaylorSgStar' := by
  intro L
  rw [h L, B.sgStar, B.sigma, C.sgStar, C.lam, dblInt_eq, mul_assoc]
  congr 1
  have h1 : MvPowerSeries.constantCoeff (B.sigS (pSeries L)) = 0 := by
    have : PowerSeries.constantCoeff (B.sigS (pSeries L)) = 0 := by
      rw [B.sigS, map_neg, B.constantCoeff_prim, neg_zero]
    exact this
  have h2 : MvPowerSeries.constantCoeff
      (-(PowerSeries.C (s2 L / 2) * PowerSeries.X ^ 2) : PowerSeries ℂ) = 0 := by
    have : PowerSeries.constantCoeff
        (-(PowerSeries.C (s2 L / 2) * PowerSeries.X ^ 2) : PowerSeries ℂ) = 0 := by simp
    exact this
  rw [← B.fExp_add h1 h2, B.sigS, ← neg_add]
  rfl

end Formalism.L2.Th1.F
end
end

