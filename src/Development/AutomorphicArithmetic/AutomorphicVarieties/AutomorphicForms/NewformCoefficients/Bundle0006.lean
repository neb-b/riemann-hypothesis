module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCritAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0064
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.StrongApp

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.CuspCrit
section
open NumberField MeasureTheory GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd UpperTheory.V.Af.Nf
open scoped Matrix MatrixGroups

private theorem two_periods {f : ℝ → ℂ} (hc : Continuous f) {N N' : ℕ} (hN' : 0 < N') (h : Function.Periodic f N)
    (h' : Function.Periodic f N') (h0 : ∫ t in (0 : ℝ)..N', f t = 0) : ∫ t in (0 : ℝ)..N, f t = 0 := by
  have e1 := h.intervalIntegral_add_zsmul_eq (N' : ℤ) 0 fun a b => hc.intervalIntegrable a b
  have e2 := h'.intervalIntegral_add_zsmul_eq (N : ℤ) 0 fun a b => hc.intervalIntegrable a b
  simp only [zero_add, zsmul_eq_mul, Int.cast_natCast] at e1 e2
  rw [h0, mul_zero, mul_comm, e1] at e2
  exact (mul_eq_zero.1 e2).resolve_left (Nat.cast_ne_zero.2 hN'.ne')

private theorem aff_add {R : Type} [CommRing R] (x y : R) : aff 1 (x + y) = aff 1 x * aff 1 y := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Fin.sum_univ_succ, add_comm]

private theorem upR_aff (t : ℝ) : upR (aff 1 t) = aff 1 (TR.sInf ℚ (algebraMap ℝ (TR.Rinf ℚ) t)) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change (1 : Matrix (Fin 2) (Fin 2) (Ad ℚ)) i j - TR.sInf ℚ ((1 : Matrix (Fin 2) (Fin 2) (TR.Rinf ℚ)) i j) +
    TR.sInf ℚ (algebraMap ℝ (TR.Rinf ℚ) ((aff 1 t).val i j)) = (aff 1 _).val i j
  fin_cases i <;> fin_cases j <;> simp [aff]

private theorem ratGL_aff (q : ℚ) : ratGL ℚ 2 (aff 1 q) = aff 1 (algebraMap ℚ (Ad ℚ) q) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  change algebraMap ℚ (Ad ℚ) ((aff 1 q).val i j) = (aff 1 _).val i j
  fin_cases i <;> fin_cases j <;> simp [aff]

theorem UpperTheory.V.Af.Nf.cuspCrit :
    UpperTheory.V.Af.Nf.CuspCrit := by
  intro φ hl ho hct r h0 h1 _ _ μ D hμ hD g
  obtain rfl : r = 1 := by omega
  obtain ⟨i1, i2, -, i3, -, hu, hx⟩ := UpperTheory.eisenstein_constantTerm_upperBlock ℚ
  have hφ := smCont ℚ 2 φ ho
  obtain ⟨N, hN, hper⟩ := autPer φ hl ho g
  let e : ℝ → BlockIx 2 1 → Ad ℚ := fun t _ => TR.sInf ℚ (algebraMap ℝ (TR.Rinf ℚ) t)
  have he : Continuous e := continuous_pi fun _ =>
    (((TR.continuous_infEq ℚ).comp (continuous_algebraMap ℝ (TR.Rinf ℚ))).prodMk continuous_const :
      Continuous fun t : ℝ => ((TR.infEq ℚ (algebraMap ℝ (TR.Rinf ℚ) t), 0) :
        InfiniteAdeleRing ℚ × Af ℚ))
  have hadd : ∀ t x, unip (e t + x) = upR (aff 1 t) * unip x := fun t x => by
    rw [hx, hx, upR_aff, ← aff_add]; rfl
  have hψ : Continuous fun x : BlockIx 2 1 → Ad ℚ => φ.1 (unip x * g) := hφ.comp (hu.mul continuous_const)
  refine avgZero _ (ratN ℚ 2 1) μ D hμ hD _ hψ ?_ e he N (Nat.cast_pos.2 hN) fun x => ?_
  · rintro _ ⟨q, rfl⟩ x
    have : ∀ y : BlockIx 2 1 → Ad ℚ, y ⟨(0, 1), by decide⟩ = algebraMap ℚ (Ad ℚ) (q ⟨(0, 1), by decide⟩) →
        unip (y + x) = ratGL ℚ 2 (aff 1 (q ⟨(0, 1), by decide⟩)) * unip x := fun y hy => by
      rw [hx, hx, ratGL_aff, ← aff_add, ← hy]; rfl
    rw [this _ rfl, mul_assoc, hl]
  · obtain ⟨N', hN', hp', hz⟩ := hct (unip x * g)
    have ef : (fun t : ℝ => φ.1 (upR (aff 1 t) * (unip x * g))) = fun t => φ.1 (unip (e t + x) * g) :=
      funext fun t => by rw [hadd, mul_assoc]
    have hp : Function.Periodic (fun t : ℝ => φ.1 (upR (aff 1 t) * (unip x * g))) N := fun t => by
      have := hper (e t + x)
      rw [hadd, mul_assoc] at this
      beta_reduce
      rw [add_comm t, aff_add, map_mul, mul_assoc, this]
    rw [ef] at hp hp' hz
    exact two_periods (hψ.comp (he.add continuous_const)) hN' hp hp' hz
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Decomp
section
open NumberField Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V.Sd Matrix in
theorem UpperTheory.V.Af.Nf.decomp :
    UpperTheory.V.Af.Nf.Decomp := by
  intro M hM g
  obtain ⟨hK, hA⟩ := UpperTheory.V.Af.Nf.kOpen M hM
  obtain ⟨γ, h, y, u, hu, -, e⟩ := UpperTheory.V.Sd.strongApp ℚ _ hK g
  obtain ⟨r, u', -, hu', rfl⟩ := UpperTheory.V.Af.Nf.ratAd.1 y
  have h1 : aff (Units.map (algebraMap ℚ (Af ℚ)).toMonoidHom r * u') 0 = toF (aff r 0) * aff u' 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [aff, toF, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨γ * aff r 0, (toR (aff r 0))⁻¹ * GeneralLinearGroup.map ev h, aff u' 0 * u,
    mul_mem (hA u' hu' 0 (zero_mem _)) hu, ?_⟩
  rw [e, h1, ← upR_ev, map_mul (ratGL ℚ 2), ratGL_eq (aff r 0), upR_comm (toR _), map_mul upR, map_inv upR, mul_assoc (toF _), map_mul (finGL ℚ 2) (toF _),
    ← mul_assoc (upR _), upR_comm _ (toF _)]
  simp only [mul_assoc, mul_inv_cancel_left]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.LiftExp
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual
open GlobalTheory.CuspRep UpperTheory.V.Sd CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Matrix MatrixGroups ModularForm

namespace UpperTheory.V.Af.Nf

private theorem reAt_rat (v : InfinitePlace ℚ) (q : ℚ) : reAt v q = (q : ℝ) := by
  simp [reAt]

private theorem sum_f {k M : ℕ} (hM : 1 ≤ M) (f : CuspForm (Gamma1 M) (k : ℤ)) (τ : ℍ) :
    HasSum (fun n : ℕ => coef f (n + 1) * Complex.exp (2 * Real.pi * Complex.I * ((n + 1 : ℕ) * (τ : ℂ)))) (f τ) := by
  haveI : NeZero M := ⟨by omega⟩
  have hp : (1 : ℝ) ∈ (Gamma1 M : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  have h := hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f hp)
    f.holo' (ModularFormClass.bdd_at_infty f) τ
  have h0 : (qExpansion 1 f).coeff 0 = 0 := CuspFormClass.qExpansion_coeff_zero f one_pos hp
  rw [← hasSum_nat_add_iff' 1] at h
  simp only [Finset.range_one, Finset.sum_singleton, h0, zero_smul, sub_zero] at h
  refine cast (congrArg (HasSum · (f τ)) (funext fun n => ?_)) h
  rw [smul_eq_mul, Function.Periodic.qParam, ← Complex.exp_nat_mul, coef]
  congr 2
  push_cast
  ring

private theorem nsl_aff (k : ℕ) (f : ℍ → ℂ) (y : ℝˣ) (hy : 0 < (y : ℝ)) (x : ℝ) :
    nsl k f (aff y x : GL (Fin 2) ℝ) UpperHalfPlane.I =
      (((y : ℝ) ^ ((k : ℝ) / 2) : ℝ) : ℂ) * f (ofComplex ((x : ℂ) + Complex.I * (y : ℝ))) := by
  have hd : (aff y x : GL (Fin 2) ℝ).val.det = y := by simp [aff, Matrix.det_fin_two]
  rw [nsl, hd, abs_of_pos hy, sign_pos hy]
  simp [aff, add_comm, mul_comm]

private theorem pt_eq (x : TR.Rinf ℚ) (y : (TR.Rinf ℚ)ˣ) (r : ℚˣ) (u : (Af ℚ)ˣ) :
    TR.infGL ℚ 2 (aff y x) * finGL ℚ 2 (aff (Units.map (algebraMap ℚ (Af ℚ)).toMonoidHom r * u) 0) =
      ratGL ℚ 2 (aff r 0) * (upR (aff (Units.map ev.toMonoidHom y * (Units.map (Rat.castHom ℝ).toMonoidHom r)⁻¹)
        (ev x / (r : ℚ))) * finGL ℚ 2 (aff u 0)) := by
  have hr : ((r : ℚ) : ℝ) ≠ 0 := by exact_mod_cast r.ne_zero
  rw [ratGL_eq, mul_assoc, ← mul_assoc (finGL ℚ 2 _), ← upR_comm, mul_assoc, ← map_mul, ← mul_assoc, ← map_mul, ← upR_ev]
  congr 2
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [aff, toR, Matrix.mul_apply, Fin.sum_univ_succ] <;> field_simp
  · ext i j : 2
    fin_cases i <;> fin_cases j <;> simp [aff, toF, Matrix.mul_apply, Fin.sum_univ_succ]

end UpperTheory.V.Af.Nf

open UpperTheory.V.Af UpperTheory.V.Af.Nf in
theorem UpperTheory.V.Af.Nf.liftExp :
    UpperTheory.V.Af.Nf.LiftExp := by
  intro k M hM f φ hφ x y hy yf
  obtain ⟨r, u, hr, hu, rfl⟩ := ratAd.1 yf
  have hr' : (0 : ℝ) < ((r : ℚ) : ℝ) := by exact_mod_cast hr
  have hrc : (((r : ℚ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hy0 : 0 < ev y.val := hy _
  have hyv : ((Units.map ev.toMonoidHom y * (Units.map (Rat.castHom ℝ).toMonoidHom r)⁻¹ : ℝˣ) : ℝ) = ev y.val * ((r : ℚ) : ℝ)⁻¹ := by
    simp
  have hpos : 0 < ev y.val * ((r : ℚ) : ℝ)⁻¹ := by positivity
  have hprod : ∏ v, y.val v = ev y.val := Fintype.prod_subsingleton _ _
  rw [pt_eq, hφ _ _ _ ((kOpen M hM).2 u hu 0 (zero_mem _)), nsl_aff _ _ _ (hyv ▸ hpos), UpperTheory.V.Af.Nf.absF r hr u hu, hyv, hprod,
    mul_div_cancel_left₀ _ (by exact_mod_cast (Real.rpow_pos_of_pos hpos _).ne'), Pi.zero_apply, sub_zero]
  have him : 0 < (((ev x / (r : ℚ) : ℝ) : ℂ) + Complex.I * ((ev y.val * ((r : ℚ) : ℝ)⁻¹ : ℝ) : ℂ)).im := by
    simpa only [Complex.add_im, Complex.ofReal_im, Complex.I_mul_im, Complex.ofReal_re, zero_add] using hpos
  have hc : ∀ q : ℚ, 0 < q → UpperTheory.V.Sd.coefAt (icoef f) (algebraMap ℚ (Af ℚ) q *
      ((Units.map (algebraMap ℚ (Af ℚ)).toMonoidHom r * u : (Af ℚ)ˣ) : Af ℚ)) =
      if (q * r).den = 1 then coef f (q * r).num.toNat else 0 := fun q hq => by
    rw [← UpperTheory.V.Af.Nf.coefAt (coef f) (q * r) (mul_pos hq hr) u hu, map_mul, mul_assoc]
    rfl
  let j : ℕ → {ξ : ℚ // ∀ v, 0 < reAt v ξ} := fun n => ⟨((n + 1 : ℕ) : ℚ) / r, fun v => by
    rw [reAt_rat]; exact_mod_cast div_pos (by positivity) hr⟩
  have hj : Function.Injective j := fun a b h => by
    have := congrArg Subtype.val h
    simpa [j, hr.ne'] using this
  have hq : ∀ ξ : {ξ : ℚ // ∀ v, 0 < reAt v ξ}, 0 < ξ.1 := fun ξ => by
    have := ξ.2 Rat.infinitePlace
    rw [reAt_rat] at this
    exact_mod_cast this
  rw [← hj.hasSum_iff fun ξ hξ => ?_]
  · convert sum_f hM f (ofComplex _) using 2 with n
    rw [ofComplex_apply_of_im_pos him]
    have e : (j n).1 * r = ((n + 1 : ℕ) : ℚ) := div_mul_cancel₀ _ hr.ne'
    simp only [Function.comp]
    rw [hc _ (hq _), e, Fintype.sum_subsingleton _ Rat.infinitePlace, reAt_rat]
    simp only [Rat.den_natCast, Rat.num_natCast, Int.toNat_natCast, if_true]
    congr 3
    change ((((((n + 1 : ℕ) : ℚ) / r : ℚ) : ℝ)) : ℂ) * ((ev x : ℂ) + Complex.I * (ev y.val : ℂ)) = _
    push_cast
    ring
  · rw [hc _ (hq ξ), if_neg, zero_mul]
    intro hd
    have h1 : 0 < (ξ.1 * r).num := Rat.num_pos.2 (mul_pos (hq ξ) hr)
    refine hξ ⟨(ξ.1 * r).num.toNat - 1, Subtype.ext ?_⟩
    have h2 : (((ξ.1 * r).num.toNat - 1 + 1 : ℕ) : ℤ) = (ξ.1 * r).num := by omega
    change ((_ : ℕ) : ℚ) / r = _
    rw [← Int.cast_natCast, h2, Rat.coe_int_num_of_den_eq_one hd, mul_div_cancel_right₀ _ hr.ne']
end
end

