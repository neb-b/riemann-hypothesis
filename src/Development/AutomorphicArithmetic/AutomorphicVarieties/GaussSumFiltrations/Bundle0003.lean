module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.HCFFromRecipB
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0031

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EzOfComplex
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.QHol

open UpperHalfPlane hiding I

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def lin (ξ : F) : (InfinitePlace F → ℂ) →L[ℂ] ℂ :=
  ∑ v, (reAt v ξ : ℂ) • ContinuousLinearMap.proj v

theorem lin_apply (ξ : F) (z : InfinitePlace F → ℂ) : lin ξ z = ∑ v, (reAt v ξ : ℂ) * z v := by
  simp [lin]

def sm (ξ : F) : ℝ := ∑ v, reAt v ξ

theorem norm_lin_le (ξ : F) (h : ∀ v, 0 ≤ reAt v ξ) : ‖lin ξ‖ ≤ sm ξ := by
  have hs : 0 ≤ sm ξ := Finset.sum_nonneg (fun v _ => h v)
  refine ContinuousLinearMap.opNorm_le_bound _ hs (fun z => ?_)
  rw [lin_apply]
  calc ‖∑ v, (reAt v ξ : ℂ) * z v‖ ≤ ∑ v, ‖(reAt v ξ : ℂ) * z v‖ := norm_sum_le _ _
    _ ≤ ∑ v, reAt v ξ * ‖z‖ := by
      apply Finset.sum_le_sum
      intro v _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (h v)]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm z v) (h v)
    _ = sm ξ * ‖z‖ := by rw [sm, Finset.sum_mul]

theorem re_lin (ξ : F) (z : InfinitePlace F → ℂ) :
    (2 * Real.pi * Complex.I * lin ξ z).re = -(2 * Real.pi * ∑ v, reAt v ξ * (z v).im) := by
  rw [lin_apply]
  simp [Complex.mul_re, Complex.mul_im, Complex.im_sum, Finset.mul_sum]

theorem ez_ofComplex (ξ : F) (z : InfinitePlace F → ℂ) (hz : ∀ v, 0 < (z v).im) :
    ez ξ (fun v => ofComplex (z v)) = Complex.exp (2 * Real.pi * Complex.I * lin ξ z) := by
  simp only [ez, lin_apply]
  congr 2
  apply Finset.sum_congr rfl
  intro v _
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos (hz v)]

private theorem mul_exp_neg_le_exp_half (m x : ℝ) (hm : 0 < m) (hx : 0 ≤ x) :
    2 * Real.pi * x * Real.exp (-(2 * Real.pi * m * x)) ≤ (2 / m) * Real.exp (-(Real.pi * m * x)) := by
  set t := Real.pi * m * x with ht_def
  have ht : 0 ≤ t := by positivity
  have e : Real.exp (-(2 * Real.pi * m * x)) = Real.exp (-t) * Real.exp (-t) := by
    rw [← Real.exp_add]
    congr 1
    rw [ht_def]
    ring
  have hexp : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add]
    simp
  have key : t * Real.exp (-t) ≤ 1 := by
    have := Real.add_one_le_exp t
    nlinarith [Real.exp_pos (-t)]
  have hx2 : 2 * Real.pi * x = (2 / m) * t := by
    rw [ht_def]
    field_simp
  rw [e, hx2]
  have hE : 0 ≤ (2 / m) * Real.exp (-t) := by positivity
  calc 2 / m * t * (Real.exp (-t) * Real.exp (-t)) = (2 / m) * Real.exp (-t) * (t * Real.exp (-t)) := by ring
    _ ≤ (2 / m) * Real.exp (-t) * 1 := mul_le_mul_of_nonneg_left key hE
    _ = (2 / m) * Real.exp (-t) := by ring

theorem hol : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (f : Hn F → ℂ) (a : F → ℂ),
    HasQ f a → Hol f := by
  intro F _ _ _ f a hQ
  obtain ⟨⟨D, hD, hsupp⟩, hsum⟩ := hQ
  have hpos : ∀ ξ, a ξ ≠ 0 → ∀ v, 0 ≤ reAt v ξ := by
    intro ξ hξ v
    rcases (hsupp ξ hξ).1 with h0 | htp
    · subst h0
      simp [reAt]
    · exact (htp v).le
  have hsm : ∀ ξ, a ξ ≠ 0 → 0 ≤ sm ξ := fun ξ hξ => Finset.sum_nonneg (fun v _ => hpos ξ hξ v)
  unfold Hol
  intro z0 hz0
  have hz0' : ∀ v, 0 < (z0 v).im := hz0
  obtain ⟨m, hmz, hm⟩ : ∃ m : ℝ, (∀ v, m < (z0 v).im) ∧ 0 < m := by
    have h1 : ∀ᶠ m in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ v, m < (z0 v).im :=
      Filter.eventually_all.2 (fun v => eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds (hz0' v)))
    exact (h1.and self_mem_nhdsWithin).exists
  set s : Set (InfinitePlace F → ℂ) := {z | ∀ v, m < (z v).im} with hs_def
  have hsopen : IsOpen s := by
    rw [hs_def, Set.setOf_forall]
    exact isOpen_iInter_of_finite (fun v => isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_apply v)))
  have hsconv : Convex ℝ s := by
    intro x hx y hy p q hp hq hpq v
    have h1 := hx v
    have h2 := hy v
    simp only [Pi.add_apply, Pi.smul_apply, Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    have e : p * (x v).im + q * (y v).im - m = p * ((x v).im - m) + q * ((y v).im - m) := by
      have : m = p * m + q * m := by rw [← add_mul, hpq, one_mul]
      linarith
    by_cases hp0 : p = 0
    · have hq1 : q = 1 := by linarith
      subst hp0 hq1
      linarith
    · have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
      have := mul_pos hp' (sub_pos.2 h1)
      have := mul_nonneg hq (sub_pos.2 h2).le
      linarith
  have hz0s : z0 ∈ s := hmz
  have hpos_s : ∀ z ∈ s, ∀ v, 0 < (z v).im := fun z hz v => hm.trans (hz v)
  let g : F → (InfinitePlace F → ℂ) → ℂ := fun ξ z => a ξ * Complex.exp (2 * Real.pi * Complex.I * lin ξ z)
  let g' : F → (InfinitePlace F → ℂ) → ((InfinitePlace F → ℂ) →L[ℂ] ℂ) := fun ξ z =>
    a ξ • (Complex.exp (2 * Real.pi * Complex.I * lin ξ z) • ((2 * Real.pi * Complex.I) • lin ξ))
  let u : F → ℝ := fun ξ => ‖a ξ‖ * (2 * Real.pi * sm ξ * Real.exp (-(2 * Real.pi * m * sm ξ)))
  have hderiv : ∀ ξ z, z ∈ s → HasFDerivAt (g ξ) (g' ξ z) z := by
    intro ξ z _
    have h1 : HasFDerivAt (fun z => 2 * Real.pi * Complex.I * lin ξ z) ((2 * Real.pi * Complex.I) • lin ξ) z :=
      (lin ξ).hasFDerivAt.const_mul (2 * Real.pi * Complex.I)
    exact (h1.cexp).const_mul (a ξ)
  have hbound : ∀ ξ z, z ∈ s → ‖g' ξ z‖ ≤ u ξ := by
    intro ξ z hz
    by_cases ha : a ξ = 0
    · simp [g', u, ha]
    have hr := hpos ξ ha
    have hsum_le : m * sm ξ ≤ ∑ v, reAt v ξ * (z v).im := by
      rw [sm, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro v _
      have := hz v
      nlinarith [hr v]
    simp only [g', u, norm_smul, Complex.norm_exp, re_lin]
    have hc : ‖(2 * (Real.pi : ℂ) * Complex.I)‖ = 2 * Real.pi := by
      simp [Real.pi_pos.le]
    rw [hc]
    have hL := norm_lin_le ξ hr
    have hexp : Real.exp (-(2 * Real.pi * ∑ v, reAt v ξ * (z v).im)) ≤ Real.exp (-(2 * Real.pi * m * sm ξ)) := by
      apply Real.exp_le_exp.2
      nlinarith [Real.pi_pos]
    have hn : 0 ≤ ‖a ξ‖ := norm_nonneg _
    calc ‖a ξ‖ * (Real.exp (-(2 * Real.pi * ∑ v, reAt v ξ * (z v).im)) * (2 * Real.pi * ‖lin ξ‖))
        ≤ ‖a ξ‖ * (Real.exp (-(2 * Real.pi * m * sm ξ)) * (2 * Real.pi * sm ξ)) := by
          apply mul_le_mul_of_nonneg_left _ hn
          apply mul_le_mul hexp _ (by positivity) (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_left hL (by positivity)
      _ = ‖a ξ‖ * (2 * Real.pi * sm ξ * Real.exp (-(2 * Real.pi * m * sm ξ))) := by ring
  let w : Hn F := fun _ => UpperHalfPlane.ofComplex (Complex.I * ((m / 2 : ℝ) : ℂ))
  have hw_im : ∀ v : InfinitePlace F, 0 < ((fun _ => Complex.I * ((m / 2 : ℝ) : ℂ)) v : ℂ).im := by
    intro v
    simp
    linarith
  have hnw : ∀ ξ, ‖a ξ * ez ξ w‖ = ‖a ξ‖ * Real.exp (-(Real.pi * m * sm ξ)) := by
    intro ξ
    have := ez_ofComplex ξ (fun _ => Complex.I * ((m / 2 : ℝ) : ℂ)) hw_im
    rw [norm_mul, this, Complex.norm_exp, re_lin]
    congr 2
    simp [sm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  have hsw : Summable (fun ξ => ‖a ξ * ez ξ w‖) := (summable_norm_iff.2 (hsum w).summable)
  have hu : Summable u := by
    refine Summable.of_nonneg_of_le (fun ξ => ?_) (fun ξ => ?_) (hsw.mul_left (2 / m))
    · by_cases ha : a ξ = 0
      · simp [u, ha]
      · have := hsm ξ ha
        positivity
    · by_cases ha : a ξ = 0
      · simp [u, ha]
      · rw [hnw ξ]
        have := mul_exp_neg_le_exp_half m (sm ξ) hm (hsm ξ ha)
        calc u ξ = ‖a ξ‖ * (2 * Real.pi * sm ξ * Real.exp (-(2 * Real.pi * m * sm ξ))) := rfl
          _ ≤ ‖a ξ‖ * ((2 / m) * Real.exp (-(Real.pi * m * sm ξ))) := mul_le_mul_of_nonneg_left this (norm_nonneg _)
          _ = 2 / m * (‖a ξ‖ * Real.exp (-(Real.pi * m * sm ξ))) := by ring
  have hf0 : Summable (fun ξ => g ξ z0) := by
    refine (hsum (fun v => UpperHalfPlane.ofComplex (z0 v))).summable.congr (fun ξ => ?_)
    simp only [g]
    rw [ez_ofComplex ξ z0 hz0']
  have hT := hasFDerivAt_tsum_of_isPreconnected hu hsopen hsconv.isPreconnected hderiv hbound hz0s hf0 hz0s
  have heq : (fun z : InfinitePlace F → ℂ => f (fun v => UpperHalfPlane.ofComplex (z v))) =ᶠ[nhds z0]
      (fun y => ∑' ξ, g ξ y) := by
    filter_upwards [hsopen.mem_nhds hz0s] with y hy
    rw [← (hsum (fun v => UpperHalfPlane.ofComplex (y v))).tsum_eq]
    apply tsum_congr
    intro ξ
    simp only [g]
    rw [ez_ofComplex ξ y (hpos_s y hy)]
  exact (hT.differentiableAt.congr_of_eventuallyEq heq).differentiableWithinAt

end GlobalTheory.HilbertThetaSeries.QHol
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.FiniteNarrowIdeleClassesAndUnitsModSquares
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.NarrowCls

theorem exists_finset_mod_sq {G : Type} [CommGroup G] [Group.FG G] :
    ∃ E : Finset G, ∀ g : G, ∃ e ∈ E, ∃ h : G, g = e * h ^ 2 := by
  classical
  let H : Subgroup G := (powMonoidHom 2 : G →* G).range
  have hfin : Finite (G ⧸ H) := by
    apply CommGroup.finite_of_fg_torsion
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    refine (isOfFinOrder_iff_pow_eq_one).2 ⟨2, by norm_num, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨g, rfl⟩
  haveI := Fintype.ofFinite (G ⧸ H)
  refine ⟨Finset.univ.image (fun q : G ⧸ H => q.out), fun g => ?_⟩
  refine ⟨(g : G ⧸ H).out, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
  have h1 : ((g : G ⧸ H).out : G ⧸ H) = (g : G ⧸ H) := Quotient.out_eq' _
  rw [QuotientGroup.eq] at h1
  obtain ⟨h, hh⟩ := h1
  refine ⟨h, ?_⟩
  simp only [powMonoidHom_apply] at hh
  rw [hh, mul_inv_cancel_left]

variable {F : Type} [Field F] [NumberField F]

def finIdele : (Af F)ˣ →* Ideles F :=
  Units.map
    { toFun := fun x => (((1 : InfiniteAdeleRing F), x) : AdeleRing (𝓞 F) F)
      map_one' := rfl
      map_mul' := fun x y => Prod.ext (mul_one 1).symm rfl }

def finClass : (Af F)ˣ →* ClassGroup (𝓞 F) := (ReciprocityTheory.Neutral.Bridge.HCFR.classOf F).comp finIdele

theorem eq_of_finClass_eq_one (z : (Af F)ˣ) (hz : finClass z = 1) :
    ∃ (k : Fˣ) (u : (Af F)ˣ), (∀ w, Valued.v (pLoc F w (u : Af F)) = 1) ∧
      z = Units.map (algebraMap F (Af F)).toMonoidHom k * u := by
  obtain ⟨k, u', hu', he⟩ := (ReciprocityTheory.Neutral.Bridge.HCFR.classOf_eq_one_iff F (finIdele z)).1 hz
  have hsnd := congrArg (ReciprocityTheory.Neutral.Bridge.HCFR.sndU F) he
  rw [map_mul] at hsnd
  have hinv : ReciprocityTheory.Neutral.Bridge.HCFR.sndU F u' * ReciprocityTheory.Neutral.Bridge.HCFR.sndU F u'⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hinv' : ReciprocityTheory.Neutral.Bridge.HCFR.sndU F u'⁻¹ * ReciprocityTheory.Neutral.Bridge.HCFR.sndU F u' = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  refine ⟨k, ⟨_, _, hinv, hinv'⟩, ?_, ?_⟩
  · intro w
    exact (ReciprocityTheory.Neutral.Bridge.HCFR.rayUnits_top_iff F u').1 hu' w
  · ext1
    exact hsnd

variable [IsTotallyReal F]

theorem reAt_eq (v : InfinitePlace F) (x : F) :
    reAt v x = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x := by
  rw [reAt, ← InfinitePlace.embedding_of_isReal_apply]
  exact Complex.ofReal_re _


open Classical in
def sgn (k : Fˣ) : InfinitePlace F → Bool := fun v => decide (0 < reAt v (k : F))

theorem tp_of_sgn_eq (k σ : Fˣ) (h : sgn k = sgn σ) : TP ((k * σ⁻¹ : Fˣ) : F) := by
  intro v
  have hv := congrFun h v
  simp only [sgn, decide_eq_decide] at hv
  rw [reAt_eq] at hv ⊢
  set e := InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v)
  have hk : e (k : F) ≠ 0 := (map_ne_zero e).2 k.ne_zero
  have hs : e (σ : F) ≠ 0 := (map_ne_zero e).2 σ.ne_zero
  rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀]
  rcases lt_or_gt_of_ne hs with h1 | h1
  · have h2 : e (k : F) < 0 := by
      rcases lt_or_gt_of_ne hk with h3 | h3
      · exact h3
      · exact absurd (hv.1 h3) (not_lt.2 h1.le)
    exact mul_pos_of_neg_of_neg h2 (inv_lt_zero.2 h1)
  · exact mul_pos (hv.2 h1) (inv_pos.2 h1)

theorem narrowClass_unitsSq_finite : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F],
    (∃ Y : Finset (Af F)ˣ, ∀ z : (Af F)ˣ, ∃ y ∈ Y, ∃ (ξ : Fˣ) (u : (Af F)ˣ), TP (ξ : F) ∧
      (∀ w, Valued.v (pLoc F w (u : Af F)) = 1) ∧ z = Units.map (algebraMap F (Af F)).toMonoidHom ξ * y * u) ∧
    ∃ E : Finset (𝓞 F)ˣ, ∀ ε : (𝓞 F)ˣ, ∃ e ∈ E, ∃ η : (𝓞 F)ˣ, ε = e * η ^ 2 := by
  intro F _ _ _
  classical
  refine ⟨?_, ?_⟩
  · let Y0 : Finset (Af F)ˣ := Finset.univ.image
      (fun c : ClassGroup (𝓞 F) => if h : ∃ y, finClass y = c then h.choose else 1)
    let S : Finset Fˣ := Finset.univ.image
      (fun b : InfinitePlace F → Bool => if h : ∃ σ : Fˣ, sgn σ = b then h.choose else 1)
    let ι := Units.map (algebraMap F (Af F)).toMonoidHom
    refine ⟨(S ×ˢ Y0).image (fun p => ι p.1 * p.2), fun z => ?_⟩
    have hc : ∃ y, finClass y = finClass z := ⟨z, rfl⟩
    set y0 := hc.choose with hy0
    have hy0c : finClass y0 = finClass z := hc.choose_spec
    have hy0m : y0 ∈ Y0 := by
      refine Finset.mem_image.2 ⟨finClass z, Finset.mem_univ _, ?_⟩
      rw [dite_eq_left hc]
    obtain ⟨k, u, hu, hk⟩ := eq_of_finClass_eq_one (z * y0⁻¹) (by rw [map_mul, map_inv, hy0c, mul_inv_cancel])
    have hs : ∃ σ : Fˣ, sgn σ = sgn k := ⟨k, rfl⟩
    set σ := hs.choose with hσ
    have hσs : sgn σ = sgn k := hs.choose_spec
    have hσm : σ ∈ S := by
      refine Finset.mem_image.2 ⟨sgn k, Finset.mem_univ _, ?_⟩
      rw [dite_eq_left hs]
    refine ⟨ι σ * y0, Finset.mem_image.2 ⟨(σ, y0), Finset.mem_product.2 ⟨hσm, hy0m⟩, rfl⟩,
      k * σ⁻¹, u, tp_of_sgn_eq k σ hσs.symm, hu, ?_⟩
    have hz : z = ι k * u * y0 := by rw [← hk, inv_mul_cancel_right]
    show z = ι (k * σ⁻¹) * (ι σ * y0) * u
    rw [← mul_assoc, ← map_mul, inv_mul_cancel_right, mul_right_comm]
    exact hz
  · haveI : Group.FG (𝓞 F)ˣ := Group.fg_iff_monoid_fg.2 inferInstance
    exact exists_finset_mod_sq

end GlobalTheory.HilbertThetaSeries.NarrowCls

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_narrowIdeleClasses_and_units_mod_squares : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], (∃ Y : Finset (Af F)ˣ, ∀ z : (Af F)ˣ, ∃ y ∈ Y, ∃ (ξ : Fˣ) (u : (Af F)ˣ), TP (ξ : F) ∧ (∀ w, Valued.v (pLoc F w (u : Af F)) = 1) ∧ z = Units.map (algebraMap F (Af F)).toMonoidHom ξ * y * u) ∧ ∃ E : Finset (𝓞 F)ˣ, ∀ ε : (𝓞 F)ˣ, ∃ e ∈ E, ∃ η : (𝓞 F)ˣ, ε = e * η ^ 2 := by
  first | exact @GlobalTheory.HilbertThetaSeries.NarrowCls.narrowClass_unitsSq_finite | exact GlobalTheory.HilbertThetaSeries.NarrowCls.narrowClass_unitsSq_finite | (intros; apply GlobalTheory.HilbertThetaSeries.NarrowCls.narrowClass_unitsSq_finite <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.GenByTranslationsInversions
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries.GeneratorMatrix

theorem matId {F : Type} [Field F] (a b c d δ τ e s : F) (hδ : δ ≠ 0) (hs : s ≠ 0) (he : e ≠ 0)
    (hc : c = s - τ * δ * a) (hdet : a * d - b * c = e) :
    !![a, b; c, d] = !![0, -δ⁻¹; δ, 0] * !![1, τ / δ; 0, 1] * !![0, -(-δ)⁻¹; -δ, 0] * !![1, a / s; 0, 1]
      * !![0, -(s / e)⁻¹; s / e, 0] * !![1, (d + τ * δ * b) * e / s; 0, 1] * !![e, 0; 0, 1] := by
  subst hc
  simp only [Matrix.mul_fin_two]
  ext i j <;> fin_cases i <;> fin_cases j <;> simp <;> field_simp
  all_goals first | ring1 | linear_combination -hdet | linear_combination δ * τ * hdet

variable {F : Type} [Field F] [NumberField F]

theorem exists_place (p : ℕ) (hp : p.Prime) :
    ∃ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal :=
  _root_.UpperTheory.Reformulated.B.Qk8.exists_place p hp

theorem ne_zero_of_pUnit {p : ℕ} {w : HeightOneSpectrum (𝓞 F)} (hw : ((p : ℕ) : 𝓞 F) ∈ w.asIdeal) {x : F}
    (h : PUnit p x) : x ≠ 0 := by
  intro hx; have := h w hw; rw [hx, map_zero] at this; exact zero_ne_one this

theorem val_wm (c : Fˣ) : ((wm c : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, -(c : F)⁻¹; (c : F), 0] := by
  simp [wm]

theorem val_aff (y : Fˣ) (x : F) : ((aff y x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![(y : F), x; 0, 1] := rfl

end GlobalTheory.HilbertThetaSeries.GeneratorMatrix

namespace GlobalTheory.HilbertThetaSeries


open GlobalTheory.HilbertThetaSeries.GeneratorMatrix in
theorem gen_by_translations_inversions : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (p : ℕ), p.Prime → ∀ δ : F, IsDel p δ → ∀ γ : GL (Fin 2) F, InG p δ γ → ∃ (b₁ b₂ b₃ : F) (c₁ c₂ c₃ ε : Fˣ), PInt p (δ * b₁) ∧ PInt p (δ * b₂) ∧ PInt p (δ * b₃) ∧ PUnit p (c₁ / δ) ∧ PUnit p (c₂ / δ) ∧ PUnit p (c₃ / δ) ∧ TP (ε : F) ∧ γ = wm c₁ * aff 1 b₁ * wm c₂ * aff 1 b₂ * wm c₃ * aff 1 b₃ * aff ε 0 := by
  intro F _ _ _ p hp δ hδ γ hγ
  classical
  obtain ⟨hA, hB, hC, hD, hE, hT⟩ := hγ
  obtain ⟨w₀, hw₀⟩ := exists_place (F := F) p hp
  have hδ0 : δ ≠ 0 := by
    intro h; have := hδ w₀ hw₀; rw [h, map_zero] at this; exact WithZero.exp_ne_zero this.symm
  have hdet : γ.val 0 0 * γ.val 1 1 - γ.val 0 1 * γ.val 1 0 = γ.val.det := (Matrix.det_fin_two _).symm
  have he0 : γ.val.det ≠ 0 := ne_zero_of_pUnit hw₀ hE
  have hI : Ideal.span {((p : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  set S := (Ideal.finite_factors hI).toFinset with hS
  have hmem : ∀ w : HeightOneSpectrum (𝓞 F), ((p : ℕ) : 𝓞 F) ∈ w.asIdeal → w ∈ S := by
    intro w hw
    rw [hS, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]
    exact hw
  obtain ⟨τ, hτ⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun w => w.asIdeal) (fun _ => 1)
    (fun w _ => w.prime) (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h))
    (fun w => if w.1.valuation F (γ.val 1 0 / δ) = 1 then 0 else 1)
  set a := γ.val 0 0 with ha
  set b := γ.val 0 1 with hb
  set c := γ.val 1 0 with hc
  set d := γ.val 1 1 with hd
  set e := γ.val.det with he
  set t : F := algebraMap (𝓞 F) F τ with ht
  set s := c + t * δ * a with hs
  have hsd : s / δ = c / δ + t * a := by rw [hs]; field_simp
  have hu : PUnit p (s / δ) := by
    intro w hw
    have hτw := hτ w (hmem w hw)
    simp only [pow_one] at hτw
    rw [hsd]
    by_cases h1 : w.valuation F (c / δ) = 1
    · rw [if_pos h1, sub_zero] at hτw
      have htlt : w.valuation F t < 1 := (w.valuation_lt_one_iff_mem τ).mpr hτw
      have : w.valuation F (t * a) < 1 := by
        rw [map_mul]
        calc w.valuation F t * w.valuation F a ≤ w.valuation F t * 1 := mul_le_mul' le_rfl (hA w hw)
          _ < 1 := by rw [mul_one]; exact htlt
      rw [Valuation.map_add_eq_of_lt_left _ (h1 ▸ this), h1]
    · rw [if_neg h1] at hτw
      have hclt : w.valuation F (c / δ) < 1 := lt_of_le_of_ne (hC w hw) h1
      have hav : w.valuation F a = 1 := by
        by_contra hne
        have halt : w.valuation F a < 1 := lt_of_le_of_ne (hA w hw) hne
        have hE' := hE w hw
        have hx : e = a * d - (δ * b) * (c / δ) := by rw [← hdet]; field_simp
        have h1' : w.valuation F (a * d) < 1 := by
          rw [map_mul]
          calc w.valuation F a * w.valuation F d ≤ w.valuation F a * 1 := mul_le_mul' le_rfl (hD w hw)
            _ < 1 := by rw [mul_one]; exact halt
        have h2' : w.valuation F ((δ * b) * (c / δ)) < 1 := by
          rw [map_mul]
          calc w.valuation F (δ * b) * w.valuation F (c / δ) ≤ 1 * w.valuation F (c / δ) := mul_le_mul' (hB w hw) le_rfl
            _ < 1 := by rw [one_mul]; exact hclt
        have : w.valuation F e < 1 := by
          rw [hx]; exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h1' h2')
        rw [hE'] at this; exact lt_irrefl _ this
      have htm : w.valuation F (t - 1) < 1 := by
        have := (w.valuation_lt_one_iff_mem (K := F) (τ - 1)).mpr hτw
        simpa [ht] using this
      have htv : w.valuation F t = 1 := by
        have : t = 1 + (t - 1) := by ring
        rw [this, Valuation.map_add_eq_of_lt_left _ (by rw [map_one]; exact htm), map_one]
      have hta : w.valuation F (t * a) = 1 := by rw [map_mul, htv, hav, mul_one]
      rw [Valuation.map_add_eq_of_lt_right _ (hta ▸ hclt), hta]
  have hs0 : s ≠ 0 := by
    intro h0; exact ne_zero_of_pUnit hw₀ hu (by rw [h0, zero_div])
  refine ⟨t / δ, a / s, (d + t * δ * b) * e / s, Units.mk0 δ hδ0, -Units.mk0 δ hδ0,
    Units.mk0 (s / e) (div_ne_zero hs0 he0), Units.mk0 e he0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw; rw [mul_div_cancel₀ _ hδ0]; exact w.valuation_le_one τ
  · intro w hw
    have : δ * (a / s) = a / (s / δ) := by field_simp
    rw [this, map_div₀, hu w hw, div_one]; exact hA w hw
  · intro w hw
    have : δ * ((d + t * δ * b) * e / s) = (d + t * (δ * b)) * e / (s / δ) := by field_simp
    rw [this, map_div₀, hu w hw, div_one, map_mul, hE w hw, mul_one]
    refine Valuation.map_add_le _ (hD w hw) ?_
    rw [map_mul]
    calc w.valuation F t * w.valuation F (δ * b) ≤ 1 * 1 :=
          mul_le_mul' (w.valuation_le_one τ) (hB w hw)
      _ = 1 := one_mul 1
  · intro w hw; rw [Units.val_mk0, div_self hδ0, map_one]
  · intro w hw; rw [Units.val_neg, Units.val_mk0, neg_div, div_self hδ0, Valuation.map_neg, map_one]
  · intro w hw
    have : s / e / δ = s / δ / e := by ring
    rw [Units.val_mk0, this, map_div₀, hu w hw, hE w hw, div_one]
  · rw [Units.val_mk0]; exact hT
  · refine Units.ext ?_
    simp only [Units.val_mul, val_wm, val_aff, Units.val_neg, Units.val_mk0, Units.val_one]
    rw [Matrix.eta_fin_two (γ : Matrix (Fin 2) (Fin 2) F)]
    exact matId a b c d δ t e s hδ0 hs0 he0 (by rw [hs]; ring) hdet

end GlobalTheory.HilbertThetaSeries
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.SlashAddSmulPow
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

namespace GlobalTheory.HilbertThetaSeries

theorem slash_add_smul_pow : ∀ (F : Type) [Field F] [NumberField F] (k M : ℕ) (h : GL (Fin 2) (InfinitePlace F → ℝ)) (f g : Hn F → ℂ) (c : ℂ), sl0 k h (f + g) = sl0 k h f + sl0 k h g ∧ sl0 k h (c • f) = c • sl0 k h f ∧ sl0 (k * M) h (f ^ M) = sl0 k h f ^ M ∧ sl k h (f + g) = sl k h f + sl k h g ∧ sl k h (c • f) = c • sl k h f ∧ sl (k * M) h (f ^ M) = sl k h f ^ M := by
  intro F _ _ k M h f g c
  have h0a : sl0 k h (f + g) = sl0 k h f + sl0 k h g := by
    funext z; simp only [sl0, Pi.add_apply]; ring
  have h0s : sl0 k h (c • f) = c • sl0 k h f := by
    funext z; simp only [sl0, Pi.smul_apply, smul_eq_mul]; ring
  have h0p : sl0 (k * M) h (f ^ M) = sl0 k h f ^ M := by
    funext z; simp only [sl0, Pi.pow_apply]; rw [mul_pow, pow_mul]
  refine ⟨h0a, h0s, h0p, ?_, ?_, ?_⟩
  · funext z; simp only [sl, h0a, Pi.add_apply]; ring
  · funext z; simp only [sl, h0s, Pi.smul_apply, smul_eq_mul]; ring
  · funext z
    simp only [sl, h0p, Pi.pow_apply]
    rw [mul_pow]
    congr 1
    have hx : (0 : ℝ) ≤ ∏ v, |(h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v| :=
      Finset.prod_nonneg fun v _ => abs_nonneg _
    rw [← Complex.ofReal_pow, ← Real.rpow_mul_natCast hx]
    congr 2
    push_cast; ring

end GlobalTheory.HilbertThetaSeries
end

