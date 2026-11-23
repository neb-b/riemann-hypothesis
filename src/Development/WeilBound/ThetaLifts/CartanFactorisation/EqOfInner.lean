module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation

@[expose] public section

noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil
open scoped Real RealInnerProductSpace FourierTransform

namespace PositivityTheory.ThKF.E

variable {l : Type} [Fintype l] [DecidableEq l]

structure Impl (s : (l ⊕ l → ℝ) → (l ⊕ l → ℝ)) (S : Sch l →ₗ[ℂ] Sch l) : Prop where
  norm : ∀ f, ‖(S f).toLp 2 volume‖ = ‖f.toLp 2 volume‖
  impl : ∀ w (f g : Sch l), ⇑g = rhoFun w f → ⇑(S g) = rhoFun (s w) (S f)

theorem Impl.inner {s} {S : Sch l →ₗ[ℂ] Sch l} (h : Impl s S) (f g : Sch l) :
    inner ℂ ((S f).toLp 2 volume) ((S g).toLp 2 volume) = inner ℂ (f.toLp 2 volume) (g.toLp 2 volume) := by
  have e : ∀ (u v : Sch l) (c : ℂ), u.toLp 2 volume + c • v.toLp 2 volume = (u + c • v).toLp 2 volume := fun u v c => by
    simp only [← schwartzToL2_apply, map_add (f := _), map_smul]
  have e' : ∀ (u v : Sch l) (c : ℂ), u.toLp 2 volume - c • v.toLp 2 volume = (u - c • v).toLp 2 volume := fun u v c => by
    simp only [← schwartzToL2_apply, map_sub, map_smul]
  have e1 := e (S f) (S g) 1
  have e2 := e' (S f) (S g) 1
  have e3 := e f g 1
  have e4 := e' f g 1
  simp only [one_smul] at e1 e2 e3 e4
  rw [inner_eq_sum_norm_sq_div_four, inner_eq_sum_norm_sq_div_four, e1, e2, e3, e4, e, e, e', e', ← map_add (f := _), ← map_sub,
    ← map_smul, ← map_add, ← map_sub, h.norm, h.norm, h.norm, h.norm]

theorem exists_rho (w : l ⊕ l → ℝ) (f : Sch l) : ∃ g : Sch l, ⇑g = rhoFun w f := by
  have ht : Function.HasTemperateGrowth (phase w) := by
    have h2 : Function.HasTemperateGrowth fun x : EuclideanSpace ℝ l => ⟪qPart w, x⟫ + ⟪pPart w, qPart w⟫ / 2 :=
      (innerSL ℝ (qPart w)).hasTemperateGrowth.add (Function.HasTemperateGrowth.const _)
    have h3 := GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp h2
    convert h3 using 1
    funext x
    simp only [phase, Function.comp_apply, GlobalTheory.Published.Metaplectic.eChar_apply]
    congr 1
    push_cast
    ring
  refine ⟨smulLeftCLM ℂ (phase w) (compSubConstCLM ℂ (-pPart w) f), ?_⟩
  funext x
  rw [smulLeftCLM_apply_apply ht]
  simp [rhoFun]

theorem toLp_rho {w : l ⊕ l → ℝ} {f g : Sch l} (h : ⇑g = rhoFun w f) : g.toLp 2 volume = rho w (f.toLp 2 volume) := by
  refine Lp.ext ((g.coeFn_toLp 2 volume).trans ?_)
  rw [h]
  exact ((coeFn_rho w _).trans (rhoFun_congr w (f.coeFn_toLp 2 volume))).symm

theorem eq_of_inner {u v : Sch l} (h : ∀ φ : Sch l, inner ℂ (φ.toLp 2 volume) (u.toLp 2 volume) =
    inner ℂ (φ.toLp 2 volume) (v.toLp 2 volume)) : u = v := by
  apply injective_toLp 2 volume
  have := h (u - v)
  rw [← sub_eq_zero, ← inner_sub_right, ← toLpCLM_apply (𝕜 := ℂ), map_sub] at this
  exact sub_eq_zero.1 (inner_self_eq_zero.1 this)

theorem Impl.dRho {s : (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ)} {S : Sch l →ₗ[ℂ] Sch l} (h : Impl s S)
    (hs : Function.Surjective S) (w : l ⊕ l → ℝ) (f : Sch l) : S (dRho w f) = dRho (s w) (S f) := by
  refine eq_of_inner fun φ => ?_
  obtain ⟨φ', rfl⟩ := hs φ
  have d1 := hasDerivAt_inner_rho w φ' f
  have d2 := hasDerivAt_inner_rho (s w) (S φ') (S f)
  rw [h.inner]
  refine d1.unique (d2.congr_of_eventuallyEq (.of_forall fun t => ?_))
  obtain ⟨g, hg⟩ := exists_rho (t • w) f
  simp only
  rw [← toLp_rho hg, ← map_smul, ← toLp_rho (h.impl _ _ _ hg), h.inner]

theorem Impl.continuous {s : (l ⊕ l → ℝ) ≃ₗ[ℝ] (l ⊕ l → ℝ)} {S : Sch l →ₗ[ℂ] Sch l} (h : Impl s S)
    (hs : Function.Surjective S) : Continuous S := by
  have hA : ∀ A ∈ weylAlg l, ∃ A' : Sch l →L[ℂ] Sch l, ∀ f, A (S f) = S (A' f) := fun A hA => by
    refine weylAlg_induction (P := fun A => ∃ A' : Sch l →L[ℂ] Sch l, ∀ f, A (S f) = S (A' f)) ⟨1, fun _ => rfl⟩ ?_
      ⟨0, fun f => by simp⟩ ?_ ?_ hA
    · rintro A w ⟨A', h'⟩
      refine ⟨A' * GlobalTheory.RealWeil.dRho (s.symm w), fun f => ?_⟩
      have := Impl.dRho (s := s.toLinearMap) h hs (s.symm w) f
      simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at this
      rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, ← this, h']
    · rintro A B ⟨A', h1⟩ ⟨B', h2⟩
      exact ⟨A' + B', fun f => by simp [h1, h2]⟩
    · rintro c A ⟨A', h1⟩
      exact ⟨c • A', fun f => by simp [h1]⟩
  refine (schwartz_withSeminorms ℂ (EuclideanSpace ℝ l) ℂ).continuous_of_continuous_comp S fun kn => ?_
  obtain ⟨A, hAm, hb⟩ := exists_seminorm_le (l := l) kn.1 kn.2
  choose A' hA' using fun r => hA _ (hAm r)
  refine Seminorm.continuous_of_continuousAt_zero (𝕝 := ℂ) ?_
  have hc : Continuous fun f : Sch l => ∑ r, ‖schwartzToL2 l (A' r f)‖ := by fun_prop
  have h0 := hc.tendsto 0
  simp only [map_zero, norm_zero, Finset.sum_const_zero] at h0
  rw [ContinuousAt, map_zero]
  refine squeeze_zero (fun f => apply_nonneg _ _) (fun f => ?_) h0
  have := hb (S f)
  simp only [hA', h.norm] at this
  exact this

theorem exists_ne_zero (x : EuclideanSpace ℝ l) : ∃ φ : Sch l, φ x ≠ 0 := by
  obtain ⟨f, h1, h2, h3, -, h4⟩ := exists_contDiff_tsupport_subset (n := ⊤) (s := Set.univ) (x := x) Filter.univ_mem
  refine ⟨(h2.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)).toSchwartzMap (ofRealCLM.contDiff.comp h3), ?_⟩
  show ((f x : ℝ) : ℂ) ≠ 0
  simp [h4]

theorem Impl.scalar {S : Sch l →ₗ[ℂ] Sch l} (h : Impl id S) (hs : Function.Surjective S) : ∃ c : ℂ, ∀ f, S f = c • f := by
  have h1 : ∀ (φ f : Sch l) x, (starRingEnd ℂ) (S φ x) * S f x = (starRingEnd ℂ) (φ x) * f x := fun φ f x => by
    have key : ∀ (a b : Sch l) (q : EuclideanSpace ℝ l) (g : Sch l), ⇑g = rhoFun (Sum.elim 0 fun i => -q i) b →
        Inner.inner ℂ (a.toLp 2 volume) (g.toLp 2 volume) = 𝓕 (fun x => (starRingEnd ℂ) (a x) * b x) q := fun a b q g hg => by
      rw [toLp_rho hg, inner_toLp_rho, Real.fourier_eq']
      refine integral_congr_ae (.of_forall fun y => ?_)
      have e1 : pPart (l := l) (Sum.elim 0 fun i => -q i) = 0 := rfl
      have e2 : qPart (l := l) (Sum.elim 0 fun i => -q i) = -q := rfl
      simp only [rhoFun, phase, e1, e2, inner_zero_left, mul_zero, add_zero, inner_neg_left, smul_eq_mul, RCLike.inner_apply,
        real_inner_comm y q]
      push_cast
      ring_nf
    have hi : ∀ a b : Sch l, Integrable (fun x => (starRingEnd ℂ) (a x) * b x) ∧
        Continuous (fun x => (starRingEnd ℂ) (a x) * b x) := fun a b =>
      ⟨b.integrable.bdd_mul (c := SchwartzMap.seminorm ℂ 0 0 a) (continuous_conj.comp a.continuous).aestronglyMeasurable
        (.of_forall fun x => by simpa using a.norm_le_seminorm ℂ x), (continuous_conj.comp a.continuous).mul b.continuous⟩
    set u := fun x => (starRingEnd ℂ) (S φ x) * S f x - (starRingEnd ℂ) (φ x) * f x with hu
    have hz : 𝓕 u = 0 := by
      funext q
      obtain ⟨g, hg⟩ := exists_rho (Sum.elim 0 fun i => -q i) f
      have := h.inner φ g
      rw [key _ _ q _ (h.impl _ _ _ hg), key _ _ q _ hg, Real.fourier_eq', Real.fourier_eq'] at this
      rw [Real.fourier_eq', hu]
      simp only [smul_sub]
      have hb : ∀ a b : Sch l, Integrable fun v => cexp (((-2 * π * ⟪v, q⟫ : ℝ) : ℂ) * I) • ((starRingEnd ℂ) (a v) * b v) :=
        fun a b => (hi a b).1.bdd_mul (c := 1) (by fun_prop) (.of_forall fun v => (norm_exp_ofReal_mul_I _).le)
      rw [integral_sub (hb _ _) (hb _ _), this, sub_self]
      rfl
    have := Continuous.fourierInv_fourier_eq (f := u) ((hi _ _).2.sub (hi _ _).2) ((hi _ _).1.sub (hi _ _).1)
      (by rw [hz]; exact integrable_zero _ _ _)
    rw [hz] at this
    have h3 := congrFun this x
    rw [Real.fourierInv_eq] at h3
    simp only [Pi.zero_apply, smul_zero, integral_zero] at h3
    exact sub_eq_zero.1 h3.symm
  have h2 : ∀ x, ∃ m : ℂ, ∀ f : Sch l, S f x = m * f x := fun x => by
    obtain ⟨φ, hφ⟩ := exists_ne_zero x
    obtain ⟨φ', rfl⟩ := hs φ
    have hn : (starRingEnd ℂ) (S φ' x) ≠ 0 := by simpa using hφ
    refine ⟨(starRingEnd ℂ) (φ' x) / (starRingEnd ℂ) (S φ' x), fun f => ?_⟩
    rw [div_mul_eq_mul_div, eq_div_iff hn, mul_comm, h1]
  obtain ⟨m, hm⟩ := h2 0
  refine ⟨m, fun f => SchwartzMap.ext fun x => ?_⟩
  obtain ⟨g, hg⟩ := exists_rho (Sum.elim (fun i => x i) 0) f
  have e1 : pPart (l := l) (Sum.elim (fun i => x i) 0) = x := rfl
  have e2 : qPart (l := l) (Sum.elim (fun i => x i) 0) = 0 := rfl
  have := hm g
  rw [h.impl _ _ _ hg, hg] at this
  simpa [rhoFun, phase, e1, e2] using this

theorem quad_mem (X : Matrix (l ⊕ l) (l ⊕ l) ℝ) : quad X ∈ weylAlg l :=
  Subalgebra.smul_mem _ (sum_mem fun _ _ => sum_mem fun _ _ => Subalgebra.smul_mem _
    (add_mem (mul_mem (dRho_mem_weylAlg _) (dRho_mem_weylAlg _)) (mul_mem (dRho_mem_weylAlg _) (dRho_mem_weylAlg _))) _) _

theorem sympl_eq (w u : l ⊕ l → ℝ) : sympl w u = -(w ⬝ᵥ Matrix.J l ℝ *ᵥ u) := by
  simp [sympl, pPart, qPart, PiLp.inner_apply, Matrix.J, mulVec, dotProduct, Matrix.one_apply, Fintype.sum_sum_type,
    mul_comm, sub_eq_add_neg, add_comm]

end PositivityTheory.ThKF.E
