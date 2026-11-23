module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0014
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeM
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M Topology Filter Set

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ} (R : AnLogRes P J e)

theorem ram_null' (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | Ψ (segre (R.lift x x)) 0 ≠ 0 ∧
      ∃ k, x ∈ (R.A.chart k).source ∧
        LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart k).symm) (R.A.chart k x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0}) = 0 := by
  apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
  rintro u0 ⟨hu0, h00, -⟩
  set x0 := (R.A.chart j).symm u0
  set V := (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x0 with hVdef
  have hV : IsOpen V := (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x0)
  have hgc : ContinuousOn (fun u => Ψ (segre (R.lift x0 ((R.A.chart j).symm u))) 0) V :=
    fun u hu => (analyticAt_pi_iff.mp (analyticAt_segre_lift R Ψ x0 j hu) 0).continuousAt.continuousWithinAt
  set O := V ∩ (fun u => Ψ (segre (R.lift x0 ((R.A.chart j).symm u))) 0) ⁻¹' {0}ᶜ with hOdef
  have hO : IsOpen O := hgc.isOpen_inter_preimage hV isOpen_compl_singleton
  have hu0O : u0 ∈ O := ⟨⟨hu0, R.mem_U x0⟩, h00⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO u0 hu0O
  have h0 : ∀ u ∈ Metric.ball u0 r,
      Ψ (segre (R.lift ((R.A.chart j).symm u) ((R.A.chart j).symm u))) 0 ≠ 0 := by
    intro u hu
    obtain ⟨μ, hμ, hμeq⟩ := psi_lift_eq R (hball hu).1.2 Ψ
    rw [hμeq, Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero hμ (hball hu).2
  have hQa : AnalyticOnNhd ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (Metric.ball u0 r) := by
    intro u hu
    have := analyticAt_brQ R Ψ _ j ((R.A.chart j).map_target (hball hu).1.1) (h0 u hu)
    rwa [(R.A.chart j).right_inv (hball hu).1.1] at this
  refine ⟨Metric.ball u0 r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball u0 r).isPreconnected, fun u => LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart j).symm) u :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)), fun u hu => analyticAt_det_fderiv (hQa u hu), ?_, ?_⟩
  · by_contra hall
    push Not at hall
    exact not_flat R Ψ hP hΨ j Metric.isOpen_ball (fun u hu => (hball hu).1.1)
      ⟨u0, Metric.mem_ball_self hr⟩ h0 hQa hall
  · rintro w ⟨⟨hwt, hw0, k, hk, hdk⟩, -⟩
    have := det_brQ_chart R Ψ (j := j) ((R.A.chart j).map_target hwt) hk hw0
    rw [(R.A.chart j).right_inv hwt] at this
    show LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart j).symm) w :
      (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0
    rw [this, hdk, zero_mul]

theorem volume_projection_zeroSet_null (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩
      (R.A.chart j).symm ⁻¹' {x | Ψ (segre (R.lift x x)) 0 = 0}) = 0 := by
  classical
  apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
  rintro u0 ⟨hu0, -⟩
  set x0 := (R.A.chart j).symm u0
  set V := (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x0 with hVdef
  have hV : IsOpen V := (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x0)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV u0 ⟨hu0, R.mem_U x0⟩
  set f : (Fin e → ℂ) → ℂ := fun u => Ψ (segre (R.lift x0 ((R.A.chart j).symm u))) 0 with hfdef
  have hfa : AnalyticOnNhd ℂ f V := fun u hu =>
    analyticAt_pi_iff.mp (analyticAt_segre_lift R Ψ x0 j hu) 0
  refine ⟨Metric.ball u0 r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball u0 r).isPreconnected, f, hfa.mono hball, ?_, ?_⟩
  · by_contra hall
    push Not at hall
    have hgood := hΨ _ (R.mem x0 x0 (R.mem_U x0))
    obtain ⟨i0, hi0⟩ : ∃ i0, Ψ (segre (R.lift x0 x0)) i0 ≠ 0 := by
      by_contra h
      push Not at h
      exact hgood (funext h)
    have hi0ne : i0 ≠ 0 := by
      rintro rfl
      exact hi0 (hall u0 (Metric.mem_ball_self hr))
    set m : Fin e := i0.pred hi0ne
    have hm : m.succ = i0 := Fin.succ_pred i0 hi0ne
    set Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ) :=
      (LinearMap.funLeft ℂ ℂ (Equiv.swap (0 : Fin (e + 1)) i0)).comp Ψ with hΨ'def
    have hΨ'app : ∀ w i, Ψ' w i = Ψ w (Equiv.swap 0 i0 i) := fun w i => rfl
    have hΨ' : IsGoodProj P Ψ' := by
      intro z hz h
      refine hΨ z hz (funext fun i => ?_)
      have := congrFun h (Equiv.swap 0 i0 i)
      rw [hΨ'app, Equiv.swap_apply_self] at this
      exact this
    have hg'c : ContinuousOn (fun u => Ψ' (segre (R.lift x0 ((R.A.chart j).symm u))) 0)
        (Metric.ball u0 r) := fun u hu =>
      (analyticAt_pi_iff.mp (analyticAt_segre_lift R Ψ' x0 j (hball hu)) 0).continuousAt.continuousWithinAt
    set O := Metric.ball u0 r ∩
      (fun u => Ψ' (segre (R.lift x0 ((R.A.chart j).symm u))) 0) ⁻¹' {0}ᶜ with hOdef
    have hO : IsOpen O := hg'c.isOpen_inter_preimage Metric.isOpen_ball isOpen_compl_singleton
    have hu0O : u0 ∈ O := by
      refine ⟨Metric.mem_ball_self hr, ?_⟩
      show Ψ' (segre (R.lift x0 x0)) 0 ≠ 0
      rw [hΨ'app, Equiv.swap_apply_left]
      exact hi0
    have h0O : ∀ u ∈ O,
        Ψ' (segre (R.lift ((R.A.chart j).symm u) ((R.A.chart j).symm u))) 0 ≠ 0 := by
      intro u hu
      obtain ⟨μ, hμ, hμeq⟩ := psi_lift_eq R (hball hu.1).2 Ψ'
      rw [hμeq, Pi.smul_apply, smul_eq_mul]
      exact mul_ne_zero hμ hu.2
    have hanO : AnalyticOnNhd ℂ (brQ R Ψ' ∘ (R.A.chart j).symm) O := by
      intro u hu
      have := analyticAt_brQ R Ψ' _ j ((R.A.chart j).map_target (hball hu.1).1) (h0O u hu)
      rwa [(R.A.chart j).right_inv (hball hu.1).1] at this
    have hzero : ∀ u ∈ O, (brQ R Ψ' ∘ (R.A.chart j).symm) u m = 0 := by
      intro u hu
      simp only [Function.comp_apply, brQ]
      rw [hm, hΨ'app, Equiv.swap_apply_right]
      obtain ⟨μ, hμ, hμeq⟩ := psi_lift_eq R (hball hu.1).2 Ψ
      rw [hμeq, Pi.smul_apply, smul_eq_mul]
      have : f u = 0 := hall u hu.1
      simp only [hfdef] at this
      rw [this, mul_zero, zero_div]
    have hdetO : ∀ u ∈ O, LinearMap.det (fderiv ℂ (brQ R Ψ' ∘ (R.A.chart j).symm) u :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) = 0 := by
      intro u hu
      have hcoord : (fun v => (brQ R Ψ' ∘ (R.A.chart j).symm) v m) =ᶠ[𝓝 u] fun _ => 0 := by
        filter_upwards [hO.mem_nhds hu] with v hv
        exact hzero v hv
      have hd : HasFDerivAt (fun v => (brQ R Ψ' ∘ (R.A.chart j).symm) v m)
          ((ContinuousLinearMap.proj m).comp (fderiv ℂ (brQ R Ψ' ∘ (R.A.chart j).symm) u)) u :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) m).hasFDerivAt.comp u
          (hanO u hu).differentiableAt.hasFDerivAt
      have hd0 : HasFDerivAt (fun v => (brQ R Ψ' ∘ (R.A.chart j).symm) v m)
          (0 : (Fin e → ℂ) →L[ℂ] ℂ) u :=
        (hasFDerivAt_const (0 : ℂ) u).congr_of_eventuallyEq hcoord
      have hrow := hd.unique hd0
      refine det_eq_zero_of_coord m fun v => ?_
      have := congrArg (fun T : (Fin e → ℂ) →L[ℂ] ℂ => T v) hrow
      simpa using this
    exact not_flat R Ψ' hP hΨ' j hO (fun u hu => (hball hu.1).1) ⟨u0, hu0O⟩ h0O hanO hdetO
  · rintro w ⟨⟨hwt, hw0⟩, hwb⟩
    obtain ⟨μ, hμ, hμeq⟩ := psi_lift_eq R (hball hwb).2 Ψ
    have := congrFun hμeq 0
    rw [Pi.smul_apply, smul_eq_mul] at this
    have hw0' : Ψ (segre (R.lift ((R.A.chart j).symm w) ((R.A.chart j).symm w))) 0 = 0 := hw0
    rw [hw0'] at this
    exact (mul_eq_zero.mp this.symm).resolve_left hμ

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeO
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory

def NormPolyStatement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (f : MRing ι) (a : K → ℕ),
    IsArithVar P (e + 1) → IsGoodProj P Ψ → IsMultiHomog f a → f ∉ P →
    ∃ (c : MvPolynomial (Fin (e + 1)) ℂ) (m : ℕ), c ≠ 0 ∧ c.IsHomogeneous m ∧
      ∀ z ∈ mcPts P, eval z (map (Int.castRingHom ℂ) f) = 0 → eval (Ψ (segre z)) c = 0

theorem eval_smul_of_isHomogeneous {n : ℕ} {c : MvPolynomial (Fin n) ℂ} {m : ℕ}
    (hc : c.IsHomogeneous m) (t : ℂ) (v : Fin n → ℂ) :
    eval (fun i => t * v i) c = t ^ m * eval v c := by
  conv_lhs => rw [c.as_sum]
  conv_rhs => rw [c.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.mul_sum, eval_monomial]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = m := by
    have h1 := hc (mem_support_iff.mp hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using h1
  simp only [mul_pow, Finsupp.prod_mul]
  rw [show (d.prod fun _ e => t ^ e) = t ^ m by
    rw [Finsupp.prod, Finset.prod_pow_eq_pow_sum, hdeg]]
  ring

theorem exists_eval_cons_ne_zero {n : ℕ} {c : MvPolynomial (Fin (n + 1)) ℂ} {m : ℕ}
    (hc0 : c ≠ 0) (hc : c.IsHomogeneous m) : ∃ y : Fin n → ℂ, eval (Fin.cons 1 y) c ≠ 0 := by
  by_contra h
  push Not at h
  apply hc0
  have hX : (X 0 : MvPolynomial (Fin (n + 1)) ℂ) * c = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_mul, eval_X, map_zero]
    by_cases hx : x 0 = 0
    · rw [hx, zero_mul]
    · have hxe : x = fun i => x 0 * (Fin.cons 1 (fun j => x j.succ / x 0) : Fin (n + 1) → ℂ) i := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp
        · rw [Fin.cons_succ, mul_div_left_comm, div_self hx, mul_one]
      have hx0 : eval x c = 0 := by
        rw [hxe, eval_smul_of_isHomogeneous hc (x 0) (Fin.cons 1 (fun j => x j.succ / x 0)), h,
          mul_zero]
      rw [hx0, mul_zero]
  rcases mul_eq_zero.mp hX with h0 | h0
  · exact absurd h0 (X_ne_zero 0)
  · exact h0

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}

private theorem volume_eval_eq_zero_lemma :
    ∀ (n : ℕ) (p : MvPolynomial (Fin n) ℂ), p ≠ 0 → volume {y : Fin n → ℂ | eval y p = 0} = 0 := by
  intro n
  induction n with
  | zero =>
    intro p hp
    refine measure_mono_null (fun y hy => ?_) measure_empty
    exfalso
    apply hp
    apply MvPolynomial.funext
    intro x
    have hxy : x = y := Subsingleton.elim _ _
    subst hxy
    simpa using hy
  | succ n ih =>
    intro p hp
    have hq0 : finSuccEquiv ℂ n p ≠ 0 := by
      intro h
      apply hp
      apply (finSuccEquiv ℂ n).injective
      rw [h, map_zero]
    have hbad := ih _ (Polynomial.leadingCoeff_ne_zero.mpr hq0)
    let E := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℂ) 0
    have hE : MeasurePreserving E (Measure.pi fun _ => (volume : Measure ℂ))
        ((volume : Measure ℂ).prod (Measure.pi fun _ : Fin n => (volume : Measure ℂ))) :=
      measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure ℂ)) 0
    have hC : MeasurableSet {y : Fin (n + 1) → ℂ | eval y p = 0} :=
      (isClosed_eq (MvPolynomial.continuous_eval p) continuous_const).measurableSet
    have hT : MeasurableSet (E.symm ⁻¹' {y : Fin (n + 1) → ℂ | eval y p = 0}) :=
      E.symm.measurable hC
    have hS : {y : Fin (n + 1) → ℂ | eval y p = 0} =
        E ⁻¹' (E.symm ⁻¹' {y : Fin (n + 1) → ℂ | eval y p = 0}) := by
      ext x
      simp only [Set.mem_preimage, MeasurableEquiv.symm_apply_apply]
    show (Measure.pi fun _ => (volume : Measure ℂ)) _ = 0
    rw [hS, hE.measure_preimage_equiv, Measure.prod_apply_symm hT]
    have hae : ∀ᵐ s ∂(Measure.pi fun _ : Fin n => (volume : Measure ℂ)),
        eval s (finSuccEquiv ℂ n p).leadingCoeff ≠ 0 :=
      ae_iff.2 (by
        have hbad' : (Measure.pi fun _ : Fin n => (volume : Measure ℂ))
            {y | eval y (finSuccEquiv ℂ n p).leadingCoeff = 0} = 0 := hbad
        simpa using hbad')
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hae] with s hs
    have hmap : (finSuccEquiv ℂ n p).map (eval s) ≠ 0 := by
      intro h0
      apply hs
      have h1 := congrArg (fun (r : Polynomial ℂ) => r.coeff (finSuccEquiv ℂ n p).natDegree) h0
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h1
      exact h1
    refine Set.Finite.measure_zero
      ((((finSuccEquiv ℂ n p).map (eval s)).roots.toFinset.finite_toSet).subset ?_) _
    intro y hy
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hy
    have hcons : E.symm (y, s) = Fin.cons y s := by
      simp [E]
    rw [hcons, eval_eq_eval_mv_eval'] at hy
    simpa [Polynomial.mem_roots hmap] using hy

theorem projB_null_of (hN : NormPolyStatement)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (hJ : IsMultiHomogIdeal J) (hJP : ¬ J ≤ P) :
    volume {y : Fin e → ℂ | ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y} = 0 := by
  obtain ⟨S, hS, rfl⟩ := hJ
  obtain ⟨f, hfS, hfP⟩ : ∃ f ∈ S, f ∉ P := by
    by_contra h
    push Not at h
    exact hJP (Ideal.span_le.2 h)
  obtain ⟨a, ha⟩ := hS f hfS
  obtain ⟨c, m, hc0, hc, hz⟩ := hN K ι P e Ψ f a hP hΨ ha hfP
  have key : ∀ y : Fin e → ℂ,
      eval y (Polynomial.eval 1 (finSuccEquiv ℂ e c)) = eval (Fin.cons 1 y) c := by
    intro y
    rw [eval_eq_eval_mv_eval', Polynomial.eval_map, Polynomial.eval₂_at_one]
  have hp0 : Polynomial.eval 1 (finSuccEquiv ℂ e c) ≠ 0 := by
    obtain ⟨y, hy⟩ := exists_eval_cons_ne_zero hc0 hc
    intro h0
    apply hy
    rw [← key, h0, map_zero]
  refine measure_mono_null ?_ (volume_eval_eq_zero_lemma e _ hp0)
  rintro y ⟨z, hzP, hzJ, hzy⟩
  have hzJ' : (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) ∧
      ∀ g ∈ Ideal.span S, eval z (map (Int.castRingHom ℂ) g) = 0 := hzJ
  show eval y (Polynomial.eval 1 (finSuccEquiv ℂ e c)) = 0
  rw [key, ← hzy]
  exact hz z hzP (hzJ'.2 f (Ideal.subset_span hfS))

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedE
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

theorem ptsIntegral_eq_mInt' (hE : ResExistsStatement) (hB : ResBridgeStatement) {K : Type}
    [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {e : ℕ}
    (R : AnLogRes P J e) {L : Fin e → HermLine ι} {A : HermLine ι} {s : MRing ι}
    (hP : IsArithVar P (e + 1)) (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A)
    (hs : IsSectionOn P A s) :
    ptsIntegral P (pot L) (logNorm A s) =
      ReciprocityTheory.AnForm.M.mInt R.A (fun j => potOf R (L j)) (fun x => logNorm A s (R.lift x x)) :=
  ptsIntegral_eq_mInt hE hB goodProjExists R hP hL hA hs

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

