module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ConeTangentLiftInChart
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
public import Development.WeilBound.CoreStatements.FlagImmersions.Transport
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0027
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.DifferentiableAtAffCoord
section
noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Cusp
open GroundTheory.Heights₂.Heights.LowerBoundFree (torusSmul)
open ReciprocityTheory.AnForm

namespace RootFieldNumerics.Levi

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem tangent_decomp (Ω : Type) [Field Ω] [Algebra ℚ Ω] (y : (Σ k, J k) → Ω) (e : ℕ)
    (hP : IsArithVar (mCoordIdeal y) (e + 1)) (hsm : SmoothGenericFibreM y)
    (γ : (Fin e → ℂ) → (Σ k, J k) → ℂ) (t : Fin e → ℂ) (hγ : AnalyticAt ℂ γ t)
    (hpts : ∀ᶠ t' in 𝓝 t, γ t' ∈ mcPts (mCoordIdeal y))
    (himm : ∀ u c, fderiv ℂ γ t u = torusSmul c (γ t) → u = 0) (v : (Σ k, J k) → ℂ)
    (hv : IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal y) (γ t) v) :
    ∃ (u : Fin e → ℂ) (c : K → ℂ), v = fderiv ℂ γ t u + torusSmul c (γ t) := by
  classical
  have hz := hpts.self_of_nhds
  have hdim := finrank_tanSub_pC_le Ω y _ hP hsm hz
  have hzI : ∀ f ∈ pC (mCoordIdeal y), eval (γ t) f = 0 := by
    have h := hz
    rw [mcPts_eq_pC] at h
    exact h.2
  have hPh : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC (mCoordIdeal y)) :=
    isMultiHomogIdeal_pC hP.2.1.2.1
  have hcone : ∀ x, IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal y) (γ t) x →
      x ∈ tanSub (pC (mCoordIdeal y)) (γ t) := by
    intro x hx f hf
    have hle : pC (mCoordIdeal y) ≤ tanIdeal (γ t) x := by
      rw [pC, Ideal.span_le]
      rintro _ ⟨g, hg, rfl⟩
      exact ⟨hz.2 g hg, hx g hg⟩
    exact (hle hf).2
  let L₁ : (Fin e → ℂ) →ₗ[ℂ] (Σ k, J k) → ℂ := (fderiv ℂ γ t).toLinearMap
  let L₂ : (K → ℂ) →ₗ[ℂ] (Σ k, J k) → ℂ :=
    { toFun := fun c => torusSmul c (γ t)
      map_add' := fun c c' => by funext q; simp only [torusSmul, Pi.add_apply]; ring
      map_smul' := fun r c => by
        funext q; simp only [torusSmul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  let L := L₁.coprod L₂
  have hL : ∀ u c, L (u, c) = fderiv ℂ γ t u + torusSmul c (γ t) := fun _ _ => rfl
  have hrange : LinearMap.range L ≤ tanSub (pC (mCoordIdeal y)) (γ t) := by
    rintro _ ⟨⟨u, c⟩, rfl⟩
    rw [hL]
    refine Submodule.add_mem _ (hcone _ ?_) fun f hf => (le_tanIdeal_torusSmul hPh hzI c hf).2
    exact GroundTheory.Heights₂.Heights.HilbertSamuel.G1.isConeTangent_of_sheet le_rfl hγ hpts u
  have hinj : Function.Injective L := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    rintro ⟨u, c⟩ h
    rw [hL] at h
    have hu : u = 0 := himm u (fun k => -c k) (by
      funext q
      have h1 := congrFun h q
      simp only [torusSmul, Pi.add_apply, Pi.zero_apply] at h1 ⊢
      linear_combination h1)
    subst hu
    have h2 : torusSmul c (γ t) = 0 := by simpa using h
    have hc : c = 0 := by
      funext k
      obtain ⟨i, hi⟩ := hz.1 k
      have h3 : c k * γ t ⟨k, i⟩ = 0 := congrFun h2 ⟨k, i⟩
      exact (mul_eq_zero.mp h3).resolve_right hi
    rw [hc]
    rfl
  have hfr : Module.finrank ℂ (LinearMap.range L) = e + Fintype.card K := by
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have heq := Submodule.eq_of_le_of_finrank_le hrange (by rw [hfr]; exact hdim)
  have hvr : v ∈ LinearMap.range L := heq ▸ hcone v hv
  obtain ⟨⟨u, c⟩, huc⟩ := hvr
  exact ⟨u, c, huc.symm⟩

theorem differentiableAt_affCoord (p : (k : K) → J k) (z : (Σ k, J k) → ℂ) (hp : ∀ k, z ⟨k, p k⟩ ≠ 0) :
    DifferentiableAt ℂ (affCoord p) z := by
  refine differentiableAt_pi.2 fun q => ?_
  have h1 : AnalyticAt ℂ (fun v : (Σ k, J k) → ℂ => v q) z :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) q).analyticAt z
  have h2 : AnalyticAt ℂ (fun v : (Σ k, J k) → ℂ => v ⟨q.1, p q.1⟩) z :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) ⟨q.1, p q.1⟩).analyticAt z
  exact (h1.div h2 (hp q.1)).differentiableAt

theorem affCoord_torus (p : (k : K) → J k) (c : K → ℂ) (hc : ∀ k, c k ≠ 0) (z : (Σ k, J k) → ℂ) :
    affCoord p (torusSmul c z) = affCoord p z := by
  funext q
  simp only [affCoord, torusSmul]
  exact mul_div_mul_left _ _ (hc q.1)

theorem fderiv_affCoord_torus (p : (k : K) → J k) (z : (Σ k, J k) → ℂ) (hp : ∀ k, z ⟨k, p k⟩ ≠ 0) (b : K → ℂ) :
    fderiv ℂ (affCoord p) z (torusSmul b z) = 0 := by
  have h1 : HasDerivAt (fun s : ℂ => torusSmul (fun k => Complex.exp (s * b k)) z) (torusSmul b z) 0 := by
    refine hasDerivAt_pi.2 fun q => ?_
    have := (((hasDerivAt_id (0 : ℂ)).mul_const (b q.1)).cexp).mul_const (z q)
    simpa [torusSmul] using this
  have h0 : torusSmul (fun k => Complex.exp ((0 : ℂ) * b k)) z = z := by
    funext q; simp [torusSmul]
  have h2 : HasFDerivAt (affCoord p) (fderiv ℂ (affCoord p) z)
      (torusSmul (fun k => Complex.exp ((0 : ℂ) * b k)) z) := by
    rw [h0]; exact (differentiableAt_affCoord p z hp).hasFDerivAt
  have h3 := h2.comp_hasDerivAt (0 : ℂ) h1
  have h4 : (affCoord p ∘ fun s : ℂ => torusSmul (fun k => Complex.exp (s * b k)) z) = fun _ => affCoord p z := by
    funext s
    exact affCoord_torus p _ (fun k => Complex.exp_ne_zero _) z
  rw [h4] at h3
  exact h3.unique (hasDerivAt_const _ _)

theorem levi_torus {e : ℕ} (φ : ((Σ k, J k) → ℂ) → ℝ) (d : K → ℝ)
    (hhom : ∀ (c : K → ℂ) (z : (Σ k, J k) → ℂ), (∀ k, c k ≠ 0) → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      φ (torusSmul c z) = ∑ k, d k * Real.log ‖c k‖ + φ z)
    (γ : (Fin e → ℂ) → (Σ k, J k) → ℂ) (t : Fin e → ℂ) (hγ : AnalyticAt ℂ γ t)
    (hpts : ∀ᶠ t' in 𝓝 t, ∀ k, ∃ i, γ t' ⟨k, i⟩ ≠ 0) (hφ : ContDiffAt ℝ 2 φ (γ t)) (u : Fin e → ℂ) (b : K → ℂ) :
    levi φ (γ t) (fderiv ℂ γ t u + torusSmul b (γ t)) = levi (φ ∘ γ) t u := by
  let ℓ : (Unit → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj ()
  let lin : (Unit → ℂ) → Fin e → ℂ := fun s => t + ℓ s • u
  have hlin : HasFDerivAt lin (ℓ.smulRight u) 0 := by
    have := (ℓ.smulRight u).hasFDerivAt (x := 0)
    exact this.const_add t
  have hlinA : AnalyticAt ℂ lin 0 := analyticAt_const.add ((ℓ.smulRight u).analyticAt 0)
  have hl0 : lin 0 = t := by simp [lin]
  have hγ' : AnalyticAt ℂ γ (lin 0) := by rw [hl0]; exact hγ
  let Γ : (Unit → ℂ) → (Σ k, J k) → ℂ := fun s => torusSmul (fun k => Complex.exp (ℓ s * b k)) (γ (lin s))
  have hΓ0 : Γ 0 = γ t := by
    funext q; simp [Γ, torusSmul, hl0]
  have hγl : AnalyticAt ℂ (γ ∘ lin) 0 := hγ'.comp hlinA
  have hΓA : AnalyticAt ℂ Γ 0 := by
    refine analyticAt_pi_iff.2 fun q => ?_
    exact (((ℓ.analyticAt 0).mul analyticAt_const).cexp').mul (analyticAt_pi_iff.1 hγl q)
  have hΓd : fderiv ℂ Γ 0 (fun _ => 1) = fderiv ℂ γ t u + torusSmul b (γ t) := by
    have hg : HasFDerivAt (γ ∘ lin) ((fderiv ℂ γ t).comp (ℓ.smulRight u)) 0 := by
      have h1 : HasFDerivAt γ (fderiv ℂ γ t) (lin 0) := by rw [hl0]; exact hγ.differentiableAt.hasFDerivAt
      exact h1.comp 0 hlin
    funext q
    have h1 := (hasFDerivAt_pi'.1 hΓA.differentiableAt.hasFDerivAt q)
    have h2 := (((ℓ.hasFDerivAt (x := 0)).mul_const (b q.1)).cexp).mul (hasFDerivAt_pi'.1 hg q)
    have h3 := congrArg (fun L => L (fun _ => 1)) (h1.unique h2)
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.proj_apply] at h3
    rw [h3]
    simp [ℓ, hl0, torusSmul]
    ring
  have hφγ : ContDiffAt ℝ 2 (φ ∘ γ) t := hφ.comp t (hγ.restrictScalars (𝕜 := ℝ)).contDiffAt
  have e1 := levi_comp (φ := φ) (τ := Γ) (z := 0) (fun _ => 1) hΓA (by rw [hΓ0]; exact hφ)
  rw [hΓ0, hΓd] at e1
  have e2 := levi_comp (φ := φ ∘ γ) (τ := lin) (z := 0) (fun _ => 1) hlinA (by rw [hl0]; exact hφγ)
  rw [hl0, hlin.fderiv] at e2
  have e3 : (ℓ.smulRight u) (fun _ => 1) = u := by simp [ℓ]
  rw [e3] at e2
  rw [← e1, ← e2]
  let G : (Unit → ℂ) → ℂ := fun s => ∑ k, (d k : ℂ) * (ℓ s * b k)
  have hG : AnalyticAt ℂ G 0 :=
    Finset.analyticAt_fun_sum _ fun k _ => analyticAt_const.mul ((ℓ.analyticAt 0).mul analyticAt_const)
  have hev : φ ∘ Γ =ᶠ[𝓝 0] fun s => ((φ ∘ γ) ∘ lin) s + 1 * (G s).re := by
    have ht : Tendsto lin (𝓝 0) (𝓝 t) := by rw [← hl0]; exact hlinA.continuousAt
    filter_upwards [ht.eventually hpts] with s hs
    simp only [Function.comp_apply, Γ]
    rw [hhom _ _ (fun k => Complex.exp_ne_zero _) hs, add_comm, one_mul]
    congr 1
    simp only [G, Complex.re_sum, Complex.re_ofReal_mul, Complex.norm_exp, Real.log_exp]
  have hc1 : ContDiffAt ℝ 2 ((φ ∘ γ) ∘ lin) 0 :=
    ContDiffAt.comp 0 (by rw [hl0]; exact hφγ) (hlinA.restrictScalars (𝕜 := ℝ)).contDiffAt
  have hc2 : ContDiffAt ℝ 2 (fun s => (G s).re) 0 :=
    Complex.reCLM.contDiff.contDiffAt.comp 0 (hG.restrictScalars (𝕜 := ℝ)).contDiffAt
  rw [levi_congr hev, levi_add_smul 1 hc1 hc2, levi_re_analytic hG]
  simp

theorem levi_nonneg (Ω : Type) [Field Ω] [Algebra ℚ Ω] (y : (Σ k, J k) → Ω) (e : ℕ)
    (hP : IsArithVar (mCoordIdeal y) (e + 1)) (hsm : SmoothGenericFibreM y) {B : Ideal (MRing J)} (hB : B = ⊤)
    (R : AnLogRes (mCoordIdeal y) B e) (φ : ((Σ k, J k) → ℂ) → ℝ) (d : K → ℝ)
    (hhom : ∀ (c : K → ℂ) (z : (Σ k, J k) → ℂ), (∀ k, c k ≠ 0) → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      φ (torusSmul c z) = ∑ k, d k * Real.log ‖c k‖ + φ z)
    (hφ : ∀ z : (Σ k, J k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ContDiffAt ℝ 2 φ z)
    (hpsh : ∀ x j, x ∈ (R.A.chart j).source → ∀ u,
      0 ≤ levi (fun t => φ (R.lift x ((R.A.chart j).symm t))) (R.A.chart j x) u)
    (z : (Σ k, J k) → ℂ) (hz : z ∈ mcPts (mCoordIdeal y)) (w : (Σ k, J k) → ℂ)
    (hw : IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal y) z w) : 0 ≤ leviForm φ z w := by
  classical
  have hno : ∀ z : (Σ k, J k) → ℂ, z ∉ mcPts B := fun z hz => by
    subst hB
    simpa using hz.2 1 Submodule.mem_top
  obtain ⟨x, c, hc, hx⟩ := R.surj z hz (hno z)
  obtain ⟨j, hj⟩ := R.A.cover x
  let γ₀ : (Fin e → ℂ) → (Σ k, J k) → ℂ := fun t => R.lift x ((R.A.chart j).symm t)
  let γ : (Fin e → ℂ) → (Σ k, J k) → ℂ := fun t => torusSmul (fun k => (c k)⁻¹) (γ₀ t)
  have hci : ∀ k, (c k)⁻¹ ≠ 0 := fun k => inv_ne_zero (hc k)
  have hsx : (R.A.chart j).symm (R.A.chart j x) = x := (R.A.chart j).left_inv hj
  have hmemO : R.A.chart j x ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
    ⟨(R.A.chart j).map_source hj, by rw [Set.mem_preimage, hsx]; exact R.mem_U x⟩
  have hO := ((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)).mem_nhds hmemO
  have hγ₀A : AnalyticAt ℂ γ₀ (R.A.chart j x) := analyticAt_pi_iff.2 fun q => R.holo x q j _ hmemO
  have hγA : AnalyticAt ℂ γ (R.A.chart j x) :=
    analyticAt_pi_iff.2 fun q => analyticAt_const.mul (analyticAt_pi_iff.1 hγ₀A q)
  have hγz : γ (R.A.chart j x) = z := by
    funext q
    simp only [γ, γ₀, torusSmul, hsx, hx]
    rw [← mul_assoc, inv_mul_cancel₀ (hc _), one_mul]
  have h0pts : ∀ᶠ t in 𝓝 (R.A.chart j x), γ₀ t ∈ mcPts (mCoordIdeal y) := by
    filter_upwards [hO] with t ht using R.mem x _ ht.2
  have hpts : ∀ᶠ t in 𝓝 (R.A.chart j x), γ t ∈ mcPts (mCoordIdeal y) := by
    filter_upwards [h0pts] with t ht
    exact mcPts_smul hP.2.1.2.1 _ hci ht
  choose p hp using hz.1
  have himm : ∀ u b, fderiv ℂ γ (R.A.chart j x) u = torusSmul b (γ (R.A.chart j x)) → u = 0 := by
    intro u b hub
    have hp' : ∀ k, R.lift x x ⟨k, p k⟩ ≠ 0 := fun k => by
      rw [hx]; exact mul_ne_zero (hc k) (hp k)
    have hk := R.immersion x (hno _) p hp' j hj
    have hfun : (fun t => affCoord p (R.lift x ((R.A.chart j).symm t))) = affCoord p ∘ γ := by
      funext t
      exact (affCoord_torus p _ hci _).symm
    rw [hfun, fderiv_comp _ (by rw [hγz]; exact differentiableAt_affCoord p z hp) hγA.differentiableAt] at hk
    have : u ∈ (⊥ : Submodule ℂ (Fin e → ℂ)) := by
      rw [← hk]
      show fderiv ℂ (affCoord p) (γ (R.A.chart j x)) (fderiv ℂ γ (R.A.chart j x) u) = 0
      rw [hub, hγz]
      exact fderiv_affCoord_torus p z hp b
    exact this
  obtain ⟨u, b, hub⟩ := tangent_decomp Ω y e hP hsm γ _ hγA hpts himm w (by rw [hγz]; exact hw)
  have h1 := levi_torus φ d hhom γ _ hγA (hpts.mono fun t ht => ht.1) (by rw [hγz]; exact hφ z hz.1) u b
  rw [← hub, hγz] at h1
  show 0 ≤ levi φ z w
  rw [h1]
  have hev : φ ∘ γ =ᶠ[𝓝 (R.A.chart j x)] fun t => φ (γ₀ t) +
      1 * ((fun _ : Fin e → ℂ => ((∑ k, d k * Real.log ‖(c k)⁻¹‖ : ℝ) : ℂ)) t).re := by
    filter_upwards [h0pts] with t ht
    simp only [Function.comp_apply, γ]
    rw [hhom _ _ hci ht.1, Complex.ofReal_re, one_mul, add_comm]
  have hc1 : ContDiffAt ℝ 2 (fun t => φ (γ₀ t)) (R.A.chart j x) :=
    (hφ _ h0pts.self_of_nhds.1).comp _ (hγ₀A.restrictScalars (𝕜 := ℝ)).contDiffAt
  rw [levi_congr hev, levi_add_smul 1 hc1 contDiffAt_const, levi_re_analytic analyticAt_const]
  simpa using hpsh x j hj u

end RootFieldNumerics.Levi
end
end

-- bundled from Development.WeilBound.CoreStatements.FlagImmersions.NeZeroOfHasVal
section
noncomputable section

namespace RootFieldNumerics.Bh

open AlgebraicGeometry CategoryTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {K : Type} [Fintype K] {J : K → Type}
  [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem exists_poly (T : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) (hn : IsNormalScheme X)
    (c : (k : K) → J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {a : Ω} (ha : a ∈ integralClosure (chartRingZ y c) Ω) :
    ∃ p : MRing J, aeval (fun q : Σ k, J k => y q / y ⟨q.1, c q.1⟩) p = a := by
  classical
  have hc0 : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
  have hle : Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) ≤ chartRingZ y c := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    show (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩ ∈ chartRingZ y c
    rw [← Finset.prod_div_distrib]
    exact Subalgebra.prod_mem _ fun k _ => Algebra.subset_adjoin ⟨⟨k, j k⟩, rfl⟩
  have hge : chartRingZ y c ≤ Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨⟨k, i⟩, rfl⟩
    refine Algebra.subset_adjoin ⟨Function.update c k i, ?_⟩
    show (∏ k', y ⟨k', Function.update c k i k'⟩) / ∏ k, y ⟨k, c k⟩ = y ⟨k, i⟩ / y ⟨k, c k⟩
    rw [← Finset.prod_div_distrib, Finset.prod_eq_single k]
    · rw [Function.update_self]
    · intro k' _ h
      rw [Function.update_of_ne h, div_self (hc k')]
    · simp
  have hmem : a ∈ chartRingZ y c := by
    refine hle ((T.ring c hc0 a).2 fun q hq => ?_)
    obtain ⟨h1, -, h3⟩ := _root_.GlobalTheory.CompanionTheory.Ar.RegAtRing.regAt_ring X Ω ξ T.gen q
    have h4 := h3 (hn q.1).2
    let φ : chartRingZ y c →+* regAt ξ q :=
      (algebraMap (chartRingZ y c) Ω).codRestrict _ fun r => (T.ring c hc0 r).1 (hge r.2) q hq
    have h5 : IsIntegral (regAt ξ q) a := IsIntegral.map_of_comp_eq φ (RingHom.id Ω) rfl ha
    obtain ⟨r, rfl⟩ := (isIntegrallyClosed_iff Ω).1 h4 h5
    exact r.2
  unfold chartRingZ at hmem
  rw [Algebra.adjoin_range_eq_range_aeval] at hmem
  exact hmem

variable {z : Spec (CommRingCat.of ℂ) ⟶ X} {w : (Σ k, J k) → ℂ}

theorem val_ratio (h : CoordsAt ξ y z w) (k : K) (i c : J k) (hc : w ⟨k, c⟩ ≠ 0) :
    ValAt ξ z (y ⟨k, i⟩ / y ⟨k, c⟩) (w ⟨k, i⟩ / w ⟨k, c⟩) := by
  obtain ⟨r, hr, e⟩ := (h.2 k c (IsUnit.mk0 _ hc)).2 i
  rwa [e, mul_div_cancel_right₀ _ hc]

theorem val_prod (hz : genPt ξ ⤳ centre z) {a : K → Ω} {r : K → ℂ} (h : ∀ k, ValAt ξ z (a k) (r k)) :
    ValAt ξ z (∏ k, a k) (∏ k, r k) := by
  classical
  have : ∀ s : Finset K, ValAt ξ z (∏ k ∈ s, a k) (∏ k ∈ s, r k) := fun s => by
    induction s using Finset.induction_on with
    | empty => simpa using CxVal.one hz
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.prod_insert hk]
      exact CxVal.mul (h k) ih
  exact this _

theorem val_pow (hz : genPt ξ ⤳ centre z) {a : Ω} {r : ℂ} (h : ValAt ξ z a r) (n : ℕ) : ValAt ξ z (a ^ n) (r ^ n) := by
  induction n with
  | zero => simpa using CxVal.one hz
  | succ n ih => rw [pow_succ, pow_succ]; exact CxVal.mul ih h

def fn (y : (Σ k, J k) → Ω) (s : Ω) (m : ℕ) (k₀ : K) (i₀ : J k₀) (c : (k : K) → J k) : Ω :=
  s * (∏ k, y ⟨k, c k⟩) / y ⟨k₀, i₀⟩ ^ m

theorem val_fn (hz : genPt ξ ⤳ centre z) (h : CoordsAt ξ y z w) {s : Ω} {m : ℕ} {k₀ : K} (i₀ : J k₀) (c c' : (k : K) → J k)
    (hc : ∀ k, w ⟨k, c' k⟩ ≠ 0) (hi : w ⟨k₀, i₀⟩ ≠ 0) {p : MRing J}
    (hp : aeval (fun q : Σ k, J k => y q / y ⟨q.1, c' q.1⟩) p = fn y s m k₀ (c' k₀) c') :
    ValAt ξ z (fn y s m k₀ i₀ c) (aeval (fun q : Σ k, J k => w q / w ⟨q.1, c' q.1⟩) p * (∏ k, w ⟨k, c k⟩ / w ⟨k, c' k⟩) *
      (w ⟨k₀, c' k₀⟩ / w ⟨k₀, i₀⟩) ^ m) := by
  have h1 := CxVal.aeval hz (fun q : Σ k, J k => val_ratio h q.1 q.2 (c' q.1) (hc q.1)) p
  have h2 := val_prod hz fun k => val_ratio h k (c k) (c' k) (hc k)
  have h3 := val_pow hz (val_ratio h k₀ (c' k₀) i₀ hi) m
  have hy := fun k => (h.2 k (c' k) (IsUnit.mk0 _ (hc k))).1
  have hy0 := (h.2 k₀ i₀ (IsUnit.mk0 _ hi)).1
  have hP : (∏ k, y ⟨k, c' k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hy k
  have hk := hy k₀
  convert CxVal.mul (CxVal.mul h1 h2) h3 using 1
  have hp' : aeval (fun q : Σ k, J k => y ⟨q.1, q.2⟩ / y ⟨q.1, c' q.1⟩) p = fn y s m k₀ (c' k₀) c' := hp
  rw [hp', Finset.prod_div_distrib, div_pow]
  unfold fn
  field_simp

theorem fn_eq [DecidableEq K] {s : Ω} {m : ℕ} {k₀ : K} {a : K → ℤ} (ha : a k₀ = 1 ∧ ∀ k, k ≠ k₀ → a k = 0)
    (c : (k : K) → J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    s * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k - 1)) = fn y s m k₀ (c k₀) c := by
  have e : ∀ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * a k - 1)) = y ⟨k, c k⟩ / y ⟨k, c k⟩ ^ ((m : ℤ) * a k) := fun k => by
    rw [neg_sub, zpow_sub₀ (hc k), zpow_one]
  simp only [e, Finset.prod_div_distrib]
  rw [Finset.prod_eq_single k₀ (f := fun k => y ⟨k, c k⟩ ^ ((m : ℤ) * a k))]
  · rw [ha.1, mul_one, zpow_natCast, fn, mul_div_assoc]
  · intro k _ h
    rw [ha.2 k h, mul_zero, zpow_zero]
  · simp

theorem ne_zero_of_hasVal (hz : genPt ξ ⤳ centre z) (h : CoordsAt ξ y z w) {s : Ω} {a : K → ℤ} (c : (k : K) → J k)
    (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) {p : MRing J}
    (hp : aeval (fun q : Σ k, J k => y q / y ⟨q.1, c q.1⟩) p = s * ∏ k, y ⟨k, c k⟩ ^ (-a k)) {v : ℂ} (hv : v ≠ 0)
    (hs : Small.HasVal y a s w v) : aeval (fun q : Σ k, J k => w q / w ⟨q.1, c q.1⟩) p ≠ 0 := by
  obtain ⟨dg, dh, g, h', hg, hh, hd, e1, hne, e2⟩ := hs
  have hy := fun k => (h.2 k (c k) (IsUnit.mk0 _ (hc k))).1
  have V := fun f : MRing J => CxVal.aeval hz (fun q : Σ k, J k => val_ratio h q.1 q.2 (c q.1) (hc q.1)) f
  have ey : y = fun q => y ⟨q.1, c q.1⟩ * (y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩) :=
    funext fun q => (mul_div_cancel₀ _ (hy q.1)).symm
  have ew : w = fun q => w ⟨q.1, c q.1⟩ * (w ⟨q.1, q.2⟩ / w ⟨q.1, c q.1⟩) :=
    funext fun q => (mul_div_cancel₀ _ (hc q.1)).symm
  have g1 := aeval_blockScale hg (fun k => y ⟨k, c k⟩) fun q => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩
  have g2 := aeval_blockScale hh (fun k => y ⟨k, c k⟩) fun q => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩
  have g3 := aeval_blockScale hg (fun k => w ⟨k, c k⟩) fun q => w ⟨q.1, q.2⟩ / w ⟨q.1, c q.1⟩
  rw [← ey] at g1 g2
  rw [← ew] at g3
  have key : aeval (fun q : Σ k, J k => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩) g =
      aeval (fun q : Σ k, J k => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩) p *
        aeval (fun q : Σ k, J k => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩) h' := by
    have hp' : aeval (fun q : Σ k, J k => y ⟨q.1, q.2⟩ / y ⟨q.1, c q.1⟩) p = s * ∏ k, y ⟨k, c k⟩ ^ (-a k) := hp
    have h0 : (∏ k, y ⟨k, c k⟩ ^ dg k) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy k)
    have h1 : (∏ k, y ⟨k, c k⟩ ^ dg k) * ∏ k, y ⟨k, c k⟩ ^ (-a k) = ∏ k, y ⟨k, c k⟩ ^ dh k := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hy k), hd k]
      congr 1
      ring
    refine mul_left_cancel₀ h0 ?_
    rw [← g1, e1, g2, hp', ← h1]
    ring
  have e3 := CxVal.unique (key ▸ V g) (CxVal.mul (V p) (V h'))
  intro h0
  have h0' : aeval (fun q : Σ k, J k => w ⟨q.1, q.2⟩ / w ⟨q.1, c q.1⟩) p = 0 := h0
  rw [h0', zero_mul] at e3
  rw [e3, mul_zero, e2] at g3
  exact mul_ne_zero hv hne g3

end RootFieldNumerics.Bh
end
end

