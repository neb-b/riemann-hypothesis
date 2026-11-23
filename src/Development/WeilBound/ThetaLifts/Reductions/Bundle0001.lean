module

public import Development.WeilBound.ThetaLifts.Reductions.MetaDef

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.Reductions.ExistsSmoothFun
section
noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E
open scoped Real RealInnerProductSpace FourierTransform

namespace PositivityTheory.ThKR

variable {l : Type} [Fintype l] [DecidableEq l]

theorem exists_sp (s : ℝ → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ))
    (sc : ∀ w, Continuous fun t => s t w) (s0 : ∀ w, s 0 w = w) (sm : ∀ t u w, s (t + u) w = s t (s u w))
    (ss : ∀ t w w', sympl (s t w) (s t w') = sympl w w') :
    ∃ X ∈ LieAlgebra.Symplectic.sp l ℝ, ∀ (t : ℝ) w, s t w = NormedSpace.exp (t • X) *ᵥ w := by
  have hsJ : ∀ w w' : l ⊕ l → ℝ, GlobalTheory.RealWeil.sympl w w' = -(w ⬝ᵥ (Matrix.J l ℝ *ᵥ w')) := by
    intro w w'
    simp [GlobalTheory.RealWeil.sympl, GlobalTheory.RealWeil.pPart, GlobalTheory.RealWeil.qPart, Matrix.J, Matrix.mulVec, dotProduct,
      Fintype.sum_sum_type, Matrix.fromBlocks, PiLp.inner_apply, Matrix.one_apply]
    simp only [mul_comm]
    ring
  have hent : ∀ (N : Matrix (l ⊕ l) (l ⊕ l) ℝ) i j, N i j = Pi.single i 1 ⬝ᵥ (N *ᵥ Pi.single j 1) := by
    intro N i j
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hinv : ∀ t, (LinearMap.toMatrix' (s t))ᵀ * Matrix.J l ℝ * LinearMap.toMatrix' (s t) = Matrix.J l ℝ := by
    intro t
    ext i j
    have h := ss t (Pi.single i 1) (Pi.single j 1)
    rw [hsJ, hsJ, neg_inj, ← LinearMap.toMatrix'_mulVec (s t), ← LinearMap.toMatrix'_mulVec (s t)] at h
    rw [hent ((LinearMap.toMatrix' (s t))ᵀ * Matrix.J l ℝ * LinearMap.toMatrix' (s t)) i j, hent (Matrix.J l ℝ) i j, ← h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_transpose]
  letI : NormedAddCommGroup (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedAddCommGroup
  letI : NormedSpace ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedSpace
  letI : NormedRing (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) := Matrix.linftyOpNormedAlgebra
  let Φ : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ := fun t => LinearMap.toMatrix' (s t)
  have hΦw : ∀ t w, s t w = Φ t *ᵥ w := fun t w => (LinearMap.toMatrix'_mulVec (s t) w).symm
  have hΦc : Continuous Φ := by
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    simp only [Φ, LinearMap.toMatrix'_apply]
    exact (continuous_apply i).comp (sc _)
  have hΦ0 : Φ 0 = 1 := by
    have : s 0 = LinearMap.id := LinearMap.ext s0
    simp only [Φ, this, LinearMap.toMatrix'_id]
  have hΦm : ∀ t u, Φ (t + u) = Φ t * Φ u := by
    intro t u
    have : s (t + u) = (s t).comp (s u) := LinearMap.ext fun w => sm t u w
    simp only [Φ, this, LinearMap.toMatrix'_comp]
  haveI : CompleteSpace (Matrix (l ⊕ l) (l ⊕ l) ℝ) := FiniteDimensional.complete ℝ _
  let G : ℝ → Matrix (l ⊕ l) (l ⊕ l) ℝ := fun x => ∫ u in (0 : ℝ)..x, Φ u
  have hG : ∀ x, HasDerivAt G (Φ x) x := fun x => (hΦc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hslope : Filter.Tendsto (fun h : ℝ => h⁻¹ • G h) (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
    have h1 := (hasDerivAt_iff_tendsto_slope.1 (hG 0))
    have hG0 : G 0 = 0 := intervalIntegral.integral_same
    rw [hΦ0] at h1
    refine h1.congr fun h => ?_
    rw [slope_def_module, hG0, sub_zero, sub_zero]
  obtain ⟨h0, hh0, hsmall⟩ : ∃ h0 : ℝ, h0 ≠ 0 ∧ ‖1 - h0⁻¹ • G h0‖ < 1 := by
    have hev : ∀ᶠ h in nhdsWithin (0 : ℝ) {0}ᶜ, ‖1 - h⁻¹ • G h‖ < 1 := by
      have := (hslope.const_sub (1 : Matrix (l ⊕ l) (l ⊕ l) ℝ)).norm
      simp only [sub_self, norm_zero] at this
      exact this.eventually (gt_mem_nhds one_pos)
    obtain ⟨h, hh, hm⟩ := (hev.and self_mem_nhdsWithin).exists
    exact ⟨h, hm, hh⟩
  let u : Matrix (l ⊕ l) (l ⊕ l) ℝ := h0⁻¹ • G h0
  let U : (Matrix (l ⊕ l) (l ⊕ l) ℝ)ˣ := Units.oneSub (1 - u) hsmall
  have hU : (U : Matrix (l ⊕ l) (l ⊕ l) ℝ) = u := by simp [U, Units.val_oneSub]
  let Binv : Matrix (l ⊕ l) (l ⊕ l) ℝ := h0⁻¹ • ((U⁻¹ : (Matrix (l ⊕ l) (l ⊕ l) ℝ)ˣ) : Matrix (l ⊕ l) (l ⊕ l) ℝ)
  have hGB : G h0 * Binv = 1 := by
    have e : G h0 = h0 • (U : Matrix (l ⊕ l) (l ⊕ l) ℝ) := by rw [hU]; simp only [u]; rw [smul_inv_smul₀ hh0]
    rw [e, smul_mul_smul_comm, mul_inv_cancel₀ hh0, Units.mul_inv, one_smul]
  have hshift : ∀ t, Φ t * G h0 = G (t + h0) - G t := by
    intro t
    have e1 : Φ t * G h0 = ∫ x in (0 : ℝ)..h0, Φ t * Φ x := by
      simpa using ((ContinuousLinearMap.mul ℝ (Matrix (l ⊕ l) (l ⊕ l) ℝ) (Φ t)).intervalIntegral_comp_comm
        (hΦc.intervalIntegrable 0 h0)).symm
    rw [e1]
    simp_rw [← hΦm]
    rw [intervalIntegral.integral_comp_add_left (fun x => Φ x) t, add_zero]
    exact (intervalIntegral.integral_interval_sub_left (hΦc.intervalIntegrable 0 (t + h0))
      (hΦc.intervalIntegrable 0 t)).symm
  let A : Matrix (l ⊕ l) (l ⊕ l) ℝ := (Φ h0 - 1) * Binv
  have hΦd : ∀ t, HasDerivAt Φ (Φ t * A) t := by
    intro t
    have hrep : Φ = fun x => (G (x + h0) - G x) * Binv := by
      funext x
      rw [← hshift x, mul_assoc, hGB, mul_one]
    have hd := (((hG (t + h0)).comp_add_const t h0).sub (hG t)).mul_const Binv
    have hval : (Φ (t + h0) - Φ t) * Binv = Φ t * A := by
      rw [hΦm, ← mul_sub_one, mul_assoc]
    rw [hval] at hd
    exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun x => congrFun hrep x)
  have hE : ∀ t : ℝ, HasDerivAt (fun x : ℝ => NormedSpace.exp ((-x) • A)) (-(A * NormedSpace.exp ((-t) • A))) t := by
    intro t
    have h1 := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) A (-t)).scomp t (hasDerivAt_neg t)
    exact h1.congr_deriv (by simp <;> rfl)
  have hP : ∀ t, Φ t * NormedSpace.exp ((-t) • A) = 1 := by
    intro t
    have hd : ∀ x, HasDerivAt (fun x => Φ x * NormedSpace.exp ((-x) • A)) 0 x := by
      intro x
      have h1 := (hΦd x).mul (hE x)
      exact h1.congr_deriv (by rw [mul_neg, mul_assoc, add_neg_cancel])
    have hc := is_const_of_deriv_eq_zero (fun x => (hd x).differentiableAt) (fun x => (hd x).deriv) t 0
    rw [hc, hΦ0, neg_zero, zero_smul, NormedSpace.exp_zero, one_mul]
  letI : NormedAlgebra ℚ (Matrix (l ⊕ l) (l ⊕ l) ℝ) :=
    { (inferInstance : Algebra ℚ (Matrix (l ⊕ l) (l ⊕ l) ℝ)) with
      norm_smul_le := fun q M => by
        rw [← Rat.cast_smul_eq_qsmul ℝ q M, norm_smul, Rat.norm_cast_real] }
  have hΦe : ∀ t, Φ t = NormedSpace.exp (t • A) := by
    intro t
    have hcomm : Commute ((-t) • A) (t • A) := ((Commute.refl A).smul_left _).smul_right _
    have h1 : NormedSpace.exp ((-t) • A) * NormedSpace.exp (t • A) = 1 := by
      have h2 := (NormedSpace.exp_add_of_commute hcomm).symm
      rw [← add_smul, neg_add_cancel, zero_smul, NormedSpace.exp_zero] at h2
      exact h2
    calc Φ t = Φ t * (NormedSpace.exp ((-t) • A) * NormedSpace.exp (t • A)) := by
          rw [h1, mul_one]
      _ = NormedSpace.exp (t • A) := by rw [← mul_assoc, hP t, one_mul]
  refine ⟨A, ?_, fun t w => ?_⟩
  · rw [LieAlgebra.Symplectic.sp, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
    let T : Matrix (l ⊕ l) (l ⊕ l) ℝ →L[ℝ] Matrix (l ⊕ l) (l ⊕ l) ℝ :=
      LinearMap.toContinuousLinearMap (Matrix.transposeLinearEquiv (l ⊕ l) (l ⊕ l) ℝ ℝ).toLinearMap
    have hT : HasDerivAt (fun t => (Φ t)ᵀ) (T (Φ 0 * A)) 0 := T.hasFDerivAt.comp_hasDerivAt 0 (hΦd 0)
    have hF := (hT.mul_const (Matrix.J l ℝ)).mul (hΦd 0)
    have hF0 : HasDerivAt (fun t => (Φ t)ᵀ * Matrix.J l ℝ * Φ t) 0 0 := by
      have e : (fun t => (Φ t)ᵀ * Matrix.J l ℝ * Φ t) = fun _ => Matrix.J l ℝ := funext hinv
      rw [e]
      exact hasDerivAt_const 0 _
    have huniq := hF.unique hF0
    simp only [T, hΦ0, one_mul, mul_one] at huniq
    have h2 : Aᵀ * Matrix.J l ℝ + Matrix.J l ℝ * A = 0 := by simpa using huniq
    show Aᵀ * Matrix.J l ℝ = Matrix.J l ℝ * -A
    rw [mul_neg]
    exact eq_neg_of_add_eq_zero_left h2
  · rw [hΦw, hΦe t]

theorem exists_smooth_fun (S : ℝ → Sch l →ₗ[ℂ] Sch l) (hn : ∀ t f, ‖(S t f).toLp 2 volume‖ = ‖f.toLp 2 volume‖)
    (S0 : ∀ f, S 0 f = f) (Sm : ∀ t u f, S (t + u) f = S t (S u f))
    (Sc : ∀ f (lam : Sch l →L[ℂ] ℂ), Continuous fun t => lam (S t f)) {φ : Sch l} (hφ : φ ≠ 0) :
    ∃ mu : Sch l →L[ℂ] ℂ, mu φ ≠ 0 ∧ DifferentiableAt ℝ (fun t => mu (S t φ)) 0 := by
  let lam : Sch l →L[ℂ] ℂ := (innerSL ℂ (φ.toLp 2 volume)).comp (schwartzToL2 l)
  have h2 : lam φ ≠ 0 := fun h => hφ (by
    apply injective_toLp 2 volume
    have : φ.toLp 2 volume = 0 := inner_self_eq_zero.1 h
    exact this.trans (map_zero (schwartzToL2 l)).symm)
  have hb : ∀ t f, ‖lam (S t f)‖ ≤ ‖φ.toLp 2 volume‖ * ‖schwartzToL2 l f‖ := fun t f => by
    have := norm_inner_le_norm (𝕜 := ℂ) (φ.toLp 2 volume) ((S t f).toLp 2 volume)
    rw [hn] at this
    exact this
  have hc := Sc φ lam
  have hI : ∀ t, HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, lam (S s φ)) (lam (S t φ)) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _) (hc.stronglyMeasurableAtFilter _ _)
      hc.continuousAt
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, (∫ s in (0 : ℝ)..δ, lam (S s φ)) ≠ 0 := by
    by_contra h
    push Not at h
    have h3 := hI 0
    simp only [h, S0] at h3
    exact h2 (h3.unique (hasDerivAt_const _ _))
  let m : Sch l →ₗ[ℂ] ℂ :=
    { toFun := fun f => ∫ s in (0 : ℝ)..δ, lam (S s f)
      map_add' := fun f g => by
        simp only [map_add (f := _)]
        exact intervalIntegral.integral_add ((Sc f lam).intervalIntegrable _ _) ((Sc g lam).intervalIntegrable _ _)
      map_smul' := fun a f => by
        simp only [map_smul, RingHom.id_apply]
        exact intervalIntegral.integral_smul _ _ }
  have mc : Continuous m := by
    refine continuous_of_continuousAt_zero m ?_
    rw [ContinuousAt, map_zero]
    have h0 : Continuous fun f : Sch l => ‖φ.toLp 2 volume‖ * ‖schwartzToL2 l f‖ * |δ - 0| := by fun_prop
    have h1 := h0.tendsto 0
    simp only [map_zero, norm_zero, mul_zero, zero_mul] at h1
    exact squeeze_zero_norm (fun f => intervalIntegral.norm_integral_le_of_norm_le_const fun s _ => hb s f) h1
  refine ⟨⟨m, mc⟩, hδ, ?_⟩
  have key : ∀ t, m (S t φ) = (∫ s in (0 : ℝ)..(δ + t), lam (S s φ)) - ∫ s in (0 : ℝ)..t, lam (S s φ) := fun t => by
    rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    have := intervalIntegral.integral_comp_add_right (fun s => lam (S s φ)) (a := 0) (b := δ) t
    rw [zero_add] at this
    rw [← this]
    simp only [Sm]
    rfl
  show DifferentiableAt ℝ (fun t => m (S t φ)) 0
  simp only [key]
  exact (((hI (δ + 0)).comp_const_add δ 0).sub (hI 0)).differentiableAt

theorem lie' (hL : PositivityTheory.ThKR.LocalLift) (s : ℝ → (l ⊕ l → ℝ) →ₗ[ℝ] (l ⊕ l → ℝ))
    (sc : ∀ w, Continuous fun t => s t w) (s0 : ∀ w, s 0 w = w) (sm : ∀ t u w, s (t + u) w = s t (s u w))
    (ss : ∀ t w w', sympl (s t w) (s t w') = sympl w w') (S : ℝ → Sch l →ₗ[ℂ] Sch l) (hS : ∀ t, Impl (s t) (S t))
    (S0 : ∀ f, S 0 f = f) (Sm : ∀ t u f, S (t + u) f = S t (S u f))
    (Sc : ∀ f (lam : Sch l →L[ℂ] ℂ), Continuous fun t => lam (S t f)) :
    ∃ Q ∈ weylAlg l, ∀ f (lam : Sch l →L[ℂ] ℂ), HasDerivAt (fun t => lam (S t f)) (lam (Q f)) 0 := by
  obtain ⟨X, hsp, hs⟩ := exists_sp s sc s0 sm ss
  obtain ⟨ε, V, W, a, hε, V0, Vi, -, Vd⟩ := hL l X hsp
  obtain ⟨φ, hφ⟩ := exists_ne_zero (0 : EuclideanSpace ℝ l)
  have hφ0 : φ ≠ 0 := fun h => hφ (by simp [h])
  have hc : ∀ t, |t| < ε → ∃ c : ℂ, ∀ f, S t f = c • V t f := fun t ht => by
    obtain ⟨h1, h2, h3⟩ := Vi t ht
    have hi : Impl id (S (-t) ∘ₗ (V t).toLinearMap) := ⟨fun f => ((hS (-t)).norm _).trans (h3.norm f), fun w f g hg => by
      have := (hS (-t)).impl _ _ _ (h3.impl w f g hg)
      rw [← hs, ← sm, neg_add_cancel, s0] at this
      exact this⟩
    obtain ⟨c, hc⟩ := hi.scalar fun f => ⟨W t (S t f), by
      show S (-t) (V t (W t _)) = f
      rw [h1, ← Sm, neg_add_cancel, S0]⟩
    have h4 : ∀ f, V t f = c • S t f := fun f => by
      rw [← map_smul, ← hc]
      show _ = S t (S (-t) (V t f))
      rw [← Sm, add_neg_cancel, S0]
    have h5 : c ≠ 0 := fun h => hφ0 (by rw [← h2 φ, h4, h, zero_smul, map_zero])
    exact ⟨c⁻¹, fun f => by rw [h4, smul_smul, inv_mul_cancel₀ h5, one_smul]⟩
  obtain ⟨mu, hmu, md⟩ := exists_smooth_fun S (fun t => (hS t).norm) S0 Sm Sc hφ0
  have hV0 : mu (V 0 φ) ≠ 0 := by rwa [V0]
  let c : ℝ → ℂ := fun t => mu (S t φ) / mu (V t φ)
  have cd : DifferentiableAt ℝ c 0 := md.div (Vd φ mu).differentiableAt hV0
  have c0 : c 0 = 1 := by simp only [c, S0, V0]; exact div_self hmu
  have ev : ∀ᶠ t in nhds (0 : ℝ), ∀ f, S t f = c t • V t f := by
    have e1 : ∀ᶠ t in nhds (0 : ℝ), |t| < ε := continuous_abs.continuousAt.eventually_lt continuousAt_const (by simpa using hε)
    filter_upwards [e1, (Vd φ mu).continuousAt.eventually_ne hV0] with t ht hne f
    obtain ⟨b, hb⟩ := hc t ht
    have : c t = b := by
      simp only [c, hb, map_smul, smul_eq_mul]
      exact mul_div_cancel_right₀ _ hne
    rw [this, hb]
  refine ⟨(deriv c 0 + a) • 1 + quad X, add_mem (Subalgebra.smul_mem _ (one_mem _) _) (quad_mem X), fun f lam => ?_⟩
  refine ((cd.hasDerivAt.fun_mul (Vd f lam)).congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp [c0, V0]
    ring
  · filter_upwards [ev] with t ht
    rw [ht, map_smul, smul_eq_mul]

end PositivityTheory.ThKR
end
end

-- bundled from Development.WeilBound.ThetaLifts.Reductions.HasDerivAtSchwartzToL2
section
noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology
open scoped Real

namespace PositivityTheory.ThKR.LL

variable {l : Type} [Fintype l]

theorem exists_decay {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : SchwartzMap (EuclideanSpace ℝ l) F) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, (1 + ‖x‖) ^ k * ‖g x‖ ≤ C := by
  have h := fun x => one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0) le_rfl le_rfl g x
  simp only [norm_iteratedFDeriv_zero] at h
  exact ⟨_, le_trans (by positivity) (h 0), h⟩

theorem csmul (r : ℝ) (x : L2 l) : (r : ℂ) • x = r • x := by
  rw [coe_smul]
  rfl

theorem hasDerivAt_schwartz_to_L2 {F : ℝ → Sch l} {G : Sch l} {t₀ : ℝ} (hp : ∀ x, HasDerivAt (fun t => F t x) (G x) t₀) {C : ℝ}
    (hb : ∀ᶠ t in 𝓝 t₀, ∀ x, (1 + ‖x‖) ^ (Module.finrank ℝ (EuclideanSpace ℝ l) + 1) * ‖F t x - F t₀ x‖ ≤ C * |t - t₀|) :
    HasDerivAt (fun t => schwartzToL2 l (F t)) (schwartzToL2 l G) t₀ := by
  set N := Module.finrank ℝ (EuclideanSpace ℝ l) + 1 with hN
  obtain ⟨C', hC', hG⟩ := exists_decay G N
  let u : ℝ → Sch l := fun t => (((t - t₀)⁻¹ : ℝ) : ℂ) • (F t - F t₀) - G
  have hu : ∀ t x, u t x = (t - t₀)⁻¹ • (F t x - F t₀ x) - G x := fun t x => by
    simp [u]
  have h1 : Tendsto (fun t => ∫ x, ‖u t x‖ ^ (2 : ℝ)) (𝓝[≠] t₀) (𝓝 (∫ _x : EuclideanSpace ℝ l, (0 : ℝ))) := by
    have hi := (integrable_one_add_norm (E := EuclideanSpace ℝ l) (μ := volume) (r := N)
      (by rw [hN]; push_cast; linarith)).const_mul ((C + C') ^ 2)
    refine tendsto_integral_filter_of_dominated_convergence _
      (.of_forall fun t => ((u t).continuous.norm.rpow_const fun _ => Or.inr (by norm_num)).aestronglyMeasurable) ?_ hi
      (.of_forall fun x => ?_)
    · filter_upwards [nhdsWithin_le_nhds hb, self_mem_nhdsWithin] with t ht ht0
      refine .of_forall fun x => ?_
      have ht1 : 0 < |t - t₀| := abs_pos.2 (sub_ne_zero.2 ht0)
      have hw : 1 ≤ (1 + ‖x‖) ^ N := one_le_pow₀ (by simp)
      have h2 : (1 + ‖x‖) ^ N * ‖u t x‖ ≤ C + C' := by
        rw [hu]
        refine (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by positivity)).trans ?_
        rw [mul_add, norm_smul, norm_inv, Real.norm_eq_abs]
        refine add_le_add ?_ (hG x)
        rw [mul_left_comm, inv_mul_le_iff₀ ht1, mul_comm |t - t₀|]
        exact ht x
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast, Real.rpow_two, Real.norm_of_nonneg (by positivity),
        ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      have h3 : ((1 + ‖x‖) ^ N * ‖u t x‖) ^ 2 ≤ (C + C') ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
      refine le_trans ?_ h3
      rw [mul_pow, mul_comm]
      gcongr
      nlinarith
    · have h2 := (hasDerivAt_iff_tendsto_slope.1 (hp x))
      have h3 := tendsto_iff_norm_sub_tendsto_zero.1 h2
      have h4 := h3.rpow_const (p := 2) (Or.inr (by norm_num))
      simpa [hu, slope_def_module] using h4
  rw [integral_zero] at h1
  have h2 := h1.rpow_const (p := 2⁻¹) (Or.inr (by norm_num))
  rw [Real.zero_rpow (by norm_num)] at h2
  rw [hasDerivAt_iff_tendsto_slope, tendsto_iff_norm_sub_tendsto_zero]
  refine h2.congr fun t => ?_
  have : slope (fun t => schwartzToL2 l (F t)) t₀ t - schwartzToL2 l G = (u t).toLp 2 volume := by
    rw [← schwartzToL2_apply, slope_def_module]
    simp only [u, map_sub, map_smul]
    simp only [csmul]
  rw [this, norm_toLp' (by simp) (by simp)]
  simp

def LD (U : ℝ → Sch l →L[ℂ] Sch l) (Q : Sch l → Sch l) (t₀ : ℝ) : Prop :=
  ∀ f, HasDerivAt (fun t => schwartzToL2 l (U t f)) (schwartzToL2 l (Q f)) t₀

theorem LD.const (U : Sch l →L[ℂ] Sch l) (t₀ : ℝ) : LD (fun _ => U) (fun _ => 0) t₀ := fun f => by
  simpa using hasDerivAt_const t₀ (schwartzToL2 l (U f))

theorem LD.smul {U : ℝ → Sch l →L[ℂ] Sch l} {Q : Sch l → Sch l} {t₀ : ℝ} (h : LD U Q t₀) {c : ℝ → ℂ} {c' : ℂ}
    (hc : HasDerivAt c c' t₀) : LD (fun t => c t • U t) (fun f => c t₀ • Q f + c' • U t₀ f) t₀ := fun f => by
  simpa using hc.fun_smul (h f)

theorem LD.mul {U W : ℝ → Sch l →L[ℂ] Sch l} {P Q : Sch l → Sch l} {t₀ : ℝ} (hU : LD U P t₀) (hW : LD W Q t₀)
    (hn : ∀ᶠ t in 𝓝 t₀, ∀ f, ‖schwartzToL2 l (U t f)‖ = ‖schwartzToL2 l f‖) :
    LD (fun t => U t * W t) (fun f => P (W t₀ f) + U t₀ (Q f)) t₀ := fun f => by
  have h1 : HasDerivAt (fun t => schwartzToL2 l (U t (W t f - W t₀ f - ((t - t₀ : ℝ) : ℂ) • Q f))) 0 t₀ := by
    have h := (hW f).isLittleO
    rw [hasDerivAt_iff_isLittleO]
    refine Asymptotics.IsBigO.trans_isLittleO (Asymptotics.IsBigO.of_bound 1 ?_) h
    filter_upwards [hn] with t ht
    simp only [sub_self, ofReal_zero, zero_smul, map_zero, smul_zero, sub_zero, ht, one_mul]
    simp only [map_sub, map_smul]
    simp only [csmul, le_refl]
  have h2 : HasDerivAt (fun t : ℝ => (t - t₀) • schwartzToL2 l (U t (Q f))) (schwartzToL2 l (U t₀ (Q f))) t₀ := by
    simpa using ((hasDerivAt_id t₀).sub_const t₀).fun_smul (hU (Q f))
  have h3 := (h1.fun_add h2).fun_add (hU (W t₀ f))
  rw [zero_add, ← map_add (f := _), add_comm (U t₀ (Q f))] at h3
  refine h3.congr_of_eventuallyEq (.of_forall fun t => ?_)
  simp only [ContinuousLinearMap.mul_apply, map_sub, map_smul]
  simp only [csmul]
  abel

variable [DecidableEq l]

theorem weyl_step {V : Sch l →L[ℂ] Sch l} {w v : l ⊕ l → ℝ} (h : ∀ f, dRho w (V f) = V (dRho v f))
    (A : Sch l →L[ℂ] Sch l) (f : Sch l) :
    schwartzToL2 l ((A * dRho w) (V f)) = ∑ a, v a • schwartzToL2 l (A (V (dRho (Pi.single a 1) f))) := by
  rw [ContinuousLinearMap.mul_apply, h, dRho_eq_sum v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, map_sum, map_smul]
  simp only [csmul]

theorem LD.differentiableAt {V : ℝ → Sch l →L[ℂ] Sch l} {Q : Sch l → Sch l} {t₀ : ℝ} (hV : LD V Q t₀)
    (v : ℝ → (l ⊕ l → ℝ) → (l ⊕ l → ℝ)) (hv : ∀ w a, DifferentiableAt ℝ (fun t => v t w a) t₀)
    (h : ∀ᶠ t in 𝓝 t₀, ∀ w f, dRho w (V t f) = V t (dRho (v t w) f)) (f : Sch l) (lam : Sch l →L[ℂ] ℂ) :
    DifferentiableAt ℝ (fun t => lam (V t f)) t₀ := by
  have key : ∀ A ∈ weylAlg l, ∀ f, DifferentiableAt ℝ (fun t => schwartzToL2 l (A (V t f))) t₀ := fun A hA => by
    refine weylAlg_induction (P := fun A => ∀ f, DifferentiableAt ℝ (fun t => schwartzToL2 l (A (V t f))) t₀)
      (fun f => (hV f).differentiableAt) ?_ (fun f => by simp) ?_ ?_ hA
    · intro A w ih f
      refine (DifferentiableAt.fun_sum (u := Finset.univ) fun a _ =>
        (hv w a).fun_smul (ih (dRho (Pi.single a 1) f))).congr_of_eventuallyEq ?_
      filter_upwards [h] with t ht
      exact weyl_step (ht w) A f
    · intro A B hA hB f
      simp only [ContinuousLinearMap.add_apply, map_add (f := _)]
      exact (hA f).add (hB f)
    · intro c A hA f
      simp only [ContinuousLinearMap.smul_apply, map_smul]
      exact (hA f).const_smul c
  obtain ⟨ι, _, A, Λ, hA, h⟩ := exists_factor lam
  simp only [h]
  exact (Λ.restrictScalars ℝ).differentiableAt.comp t₀ (differentiableAt_pi.2 fun i => key _ (hA i) f)

theorem LD.hasDerivAt {V : ℝ → Sch l →L[ℂ] Sch l} {Q : Sch l →L[ℂ] Sch l} (hV : LD V Q 0) (h0 : ∀ f, V 0 f = f)
    (v : ℝ → (l ⊕ l → ℝ) → (l ⊕ l → ℝ)) (v' : (l ⊕ l → ℝ) → (l ⊕ l → ℝ)) (hv0 : ∀ w, v 0 w = w)
    (hv : ∀ w a, HasDerivAt (fun t => v t w a) (-v' w a) 0) (hQ : ∀ w, Q * dRho w - dRho w * Q = dRho (v' w))
    (h : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ w f, dRho w (V t f) = V t (dRho (v t w) f)) (f : Sch l) (lam : Sch l →L[ℂ] ℂ) :
    HasDerivAt (fun t => lam (V t f)) (lam (Q f)) 0 := by
  have key : ∀ A ∈ weylAlg l, ∀ f, HasDerivAt (fun t => schwartzToL2 l (A (V t f))) (schwartzToL2 l (A (Q f))) 0 := fun A hA => by
    refine weylAlg_induction (P := fun A => ∀ f, HasDerivAt (fun t => schwartzToL2 l (A (V t f))) (schwartzToL2 l (A (Q f))) 0)
      hV ?_ (fun f => by simpa using hasDerivAt_const _ _) ?_ ?_ hA
    · intro A w ih f
      refine ((HasDerivAt.fun_sum (u := Finset.univ) fun a _ =>
        (hv w a).fun_smul (ih (dRho (Pi.single a 1) f))).congr_deriv ?_).congr_of_eventuallyEq ?_
      · have e : dRho w * Q = Q * dRho w - dRho (v' w) := by rw [← hQ, sub_sub_cancel]
        rw [ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply (dRho w), e, dRho_eq_sum w,
          dRho_eq_sum (v' w)]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, map_sum, map_smul, hv0, h0,
          ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, map_sub, neg_smul, ← sub_eq_add_neg,
          Finset.sum_sub_distrib]
        simp only [csmul]
      · filter_upwards [h] with t ht
        exact weyl_step (ht w) A f
    · intro A B hA hB f
      simp only [ContinuousLinearMap.add_apply, map_add (f := _)]
      exact (hA f).add (hB f)
    · intro c A hA f
      simp only [ContinuousLinearMap.smul_apply, map_smul]
      exact (hA f).const_smul c
  obtain ⟨ι, _, A, Λ, hA, h⟩ := exists_factor lam
  simp only [h]
  exact (Λ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_pi.2 fun i => key _ (hA i) f)

end PositivityTheory.ThKR.LL
end
end

