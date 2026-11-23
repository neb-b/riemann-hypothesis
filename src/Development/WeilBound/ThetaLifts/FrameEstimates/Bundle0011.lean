module

public import Development.WeilBound.ThetaLifts.FrameEstimates.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.TwistedProofs.Bundle0007

@[expose] public section

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.LineEx
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace ExponentialLineExistence

open GlobalTheory.CompanionTheory.CMAdele

section Cx

variable {d : ℕ}

theorem exp_line_add (Y : Matrix (Fin d) (Fin d) ℂ) (s t : ℝ) :
    NormedSpace.exp (((s + t : ℝ) : ℂ) • Y) = NormedSpace.exp ((s : ℂ) • Y) * NormedSpace.exp ((t : ℂ) • Y) := by
  rw [← Matrix.exp_add_of_commute _ _ (((Commute.refl Y).smul_left _).smul_right _), Complex.ofReal_add, add_smul]

theorem exp_map_star (A : Matrix (Fin d) (Fin d) ℂ) :
    (NormedSpace.exp A).map star = NormedSpace.exp (A.map star) := by
  have e : ∀ B : Matrix (Fin d) (Fin d) ℂ, B.map star = Bᴴᵀ := fun B => rfl
  rw [e, e, Matrix.exp_transpose, Matrix.exp_conjTranspose]

set_option backward.isDefEq.respectTransparency false in
theorem exp_semiconj {J A B : Matrix (Fin d) (Fin d) ℂ} (h : SemiconjBy J A B) :
    NormedSpace.exp (-B) * J * NormedSpace.exp A = J :=
  open scoped Matrix.Norms.Operator in h.exp_neg_mul_mul_exp_eq_self

set_option backward.isDefEq.respectTransparency false in
theorem continuous_exp_mat : Continuous (NormedSpace.exp : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ) :=
  open scoped Matrix.Norms.Operator in NormedSpace.exp_continuous

theorem exp_unitary {J Y : Matrix (Fin d) (Fin d) ℂ} (h : Yᵀ * J + J * Y.map star = 0) (t : ℝ) :
    (NormedSpace.exp ((t : ℂ) • Y))ᵀ * J * (NormedSpace.exp ((t : ℂ) • Y)).map star = J := by
  have h1 : SemiconjBy J (((t : ℂ) • Y).map star) (-((t : ℂ) • Y)ᵀ) := by
    have e : ((t : ℂ) • Y).map star = (t : ℂ) • Y.map star := by
      ext i j
      simp
    rw [SemiconjBy, e, Matrix.transpose_smul, Matrix.mul_smul, neg_mul, Matrix.smul_mul, ← smul_neg,
      eq_neg_of_add_eq_zero_right h]
  have h2 := exp_semiconj h1
  rwa [neg_neg, Matrix.exp_transpose, ← exp_map_star] at h2

end Cx

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem piInf_cA (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (z : AE F E) :
    piInf τ (cA σ z) = star (piInf τ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, star_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, star_add]
  | tmul a x =>
    change piInf τ (a ⊗ₜ[F] σ x) = _
    rw [piInf_tmul, piInf_tmul, h.2.2.2, star_mul', show star (InfinitePlace.Completion.extensionEmbedding w (a.1 w)) = _ from
      Complex.conj_eq_iff_im.2 (im_extension h.1 w _)]

theorem map_incM {w : InfinitePlace F} (τ : EmbOver E w) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  exact (piInf_tmul τ 1 (J i j)).trans (by rw [show (1 : AF F).1 w = 1 from rfl, map_one, one_mul]; rfl)

theorem continuous_realAd : Continuous (realAd F) := by
  refine Continuous.prodMk (f := fun t => (realAd F t).1) (g := fun _ => (0 : Af F)) ?_ continuous_const
  refine continuous_pi fun w => ?_
  refine (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.isInducing.continuous_iff.2 ?_
  have e : (InfinitePlace.Completion.extensionEmbedding w) ∘ (fun t => (realAd F t).1 w) = fun t : ℝ => (t : ℂ) :=
    funext fun t => GlobalTheory.CompanionTheory.RealAdeleComponent.extensionEmbedding_evInf_realAd w t
  exact e ▸ Complex.continuous_ofReal

theorem exists_section (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    ∃ s : (InfinitePlace F → ℂ) → AE F E, Continuous s ∧ (∀ z, At (evI F) (s z)) ∧ ∀ z w, piInf (τ w) (s z) = z w := by
  classical
  choose x hx hx' using fun w : InfinitePlace F =>
    GlobalTheory.CompanionTheory.RealPlaceAdele.exists_adele_piInf σ h τ (Pi.single w 1)
  choose y hy hy' using fun w : InfinitePlace F =>
    GlobalTheory.CompanionTheory.RealPlaceAdele.exists_adele_piInf σ h τ (Pi.single w Complex.I)
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  refine ⟨fun z => ∑ w, (realAd F (z w).re • x w + realAd F (z w).im • y w), ?_, fun z c hc => ?_, fun z w => ?_⟩
  · have hr : ∀ (a : AE F E) (f : (InfinitePlace F → ℂ) → ℝ), Continuous f → Continuous fun z => realAd F (f z) • a :=
      fun a f hf => ((continuous_realAd (F := F)).comp hf).smul (continuous_const (y := a))
    refine continuous_finsetSum _ fun w _ => Continuous.add (hr _ _ ?_) (hr _ _ ?_)
    · exact Complex.continuous_re.comp (continuous_apply (A := fun _ => ℂ) w)
    · exact Complex.continuous_im.comp (continuous_apply (A := fun _ => ℂ) w)
  · rw [Finset.smul_sum]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [smul_add, smul_comm c, smul_comm c, hx w c hc, hy w c hc, smul_zero, smul_zero, add_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum, Finset.sum_eq_single w]
      · rw [map_add (f := _), GlobalTheory.CompanionTheory.RealAdeleComponent.piInf_realAd_smul, GlobalTheory.CompanionTheory.RealAdeleComponent.piInf_realAd_smul, hx', hy',
        Pi.single_eq_same, Pi.single_eq_same, mul_one, Complex.re_add_im]
      · intro v _ hv
        rw [map_add (f := _), GlobalTheory.CompanionTheory.RealAdeleComponent.piInf_realAd_smul, GlobalTheory.CompanionTheory.RealAdeleComponent.piInf_realAd_smul, hx', hy',
        Pi.single_eq_of_ne hv.symm, Pi.single_eq_of_ne hv.symm, mul_zero, mul_zero, add_zero]
      · simp

variable {d : ℕ}

theorem mat_ext (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {u v : Matrix (Fin d) (Fin d) (AE F E)}
    (hf : ∀ c : AF F, evI F c = 0 → c • u = c • v) (e : ∀ w, u.map (piInf (τ w)) = v.map (piInf (τ w))) : u = v := by
  ext i j
  refine sub_eq_zero.1 (eq_zero_of_piInf σ h τ _ (fun c hc => ?_) fun w => ?_)
  · rw [smul_sub]
    exact sub_eq_zero.2 (congrFun (congrFun (hf c hc) i) j)
  · rw [map_sub]
    exact sub_eq_zero.2 (congrFun (congrFun (e w) i) j)

omit [NumberField E] in
theorem at_iff {u : Matrix (Fin d) (Fin d) (AE F E)} :
    At (evI F) (u - 1) ↔ ∀ c : AF F, evI F c = 0 → c • u = c • (1 : Matrix (Fin d) (Fin d) (AE F E)) :=
  forall_congr' fun c => forall_congr' fun _ => by rw [smul_sub, sub_eq_zero]

theorem exists_matSection (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (d : ℕ) :
    ∃ S : (InfinitePlace F → Matrix (Fin d) (Fin d) ℂ) → Matrix (Fin d) (Fin d) (AE F E), Continuous S ∧
      (∀ z (c : AF F), evI F c = 0 → c • S z = c • (1 : Matrix (Fin d) (Fin d) (AE F E))) ∧
      ∀ z w, (S z).map (piInf (τ w)) = z w := by
  obtain ⟨s, hs, hA, hp⟩ := exists_section h τ
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  refine ⟨fun z => Matrix.of fun i j => (1 : Matrix (Fin d) (Fin d) (AE F E)) i j +
    s fun w => z w i j - (1 : Matrix (Fin d) (Fin d) ℂ) i j, ?_, fun z c hc => ?_, fun z w => ?_⟩
  · refine continuous_matrix fun i j => continuous_const.add (hs.comp (continuous_pi fun w => ?_))
    exact ((continuous_apply w).matrix_elem i j).sub continuous_const
  · ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply]
    rw [smul_add, hA _ c hc, add_zero]
  · ext i j
    have e := congrFun (congrFun (Matrix.map_one (n := Fin d) (piInf (τ w)) (map_zero _) (map_one _)) i) j
    rw [Matrix.map_apply] at e
    simp only [Matrix.map_apply, Matrix.of_apply]
    rw [map_add (f := _), hp, e, add_sub_cancel]

end ExponentialLineExistence

open ExponentialLineExistence in
theorem lineEx_of : LineEx := by
  intro F E _ _ _ _ _ σ h τ d W _ Y hY
  obtain ⟨S, hS, hf, hp⟩ := exists_matSection h τ d
  let g : ℝ → Matrix (Fin d) (Fin d) (AE F E) := fun t => S fun w => NormedSpace.exp ((t : ℂ) • Y w)
  have gp : ∀ t w, (g t).map (piInf (τ w)) = NormedSpace.exp ((t : ℂ) • Y w) := fun t w => hp _ w
  have gf : ∀ t (c : AF F), evI F c = 0 → c • g t = c • (1 : Matrix (Fin d) (Fin d) (AE F E)) := fun t => hf _
  have gc : Continuous g := hS.comp (continuous_pi fun w =>
    continuous_exp_mat.comp (Complex.continuous_ofReal.smul continuous_const))
  have g0 : g 0 = 1 := mat_ext h τ (gf 0) fun w => by
    rw [gp, Matrix.map_one _ (map_zero _) (map_one _), Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero]
  have ga : ∀ s t, g (s + t) = g s * g t := fun s t => mat_ext h τ
    (fun c hc => by rw [gf _ c hc, ← Matrix.smul_mul, gf _ c hc, Matrix.smul_mul, Matrix.one_mul, gf _ c hc])
    fun w => by rw [Matrix.map_mul, gp, gp, gp, exp_line_add]
  have gu : ∀ t, (g t)ᵀ * incM F W.J * (g t).map (cA σ) = incM F W.J := fun t => mat_ext h τ
    (fun c hc => by
      have e : ∀ u : Matrix (Fin d) (Fin d) (AE F E), c • u.map (cA σ) = (c • u).map (cA σ) := fun u => by
        ext i j
        simp only [Matrix.smul_apply, Matrix.map_apply, map_smul]
      rw [← Matrix.smul_mul, ← Matrix.smul_mul, ← Matrix.transpose_smul, gf _ c hc, Matrix.transpose_smul,
        Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, ← Matrix.mul_smul, e, gf _ c hc, ← e,
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_smul, Matrix.mul_one])
    fun w => by
      have e : ((g t).map (cA σ)).map (piInf (τ w)) = ((g t).map (piInf (τ w))).map star := by
        ext i j
        exact piInf_cA h _ _
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, map_incM, e, gp]
      exact exp_unitary (hY w) t
  let G : ℝ → GL (Fin d) (AE F E) := fun t =>
    ⟨g t, g (-t), by rw [← ga, add_neg_cancel, g0], by rw [← ga, neg_add_cancel, g0]⟩
  let γ : Multiplicative ℝ →* UA σ W.J :=
    { toFun := fun t => ⟨G t.toAdd, gu _⟩
      map_one' := Subtype.ext (Units.ext g0)
      map_mul' := fun s t => Subtype.ext (Units.ext (ga _ _)) }
  refine ⟨γ, ⟨?_, fun t => at_iff.2 (gf _)⟩, fun w t => gp t w, fun γ' hγ' hG => ?_⟩
  · refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
    · exact gc.comp continuous_toAdd
    · exact (gc.comp continuous_neg).comp continuous_toAdd
  · refine MonoidHom.ext fun t => Subtype.ext (Units.ext ?_)
    refine mat_ext h τ (u := mat (γ' t)) (v := g t.toAdd) (fun c hc => ?_) fun w => ?_
    · rw [at_iff.1 (hγ'.2 t) c hc, gf _ c hc]
    · rw [gp]
      exact hG w t.toAdd

end PositivityTheory.ThKEst

end
end

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.LineGen
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace ExponentialLineGeneration

set_option linter.unusedSectionVars false

section Banach

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

theorem exists_deriv {g : ℝ → A} (hc : Continuous g) (h0 : g 0 = 1) (ha : ∀ s t, g (s + t) = g s * g t) :
    ∃ Y : A, ∀ t, HasDerivAt g (g t * Y) t := by
  let G : ℝ → A := fun t => ∫ s in (0 : ℝ)..t, g s
  have hG : ∀ t, HasDerivAt G (g t) t := fun t => (hc.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hG0 : G 0 = 0 := intervalIntegral.integral_same
  have h1 : Tendsto (slope G 0) (𝓝[≠] 0) (𝓝 1) := by
    have := hasDerivAt_iff_tendsto_slope.1 (hG 0)
    rwa [h0] at this
  have h2 : ∀ᶠ h in 𝓝[≠] (0 : ℝ), IsUnit (slope G 0 h) := h1 (Units.isOpen.mem_nhds isUnit_one)
  obtain ⟨h, hu, hne⟩ := (h2.and self_mem_nhdsWithin).exists
  have hne' : h ≠ 0 := hne
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  rw [slope_def_module, hG0, sub_zero, sub_zero] at hv
  have hv' : G h * (h⁻¹ • v) = 1 := by rw [mul_smul_comm, ← smul_mul_assoc, hv]
  set u := h⁻¹ • v
  have key : ∀ t, g t * G h = G (t + h) - G t := by
    intro t
    have e1 : g t * G h = ∫ s in (0 : ℝ)..h, g (t + s) := by
      simp only [ha]
      exact ((ContinuousLinearMap.mul ℝ A (g t)).intervalIntegral_comp_comm (hc.intervalIntegrable 0 h)).symm
    rw [e1, intervalIntegral.integral_comp_add_left, add_zero]
    exact (intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)).symm
  have e : g = fun t => (G (t + h) - G t) * u := by
    funext t
    rw [← key, mul_assoc, hv', mul_one]
  refine ⟨(g h - 1) * u, fun t => ?_⟩
  have d := (((hG (t + h)).comp_add_const t h).sub (hG t)).mul_const u
  have e2 : g t * ((g h - 1) * u) = (g (t + h) - g t) * u := by
    rw [← mul_assoc, mul_sub, mul_one, ha]
  rw [e2]
  exact d.congr_of_eventuallyEq (Eventually.of_forall fun s => congrFun e s)

theorem exists_exp {g : ℝ → A} (hc : Continuous g) (h0 : g 0 = 1) (ha : ∀ s t, g (s + t) = g s * g t) :
    ∃ Y : A, HasDerivAt g Y 0 ∧ ∀ t, g t = NormedSpace.exp (t • Y) := by
  obtain ⟨Y, hY⟩ := exists_deriv hc h0 ha
  refine ⟨Y, by simpa [h0] using hY 0, fun t => ?_⟩
  have d : ∀ s : ℝ, HasDerivAt (fun s : ℝ => g s * NormedSpace.exp ((t - s) • Y)) 0 s := by
    intro s
    have d1 := (hasDerivAt_exp_smul_const' (𝕂 := ℝ) Y (t - s)).scomp s ((hasDerivAt_id s).const_sub t)
    have d2 := (hY s).mul d1
    refine d2.congr_deriv ?_
    simp [mul_assoc]
  have c := is_const_of_deriv_eq_zero (fun s => (d s).differentiableAt) (fun s => (d s).deriv) t 0
  simpa [h0] using c

end Banach

set_option backward.isDefEq.respectTransparency false in
theorem mat_exp {d : ℕ} {g : ℝ → Matrix (Fin d) (Fin d) ℂ} (hc : Continuous g) (h0 : g 0 = 1)
    (ha : ∀ s t, g (s + t) = g s * g t) :
    ∃ Y : Matrix (Fin d) (Fin d) ℂ, (∀ i j, HasDerivAt (fun t => g t i j) (Y i j) 0) ∧
      ∀ t : ℝ, g t = NormedSpace.exp ((t : ℂ) • Y) := by
  open scoped Matrix.Norms.Operator in
  obtain ⟨Y, h1, h2⟩ := exists_exp (A := Matrix (Fin d) (Fin d) ℂ) hc h0 ha
  refine ⟨Y, fun i j => ?_, fun t => ?_⟩
  · exact (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j :
      Matrix (Fin d) (Fin d) ℂ →ₗ[ℝ] ℂ)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  · rw [h2 t, Complex.coe_smul]

theorem lie_of_unitary {d : ℕ} {g : ℝ → Matrix (Fin d) (Fin d) ℂ} {J Y : Matrix (Fin d) (Fin d) ℂ} (h0 : g 0 = 1)
    (hd : ∀ i j, HasDerivAt (fun t => g t i j) (Y i j) 0) (hu : ∀ t, (g t)ᵀ * J * (g t).map star = J) :
    Yᵀ * J + J * Y.map star = 0 := by
  ext i j
  have d1 : HasDerivAt (fun t => ∑ l, (∑ k, g t k i * J k l) * star (g t l j))
      (∑ l, ((∑ k, Y k i * J k l) * star (g 0 l j) + (∑ k, g 0 k i * J k l) * star (Y l j))) 0 :=
    HasDerivAt.fun_sum fun l _ => (HasDerivAt.fun_sum fun k _ => (hd k i).mul_const (J k l)).fun_mul (hd l j).star
  have e : (fun t => ∑ l, (∑ k, g t k i * J k l) * star (g t l j)) = fun _ => J i j := by
    funext t
    rw [← congrFun (congrFun (hu t) i) j]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rw [e] at d1
  have z := d1.unique (hasDerivAt_const (0 : ℝ) (J i j))
  have e1 : (Yᵀ * J * (g 0).map star + (g 0)ᵀ * J * Y.map star) i j = 0 := by
    rw [← z, Finset.sum_add_distrib]
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  rwa [h0, Matrix.map_one _ (star_zero _) (star_one _), Matrix.mul_one, Matrix.transpose_one, Matrix.one_mul] at e1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem piInf_tmul' {w : InfinitePlace F} (τ : EmbOver E w) (a : AF F) (x : E) :
    piInf τ (a ⊗ₜ[F] x) = InfinitePlace.Completion.extensionEmbedding w (a.1 w) * τ.1 x := by
  change infEmb τ (evInf F w a ⊗ₜ[F] x) = _
  rw [infEmb_tmul]
  rfl

theorem continuous_piInf {w : InfinitePlace F} (τ : EmbOver E w) : Continuous (piInf τ) := by
  refine IsModuleTopology.continuous_of_ringHom (R := AF F) (piInf τ) ?_
  have h : ⇑((piInf τ).comp (algebraMap (AF F) (AE F E))) =
      fun a : AF F => InfinitePlace.Completion.extensionEmbedding w (a.1 w) := by
    funext a
    change piInf τ (a ⊗ₜ[F] (1 : E)) = _
    rw [piInf_tmul', map_one, mul_one]
  rw [h]
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
    ((continuous_apply w).comp continuous_fst)

theorem piInf_cA (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) (z : AE F E) :
    piInf τ (cA σ z) = star (piInf τ z) := by
  have hw : w.IsReal := h.1.isReal w
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, star_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, star_add]
  | tmul a x =>
    change piInf τ (a ⊗ₜ[F] σ x) = _
    rw [piInf_tmul', piInf_tmul', h.2.2.2, star_mul',
      ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw]
    rw [Complex.star_def, Complex.conj_ofReal]

theorem map_incM {w : InfinitePlace F} (τ : EmbOver E w) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  exact (piInf_tmul' τ 1 (J i j)).trans (by rw [show (1 : AF F).1 w = 1 from rfl, map_one, one_mul]; rfl)

end ExponentialLineGeneration

open ExponentialLineGeneration in
theorem lineGen_of : LineGen := by
  intro F E _ _ _ _ _ σ h τ d W _ γ hγ
  have main : ∀ w, ∃ Y : Matrix (Fin d) (Fin d) ℂ,
      Yᵀ * W.J.map (τ w).1 + W.J.map (τ w).1 * Y.map star = 0 ∧
      ∀ t : ℝ, (mat (γ (Multiplicative.ofAdd t))).map (piInf (τ w)) = NormedSpace.exp ((t : ℂ) • Y) := by
    intro w
    let g : ℝ → Matrix (Fin d) (Fin d) ℂ := fun t => (mat (γ (Multiplicative.ofAdd t))).map (piInf (τ w))
    have hm : Continuous (mat : UA σ W.J → Matrix (Fin d) (Fin d) (AE F E)) :=
      Units.continuous_val.comp continuous_subtype_val
    have hc : Continuous g :=
      ((hm.comp (hγ.1.comp continuous_ofAdd))).matrix_map (continuous_piInf (τ w))
    have h0 : g 0 = 1 := by
      change (mat (γ 1)).map (piInf (τ w)) = 1
      rw [map_one]
      exact Matrix.map_one _ (map_zero _) (map_one _)
    have ha : ∀ s t, g (s + t) = g s * g t := by
      intro s t
      change (mat (γ (Multiplicative.ofAdd s * Multiplicative.ofAdd t))).map (piInf (τ w)) = _
      rw [map_mul]
      exact Matrix.map_mul
    obtain ⟨Y, h1, h2⟩ := mat_exp hc h0 ha
    refine ⟨Y, lie_of_unitary h0 h1 fun t => ?_, h2⟩
    have hu : (mat (γ (Multiplicative.ofAdd t)))ᵀ * incM F W.J * (mat (γ (Multiplicative.ofAdd t))).map (cA σ) =
        incM F W.J := (γ (Multiplicative.ofAdd t)).2
    have e : ((mat (γ (Multiplicative.ofAdd t))).map (cA σ)).map (piInf (τ w)) = (g t).map star := by
      ext i j
      exact piInf_cA h _ _
    have hv := congrArg (fun M : Matrix (Fin d) (Fin d) (AE F E) => M.map (piInf (τ w))) hu
    simp only [Matrix.map_mul] at hv
    rwa [Matrix.transpose_map, map_incM, e] at hv
  choose Y hY using main
  exact ⟨Y, fun w => (hY w).1, fun w => (hY w).2⟩

end PositivityTheory.ThKEst

end
end

-- bundled from Development.WeilBound.ThetaLifts.FrameEstimates.SoSemi
section
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem qht_le {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J) {γ : UA σ J} (hγ : γ ∈ ratU σ J) : qht g ≤ ht (γ * g) :=
  ciInf_le (OrderBot.bddBelow _) (⟨γ, hγ⟩ : ratU σ J)

theorem psum_self {r : ℕ} (t : Fin r → ℝ) : psum t r = ∑ i, t i :=
  Finset.sum_congr rfl fun j _ => if_pos j.2

theorem psum_le {r : ℕ} {t : Fin r → ℝ} (h : t ∈ Cone r) (i : ℕ) : psum t i ≤ ∑ j, t j :=
  Finset.sum_le_sum fun j _ => by split_ifs; exacts [le_rfl, h.2 j]

theorem soSemiU_of (hT : GrpTop) (hE : EpsOf) (hS : SiegelAll) (hQ : SqSo) (hI : LatInv) (hK : LatCpt) (hL : LatFull)
    (hP : PosWt) : SoSemiU := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp N₀
  have hc := hp.base.cm
  obtain ⟨hJ, -, -⟩ := hE F E σ B hp.base n X r s (Or.inl hp.herm)
  obtain ⟨hJ', -, -⟩ := hE F E σ B hp.base d W r' s' (Or.inr hp.skew)
  obtain ⟨fr, hg, -, ⟨Ω, hΩ, hcov⟩, -, ⟨C₀, k₀, hht⟩⟩ := hS F E σ hc n X.J hJ
  obtain ⟨fr', hg', -, ⟨Ω', hΩ', hcov'⟩, -, hht'⟩ := hS F E σ hc d W.J hJ'
  obtain ⟨A, k₁, hA0, hAk⟩ := exp_le_ht hT hc hJ' hht' hΩ'
  obtain ⟨B₀, hB₀⟩ := (hT F E σ hc n X.J hJ).2.2.2.2.2.2.2 Ω hΩ
  set D : ℕ := Module.finrank ℚ E with hD
  set m : ℕ := D * d + 2 * (k₀ * N₀) with hm
  obtain ⟨N, hN⟩ := hL F E σ hc B.emb n d X.J W.J hJ hJ' fr fr' hg hg' m
  refine ⟨k₁ * (m + D * n), fun φ hφ => ?_⟩
  obtain ⟨p, C, hpc, hC, hb⟩ := hQ F E σ B n d X W M χX χW om r s r' s' hp φ hφ N
  obtain ⟨C₁, K₁, hC₁, h₁⟩ := hK F E σ hc B.emb n d X.J W.J hJ hJ' Ω Ω' hΩ hΩ' C N hC
  obtain ⟨K₂, h₂⟩ := hN C₁ hC₁
  set K : ℝ := (K₁ * K₂ + 1) * (max C₀ 0 * B₀) ^ N₀ * A ^ (m + D * n) with hKdef
  have hK0 : 0 ≤ K := by positivity
  refine ⟨NNReal.mk K hK0 • p, (continuous_const.mul hpc : Continuous fun f => K * p f), fun f g h => ?_⟩
  obtain ⟨γ, hγ, s₁, hs, κ, hκ, e⟩ := hcov g
  obtain ⟨δ, hδ, t, ht', κ', hκ', e'⟩ := hcov' h
  have hpf : 0 ≤ p f := apply_nonneg p f
  obtain ⟨hw, hv0, hv⟩ := hP n d fr.r fr'.r s₁ t hs ht'
  set S := ∑ i, s₁ i with hSdef
  set T := ∑ j, t j with hTdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => hs.2 i
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun i _ => ht'.2 i
  have hST : S ≤ T + viol s₁ t := by
    have := hv fr.r le_rfl
    rw [psum_self] at this
    linarith [psum_le ht' fr.r]
  have e1 := hb f g h
  rw [← hI F E σ hc B.emb n d X.J W.J hJ hJ' C N (fullRank E n d) (by simp) γ hγ δ hδ g h, e, e'] at e1
  have e2 := e1.trans (mul_le_mul_right ((h₁ _ _ _ κ hκ κ' hκ').trans (mul_le_mul_right (h₂ s₁ hs t ht') _)) _)
  set x : ℝ := D * posWt n d s₁ t - m * viol s₁ t with hx
  have e3 : ‖theta om (pureA F f φ) g h‖ ^ 2 ≤ p f ^ 2 * (K₁ * (K₂ * Real.exp x)) := by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow hpf, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_coe_nnreal (p := K₂), ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)] at e2
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 e2
  have e4 : ‖theta om (pureA F f φ) g h‖ ≤ p f * ((K₁ * K₂ + 1) * Real.exp (x / 2)) := by
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    refine e3.trans ?_
    have h5 : Real.exp (x / 2) ^ 2 = Real.exp x := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have h6 : (0 : ℝ) ≤ K₁ * K₂ := by positivity
    rw [mul_pow, mul_pow, h5, ← mul_assoc (K₁ : ℝ)]
    gcongr
    nlinarith
  have e5 : (qht g : ℝ) ≤ max C₀ 0 * B₀ * Real.exp (k₀ * S) := by
    have a1 : (qht g : ℝ) ≤ ht (fr.a s₁) * B₀ := by
      have := (qht_le g hγ).trans (e ▸ (ht_mul_le _ _).trans (mul_le_mul_right (hB₀ κ hκ) _))
      exact_mod_cast this
    have a2 : (ht (fr.a s₁) : ℝ) ≤ max C₀ 0 * Real.exp (k₀ * S) :=
      (hht s₁ hs).1.trans (by gcongr; exact le_max_left _ _)
    calc _ ≤ _ := a1
      _ ≤ max C₀ 0 * Real.exp (k₀ * S) * B₀ := by gcongr
      _ = _ := by ring
  have e6 : x / 2 + N₀ * (k₀ * S) ≤ ((m + D * n : ℕ) : ℝ) * T := by
    have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg _
    have b1 : (D : ℝ) * posWt n d s₁ t ≤ D * (d * S + n * T) := mul_le_mul_of_nonneg_left hw hD0
    have hmr : (m : ℝ) = D * d + 2 * (k₀ * N₀) := by rw [hm]; push_cast; ring
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have b2 : (m : ℝ) * S ≤ m * (T + viol s₁ t) := mul_le_mul_of_nonneg_left hST hm0
    have b3 : (0 : ℝ) ≤ m * T := mul_nonneg hm0 hT0
    have b4 : (0 : ℝ) ≤ D * n * T := by positivity
    have b5 : (m : ℝ) * S = D * d * S + 2 * (N₀ * (k₀ * S)) := by rw [hmr]; ring
    rw [hx]
    push_cast
    nlinarith
  have e7 : Real.exp (((m + D * n : ℕ) : ℝ) * T) ≤ A ^ (m + D * n) * (ht h : ℝ) ^ (k₁ * (m + D * n)) := by
    rw [Real.exp_nat_mul, pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (Real.exp_pos _).le (hAk h δ hδ t ht' κ' hκ' e') _
  calc ‖theta om (pureA F f φ) g h‖ * (qht g : ℝ) ^ N₀
      ≤ p f * ((K₁ * K₂ + 1) * Real.exp (x / 2)) * (max C₀ 0 * B₀ * Real.exp (k₀ * S)) ^ N₀ := by gcongr
    _ = p f * ((K₁ * K₂ + 1) * (max C₀ 0 * B₀) ^ N₀) * Real.exp (x / 2 + N₀ * (k₀ * S)) := by
        rw [Real.exp_add, mul_pow _ (Real.exp _), ← Real.exp_nat_mul]; ring
    _ ≤ p f * ((K₁ * K₂ + 1) * (max C₀ 0 * B₀) ^ N₀) * (A ^ (m + D * n) * (ht h : ℝ) ^ (k₁ * (m + D * n))) := by
        gcongr
        exact (Real.exp_le_exp.2 e6).trans e7
    _ = (K * p f) * (ht h : ℝ) ^ (k₁ * (m + D * n)) := by rw [hKdef]; ring

theorem domSoU_of (hE : EpsOf) (hV : FinVolU) (hS : SoSemiU) : DomSoU := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp
  obtain ⟨hJ, -, -⟩ := hE F E σ B hp.base n X r s (Or.inl hp.herm)
  obtain ⟨k, hk⟩ := hS F E σ B n d X W M χX χW om r s r' s' hp 0
  refine ⟨k, fun φ hφ => ?_⟩
  obtain ⟨p, hpc, hb⟩ := hk φ hφ
  refine ⟨p, fun _ => 1, hpc, measurable_const, ?_, fun f g h => ?_⟩
  · rw [setLIntegral_one]
    exact hV F E σ hp.base.cm n X.J hJ M.μ M.dom hp.good.haar hp.good.dom
  · rw [mul_one, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (by simpa using hb f g h)

end PositivityTheory.ThKEst

end
end

