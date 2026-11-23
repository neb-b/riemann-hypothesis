module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.ActLaws
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ScatOnSpan
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.FamEx
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.famEx :
    (ForAllC fun _ _ _ μ _ _ _ _ _ _ _ _ A A' => TruncCpt μ A A') → UnitB → UnipotentBlockPairs → PositivityTheory.Rg.Tf.IntegralApplyAeEq.Main → FamEx := by
  intro hC hU hF hM K _ _ _ μ _ μ₂ _ τ₁ τ₂ hp D d d' A A' P hP
  obtain ⟨a, β, β', sm, hk, st, ⟨k, c, -⟩, ⟨k', c', -⟩, u, u'⟩ := hU K μ μ₂ τ₁ τ₂ hp D d d' A A'
  obtain ⟨sh, ca⟩ := hF K μ μ₂ τ₁ τ₂ hp D d d' A A'
  have sa : IsSelfAdjoint (Rop μ a) := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff', UpperTheory.ConvolutionTheory.K.ropAdj, st]
  obtain ⟨N, h1, h2⟩ := scat_on_span hM A.J A'.J P hP sh ca (Rop μ a) β β' k k' u u' sa c c'
    fun T Λ hT hΛ => hC K μ μ₂ τ₁ τ₂ hp D d d' A A' a P Λ T sm hk hP hT hΛ
  refine ⟨N, Module.finrank ℂ (Eu d), ⟨fun f b b' hb hb' => h1 _ b b' hb.1 hb'.1 hb.2.1 hb'.2.1, h2⟩, ?_⟩
  intro Y s s' hs hs' w
  obtain ⟨κ, m1, m2, m3⟩ := (actLaws A.J).2.2.2.2 _ Y β s k c hs
  obtain ⟨κ', n1, n2, n3⟩ := (actLaws A'.J).2.2.2.2 _ Y β' s' k' c' hs'
  have e := h1 _ κ κ' m1 n1 m2 n2 w
  rw [m3, n3, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, h1 _ β β' k k' c c'] at e
  obtain ⟨g, hg⟩ := u.exists_left_inv
  have inv : ∀ x, g (symb β 0 x) = x := fun x => congrArg (fun B : Eu d →L[ℂ] Eu d => B x) hg
  rw [← inv (N _), e, inv]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.FamExp
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci
open PositivityTheory.Rg.Fx hiding Fam
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

section SlopeTestRemainingChoices

variable {H V W : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W]

omit [FiniteDimensional ℂ V] [CompleteSpace V] [FiniteDimensional ℂ W] [CompleteSpace W] in
private theorem lift_sh (S : V →L[ℂ] W) (S' : W →L[ℂ] V) (c : V →L[ℂ] V) (t : ℝ) (x : L W) :
    (S ∘L c ∘L S').compLpL 2 volume (sh W t x) =
      S.compLpL 2 volume (c.compLpL 2 volume (sh V t (S'.compLpL 2 volume x))) := by
  refine Lp.ext ?_
  filter_upwards [(S ∘L c ∘L S').coeFn_compLpL (sh W t x), sh_ae W t x,
    S.coeFn_compLpL (c.compLpL 2 volume (sh V t (S'.compLpL 2 volume x))),
    c.coeFn_compLpL (sh V t (S'.compLpL 2 volume x)), sh_ae V t (S'.compLpL 2 volume x),
    (measurePreserving_add_right volume t).quasiMeasurePreserving.ae (S'.coeFn_compLpL x)] with y h1 h2 h3 h4 h5 h6
  rw [h1, h2, h3, h4, h5, h6]; rfl

private theorem act_transp (J : L V →ₗᵢ[ℂ] H) (J' : L W →ₗᵢ[ℂ] H) (S : V →L[ℂ] W) (S' : W →L[ℂ] V) (T T' Y : H →L[ℂ] H)
    (hT : ∀ u, T (J u) = J' (S.compLpL 2 volume u)) (hT' : ∀ w, T' (J' w) = J (S'.compLpL 2 volume w))
    (σ : ℂ → V →L[ℂ] V) (h : Act J Y σ) : Act J' (T ∘L Y ∘L T') fun z => S ∘L σ z ∘L S' := by
  obtain ⟨u, κ, hk, h1, h2⟩ := h
  have hk' : Ker fun t => S ∘L κ t ∘L S' := by
    refine ⟨continuous_const.clm_comp (hk.1.clm_comp continuous_const), hk.2.mono fun t ht h0 => ht ?_⟩
    simp [h0]
  refine ⟨u.mapRange (fun c => S ∘L c ∘L S') (by simp), fun t => S ∘L κ t ∘L S', hk', fun x => ?_, fun z => ?_⟩
  · rw [Finsupp.sum_mapRange_index fun a => Lp.ext (by
      filter_upwards [(0 : W →L[ℂ] W).coeFn_compLpL (sh W a x), Lp.coeFn_zero W 2 (volume : Measure ℝ)] with y a b
      rw [a, b]; rfl)]
    simp only [ContinuousLinearMap.comp_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hT', h1, hT, map_add (f := _), Finsupp.sum, Finsupp.sum, map_sum, (convSpec _ hk' x).2.2, (convSpec _ hk _).2.2,
      ← ContinuousLinearMap.integral_comp_comm _ (convSpec _ hk _).2.1]
    simp only [lift_sh]
  · beta_reduce
    rw [Finsupp.sum_mapRange_index (by simp), h2]
    have hi : Integrable fun t : ℝ => Complex.exp (z * t) • κ t := by
      have c0 : Continuous fun t : ℝ => Complex.exp (z * t) := by fun_prop
      refine Continuous.integrable_of_hasCompactSupport (c0.smul hk.1) (hk.2.mono fun t ht h0 => ht ?_)
      show Complex.exp (z * t) • κ t = 0
      rw [h0, smul_zero]
    let Φ : (V →L[ℂ] V) →L[ℂ] (W →L[ℂ] W) :=
      (ContinuousLinearMap.compL ℂ W V W S) ∘L ((ContinuousLinearMap.compL ℂ W V V).flip S')
    have hΦ : ∀ c, Φ c = S ∘L c ∘L S' := fun c => rfl
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← hΦ, symb, Finsupp.sum, map_add (f := _), map_sum, map_smul]
    rw [← Φ.integral_comp_comm hi]
    simp only [map_smul]

omit [FiniteDimensional ℂ V] [CompleteSpace V] [CompleteSpace H] in
private theorem act_congr (J : L V →ₗᵢ[ℂ] H) (Y Y' : H →L[ℂ] H) (σ : ℂ → V →L[ℂ] V) (e : ∀ u, Y' (J u) = Y (J u))
    (h : Act J Y σ) : Act J Y' σ := by
  obtain ⟨u, κ, hk, h1, h2⟩ := h
  exact ⟨u, κ, hk, fun x => (e x).trans (h1 x), h2⟩

private theorem act_comm (J : L V →ₗᵢ[ℂ] H) (Y Y' : H →L[ℂ] H) (σ σ' : ℂ → V →L[ℂ] V) (e : Commute Y Y')
    (h : Act J Y σ) (h' : Act J Y' σ') : Commute (σ 0) (σ' 0) := by
  have a := ((actLaws J).2.2.2.1 _ _ _ _ h h').2
  have b := ((actLaws J).2.2.2.1 _ _ _ _ h' h).2
  have e' : Y ∘L Y' = Y' ∘L Y := e
  rw [e'] at a
  exact congrFun (actUniq J _ _ _ a b) 0

private theorem eigP_comm {d : ℕ} (a u : Eu d →L[ℂ] Eu d) (ha : IsSelfAdjoint a) (h : Commute u a) (x : ℝ) :
    Commute (eigP a x) u := by
  have key : ∀ w : Eu d →L[ℂ] Eu d, Commute w a → ∀ v ∈ Module.End.eigenspace (a : Eu d →ₗ[ℂ] Eu d) (x : ℂ),
      w v ∈ Module.End.eigenspace (a : Eu d →ₗ[ℂ] Eu d) (x : ℂ) := by
    intro w hw v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    have h1 : w (a v) = a (w v) := DFunLike.congr_fun hw.eq v
    have h2 : a v = (x : ℂ) • v := hv
    show a (w v) = _
    rw [← h1, h2, map_smul]
  have h' : Commute (star u) a := by
    have := h.star_star
    rwa [ha.star_eq] at this
  refine ContinuousLinearMap.ext fun v => ?_
  show eigP a x (u v) = u (eigP a x v)
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (key u h _ (Submodule.starProjection_apply_mem _ v)) fun w hw => ?_
  rw [← map_sub, ← ContinuousLinearMap.adjoint_inner_right]
  exact Submodule.starProjection_inner_eq_zero v _ (key _ h' w hw)

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.famExp :
    ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {μ : Measure (normOneGL (K := E) (n := (2 + 2)))} [μ.IsHaarMeasure] {θ : Twist μ} {𝔢 : Side θ 2} (𝔵 : Fam 𝔢) (N : Eu 𝔵.d' ≃ₗᵢ[ℂ] Eu 𝔵.d) (C₀ : ℝ), Family2 μ 𝔵.A 𝔵.A' 𝔵.P N C₀ → 0 ≤ 𝔢.toAmp.A → ‖𝔢.toAmp.A‖ ≤ 1 →
      (∃ sp : Finset ℝ, (∀ x, x ∈ sp ↔ 0 < x ∧ Module.End.eigenspace (𝔵.a₀ : Eu 𝔵.d' →ₗ[ℂ] Eu 𝔵.d') (x : ℂ) ≠ ⊥) ∧ (∀ x ∈ sp, x ≤ 1) ∧
        ∀ x : ℝ, 0 < x → x ∉ sp → ∀ j, 𝔵.tr N x j = 0) ∧
      ∀ x : ℝ, ∃ (s : Finset ℂ) (c : ℂ → ℂ), 0 ∉ s ∧ ∀ᶠ j : ℕ in atTop, 𝔵.tr N x j = ∑ ζ ∈ s, c ζ * ζ ^ j := by
  intro E _ _ _ μ _ θ 𝔢 𝔵 N C₀ hF h0 h1
  have ha : Conv 𝔵.A'.J 𝔵.A'.J 𝔢.toAmp.A 𝔵.βa := 𝔢.a_op ▸ 𝔵.a_acts.2.1
  obtain ⟨p0, p1⟩ : 0 ≤ 𝔵.a₀ ∧ ‖𝔵.a₀‖ ≤ 1 := posSymb 𝔵.A'.J _ _ 𝔵.a_acts.1 ha h0 h1
  refine ⟨?_, fun x => ?_⟩
  · have fin : {x : ℝ | 0 < x ∧ Module.End.eigenspace (𝔵.a₀ : Eu 𝔵.d' →ₗ[ℂ] Eu 𝔵.d') (x : ℂ) ≠ ⊥}.Finite :=
      ((Module.End.finite_hasEigenvalue (𝔵.a₀ : Eu 𝔵.d' →ₗ[ℂ] Eu 𝔵.d')).preimage
        Complex.ofReal_injective.injOn).subset fun x hx => hx.2
    refine ⟨fin.toFinset, fun x => fin.mem_toFinset, fun x hx => ?_, fun x hx hx' j => ?_⟩
    · obtain ⟨hx0, hx⟩ := fin.mem_toFinset.1 hx
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hx
      have e : 𝔵.a₀ v = (x : ℂ) • v := Module.End.mem_eigenspace_iff.1 hv
      have := (𝔵.a₀.le_opNorm v).trans (mul_le_mul_of_nonneg_right p1 (norm_nonneg v))
      rw [e, norm_smul, Complex.norm_real, Real.norm_of_nonneg hx0.le] at this
      exact le_of_mul_le_mul_right this (norm_pos_iff.2 hv0)
    · have hb : Module.End.eigenspace (𝔵.a₀ : Eu 𝔵.d' →ₗ[ℂ] Eu 𝔵.d') (x : ℂ) = ⊥ := by
        by_contra hb
        exact hx' (fin.mem_toFinset.2 ⟨hx, hb⟩)
      have : eigP 𝔵.a₀ x = 0 := by
        refine ContinuousLinearMap.ext fun v => ?_
        have := Submodule.starProjection_apply_mem (Module.End.eigenspace (𝔵.a₀ : Eu 𝔵.d' →ₗ[ℂ] Eu 𝔵.d') (x : ℂ)) v
        exact (Submodule.eq_bot_iff _).1 hb _ this
      simp [Fam.tr, this]
  · have sa : IsSelfAdjoint 𝔵.a₀ := IsSelfAdjoint.of_nonneg p0
    have aA : Act 𝔵.A'.J 𝔢.toAmp.A (symb 𝔵.βa) := (actLaws _).2.1 _ _ 𝔵.a_acts.1 ha
    have aG : Act 𝔵.A'.J (Rop μ 𝔢.g) (symb 𝔵.βg) := (actLaws _).2.1 _ _ 𝔵.g_acts.1 𝔵.g_acts.2.1
    have cP : ∀ i, Commute (eigP 𝔵.a₀ x) (𝔵.u i 0) := fun i =>
      eigP_comm _ _ sa (act_comm _ _ _ _ _ (𝔢.Uq_amp i) (𝔵.u_act i) aA) x
    let S : Eu 𝔵.d →L[ℂ] Eu 𝔵.d' := 𝔵.s.toContinuousLinearEquiv
    let S' : Eu 𝔵.d' →L[ℂ] Eu 𝔵.d := 𝔵.s.symm.toContinuousLinearEquiv
    let T' : L2 μ →L[ℂ] L2 μ :=
      𝔵.A.J.toContinuousLinearMap ∘L S'.compLpL 2 volume ∘L ContinuousLinearMap.adjoint 𝔵.A'.J.toContinuousLinearMap
    have hT : ∀ u, θ.U (𝔵.A.J u) = 𝔵.A'.J (S.compLpL 2 volume u) := fun u => 𝔵.s_op u _ (S.coeFn_compLpL u)
    have hT' : ∀ w, T' (𝔵.A'.J w) = 𝔵.A.J (S'.compLpL 2 volume w) := fun w => by
      have : ContinuousLinearMap.adjoint 𝔵.A'.J.toContinuousLinearMap (𝔵.A'.J w) = w := by
        refine ext_inner_left ℂ fun y => ?_
        rw [ContinuousLinearMap.adjoint_inner_right]
        exact 𝔵.A'.J.inner_map_map y w
      show 𝔵.A.J (S'.compLpL 2 volume (ContinuousLinearMap.adjoint 𝔵.A'.J.toContinuousLinearMap (𝔵.A'.J w))) = _
      rw [this]
    have hTT : ∀ w, θ.U (T' (𝔵.A'.J w)) = 𝔵.A'.J w := fun w => by
      rw [hT']
      refine 𝔵.s_op _ _ ?_
      filter_upwards [S'.coeFn_compLpL w] with y hy
      rw [hy]
      exact (𝔵.s.apply_symm_apply _).symm
    have perm : ∀ i w, symb 𝔵.βg 0 (𝔵.s (𝔵.v i 0 w)) = 𝔵.u (i + 1) 0 (symb 𝔵.βg 0 (𝔵.s w)) := fun i w => by
      have a := ((actLaws _).2.2.2.1 _ _ _ _ aG (act_transp _ _ S S' _ _ _ hT hT' _ (𝔵.v_act i))).2
      have b := ((actLaws _).2.2.2.1 _ _ _ _ (𝔵.u_act (i + 1)) aG).2
      have c := actUniq _ _ _ _ a (act_congr _ _ _ _ (fun y => ?_) b)
      · have := DFunLike.congr_fun (congrFun c 0) (𝔵.s w)
        simpa [S, S'] using this
      · have := DFunLike.congr_fun (𝔢.Uq_perm i) (T' (𝔵.A'.J y))
        simp only [ContinuousLinearMap.comp_apply] at this ⊢
        rw [this, hTT]
    let B : Module.End ℂ (Eu 𝔵.d') := ((eigP 𝔵.a₀ x ∘L symb 𝔵.βg 0 : Eu 𝔵.d' →L[ℂ] Eu 𝔵.d') : Eu 𝔵.d' →ₗ[ℂ] Eu 𝔵.d') ∘ₗ
      (𝔵.s.toLinearEquiv : Eu 𝔵.d →ₗ[ℂ] Eu 𝔵.d') ∘ₗ (N.toLinearEquiv : Eu 𝔵.d' →ₗ[ℂ] Eu 𝔵.d)
    have hB : ∀ w, B w = eigP 𝔵.a₀ x (symb 𝔵.βg 0 (𝔵.s (N w))) := fun w => rfl
    obtain ⟨s, c, hs, h⟩ := expForm (Eu 𝔵.d') 2 two_pos (fun i => (𝔵.u i 0 : Eu 𝔵.d' →ₗ[ℂ] Eu 𝔵.d')) B
      (fun i k => LinearMap.ext fun w =>
        DFunLike.congr_fun (act_comm _ _ _ _ _ (𝔢.Uq_comm i k) (𝔵.u_act i) (𝔵.u_act k)).eq w)
      (fun i => LinearMap.ext fun w => by
        show B (𝔵.u i 0 w) = 𝔵.u (i + 1) 0 (B w)
        rw [hB, hB, hF.2 _ _ _ (𝔵.v_act i) (𝔵.u_act i), perm]
        exact DFunLike.congr_fun (cP (i + 1)).eq _)
    refine ⟨s, c, hs, (eventually_ge_atTop (Module.finrank ℂ (Eu 𝔵.d'))).mono fun j hj => ?_⟩
    rw [← h j hj, Fam.tr, LinearMap.trace_comp_comm']
    congr 1
    refine LinearMap.ext fun w => ?_
    have e : ((𝔵.u 0 0 ^ j : Eu 𝔵.d' →L[ℂ] Eu 𝔵.d') : Eu 𝔵.d' →ₗ[ℂ] Eu 𝔵.d') = (𝔵.u 0 0 : Eu 𝔵.d' →ₗ[ℂ] Eu 𝔵.d') ^ j :=
      map_pow (ContinuousLinearMap.toLinearMapRingHom (R₁ := ℂ) (M₁ := Eu 𝔵.d')) _ j
    rw [Module.End.mul_apply, hB, ← e]
    exact DFunLike.congr_fun ((cP 0).pow_right j).eq _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.Regroup
section
open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci PositivityTheory.Rg.Fx
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

open Classical in
private lemma regroup {T : Type} (s : Finset T) (a : T → ℝ) (S : T → Finset ℂ) (c : T → ℂ → ℂ) (w : T → ℂ) (P : Finset (ℝ × ℂ))
    (hP : ∀ i ∈ s, ∀ ζ ∈ S i, (a i, ζ) ∈ P) (f : ℝ × ℂ → ℂ) :
    ∑ q ∈ P, (∑ i ∈ s, if a i = q.1 ∧ q.2 ∈ S i then w i * c i q.2 else 0) * f q =
      ∑ i ∈ s, w i * ∑ ζ ∈ S i, c i ζ * f (a i, ζ) := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mul_sum]
  symm
  have hinj : Set.InjOn (fun ζ : ℂ => (a i, ζ)) (S i) := fun z _ z' _ h => (Prod.ext_iff.1 h).2
  calc ∑ ζ ∈ S i, w i * (c i ζ * f (a i, ζ))
      = ∑ q ∈ (S i).image (fun ζ : ℂ => (a i, ζ)), (if a i = q.1 ∧ q.2 ∈ S i then w i * c i q.2 else 0) * f q := by
        rw [Finset.sum_image hinj]
        refine Finset.sum_congr rfl fun ζ hζ => ?_
        rw [if_pos ⟨rfl, hζ⟩, mul_assoc]
    _ = _ := by
        refine Finset.sum_subset ?_ ?_
        · intro q hq
          obtain ⟨ζ, hζ, rfl⟩ := Finset.mem_image.1 hq
          exact hP i hi ζ hζ
        · intro q _ hq
          rw [if_neg, zero_mul]
          rintro ⟨h1, h2⟩
          exact hq (Finset.mem_image.2 ⟨q.2, h2, Prod.ext h1 rfl⟩)

private lemma d_top (d : ℕ → ℕ) (h : ∀ B : ℝ, ∀ᶠ j : ℕ in atTop, Real.exp (B * j) ≤ (d j).factorial) :
    Tendsto d atTop atTop := by
  refine tendsto_atTop.2 fun M => ?_
  filter_upwards [h 1, eventually_ge_atTop M.factorial] with j hj hM
  by_contra hlt
  have h1 : (d j).factorial ≤ M.factorial := Nat.factorial_le (not_le.1 hlt).le
  have h2 : ((d j).factorial : ℝ) ≤ j := by exact_mod_cast h1.trans hM
  have h3 := Real.add_one_le_exp (1 * (j : ℝ))
  linarith

private lemma low_bd (Z : Finset ℂ) (hZ : ∀ ζ ∈ Z, ζ ≠ 0) : ∃ cq : ℝ, ∀ ζ ∈ Z, Real.exp (-cq) ≤ ‖ζ‖ := by
  obtain ⟨M, hM⟩ := (Z.image fun ζ => -Real.log ‖ζ‖).bddAbove
  refine ⟨M, fun ζ hζ => ?_⟩
  have h1 : -Real.log ‖ζ‖ ≤ M := hM (by simpa using ⟨ζ, hζ, rfl⟩)
  calc Real.exp (-M) ≤ Real.exp (Real.log ‖ζ‖) := Real.exp_le_exp.2 (by linarith)
    _ = ‖ζ‖ := Real.exp_log (norm_pos_iff.2 (hZ ζ hζ))

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.absX :
    ∀ (T : Type) (a : T → ℝ) (τ : T → ℕ → ℂ) (act good : T → Prop) (x : ℝ), 0 < x → x ≤ 1 → ∀ (p : ℕ), 0 < p → ∀ (d : ℕ → ℕ),
      Tendsto (fun j : ℕ => (d j : ℝ) / j) atTop (𝓝 0) → (∀ B : ℝ, ∀ᶠ j : ℕ in atTop, Real.exp (B * j) ≤ (d j).factorial) →
      (∀ i, act i → 0 < a i → ∃ (s : Finset ℂ) (c : ℂ → ℂ), 0 ∉ s ∧ ∀ᶠ j : ℕ in atTop, τ i j = ∑ ζ ∈ s, c ζ * ζ ^ j) →
      {i | act i ∧ a i = x}.Finite →
      (∀ N : ℝ, ∃ c₁ : ℝ, ∀ η : ℝ, 0 < η → η < x → ∃ (s : Finset T) (u : T → ℕ → ℂ) (u' : T → ℂ) (k : ℂ), k ≠ 0 ∧ (∀ i, i ∈ s ↔ η < a i ∧ act i) ∧
        (∀ i ∈ s, Tendsto (u i) atTop (𝓝 (u' i))) ∧ (∀ i ∈ s, good i → a i = x → u' i = k) ∧ (∀ i ∈ s, ¬ good i → u' i = 0) ∧
        ∀ s₀ : ℕ, ∃ K : ℝ, ∀ᶠ j : ℕ in atTop, ∀ m ≤ s₀, ∀ m' ≤ s₀,
          ‖∑ i ∈ s, u i (d j) * (a i : ℂ) ^ d j * (cheb η (j / p + m) (a i) : ℂ) * τ i (j + m')‖ ≤
            K ^ (d j + 1) * (Real.exp (c₁ * j) * (1 + (4 / η) ^ (j / p) / (d j).factorial) + (4 / η) ^ (j / p) * Real.exp (-N * j))) →
      ∀ᶠ j : ℕ in atTop, ∑ᶠ i ∈ {i | act i ∧ good i ∧ a i = x}, τ i j = 0 := by
  classical
  intro T a τ act good x hx hx1 p hp d hd hfac hexp hfin H
  choose! S c hS0 hτ using hexp
  obtain ⟨cq, hcq⟩ := low_bd (hfin.toFinset.biUnion S) (by
    intro ζ hζ h0
    obtain ⟨i, hi, hζ⟩ := Finset.mem_biUnion.1 hζ
    have hi' := hfin.mem_toFinset.1 hi
    exact hS0 i hi'.1 (hi'.2 ▸ hx) (h0 ▸ hζ))
  obtain ⟨N, hN⟩ := exponents3 d hd hfac p hp cq x hx hx1
  obtain ⟨c₁, H⟩ := H N
  obtain ⟨η, hη, hηx, hE⟩ := hN c₁
  obtain ⟨s, u, u', k, hk, hs, hu, hgood, hbad, hest⟩ := H η hη hηx
  have hsp : ∀ i ∈ s, act i ∧ 0 < a i := fun i hi => ⟨((hs i).1 hi).2, hη.trans ((hs i).1 hi).1⟩
  set P : Finset (ℝ × ℂ) := s.biUnion fun i => (S i).image fun ζ => (a i, ζ) with hPdef
  have hP : ∀ i ∈ s, ∀ ζ ∈ S i, (a i, ζ) ∈ P := fun i hi ζ hζ =>
    Finset.mem_biUnion.2 ⟨i, hi, Finset.mem_image.2 ⟨ζ, hζ, rfl⟩⟩
  have hP' : ∀ q ∈ P, ∃ i ∈ s, a i = q.1 ∧ q.2 ∈ S i := by
    intro q hq
    obtain ⟨i, hi, hq⟩ := Finset.mem_biUnion.1 hq
    obtain ⟨ζ, hζ, rfl⟩ := Finset.mem_image.1 hq
    exact ⟨i, hi, rfl, hζ⟩
  have hall : ∀ᶠ j : ℕ in atTop, ∀ i ∈ s, τ i j = ∑ ζ ∈ S i, c i ζ * ζ ^ j :=
    (Filter.eventually_all_finset s).2 fun i hi => hτ i (hsp i hi).1 (hsp i hi).2
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hall
  let C : (T → ℂ) → ℝ × ℂ → ℂ := fun w q => ∑ i ∈ s, if a i = q.1 ∧ q.2 ∈ S i then w i * c i q.2 else 0
  have key := hE η hη le_rfl P (fun q => q.1.1) (fun q => q.1.2)
    (fun q => by
      obtain ⟨i, hi, h1, -⟩ := hP' q.1 q.2
      exact h1 ▸ ((hs i).1 hi).1)
    (fun q h0 => by
      obtain ⟨i, hi, -, h2⟩ := hP' q.1 q.2
      exact hS0 i (hsp i hi).1 (hsp i hi).2 (h0 ▸ h2))
    (fun q q' h => Subtype.ext h)
    (fun j q => C (fun i => u i (d j)) q.1) (fun q => C u' q.1)
    (fun q => by
      refine tendsto_finsetSum _ fun i hi => ?_
      split_ifs
      · exact ((hu i hi).comp (d_top d hfac)).mul_const _
      · exact tendsto_const_nhds)
    (fun s₀ => by
      obtain ⟨K, hK⟩ := hest s₀
      refine ⟨K, ?_⟩
      filter_upwards [hK, eventually_ge_atTop J] with j hj hjJ m hm m' hm'
      refine le_of_eq_of_le ?_ (hj m hm m' hm')
      congr 1
      have h1 := regroup s a S c (fun i => u i (d j)) P hP
        (fun q => (q.1 : ℂ) ^ d j * (cheb η (j / p + m) q.1 : ℂ) * q.2 ^ (j + m'))
      rw [← Finset.sum_coe_sort P] at h1
      refine Eq.trans (Finset.sum_congr rfl fun q _ => by simp only [C, mul_assoc]) (h1.trans ?_)
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hJ (j + m') (by omega) i hi, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun ζ _ => ?_
      ring)
  filter_upwards [hall] with j hj
  have h1 := regroup s a S c u' P hP (fun q => if q.1 = x then q.2 ^ j else 0)
  have h2 : ∑ q ∈ P, C u' q * (if q.1 = x then q.2 ^ j else 0) = 0 := by
    refine Finset.sum_eq_zero fun q hq => ?_
    split_ifs with hqx
    · obtain ⟨i, hi, h1, h2⟩ := hP' q hq
      have := key ⟨q, hq⟩ hqx.ge (hcq _ (Finset.mem_biUnion.2
        ⟨i, hfin.mem_toFinset.2 ⟨(hsp i hi).1, h1.trans hqx⟩, h2⟩))
      rw [this, zero_mul]
    · exact mul_zero _
  have h3 : k * ∑ i ∈ s.filter (fun i => good i ∧ a i = x), τ i j = 0 := by
    rw [← h2]
    refine Eq.trans ?_ h1.symm
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i hi => ?_
    by_cases hg : good i
    · by_cases ha : a i = x
      · simp only [hg, ha, and_self, if_true, hgood i hi hg ha, hj i hi]
      · simp [ha]
    · simp [hg, hbad i hi hg]
  have h4 : {i | act i ∧ good i ∧ a i = x} = ↑(s.filter (fun i => good i ∧ a i = x)) := by
    ext i
    simp only [Set.mem_setOf_eq, Finset.coe_filter]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨(hs i).2 ⟨h3 ▸ hηx, h1⟩, h2, h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(hsp i h1).1, h2⟩
  show ∑ᶠ i ∈ {i | act i ∧ good i ∧ a i = x}, τ i j = 0
  rw [h4, finsum_mem_coe_finset]
  exact (mul_eq_zero.1 h3).resolve_left hk
end

