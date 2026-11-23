module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.Carries
public import GroundTheory.AutomorphicForms.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.BandTC
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W]

private theorem widen (M : Sc H V W) (φ : ℝ → ℂ) (hi : Integrable φ) (ρ a b : ℝ) (hρ : ∀ t, ρ < |t| → φ t = 0) :
    M.P (Ioc (a - ρ) (b + ρ)) * (M.F.av φ * M.P (Ioc a b)) = M.F.av φ * M.P (Ioc a b) := by
  ext h
  obtain ⟨i1, i2⟩ := ((avSpec M.F).2.2.2 φ hi).1 (M.P (Ioc a b) h)
  simp only [ContinuousLinearMap.mul_apply]
  rw [i2, ← ContinuousLinearMap.integral_comp_comm _ i1]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  by_cases ht : ρ < |t|
  · simp [hρ t ht]
  have pl := (projLaws M).2.2.2.2.1
  have m : MeasurableSet ((fun x => x + t) ⁻¹' Ioc a b) := measurableSet_Ioc.preimage (measurable_add_const t)
  have e1 : M.F.U t (M.P (Ioc a b) h) = _ :=
    DFunLike.congr_fun ((pl (Ioc a b) (Ioc a b) measurableSet_Ioc measurableSet_Ioc).2.2.2.2 t).1 h
  have e2 := (pl (Ioc (a - ρ) (b + ρ)) _ measurableSet_Ioc m).1
  rw [inter_eq_right.2 (by
    rintro x ⟨h1, h2⟩
    have := abs_le.1 (not_lt.1 ht)
    constructor <;> linarith [this.1, this.2])] at e2
  simp only [map_smul]
  rw [e1]
  exact congrArg _ (DFunLike.congr_fun e2 _)
end

theorem UpperTheory.V.Z.IntegralApplyAeEq.bandTC :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (X : H →L[ℂ] H) (κ : ℝ → V →L[ℂ] W), Ker κ → M.Carries X κ → ∀ (ψ : ℝ → ℝ) (δ a b : ℝ), Bump ψ (-δ) 0 → a ≤ b →
      IsTraceClass ((M.F.av (fun t => (ψ t : ℂ)) ∘L X) ∘L M.P (Ioc a b)) ∧ IsTraceClass (M.P' (Ioc a b) ∘L (M.F.av (fun t => (ψ t : ℂ)) ∘L X)) ∧
      IsTraceClass ((M.F.av (fun t => (ψ t : ℂ)) ∘L X) ∘L M.P' (Ioc a b)) ∧
      trace ((M.F.av (fun t => (ψ t : ℂ)) ∘L X) ∘L M.P (Ioc a b)) = ∫ y in a..b, ∑ i, M.cor (fun x => (ψ x : ℂ)) (stdOrthonormalBasis ℂ V i) (kv κ (stdOrthonormalBasis ℂ V i)) (2 * y) ∧
      trace (M.P' (Ioc a b) ∘L (M.F.av (fun t => (ψ t : ℂ)) ∘L X)) =
        conj (∫ y in a..b, ∑ j, M.swap.cor (fun x => (ψ (-x) : ℂ)) (stdOrthonormalBasis ℂ W j) (kv (sharp κ) (stdOrthonormalBasis ℂ W j)) (2 * y)) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M X κ hk hX ψ δ a b hψ hab
  obtain ⟨c1, c2, -⟩ := carLaws M X κ hk hX
  have hk' := (convAdj κ hk).1
  obtain ⟨s0, hi, -⟩ := avApprox.2.1 ψ _ _ hψ
  have cc : Continuous fun t => (ψ t : ℂ) := Complex.continuous_ofReal.comp hψ.cont
  have sc : HasCompactSupport fun t => (ψ t : ℂ) := s0.comp_left Complex.ofReal_zero
  have cn : Continuous fun t => (ψ (-t) : ℂ) := cc.comp continuous_neg
  have sn : HasCompactSupport fun t => (ψ (-t) : ℂ) := sc.comp_homeomorph (Homeomorph.neg ℝ)
  have z : ∀ t, |δ| < |t| → ψ t = 0 := fun t ht => hψ.supp t fun h => by
    have : |t| ≤ |δ| := abs_le.2 ⟨by linarith [h.1, le_abs_self δ], h.2.trans (abs_nonneg δ)⟩
    linarith
  obtain ⟨-, -, a1, a2, -⟩ := (avSpec M.F).2.2.2 _ hi
  simp only [Complex.conj_ofReal] at a1
  set Ψ := M.F.av fun t => (ψ t : ℂ) with hΨ
  set Ψn := M.F.av fun t => (ψ (-t) : ℂ) with hΨn
  have a3 : M.swap.F.av (fun t => (ψ t : ℂ)) = Ψn := a2
  have cm : Ψ * X = X * Ψn := by
    have := ((avSpec M.F.rev).2.2.2 _ hi).2.2.2.2 M.F X fun t h => by
      show X (M.F.U (-t) h) = _
      rw [c1, neg_neg]
    rw [a2] at this
    exact this.symm
  have hab' : a - |δ| ≤ b + |δ| := by linarith [abs_nonneg δ]
  have w1 := widen M (fun t => (ψ (-t) : ℂ)) hi.comp_neg |δ| a b fun t ht => by rw [z (-t) (by rwa [abs_neg])]; simp
  have w2 := widen M.swap (fun t => (ψ t : ℂ)) hi |δ| a b fun t ht => by rw [z t ht]; simp
  rw [a3] at w2
  obtain ⟨b1, -, b2, -, b3⟩ := bandHS M X κ hk hX _ a b cn sn hab
  obtain ⟨b4, -⟩ := bandHS M X κ hk hX _ _ _ cn sn hab'
  obtain ⟨d1, -, d2, -, d3⟩ := bandHS M.swap _ _ hk' c2 _ a b cc sc hab
  obtain ⟨d4, -⟩ := bandHS M.swap _ _ hk' c2 _ _ _ cc sc hab'
  rw [a3] at d2 d3
  obtain ⟨p1, p2, -⟩ := (projLaws M).2.2.2.2.1 (Ioc a b) (Ioc a b) measurableSet_Ioc measurableSet_Ioc
  obtain ⟨q1, q2, -⟩ := (projLaws M.swap).2.2.2.2.1 (Ioc a b) (Ioc a b) measurableSet_Ioc measurableSet_Ioc
  obtain ⟨-, q3, -⟩ := (projLaws M.swap).2.2.2.2.1 (Ioc (a - |δ|) (b + |δ|)) (Ioc a b) measurableSet_Ioc measurableSet_Ioc
  rw [inter_self] at p1 q1
  have d5 : IsHilbertSchmidt (X ∘L M.swap.P (Ioc (a - |δ|) (b + |δ|))) := by
    refine flip M.swap X _ _ (fun t h => c1 (-t) h) ?_
    have := d4.adjoint
    rwa [ContinuousLinearMap.adjoint_comp, q3.adjoint_eq, ContinuousLinearMap.adjoint_adjoint] at this
  simp only [Sc.P']
  set P := M.P (Ioc a b)
  set Q := M.swap.P (Ioc a b)
  set P₁ := M.P (Ioc (a - |δ|) (b + |δ|))
  set Q₁ := M.swap.P (Ioc (a - |δ|) (b + |δ|))
  have a1' : star Ψ = Ψn := a1
  have a4 : star Ψn = Ψ := by rw [← a1', star_star]
  have t1 : IsTraceClass (Ψ * X * P) := by
    rw [cm, mul_assoc, ← w1, ← mul_assoc]
    exact isTraceClass_comp b4 b2
  have t3 : IsTraceClass (Ψ * X * Q) := by
    rw [cm, mul_assoc, ← w2, ← mul_assoc]
    exact isTraceClass_comp d5 d2
  have t2 : IsTraceClass (Q * (Ψ * X)) := by
    have h : IsTraceClass (star X * Q₁ * (Ψn * Q)) := isTraceClass_comp d4 d2
    rw [mul_assoc, w2] at h
    have h' : IsTraceClass (star (star X * (Ψn * Q))) := h.adjoint
    rwa [star_mul, star_mul, star_star, q2.star_eq, a4, mul_assoc] at h'
  refine ⟨t1, t2, t3, ?_, ?_⟩
  · simp only [neg_neg] at b3
    rw [← b3]
    have h := trace_comp_comm t1 P
    change trace (P * (Ψ * X * P)) = trace (Ψ * X * P * P) at h
    change P * P = P at p1
    rw [mul_assoc (Ψ * X), p1] at h
    change trace (Ψ * X * P) = trace (star (Ψn * P) * (X * P))
    rw [← h, star_mul, p2.star_eq, a4]
    simp only [mul_assoc]
  · rw [← d3, ← trace_adjoint (isTraceClass_comp d2.adjoint d1)]
    have h := trace_comp_comm t2 Q
    change trace (Q * (Q * (Ψ * X))) = trace (Q * (Ψ * X) * Q) at h
    change Q * Q = Q at q1
    rw [← mul_assoc, q1] at h
    change trace (Q * (Ψ * X)) = trace (star (star (Ψn * Q) * (star X * Q)))
    rw [h, star_mul, star_star, star_mul, star_star, q2.star_eq, cm]
    simp only [mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ImportsBis
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.model :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (D : Datum H V W), ∃ M : Sc H V W, M.T₀ = D.T₀ ∧ (∀ u, M.J u = D.J u) ∧ (∀ v, M.J' v = D.J' v) ∧
      ∀ T Λ, D.T₀ ≤ T → (IsTrunc D.J D.J' T Λ ↔ Λ = M.abelian₂ T T) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ D
  let D' : Datum H W V :=
    { J := D.J', J' := D.J, T₀ := D.T₀, B := D.B, β := D.β', β' := D.β
      span := fun h a b => D.span h b a
      shift := fun t u u' v v' a b => by
        rw [← inner_conj_symm, ← D.shift t v v' u u' b a, inner_conj_symm]
      causal := fun s u v a b => by
        rw [← inner_conj_symm, D.causal (2 * D.T₀ - s) v u b (by simpa using a), map_zero]
      β_ker := D.β'_ker, β'_ker := D.β_ker, β_unit := D.β'_unit, β'_unit := D.β_unit, B_sa := D.B_sa
      B_J := D.B_J', B_J' := D.B_J
      compact := fun T Λ hT h => D.compact T Λ hT ⟨h.1, h.2.1, fun x => (h.2.2 x).trans
        ⟨fun ⟨u, v, a, b, c⟩ => ⟨v, u, b, a, c.trans (add_comm _ _)⟩, fun ⟨u, v, a, b, c⟩ => ⟨v, u, b, a, c.trans (add_comm _ _)⟩⟩⟩ }
  let J := LinearIsometryEquiv.ofSurjective D.J (ontoJ D)
  let J' := LinearIsometryEquiv.ofSurjective D.J' (ontoJ D')
  have hJ : ∀ u, J u = D.J u := fun _ => rfl
  have hJ' : ∀ u, J' u = D.J' u := fun _ => rfl
  let F : Flow H :=
    { U := fun t => (J.toContinuousLinearEquiv : L V →L[ℂ] H) ∘L sh V t ∘L (J.symm.toContinuousLinearEquiv : H →L[ℂ] L V)
      zero := fun h => by
        show J ((shF V).U 0 (J.symm h)) = h
        rw [(shF V).zero, J.apply_symm_apply]
      add := fun s t h => by
        show J ((shF V).U (s + t) (J.symm h)) = J ((shF V).U s (J.symm (J ((shF V).U t (J.symm h)))))
        rw [(shF V).add, J.symm_apply_apply]
      norm := fun t h => by
        show ‖J ((shF V).U t (J.symm h))‖ = _
        rw [J.norm_map, (shF V).norm, J.symm.norm_map]
      cont := fun h => J.continuous.comp ((shF V).cont _) }
  have hU : ∀ t u, F.U t (J u) = J (sh V t u) := fun t u => by
    show J (sh V t (J.symm (J u))) = _
    rw [J.symm_apply_apply]
  have sup : ∀ {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] [CompleteSpace X] (s : ℝ) (u : L X),
      ∀ᵐ x : ℝ, x ≤ s → cut X (Ioi s) u x = 0 := fun s u =>
    (cutSpec (Ioi s) measurableSet_Ioi u).mono fun x h hx => by rw [h, indicator_of_notMem (by simpa using hx)]
  have caus : ∀ (s : ℝ) (u : L V) (v : L W), ⟪J (cut V (Ioi s) u), J' (cut W (Ioi (2 * D.T₀ - s)) v)⟫_ℂ = 0 :=
    fun s u v => D.causal s _ _ (sup s u) (sup _ v)
  refine ⟨⟨J, J', F, D.T₀, hU, fun t v => ?_, caus⟩, rfl, hJ, hJ', fun T Λ hT => ?_⟩
  · refine ext_inner_left ℂ fun h => ?_
    obtain ⟨u, rfl⟩ := J.surjective h
    have e : J u = F.U t (J (sh V (-t) u)) := by rw [← hU, ← F.add, add_neg_cancel, F.zero]
    conv_lhs => rw [e]
    refine ((⟨(F.U t : H →ₗ[ℂ] H), F.norm t⟩ : H →ₗᵢ[ℂ] H).inner_map_map _ _).trans ?_
    exact D.shift (-t) u _ v _ (sh_ae V _ u) (sh_ae W _ v)
  · rw [truncEq D.J D.J' T Λ fun u v => D.causal T _ _ (sup T u) ((sup T v).mono fun x h hx => h (by linarith))]
    have a1 : ContinuousLinearMap.adjoint D.J.toContinuousLinearMap = (J.symm.toContinuousLinearEquiv : H →L[ℂ] L V) :=
      ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => (J.inner_map_map _ _).symm.trans (by
        show ⟪J (J.symm x), J y⟫_ℂ = _
        rw [J.apply_symm_apply]; rfl)).symm
    have a2 : ContinuousLinearMap.adjoint D.J'.toContinuousLinearMap = (J'.symm.toContinuousLinearEquiv : H →L[ℂ] L W) :=
      ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun x y => (J'.inner_map_map _ _).symm.trans (by
        show ⟪J' (J'.symm x), J' y⟫_ℂ = _
        rw [J'.apply_symm_apply]; rfl)).symm
    rw [a1, a2]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ResInv
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

theorem UpperTheory.V.Z.IntegralApplyAeEq.resInv :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (B : H →L[ℂ] H) (β : ℝ → V →L[ℂ] V) (β' : ℝ → W →L[ℂ] W), Ker β → Ker β' → IsUnit (symb β 0) → IsUnit (symb β' 0) → M.Acts B β β' → IsCompactOperator (M.abelian₂ M.T₀ M.T₀ ∘L B ∘L M.abelian₂ M.T₀ M.T₀) →
      Function.Surjective (1 - M.abelian₂ M.T₀ M.T₀ ∘L M.F.av wR ∘L M.abelian₂ M.T₀ M.T₀ : H →L[ℂ] H) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M B β β' k1 k2 u1 u2 ha hc
  obtain ⟨-, -, l0, sa, ln, -⟩ := (projLaws M).2.2.2.2.2.2.2 M.T₀ M.T₀ (by linarith)
  set Λ := M.abelian₂ M.T₀ M.T₀ with hΛ
  set R := M.F.av wR with hR
  have hΛΛ : ∀ x, Λ (Λ x) = Λ x := fun x => DFunLike.congr_fun l0 x
  have below : ∀ S : H →L[ℂ] H, (∀ x, (⟪x, S x⟫_ℂ).re = (⟪x, R x⟫_ℂ).re) →
      ∃ c : ℝ, 0 < c ∧ ∀ x, c * ‖x‖ ≤ ‖x - Λ (S (Λ x))‖ := by
    intro S hS
    by_contra hcon
    push Not at hcon
    choose x hx using fun n : ℕ => hcon (1 / ((n : ℝ) + 1)) Nat.one_div_pos_of_nat
    have h0 : ∀ n, x n ≠ 0 := fun n h => by simpa [h] using hx n
    let f : ℕ → H := fun n => (‖x n‖⁻¹ : ℂ) • x n
    have hf : ∀ n, ‖f n‖ = 1 := fun n => norm_smul_inv_norm (h0 n)
    have t0 : Tendsto (fun n => f n - Λ (S (Λ (f n)))) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun n => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
      have e : f n - Λ (S (Λ (f n))) = (‖x n‖⁻¹ : ℂ) • (x n - Λ (S (Λ (x n)))) := by simp [f, smul_sub]
      rw [e, norm_smul, norm_inv, Complex.norm_real, norm_norm, inv_mul_le_iff₀ (norm_pos_iff.2 (h0 n)), mul_comm]
      exact (hx n).le
    have t1 : Tendsto (fun n => Λ (f n) - f n) atTop (𝓝 0) := by
      have := ((Λ.continuous.tendsto 0).comp t0).sub t0
      simpa [Function.comp_def, hΛΛ] using this
    have t2 : Tendsto (fun n => f n - Λ (S (f n))) atTop (𝓝 0) := by
      have := t0.add (((Λ ∘L S).continuous.tendsto 0).comp t1)
      simpa [Function.comp_def] using this
    have t3 : Tendsto (fun n => ⟪f n, f n - Λ (S (f n))⟫_ℂ + ⟪Λ (f n) - f n, S (f n)⟫_ℂ) atTop (𝓝 0) := by
      have a : Tendsto (fun n => ⟪f n, f n - Λ (S (f n))⟫_ℂ) atTop (𝓝 0) :=
        squeeze_zero_norm (fun n => (norm_inner_le_norm _ _).trans_eq (by rw [hf, one_mul])) (tendsto_zero_iff_norm_tendsto_zero.1 t2)
      have b : Tendsto (fun n => ⟪Λ (f n) - f n, S (f n)⟫_ℂ) atTop (𝓝 0) := by
        refine squeeze_zero_norm (a := fun n => ‖Λ (f n) - f n‖ * ‖S‖) (fun n => (norm_inner_le_norm _ _).trans ?_) ?_
        · gcongr; simpa [hf] using S.le_opNorm (f n)
        · simpa using (tendsto_zero_iff_norm_tendsto_zero.1 t1).mul_const ‖S‖
      simpa using a.add b
    refine resBelow M B β β' k1 k2 u1 u2 ha hc f hf t1 ?_
    have t4 := (tendsto_const_nhds (x := (1 : ℝ))).sub ((Complex.continuous_re.tendsto 0).comp t3)
    simp only [Complex.zero_re, sub_zero] at t4
    refine t4.congr fun n => ?_
    have e1 : ⟪f n, f n⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hf]; simp
    rw [← hS, Function.comp_apply, inner_sub_right, inner_sub_left, sa.isSymmetric.apply_clm, e1]
    simp
  obtain ⟨c, c0, h1⟩ := below R fun _ => rfl
  obtain ⟨c', c0', h2⟩ := below (ContinuousLinearMap.adjoint R) fun x => by
    rw [ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm, Complex.conj_re]
  set A : H →L[ℂ] H := 1 - Λ ∘L R ∘L Λ with hA
  have anti : AntilipschitzWith ⟨c⁻¹, by positivity⟩ A := A.antilipschitz_of_bound fun x => by
    show ‖x‖ ≤ c⁻¹ * ‖x - Λ (R (Λ x))‖
    rw [le_inv_mul_iff₀ c0]; exact h1 x
  have cl : IsClosed (LinearMap.range (A : H →ₗ[ℂ] H) : Set H) := anti.isClosed_range A.uniformContinuous
  have bot : (LinearMap.range (A : H →ₗ[ℂ] H))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    have h3 : y - Λ (ContinuousLinearMap.adjoint R (Λ y)) = 0 := ext_inner_left ℂ fun x => by
      have := hy (A x) ⟨x, rfl⟩
      rw [inner_sub_right, ← sa.isSymmetric.apply_clm, ContinuousLinearMap.adjoint_inner_right, ← sa.isSymmetric.apply_clm,
        ← inner_sub_left, inner_zero_right]
      exact this
    have := h2 y
    rw [h3, norm_zero] at this
    exact norm_le_zero_iff.1 (nonpos_of_mul_nonpos_right this c0')
  haveI := cl.completeSpace_coe
  exact LinearMap.range_eq_top.1 ((Submodule.orthogonal_eq_bot_iff).1 bot)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.TraceFar
section
open MeasureTheory GroundTheory.Automorphic PositivityTheory.Rg.Tf.IntegralApplyAeEq Set Filter Topology UpperTheory.V.Z.IntegralApplyAeEq
open scoped InnerProductSpace FourierTransform ComplexConjugate

section
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W)

private theorem k1 {T : ℝ} (hT : M.T₀ ≤ T) {r : ℝ} (hr : r ≤ 0) (h : H) : M.abelian₂ T T (M.F.U r (M.P (Ioi T) h)) = 0 := by
  obtain ⟨-, -, -, -, hP, -, -, hL⟩ := projLaws M
  have x1 := DFunLike.congr_fun ((hP _ _ (measurableSet_Ioi (a := T)) (measurableSet_Ioi (a := T))).2.2.2.2 r).1 h
  have y1 : (fun x : ℝ => x + r) ⁻¹' Ioi T = Ioi (T - r) := by ext x; simp [sub_lt_iff_lt_add]
  have x2 := (hP _ _ (measurableSet_Ioi (a := T)) (measurableSet_Ioi (a := T - r))).1
  rw [inter_eq_right.2 (Ioi_subset_Ioi (by linarith))] at x2
  rw [y1, ← x2] at x1
  simp only [ContinuousLinearMap.comp_apply] at x1
  rw [x1]
  exact DFunLike.congr_fun (hL T T (by linarith)).2.2.2.2.2.1 _

private theorem k2 {T δ : ℝ} (hT : M.T₀ ≤ T) {r : ℝ} (hr : -δ ≤ r) (h : H) : M.abelian₂ T T (M.F.U r (M.P' (Ioi (T + δ)) h)) = 0 := by
  obtain ⟨-, -, -, -, hP, -, -, hL⟩ := projLaws M
  have x1 := DFunLike.congr_fun ((hP _ _ (measurableSet_Ioi (a := T + δ)) (measurableSet_Ioi (a := T))).2.2.2.2 r).2 h
  have y1 : (fun x : ℝ => x - r) ⁻¹' Ioi (T + δ) = Ioi (T + δ + r) := by ext x; simp [lt_sub_iff_add_lt]
  have x2 : M.P' (Ioi T) ∘L M.P' (Ioi (T + δ + r)) = M.P' (Ioi T ∩ Ioi (T + δ + r)) :=
    ((projLaws M.swap).2.2.2.2.1 _ _ (measurableSet_Ioi (a := T)) (measurableSet_Ioi (a := T + δ + r))).1
  rw [inter_eq_right.2 (Ioi_subset_Ioi (by linarith))] at x2
  rw [y1, ← x2] at x1
  simp only [ContinuousLinearMap.comp_apply] at x1
  rw [x1]
  exact DFunLike.congr_fun (hL T T (by linarith)).2.2.2.2.2.2.2.1 _

private theorem k3 {ψ : ℝ → ℝ} {δ : ℝ} (hψ : Bump ψ (-δ) 0) (A : H →L[ℂ] H) (h : H)
    (hA : ∀ r, -δ ≤ r → r ≤ 0 → A (M.F.U r h) = 0) : A (M.F.av (fun t => (ψ t : ℂ)) h) = 0 := by
  obtain ⟨i, e⟩ := ((avSpec M.F).2.2.2 _ (avApprox.2.1 ψ _ _ hψ).2.1).1 h
  rw [e, ← A.integral_comp_comm i]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun r => ?_)
  by_cases hr : r ∈ Icc (-δ) 0
  · simp [hA r hr.1 hr.2]
  · simp [hψ.supp r hr]

private theorem k4 {T ρ : ℝ} (hρ : 0 ≤ ρ) : M.P' (Ioi T) = M.P' (Ioc T (T + ρ)) + M.P' (Ioi (T + ρ)) := by
  have := ((projLaws M.swap).2.2.2.2.1 _ _ (measurableSet_Ioc (a := T) (b := T + ρ)) (measurableSet_Ioi (a := T + ρ))).2.2.2.1
    (Ioc_disjoint_Ioi le_rfl)
  rwa [Ioc_union_Ioi_eq_Ioi (by linarith)] at this

private theorem k5 (T : ℝ) (h : H) : h = M.abelian₂ T T h + M.P (Ioi T) h + M.P' (Ioi T) h := by
  show h = h - M.P (Ioi T) h - M.P' (Ioi T) h + _ + _
  abel

private theorem k6 {X : H →L[ℂ] H} {κ : ℝ → V →L[ℂ] W} (hk : Ker κ) (hX : M.Carries X κ) {ψ : ℝ → ℝ} {δ : ℝ} (hψ : Bump ψ (-δ) 0)
    {a b : ℝ} (hab : a ≤ b) :
    IsHilbertSchmidt (M.F.av (fun t => (ψ t : ℂ)) ∘L M.P' (Ioc a b)) ∧ IsHilbertSchmidt (M.P' (Ioc a b) ∘L X) ∧
    hsNorm (M.F.av (fun t => (ψ t : ℂ)) ∘L M.P' (Ioc a b)) ^ 2 = (b - a) * (Module.finrank ℂ W * ∫ x, ψ x ^ 2) ∧
    hsNorm (M.P' (Ioc a b) ∘L X) ^ 2 = (b - a) * ∑ i, ‖kv (sharp κ) (stdOrthonormalBasis ℂ W i)‖ ^ 2 ∧
    M.P' (Ioc a b) ∘L M.P' (Ioc a b) = M.P' (Ioc a b) := by
  obtain ⟨hs, hi, -⟩ := avApprox.2.1 ψ _ _ hψ
  obtain ⟨b1, b2, b3, b4, -⟩ := bandHS M.swap _ _ (convAdj κ hk).1 (carLaws M X κ hk hX).2.1 (fun t => (ψ (-t) : ℂ)) a b
    (Complex.continuous_ofReal.comp (hψ.cont.comp continuous_neg))
    ((hs.comp_homeomorph (Homeomorph.neg ℝ)).comp_left (g := fun x : ℝ => (x : ℂ)) rfl) hab
  have e : M.swap.F.av (fun t => (ψ (-t) : ℂ)) = M.F.av fun t => (ψ t : ℂ) := by
    have := ((avSpec M.F).2.2.2 _ hi.comp_neg).2.2.2.1
    simp only [neg_neg] at this
    exact this
  rw [e] at b3 b4
  obtain ⟨p1, p2, -⟩ := (projLaws M.swap).2.2.2.2.1 _ _ (measurableSet_Ioc (a := a) (b := b)) (measurableSet_Ioc (a := a) (b := b))
  rw [inter_self] at p1
  have e2 : M.P' (Ioc a b) ∘L X = ContinuousLinearMap.adjoint (ContinuousLinearMap.adjoint X ∘L M.swap.P (Ioc a b)) := by
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint, p2.adjoint_eq]; rfl
  refine ⟨b3, e2 ▸ b1.adjoint, b4.trans ?_, by rw [e2, hsNorm_adjoint, b2], p1⟩
  have := integral_neg_eq_self (fun x => ψ x ^ 2) volume
  simp [this]
end

theorem UpperTheory.V.Z.IntegralApplyAeEq.traceFar :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [CompleteSpace V] {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] [CompleteSpace W] (M : Sc H V W) (X : H →L[ℂ] H) (κ : ℝ → V →L[ℂ] W), Ker κ → M.Carries X κ → ∀ (ψ : ℝ → ℝ) (δ T : ℝ), Bump ψ (-δ) 0 → M.T₀ ≤ T → IsTraceClass (M.abelian₂ T T ∘L X ∘L M.abelian₂ T T) →
      IsTraceClass (M.abelian₂ T T ∘L (M.F.av (fun t => (ψ t : ℂ)) ∘L X) ∘L M.abelian₂ T T) ∧
      Tendsto (fun a : ℝ => trace (M.abelian₂ T T ∘L M.F.U (-(2 * a)) ∘L (M.F.av (fun t => (ψ t : ℂ)) ∘L X) ∘L M.abelian₂ T T)) atTop (𝓝 0) := by
  intro H _ _ _ V _ _ _ _ W _ _ _ _ M X κ hk hX ψ δ T hψ hT htc
  obtain ⟨ρ₀, hρ₀⟩ := hk.2.isCompact.isBounded.subset_closedBall 0
  have hρ : ∀ t, max ρ₀ 0 < |t| → κ t = 0 := fun t ht => image_eq_zero_of_notMem_tsupport fun h => by
    have := hρ₀ h
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs] at this
    linarith [le_max_left ρ₀ 0]
  set ρ := max ρ₀ 0
  have r0 : 0 ≤ ρ := le_max_right _ _
  obtain ⟨h1, h2, -, -, h3⟩ := k6 M hk hX hψ (a := T) (b := T + ρ) (by linarith)
  obtain ⟨-, -, l0, -, ln, -, l2, -⟩ := (projLaws M).2.2.2.2.2.2.2 T T (by linarith)
  set Λ := M.abelian₂ T T
  set Ψ := M.F.av (fun t => (ψ t : ℂ))
  set E := M.P' (Ioc T (T + ρ))
  let Z : H →L[ℂ] H := Ψ ∘L (Λ ∘L X ∘L Λ) + ((Ψ ∘L E) ∘L (E ∘L X)) ∘L Λ
  have hZ : IsTraceClass Z := (htc.comp_left Ψ).add ((isTraceClass_comp h1 h2).comp_right Λ)
  have key : ∀ t, 0 ≤ t → Λ ∘L M.F.U (-t) ∘L (Ψ ∘L X) ∘L Λ = (Λ ∘L M.F.U (-t)) ∘L Z := fun t ht => by
    ext h
    have a1 : (Λ ∘L M.F.U (-t)) (Ψ (M.P (Ioi T) (X (Λ h)))) = 0 := k3 M hψ _ _ fun r _ hr => by
      rw [ContinuousLinearMap.comp_apply, ← M.F.add]; exact k1 M hT (by linarith) _
    have a2 : M.P' (Ioi (T + ρ)) (X (Λ h)) = 0 := by
      have := DFunLike.congr_fun ((carLaws M X κ hk hX).2.2 ρ T hρ) (Λ h)
      have l : M.P (Ioi T) (Λ h) = 0 := DFunLike.congr_fun l2 h
      simpa [l] using this
    have a3 : E (E (X (Λ h))) = E (X (Λ h)) := DFunLike.congr_fun h3 _
    show (Λ ∘L M.F.U (-t)) (Ψ (X (Λ h))) = (Λ ∘L M.F.U (-t)) (Ψ (Λ (X (Λ h))) + Ψ (E (E (X (Λ h)))))
    conv_lhs => rw [k5 M T (X (Λ h)), k4 M r0, ContinuousLinearMap.add_apply, a2, add_zero, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), a1, add_zero]
    rw [a3, map_add (f := _)]
  constructor
  · have := key 0 le_rfl
    have e : M.F.U (-0) = 1 := by ext h; simpa using M.F.zero h
    rw [e] at this
    exact this ▸ hZ.comp_left _
  · have t := trWeak atTop (fun a : ℝ => Λ ∘L M.F.U (-(2 * a))) 0 Z hZ (fun a =>
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun h => by
        rw [ContinuousLinearMap.comp_apply]
        exact (Λ.le_opNorm _).trans (by rw [M.F.norm]; gcongr)) (fun x y => by
      have sa := ((projLaws M).2.2.2.2.2.2.2 T T (by linarith)).2.2.2.1
      have := ((projLaws M).1 y (Λ x)).2.comp (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop two_pos))
      simp only [ContinuousLinearMap.zero_apply, inner_zero_right]
      exact this.congr fun a => sa.isSymmetric.apply_clm _ _)
    have z : trace ((0 : H →L[ℂ] H) ∘L Z) = 0 := by
      have := trace_smul 0 hZ
      simpa using this
    rw [z] at t
    refine t.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
    rw [key _ (by linarith)]
end

