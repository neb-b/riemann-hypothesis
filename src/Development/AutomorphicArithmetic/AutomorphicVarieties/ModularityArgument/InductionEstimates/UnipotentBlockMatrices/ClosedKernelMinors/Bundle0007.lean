module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.UnipotentBlockPairs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.BfFun
section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

theorem bfFun :
    ∀ {K : Type} [Field K] [NumberField K] (f : G1 K (2 + 2) → ℂ) (β : ℝ → ℂ),
      SFun f → Continuous β → HasCompactSupport β →
        PFun (bf β f) ∧ InBand (bf β f) ∧ Decays (bf β f) := by
  intro K _ _ f β hf hβ hc
  obtain ⟨h1, -, h3, h4, -⟩ := hpSpec (K := K)
  obtain ⟨-, -, hl, -⟩ := blkLaws (K := K)
  obtain ⟨w, hw⟩ : ∃ w : ℝ → ℂ, w = fun t => β t * Complex.exp ((((2 + 2 : ℕ) : ℝ) / 2 * t : ℝ) : ℂ) := ⟨_, rfl⟩
  have hbf : ∀ g, bf β f g = w (HH g) * f g := fun g => by rw [hw]; rfl
  have hwc : Continuous w := by
    rw [hw]
    exact hβ.mul (Complex.continuous_exp.comp (Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)))
  have hws : HasCompactSupport w := by
    rw [hw]
    exact hc.mul_right
  obtain ⟨B, hB⟩ := hwc.bounded_above_of_compact_support hws
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hn : ∀ (X : UPos (2 + 2) 2 → 𝔸[K]) (g : G1 K (2 + 2)), HH (nn X * g) = HH g := fun X g => by
    have := h1 X 1 1 0 g
    rwa [hl, mul_one, zero_add] at this
  have hm : ∀ (m₁ m₂ : G1 K 2) (g : G1 K (2 + 2)), HH (lv m₁ m₂ 0 * g) = HH g := fun m₁ m₂ g => by
    have := h1 0 m₁ m₂ 0 g
    rwa [mul_assoc, hn, zero_add] at this
  have hle : ∀ g, ‖bf β f g‖ ≤ B * ‖f g‖ := fun g => by
    rw [hbf, norm_mul]
    exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [show bf β f = fun g => w (HH g) * f g from funext hbf]
    exact (hwc.comp h4).mul hf.cont
  · obtain ⟨C, hC⟩ := hf.bdd
    exact ⟨B * C, fun g => (hle g).trans (mul_le_mul_of_nonneg_left (hC g) hB0)⟩
  · intro X g
    rw [hbf, hbf, hn, hf.unip]
  · intro γ hγ g
    rw [hbf, hbf, h3 γ hγ, hf.rat γ hγ]
  · intro g
    simp_rw [hbf, hm]
    rw [integral_const_mul, hf.cusp₁ g, mul_zero]
  · intro g
    simp_rw [hbf, hm]
    rw [integral_const_mul, hf.cusp₂ g, mul_zero]
  · obtain ⟨R, hR⟩ := hws.isCompact.isBounded.exists_norm_le
    refine ⟨R, fun g hg => ?_⟩
    rw [hbf] at hg
    exact hR _ (subset_tsupport w (left_ne_zero_of_mul hg))
  · intro N R
    obtain ⟨C, hC⟩ := hf.dec N R
    refine ⟨B * C, fun x hx => ?_⟩
    obtain ⟨γ, hγ, h⟩ := hC x hx
    refine ⟨γ, hγ, ?_⟩
    refine (mul_le_mul_of_nonneg_right (hle x) (pow_nonneg (AutomorphicForm.height_pos _).le N)).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left h hB0

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.GalLaws
section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

section SlopeTestRemainingChoices

open IsDedekindDomain Formalism.L2.Host GroundTheory.Global GroundTheory.Global.IdeleGroup
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private noncomputable abbrev act (σ : K ≃+* K) (g : AdelicGLn.AdelicGL K n) : AdelicGLn.AdelicGL K n :=
  Matrix.GeneralLinearGroup.map (CT.adMap σ) g

private theorem ad_symm (σ : K ≃+* K) (a : 𝔸[K]) : CT.adMap σ.symm (CT.adMap σ a) = a := by
  rw [← (UpperTheory.ConvolutionTheory.K.adBasic K).2.2, RingEquiv.self_trans_symm, (UpperTheory.ConvolutionTheory.K.adBasic K).2.1]

private theorem act_symm (σ : K ≃+* K) (g : AdelicGLn.AdelicGL K n) : act σ.symm (act σ g) = g :=
  Matrix.GeneralLinearGroup.ext fun _ _ => ad_symm σ _

private theorem act_mul (σ : K ≃+* K) (g h : AdelicGLn.AdelicGL K n) : act σ (g * h) = act σ g * act σ h :=
  map_mul (Matrix.GeneralLinearGroup.map (CT.adMap σ)) g h

private theorem act_unip (σ : K ≃+* K) {r : ℕ} (X : UPos n r → 𝔸[K]) :
    act σ (unipGL X) = unipGL fun p => CT.adMap σ (X p) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change CT.adMap σ (unipMatrix X i j) = unipMatrix _ i j
  simp only [unipMatrix, Matrix.add_apply, blockEntry_apply, Matrix.one_apply]
  split_ifs <;> simp

private theorem act_blk (σ : K ≃+* K) {a b : ℕ} (x : AdelicGLn.AdelicGL K a) (y : AdelicGLn.AdelicGL K b) :
    act σ (blk x y) = blk (act σ x) (act σ y) := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change CT.adMap σ (Matrix.fromBlocks x.val 0 0 y.val (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)) =
    Matrix.fromBlocks (act σ x).val 0 0 (act σ y).val (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
  rcases finSumFinEquiv.symm i with p | p <;> rcases finSumFinEquiv.symm j with q | q
  · rfl
  · exact map_zero _
  · exact map_zero _
  · rfl


open Classical in
private noncomputable def rl (w : InfinitePlace K) : ℝ →+* w.Completion :=
  if hw : w.IsReal then ((ringEquivRealOfIsReal hw).symm : ℝ ≃+* w.Completion).toRingHom
  else ((ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.1 hw)).symm : ℂ ≃+* w.Completion).toRingHom.comp
    Complex.ofRealHom

omit [NumberField K] in
private theorem continuous_rl (w : InfinitePlace K) : Continuous (rl w) := by
  unfold rl
  split_ifs with hw
  · exact (isometryEquivRealOfIsReal hw).symm.continuous
  · exact (isometryEquivComplexOfIsComplex (not_isReal_iff_isComplex.1 hw)).symm.continuous.comp
      Complex.continuous_ofReal

private theorem pos_fst (ρ : ℝ) (hρ : 0 < ρ) (w : InfinitePlace K) :
    ((posIdele ρ hρ : IdeleGroup K) : 𝔸[K]).1 w = rl w ρ := by
  rw [← coe_infiniteProj, infiniteProj_posIdele]
  change posRealElem w (ρ ^ w.mult) = _
  unfold posRealElem rl
  split_ifs with hw
  · simp [InfinitePlace.mult, hw]
  · simp [InfinitePlace.mult, hw, Real.sqrt_sq hρ.le]

private theorem ad_pos (σ : K ≃+* K) (ρ : ℝ) (hρ : 0 < ρ) :
    CT.adMap σ ((posIdele ρ hρ : IdeleGroup K) : 𝔸[K]) = ((posIdele ρ hρ : IdeleGroup K) : 𝔸[K]) := by
  refine adele_ext (fun u => ?_) fun v => ?_
  · change CT.infEquiv σ u (((posIdele ρ hρ : IdeleGroup K) : 𝔸[K]).1 (u.comap σ.toRingHom)) = _
    rw [pos_fst, pos_fst]
    exact congrFun ((Rat.denseRange_cast (𝕜 := ℝ)).equalizer
      ((CT.continuous_infEquiv σ u).comp (continuous_rl (u.comap σ.toRingHom))) (continuous_rl u)
      (funext fun q => (map_ratCast ((CT.infEquiv σ u).toRingHom.comp (rl (u.comap σ.toRingHom))) q).trans
        (map_ratCast (rl u) q).symm)) ρ
  · change (CT.compEquiv σ.symm v).symm (((posIdele ρ hρ : IdeleGroup K) : 𝔸[K]).2 (CT.plMap σ.symm v)) = _
    rw [posIdele_finite, posIdele_finite, map_one]

private theorem act_central (σ : K ≃+* K) (s : {r : ℝ // 0 < r}) :
    act σ (centralSection K n s) = centralSection K n s := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change CT.adMap σ ((centralSection K n s : Matrix (Fin n) (Fin n) 𝔸[K]) i j) = _
  rw [centralSection, MonoidHom.comp_apply, MonoidHom.comp_apply, scalarUnits_apply, coe_diagUnits, posIdeleHom_apply,
    Matrix.diagonal_apply]
  split_ifs
  · exact ad_pos σ _ _
  · exact map_zero _

private theorem norm_inf (σ : K ≃+* K) (u : InfinitePlace K) (y : (u.comap σ.toRingHom).Completion) :
    ‖CT.infEquiv σ u y‖ = ‖y‖ := by
  have hd : DenseRange (algebraMap K (u.comap σ.toRingHom).Completion) := by
    apply (AbsoluteValue.Completion.denseRange_coe (u.comap σ.toRingHom).1).mono
    rintro _ ⟨x, rfl⟩
    refine ⟨x.ofAbs, ?_⟩
    rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply, Algebra.algebraMap_self_apply]
  have hn : ∀ (w : InfinitePlace K) (x : K), ‖algebraMap K w.Completion x‖ = w x := fun w x => by
    rw [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply, Algebra.algebraMap_self_apply]
    exact AbsoluteValue.Completion.norm_coe _
  refine congrFun (hd.equalizer (continuous_norm.comp (CT.continuous_infEquiv σ u)) continuous_norm
    (funext fun x => ?_)) y
  simp only [Function.comp_apply]
  rw [CT.infEquiv_algebraMap, hn, hn]
  rfl

private theorem mem_int (v : HeightOneSpectrum (𝓞 K)) (y : v.adicCompletion K) :
    y ∈ (ValuativeRel.valuation (v.adicCompletion K)).integer ↔ Valued.v y ≤ 1 := by
  haveI : (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [Valuation.mem_integer_iff, (ValuativeRel.isEquiv (ValuativeRel.valuation (v.adicCompletion K))
    (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ)))).le_one_iff_le_one]

private theorem act_compact (σ : K ≃+* K) {k : AdelicGLn.AdelicGL K n} (hk : k ∈ (maxCompact : Subgroup _)) :
    act σ k ∈ (maxCompact : Subgroup (AdelicGLn.AdelicGL K n)) := by
  refine ⟨fun u y => ?_, fun v => ?_⟩
  · obtain ⟨x, rfl⟩ : ∃ x : Fin n → (u.comap σ.toRingHom).Completion, y = fun i => (CT.infEquiv σ u).toRingHom (x i) :=
      ⟨fun i => (CT.infEquiv σ u).symm (y i), funext fun i => ((CT.infEquiv σ u).apply_symm_apply _).symm⟩
    have hN := fun z : Fin n → (u.comap σ.toRingHom).Completion =>
      euclidNorm_map (CT.infEquiv σ u).toRingHom (norm_inf σ u) z
    have hv : Matrix.vecMul (fun i => (CT.infEquiv σ u).toRingHom (x i)) (infAt u (act σ k) : Matrix (Fin n) (Fin n) u.Completion) =
        fun j => (CT.infEquiv σ u).toRingHom
          (Matrix.vecMul x (infAt (u.comap σ.toRingHom) k : Matrix (Fin n) (Fin n) (u.comap σ.toRingHom).Completion) j) := by
      funext j
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.vecMul, dotProduct, map_sum, map_mul]
      rfl
    rw [hv, hN, hN, hk.1 (u.comap σ.toRingHom) x]
  · have h : ∀ y : (CT.plMap σ.symm v).adicCompletion K, y ∈ (ValuativeRel.valuation _).integer →
        (CT.compEquiv σ.symm v).symm y ∈ (ValuativeRel.valuation _).integer := fun y hy => by
      rw [mem_int] at hy ⊢
      rwa [← CT.valued_le_one_iff σ.symm v, RingEquiv.apply_symm_apply]
    have hv := (GLnLocal.mem_integralGL_iff _ _).1 (hk.2 (CT.plMap σ.symm v))
    have hf : finAt v (act σ k) =
        Matrix.GeneralLinearGroup.map (CT.compEquiv σ.symm v).symm.toRingHom (finAt (CT.plMap σ.symm v) k) := by
      ext i j
      rfl
    rw [hf]
    refine (GLnLocal.mem_integralGL_iff _ _).2 ⟨fun i j => h _ (hv.1 i j), fun i j => ?_⟩
    rw [← map_inv]
    exact h _ (hv.2 i j)

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.galLaws :
    ∀ {K : Type} [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (μ₂ : Measure (G1 K 2)) [μ₂.IsHaarMeasure] (σ : K ≃+* K) (θ : Twist μ) (θ₂ : Twist μ₂), UpperTheory.ConvolutionTheory.K.IsGal σ θ → UpperTheory.ConvolutionTheory.K.IsGal σ θ₂ →
      (∀ m₁ m₂ t, θ.e (lv m₁ m₂ t) = lv (θ₂.e m₁) (θ₂.e m₂) t) ∧
      (∀ X : UPos (2 + 2) 2 → 𝔸[K],
        (∃ Y, θ.e (unipOne (K := K) (n := 2 + 2) 2 X) = unipOne (K := K) (n := 2 + 2) 2 Y) ∧
        ∃ Y, θ.e.symm (unipOne (K := K) (n := 2 + 2) 2 X) = unipOne (K := K) (n := 2 + 2) 2 Y) ∧
      (∀ k, θ.e k ∈ KG K (2 + 2) ↔ k ∈ KG K (2 + 2)) ∧ (∀ γ, θ.e γ ∈ PK K ↔ γ ∈ PK K) ∧ ∀ g, HH (θ.e g) = HH g := by
  intro K _ _ μ _ μ₂ _ σ θ θ₂ h h₂
  have e : ∀ g, ((θ.e g : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) = act σ g := h
  have e₂ : ∀ g, ((θ₂.e g : G1 K 2) : AdelicGLn.AdelicGL K 2) = act σ g := h₂
  have hl : ∀ (m₁ m₂ : G1 K 2) (t : ℝ), θ.e (lv m₁ m₂ t) = lv (θ₂.e m₁) (θ₂.e m₂) t := fun m₁ m₂ t => Subtype.ext (by
    rw [e, blkLaws.1, blkLaws.1, act_blk, act_mul, act_mul, e₂, e₂, zt, zt, act_central, act_central])
  have hn (X : UPos (2 + 2) 2 → 𝔸[K]) :
      θ.e (unipOne (K := K) (n := 2 + 2) 2 X) =
        unipOne (K := K) (n := 2 + 2) 2 (fun p => Formalism.L2.Host.CT.adMap σ (X p)) := by
    apply Subtype.ext
    rw [e, coe_unipOne, coe_unipOne, act_unip]
  have hk : ∀ k, θ.e k ∈ KG K (2 + 2) ↔ k ∈ KG K (2 + 2) := fun k => by
    change ((θ.e k : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ∈ (maxCompact : Subgroup _) ↔
      (k : AdelicGLn.AdelicGL K (2 + 2)) ∈ (maxCompact : Subgroup _)
    rw [e]
    exact ⟨fun hh => act_symm σ (k : AdelicGLn.AdelicGL K (2 + 2)) ▸ act_compact σ.symm hh, act_compact σ⟩
  have hP : ∀ γ : G1 K (2 + 2), γ ∈ PK K ↔ γ ∈ Gam K (2 + 2) ∧ ∀ i j : Fin (2 + 2), 2 ≤ (i : ℕ) → (j : ℕ) < 2 →
      ((γ : AdelicGLn.AdelicGL K (2 + 2)) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]) i j = 0 := fun γ =>
    ⟨fun ⟨δ, hδ, hh⟩ => hh ▸ ⟨δ.2, (pkLaws.1 δ).1 hδ⟩, fun ⟨h1, h2⟩ => ⟨⟨γ, h1⟩, (pkLaws.1 ⟨γ, h1⟩).2 h2, rfl⟩⟩
  refine ⟨hl, fun X => ⟨⟨_, hn X⟩, fun p => Formalism.L2.Host.CT.adMap σ.symm (X p), ?_⟩, hk, fun γ => ?_, fun g => ?_⟩
  · apply θ.e.injective
    rw [θ.e.apply_symm_apply, hn]
    exact congrArg (unipOne (K := K) (n := 2 + 2) 2) (funext fun p => (ad_symm σ.symm (X p)).symm)
  · rw [hP, hP, θ.mem_gam, e]
    refine and_congr_right fun _ => forall₄_congr fun i j _ _ => ?_
    change Formalism.L2.Host.CT.adMap σ (((γ : AdelicGLn.AdelicGL K (2 + 2)) : Matrix _ _ 𝔸[K]) i j) = 0 ↔ _
    exact map_eq_zero_iff _ (Function.LeftInverse.injective (ad_symm σ))
  · obtain ⟨X, m₁, m₂, t, k, hk', rfl⟩ := iwa g
    rw [map_mul, map_mul, hn, hl, hpSpec.1, hpSpec.1, (hpSpec.2.1 k hk').1, (hpSpec.2.1 _ ((hk k).2 hk')).1]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpqMinor
section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate
open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial

private theorem hpq_loc {E : Type*} [NormedField E] {n : ℕ} (g : GL (Fin n) E) (i j p q : Fin n) :
    ‖(g : Matrix (Fin n) (Fin n) E) i j * (g : Matrix (Fin n) (Fin n) E) p q‖ ≤ locHeight g ^ 2 := by
  rw [norm_mul, sq]
  exact mul_le_mul (norm_apply_le_locHeight g i j) (norm_apply_le_locHeight g p q) (norm_nonneg _) (locHeight_pos g).le

private theorem hpq_minor {K : Type} [Field K] [NumberField K] {n : ℕ} (h : AdelicGLn.AdelicGL K n) (r c : Fin 2 → Fin n)
    (y : GroundTheory.Global.IdeleGroup K) (hy : (y : 𝔸[K]) = ((h : Matrix (Fin n) (Fin n) 𝔸[K]).submatrix r c).det) :
    (GroundTheory.Global.IdeleGroup.ideleModule K y : ℝ) ≤ (∏ w : InfinitePlace K, (2 : ℝ) ^ w.mult) * AutomorphicForm.height h ^ 2 := by
  classical
  rw [Matrix.det_fin_two] at hy
  simp only [Matrix.submatrix_apply] at hy
  have hi : ∀ w : InfinitePlace K, ‖(y : 𝔸[K]).1 w‖ ≤ 2 * locHeight (infAt w h) ^ 2 := by
    intro w
    have e : (y : 𝔸[K]).1 w = (infAt w h : Matrix (Fin n) (Fin n) w.Completion) (r 0) (c 0) * (infAt w h : Matrix (Fin n) (Fin n) w.Completion) (r 1) (c 1) -
        (infAt w h : Matrix (Fin n) (Fin n) w.Completion) (r 0) (c 1) * (infAt w h : Matrix (Fin n) (Fin n) w.Completion) (r 1) (c 0) := by
      rw [hy]; rfl
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have h1 := hpq_loc (infAt w h) (r 0) (c 0) (r 1) (c 1)
    have h2 := hpq_loc (infAt w h) (r 0) (c 1) (r 1) (c 0)
    linarith
  have hf : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), ‖(y : 𝔸[K]).2 v‖ ≤ locHeight (finAt v h) ^ 2 := by
    intro v
    have e : (y : 𝔸[K]).2 v = (finAt v h : Matrix (Fin n) (Fin n) (v.adicCompletion K)) (r 0) (c 0) * (finAt v h : Matrix (Fin n) (Fin n) (v.adicCompletion K)) (r 1) (c 1) +
        -((finAt v h : Matrix (Fin n) (Fin n) (v.adicCompletion K)) (r 0) (c 1) * (finAt v h : Matrix (Fin n) (Fin n) (v.adicCompletion K)) (r 1) (c 0)) := by
      rw [hy, sub_eq_add_neg]; rfl
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hpq_loc _ _ _ _ _) ?_)
    rw [norm_neg]
    exact hpq_loc _ _ _ _ _
  set s := (finite_mulSupport_locHeight_finAt h).union (GroundTheory.Global.IdeleGroup.finite_mulSupport_norm y)
  have h1 : ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), locHeight (finAt v h) = ∏ v ∈ s.toFinset, locHeight (finAt v h) :=
    finprod_eq_prod_of_mulSupport_subset _ fun v hv => by
      simp only [Set.Finite.coe_toFinset, Set.mem_union]; exact Or.inl hv
  have h2 : ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), ‖(y : 𝔸[K]).2 v‖ = ∏ v ∈ s.toFinset, ‖(y : 𝔸[K]).2 v‖ :=
    finprod_eq_prod_of_mulSupport_subset _ fun v hv => by
      simp only [Set.Finite.coe_toFinset, Set.mem_union]; exact Or.inr hv
  rw [GroundTheory.Global.IdeleGroup.ideleModule_eq, AutomorphicForm.height, h1, h2, mul_pow, ← mul_assoc, ← Finset.prod_pow, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib]
  refine mul_le_mul (Finset.prod_le_prod₀ (fun w _ => by positivity) fun w _ => ?_)
    (Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) fun v _ => hf v) (Finset.prod_nonneg fun v _ => norm_nonneg _)
    (Finset.prod_nonneg fun w _ => by positivity)
  rw [← pow_mul, mul_comm w.mult 2, pow_mul, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (hi w) _

private theorem hpq_rows {R : Type} [CommRing R] (X : UPos (2 + 2) 2 → R) (a b : GL (Fin 2) R) (k : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R)
    (c : Fin 2 → Fin (2 + 2)) :
    (((unipGL X * blk a b : GL (Fin (2 + 2)) R) : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) * k).submatrix (Fin.natAdd 2) c =
      (b : Matrix (Fin 2) (Fin 2) R) * k.submatrix (Fin.natAdd 2) c := by
  have h1 : ∀ (M : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) (i : Fin 2) j, (unipMatrix X * M) (Fin.natAdd 2 i) j = M (Fin.natAdd 2 i) j := by
    intro M i j
    have : (blockEntry X * M) (Fin.natAdd 2 i) j = 0 := by
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [blockEntry_apply, dite_eq_right (by simp), zero_mul]
    rw [unipMatrix, add_mul, one_mul, Matrix.add_apply, this, add_zero]
  ext i j
  rw [Matrix.submatrix_apply, Units.val_mul, coe_unipGL, mul_assoc, h1, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_add]
  simp only [blk, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_castAdd,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.hpQht :
    ∀ {K : Type} [Field K] [NumberField K], ∃ c C : ℝ, 0 < c ∧ ∀ g : G1 K (2 + 2), HH g ≤ c * Real.log (qht g) + C := by
  intro K _ _
  set D : ℝ := (∏ w : InfinitePlace K, (2 : ℝ) ^ w.mult) * heightConst K (2 + 2) ^ 2 with hD
  have hc1 := one_le_heightConst (K := K) (n := 2 + 2)
  have hD0 : 0 < D := mul_pos (Finset.prod_pos fun w _ => by positivity) (by positivity)
  refine ⟨2, Real.log D, two_pos, fun g => ?_⟩
  obtain ⟨X, m₁, m₂, t, k, hk, hg⟩ := iwa g
  have ht : HH g = t := by
    rw [hg, (hpSpec (K := K)).1, ((hpSpec (K := K)).2.1 k hk).1, add_zero]
  have key : ∀ γ : Gam K (2 + 2), Real.exp t ≤
      D * AutomorphicForm.height (((γ : G1 K (2 + 2)) * g : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) ^ 2 := by
    intro γ
    obtain ⟨δ, hδ⟩ : ∃ δ : GL (Fin (2 + 2)) K, AdelicGLn.diagonal K (2 + 2) δ = ((γ⁻¹ : Gam K (2 + 2)) : G1 K (2 + 2)) := (γ⁻¹).2
    set h : AdelicGLn.AdelicGL K (2 + 2) := (((γ : G1 K (2 + 2)) * g : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) with hh
    set b : AdelicGLn.AdelicGL K 2 := (m₂ : AdelicGLn.AdelicGL K 2) * zt K (-t) with hb
    have hb' : (detModule K 2 b : ℝ) = Real.exp (-t) := by
      rw [hb, map_mul, mem_normOneGL_iff_detModule.1 m₂.2, one_mul, zt, detModule_centralSection two_pos]
    have e1 : AdelicGLn.diagonal K (2 + 2) δ =
        unipGL X * blk ((m₁ : AdelicGLn.AdelicGL K 2) * zt K t) b * ((k : AdelicGLn.AdelicGL K (2 + 2)) * h⁻¹) := by
      rw [← mul_assoc, hb, ← (blkLaws (K := K)).1, ← coe_unipOne, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← hg, hδ, hh]
      simp
    obtain ⟨c, -, hc⟩ := (pluck δ δ).1
    have e2 : algebraMap K 𝔸[K] ((δ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K).submatrix (Fin.natAdd 2) c).det =
        (b : Matrix (Fin 2) (Fin 2) 𝔸[K]).det * ((((k : AdelicGLn.AdelicGL K (2 + 2)) * h⁻¹ : AdelicGLn.AdelicGL K (2 + 2)) :
          Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]).submatrix (Fin.natAdd 2) c).det := by
      rw [← Matrix.det_mul, ← hpq_rows X ((m₁ : AdelicGLn.AdelicGL K 2) * zt K t) b, ← Units.val_mul, ← e1, RingHom.map_det]
      rfl
    have h3 := hpq_minor ((k : AdelicGLn.AdelicGL K (2 + 2)) * h⁻¹) (Fin.natAdd 2) c
      ((AdelicGLn.det K 2 b)⁻¹ * GroundTheory.Global.IdeleGroup.diagonal K (Units.mk0 _ hc)) (by
        rw [Units.val_mul, GroundTheory.Global.IdeleGroup.coe_diagonal, Units.val_mk0, e2, ← AdelicGLn.coe_det, Units.inv_mul_cancel_left])
    rw [map_mul, GroundTheory.Global.IdeleGroup.ideleModule_diagonal, mul_one, map_inv, Positive.coe_inv] at h3
    change (detModule K 2 b : ℝ)⁻¹ ≤ _ at h3
    rw [hb', Real.exp_neg, inv_inv] at h3
    have h4 := height_mul_le (k : AdelicGLn.AdelicGL K (2 + 2)) h⁻¹
    rw [height_eq_one_of_mem_maxCompact (k := (k : AdelicGLn.AdelicGL K (2 + 2))) hk, mul_one, height_inv] at h4
    refine h3.trans ?_
    rw [hD, mul_assoc, ← mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos _).le h4 _) (Finset.prod_nonneg fun w _ => by positivity)
  have hs : 0 < Real.sqrt (Real.exp t / D) := Real.sqrt_pos.2 (div_pos (Real.exp_pos t) hD0)
  have hq : Real.sqrt (Real.exp t / D) ≤ qht g := by
    refine le_ciInf fun γ => ?_
    rw [Real.sqrt_le_left (height_pos _).le, div_le_iff₀ hD0, mul_comm]
    exact key γ
  have h5 := Real.log_le_log hs hq
  rw [Real.log_sqrt (div_pos (Real.exp_pos t) hD0).le, Real.log_div (Real.exp_pos t).ne' hD0.ne', Real.log_exp] at h5
  rw [ht]
  linarith
end

