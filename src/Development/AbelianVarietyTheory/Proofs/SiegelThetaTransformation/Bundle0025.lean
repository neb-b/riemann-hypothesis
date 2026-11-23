module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DifferentiableOnDetHMat
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HMatMulVecPerCrd
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (omegaStd)

namespace GlobalTheory.SW

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)
  (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r)

theorem vecQ_add (m m' : Fin g ⊕ Fin g → ℚ) :
    vecQ X bas (m + m') = vecQ X bas m + vecQ X bas m' := by
  simp only [vecQ, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem vecQ_smul (q : ℚ) (m : Fin g ⊕ Fin g → ℚ) : vecQ X bas (q • m) = q • vecQ X bas m := by
  simp only [vecQ, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem vecQ_zero : vecQ X bas 0 = 0 := by simp [vecQ]

theorem vecQ_intCast (m : Fin g ⊕ Fin g → ℤ) :
    vecQ X bas (fun j => (m j : ℚ)) = (bas m : Fin r → E) := by
  have hm : m = ∑ j, m j • Pi.single j (1 : ℤ) := by
    funext j; simp [Pi.single_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [hm, map_sum, AddSubmonoidClass.coe_finsetSum]
  simp only [vecQ, map_zsmul, AddSubgroupClass.coe_zsmul, Int.cast_smul_eq_zsmul]

theorem vecQ_surjective : Function.Surjective (vecQ X bas) := by
  intro v
  obtain ⟨k, hk, hv⟩ := GlobalTheory.LatFin.exists_int_smul_mem X.Λ X.Λ_span v
  refine ⟨(k : ℚ)⁻¹ • fun j => (bas.symm ⟨_, hv⟩ j : ℚ), ?_⟩
  rw [vecQ_smul, vecQ_intCast, LinearEquiv.apply_symm_apply]
  change (k : ℚ)⁻¹ • k • v = v
  rw [← Int.cast_smul_eq_zsmul ℚ, inv_smul_smul₀ (Int.cast_ne_zero.2 hk)]

theorem vecQ_crd (v : Fin r → E) : vecQ X bas (crd X bas v) = v :=
  Function.rightInverse_invFun (vecQ_surjective X bas) v

noncomputable def EFBil : (Fin r → E) →ₗ[ℚ] (Fin r → E) →ₗ[ℚ] ℚ :=
  LinearMap.mk₂ ℚ (EF X)
    (fun u u' v => by
      simp only [EF_def, ← map_add (f := _), herm, Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add])
    (fun q u v => by
      simp only [EF_def, ← map_smul, herm, Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum,
        mul_smul_comm])
    (fun u v v' => by
      simp only [EF_def, herm, cc, Pi.add_apply, map_add (f := _), Finset.sum_add_distrib, mul_add])
    (fun q u v => by
      simp only [EF_def, herm, cc, Pi.smul_apply, map_rat_smul, ← Finset.smul_sum,
        mul_smul_comm])

variable {X bas}

theorem EF_vecQ (hs : IsSympl X bas) (m m' : Fin g ⊕ Fin g → ℚ) :
    EF X (vecQ X bas m) (vecQ X bas m') =
      -∑ i, (m (Sum.inl i) * m' (Sum.inr i) - m (Sum.inr i) * m' (Sum.inl i)) := by
  change EFBil X _ _ = _
  have h (j k) : EFBil X (bas (Pi.single j 1)) (bas (Pi.single k 1)) =
      -(omegaStd (Pi.single j 1) (Pi.single k 1) : ℤ) := hs _ _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [vecQ, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, h]
  simp [Fintype.sum_sum_type, omegaStd, Pi.single_apply, Finset.sum_sub_distrib, mul_comm]
  ring

theorem vecQ_injective (hs : IsSympl X bas) : Function.Injective (vecQ X bas) := by
  intro m m' h
  have h' (t) := (EF_vecQ hs m t).symm.trans (h ▸ EF_vecQ hs m' t)
  funext j
  rcases j with j | j
  · simpa [Pi.single_apply] using h' (Pi.single (Sum.inr j) 1)
  · simpa [Pi.single_apply] using h' (Pi.single (Sum.inl j) 1)

theorem crd_vecQ (hs : IsSympl X bas) (m : Fin g ⊕ Fin g → ℚ) : crd X bas (vecQ X bas m) = m :=
  Function.leftInverse_invFun (vecQ_injective hs) m

theorem crd_add (hs : IsSympl X bas) (u v : Fin r → E) :
    crd X bas (u + v) = crd X bas u + crd X bas v :=
  vecQ_injective hs (by rw [vecQ_add, vecQ_crd, vecQ_crd, vecQ_crd])

theorem crd_smul (hs : IsSympl X bas) (q : ℚ) (v : Fin r → E) :
    crd X bas (q • v) = q • crd X bas v :=
  vecQ_injective hs (by rw [vecQ_smul, vecQ_crd, vecQ_crd])

theorem crd_zero (hs : IsSympl X bas) : crd X bas 0 = 0 :=
  vecQ_injective hs (by rw [vecQ_crd, vecQ_zero])

theorem EF_crd (hs : IsSympl X bas) (u v : Fin r → E) :
    EF X u v = -∑ i, (crd X bas u (Sum.inl i) * crd X bas v (Sum.inr i) -
      crd X bas u (Sum.inr i) * crd X bas v (Sum.inl i)) := by
  rw [← EF_vecQ hs, vecQ_crd, vecQ_crd]

theorem hMat_mulVec_per_crd (hs : IsSympl X bas) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (v : Fin r → E) :
    hMat X bas idx x *ᵥ (per X x v ∘ idx) = qv (fun i => crd X bas v (Sum.inl i)) +
      tauMat X bas idx x *ᵥ qv fun i => crd X bas v (Sum.inr i) := by
  have h : per X x v ∘ idx =
      perMat X bas idx Sum.inl x *ᵥ qv (fun i => crd X bas v (Sum.inl i)) +
      perMat X bas idx Sum.inr x *ᵥ qv fun i => crd X bas v (Sum.inr i) := by
    funext i
    conv_lhs => rw [← vecQ_crd X bas v, vecQ, per_sum]
    simp only [per_ratSmul, Fintype.sum_sum_type]
    simp [mulVec, dotProduct, mul_comm, qv, Rat.smul_def]
  rw [h, mulVec_add, mulVec_mulVec, mulVec_mulVec, tauMat, hMat_mul_perMat idx hs hx, one_mulVec]

theorem heis_exponent {ι : Type} [Fintype ι] [DecidableEq ι] (τ W : Matrix ι ι ℂ)
    (hτ : τ.IsSymm) (hW : W.IsSymm) (hY : W * τ.map (fun z => (z.im : ℂ)) = 1) (a b : ι → ℚ)
    (u : ι → ℂ) :
    π / 2 * (u ⬝ᵥ W *ᵥ u) + π * I * (qv b ⬝ᵥ τ *ᵥ qv b + 2 * (qv b ⬝ᵥ u) + qv a ⬝ᵥ qv b) =
      -(π * ((u + (1 / 2 : ℂ) • (qv a + τ *ᵥ qv b)) ⬝ᵥ W *ᵥ star (qv a + τ *ᵥ qv b))) +
        π / 2 * ((u + (qv a + τ *ᵥ qv b)) ⬝ᵥ W *ᵥ (u + (qv a + τ *ᵥ qv b))) := by
  have h1 : star (qv a + τ *ᵥ qv b) =
      (qv a + τ *ᵥ qv b) - (2 * I) • (τ.map (fun z => (z.im : ℂ)) *ᵥ qv b) := by
    funext i
    simp only [Pi.star_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, mulVec, dotProduct, qv,
      star_add, star_sum, star_mul', RCLike.star_def, map_ratCast, map_apply, smul_eq_mul,
      Finset.mul_sum, add_sub_assoc, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    have := Complex.sub_conj (τ i j)
    push_cast at this
    linear_combination (-(b j : ℂ)) * this
  have h2 : qv b ⬝ᵥ (qv a + τ *ᵥ qv b) = qv a ⬝ᵥ qv b + qv b ⬝ᵥ τ *ᵥ qv b := by
    rw [dotProduct_add, dotProduct_comm]
  generalize qv a + τ *ᵥ qv b = w at h1 h2 ⊢
  have h3 : w ⬝ᵥ W *ᵥ u = u ⬝ᵥ W *ᵥ w := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hW.eq, dotProduct_comm]
  rw [h1, mulVec_sub, mulVec_smul, mulVec_mulVec, hY, one_mulVec]
  simp only [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_sub, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, h3, dotProduct_comm u (qv b), dotProduct_comm w (qv b), h2]
  ring

theorem heisG_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → (∀ v, vecQ X bas (crd X bas v) = v) ∧ (∀ u v, crd X bas (u + v) = crd X bas u + crd X bas v) ∧ (∀ u v, EF X u v = -∑ i, (crd X bas u (Sum.inl i) * crd X bas v (Sum.inr i) - crd X bas u (Sum.inr i) * crd X bas v (Sum.inl i))) ∧ ∀ (y : Matrix (Fin n) (Fin r) E) (φ : TF n g), IsSB φ → IsSB (heisG X bas y φ) ∧ heisG X bas 0 φ = φ ∧ (∀ y', heisG X bas y (heisG X bas y' φ) = cexp (-(π * I * ((∑ k, EF X (y k) (y' k) : ℚ) : ℂ))) • heisG X bas (y + y') φ) ∧ (∀ ψ, IsSB ψ → ip (heisG X bas y φ) (heisG X bas y ψ) = ip φ ψ) ∧ ∀ x ∈ X.dom, ∀ z : Fin n → Fin g → ℂ, thA X bas idx (heisG X bas y φ) x z = cexp (-(π * ∑ k, (hMat X bas idx x *ᵥ (z k + (1 / 2 : ℂ) • (per X x (y k) ∘ idx))) ⬝ᵥ imInv X bas idx x *ᵥ star (hMat X bas idx x *ᵥ (per X x (y k) ∘ idx)))) * thA X bas idx φ x (fun k => z k + per X x (y k) ∘ idx) := by
  intro E _ _ _ r X g bas idx n hs _
  refine ⟨vecQ_crd X bas, crd_add hs, EF_crd hs, fun y φ hφ => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := _root_.GlobalTheory.SW.heisS_laws _ _
    (Matrix.of fun k i => crd X bas (y k) (Sum.inl i))
    (Matrix.of fun k i => crd X bas (y k) (Sum.inr i)) φ hφ
  refine ⟨h1, ?_, fun y' => ?_, h5, fun x hx z => ?_⟩
  · simp only [heisG, Matrix.zero_apply, crd_zero hs, show ∀ k, (0 : Matrix (Fin n) (Fin r) E) k = 0
      from fun _ => rfl]
    exact h4
  · rw [heisG, heisG, h3, heisG]
    congr 2
    · rw [← mul_neg, ← Rat.cast_neg, ← Finset.sum_neg_distrib]
      congr 2
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [EF_crd hs, neg_neg, Finset.sum_sub_distrib]
      simp only [dotProduct, of_apply, mul_comm]
    · ext k i
      exact (congrFun (crd_add hs (y k) (y' k)) _).symm
    · ext k i
      exact (congrFun (crd_add hs (y k) (y' k)) _).symm
  · have hz (w v) : hMat X bas idx x *ᵥ (w + per X x v ∘ idx) = hMat X bas idx x *ᵥ w +
        (qv (fun i => crd X bas v (Sum.inl i)) +
          tauMat X bas idx x *ᵥ qv fun i => crd X bas v (Sum.inr i)) := by
      rw [mulVec_add, hMat_mulVec_per_crd idx hs hx]
    have hz' (w v) : hMat X bas idx x *ᵥ (w + (1 / 2 : ℂ) • (per X x v ∘ idx)) =
        hMat X bas idx x *ᵥ w + (1 / 2 : ℂ) • (qv (fun i => crd X bas v (Sum.inl i)) +
          tauMat X bas idx x *ᵥ qv fun i => crd X bas v (Sum.inr i)) := by
      rw [mulVec_add, mulVec_smul, hMat_mulVec_per_crd idx hs hx]
    rw [thA, thA, heisG, h2 _ ⟨tauMat_isSymm idx hs hx, tauMat_im_posDef idx hs hx⟩]
    change Fin n → Fin r → E at y
    simp only [hz, hz', hMat_mulVec_per_crd idx hs hx]
    have he := Finset.sum_congr (s₁ := Finset.univ) rfl fun (k : Fin n) _ =>
      heis_exponent _ _ (tauMat_isSymm idx hs hx) (imInv_isSymm idx hs hx) (imInv_mul_im idx hs hx)
        (fun i => crd X bas (y k) (Sum.inl i)) (fun i => crd X bas (y k) (Sum.inr i))
        (hMat X bas idx x *ᵥ z k)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_add_distrib (f := fun k => -_),
      Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at he
    have he' := congrArg cexp he
    rw [Complex.exp_add, Complex.exp_add] at he'
    simp only [← add_assoc (hMat X bas idx x *ᵥ z _)] at he' ⊢
    rw [mul_assoc, ← mul_assoc (cexp _)]
    erw [he']
    rw [mul_assoc, mul_left_comm, ← mul_assoc _ (cexp (π / 2 * _))]
    rfl

end GlobalTheory.SW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IntegrableTsumOfSummableIntegralNorm
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

private theorem integrable_tsum_of_summable_integral_norm' {ι Y E : Type} [Countable ι] [MeasurableSpace Y]
    [NormedAddCommGroup E] [CompleteSpace E]
    (μ : Measure Y) (F : ι → Y → E) (hF : ∀ i, Integrable (F i) μ)
    (hs : Summable fun i => ∫ y, ‖F i y‖ ∂μ) :
    Integrable (fun y => ∑' i, F i y) μ ∧ ∀ᵐ y ∂μ, Summable fun i => ‖F i y‖ := by
  have hmeas : ∀ i, AEMeasurable (fun y => ‖F i y‖ₑ) μ := fun i => (hF i).1.enorm

  have htot : ∫⁻ y, ∑' i, ‖F i y‖ₑ ∂μ ≠ ⊤ := by
    rw [lintegral_tsum hmeas]
    have h : ∀ i, ∫⁻ y, ‖F i y‖ₑ ∂μ = ENNReal.ofReal (∫ y, ‖F i y‖ ∂μ) := fun i =>
      (ofReal_integral_norm_eq_lintegral_enorm (hF i)).symm
    simp_rw [h]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => integral_nonneg fun y => norm_nonneg _) hs]
    exact ENNReal.ofReal_ne_top

  have hsum : ∀ᵐ y ∂μ, Summable fun i => ‖F i y‖ := by
    filter_upwards [ae_lt_top' (AEMeasurable.tsum hmeas) htot] with y hy
    exact tsum_enorm_ne_top_iff_summable_norm.1 hy.ne
  refine ⟨⟨?_, ?_⟩, hsum⟩
  · refine aestronglyMeasurable_of_tendsto_ae (Filter.atTop : Filter (Finset ι))
      (f := fun s y => ∑ i ∈ s, F i y) (fun s => ?_) ?_
    · exact Finset.aestronglyMeasurable_fun_sum s fun i _ => (hF i).1
    · filter_upwards [hsum] with y hy
      exact hy.of_norm.hasSum
  · exact lt_of_le_of_lt (lintegral_mono fun y => enorm_tsum_le_tsum_enorm) htot.lt_top

theorem integrable_tsum_of_summable_integral_norm {ι Y : Type} [Countable ι] [MeasurableSpace Y]
    (μ : Measure Y) (F : ι → Y → ℂ) (hF : ∀ i, Integrable (F i) μ)
    (hs : Summable fun i => ∫ y, ‖F i y‖ ∂μ) :
    Integrable (fun y => ∑' i, F i y) μ ∧ ∫ y, ‖∑' i, F i y‖ ∂μ ≤ ∑' i, ∫ y, ‖F i y‖ ∂μ := by
  obtain ⟨hint, hsum⟩ := integrable_tsum_of_summable_integral_norm' μ F hF hs
  refine ⟨hint, ?_⟩
  have hnorm : ∀ i, Integrable (fun y => ‖F i y‖) μ := fun i => (hF i).norm
  have hs' : Summable fun i => ∫ y, ‖‖F i y‖‖ ∂μ := by simpa only [norm_norm] using hs
  calc ∫ y, ‖∑' i, F i y‖ ∂μ ≤ ∫ y, ∑' i, ‖F i y‖ ∂μ := by
        refine integral_mono_ae hint.norm (integrable_tsum_of_summable_integral_norm' μ _ hnorm hs').1 ?_
        filter_upwards [hsum] with y hy
        exact norm_tsum_le_tsum_norm hy
    _ = ∑' i, ∫ y, ‖F i y‖ ∂μ := (integral_tsum_of_summable_integral_norm hnorm hs').symm

theorem hasSum_setIntegral_of_ae_existsUnique {ι Y E : Type} [Countable ι] [MeasurableSpace Y]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Y) (S : ι → Set Y) (hS : ∀ i, MeasurableSet (S i))
    (hu : ∀ᵐ y ∂μ, ∃! i, y ∈ S i) (f : Y → E) (hf : Integrable f μ) :
    HasSum (fun i => ∫ y in S i, f y ∂μ) (∫ y, f y ∂μ) := by

  have hdisj : Pairwise fun i j => AEDisjoint μ (S i) (S j) := by
    intro i j hij
    refine measure_mono_null (t := {y | ¬ ∃! k, y ∈ S k}) ?_ (ae_iff.1 hu)
    intro y hy h
    exact hij (ExistsUnique.unique h hy.1 hy.2)

  have hcover : (⋃ i, S i : Set Y) =ᵐ[μ] (Set.univ : Set Y) := by
    filter_upwards [hu] with y ⟨i, hi, _⟩
    exact ⟨fun _ => trivial, fun _ => Set.mem_iUnion.2 ⟨i, hi⟩⟩
  have h := hasSum_integral_iUnion_ae (fun i => (hS i).nullMeasurableSet) hdisj hf.integrableOn
  rwa [setIntegral_congr_set hcover, setIntegral_univ] at h

theorem setIntegral_smul_of_measurePreserving {Γ Y E : Type} [Group Γ] [MeasurableSpace Y]
    [MulAction Γ Y] [NormedAddCommGroup E] [NormedSpace ℝ E] (ν : Measure Y)
    (hν : ∀ γ : Γ, MeasurePreserving (fun y : Y => γ • y) ν ν) (γ : Γ) (D : Set Y) (g : Y → E) :
    ∫ y in D, g (γ • y) ∂ν = ∫ y in (fun y : Y => γ⁻¹ • y) ⁻¹' D, g y ∂ν := by
  let φ : Y ≃ᵐ Y :=
    { toEquiv := MulAction.toPerm γ
      measurable_toFun := (hν γ).measurable
      measurable_invFun := (hν γ⁻¹).measurable }
  have hemb : MeasurableEmbedding (fun y : Y => γ • y) := φ.measurableEmbedding
  have hD : D = (fun y : Y => γ • y) ⁻¹' ((fun y : Y => γ⁻¹ • y) ⁻¹' D) := by
    ext y
    simp
  have key := (hν γ).setIntegral_preimage_emb hemb g ((fun y : Y => γ⁻¹ • y) ⁻¹' D)
  rw [← hD] at key
  exact key

theorem unfolding_abstract : ∀ (Γ I Y : Type) [Group Γ] [Countable Γ] [Countable I] [MeasurableSpace Y] [MulAction Γ I] [MulAction Γ Y] (ν : Measure Y) [SFinite ν], (∀ γ : Γ, MeasurePreserving (fun y : Y => γ • y) ν ν) → ∀ D : I → Set Y, (∀ i, MeasurableSet (D i)) → (∀ i, ∀ᵐ y ∂ν, ∃! γ : Γ, γ • y ∈ D (γ • i)) → ∀ f : I → Y → ℂ, (∀ i, Integrable (f i) ν) → Summable (fun i => ∫ y, ‖f i y‖ ∂ν) → (∀ i, IntegrableOn (fun y => ∑' γ : Γ, f (γ • i) (γ • y)) (D i) ν) ∧ Summable (fun i => ∫ y in D i, ‖∑' γ : Γ, f (γ • i) (γ • y)‖ ∂ν) ∧ ∑' i, ∫ y in D i, ∑' γ : Γ, f (γ • i) (γ • y) ∂ν = ∑' i, ∫ y, f i y ∂ν := by
  intro Γ I Y _ _ _ _ _ _ ν _ hν D hD hcov f hf hs

  have hSm : ∀ (j : I) (δ : Γ), MeasurableSet ((fun y : Y => δ • y) ⁻¹' D (δ • j)) :=
    fun j δ => (hν δ).measurable (hD _)
  have hP : ∀ (j : I) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (g : Y → E),
      Integrable g ν →
      HasSum (fun δ : Γ => ∫ y in (fun y : Y => δ • y) ⁻¹' D (δ • j), g y ∂ν) (∫ y, g y ∂ν) :=
    fun j E _ _ g hg => hasSum_setIntegral_of_ae_existsUnique ν
      (fun δ : Γ => (fun y : Y => δ • y) ⁻¹' D (δ • j)) (hSm j) (hcov j) g hg

  have hmove : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (j : I) (δ : Γ) (g : Y → E),
      ∫ y in D (δ • j), g (δ⁻¹ • y) ∂ν = ∫ y in (fun y : Y => δ • y) ⁻¹' D (δ • j), g y ∂ν := by
    intro E _ _ j δ g
    rw [setIntegral_smul_of_measurePreserving ν hν δ⁻¹ (D (δ • j)) g]
    simp only [inv_inv]

  let e : I × Γ ≃ I × Γ :=
    { toFun := fun p => (p.2 • p.1, p.2⁻¹)
      invFun := fun p => (p.2 • p.1, p.2⁻¹)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  have he : ∀ p : I × Γ, e p = (p.2 • p.1, p.2⁻¹) := fun p => rfl
  obtain ⟨c, hc⟩ : ∃ c : I × Γ → ℂ,
      ∀ p, c p = ∫ y in D p.1, f (p.2 • p.1) (p.2 • y) ∂ν := ⟨_, fun _ => rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : I × Γ → ℝ,
      ∀ p, a p = ∫ y in D p.1, ‖f (p.2 • p.1) (p.2 • y)‖ ∂ν := ⟨_, fun _ => rfl⟩
  have hce : ∀ p : I × Γ,
      c (e p) = ∫ y in (fun y : Y => p.2 • y) ⁻¹' D (p.2 • p.1), f p.1 y ∂ν := by
    rintro ⟨j, δ⟩
    rw [he, hc]
    dsimp only
    simp only [inv_smul_smul]
    exact hmove j δ (f j)
  have hae : ∀ p : I × Γ,
      a (e p) = ∫ y in (fun y : Y => p.2 • y) ⁻¹' D (p.2 • p.1), ‖f p.1 y‖ ∂ν := by
    rintro ⟨j, δ⟩
    rw [he, ha]
    dsimp only
    simp only [inv_smul_smul]
    exact hmove j δ (fun y => ‖f j y‖)
  have hnorm_int : ∀ j, Integrable (fun y => ‖f j y‖) ν := fun j => (hf j).norm

  have ha0 : 0 ≤ a := fun p => by
    rw [Pi.zero_apply, ha]
    exact integral_nonneg fun _ => norm_nonneg _
  have hb_sum : Summable (a ∘ e) := by
    have h0 : 0 ≤ a ∘ e := fun p => ha0 (e p)
    refine (summable_prod_of_nonneg h0).2 ⟨fun j => ?_, ?_⟩
    · simp only [Function.comp_apply, hae]
      exact (hP j _ (hnorm_int j)).summable
    · simp only [Function.comp_apply, hae]
      have h1 : ∀ j : I, ∑' δ : Γ, ∫ y in (fun y : Y => δ • y) ⁻¹' D (δ • j), ‖f j y‖ ∂ν =
          ∫ y, ‖f j y‖ ∂ν := fun j => (hP j _ (hnorm_int j)).tsum_eq
      simpa only [h1] using hs
  have ha_sum : Summable a := e.summable_iff.1 hb_sum
  have hc_sum : Summable c := ha_sum.of_norm_bounded fun p => by
    rw [hc, ha]
    exact norm_integral_le_integral_norm _

  have hFint : ∀ (i : I) (γ : Γ), Integrable (fun y => f (γ • i) (γ • y)) (ν.restrict (D i)) :=
    fun i γ => ((hν γ).integrable_comp_of_integrable (hf (γ • i))).restrict
  have hFsum : ∀ i, Summable fun γ : Γ => ∫ y in D i, ‖f (γ • i) (γ • y)‖ ∂ν := fun i => by
    simpa only [ha] using ha_sum.prod_factor i
  have hmain := fun i => integrable_tsum_of_summable_integral_norm (ν.restrict (D i))
    (fun (γ : Γ) (y : Y) => f (γ • i) (γ • y)) (hFint i) (hFsum i)
  refine ⟨fun i => (hmain i).1, ?_, ?_⟩
  · refine Summable.of_nonneg_of_le (fun i => integral_nonneg fun y => norm_nonneg _)
      (fun i => (hmain i).2) ?_
    simpa only [ha] using ((summable_prod_of_nonneg ha0).1 ha_sum).2
  · have hrow : ∀ i, ∫ y in D i, ∑' γ : Γ, f (γ • i) (γ • y) ∂ν = ∑' γ : Γ, c (i, γ) :=
      fun i => (integral_tsum_of_summable_integral_norm (hFint i) (hFsum i)).symm.trans
        (tsum_congr fun γ => (hc (i, γ)).symm)
    have hd : Summable fun p : I × Γ =>
        ∫ y in (fun y : Y => p.2 • y) ⁻¹' D (p.2 • p.1), f p.1 y ∂ν := by
      have h1 := e.summable_iff.2 hc_sum
      simpa only [Function.comp_def, hce] using h1
    calc ∑' i, ∫ y in D i, ∑' γ : Γ, f (γ • i) (γ • y) ∂ν = ∑' i, ∑' γ : Γ, c (i, γ) :=
          tsum_congr hrow
      _ = ∑' p, c p := (hc_sum.tsum_prod' hc_sum.prod_factor).symm
      _ = ∑' p, c (e p) := (e.tsum_eq c).symm
      _ = ∑' p : I × Γ, ∫ y in (fun y : Y => p.2 • y) ⁻¹' D (p.2 • p.1), f p.1 y ∂ν :=
          tsum_congr hce
      _ = ∑' j, ∑' δ : Γ, ∫ y in (fun y : Y => δ • y) ⁻¹' D (δ • j), f j y ∂ν :=
          hd.tsum_prod' hd.prod_factor
      _ = ∑' j, ∫ y, f j y ∂ν := tsum_congr fun j => (hP j (f j) (hf j)).tsum_eq

end GlobalTheory.SW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.OneMemRowHighestAndThPSmulOne
section
open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

theorem one_mem_rowHighest_and_thP_smul_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), (1 : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) ∈ Harm.rowHighest ℂ (fun _ _ => 0) (fun _ _ => 0) ∧ ∀ (c : ℂ) (φ : TF n g) (x : Frame X.Ψ r), thP X hr bas idx (c • φ) 1 x = c * (hMat X bas idx x).det ^ (n / 2) * thS φ (tauMat X bas idx x) 0 := by
  intro E _ _ _ r X g q0 hr bas idx n
  refine ⟨?_, fun c φ x => ?_⟩
  · simp only [Harm.rowHighest, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, MvPolynomial.mem_weightedHomogeneousSubmodule]
    refine ⟨⟨?_, fun _ _ => ?_, fun _ _ => ?_⟩, ?_, ?_⟩
    · show Harm.IsHarmonic _
      unfold Harm.IsHarmonic
      intro t a b
      simp [Harm.laplacian]
    · simp only [Harm.partOf, Finset.sum_const_zero]
      exact MvPolynomial.isWeightedHomogeneous_one _ _
    · simp only [Harm.partOf, Finset.sum_const_zero]
      exact MvPolynomial.isWeightedHomogeneous_one _ _
    · intro t a b _ s
      simp
    · intro t a b _ s
      simp
  · simp only [thP, ReciprocityTheory.ChartRestriction.G.I2.polyDeriv, MvPolynomial.support_one, Finset.sum_singleton,
      MvPolynomial.coeff_zero_one, one_mul]
    have h0 : ∀ (k : ℕ) (hk : k = 0) (v : Fin k → (Fin n → Fin g → ℂ)),
        iteratedFDeriv ℂ k (thA X bas idx (c • φ) x) 0 v = thA X bas idx (c • φ) x 0 := by
      rintro _ rfl v
      exact iteratedFDeriv_zero_apply v
    rw [h0 _ (by simp)]
    unfold thA thS
    simp only [Pi.zero_apply, Matrix.mulVec_zero, dotProduct_zero, Finset.sum_const_zero, mul_zero, Complex.exp_zero,
      one_mul, Pi.smul_apply, smul_eq_mul, mul_assoc, tsum_mul_left, add_zero]
    ring

end GlobalTheory.SW
end

