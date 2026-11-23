module

public import Mathlib

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GroupActionHaarScalingContinuous
section
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.Adelic.ModulusAction

theorem exists_continuous_modulus :
    ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
      [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
      (μ : Measure V) [μ.IsAddHaarMeasure] (T : Type) [Group T] [TopologicalSpace T]
      [FirstCountableTopology T] [LocallyCompactSpace T] (a : T → V →+ V),
      (Continuous fun p : T × V => a p.1 p.2) → Continuous (fun t : T => t⁻¹) →
      (∀ y, a 1 y = y) → (∀ s t y, a (s * t) y = a s (a t y)) →
      ∃ χ : T →* ℝ≥0, Continuous χ ∧ ∀ t, μ.map (a t) = χ t • μ := by
  intro V _ _ _ _ _ _ _ _ μ _ T _ _ _ _ a ha hinv h1 hmul
  have hat : ∀ t, Continuous (a t) := fun t => by
    have h := ha.comp (continuous_const.prodMk (continuous_id (X := V)) :
      Continuous fun y : V => (t, y))
    exact h
  have hleft : ∀ t y, a t⁻¹ (a t y) = y := by
    intro t y
    rw [← hmul, inv_mul_cancel, h1]
  have hright : ∀ t y, a t (a t⁻¹ y) = y := by
    intro t y
    rw [← hmul, mul_inv_cancel, h1]
  have hfin : ∀ t, IsFiniteMeasureOnCompacts (μ.map (a t)) := by
    intro t
    refine ⟨fun K hK => ?_⟩
    rw [Measure.map_apply (hat t).measurable hK.isClosed.measurableSet]
    refine lt_of_le_of_lt (measure_mono ?_) ((hK.image (hat t⁻¹)).measure_lt_top)
    intro y hy
    exact ⟨a t y, hy, hleft t y⟩
  have hinvar : ∀ t, (μ.map (a t)).IsAddLeftInvariant := by
    intro t
    refine ⟨fun g => ?_⟩
    rw [Measure.map_map (measurable_const_add g) (hat t).measurable]
    have e : (fun x => g + x) ∘ a t = a t ∘ fun x => a t⁻¹ g + x := by
      funext x
      simp only [Function.comp_apply, map_add (f := _), hright]
    rw [e, ← Measure.map_map (hat t).measurable (measurable_const_add _),
      map_add_left_eq_self]
  have hscale : ∀ t, ∃ c : ℝ≥0, μ.map (a t) = c • μ := by
    intro t
    haveI := hfin t
    haveI := hinvar t
    exact ⟨_, Measure.isAddLeftInvariant_eq_smul _ μ⟩
  choose c hc using hscale
  obtain ⟨f, hfc, hf0, hfx⟩ := exists_continuous_nonneg_pos (0 : V)
  have hI : 0 < ∫ y, f y ∂μ :=
    f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hfc hf0 hfx
  have hint : ∀ t (g : V → ℝ), Continuous g →
      ∫ y, g (a t y) ∂μ = (c t : ℝ) * ∫ y, g y ∂μ := by
    intro t g hg
    rw [← integral_map (hat t).measurable.aemeasurable hg.aestronglyMeasurable, hc t,
      integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
  have hform : ∀ t, (c t : ℝ) * ∫ y, f y ∂μ = ∫ y, f (a t y) ∂μ := fun t =>
    (hint t f f.continuous).symm
  have hone : c 1 = 1 := by
    apply NNReal.coe_injective
    apply mul_right_cancel₀ hI.ne'
    rw [hform, NNReal.coe_one, one_mul]
    simp only [h1]
  have hmulc : ∀ s t, c (s * t) = c s * c t := by
    intro s t
    apply NNReal.coe_injective
    apply mul_right_cancel₀ hI.ne'
    rw [hform, NNReal.coe_mul]
    calc ∫ y, f (a (s * t) y) ∂μ = ∫ y, f (a s (a t y)) ∂μ := by simp only [hmul]
      _ = (c t : ℝ) * ∫ y, f (a s y) ∂μ := hint t (fun z => f (a s z)) (f.continuous.comp (hat s))
      _ = (c s : ℝ) * (c t : ℝ) * ∫ y, f y ∂μ := by rw [← hform s]; ring
  have hF : Continuous fun t => ∫ y, f (a t y) ∂μ := by
    refine continuous_iff_continuousAt.2 fun t₀ => ?_
    obtain ⟨N, hN, hNn⟩ := exists_compact_mem_nhds t₀
    set s : Set V := (fun p : T × V => a p.1 p.2) '' (((fun t => t⁻¹) '' N) ×ˢ tsupport f)
      with hsdef
    have hs : IsCompact s := ((hN.image hinv).prod hfc.isCompact).image ha
    have hG : Continuous fun t => ∫ y in s, f (a t y) ∂μ := by
      refine continuous_parametric_integral_of_continuous ?_ hs
      exact f.continuous.comp ha
    refine hG.continuousAt.congr (Filter.eventually_of_mem hNn fun t ht => ?_)
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
    by_contra hne
    exact hy ⟨(t⁻¹, a t y), ⟨⟨t, ht, rfl⟩, subset_tsupport _ hne⟩, hleft t y⟩
  have hcreal : (fun t => (c t : ℝ)) = fun t => (∫ y, f (a t y) ∂μ) / ∫ y, f y ∂μ :=
    funext fun t => eq_div_of_mul_eq hI.ne' (hform t)
  refine ⟨{ toFun := c, map_one' := hone, map_mul' := hmulc }, ?_, hc⟩
  show Continuous c
  have hcont : Continuous fun t => (c t : ℝ) := by
    rw [hcreal]
    exact hF.div_const _
  exact Continuous.subtype_mk hcont fun t => (c t).2

end GlobalTheory.CompanionTheory.Adelic.ModulusAction
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SymmetricInvertibleExistsPosdefCongruence
section
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem exists_posDef_majorant_of_isSymm :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℝ), B.IsSymm → B.det ≠ 0 →
      ∃ P : Matrix ι ι ℝ, P.PosDef ∧ P * B⁻¹ * P = B := by
  intro ι _ _ B hsym hdet
  have hH : B.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hsym
  obtain ⟨U, hU⟩ : ∃ U : Matrix ι ι ℝ, U = (hH.eigenvectorUnitary : Matrix ι ι ℝ) := ⟨_, rfl⟩
  obtain ⟨d, hdd⟩ : ∃ d : ι → ℝ, d = hH.eigenvalues := ⟨_, rfl⟩
  have hUs : star U * U = 1 := by subst hU; simp
  have hsU : U * star U = 1 := by subst hU; simp
  have hspec : B = U * Matrix.diagonal d * star U := by
    conv_lhs => rw [hH.spectral_theorem]
    subst hU hdd
    simp [Unitary.conjStarAlgAut_apply]
  have hd : ∀ i, d i ≠ 0 := by
    intro i hi
    rw [hdd] at hi
    apply hdet
    rw [hH.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  have conj : ∀ a b : ι → ℝ, (U * Matrix.diagonal a * star U) * (U * Matrix.diagonal b * star U) =
      U * Matrix.diagonal (fun i => a i * b i) * star U := by
    intro a b
    calc U * Matrix.diagonal a * star U * (U * Matrix.diagonal b * star U)
        = U * Matrix.diagonal a * (star U * U) * Matrix.diagonal b * star U := by
          simp only [Matrix.mul_assoc]
      _ = U * (Matrix.diagonal a * Matrix.diagonal b) * star U := by
          rw [hUs, Matrix.mul_one, Matrix.mul_assoc U]
      _ = _ := by rw [Matrix.diagonal_mul_diagonal]
  have hinv : B⁻¹ = U * Matrix.diagonal (fun i => (d i)⁻¹) * star U := by
    apply Matrix.inv_eq_right_inv
    rw [hspec, conj]
    rw [show (fun i => d i * (d i)⁻¹) = fun _ => (1 : ℝ) from funext fun i => mul_inv_cancel₀ (hd i),
      Matrix.diagonal_one, Matrix.mul_one, hsU]
  refine ⟨U * Matrix.diagonal (fun i => |d i|) * star U, ?_, ?_⟩
  · rw [Matrix.IsUnit.posDef_star_right_conjugate_iff ⟨⟨U, star U, hsU, hUs⟩, rfl⟩,
      Matrix.posDef_diagonal_iff]
    exact fun i => abs_pos.mpr (hd i)
  · rw [hinv, conj, conj]
    conv_rhs => rw [hspec]
    congr 3
    funext i
    show |d i| * (d i)⁻¹ * |d i| = d i
    rw [mul_right_comm, abs_mul_abs_self, mul_inv_cancel_right₀ (hd i)]

end GlobalTheory.CompanionTheory.SW
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TotallyRealContinuousEmbeddingInfiniteAdeles
section
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.AdelicRealLine

theorem norm_eq_abs_ringEquiv {F : Type} [Field F] {w : InfinitePlace F} (hw : w.IsReal)
    (x : w.Completion) :
    ‖x‖ = |InfinitePlace.Completion.ringEquivRealOfIsReal hw x| := by
  have h := (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).dist_eq x 0
  have h0 : (InfinitePlace.Completion.isometryEquivRealOfIsReal hw) 0 = 0 :=
    map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hw)
  rw [h0, dist_zero_right, dist_zero_right] at h
  rw [← h, Real.norm_eq_abs]
  rfl

theorem exists_continuous_real_embedding :
    ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F →
      (∃ θ : ℝ →+* InfiniteAdeleRing F, Continuous θ) ∧
        ∀ θ : ℝ →+* InfiniteAdeleRing F, Continuous θ →
          ∀ (t : ℝ) (w : InfinitePlace F), ‖θ t w‖ = |t| := by
  intro F _ _ hF
  have hr : ∀ w : InfinitePlace F, w.IsReal := fun w => @IsTotallyReal.isReal F _ hF w
  refine ⟨⟨Pi.ringHom fun w =>
    (InfinitePlace.Completion.ringEquivRealOfIsReal (hr w)).symm.toRingHom, ?_⟩, ?_⟩
  · refine continuous_pi fun w => ?_
    exact (InfinitePlace.Completion.isometryEquivRealOfIsReal (hr w)).symm.continuous
  · intro θ _ t w
    have hφ := DFunLike.congr_fun (Subsingleton.elim
      (((InfinitePlace.Completion.ringEquivRealOfIsReal (hr w)).toRingHom.comp
        ((Pi.evalRingHom (fun v : InfinitePlace F => v.Completion) w).comp θ)) : ℝ →+* ℝ)
      (RingHom.id ℝ)) t
    change InfinitePlace.Completion.ringEquivRealOfIsReal (hr w) (θ t w) = t at hφ
    rw [GlobalTheory.CompanionTheory.AdelicRealLine.norm_eq_abs_ringEquiv (hr w), hφ]

end GlobalTheory.CompanionTheory.AdelicRealLine
end

