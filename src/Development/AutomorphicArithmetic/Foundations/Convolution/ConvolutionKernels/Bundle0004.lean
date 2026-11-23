module

public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.Bundle0003
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalTwistEx
public import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.AdNormOne
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalAdEq
section
open MeasureTheory NumberField PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.K

open GroundTheory.Global.AdeleBaseChange in
open scoped NumberField.AdeleRing TensorProduct in
private theorem galAd_eq_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E ≃ₐ[F] E) : galAd σ = MulSemiringAction.toRingHom (E ≃ₐ[F] E) 𝔸[E] σ := by
  refine adeleRingHom_ext (K := F) (fun l => ?_) (fun a => ?_)
  · change adeleTensorEquiv F E (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F 𝔸[F])
      ((adeleTensorEquiv F E).symm (algebraMap E 𝔸[E] l))) = σ • algebraMap E 𝔸[E] l
    rw [adeleTensorEquiv_symm_algebraMap, Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul,
      GroundTheory.Global.AdeleBaseChange.smul_algebraMap, map_one, map_one, mul_one]
    rfl
  · change adeleTensorEquiv F E (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F 𝔸[F])
      ((adeleTensorEquiv F E).symm (adeleMap F E a))) = σ • adeleMap F E a
    rw [adeleTensorEquiv_symm_adeleMap, Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul,
      smul_adeleMap, map_one, map_one, one_mul]
    rfl

theorem UpperTheory.ConvolutionTheory.K.galAdEq :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E),
      galAd σ = Formalism.L2.Host.CT.adMap σ.toRingEquiv := by
  intro F E _ _ _ _ _ σ
  refine UpperTheory.ConvolutionTheory.K.adUnique E σ.toRingEquiv (galAd σ) ?_ fun x => ?_
  · rw [galAd_eq_smul]
    exact continuous_const_smul σ
  · rw [galAd_eq_smul]
    exact GroundTheory.Global.AdeleBaseChange.smul_algebraMap σ x
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalCusp
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

theorem UpperTheory.ConvolutionTheory.K.galCusp :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (σ : K ≃+* K) (e : G1 K n ≃ₜ* G1 K n),
      (∀ g : G1 K n, ((e g : G1 K n) : AdelicGLn.AdelicGL K n) =
        Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap σ) (g : AdelicGLn.AdelicGL K n)) →
      (∀ g, e g ∈ Gam K n ↔ g ∈ Gam K n) → MeasurePreserving e μ μ → ∀ φ ψ : L2 μ, φ ∈ cuspidalL2 μ →
      ((ψ : RightCosetSpace (Gam K n) → ℂ) =ᵐ[quotientMeasure (Gam K n) μ]
        fun y => (φ : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) (e (Quotient.out y)))) → ψ ∈ cuspidalL2 μ := by
  intro K _ _ n μ _ σ e he hg hp φ ψ hφ hψ r hr hrn
  obtain ⟨h1, -⟩ := qmapPres (Gam K n) μ e hg hp
  obtain ⟨a1, a2, a3⟩ := adBasic K
  have hinv : ∀ (τ : K ≃+* K) a, Formalism.L2.Host.CT.adMap τ.symm (Formalism.L2.Host.CT.adMap τ a) = a := fun τ a => by
    rw [← a3, RingEquiv.self_trans_symm, a2]
  let s : (AutomorphicForm.UPos n r → AdeleRing (𝓞 K) K) ≃ₜ+ (AutomorphicForm.UPos n r → AdeleRing (𝓞 K) K) :=
    { toFun := fun X p => Formalism.L2.Host.CT.adMap σ (X p)
      invFun := fun X p => Formalism.L2.Host.CT.adMap σ.symm (X p)
      left_inv := fun X => funext fun p => hinv σ _
      right_inv := fun X => funext fun p => hinv σ.symm _
      map_add' := fun X Y => funext fun p => map_add _ _ _
      continuous_toFun := continuous_pi fun p => (Formalism.L2.Host.CT.continuous_adMap σ).comp (continuous_apply p)
      continuous_invFun := continuous_pi fun p => (Formalism.L2.Host.CT.continuous_adMap σ.symm).comp (continuous_apply p) }
  set ν := AutomorphicForm.unipMeasure K n r with hν
  haveI : ν.IsAddHaarMeasure := by rw [hν]; infer_instance
  haveI : (Measure.map s ν).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν s
  haveI : (Measure.map s.symm ν).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν s.symm
  obtain ⟨c, hc⟩ : ∃ c : NNReal, Measure.map s ν = c • ν := ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  have hq : Measure.QuasiMeasurePreserving s.symm ν ν :=
    ⟨s.symm.continuous.measurable.aemeasurable, by
      rw [Measure.isAddLeftInvariant_eq_smul (Measure.map s.symm ν) ν]
      exact Measure.smul_absolutelyContinuous⟩
  have hL : ∀ (τ : K ≃+* K) (X : AutomorphicForm.UPos n r → AdeleRing (𝓞 K) K), X ∈ AutomorphicForm.unipLattice K n r →
      (fun p => Formalism.L2.Host.CT.adMap τ (X p)) ∈ AutomorphicForm.unipLattice K n r := by
    rintro τ _ ⟨ξ, rfl⟩
    exact ⟨fun p => τ (ξ p), funext fun p => (a1 τ (ξ p)).symm⟩
  have hD := (AutomorphicForm.isAddFundamentalDomain_unipFundamentalDomain (K := K) (n := n) (r := r))
  have hD' : IsAddFundamentalDomain (AutomorphicForm.unipLattice K n r)
      (s.symm ⁻¹' AutomorphicForm.unipFundamentalDomain K n r) ν := by
    refine hD.preimage_of_equiv hq (e := fun g => ⟨s g, hL σ g g.2⟩) ⟨fun a b h => ?_, fun b => ?_⟩ fun g X => ?_
    · exact Subtype.ext (s.injective (congrArg Subtype.val h))
    · exact ⟨⟨s.symm b, hL σ.symm b b.2⟩, Subtype.ext (s.apply_symm_apply _)⟩
    · change s.symm (s g + X) = g + s.symm X
      rw [map_add (f := _), s.symm_apply_apply]
  have hu : ∀ X, e (unipOne (K := K) (n := n) r X) = unipOne (K := K) (n := n) r (s X) := by
    intro X
    refine Subtype.ext ?_
    rw [he]
    ext i j : 2
    change Formalism.L2.Host.CT.adMap σ (AutomorphicForm.unipMatrix X i j) = AutomorphicForm.unipMatrix (s X) i j
    simp only [AutomorphicForm.unipMatrix, Matrix.add_apply, AutomorphicForm.blockEntry_apply, Matrix.one_apply, map_add (f := _)]
    congr 1
    · split_ifs <;> simp
    · split_ifs
      · rfl
      · exact map_zero _
  have key : ∀ y, ctFun (K := K) (n := n) r (fun z => (φ : RightCosetSpace (Gam K n) → ℂ) (mk (Gam K n) (e (Quotient.out z)))) y =
      (c : ℝ) • constantTermL2 μ r φ (e y) := by
    intro y
    let F : (AutomorphicForm.UPos n r → AdeleRing (𝓞 K) K) → ℂ := fun X => φ (mk (Gam K n) (unipOne (K := K) (n := n) r X * e y))
    have e1 := setIntegral_map_equiv (μ := ν) s.toHomeomorph.toMeasurableEquiv F
      (s.symm ⁻¹' AutomorphicForm.unipFundamentalDomain K n r)
    have e2 : s.toHomeomorph.toMeasurableEquiv ⁻¹' (s.symm ⁻¹' AutomorphicForm.unipFundamentalDomain K n r) =
        AutomorphicForm.unipFundamentalDomain K n r := by
      ext X
      change s.symm (s X) ∈ AutomorphicForm.unipFundamentalDomain K n r ↔ _
      rw [s.symm_apply_apply]
    rw [e2] at e1
    change ∫ X in _, F X ∂Measure.map s ν = ∫ X in _, F (s X) ∂ν at e1
    rw [hc, Measure.restrict_smul, integral_smul_nnreal_measure] at e1
    have e3 : ∫ X in s.symm ⁻¹' AutomorphicForm.unipFundamentalDomain K n r, F X ∂ν =
        ∫ X in AutomorphicForm.unipFundamentalDomain K n r, F X ∂ν := by
      refine hD'.setIntegral_eq hD fun ξ X => ?_
      change φ (mk (Gam K n) (unipOne (K := K) (n := n) r (ξ + X) * e y)) = _
      rw [unipOne_add, mul_assoc, mk_mul_of_mem (unipOne_mem_rationalGLOne r ξ)]
    rw [e3] at e1
    simp only [ctFun, constantTermL2, h1, map_mul, hu]
    exact e1.symm
  have h4 : ∀ᵐ y ∂μ, constantTermL2 μ r φ (e y) = 0 := hp.quasiMeasurePreserving.ae ((hφ : IsCuspidalL2 μ φ) r hr hrn)
  filter_upwards [ae_ctFun_congr μ r hψ, h4] with y hy1 hy2
  rw [constantTermL2, hy1, key, hy2, smul_zero, Pi.zero_apply]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.GalEquiv
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

private theorem mapTrans (K : Type) [Field K] [NumberField K] (n : ℕ) (σ τ : K ≃+* K)
    (g : AdelicGLn.AdelicGL K n) :
    (Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap (σ.trans τ)) g : AdelicGLn.AdelicGL K n) =
      Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap τ)
        (Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap σ) g) := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  exact (UpperTheory.ConvolutionTheory.K.adBasic K).2.2 σ τ _

private theorem mapRefl (K : Type) [Field K] [NumberField K] (n : ℕ)
    (g : AdelicGLn.AdelicGL K n) :
    (Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap (RingEquiv.refl K)) g : AdelicGLn.AdelicGL K n) = g := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  exact (UpperTheory.ConvolutionTheory.K.adBasic K).2.1 _

private noncomputable def resMap (K : Type) [Field K] [NumberField K] (n : ℕ) (σ : K ≃+* K) (g : G1 K n) :
    G1 K n :=
  ⟨Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap σ) (g : AdelicGLn.AdelicGL K n),
    (UpperTheory.ConvolutionTheory.K.adNormOne K n σ g).1.2 g.2⟩

private theorem resMap_trans (K : Type) [Field K] [NumberField K] (n : ℕ) (σ τ : K ≃+* K) (g : G1 K n) :
    resMap K n τ (resMap K n σ g) = resMap K n (σ.trans τ) g :=
  Subtype.ext (mapTrans K n σ τ g).symm

private theorem resMap_refl (K : Type) [Field K] [NumberField K] (n : ℕ) (g : G1 K n) :
    resMap K n (RingEquiv.refl K) g = g :=
  Subtype.ext (mapRefl K n g)

private theorem resMap_cont (K : Type) [Field K] [NumberField K] (n : ℕ) (σ : K ≃+* K) :
    Continuous (resMap K n σ) := by
  apply Continuous.subtype_mk _ _
  exact (show Continuous (Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap σ) :
      AdelicGLn.AdelicGL K n → AdelicGLn.AdelicGL K n) from
    (continuous_id.matrix_map (Formalism.L2.Host.CT.continuous_adMap σ)).units_map _).comp
      continuous_subtype_val

private theorem resMap_iter (K : Type) [Field K] [NumberField K] (n : ℕ) (σ : K ≃+* K) (m : ℕ) (g : G1 K n) :
    (resMap K n σ)^[m] g = resMap K n (σ ^ m) g := by
  induction m with
  | zero => exact (resMap_refl K n g).symm
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, resMap_trans, pow_succ']
    rfl

theorem UpperTheory.ConvolutionTheory.K.galEquiv :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (σ : K ≃+* K), ∃ e : G1 K n ≃ₜ* G1 K n,
      (∀ g : G1 K n, ((e g : G1 K n) : AdelicGLn.AdelicGL K n) =
        Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap σ) (g : AdelicGLn.AdelicGL K n)) ∧
      (∀ g : G1 K n, ((e.symm g : G1 K n) : AdelicGLn.AdelicGL K n) =
        Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap σ.symm) (g : AdelicGLn.AdelicGL K n)) ∧
      (∀ g, e g ∈ Gam K n ↔ g ∈ Gam K n) ∧ ∃ m : ℕ, 0 < m ∧ ∀ g, (⇑e)^[m] g = g := by
  intro K _ _ n σ
  obtain ⟨m, hm, hσ⟩ := UpperTheory.ConvolutionTheory.K.autOrder K σ
  refine ⟨{ toFun := resMap K n σ
            invFun := resMap K n σ.symm
            left_inv := fun g => by rw [resMap_trans, RingEquiv.self_trans_symm, resMap_refl]
            right_inv := fun g => by rw [resMap_trans, RingEquiv.symm_trans_self, resMap_refl]
            map_mul' := fun g h => Subtype.ext (map_mul (Matrix.GeneralLinearGroup.map (Formalism.L2.Host.CT.adMap σ))
              (g : AdelicGLn.AdelicGL K n) (h : AdelicGLn.AdelicGL K n))
            continuous_toFun := resMap_cont K n σ
            continuous_invFun := resMap_cont K n σ.symm },
    fun _ => rfl, fun _ => rfl, fun g => ?_, m, hm, fun g => ?_⟩
  · exact (UpperTheory.ConvolutionTheory.K.adNormOne K n σ g).2
  · change (resMap K n σ)^[m] g = g
    rw [resMap_iter, hσ]
    exact resMap_refl K n g
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KvCont
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

section

open Filter Topology Set
open scoped ENNReal Pointwise

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsMulLeftInvariant]
  [IsFiniteMeasureOnCompacts μ]

private theorem continuous_rightConvolutionCLM (f : CompactlySupportedContinuousMap G ℂ) :
    Continuous (rconvCLM Γ μ f) := by
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨V, hVc, hV⟩ := exists_compact_mem_nhds x₀
  have hx₀ : x₀ ∈ V := mem_of_mem_nhds hV
  have hS : IsCompact (V * tsupport (f : G → ℂ)) := hVc.mul f.hasCompactSupport
  obtain ⟨N, hN⟩ := exists_encard_le_of_isCompact Γ hS
  obtain ⟨M, hM⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  have hzero : ∀ x ∈ V, ∀ y ∉ V * tsupport (f : G → ℂ), f (x⁻¹ * y) = 0 := fun x hx y hy => by
    have : x⁻¹ * y ∉ tsupport (f : G → ℂ) := fun h => hy ⟨x, hx, x⁻¹ * y, h, by simp⟩
    exact image_eq_zero_of_notMem_tsupport this
  have hcont : ∀ x : G, Continuous fun y => f (x⁻¹ * y) := fun x =>
    f.continuous.comp (continuous_const_mul x⁻¹)
  let A : G → ℝ≥0∞ := fun x => ∫⁻ y, ‖f (x⁻¹ * y) - f (x₀⁻¹ * y)‖ₑ ^ 2 ∂μ
  have hA : Tendsto A (𝓝 x₀) (𝓝 0) := by
    have h0 : (0 : ℝ≥0∞) = ∫⁻ _, 0 ∂μ := by simp
    rw [h0]
    refine tendsto_lintegral_filter_of_dominated_convergence
      ((V * tsupport (f : G → ℂ)).indicator fun _ => ENNReal.ofReal (M + M) ^ 2) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun x =>
        ((hcont x).sub (hcont x₀)).measurable.enorm.pow_const 2
    · filter_upwards [hV] with x hx
      refine Eventually.of_forall fun y => ?_
      by_cases hy : y ∈ V * tsupport (f : G → ℂ)
      · rw [indicator_of_mem hy]
        gcongr
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal ((norm_sub_le _ _).trans (add_le_add (hM _) (hM _)))
      · simp [hzero x hx y hy, hzero x₀ hx₀ y hy]
    · rw [lintegral_indicator hS.measurableSet, lintegral_const]
      exact (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
        (by rw [Measure.restrict_apply_univ]; exact hS.measure_lt_top)).ne
    · refine Eventually.of_forall fun y => ?_
      have hc : Continuous fun x : G => ‖f (x⁻¹ * y) - f (x₀⁻¹ * y)‖ₑ ^ 2 :=
        (ENNReal.continuous_pow 2).comp
          ((f.continuous.comp (continuous_inv.mul continuous_const)).sub continuous_const).enorm
      simpa using hc.tendsto x₀
  have hkey : ∀ x ∈ V, ∀ φ : Lp ℂ 2 (quotientMeasure Γ μ),
      ‖rconv Γ μ f φ x - rconv Γ μ f φ x₀‖ₑ ^ 2 ≤ (A x * N) * ‖φ‖ₑ ^ 2 := by
    intro x hx φ
    have hsub : rconv Γ μ f φ x - rconv Γ μ f φ x₀ =
        ∫ y, (f (x⁻¹ * y) - f (x₀⁻¹ * y)) * φ (mk Γ y) ∂μ := by
      unfold rconv
      rw [← integral_sub (integrable_rconv Γ μ f φ x) (integrable_rconv Γ μ f φ x₀)]
      simp only [sub_mul]
    have hm1 : AEMeasurable (fun y => ‖f (x⁻¹ * y) - f (x₀⁻¹ * y)‖ₑ) μ :=
      ((hcont x).sub (hcont x₀)).measurable.enorm.aemeasurable
    have hm2 : AEMeasurable
        ((V * tsupport (f : G → ℂ)).indicator fun y => ‖φ (mk Γ y)‖ₑ) μ :=
      ((stronglyMeasurable_lift Γ μ φ).measurable.enorm.indicator hS.measurableSet).aemeasurable
    calc ‖rconv Γ μ f φ x - rconv Γ μ f φ x₀‖ₑ ^ 2
        ≤ (∫⁻ y, ‖f (x⁻¹ * y) - f (x₀⁻¹ * y)‖ₑ *
            (V * tsupport (f : G → ℂ)).indicator (fun y => ‖φ (mk Γ y)‖ₑ) y ∂μ) ^ 2 := by
          rw [hsub]
          gcongr
          refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
          congr 1
          ext y
          by_cases hy : y ∈ V * tsupport (f : G → ℂ)
          · rw [indicator_of_mem hy, enorm_mul]
          · rw [indicator_of_notMem hy, hzero x hx y hy, hzero x₀ hx₀ y hy]
            simp
      _ ≤ A x * ∫⁻ y, (V * tsupport (f : G → ℂ)).indicator
            (fun y => ‖φ (mk Γ y)‖ₑ) y ^ 2 ∂μ :=
          L2Kernel.lintegral_mul_sq_le μ hm1 hm2
      _ = A x * ∫⁻ y in V * tsupport (f : G → ℂ), ‖φ (mk Γ y)‖ₑ ^ 2 ∂μ := by
          congr 1
          rw [← lintegral_indicator hS.measurableSet]
          congr 1
          ext y
          by_cases hy : y ∈ V * tsupport (f : G → ℂ)
          · simp [hy]
          · simp [hy]
      _ ≤ A x * (N * ‖φ‖ₑ ^ 2) := by
          gcongr
          exact lintegral_lift_sq_le Γ μ φ hS.measurableSet hN
      _ = (A x * N) * ‖φ‖ₑ ^ 2 := by rw [mul_assoc]
  have hAN : Tendsto (fun x => A x * N) (𝓝 x₀) (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const hA (Or.inr (ENNReal.natCast_ne_top N))
  have hlim : Tendsto (fun x => √(A x * N).toReal) (𝓝 x₀) (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto _).comp
      ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hAN)
    rw [ENNReal.toReal_zero, Real.sqrt_zero] at this
    exact this
  have hfin : ∀ᶠ x in 𝓝 x₀, A x * N < 1 := hAN.eventually_lt_const zero_lt_one
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [hV, hfin] with x hx hxf
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun φ => ?_
  rw [ContinuousLinearMap.sub_apply, rconvCLM_apply, rconvCLM_apply]
  exact norm_le_of_enorm_sq_le (ne_top_of_lt hxf) (hkey x hx φ)

end

theorem UpperTheory.ConvolutionTheory.K.kvCont :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (f : CC K n),
      Continuous (kv μ f) := by
  intro K _ _ n μ _ f
  exact (InnerProductSpace.toDual ℂ (L2 μ)).symm.continuous.comp
    (continuous_rightConvolutionCLM (Gam K n) μ f)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.QhtBasic
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.Reduction
open IsDedekindDomain

namespace UpperTheory.ConvolutionTheory.K

private theorem continuous_locHeight {E : Type*} [NormedField E] {n : ℕ} :
    Continuous (locHeight : GL (Fin n) E → ℝ) := by
  unfold locHeight
  refine continuous_const.max (NNReal.continuous_coe.comp ?_)
  refine Continuous.finset_sup_apply fun p _ => ?_
  refine Continuous.max ?_ ?_
  · exact (continuous_GL_apply p.1 p.2).nnnorm
  · exact ((continuous_GL_apply p.1 p.2).comp continuous_inv).nnnorm

private theorem locHeight_mul_integral {K : Type} [Field K] [NumberField K] {n : ℕ}
    {v : HeightOneSpectrum (𝓞 K)} (x k : GL (Fin n) (v.adicCompletion K))
    (hk : k ∈ GLnLocal.integralGL (v.adicCompletion K) n) : locHeight (x * k) = locHeight x := by
  refine le_antisymm ?_ ?_
  · have h := locHeight_mul_le_of_ultrametric x k
    rwa [locHeight_eq_one_of_mem_integralGL hk, mul_one] at h
  · have h := locHeight_mul_le_of_ultrametric (x * k) k⁻¹
    rwa [locHeight_eq_one_of_mem_integralGL (inv_mem hk), mul_one, mul_inv_cancel_right] at h

private theorem finprod_mul_integral {K : Type} [Field K] [NumberField K] {n : ℕ}
    (g w : AdelicGLn.AdelicGL K n)
    (hw : (AdelicGLn.prodEquiv K n w).2 ∈ AdelicGLn.integralFiniteGL K n) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 K), locHeight (finAt v (g * w)) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), locHeight (finAt v g) := by
  rw [AdelicGLn.mem_integralFiniteGL_iff_forall] at hw
  refine finprod_congr fun v => ?_
  rw [finAt_mul]
  exact locHeight_mul_integral _ _ (hw v)

private theorem continuous_finprod {K : Type} [Field K] [NumberField K] {n : ℕ} :
    Continuous fun g : AdelicGLn.AdelicGL K n =>
      ∏ᶠ v : HeightOneSpectrum (𝓞 K), locHeight (finAt v g) := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun x => ?_)
  have hcF : Continuous fun g : AdelicGLn.AdelicGL K n => (AdelicGLn.prodEquiv K n g).2 :=
    continuous_snd.comp (AdelicGLn.prodEquiv K n).continuous
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' ((fun g => (AdelicGLn.prodEquiv K n g).2) ⁻¹'
      (AdelicGLn.integralFiniteGL K n : Set (AdelicGLn.FiniteAdelicGL K n))), ?_, ?_, ?_⟩
  · exact ((AdelicGLn.isOpen_integralFiniteGL K n).preimage hcF).preimage
      (continuous_const.mul continuous_id)
  · simp only [Set.mem_preimage, inv_mul_cancel, map_one, Prod.snd_one, SetLike.mem_coe]
    exact one_mem _
  · intro y hy
    have := finprod_mul_integral x (x⁻¹ * y) hy
    rwa [mul_inv_cancel_left] at this

private theorem continuous_height {K : Type} [Field K] [NumberField K] {n : ℕ} :
    Continuous (AutomorphicForm.height : AdelicGLn.AdelicGL K n → ℝ) := by
  unfold AutomorphicForm.height
  refine Continuous.mul ?_ continuous_finprod
  exact continuous_finsetProd _ fun w _ => (continuous_locHeight.comp (continuous_infAt w)).pow _

private theorem measurable_qht {K : Type} [Field K] [NumberField K] {n : ℕ} :
    Measurable (qht : G1 K n → ℝ) := by
  set_option synthInstance.maxHeartbeats 400000 in
  haveI : Countable (Gam K n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  unfold qht
  refine Measurable.iInf fun γ => Continuous.measurable ?_
  exact continuous_height.comp (continuous_subtype_val.comp (continuous_const.mul continuous_id))

private theorem qht_mul_left {K : Type} [Field K] [NumberField K] {n : ℕ} (γ : G1 K n)
    (hγ : γ ∈ Gam K n) (x : G1 K n) : qht (γ * x) = qht x := by
  unfold qht
  have h := (Equiv.mulRight (⟨γ, hγ⟩ : Gam K n)).iInf_comp
    (g := fun δ : Gam K n => AutomorphicForm.height (((δ : G1 K n) * x : G1 K n) : AdelicGLn.AdelicGL K n))
  rw [← h]
  refine congrArg _ (funext fun δ => ?_)
  simp only [Equiv.coe_mulRight, Subgroup.coe_mul, mul_assoc]

end UpperTheory.ConvolutionTheory.K

theorem UpperTheory.ConvolutionTheory.K.qhtBasic :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), (∀ x : G1 K n, 1 ≤ qht x) ∧ (∀ γ ∈ Gam K n, ∀ x : G1 K n, qht (γ * x) = qht x) ∧
      Measurable fun y : RightCosetSpace (Gam K n) => qht (Quotient.out y : G1 K n) := by
  intro K _ _ n
  refine ⟨fun x => le_ciInf fun _ => one_le_height _, qht_mul_left, ?_⟩
  rw [measurable_from_quotient]
  have h : ((fun y : RightCosetSpace (Gam K n) => qht (Quotient.out y : G1 K n)) ∘ Quotient.mk'') =
      (qht : G1 K n → ℝ) := by
    funext x
    obtain ⟨γ, hγ⟩ := mk_eq_mk_iff.1 (Quotient.out_eq (mk (Gam K n) x))
    change qht (Quotient.out (mk (Gam K n) x)) = qht x
    rw [← hγ]
    exact qht_mul_left _ γ.2 x
  rw [h]
  exact measurable_qht
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.QhtTw
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

theorem UpperTheory.ConvolutionTheory.K.qhtTw :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (θ : Twist μ),
      ∃ C : ℝ, ∃ c : ℕ, 0 ≤ C ∧ ∀ x : G1 K n, qht (θ.e x) ≤ C * qht x ^ c := by
  intro K _ _ n μ _ θ
  obtain ⟨C, c, h⟩ := θ.height_le
  have hb : ∀ x : G1 K n, BddBelow (Set.range fun γ : Gam K n =>
      AutomorphicForm.height (((γ : G1 K n) * x : G1 K n) : AdelicGLn.AdelicGL K n)) :=
    fun x => ⟨1, by rintro _ ⟨γ, rfl⟩; exact AutomorphicForm.one_le_height _⟩
  refine ⟨max C 0, c, le_max_right _ _, fun x => ?_⟩
  have hmono : Monotone fun t : ℝ => max C 0 * (max t 0) ^ c := fun a b hab =>
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_max_right _ _) (max_le_max hab le_rfl) c) (le_max_right _ _)
  have hcont : Continuous fun t : ℝ => max C 0 * (max t 0) ^ c := by fun_prop
  have h1 : 0 ≤ qht x := le_ciInf fun γ => (AutomorphicForm.height_pos _).le
  have := hmono.map_ciInf_of_continuousAt (hcont.continuousAt) (hb x)
  change max C 0 * (max (qht x) 0) ^ c = _ at this
  rw [max_eq_left h1] at this
  rw [this]
  refine le_ciInf fun γ => ?_
  refine (ciInf_le (hb (θ.e x)) ⟨θ.e γ, (θ.mem_gam _).2 γ.2⟩).trans ?_
  change AutomorphicForm.height ((θ.e γ * θ.e x : G1 K n) : AdelicGLn.AdelicGL K n) ≤ max C 0 * (max (AutomorphicForm.height (((γ : G1 K n) * x : G1 K n) : AdelicGLn.AdelicGL K n)) 0) ^ c
  rw [← map_mul, max_eq_left (AutomorphicForm.height_pos _).le]
  refine (h _).trans ?_
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (AutomorphicForm.height_pos _).le _)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.RopAdj
section
open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalProjection PositivityTheory.Rg.Tf.Core UpperTheory.ConvolutionTheory.K
open scoped InnerProductSpace

theorem UpperTheory.ConvolutionTheory.K.ropAdj :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (G1 K n)) [μ.IsHaarMeasure] (f : CC K n),
      ContinuousLinearMap.adjoint (Rop μ f) = Rop μ (ccStar f) := by
  intro K _ _ n μ _ f
  have := isInvInvariant_of_isMulRightInvariant μ
  exact ((rightRegularRep (Gam K n) μ).adjoint_integrated μ (UnitaryRep.ccToL1 μ f)).trans
      (congrArg _ (ccToL1_ccStar (μ := μ) f).symm)
end

