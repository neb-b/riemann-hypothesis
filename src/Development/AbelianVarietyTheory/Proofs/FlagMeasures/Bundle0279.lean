module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HaarMeasureGramGL2ActionTensor
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.HermitianLattices.FinalNeighbourConstruct
public import Formalism.HermitianLattices.HermitianLatticesProofs.ClassSetAssembly
public import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovolBound
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0273

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerivativesCoefficientsConvolutionFixedVector
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff Topology Pointwise

namespace GlobalTheory.DerivConv

theorem exists_weak_deriv {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (c : ℝ → H) (hc : ∀ u, DifferentiableAt ℝ (fun t => ⟪u, c t⟫_ℂ) 0) :
    ∃ v : H, ∀ u, deriv (fun t => ⟪u, c t⟫_ℂ) 0 = ⟪u, v⟫_ℂ := by
  have h : Filter.Tendsto (fun (t : ℝ) (u : H) => innerSL ℂ (slope c 0 t) u) (𝓝[≠] 0)
      (𝓝 fun u => (starRingEnd ℂ) (deriv (fun t => ⟪u, c t⟫_ℂ) 0)) := by
    refine tendsto_pi_nhds.2 fun u => ?_
    have h1 := (Complex.continuous_conj.tendsto _).comp (hc u).hasDerivAt.tendsto_slope
    refine h1.congr fun t => ?_
    simp only [Function.comp, innerSL_apply_apply]
    rw [← inner_conj_symm (slope c 0 t) u]
    congr 1
    simp only [slope_def_module, inner_sub_right, ← Complex.coe_smul, inner_smul_right, smul_eq_mul]
  let L : H →L[ℂ] ℂ := continuousLinearMapOfTendsto (fun t : ℝ => innerSL ℂ (slope c 0 t)) h
  refine ⟨(InnerProductSpace.toDual ℂ H).symm L, fun u => ?_⟩
  rw [← inner_conj_symm, InnerProductSpace.toDual_symm_apply]
  exact (Complex.conj_conj _).symm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool}

theorem differentiableAt_curve {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    DifferentiableAt ℝ (fun t : ℝ => f (NormedSpace.exp ((t : ℂ) • X))) 0 := by
  have h1 : inUJ ε (1 : Matrix (Fin n) (Fin n) ℂ) := by simp [inUJ]
  obtain ⟨U, F, hU, hg, hF, hfF⟩ := hf 1 h1
  have hγ := hasDerivAt_mul_exp_smul_zero 1 X
  simp only [Matrix.one_mul] at hγ
  have hγ0 : NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1 := by simp [NormedSpace.exp_zero]
  have hFd : DifferentiableAt ℝ F 1 :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hg)
  have hcomp := hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  refine hcomp.differentiableAt.congr_of_eventuallyEq ?_
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, NormedSpace.exp ((t : ℂ) • X) ∈ U :=
    hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hg)
  filter_upwards [hmem] with t ht
  exact hfF _ ht (exp_indefinite_unitary_holds n ε X hX t)

theorem smooth_congr {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : SmoothOnG ε f)
    (h : ∀ g, inUJ ε g → f g = f' g) : SmoothOnG ε f' := by
  intro g hg
  obtain ⟨U, F, hU, hgU, hF, e⟩ := hf g hg
  exact ⟨U, F, hU, hgU, hF, fun x hx hxJ => (h x hxJ).symm.trans (e x hx hxJ)⟩

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem exists_Rd (hσ : IsURepOn (UJset ε) σ) {s : H} (hs : ∀ u, SmoothOnG ε (fun g => ⟪u, σ g s⟫_ℂ))
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : inG ε X) :
    ∃ v : H, ∀ u, ∀ g, inUJ ε g → Rd X (fun x => ⟪u, σ x s⟫_ℂ) g = ⟪u, σ g v⟫_ℂ := by
  obtain ⟨v, hv⟩ := exists_weak_deriv (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) s)
    fun u => differentiableAt_curve (hs u) hX
  refine ⟨v, fun u g hg => ?_⟩
  rw [← ContinuousLinearMap.adjoint_inner_left, ← hv]
  unfold Rd
  congr 1
  funext t
  beta_reduce
  rw [hσ.1.2 g hg _ (exp_indefinite_unitary_holds n ε X hX t), ContinuousLinearMap.adjoint_inner_left]
  rfl

theorem exists_Eword (hσ : IsURepOn (UJset ε) σ) {s : H} (hs : ∀ u, SmoothOnG ε (fun g => ⟪u, σ g s⟫_ℂ))
    (w : List (Fin n × Fin n)) :
    ∃ s' : H, (∀ u, SmoothOnG ε (fun g => ⟪u, σ g s'⟫_ℂ)) ∧
      ∀ u, ∀ g, inUJ ε g → Eword ε w (fun x => ⟪u, σ x s⟫_ℂ) g = ⟪u, σ g s'⟫_ℂ := by
  induction w with
  | nil => exact ⟨s, hs, fun _ _ _ => rfl⟩
  | cons p w ih =>
    obtain ⟨s', hs', e⟩ := ih
    have hc := complex_parts_mem_lie_algebra_holds n ε (Matrix.single p.1 p.2 1)
    obtain ⟨v₁, h₁⟩ := exists_Rd hσ hs' hc.1
    obtain ⟨v₂, h₂⟩ := exists_Rd hσ hs' hc.2.1
    refine ⟨v₁ + Complex.I • v₂, fun u g hg => ?_, fun u g hg => ?_⟩
    · obtain ⟨U, F, hU, hgU, hF, e⟩ := smooth_congr (rdSmooth_of right_derivative_extends n ε _ _ (hs' u) hc.1) (h₁ u) g hg
      obtain ⟨U', F', hU', hgU', hF', e'⟩ :=
        smooth_congr (rdSmooth_of right_derivative_extends n ε _ _ (hs' u) hc.2.1) (h₂ u) g hg
      refine ⟨U ∩ U', fun h => F h + Complex.I * F' h, hU.inter hU', ⟨hgU, hgU'⟩,
        (hF.mono Set.inter_subset_left).add (contDiffOn_const.mul (hF'.mono Set.inter_subset_right)), ?_⟩
      intro x hx hxJ
      simp only [← e x hx.1 hxJ, ← e' x hx.2 hxJ, map_add (f := _), map_smul, inner_add_right, inner_smul_right]
    · refine (Eword_congr ε (e u) [p] g hg).trans ?_
      simp only [Eword, Eab, Ec, id, h₁ u g hg, h₂ u g hg, map_add (f := _), map_smul, inner_add_right, inner_smul_right]

theorem smooth_coef (hσ : IsURepOn (UJset ε) σ) {α : Matrix (Fin n) (Fin n) ℂ → ℂ} {s : H}
    (hα : SmoothOnG ε α) (hαc : HasCompactSupport (fun g : UJ ε => α (umat g)))
    (hfix : ∀ u : H, ∫ g : UJ ε, α (umat g) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε) = ⟪u, s⟫_ℂ) (u : H) :
    SmoothOnG ε (fun g => ⟪u, σ g s⟫_ℂ) := by
  obtain ⟨⟨h1, hmul⟩, -, hcont⟩ := hσ
  obtain ⟨hemb, hrange⟩ := isClosedEmbeddingMatrix n ε
  obtain ⟨F, hF, hFα⟩ := GlobalTheory.smoothOnG_exists_contDiff_extension n ε α hα
  have hmem : ∀ g : UJ ε, inUJ ε (umat g) := fun g => g.2
  have hu : Continuous fun g : UJ ε => umat g := hemb.continuous
  have hb : Continuous fun g : UJ ε => ⟪u, σ (umat g) s⟫_ℂ :=
    continuous_const.inner ((hcont s).comp_continuous hu hmem)
  have hlift : ∀ x, inUJ ε x → ∃ z : UJ ε, umat z = x := fun x hx => by
    have : x ∈ Set.range (fun g : UJ ε => umat g) := by
      rw [show Set.range (fun g : UJ ε => umat g) = _ from hrange]; exact hx
    exact this
  have hinv : ∀ z : UJ ε, Jm ε * (umat z)ᴴ * Jm ε = umat z⁻¹ := fun z => by
    have h : (umat z)ᴴ * Jm ε * umat z = Jm ε := hmem z
    have i2 : umat z * umat z⁻¹ = 1 := Units.mul_inv _
    calc Jm ε * (umat z)ᴴ * Jm ε = Jm ε * (umat z)ᴴ * Jm ε * (umat z * umat z⁻¹) := by rw [i2, Matrix.mul_one]
      _ = Jm ε * ((umat z)ᴴ * Jm ε * umat z) * umat z⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h, Jm_mul_self, Matrix.one_mul]
  have hform : ∀ z : UJ ε, ⟪u, σ (umat z) s⟫_ℂ
      = ∫ g : UJ ε, α (umat (z⁻¹ * g)) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε) := by
    intro z
    rw [← ContinuousLinearMap.adjoint_inner_left, ← hfix,
      ← integral_mul_left_eq_self (fun g : UJ ε => α (umat (z⁻¹ * g)) * ⟪u, σ (umat g) s⟫_ℂ) z]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    have e : umat (z * g) = umat z * umat g := rfl
    simp only [inv_mul_cancel_left, e]
    rw [hmul _ (hmem z) _ (hmem g), ContinuousLinearMap.adjoint_inner_left]
    rfl
  intro g₀ hg₀
  have hC : IsCompact ((fun g : UJ ε => umat g) ⁻¹' Metric.closedBall g₀ 1) :=
    hemb.isCompact_preimage (isCompact_closedBall g₀ 1)
  have hK := hC.mul hαc
  set K := ((fun g : UJ ε => umat g) ⁻¹' Metric.closedBall g₀ 1) * tsupport (fun g : UJ ε => α (umat g))
  have hΨ : ContDiff ℝ ∞ fun z : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × ℂ) =>
      F (fun i j => (Jm ε * z.1ᴴ * Jm ε * z.2.1) i j) * z.2.2 := by
    refine ContDiff.mul (hF.comp ?_) (contDiff_snd.comp contDiff_snd)
    refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
    have e1 : ∀ a b, ContDiff ℝ ∞ fun z : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × ℂ) =>
        star (z.1 a b) := fun a b =>
      Complex.conjCLE.contDiff.comp ((contDiff_apply_apply (𝕜 := ℝ) a b).comp contDiff_fst)
    have e2 : ∀ a b, ContDiff ℝ ∞ fun z : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × ℂ) =>
        z.2.1 a b := fun a b =>
      (contDiff_apply_apply (𝕜 := ℝ) a b).comp (contDiff_fst.comp contDiff_snd)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact ContDiff.sum fun a _ => (ContDiff.sum fun b _ => (ContDiff.sum fun c _ =>
      contDiff_const.mul (e1 _ _)).mul contDiff_const).mul (e2 _ _)
  refine ⟨Metric.ball g₀ 1, fun x => ∫ g in K, F (fun i j => (Jm ε * xᴴ * Jm ε * umat g) i j) *
    ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε), Metric.isOpen_ball, Metric.mem_ball_self one_pos, ?_, ?_⟩
  · exact (contDiff_infty.2 fun m =>
      GlobalTheory.GardingVec.contDiff_setIntegral_nat (muG ε) hK (hu.prodMk hb) m _ hΨ).contDiffOn
  · intro x hx hxJ
    obtain ⟨z, rfl⟩ := hlift x hxJ
    have e : ∀ g : UJ ε, F (fun i j => (Jm ε * (umat z)ᴴ * Jm ε * umat g) i j) = α (umat (z⁻¹ * g)) := fun g => by
      rw [hinv]; exact hFα _ (hmem (z⁻¹ * g))
    simp only [e]
    rw [hform z]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun g hg => ?_).symm
    by_contra hne
    exact hg ⟨z, Metric.ball_subset_closedBall hx, z⁻¹ * g,
      subset_tsupport _ fun h => hne (by rw [show α (umat (z⁻¹ * g)) = 0 from h, zero_mul]),
      mul_inv_cancel_left z g⟩

theorem derivConv : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (s : H), IsURepOn (UJset ε) σ → SmoothOnG ε α → HasCompactSupport (fun g : UJ ε => α (umat g)) → (∀ u : H, ∫ g : UJ ε, α (umat g) * ⟪u, σ (umat g) s⟫_ℂ ∂(muG ε) = ⟪u, s⟫_ℂ) → (∀ u, SmoothOnG ε (fun g => ⟪u, σ g s⟫_ℂ)) ∧ ∀ w : List (Fin n × Fin n), ∃ s' : H, ∀ u, ∀ g ∈ UJset ε, Eword ε w (fun x => ⟪u, σ x s⟫_ℂ) g = ⟪u, σ g s'⟫_ℂ := by
  intro n ε H _ _ _ σ α s hσ hα hαc hfix
  have hs := smooth_coef hσ hα hαc hfix
  refine ⟨hs, fun w => ?_⟩
  obtain ⟨s', -, h⟩ := exists_Eword hσ hs w
  exact ⟨s', h⟩

end GlobalTheory.DerivConv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddConjEqOneOfFormallyUnramified
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors Classical in
private theorem algebraMap_trace_eq_add_of_ne_id {F E : Type} [Field F] [Field E] [Algebra F E]
    [Algebra.IsSeparable F E] (h2 : Module.finrank F E = 2) (σ : E →ₐ[F] E)
    (hσ : σ ≠ AlgHom.id F E) (x : E) :
    algebraMap F E (Algebra.trace F E x) = x + σ x := by
  classical
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  let τ : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  have hτ : τ ≠ 1 := by
    intro h
    apply hσ
    ext y
    have := congrArg (fun f : E ≃ₐ[F] E => f y) h
    simpa [τ] using this
  have huniv : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, τ} := by
    symm
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, h2,
      Finset.card_pair (Ne.symm hτ)]
  rw [trace_eq_sum_automorphisms, huniv, Finset.sum_pair (Ne.symm hτ)]
  simp [τ]

open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors Classical in
private theorem ne_id_of_embedding_conj {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E]
    (hE : IsTotallyComplex E) (σ : E →ₐ[F] E)
    (hσ : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) :
    σ ≠ AlgHom.id F E := by
  intro h
  obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
  have hc := hE.isComplex w
  rw [InfinitePlace.isComplex_iff] at hc
  apply hc
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have := hσ w.embedding x
  rw [h] at this
  simpa [ComplexEmbedding.conjugate_coe_eq] using this.symm


open NumberField IsDedekindDomain MeasureTheory Matrix in
open scoped TensorProduct ENNReal nonZeroDivisors Classical in
theorem _root_.GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (σ : E →ₐ[F] E), _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) →
      ∃ θ : 𝓞 E, (θ : E) + σ θ = 1 := by
  intro F E _ _ _ _ _ σ hCM hU
  obtain ⟨-, hE, h2, hσ⟩ := hCM
  have hD := (_root_.GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top F E).1 hU
  have hdual : FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) = 1 := by
    have := coeIdeal_differentIdeal (𝓞 F) F E (𝓞 E)
    rw [hD, FractionalIdeal.coeIdeal_top] at this
    exact inv_eq_one.mp this.symm
  have key : ∀ a : F, (∀ b : 𝓞 E, a * Algebra.trace F E (algebraMap (𝓞 E) E b) ∈ (algebraMap (𝓞 F) F).range) →
      a ∈ (algebraMap (𝓞 F) F).range := by
    intro a ha
    have hmem : algebraMap F E a ∈ FractionalIdeal.dual (𝓞 F) F (1 : FractionalIdeal (𝓞 E)⁰ E) := by
      rw [FractionalIdeal.mem_dual (fun h => by
        simpa using congrArg (fun J : FractionalIdeal (𝓞 E)⁰ E => (1 : E) ∈ J) h)]
      intro y hy
      obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hy
      rw [Algebra.traceForm_apply, ← Algebra.smul_def, LinearMap.map_smul, smul_eq_mul]
      exact ha b
    rw [hdual] at hmem
    obtain ⟨b, hb⟩ := (FractionalIdeal.mem_one_iff _).1 hmem
    have hint : IsIntegral ℤ (algebraMap F E a) := by
      rw [← hb]
      exact b.isIntegral_coe
    have hint' : IsIntegral ℤ a :=
      (isIntegral_algebraMap_iff ).1 hint
    exact ⟨⟨a, hint'⟩, rfl⟩
  set I : Ideal (𝓞 F) := LinearMap.range (Algebra.intTrace (𝓞 F) (𝓞 E)) with hI
  have hItop : I = ⊤ := by
    by_contra hne
    obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal I hne
    have hp0 : p ≠ ⊥ := (Ideal.bot_lt_of_maximal p (RingOfIntegers.not_isField F)).ne'
    obtain ⟨x, hx, hx1⟩ := FractionalIdeal.exists_notMem_one_of_ne_bot (K := F) hp0 hp.ne_top
    apply hx1
    obtain ⟨r, hr⟩ := key x (by
      intro b
      have ht : Algebra.intTrace (𝓞 F) (𝓞 E) b ∈ p := hIp ⟨b, rfl⟩
      have hmem := (FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.mpr hp0)).1 hx
        _ (FractionalIdeal.mem_coeIdeal_of_mem (𝓞 F)⁰ ht)
      obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 hmem
      refine ⟨r, ?_⟩
      rw [hr, Algebra.algebraMap_intTrace (K := F) (L := E)])
    rw [← hr]
    exact (FractionalIdeal.mem_one_iff _).2 ⟨r, rfl⟩
  have h1 : (1 : 𝓞 F) ∈ I := hItop ▸ Submodule.mem_top
  obtain ⟨θ, hθ⟩ := h1
  refine ⟨θ, ?_⟩
  rw [← algebraMap_trace_eq_add_of_ne_id h2 σ (ne_id_of_embedding_conj hE σ hσ)]
  have := Algebra.algebraMap_intTrace (A := 𝓞 F) (K := F) (L := E) (B := 𝓞 E) θ
  rw [hθ, map_one] at this
  rw [← this]
  exact map_one _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometryExtendOrthogonalByIdentity
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OrthExt

theorem hT_orth_right {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E)
    (U : Submodule E S.V) {u v : S.V} (hu : u ∈ U) (hv : v ∈ orth S U) : S.hT u v = 0 := by
  have := hv
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at this
  exact this u hu

theorem hT_orth_left {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E)
    (U : Submodule E S.V) {u v : S.V} (hu : u ∈ U) (hv : v ∈ orth S U) : S.hT v u = 0 := by
  have h1 := S.herm.eq u v
  rw [hT_orth_right S U hu hv] at h1
  simpa using h1.symm

theorem extend_isom : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (U : Submodule E S.V), IsCompl U (orth S U) → ∀ g : ↥(orth S U) ≃ₗ[E] ↥(orth S U), (∀ x y : ↥(orth S U), S.hT (g x : S.V) (g y : S.V) = S.hT (x : S.V) (y : S.V)) → ∃ γ : S.V ≃ₗ[E] S.V, γ ∈ Formalism.HermitianLatticesTheory.isom S.hT ∧ (∀ u ∈ U, γ u = u) ∧ ∀ w : ↥(orth S U), γ (w : S.V) = (g w : S.V) := by
  intro E _ _ _ S U hc g hg
  let e := Submodule.prodEquivOfIsCompl U (orth S U) hc
  let γ : S.V ≃ₗ[E] S.V := (e.symm.trans ((LinearEquiv.refl E U).prodCongr g)).trans e
  have hγ : ∀ x, γ x = ((e.symm x).1 : S.V) + (g (e.symm x).2 : S.V) := fun x => rfl
  have hx : ∀ x, x = ((e.symm x).1 : S.V) + ((e.symm x).2 : S.V) := fun x => by
    conv_lhs => rw [← e.apply_symm_apply x]
    rfl
  have key : ∀ (a b : U) (c d : ↥(orth S U)),
      S.hT ((a : S.V) + (c : S.V)) ((b : S.V) + (d : S.V)) = S.hT a b + S.hT c d := by
    intro a b c d
    simp only [map_add (f := _), LinearMap.add_apply]
    rw [GlobalTheory.OrthExt.hT_orth_right S U a.2 d.2, GlobalTheory.OrthExt.hT_orth_left S U b.2 c.2]
    ring
  refine ⟨γ, ?_, ?_, ?_⟩
  · intro x y
    change S.hT (γ x) (γ y) = S.hT x y
    rw [hγ, hγ, key, hg, ← key, ← hx, ← hx]
  · intro u hu
    rw [hγ]
    have : e.symm u = (⟨u, hu⟩, 0) := Submodule.prodEquivOfIsCompl_symm_apply_left U (orth S U) hc ⟨u, hu⟩
    rw [this]; simp
  · intro w
    rw [hγ]
    have : e.symm w = (0, w) := Submodule.prodEquivOfIsCompl_symm_apply_right U (orth S U) hc w
    rw [this]; simp

end GlobalTheory.OrthExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNatSmulMemOfMemSpan
section
open NumberField

namespace GlobalTheory.NatSmulMemOfSpan

theorem exists_nat_mul_eq_coe {K : Type*} [Field K] [NumberField K] (c : K) :
    ∃ m : ℕ, 0 < m ∧ ∃ a : 𝓞 K, algebraMap (𝓞 K) K a = (m : K) * c := by
  have halg : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨y, hy, hint⟩ := halg.exists_integral_multiple
  have hint' : IsIntegral ℤ ((y.natAbs : K) * c) := by
    have hc : (y.natAbs : K) = ((y.natAbs : ℤ) : K) := (Int.cast_natCast _).symm
    rw [zsmul_eq_mul] at hint
    rcases Int.natAbs_eq y with h | h
    · rw [hc, ← h]; exact hint
    · have h2 : ((y.natAbs : ℤ) : K) = -(y : K) := by
        have : (y.natAbs : ℤ) = -y := by omega
        rw [this, Int.cast_neg]
      rw [hc, h2, neg_mul]; exact hint.neg
  exact ⟨y.natAbs, Int.natAbs_pos.2 hy, ⟨_, hint'⟩, rfl⟩

theorem exists_nat_smul_mem_of_mem_span {K V : Type*} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (Λ : Submodule (𝓞 K) V) {v : V}
    (hv : v ∈ Submodule.span K (Λ : Set V)) : ∃ n : ℕ, 0 < n ∧ (n : K) • v ∈ Λ := by
  have key : ∀ (a : 𝓞 K) (w : V), w ∈ Λ → algebraMap (𝓞 K) K a • w ∈ Λ := fun a w hw => by
    rw [algebraMap_smul]; exact Λ.smul_mem a hw
  have keyN : ∀ (m : ℕ) (w : V), w ∈ Λ → (m : K) • w ∈ Λ := fun m w hw => by
    simpa using key (m : 𝓞 K) w hw
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨m, hm, hx⟩ := hx
    obtain ⟨n, hn, hy⟩ := hy
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    have : ((m * n : ℕ) : K) • (x + y) = (n : K) • ((m : K) • x) + (m : K) • ((n : K) • y) := by
      rw [smul_add, smul_smul, smul_smul, Nat.cast_mul, mul_comm (n : K)]
    rw [this]
    exact Λ.add_mem (keyN n _ hx) (keyN m _ hy)
  | smul c x _ hx =>
    obtain ⟨n, hn, hx⟩ := hx
    obtain ⟨m, hm, a, ha⟩ := exists_nat_mul_eq_coe c
    refine ⟨m * n, Nat.mul_pos hm hn, ?_⟩
    have : ((m * n : ℕ) : K) • (c • x) = algebraMap (𝓞 K) K a • ((n : K) • x) := by
      rw [ha, smul_smul, smul_smul, Nat.cast_mul]
      congr 1
      ring
    rw [this]
    exact key a _ hx

theorem exists_nat_smul_mem {D : Formalism.BasicNotions.D7} (Λ : GlobalTheory.Unfold.LV D)
    (hΛ : Submodule.IsFullLattice ((Formalism.BasicNotions.D7.host D).E) Λ)
    (v : Formalism.BasicNotions.HSpace.V (Formalism.MainNotions.S.VS D)) :
    ∃ n : ℕ, 0 < n ∧ (n : (Formalism.BasicNotions.D7.host D).E) • v ∈ Λ :=
  exists_nat_smul_mem_of_mem_span Λ (by rw [hΛ.span_eq_top]; exact Submodule.mem_top)

end GlobalTheory.NatSmulMemOfSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsNeZeroSmulMem
section
open NumberField

namespace GlobalTheory.NonzeroIntegerSmulMem

theorem exists_ne_zero_smul_mem {E : Type} [Field E] [NumberField E] [StarRing E]
    {S : Formalism.BasicNotions.HSpace E} (L : Submodule (RingOfIntegers E) (Formalism.BasicNotions.HSpace.V S))
    (hL : Submodule.IsFullLattice E L) (x : Formalism.BasicNotions.HSpace.V S) :
    ∃ r : RingOfIntegers E, r ≠ (0 : RingOfIntegers E) ∧ r • x ∈ L := by

  have hx : x ∈ Submodule.span E (L : Set (Formalism.BasicNotions.HSpace.V S)) := by
    rw [hL.span_eq_top]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨r, hr, hrL⟩ := hy
    obtain ⟨t, ht, htL⟩ := hz
    refine ⟨r * t, mul_ne_zero hr ht, ?_⟩
    have e : (r * t) • (y + z) = t • (r • y) + r • (t • z) := by
      rw [smul_add, mul_smul, mul_smul, smul_comm r t y]
    rw [e]
    exact L.add_mem (L.smul_mem t hrL) (L.smul_mem r htL)
  | smul a y _ hy =>
    obtain ⟨r, hr, hrL⟩ := hy

    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors (RingOfIntegers E)) a
    refine ⟨r * (d : RingOfIntegers E), mul_ne_zero hr (nonZeroDivisors.coe_ne_zero d), ?_⟩
    have e1 : (d : RingOfIntegers E) • a = algebraMap (RingOfIntegers E) E n := by
      rw [Algebra.smul_def, mul_comm]
      exact hnd
    have e : (r * (d : RingOfIntegers E)) • (a • y) = n • (r • y) := by
      rw [mul_smul, ← smul_assoc (d : RingOfIntegers E) a y, e1, algebraMap_smul E n y,
        smul_comm r n y]
    rw [e]
    exact L.smul_mem n hrL

end GlobalTheory.NonzeroIntegerSmulMem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagLatticeStabiliserRealGroupMulMem
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

namespace GlobalTheory.FlagStabMul

theorem latGroup_mul (I : AutInst) (xf : I.Gf) {x y : I.Ginf} (hx : x ∈ latGroup I xf)
    (hy : y ∈ latGroup I xf) : x * y ∈ latGroup I xf := by
  obtain ⟨γ, hγ, rfl, hk⟩ := hx
  obtain ⟨δ, hδ, rfl, hl⟩ := hy
  refine ⟨γ * δ, (GlobalTheory.RatDiscrete.ratSub I).mul_mem hγ hδ, rfl, ?_⟩
  have h : xf⁻¹ * (γ * δ).2 * xf = (xf⁻¹ * γ.2 * xf) * (xf⁻¹ * δ.2 * xf) := by
    rw [Prod.snd_mul]; group
  rw [h]
  exact (Formalism.UG.stabGL I.Lf).mul_mem hk hl

theorem flagGroup_mul : ∀ (I : AutInst) (xf : I.Gf) (a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), ∀ x ∈ flagGroup I xf S, ∀ y ∈ flagGroup I xf S, x * y ∈ flagGroup I xf S := by
  intro I xf a S x hx y hy
  refine ⟨latGroup_mul I xf hx.1 hy.1, fun v k z hz => ?_⟩
  have h : uMat ((x * y) v) = uMat (x v) * uMat (y v) := rfl
  rw [h, ← Matrix.mulVec_mulVec]
  exact hx.2 v k _ (hy.2 v k z hz)

end GlobalTheory.FlagStabMul
end

