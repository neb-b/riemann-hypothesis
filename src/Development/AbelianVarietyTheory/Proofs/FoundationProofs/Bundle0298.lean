module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TheoremOfCubeOfAdditionFormulas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0267
public import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0294
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModelParameterSeriesDerivTransport
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

noncomputable section

namespace GlobalTheory.DerivTransport

theorem taylorCoeffAtZero_deriv (F : ℂ → ℂ) (n : ℕ) :
    coef1 (deriv F) n = ((n : ℂ) + 1) * coef1 F (n + 1) := by
  simp only [coef1]
  rw [← iteratedDeriv_succ', Nat.factorial_succ]
  have h1 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h2 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  push_cast
  field_simp

theorem algEnt_deriv {F : ℂ → ℂ} (hF : AlgEnt F) : AlgEnt (deriv F) := by
  refine ⟨?_, fun n => ?_⟩
  · exact (contDiff_infty_iff_deriv.1 (hF.1.contDiff)).2.differentiable (by simp)
  · rw [taylorCoeffAtZero_deriv]
    exact mul_mem (add_mem (natCast_mem _ n) (one_mem _)) (hF.2 _)

variable {p : ℕ} [Fact p.Prime]

theorem padicTaylorSeries_deriv_eq_derivative (lam : Qbar →+* ℂ_[p]) {F : ℂ → ℂ} (hF : AlgEnt F) :
    GL3Theta.ser1 lam (deriv F) = PowerSeries.derivative (R := ℂ_[p]) (GL3Theta.ser1 lam F) := by
  obtain ⟨a, ha⟩ := GlobalTheory.SerTransport.exists_coef hF
  ext n
  have e : coef1 (deriv F) n = (((n + 1 : Qbar) * a (n + 1) : Qbar) : ℂ) := by
    rw [taylorCoeffAtZero_deriv, ha]; push_cast; rfl
  rw [PowerSeries.coeff_derivative, GlobalTheory.SerTransport.coeff_padicTransportSeries, GlobalTheory.SerTransport.coeff_padicTransportSeries, e, ha,
    GlobalTheory.SerTransport.lamC_coe, GlobalTheory.SerTransport.lamC_coe, map_mul]
  simp [mul_comm]

theorem atU_deriv : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (F : ℂ → ℂ), AlgEnt F → AlgEnt (deriv F) ∧ PowerSeries.derivative (R := ℂ_[p]) (g.atU F) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * omegaW g.W g.wq * g.atU (deriv F) := by
  intro p _ g F hF
  refine ⟨algEnt_deriv hF, ?_⟩
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero'
    (GlobalTheory.SerTransport.const_Cl g ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]))
  rw [GlobalTheory.SerTransport.atU_eq, GlobalTheory.SerTransport.atU_eq, padicTaylorSeries_deriv_eq_derivative g.lam hF,
    PowerSeries.derivative_subst hs]
  have hd : PowerSeries.derivative (R := ℂ_[p]) (PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * g.l) =
      PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * omegaW g.W g.wq := by
    rw [Derivation.leibniz, PowerSeries.derivative_C, smul_zero, add_zero, smul_eq_mul, GL3Theta.G1.l,
      GlobalTheory.WpForm.derivative_flog]
  rw [hd]
  ring

end GlobalTheory.DerivTransport

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport
section
noncomputable section

namespace GlobalTheory.AdelicU

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

namespace HeightProper


omit [NumberField F] [NumberField E] in
theorem repr_map {R R' ι : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (b : Module.Basis ι F E)
    (φ : R →ₐ[F] R') (z : R ⊗[F] E) (i : ι) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) z) i =
      φ ((Algebra.TensorProduct.basis R b).repr z i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add y z hy hz => simp only [map_add (f := _), Finsupp.add_apply, hy, hz]
  | tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]

theorem nnnorm_repr_le_absFin {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
    (hb : ∀ i, IsIntegral ℤ (b i)) (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) (i : ι) :
    ‖(Algebra.TensorProduct.basis (Fv F v) b.traceDual).repr y i‖₊ ≤ absFin F v y := by
  rw [← absBar_algebraMap, algebraMap_basis_repr]
  refine (valBar F v).map_sum_le fun τ _ => ?_
  change absBar F v _ ≤ _
  rw [absBar_mul]
  refine (mul_le_of_le_one_right' ?_).trans (le_absFin F v τ y)
  have := (le_absFin F v τ _).trans (absFin_tmul_le F v 1 (⟨b i, hb i⟩ : 𝓞 E))
  rw [finEmb_tmul, map_one, one_mul, nnnorm_one] at this
  exact this

theorem exists_norm_repr_le {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
    (w : InfinitePlace F) (c : ℝ) (i : ι) : ∃ B : ℝ, ∀ y : w.Completion ⊗[F] E,
      (∀ τ : EmbOver E w, ‖infEmb τ y‖ ≤ c) →
      ‖(Algebra.TensorProduct.basis w.Completion b.traceDual).repr y i‖ ≤ B := by
  letI : Algebra F ℂ := w.embedding.toAlgebra
  let t : (E →ₐ[F] ℂ) → EmbOver E w := fun τ => ⟨τ, RingHom.ext τ.commutes⟩
  have key : ∀ y : w.Completion ⊗[F] E, InfinitePlace.Completion.extensionEmbedding w
      ((Algebra.TensorProduct.basis w.Completion b.traceDual).repr y i) =
      ∑ τ : E →ₐ[F] ℂ, infEmb (t τ) y * τ (b i) := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => simp only [map_add (f := _), Finsupp.add_apply, hy, hz, add_mul, Finset.sum_add_distrib]
    | tmul a e =>
      have h : ∀ x : F, InfinitePlace.Completion.extensionEmbedding w (algebraMap F w.Completion x) =
          algebraMap F ℂ x := fun x => by
        rw [AbsoluteValue.Completion.algebraMap_def, InfinitePlace.Completion.extensionEmbedding_coe]
        rfl
      rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul,
        h, Module.Basis.traceDual_repr_apply, Algebra.traceForm_apply,
        trace_eq_sum_embeddings, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [infEmb_tmul, map_mul, mul_assoc]; rfl
  refine ⟨∑ τ : E →ₐ[F] ℂ, c * ‖τ (b i)‖, fun y hy => ?_⟩
  rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _), key]
  refine norm_sum_le_of_le _ fun τ _ => ?_
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hy _) (norm_nonneg _)

theorem norm_entry_le_opNorm {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (i j : n) :
    ‖A i j‖ ≤ opNorm A := by
  have h := (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A).le_opNorm (EuclideanSpace.single j 1)
  have h2 := PiLp.norm_apply_le (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A (EuclideanSpace.single j 1)) i
  have h3 : (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) A (EuclideanSpace.single j 1)) i = A i j := by
    change ∑ k, A i k * (EuclideanSpace.single j (1 : ℂ)) k = _
    simp [Pi.single_apply]
  rw [h3] at h2
  simpa [opNorm] using h2.trans h

theorem exists_compact_adeles (B : InfinitePlace F → ℝ) (c : ℝ≥0) : ∃ C : Set (AF F), IsCompact C ∧
    ∀ a : AF F, (∀ w, ‖evInf F w a‖ ≤ B w) → ∀ d : ℕ, 0 < d → (d : ℝ≥0) ≤ c →
      (∀ v, ‖(d : Fv F v) * evFin F v a‖ ≤ 1) → a ∈ C := by
  have h1 : IsCompact (X := Ainf F) (Set.pi Set.univ fun w : InfinitePlace F => {x : w.Completion | ‖x‖ ≤ B w}) :=
    isCompact_univ_pi fun w => by
      have := (InfinitePlace.Completion.isometry_extensionEmbedding w).isClosedEmbedding.isCompact_preimage
        (isCompact_closedBall 0 (B w))
      convert this using 1
      ext x
      rw [Set.mem_preimage, mem_closedBall_zero_iff,
        (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _), Set.mem_setOf_eq]
  have h2 : IsCompact (⋃ d ∈ Finset.range (⌊c⌋₊ + 1), (fun x : Af F => algebraMap F (Af F) (d : F)⁻¹ * x) ''
      {a : Af F | ∀ v, a v ∈ v.adicCompletionIntegers F}) :=
    (Finset.range _).isCompact_biUnion fun d _ =>
      (GlobalTheory.AdeleCocompact.isCompact_integral F).image (continuous_const.mul continuous_id)
  refine ⟨_, h1.prod h2, fun a ha d hd hdc hv => ⟨fun w _ => ha w, ?_⟩⟩
  refine Set.mem_biUnion (x := d) (Finset.mem_coe.2 (Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.le_floor hdc))))
    ⟨(d : Af F) * a.2, fun v => ?_, ?_⟩
  · have := hv v
    rw [← map_natCast (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v)] at this
    exact Valued.toNormedField.norm_le_one_iff.1 this
  · have hd0 : (d : F) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
    beta_reduce
    rw [← mul_assoc, ← map_natCast (algebraMap F (Af F)), ← map_mul, inv_mul_cancel₀ hd0, map_one, one_mul]

theorem exists_compact_entries (n : Type) [Fintype n] [DecidableEq n] (c : ℝ≥0) :
    ∃ C : Set (AF F ⊗[F] E), IsCompact C ∧
      ∀ g : GL n (AF F ⊗[F] E), heightGL F g ≤ c → ∀ i j, g.1 i j ∈ C := by
  classical
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral (𝓞 F) F E
  have hb' : ∀ i, IsIntegral ℤ (b i) := fun i => isIntegral_trans _ (hb i)
  choose B hB using fun (k : s) (w : InfinitePlace F) => exists_norm_repr_le b w c k
  choose C hC hC' using fun k : s => exists_compact_adeles (B k) c
  let e := (Algebra.TensorProduct.basis (AF F) b.traceDual).equivFun
  have he : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  refine ⟨e.symm '' Set.pi Set.univ C, (isCompact_univ_pi hC).image he, fun g hg i j =>
    ⟨e (g.1 i j), fun k _ => ?_, e.symm_apply_apply _⟩⟩
  obtain ⟨d, hd, hdc, hv⟩ := GlobalTheory.SmoothForms.denom_global (fun v => htFin F v (bc (compFin F E v) g))
    (fun v => one_le_htOf _ _) (finite_mulSupport_htFin F g)
  refine hC' k _ (fun w => ?_) d hd ?_ fun v => hv v _ ?_
  · refine (congrArg norm (repr_map b.traceDual (evInf F w) (g.1 i j) k)).symm.trans_le (hB k w _ fun τ => ?_)
    have h := (((normInf_le_iff F w).1 (le_htOf _ _) τ).trans (GlobalTheory.Grow.htInf_le_heightGL F g w)).trans hg
    exact (norm_entry_le_opNorm _ i j).trans (NNReal.coe_le_coe.2 h)
  · exact (hdc.trans (le_mul_of_one_le_left' (Finset.one_le_prod' fun _ _ => one_le_htOf _ _))).trans hg
  · refine (congrArg nnnorm (repr_map b.traceDual (evFin F v) (g.1 i j) k)).symm.trans_le
      ((nnnorm_repr_le_absFin b hb' v _ k).trans ?_)
    exact (absFin_le_normFin F v (bc (compFin F E v) g).1 i j).trans (le_htOf _ _)

end HeightProper

section GeneralLinearIntegers

variable (F) {n : Type} [Fintype n] [DecidableEq n]

theorem isCompact_heightGL_le (c : ℝ≥0) : IsCompact {g : GL n (AF F ⊗[F] E) | heightGL F g ≤ c} := by
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : T2Space (AF F ⊗[F] E) := e.isEmbedding.t2Space
  obtain ⟨C, hC, hC'⟩ := HeightProper.exists_compact_entries (F := F) (E := E) n c
  let S : Set (Matrix n n (AF F ⊗[F] E)) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => C
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC
  have hK := (Units.isClosedEmbedding_embedProduct (α := Matrix n n (AF F ⊗[F] E))).isCompact_preimage
    (hS.prod (hS.image MulOpposite.continuous_op))
  refine hK.of_isClosed_subset (isClosed_le (GlobalTheory.Grow.continuous_heightGL F) continuous_const) fun g hg => ?_
  exact ⟨fun i _ j _ => hC' g hg i j, (g⁻¹).1, fun i _ j _ => hC' g⁻¹ (by rwa [heightGL_inv]) i j, rfl⟩

end GeneralLinearIntegers

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem isClosedEmbedding_matHom_GAd : Topology.IsClosedEmbedding (matHom (AF F) σ J) := by
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : T2Space (AF F ⊗[F] E) := e.isEmbedding.t2Space
  have hcl : IsClosed (HR (AF F) σ J : Set (GL (Fin n) (AF F ⊗[F] E))) := by
    have hv : Continuous fun g : GL (Fin n) (AF F ⊗[F] E) => (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) :=
      Units.continuous_val
    exact isClosed_eq (((hv.matrix_map (GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ)).matrix_transpose.matrix_mul
      continuous_const).matrix_mul hv) continuous_const
  exact hcl.isClosedEmbedding_subtypeVal

theorem continuous_height_GAd : Continuous (height σ J) :=
  (GlobalTheory.Grow.continuous_heightGL F).comp (isEmbedding_matHom _ σ J).continuous

theorem isCompact_height_le (c : ℝ≥0) : IsCompact {g : GAd σ J | height σ J g ≤ c} :=
  (isClosedEmbedding_matHom_GAd σ J).isCompact_preimage (isCompact_heightGL_le F c)

theorem height_bddAbove_of_isCompact {K : Set (GAd σ J)} (hK : IsCompact K) :
    ∃ c : ℝ≥0, ∀ g ∈ K, height σ J g ≤ c := by
  obtain ⟨c, hc⟩ := hK.bddAbove_image (continuous_height_GAd σ J).continuousOn
  exact ⟨c, fun g hg => hc ⟨g, hg, rfl⟩⟩

end GlobalTheory.AdelicU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralNormRmulLe
section
open MeasureTheory Filter Set GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.AutomorphicL2Pointwise

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ] {μ : Measure G}
  [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {f : G → ℂ}

theorem integrableOn_rmul (F : L2 Γ μ) (y : G) {s : Set (Quot Γ)} (hs : quotMeasure Γ μ s ≠ ⊤) :
    IntegrableOn (fun q => F (rmul Γ y q)) s (quotMeasure Γ μ) :=
  (integrableOn_Lp_of_measure_ne_top (R Γ μ y F) (by norm_num) hs).congr (ae_restrict_of_ae (coeFn_R y F))

theorem setIntegral_norm_rmul_le (F : L2 Γ μ) (y : G) {s : Set (Quot Γ)} (hs : quotMeasure Γ μ s ≠ ⊤) :
    ∫ q in s, ‖F (rmul Γ y q)‖ ∂quotMeasure Γ μ ≤
      (quotMeasure Γ μ).real s + ∫ q, ‖F q‖ ^ 2 ∂quotMeasure Γ μ := by
  have h2 : Integrable (fun q => ‖F q‖ ^ 2) (quotMeasure Γ μ) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable F)).1 (Lp.memLp F)
  have h3 : Integrable (fun q => ‖F (rmul Γ y q)‖ ^ 2) (quotMeasure Γ μ) :=
    ((measurePreserving_rmul y).integrable_comp h2.1).2 h2
  have h4 : ∫ q, ‖F (rmul Γ y q)‖ ^ 2 ∂quotMeasure Γ μ = ∫ q, ‖F q‖ ^ 2 ∂quotMeasure Γ μ := by
    have h := integral_map (μ := quotMeasure Γ μ) (measurable_rmul (Γ := Γ) y).aemeasurable
      (f := fun q => ‖F q‖ ^ 2) (by rw [(measurePreserving_rmul y).map_eq]; exact h2.1)
    rw [(measurePreserving_rmul y).map_eq] at h
    exact h.symm
  have h1 : IntegrableOn (fun _ => (1 : ℝ)) s (quotMeasure Γ μ) := integrableOn_const hs
  calc ∫ q in s, ‖F (rmul Γ y q)‖ ∂quotMeasure Γ μ
      ≤ ∫ q in s, (1 + ‖F (rmul Γ y q)‖ ^ 2) ∂quotMeasure Γ μ :=
        integral_mono (integrableOn_rmul F y hs).norm (Integrable.add h1 h3.integrableOn) fun q => by
          beta_reduce
          nlinarith [sq_nonneg (‖F (rmul Γ y q)‖ - 1), norm_nonneg (F (rmul Γ y q))]
    _ = (quotMeasure Γ μ).real s + ∫ q in s, ‖F (rmul Γ y q)‖ ^ 2 ∂quotMeasure Γ μ := by
        rw [integral_add h1 h3.integrableOn]
        simp
    _ ≤ _ := by
        rw [← h4]
        exact add_le_add le_rfl (setIntegral_le_integral h3 (.of_forall fun q => by positivity))

variable [SigmaFinite μ]

theorem integrable_prod (hf : Integrable f μ) (F : L2 Γ μ) {s : Set (Quot Γ)} (hs : quotMeasure Γ μ s ≠ ⊤) :
    Integrable (fun p : Quot Γ × G => f p.2 * F (rmul Γ p.2 p.1)) (((quotMeasure Γ μ).restrict s).prod μ) := by
  haveI : IsFiniteMeasure ((quotMeasure Γ μ).restrict s) := isFiniteMeasure_restrict.2 hs
  have hm : AEStronglyMeasurable (fun p : Quot Γ × G => f p.2 * F (rmul Γ p.2 p.1))
      (((quotMeasure Γ μ).restrict s).prod μ) :=
    hf.1.comp_snd.mul ((Lp.stronglyMeasurable F).comp_measurable measurable_rmul_uncurry).aestronglyMeasurable
  refine (integrable_prod_iff' hm).2 ⟨.of_forall fun y => (integrableOn_rmul F y hs).const_mul (f y), ?_⟩
  refine (hf.norm.mul_const ((quotMeasure Γ μ).real s + ∫ q, ‖F q‖ ^ 2 ∂quotMeasure Γ μ)).mono'
    hm.norm.prod_swap.integral_prod_right' (.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  simp only [norm_mul]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (setIntegral_norm_rmul_le F y hs) (norm_nonneg _)

theorem ae_integrable (hf : Integrable f μ) (F : L2 Γ μ) :
    ∀ᵐ q ∂quotMeasure Γ μ, Integrable (fun y => f y * F (rmul Γ y q)) μ := by
  haveI : SigmaFinite (quotMeasure Γ μ) :=
    SigmaFinite.of_map _ (measurePreserving_sec (Γ := Γ) (μ := μ)).measurable.aemeasurable
      (by rw [measurePreserving_sec.map_eq]; infer_instance)
  refine ae_of_forall_measure_lt_top_ae_restrict _ fun s _ hs => ?_
  haveI : IsFiniteMeasure ((quotMeasure Γ μ).restrict s) := isFiniteMeasure_restrict.2 hs.ne
  exact (integrable_prod hf F hs.ne).prod_right_ae

theorem coeFn_Rop [LocallyCompactSpace G] [IsFiniteMeasureOnCompacts μ] (hf : Integrable f μ) (F : L2 Γ μ) :
    Rop Γ μ f F =ᵐ[quotMeasure Γ μ] fun q => ∫ y, f y * F (rmul Γ y q) ∂μ := by
  haveI : SigmaFinite (quotMeasure Γ μ) :=
    SigmaFinite.of_map _ (measurePreserving_sec (Γ := Γ) (μ := μ)).measurable.aemeasurable
      (by rw [measurePreserving_sec.map_eq]; infer_instance)
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
    (fun s _ hs => integrableOn_Lp_of_measure_ne_top _ (by norm_num) hs.ne)
    (fun s _ hs => (integrable_prod hf F hs.ne).integral_prod_left) fun s hs hfin => ?_
  have hR := isRepOp_Rop (Γ := Γ) hf F
  rw [integral_integral_swap (f := fun q y => f y * F (rmul Γ y q)) (integrable_prod hf F hfin.ne),
    ← L2.inner_indicatorConstLp_one hs hfin.ne, hR.2]
  refine (integral_inner (𝕜 := ℂ) hR.1 _).symm.trans (integral_congr_ae (.of_forall fun y => ?_))
  beta_reduce
  rw [inner_smul_right, L2.inner_indicatorConstLp_one hs hfin.ne, integral_const_mul,
    integral_congr_ae (ae_restrict_of_ae (coeFn_R y F))]

theorem lift_Rop_eq_convR (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] :
    ∀ f : G → ℂ, Integrable f μ → ∀ F : L2 Γ μ,
      (∀ᵐ x ∂μ, Integrable (fun y => f y * lift Γ F (x * y)) μ) ∧
        lift Γ (Rop Γ μ f F) =ᵐ[μ] convR μ f (lift Γ F) :=
  fun _ hf F => ⟨ae_quotMeasure_iff.1 (ae_integrable hf F), ae_quotMeasure_iff.1 (coeFn_Rop hf F)⟩

end GlobalTheory.AutomorphicL2Pointwise
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarCubeColumnsModelParameterSeries
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
open PowerSeries

noncomputable section

namespace GlobalTheory.FrobStick

theorem sgStar_atU {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (hL : IsLat g.abelian₂) (hσ : AlgEnt (sgStar g.abelian₂)) :
    g.atU (sgStar g.abelian₂) =
      C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * X * ePhi1 g.lam g.abelian₂ g.C g.wq := by
  have h0 : coef1 (sgStar g.abelian₂) 0 = 0 := by
    simp [coef1, (hL.sg_eq_zero 0).2 (zero_mem _)]
  obtain ⟨S, hS⟩ : ∃ S : PowerSeries Qbar,
      PowerSeries.mk (coef1 (sgStar g.abelian₂)) = PowerSeries.map (algebraMap Qbar ℂ) (X * S) := by
    refine ⟨PowerSeries.mk fun n => ⟨coef1 (sgStar g.abelian₂) (n + 1), hσ.2 _⟩, ?_⟩
    ext n
    cases n with
    | zero => simp [h0]
    | succ n => rw [coeff_map, coeff_succ_X_mul, coeff_mk, coeff_mk]; rfl
  have hS' : GL3Theta.ser1 g.lam (sgStar g.abelian₂) = X * PowerSeries.map g.lam S := by
    rw [GlobalTheory.EvenTheta.Param.theta_series_map_coefficients g.lam _ _ hS, map_mul, map_X]
  have hE := GlobalTheory.EvenTheta.Param.X_mul_ePhi1 g _ hS'
  have hs := HasSubst.of_constantCoeff_zero'
    (GlobalTheory.SerTransport.const_Cl g ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]))
  rw [GlobalTheory.SerTransport.atU_eq, hS', subst_mul hs, subst_X hs, mul_assoc, mul_assoc, hE]

theorem colAB_atU : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), IsWq g.W g.wq → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar → AlgEnt (GlobalTheory.FrobStick.colA g.abelian₂) ∧ AlgEnt (GlobalTheory.FrobStick.colB g.abelian₂ v) ∧ g.atU (sgStar g.abelian₂) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * PowerSeries.X * ePhi1 g.lam g.abelian₂ g.C g.wq ∧ g.atU (GlobalTheory.FrobStick.colA g.abelian₂) = PowerSeries.C (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 3) * PowerSeries.X ^ 3 * ePhi1 g.lam g.abelian₂ g.C g.wq ^ 3 ∧ g.atU (GlobalTheory.FrobStick.colB g.abelian₂ v) = PowerSeries.C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * ePhi1 g.lam g.abelian₂ g.C g.wq ^ 3 * (PowerSeries.X * g.wq⁻¹ + PowerSeries.C (((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * g.C.r) * PowerSeries.X ^ 3) := by
  intro p _ g hq hL h2 h3 hσ v hv hw
  obtain ⟨hT, hC, -, -⟩ := GlobalTheory.SerTransport.transport p g
  obtain ⟨aT, eT⟩ := GlobalTheory.EvenTheta.Param.sqTh_atU p g hq hL h2 h3 hσ v hv hw
  have e1 := sgStar_atU g hL hσ
  obtain ⟨⟨a2, e2⟩, -⟩ := hT _ _ hσ hσ
  obtain ⟨⟨a3, e3⟩, -⟩ := hT _ _ a2 hσ
  obtain ⟨aw, ew⟩ := hC _ hw
  obtain ⟨⟨a4, e4⟩, -⟩ := hT _ _ aw a2
  obtain ⟨-, a5, e5⟩ := hT _ _ aT a4
  obtain ⟨⟨a6, e6⟩, -⟩ := hT _ _ hσ a5
  have hA : colA g.abelian₂ = fun z => sgStar g.abelian₂ z * sgStar g.abelian₂ z * sgStar g.abelian₂ z := by
    funext z; rw [colA]; ring
  have hB : colB g.abelian₂ v = fun z => sgStar g.abelian₂ z *
      (sqTh g.abelian₂ v z + wpF g.abelian₂ v * (sgStar g.abelian₂ z * sgStar g.abelian₂ z)) := by
    funext z; rw [colB]; ring
  rw [hA, hB]
  refine ⟨a3, a6, e1, ?_, ?_⟩
  · rw [e3, e2, e1, map_pow]; ring
  · rw [e6, e5, e4, e2, ew, eT, e1, lineSer, xAt]
    simp only [map_mul, map_pow, map_sub]
    ring

end GlobalTheory.FrobStick
end
end

