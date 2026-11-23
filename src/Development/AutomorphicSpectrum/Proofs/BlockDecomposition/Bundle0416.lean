module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0394
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.L2ConvolutionLocallyCompactMem
section
open MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.AutomorphicL2Convolution

private theorem descend_eq_sec_lemma {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ]
    {φ : G → ℂ} (hφ : LeftInv Γ φ) (q : Quot Γ) : descend Γ φ q = φ (sec Γ q) := by
  have h2 : mk Γ (Quotient.out q) = mk Γ (sec Γ q) := (Quotient.out_eq q).trans (mk_sec q).symm
  obtain ⟨γ, hγ⟩ := mk_eq_iff.1 h2
  show φ (Quotient.out q) = φ (sec Γ q)
  rw [← hγ, hφ _ γ.2]

private theorem descend_rmul_lemma_2 {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ]
    {φ : G → ℂ} (hφ : LeftInv Γ φ) (g : G) (q : Quot Γ) :
    descend Γ φ (rmul Γ g q) = φ (sec Γ q * g) := by
  rw [descend_eq_sec_lemma hφ]
  have h1 : rmul Γ g q = mk Γ (sec Γ q * g) := by
    rw [← rmul_mk, mk_sec]
  have h2 : mk Γ (sec Γ (rmul Γ g q)) = mk Γ (sec Γ q * g) := (mk_sec _).trans h1
  obtain ⟨γ, hγ⟩ := mk_eq_iff.1 h2
  rw [← hγ, hφ _ γ.2]

private theorem coeFn_R_lemma_3 {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {Γ : Subgroup G} [DiscreteTopology Γ]
    {μ : Measure G} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {φ : G → ℂ} (h : MemL2Quotient Γ μ φ) (g : G) :
    ∀ᵐ q ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ),
      (((R Γ μ) g) h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) q = φ (sec Γ q * g) := by
  have h2 : (fun q => (h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) (rmul Γ g q)) =ᵐ[GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ]
      fun q => descend Γ φ (rmul Γ g q) :=
    (measurePreserving_rmul g).quasiMeasurePreserving.ae_eq_comp h.coeFn_toL2
  refine (coeFn_R g h.toL2).trans (h2.trans (Filter.Eventually.of_forall fun q => ?_))
  exact descend_rmul_lemma_2 h.1 g q

private theorem integral_norm_sq_lemma_4 {α : Type} [MeasurableSpace α] {m : Measure α} (F : Lp ℂ 2 m) :
    ∫ q, ‖F q‖ ^ 2 ∂m = ‖F‖ ^ 2 := by
  have h1 := MeasureTheory.L2.inner_def (𝕜 := ℂ) F F
  simp only [inner_self_eq_norm_sq_to_K] at h1
  simp_rw [← RCLike.ofReal_pow] at h1
  rw [integral_ofReal] at h1
  exact (RCLike.ofReal_inj.mp h1).symm

private theorem setIntegral_norm_le_lemma_5 {α : Type} [MeasurableSpace α] {m : Measure α} {S : Set α}
    (hS : m S < ∞) (F : Lp ℂ 2 m) :
    ∫ q in S, ‖F q‖ ∂m ≤ ((∫ q in S, (1 : ℝ) ∂m) + ‖F‖ ^ 2) / 2 := by
  haveI : IsFiniteMeasure (m.restrict S) := isFiniteMeasure_restrict.2 hS.ne
  have hsq : Integrable (fun q => ‖F q‖ ^ 2) m := (Lp.memLp F).norm.integrable_sq
  have hint1 : Integrable (fun q => (1 + ‖F q‖ ^ 2) / 2) (m.restrict S) :=
    ((integrable_const (1 : ℝ)).add hsq.restrict).div_const 2
  calc ∫ q in S, ‖F q‖ ∂m ≤ ∫ q in S, (1 + ‖F q‖ ^ 2) / 2 ∂m := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun q => norm_nonneg (F q)) hint1
          (Filter.Eventually.of_forall fun q => ?_)
        nlinarith [sq_nonneg (‖F q‖ - 1)]
    _ = ((∫ q in S, (1 : ℝ) ∂m) + ∫ q in S, ‖F q‖ ^ 2 ∂m) / 2 := by
        rw [integral_div, integral_add (integrable_const (1 : ℝ)) hsq.restrict]
    _ ≤ ((∫ q in S, (1 : ℝ) ∂m) + ‖F‖ ^ 2) / 2 := by
        have := setIntegral_le_integral (s := S) hsq (Filter.Eventually.of_forall fun q => by positivity)
        rw [integral_norm_sq_lemma_4 F] at this
        linarith

theorem memL2_convolution_mem {G L : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ]
    (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μ] [Group L]
    [TopologicalSpace L] [IsTopologicalGroup L] [SecondCountableTopology L] [T2Space L] [LocallyCompactSpace L]
    [MeasurableSpace L] [BorelSpace L] (ν : Measure L) [IsFiniteMeasureOnCompacts ν] (j : L →* G)
    (hj : Continuous j) (D : L → ℂ) (hD : Continuous D) (hDc : HasCompactSupport D) (φ ψ : G → ℂ)
    (_hφ : Continuous φ) (h : MemL2Quotient Γ μ φ) (hψ : ∀ g, ψ g = ∫ y, φ (g * j y) * D y ∂ν) :
    ∃ h' : MemL2Quotient Γ μ ψ, ∀ W : Submodule ℂ (L2 Γ μ), IsSubrep (R Γ μ) W → h.toL2 ∈ W → h'.toL2 ∈ W := by
  classical
  have hLφ : LeftInv Γ φ := h.1
  have hπ' : GlobalTheory.OpTrace.IsUnitaryRep ((R Γ μ).comp j) :=
    ⟨fun y w => norm_R (j y) w, fun w => (continuous_R w).comp hj⟩
  have hDint : Integrable D ν := hD.integrable_of_hasCompactSupport hDc
  obtain ⟨hTint, hTv⟩ := isRepOp_of_integrable (μ := ν) hπ' hDint h.toL2
  set T := GlobalTheory.OpTrace.repOp ((R Γ μ).comp j) ν D with hTdef
  have hLψ : LeftInv Γ ψ := by
    intro γ hγ g
    rw [hψ (γ * g), hψ g]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show φ (γ * g * j y) * D y = φ (g * j y) * D y
    rw [mul_assoc γ g (j y), hLφ γ hγ]
  have hmeasH : Measurable fun p : L × Quot Γ => φ (sec Γ p.2 * j p.1) * D p.1 :=
    (_hφ.measurable.comp ((measurableEmbedding_sec.measurable.comp measurable_snd).mul
      (hj.measurable.comp measurable_fst))).mul (hD.measurable.comp measurable_fst)
  have hprod : ∀ S : Set (Quot Γ), MeasurableSet S → GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ S < ∞ →
      Integrable (fun p : L × Quot Γ => φ (sec Γ p.2 * j p.1) * D p.1)
        (ν.prod ((GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ).restrict S)) := by
    intro S hS hSf
    haveI : IsFiniteMeasure ((GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ).restrict S) := isFiniteMeasure_restrict.2 hSf.ne
    rw [integrable_prod_iff hmeasH.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun y => ?_, ?_⟩
    · have hc := coeFn_R_lemma_3 h (j y)
      refine ((((Lp.memLp (((R Γ μ) (j y)) h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ))).restrict S).integrable
        one_le_two).mul_const (D y)).congr ?_
      exact ae_restrict_of_ae (hc.mono fun q hq => by simp only [hq])
    · refine Integrable.mono'
        (hDint.norm.mul_const (((∫ q in S, (1 : ℝ) ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) +
          ‖(h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ))‖ ^ 2) / 2))
        (hmeasH.norm.aestronglyMeasurable.integral_prod_right') (Filter.Eventually.of_forall fun y => ?_)
      have hc := coeFn_R_lemma_3 h (j y)
      rw [Real.norm_of_nonneg (integral_nonneg fun q => norm_nonneg _)]
      have e1 : ∫ q, ‖φ (sec Γ q * j y) * D y‖ ∂((GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ).restrict S)
          = (∫ q in S, ‖(((R Γ μ) (j y)) h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) q‖ ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) * ‖D y‖ := by
        simp_rw [norm_mul]
        rw [integral_mul_const]
        congr 1
        exact integral_congr_ae (ae_restrict_of_ae (hc.mono fun q hq => by simp only [hq]))
      have hb := setIntegral_norm_le_lemma_5 hSf ((((R Γ μ) (j y)) h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)))
      have hn : ‖(((R Γ μ) (j y)) h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ))‖
          = ‖(h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ))‖ := norm_R _ _
      rw [hn] at hb
      show ∫ q, ‖φ (sec Γ q * j y) * D y‖ ∂((GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ).restrict S) ≤ _
      rw [e1, mul_comm _ (‖D y‖)]
      exact mul_le_mul_of_nonneg_left hb (norm_nonneg _)
  have hkey : (fun q => (T h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) q) =ᵐ[GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ]
      fun q => ψ (sec Γ q) := by
    refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite ?_ ?_ ?_
    · intro S hS hSf
      haveI : IsFiniteMeasure ((GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ).restrict S) := isFiniteMeasure_restrict.2 hSf.ne
      exact ((Lp.memLp (T h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ))).restrict S).integrable one_le_two
    · intro S hS hSf
      exact (hprod S hS hSf).integral_prod_right.congr
        (Filter.Eventually.of_forall fun q => (hψ (sec Γ q)).symm)
    · intro S hS hSf
      have hSf' : GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ S ≠ ∞ := hSf.ne
      have hstep : ∀ y, ⟪indicatorConstLp 2 hS hSf' (1 : ℂ),
          (D y • ((((R Γ μ).comp j) y h.toL2 : L2 Γ μ) : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)))⟫_ℂ
          = ∫ q in S, φ (sec Γ q * j y) * D y ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) := by
        intro y
        have hc := coeFn_R_lemma_3 h (j y)
        rw [inner_smul_right, L2.inner_indicatorConstLp_one, integral_mul_const, mul_comm (D y)]
        congr 1
        exact integral_congr_ae (ae_restrict_of_ae (hc.mono fun q hq => by
          simp only [MonoidHom.comp_apply]; exact hq))
      calc ∫ q in S, (T h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) q ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)
          = ⟪indicatorConstLp 2 hS hSf' (1 : ℂ), (T h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ))⟫_ℂ :=
            (L2.inner_indicatorConstLp_one hS hSf' _).symm
        _ = ⟪indicatorConstLp 2 hS hSf' (1 : ℂ),
              ((∫ y, D y • ((R Γ μ).comp j) y h.toL2 ∂ν : L2 Γ μ) : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ))⟫_ℂ := by
            rw [hTv]; rfl
        _ = ∫ y, ⟪indicatorConstLp 2 hS hSf' (1 : ℂ),
              (D y • ((((R Γ μ).comp j) y h.toL2 : L2 Γ μ) : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)))⟫_ℂ ∂ν :=
            (integral_inner hTint _).symm
        _ = ∫ y, ∫ q in S, φ (sec Γ q * j y) * D y ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) ∂ν :=
            integral_congr_ae (Filter.Eventually.of_forall hstep)
        _ = ∫ q in S, ∫ y, φ (sec Γ q * j y) * D y ∂ν ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) :=
            integral_integral_swap (hprod S hS hSf)
        _ = ∫ q in S, ψ (sec Γ q) ∂(GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ) :=
            integral_congr_ae (Filter.Eventually.of_forall fun q => (hψ (sec Γ q)).symm)
  have hae : descend Γ ψ =ᵐ[GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ] fun q => (T h.toL2 : Lp ℂ 2 (GlobalTheory.AutomorphicL2Unitary.quotMeasure Γ μ)) q :=
    Filter.EventuallyEq.trans (Filter.Eventually.of_forall fun q => descend_eq_sec_lemma hLψ q) hkey.symm
  have hmem : MemL2Quotient Γ μ ψ := ⟨hLψ, MemLp.ae_eq hae.symm (Lp.memLp _)⟩
  refine ⟨hmem, fun W hW hvW => ?_⟩
  have hEq : hmem.toL2 = T h.toL2 := Lp.ext (hmem.coeFn_toL2.trans hae)
  rw [hEq]
  exact IsSubrep.map_mem_of_isRepOp (π := (R Γ μ).comp j) ⟨hW.1, fun y w hw => hW.2 (j y) w hw⟩
    (isRepOp_of_integrable hπ' hDint) hvW

end GlobalTheory.CompanionTheory.AutomorphicL2Convolution
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeMaxEvenAlmostAll
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

set_option linter.unusedSectionVars false

noncomputable section

namespace GlobalTheory.CompanionTheory.KFin.AE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}

theorem sigR_inclR (e : E) : sigR (Fv F v) σ (inclR (Fv F v) e) = inclR (Fv F v) (σ e) := rfl

theorem hR_apply (x y : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x y = ∑ i, ∑ j, sigR (Fv F v) σ (x i) * inclR (Fv F v) (J i j) * y j := rfl

theorem sigR_sigR (hσ : ∀ e, σ (σ e) = e) (y : Fv F v ⊗[F] E) : sigR (Fv F v) σ (sigR (Fv F v) σ y) = y := by
  induction y with
  | tmul a b => simp [sigR, hσ]
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

theorem sigR_hR (hσ : ∀ e, σ (σ e) = e) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (hR (Fv F v) σ J x y) = hR (Fv F v) σ J y x := by
  rw [hR_apply, hR_apply, Finset.sum_comm]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, sigR_sigR hσ, sigR_inclR]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hJ i j]
  ring

theorem hR_mem (hJv : ∀ i j, inclR (Fv F v) (J i j) ∈ intLoc F E v) {x y : Fin n → Fv F v ⊗[F] E}
    (hx : ∀ i, x i ∈ intLoc F E v) (hy : ∀ i, y i ∈ intLoc F E v) : hR (Fv F v) σ J x y ∈ intLoc F E v := by
  rw [hR_apply]
  exact sum_mem fun i _ => sum_mem fun j _ => mul_mem (mul_mem (sigR_mem_intLoc σ (hx i)) (hJv i j)) (hy j)

theorem hR_single (i : Fin n) (z : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J (Pi.single i 1) z = (J.map (inclR (F := F) (Fv F v)) *ᵥ z) i := by
  rw [hR_apply, Finset.sum_eq_single i]
  · simp [Matrix.mulVec, dotProduct]
  · intro j _ hj
    simp [Pi.single_apply, hj]
  · simp

theorem mem_of_hR_single (hdet : J.det ≠ 0) (hJi : ∀ i j, inclR (Fv F v) (J⁻¹ i j) ∈ intLoc F E v)
    {z : Fin n → Fv F v ⊗[F] E} (hz : ∀ i, hR (Fv F v) σ J (Pi.single i 1) z ∈ intLoc F E v) (a : Fin n) :
    z a ∈ intLoc F E v := by
  have e : J⁻¹.map (inclR (F := F) (Fv F v)) * J.map (inclR (F := F) (Fv F v)) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet), Matrix.map_one _ (map_zero _) (map_one _)]
  have hz' : z = J⁻¹.map (inclR (F := F) (Fv F v)) *ᵥ (J.map (inclR (F := F) (Fv F v)) *ᵥ z) := by
    rw [Matrix.mulVec_mulVec, e, Matrix.one_mulVec]
  obtain ⟨w, hw⟩ : ∃ w, w = J.map (inclR (F := F) (Fv F v)) *ᵥ z := ⟨_, rfl⟩
  have hw' : ∀ j, w j ∈ intLoc F E v := fun j => by rw [hw, ← hR_single (σ := σ)]; exact hz j
  rw [← hw] at hz'
  rw [hz']
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun j _ => mul_mem (hJi a j) (hw' j)

end GlobalTheory.CompanionTheory.KFin.AE

namespace GlobalTheory.CompanionTheory.KFin.AE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}

theorem single_mem_latLoc_std (i : Fin n) :
    (Pi.single i 1 : Fin n → Fv F v ⊗[F] E) ∈ latLoc F (stdLattice E n) v := by
  refine mem_latLoc_stdLattice.2 fun j => ?_
  by_cases h : j = i
  · subst h; simp only [Pi.single_eq_same]; exact one_mem _
  · rw [Pi.single_eq_of_ne h]; exact zero_mem _

theorem sum_single_smul (y : Fin n → Fv F v ⊗[F] E) : ∑ i, y i • (Pi.single i 1 : Fin n → Fv F v ⊗[F] E) = y := by
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem isLat_latLoc_std : IsLat (intLoc F E v) (latLoc F (stdLattice E n) v) := by
  constructor
  · refine Submodule.fg_def.2 ⟨Set.range fun i => (Pi.single i 1 : Fin n → Fv F v ⊗[F] E), Set.finite_range _,
      le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      rintro y ⟨i, rfl⟩
      exact single_mem_latLoc_std i
    · intro y hy
      have h := mem_latLoc_stdLattice.1 hy
      rw [← sum_single_smul y]
      refine sum_mem fun i _ => ?_
      have : y i • (Pi.single i 1 : Fin n → Fv F v ⊗[F] E) =
          (⟨y i, h i⟩ : intLoc F E v) • (Pi.single i 1 : Fin n → Fv F v ⊗[F] E) := rfl
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  · rw [eq_top_iff]
    intro y _
    rw [← sum_single_smul y]
    exact sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (single_mem_latLoc_std i))

end GlobalTheory.CompanionTheory.KFin.AE

namespace GlobalTheory.CompanionTheory.KFin.AE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {v : HeightOneSpectrum (𝓞 F)}

theorem hR_self_eq (hσ : ∀ e, σ (σ e) = e) (hJ : ∀ i j, σ (J j i) = J i j) (x : Fin n → Fv F v ⊗[F] E) :
    hR (Fv F v) σ J x x = inclR (Fv F v) (2⁻¹ : E) * hR (Fv F v) σ J x x +
      sigR (Fv F v) σ (inclR (Fv F v) (2⁻¹ : E) * hR (Fv F v) σ J x x) := by
  have hs : σ (2⁻¹ : E) = 2⁻¹ := by rw [map_inv₀, map_ofNat]
  rw [map_mul, sigR_hR hσ hJ, sigR_inclR, hs, ← add_mul, ← map_add (f := _)]
  have : (2⁻¹ : E) + 2⁻¹ = 1 := by norm_num
  rw [this, map_one, one_mul]

theorem isMaxEven_isAdapted_std (hσ : ∀ e, σ (σ e) = e) (hJ : IsHermND σ J)
    (hJv : ∀ i j, inclR (Fv F v) (J i j) ∈ intLoc F E v) (hJi : ∀ i j, inclR (Fv F v) (J⁻¹ i j) ∈ intLoc F E v)
    (h2 : inclR (Fv F v) (2⁻¹ : E) ∈ intLoc F E v) {r : ℕ} (x y : Fin r → Fin n → Fv F v ⊗[F] E)
    (hx : ∀ i a, x i a ∈ intLoc F E v) (hy : ∀ i a, y i a ∈ intLoc F E v) :
    IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) (latLoc F (stdLattice E n) v) ∧
      IsAdapted (intLoc F E v) (hR (Fv F v) σ J) x y (latLoc F (stdLattice E n) v) := by
  have hint : ∀ a ∈ latLoc F (stdLattice E n) v, ∀ b ∈ latLoc F (stdLattice E n) v,
      hR (Fv F v) σ J a b ∈ intLoc F E v := fun a ha b hb =>
    hR_mem hJv (mem_latLoc_stdLattice.1 ha) (mem_latLoc_stdLattice.1 hb)
  refine ⟨⟨isLat_latLoc_std, ⟨hint, fun a ha => ⟨_, mul_mem h2 (hint a ha a ha), hR_self_eq hσ hJ.1 a⟩⟩, ?_⟩, ?_⟩
  · intro L' hL' hle z hz
    refine mem_latLoc_stdLattice.2 (mem_of_hR_single (σ := σ) hJ.2 hJi fun i => ?_)
    exact hL'.1 _ (hle (single_mem_latLoc_std i)) _ hz
  · intro z
    simp only [mem_latLoc_stdLattice]
    have hc : ∀ (c d : Fin r → Fv F v ⊗[F] E) (a : Fin n),
        (z - ∑ i, c i • x i - ∑ i, d i • y i) a = z a - ∑ i, c i * x i a - ∑ i, d i * y i a := by
      intro c d a
      simp [Finset.sum_apply]
    constructor
    · intro hz
      have h1 : ∀ i, hR (Fv F v) σ J (x i) z ∈ intLoc F E v := fun i => hR_mem hJv (hx i) hz
      have h3 : ∀ i, hR (Fv F v) σ J (y i) z ∈ intLoc F E v := fun i => hR_mem hJv (hy i) hz
      refine ⟨h1, h3, fun a => ?_⟩
      rw [hc]
      exact sub_mem (sub_mem (hz a) (sum_mem fun i _ => mul_mem (h3 i) (hx i a)))
        (sum_mem fun i _ => mul_mem (h1 i) (hy i a))
    · rintro ⟨h1, h3, hw⟩ a
      have := hw a
      rw [hc] at this
      have e : z a = (z a - ∑ i, hR (Fv F v) σ J (y i) z * x i a - ∑ i, hR (Fv F v) σ J (x i) z * y i a) +
          ∑ i, hR (Fv F v) σ J (y i) z * x i a + ∑ i, hR (Fv F v) σ J (x i) z * y i a := by ring
      rw [e]
      exact add_mem (add_mem this (sum_mem fun i _ => mul_mem (h3 i) (hx i a)))
        (sum_mem fun i _ => mul_mem (h1 i) (hy i a))

end GlobalTheory.CompanionTheory.KFin.AE

namespace GlobalTheory.CompanionTheory.KFin.AE

theorem exists_lattice_maxEven_adapted : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∃ (L : Submodule (𝓞 E) (Fin n → E)) (_ : Submodule.IsLattice E L), ∀ᶠ v in Filter.cofinite, IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) (latLoc F L v) ∧ IsAdapted (intLoc F E v) (hR (Fv F v) σ J) (colV v X) (colV v Y) (latLoc F L v) := by
  intro F E _ _ _ _ _ σ n J r X Y hcm hJ _hW
  have hσ : ∀ e, σ (σ e) = e := fun e => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  refine ⟨stdLattice E n, isLattice_stdLattice.toIsLattice, ?_⟩
  filter_upwards [Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_one_tmul_mem_intLoc (F := F) (J i j),
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => eventually_one_tmul_mem_intLoc (F := F) (J⁻¹ i j),
    eventually_one_tmul_mem_intLoc (F := F) (2⁻¹ : E),
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun a => eventually_one_tmul_mem_intLoc (F := F) (X a i),
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun a => eventually_one_tmul_mem_intLoc (F := F) (Y a i)]
    with v h1 h2 h3 h4 h5
  exact isMaxEven_isAdapted_std hσ hJ h1 h2 h3 (colV v X) (colV v Y) h4 h5

end GlobalTheory.CompanionTheory.KFin.AE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviBlockMemParabolic
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.BZPsiPG.QLevi

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ePG_true_eq (i t : ℕ) (b : Fin t) :
    ePG i t ⟨true, b⟩ = Fin.castSucc (Fin.natAdd i b) := by
  apply Fin.ext
  simp [ePG]

theorem ePG_false_eq (i t : ℕ) (a : Fin i) :
    ePG i t ⟨false, Fin.castSucc a⟩ = Fin.castSucc (Fin.castAdd t a) := by
  apply Fin.ext
  simp [ePG, finSumFinEquiv_symm_apply_castSucc]

theorem two_true_eq (i t : ℕ) (b : Fin t) :
    two (stdSum (rfl : i + t = i + t)) ⟨true, b⟩ = Fin.natAdd i b := by
  apply Fin.ext
  simp

theorem two_false_eq (i t : ℕ) (a : Fin i) :
    two (stdSum (rfl : i + t = i + t)) ⟨false, a⟩ = Fin.castAdd t a := by
  apply Fin.ext
  simp

theorem levi_entry (n : ℕ) (g : GL (Fin n) k) (a b : Fin n) :
    ((levi k n g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc a) (Fin.castSucc b) =
      (g : Matrix (Fin n) (Fin n) k) a b := by
  show glEmbMat k n (g : Matrix (Fin n) (Fin n) k) _ _ = _
  simp [glEmbMat]

theorem levi_entry_last_col (n : ℕ) (g : GL (Fin n) k) (a : Fin n) :
    ((levi k n g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.castSucc a) (Fin.last n) = 0 := by
  show glEmbMat k n (g : Matrix (Fin n) (Fin n) k) _ _ = _
  simp [glEmbMat]

theorem levi_entry_last_row (n : ℕ) (g : GL (Fin n) k) (b : Fin n) :
    ((levi k n g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.castSucc b) = 0 := by
  show glEmbMat k n (g : Matrix (Fin n) (Fin n) k) _ _ = _
  simp [glEmbMat]

theorem levi_entry_last (n : ℕ) (g : GL (Fin n) k) :
    ((levi k n g : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) (Fin.last n) = 1 := by
  show glEmbMat k n (g : Matrix (Fin n) (Fin n) k) _ _ = _
  simp [glEmbMat]

theorem levi_mem_HPG (i t : ℕ) (q : Qp k i t) : levi k (i + t) (q : GL (Fin (i + t)) k) ∈ HPG k i t := by
  show ((levi k (i + t) (q : GL (Fin (i + t)) k) : Mir k (i + t)) : GL (Fin (i + t + 1)) k) ∈ parab k (ePG i t)
  refine mem_parab_iff.2 ?_
  intro a c x y hac
  obtain ⟨rfl, rfl⟩ : a = true ∧ c = false := by
    revert hac; cases a <;> cases c <;> decide
  have hx : ePG i t ⟨true, x⟩ = Fin.castSucc (Fin.natAdd i (x : Fin t)) := ePG_true_eq i t x
  rw [hx]
  induction (y : Fin (i + 1)) using Fin.lastCases with
  | last =>
    rw [ePG_false_last]
    exact levi_entry_last_col _ _ _
  | cast y =>
    rw [ePG_false_eq, levi_entry]
    have := mem_parab_iff.1 q.2 true false (x : Fin t) (y : Fin i) (by decide)
    rwa [two_true_eq, two_false_eq] at this

theorem pgProj_levi (i t : ℕ) (q : Qp k i t) (h : levi k (i + t) (q : GL (Fin (i + t)) k) ∈ HPG k i t) :
    pgProj k i t ⟨_, h⟩ = (levi k i (qBlocks k i t q).1, (qBlocks k i t q).2) := by
  apply Prod.ext
  · apply Subtype.ext
    apply Units.ext
    ext a b
    show (leviProj k (ePG i t) (hpgIncl k i t ⟨_, h⟩) false : GL (Fin (i + 1)) k).val a b =
      ((levi k i (qBlocks k i t q).1 : GL (Fin (i + 1)) k) : Matrix (Fin (i + 1)) (Fin (i + 1)) k) a b
    rw [leviProj_apply]
    show ((levi k (i + t) (q : GL (Fin (i + t)) k) : GL (Fin (i + t + 1)) k) : Matrix _ _ k)
      (ePG i t ⟨false, a⟩) (ePG i t ⟨false, b⟩) = _
    induction a using Fin.lastCases with
    | last =>
      rw [ePG_false_last]
      induction b using Fin.lastCases with
      | last => rw [ePG_false_last, levi_entry_last, levi_entry_last]
      | cast b => rw [ePG_false_eq, levi_entry_last_row, levi_entry_last_row]
    | cast a =>
      rw [ePG_false_eq]
      induction b using Fin.lastCases with
      | last => rw [ePG_false_last, levi_entry_last_col, levi_entry_last_col]
      | cast b =>
        rw [ePG_false_eq, levi_entry, levi_entry]
        show _ = (leviProj k (two (stdSum (rfl : i + t = i + t))) q false : GL (Fin i) k).val a b
        rw [leviProj_apply, two_false_eq, two_false_eq]
  · apply Units.ext
    ext a b
    show (leviProj k (ePG i t) (hpgIncl k i t ⟨_, h⟩) true : GL (Fin t) k).val a b =
      (leviProj k (two (stdSum (rfl : i + t = i + t))) q true : GL (Fin t) k).val a b
    rw [leviProj_apply, leviProj_apply]
    show ((levi k (i + t) (q : GL (Fin (i + t)) k) : GL (Fin (i + t + 1)) k) : Matrix _ _ k)
      (ePG i t ⟨true, a⟩) (ePG i t ⟨true, b⟩) = _
    rw [ePG_true_eq, ePG_true_eq, levi_entry, two_true_eq, two_true_eq]

end GlobalTheory.CompanionTheory.BZPsiPG.QLevi

namespace GlobalTheory.CompanionTheory.BZPsiPG

theorem levi_Qp_mem_pgProj (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (i t : ℕ) (q : Qp k i t) :
    ∃ h : levi k (i + t) (q : GL (Fin (i + t)) k) ∈ HPG k i t,
      pgProj k i t ⟨_, h⟩ = (levi k i (qBlocks k i t q).1, (qBlocks k i t q).2) :=
  ⟨QLevi.levi_mem_HPG i t q, QLevi.pgProj_levi i t q _⟩

end GlobalTheory.CompanionTheory.BZPsiPG

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulVecMidBlockDecomp
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG

theorem qp_mulVec_midV_exists_top (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (i t : ℕ) (q : Qp k i t) (v : Fin t → k) :
    ∃ x : Fin i → k, ((q : GL (Fin (i + t)) k) : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec (midV k i t v) =
      topV k i t x + midV k i t ((((qBlocks k i t q).2 : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec v) := by
  refine ⟨fun r => ((q : GL (Fin (i + t)) k) : Matrix (Fin (i + t)) (Fin (i + t)) k).mulVec
    (GlobalTheory.CompanionTheory.BZPsiPG.midV k i t v) (Fin.castAdd t r), ?_⟩
  rw [GlobalTheory.CompanionTheory.BZPsiPG.topV_add_midV]
  funext r
  refine Fin.addCases (fun a => ?_) (fun b => ?_) r
  · rw [Fin.append_left]
  · rw [Fin.append_right]
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_add, GlobalTheory.CompanionTheory.BZPsiPG.midV, Fin.append_left,
      Fin.append_right, Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add]
    rfl

end GlobalTheory.CompanionTheory.BZPsiPG
end

