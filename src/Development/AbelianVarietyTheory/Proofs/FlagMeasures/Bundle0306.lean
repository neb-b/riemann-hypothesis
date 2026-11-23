module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelicUnitaryCongruenceTopology
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0244
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0247
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0279
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0001
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.NoncompactGeneratorRaisesPfil
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSmoothCompactSupportFixLowestKType
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsContDiffExtension
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KTypeGeneratedByHighest
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0142
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EmbeddingTraceSumAlt.NormUnitsOfCalculation

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RightConvolutionOperatorAeEqIntegralAdelic
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.ConvKernel

section General

variable {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {ν : Measure X} {μ : Measure Y}

theorem integrable_prod_restrict [SFinite ν] [SFinite μ] (K : X → Y → ℂ)
    (hK : AEStronglyMeasurable (fun p : X × Y => K p.1 p.2) (ν.prod μ))
    (r : Y → Lp ℂ 2 ν) (hr : ∀ g, (r g : X → ℂ) =ᵐ[ν] fun x => K x g) (C : ℝ)
    (hC : ∀ g, ‖r g‖ ≤ C) (φ : Y → ℂ) (hφ : Integrable φ μ) (s : Set X) (hs : ν s < ⊤) :
    Integrable (fun p : X × Y => φ p.2 * K p.1 p.2) ((ν.restrict s).prod μ) := by
  have hK' : AEStronglyMeasurable (fun p : X × Y => K p.1 p.2) ((ν.restrict s).prod μ) :=
    hK.mono_ac (Measure.AbsolutelyContinuous.prod
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self) Measure.AbsolutelyContinuous.rfl)
  have hm : AEStronglyMeasurable (fun p : X × Y => φ p.2 * K p.1 p.2) ((ν.restrict s).prod μ) :=
    (hφ.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd).mul hK'
  refine ⟨hm, ?_⟩
  set M : ENNReal := ENNReal.ofReal C * (ν s) ^ (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal)
    with hM
  have hMfin : M ≠ ⊤ := by
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    refine ENNReal.rpow_ne_top_of_nonneg ?_ hs.ne
    norm_num
  have hb : ∀ g, ∫⁻ x, ‖K x g‖ₑ ∂(ν.restrict s) ≤ M := by
    intro g
    have e1 : ∫⁻ x, ‖K x g‖ₑ ∂(ν.restrict s) = eLpNorm (r g : X → ℂ) 1 (ν.restrict s) := by
      rw [eLpNorm_one_eq_lintegral_eNorm (Lp.aestronglyMeasurable (r g)).restrict]
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_of_ae (s := s) (hr g)] with x hx
      rw [hx]
    have e2 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := ν.restrict s) (p := 1) (q := 2)
      (f := (r g : X → ℂ)) (by norm_num) (Lp.aestronglyMeasurable (r g)).restrict
    rw [Measure.restrict_apply_univ] at e2
    rw [e1]
    refine e2.trans ?_
    refine mul_le_mul' ?_ le_rfl
    refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
    have h3 := hC g
    rw [Lp.norm_def] at h3
    rw [← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top (r g))]
    exact ENNReal.ofReal_le_ofReal h3
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod_symm _ hm.enorm]
  calc ∫⁻ g, ∫⁻ x, ‖φ g * K x g‖ₑ ∂(ν.restrict s) ∂μ ≤ ∫⁻ g, ‖φ g‖ₑ * M ∂μ := by
        refine lintegral_mono fun g => ?_
        simp only [enorm_mul]
        rw [lintegral_const_mul' _ _ enorm_ne_top]
        exact mul_le_mul' le_rfl (hb g)
    _ = (∫⁻ g, ‖φ g‖ₑ ∂μ) * M := lintegral_mul_const' _ _ hMfin
    _ < ⊤ := ENNReal.mul_lt_top hφ.2 hMfin.lt_top

theorem weak_integral_ae_eq [SigmaFinite ν] [SFinite μ] (K : X → Y → ℂ)
    (hK : AEStronglyMeasurable (fun p : X × Y => K p.1 p.2) (ν.prod μ))
    (r : Y → Lp ℂ 2 ν) (hr : ∀ g, (r g : X → ℂ) =ᵐ[ν] fun x => K x g) (C : ℝ)
    (hC : ∀ g, ‖r g‖ ≤ C) (φ : Y → ℂ) (hφ : Integrable φ μ) (t : Lp ℂ 2 ν)
    (ht : ∀ u : Lp ℂ 2 ν, ⟪u, t⟫_ℂ = ∫ g, φ g * ⟪u, r g⟫_ℂ ∂μ) :
    (∀ᵐ x ∂ν, Integrable (fun g => φ g * K x g) μ) ∧
      (t : X → ℂ) =ᵐ[ν] fun x => ∫ g, φ g * K x g ∂μ := by
  have hI := integrable_prod_restrict K hK r hr C hC φ hφ
  refine ⟨?_, ?_⟩
  · refine ae_of_forall_measure_lt_top_ae_restrict _ fun s _ hs => ?_
    exact (hI s hs).prod_right_ae
  · refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun s _ hs => ?_) (fun s _ hs => ?_)
      (fun s hsm hs => ?_)
    · exact integrableOn_Lp_of_measure_ne_top t (by norm_num) hs.ne
    · exact (hI s hs).integral_prod_left
    · have h := ht (indicatorConstLp 2 hsm hs.ne (1 : ℂ))
      simp only [L2.inner_indicatorConstLp_one] at h
      rw [h, integral_integral_swap (f := fun x g => φ g * K x g) (hI s hs)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      simp only
      rw [integral_const_mul]
      congr 1
      exact integral_congr_ae (ae_restrict_of_ae (hr g))

end General

theorem rconv_eq_integral : ∀ (B : RowsAut) (φ : B.I.GA → ℂ) (T : B.I.L2 B.μf B.fund →L[ℂ] B.I.L2 B.μf B.fund), B.I.IsRConv B.μf B.fund B.R φ T → ∀ y : B.I.L2 B.μf B.fund, (∀ᵐ x ∂((B.I.muA B.μf).restrict B.fund), Integrable (fun g => φ g * B.I.ext y (x * g)) (B.I.muA B.μf)) ∧ (T y : B.I.GA → ℂ) =ᵐ[(B.I.muA B.μf).restrict B.fund] fun x => ∫ g, φ g * B.I.ext y (x * g) ∂(B.I.muA B.μf) := by
  intro B φ T hT y
  obtain ⟨hT2, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology B.I
  obtain ⟨hl, -⟩ := _root_.GlobalTheory.AdelicUnimod.adelic_unimodular B.I B.μf
  obtain ⟨-, -, hn, -, hext⟩ := _root_.GlobalTheory.RightRegFund.rightReg_unitary_continuous B
  have : BorelSpace B.I.GA := inferInstance
  have : (B.I.muA B.μf).IsMulLeftInvariant := ⟨hl⟩
  have : SigmaFinite (B.I.muA B.μf) := by
    unfold AutInst.muA; infer_instance
  have hq : Measure.QuasiMeasurePreserving (fun p : B.I.GA × B.I.GA => p.1 * p.2)
      (((B.I.muA B.μf).restrict B.fund).prod (B.I.muA B.μf)) (B.I.muA B.μf) :=
    Measure.quasiMeasurePreserving_snd.comp
      (measurePreserving_prod_mul ((B.I.muA B.μf).restrict B.fund)
        (B.I.muA B.μf)).quasiMeasurePreserving
  exact weak_integral_ae_eq (fun x g => B.I.ext y (x * g))
    ((hext y).2.comp_quasiMeasurePreserving hq) (fun g => B.R g y) (fun g => B.R_spec g y) ‖y‖
    (fun g => (hn g y).le) φ hT.1 (T y) (fun u => hT.2 u y)

end GlobalTheory.ConvKernel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SkewLatticeInverseDifferentPowCovolume
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.SkewVol
theorem dom_of_basis {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {ι : Type} [Finite ι]
    (b : Module.Basis ι ℝ W) (v : W) :
    ∃! l, l ∈ (Submodule.span ℤ (Set.range b) : Set W) ∧ v + l ∈ ZSpan.fundamentalDomain b := by
  obtain ⟨⟨l, hl⟩, h1, h2⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b v
  refine ⟨l, ⟨hl, by simpa [Submodule.vadd_def, add_comm] using h1⟩, ?_⟩
  rintro l' ⟨hl', h'⟩
  have := h2 ⟨l', hl'⟩ (by simpa [Submodule.vadd_def, add_comm] using h')
  simpa using congrArg Subtype.val this

theorem dInv_ne_zero (K : Type) [Field K] [NumberField K] (j : ℕ) : GlobalTheory.SgGlob.dInv K j ≠ 0 := by
  unfold GlobalTheory.SgGlob.dInv
  refine pow_ne_zero _ (inv_ne_zero ?_)
  exact FractionalIdeal.coeIdeal_ne_zero.2 differentIdeal_ne_bot

theorem skew_covol_dInv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → ∀ (t : ℕ) (c : ℝ), 0 < c → HasDom volume (skewLat (σ : E →+* E) (GlobalTheory.SgGlob.dInv E (2 * t)) c : Set (InfinitePlace E → ℝ)) (ENNReal.ofReal (|(NumberField.discr F : ℝ)| ^ (1 / 2 - 2 * (t : ℝ)) * c ^ Fintype.card (InfinitePlace E))) := by
  intro F E _ _ _ _ _ σ hCM hU t c hc
  have hTC : IsTotallyComplex E := hCM.2.1
  have hTR : IsTotallyReal F := hCM.1
  have hσw : ∀ (w : InfinitePlace E) (x : E), w.embedding (σ x) = star (w.embedding x) :=
    fun w x => hCM.2.2.2 w.embedding x
  have hre : ∀ x : E, reV (σ x) = reV x := fun x => funext fun w => by simp [reV, hσw]
  have him : ∀ x : E, imV (σ x) = -imV x := fun x => funext fun w => by simp [imV, hσw]
  obtain ⟨e, he, hex⟩ := _root_.GlobalTheory.SnMass.SkewVol.mixedSpace_reIm_coords E hTC
  obtain ⟨ι, _, b, hbs, hbv⟩ := GlobalTheory.T.fractionalIdeal_basis_transport_measurePreserving E volume e he (Units.mk0 (GlobalTheory.SgGlob.dInv E (2 * t)) (dInv_ne_zero E _))
  obtain ⟨e1, he1, he1x⟩ := _root_.GlobalTheory.SnMass.ReCoords.mixedSpace_reCoords F E σ hCM
  obtain ⟨ι1, _, b1, hb1s, hb1v⟩ :=
    GlobalTheory.T.fractionalIdeal_basis_transport_measurePreserving F volume e1 he1 (Units.mk0 (GlobalTheory.SgGlob.dInv F (2 * t)) (dInv_ne_zero F _))
  simp only [Units.val_mk0] at hbs hbv hb1s hb1v
  set Λ := Submodule.span ℤ (Set.range b) with hΛdef
  have hΛ : ∀ p, p ∈ Λ ↔ ∃ x ∈ GlobalTheory.SgGlob.dInv E (2 * t), (reV x, imV x) = p := by
    intro p
    rw [← SetLike.mem_coe, hbs]
    simp [hex]
  have hL1 : ∀ a, a ∈ (Submodule.span ℤ (Set.range b1) : Set (InfinitePlace E → ℝ)) ↔
      (a, (0 : InfinitePlace E → ℝ)) ∈ Λ := by
    intro a
    rw [hb1s, hΛ]
    simp only [Set.mem_image, Set.mem_setOf_eq, he1x, Prod.mk.injEq]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h := (_root_.GlobalTheory.SnMass.SkewVol.mem_dInv_imV_iff F E σ hCM hU (2 * t) (algebraMap F E y)).2 ⟨y, hy, rfl⟩
      exact ⟨_, h.1, rfl, h.2⟩
    · rintro ⟨x, hx, rfl, h0⟩
      obtain ⟨y, hy, rfl⟩ := (_root_.GlobalTheory.SnMass.SkewVol.mem_dInv_imV_iff F E σ hCM hU _ _).1 ⟨hx, h0⟩
      exact ⟨y, hy, rfl⟩
  have hD1 : ∀ a, ∃! l, l ∈ {a : InfinitePlace E → ℝ | (a, (0 : InfinitePlace E → ℝ)) ∈ Λ.toAddSubgroup} ∧
      a + l ∈ ZSpan.fundamentalDomain b1 := by
    intro a
    obtain ⟨l, hl, hu⟩ := dom_of_basis b1 a
    exact ⟨l, ⟨(hL1 l).1 hl.1, hl.2⟩, fun l' hl' => hu l' ⟨(hL1 l').2 hl'.1, hl'.2⟩⟩
  have h2 : ∀ a y, (a, y) ∈ Λ → ((0 : InfinitePlace E → ℝ), (2 : ℝ) • y) ∈ Λ := by
    intro a y hay
    obtain ⟨x, hx, hxe⟩ := (hΛ _).1 hay
    rw [Prod.mk.injEq] at hxe
    refine (hΛ _).2 ⟨x - σ x, Submodule.sub_mem (GlobalTheory.SgGlob.dInv E (2 * t) : Submodule (𝓞 E) E) hx (_root_.GlobalTheory.SnMass.VolN.conj_mem_dInv F E σ hCM _ x hx), ?_⟩
    have h1 : reV (x - σ x) = reV x - reV (σ x) := funext fun w => by simp [reV]
    have h1' : imV (x - σ x) = imV x - imV (σ x) := funext fun w => by simp [imV]
    rw [h1, h1', hre, him, ← hxe.2]
    refine Prod.ext ?_ ?_
    · simp
    · funext w; simp; ring
  have hsp : Submodule.span ℝ (Λ : Set ((InfinitePlace E → ℝ) × (InfinitePlace E → ℝ))) = ⊤ := by
    rw [hΛdef, Submodule.span_span_of_tower, b.span_eq]
  obtain ⟨D2, hD2m, hD2⟩ := _root_.GlobalTheory.exists_fundamentalDomain_snd_of_two_smul_mem Λ hsp h2
  have hprod := _root_.GlobalTheory.prod_fundamentalDomain_of_extension Λ.toAddSubgroup _ D2 hD1 hD2
  have heq := _root_.GlobalTheory.addFundamentalDomains_measure_eq ((volume : Measure (InfinitePlace E → ℝ)).prod (volume : Measure (InfinitePlace E → ℝ))) Λ _ _ ((ZSpan.fundamentalDomain_measurableSet b1).prod hD2m)
    (ZSpan.fundamentalDomain_measurableSet b) hprod (dom_of_basis b)
  rw [Measure.prod_prod, ← Measure.volume_eq_prod, hbv, hb1v] at heq
  have hL2 : ∀ y, (∃ a, (a, y) ∈ Λ) ↔ ∃ x ∈ GlobalTheory.SgGlob.dInv E (2 * t), imV x = y := by
    intro y
    simp only [hΛ, Prod.mk.injEq]
    constructor
    · rintro ⟨a, x, hx, -, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, x, hx, rfl, rfl⟩
  obtain ⟨θ, hθ⟩ := _root_.GlobalTheory.exists_integer_add_conj_eq_one_of_formallyUnramified F E σ hCM hU
  have hfin := _root_.GlobalTheory.SnMass.SkewDom.skewDom F E σ hCM (GlobalTheory.SgGlob.dInv E (2 * t)) (fun x hx => _root_.GlobalTheory.SnMass.VolN.conj_mem_dInv F E σ hCM _ x hx) θ hθ c hc D2 _
    hD2m (fun y => by simpa only [Set.mem_setOf_eq, hL2] using hD2 y) rfl
  have hd : (1 : ℝ) ≤ |(discr F : ℝ)| := by
    have h := Int.one_le_abs (discr_ne_zero F)
    rw [← Int.cast_abs]
    exact_mod_cast h
  have hnc : InfinitePlace.nrComplexPlaces E = Fintype.card (InfinitePlace E) := by
    have h := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces E
    rw [IsTotallyComplex.nrRealPlaces_eq_zero E, zero_add] at h
    exact h.symm
  have hnr : InfinitePlace.nrComplexPlaces F = 0 := IsTotallyReal.nrComplexPlaces_eq_zero F
  rw [_root_.GlobalTheory.SnMass.VolN.absNorm_dInv_eq_abs_discr_pow_inv, _root_.GlobalTheory.SnMass.VolN.absNorm_dInv_eq_abs_discr_pow_inv, _root_.GlobalTheory.SnMass.VolN.abs_discr_eq_abs_discr_sq_of_unramified F E σ hCM hU, hnc, hnr] at heq
  rw [_root_.GlobalTheory.covolQuotient_arith _ c _ t _ hd hc heq.symm] at hfin
  exact hfin

end GlobalTheory.SnMass.SkewVol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothOfMemLowKSub
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.StepBoundOneRep

open GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem stepConst_nonneg (n : ℕ) (b : ℝ) (P : ℕ) : 0 ≤ stepConst n b P := by
  have h1 : 0 ≤ (n : ℝ) ^ (1 / 2 : ℝ) * b ^ 2 :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _) (sq_nonneg b)
  have h2 : 0 ≤ 3 / 2 * (n : ℝ) ^ (3 / 2 : ℝ) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have h3 : 0 ≤ 3 * (P : ℝ) := mul_nonneg (by norm_num) (Nat.cast_nonneg P)
  simp only [stepConst]
  linarith

theorem stepSpace_le {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (Vs : Submodule ℂ H)
    (E : Fin n → Fin n → Module.End ℂ Vs) (hE : GlRel E)
    (hd : ∀ X, inG ε X → ∀ u : Vs, HasDerivAt (orbit σ X u) ((∑ a, ∑ b, X a b • E a b u : Vs) : H) 0)
    (u : Vs) (hu : (kSpan ε E u).map Vs.subtype = lowKSub ε lam σ) (P : ℕ) :
    stepSpace ε lam σ P ≤ (pfil ε E u P).map Vs.subtype := by
  have key : ∀ l : List (Matrix (Fin n) (Fin n) ℂ), (∀ X ∈ l, inG ε X) → ∀ w ∈ lowKSub ε lam σ,
      ∃ x : Vs, x ∈ pfil ε E u l.length ∧ (x : H) = dWord σ l w := by
    intro l
    induction l with
    | nil =>
      intro _ w hw
      rw [← hu] at hw
      obtain ⟨x, hx, hxw⟩ := Submodule.mem_map.mp hw
      refine ⟨x, ?_, ?_⟩
      · rw [List.length_nil, poincare_filtration_zero]
        exact hx
      · exact hxw
    | cons X l ih =>
      intro hl w hw
      obtain ⟨x, hx, hxe⟩ := ih (fun Y hY => hl Y (List.mem_cons_of_mem _ hY)) w hw
      refine ⟨∑ a, ∑ b, X a b • E a b x, ?_, ?_⟩
      · exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
          Submodule.smul_mem _ _ (poincare_filtration_succ ε E u hE _ a b x hx)
      · change _ = dAct σ X (dWord σ l w)
        rw [← hxe, dAct, (hd X (hl X List.mem_cons_self) x).deriv]
  rw [stepSpace, Submodule.span_le]
  rintro v ⟨l, w, hl, hX, hw, rfl⟩
  obtain ⟨x, hx, hxe⟩ := key l hX w hw
  exact Submodule.mem_map.mpr ⟨x, pfil_monotone_in_length ε E u hl hx, hxe⟩

theorem smooth_of_mem_lowKSub {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ) {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hU : IsURepOn (UJset ε) σ)
    (hS : IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ)) (v : H) (hv : v ∈ lowKSub ε lam σ) :
    SmoothOnGV ε (fun g => σ g v) := by
  obtain ⟨α, hα, hαc, hfix⟩ := exists_smooth_fix_lowKSub n ε lam H σ hU hS
  have hcu : Continuous (fun g : UJ ε => umat g) := Units.continuous_val.comp continuous_subtype_val
  have hcα : Continuous (fun g : UJ ε => α (umat g)) := by
    refine continuous_iff_continuousAt.mpr fun g₀ => ?_
    obtain ⟨U, F, hUo, hgU, hF, hFα⟩ := hα (umat g₀) g₀.2
    have hev : (fun g : UJ ε => F (umat g)) =ᶠ[nhds g₀] (fun g : UJ ε => α (umat g)) := by
      filter_upwards [hcu.continuousAt.preimage_mem_nhds (hUo.mem_nhds hgU)] with g hg
      exact (hFα _ hg g.2).symm
    exact ((hF.continuousOn.continuousAt (hUo.mem_nhds hgU)).comp hcu.continuousAt).congr hev
  have hcσ : Continuous (fun g : UJ ε => σ (umat g) v) :=
    (hU.2.2 v).comp_continuous hcu fun g => g.2
  have hint : Integrable (fun g : UJ ε => α (umat g) • σ (umat g) v) (muG ε) :=
    (hcα.smul hcσ).integrable_of_hasCompactSupport (hαc.smul_right)
  have hv : v = ∫ g : UJ ε, α (umat g) • σ (umat g) v ∂(muG ε) := by
    refine ext_inner_left ℂ fun y => ?_
    rw [← integral_inner hint y, ← hfix v hv y]
    simp only [inner_smul_right]
  have hsm := GlobalTheory.GardingSmooth.garding_smooth n ε H σ hU α hα hαc v
  rw [← hv] at hsm
  exact hsm

theorem stepBound_of_eigen : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ) (b : ℝ), IsURepOn (UJset ε) σ → IsKTypeOf ε σ (lowK ε lam) (lowKSub ε lam σ) → (∀ s ∈ lowKSub ε lam σ, ∀ y : H, IsZEigen ε (fun a => (lam a : ℂ)) (fun g => ⟪y, σ g s⟫_ℂ)) → (∀ a, |lam a| ≤ b ^ 2) → (∀ P : ℕ, FiniteDimensional ℂ (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P) ∧ (∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P, GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.IsDiffVec ε σ w) ∧ (∀ F : Fin (n ^ 2) → Matrix (Fin n) (Fin n) ℂ, GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.IsONFamily ε F → ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P, ∑ i, ‖GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ (F i) w‖ ^ 2 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P ^ 2 * ‖w‖ ^ 2) ∧ ∀ X, Formalism.REAL.inG ε X → ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P, ‖GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X w‖ ≤ Real.sqrt (Formalism.REAL.hs X) * GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P * ‖w‖) := by
  intro n ε H _ _ _ σ lam b hU hS heig hb
  obtain ⟨Vs, E, hVs, hGl, hUn, hD, hEq⟩ := SmoothVecMod.smoothVec_unitary_module n ε H σ hU
  have hlow : lowKSub ε lam σ ≤ Vs := fun v hv =>
    (hVs v).mpr (smooth_of_mem_lowKSub ε lam σ hU hS v hv)
  obtain ⟨u, -, hKu, hmap, hfd⟩ := GlobalTheory.KTypeHighest.kType_generated_by_highest n ε H σ Vs E hU
    ⟨hVs, hGl, hUn, hD, hEq⟩ _ (lowKSub ε lam σ) hS hlow
  have huS : (u : H) ∈ lowKSub ε lam σ := by
    rw [← hmap]
    exact Submodule.mem_map_of_mem (mem_kSpan_self' ε E u)
  have hCas := GlobalTheory.CasimirEigen.cas_eq_of_isZEigen n ε H σ Vs E lam hU ⟨hVs, hGl, hUn, hD, hEq⟩ u
    (heig _ huS)
  have hKind : KindA ε E lam u := ⟨hKu, hCas, hfd⟩
  have hAlg := GlobalTheory.algebraic_step_bound Vs n ε E lam u b hGl hUn hKind hb
  have hC : ∀ P : ℕ, 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P := fun P => stepConst_nonneg n b P
  have hmem : ∀ (P : ℕ) (w : H), w ∈ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepSpace ε lam σ P →
      ∃ x : Vs, x ∈ pfil ε E u P ∧ (x : H) = w := fun P w hw =>
    Submodule.mem_map.mp (stepSpace_le ε lam σ Vs E hGl (fun X hX x => hD X hX x) u hmap P hw)
  have hact : ∀ X, inG ε X → ∀ x : Vs,
      GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X (x : H) = ((∑ a, ∑ c, X a c • E a c x : Vs) : H) := fun X hX x => by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct, (hD X hX x).deriv]
  have hbound : ∀ P : ℕ, ∀ x ∈ pfil ε E u P,
      ∑ a, ∑ c, ‖E a c x‖ ^ 2 ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P ^ 2 * ‖x‖ ^ 2 := hAlg
  intro P
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : FiniteDimensional ℂ (pfil ε E u P) := pfil_finite_dimensional ε E u hfd P
    exact Submodule.finiteDimensional_of_le
      (stepSpace_le ε lam σ Vs E hGl (fun X hX x => hD X hX x) u hmap P)
  · intro w hw
    obtain ⟨x, -, rfl⟩ := hmem P w hw
    exact fun X hX => (hD X hX x).differentiableAt
  · intro F hF w hw
    obtain ⟨x, hx, rfl⟩ := hmem P w hw
    have hON := (GlobalTheory.OnbSum.onb_sum n ε Vs (fun a c => E a c x)).1 F hF
    calc ∑ i, ‖GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ (F i) (x : H)‖ ^ 2
        = ∑ i, ‖∑ a, ∑ c, F i a c • E a c x‖ ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hact (F i) (hF.1 i) x]
          rfl
      _ = ∑ a, ∑ c, ‖E a c x‖ ^ 2 := hON
      _ ≤ GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P ^ 2 * ‖x‖ ^ 2 := hbound P x hx
      _ = GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P ^ 2 * ‖(x : H)‖ ^ 2 := rfl
  · intro X hX w hw
    obtain ⟨x, hx, rfl⟩ := hmem P w hw
    have hsq := (GlobalTheory.OnbSum.onb_sum n ε Vs (fun a c => E a c x)).2 X
    have hhs : 0 ≤ Formalism.REAL.hs X := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    have hnorm : ‖GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X (x : H)‖ = ‖∑ a, ∑ c, X a c • E a c x‖ := by
      rw [hact X hX x]
      rfl
    have h2 : ‖GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X (x : H)‖ ^ 2 ≤
        (Real.sqrt (Formalism.REAL.hs X) * GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P * ‖(x : H)‖) ^ 2 := by
      rw [hnorm, mul_pow, mul_pow, Real.sq_sqrt hhs]
      calc ‖∑ a, ∑ c, X a c • E a c x‖ ^ 2 ≤ Formalism.REAL.hs X * ∑ a, ∑ c, ‖E a c x‖ ^ 2 := hsq
        _ ≤ Formalism.REAL.hs X * (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P ^ 2 * ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (hbound P x hx) hhs
        _ = Formalism.REAL.hs X * GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P ^ 2 * ‖(x : H)‖ ^ 2 := by
          rw [mul_assoc]
          rfl
    have hr : 0 ≤ Real.sqrt (Formalism.REAL.hs X) * GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.stepConst n b P * ‖(x : H)‖ :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hC P)) (norm_nonneg _)
    nlinarith [norm_nonneg (GlobalTheory.IndefiniteRowSideFullHecke.OrbitDifferenceSpace.dAct σ X (x : H))]

end GlobalTheory.StepBoundOneRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportedFiniteCharacterInverseExpTrace
section
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St GlobalTheory.St.G
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.St.G

theorem trace_cm_eq_add_star {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E]
    [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (x : E) :
    algebraMap F E (Algebra.trace F E x) = x + star x := by
  have : FiniteDimensional F E := Module.finite_of_finrank_eq_succ hc.deg2
  have : Algebra.IsQuadraticExtension F E := ⟨hc.deg2⟩
  classical
  let s : E ≃ₐ[F] E := AlgEquiv.ofAlgHom hc.sig hc.sig
    (by ext y; simp [Formalism.BasicNotions.CMData.sig]) (by ext y; simp [Formalism.BasicNotions.CMData.sig])
  have hs : ∀ y, s y = star y := fun y => rfl
  have hne : (1 : E ≃ₐ[F] E) ≠ s := by
    intro h
    have hall : ∀ y : E, y ∈ (algebraMap F E).range := fun y => (hc.fixed y).1 (by
      rw [← hs, ← h]; rfl)
    have h1 : Module.finrank F E = 1 := by
      apply finrank_eq_one (1 : E) one_ne_zero
      intro w
      obtain ⟨a, ha⟩ := hall w
      exact ⟨a, by rw [Algebra.smul_def, mul_one, ha]⟩
    rw [hc.deg2] at h1
    omega
  have hcard : Fintype.card (E ≃ₐ[F] E) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hc.deg2]
  have huniv : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, s} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hne, hcard]
  rw [trace_eq_sum_automorphisms, huniv, Finset.sum_pair hne, hs]
  rfl

theorem psiEinf_eq_exp_trace (I : Formalism.MainNotions.S.AutInst) (y : I.E) :
    psiEinf I y = Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ I.E y : ℚ) : ℂ)) := by
  have := I.cm.totReal
  rw [show psiEinf I y = PI.ScPsiExists.psiEinf I y from rfl, PI.ScPsiExists.UnitaryGroupMassFormula.psiEinf_eq,
    PI.ScPsiExists.UnitaryGroupMassFormula.sHom_coe]
  have h2 : ∀ v, I.φ v y + star (I.φ v y) =
      v.embedding (PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed y) := by
    intro v
    rw [← I.φ_over, PI.ScPsiExists.UnitaryGroupMassFormula.tau_apply, map_add (f := _), I.cm.cmUnram.2.1 (I.φ v) y]
    rfl
  have h3 : PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed y = Algebra.trace I.F I.E y := by
    apply (algebraMap I.F I.E).injective
    rw [PI.ScPsiExists.UnitaryGroupMassFormula.tau_apply, trace_cm_eq_add_star I.cm]
  rw [Finset.sum_congr rfl (fun v _ => h2 v), PI.ScPsiExists.UnitaryGroupMassFormula.sum_embedding_eq_trace, h3,
    Algebra.trace_trace]
  rfl

theorem psiEf_transport_rat : ∀ (D : D7) (X : HidaSetting D) (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F), IsAdeleIso X ιA → ∀ x : D.host.E, X.psiEf (ιA.symm (Formalism.UG.inclE (F := D.host.F) (Ad D.host.F) x)) * Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ D.host.E x : ℚ) : ℂ)) = 1 := by
  intro D X ιA hA x
  have h1 : ιA.symm (Formalism.UG.inclE (F := D.host.F) (Ad D.host.F) x) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm x) := by
    rw [RingEquiv.symm_apply_eq, hA.1 (X.ιE.symm x), X.ιE.apply_symm_apply]
  have htr : Algebra.trace ℚ D.host.E x = Algebra.trace ℚ X.B.I.E (X.ιE.symm x) := by
    conv_lhs => rw [← X.ιE.apply_symm_apply x]
    exact Algebra.trace_eq_of_algEquiv X.ιE.toRatAlgEquiv (X.ιE.symm x)
  rw [h1, htr, ← psiEinf_eq_exp_trace]
  exact X.psiEf_rat (X.ιE.symm x)

end GlobalTheory.St.G

end
end

