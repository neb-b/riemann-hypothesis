module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
public import GroundTheory.LocalFields.LocalFourier
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalFieldSelfdualMeasureExists
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0059
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0060
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import CompanionTheory.AutomorphicTheory.ThetaDilations.FstarDil
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0044
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicBoxesCompactExhaust
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RationalGramAdelicCompactFinite
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0056
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0058
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0051
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0042
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SelfDualStandardMeasures
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.SDOne
open GroundTheory.Global GroundTheory.LocalField

variable (F : Type) [Field F] [NumberField F]

theorem psiV_std (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) :
    psiV F (Circle.coeHom.compAddChar (adelicChar F)) v y = ((localAdelicChar F v y : Circle) : ℂ) := by
  classical
  show ((adelicChar F (pairA F 0 (singleV F v y)) : Circle) : ℂ) = ((adelicChar F (finitePlaceIncl v y) : Circle) : ℂ)
  congr 2

theorem coe_integers_eq (v : HeightOneSpectrum (𝓞 F)) :
    ((ValuativeRel.valuation (Fv F v)).integer : Set (Fv F v)) = (v.adicCompletionIntegers F : Set (Fv F v)) := by
  rw [show ((ValuativeRel.valuation (Fv F v)).integer : Set (Fv F v)) = (valBall (Fv F v) 0 : Set (Fv F v)) from coe_valBall_zero.symm]
  ext x
  show x ∈ valBall (Fv F v) 0 ↔ x ∈ v.adicCompletionIntegers F
  rw [mem_valBall_iff_valued, HeightOneSpectrum.mem_adicCompletionIntegers]
  simp

noncomputable def cV (v : HeightOneSpectrum (𝓞 F)) : ℝ≥0 :=
  (Ideal.absNorm v.asIdeal : ℝ≥0) ^ (((-differentExp v : ℤ) : ℝ) / 2)

theorem smul_eq_selfDualMeasure (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)) (h : IsStdV v lam) :
    cV F v • lam = GroundTheory.LocalField.selfDualMeasure (localAdelicChar F v) := by
  obtain ⟨hH, h1⟩ := h
  have e := eq_smul_haarIntegers lam
  rw [coe_integers_eq F v, h1, one_smul] at e
  rw [e, GroundTheory.LocalField.selfDualMeasure, addCharConductor_localAdelicChar, residueCard_adicCompletion]
  rfl

theorem selfDual_std : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (laminf : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf laminf → (∀ v, IsStdV v (lam v)) → ∃ ψ, IsCharAF F ψ ∧ ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (SelfDual (cinf • laminf) (fun s t => psiInf F ψ (s * t))) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (SelfDual (c v • lam v) (fun s t => psiV F ψ v (s * t))) := by
  intro F _ _ hF laminf lam hinf hlam
  refine ⟨Circle.coeHom.compAddChar (adelicChar F), ?_, Real.toNNReal (Real.sqrt |(discr F : ℝ)|), cV F, ?_, GlobalTheory.T.archimedean_selfdual_measure_discriminant_scaled F hF laminf hinf, fun v => ?_⟩
  · refine ⟨continuous_subtype_val.comp (continuous_adelicChar (K := F)), fun x => Circle.norm_coe _, fun a => ?_, ?_⟩
    · show ((adelicChar F _ : Circle) : ℂ) = 1
      rw [adelicChar_algebraMap]
      rfl
    · by_contra h
      push Not at h
      apply adelicChar_ne_one (K := F)
      ext x
      exact h x
  · exact _root_.GlobalTheory.CompanionTheory.SW.SelfDual.sqrt_discr_mul_finprod_different F
  · rw [smul_eq_selfDualMeasure F v (lam v) (hlam v)]
    simp only [psiV_std]
    exact _root_.GlobalTheory.CompanionTheory.SW.selfDual_selfDualMeasure _ _ (continuous_localAdelicChar v) (localAdelicChar_ne_one v)

end GlobalTheory.CompanionTheory.SW.SDOne
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaFunctionCuspExpansion
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Core.EiInv

theorem ei_inv : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → 3 ≤ M → ∀ φ : (ι → A F) → ℂ, SB φ → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → (∀ b : F, eis ψ lf B ρ P (opU ψ (hf F) (Bf B) (algebraMap F (A F) b) φ) (fun w => τ w + (ρ w b : ℝ)) = eis ψ lf B ρ P φ τ) ∧ (∀ a : F, a ≠ 0 → eis ψ lf B ρ P (opD 1 (algebraMap F (A F) a) φ) (fun w => ((ρ w a : ℝ) : ℂ) ^ 2 * τ w) = eis ψ lf B ρ P φ τ) ∧ (cG B ρ P τ * eis ψ lf B ρ P (fou (chiB ψ (Bf B)) (muF B lf) φ) (fun w => -(τ w)⁻¹) = eis ψ lf B ρ P φ τ) ∧ ∀ c : ℂ, eis ψ lf B ρ P (c • φ) τ = c * eis ψ lf B ρ P φ τ :=
  CompanionTheory.PlacePermOperatorBicommutantSpan.ei_inv

end GlobalTheory.CompanionTheory.SW.Core.EiInv
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaMeasureNonzeroVectorsBound
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.MeanCount

theorem box_mono {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d M n : ℕ}
    (b : Module.Basis (Fin d) F E) (N : ℕ) {r r' : ℝ} (h : r ≤ r') :
    (box b N r : Set (Fin n → Fin M → AF F ⊗[F] E)) ⊆ box b N r' :=
  fun _ hX => ⟨hX.1, hX.2.trans h⟩

theorem real_bound {C₁ C₂ x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hxy : x ≤ y) :
    C₁ * x ≤ (|C₁| + |C₂|) * (y + z) := by
  have h1 := abs_nonneg C₁
  have h2 := abs_nonneg C₂
  calc C₁ * x ≤ |C₁| * x := mul_le_mul_of_nonneg_right (le_abs_self _) hx
    _ ≤ |C₁| * y := mul_le_mul_of_nonneg_left hxy h1
    _ ≤ (|C₁| + |C₂|) * (y + z) :=
        mul_le_mul (by linarith) (by linarith) hy (by linarith)

theorem mean_count_box : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ N : ℕ, 0 < N → ∃ C : ℝ, ∀ r : ℝ, 0 < r → thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0} {X | (∀ v, (fun a i => (N : Fv F v ⊗[F] E) * projV v (projFin X) a i) ∈ latV b v) ∧ sizeTup b (projInf X) ≤ r} ≤ ENNReal.ofReal (C * (r ^ (Module.finrank ℚ F * M) + r ^ (2 * Module.finrank ℚ F * M))) := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM d b μ 𝓕 hμ h𝓕 N hN
  obtain ⟨⟨lcA, scA, t2A⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := lcA
  haveI := scA
  haveI := t2A
  obtain ⟨-, -, -, t2K, -, -, -, borelK, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (AF F)
  haveI := t2K
  haveI := borelK 1 M
  have hact := (_root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hCM M J hJ (AF F))
  have hgram : ∀ (h : HA (AF F) σ J) (X : Fin 1 → Fin M → AF F ⊗[F] E),
      gramR (AF F) σ J (actW (AF F) σ J h X) = gramR (AF F) σ J X :=
    (hact.2.2.2.2.2 1).2.2.2
  obtain ⟨hfin1, hfin2, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.FinQ.gram_rational_finite F E σ hCM M J hJ
  have h0 : μ 𝓕 ≠ 0 := ((_root_.GlobalTheory.CompanionTheory.SW.haar_fundamental_exist F E σ hCM M J hJ).2 μ hμ).2.2 𝓕 h𝓕
  have hc : (μ 𝓕)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 h0
  obtain ⟨r₀, hr₀, hsmall⟩ := _root_.GlobalTheory.CompanionTheory.SW.SmallQ.small_length F E σ hCM M J hJ d b N hN
  have hr₁ : 0 < min r₀ 1 := lt_min hr₀ one_pos
  obtain ⟨C₁, hC₁⟩ := _root_.GlobalTheory.CompanionTheory.SW.mean_isotropic_box F E σ hCM M J hJ hM μ 𝓕 hμ h𝓕 d b N hN
  obtain ⟨C₂, hC₂⟩ := _root_.GlobalTheory.CompanionTheory.SW.CntLarge.cnt_large F E σ hCM M J hJ hM μ 𝓕 hμ h𝓕 d b N (min r₀ 1) hN hr₁
  refine ⟨((μ 𝓕)⁻¹).toReal * (|C₁| + |C₂|), fun r hr => ?_⟩
  change thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0} (box b N r) ≤ _
  have hmeas : MeasurableSet (box b N r : Set (Fin 1 → Fin M → AF F ⊗[F] E)) :=
    ((_root_.GlobalTheory.CompanionTheory.SW.BoxF.box_facts F E σ hCM d b 1 M).1 N r hN).measurableSet
  have hval : thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0} (box b N r) =
      (μ 𝓕)⁻¹ * cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0}
        (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) := by
    have h := _root_.GlobalTheory.CompanionTheory.SW.ThetaCnt.lintegral_thetaMeas F E σ hCM M J hJ μ 𝓕 hμ h𝓕 1 {X : Fin 1 → Fin M → E | X ≠ 0}
      (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hmeas)
    rw [lintegral_indicator_const hmeas, one_mul] at h
    exact h
  have hx : 0 ≤ r ^ (Module.finrank ℚ F * M) := by positivity
  have hy : 0 ≤ r ^ (2 * Module.finrank ℚ F * M) := by positivity
  have hbound : cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0}
      (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) ≤
      ENNReal.ofReal ((|C₁| + |C₂|) * (r ^ (Module.finrank ℚ F * M) +
        r ^ (2 * Module.finrank ℚ F * M))) := by
    rcases le_total r (min r₀ 1) with hle | hle
    · have hrr₀ : r ≤ r₀ := hle.trans (min_le_left _ _)
      have hr1 : r ≤ 1 := hle.trans (min_le_right _ _)
      have hiso : ∀ (h : HA (AF F) σ J) (X : Fin 1 → Fin M → E),
          actW (AF F) σ J h⁻¹ (ratTup (AF F) X) ∈ (box b N r : Set (Fin 1 → Fin M → AF F ⊗[F] E)) →
          gramE σ J X = 0 := by
        intro h X hX
        obtain ⟨t, ht⟩ := hfin1 X
        have hY : gramR (AF F) σ J (actW (AF F) σ J h⁻¹ (ratTup (AF F) X)) =
            fun _ _ => inclR (AF F) (algebraMap F E t) := by
          rw [hgram, hfin2, ht]
          rfl
        have ht0 : t = 0 := hsmall t _ (box_mono b N hrr₀ hX) hY
        rw [ht, ht0]
        funext a c
        simp
      have heq : cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0}
            (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) =
          cntI σ J μ 𝓕 {X : Fin 1 → Fin M → E | X ≠ 0 ∧ gramE σ J X = 0}
            (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) := by
        unfold cntI
        refine lintegral_congr fun h => ?_
        rw [tsum_subtype {X : Fin 1 → Fin M → E | X ≠ 0}
            (fun X => Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))
              (actW (AF F) σ J h⁻¹ (ratTup (AF F) X))),
          tsum_subtype {X : Fin 1 → Fin M → E | X ≠ 0 ∧ gramE σ J X = 0}
            (fun X => Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))
              (actW (AF F) σ J h⁻¹ (ratTup (AF F) X)))]
        congr 1
        funext X
        by_cases hB : actW (AF F) σ J h⁻¹ (ratTup (AF F) X) ∈
            (box b N r : Set (Fin 1 → Fin M → AF F ⊗[F] E))
        · have hg := hiso h X hB
          by_cases hX : X ≠ 0
          · rw [Set.indicator_of_mem (show X ∈ {X : Fin 1 → Fin M → E | X ≠ 0} from hX),
              Set.indicator_of_mem
                (show X ∈ {X : Fin 1 → Fin M → E | X ≠ 0 ∧ gramE σ J X = 0} from ⟨hX, hg⟩)]
          · rw [Set.indicator_of_notMem (show X ∉ {X : Fin 1 → Fin M → E | X ≠ 0} from hX),
              Set.indicator_of_notMem
                (show X ∉ {X : Fin 1 → Fin M → E | X ≠ 0 ∧ gramE σ J X = 0} from fun h' => hX h'.1)]
        · simp only [Set.indicator, hB, if_false, ite_self]
      rw [heq]
      refine (hC₁ r hr).trans (ENNReal.ofReal_le_ofReal ?_)
      have hexp : Module.finrank ℚ F * M ≤ 2 * Module.finrank ℚ F * (M - 1) := by
        have h2 : M ≤ 2 * (M - 1) := by omega
        calc Module.finrank ℚ F * M ≤ Module.finrank ℚ F * (2 * (M - 1)) :=
              Nat.mul_le_mul_left _ h2
          _ = 2 * Module.finrank ℚ F * (M - 1) := by ring
      exact real_bound (by positivity) hx hy (pow_le_pow_of_le_one hr.le hr1 hexp)
    · refine (hC₂ r hle).trans (ENNReal.ofReal_le_ofReal ?_)
      have := real_bound (C₁ := C₂) (C₂ := C₁) hy hy hx le_rfl
      rw [add_comm |C₂|, add_comm (r ^ (2 * Module.finrank ℚ F * M))] at this
      exact this
  rw [hval, mul_assoc, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hc]
  exact mul_le_mul_right hbound _

end GlobalTheory.CompanionTheory.SW.MeanCount
end
end

