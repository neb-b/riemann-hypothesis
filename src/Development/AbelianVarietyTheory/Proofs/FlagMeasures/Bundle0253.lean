module

public import Mathlib
public import Formalism.LocalRingCardinality.DataCD
public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0250
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0242
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.NormAdditiveCharacterTypePrimeEqOne
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SymmetricMeasureL2NormEqResolutionL2
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0049
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BallVolSuccSq
section
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.GaugeQuot.BallProd

theorem volume_ball_eq_ballVol {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] {d : ℕ}
    (hd : Module.finrank ℝ F = d) (r : ℝ) :
    (volume : Measure F) (Metric.ball 0 r) = ballVol d r := by
  subst hd
  unfold ballVol
  have h := (stdOrthonormalBasis ℝ F).measurePreserving_repr
  rw [← h.measure_preimage measurableSet_ball.nullMeasurableSet]
  congr 1
  ext x
  simp

theorem prod_region_eq_ballVol (P Q : ℕ) (r : ℝ) (hr : 0 < r) :
    ((volume : Measure (ℝ × Sp P Q)).prod
      (volume : Measure (EuclideanSpace ℝ (Fin ((P + Q) ^ 2)))))
      {p | p.1.1 ^ 2 + ∑ i, ‖p.1.2 i‖ ^ 2 + ‖p.2‖ ^ 2 < r ^ 2} = ballVol ((P + Q + 1) ^ 2) r := by
  have h0 := GlobalTheory.volume_preserving_ofLp_complex (Fin P ⊕ Fin Q)
  have h1 := ((MeasurePreserving.id (volume : Measure ℝ)).prod h0).comp
    (WithLp.volume_preserving_ofLp ℝ (EuclideanSpace ℂ (Fin P ⊕ Fin Q)))
  have h2 := (h1.prod (MeasurePreserving.id
      (volume : Measure (EuclideanSpace ℝ (Fin ((P + Q) ^ 2)))))).comp
    (WithLp.volume_preserving_ofLp (WithLp 2 (ℝ × EuclideanSpace ℂ (Fin P ⊕ Fin Q)))
      (EuclideanSpace ℝ (Fin ((P + Q) ^ 2))))
  have hm : MeasurableSet {p : (ℝ × Sp P Q) × EuclideanSpace ℝ (Fin ((P + Q) ^ 2)) |
      p.1.1 ^ 2 + ∑ i, ‖p.1.2 i‖ ^ 2 + ‖p.2‖ ^ 2 < r ^ 2} :=
    (isOpen_lt (by fun_prop) continuous_const).measurableSet
  rw [Measure.volume_eq_prod, ← h2.measure_preimage hm.nullMeasurableSet,
    ← volume_ball_eq_ballVol (F := WithLp 2 (WithLp 2 (ℝ × EuclideanSpace ℂ (Fin P ⊕ Fin Q)) ×
      EuclideanSpace ℝ (Fin ((P + Q) ^ 2))))]
  · congr 1
    ext x
    rw [mem_ball_zero_iff, ← sq_lt_sq₀ (norm_nonneg _) hr.le, WithLp.prod_norm_sq_eq_of_L2,
      WithLp.prod_norm_sq_eq_of_L2, EuclideanSpace.norm_sq_eq]
    simp
  · rw [(WithLp.linearEquiv 2 ℝ _).finrank_eq, Module.finrank_prod,
      (WithLp.linearEquiv 2 ℝ _).finrank_eq, Module.finrank_prod,
      (WithLp.linearEquiv 2 ℝ (Fin P ⊕ Fin Q → ℂ)).finrank_eq, Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex]
    ring

theorem ballVol_succ_sq (P Q : ℕ) (r : ℝ) (hr : 0 < r) :
    ballVol ((P + Q + 1) ^ 2) r = (2 : ℝ≥0∞) ^ (P + Q) *
      ((volume : Measure (ℝ × Sp P Q)).prod
        (volume : Measure (EuclideanSpace ℝ (Fin ((P + Q) ^ 2)))))
        {p | tanSq p.1 + ‖p.2‖ ^ 2 < r ^ 2} := by
  have hs : (√2 : ℝ) ≠ 0 := by positivity
  have hfin : Module.finrank ℝ (Sp P Q) = 2 * (P + Q) := by
    rw [Module.finrank_pi_fintype]; simp [Complex.finrank_real_complex]; ring
  have h0 : MeasurePreserving (fun y : Sp P Q => (√2 : ℝ) • y) volume
      (((2 : ℝ≥0∞) ^ (P + Q))⁻¹ • volume) := by
    refine ⟨by fun_prop, ?_⟩
    rw [Measure.map_addHaar_smul _ hs, hfin, pow_mul, Real.sq_sqrt (by norm_num),
      abs_of_pos (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_pow (by norm_num)]
    simp
  have hne : ((2 : ℝ≥0∞) ^ (P + Q)) ≠ 0 := by simp
  have hnt : ((2 : ℝ≥0∞) ^ (P + Q)) ≠ ⊤ := by simp
  haveI : SFinite (((2 : ℝ≥0∞) ^ (P + Q))⁻¹ • (volume : Measure (Sp P Q))) := inferInstance
  have h1 := ((MeasurePreserving.id (volume : Measure ℝ)).prod h0).prod (MeasurePreserving.id
      (volume : Measure (EuclideanSpace ℝ (Fin ((P + Q) ^ 2)))))
  have hm : MeasurableSet {p : (ℝ × Sp P Q) × EuclideanSpace ℝ (Fin ((P + Q) ^ 2)) |
      p.1.1 ^ 2 + ∑ i, ‖p.1.2 i‖ ^ 2 + ‖p.2‖ ^ 2 < r ^ 2} :=
    (isOpen_lt (by fun_prop) continuous_const).measurableSet
  have h2 := h1.measure_preimage hm.nullMeasurableSet
  rw [Measure.prod_smul_right, Measure.prod_smul_left, Measure.smul_apply,
    ← Measure.volume_eq_prod, prod_region_eq_ballVol P Q r hr, smul_eq_mul] at h2
  have h3 : {p : (ℝ × Sp P Q) × EuclideanSpace ℝ (Fin ((P + Q) ^ 2)) |
      tanSq p.1 + ‖p.2‖ ^ 2 < r ^ 2} =
      Prod.map (Prod.map id fun y : Sp P Q => (√2 : ℝ) • y) id ⁻¹'
      {p | p.1.1 ^ 2 + ∑ i, ‖p.1.2 i‖ ^ 2 + ‖p.2‖ ^ 2 < r ^ 2} := by
    ext p
    simp [tanSq, norm_smul, mul_pow, Finset.mul_sum, mul_add]
  rw [h3, h2, ← mul_assoc, ENNReal.mul_inv_cancel hne hnt, one_mul]

end GlobalTheory.GaugeQuot.BallProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMapPairingBoundStatement
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_map_pairing_bound : Hyps → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS) (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (R : Rep D.R.k D.R.rS) (h : ℝ) (l : R.H → W.Wp) (l' : R.H → W.Wq) (dd : ℝ), cdScaleTie D → GoodW D τ w w' θ W → R.IsDS (epsSH D.R) lam → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z (psiS D W.z) R.σ W.π l → PI.BesselMapUniq.IsBesselMapSm (k := D.R.k) (r := D.R.rS) W.z' (psiS D W.z') R.σ W.π' l' → 0 < dd → (∀ v ∈ R.sm, l2SG W.νS (fun g => l (R.σ g v)) = ENNReal.ofReal (‖v‖ ^ 2 / dd)) → (∀ v ∈ R.sm, l2SG W.νS' (fun g => l' (R.σ g v)) = ENNReal.ofReal (‖v‖ ^ 2 / dd)) → ∃ A : LocS W, GoodS D lam A := by
  first | exact @GlobalTheory.DatumOfPeriods.exists_goodS | exact GlobalTheory.DatumOfPeriods.exists_goodS | (intros; apply GlobalTheory.DatumOfPeriods.exists_goodS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelProjectorOnLine
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf.ProjLine

theorem mul_mem_GG_iff {k r : ℕ} {s x : Mat k r} (hs : s ∈ GG k r) : s * x ∈ GG k r ↔ x ∈ GG k r := by
  simp only [GG, UH, Set.mem_setOf_eq] at hs ⊢
  have e : (s * x)ᴴ * Hpk k r * (s * x) = xᴴ * (sᴴ * Hpk k r * s) * x := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [e, hs]

theorem Sset_subset_GG {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) : Sset k r z ⊆ GG k r := by
  rintro s ⟨h, hh, m, hm, rfl⟩
  exact (mul_mem_GG_iff hh.1).2 hm.1

theorem isClosed_GG (k r : ℕ) : IsClosed {x : Mt k r | (Matrix.of x : Mat k r) ∈ GG k r} := by
  have hc : Continuous fun x : Mat k r => xᴴ * Hpk k r * x :=
    ((continuous_id.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul continuous_id
  exact isClosed_eq (X := Mt k r) hc continuous_const

theorem rankOneInnerOperator_self_apply {Wp : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (x y : Wp) :
    rk1 y x x = ((‖x‖ ^ 2 : ℝ) : ℂ) • y := by
  rw [rankOneInnerOperator_apply, inner_self_eq_norm_sq_to_K]; push_cast; rfl

theorem inner_rankOneInnerOperator_self {Wp : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (x : Wp) :
    ⟪x, rk1 x x x⟫_ℂ = (((‖x‖ ^ 2) ^ 2 : ℝ) : ℂ) := by
  rw [rankOneInnerOperator_self_apply, inner_smul_right, inner_self_eq_norm_sq_to_K]
  have e : ((‖x‖ : ℝ) : ℂ) = (RCLike.ofReal ‖x‖ : ℂ) := rfl
  push_cast
  rw [← e]; ring

theorem ae_mem_GG {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {μG μS ν : Measure (Mt k r)}
    (hG : IsHaarOn (GG k r) μG) (hS : IsHaarOn (Sset k r z) μS) (hq : IsQuotMeas μG μS ν) :
    ∀ᵐ x ∂ν, (Matrix.of x : Mat k r) ∈ GG k r := by
  set B : Set (Mt k r) := {x | (Matrix.of x : Mat k r) ∉ GG k r} with hBdef
  have hB : MeasurableSet B := (isClosed_GG k r).measurableSet.compl
  have h0 := hq (B.indicator 1) (measurable_one.indicator hB)
  rw [lintegral_indicator_one hB, hG.2.2.1] at h0
  have hc : μS Set.univ ≠ 0 := by
    intro h; exact hS.2.1 (Measure.measure_univ_eq_zero.1 h)
  have hle : ∀ x, B.indicator (fun _ => μS Set.univ) x ≤
      ∫⁻ s, B.indicator 1 (fun i j => (Matrix.of s * Matrix.of x : Mat k r) i j) ∂μS := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]
      calc μS Set.univ = ∫⁻ _, 1 ∂μS := (lintegral_one).symm
        _ ≤ _ := by
          apply lintegral_mono_ae
          have hnull : ∀ᵐ s ∂μS, (Matrix.of s : Mat k r) ∈ Sset k r z := by
            rw [ae_iff]; simpa using hS.2.2.1
          filter_upwards [hnull] with s hs
          have hmem : (fun i j => (Matrix.of s * Matrix.of x : Mat k r) i j) ∈ B := by
            show ¬ ((Matrix.of s * Matrix.of x : Mat k r) ∈ GG k r)
            intro h; exact hx ((mul_mem_GG_iff (Sset_subset_GG z hs)).1 h)
          rw [Set.indicator_of_mem hmem]; rfl
    · rw [Set.indicator_of_notMem hx]; exact zero_le
  have hmul : μS Set.univ * ν B = 0 := by
    rw [← lintegral_indicator_const hB]
    exact le_antisymm ((lintegral_mono hle).trans h0.symm.le) (zero_le)
  have hνB : ν B = 0 := (mul_eq_zero.1 hmul).resolve_left hc
  rw [ae_iff]; simpa [hBdef] using hνB

theorem projector_line : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → ∀ l : H → Wp, IsEll z (psiGen k r z c) π μS σ (DD σ w) l → (∀ u ∈ DD σ w, l2SG ν (fun x => l (σ x u)) = ENNReal.ofReal (‖u‖ ^ 2 / d)) ∧ (∀ v ∈ DD σ w, ∀ ξ : Wp, ∀ x ∈ GG k r, Afun (psiGen k r z c) π μS σ w v ξ x = ⟪l v, ξ⟫_ℂ • l (σ x w)) ∧ ∀ W : Mat k r → Wp, AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) μG → AEStronglyMeasurable (fun x : Mt k r => W (Matrix.of x)) ν → IsSPsiEquiv z (psiGen k r z c) π W → l2SG ν W < ⊤ → ∀ y ∈ GG k r, rconv μG (eFun μG σ w) W y = ((d : ℂ) * ∫ g, ⟪l (σ (Matrix.of g) w), W (Matrix.of g)⟫_ℂ ∂ν) • l (σ y w) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide ν hq l hl
  have hG : IsHaarOn (GG k r) μG := hStd.2.2.2.2.1
  have hU : IsURepOn (GG k r) σ := hStd.2.1
  have hd : 0 < d := hStd.2.2.2.2.2.1.1
  have hS : IsHaarOn (Sset k r z) μS := hSide.2.2.2.1
  have hae := ae_mem_GG hG hS hq
  have hstab := (_root_.GlobalTheory.SgInfDD.DD_stable_dense k r σ w hU).1
  obtain ⟨_, ⟨v0, hv0, hlv0⟩, hbe⟩ := hl
  refine ⟨?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨_, _, hmem, heq, _, _⟩ :=
      _root_.GlobalTheory.SgInf.normIdentity_besselCoef k r σ w a μG d z c π μS hStd hSide ν hq u hu u hu v0 hv0 (l v0)
    set A : Mt k r → Wp := fun x => Afun (psiGen k r z c) π μS σ u v0 (l v0) (Matrix.of x) with hAdef
    set L : Mt k r → Wp := fun x => l (σ (Matrix.of x) u) with hLdef
    set N : ℝ := ‖l v0‖ ^ 2 with hNdef
    have hN : 0 < N := by positivity
    have hAL : ∀ᵐ x ∂ν, A x = (N : ℂ) • L x := by
      filter_upwards [hae] with x hx
      simp only [hAdef, hLdef, Afun]
      rw [hbe _ (hstab _ hx _ hu) _ hv0, rankOneInnerOperator_apply, inner_self_eq_norm_sq_to_K]
      simp [hNdef]
    have hnA : ∀ᵐ x ∂ν, ‖A x‖ ^ 2 = N ^ 2 * ‖L x‖ ^ 2 := by
      filter_upwards [hAL] with x hx
      rw [hx, norm_smul, Complex.norm_real, Real.norm_of_nonneg hN.le, mul_pow]
    have hIA : Integrable (fun x => ‖A x‖ ^ 2) ν := hmem.integrable_norm_pow two_ne_zero
    have hIL : Integrable (fun x => ‖L x‖ ^ 2) ν := by
      have : (fun x => ‖L x‖ ^ 2) =ᵐ[ν] fun x => (N ^ 2)⁻¹ * ‖A x‖ ^ 2 := by
        filter_upwards [hnA] with x hx
        rw [hx, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
      exact (hIA.const_mul _).congr this.symm
    have hbevv : ⟪l v0, be (psiGen k r z c) π μS σ v0 v0 (l v0)⟫_ℂ = ((N ^ 2 : ℝ) : ℂ) := by
      rw [hbe _ hv0 _ hv0, inner_rankOneInnerOperator_self]
    have hintA : ∫ x, ‖A x‖ ^ 2 ∂ν = N ^ 2 * (‖u‖ ^ 2 / d) := by
      have h1 : ∫ x, ⟪A x, A x⟫_ℂ ∂ν = ((∫ x, ‖A x‖ ^ 2 ∂ν : ℝ) : ℂ) := by
        rw [← integral_complex_ofReal]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [inner_self_eq_norm_sq_to_K]; push_cast; rfl
      have h2 := heq
      rw [hbevv, inner_self_eq_norm_sq_to_K u] at h2
      have h3 : ((∫ x, ‖A x‖ ^ 2 ∂ν : ℝ) : ℂ) = ((N ^ 2 * (‖u‖ ^ 2 / d) : ℝ) : ℂ) := by
        rw [← h1]; refine h2.trans ?_
        have e : ((‖u‖ : ℝ) : ℂ) = (RCLike.ofReal ‖u‖ : ℂ) := rfl
        push_cast
        rw [← e]; ring
      exact_mod_cast h3
    have hintL : ∫ x, ‖L x‖ ^ 2 ∂ν = ‖u‖ ^ 2 / d := by
      have : ∫ x, ‖A x‖ ^ 2 ∂ν = N ^ 2 * ∫ x, ‖L x‖ ^ 2 ∂ν := by
        rw [← integral_const_mul]; exact integral_congr_ae hnA
      rw [this] at hintA
      exact mul_left_cancel₀ (by positivity) hintA
    unfold l2SG
    rw [← hintL, ofReal_integral_eq_lintegral_ofReal hIL (Filter.Eventually.of_forall fun x => by positivity)]
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    rfl
  · intro v hv ξ x hx
    simp only [Afun]
    rw [hbe _ (mem_DD σ w hx) _ hv, rankOneInnerOperator_apply]
  · intro W hW1 hW2 hEq hL2 y hy
    obtain ⟨_, hconv⟩ := _root_.GlobalTheory.SgInf.KernelRe.kernel_rconv k r σ w a μG d z c π μS hStd hSide ν hq W hW1 hW2 hEq hL2 y hy
    rw [hconv]
    have h : ∀ᵐ g ∂ν, be (psiGen k r z c) π μS σ (σ y w) (σ (Matrix.of g) w) (W (Matrix.of g)) =
        ⟪l (σ (Matrix.of g) w), W (Matrix.of g)⟫_ℂ • l (σ y w) := by
      filter_upwards [hae] with g hg
      rw [hbe _ (mem_DD σ w hy) _ (mem_DD σ w hg), rankOneInnerOperator_apply]
    rw [integral_congr_ae h, integral_smul_const, smul_smul]

end GlobalTheory.SgInf.ProjLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockPerpEmbeddingOfDiagonalFrame
section
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot GlobalTheory.GaugeQuot GlobalTheory.Mem.Vol.Scale
open scoped ENNReal NNReal

namespace GlobalTheory.PerpSort

theorem herm_comp {n P Q : ℕ} {ε : Fin n → Bool} {f : Fin P ⊕ Fin Q ≃ Fin n} (hf : Sorts ε f)
    (x y : Fin n → ℂ) : herm (x ∘ f) (y ∘ f) = star y ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) := by
  obtain ⟨h1, h2⟩ := hf
  rw [dotProduct, ← Equiv.sum_comp f, Fintype.sum_sum_type, herm]
  simp only [Function.comp_apply, Pi.star_apply, Formalism.REAL.Jm, mulVec_diagonal, h1, h2, if_true,
    Bool.false_eq_true, if_false, one_mul, neg_one_mul, mul_neg, Finset.sum_neg_distrib, ← sub_eq_add_neg]
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem form_self {n : ℕ} (ε : Fin n → Bool) (x : Fin n → ℂ) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x) = (GlobalTheory.GaussMean.qEps ε x : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Formalism.REAL.Jm, mulVec_diagonal, GlobalTheory.GaussMean.qEps]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  have hx : star (x i) * x i = ((‖x i‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul']
    push_cast; ring
  rw [mul_left_comm, hx]
  split_ifs <;> push_cast <;> ring

theorem mat_symm {n P Q : ℕ} {ε : Fin n → Bool} {f : Fin P ⊕ Fin Q ≃ Fin n} (hf : Sorts ε f)
    (k : Formalism.REAL.UJ ε) : (hf.equiv.symm k).mat = (Formalism.MainNotions.S.uMat k).submatrix f f := by
  have h := hf.umat_equiv (hf.equiv.symm k)
  rw [ContinuousMulEquiv.apply_symm_apply] at h
  ext i j
  have e := congrFun (congrFun h (f i)) (f j)
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply] at e
  exact e.symm

theorem act_symm {n P Q : ℕ} {ε : Fin n → Bool} {f : Fin P ⊕ Fin Q ≃ Fin n} (hf : Sorts ε f)
    (k : Formalism.REAL.UJ ε) (x : Fin n → ℂ) :
    act (hf.equiv.symm k) (x ∘ f) = (Formalism.MainNotions.S.uMat k *ᵥ x) ∘ f := by
  rw [act, mat_symm hf, Matrix.submatrix_mulVec_equiv, Function.comp_assoc, f.self_comp_symm,
    Function.comp_id]

private theorem of_fin_cases_mulVec {n : ℕ} (x₀ : Fin (n + 1) → ℂ) (B : Matrix (Fin (n + 1)) (Fin n) ℂ)
    (w : Fin (n + 1) → ℂ) :
    (Matrix.of fun i j => Fin.cases (motive := fun _ => ℂ) (x₀ i) (fun k => B i k) j) *ᵥ w =
      w 0 • x₀ + B *ᵥ fun k => w k.succ := by
  ext i
  simp only [mulVec, dotProduct, Fin.sum_univ_succ, Matrix.of_apply, Fin.cases_zero, Fin.cases_succ,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem exists_mulVec_eq {n : ℕ} (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool)
    (x₀ : Fin (n + 1) → ℂ) (B : Matrix (Fin (n + 1)) (Fin n) ℂ)
    (h0 : star x₀ ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x₀) ≠ 0) (h1 : star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0)
    (h2 : Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε') (y : Fin (n + 1) → ℂ)
    (hy : star x₀ ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0) : ∃ u, B *ᵥ u = y := by
  set J := Formalism.REAL.Jm ε
  set M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    Matrix.of fun i j => Fin.cases (motive := fun _ => ℂ) (x₀ i) (fun k => B i k) j with hM
  have hMv : ∀ w, M *ᵥ w = w 0 • x₀ + B *ᵥ fun k : Fin n => w k.succ := fun w => of_fin_cases_mulVec x₀ B w
  have key : ∀ t : Fin n → ℂ, star x₀ ⬝ᵥ (J *ᵥ (B *ᵥ t)) = 0 := by
    intro t
    rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, h1, zero_dotProduct]
  have hval : ∀ w, star x₀ ⬝ᵥ (J *ᵥ (M *ᵥ w)) = w 0 * (star x₀ ⬝ᵥ (J *ᵥ x₀)) := by
    intro w
    rw [hMv, Matrix.mulVec_add, dotProduct_add, key, add_zero, Matrix.mulVec_smul,
      dotProduct_smul, smul_eq_mul]
  have hinj : Function.Injective M.mulVec := by
    intro a b hab
    have hz : M *ᵥ (a - b) = 0 := by
      rw [Matrix.mulVec_sub]; exact sub_eq_zero.mpr hab
    have hw0 : (a - b) 0 = 0 := by
      have e := hval (a - b)
      rw [hz, Matrix.mulVec_zero, dotProduct_zero] at e
      exact (mul_eq_zero.mp e.symm).resolve_right h0
    have hBt : B *ᵥ (fun k : Fin n => (a - b) k.succ) = 0 := by
      have e := hMv (a - b)
      rw [hz, hw0, zero_smul, zero_add] at e
      exact e.symm
    have ht : (fun k : Fin n => (a - b) k.succ) = 0 := by
      have hJ' : Formalism.REAL.Jm ε' *ᵥ (fun k : Fin n => (a - b) k.succ) = 0 := by
        rw [← h2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hBt, Matrix.mulVec_zero,
          Matrix.mulVec_zero]
      rw [← Matrix.one_mulVec (fun k : Fin n => (a - b) k.succ), ← Formalism.REAL.Jm_mul_self ε',
        ← Matrix.mulVec_mulVec, hJ', Matrix.mulVec_zero]
    rw [← sub_eq_zero]
    funext i
    refine Fin.cases hw0 (fun k => ?_) i
    exact congrFun ht k
  have hsurj : Function.Surjective M.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  obtain ⟨w, hw⟩ := hsurj y
  have hw0 : w 0 = 0 := by
    have e := hval w
    rw [hw, hy] at e
    exact (mul_eq_zero.mp e.symm).resolve_right h0
  refine ⟨fun k : Fin n => w k.succ, ?_⟩
  rw [← hw, hMv, hw0, zero_smul, zero_add]

theorem isPerpEmb_of_sorts : ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (ε' : Fin n → Bool) (s : Bool) (x₀ : Fin (n + 1) → ℂ) (B : Matrix (Fin (n + 1)) (Fin n) ℂ) (j : Formalism.REAL.UJ ε' → Formalism.REAL.UJ ε), GlobalTheory.GaussMean.qEps ε x₀ = GlobalTheory.GaussMean.sgn ℝ s → star x₀ ᵥ* (Formalism.REAL.Jm ε * B) = 0 → Bᴴ * Formalism.REAL.Jm ε * B = Formalism.REAL.Jm ε' → (∀ g, Formalism.MainNotions.S.uMat (j g) *ᵥ x₀ = x₀ ∧ Formalism.MainNotions.S.uMat (j g) * B = B * Formalism.MainNotions.S.uMat g) → ∀ (P Q P' Q' : ℕ) (f : Fin P ⊕ Fin Q ≃ Fin (n + 1)) (f' : Fin P' ⊕ Fin Q' ≃ Fin n) (hf : Sorts ε f) (hf' : Sorts ε' f'), IsPerpEmb (fun i => x₀ (f i)) (B.submatrix f f') (fun g => hf.equiv.symm (j (hf'.equiv g))) := by
  intro n ε ε' s x₀ B j hq h1 h2 hj P Q P' Q' f f' hf hf'
  change IsPerpEmb (x₀ ∘ f) _ _
  have hsub : ∀ u : Fin P' ⊕ Fin Q' → ℂ, B.submatrix f f' *ᵥ u = (B *ᵥ (u ∘ f'.symm)) ∘ f :=
    fun u => Matrix.submatrix_mulVec_equiv _ _ _ _
  have hc : star x₀ ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ x₀) ≠ 0 := by
    rw [form_self, hq]
    cases s <;> simp [GlobalTheory.GaussMean.sgn]
  refine ⟨fun u v => ?_, fun y => ⟨fun h0 => ?_, ?_⟩, fun g => ?_⟩
  · have e := herm_comp hf' (u ∘ f'.symm) (v ∘ f'.symm)
    rw [Function.comp_assoc, f'.symm_comp_self, Function.comp_id, Function.comp_assoc,
      f'.symm_comp_self, Function.comp_id] at e
    rw [e, hsub, hsub, herm_comp hf, ← h2, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  · have e := herm_comp hf (y ∘ f.symm) x₀
    rw [Function.comp_assoc, f.symm_comp_self, Function.comp_id] at e
    rw [e] at h0
    obtain ⟨u, hu⟩ := exists_mulVec_eq ε ε' x₀ B hc h1 h2 _ h0
    refine ⟨u ∘ f', ?_⟩
    rw [hsub, Function.comp_assoc, f'.self_comp_symm, Function.comp_id, hu, Function.comp_assoc,
      f.symm_comp_self, Function.comp_id]
  · rintro ⟨u, rfl⟩
    rw [hsub, herm_comp hf, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, h1,
      zero_dotProduct]
  · obtain ⟨hfix, hcomm⟩ := hj (hf'.equiv g)
    refine ⟨?_, fun u => ?_⟩
    · show act (hf.equiv.symm (j (hf'.equiv g))) (x₀ ∘ f) = x₀ ∘ f
      rw [act_symm hf, hfix]
    · show act (hf.equiv.symm (j (hf'.equiv g))) _ = _
      have e := act_symm hf' (hf'.equiv g) (u ∘ f'.symm)
      rw [ContinuousMulEquiv.symm_apply_apply, Function.comp_assoc, f'.symm_comp_self,
        Function.comp_id] at e
      rw [hsub, hsub, act_symm hf, Matrix.mulVec_mulVec, hcomm, ← Matrix.mulVec_mulVec, e,
        Function.comp_assoc, f'.self_comp_symm, Function.comp_id]

end GlobalTheory.PerpSort
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFlagStepLocallyStandardDualCoeffOne
section
open Formalism.MainNotions.S

namespace GlobalTheory

theorem locStd_exists_flag_coef_one : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : Formalism.MainNotions.S.Loc.HermSp M V} {r : ℕ} (Fr : Formalism.MainNotions.S.LocNG.FrameD H r) (n : V ≃ₗ[E] V), n ∈ Fr.N → ∀ (L : Submodule M.L.O (H.Wb Fr.f)) (a : Fin r), ∃ v ∈ Formalism.MainNotions.S.LocNG.img n (Fr.LamStd L), v ∈ Fr.Fj (a.val + 1) ∧ H.h v (Fr.es a) = 1 := by
  intro F _ _ _ E _ _ _ _ M V _ _ H r Fr n hn L a

  have hiso : ∀ b c : Fin r, H.h (Fr.e b) (Fr.e c) = 0 := fun b c =>
    Fr.h_iso b.castSucc c.castSucc (Or.inl (Fin.castSucc_lt_last b).ne)
  have hes : ∀ b c : Fin r, H.h (Fr.e b) (Fr.es c) = if b = c then 1 else 0 := fun b c =>
    Fr.h_es b c

  have hlam : Fr.e a ∈ Fr.LamStd L := by
    refine Submodule.subset_span ⟨fun b => ?_, fun b => ?_, ⟨0, ?_, ?_⟩⟩
    · rw [hes]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · rw [hiso]
      exact zero_mem _
    · simp only [Formalism.MainNotions.S.LocNG.FrameD.prF, hes, hiso, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const_zero, sub_self,
        ZeroMemClass.coe_zero]
    · rw [map_zero]
      exact L.zero_mem

  have hperp : ∀ w ∈ Fr.Fj a.val, H.h w (Fr.es a) = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb, rfl⟩ := hx
      rw [hes, if_neg (Fin.ne_of_val_ne (Nat.ne_of_lt hb))]
    | zero => exact H.h_zero_left _
    | add x y _ _ hx hy => rw [H.h_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [H.h_smul_left, hx, mul_zero]

  have hmem : Fr.e a ∈ Fr.Fj (a.val + 1) :=
    Submodule.subset_span ⟨a, Nat.lt_succ_self _, rfl⟩
  have hle : a.val + 1 ≤ r := a.isLt
  have hdiff : n (Fr.e a) - Fr.e a ∈ Fr.Fj a.val := by
    have := (_root_.GlobalTheory.unipRadical_moves_step_into_prev Fr n hn (a.val + 1) hle (Fr.e a) hmem).1
    simpa using this
  have hmono : Fr.Fj a.val ≤ Fr.Fj (a.val + 1) :=
    Submodule.span_mono (Set.image_mono fun b (hb : b.val < a.val) => Nat.lt_succ_of_lt hb)
  refine ⟨n (Fr.e a), Submodule.mem_map.mpr ⟨Fr.e a, hlam, rfl⟩, ?_, ?_⟩
  · have := (Fr.Fj (a.val + 1)).add_mem (hmono hdiff) hmem
    simpa using this
  · have hsplit : n (Fr.e a) = (n (Fr.e a) - Fr.e a) + Fr.e a := by abel
    rw [hsplit, H.h_add_left, hperp _ hdiff, hes, if_pos rfl, zero_add]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnipotentHaarMeasureRatio
section
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace

namespace GlobalTheory.ThA

theorem exists_isRatioN : ∀ (k r : ℕ), ∃ cN : ℝ, IsRatioN k r cN := by
  intro k r
  have h1 : PI.BesselPeriodGGP.IsHaarOn (Nset k r) (Formalism.MainNotions.S.haarLie (Nset k r) 1) :=
    _root_.GlobalTheory.haarLie_isHaarOn_Nset k r 1 one_pos ENNReal.one_lt_top
  have h2 : PI.BesselPeriodGGP.IsHaarOn (Nset k r) (D.muN k r) :=
    ((GlobalTheory.HaarNotions.isHaarOn_iff_groups k r (D.muN k r)).2.1).2 (P.nilpotent_measure_is_haar k r)
  obtain ⟨c, c0, c1, e⟩ := GlobalTheory.BesselPeriodCompare.haar_unique (P.unipotent_radical_closed k r) h1 h2
  exact ⟨c.toReal, ENNReal.toReal_pos c0 c1, by rw [ENNReal.ofReal_toReal c1]; exact e⟩

end GlobalTheory.ThA
end

