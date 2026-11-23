module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.RealPlaceAnalysis.FinalF
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Formalism.LocalRingCardinality.Bundle0003
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedVectorDifferentiable
section
open MeasureTheory NumberField Matrix Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId
open Filter Topology
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.GardingVec

theorem hasDerivAt_orbit {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (ρ : G → H →L[ℂ] H) (w : H) (hmul : ∀ a b, ρ (a * b) w = ρ a (ρ b w))
    (hc : Continuous fun y => ρ y w) (a : G → ℂ) (ha : Continuous a) (hs : HasCompactSupport a)
    (hw : ∫ y, a y • ρ y w ∂μ = w) (e : ℝ → G) (he : Continuous e) (he0 : e 0 = 1)
    (D : ℝ → G → ℂ) (hD : Continuous fun p : ℝ × G => D p.1 p.2)
    (hd : ∀ s y, HasDerivAt (fun t => a ((e t)⁻¹ * y)) (D s y) s) :
    HasDerivAt (fun s => ρ (e s) w) (∫ y in tsupport a, D 0 y • ρ y w ∂μ) 0 := by
  have hint : Integrable (fun y => a y • ρ y w) μ :=
    (ha.smul hc).integrable_of_hasCompactSupport hs.smul_right
  have hform : (fun s => ρ (e s) w) = fun s => ∫ y, a ((e s)⁻¹ * y) • ρ y w ∂μ := by
    funext s
    rw [← integral_mul_left_eq_self (fun y => a ((e s)⁻¹ * y) • ρ y w) (e s)]
    conv_lhs => rw [← hw]
    rw [← ContinuousLinearMap.integral_comp_comm _ hint]
    simp only [inv_mul_cancel_left, hmul, map_smul]
  have hzero : ∀ s y, (e s)⁻¹ * y ∉ tsupport a → D s y = 0 := by
    intro s y hy
    have h1 : ∀ᶠ t in 𝓝 s, (e t)⁻¹ * y ∈ (tsupport a)ᶜ :=
      (he.inv.mul continuous_const).continuousAt.preimage_mem_nhds
        ((isClosed_tsupport a).isOpen_compl.mem_nhds hy)
    have h2 : HasDerivAt (fun t => a ((e t)⁻¹ * y)) 0 s :=
      (hasDerivAt_const s (0 : ℂ)).congr_of_eventuallyEq
        (h1.mono fun t ht => image_eq_zero_of_notMem_tsupport ht)
    exact (hd s y).unique h2
  have hK : IsCompact ((fun p : ℝ × G => e p.1 * p.2) '' (Set.Icc (-1) 1 ×ˢ tsupport a)) :=
    (isCompact_Icc.prod hs.isCompact).image ((he.comp continuous_fst).mul continuous_snd)
  set K := (fun p : ℝ × G => e p.1 * p.2) '' (Set.Icc (-1) 1 ×ˢ tsupport a) with hKdef
  have hcD : Continuous fun p : ℝ × G => D p.1 p.2 • ρ p.2 w := hD.smul (hc.comp continuous_snd)
  obtain ⟨M, hM⟩ := ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).prod hK).exists_bound_of_continuousOn
    hcD.continuousOn
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℝ)
    (F := fun s y => a ((e s)⁻¹ * y) • ρ y w) (F' := fun s y => D s y • ρ y w) (x₀ := 0)
    (bound := K.indicator fun _ => M) (s := Set.Icc (-1) 1) (Icc_mem_nhds (by norm_num) (by norm_num))
    (Eventually.of_forall fun s =>
      ((ha.comp (continuous_const.mul continuous_id)).smul hc).aestronglyMeasurable)
    (by simpa [he0] using hint)
    (hcD.comp (Continuous.prodMk_right 0)).aestronglyMeasurable
    (Eventually.of_forall fun y s hs' => by
      by_cases hy : y ∈ K
      · rw [Set.indicator_of_mem hy]; exact hM (s, y) ⟨hs', hy⟩
      · rw [Set.indicator_of_notMem hy, hzero s y, zero_smul, norm_zero]
        intro h
        exact hy ⟨(s, (e s)⁻¹ * y), ⟨hs', h⟩, by simp⟩)
    ((integrable_indicator_iff hK.isClosed.measurableSet).2 (integrableOn_const hK.measure_lt_top.ne))
    (Eventually.of_forall fun y s _ => (hd s y).smul_const _)
  rw [hform, setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact key.2
  · intro y hy
    rw [hzero 0 y (by simpa [he0] using hy), zero_smul]

theorem decay_setIntegral {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ : G → H →L[ℂ] H) (w : H) (hmul : ∀ a b, ρ (a * b) w = ρ a (ρ b w))
    (hc : Continuous fun y => ρ y w) {K : Set G} (hK : IsCompact K) (φ : G → ℂ) (hφ : Continuous φ)
    (d : G → ℝ) (hd : Continuous d) (hsub : ∀ a b, d (a * b) ≤ d a + d b) (c : ℝ) (hc0 : 0 ≤ c) (v : H)
    (h : ∃ C : ℝ, ∀ g, ‖⟪v, ρ g w⟫_ℂ‖ ≤ C * Real.exp (-(c * d g))) :
    ∃ C : ℝ, ∀ g, ‖⟪v, ρ g (∫ y in K, φ y • ρ y w ∂μ)⟫_ℂ‖ ≤ C * Real.exp (-(c * d g)) := by
  obtain ⟨C, hC⟩ := h
  have hC0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 1)
    exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (f := fun y => ‖φ y‖ * Real.exp (c * d y⁻¹))
    (hφ.norm.mul (Real.continuous_exp.comp (continuous_const.mul (hd.comp continuous_inv)))).continuousOn
  have hint : IntegrableOn (fun y => φ y • ρ y w) K μ :=
    (hφ.smul hc).continuousOn.integrableOn_compact hK
  refine ⟨C * M * μ.real K, fun g => ?_⟩
  have e1 : ⟪v, ρ g (∫ y in K, φ y • ρ y w ∂μ)⟫_ℂ = ∫ y in K, φ y * ⟪v, ρ (g * y) w⟫_ℂ ∂μ := by
    have := ContinuousLinearMap.integral_comp_comm ((innerSL ℂ v).comp (ρ g)) hint
    simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, map_smul, smul_eq_mul] at this
    simp only [hmul, this]
  rw [e1]
  refine (norm_setIntegral_le_of_norm_le_const (C := C * M * Real.exp (-(c * d g)))
    hK.measure_lt_top fun y hy => ?_).trans (le_of_eq (by ring))
  have h1 : d g ≤ d (g * y) + d y⁻¹ := by simpa using hsub (g * y) y⁻¹
  have h2 : Real.exp (-(c * d (g * y))) ≤ Real.exp (c * d y⁻¹) * Real.exp (-(c * d g)) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith
  have h3 : ‖φ y‖ * Real.exp (c * d y⁻¹) ≤ M := (le_abs_self _).trans (hM y hy)
  rw [norm_mul]
  calc ‖φ y‖ * ‖⟪v, ρ (g * y) w⟫_ℂ‖
      ≤ ‖φ y‖ * (C * (Real.exp (c * d y⁻¹) * Real.exp (-(c * d g)))) :=
        mul_le_mul_of_nonneg_left ((hC _).trans (mul_le_mul_of_nonneg_left h2 hC0)) (norm_nonneg _)
    _ = C * (‖φ y‖ * Real.exp (c * d y⁻¹)) * Real.exp (-(c * d g)) := by ring
    _ ≤ _ := by gcongr

section
attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
  Matrix.linftyOpNormedSpace

theorem tendsto_slope_exp {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) :
    Tendsto (slope (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) s) (𝓝[≠] s)
      (𝓝 (NormedSpace.exp ((s : ℂ) • X) * X)) := by
  have h := (hasDerivAt_exp_smul_const (𝕂 := ℂ) X ((s : ℝ) : ℂ))
  have h2 := h.scomp (x := s) Complex.ofRealCLM.hasDerivAt
  have h3 : HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X))
      (NormedSpace.exp ((s : ℂ) • X) * X) s := h2.congr_deriv (by rw [Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul]; rfl)
  exact h3.tendsto_slope

theorem continuous_exp_curve {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Continuous (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) :=
  NormedSpace.exp_continuous.comp (Complex.continuous_ofReal.smul continuous_const)

end

theorem hasDerivAt_exp_mul {n : ℕ} (X y : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) :
    HasDerivAt (F := Fin n → Fin n → ℂ) (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X) * y : Matrix _ _ ℂ))
      (NormedSpace.exp ((s : ℂ) • X) * X * y : Matrix _ _ ℂ) s := by
  refine (hasDerivAt_iff_tendsto_slope (F := Fin n → Fin n → ℂ)).mpr ?_
  have h := (tendsto_slope_exp X s).mul_const y
  refine h.congr (fun t => ?_)
  have : ∀ f : ℝ → Matrix (Fin n) (Fin n) ℂ, slope f s t * y = slope (fun t => f t * y) s t := by
    intro f
    simp only [slope_def_module, Matrix.sub_mul, Matrix.smul_mul]
  exact this _

theorem fixed_vector_differentiable : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (α : Matrix (Fin n) (Fin n) ℂ → ℂ) (w : H), IsURepOn (UJset ε) σ → SmoothOnG ε α → HasCompactSupport (fun g : UJ ε => α (umat g)) → (∀ u : H, ∫ g : UJ ε, α (umat g) * ⟪u, σ (umat g) w⟫_ℂ ∂(muG ε) = ⟪u, w⟫_ℂ) → ∃ L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] H, ∀ X, inG ε X → HasDerivAt (fun s : ℝ => σ (NormedSpace.exp ((s : ℂ) • X)) w) (L X) 0 ∧ ∀ (c : ℝ) (v : H), 0 ≤ c → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) w⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) → (∃ C : ℝ, ∀ g : UJ ε, ‖⟪v, σ (umat g) (L X)⟫_ℂ‖ ≤ C * Real.exp (-(c * dOp (umat g)))) := by
  intro n ε H _ _ _ σ α w hσ hα hs hw
  obtain ⟨F, hF, hFα⟩ := smoothOnG_exists_contDiff_extension n ε α hα
  have hu : Continuous fun g : UJ ε => umat g := (isClosedEmbeddingMatrix n ε).1.continuous
  have hmem : ∀ g : UJ ε, umat g ∈ UJset ε := fun g => g.2
  have hum : ∀ a b : UJ ε, umat (a * b) = umat a * umat b := fun _ _ => rfl
  have hmul : ∀ a b : UJ ε, σ (umat (a * b)) w = σ (umat a) (σ (umat b) w) := by
    intro a b
    rw [hum, hσ.1.2 _ (hmem a) _ (hmem b)]; rfl
  have hc : Continuous fun y : UJ ε => σ (umat y) w := (hσ.2.2 w).comp_continuous hu hmem
  have hFα' : ∀ g : UJ ε, α (umat g) = F (umat g) := fun g => (hFα _ g.2).symm
  have ha : Continuous fun g : UJ ε => α (umat g) := by
    simp only [hFα']; exact hF.continuous.comp hu
  have hint : Integrable (fun y : UJ ε => α (umat y) • σ (umat y) w) (muG ε) :=
    (ha.smul hc).integrable_of_hasCompactSupport hs.smul_right
  have hw' : ∫ y : UJ ε, α (umat y) • σ (umat y) w ∂(muG ε) = w := by
    refine ext_inner_left ℂ fun u => ?_
    rw [← integral_inner hint, ← hw u]
    simp only [inner_smul_right]
  have hfd : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by simp)
  let φ : Matrix (Fin n) (Fin n) ℂ → UJ ε → ℂ := fun X y =>
    fderiv ℝ F (umat y) ((-X) * umat y : Matrix _ _ ℂ)
  have hφ : ∀ X, Continuous (φ X) := fun X =>
    (hfd.comp hu).clm_apply (continuous_const.matrix_mul hu)
  have hφi : ∀ X, IntegrableOn (fun y => φ X y • σ (umat y) w)
      (tsupport fun g : UJ ε => α (umat g)) (muG ε) := fun X =>
    ((hφ X).smul hc).continuousOn.integrableOn_compact hs.isCompact
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] H :=
    { toFun := fun X => ∫ y in tsupport fun g : UJ ε => α (umat g), φ X y • σ (umat y) w ∂(muG ε)
      map_add' := fun X Y => by
        rw [← integral_add (hφi X) (hφi Y)]
        congr 1; funext y
        rw [← add_smul]
        congr 1
        have : (-(X + Y) * umat y : Matrix _ _ ℂ) = -X * umat y + -Y * umat y := by
          rw [neg_add, Matrix.add_mul]
        simp only [φ, this]
        exact (fderiv ℝ F (umat y)).map_add _ _
      map_smul' := fun r X => by
        rw [RingHom.id_apply, ← integral_smul]
        congr 1; funext y
        rw [← smul_assoc]
        congr 1
        have : (-(r • X) * umat y : Matrix _ _ ℂ) = r • (-X * umat y) := by
          rw [← smul_neg, Matrix.smul_mul]
        simp only [φ, this]
        exact (fderiv ℝ F (umat y)).map_smul _ _ }
  refine ⟨L, fun X hX => ⟨?_, fun c v hc0 h => ?_⟩⟩
  · let e : ℝ → UJ ε := fun t =>
      ⟨(Matrix.isUnit_exp ((t : ℂ) • X)).unit, exp_indefinite_unitary_holds n ε X hX t⟩
    have hev : ∀ t, umat (e t) = NormedSpace.exp ((t : ℂ) • X) := fun t => rfl
    have hei : ∀ t, umat (e t)⁻¹ = NormedSpace.exp ((t : ℂ) • (-X)) := fun t => by
      rw [smul_neg, Matrix.exp_neg, ← hev]
      exact Matrix.coe_units_inv _
    have he : Continuous e := by
      rw [(isClosedEmbeddingMatrix n ε).1.isInducing.continuous_iff]
      exact continuous_exp_curve X
    have he0 : e 0 = 1 := by
      apply Subtype.ext; apply Units.ext
      show umat (e 0) = 1
      rw [hev]; simp
    have hcE := continuous_exp_curve (-X)
    have key := hasDerivAt_orbit (muG ε) (fun g => σ (umat g)) w hmul hc _ ha hs hw' e he he0
      (fun s y => fderiv ℝ F (NormedSpace.exp ((s : ℂ) • (-X)) * umat y : Matrix _ _ ℂ)
        (NormedSpace.exp ((s : ℂ) • (-X)) * (-X) * umat y : Matrix _ _ ℂ))
      ((hfd.comp ((hcE.comp continuous_fst).matrix_mul (hu.comp continuous_snd))).clm_apply
        (((hcE.comp continuous_fst).matrix_mul continuous_const).matrix_mul (hu.comp continuous_snd)))
      (fun s y => by
        simp only [hFα']
        simp only [hum, hei]
        exact ((hF.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt s
          (hasDerivAt_exp_mul (-X) (umat y) s))
    simp only [hev, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, Matrix.one_mul] at key
    exact key
  · exact decay_setIntegral (muG ε) (fun g => σ (umat g)) w hmul hc hs.isCompact (φ X) (hφ X)
      (fun g => dOp (umat g)) ((dFacts_holds n ε).2.1.comp_continuous hu hmem)
      (fun a b => ((dFacts_holds n ε).1 _ (hmem a)).2.2.1 _ (hmem b)) c hc0 v h

end GlobalTheory.GardingVec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagWedgeFixedAndLengthEqProdDistances
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.FlagPartialWedge

open Formalism.HermitianLatticeCounting.ExpansionTerms (majorantDistance)

theorem len_castLE {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {l n : ℕ} (hl : l ≤ n)
    (y : Fin n → V) (a : Fin l) :
    majorantDistance (fun b : Fin l => y (Fin.castLE hl b)) a = majorantDistance y (Fin.castLE hl a) := by
  have ha := a.isLt
  have hS : (fun b : Fin l => y (Fin.castLE hl b)) '' {b | b < a} = y '' {b | b < Fin.castLE hl a} := by
    ext v
    constructor
    · rintro ⟨b, hb, rfl⟩
      refine ⟨Fin.castLE hl b, ?_, rfl⟩
      simp only [Set.mem_ofPred_eq, Fin.lt_def, Fin.val_castLE] at hb ⊢
      exact hb
    · rintro ⟨b, hb, rfl⟩
      simp only [Set.mem_ofPred_eq, Fin.lt_def, Fin.val_castLE] at hb
      refine ⟨⟨b.val, by omega⟩, ?_, ?_⟩
      · simp only [Set.mem_ofPred_eq, Fin.lt_def]
        exact hb
      · exact congrArg y (Fin.ext rfl)
  unfold majorantDistance
  rw [hS]

theorem fixes_partial_wedge_and_length : ∀ (k r l : ℕ) (hl : l ≤ r + 1) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → (∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, cmp l s *ᵥ (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a))) = (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a)))) ∧ ∀ g ∈ GG k r, ∑ J, ‖(cmp l g⁻¹ *ᵥ (wedge (fun a : Fin l => Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a)))) J‖ ^ 2 = ∏ a : Fin l, lenA k r z g (Fin.castLE hl a) ^ 2 := by
  intro k r l hl z hz
  refine ⟨fun s hs => ?_, fun g _ => ?_⟩
  ·
    obtain ⟨U, hU0, hU1, hsF⟩ := Formalism.QuantumDeterminants.S_F hz hs
    rw [GlobalTheory.TensLen.cmp_mulVec_wedge]
    refine GlobalTheory.FlagFix.wedge_eq_of_mul _ _ (U.submatrix (Fin.castLE hl) (Fin.castLE hl)) ?_ ?_ ?_
    · intro c a hac
      simp only [Matrix.submatrix_apply]
      refine hU0 _ _ ?_
      simp only [Fin.lt_def, Fin.val_castLE] at hac ⊢
      exact hac
    · intro c
      simp only [Matrix.submatrix_apply]
      exact hU1 _
    · intro i a
      have ha := a.isLt
      show (s *ᵥ Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a)) i =
        ∑ c : Fin l, Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl c) i * U (Fin.castLE hl c) (Fin.castLE hl a)
      have h1 := congrFun (congrFun hsF i) (Fin.castLE hl a)
      simp only [Matrix.mul_apply, Formalism.QuantumDeterminants.Fm, Matrix.of_apply] at h1
      have h2 : (s *ᵥ Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a)) i =
          ∑ j, s i j * Formalism.QuantumDeterminants.fvec k r z (Fin.castLE hl a) j := rfl
      rw [h2, h1]
      refine Formalism.QuantumDeterminants.sum_fin_castLE hl _ ?_
      intro j hj
      show Formalism.QuantumDeterminants.fvec k r z j i * U j (Fin.castLE hl a) = 0
      rw [hU0 j (Fin.castLE hl a) ?_, mul_zero]
      rw [Fin.lt_def, Fin.val_castLE]
      omega
  ·
    rw [GlobalTheory.TensLen.cmp_mulVec_wedge, GlobalTheory.TensLen.sum_norm_wedge]
    refine Finset.prod_congr rfl (fun a _ => ?_)
    congr 1
    exact len_castLE hl (fun b : Fin (r + 1) =>
      (WithLp.toLp 2 (g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z b) : EuclideanSpace ℂ (Fin (2 * r + k + 1)))) a

end GlobalTheory.FlagPartialWedge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormalDegreeProportional
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.DegreeTie

open Formalism.FourierDecayAlt.P.HaarUniquenessConjugation

theorem map_phi_eq {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P Q : MatKR k r} (hP : IsCayley k r ε P)
    (hQ : IsCayley k r ε Q) : (Formalism.REAL.muG ε).map (phi ε P) = (Formalism.REAL.muG ε).map (phi ε Q) := by
  obtain ⟨hPu, hPJ⟩ := hP
  obtain ⟨hQu, hQJ⟩ := hQ

  set Pu := hPu.unit with hPu_def
  set Qu := hQu.unit with hQu_def
  have hQQ : Q * Q⁻¹ = 1 := by
    rw [← hQu.unit_spec, ← Matrix.coe_units_inv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hmJ : (P * Q⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * Q⁻¹) = Formalism.REAL.Jm ε := by
    have h1 : (Q⁻¹)ᴴ * Qᴴ = 1 := by
      rw [← Matrix.conjTranspose_mul, hQQ, Matrix.conjTranspose_one]
    calc (P * Q⁻¹)ᴴ * Formalism.REAL.Jm ε * (P * Q⁻¹) = (Q⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε * P) * Q⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = ((Q⁻¹)ᴴ * Qᴴ) * Formalism.REAL.Jm ε * (Q * Q⁻¹) := by
          rw [hPJ, ← hQJ]; simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [h1, hQQ, Matrix.one_mul, Matrix.mul_one]
  have hmem : Pu * Qu⁻¹ ∈ Formalism.REAL.UJ ε := by
    have hv : ((Pu * Qu⁻¹ : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ) :
        Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) = P * Q⁻¹ := by
      rw [Units.val_mul, Matrix.coe_units_inv, hPu_def, hQu_def, hPu.unit_spec, hQu.unit_spec]
    show Formalism.REAL.inUJ ε _
    rw [hv]
    exact hmJ
  set m : Formalism.REAL.UJ ε := ⟨Pu * Qu⁻¹, hmem⟩ with hm_def
  have hval : ∀ (A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hA : IsUnit A)
      (u : Formalism.REAL.UJ ε), phi ε A u = ((hA.unit⁻¹ * (u : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ) * hA.unit :
        (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := by
    intro A hA u
    rw [Units.val_mul, Units.val_mul, Matrix.coe_units_inv, hA.unit_spec]
    rfl
  have hconj : phi ε Q = phi ε P ∘ (fun u => m * u * m⁻¹) := by
    funext u
    rw [Function.comp_apply, hval Q hQu, hval P hPu]
    congr 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hm_def]
    rw [hPu_def, hQu_def]
    group <;> rfl
  have hcont : ∀ A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ, Continuous (phi ε A) := by
    intro A
    have : Continuous (fun u : Formalism.REAL.UJ ε =>
        ((u : (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)ˣ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) :=
      Units.continuous_val.comp continuous_subtype_val
    exact (continuous_const.matrix_mul this).matrix_mul continuous_const
  have hinv : (Formalism.REAL.muG ε).map (fun u => m * u * m⁻¹) = Formalism.REAL.muG ε := by
    have hL : Measurable (fun u : Formalism.REAL.UJ ε => m * u) := measurable_const_mul m
    have hR : Measurable (fun u : Formalism.REAL.UJ ε => u * m⁻¹) := measurable_mul_const m⁻¹
    calc (Formalism.REAL.muG ε).map (fun u => m * u * m⁻¹)
        = ((Formalism.REAL.muG ε).map (fun u => m * u)).map (fun u => u * m⁻¹) := by
          rw [Measure.map_map hR hL]; rfl
      _ = (Formalism.REAL.muG ε).map (fun u => u * m⁻¹) := by
          rw [MeasureTheory.map_mul_left_eq_self (Formalism.REAL.muG ε) m]
      _ = Formalism.REAL.muG ε := Formalism.REAL.indefinite_unitary_unimodular _ ε m⁻¹
  rw [hconj, ← Measure.map_map (hcont P).measurable (by
    exact (measurable_const_mul m).mul_const m⁻¹), hinv]

theorem deg_eq_mul_fdegH : Hyps → ∀ (D : D7) τ w w' θ (W : LocW D.R.k D.R.rS), cdScaleTie D → GoodW D τ w w' θ W → ∃ κ : ℝ, 0 < κ ∧ ∀ (lam : Fin (2 * D.R.rS + D.R.k + 1) → ℝ) (A : LocS W), GoodS D lam A → ∀ v : A.H, v ≠ 0 → A.deg = κ * PI.BesselPeriodGGP.fdegH W.μG A.σ v ∧ 0 < A.deg := by
  intro _ D τ w w' θ W _ hW

  by_cases hC : ∃ P0 : MatKR D.R.k D.R.rS, IsCayley D.R.k D.R.rS (epsSH D.R) P0
  swap
  · refine ⟨1, one_pos, ?_⟩
    intro lam A hA
    obtain ⟨P, hP, -⟩ := hA.2.2.2.2.2.2.2.2.2.2
    exact absurd ⟨P, hP⟩ hC
  obtain ⟨P0, hP0⟩ := hC
  have hP0det : IsUnit P0.det := (Matrix.isUnit_iff_isUnit_det P0).1 hP0.1
  obtain ⟨c, hc0, hctop, hμ⟩ :=
    GlobalTheory.BesselDegree.haar_eq_smul (ε := epsSH D.R) hP0det hP0.2 W.μG hW.2.2.2.2.2.2.1
  set cd : NNReal := D.s.cdScale _ (epsSH D.R) with hcd_def

  have hI : ∀ (P : MatKR D.R.k D.R.rS), IsCayley D.R.k D.R.rS (epsSH D.R) P →
      ∀ (F : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS → ℝ),
        ∫ x, F x ∂W.μG = c.toReal * ∫ u, F (phi (epsSH D.R) P u) ∂(Formalism.REAL.muG (epsSH D.R)) := by
    intro P hP F
    have hPP : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).1 hP.1)
    have hPP' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).1 hP.1)
    let h : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ ≃ₜ
        Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ :=
      { toFun := fun x => P⁻¹ * x * P
        invFun := fun x => P * x * P⁻¹
        left_inv := fun x => by
          simp only [← Matrix.mul_assoc, hPP, Matrix.one_mul]
          rw [Matrix.mul_assoc, hPP, Matrix.mul_one]
        right_inv := fun x => by
          simp only [← Matrix.mul_assoc, hPP', Matrix.one_mul]
          rw [Matrix.mul_assoc, hPP', Matrix.mul_one]
        continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
        continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
    have hemb : Topology.IsClosedEmbedding (phi (epsSH D.R) P) :=
      h.isClosedEmbedding.comp (Formalism.REAL.isClosedEmbeddingMatrix _ (epsSH D.R)).1
    rw [hμ, map_phi_eq hP0 hP, integral_smul_measure, smul_eq_mul,
      hemb.measurableEmbedding.integral_map]
  by_cases hcd : cd = 0
  · refine ⟨1, one_pos, ?_⟩
    intro lam A hA v hv
    obtain ⟨P, -, hF⟩ := hA.2.2.2.2.2.2.2.2.2.2
    have h2 := (hF.2 v v v v).2
    rw [← hcd_def] at h2
    rw [hcd, ENNReal.coe_zero, zero_smul, integral_zero_measure] at h2
    have hv' : (⟪v, v⟫_ℂ : ℂ) ≠ 0 := inner_self_ne_zero.2 hv
    have hd : (A.deg : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hF.1.ne'
    exact absurd h2.symm (div_ne_zero (mul_ne_zero hv' hv') hd)
  have hcpos : 0 < c.toReal := ENNReal.toReal_pos hc0 hctop
  have hcdpos : (0 : ℝ) < cd := by
    rw [NNReal.coe_pos]; exact pos_iff_ne_zero.2 hcd
  refine ⟨c.toReal / cd, div_pos hcpos hcdpos, ?_⟩
  intro lam A hA v hv
  obtain ⟨P, hP, hF⟩ := hA.2.2.2.2.2.2.2.2.2.2
  refine ⟨?_, hF.1⟩
  have h2 := (hF.2 v v v v).2
  rw [← hcd_def] at h2

  set J := ∫ u, ‖⟪v, A.σ (P⁻¹ * ((u : (Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ)ˣ) :
      Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) * P) v⟫_ℂ‖ ^ 2
      ∂(Formalism.REAL.muG (epsSH D.R)) with hJ
  have hJc : ((cd : ℝ) * J : ℂ) = (‖v‖ ^ 4 / A.deg : ℝ) := by
    have hin : (⟪v, v⟫_ℂ : ℂ) = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    have hint : ∫ g, coefOn (fun g => A.σ (P⁻¹ * g * P)) v v g * star (coefOn (fun g => A.σ (P⁻¹ * g * P)) v v g)
        ∂(Formalism.REAL.muG (epsSH D.R)) = ((J : ℝ) : ℂ) := by
      rw [hJ, ← integral_complex_ofReal]
      congr 1
      funext g
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      rfl
    rw [integral_smul_measure, hint, hin, ENNReal.coe_toReal, Complex.real_smul] at h2
    rw [h2]
    push_cast
    ring
  have hJr : (cd : ℝ) * J = ‖v‖ ^ 4 / A.deg := by exact_mod_cast hJc
  have hIv := hI P hP (fun x => ‖⟪v, A.σ (Matrix.of x) v⟫_ℂ‖ ^ 2)
  have hnv : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hdeg := hF.1
  unfold PI.BesselPeriodGGP.fdegH
  rw [hIv]
  change A.deg = c.toReal / cd * (‖v‖ ^ 4 / (c.toReal * J))
  have hJ' : J = ‖v‖ ^ 4 / A.deg / cd := by
    rw [← hJr]; field_simp
  rw [hJ']
  field_simp

end GlobalTheory.DegreeTie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagLeviMaxCompactClosedSubgroupsStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicFlagLevi_maxCompact_closed_subgroups : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), (∃ M : Subgroup (Formalism.REAL.UJ ε), (M : Set (Formalism.REAL.UJ ε)) = flagM ε W) ∧ IsClosed (flagM ε W) ∧ (∃ K : Subgroup (Formalism.REAL.UJ ε), (K : Set (Formalism.REAL.UJ ε)) = maxK ε) ∧ IsClosed (maxK ε) ∧ ∀ m ∈ flagM ε W, ∀ u ∈ flagN ε W, m * u * m⁻¹ ∈ flagN ε W := by
  first | exact @GlobalTheory.FlagLeviGroup.levi_compact_subgroups | exact GlobalTheory.FlagLeviGroup.levi_compact_subgroups | (intros; apply GlobalTheory.FlagLeviGroup.levi_compact_subgroups <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnipotentRadicalClosedSubgroupKeepsStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicFlagUnipotentRadical_closed_subgroup_keeps : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → (∃ N : Subgroup (Formalism.REAL.UJ ε), (N : Set (Formalism.REAL.UJ ε)) = flagN ε W) ∧ IsClosed (flagN ε W) ∧ ∀ u ∈ flagN ε W, ∀ i, ∀ y ∈ W i, uMat u *ᵥ y ∈ W i := by
  first | exact @GlobalTheory.FlagMeas.UnipRad.flagN_subgroup_closed_keeps | exact GlobalTheory.FlagMeas.UnipRad.flagN_subgroup_closed_keeps | (intros; apply GlobalTheory.FlagMeas.UnipRad.flagN_subgroup_closed_keeps <;> assumption)
end

