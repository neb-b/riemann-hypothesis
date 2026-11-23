module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0033
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0006
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0030
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PHolGermsDomain
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0031

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTangentGraphLowerDensity
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

def TangentGraphLowerDensity.inPart {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ I :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : I => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i : I => innerSL ℂ (b i))

def TangentGraphLowerDensity.outPart {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ {j : Fin n // j ∉ I} :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : {j : Fin n // j ∉ I} => ℂ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j : {j : Fin n // j ∉ I} => innerSL ℂ (b j))

theorem TangentGraphLowerDensity.inPart_apply {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) (i : I) :
    TangentGraphLowerDensity.inPart b I z i = inner ℂ (b i) z := by
  simp [TangentGraphLowerDensity.inPart]

theorem TangentGraphLowerDensity.outPart_apply {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) (j : {j : Fin n // j ∉ I}) :
    TangentGraphLowerDensity.outPart b I z j = inner ℂ (b j) z := by
  simp [TangentGraphLowerDensity.outPart]

theorem TangentGraphLowerDensity.inPart_eq_toLp {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) :
    TangentGraphLowerDensity.inPart b I z = WithLp.toLp 2 (frameProj b I z) := by
  refine PiLp.ext fun i => ?_
  simp [TangentGraphLowerDensity.inPart_apply, frameProj]

theorem TangentGraphLowerDensity.norm_sq_split {n : ℕ}
    (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I : Finset (Fin n))
    (z : EuclideanSpace ℂ (Fin n)) :
    ‖z‖ ^ 2 = ‖TangentGraphLowerDensity.inPart b I z‖ ^ 2 + ‖TangentGraphLowerDensity.outPart b I z‖ ^ 2 := by
  classical
  rw [← b.repr.norm_map z, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [TangentGraphLowerDensity.inPart_apply, TangentGraphLowerDensity.outPart_apply,
    OrthonormalBasis.repr_apply_apply]
  convert (Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ I) (fun i => ‖inner ℂ (b i) z‖ ^ 2)).symm using 3
  congr 1; exact Subsingleton.elim _ _

theorem TangentGraphLowerDensity.proof : TangentGraphLowerDensity.Statement := by
  intro n d b I₀ S Ω V g w₀ hcard hΩ _hV hw₀ hg hproj hSV htan θ hθ
  classical
  set P := TangentGraphLowerDensity.inPart b I₀ with hPdef
  set Q := TangentGraphLowerDensity.outPart b I₀ with hQdef
  have hgd : DifferentiableAt ℂ g w₀ := hg.differentiableAt (hΩ.mem_nhds hw₀)

  have hQ0 : Q.comp (fderiv ℂ g w₀) = 0 := by
    refine ContinuousLinearMap.ext fun v => PiLp.ext fun j => ?_
    have h1 : HasFDerivAt (fun w => inner ℂ (b j) (g w))
        ((innerSL ℂ (b (j : Fin n))).comp (fderiv ℂ g w₀)) w₀ :=
      (innerSL ℂ (b (j : Fin n))).hasFDerivAt.comp w₀ hgd.hasFDerivAt
    have h2 := h1.fderiv
    rw [htan j j.2] at h2
    have h3 := congrArg (fun L => L v) h2
    simpa [hQdef, TangentGraphLowerDensity.outPart_apply] using h3.symm
  have hQd : HasFDerivAt (fun w => Q (g w)) (0 : (I₀ → ℂ) →L[ℂ] EuclideanSpace ℂ {j : Fin n // j ∉ I₀}) w₀ := by
    have h := Q.hasFDerivAt.comp w₀ hgd.hasFDerivAt
    rw [hQ0] at h
    exact h

  obtain ⟨η, hη, hθη⟩ : ∃ η : ℝ, 0 < η ∧ θ * (1 + η) ^ (2 * d) < 1 := by
    have hc : Continuous fun η : ℝ => θ * (1 + η) ^ (2 * d) := by fun_prop
    have h0 : ∀ᶠ η in 𝓝 (0 : ℝ), θ * (1 + η) ^ (2 * d) < 1 :=
      hc.continuousAt.eventually_lt continuousAt_const (by simpa using hθ.2)
    have h0' : ∀ᶠ η in 𝓝[>] (0 : ℝ), θ * (1 + η) ^ (2 * d) < 1 := nhdsWithin_le_nhds h0
    obtain ⟨η, h1, h2⟩ := (h0'.and (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))).exists
    exact ⟨η, h2, h1⟩
  have hlo := hasFDerivAt_iff_isLittleO.1 hQd
  have hev : ∀ᶠ w in 𝓝 w₀, ‖Q (g w) - Q (g w₀)‖ ≤ η * ‖w - w₀‖ ∧ w ∈ Ω := by
    refine ((hlo.def hη).mono fun w hw => ?_).and (hΩ.mem_nhds hw₀)
    simpa using hw
  obtain ⟨δ, hδ, hδw⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨(1 + η) * δ, by positivity, fun ρ hρ => ?_⟩
  have h1η : 0 < 1 + η := by linarith
  set s := ρ / (1 + η) with hs
  have hs0 : 0 < s := div_pos hρ.1 h1η
  have hsδ : s < δ := by
    rw [hs, div_lt_iff₀ h1η]
    linarith [hρ.2]
  set x₀ : EuclideanSpace ℂ I₀ := WithLp.toLp 2 w₀ with hx₀
  have hPx : ∀ w ∈ Ω, P (g w) = WithLp.toLp 2 w := fun w hw => by
    rw [hPdef, TangentGraphLowerDensity.inPart_eq_toLp, hproj w hw]

  have hsub : Metric.ball x₀ s ⊆ P '' (S ∩ Metric.ball (g w₀) ρ) := by
    intro v hv
    have hv' : ‖v - x₀‖ < s := by rwa [Metric.mem_ball, dist_eq_norm] at hv
    have hww : ‖WithLp.ofLp v - w₀‖ ≤ ‖v - x₀‖ := by
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
      simpa [hx₀] using PiLp.norm_apply_le (v - x₀) i
    have hwδ : dist (WithLp.ofLp v) w₀ < δ := by
      rw [dist_eq_norm]
      linarith
    obtain ⟨hQw, hwΩ⟩ := hδw hwδ
    refine ⟨g (WithLp.ofLp v), ⟨?_, ?_⟩, by rw [hPx _ hwΩ, WithLp.toLp_ofLp]⟩
    · have hm : g (WithLp.ofLp v) ∈ S ∩ V := hSV ▸ Set.mem_image_of_mem g hwΩ
      exact hm.1
    · rw [Metric.mem_ball, dist_eq_norm]
      have hsplit := TangentGraphLowerDensity.norm_sq_split b I₀ (g (WithLp.ofLp v) - g w₀)
      have hPd : P (g (WithLp.ofLp v) - g w₀) = v - x₀ := by
        rw [map_sub, hPx _ hwΩ, hPx _ hw₀, WithLp.toLp_ofLp]
      have hQd' : Q (g (WithLp.ofLp v) - g w₀) = Q (g (WithLp.ofLp v)) - Q (g w₀) := map_sub _ _ _
      rw [← hPdef, ← hQdef, hPd, hQd'] at hsplit
      have hle : ‖g (WithLp.ofLp v) - g w₀‖ ≤ ‖v - x₀‖ + ‖Q (g (WithLp.ofLp v)) - Q (g w₀)‖ := by
        nlinarith [norm_nonneg (g (WithLp.ofLp v) - g w₀), norm_nonneg (v - x₀),
          norm_nonneg (Q (g (WithLp.ofLp v)) - Q (g w₀))]
      calc ‖g (WithLp.ofLp v) - g w₀‖ ≤ ‖v - x₀‖ + η * ‖v - x₀‖ := by nlinarith
        _ = (1 + η) * ‖v - x₀‖ := by ring
        _ < (1 + η) * s := by gcongr
        _ = ρ := by rw [hs]; field_simp

  have hd0 : (0 : ℝ) ≤ ((2 * d : ℕ) : ℝ) := Nat.cast_nonneg _
  have hcardI : Fintype.card I₀ = d := by rw [Fintype.card_coe, hcard]
  let L := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Fintype.equivFinOfCardEq hcardI)
  have hball : μH[((2 * d : ℕ) : ℝ)] (Metric.ball x₀ s) =
      ENNReal.ofReal (s ^ (2 * d)) *
        μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1) := by
    rw [← VarietyLelongMono.euclBall_measure d (L x₀) hs0, ← L.image_ball,
      L.isometry.hausdorffMeasure_image (Or.inl hd0)]
  have hLip : LipschitzWith 1 P := LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, NNReal.coe_one, one_mul]
    have h := TangentGraphLowerDensity.norm_sq_split b I₀ (x - y)
    rw [← hPdef, ← hQdef] at h
    nlinarith [norm_nonneg (P (x - y)), norm_nonneg (x - y), norm_nonneg (Q (x - y))]
  have hreal : θ * ρ ^ (2 * d) ≤ s ^ (2 * d) := by
    have hpos : 0 < (1 + η) ^ (2 * d) := by positivity
    have hρp : 0 ≤ ρ ^ (2 * d) := by have := hρ.1; positivity
    rw [hs, div_pow, le_div_iff₀ hpos]
    calc θ * ρ ^ (2 * d) * (1 + η) ^ (2 * d) = ρ ^ (2 * d) * (θ * (1 + η) ^ (2 * d)) := by ring
      _ ≤ ρ ^ (2 * d) * 1 := by gcongr
      _ = ρ ^ (2 * d) := mul_one _
  calc ENNReal.ofReal (θ * ρ ^ (2 * d)) *
        μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1)
      ≤ ENNReal.ofReal (s ^ (2 * d)) *
        μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1) := by
        gcongr
    _ = μH[((2 * d : ℕ) : ℝ)] (Metric.ball x₀ s) := hball.symm
    _ ≤ μH[((2 * d : ℕ) : ℝ)] (P '' (S ∩ Metric.ball (g w₀) ρ)) := measure_mono hsub
    _ ≤ μH[((2 * d : ℕ) : ℝ)] (S ∩ Metric.ball (g w₀) ρ) := by
        have h := hLip.hausdorffMeasure_image_le hd0 (S ∩ Metric.ball (g w₀) ρ)
        simpa using h

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarSlabMeasure
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

theorem VarSlabMeasure.proof (hV : VarietySlabMeasure.Statement) : VarSlabMeasure.Statement := by
  intro n d J u R hJ hd hu
  obtain ⟨C, α, -, hα, hb⟩ := hV n d J u hJ hd.le hu R
  refine ⟨C, α, hα, fun ε hε hε1 => ?_⟩
  have hset : zeroSetEuc J ∩ {z | ‖z‖ ≤ R} ∩ {z | ‖∑ j, u j * z j‖ ≤ ε} =
      {z | z ∈ zeroSetEuc J ∧ ‖z‖ ≤ R ∧ ‖∑ j, u j * z j‖ ≤ ε} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_assoc]
  rw [hset]
  exact hb ε hε hε1

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.RingKrullDimQuotBotOne
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory Matrix
open scoped ENNReal

noncomputable section

def pairPt {k m : ℕ} (x : EuclideanSpace ℝ (Fin k)) (y : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin k ⊕ Fin m) :=
  WithLp.toLp 2 (Sum.elim (fun i => x i) (fun j => y j))

def coordGraph {n : ℕ} (P : Finset (Fin n)) (Ω : Set (P → ℂ)) (F : (P → ℂ) → Fin n → ℂ) :
    Set (EuclideanSpace ℂ (Fin n)) :=
  {z | (fun i : P => z i) ∈ Ω ∧ ∀ j, j ∉ P → z j = F (fun i : P => z i) j}

def frameProj {n : ℕ} (e : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (z : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ I :=
  WithLp.toLp 2 (fun i : I => e.repr z i)

def ProjectionFormula.Statement : Prop :=
  ∀ (n d : ℕ) (P : Finset (Fin n)) (Ω : Set (P → ℂ)) (F : (P → ℂ) → Fin n → ℂ),
    P.card = d → IsOpen Ω → DifferentiableOn ℂ F Ω →
    ∀ (e : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
      (B : Set (EuclideanSpace ℂ (Fin n))), MeasurableSet B →
      Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ) (coordGraph P Ω F ∩ B) =
        ∑ I ∈ Finset.powersetCard d (Finset.univ : Finset (Fin n)),
          ∫⁻ x : EuclideanSpace ℂ I,
            (({z | z ∈ coordGraph P Ω F ∩ B ∧ frameProj e I z = x}.encard : ℕ∞) : ℝ≥0∞)
            ∂(Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ))


def PolySublevel.Statement : Prop :=
  ∀ (d : ℕ) (Q : MvPolynomial (Fin d) ℂ), Q ≠ 0 → ∀ R : ℝ, 0 < R →
    ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∀ η : ℝ, 0 < η → η ≤ 1 →
      Measure.hausdorffMeasure ((2 * d : ℕ) : ℝ)
          {x : EuclideanSpace ℂ (Fin d) | x ∈ Metric.ball 0 R ∧ ‖eval (fun i => x i) Q‖ ≤ η} ≤
        ENNReal.ofReal (C * η ^ α)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchInverseOffHypersurface
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

def BranchInverseOffHypersurface.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (k : ℕ),
    I.IsPrime → ringKrullDim (MvPolynomial σ ℂ ⧸ I) = (k : ℕ) →
    ∃ h' : MvPolynomial σ ℂ, h' ∉ I ∧
      ∀ (U : Set (Fin k → ℂ)) (φ : (Fin k → ℂ) → σ → ℂ) (ψ : (σ → ℂ) → Fin k → ℂ),
        IsOpen U → DifferentiableOn ℂ φ U → Set.InjOn φ U → Set.MapsTo φ U (zeroSetIn I) →
        (∀ t ∈ U, ψ (φ t) = t) →
        HolomorphicOnSubset ψ ((φ '' U) \ {z | eval z h' = 0})

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteProjectionOffZerosDense
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def FiniteProjectionOffZerosDense.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w → GermIrreducibleAt X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) →
    ∀ δ : (Fin d → ℂ) → ℂ, AnalyticAt ℂ δ (A w) → (¬ ∀ᶠ y in 𝓝 (A w), δ y = 0) →
      ∃ N ∈ 𝓝 w, X ∩ N ⊆ closure {z | z ∈ X ∧ δ (A z) ≠ 0}

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteProjectionSheetedClosureEquations
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def FiniteProjectionSheetedClosureEquations.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    (∀ h : (Fin d → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ X → h (A z) = 0) →
        ∀ᶠ y in 𝓝 (A w), h y = 0) →
    ∀ δ : (Fin d → ℂ) → ℂ, AnalyticAt ℂ δ (A w) →
      (∃ M ∈ 𝓝 w, ∀ y ∈ X ∩ M, δ (A y) ≠ 0 → ∃ (O : Set (Fin d → ℂ)) (V : Set (σ → ℂ))
        (g : (Fin d → ℂ) → σ → ℂ), IsOpen O ∧ IsOpen V ∧ y ∈ V ∧ AnalyticOnNhd ℂ g O ∧
          (∀ t ∈ O, A (g t) = t) ∧ X ∩ V = g '' O) →
      ∃ (m : ℕ) (c : Fin m → (σ → ℂ) → ℂ), (∀ k, AnalyticAt ℂ (c k) w) ∧
        (∀ᶠ z in 𝓝 w, z ∈ X → δ (A z) ≠ 0 → ∀ k, c k z = 0) ∧
        (∀ᶠ z in 𝓝 w, z ∈ X → (∀ k, c k z = 0) → z ∈ closure {x | x ∈ X ∧ δ (A x) ≠ 0})

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermCompletionEquiv
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def GermCompletionEquiv.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ),
    ∃ e : AdicCompletion (germQuotPointIdeal I w) (holGerms w ⧸ I.map (polyGerm w)) ≃+*
        AdicCompletion (polyPointIdeal I w) (MvPolynomial σ ℂ ⧸ I),
      ∀ q : MvPolynomial σ ℂ,
        e (AdicCompletion.of (germQuotPointIdeal I w) (holGerms w ⧸ I.map (polyGerm w))
            (Ideal.Quotient.mk (I.map (polyGerm w)) (polyGerm w q))) =
          AdicCompletion.of (polyPointIdeal I w) (MvPolynomial σ ℂ ⧸ I) (Ideal.Quotient.mk I q)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGermWeierstrassDivision
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

def pointWithLast {σ : Type} (z : σ → ℂ) (t : ℂ) : Option σ → ℂ
  | none => t
  | some i => z i

def WeierstrassDivision.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (d : ℕ) (f g : (Option σ → ℂ) → ℂ),
    AnalyticAt ℂ f 0 → AnalyticAt ℂ g 0 →
    analyticOrderAt (fun t => f (pointWithLast 0 t)) 0 = d →
    ∃ (q : (Option σ → ℂ) → ℂ) (a : Fin d → (σ → ℂ) → ℂ),
      AnalyticAt ℂ q 0 ∧ (∀ j, AnalyticAt ℂ (a j) 0) ∧
      ∀ᶠ x in 𝓝 (0 : Option σ → ℂ),
        g x = q x * f x + ∑ j : Fin d, a j (fun i => x (some i)) * x none ^ (j : ℕ)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolGermsNoetherian
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def HolGermsNoetherian.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ), IsNoetherianRing (holGerms w)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StHolGermsUFD
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

def HolGermsUFD.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ), UniqueFactorizationMonoid (holGerms w)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalGraphProjectionMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

noncomputable section


open Classical in
def LocalGraphProjectionMass.Statement : Prop :=
  ∀ (n d : ℕ) (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I₀ : Finset (Fin n))
    (S : Set (EuclideanSpace ℂ (Fin n))), I₀.card = d →
    (∀ z ∈ S, ∃ (Ω : Set (I₀ → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n)))
      (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)), IsOpen Ω ∧ IsOpen V ∧ z ∈ V ∧
        DifferentiableOn ℂ g Ω ∧ (∀ w ∈ Ω, frameProj b I₀ (g w) = w) ∧ S ∩ V = g '' Ω) →
    ∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ B : Set (EuclideanSpace ℂ (Fin n)), MeasurableSet B →
      μH[((2 * d : ℕ) : ℝ)] (S ∩ B) ≤
        ∑ s ∈ Finset.univ.filter (fun s : Fin d → Fin n => StrictMono s),
          (⨆ x : EuclideanSpace ℂ (Fin d),
              (({z | z ∈ S ∩ B ∧ rowsProj U s z = x}.encard : ℕ∞) : ℝ≥0∞)) *
            μH[((2 * d : ℕ) : ℝ)] (rowsProj U s '' (S ∩ B))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPolyGermPointPow
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

def PolyGermPointPow.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (w : σ → ℂ) (k : ℕ) (q : MvPolynomial σ ℂ),
    polyGerm w q ∈ holGermPointIdeal w ^ k → q ∈ RingHom.ker (MvPolynomial.eval w) ^ k

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

