module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationLength
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0059
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0071
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0072
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0070
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0073

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchNormalisation
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

variable {n : ℕ}

def branchOrder {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ} (c : VarBranch I 1 q)
    (f : MvPolynomial (Fin n) ℂ) : ℕ∞ :=
  analyticOrderAt (fun τ : ℂ ↦ eval (c.toFun fun _ ↦ τ) f) 0

theorem branchOrder_eq_of_vanishesToOrder {I : Ideal (MvPolynomial (Fin n) ℂ)} {q : Fin n → ℂ}
    (c : VarBranch I 1 q) (f : MvPolynomial (Fin n) ℂ) (k : ℕ)
    (h : VanishesToOrder (fun t ↦ eval (c.toFun t) f) c.radius k) : branchOrder c f = k := by
  obtain ⟨H, hHd, hH0, hF⟩ := h
  let ι : ℂ → (Fin 1 → ℂ) := fun τ _ ↦ τ
  have hιd : Differentiable ℂ ι := differentiable_pi.2 fun _ ↦ differentiable_id
  have hball : ∀ τ ∈ Metric.ball (0 : ℂ) c.radius, ι τ ∈ Metric.ball (0 : Fin 1 → ℂ) c.radius := by
    intro τ hτ
    simpa [ι, Metric.mem_ball, dist_zero_right, pi_norm_const] using hτ
  have hg : AnalyticAt ℂ (H ∘ ι) 0 :=
    (hHd.comp hιd.differentiableOn hball).analyticAt (Metric.ball_mem_nhds 0 c.radius_pos)
  have hev : ∀ᶠ τ in 𝓝 (0 : ℂ), eval (c.toFun (ι τ)) f = (τ - 0) ^ k • (H ∘ ι) τ := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) c.radius_pos] with τ hτ
    refine (hF _ (hball τ hτ)).trans ?_
    simp [ι]
  have hF' : AnalyticAt ℂ (fun τ : ℂ ↦ eval (c.toFun (ι τ)) f) 0 :=
    AnalyticAt.congr (((analyticAt_id.sub analyticAt_const).pow k).smul hg) (hev.mono fun τ h ↦ h.symm)
  exact hF'.analyticOrderAt_eq_natCast.2
    ⟨H ∘ ι, hg, hH0 _ (hball 0 (Metric.mem_ball_self c.radius_pos)), hev⟩

def BranchNormalisation.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (m : ℕ) (c : Fin m → VarBranch I 1 q),
    IsRadicalAt I q → 0 < m →
    (∃ N ∈ 𝓝 q, zeroSet I ∩ N ⊆ ⋃ b, (c b).image) →
    (∀ b b', b ≠ b' → (c b).image ∩ (c b').image ⊆ {q}) →
      ringKrullDim (curveLocalRing I q) = 1 ∧
      (∀ f : MvPolynomial (Fin n) ℂ, (∀ b, branchOrder (c b) f ≠ ⊤) →
        algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f ∈ nonZeroDivisors (curveLocalRing I q)) ∧
      ∃ e : Fin m ≃ MaximalSpectrum (curveNormalisation I q), ∀ b,
        Module.length (curveLocalRing I q) (curveNormalisation I q ⧸ (e b).asIdeal) = 1 ∧
        ∀ f : MvPolynomial (Fin n) ℂ,
          Ring.ord (Localization.AtPrime (e b).asIdeal)
              (algebraMap (curveNormalisation I q) (Localization.AtPrime (e b).asIdeal)
                (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                  (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) =
            branchOrder (c b) f

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveRegularOffFinite
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def CurveRegularOffFinite.Statement : Prop :=
  ∀ (n : ℕ) (W : Ideal (MvPolynomial (Fin n) ℂ)), W.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = 1 →
      ∃ F : Set (Fin n → ℂ), F.Finite ∧ ∀ x ∈ zeroSet W, x ∉ F →
        ∃ (A : (Fin n → ℂ) →L[ℂ] ℂ) (O : Set ℂ) (V : Set (Fin n → ℂ)) (g : ℂ → Fin n → ℂ),
          IsOpen O ∧ IsOpen V ∧ x ∈ V ∧ AnalyticOnNhd ℂ g O ∧ (∀ y ∈ O, A (g y) = y) ∧
            zeroSet W ∩ V = g '' O

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteGermProjectionObjects
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

noncomputable section

def coordGerm {σ : Type} [Fintype σ] (w : σ → ℂ) (i : σ) : holGerms w :=
  ⟨↑(fun z : σ → ℂ => z i), fun z => z i,
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticAt w, rfl⟩

def IsFiniteGermProjection {σ : Type} [Fintype σ] (w : σ → ℂ) (P : Ideal (holGerms w)) {d : ℕ}
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) : Prop :=
  (∀ φ : holGerms (A w), germPull A (A.analyticAt w) rfl φ ∈ P → φ = 0) ∧
  (∀ ψ : holGerms w, ∃ F : MvPolynomial σ (holGerms (A w)),
      ψ - MvPolynomial.eval₂ (germPull A (A.analyticAt w) rfl) (coordGerm w) F ∈ P) ∧
  (∀ i : σ, ∃ q : Polynomial (holGerms (A w)), q.Monic ∧
      q.eval₂ (germPull A (A.analyticAt w) rfl) (coordGerm w i) ∈ P)

theorem isFiniteGermProjection_bot {σ : Type} [Fintype σ] (w : σ → ℂ) :
    ∃ (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)), IsFiniteGermProjection w ⊥ A := by
  classical
  let e : (σ → ℂ) ≃L[ℂ] (Fin (Fintype.card σ) → ℂ) :=
    (LinearEquiv.funCongrLeft ℂ ℂ (Fintype.equivFin σ).symm).toContinuousLinearEquiv
  let A : (σ → ℂ) →L[ℂ] (Fin (Fintype.card σ) → ℂ) := e
  have hA : AnalyticAt ℂ (⇑A) w := A.analyticAt w
  have hB : AnalyticAt ℂ (⇑e.symm) (A w) := e.symm.analyticAt _
  have hBe : e.symm (A w) = w := e.symm_apply_apply w
  have back : ∀ φ : holGerms (A w), germPull e.symm hB hBe (germPull A hA rfl φ) = φ := fun φ =>
    germPull_germPull _ _ hA rfl hB hBe (fun y => e.apply_symm_apply y) φ
  have fwd : ∀ ψ : holGerms w, germPull A hA rfl (germPull e.symm hB hBe ψ) = ψ := fun ψ =>
    germPull_germPull _ _ hB hBe hA rfl (fun z => e.symm_apply_apply z) ψ
  refine ⟨Fintype.card σ, A, ?_, ?_, ?_⟩
  · intro φ hφ
    rw [Ideal.mem_bot] at hφ
    rw [← back φ, hφ, map_zero]
  · intro ψ
    refine ⟨MvPolynomial.C (germPull e.symm hB hBe ψ), ?_⟩
    rw [MvPolynomial.eval₂_C, fwd, sub_self]
    exact Ideal.zero_mem _
  · intro i
    have hc : AnalyticAt ℂ (fun y : Fin (Fintype.card σ) → ℂ => e.symm y i) (A w) :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).comp
        (e.symm : (Fin (Fintype.card σ) → ℂ) →L[ℂ] (σ → ℂ))).analyticAt _
    let c : holGerms (A w) := ⟨↑(fun y : Fin (Fintype.card σ) → ℂ => e.symm y i), _, hc, rfl⟩
    refine ⟨Polynomial.X - Polynomial.C c, Polynomial.monic_X_sub_C c, ?_⟩
    rw [Ideal.mem_bot, Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero]
    apply Subtype.ext
    rw [germPull_coe _ hA rfl c _ rfl]
    show (↑(fun z : σ → ℂ => z i) : Germ (𝓝 w) ℂ) = ↑((fun y => e.symm y i) ∘ ⇑A)
    congr 1
    funext z
    simp [A]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StLocalDimComponentBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def LocalDimComponentBound.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ), q ∈ zeroSet I →
    ∃ W : Ideal (MvPolynomial (Fin n) ℂ), W.IsPrime ∧ I ≤ W ∧ q ∈ zeroSet W ∧
      ringKrullDim (curveLocalRing I q) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalCodimOneCompleteIntersection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def NormalCodimOneCompleteIntersection.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (P Q : Ideal (MvPolynomial σ ℂ)) (e : ℕ), P.IsPrime → Q.IsPrime → P ≤ Q →
    IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ P) →
    ringKrullDim (MvPolynomial σ ℂ ⧸ P) = (e + 1 : ℕ) → ringKrullDim (MvPolynomial σ ℂ ⧸ Q) = (e : ℕ) →
      ∃ (c : ℕ) (f : Fin c → MvPolynomial σ ℂ) (h : MvPolynomial σ ℂ),
        c + (e + 1) = Fintype.card σ ∧ (∀ j, f j ∈ P) ∧ h ∉ Q ∧
          ∀ p ∈ P, ∃ k : ℕ, h ^ k * p ∈ Ideal.span (Set.range f)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelGoodPointChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def NormalModelGoodPointChart.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (w : Fin n ⊕ Fin M.m → ℂ), NormalModelDivisorGoodPoint M u d w → NormalDivisorChartAtPoint M u d w

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelGoodPointGeneric
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def NormalModelGoodPointGeneric.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
      ∃ B : Ideal (MvPolynomial (Fin n ⊕ Fin M.m) ℂ),
        M.ideal ⊔ Ideal.span {rename (Sum.inl : Fin n → Fin n ⊕ Fin M.m) (linForm u)} ≤ B ∧
        ringKrullDim (MvPolynomial (Fin n ⊕ Fin M.m) ℂ ⧸ B) < (d : ℕ) ∧
        ∀ w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal, linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords w) = 0 →
          w ∉ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn B → NormalModelDivisorGoodPoint M u d w

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveFormFullBranchConstant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def PrimitiveFormFullBranchConstant.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X W N' : Set (σ → ℂ)) (k : ℕ) (f : Fin k → (σ → ℂ) → ℂ) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ)
    (δ : (Fin d → ℂ) → ℂ) (q : σ → Fin N → (Fin d → ℂ) → ℂ) (B O : Set (Fin d → ℂ)) (r : (Fin d → ℂ) → ℂ),
    IsOpen W → IsOpen N' → closure W ⊆ N' → (∀ i, AnalyticOnNhd ℂ (f i) N') →
    X ∩ N' = {z | z ∈ N' ∧ ∀ i, f i z = 0} →
    (∀ z ∈ X ∩ closure W, A z ∈ B → z ∈ W) →
    (∀ z ∈ X ∩ W, ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) →
    IsOpen B → (∀ j, AnalyticOnNhd ℂ (a j) B) → AnalyticOnNhd ℂ δ B → (∀ i j, AnalyticOnNhd ℂ (q i j) B) →
    IsOpen O → IsPreconnected O → O ⊆ B → (∀ s ∈ O, δ s ≠ 0) →
    (∀ s ∈ O, (Polynomial.X ^ N + ∑ j, Polynomial.C (a j s) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) →
    AnalyticOnNhd ℂ r O → (∀ s ∈ O, r s ^ N + ∑ j, a j s * r s ^ (j : ℕ) = 0) →
    ∀ s ∈ O, ∀ s' ∈ O,
      (PrimitiveFormRootFull X W A ℓ δ q s (r s) ↔ PrimitiveFormRootFull X W A ℓ δ q s' (r s'))

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveFormFullRootFactor
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def PrimitiveFormFullRootFactor.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (d : ℕ) (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)),
    IsAnalyticNear X w →
    (∃ W ∈ 𝓝 w, ∀ x ∈ X ∩ W, A x = A w → x = w) →
    ∀ (ℓ : (σ → ℂ) →L[ℂ] ℂ) (N : ℕ) (a : Fin N → (Fin d → ℂ) → ℂ) (δ : (Fin d → ℂ) → ℂ)
      (q : σ → Fin N → (Fin d → ℂ) → ℂ),
      (∀ j, AnalyticAt ℂ (a j) (A w)) → AnalyticAt ℂ δ (A w) → (∀ i j, AnalyticAt ℂ (q i j) (A w)) →
      (¬ ∀ᶠ y in 𝓝 (A w), δ y = 0) →
      (∀ᶠ z in 𝓝 w, z ∈ X → ℓ z ^ N + ∑ j, a j (A z) * ℓ z ^ (j : ℕ) = 0) →
      (∀ᶠ y in 𝓝 (A w), δ y ≠ 0 →
        (Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) : Polynomial ℂ).Separable) →
      (∀ i, ∀ᶠ z in 𝓝 w, z ∈ X → δ (A z) * z i = ∑ j, q i j (A z) * ℓ z ^ (j : ℕ)) →
      ∃ (W : Set (σ → ℂ)) (B : Set (Fin d → ℂ)) (C E : (Fin d → ℂ) → ℂ → ℂ),
        IsOpen W ∧ w ∈ W ∧ IsOpen B ∧ A w ∈ B ∧
        (∀ t ∈ B, ∀ T : ℂ, AnalyticAt ℂ (fun u : (Fin d → ℂ) × ℂ => C u.1 u.2) (t, T) ∧
          AnalyticAt ℂ (fun u : (Fin d → ℂ) × ℂ => E u.1 u.2) (t, T)) ∧
        (∀ t ∈ B, ∀ T : ℂ, C t T * E t T = T ^ N + ∑ j, a j t * T ^ (j : ℕ)) ∧
        ∀ t ∈ B, δ t ≠ 0 → ∀ τ : ℂ, τ ^ N + ∑ j, a j t * τ ^ (j : ℕ) = 0 →
          (C t τ = 0 ↔ PrimitiveFormRootFull X W A ℓ δ q t τ) ∧
          (E t τ = 0 ↔ ¬ PrimitiveFormRootFull X W A ℓ δ q t τ)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegLelongAnnulus
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

theorem ne_of_mem_euclBall_diff {n : ℕ} {x z : Fin n → ℂ} {r s : ℝ} (hr : 0 < r)
    (hz : z ∈ euclBall x s \ euclBall x r) : z ≠ x := by
  rintro rfl
  exact hz.2 (mem_euclBall_self z hr)

def RegLelongAnnulus.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin (d + 1)) (Fin n) ℂ)
    (u : Fin n → ℂ) (ε : ℝ) (x : Fin n → ℂ) (r s : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → IsFiniteProjection J A →
    0 < ε → 0 < r → r ≤ s →
      r ^ (2 * d) * (∫ y, chartDens J A ((euclBall x s).indicator fun _ => 1)
          (vecCons (logReg u ε) fun _ => euclPot) y) -
        s ^ (2 * d) * (∫ y, chartDens J A ((euclBall x r).indicator fun _ => 1)
          (vecCons (logReg u ε) fun _ => euclPot) y) =
      r ^ (2 * d) * s ^ (2 * d) * ∫ y, chartDens J A ((euclBall x s \ euclBall x r).indicator fun _ => 1)
          (vecCons (logReg u ε) fun _ => logDistSq x) y

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceBranchInt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def SliceBranchInt.Statement : Prop :=
  ∀ (n d : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u q : Fin n → ℂ) (m : ℕ)
    (γ : Fin m → VarBranch J (d + 1) q) (ord : Fin m → ℕ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes → q ∈ zeroSet W →
    (∃ N ∈ 𝓝 q, ∀ x ∈ zeroSet J ∩ N, linEval u x = 0 → x ∈ zeroSet W) →
    (∃ N ∈ 𝓝 q, zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) →
    (∃ N ∈ 𝓝 q, ∀ b, zeroSet W ∩ N ⊆ (γ b).slice) →
    (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {x | linEval u x = 0}) →
    (∀ b, VanishesToOrder (fun t => linEval u ((γ b).toFun t)) (γ b).radius (ord b)) →
      ∃ N ∈ 𝓝 q, ∀ (b : Fin m) (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ),
        ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ N →
        (∀ i, SmoothNear (zeroSet J) (φ i)) →
          varInt W d f φ =
            ∫ w in Metric.ball (0 : Fin d → ℂ) (γ b).radius,
              f ((γ b).toFun (ReciprocityTheory.AnForm.A.hypIncl w)) *
                ReciprocityTheory.AnForm.A.densHyp (fun k => φ k ∘ (γ b).toFun) w

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceMultGeneral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

noncomputable section

def SliceMultGeneral.Statement : Prop :=
  ∀ (n d : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes →
      ∃ f : MvPolynomial (Fin n) ℂ, f ∉ W ∧ ∀ q ∈ zeroSet W, eval q f ≠ 0 →
        ∃ O : Set (Matrix (Fin d) (Fin n) ℂ), IsOpen O ∧ Dense O ∧
          ∀ L ∈ O, localMult (J ⊔ Ideal.span {linForm u}) W =
            localMult (sliceIdeal J L q ⊔ Ideal.span {linForm u}) (RingHom.ker (eval q))

end

end GroundTheory.Heights₂.Heights
end

