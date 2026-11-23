module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0020

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSheetPieceReachesCentre
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def SheetPieceReachesCentre.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (B : Set (σ → ℂ)) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ)) (δ : (Fin d → ℂ) → ℂ) (N : ℕ)
    (U V : Set (σ → ℂ)),
    IsLocalParametrisation X w B A D δ N → IsOpen U → IsOpen V →
    {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ⊆ U ∪ V → {x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ (U ∩ V) = ∅ →
    ({x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ U).Nonempty →
      w ∈ closure ({x | x ∈ X ∩ B ∧ δ (A x) ≠ 0} ∩ U)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTangentGraphLowerDensity
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory
open scoped ENNReal

noncomputable section

def TangentGraphLowerDensity.Statement : Prop :=
  ∀ (n d : ℕ) (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I₀ : Finset (Fin n))
    (S : Set (EuclideanSpace ℂ (Fin n))) (Ω : Set (I₀ → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n)))
    (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)) (w₀ : I₀ → ℂ),
    I₀.card = d → IsOpen Ω → IsOpen V → w₀ ∈ Ω → DifferentiableOn ℂ g Ω →
    (∀ w ∈ Ω, frameProj b I₀ (g w) = w) → S ∩ V = g '' Ω →
    (∀ j ∉ I₀, fderiv ℂ (fun w => inner ℂ (b j) (g w)) w₀ = 0) →
    ∀ θ ∈ Set.Ioo (0 : ℝ) 1, ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ ρ ∈ Set.Ioo (0 : ℝ) r₀,
      ENNReal.ofReal (θ * ρ ^ (2 * d)) *
          μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1) ≤
        μH[((2 * d : ℕ) : ℝ)] (S ∩ Metric.ball (g w₀) ρ)

theorem TangentGraphLowerDensity.unitBall_pos (d : ℕ) :
    0 < μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1) := by
  have h : ((2 * d : ℕ) : ℝ) = ((Module.finrank ℝ (EuclideanSpace ℂ (Fin d)) : ℕ) : ℝ) := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ (Fin d)), Complex.finrank_real_complex,
      finrank_euclideanSpace_fin]
  rw [h]
  exact Metric.isOpen_ball.measure_pos _ ⟨0, Metric.mem_ball_self one_pos⟩

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUnbranchedFibreSections
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology

def UnbranchedFibreSections.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (X : Set (σ → ℂ)) (w : σ → ℂ) (B : Set (σ → ℂ)) (d : ℕ)
    (A : (σ → ℂ) →L[ℂ] (Fin d → ℂ)) (D : Set (Fin d → ℂ)) (δ : (Fin d → ℂ) → ℂ) (N : ℕ),
    IsLocalParametrisation X w B A D δ N → ∀ y₀ ∈ D, δ y₀ ≠ 0 →
    ∃ (r : ℝ) (g : Fin N → (Fin d → ℂ) → σ → ℂ), 0 < r ∧ Metric.ball y₀ r ⊆ D ∧
      (∀ y ∈ Metric.ball y₀ r, δ y ≠ 0) ∧ (∀ i, AnalyticOnNhd ℂ (g i) (Metric.ball y₀ r)) ∧
      ∀ y ∈ Metric.ball y₀ r, Function.Injective (fun i => g i y) ∧
        {x | x ∈ X ∩ B ∧ A x = y} = Set.range (fun i => g i y)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarSlabMeasure
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

noncomputable section

def VarSlabMeasure.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (R : ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → linForm u ∉ J →
      ∃ C α : ℝ, 0 < α ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ {z | ‖z‖ ≤ R} ∩ {z | ‖∑ j, u j * z j‖ ≤ ε}) ≤
          ENNReal.ofReal (C * ε ^ α)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarietyLelongMono
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory
open scoped ENNReal

noncomputable section

def VarietyLelongMono.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    ∀ z ∈ zeroSetEuc J, ∀ r s : ℝ, 0 < r → r ≤ s →
      ENNReal.ofReal (s ^ (2 * d)) * μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball z r) ≤
        ENNReal.ofReal (r ^ (2 * d)) * μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball z s)

theorem VarietyLelongMono.euclBall_measure (d : ℕ) (z : EuclideanSpace ℂ (Fin d)) {r : ℝ} (hr : 0 < r) :
    μH[((2 * d : ℕ) : ℝ)] (Metric.ball z r) =
      ENNReal.ofReal (r ^ (2 * d)) * μH[((2 * d : ℕ) : ℝ)] (Metric.ball (0 : EuclideanSpace ℂ (Fin d)) 1) := by
  have hf : Module.finrank ℝ (EuclideanSpace ℂ (Fin d)) = 2 * d := by
    rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ (Fin d)), Complex.finrank_real_complex,
      finrank_euclideanSpace_fin]
  have h : ((2 * d : ℕ) : ℝ) = ((Module.finrank ℝ (EuclideanSpace ℂ (Fin d)) : ℕ) : ℝ) := by rw [hf]
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    have hb : ∀ (x : EuclideanSpace ℂ (Fin 0)) (t : ℝ), 0 < t → Metric.ball x t = Set.univ := fun x t ht =>
      Set.eq_univ_of_forall fun y => Metric.mem_ball.2 (by rw [Subsingleton.elim y x, dist_self]; exact ht)
    rw [hb z r hr, hb 0 1 one_pos]
    simp
  · have : Nontrivial (EuclideanSpace ℂ (Fin d)) :=
      Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [hf]; omega)
    rw [h, Measure.addHaar_ball _ _ hr.le, hf]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarietyProjectionMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

open scoped ENNReal

noncomputable section

def rowsProj {n d : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (s : Fin d → Fin n)
    (z : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin d) :=
  WithLp.toLp 2 ((U.submatrix s id).mulVec fun j => z j)


open Classical in
def VarietyProjectionMass.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    ∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ B : Set (EuclideanSpace ℂ (Fin n)), MeasurableSet B →
      μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ B) ≤
        ∑ s ∈ Finset.univ.filter (fun s : Fin d → Fin n => StrictMono s),
          (⨆ x : EuclideanSpace ℂ (Fin d),
              (({z | z ∈ zeroSetEuc J ∩ B ∧ rowsProj U s z = x}.encard : ℕ∞) : ℝ≥0∞)) *
            μH[((2 * d : ℕ) : ℝ)] (rowsProj U s '' (zeroSetEuc J ∩ B))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarietySlabMeasure
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

open scoped ENNReal

noncomputable section

def VarietySlabMeasure.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) ≤ d → linForm u ∉ J → ∀ R : ℝ,
      ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        μH[((2 * d : ℕ) : ℝ)] {z | z ∈ zeroSetEuc J ∧ ‖z‖ ≤ R ∧ ‖∑ j, u j * z j‖ ≤ ε} ≤
          ENNReal.ofReal (C * ε ^ α)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StVarietyTangentGraphDense
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def VarietyTangentGraphDense.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)), J.IsPrime →
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d →
    ∀ z ∈ zeroSetEuc J, ∀ ε : ℝ, 0 < ε →
      ∃ (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) (I₀ : Finset (Fin n))
        (Ω : Set (I₀ → ℂ)) (V : Set (EuclideanSpace ℂ (Fin n)))
        (g : (I₀ → ℂ) → EuclideanSpace ℂ (Fin n)) (w₀ : I₀ → ℂ),
        I₀.card = d ∧ IsOpen Ω ∧ IsOpen V ∧ w₀ ∈ Ω ∧ DifferentiableOn ℂ g Ω ∧
          (∀ w ∈ Ω, frameProj b I₀ (g w) = w) ∧ zeroSetEuc J ∩ V = g '' Ω ∧
          (∀ j ∉ I₀, fderiv ℂ (fun w => inner ℂ (b j) (g w)) w₀ = 0) ∧ dist (g w₀) z < ε

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StWeierstrassDivisionAtPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter

def WeierstrassDivisionAtPoint.Statement : Prop :=
  ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (y₀ : τ → ℂ) (c : τ) (d : ℕ) (F g : (τ → ℂ) → ℂ),
    AnalyticAt ℂ F y₀ → AnalyticAt ℂ g y₀ →
    analyticOrderAt (fun s : ℂ => F (y₀ + Pi.single c s)) 0 = d →
    ∃ (q : (τ → ℂ) → ℂ) (a : Fin d → (τ → ℂ) → ℂ),
      AnalyticAt ℂ q y₀ ∧ (∀ j, AnalyticAt ℂ (a j) (zeroCoordinate c y₀)) ∧
      ∀ᶠ y in 𝓝 y₀, g y = q y * F y + ∑ j : Fin d, a j (zeroCoordinate c y) * (y c - y₀ c) ^ (j : ℕ)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StZariskiObjects
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Topology Filter

noncomputable section

def holGermValue {σ : Type} [Fintype σ] (w : σ → ℂ) : holGerms w →+* ℂ :=
  (Germ.valueRingHom (x := w)).comp (holGerms w).subtype

def holGermPointIdeal {σ : Type} [Fintype σ] (w : σ → ℂ) : Ideal (holGerms w) :=
  RingHom.ker (holGermValue w)

def polyPointIdeal {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) :
    Ideal (MvPolynomial σ ℂ ⧸ I) :=
  (RingHom.ker (MvPolynomial.eval w)).map (Ideal.Quotient.mk I)

def germQuotPointIdeal {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) :
    Ideal (holGerms w ⧸ I.map (polyGerm w)) :=
  (holGermPointIdeal w).map (Ideal.Quotient.mk _)

theorem holGermValue_polyGerm {σ : Type} [Fintype σ] (w : σ → ℂ) (q : MvPolynomial σ ℂ) :
    holGermValue w (polyGerm w q) = eval w q := rfl

theorem polyPointIdeal_isMaximal {σ : Type} [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ)
    (hw : w ∈ zeroSetIn I) : (polyPointIdeal I w).IsMaximal := by
  have hmax : (RingHom.ker (MvPolynomial.eval w)).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun a => ⟨C a, eval_C a⟩
  have hle : I ≤ RingHom.ker (MvPolynomial.eval w) := fun q hq => RingHom.mem_ker.2 (hw q hq)
  refine (Ideal.map_eq_top_or_isMaximal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective hmax).resolve_left ?_
  intro htop
  have h := Ideal.comap_map_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective (RingHom.ker (MvPolynomial.eval w))
  rw [htop, Ideal.comap_top, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.2 hle] at h
  exact hmax.ne_top h.symm

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

