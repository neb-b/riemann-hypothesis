module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDefectMetricChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

def HSMDatum.withMetric (d : HSMDatum D Ω κ) (m : ConeMetric ℂ (Ix κ)) (P0 : Ideal (MRing (GlobalTheory κ)))
    (hs : IsSmoothMetric m) (hc : IsConjInvariant m) (hle : P0 ≤ coordIdeal ℤ d.x)
    (hp : IsSemipositiveRel P0 (coordIdeal ℤ d.x) (HermLine.ofCone m)) : HSMDatum D Ω κ :=
  { d with m := m, P0 := P0, smooth := hs, conjInv := hc, normalForm_baseLattice_le_dualSpan_sup_line := hle, semipos := hp }

def DefectMetricChange.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (I : AllFam) (d : HSMDatum D Ω κ)
    (m₁ : ConeMetric ℂ (Ix κ)) (P0₁ : Ideal (MRing (GlobalTheory κ))) (hs : IsSmoothMetric m₁)
    (hc : IsConjInvariant m₁) (hle : P0₁ ≤ coordIdeal ℤ d.x)
    (hp : IsSemipositiveRel P0₁ (coordIdeal ℤ d.x) (HermLine.ofCone m₁)) (e : Fin (D + 1) → Ix κ),
    I.IsFamily → IsProjFrame d.x e →
    (fun n => hsDefect D (resChi (d.withMetric m₁ P0₁ hs hc hle hp)) (top I d.x m₁ D) n -
        hsDefect D (resChi d) (top I d.x d.m D) n) =o[atTop] pw D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingWeight
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

def EmbeddingWeight.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω) (Λ : (F →+* ℂ) → ℝ),
    (∀ sg, 0 < Λ sg) → (∀ sg, Λ (NumberField.ComplexEmbedding.conjugate sg) = Λ sg) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z) →
    ∃ B : HermLine ι, B.a = 0 ∧ IsSmoothHerm B ∧ IsConjInvariantH B ∧
      ∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z → B.h =ᶠ[𝓝 z] fun _ => Λ sg

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEuclideanSections
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

def imageLattice {E V : Type*} [AddCommGroup E] [AddCommGroup V] (φ : E →+ V) : Submodule ℤ V :=
  AddSubgroup.toIntSubmodule φ.range

def EuclideanSections.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    IsSmallGeneratedDatum P0 y D A → IsConjInvariantH A →
    ∃ (r : ℕ → ℕ) (φ : ∀ n : ℕ, chartLat y A.a n →+ EuclideanSpace ℝ (Fin (r n))),
      (∀ n, Function.Injective (φ n)) ∧
      (∀ n, DiscreteTopology (imageLattice (φ n))) ∧
      (∀ n [DiscreteTopology (imageLattice (φ n))], IsZLattice ℝ (imageLattice (φ n))) ∧
      (∀ (n : ℕ) (c : ℝ) (s : chartLat y A.a n), 0 ≤ c →
        IsBoundedH (mCoordIdeal y) y A n c (s : Ω) → ‖φ n s‖ ≤ c) ∧
      (∃ C : ℝ, ∀ n : ℕ, (r n : ℝ) ≤ C * ((n : ℝ) + 1) ^ D) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
        ∀ [DiscreteTopology (imageLattice (φ n))] [IsZLattice ℝ (imageLattice (φ n))],
          -Real.log (ZLattice.covolume (imageLattice (φ n))) ≤
            (II K ι (mCoordIdeal y) (D + 1) (fun _ => A) + ε) *
              ((n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFSGeomDegPos
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

def FSGeomDegPos.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ),
    IsArithVar P (e + 1) → 0 < ptsIntegral P (pot fun _ : Fin e => fsH ι) (fun _ => 1)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def FibreNormBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (df : K → ℕ) (f : MRing ι),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmoothHerm A →
    IsMultiHomog f df → f ∉ mCoordIdeal y →
    ∃ (n c : ℕ) (B : ℝ) (G : MvPolynomial (Fin (D + 1)) ℤ)
      (Fib : (Fin (D + 1) → ℂ) → Finset ((Σ k, ι k) → ℂ)),
      1 ≤ n ∧ 1 ≤ B ∧ G ≠ 0 ∧
      (∀ ζ : Fin (D + 1) → ℂ, (∀ i, ‖ζ i‖ = 1) → eval ζ (map (Int.castRingHom ℂ) G) ≠ 0 →
        ∀ z ∈ Fib ζ, z ∈ mcPts (mCoordIdeal y) ∧ eval z (map (Int.castRingHom ℂ) f) ≠ 0) ∧
      ∀ τ : ℕ, ∀ u ∈ chartLatNm y A.a τ, u ≠ 0 →
        ∃ F : MvPolynomial (Fin (D + 1)) ℤ, F ≠ 0 ∧ (∀ i, F.degreeOf i ≤ c * (τ + 1)) ∧
          ∀ ζ : Fin (D + 1) → ℂ, (∀ i, ‖ζ i‖ = 1) → eval ζ (map (Int.castRingHom ℂ) G) ≠ 0 →
          ∀ M : ℝ, 0 ≤ M →
            (∀ z ∈ Fib ζ, ∃ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧
              (∀ k, (dg k : ℤ) = dh k + τ * A.a k) ∧ aeval y g = u * aeval y h ∧
              eval z (map (Int.castRingHom ℂ) h) ≠ 0 ∧
              ‖eval z (map (Int.castRingHom ℂ) g)‖ ≤
                M * A.h z ^ τ * ‖eval z (map (Int.castRingHom ℂ) h)‖) →
            ‖eval ζ (map (Int.castRingHom ℂ) F)‖ ≤ B ^ (τ + 1) * M ^ n

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreNormMax
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def FibreNormMax.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℤ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    (∀ k, 1 ≤ e k) → (∀ j, IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∃ (n c : ℕ) (B : ℝ), 1 ≤ n ∧ 1 ≤ B ∧
      ∀ τ : ℕ, ∀ u ∈ chartLatNm y a τ, u ≠ 0 →
        ∃ F : MvPolynomial (Fin (D + 1)) ℤ, F ≠ 0 ∧ (∀ i, F.degreeOf i ≤ c * (τ + 1)) ∧
          ∀ ζ : Fin (D + 1) → ℂ, (∀ i, ‖ζ i‖ = 1) →
          ∀ S : Finset ((Σ k, ι k) → ℂ),
            (∀ z ∈ mcPts (mCoordIdeal y),
              (∃ t : ℂ, ∀ j, eval z (map (Int.castRingHom ℂ) (L j)) = t * ζ j) →
              ∃ z' ∈ S, ∃ r : K → ℂ, (∀ k, r k ≠ 0) ∧ z = fun p => r p.1 * z' p) →
          ∀ M : ℝ, 0 ≤ M →
            (∀ z ∈ S, ∃ (dg dh : K → ℕ) (g h : MRing ι), IsMultiHomog g dg ∧ IsMultiHomog h dh ∧
              (∀ k, (dg k : ℤ) = dh k + τ * a k) ∧ aeval y g = u * aeval y h ∧
              eval z (map (Int.castRingHom ℂ) h) ≠ 0 ∧
              ‖eval z (map (Int.castRingHom ℂ) g)‖ ≤
                M * (HermLine.ofMetrics (fun k => maxMetric (C := ℂ) (ι := ι k)) a).h z ^ τ *
                  ‖eval z (map (Int.castRingHom ℂ) h)‖) →
            ‖eval ζ (map (Int.castRingHom ℂ) F)‖ ≤ B ^ (τ + 1) * M ^ n



end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFibreRepresentatives
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def FibreRepresentatives.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι),
    (∀ k, 1 ≤ e k) → (∀ j, IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∀ ζ : Fin (D + 1) → ℂ, ∃ S : Finset ((Σ k, ι k) → ℂ),
      (∀ z ∈ S, z ∈ mcPts (mCoordIdeal y) ∧
        ∃ t : ℂ, ∀ j, eval z (map (Int.castRingHom ℂ) (L j)) = t * ζ j) ∧
      ∀ z ∈ mcPts (mCoordIdeal y),
        (∃ t : ℂ, ∀ j, eval z (map (Int.castRingHom ℂ) (L j)) = t * ζ j) →
        ∃ z' ∈ S, ∃ r : K → ℂ, (∀ k, r k ≠ 0) ∧ z = fun p => r p.1 * z' p

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsFrameChange
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def FrameChange.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ),
    ∃ (B : Matrix (Ix κ) (Ix κ) ℚ) (d' : HSMDatum D Ω κ) (e : Fin (D + 1) → Ix κ),
      IsInvMat B ∧ d'.x = matAct B d.x ∧ (∀ z, d'.m.ρ (matActC B z) = d.m.ρ z) ∧ IsProjFrame d'.x e ∧
      (fun n => resChi d' n - resChi d n - latLogIndex d.x d'.x n) =o[atTop] pw D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenDegAmple
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def GenDegAmple.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (d : K → ℤ),
    IsArithVar (mCoordIdeal y) (D + 1) → (∀ k, 1 ≤ d k) → 0 < genDeg (mCoordIdeal y) D d

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenDegGeomDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def GenDegGeomDeg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι),
    IsArithVar (mCoordIdeal y) (D + 1) → IsSmoothHerm A →
    geomDeg (mCoordIdeal y) A D = (genDeg (mCoordIdeal y) D A.a : ℝ)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenDegMatAct
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

def GenDegMatAct.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ),
    IsInvMat B → genDeg (ι := GlobalTheory κ) (coordIdeal ℤ (matAct B x)) D 1 = genDeg (ι := GlobalTheory κ) (coordIdeal ℤ x) D 1

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenFibreHomog
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def GenFibreHomog.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω),
    GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal
      ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ)))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

