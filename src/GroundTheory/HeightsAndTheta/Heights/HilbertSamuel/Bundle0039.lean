module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0021
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0009

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftVolumeBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter

noncomputable section

def ShiftVolumeBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι)),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P0 ≤ mCoordIdeal y → ReciprocityTheory.ChartRestriction.G.Geo.IsSemipositiveRel P0 (mCoordIdeal y) A → NefOnFibres (mCoordIdeal y) A.a →
    IsConjInvariantH A →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℕ, 1 ≤ q →
      arVolP (IsSmallH (mCoordIdeal y) y (HermLine.zcomb A (fsH ι) (q : ℤ) 1))
          (chartLat y (HermLine.zcomb A (fsH ι) (q : ℤ) 1).a) 1 D ≤
        C * ((q : ℝ) + 1) * (genDeg (mCoordIdeal y) D (HermLine.zcomb A (fsH ι) (q : ℤ) 1).a : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSmallSectionsSeparated
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def SmallSectionsSeparated.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι),
    IsArithVar (mCoordIdeal y) (D + 1) → Birational y → IsSmoothHerm A →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℕ, ∃ (Z : Finset ((Σ k, ι k) → ℂ)) (ev : chartLatNm y A.a τ →+ (Z → ℂ)),
      (∀ z ∈ Z, z ∈ mcPts (mCoordIdeal y)) ∧
      (∀ (s : chartLatNm y A.a τ) (z : Z), ∃ (dg dh : K → ℕ) (g h : MRing ι),
        IsMultiHomog g dg ∧ IsMultiHomog h dh ∧ (∀ k, (dg k : ℤ) = dh k + τ * A.a k) ∧
        aeval y g = (s : Ω) * aeval y h ∧ eval (z : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) h) ≠ 0 ∧
        ev s z * eval (z : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) h) =
          eval (z : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) g)) ∧
      ∀ s t : chartLatNm y A.a τ, IsSmallH (mCoordIdeal y) y A τ (s : Ω) →
        IsSmallH (mCoordIdeal y) y A τ (t : Ω) → s ≠ t →
        ∃ z : Z, Real.exp (-(C * ((τ : ℝ) + 1))) * A.h z ^ τ ≤ ‖ev s z - ev t z‖

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSpanStepHomog
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SpanStepHomog.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (q : ℕ) (w : Fin q → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ j, w j ∈ chartLat y a 1) → KH.GeneratesOn y a w →
    ∃ (m r : ℕ) (t : Fin r → Ω), (∀ l, t l ∈ chartLat y a m) ∧
      ∀ (n : ℕ), ∀ s ∈ chartLat y a n, ∀ j, w j ≠ 0 →
        ∃ D : ℕ, s * w j ^ D ∈ gradedSpan w (fun _ => m) t (n + D)

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSpanStepLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SpanStepLocal.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (q : ℕ) (w : Fin q → Ω),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ j, w j ∈ chartLat y a 1) → KH.GeneratesOn y a w →
    ∀ j, w j ≠ 0 → ∃ (r : ℕ) (b : Fin r → Ω), (∀ l, ∃ n : ℕ, b l * w j ^ n ∈ chartLat y a n) ∧
      ∀ (g : Ω) (n : ℕ), g * w j ^ n ∈ chartLat y a n →
        ∃ c : Fin r → Ω, (∀ l, c l ∈ Algebra.adjoin ℤ (Set.range fun i => w i / w j)) ∧ g = ∑ l, c l * b l

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSublatticeDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def SublatticeDegree.Statement : Prop :=
  ∀ (E E' : Type) [AddCommGroup E] [AddCommGroup E'] (R R' : ℕ) (φ : E →+ EuclideanSpace ℝ (Fin R))
    (φ' : E' →+ EuclideanSpace ℝ (Fin R')) [DiscreteTopology (imageLattice φ)] [IsZLattice ℝ (imageLattice φ)]
    [DiscreteTopology (imageLattice φ')] [IsZLattice ℝ (imageLattice φ')] (ψ : E' →+ E) (S : Set E) (C : ℝ),
    Function.Injective φ → Function.Injective φ' → Function.Injective ψ → (∀ x, ‖φ (ψ x)‖ ≤ ‖φ' x‖) →
    AddSubgroup.closure S = ⊤ → (∀ s ∈ S, ‖φ s‖ ≤ C) → 1 ≤ C →
    -Real.log (ZLattice.covolume (imageLattice φ')) ≤
      -Real.log (ZLattice.covolume (imageLattice φ)) + R * Real.log C

namespace SublatticeDegree

abbrev b1 : Module.Basis (Fin 1) ℝ (EuclideanSpace ℝ (Fin 1)) := (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis

abbrev lat1 : Submodule ℤ (EuclideanSpace ℝ (Fin 1)) := Submodule.span ℤ (Set.range b1)

abbrev φ1 : lat1 →+ EuclideanSpace ℝ (Fin 1) := lat1.subtype.toAddMonoidHom

end SublatticeDegree

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwistIntersectionAnyDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

def TwistIntersectionAnyDegree.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (II : IntersectionSystem)
    (Λ : (F →+* ℂ) → ℝ),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    IsSmoothHerm A → B.a = 0 → IsSmoothHerm B → (∀ sg, 0 < Λ sg) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z → B.h =ᶠ[𝓝 z] fun _ => Λ sg) →
    II K ι (mCoordIdeal y) (D + 1) (fun _ => A.tensor B) =
      II K ι (mCoordIdeal y) (D + 1) (fun _ => A) +
        ((D + 1 : ℕ) : ℝ) * genDeg (mCoordIdeal y) D A.a *
          ((∑ sg, Real.log (Λ sg)) / Fintype.card (F →+* ℂ))

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwistIntersectionInt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology

noncomputable section

def TwistIntersectionInt.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (F : Type) [Field F] [NumberField F] [Algebra F Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (II : IntersectionSystem)
    (Λ : (F →+* ℂ) → ℝ),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    IsSmoothHerm A → B.a = 0 → IsSmoothHerm B → (∀ sg, 0 < Λ sg) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃! sg : F →+* ℂ, LiesOver y sg z) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∀ sg : F →+* ℂ, LiesOver y sg z → B.h =ᶠ[𝓝 z] fun _ => Λ sg) →
    II K ι (mCoordIdeal y) (D + 1) (fun _ => A.tensor B) =
      II K ι (mCoordIdeal y) (D + 1) (fun _ => A) +
        ((D + 1 : ℕ) : ℝ) * genDeg (mCoordIdeal y) D A.a *
          ((∑ sg, Real.log (Λ sg)) / Fintype.card (F →+* ℂ))

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.TwoBlockModel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

section TwoBlock

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

def twoBlockIdeal (x x' : Ix κ → Ω) : Ideal (MRing (FinTwoTypeFamily κ)) :=
  mCoordIdeal (ι := FinTwoTypeFamily κ) (pair x x')

def blockLine (m : ConeMetric (C := ℂ) (ι := Ix κ)) (k₀ : Fin 2) :
    ReciprocityTheory.ChartRestriction.G.Geo.HermLine (ι := FinTwoTypeFamily κ) where
  a := Pi.single k₀ 1
  h z := m.ρ fun p : Ix κ => z ⟨k₀, p.2⟩
  pos z hz := m.pos _ fun h0 => by
    obtain ⟨i, hi⟩ := hz k₀
    exact hi (congrFun h0 ⟨(), i⟩)
  smul c z _ := by
    have e : (fun p : Ix κ => c k₀ * z ⟨k₀, p.2⟩) = c k₀ • fun p : Ix κ => z ⟨k₀, p.2⟩ := rfl
    show m.ρ (fun p : Ix κ => c k₀ * z ⟨k₀, p.2⟩) = _
    rw [e, m.smul, Finset.prod_eq_single k₀ (fun k _ hk => by simp [hk]) (by simp)]
    simp

def twoBlockList (m m' : ConeMetric (C := ℂ) (ι := Ix κ)) (D i : ℕ) :
    Fin (D + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine (ι := FinTwoTypeFamily κ) :=
  fun j => if (j : ℕ) < i then blockLine m 0 else blockLine m' 1

def twoBlockCoeff (I : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.AllFam)
    (x x' : Ix κ → Ω) (m m' : ConeMetric (C := ℂ) (ι := Ix κ)) (D i : ℕ) : ℝ :=
  I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x x') (D + 1) (twoBlockList m m' D i) -
    I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x x') (D + 1) (twoBlockList m m' D (i + 1))

def twoBlockStep (x x' : Ix κ → Ω) (a b : ℕ) : ℝ :=
  Real.log ((sec ℤ x (a + 1) * sec ℤ x' b).toAddSubgroup.relIndex (sec ℤ x a * sec ℤ x' (b + 1)).toAddSubgroup)

theorem twoBlockList_zero (m m' : ConeMetric (C := ℂ) (ι := Ix κ)) (D : ℕ) :
    twoBlockList m m' D 0 = fun _ => blockLine m' 1 := by
  funext j
  simp [twoBlockList]

theorem twoBlockList_last (m m' : ConeMetric (C := ℂ) (ι := Ix κ)) (D : ℕ) :
    twoBlockList m m' D (D + 1) = fun _ => blockLine m 0 := by
  funext j
  simp [twoBlockList, j.2]

theorem sum_twoBlockCoeff (I : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.AllFam)
    (x x' : Ix κ → Ω) (m m' : ConeMetric (C := ℂ) (ι := Ix κ)) (D : ℕ) :
    ∑ i ∈ Finset.range (D + 1), twoBlockCoeff I x x' m m' D i =
      I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x x') (D + 1) (fun _ => blockLine m' 1) -
        I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x x') (D + 1) (fun _ => blockLine m 0) := by
  unfold twoBlockCoeff
  rw [Finset.sum_range_sub', twoBlockList_zero, twoBlockList_last]

end TwoBlock

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.UnifBergmanLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights

noncomputable section

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X} {L : HolLineBundle A}

theorem le_l2NormSq_of_chart [CompactSpace X] [MeasurableSpace X] [BorelSpace X] (W : Weight L)
    (dV : SmoothVolume A) {n : ℕ} {s : Fin A.n → X → ℂ} (hs : s ∈ L.sections n) (j : Fin A.n)
    {B : Set (Fin D → ℂ)} (hB : MeasurableSet B) (hBt : B ⊆ (A.chart j).target) {c : ℝ}
    (hc : 0 ≤ c) (hdens : ∀ y ∈ B, c ≤ dV.dens j y) :
    c * ∫ y in B, ‖s j ((A.chart j).symm y)‖ ^ 2 *
        Real.exp (-(n : ℝ) * W.φ j ((A.chart j).symm y)) ≤ sectionL2NormSq W dV n s := by
  have := dV.isProb
  set P := ptNormSq W n s with hPdef
  have hPc : Continuous P := continuous_ptNormSq W hs
  have hP0 : ∀ x, 0 ≤ P x := ptNormSq_nonneg W n s
  have hPi : Integrable P dV.μ := integrable_ptNormSq W dV hs
  have hl0 : 0 ≤ sectionL2NormSq W dV n s := integral_nonneg hP0
  set h : (Fin D → ℂ) → ℝ := fun y => ‖s j ((A.chart j).symm y)‖ ^ 2 *
    Real.exp (-(n : ℝ) * W.φ j ((A.chart j).symm y)) with hh
  have hPh : ∀ y ∈ B, P ((A.chart j).symm y) = h y := fun y hy =>
    ptNormSq_eq_of_mem W hs j ((A.chart j).map_target (hBt hy))
  have hh0 : ∀ y, 0 ≤ h y := fun y => by rw [hh]; positivity
  rw [← integral_const_mul]
  by_cases hi : Integrable (fun y => c * h y) (volume.restrict B)
  swap
  · rw [integral_undef hi]; exact hl0
  rw [← ENNReal.ofReal_le_ofReal_iff hl0, ofReal_integral_eq_lintegral_ofReal hi
    (ae_of_all _ fun y => mul_nonneg hc (hh0 y)), sectionL2NormSq,
    ofReal_integral_eq_lintegral_ofReal hPi (ae_of_all _ hP0)]
  calc ∫⁻ y in B, ENNReal.ofReal (c * h y)
      ≤ ∫⁻ y in B, ENNReal.ofReal (P ((A.chart j).symm y)) * ENNReal.ofReal (dV.dens j y) := by
        refine setLIntegral_mono' hB fun y hy => ?_
        rw [hPh y hy, ← ENNReal.ofReal_mul (hh0 y), mul_comm c]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hdens y hy) (hh0 y))
    _ ≤ ∫⁻ y in (A.chart j).target, ENNReal.ofReal (P ((A.chart j).symm y)) *
          ENNReal.ofReal (dV.dens j y) := lintegral_mono_set hBt
    _ = ∫⁻ x in (A.chart j).source, ENNReal.ofReal (P x) ∂dV.μ :=
        (dV.chart_lintegral j _ hPc.measurable.ennreal_ofReal).symm
    _ ≤ ∫⁻ x, ENNReal.ofReal (P x) ∂dV.μ := setLIntegral_le_lintegral _ _

lemma setIntegral_closedBall_add (y : Fin D → ℂ) (ρ : ℝ) (H : (Fin D → ℂ) → ℝ) :
    ∫ z in Metric.closedBall (0 : Fin D → ℂ) ρ, H (y + z) =
      ∫ w in Metric.closedBall y ρ, H w := by
  rw [← integral_indicator Metric.isClosed_closedBall.measurableSet,
    ← integral_indicator Metric.isClosed_closedBall.measurableSet]
  have e : (Metric.closedBall (0 : Fin D → ℂ) ρ).indicator (fun z => H (y + z)) =
      fun z => (Metric.closedBall y ρ).indicator H (y + z) := by
    funext z
    simp [Set.indicator, Metric.mem_closedBall, dist_eq_norm]
  rw [e, integral_add_left_eq_self]

theorem gauss_local (hP : PolydiscSubmean.Statement) {n : ℕ} (hn : 0 < n) {r M : ℝ} (hr : 0 < r)
    (hM : 0 ≤ M) {y : Fin D → ℂ} {F : (Fin D → ℂ) → ℂ} {ψ : (Fin D → ℂ) → ℝ}
    (hF : AnalyticOnNhd ℂ F (Metric.closedBall y r)) (hψ : ContinuousOn ψ (Metric.closedBall y r))
    (ℓ : (Fin D → ℂ) →L[ℝ] ℝ)
    (hT : ∀ z : Fin D → ℂ, ‖z‖ ≤ r → ψ (y + z) ≤ ψ y + ℓ z + M * ∑ i, ‖z i‖ ^ 2) :
    ‖F y‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y) * ((n : ℝ) ^ D)⁻¹ * gaussDiscMass M r ^ D ≤
      ∫ w in Metric.closedBall y (r / Real.sqrt n), ‖F w‖ ^ 2 * Real.exp (-(n : ℝ) * ψ w) := by
  set ρ := r / Real.sqrt n with hρ
  have hsq : 1 ≤ Real.sqrt n := Real.one_le_sqrt.2 (by exact_mod_cast hn)
  have hρr : ρ ≤ r := div_le_self hr.le hsq
  have hρ0 : 0 ≤ ρ := div_nonneg hr.le (Real.sqrt_nonneg _)
  set ℓc : StrongDual ℂ (Fin D → ℂ) := StrongDual.extendRCLike ℓ with hℓc
  have hre : ∀ z, (ℓc z).re = ℓ z := fun z => by
    rw [hℓc]; exact StrongDual.re_extendRCLike_apply (𝕜 := ℂ) ℓ z
  set f : (Fin D → ℂ) → ℂ := fun z => F (y + z) * Complex.exp (-(n : ℂ) * ℓc z / 2) with hf
  have hyz : ∀ z : Fin D → ℂ, ‖z‖ ≤ r → y + z ∈ Metric.closedBall y r := fun z hz => by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hfa : AnalyticOnNhd ℂ f (Metric.closedBall 0 (r / Real.sqrt n)) := by
    intro z hz
    have hz' : ‖z‖ ≤ r := (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz : ‖z‖ ≤ ρ).trans hρr
    have h1 : AnalyticAt ℂ (fun z : Fin D → ℂ => F (y + z)) z :=
      (hF (y + z) (hyz z hz')).comp (analyticAt_const.add analyticAt_id)
    have h2 : AnalyticAt ℂ (fun z : Fin D → ℂ => Complex.exp (-(n : ℂ) * ℓc z / 2)) z :=
      ((analyticAt_const.mul (ℓc.analyticAt z)).div_const).cexp
    exact h1.mul h2
  have hnorm : ∀ z, ‖f z‖ ^ 2 = ‖F (y + z)‖ ^ 2 * Real.exp (-(n : ℝ) * ℓ z) := fun z => by
    have : (-(n : ℂ) * ℓc z / 2).re = -(n : ℝ) * ℓ z / 2 := by
      rw [← hre z]; simp [Complex.mul_re]
    rw [hf, norm_mul, Complex.norm_exp, this, mul_pow, ← Real.exp_nat_mul]
    congr 2; push_cast; ring
  have hf0 : f 0 = F y := by simp [hf]
  have key := hP D n (fun _ => M) r f hn hr (fun _ => hM) hfa
  rw [hf0, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at key

  set H : (Fin D → ℂ) → ℝ := fun w => ‖F w‖ ^ 2 * Real.exp (-(n : ℝ) * ψ w) with hH
  have hHc : ContinuousOn H (Metric.closedBall y r) := by
    refine (hF.continuousOn.norm.pow 2).mul ?_
    exact (continuousOn_const.mul hψ).rexp
  have hHi : IntegrableOn (fun z => Real.exp ((n : ℝ) * ψ y) * H (y + z))
      (Metric.closedBall (0 : Fin D → ℂ) ρ) := by
    refine ContinuousOn.integrableOn_compact (isCompact_closedBall _ _) ?_
    refine continuousOn_const.mul (hHc.comp (continuousOn_const.add continuousOn_id) ?_)
    intro z hz
    exact hyz z ((by simpa [Metric.mem_closedBall, dist_eq_norm] using hz : ‖z‖ ≤ ρ).trans hρr)
  have hmono : ∫ z in Metric.closedBall (0 : Fin D → ℂ) ρ,
      ‖f z‖ ^ 2 * Real.exp (-(n : ℝ) * ∑ j, M * ‖z j‖ ^ 2) ≤
      ∫ z in Metric.closedBall (0 : Fin D → ℂ) ρ, Real.exp ((n : ℝ) * ψ y) * H (y + z) := by
    refine integral_mono_of_nonneg (ae_of_all _ fun z => by positivity) hHi ?_
    refine (ae_restrict_iff' Metric.isClosed_closedBall.measurableSet).2 (ae_of_all _ fun z hz => ?_)
    have hz' : ‖z‖ ≤ r := (by simpa [Metric.mem_closedBall, dist_eq_norm] using hz : ‖z‖ ≤ ρ).trans hρr
    have hTz := hT z hz'
    dsimp only
    rw [hnorm, hH]
    dsimp only
    rw [mul_assoc, ← Real.exp_add, mul_left_comm, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    rw [← Finset.mul_sum]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [mul_le_mul_of_nonneg_left hTz hn0]
  rw [setIntegral_closedBall_add y ρ (fun w => Real.exp ((n : ℝ) * ψ y) * H w),
    integral_const_mul] at hmono
  have hchain := key.trans hmono
  have he : Real.exp (-(n : ℝ) * ψ y) * Real.exp ((n : ℝ) * ψ y) = 1 := by
    rw [← Real.exp_add]; simp
  calc ‖F y‖ ^ 2 * Real.exp (-(n : ℝ) * ψ y) * ((n : ℝ) ^ D)⁻¹ * gaussDiscMass M r ^ D
      = Real.exp (-(n : ℝ) * ψ y) * (‖F y‖ ^ 2 * ((n : ℝ) ^ D)⁻¹ * gaussDiscMass M r ^ D) := by
        ring
    _ ≤ Real.exp (-(n : ℝ) * ψ y) * (Real.exp ((n : ℝ) * ψ y) *
          ∫ w in Metric.closedBall y ρ, H w) :=
        mul_le_mul_of_nonneg_left hchain (Real.exp_pos _).le
    _ = ∫ w in Metric.closedBall y ρ, H w := by rw [← mul_assoc, he, one_mul]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

