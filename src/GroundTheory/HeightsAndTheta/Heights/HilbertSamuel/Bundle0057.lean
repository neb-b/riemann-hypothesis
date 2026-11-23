module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0032
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0027
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0037
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0039
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRelSecM
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]

def relSecM (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (b : K → ℕ) : Submodule R Ω :=
  Submodule.span R ((fun μ : (Σ k, ι k) → ℕ => ∏ p, y p ^ μ p) '' {μ | ∀ k, ∑ i, μ ⟨k, i⟩ = b k})

theorem monomial_mem_relSecM (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) {b : K → ℕ} (μ : (Σ k, ι k) → ℕ)
    (hμ : ∀ k, ∑ i, μ ⟨k, i⟩ = b k) : ∏ p, y p ^ μ p ∈ relSecM R y b :=
  Submodule.subset_span ⟨μ, hμ, rfl⟩

theorem relSecM_fg (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) (b : K → ℕ) : (relSecM R y b).FG := by
  have hfin : {μ : (Σ k, ι k) → ℕ | ∀ k, ∑ i, μ ⟨k, i⟩ = b k}.Finite := by
    refine (Set.Finite.pi (t := fun p : (Σ k, ι k) => Set.Iic (b p.1)) fun p => Set.finite_Iic _).subset ?_
    intro μ hμ p _
    simp only [Set.mem_Iic]
    rw [← hμ p.1]
    exact Finset.single_le_sum (f := fun i => μ ⟨p.1, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ p.2)
  exact Submodule.fg_span (hfin.image _)

theorem mul_mem_relSecM (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) {b b' : K → ℕ} {x x' : Ω}
    (hx : x ∈ relSecM R y b) (hx' : x' ∈ relSecM R y b') : x * x' ∈ relSecM R y (b + b') := by
  have hle : relSecM R y b * relSecM R y b' ≤ relSecM R y (b + b') := by
    rw [relSecM, relSecM, Submodule.span_mul_span, Submodule.span_le]
    rintro _ ⟨_, ⟨μ, hμ, rfl⟩, _, ⟨ν, hν, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨μ + ν, fun k => ?_, ?_⟩
    · simp [Finset.sum_add_distrib, hμ k, hν k]
    · simp [pow_add, Finset.prod_mul_distrib]
  exact hle (Submodule.mul_mem_mul hx hx')

theorem adjoin_isNoetherianRing {m : ℕ} (g : Fin m → Ω) : IsNoetherianRing (Algebra.adjoin ℤ (Set.range g)) := by
  have : Algebra.FiniteType ℤ (Algebra.adjoin ℤ (Set.range g)) :=
    Algebra.FiniteType.adjoin_of_finite (Set.finite_range g)
  exact Algebra.FiniteType.isNoetherianRing ℤ _


omit [∀ k, Fintype (ι k)] in
theorem mul_prod_mem_relChartLat (R : Subalgebra ℤ Ω) (y : (Σ k, ι k) → Ω) {a a' : K → ℤ} {n : ℕ} (e : K → ℕ)
    (c0 : ∀ k, ι k) (h : ∀ k, a' k = n * a k + e k) {s : Ω} (hs : s ∈ relChartLat R y a n) :
    s * ∏ k, y ⟨k, c0 k⟩ ^ e k ∈ relChartLat R y a' 1 := by
  intro c hc
  have key : ∀ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * a' k)) =
      y ⟨k, c k⟩ ^ (-((n : ℤ) * a k)) * (y ⟨k, c k⟩ ^ e k)⁻¹ := by
    intro k
    rw [h k, show -(((1 : ℕ) : ℤ) * ((n : ℤ) * a k + (e k : ℤ))) = -((n : ℤ) * a k) + -((e k : ℕ) : ℤ) by push_cast; ring,
      zpow_add₀ (hc k), zpow_neg (y ⟨k, c k⟩) ((e k : ℕ) : ℤ), zpow_natCast]
  rw [Finset.prod_congr rfl fun k _ => key k, Finset.prod_mul_distrib]
  have hmem : (s * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k))) * ∏ k, (y ⟨k, c0 k⟩ / y ⟨k, c k⟩) ^ e k ∈
      Algebra.adjoin R (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) :=
    mul_mem (hs c hc) (prod_mem fun k _ => pow_mem (Algebra.subset_adjoin
      (Set.mem_range_self (f := fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) ⟨k, c0 k⟩)) _)
  convert hmem using 1
  simp only [div_pow, Finset.prod_div_distrib, Finset.prod_inv_distrib]
  ring

end Objects

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def ResolutionDegree.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (e : Fin (D + 1) → Ix κ) (m : ConeMetric ℂ (Ix κ)), IsProjFrame d.x e → IsSmoothMetric m →
    mInt d.R.A (fun _ => resPot d m) (fun _ => 1) = (projDeg d.x e : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionInterpIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def ResolutionInterpIntegral.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (m₁ : ConeMetric ℂ (Ix κ)), IsSmoothMetric m₁ →
    ((D : ℝ) + 1) * resMetricInt d m₁ =
      ∑ i ∈ Finset.range (D + 1),
        mInt d.R.A (fun j : Fin D => if j.val < i then resPot d m₁ else resPot d d.m)
          (fun y => logRatio d.m m₁ (resPt d y))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionMetricPair
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory

noncomputable section

def ResolutionMetricPair.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (m₁ : ConeMetric ℂ (Ix κ)) (P0₁ : Ideal (MRing (GlobalTheory κ))), IsSmoothMetric m₁ →
    P0₁ ≤ coordIdeal ℤ d.x → IsSemipositiveRel P0₁ (coordIdeal ℤ d.x) (HermLine.ofCone m₁) →
    ∃ (A : FinHolAtlas D d.R.X) (L : HolLineBundle A) (W₀ W₁ : Weight L) (dV : SmoothVolume A)
      (σ : ℕ → MvPolynomial (Ix κ) ℚ → Fin A.n → d.R.X → ℂ),
      A.Compatible d.R.A ∧ W₀.IsSemipositive ∧ W₁.IsSemipositive ∧ dV.μ = d.dV ∧
      (∀ (n : ℕ) (b : MvPolynomial (Ix κ) ℚ), b.IsHomogeneous n → σ n b ∈ L.sections n) ∧
      (∀ y : d.R.X, ∃ c : ℂ, c ≠ 0 ∧
        (∀ (n : ℕ) (b : MvPolynomial (Ix κ) ℚ), b.IsHomogeneous n →
          σ n b (chartIdx A y) y = eval (c • resPt d y) (map (algebraMap ℚ ℂ) b)) ∧
        W₀.φ (chartIdx A y) y = 2 * Real.log (d.m.ρ (c • resPt d y)) ∧
        W₁.φ (chartIdx A y) y = 2 * Real.log (m₁.ρ (c • resPt d y))) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ g : d.R.X → ℝ, Continuous g →
        ∫ y, g y * bergmanDens (W₀.lerp W₁ t) dV y ∂dV.μ =
          mInt d.R.A (fun _ => resPot d (interp d.m m₁ t)) g / (D.factorial : ℝ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionMixedBridge
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M

noncomputable section

def ResolutionMixedBridge.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (M : Fin D → ConeMetric ℂ (Ix κ)) (m₁ : ConeMetric ℂ (Ix κ)),
    (∀ j, IsSmoothMetric (M j)) → IsSmoothMetric m₁ →
    ptsIntegral (ι := GlobalTheory κ) (coordIdeal ℤ d.x) (fun j z => Real.log ((M j).ρ z)) (logRatio d.m m₁) =
      mInt d.R.A (fun j => resPot d (M j)) (fun y => logRatio d.m m₁ (resPt d y))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResolutionMixedIntegral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ResolutionMixedIntegral.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (d : HSMDatum D Ω κ)
    (m₁ : ConeMetric ℂ (Ix κ)), IsSmoothMetric m₁ →
    ∑ i ∈ Finset.range (D + 1),
        ptsIntegral (ι := GlobalTheory κ) (coordIdeal ℤ d.x) (mixPot d.m m₁ D i) (logRatio d.m m₁) =
      ((D : ℝ) + 1) * resMetricInt d m₁

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionPointValue
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SectionPointValue.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι),
    IsRelevant (mCoordIdeal y) → ContinuousOn A.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} →
    ∃ w : ∀ n : ℕ, chartLat y A.a n →+ (((Σ k, ι k) → ℂ) → ℂ),
      (∀ (n : ℕ) (s : chartLat y A.a n), ContinuousOn (w n s) (mcPts (mCoordIdeal y))) ∧
      (∀ (n : ℕ) (s : chartLat y A.a n) (dg dh : K → ℕ) (g h : MRing ι) (z : (Σ k, ι k) → ℂ),
        IsMultiHomog g dg → IsMultiHomog h dh → (∀ k, (dg k : ℤ) = dh k + n * A.a k) →
        aeval y g = (s : Ω) * aeval y h → z ∈ mcPts (mCoordIdeal y) →
        eval z (map (Int.castRingHom ℂ) g) =
          w n s z * eval z (map (Int.castRingHom ℂ) h) * (A.h z : ℂ) ^ n) ∧
      (∀ (n : ℕ) (s : chartLat y A.a n), ∀ z ∈ mcPts (mCoordIdeal y),
        secNormAt y A n (s : Ω) z = ‖w n s z‖) ∧
      (∀ (n k : ℕ) (s : chartLat y A.a n) (t : chartLat y A.a k) (st : chartLat y A.a (n + k)),
        (st : Ω) = s * t → ∀ z ∈ mcPts (mCoordIdeal y), w (n + k) st z = w n s z * w k t z) ∧
      ∀ (n r : ℕ) (s : Fin r → chartLat y A.a n),
        ∃ (e e' : K → ℕ) (h : MRing ι) (g : Fin r → MRing ι),
          IsMultiHomog h e' ∧ (∀ i, IsMultiHomog (g i) e) ∧ (∀ k, (e k : ℤ) = e' k + n * A.a k) ∧
          aeval y h ≠ 0 ∧ ∀ i, aeval y (g i) = (s i : Ω) * aeval y h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsShiftQuotientBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

def ShiftQuotientBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (a b : K → ℤ) (c : ∀ k, ι k),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → (∀ k, y ⟨k, c k⟩ ≠ 0) →
    ∃ C : ℝ, ∀ᶠ n : ℕ in atTop,
      (Module.finrank ℚ (chartLatQ y ((n : ℤ) • a + b) 1 ⧸ chartDivSec y c ((n : ℤ) • a + b)) : ℝ) ≤
        C * (n : ℝ) ^ (D - 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSublatticeDegreeSteps
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def SublatticeExtension.Statement : Prop :=
  ∀ (E E' : Type) [AddCommGroup E] [AddCommGroup E'] (R R' : ℕ) (φ : E →+ EuclideanSpace ℝ (Fin R))
    (φ' : E' →+ EuclideanSpace ℝ (Fin R')) [DiscreteTopology (imageLattice φ)]
    [DiscreteTopology (imageLattice φ')] [IsZLattice ℝ (imageLattice φ')] (ψ : E' →+ E),
    Function.Injective φ → Function.Injective φ' → Function.Injective ψ → (∀ x, ‖φ (ψ x)‖ ≤ ‖φ' x‖) →
    ∃ Ψ : EuclideanSpace ℝ (Fin R') →ₗ[ℝ] EuclideanSpace ℝ (Fin R),
      (∀ x, Ψ (φ' x) = φ (ψ x)) ∧ (∀ y, ‖Ψ y‖ ≤ ‖y‖) ∧ Function.Injective Ψ

def SpanningExtension.Statement : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] (ι : Type) [Fintype ι]
    (v : ι → V) (S : Set V), LinearIndependent ℝ v → Submodule.span ℝ S = ⊤ →
    ∃ w : Fin (Module.finrank ℝ V - Fintype.card ι) → V, (∀ j, w j ∈ S) ∧ LinearIndependent ℝ (Sum.elim v w)

def CovolumeLeGram.Statement : Prop :=
  ∀ (n : ℕ) (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L] [IsZLattice ℝ L]
    (ι : Type) [Fintype ι] [DecidableEq ι] (x : ι → EuclideanSpace ℝ (Fin n)), (∀ i, x i ∈ L) →
    LinearIndependent ℝ x → Fintype.card ι = n → ZLattice.covolume L ≤ Real.sqrt (Matrix.gram ℝ x).det

def GramContraction.Statement : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (Ψ : EuclideanSpace ℝ ι →ₗ[ℝ] V) (u : ι → EuclideanSpace ℝ ι) (w : κ → V),
    (∀ y, ‖Ψ y‖ ≤ ‖y‖) →
      (Matrix.gram ℝ (Sum.elim (Ψ ∘ u) w)).det ≤ (Matrix.gram ℝ u).det * ∏ j, ‖w j‖ ^ 2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockChainSum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

def TwoBlockChainSum.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (I : AllFam) (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (m m' : ConeMetric ℂ (Ix κ)),
    I.IsFamily → IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    IsSmoothMetric m → (∀ z, m'.ρ (matActC B z) = m.ρ z) →
    Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)) →
    (fun n : ℕ => ∑ j ∈ Finset.range n, twoBlockStep x (matAct B x) (n - j - 1) j -
        (I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x (matAct B x)) (D + 1) (fun _ => blockLine m' 1) -
          I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x (matAct B x)) (D + 1) (fun _ => blockLine m 0)) *
          (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ))
      =O[atTop] fun n : ℕ => (n : ℝ) ^ D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockFnField
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

def TwoBlockFnField.Statement : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (B : Matrix (Ix κ) (Ix κ) ℚ),
    IsInvMat B →
      blockFnField (ι := FinTwoTypeFamily κ) (pair x (matAct B x)) = blockFnField (ι := GlobalTheory κ) x ∧
        blockFnField (ι := GlobalTheory κ) (matAct B x) = blockFnField (ι := GlobalTheory κ) x

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockStepBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

def TwoBlockStepBound.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω) (B : Matrix (Ix κ) (Ix κ) ℚ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)) →
    ∃ K : ℝ, ∀ a b : ℕ, |twoBlockStep x (matAct B x) a b| ≤ K * ((a + b : ℝ) + 1) ^ D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

