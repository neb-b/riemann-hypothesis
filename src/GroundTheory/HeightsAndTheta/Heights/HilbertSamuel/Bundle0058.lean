module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0039
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockStepLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

def TwoBlockStepLocal.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (I : AllFam) (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (m m' : ConeMetric ℂ (Ix κ)),
    I.IsFamily → IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    IsSmoothMetric m → (∀ z, m'.ρ (matActC B z) = m.ρ z) →
    Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)) →
    ∃ (a₀ : ℕ) (C : ℝ), ∀ a b : ℕ, a₀ ≤ a → a₀ ≤ b →
      |twoBlockStep x (matAct B x) a b -
          ∑ i ∈ Finset.range (D + 1), twoBlockCoeff I x (matAct B x) m m' D i *
            ((a : ℝ) ^ i * (b : ℝ) ^ (D - i) / ((i.factorial : ℝ) * ((D - i).factorial : ℝ)))| ≤
        C * ((a + b : ℝ) + 1) ^ D / ((a + b : ℝ) + 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockTop
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Asymptotics

noncomputable section

def TwoBlockTop.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (I : AllFam) (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (m m' : ConeMetric ℂ (Ix κ)),
    I.IsFamily → IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    IsSmoothMetric m → (∀ z, m'.ρ (matActC B z) = m.ρ z) →
    I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x (matAct B x)) (D + 1) (fun _ => blockLine m 0) = top I x m D ∧
      I (Fin 2) (FinTwoTypeFamily κ) (twoBlockIdeal x (matAct B x)) (D + 1) (fun _ => blockLine m' 1) =
        top I (matAct B x) m' D

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.TwoBlockCycle
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

section Cycle

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


open Classical in
def vertCycleNum (P : Ideal (MRing ι)) (s : MRing ι) {n : ℕ} (e : Fin n → K → ℤ) : ℝ :=
  ∑ᶠ W ∈ divSupp P s, (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
    (if IsHorizontal W then 0 else (geoNum n W e : ℝ) * Real.log (charOf W))

theorem vertR_eq_vertCycleNum (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι) :
    ReciprocityTheory.ChartRestriction.G.AI.I2.vertR P L s = vertCycleNum P s (fun j => (L j).a) :=
  rfl

end Cycle

section TwoBlock

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

def twoBlockDen (c : κ) : MRing (FinTwoTypeFamily κ) :=
  X ⟨0, c⟩

def twoBlockNum (l : Ix κ → ℤ) : MRing (FinTwoTypeFamily κ) :=
  ∑ j : Ix κ, MvPolynomial.C (l j) * X ⟨1, j.2⟩

def twoBlockVert (x x' : Ix κ → Ω) (c : κ) (l : Ix κ → ℤ) {n : ℕ} (e : Fin n → Fin 2 → ℤ) : ℝ :=
  vertCycleNum (twoBlockIdeal x x') (twoBlockNum l) e - vertCycleNum (twoBlockIdeal x x') (twoBlockDen c) e

def twoBlockDegList (D i : ℕ) : Fin D → Fin 2 → ℤ :=
  fun j => if (j : ℕ) < i then Pi.single 0 1 else Pi.single 1 1

theorem twoBlockDegList_eq (m m' : ConeMetric ℂ (Ix κ)) (D i : ℕ) (j : Fin D) :
    twoBlockDegList D i j = (twoBlockList m m' D i (if (j : ℕ) < i then j.castSucc else j.succ)).a := by
  unfold twoBlockDegList twoBlockList
  split_ifs with h1 h2 h2 <;> simp_all [blockLine]
  omega

end TwoBlock

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

