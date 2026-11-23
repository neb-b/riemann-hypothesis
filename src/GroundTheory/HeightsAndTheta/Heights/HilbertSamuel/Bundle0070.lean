module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerBlock
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0051
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0047
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0057
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0058
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0023

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPowerHeightsirational
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def PowerHeightsirational.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    [CharZero Ω] (y : (Σ k, ι k) → Ω) (D : ℕ) (a : K → ℤ) (q : ℕ) (w : Fin q → Ω),
    1 ≤ D → IsArithVar (mCoordIdeal y) (D + 1) → Birational y → (∀ j, w j ∈ chartLat y a 1) →
    KH.GeneratesOn y a w → 0 < genDeg (mCoordIdeal y) D a →
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (N : ℕ) (v : Fin N → Ω), AddSubgroup.closure (Set.range v) = chartLat y a m →
      BlockBirational (addBlock y v) (none : Option K)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullRatiosAlgebraic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def PullRatiosAlgebraic.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ k, 1 ≤ e k) → (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∀ p q : Σ k, ι k, p.1 = q.1 → IsAlgebraic (pullField y L) (y p / y q)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsReductionComplex
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace FibreReduction

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem idealOver_int (y : (Σ k, ι k) → Ω) : GenOnFibres.idealOver y ℤ = mCoordIdeal y := by
  have h : (MvPolynomial.map (Int.castRingHom ℤ) : MRingOver ℤ ι →+* MRingOver ℤ ι) = RingHom.id _ := by
    refine RingHom.ext fun f => ?_
    rw [show Int.castRingHom ℤ = RingHom.id ℤ from RingHom.ext_int _ _, map_id]
    rfl
  show Ideal.map _ _ = _
  rw [h, Ideal.map_id]

def redRing (y : (Σ k, ι k) → Ω) (p : ℕ) :
    (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) →+* (MRingOver (ZMod p) ι ⧸ GenOnFibres.idealOver y (ZMod p)) :=
  Ideal.quotientMap _ (MvPolynomial.map (Int.castRingHom (ZMod p))) (by
    rw [idealOver_int]
    exact Ideal.le_comap_map)

theorem redRing_mk (y : (Σ k, ι k) → Ω) (p : ℕ) (f : MRingOver ℤ ι) :
    redRing y p (Ideal.Quotient.mk _ f) = Ideal.Quotient.mk _ (MvPolynomial.map (Int.castRingHom (ZMod p)) f) :=
  Ideal.quotientMap_mk

theorem redRing_smul (y : (Σ k, ι k) → Ω) (p : ℕ) (r : MRingOver ℤ ι)
    (x : MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) :
    redRing y p (r • x) = MvPolynomial.map (Int.castRingHom (ZMod p)) r • redRing y p x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [GenOnFibres.smul_mk, redRing_mk, redRing_mk, GenOnFibres.smul_mk, map_mul]

theorem map_mem_cellMon (p : ℕ) {I : ∀ k, Finset (ι k)} {t : MRingOver ℤ ι} (ht : t ∈ KH.cellMon ℤ I) :
    MvPolynomial.map (Int.castRingHom (ZMod p)) t ∈ KH.cellMon (ZMod p) I := by
  unfold KH.cellMon at ht ⊢
  induction ht using Submonoid.closure_induction with
  | mem f hf =>
    obtain ⟨k, i, hi, rfl⟩ := hf
    rw [map_X]
    exact Submonoid.subset_closure ⟨k, i, hi, rfl⟩
  | one => rw [map_one]; exact one_mem _
  | mul f g _ _ hf hg => rw [map_mul]; exact mul_mem hf hg

def redLocFun (y : (Σ k, ι k) → Ω) (p : ℕ) (I : ∀ k, Finset (ι k))
    (x : LocalizedModule (KH.cellMon ℤ I) (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ)) :
    LocalizedModule (KH.cellMon (ZMod p) I) (MRingOver (ZMod p) ι ⧸ GenOnFibres.idealOver y (ZMod p)) :=
  x.liftOn (fun mt => LocalizedModule.mk (redRing y p mt.1) ⟨_, map_mem_cellMon p mt.2.2⟩) (by
    rintro ⟨m, s⟩ ⟨m', s'⟩ ⟨u, hu⟩
    refine LocalizedModule.mk_eq.mpr ⟨⟨_, map_mem_cellMon p u.2⟩, ?_⟩
    have h := congrArg (redRing y p) hu
    simp only [Submonoid.smul_def, redRing_smul] at h ⊢
    exact h)

theorem redLocFun_mk (y : (Σ k, ι k) → Ω) (p : ℕ) (I : ∀ k, Finset (ι k))
    (m : MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) (t : KH.cellMon ℤ I) :
    redLocFun y p I (LocalizedModule.mk m t) =
      LocalizedModule.mk (redRing y p m) ⟨_, map_mem_cellMon p t.2⟩ := by
  unfold redLocFun
  exact LocalizedModule.liftOn_mk _ _ _

def redLoc (y : (Σ k, ι k) → Ω) (p : ℕ) (I : ∀ k, Finset (ι k)) :
    LocalizedModule (KH.cellMon ℤ I) (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) →+
      LocalizedModule (KH.cellMon (ZMod p) I) (MRingOver (ZMod p) ι ⧸ GenOnFibres.idealOver y (ZMod p)) where
  toFun := redLocFun y p I
  map_zero' := by
    rw [← LocalizedModule.zero_mk 1, redLocFun_mk, map_zero, LocalizedModule.zero_mk]
  map_add' x x' := by
    induction x, x' using LocalizedModule.induction_on₂ with
    | h m m' s s' =>
      rw [LocalizedModule.mk_add_mk, redLocFun_mk, redLocFun_mk, redLocFun_mk,
        LocalizedModule.mk_add_mk, (redRing y p).map_add]
      simp only [Submonoid.smul_def, redRing_smul]
      congr 1
      exact Subtype.ext (map_mul _ _ _)

theorem redLoc_mk (y : (Σ k, ι k) → Ω) (p : ℕ) (I : ∀ k, Finset (ι k))
    (m : MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) (t : KH.cellMon ℤ I) :
    redLoc y p I (LocalizedModule.mk m t) = LocalizedModule.mk (redRing y p m) ⟨_, map_mem_cellMon p t.2⟩ :=
  redLocFun_mk y p I m t

def redCoch (y : (Σ k, ι k) → Ω) (p n : ℕ) :
    KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n →+
      KH.CechC (ZMod p) ι (MRingOver (ZMod p) ι ⧸ GenOnFibres.idealOver y (ZMod p)) n :=
  { toFun := fun w I => redLoc y p I.1 (w I)
    map_zero' := funext fun I => map_zero (redLoc y p I.1)
    map_add' := fun w w' => funext fun I => map_add (redLoc y p I.1) (w I) (w' I) }

theorem redCoch_apply (y : (Σ k, ι k) → Ω) (p n : ℕ)
    (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n) (I : KH.Cell K ι n) :
    redCoch y p n w I = redLoc y p I.1 (w I) :=
  rfl

end FibreReduction

def ReductionComplex.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (D p : ℕ) (a : K → ℤ),
    IsArithVar (mCoordIdeal y) (D + 1) → p.Prime →
    (∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      FibreReduction.redCoch y p (n + 1) (KH.cechD ℤ ι _ n w) =
        KH.cechD (ZMod p) ι _ n (FibreReduction.redCoch y p n w)) ∧
    (∀ n : ℕ, ∀ w ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n,
      FibreReduction.redCoch y p n w ∈
        KH.cechCc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a n) ∧
    (∀ n : ℕ, ∀ z ∈ KH.cechCc ι (KH.quotPart (ZMod p) (GenOnFibres.idealOver y (ZMod p))) a n,
      ∃ w ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n, FibreReduction.redCoch y p n w = z) ∧
    (∀ n : ℕ, ∀ w ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n,
      FibreReduction.redCoch y p n w = 0 →
        ∃ w' ∈ KH.cechCc ι (KH.quotPart ℤ (GenOnFibres.idealOver y ℤ)) a n, w = (p : ℤ) • w') ∧
    (∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n), (p : ℤ) • w = 0 → w = 0) ∧
    (∀ (n : ℕ) (w : KH.CechC ℤ ι (MRingOver ℤ ι ⧸ GenOnFibres.idealOver y ℤ) n),
      FibreReduction.redCoch y p n ((p : ℤ) • w) = 0)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRelChartPoly
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def RelChartPoly.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (R : Subalgebra ℤ Ω)
    (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k),
    ∀ σ ∈ Algebra.adjoin R (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩),
      ∃ N : ℕ, σ * (∏ k, y ⟨k, c k⟩) ^ N ∈ relSecM R y (fun _ => N)

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRelOneStep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def RelOneStep.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (R : Subalgebra ℤ Ω), IsNoetherianRing R → ∀ (y : (Σ k, ι k) → Ω) (c0 : ∀ k, ι k),
    (∀ k, y ⟨k, c0 k⟩ ≠ 0) → ∃ n₁ : ℕ, ∀ b : K → ℕ, (∀ k, n₁ ≤ b k) → ∀ k0 : K,
      ∀ t ∈ relChartLat R y (fun k => (b k : ℤ)) 1, y ⟨k0, c0 k0⟩ * t ∈ relSecM R y (b + Pi.single k0 1) →
        t ∈ relSecM R y b

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRelSectionsLarge
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def RelSectionsLarge.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (R : Subalgebra ℤ Ω), IsNoetherianRing R → ∀ y : (Σ k, ι k) → Ω, (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
      ∃ n₁ : ℕ, ∀ b : K → ℕ, (∀ k, n₁ ≤ b k) → relChartLat R y (fun k => (b k : ℤ)) 1 ≤ relSecM R y b

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsRelTorsionBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def RelTorsionBound.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (R : Subalgebra ℤ Ω), IsNoetherianRing R → ∀ (y : (Σ k, ι k) → Ω) (c0 : ∀ k, ι k),
    (∀ k, y ⟨k, c0 k⟩ ≠ 0) → ∀ k0 : K, ∃ n₁ : ℕ, ∀ b : K → ℕ, (∀ k, n₁ ≤ b k) →
      ∀ f ∈ relSecM R y (b + Pi.single k0 1),
        (∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∃ D : ℕ, ∃ g ∈ relSecM R y (b + fun _ => D),
          (∏ k, y ⟨k, c k⟩) ^ D * f = y ⟨k0, c0 k0⟩ * g) →
        ∃ g ∈ relSecM R y b, f = y ⟨k0, c0 k0⟩ * g

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockCoeffCycle
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def TwoBlockCoeffCycle.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (I : AllFam) (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (m m' : ConeMetric ℂ (Ix κ)) (c : κ) (l : Ix κ → ℤ),
    I.IsFamily → IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    IsSmoothMetric m → (∀ z, m'.ρ (matActC B z) = m.ρ z) →
    Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)) →
    x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j →
    ∀ i ≤ D, twoBlockCoeff I x (matAct B x) m m' D i = twoBlockVert x (matAct B x) c l (twoBlockDegList D i)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockCycleExpand
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def TwoBlockCycleExpand.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (c : κ) (l : Ix κ → ℤ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)) →
    x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j →
    ∀ a b : ℕ, twoBlockVert x (matAct B x) c l (fun _ : Fin D => ![(a : ℤ), (b : ℤ)]) =
      ∑ i ∈ Finset.range (D + 1), (D.choose i : ℝ) * (a : ℝ) ^ i * (b : ℝ) ^ (D - i) *
        twoBlockVert x (matAct B x) c l (twoBlockDegList D i)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwoBlockPieceCycle
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def TwoBlockPieceCycle.Statement : Prop :=
  ∀ (D : ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (κ : Type) [Fintype κ] (x : Ix κ → Ω)
    (B : Matrix (Ix κ) (Ix κ) ℚ) (c : κ) (l : Ix κ → ℤ),
    IsArithVar (ι := GlobalTheory κ) (coordIdeal ℤ x) (D + 1) → LinearIndependent ℤ x → IsInvMat B →
    Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)) →
    x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j →
    ∃ (a₀ : ℕ) (C : ℝ), ∀ a b : ℕ, a₀ ≤ a → a₀ ≤ b →
      |twoBlockStep x (matAct B x) a b -
          twoBlockVert x (matAct B x) c l (fun _ : Fin D => ![(a : ℤ), (b : ℤ)]) / (D.factorial : ℝ)| ≤
        C * ((a + b : ℝ) + 1) ^ D / ((a + b : ℝ) + 1)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.TwoBlockModule
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

set_option linter.unusedSectionVars false

section Module

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def modPieceCard (J₁ J₂ : Ideal (MRing ι)) (a : K → ℕ) : ℕ :=
  (J₂.restrictScalars ℤ ⊓ mHom ι a).toAddSubgroup.relIndex (J₁.restrictScalars ℤ ⊓ mHom ι a).toAddSubgroup

def topComps (J : Ideal (MRing ι)) (d : ℕ) : Set (Ideal (MRing ι)) :=
  {W | W ∈ J.minimalPrimes ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant W ∧
    ringKrullDim (MRing ι ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)}

theorem modPieceCard_self (J : Ideal (MRing ι)) (a : K → ℕ) : modPieceCard J J a = 1 :=
  AddSubgroup.relIndex_self _

end Module

section TwoBlock

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

def twoBlockMOuter (x x' : Ix κ → Ω) (c : κ) : Ideal (MRing (FinTwoTypeFamily κ)) :=
  twoBlockIdeal x x' ⊔ Ideal.span (Set.range fun j : κ => twoBlockDen c * X ⟨1, j⟩)

def twoBlockMInner (x x' : Ix κ → Ω) (l : Ix κ → ℤ) : Ideal (MRing (FinTwoTypeFamily κ)) :=
  twoBlockIdeal x x' ⊔ Ideal.span (Set.range fun i : κ => twoBlockNum l * X ⟨0, i⟩)

end TwoBlock

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

