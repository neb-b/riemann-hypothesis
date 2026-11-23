module

public import Mathlib
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.InstCommRingBcris
public import GroundTheory.PAdicHodge.BStPeriod
public import GroundTheory.PAdicHodge.BdRAlg

@[expose] public section

noncomputable section

namespace DeRhamPotentiallySemistable.DRPst

open Formalism.Per6 GroundTheory.PAdicHodge

variable (l : ℕ) [Fact l.Prime]

def qQ : ℚ_[l] →+* BdR l := (algebraMap (BdRp l) (BdR l)).comp (algebraMap ℚ_[l] (BdRp l))

def iC : ACris.ACris ℂ_[l] l →+* BdR l :=
  (algebraMap (BdRp l) (BdR l)).comp (ACris.iota ℂ_[l] l)

def tQ : BdR l := iC l (tA l)

def uQ : BdR l := algebraMap (BdRp l) (BdR l) (uBdR l)

def Bst : Subring (BdR l) :=
  Subring.closure (Set.range (iC l) ∪ {((l : BdR l))⁻¹, (tQ l)⁻¹, uQ l})

variable {l}

def IsAdm (S : Set (BdR l)) {d : ℕ} (G : Subgroup (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l))
    (r : G → Matrix (Fin d) (Fin d) ℚ_[l]) : Prop :=
  ∃ P Q : Matrix (Fin d) (Fin d) (BdR l), (∀ i j, P i j ∈ S ∧ Q i j ∈ S) ∧ P * Q = 1 ∧
    ∀ σ : G, (r σ).map (qQ l) * P.map (σD σ.1) = P

end DeRhamPotentiallySemistable.DRPst

