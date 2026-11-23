module

public import Formalism.SharpRestriction.GlobalSchurBounds.LinkMin
public import Formalism.LocalToGlobal.GlobalTheory.GL6.Bundle0003
public import Formalism.LocalToGlobal.HermitianForms.TiedSym
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.Bundle0002
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Formalism.LocalToGlobal.GlobalTheory.GL5.TheoremThreeAllUnitary
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
public import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
public import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.NumericSettingWithGapSatisfiable

@[expose] public section

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.IntegralityOfRationalityLocal
section
noncomputable section

namespace Formalism.MainNotions.RT

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.GlobalTheoryTheory

variable (D : D7) (u : D.what₂.Word)


variable {D u} in
def ChiFin0 {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (T : Formalism.L2.Forms.FormsTiedSym D u Ch chOf) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∀ x : (T.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.U,
    ((((T.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.chi x : ℂˣ) : ℂ)) ^ n = 1 ∧
      ∃ r : D.what₂.LL, D.what₂.embLL r = (((T.cls 0 (Nat.zero_le _) (Or.inl rfl)).lev.chi x : ℂˣ) : ℂ)

def FormsTwistCompatibilityFamily : Prop :=
  ∃ (Ch : ℕ → Type) (chOf : ∀ i, (D.mem u).C.cls i → Ch i) (T : Formalism.L2.Forms.FormsTiedSym D u Ch chOf), ChiFin0 T

def IntegralityLevelZeroUnderForms : Prop := FormsTwistCompatibilityFamily D u → admS D u → HidaSetting D u → LocalLatticeBases.HeckeIntegralLevelZero D u

variable {D u}

variable {eps : ℝ}

theorem hI_tied (Fm : FamP eps) (tie : FamU Fm fun D u => FormsTwistCompatibilityFamily D u ∧ admS D u)
    (hI : ∀ (D : D7) (u : D.what₂.Word), IntegralityLevelZeroUnderForms D u) : FamU Fm LocalLatticeBases.HeckeIntegralLevelZero := by
  obtain ⟨x0, hx0⟩ := tie
  refine ⟨x0, fun x hx hx1 i u hs => ?_⟩
  obtain ⟨hT, hA⟩ := hx0 x hx hx1 i u hs
  exact hI _ _ hT hA hs

end Formalism.MainNotions.RT

end
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.MassRatioUnfoldedOfTheoremTwo
section
noncomputable section

namespace Formalism.MainNotions.RT

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory

def MassRatioUnderVolume (D : D7) : Prop := StandardLattice.VolTie D → StandardLattice.VolumeRatio₂ D

theorem volTie_of_realTied (D : D7) (h : Formalism.L2.Theta.RealTied D) : StandardLattice.VolTie D := by
  intro W P Q hW hs
  have hv := h.vol W hW
  simp only [hs] at hv
  exact hv

variable {eps : ℝ}

end Formalism.MainNotions.RT

end
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeUnderScaleOfGeneral
section
noncomputable section

namespace Formalism.MainNotions.RT

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S MeasureTheory Matrix

def DiscreteSeriesDegreeBoundsOfScaleAgreement (D : D7) : Prop := cdScaleTie D → StandardLattice.DiscreteSeriesDegreeBoundsOfGap D

def cdScaleTieR (cd : CDHaar) (s : (n : ℕ) → (Fin n → Bool) → NNReal) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n),
    (∀ i, ε (e (Sum.inl i)) = true) → (∀ j, ε (e (Sum.inr j)) = false) →
    ∀ A : Set (Formalism.REAL.UJ ε), MeasurableSet A →
      ((s n ε : ENNReal) • Formalism.REAL.muG ε) A =
        cd.cd P Q {g | ∃ a ∈ A, umat a = Matrix.reindex e e (Formalism.BasicNotions.UpqT.mat g)}

theorem cdScaleTie_iff (D : D7) : cdScaleTie D ↔ cdScaleTieR D.cd D.s.cdScale := Iff.rfl

def DiscreteSeriesDegreeBoundsAtScale (s : (n : ℕ) → (Fin n → Bool) → NNReal) : Prop :=
  ∀ (N : ℕ) (ε : Fin N → Bool) (lam : Fin N → ℝ) (ep0 h0 : ℝ) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (w : H),
    let p : ℝ := (Finset.univ.filter (fun a => ε a = true)).card
    let q : ℝ := (Finset.univ.filter (fun a => ε a = false)).card
    1 ≤ p → 1 ≤ q →
    Formalism.QuantumDeterminants.IsHCParam lam → Formalism.QuantumDeterminants.GapAtLeast ε lam h0 →
    Real.exp (-(N : ℝ)) ≤ ep0 → ep0 < 1 / 2 →
    8192 * min p q * (p * q) ^ 3 * Real.log N / ep0 ^ 2 ≤ h0 →
    IsDS ε lam σ → w ≠ 0 →
    (1 - ep0) * Formalism.QuantumDeterminants.fdegHC lam ≤ fdegOf ((s N ε : ENNReal) • Formalism.REAL.muG ε) σ w ∧
    fdegOf ((s N ε : ENNReal) • Formalism.REAL.muG ε) σ w ≤
      4 * (Module.finrank ℂ (lowKSub ε lam σ) : ℝ) * (3 * p * q * StandardLattice.lamAbs lam) ^ (p * q)

theorem theorem_three_explicit_iff_scale (D : D7) : StandardLattice.DiscreteSeriesDegreeBoundsOfGap D ↔ DiscreteSeriesDegreeBoundsAtScale D.s.cdScale := Iff.rfl

def DiscreteSeriesDegreeBoundsAllScales : Prop :=
  ∀ (cd : CDHaar) (s : (n : ℕ) → (Fin n → Bool) → NNReal), cdScaleTieR cd s → DiscreteSeriesDegreeBoundsAtScale s

theorem theorem_three_under_scale_of_general (h : DiscreteSeriesDegreeBoundsAllScales) (D : D7) : DiscreteSeriesDegreeBoundsOfScaleAgreement D := fun hT => (theorem_three_explicit_iff_scale D).mpr (h D.cd D.s.cdScale ((cdScaleTie_iff D).mp hT))

variable {eps : ℝ}

end Formalism.MainNotions.RT

end
end

