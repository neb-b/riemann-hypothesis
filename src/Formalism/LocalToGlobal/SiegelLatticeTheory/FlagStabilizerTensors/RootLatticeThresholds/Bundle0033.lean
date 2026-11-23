module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0025
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0019
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0032
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0019
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0002
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
public import Formalism.SatakeDualWeyl.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.CoefWeightedLocHolds
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0010
public import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TermTiesEmptyOfLargeIndex
public import Formalism.LocalToGlobal.SiegelLatticeTheory.WeightedGaugeFactors.FactsDS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0027
public import Formalism.PeriodIntegrals.ZuckTensor
public import Formalism.PeriodIntegrals.UpqRep
public import Formalism.PeriodIntegrals.Bundle0011
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.HarishChandraMultiplicityBound
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0022
public import Formalism.LocalToGlobal.IndefiniteReal.SchurOrthogonality
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.HidaSetting
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.WeylBridge
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.BesselSplit
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LowerSmoothStability.ExistsFinStableOfMemSSup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0002

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyFinal
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Classical
open Formalism.FourierDecayAlt Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full

namespace Formalism.L2.SG.Pf.Carrier.EnergyFinal

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.Carrier.EnergyPf
  Formalism.L2.SG.Pf.Carrier.EnergyPlace Formalism.L2.SG.AdBridge Formalism.L2.SG.SpectralTiesReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word}

def PlaceNormG (P : Parts X u u') (hr : P.S.G.r = D.R.rS) : Prop :=
  ∀ (v : InfinitePlace X.B.I.F) (g : Formalism.REAL.UJ (X.B.I.ε v)) (cv : Fin (D.R.rS + 1) → ℂ), cv ∈ GoodV u u' →
    Zhat (X.B.I.ε v) (frm X u 1 v) (frm X u' 1 v) (uMat g) = Matrix.diagonal cv →
    hs2 (JvX X u u' v g) =
      ‖Formalism.FourierDecayAlt.B.hsVec (Formalism.FourierDecayAlt.B.JF (P.T (P.τ.symm v)).base (P.f (P.τ.symm v))
        (Formalism.FourierDecayAlt.B.gq (P.T (P.τ.symm v)).base (phiQ P hr cv)))‖ ^ 2

theorem placeNorm_of_G (P : Parts X u u') (hr : P.S.G.r = D.R.rS) (hG : PlaceNormG P hr)
    (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ) (hL : LocRep X u u' L) : PlaceNorm P hr L := by
  intro v cv hcv
  let c : Cinf X := fun _ => cv
  have hc : c ∈ Good X u u' := fun _ => hcv
  obtain ⟨γ, hγ⟩ := InfCut.ProductExactness.StepReal_holds D X u u' 1 one_pos c hc
  have hex : ∃ γ, HasDiag X u u' 1 c γ := ⟨γ, hγ⟩
  have hd : HasDiag X u u' 1 c (hOf X u u' 1 c) := by
    unfold hOf
    rw [dite_eq_left hex]
    exact hex.choose_spec
  have h1 : hs2 (JvX X u u' v ((hOf X u u' 1 c) v)) = L v cv := hL.2 c hc v
  have h2 := hG v ((hOf X u u' 1 c) v) cv hcv (hd v)
  exact h1.symm.trans h2

end Formalism.L2.SG.Pf.Carrier.EnergyFinal
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ConcreteSettingExists
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.SplitPrimeNormLemmas

namespace Formalism.L2.SG.Pf.Set3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Witt

variable {D : D7}

end Witt

end Formalism.L2.SG.Pf.Set3

namespace Formalism.L2.SG.Pf.Set3

variable (D : D7)

def WBlkExists : Prop :=
  Formalism.L2.SG.ConcreteSettingExists.GapHyp D → ∀ (A : UnitaryGroupInstance D) (L : UnitaryLatticeData D) (P : AdditiveCharacterData A) (Rf : ReferenceFrame A L)
    (Bu : AutomorphicBundle A P Rf) (Pi : RepresentationData A L) (Mu : MuBlocks A L), Nonempty (WBlk A L Bu Pi Mu)

end Formalism.L2.SG.Pf.Set3

namespace Formalism.L2.SG.Pf.Set3

variable {D : D7}

variable (D)

end Formalism.L2.SG.Pf.Set3
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTPh
section
noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.ProjRows Formalism.MainNotions.S
open scoped InnerProductSpace TensorProduct

namespace Formalism.L2.SG.EvalTPh

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem phLoc_int_of_gap (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D)
    (v : NumberField.InfinitePlace X.B.I.F) :
    Integrable (phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (X.dv v)) (Formalism.REAL.muG (X.B.I.ε v)) := by
  have h := Formalism.L2.SG.WuDecayPf.coef_integrable_of_weighted X
    (Formalism.L2.SG.Pf.WuDec.coefWeighted_of_gap X Formalism.L2.SG.Closed.CoefWeightedLoc_holds hG) v
  have hs : Integrable (star (Formalism.L2.SG.WuDecayPf.coefV X v)) (Formalism.REAL.muG (X.B.I.ε v)) :=
    memLp_one_iff_integrable.mp (memLp_one_iff_integrable.mpr h).star
  exact hs.const_mul (X.dv v : ℂ)

variable {S : D.what₂.Tau → SPar} {M : DSModel (D.sp.Y 0) S} {E : Submodule ℂ (MMap M)}
  {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {ι : GA D (D.sp.Y 0) ≃* X.B.I.GA} {t : GA D (D.sp.Y 0)} {v₀ : M.Vec}

end Formalism.L2.SG.EvalTPh

end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocUniq
section
noncomputable section

open MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.CayleySignature
open scoped InnerProductSpace ENNReal

namespace Formalism.L2.SG.Pf.WuDec

section Core

variable {k r : ℕ}

theorem lowSmoothSK {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} {w : H}
    (hds : IsDSHpk k r ε lam σ) (hlow : IsLowUnitH k r ε lam σ w) : w ∈ smoothVecs (k := k) (r := r) σ :=
  Formalism.L2.SG.Pf.k_finite_smooth k r ε lam H σ hds w (PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hlow)

theorem besselUniq_core (hBW : Formalism.L2.SG.LocWSOf.BesselOfW) (hM1 : Formalism.L2.SG.LitS.BesselMultOne)
    {z : Fin (2 * r + k + 1) → ℂ} {c : ℂ} {u : Fin k → ℝ} {lam : Fin (2 * r + k + 1) → ℝ}
    {ε : Fin (2 * r + k + 1) → Bool} {h : ℝ}
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Mat k r → (H →L[ℂ] H)}
    (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hds : IsDSHpk k r ε lam σ) (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam h)
    (hok : Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h) (hz : Formalism.QuantumDeterminants.inWb k r z) (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hc : c ≠ 0)
    {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [FiniteDimensional ℂ Vp] {π : Mat k r → (Vp →L[ℂ] Vp)}
    (hπ : IsHCTypeW k r z u π) {w : H} (hw : IsLowUnitH k r ε lam σ w) (hws : w ∈ smoothVecs (k := k) (r := r) σ)
    {μG μW μN ν : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hG : IsHaarOn (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) μG) (hW : IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) (hQ : IsQuotMeas μG (Formalism.MainNotions.S.muS μW μN) ν)
    {W W0 : Mat k r → Vp}
    (hc1 : ContinuousOn W (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))) (he1 : IsSPsiEquiv z (Formalism.QuantumDeterminants.psi k r z c) π W)
    (hr1 : ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => eFun μG σ w (Matrix.of g) • W (x * Matrix.of g)) μG ∧
      rconv μG (eFun μG σ w) W x = W x)
    (hl1 : l2SG ν W ≠ 0) (hl1' : l2SG ν W < ⊤)
    (hc2 : ContinuousOn W0 (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r))) (he2 : IsSPsiEquiv z (Formalism.QuantumDeterminants.psi k r z c) π W0)
    (hr2 : ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      Integrable (fun g : Formalism.QuantumDeterminants.Mt k r => eFun μG σ w (Matrix.of g) • W0 (x * Matrix.of g)) μG ∧
      rconv μG (eFun μG σ w) W0 x = W0 x)
    (hl2 : l2SG ν W0 ≠ 0) (hl2' : l2SG ν W0 < ⊤)
    (hx0 : ∃ x0 ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), W0 x0 ≠ 0) :
    ∃ a : ℂ, ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), W x = a • W0 x := by
  obtain ⟨B, hB, hWB⟩ := hBW k r z c u lam ε h H σ hl hds hg hok hz hT hc Vp π hπ w hw μG μW μN ν hG hW hN hQ
    W hc1 he1 hr1 hl1 hl1'
  obtain ⟨B0, hB0, hW0B⟩ := hBW k r z c u lam ε h H σ hl hds hg hok hz hT hc Vp π hπ w hw μG μW μN ν hG hW hN hQ
    W0 hc2 he2 hr2 hl2 hl2'
  rw [Formalism.L2.SG.LitS.psi_eq_psiGen] at hB hB0
  obtain ⟨a, b, hab, hlin⟩ := hM1 k r ε lam H σ z (fun _ => c) u Vp π hl hds hz hT (fun _ => hc) hπ B B0 hB hB0
  have hsm : ∀ x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r), σ x w ∈ smoothVecs (k := k) (r := r) σ :=
    fun x hx => Formalism.L2.SG.BesselSplit.smooth_translate_ds hds hws hx
  by_cases ha : a = 0
  · exfalso
    have hb : b ≠ 0 := hab.resolve_left (not_not.2 ha)
    obtain ⟨x0, hx0U, hx0W⟩ := hx0
    have h1 := hlin (σ x0 w) (hsm x0 hx0U)
    rw [ha, zero_smul, zero_add] at h1
    have h2 : B0 (σ x0 w) = 0 := (smul_eq_zero.1 h1).resolve_left hb
    exact hx0W (by rw [hW0B x0 hx0U, h2])
  · refine ⟨-(b / a), fun x hx => ?_⟩
    have h1 := hlin (σ x w) (hsm x hx)
    rw [hWB x hx, hW0B x hx]
    have : a • B (σ x w) = -(b • B0 (σ x w)) := eq_neg_of_add_eq_zero_left h1
    calc B (σ x w) = a⁻¹ • (a • B (σ x w)) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
      _ = -(b / a) • B0 (σ x w) := by
          rw [this, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]

end Core

end Formalism.L2.SG.Pf.WuDec
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.YcUnitary
section
noncomputable section

open Matrix

namespace Formalism.L2.S.L6.UnitaryStandardVectors

open Formalism.L2.SG.HidaSetting

variable {N r : ℕ} (ε : Fin N → Bool) (F G : Fin (r + 1) → Fin N → ℂ)

def Wfg : Matrix (Fin N) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ := Matrix.of fun p k => Sum.elim F G k p

theorem gram_Wfg : (Wfg F G)ᴴ * Formalism.REAL.Jm ε * Wfg F G =
    Matrix.fromBlocks (Matrix.of fun a b => hJ ε (F a) (F b)) (Matrix.of fun a b => hJ ε (F a) (G b))
      (Matrix.of fun a b => hJ ε (G a) (F b)) (Matrix.of fun a b => hJ ε (G a) (G b)) := by
  ext k l
  rw [Matrix.mul_assoc]
  rcases k with a | a <;> rcases l with b | b <;>
    simp [hJ, Matrix.mul_apply, mulVec, dotProduct, Wfg, conjTranspose_apply]

theorem wjx (x : Fin N → ℂ) : ((Wfg F G)ᴴ * Formalism.REAL.Jm ε) *ᵥ x = Sum.elim (fun a => hJ ε (F a) x) (fun b => hJ ε (G b) x) := by
  funext k
  rw [← mulVec_mulVec]
  rcases k with a | b <;> simp [hJ, mulVec, dotProduct, Wfg, conjTranspose_apply]

theorem Wfg_mulVec (v : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) :
    Wfg F G *ᵥ v = ∑ a, v (Sum.inl a) • F a + ∑ b, v (Sum.inr b) • G b := by
  funext p
  simp [mulVec, dotProduct, Fintype.sum_sum_type, Wfg, Finset.sum_apply, mul_comm]

section Main

variable (T T' : ℝ) (π : Fin (r + 1) → Fin (r + 1)) (blk : Fin (r + 1) → ℕ)

def Zm : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.of fun a b => hJ ε (F a) (G b)

def Am (C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  (Zm ε F G * C⁻¹ * (Zm ε F G)⁻¹)ᴴ

def Mm (C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ :=
  Matrix.fromBlocks (Am ε F G C - 1) 0 0 (C - 1)

def Yc (C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  Ymat (Formalism.REAL.Jm ε) (Wfg F G) (Mm ε F G C)

variable (hFF : ∀ a b, hJ ε (F a) (F b) = lastDiag (-(T : ℂ)) a b)
  (hGG : ∀ a b, hJ ε (G a) (G b) = lastDiag (-(T' : ℂ)) a b)
  (hπ : ∀ a, π (π a) = a) (hblk : ∀ a, blk (π a) = blk a) (hanti : ∀ a b, blk a = blk b → a < b → π b < π a)
  (hZ : ∀ c b, Zm ε F G c b ≠ 0 ↔ c = π b)
  (hgap : 1 - (T : ℂ) * T' * ((Zm ε F G)⁻¹ (Fin.last r) (Fin.last r) *
    starRingEnd ℂ ((Zm ε F G)⁻¹ (Fin.last r) (Fin.last r))) ≠ 0)

theorem Jm_herm : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a = true <;> simp [h]

include hFF hGG hπ hZ in
theorem gram_eq : (Wfg F G)ᴴ * Formalism.REAL.Jm ε * Wfg F G =
    Matrix.fromBlocks (lastDiag (-(T : ℂ))) (Zm ε F G) (Zm ε F G)ᴴ (lastDiag (-(T' : ℂ))) := by
  rw [gram_Wfg]
  refine fromBlocks_inj.2 ⟨?_, rfl, ?_, ?_⟩
  · ext a b
    simp [hFF]
  · ext a b
    simp only [of_apply, conjTranspose_apply, Zm]
    unfold hJ Formalism.REAL.Jm
    simp only [mulVec_diagonal, dotProduct, star_sum, star_mul', star_star, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp <;> ring
  · ext a b
    simp [hGG]

include hFF hGG hπ hZ hgap in
theorem gram_unit : IsUnit ((Wfg F G)ᴴ * Formalism.REAL.Jm ε * Wfg F G).det := by
  rw [gram_eq ε F G T T' π hFF hGG hπ hZ]
  exact gram_isUnit _ (isUnit_Z π hπ _ hZ) T T' hgap

include hFF hGG hπ hblk hanti hZ hgap in
theorem Yc_unitary {C : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hC : IsUB blk C) :
    (Yc ε F G C)ᴴ * Formalism.REAL.Jm ε * Yc ε F G C = Formalism.REAL.Jm ε := by
  have hA := isUB_A π hπ hblk hanti (Zm ε F G) hZ hC
  have hAZC : (Am ε F G C)ᴴ * Zm ε F G * C = Zm ε F G := A_Z_C π hπ hblk hanti _ hZ hC
  have hL : ∀ t : ℂ, ∀ i j : Fin (r + 1), i ≠ Fin.last r ∨ j ≠ Fin.last r → lastDiag t i j = 0 := by
    intro t i j h
    simp only [lastDiag, of_apply]
    rw [if_neg]
    tauto
  unfold Yc
  refine Ymat_unitary _ (Jm_herm ε) _ _ (gram_unit ε F G T T' π hFF hGG hπ hZ hgap) ?_
  rw [gram_eq ε F G T T' π hFF hGG hπ hZ]
  have h1 : (1 : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ) + Mm ε F G C =
      fromBlocks (Am ε F G C) 0 0 C := by
    rw [Mm, ← fromBlocks_one, fromBlocks_add]
    simp
  rw [h1, fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp only [conjTranspose_zero, zero_mul, mul_zero, add_zero, zero_add]
  refine fromBlocks_inj.2 ⟨?_, ?_, ?_, ?_⟩
  · exact gram_last hA _ (hL _)
  · exact hAZC
  · have h2 := congrArg conjTranspose hAZC
    simpa [conjTranspose_mul, Matrix.mul_assoc] using h2
  · exact gram_last hC _ (hL _)

end Main

end Formalism.L2.S.L6.UnitaryStandardVectors
end
end

