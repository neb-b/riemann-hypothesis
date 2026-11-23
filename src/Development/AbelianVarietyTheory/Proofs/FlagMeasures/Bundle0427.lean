module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0217
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RedBasicsPf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodAtReductionConjugatedUnitaryElement
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0135
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0376
public import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1620
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0216
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteCosetsHeckeSetAtSplitPlaceOutsideLevel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularChangeRationalFlagIffRationalUnipot
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0421
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0422
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0420
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0424

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemMaximalCompactOfTrivialOffSplitPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

noncomputable section

namespace GlobalTheory.SplitPairK

open Matrix Formalism.MainNotions.S GlobalTheory.RowLev
open scoped TensorProduct

theorem hform_mulVec_mulVec {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A)
    (J M : Matrix n n A) (x y : n → A) :
    Formalism.UG.hform σ J (M *ᵥ x) (M *ᵥ y) = Formalism.UG.hform σ (Formalism.UG.cT σ M * J * M) x y := by
  have e : ∀ (N : Matrix n n A) (u v : n → A), Formalism.UG.hform σ N u v = (σ ∘ u) ⬝ᵥ (N *ᵥ v) := by
    intro N u v
    simp only [Formalism.UG.hform, dotProduct, mulVec, Function.comp_apply, Finset.mul_sum, mul_assoc]
  have hσ : σ ∘ (M *ᵥ x) = M.map σ *ᵥ (σ ∘ x) := by
    funext i
    exact RingHom.map_mulVec σ M x i
  rw [e, e, hσ, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec,
    mulVec_mulVec, Formalism.UG.cT, Matrix.mul_assoc]

variable (I : AutInst)

theorem fmat_mul_inv (x : I.Gf) : I.fmat x * I.fmat x⁻¹ = 1 := by
  simp [AutInst.fmat]

theorem fmat_inv_mul (x : I.Gf) : I.fmat x⁻¹ * I.fmat x = 1 := by
  simp [AutInst.fmat]

theorem hAf_unitary (x : I.Gf) (v w : Fin I.n → I.E ⊗[I.F] Af I.F) :
    hAf I (I.fmat x *ᵥ v) (I.fmat x *ᵥ w) = hAf I v w := by
  unfold hAf
  rw [hform_mulVec_mulVec]
  have h : Formalism.UG.cT (Formalism.UG.sigR I.cm.sig (Af I.F)) (I.fmat x) * I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) *
      I.fmat x = I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F)) := x.2
  rw [h]

theorem hAf_move (x : I.Gf) (v w : Fin I.n → I.E ⊗[I.F] Af I.F) :
    hAf I v (I.fmat x *ᵥ w) = hAf I (I.fmat x⁻¹ *ᵥ v) w := by
  rw [← hAf_unitary I x (I.fmat x⁻¹ *ᵥ v) w, mulVec_mulVec, fmat_mul_inv, one_mulVec]

theorem hAf_smul_right (v w : Fin I.n → I.E ⊗[I.F] Af I.F) (c : I.E ⊗[I.F] Af I.F) :
    hAf I v (c • w) = c * hAf I v w := by
  simp only [hAf, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hAf_smul_left (v w : Fin I.n → I.E ⊗[I.F] Af I.F) (c : I.E ⊗[I.F] Af I.F) :
    hAf I (c • v) w = sigA I c * hAf I v w := by
  simp only [hAf, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hAf_sub_right (u v w : Fin I.n → I.E ⊗[I.F] Af I.F) : hAf I u (v - w) = hAf I u v - hAf I u w := by
  simp only [hAf, Formalism.UG.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem hAf_sub_left (u u' w : Fin I.n → I.E ⊗[I.F] Af I.F) : hAf I (u - u') w = hAf I u w - hAf I u' w := by
  simp only [hAf, Formalism.UG.hform, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem lf_iff {β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hβ : Formalism.L2.DIV.IsFrame β₀ I.L)
    (y : Fin I.n → I.E ⊗[I.F] Af I.F) :
    y ∈ I.Lf ↔ ∀ i, (((β₀⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))
      *ᵥ y) i ∈ IntAf I.F I.E := by
  have e : Formalism.L2.Herm.hatL (F := I.F) I.L = I.Lf := by
    show Submodule.span _ _ = Submodule.span _ _
    congr 1
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hz⟩, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z.1, z.2, rfl⟩
  rw [← e]
  exact hβ y

theorem eps_mem {β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hβ : Formalism.L2.DIV.IsFrame β₀ I.L)
    {ε : I.E ⊗[I.F] Af I.F} (hεi : ε ∈ IntAf I.F I.E) (x : I.Gf)
    (hx : ∀ i j, ε * ((β₀⁻¹ * (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
      Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j ∈ IntAf I.F I.E)
    {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ I.Lf) :
    ε • ((I.fmat x - 1) *ᵥ y) ∈ I.Lf := by
  rw [lf_iff I hβ] at hy ⊢
  intro i
  set Bi : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) :=
    ((β₀⁻¹ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) with hBi
  set B : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F) :=
    ((β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) with hB
  have hBB : B * Bi = 1 := by rw [hB, hBi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hM : ∀ i j, ε * (Bi * I.fmat x * B) i j ∈ IntAf I.F I.E := by
    intro i j
    have := hx i j
    rwa [Units.val_mul, Units.val_mul] at this
  have key : Bi *ᵥ ((I.fmat x - 1) *ᵥ y) = (Bi * I.fmat x * B) *ᵥ (Bi *ᵥ y) - Bi *ᵥ y := by
    rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc (Bi * I.fmat x), hBB, Matrix.mul_one, Matrix.mul_sub,
      Matrix.mul_one, sub_mulVec]
  rw [mulVec_smul, key]
  generalize Bi *ᵥ y = z at hy ⊢
  show ε * ((Bi * I.fmat x * B) *ᵥ z - z) i ∈ IntAf I.F I.E
  rw [Pi.sub_apply, mul_sub]
  refine sub_mem ?_ (mul_mem hεi (hy i))
  simp only [mulVec, dotProduct, Finset.mul_sum]
  refine Subring.sum_mem _ fun j _ => ?_
  rw [← mul_assoc]
  exact mul_mem (hM i j) (hy j)

theorem sig_mem {β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hβ : Formalism.L2.DIV.IsFrame β₀ I.L)
    {ε : I.E ⊗[I.F] Af I.F} (hεi : ε ∈ IntAf I.F I.E) (x : I.Gf)
    (hxi : ∀ i j, ε * ((β₀⁻¹ * ((x⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
      Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j ∈ IntAf I.F I.E)
    {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ I.Lf) :
    sigA I ε • ((I.fmat x - 1) *ᵥ y) ∈ I.Lf := by
  rw [GlobalTheory.AdelicLattice.adelicLattice_selfDual]
  intro y' hy'
  have h1 := eps_mem I hβ hεi x⁻¹ hxi hy'
  have h2 := (GlobalTheory.AdelicLattice.adelicLattice_selfDual I y).1 hy _ h1
  have e : hAf I y' (sigA I ε • ((I.fmat x - 1) *ᵥ y)) = hAf I (ε • ((I.fmat x⁻¹ - 1) *ᵥ y')) y := by
    rw [hAf_smul_right, hAf_smul_left, sub_mulVec, sub_mulVec, one_mulVec, one_mulVec, hAf_sub_right,
      hAf_sub_left, hAf_move]
  rw [e]
  exact h2

theorem mv_mem {β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)} (hβ : Formalism.L2.DIV.IsFrame β₀ I.L)
    {ε : I.E ⊗[I.F] Af I.F} (hεi : ε ∈ IntAf I.F I.E) (x : I.Gf)
    (h1 : ∀ i j, (1 - ε - sigA I ε) * (I.fmat x - 1) i j = 0)
    (hx : ∀ i j, ε * ((β₀⁻¹ * (x : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
      Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j ∈ IntAf I.F I.E)
    (hxi : ∀ i j, ε * ((β₀⁻¹ * ((x⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) :
      Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F)) i j ∈ IntAf I.F I.E)
    {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ I.Lf) :
    I.fmat x *ᵥ y ∈ I.Lf := by
  set w := (I.fmat x - 1) *ᵥ y with hw
  have hxy : I.fmat x *ᵥ y = y + w := by
    rw [hw, sub_mulVec, one_mulVec]
    abel
  have h0 : (1 - ε - sigA I ε) • w = 0 := by
    funext i
    simp only [hw, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, Finset.mul_sum, Pi.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← mul_assoc, h1 i j, zero_mul]
  have hsplit : w = ε • w + sigA I ε • w + (1 - ε - sigA I ε) • w := by
    rw [← add_smul, ← add_smul, show ε + sigA I ε + (1 - ε - sigA I ε) = 1 by ring, one_smul]
  rw [hxy, hsplit, h0, add_zero, ← add_assoc]
  exact add_mem (add_mem hy (eps_mem I hβ hεi x hx hy)) (sig_mem I hβ hεi x hxi hy)

end GlobalTheory.SplitPairK


open GlobalTheory.SplitPairK in
theorem GlobalTheory.SplitPairK.mem_kset_of_split : ∀ (I : Formalism.MainNotions.S.AutInst) (β₀ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)), Formalism.L2.DIV.IsFrame β₀ I.L → ∀ (ε : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F), ε * ε = ε → ε * Formalism.L2.SG.HidaSetting.sigA I ε = 0 → ε ∈ Formalism.MainNotions.S.IntAf I.F I.E → ∀ (k : I.Gf), (∀ i j, (1 - ε - Formalism.L2.SG.HidaSetting.sigA I ε) * (I.fmat k - 1) i j = 0) → (∀ i j, ε * ((β₀⁻¹ * (k : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) i j ∈ Formalism.MainNotions.S.IntAf I.F I.E) → (∀ i j, ε * ((β₀⁻¹ * ((k⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * β₀ : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) i j ∈ Formalism.MainNotions.S.IntAf I.F I.E) → k ∈ I.Kset := by
  intro I β₀ hβ ε _ _ hεi k h1 h2 h3
  have h1' : ∀ i j, (1 - ε - sigA I ε) * (I.fmat k⁻¹ - 1) i j = 0 := by
    intro i j
    have e : I.fmat k⁻¹ - 1 = -(I.fmat k⁻¹ * (I.fmat k - 1)) := by
      rw [Matrix.mul_sub, fmat_inv_mul, Matrix.mul_one]
      abel
    rw [e, Matrix.neg_apply, Matrix.mul_apply, mul_neg, Finset.mul_sum, neg_eq_zero]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [mul_left_comm, h1 l j, mul_zero]
  have h3' : ∀ i j, ε * ((β₀⁻¹ * ((k⁻¹⁻¹ : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) * β₀ :
      GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F)) i j ∈
      Formalism.MainNotions.S.IntAf I.F I.E := by
    simpa only [inv_inv] using h2
  show ((k : GL (Fin I.n) (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F))) ∈ Formalism.UG.stabGL I.Lf
  intro y
  refine ⟨fun hy => mv_mem I hβ hεi k h1 h2 h3 hy, fun hy => ?_⟩
  have := mv_mem I hβ hεi k⁻¹ h1' h3 h3' hy
  rwa [Matrix.mulVec_mulVec, fmat_inv_mul, Matrix.one_mulVec] at this

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalUnipotentGroupsLatticesGlobalCoordinates
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL.GrpCoord

theorem rat_iff (D : D7) (Z : LocDat D) {T T' : D.host.E} (F0 : LFlag (D.sp.Y 0) D.R.rS T) (F0' : LFlag (D.sp.Y 0) D.R.rS T')
    (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (G : GFrames (placesOf Z) D.R.rS D.R.k) (c : GCoord Z F0 F0' FP G)
    {T₁ : D.host.E} (F₁ : LFlag (D.sp.Y 0) D.R.rS T₁) (g : ∀ p, Fin (D.R.rS + 1) → (G.S p).V)
    (hg : ∀ p a, g p a = (c.c p).e (scaled Z p (frame F₁) a)) (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    γ ∈ NRat F₁ ↔ (c.e.symm.trans γ).trans c.e ∈ (placesOf Z).rat (fun p => (G.S p).Nof (g p)) := by
  have hgf : ∀ p, g p = fun a => (c.c p).e (scaled Z p (frame F₁) a) := fun p => funext (hg p)
  constructor
  · intro hγ p
    obtain ⟨h, hext, -, -, -, hNU⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D Z p γ hγ.1
    let k := ((c.c p).e.symm.trans h).trans (c.c p).e
    have hk : k ∈ (G.S p).Nof (g p) := by
      rw [hgf p]; exact (GlobalTheory.T.localUnipotent_frame_corresponds_under_isometry (c.c p) _ h).1 (hNU F₁ hγ)
    refine ⟨k, hk, ?_⟩
    · intro x
      obtain ⟨y, rfl⟩ := c.e.surjective x
      have h1 : (placesOf Z).bc p (c.e y) = (c.c p).e (baseChange₂ D p y) := (c.compat p y).symm
      have h2 : ((c.e.symm.trans γ).trans c.e) (c.e y) = c.e (γ y) := by simp
      rw [h2, h1, ← c.compat p (γ y), ← hext y]
      show (c.c p).e (h ((c.c p).e.symm ((c.c p).e (baseChange₂ D p y)))) = _
      rw [LinearEquiv.symm_apply_apply]
  · intro hγ
    have hne : Nonempty (PlF D) := by
      obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.F)
      exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField _)⟩⟩
    obtain ⟨p⟩ := hne
    obtain ⟨g₀, hg'N, hg'E⟩ := hγ p
    let g' : type_of% ((c.c p).e.symm.trans (c.c p).e) := g₀
    let h : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p := ((c.c p).e.trans g').trans (c.c p).e.symm
    have hconj : ((c.c p).e.symm.trans h).trans (c.c p).e = g' := by
      ext x; simp [h]
    have hN : h ∈ NU (locH Z p) (scaled Z p (frame F₁)) := by
      rw [GlobalTheory.T.localUnipotent_frame_corresponds_under_isometry (c.c p), hconj, ← hgf p]; exact hg'N
    refine _root_.GlobalTheory.LocReflect.mem_nrat_of_ext D Z p F₁ γ h ?_ hN
    intro y
    have h1 : (c.c p).e (baseChange₂ D p y) = (placesOf Z).bc p (c.e y) := c.compat p y
    have h3 : g₀ ((placesOf Z).bc p (c.e y)) = (placesOf Z).bc p (c.e (γ y)) :=
      (hg'E _).trans (by simp)
    show (c.c p).e.symm (g₀ ((c.c p).e (baseChange₂ D p y))) = baseChange₂ D p (γ y)
    rw [h1, h3, ← c.compat p (γ y), LinearEquiv.symm_apply_apply]

theorem grp_eq {D : D7} {Z : LocDat D} {T T' : D.host.E} {F0 : LFlag (D.sp.Y 0) D.R.rS T} {F0' : LFlag (D.sp.Y 0) D.R.rS T'}
    {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS} {G : GFrames (placesOf Z) D.R.rS D.R.k} (c : GCoord Z F0 F0' FP G)
    (σ n : (VS D).V ≃ₗ[D.host.E] (VS D).V) : c.grp σ n = (c.e.symm.trans (σ * n * σ⁻¹)).trans c.e := by
  ext x; simp [GCoord.grp]

theorem frame_mapLF (D : D7) {T : D.host.E} (γ : (VS D).V ≃ₗ[D.host.E] (VS D).V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT)
    (F : LFlag (D.sp.Y 0) D.R.rS T) (b : Fin (D.R.rS + 1)) : frame (mapLF γ F) b = γ (frame F b) := by
  unfold mapLF; rw [dite_eq_left hγ]
  induction b using Fin.lastCases with
  | last => simp [frame, FlagG.fvec, mapFlag]
  | cast b => simp [frame, FlagG.fvec, mapFlag]

theorem grp_coords : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → (∀ n, n ∈ NRat (lf D (X.Fu u)) ↔ c.grp ρ n ∈ G.N) ∧ (∀ m, m ∈ NRat (lf D (X.Fu u')) ↔ c.grp (ρ * t₀.lin) m ∈ G.N') ∧ (∀ (σ n : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) Λ, c.lat (σ * n) Λ = (c.lat σ Λ).map (((c.grp σ n : G.GLV) : G.V →ₗ[D.host.E] G.V).restrictScalars (𝓞 D.host.E))) ∧ (∀ (σ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (x : G.GLV), ∃ n, c.grp σ n = x) ∧ (∀ σ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT, ∀ (p : PlF D) g Λ, GlobalTheory.LocOver.Ext p σ g → (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).lat p (c.lat σ Λ) = (c.c p).lat (LocNG.img (M := Y.M p) g (lattice₂ D Y.M p Λ))) ∧ ∀ (t : TauC Y u u') n m, n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ∃ A A' : Formalism.L2.SG.PairVal.MatR D, IsUpUni A ∧ IsUpUni A' ∧ (∀ b, n (frame (lf D (X.Fu u)) b) = ∑ a, A a b • frame (lf D (X.Fu u)) a) ∧ (∀ b, m (frame (lf D (X.Fu u')) b) = ∑ a, A' a b • frame (lf D (X.Fu u')) a) ∧ MovesTo F00 F'0 (lf D (X.Fu u)) t.frame (ρ * n) (U * A) (U' * A') := by
  intro D X Y u u' _ _ w F00 F'0 FP _ _ hAB G c t₀ ρ U U' hmv
  obtain ⟨hρ, hU, hU', hF, hF'⟩ := hmv
  have hN : G.N = (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).rat
      (fun p => (G.S p).Nof (fun a => (c.c p).e (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame F00) a))) := by
    unfold GFrames.N Frames.N
    congr 1; funext p; congr 1; funext a; rw [(c.c p).f_eq, (hAB p).1.1]
  have hN' : G.N' = (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)).rat
      (fun p => (G.S p).Nof (fun a => (c.c p).e (scaled (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p (frame F'0) a))) := by
    unfold GFrames.N' Frames.N'
    congr 1; funext p; congr 1; funext a; rw [(c.c p).f'_eq, (hAB p).1.2.1]
  have hlin : t₀.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t₀.rep.2.2.1
  refine ⟨fun n => ?_, fun m => ?_, fun σ n Λ => ?_, fun σ x => ?_, fun σ _ p g Λ hg => ?_, ?_⟩
  · refine (_root_.GlobalTheory.FlagMove.nrat_conj_iff D _ F00 ρ U hρ hU hF n).trans ?_
    rw [grp_eq, hN]
    exact rat_iff D _ F00 F'0 FP G c _ _ (fun p a => rfl) _
  · have hF2 : ∀ b, (ρ * t₀.lin) (frame (lf D (X.Fu u')) b) = ∑ a, U' a b • frame F'0 a := by
      intro b
      rw [← hF' b]
      show ρ (t₀.lin _) = ρ (frame (mapLF t₀.lin (lf D (X.Fu u'))) b)
      rw [frame_mapLF D _ hlin]
    refine (_root_.GlobalTheory.FlagMove.nrat_conj_iff D _ F'0 (ρ * t₀.lin) U' (Subgroup.mul_mem _ hρ hlin) hU' hF2 m).trans ?_
    rw [grp_eq, hN']
    exact rat_iff D _ F00 F'0 FP G c _ _ (fun p a => rfl) _
  · unfold GCoord.lat
    rw [← Submodule.map_comp]
    congr 1
    ext x
    simp [GCoord.grp]
  · refine ⟨((σ.trans c.e).trans x).trans (σ.trans c.e).symm, ?_⟩
    ext y; simp [GCoord.grp]
  · exact GlobalTheory.T.completion_moved_lattice_eq_local_coordinates D _ F00 F'0 FP G c σ p g Λ hg
  · exact _root_.GlobalTheory.FrameStep.step D X Y u u' F00 F'0 t₀ ρ U U' ⟨hρ, hU, hU', hF, hF'⟩

end GlobalTheory.HL.GrpCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ResidueCmFieldFiniteAdeleTensorEquivEqNatCast
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM

noncomputable section

namespace GlobalTheory.SplitRes

open IsDedekindDomain

section Cast

variable {E : Type} [Field E] [NumberField E]

theorem tensCastR_comm_symm_tmul_one {F₁ F₂ : Subfield E} (h : F₁ = F₂) (y : E) :
    GlobalTheory.StdFrame.tensCastR h ((Algebra.TensorProduct.comm F₁ (FiniteAdeleRing (𝓞 F₁) F₁) E).symm
      (y ⊗ₜ[F₁] (1 : FiniteAdeleRing (𝓞 F₁) F₁))) = y ⊗ₜ[F₂] (1 : FiniteAdeleRing (𝓞 F₂) F₂) := by
  subst h
  exact (Algebra.TensorProduct.comm F₁ (FiniteAdeleRing (𝓞 F₁) F₁) E).apply_symm_apply _

theorem tensCastR_comm_symm_one_tmul {F₁ F₂ : Subfield E} (h : F₁ = F₂) (c : FiniteAdeleRing (𝓞 F₁) F₁)
    (hc : ∀ v, c v ∈ v.adicCompletionIntegers F₁) :
    ∃ c' : FiniteAdeleRing (𝓞 F₂) F₂, (∀ v, c' v ∈ v.adicCompletionIntegers F₂) ∧
      GlobalTheory.StdFrame.tensCastR h ((Algebra.TensorProduct.comm F₁ (FiniteAdeleRing (𝓞 F₁) F₁) E).symm
        ((1 : E) ⊗ₜ[F₁] c)) = (1 : E) ⊗ₜ[F₂] c' := by
  subst h
  exact ⟨c, hc, (Algebra.TensorProduct.comm F₁ (FiniteAdeleRing (𝓞 F₁) F₁) E).apply_symm_apply _⟩

end Cast

def projE (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) :
    Formalism.IndefR.Lev.EAf D →+* s.v.adicCompletion (maximalRealSubfield D.host.E) :=
  s.proj.comp (GlobalTheory.FixedConj.adeleEquiv D hF).symm.toRingHom

theorem projE_apply (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E)
    (x : Formalism.IndefR.Lev.EAf D) :
    projE D hF s x = s.proj (GlobalTheory.StdFrame.tensCastR hF
      ((Algebra.TensorProduct.comm (↥D.host.F) (FiniteAdeleRing (𝓞 ↥D.host.F) ↥D.host.F) D.host.E).symm x)) := rfl

theorem projE_adeleEquiv (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E)
    (a : ReciprocityTheory.Aut.AL D.host.E) : projE D hF s (GlobalTheory.FixedConj.adeleEquiv D hF a) = s.proj a := by
  simp [projE]

theorem projE_tmul_one (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E)
    (y : D.host.E) : projE D hF s (y ⊗ₜ[↥D.host.F] (1 : Formalism.L2.Herm.Af ↥D.host.F)) = s.i y := by
  rw [projE_apply, tensCastR_comm_symm_tmul_one]
  simp [SplitPlace.proj, Algebra.TensorProduct.lift_tmul]

theorem projE_le_one (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E)
    (z : Formalism.IndefR.Lev.EAf D) (hz : z ∈ Formalism.L2.Herm.intAf (↥D.host.F) D.host.E) : Valued.v (projE D hF s z) ≤ 1 := by
  have hle : Formalism.L2.Herm.intAf (↥D.host.F) D.host.E ≤
      (s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)).toSubring.comap (projE D hF s) := by
    refine Subring.closure_le.2 ?_
    rintro x (⟨⟨_, y, rfl⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩)
    · show projE D hF s _ ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, projE_tmul_one]
      exact s.split_le_one y
    · show projE D hF s _ ∈ s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)
      obtain ⟨c', hc', e⟩ := tensCastR_comm_symm_one_tmul hF c hc
      rw [projE_apply, e]
      simp only [SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      exact hc' s.v
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hle hz)

theorem projE_lt_one (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E)
    (z : Formalism.L2.Herm.intAf (↥D.host.F) D.host.E) (hz : z ∈ Formalism.L2.DIV.idS (↥D.host.F) s.w.asIdeal) :
    Valued.v (projE D hF s (z : Formalism.IndefR.Lev.EAf D)) < 1 := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    rw [Formalism.L2.DIV.oToS_coe, projE_tmul_one]
    exact hy
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Subring.coe_add, map_add (f := _)]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hx hy)
  | smul c x _ hx =>
    rw [smul_eq_mul, Subring.coe_mul, map_mul, map_mul]
    calc Valued.v (projE D hF s (c : Formalism.IndefR.Lev.EAf D)) * Valued.v (projE D hF s (x : Formalism.IndefR.Lev.EAf D))
        ≤ 1 * Valued.v (projE D hF s (x : Formalism.IndefR.Lev.EAf D)) := by
          gcongr
          exact projE_le_one D hF s _ c.2
      _ < 1 := by rwa [one_mul]

theorem resS_adeleEquiv_eq_natCast : ∀ (D : D7) (hF : D.host.F = maximalRealSubfield D.host.E) (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (a : ReciprocityTheory.Aut.AL D.host.E) (ha : GlobalTheory.FixedConj.adeleEquiv D hF a ∈ Formalism.L2.Herm.intAf (↥D.host.F) D.host.E) (m : ℕ), a ∈ ReciprocityTheory.Aut.ALint D.host.E → Valued.v (s.proj a - (m : s.v.adicCompletion (maximalRealSubfield D.host.E))) < 1 → Formalism.L2.DIV.resS (↥D.host.F) s.w ⟨_, ha⟩ = (m : Formalism.L2.DIV.kP s.w) := by
  intro D hF s a ha m _hA hm
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (Formalism.L2.DIV.resS (↥D.host.F) s.w ⟨_, ha⟩)
  have e1 : Formalism.L2.DIV.cmpS (↥D.host.F) s.w.asIdeal (Formalism.L2.DIV.resS (↥D.host.F) s.w ⟨_, ha⟩) =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS (↥D.host.F) s.w.asIdeal) ⟨_, ha⟩ :=
    (RingEquiv.ofBijective (Formalism.L2.DIV.cmpS (↥D.host.F) s.w.asIdeal)
      (Formalism.L2.DIV.cmpS_bij (F := ↥D.host.F) s.w.asIdeal s.w.ne_bot)).apply_symm_apply _
  have e2 : Formalism.L2.DIV.cmpS (↥D.host.F) s.w.asIdeal (Ideal.Quotient.mk s.w.asIdeal b) =
      Ideal.Quotient.mk (Formalism.L2.DIV.idS (↥D.host.F) s.w.asIdeal) (Formalism.L2.DIV.oToS (↥D.host.F) D.host.E b) :=
    Ideal.quotientMap_mk
  have hmem : (⟨_, ha⟩ : Formalism.L2.Herm.intAf (↥D.host.F) D.host.E) - Formalism.L2.DIV.oToS (↥D.host.F) D.host.E b ∈
      Formalism.L2.DIV.idS (↥D.host.F) s.w.asIdeal := by
    refine Ideal.Quotient.eq.1 ?_
    exact e1.symm.trans ((congrArg (Formalism.L2.DIV.cmpS (↥D.host.F) s.w.asIdeal) hb.symm).trans e2)
  have h1 : Valued.v (s.proj a - s.i (algebraMap (𝓞 D.host.E) D.host.E b)) < 1 := by
    have := projE_lt_one D hF s _ hmem
    rwa [AddSubgroupClass.coe_sub, map_sub, Formalism.L2.DIV.oToS_coe, projE_tmul_one, projE_adeleEquiv] at this
  have h2 : b - (m : 𝓞 D.host.E) ∈ s.w.asIdeal := by
    show Valued.v (s.i ((b - (m : 𝓞 D.host.E) : 𝓞 D.host.E) : D.host.E)) < 1
    have e : s.i ((b - (m : 𝓞 D.host.E) : 𝓞 D.host.E) : D.host.E) =
        (s.proj a - (m : s.v.adicCompletion (maximalRealSubfield D.host.E))) -
          (s.proj a - s.i (algebraMap (𝓞 D.host.E) D.host.E b)) := by
      rw [RingOfIntegers.coe_eq_algebraMap, map_sub, map_sub, map_natCast, map_natCast]
      ring
    rw [e]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hm h1)
  rw [← hb, ← map_natCast (Ideal.Quotient.mk s.w.asIdeal) m, Ideal.Quotient.eq]
  exact h2

end GlobalTheory.SplitRes

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermMovesToBaseFramesUpToUnitriangular
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.MoveTerm

theorem term_moves_to_base : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ t₀ : TauC Y u u', t₀.toTerm.atPt w → ∃ (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' := by
  intro D X Y u u' _hS w F00 F'0 FP hZ _hG _hB t₀ ht
  obtain ⟨F', ⟨hP, hmk⟩, hGv, hCell⟩ := ht
  have hrow : IsRowLat D (X.Fu u) t₀.lam := (Y.rowsOK u).1 _ t₀.mem
  obtain ⟨hGF, hCF, -⟩ := Formalism.L2.SG.Closed.TermFun_holds D u u' (X.Fu u) t₀.lam hrow
  have hrel := (Formalism.L2.SG.Closed.TermEqIff_holds D u u' (X.Fu u) t₀.lam hrow _ _).1 hmk
  have hGt : Gval (lf D (X.Fu u)) t₀.frame ≠ 0 := by
    intro h
    apply hGv
    rw [hGF _ _ hrel]
    exact h
  have hCt := (hCF _ _ hrel w).1 hCell
  have hTu : ∀ v : D.what₂.Word, ((Tu D v : ℕ) : D.host.E) ≠ 0 := fun v =>
    Nat.cast_ne_zero.mpr (Formalism.L2.SG.GramJoint.Tu_pos D v).ne'
  obtain ⟨-, γ, hγ, ⟨A, hA, hAc⟩, ⟨A', hA', hAc'⟩⟩ :=
    _root_.GlobalTheory.LocOver.witt_frames_at_point D (lf D (X.Fu u)) F00 t₀.frame F'0 w (hTu u) (hTu u') hGt hCt hZ
  refine ⟨γ, A, A', hγ, ?_, ?_, fun b => hAc b, fun b => hAc' b⟩
  · exact fun i j => ⟨fun h => hA.1 i j h, fun h => h ▸ hA.2 i⟩
  · exact fun i j => ⟨fun h => hA'.1 i j h, fun h => h ▸ hA'.2 i⟩

end GlobalTheory.HL.MoveTerm
end
end

