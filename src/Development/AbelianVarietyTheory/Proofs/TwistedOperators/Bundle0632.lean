module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0464
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0472
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovesOfSelfDual
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0269
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0242
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2724
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0765
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddnessConditionHolds
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0625
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0611
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0628
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationDetStageVariablesEmbedGLEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2726
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilOver
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PadOneMemSecondBlockTriangular
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0627
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0493
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0537
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0542
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0621
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0622
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0610
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0442
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0609
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierCoeffScalarInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

namespace GlobalTheory.MovedKappaArith

theorem selfDualIntertwiner_baseVector_ne_zero {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} (hC : Crv D cc δ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) {N N' : ℕ} {e0 : VC D N N' → ℂ} (he : oddE0 D cc δ t0 N N' e0)
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hL : SD D L) (hL' : SD D L') :
    Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) L L') e0 ≠ 0 := by
  have s0 := GlobalTheory.MovedVacuum.sd_stdL D N
  have s0' := GlobalTheory.MovedVacuum.sd_stdL D N'
  have k0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') := Or.inr ⟨_, _, s0, s0', rfl⟩
  have k1 : KLat D (tor0 D cc δ) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) L L') := Or.inr ⟨_, _, hL, hL', rfl⟩
  have huni := GlobalTheory.theta_translation_intertwiner_unitary D cc δ hC N N' _ _ k0 k1
  intro h
  exact GlobalTheory.TrueTheta.ne_zero_of_like hC ht s0 s0' he.2.2.2.1
    (by rw [← (huni e0 he.1).2.2.2, h, GlobalTheory.VacuumScalar.Iop_zero])

theorem applyAt0_monomial (D : D7) {N N' : ℕ} (α : Mono D N N') (G : VC D N N' → ℂ) :
    Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial α 1) G
      = (α.prod fun _ n => (n.factorial : ℂ)) * Formalism.MainNotions.TaylorLogMetric.taylor D G α := by
  classical
  unfold Formalism.MainNotions.GL3Theta.applyAt0
  rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.sum_singleton, MvPolynomial.coeff_monomial,
    if_pos rfl, one_mul]

end GlobalTheory.MovedKappaArith

namespace GlobalTheory.MovedKappaArith

end GlobalTheory.MovedKappaArith

namespace GlobalTheory.MovedKappaArith

end GlobalTheory.MovedKappaArith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiStepLeftChangeMeasurePreserving
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

noncomputable section
namespace GlobalTheory.StepLeft
open Classical

theorem affine {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
    (g : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (x₀ : Matrix n n' k) (e : StepVar n c n' → k) :
    (fun a : StepVar n c n' => (g * stepPt x₀ e) a.1.1 a.1.2) =
      (stepLin n' g).mulVec e + fun a => (g * stepPt x₀ (0 : StepVar n c n' → k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) a.1.1 a.1.2 := by
  funext a
  obtain ⟨⟨r, s⟩, ha⟩ := a
  have h1 : (stepLin n' g).mulVec e ⟨(r, s), ha⟩ =
      ∑ t, g r t * (if h : (Free (c / 2 + 1) (t, s) ∨ Kept (t, s)) then e ⟨(t, s), h⟩ else 0) := by
    have h2 : (stepLin n' g).mulVec e ⟨(r, s), ha⟩ = ∑ b : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)),
        (if s = b.2 then g r b.1 else 0) * (if h : (Free (c / 2 + 1) b ∨ Kept b) then e ⟨b, h⟩ else 0) := by
      rw [← Fintype.sum_subtype_add_sum_subtype (fun b => Free (c / 2 + 1) b ∨ Kept b)]
      rw [Finset.sum_eq_zero (s := Finset.univ) (f := fun b : {b // ¬ (Free (c / 2 + 1) b ∨ Kept b)} => _)
        (fun b _ => by rw [dite_eq_right b.2, mul_zero]), add_zero]
      simp only [Matrix.mulVec, dotProduct, stepLin, of_apply]
      refine Finset.sum_congr rfl fun b _ => by rw [dite_eq_left b.2]
    rw [h2, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_eq_single s]
    · simp
    · intro s' _ hs
      simp [Ne.symm hs]
    · simp
  simp only [Pi.add_apply]
  rw [h1]
  simp only [stepPt, Matrix.mul_apply, Matrix.add_apply, of_apply, mul_add, Finset.sum_add_distrib, Pi.zero_apply,
    dite_eq_ite, ite_self, mul_zero, Finset.sum_const_zero, add_zero]
  ring

theorem det_unip {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
    (u : GL (n ⊕ Fin c) k) (hu : u ∈ symN k n c) : (stepLin n' u.val).det = 1 := by
  apply GlobalTheory.RootExSource.det_eq_one_of_unip (fun a : StepVar n c n' => GlobalTheory.DiagVol.ordL c a.1.1)
  intro a b hab
  have hu' : u.val a.1.1 b.1.1 = (1 : Matrix _ _ k) a.1.1 b.1.1 := GlobalTheory.DiagVol.symN_le_unipSub hu a.1.1 b.1.1 hab
  simp only [stepLin, of_apply]
  by_cases hab' : a = b
  · subst hab'; simp [hu']
  · rw [Matrix.one_apply_ne hab']
    split_ifs with h
    · rw [hu', Matrix.one_apply_ne]
      intro hr
      exact hab' (Subtype.ext (Prod.ext hr h))
    · rfl

theorem var_inl_iff {n n' : Type} {c : ℕ} (r t : n) (s : n' ⊕ Fin (c + 1)) :
    (Free (c / 2 + 1) ((Sum.inl r : n ⊕ Fin c), s) ∨ Kept ((Sum.inl r : n ⊕ Fin c), s)) ↔
      (Free (c / 2 + 1) ((Sum.inl t : n ⊕ Fin c), s) ∨ Kept ((Sum.inl t : n ⊕ Fin c), s)) := by
  rcases s with s | s <;> simp [Free, Kept]

theorem embX_apply_eq_zero {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] {c : ℕ} (κ : GL n k)
    (r t : n ⊕ Fin c) (s : n' ⊕ Fin (c + 1)) (hr : Free (c / 2 + 1) (r, s) ∨ Kept (r, s))
    (ht : ¬ (Free (c / 2 + 1) (t, s) ∨ Kept (t, s))) : (embX c κ).val r t = 0 := by
  change (fromBlocks κ.val 0 0 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r t = 0
  rcases r with r | r <;> rcases t with t | t
  · exact absurd ((var_inl_iff r t s).1 hr) ht
  · rfl
  · rfl
  · simp only [fromBlocks_apply₂₂]
    rw [Matrix.one_apply_ne]
    rintro rfl
    exact ht hr

theorem mul_embX {k : Type} [Field k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
    (κ : GL n k) (g : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) :
    stepLin n' ((embX c κ).val * g) = stepLin n' (embX c κ).val * stepLin n' g := by
  ext a b
  obtain ⟨⟨r, s⟩, ha⟩ := a
  obtain ⟨⟨r', s'⟩, hb⟩ := b
  set E := (embX c κ).val
  set F : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) → k := fun d =>
    (if s = d.2 then E r d.1 else 0) * (if d.2 = s' then g d.1 r' else 0) with hF
  have hF0 : ∀ d : {d : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // ¬ (Free (c / 2 + 1) d ∨ Kept d)}, F d.1 = 0 := by
    rintro ⟨⟨t, s''⟩, hd⟩
    by_cases h1 : s = s''
    · subst h1
      have hz : E r t = 0 := embX_apply_eq_zero κ r t s ha hd
      simp [hF, hz]
    · simp [hF, h1]
  have hR : (stepLin n' E * stepLin n' g) ⟨(r, s), ha⟩ ⟨(r', s'), hb⟩ = ∑ d, F d := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun d => Free (c / 2 + 1) d ∨ Kept d),
      Finset.sum_eq_zero (s := Finset.univ) (fun d _ => hF0 d), add_zero]
    simp only [Matrix.mul_apply, stepLin, of_apply, hF]
  rw [hR, Fintype.sum_prod_type, Finset.sum_comm, Finset.sum_eq_single s]
  · simp only [stepLin, of_apply, hF, Matrix.mul_apply]
    split_ifs with h
    · simp
    · simp [h]
  · intro s'' _ hs
    refine Finset.sum_eq_zero fun t _ => ?_
    simp [hF, Ne.symm hs]
  · simp

theorem mp_affine {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι k) (hM : valuation k M.det = 1) (b : ι → k) :
    MeasurePreserving (fun e => M.mulVec e + b) (Measure.pi fun _ : ι => ν) (Measure.pi fun _ : ι => ν) := by
  haveI := GlobalTheory.SplitWeil.secondCountable k
  have hU : IsUnit M.det := isUnit_iff_ne_zero.2 fun h => by rw [h, map_zero] at hM; exact zero_ne_one hM
  have h1 := GlobalTheory.WeilM.smul_map_mulVec_pi ν M hU.unit hU.unit_spec
  have h2 : distribHaarChar k hU.unit = 1 := by
    have := nabs_of_valuation_eq_one (k := k) (x := hU.unit) (by rw [hU.unit_spec]; exact hM)
    exact NNReal.coe_eq_one.1 this
  rw [h2, ENNReal.coe_one, one_smul] at h1
  have hm : Measurable M.mulVec := (continuous_const.matrix_mulVec continuous_id).measurable
  exact (measurePreserving_add_right (Measure.pi fun _ : ι => ν) b).comp ⟨hm, h1⟩

end GlobalTheory.StepLeft

namespace GlobalTheory.StepLeft
open Classical

theorem left_change : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} (ν : Measure k) [ν.IsAddHaarMeasure],
    ∀ v ∈ symN k n c, ∀ κ : GL n k, valuation k (gdet κ : k) = 1 → ∀ x₀ : Matrix n n' k,
      ∃ φ : (StepVar n c n' → k) ≃ᵐ (StepVar n c n' → k), MeasurePreserving φ (stepVol ν n c n') (stepVol ν n c n') ∧
        ∀ e, ((v * embX c κ)⁻¹).val * stepPt x₀ e = stepPt ((κ⁻¹).val * x₀) (φ e) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c ν _ v hv κ hκ x₀
  haveI := GlobalTheory.SplitWeil.secondCountable k
  set g := ((v * embX c κ)⁻¹).val with hgdef
  set M := stepLin n' g with hMdef
  set b : StepVar n c n' → k := fun a =>
    (g * stepPt x₀ (0 : StepVar n c n' → k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) a.1.1 a.1.2 with hb
  have hg : g = (embX c κ⁻¹).val * (v⁻¹).val := by
    rw [hgdef, _root_.mul_inv_rev, map_inv, Units.val_mul]
  have hκ' : valuation k (gdet κ⁻¹ : k) = 1 := by
    rw [gdet, map_inv, Units.val_inv_eq_inv_val, map_inv₀]
    exact (congrArg (·⁻¹) hκ).trans inv_one
  have hdet : valuation k M.det = 1 := by
    rw [hMdef, hg, mul_embX, det_mul, map_mul, det_unip _ (inv_mem hv), map_one, mul_one]
    exact _root_.GlobalTheory.StepLeft.valuation_det_stepLin_embX (n' := n') (c := c) κ⁻¹ hκ'
  have hM0 : IsUnit M.det := isUnit_iff_ne_zero.2 fun h => by rw [h, map_zero] at hdet; exact zero_ne_one hdet
  have hcont : ∀ (A : Matrix (StepVar n c n') (StepVar n c n') k) (w : StepVar n c n' → k),
      Continuous fun e : StepVar n c n' → k => A.mulVec e + w := fun A w =>
    (continuous_const.matrix_mulVec continuous_id).add continuous_const
  let φ : (StepVar n c n' → k) ≃ᵐ (StepVar n c n' → k) :=
    { toFun := fun e => M.mulVec e + b
      invFun := fun e => M⁻¹.mulVec e + M⁻¹.mulVec (-b)
      left_inv := fun e => by
        simp only [mulVec_add, mulVec_mulVec, nonsing_inv_mul _ hM0, one_mulVec, mulVec_neg, add_neg_cancel_right]
      right_inv := fun e => by
        simp only [mulVec_add, mulVec_mulVec, mul_nonsing_inv _ hM0, one_mulVec, mulVec_neg, neg_add_cancel_right]
      measurable_toFun := (hcont M b).measurable
      measurable_invFun := (hcont M⁻¹ _).measurable }
  refine ⟨φ, mp_affine ν M hdet b, fun e => ?_⟩
  change g * stepPt x₀ e = stepPt ((κ⁻¹).val * x₀) (M.mulVec e + b)
  rw [hMdef, hb, ← affine]
  exact _root_.GlobalTheory.StepLeft.inv_mul_stepPt_shape v hv κ x₀ e

end GlobalTheory.StepLeft

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridFirstColumnStepIsSchwartzBruhatHalf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FlipTop

open GlobalTheory.FunObj.Comparison₂

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}


open Classical in
theorem stepFn_congr_red (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) (t : T) {j : ℕ} (hj : j < D.R.m) {w : Pl D.host.E}
    (hw : w ∈ topPl L t) {a b : ℕ} (ha : a = D.R.r + j * D.R.t) (hb : b = D.R.r + (j + 1) * D.R.t)
    (N N' : Matrix (Fin b) (Fin a) (OA D)) (h : N.map (resS D.host.F w) = N'.map (resS D.host.F w)) :
    stepFn L t w j ((N.map (cptO w)).submatrix (ixOf G t w hb) (ixOf G t w ha)) =
      stepFn L t w j ((N'.map (cptO w)).submatrix (ixOf G t w hb) (ixOf G t w ha)) := by
  by_cases hP : w ∈ L.Pg
  · have hr : D.R.r ≤ a := ha ▸ Nat.le_add_right _ _
    rw [stepFn_of_mem_Pg t w hP]
    by_cases H : LowZero a (N.map (resS D.host.F w)) ∧ ∃ g, TopCond D.R.t hr (N.map (resS D.host.F w)) g
    · obtain ⟨h0, g, hg⟩ := H
      have h0' : LowZero a (N'.map (resS D.host.F w)) := by rw [← h]; exact h0
      have hg' : TopCond D.R.t hr (N'.map (resS D.host.F w)) g := by rw [← h]; exact hg
      have e1 := iterPhi_eq (isTame_muBase (L := L) w) (isRed w) (isIx_ixOf G t w ha) (isIx_ixOf G t w hb) hr (χ := fun c => L.chi c w)
          (fun c hc => compat_chi w hL hP (hc.trans_lt hj)) N h0 hg
      have e2 := iterPhi_eq (isTame_muBase (L := L) w) (isRed w) (isIx_ixOf G t w ha) (isIx_ixOf G t w hb) hr (χ := fun c => L.chi c w)
          (fun c hc => compat_chi w hL hP (hc.trans_lt hj)) N' h0' hg'
      exact e1.trans e2.symm
    · have H' : ¬ (LowZero a (N'.map (resS D.host.F w)) ∧ ∃ g, TopCond D.R.t hr (N'.map (resS D.host.F w)) g) := by rw [← h]; exact H
      have e1 := not_ne_iff.1 (mt (iterPhi_ne_zero_iff (isTame_muBase (L := L) w) (isRed w) (isIx_ixOf G t w ha) (isIx_ixOf G t w hb) hr N).1 H)
      have e2 := not_ne_iff.1 (mt (iterPhi_ne_zero_iff (isTame_muBase (L := L) w) (isRed w) (isIx_ixOf G t w ha) (isIx_ixOf G t w hb) hr N').1 H')
      exact e1.trans e2.symm
  · have hQ : w ∈ L.Q t := by
      unfold topPl at hw
      exact (Finset.mem_union.1 hw).resolve_left hP
    have e1 := stepFn_eq_of_mem_Q G t w hL hQ ha hb N
    have e2 := stepFn_eq_of_mem_Q G t w hL hQ ha hb N'
    refine e1.trans (Eq.trans ?_ e2.symm)
    exact congrArg (fun y => if H : LowZero D.R.r y ∧ IsUnit (topL D.R.r y).det then (L.xiR t w H.2.unit : ℂ) else 0) h


set_option maxHeartbeats 1000000 in
theorem isSBHalf_topFn : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (B : Frames G) {μ₀ : T},
    L.Is μ₀ → ∀ (t : T) {e : AE D}, IsIdemSum e (GlobalTheory.FlipTop.topPl L t) → ∀ (j : ℕ) (hj : j < D.R.m),
    IsSBHalf e (latO (G.pS (.mu t 0 j)) (G.pT (.mu t 0 j)) (G.latS (.mu t 0 j) : Set _) (G.latT (.mu t 0 j) : Set _)
      fun _ => True) (GlobalTheory.FlipTop.topFn B t e j (GlobalTheory.FlipTop.rank_col G hj.le) (GlobalTheory.FlipTop.rank_col G hj)) := by
  intro D T L sc G B μ₀ hL t e he j hj
  classical
  have hFS : IsFrame (B.β 0 j) (G.Λ (.grid 0 j)) := B.isFrame_β hL (Nat.zero_le _) hj.le
  have hFT : IsFrame (B.β 0 (j + 1)) (G.Λ (.grid 0 (j + 1))) := B.isFrame_β hL (Nat.zero_le _) hj
  obtain ⟨a, ha, h1⟩ := WeilOver.exists_hom_le (S := G.V (.grid 0 j)) (T := G.V (.grid 0 (j + 1)))
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice _ _ (node_isV G hL (X := .grid 0 j) ⟨Nat.zero_le _, hj.le⟩).sd)
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice _ _ (node_isV G hL (X := .grid 0 (j + 1)) ⟨Nat.zero_le _, hj⟩).sd)
  obtain ⟨b, hb, h2⟩ := WeilOver.exists_le_hom (S := G.V (.grid 0 j)) (T := G.V (.grid 0 (j + 1)))
    (GlobalTheory.DiagLiftFix.isLattice_of_isFrame hFS) (GlobalTheory.DiagLiftFix.isLattice_of_isFrame hFT)
  obtain ⟨e0, -, -⟩ := cpt_idemSum he

  set 𝔪 : Ideal (𝓞 D.host.E) := ∏ w ∈ topPl L t, w.asIdeal ^ 1 with h𝔪
  have hN : 0 < Ideal.absNorm 𝔪 :=
    Nat.pos_of_ne_zero fun h => CosSB.prod_pow_ne_bot (topPl L t) 1 (Ideal.absNorm_eq_zero_iff.1 h)
  have hle : ∀ w ∈ topPl L t, 𝔪 ≤ w.asIdeal ^ 1 := fun w hw =>
    Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun w : Pl D.host.E => w.asIdeal ^ 1) hw)
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = a * (b * Ideal.absNorm 𝔪) := ⟨_, rfl⟩
  refine ⟨fun x hx => ?_, K, by rw [hK]; positivity, fun u hu hh x => ?_, fun x hx => ?_⟩
  · by_contra h
    exact hx (by unfold GlobalTheory.FlipTop.topFn; rw [if_neg fun H => h H.1])
  · have hk : K • u ∈ hatMx (𝔪 • homLat (G.Λ (.grid 0 j)) (G.Λ (.grid 0 (j + 1)))) := by
      have := nsmul_mem (CosSB.nsmul_mem_hatMx h2 𝔪 hu) a
      rwa [smul_smul, ← hK] at this
    have hk2 := ((mem_hatMx_iff hFS hFT 𝔪 _).1 hk).2
    have hXYZ : fr (B.β 0 (j + 1)) (B.β 0 j) ((x + K • u).map (toEAf D)) =
        fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D)) + fr (B.β 0 (j + 1)) (B.β 0 j) ((K • u).map (toEAf D)) := by
      have hm : (x + K • u).map (toEAf D) = x.map (toEAf D) + (K • u).map (toEAf D) := by
        ext i l
        exact (toEAf D).map_add _ _
      rw [hm, fr_add]
    have hZ : ∀ i l, fr (B.β 0 (j + 1)) (B.β 0 j) ((K • u).map (toEAf D)) i l ∈ OA D := fun i l => by
      obtain ⟨s, -, hs⟩ := hk2 i l
      rw [← hs]
      exact s.2
    have hint : IsIntM (fr (B.β 0 (j + 1)) (B.β 0 j) ((x + K • u).map (toEAf D))) ↔
        IsIntM (fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D))) := by
      refine forall₂_congr fun i l => ?_
      rw [hXYZ, Matrix.add_apply]
      exact ⟨fun h => by simpa using sub_mem h (hZ i l), fun h => add_mem h (hZ i l)⟩
    unfold GlobalTheory.FlipTop.topFn
    split_ifs with H1 H2 H2
    · refine Finset.prod_congr rfl fun w hw => ?_
      let NX : Matrix (Fin (G.V (.grid 0 (j + 1))).rank) (Fin (G.V (.grid 0 j)).rank) (OA D) :=
        fun i l => ⟨_, H1.2 i l⟩
      let NY : Matrix (Fin (G.V (.grid 0 (j + 1))).rank) (Fin (G.V (.grid 0 j)).rank) (OA D) :=
        fun i l => ⟨_, H2.2 i l⟩
      have eX : (fr (B.β 0 (j + 1)) (B.β 0 j) ((x + K • u).map (toEAf D))).map (cpt (D := D) w) = NX.map (cptO w) :=
        Matrix.ext fun i l => (cptO_apply w (NX i l)).symm
      have eY : (fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D))).map (cpt (D := D) w) = NY.map (cptO w) :=
        Matrix.ext fun i l => (cptO_apply w (NY i l)).symm
      rw [eX, eY]
      refine stepFn_congr_red G hL t hj hw _ _ NX NY (Matrix.ext fun i l => ?_)
      rw [Matrix.map_apply, Matrix.map_apply, ← sub_eq_zero, ← map_sub, (isRed w).ker, cptO_apply]
      obtain ⟨s, hs, hs'⟩ := hk2 i l
      have e3 : ((NX i l - NY i l : OA D) : EAf D) = s.1 := by
        rw [hs', AddSubgroupClass.coe_sub]
        change fr (B.β 0 (j + 1)) (B.β 0 j) ((x + K • u).map (toEAf D)) i l -
          fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D)) i l = _
        rw [hXYZ, Matrix.add_apply, add_sub_cancel_left]
      rw [e3]
      exact (vEq w).lt_one_iff_lt_one.2 ((v_lt_one_iff _).2 (v_le_of_mem_idS (hle w hw) hs))
    · exact absurd ⟨(CosSB.isHalf_add_nsmul K hh).1 H1.1, hint.1 H1.2⟩ H2
    · exact absurd ⟨(CosSB.isHalf_add_nsmul K hh).2 H2.1, hint.2 H2.2⟩ H1
    · rfl
  · obtain ⟨hth, hti⟩ : IsHalf e x ∧ IsIntM (fr (B.β 0 (j + 1)) (B.β 0 j) (x.map (toEAf D))) := by
      by_contra h
      exact hx (by unfold GlobalTheory.FlipTop.topFn; rw [if_neg h])
    have hmem : x ∈ hatMx ((⊤ : Ideal (𝓞 D.host.E)) • homLat (G.Λ (.grid 0 j)) (G.Λ (.grid 0 (j + 1)))) := by
      refine (mem_hatMx_iff hFS hFT ⊤ _).2 ⟨fun i l => ?_, fun i l => ⟨⟨_, hti i l⟩, ?_, rfl⟩⟩
      · rw [← hth i l, map_mul, e0, zero_mul]
      · rw [idS, Ideal.map_top]
        exact Submodule.mem_top
    have := nsmul_mem (CosSB.nsmul_mem_latO h1 ⊤ hmem) (b * Ideal.absNorm 𝔪)
    rwa [smul_smul, mul_comm (b * Ideal.absNorm 𝔪) a, ← hK] at this

end GlobalTheory.FlipTop

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridLatticesCompactSelfDualSplitting
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.GridLat

theorem lattices_grid : OnStd fun {D} _ _ {sc} {G} W F => (∀ i, i < D.R.m → FinLat (latRow G i) ∧ FinLat (latCore G i) ∧ FinLat (latBig G i) ∧ IsSelfDualC (G.V (.grid i 0)) (idLat (shiftId G) (G.Λ (.grid i 0)))) ∧ (∀ ρ h, IsSelfDualC (F.V₀ ρ) (lat0 F ρ h) ∧ (∀ v, MonoAt (F.dB ρ h) (G.Λ (.grid (2 * ρ + 2) 0)) (lat0 F ρ h) v ∧ MonoAt (F.dJ ρ h) (G.Λ (.grid (2 * ρ + 1) 0)) (G.Λ (.core (2 * ρ + 1))) v) ∧ IsSelfDualC (negSp F.Lz) (idLat (G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) ∧ ∀ v, OrthAt (F.oB ρ h) (lat0 F ρ h) (G.Λ (.core (2 * ρ + 2))) (idLat (G.pl.stA sc ^ (ρ + 1) * (G.pl.stAbar sc ^ (ρ + 1))⁻¹) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) v) ∧ ∀ ρ, IsSelfDualC (negSp F.Lz) (idLat (G.pl.stA sc ^ ρ * (G.pl.stAbar sc ^ ρ)⁻¹ * shiftId G) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) := by
  intro D hq T L μ0 hL sc G W M hM F hF
  have sdG : ∀ i, i ≤ D.R.m → IsSelfDualC (G.V (.grid i 0)) (G.Λ (.grid i 0)) := by
    intro i hi
    cases i with
    | zero =>
      obtain ⟨c, hc⟩ := (hL.βY 0 (by have := D.R.two_le_m; omega) : ∃ c, _)
      exact Formalism.IndefR.Eqv.KerDiag.isSelfDualC_of_base hc
    | succ i => exact (G.sp.V_is (i + 1) 0 (by omega) hi (by omega)).sd
  have sdP : ∀ i, i ≤ D.R.m → IsSelfDualC (G.V (.core i)) (G.Λ (.core i)) := fun i hi => (G.sp.P_is i hi).sd
  have sdShift : ∀ i, i ≤ D.R.m → IsSelfDualC (G.V (.grid i 0)) (idLat (shiftId G) (G.Λ (.grid i 0))) := by
    intro i hi
    obtain ⟨I', h1, h2⟩ := _root_.GlobalTheory.ConjIdeal.stA_modul_conj_inv G.pl sc 0 1
    simp only [pow_zero, pow_one, inv_one, one_mul] at h1 h2
    exact _root_.GlobalTheory.idLat_isSelfDualC _ _ _ I' (sdG i hi) h1 h2
  have sdLine : ∀ a b : ℕ, IsSelfDualC (negSp F.Lz) (idLat (G.pl.stA sc ^ a * (G.pl.stAbar sc ^ a)⁻¹ *
      (((G.pl.modul sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b *
        (((G.pl.modulBar sc : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ^ b)⁻¹))
      (Submodule.span (𝓞 D.host.E) {F.ζ 0})) := by
    intro a b
    obtain ⟨I', h1, h2⟩ := _root_.GlobalTheory.ConjIdeal.stA_modul_conj_inv G.pl sc a b
    exact _root_.GlobalTheory.idLat_isSelfDualC _ _ _ I' (_root_.GlobalTheory.AscFin.isSelfDualC_line F hF) h1 h2
  refine ⟨fun i hi => ⟨_root_.GlobalTheory.AscFin.DepLat.finLat_depLat G (.chi i 0) (isSelfDualC_neg (sdG (i + 1) hi)) (sdG i hi.le),
    _root_.GlobalTheory.AscFin.DepLat.finLat_depLat G (.core i) (isSelfDualC_neg (sdP (i + 1) hi)) (sdP i hi.le),
    _root_.GlobalTheory.AscFin.finLat_latO_selfDual _ _ _ _ (sdG (i + 1) hi) (sdShift i hi.le), sdShift i hi.le⟩,
    fun ρ h => ⟨GlobalTheory.T.isSelfDual_besselCoreVertexLattice F hF ρ h, fun v => ⟨_root_.GlobalTheory.MonoBes.monoAt_bes F hF ρ h v, _root_.GlobalTheory.AscFin.MonoJac.monoAt_jac F hF ρ h v⟩, ?_, fun v => _root_.GlobalTheory.AscFin.CoreSum.besselCoreVertexLattice_splitsAlongOrthDecomposition F hF ρ h v⟩,
    fun ρ => ?_⟩
  · have := sdLine (ρ + 1) 0
    simpa only [pow_zero, inv_one, mul_one] using this
  · have := sdLine ρ 1
    simp only [pow_one] at this
    exact this

end GlobalTheory.AscFin.GridLat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridTupleHeckeCharacterDetIdeleEqProdLocal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv

namespace GlobalTheory.TopLevelInv

theorem chrEq_mu_succ_succ : ∀ {D : D7} {T : Type} {L : LevCh D T} {μ₀ : T}, L.Is μ₀ → ∀ (t : T) (j : ℕ), j + 1 < D.R.m → ChrEq (L.mu t (j + 1 + 1)) (muBase L (j + 1 + 1) * L.xiH t) ∧ ∀ P, (muBase L (j + 1 + 1) * L.xiH t).TameAt P := by
  intro D T L μ₀ hL t j hj
  have hm : ChrEq (L.mu0 (j + 1 + 1)) (muBase L (j + 1 + 1)) := by
    have := hL.mu0 ⟨j + 1, hj⟩
    simpa [muBase, hj] using this
  refine ⟨GlobalTheory.TowerCharRead.chrEq_mul hm (hL.xi t), fun P => ?_⟩
  have h1 : (muBase L (j + 1 + 1)).TameAt P := by
    rw [muBase, dite_eq_left hj]; exact (L.C.isMu0 ⟨j + 1, hj⟩).tame P
  exact Formalism.L2.Host.HChar.LevelLe.mul h1 (hL.xi_tame t P)

theorem mu_detAt_eq_prod_loc : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {μ₀ : T}, L.Is μ₀ → t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} (j : ℕ) (hj : j + 1 < D.R.m) (k : FinPt G (.top (j + 1))),
    finG (G.V (.top (j + 1))) k ∈ S.levTop t Φ β (j + 1) hj → ∀ (e : AE D) (he : IsIdemSum e (locPl G t)),
    ((L.mu t (j + 1 + 1) (GlobalTheory.VecInv.detAt e (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he).idem (G.V (.top (j + 1)))
      (cutPart (e + cA D e) (G.V (.top (j + 1))) ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1))))))) : Circle) : ℂ) =
      ∏ w : locPl G t, (((locGrid G t w).mu (j + 1 + 1) (gdet (kapAt S t j hj k w)) : ℂˣ) : ℂ) := by
  intro D T L sc G W U S t μ₀ hL ht Φ β j hj k hk e he
  obtain ⟨hχ, htame⟩ := chrEq_mu_succ_succ hL t j hj
  obtain ⟨hinf, hin, hout⟩ := GlobalTheory.T.determinantIdeleAtIdempotent_idempotentPart_components he (G.V (.top (j + 1)))
    ((((S.N.u (.top (j + 1)))⁻¹ * k * S.N.u (.top (j + 1)) : FinPt G (.top (j + 1))) : GA D (G.V (.top (j + 1)))))
  rw [_root_.GlobalTheory.TameCharProd.char_eq_prod_loc_of_tame hχ (locPl G t) (fun P _ => htame P) (fun P => gdet (kapAt S t j hj k P)) _ hinf
    (fun P hP => (hin P hP).trans (_root_.GlobalTheory.TopLevelInv.det_mt_conj_eq_gdet_kapAt S t j hj k _ P)) hout]
  rw [← Finset.prod_coe_sort]
  rfl

end GlobalTheory.TopLevelInv
end

