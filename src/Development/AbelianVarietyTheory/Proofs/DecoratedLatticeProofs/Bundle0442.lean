module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0534
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0362
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0180
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsDoubleLiftPeriodValue
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0264
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0416
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0407
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0267
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0398
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedConjugatePlaceInverseUniformizerValue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SplitUnr

open GlobalTheory.LFun

theorem unrAt_and_val_inv : ∀ (D : D7) (χ : (AE D)ˣ →* Circle), ResEta D χ 0 → ∀ w w' : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F) → w ≠ w' → GlobalTheory.LFun.UnrAt (F := D.host.F) χ w → GlobalTheory.LFun.UnrAt (F := D.host.F) χ w' ∧ GlobalTheory.LFun.val (F := D.host.F) χ w' = (GlobalTheory.LFun.val (F := D.host.F) χ w)⁻¹ := by
  intro D χ hr w w' hww hne hu
  have hE := GlobalTheory.AdelicU.isCMExt_host D
  have hres := (GlobalTheory.LFun.resEta_iff χ 0).1 hr
  obtain ⟨⟨η, hη⟩, hμ⟩ := hres
  generalize hv : w'.under (𝓞 D.host.F) = v at hww
  obtain ⟨τ', hτ', -⟩ := GlobalTheory.AdelicU.existsUnique_splitPrime_eq hE hne.symm hv hww
  have key : ∀ a : (Fv D.host.F v)ˣ, locChar χ w' (Units.map (complMap hv).toMonoidHom a) =
      (locChar χ w (Units.map (complMap hww).toMonoidHom a))⁻¹ := by
    intro a
    have e : locIdele D.host.F w (Units.map (complMap hww).toMonoidHom a) *
        locIdele D.host.F w' (Units.map (complMap hv).toMonoidHom a) =
        ideleMap D.host.F D.host.E (Units.map (Algebra.norm (AF D.host.F) : AF D.host.F ⊗[D.host.F] D.host.E →* AF D.host.F)
          (locIdele D.host.F w (Units.map (complMap hww).toMonoidHom a))) :=
      Units.ext (by
        rw [Units.val_mul, ← GlobalTheory.LFun.SplitVal.sigR_locIdele hE hww hv hne a, ← GlobalTheory.Doubling.algebraMap_norm_eq hE]
        rfl)
    have k := congrArg χ e
    rw [hμ η hη, pow_zero, map_mul] at k
    have k2 := (map_mul Circle.toUnits _ _).symm.trans ((congrArg Circle.toUnits k).trans (map_one _))
    exact eq_inv_of_mul_eq_one_right k2
  have hunr : UnrAt χ w' := by
    intro x hx
    set a : (Fv D.host.F v)ˣ := Units.map (ConjPlace.complEquiv hE hv hτ').symm.toRingHom.toMonoidHom x with ha
    have hax : Units.map (complMap hv).toMonoidHom a = x :=
      Units.ext ((ConjPlace.complEquiv hE hv hτ').apply_symm_apply (x : _))
    rw [← hax, key, hu _ ?_, inv_one]
    obtain ⟨τ, hτ, -⟩ := GlobalTheory.AdelicU.existsUnique_splitPrime_eq hE hne hww hv
    unfold Formalism.L2.Host.IsUnitAt at hx ⊢
    have h1 : Valued.v ((complMap hv) (a : Fv D.host.F v)) = 1 := by
      rw [show (complMap hv) (a : Fv D.host.F v) = (x : _) from congrArg Units.val hax]; exact hx
    rw [ConjPlace.valued_complMap hE hv hτ'] at h1
    change Valued.v (complMap hww (a : Fv D.host.F v)) = 1
    rw [ConjPlace.valued_complMap hE hww hτ, h1]
  exact ⟨hunr, eq_inv_of_mul_eq_one_right (GlobalTheory.LFun.SplitVal.val_mul_val_eq_one D.host.F D.host.E _ hE χ 0 ((GlobalTheory.LFun.resEta_iff χ 0).1 hr) w w' (hww.trans hv.symm) hne hu hunr)⟩

end GlobalTheory.SplitUnr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorLastDefiniteLocalBiModelSecond
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LastOmb

theorem isComp_inv {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ} (Q : QStep S) :
    (ofSplit Q.q).IsComp S.χ₂ Q.μ₂⁻¹ := by
  intro t a ha
  have := Q.comp₂ t a ha
  rw [MonoidHom.inv_apply] at this
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, this, Circle.coe_inv, inv_inv]

theorem isLoc_one {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ} (Q : QStep S) :
    (ofSplit Q.q).IsLoc Q.F.F₁ (1 : GA D S.J.W₀) (1 : GL Q.n₁ Q.k) := by
  refine ⟨?_, ?_⟩
  · intro i j
    simp [GlobalTheory.MixModel.mt_one]
  · rw [GlobalTheory.MixModel.mt_one, Units.val_one, Matrix.mul_one, Q.F.F₁.βγ, Matrix.map_one _ (map_zero _) (map_one _)]

theorem actO_one_of_away {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ} (Q : QStep S) {g : GL Q.n₂ Q.k}
    {a₀ : GA D S.B'.A} (hloc : (ofSplit Q.q).IsLoc Q.F.F₂ a₀ g) (y : WO S.J.W₀ S.B'.A)
    (hy' : IsHalf (1 - (Q.q.e + cA D Q.q.e)) y) : actO S.J.W₀ S.B'.A 1 a₀ y = y := by
  have hsupp := GlobalTheory.LocGrp.suppAt_iff.1 hloc.1
  have he := Q.q.split
  set f : AE D := Q.q.e + cA D Q.q.e with hf
  have hce : cA D Q.q.e * cA D Q.q.e = cA D Q.q.e := by rw [← map_mul, he.1]
  have hff : f * (1 - f) = 0 := by
    rw [hf]; linear_combination (-1 : AE D) * he.1 - hce - 2 * he.2.1
  have hfy : f • y = 0 := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    rw [← hy' i j, ← mul_assoc, hff, zero_mul]
  have hz : HMul.hMul (Formalism.L2.Theta.mt S.B'.A a₀ - 1) (show Matrix (Fin S.B'.A.rank) (Fin S.J.W₀.rank) (AE D) from y) = 0 := by
    rw [← hsupp, Matrix.smul_mul, ← Matrix.mul_smul]
    have h0 : ((ofSplit Q.q).e + cA D (ofSplit Q.q).e) • (show Matrix (Fin S.B'.A.rank) (Fin S.J.W₀.rank) (AE D) from y) = 0 := hfy
    rw [h0, Matrix.mul_zero]
  simp only [actO, inv_one, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hz
  exact hz

theorem biComb_eq_sum {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c₁ : WO A S →₀ ℂ) (c₂ : WO S A' →₀ ℂ)
    (C : WO A S → WO S A' → ℂ) (u : WO A S) :
    biComb ψ A S A' c₁ c₂ C u =
      ∑ x ∈ c₁.support, (c₁ x * ψ (symplOH A S u x)) • GlobalTheory.SeeSaw.comb ψ S A' c₂ (C (u + x)) := by
  funext v
  simp only [biComb, GlobalTheory.SeeSaw.comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

theorem weil_last_local : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₂ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ (g : GL Q.n₂ Q.k) (a₀ : GA D S.B'.A), (ofSplit Q.q).IsLoc Q.F.F₂ a₀ g → ∀ (Ξ₁ : SB (Matrix Q.n₁ Q.n₀ Q.k)) (Ξ₂ Ξ₂' : SB (Matrix Q.n₂ Q.n₁ Q.k)), Ξ₂'.1 = om Q.μ₂ 1 g Ξ₂.1 → ∀ u, S.omb (1, a₀) (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u) = biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂')) u := by
  intro D ψ σ S Q c₁ c₂ hAway Λ hbi g a₀ hloc Ξ₁ Ξ₂ Ξ₂' hΞ u
  have hcomm : ∀ G, IsThetaFunO ψ S.J.W₀ S.B'.A G →
      S.omb (1, a₀) (GlobalTheory.SeeSaw.comb ψ S.J.W₀ S.B'.A c₂ G) = GlobalTheory.SeeSaw.comb ψ S.J.W₀ S.B'.A c₂ (S.omb (1, a₀) G) := by
    intro G hG
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [GlobalTheory.SeeSaw.comb, map_sum, map_smul]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [S.weilb.om_heis 1 a₀ y G hG, actO_one_of_away Q hloc y (hAway y hy)]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [biComb_eq_sum, biComb_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_smul]
  obtain ⟨T₂, hT₂, hΛ⟩ := hbi.2 Ξ₁ (u + x)
  have e1 : Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) (u + x) = T₂ Ξ₂ :=
    funext fun v => hΛ Ξ₂ _ (fun q => GlobalTheory.LocFlat.CFac.prodSB_apply _ _ _) v
  have e2 : Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂') (u + x) = T₂ Ξ₂' :=
    funext fun v => hΛ Ξ₂' _ (fun q => GlobalTheory.LocFlat.CFac.prodSB_apply _ _ _) v
  have e3 : S.omb (1, a₀) (T₂ Ξ₂) = T₂ Ξ₂' := by
    refine GlobalTheory.LocOm.omLoc D Q.k (ofSplit Q.q) ψ S.J.W₀ S.B'.A S.χ₂ S.χ₂ S.omb S.weilb Q.μ₂⁻¹ Q.μ₂⁻¹ (isComp_inv Q)
      (isComp_inv Q) Q.n₂ Q.n₁ Q.F.F₁ Q.F.F₂ T₂ hT₂ 1 1 a₀ g (isLoc_one Q) hloc Ξ₂ Ξ₂' ?_
    rw [hΞ, inv_inv]
    simp
  rw [e1, e2, hcomm _ (hT₂.theta _), e3]

end GlobalTheory.LastOmb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeylFormulaStandardUnitaryGroupWeilDatum
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.WeylStd

theorem trA_incA_mul (D : D7) (lam : D.host.F) (t : AE D) :
    trA (incA D (algebraMap D.host.F D.host.E lam) * t) = algebraMap D.host.F (AF D.host.F) lam * trA t := by
  have h : incA D (algebraMap D.host.F D.host.E lam) = algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) lam) := by
    show Algebra.TensorProduct.includeRight (algebraMap D.host.F D.host.E lam) = _
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply D.host.F (AF D.host.F) (AE D)]
  rw [h, ← Algebra.smul_def]
  show Algebra.trace (AF D.host.F) (AE D) (_ • t) = _
  rw [LinearMap.map_smul, smul_eq_mul]

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ θ : InfFam D, IsInfFam θ → ∀ μ : D.host.E, IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ omS : G D A.rank →* Module.End ℂ (schwartzA θ B.rank A.rank), IsTransport ψ θ A B ν 𝓨 omh κ omS → ∀ lam : D.host.F, algebraMap D.host.F D.host.E lam = -D.host.xi0 / μ → ∀ g : G D A.rank, mat g = blk4 0 1 (-1) 0 → ∀ Φ x, (omS g Φ).1 x = ∫ y, Φ.1 y * shift ψ lam (trA (Matrix.trace (GlobalTheory.StdUnn.inner B x y))) ∂ν := by
  intro D ψ A B χB omh hW ν 𝓨 hν θ hθ μ hμ κ hκ omS hT lam hlam g hg Φ x
  obtain ⟨f, hf, hΦ⟩ := (_root_.GlobalTheory.SchSchwartzAll.schSchwartz D ψ hW.std θ hθ A B ν 𝓨 hν).2.1 Φ.1 Φ.2
  have hw : mat (κ (κ.symm g)) = blk4 0 1 (-1) 0 := by rw [MulEquiv.apply_symm_apply]; exact hg
  obtain ⟨hW1, h1, h2⟩ := _root_.GlobalTheory.StdUnn.chart_weyl D A μ hμ κ hκ (κ.symm g) hw
  have hg' := hT (κ.symm g) f hf Φ hΦ.symm
  rw [MulEquiv.apply_symm_apply] at hg'
  rw [hg', _root_.GlobalTheory.StdUnn.WeylFourier.sch_weyl D ψ A B χB omh hW ν 𝓨 hν μ hμ (κ.symm g) hW1 h1 h2 f hf x, ← hΦ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [shift, AddChar.mulShift_apply]
  rw [← hlam, trA_incA_mul]

end GlobalTheory.StdUnn.WeylStd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittProjAnisotropicMulVecLeviEq
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.MonoIdele

variable {D : D7} {S S₀ : HSp D} {ρ : ℕ}

def diagU (b : Fin ρ → (AE D)ˣ) : GL (Fin ρ) (AE D) :=
  ⟨Matrix.diagonal fun i => (b i : AE D), Matrix.diagonal fun i => (((b i)⁻¹ : (AE D)ˣ) : AE D),
    by rw [Matrix.diagonal_mul_diagonal]; simp, by rw [Matrix.diagonal_mul_diagonal]; simp⟩

theorem diagU_inv_val (b : Fin ρ → (AE D)ˣ) :
    ((diagU b)⁻¹).1 = Matrix.diagonal fun i => (((b i)⁻¹ : (AE D)ˣ) : AE D) := rfl

theorem diagU_inv_inv_val (b : Fin ρ → (AE D)ˣ) :
    (((diagU b)⁻¹)⁻¹).1 = Matrix.diagonal fun i => (b i : AE D) := by rw [inv_inv]; rfl

theorem mulVec_supp {m n : ℕ} (A : Matrix (Fin m) (Fin n) (AE D)) {P : Pl D → Prop} {z : Fin n → AE D}
    (hz : ∀ j, z j ∈ idAt D P) (k : Fin m) : (A *ᵥ z) k ∈ idAt D P := by
  simp only [Matrix.mulVec, dotProduct]
  exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hz j)

theorem mt_mulVec_inv (g : GA D S) (z : Fin S.rank → AE D) : mt S g *ᵥ (mt S g⁻¹ *ᵥ z) = z := by
  rw [Matrix.mulVec_mulVec, show mt S g * mt S g⁻¹ = mt S (g * g⁻¹) from rfl, mul_inv_cancel]
  exact Matrix.one_mulVec z

theorem mem_iff_of_moves {L M : Lat S} {v : Pl D} {g : GA D S} (hm : Moves S g L M (· = v)) (z : Fin S.rank → AE D) :
    z ∈ latV S M (· = v) ↔ mt S g⁻¹ *ᵥ z ∈ latV S L (· = v) := by
  constructor
  · intro hz
    have hs : ∀ k, z k ∈ idAt D (· = v) := fun k => GlobalTheory.FinPl.FrameLat.latV_supp hz k
    rw [hm _ (fun k => mulVec_supp _ hs k), mt_mulVec_inv]
    exact hz
  · intro hz
    have hs : ∀ k, (mt S g⁻¹ *ᵥ z) k ∈ idAt D (· = v) := fun k => GlobalTheory.FinPl.FrameLat.latV_supp hz k
    have h := (hm _ hs).1 hz
    rwa [mt_mulVec_inv] at h

theorem diagonal_mulVec_single {n : ℕ} (u : Fin n → AE D) (i : Fin n) (c : AE D) :
    Matrix.diagonal u *ᵥ Pi.single i c = Pi.single i (u i * c) := by
  funext j
  rw [Matrix.mulVec_diagonal]
  by_cases h : j = i
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem adj_diagonal {n : ℕ} (u : Fin n → AE D) :
    adj (Matrix.diagonal u) = Matrix.diagonal fun i => cA D (u i) := by
  ext i j
  show cA D (Matrix.diagonal u j i) = Matrix.diagonal (fun k => cA D (u k)) i j
  by_cases h : i = j
  · subst h; simp
  · rw [Matrix.diagonal_apply_ne _ (Ne.symm h), Matrix.diagonal_apply_ne _ h, map_zero]

variable (d : HypDec S S₀ ρ)

theorem levi_colMul_jX (a : GL (Fin ρ) (AE D)) {u : Fin ρ → AE D} (ha : a.1 = Matrix.diagonal u) (i : Fin ρ) (c : AE D) :
    mt S (d.levi a) *ᵥ colMul d.jX i c = colMul d.jX i (u i * c) := by
  rw [SplitLat.colMul_eq_mulVec, SplitLat.colMul_eq_mulVec, Matrix.mulVec_mulVec, d.levi_jX, ← Matrix.mulVec_mulVec, ha,
    diagonal_mulVec_single]

theorem levi_colMul_jY (a : GL (Fin ρ) (AE D)) {u : Fin ρ → AE D} (ha : (a⁻¹).1 = Matrix.diagonal u) (i : Fin ρ) (c : AE D) :
    mt S (d.levi a) *ᵥ colMul d.jY i c = colMul d.jY i (cA D (u i) * c) := by
  rw [SplitLat.colMul_eq_mulVec, SplitLat.colMul_eq_mulVec, Matrix.mulVec_mulVec, d.levi_jY, ← Matrix.mulVec_mulVec, ha,
    adj_diagonal, diagonal_mulVec_single]

theorem pX_levi_mulVec (a : GL (Fin ρ) (AE D)) {u : Fin ρ → AE D} (ha : a.1 = Matrix.diagonal u) (y : Fin S.rank → AE D)
    (i : Fin ρ) : (d.pX *ᵥ (mt S (d.levi a) *ᵥ y)) i = u i * (d.pX *ᵥ y) i := by
  rw [Matrix.mulVec_mulVec, d.pX_levi, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_diagonal]

theorem pY_levi_mulVec (a : GL (Fin ρ) (AE D)) {u : Fin ρ → AE D} (ha : (a⁻¹).1 = Matrix.diagonal u)
    (y : Fin S.rank → AE D) (i : Fin ρ) : (d.pY *ᵥ (mt S (d.levi a) *ᵥ y)) i = cA D (u i) * (d.pY *ᵥ y) i := by
  rw [Matrix.mulVec_mulVec, d.pY_levi, ← Matrix.mulVec_mulVec, ha, adj_diagonal, Matrix.mulVec_diagonal]

theorem wittProjAnisotropic_mulVec_levi_eq (a : GL (Fin ρ) (AE D)) (y : Fin S.rank → AE D) :
    d.p0 *ᵥ (mt S (d.levi a) *ᵥ y) = d.p0 *ᵥ y := by
  rw [Matrix.mulVec_mulVec, d.wittDecomp_projAnisotropic_levi]

theorem mem_dualC_one (c : D.host.E) : c ∈ SplitLat.dualC (1 : FI D) ↔ c ∈ (1 : FI D) := by
  rw [SplitLat.mem_dualC, FractionalIdeal.mem_one_iff]
  constructor
  · intro h
    obtain ⟨o, ho⟩ := h 1 ((FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩)
    exact ⟨o, by rw [ho, star_one, one_mul]⟩
  · rintro ⟨o, rfl⟩ b hb
    obtain ⟨o', rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hb
    obtain ⟨r, hr⟩ := GlobalTheory.HypLattice.star_mem_int ⟨o', rfl⟩
    exact ⟨r * o, by rw [map_mul, hr]⟩

variable (L₀ : Lat S₀)

theorem line_splitL_jY (v : Pl D) (i : Fin ρ) (a : AE D) :
    colMul d.jY i a ∈ latV S (SplitLat.splitL d L₀ (fun _ => (1 : FI D))) (· = v) ↔ a ∈ idV (1 : FI D) v := by
  constructor
  · intro ha
    have key : ∀ y ∈ latV S (SplitLat.splitL d L₀ (fun _ => (1 : FI D))) (· = v), (d.pY *ᵥ y) i ∈ idV (1 : FI D) v := by
      intro y hy
      induction hy using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
        rw [Set.mem_singleton_iff] at hc
        subst hc
        change (rat d.qY *ᵥ _) i ∈ _
        rw [SplitLat.rat_mulVec_gen]
        refine AddSubgroup.subset_closure ⟨β, hβi, hβ, _, ?_, rfl⟩
        rw [one_mul]
        exact (mem_dualC_one _).1 (((SplitLat.mem_splitL d L₀ _ x).1 hx).2.2 i)
      | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
      | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
      | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz
    have h := key _ ha
    rwa [SplitLat.colMul_eq_mulVec, Matrix.mulVec_mulVec, d.pY_jY, Matrix.one_mulVec, Pi.single_eq_same] at h
  · intro ha
    rw [idV] at ha
    induction ha using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨β, hβi, hβ, b, hb, rfl⟩ := hz
      have e : colMul d.jY i (pairA D.host.F 0 β ⊗ₜ[D.host.F] b) =
          rat d.e' *ᵥ fun l => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * (Pi.single i b : Fin ρ → D.host.E) l) := by
        rw [SplitLat.colMul_eq_mulVec]
        change rat d.e' *ᵥ _ = _
        congr 1
        funext l
        by_cases h : l = i
        · subst h; simp
        · simp [Pi.single_eq_of_ne h]
      rw [e, SplitLat.rat_mulVec_gen]
      exact AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, _,
        SplitLat.e'_mem (SplitLat.single_mem_of_mem (I := fun _ => SplitLat.dualC (1 : FI D)) i ((mem_dualC_one _).2 hb)), rfl⟩
    | zero =>
      have : colMul d.jY i 0 = 0 := by funext k; simp [colMul]
      rw [this]; exact zero_mem _
    | add z z' _ _ hz hz' =>
      have : colMul d.jY i (z + z') = colMul d.jY i z + colMul d.jY i z' := by funext k; simp [colMul, add_mul]
      rw [this]; exact add_mem hz hz'
    | neg z _ hz =>
      have : colMul d.jY i (-z) = -colMul d.jY i z := by funext k; simp [colMul]
      rw [this]; exact neg_mem hz

end GlobalTheory.FinPl.MonoIdele


open GlobalTheory.FinPl.MonoIdele in
theorem GlobalTheory.FinPl.exists_selfDual_mono_idele : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L₀ : Lat S₀), IsSelfDualC S₀ L₀ → ∀ b : Fin ρ → (AE D)ˣ, ∃ L : Lat S, IsSelfDualC S L ∧ ∀ x : Pl D, MonoAt d L L₀ x ∧ (∀ i, ∀ a ∈ idAt D (· = x), colMul d.jX i a ∈ latV S L (· = x) ↔ (((b i)⁻¹ : (AE D)ˣ) : AE D) * a ∈ intAt D (· = x)) ∧ ∀ i, ∀ a ∈ idAt D (· = x), colMul d.jY i a ∈ latV S L (· = x) ↔ cA D (b i : AE D) * a ∈ intAt D (· = x) := by
  intro D S S₀ ρ d L₀ hL₀ b
  have hL1 : IsSelfDualC S (SplitLat.splitL d L₀ (fun _ => (1 : FI D))) :=
    SplitLat.isSelfDualC_splitL d (fun _ => one_ne_zero) hL₀
  obtain ⟨M, hM, hmv⟩ := (_root_.GlobalTheory.FinPl.GlobImage.glob D S _ hL1).1 (d.levi (diagU b))
  refine ⟨M, hM, fun x => ⟨?_, fun i a _ => ?_, fun i a _ => ?_⟩⟩
  · have key := mem_iff_of_moves (hmv (· = x))
    rw [← map_inv] at key
    intro y
    rw [key y, SplitLat.monoAt_splitL d L₀ (fun _ => (1 : FI D)) x (mt S (d.levi (diagU b)⁻¹) *ᵥ y)]
    simp only [key, levi_colMul_jX d _ (diagU_inv_val b), levi_colMul_jY d _ (diagU_inv_inv_val b),
      pX_levi_mulVec d _ (diagU_inv_val b), pY_levi_mulVec d _ (diagU_inv_inv_val b), wittProjAnisotropic_mulVec_levi_eq]
  · have key := mem_iff_of_moves (hmv (· = x))
    rw [← map_inv] at key
    rw [key, levi_colMul_jX d _ (diagU_inv_val b)]
    exact (SplitLat.line_splitL d L₀ _ x i _).trans (GlobalTheory.SeeSaw.idV_one_eq_intAt D x _)
  · have key := mem_iff_of_moves (hmv (· = x))
    rw [← map_inv] at key
    rw [key, levi_colMul_jY d _ (diagU_inv_inv_val b)]
    exact (line_splitL_jY d L₀ x i _).trans (GlobalTheory.SeeSaw.idV_one_eq_intAt D x _)

end
end

