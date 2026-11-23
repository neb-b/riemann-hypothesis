module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.AtTauExUniqueHolds
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0927
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0931
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0948
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemMultiplicitySpaceLevelOfKFiniteTensors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KFiniteLevel

theorem mem_multT_of_kfin : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (θ : InfFam D), IsInfFam θ → ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), (∀ κ ∈ J, κ ∈ GfC V) → ∀ F ∈ MultT θ M ∅ 1, (∀ w ∈ (Submodule.span ℂ {w : SmT M | ∃ v : (M).Vec, (∀ τ, (v τ : (M).H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧ w = PiTensorProduct.tprod ℂ v}), ∀ κ ∈ J, ∀ g, F w (g * κ) = χ κ * F w g) → F ∈ MultT θ M J χ := by
  intro D V S M θ hθ J χ hJ F hF hk
  rw [mem_multT, GlobalTheory.MultMem.mem_mult_iff] at hF ⊢
  set T : MMap M := PiTensorProduct.lift.symm F with hTdef
  have hT : ∀ v : M.Vec, T v = F (PiTensorProduct.tprod ℂ v) := fun v => by
    rw [hTdef, PiTensorProduct.lift_symm]; rfl
  refine ⟨hF.aut, hF.cusp, fun v κ hκ g => ?_, hF.equiv, hF.cont⟩
  set U : MMap M := heckeOn M {κ} T - χ κ • T with hUdef
  have hU : U ∈ Mult θ M ∅ 1 :=
    sub_mem ((GlobalTheory.MultMem.mem_mult_iff ..).2 (GlobalTheory.SphericalOps.isMultMap_single hF (hJ κ hκ)))
      (Submodule.smul_mem _ _ ((GlobalTheory.MultMem.mem_mult_iff ..).2 hF))
  have hUv : ∀ (u : M.Vec) (x : GA D V), U u x = T u (x * κ) - χ κ * T u x := fun u x => by
    simp [hUdef, heckeOn, postOn_apply, heckeLin_apply]
  have h0 : U = 0 := GlobalTheory.KFiniteDetermined.restrInj D θ hθ V S M ∅ 1 U hU fun u hu => by
    funext x
    rw [hUv, hT, Pi.zero_apply, sub_eq_zero]
    exact hk _ (Submodule.subset_span ⟨u, fun τ => Submodule.subset_span (hu τ), rfl⟩) κ hκ x
  have := hUv v g
  rw [h0] at this
  exact (sub_eq_zero.1 this.symm)

end GlobalTheory.KFiniteLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
section
namespace I195MixedCoordinates_38e171c1cdbf76962db34e8f

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

end I195MixedCoordinates_38e171c1cdbf76962db34e8f

@[expose] public section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

open GlobalTheory.MixModel Matrix

noncomputable section

namespace GlobalTheory.Core.Rk.SWLaw

variable {D : D7}

abbrev zeroSp (D : D7) : HSp D := Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral 0

def stackRows {a k : ℕ} (X Y : Matrix (Fin a) (Fin k) D.host.E) : Matrix (Fin (a + a)) (Fin k) D.host.E :=
  (Matrix.fromRows X Y).submatrix finSumFinEquiv.symm id

theorem stackRows_gram (A : HSp D) {k l : ℕ} (X Y : Matrix (Fin A.rank) (Fin k) D.host.E)
    (P Q : Matrix (Fin A.rank) (Fin l) D.host.E) :
    (stackRows X Y)ᴴ * (dblSp A).gram * stackRows P Q = Xᴴ * A.gram * P - Yᴴ * A.gram * Q := by
  rw [GlobalTheory.Doubling.gram_hdbl, GlobalTheory.Doubling.dblGram, GlobalTheory.Doubling.blkMat, stackRows, stackRows,
    conjTranspose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv, submatrix_id_id,
    conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul, sub_eq_add_neg]

def dblDec (A : HSp D) : HypDec (dblSp A) (zeroSp D) A.rank where
  e := stackRows A.gram⁻¹ A.gram⁻¹
  e' := stackRows ((2 : D.host.E)⁻¹ • 1) (-((2 : D.host.E)⁻¹ • 1))
  i₀ := 0
  ee := by rw [stackRows_gram, sub_self]
  e'e' := by
    rw [stackRows_gram, conjTranspose_neg, Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg, sub_self]
  e'e := by
    have hG : IsUnit A.gram.det := (gram_det_ne A).isUnit
    rw [stackRows_gram, conjTranspose_neg, Matrix.neg_mul, Matrix.neg_mul, sub_neg_eq_add, Matrix.mul_assoc,
      mul_nonsing_inv _ hG, Matrix.mul_one, conjTranspose_smul, conjTranspose_one, ← add_smul, star_inv₀, star_ofNat]
    rw [show ((2 : D.host.E)⁻¹ + 2⁻¹) = 1 by rw [← two_mul, mul_inv_cancel₀ two_ne_zero], one_smul]
  iso := Matrix.ext fun i _ => Fin.elim0 i
  i₀e := by rw [conjTranspose_zero, Matrix.zero_mul, Matrix.zero_mul]
  i₀e' := by rw [conjTranspose_zero, Matrix.zero_mul, Matrix.zero_mul]
  rank_add := by show 0 + 2 * A.rank = A.rank + A.rank; omega

theorem dblDec_qY (A : HSp D) :
    (dblDec A).qY = (Matrix.fromCols (1 : Matrix (Fin A.rank) (Fin A.rank) D.host.E) (-1)).submatrix id
      finSumFinEquiv.symm := by
  have hG : IsUnit A.gram.det := (gram_det_ne A).isUnit
  rw [HypDec.qY]
  show (stackRows A.gram⁻¹ A.gram⁻¹)ᴴ * (dblSp A).gram = _
  rw [GlobalTheory.Doubling.gram_hdbl, GlobalTheory.Doubling.dblGram, GlobalTheory.Doubling.blkMat, stackRows, conjTranspose_submatrix,
    submatrix_mul_equiv, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromBlocks,
    conjTranspose_nonsing_inv, gram_conjTranspose, nonsing_inv_mul _ hG]
  simp only [Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg, nonsing_inv_mul _ hG]

theorem extY_dblDec (A B : HSp D) (w : Mx D B.rank A.rank) : (dblDec A).extY B w = GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr A B w := by
  rw [HypDec.extY_apply, HypDec.pY, dblDec_qY]
  ext i j
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective j
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.lagr, rat, Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply, Matrix.submatrix_apply,
    id, Equiv.symm_apply_apply]
  rcases s with k | k
  · simp [Matrix.one_apply]
  · simp [Matrix.one_apply]

theorem mixS_dblDec_zero (A B : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (ν : Measure (WO A B)) (𝓕 : Set (WO A B))
    (f : WO (dblSp A) B → ℂ) (w₀ : WO (zeroSp D) B) :
    (dblDec A).mixS B ψ ν 𝓕 f 0 w₀ = GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.evZero A B ν 𝓕 f := by
  have hw : w₀ = 0 := Matrix.ext fun _ j => Fin.elim0 j
  subst hw
  have hz : ∀ y : WO (dblSp A) B, symplOH (dblSp A) B y 0 = 0 := fun y => by
    have h := GlobalTheory.OrientedHeis.symplOH_add_right (S := dblSp A) (T := B) y 0 0
    rw [add_zero] at h
    exact left_eq_add.1 h
  unfold HypDec.mixS GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.evZero
  congr 1
  funext a
  rw [HypDec.integrandS_eq, map_zero, map_zero, hz, AddChar.map_zero_eq_one, one_mul, add_zero, add_zero,
    extY_dblDec]

end GlobalTheory.Core.Rk.SWLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ModelIdentificationRespectsRealAndFinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open Formalism.MainNotions.StandardLattice

namespace GlobalTheory.Core.Mi.SeeReal

variable {D : D7}

theorem isAtTau_atTau (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (τ : D.what₂.Tau)
    (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) (hg : gᴴ * gramAt D V τ * g = gramAt D V τ) :
    IsAtTau θ V τ g (atTau θ V τ g) := by
  have hex := (Formalism.IndefR.Eqv.atTauExUnique_holds D θ hθ V τ g hg).exists
  unfold atTau
  rw [dite_eq_left hex]
  exact hex.choose_spec

theorem eq_of_conj {n : ℕ} {P A B : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P.det) (e : P * A * P⁻¹ = B) :
    A = P⁻¹ * B * P := by
  rw [← e]
  simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul P hP, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left P A hP]

theorem phi_inst (v : InfinitePlace D.host.F) (x : D.host.E) :
    (Formalism.IndefR.RationalEmbedding.inst D).φ v x = embS D ((Formalism.L2.Host.tauPl D).symm v) x := rfl

theorem realSplit_gen {I : Formalism.MainNotions.S.AutInst} (h : I = Formalism.L2.SG.InstExistsPf.instOf D)
    (ιE : I.E ≃+* D.host.E) (hιE : ∀ x : I.E, HEq (ιE x) x) (pl : InfinitePlace I.F ≃ D.what₂.Tau)
    (hφ : ∀ v (x : I.E), I.φ v x = embS D (pl v) (ιE x)) (θ : InfFam D) (hθ : IsInfFam θ) :
    (∀ k : GA D (D.sp.Y 0), k ∈ GfC (D.sp.Y 0) ↔ ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) k).1 = 1) ∧
    (∀ k : GA D (D.sp.Y 0), k ∈ GinfC (D.sp.Y 0) ↔ ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) k).2 = 1) ∧
    (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ),
      ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) (atTau θ (D.sp.Y 0) τ g)).2 = 1 ∧
      (∀ v, v ≠ pl.symm τ → ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) (atTau θ (D.sp.Y 0) τ g)).1 v = 1) ∧
      HEq (uMat (((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) (atTau θ (D.sp.Y 0) τ g)).1 (pl.symm τ)))
        ((fun Pm : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ => Pm⁻¹ * g * Pm)
          ((Formalism.L2.SG.InstExistsPf.instOf D).P (Formalism.L2.Host.tauPl D τ)))) ∧
    ∀ τ (y : Formalism.REAL.UJ (I.ε (pl.symm τ))), ∃ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ),
      ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm) (atTau θ (D.sp.Y 0) τ g)).1 (pl.symm τ) = y := by
  subst h
  obtain rfl := Formalism.IndefR.Eqv.eq_thetaC D hθ
  have hι : ∀ x, ιE x = x := fun x => eq_of_heq (hιE x)
  have key : ∀ τ τ' : D.what₂.Tau, embS D τ = embS D τ' → τ = τ' :=
    fun τ τ' e => D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 e))
  have hpl : pl = (Formalism.L2.Host.tauPl D).symm := Equiv.ext fun v => key _ _ (RingHom.ext fun x => by
    have e := hφ v x
    have e2 : embS D (pl v) (ιE x) = embS D (pl v) x := congrArg _ (hι x)
    exact (e2.symm.trans e.symm).trans (phi_inst v x))
  subst hpl
  have hT : ∀ k, ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA (rfl : Formalism.L2.SG.InstExistsPf.instOf D = _).symm)) k =
      Formalism.IndefR.RationalEmbedding.iota D k := fun _ => rfl
  have hP : ∀ v, IsUnit ((Formalism.IndefR.RationalEmbedding.inst D).P v).det :=
    fun v => (Matrix.isUnit_iff_isUnit_det _).mp ((Formalism.IndefR.RationalEmbedding.inst D).P_unit v)
  refine ⟨fun k => ?_, fun k => ?_, fun τ g hg => ?_, fun τ y => ?_⟩
  · rw [hT]
    have e := Formalism.L2.SG.EvalTIota.brg_mem_GfC_i (Formalism.IndefR.RationalEmbedding.iota D k)
    rwa [ContinuousMulEquiv.symm_apply_apply] at e
  · rw [hT]
    have e := Formalism.L2.SG.EvalTIota.iota_symm_mem_GinfC (Formalism.IndefR.RationalEmbedding.iota D k)
    rwa [ContinuousMulEquiv.symm_apply_apply] at e
  · have hg' : gᴴ * gramAt D (D.sp.Y 0) τ * g = gramAt D (D.sp.Y 0) τ := hg
    have hk := isAtTau_atTau (Formalism.IndefR.Eqv.thetaC D) (Formalism.IndefR.Eqv.isInfFam_thetaC D) _ τ g hg'
    rw [hT]
    generalize atTau (Formalism.IndefR.Eqv.thetaC D) (D.sp.Y 0) τ g = k at hk ⊢
    obtain ⟨x, rfl⟩ := (Formalism.IndefR.RationalEmbedding.iota D).symm.surjective k
    rw [ContinuousMulEquiv.apply_symm_apply]
    have hbr := Formalism.L2.SG.EvalTIota.infMat_brg_i x
    refine ⟨(Formalism.L2.SG.EvalTIota.iota_symm_mem_GinfC x).1 hk.1, fun v hv => ?_, heq_of_eq ?_⟩
    · obtain ⟨ρ, rfl⟩ := (Formalism.L2.Host.tauPl D).surjective v
      have hρ : ρ ≠ τ := fun e => hv (by rw [e]; rfl)
      have e0 : Formalism.L2.SG.EvalTIota.Pi (Formalism.L2.Host.tauPl D ρ) * Formalism.L2.SG.EvalTIota.uM' x (Formalism.L2.Host.tauPl D ρ) *
          (Formalism.L2.SG.EvalTIota.Pi (Formalism.L2.Host.tauPl D ρ))⁻¹ = (1 : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ) := by
        rw [← hbr ρ, hk.2.2 ρ hρ]
      have e1 := eq_of_conj (hP _) e0
      simp only [Formalism.L2.SG.EvalTIota.Pi, Formalism.L2.SG.EvalTIota.uM'] at e1
      have e2 : uMat (x.1 (Formalism.L2.Host.tauPl D ρ)) = 1 := by
        rw [e1]
        erw [Matrix.mul_one]
        exact Matrix.nonsing_inv_mul _ (hP _)
      exact Subtype.ext (Units.ext e2)
    · exact eq_of_conj (hP _) ((hbr τ).symm.trans hk.2.1)
  · classical
    let x0 : (Formalism.IndefR.RationalEmbedding.inst D).GA :=
      (Pi.mulSingle (M := fun v => Formalism.REAL.UJ ((Formalism.IndefR.RationalEmbedding.inst D).ε v)) (Formalism.L2.Host.tauPl D τ) y, 1)
    have hbr := Formalism.L2.SG.EvalTIota.infMat_brg_i x0
    let g : Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.Y 0).rank) ℂ :=
      (Formalism.IndefR.RationalEmbedding.inst D).P (Formalism.L2.Host.tauPl D τ) * uMat y * ((Formalism.IndefR.RationalEmbedding.inst D).P (Formalism.L2.Host.tauPl D τ))⁻¹
    have hk0 : IsAtTau (Formalism.IndefR.Eqv.thetaC D) (D.sp.Y 0) τ g ((Formalism.IndefR.RationalEmbedding.iota D).symm x0) := by
      refine ⟨(Formalism.L2.SG.EvalTIota.iota_symm_mem_GinfC x0).2 rfl, ?_, fun ρ hρ => ?_⟩
      · rw [hbr τ]
        have hy : x0.1 (Formalism.L2.Host.tauPl D τ) = y :=
          Pi.mulSingle_eq_same (M := fun v => Formalism.REAL.UJ ((Formalism.IndefR.RationalEmbedding.inst D).ε v)) (Formalism.L2.Host.tauPl D τ) y
        have hy' : Formalism.L2.SG.EvalTIota.uM' x0 (Formalism.L2.Host.tauPl D τ) = uMat y := by
          show uMat (x0.1 (Formalism.L2.Host.tauPl D τ)) = uMat y
          rw [hy]
        rw [hy']
        rfl
      · rw [hbr ρ]
        have hne : Formalism.L2.Host.tauPl D ρ ≠ Formalism.L2.Host.tauPl D τ := (Formalism.L2.Host.tauPl D).injective.ne hρ
        have h1 : x0.1 (Formalism.L2.Host.tauPl D ρ) = 1 := Pi.mulSingle_eq_of_ne hne _
        have h1' : Formalism.L2.SG.EvalTIota.uM' x0 (Formalism.L2.Host.tauPl D ρ) = 1 := by
          show uMat (x0.1 (Formalism.L2.Host.tauPl D ρ)) = 1
          rw [h1]
          rfl
        rw [h1']
        erw [Matrix.mul_one]
        exact Matrix.mul_nonsing_inv _ (hP _)
    have hgU : gᴴ * gramAt D (D.sp.Y 0) τ * g = gramAt D (D.sp.Y 0) τ :=
      Formalism.IndefR.Eqv.atTauUnitary_holds D _ (Formalism.IndefR.Eqv.isInfFam_thetaC D) _ τ g _ hk0
    refine ⟨g, hgU, ?_⟩
    have hu := (Formalism.IndefR.Eqv.atTauExUnique_holds D _ (Formalism.IndefR.Eqv.isInfFam_thetaC D) _ τ g hgU).unique
      (isAtTau_atTau _ (Formalism.IndefR.Eqv.isInfFam_thetaC D) _ τ g hgU) hk0
    rw [hT, hu, ContinuousMulEquiv.apply_symm_apply]
    exact Pi.mulSingle_eq_same (M := fun v => Formalism.REAL.UJ ((Formalism.IndefR.RationalEmbedding.inst D).ε v)) _ _

theorem realSplit_of_idE : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (θ : InfFam D), IsInfFam θ → IdE X → RealSplit X h θ :=
  fun _ X h θ hθ hE => realSplit_gen h X.ιE hE X.pl X.φ_eq θ hθ

end GlobalTheory.Core.Mi.SeeReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulVecPairVecDiag
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.Dich

open Matrix

section Mat

variable {A B : Type} [CommRing A] [CommRing B] {n : ℕ}

def diagSnd (M : Matrix (Fin (n + n)) (Fin (n + n)) A) : Matrix (Fin n) (Fin n) A :=
  (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁ + (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂

theorem mulVec_pairVec_diag (M : Matrix (Fin (n + n)) (Fin (n + n)) A) (x : Fin n → A) :
    M *ᵥ pairVec finSumFinEquiv x x =
      pairVec finSumFinEquiv (leviMat finSumFinEquiv M *ᵥ x) (diagSnd M *ᵥ x) := by
  rw [mulVec_pairVec, leviMat, diagSnd, add_mulVec, add_mulVec]

theorem diagSnd_map (f : A →+* B) (M : Matrix (Fin (n + n)) (Fin (n + n)) A) :
    diagSnd (M.map f) = (diagSnd M).map f := by
  ext i j; simp [diagSnd, toBlocks₂₁, toBlocks₂₂]

theorem isotropic_diag {σ : A →+* A} {J : Matrix (Fin n) (Fin n) A} {M : Matrix (Fin (n + n)) (Fin (n + n)) A}
    (hM : Formalism.UG.cT σ M * dblGram finSumFinEquiv J * M = dblGram finSumFinEquiv J) :
    Formalism.UG.cT σ (leviMat finSumFinEquiv M) * J * leviMat finSumFinEquiv M =
      Formalism.UG.cT σ (diagSnd M) * J * diagSnd M := by
  have h1 : Formalism.UG.cT σ (M.submatrix finSumFinEquiv finSumFinEquiv) * fromBlocks J 0 0 (-J) *
      M.submatrix finSumFinEquiv finSumFinEquiv = fromBlocks J 0 0 (-J) := by
    rw [← submatrix_blkMat finSumFinEquiv,
      show Formalism.UG.cT σ (M.submatrix finSumFinEquiv finSumFinEquiv) =
        (Formalism.UG.cT σ M).submatrix finSumFinEquiv finSumFinEquiv from rfl, submatrix_mul_equiv, submatrix_mul_equiv]
    exact congrArg (fun X => X.submatrix finSumFinEquiv finSumFinEquiv) hM
  rw [← fromBlocks_toBlocks (M.submatrix finSumFinEquiv finSumFinEquiv)] at h1
  simp only [Formalism.UG.cT, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, Matrix.mul_zero, add_zero,
    zero_add, Matrix.mul_neg, Matrix.neg_mul, fromBlocks_inj] at h1
  obtain ⟨h11, h12, h21, h22⟩ := h1
  simp only [Formalism.UG.cT, leviMat, diagSnd, Matrix.map_add _ (map_add σ), transpose_add, Matrix.add_mul, Matrix.mul_add]
  set a := (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₁
  set b := (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂
  set c := (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₁
  set d := (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂
  rw [← sub_eq_zero]
  have := congrArg₂ (fun a b => a + b) (congrArg₂ (fun a b => a + b) h11 h12) (congrArg₂ (fun a b => a + b) h21 h22)
  simp only [add_zero, add_neg_cancel] at this
  rw [← sub_eq_zero] at this
  rw [← this]
  abel

end Mat

section Rat

open Formalism.BasicNotions Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_rat (W : HSp D) {γ : GA D W} (hγ : γ ∈ GQ W) :
    ∃ g : GL (Fin W.rank) D.host.E, g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram ∧
      (matHom W γ).1 = g.1.map (incA D) ∧ (matHom W γ⁻¹).1 = (g⁻¹).1.map (incA D) := by
  obtain ⟨g, hg, e⟩ := hγ
  have e' : matHom W γ = Formalism.UG.bc (incA D) g := e.symm
  refine ⟨g, hg, congrArg Units.val e', ?_⟩
  rw [map_inv, e', ← map_inv]
  rfl

theorem exists_of_rat (W : HSp D) {g : GL (Fin W.rank) D.host.E}
    (hg : g ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) W.gram) :
    ∃ δ ∈ GQ W, (matHom W δ).1 = g.1.map (incA D) := by
  have hm : Formalism.UG.bc (incA D) g ∈ HR (AF D.host.F) D.sp.cm.sig W.gram := by
    have hc : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) ((g : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D)) =
        (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E)).map (incA D) := by
      ext i j; simp [Formalism.UG.cT, sigR, inclR]
    have hg' : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) * W.gram *
        (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) = W.gram := hg
    change Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) ((g : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D)) *
      W.gram.map (incA D) * (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D) = W.gram.map (incA D)
    rw [hc, ← Matrix.map_mul, ← Matrix.map_mul, hg']
  exact ⟨⟨_, hm⟩, ⟨g, hg, rfl⟩, rfl⟩

end Rat

end GlobalTheory.Core.Rk.Dich
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicitySpaceEquivariantRealPoints
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem mult_equiv_real : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (Sp : D.what₂.Tau → SPar) (M : DSModel V Sp) (J : Set (GA D V)) (χ : GA D V → ℂ), IsInfFam θ → ∀ (v : M.Vec) (b : GinfC V), ∃ w : M.Vec, (∀ τ, (w τ : M.H τ) = M.rep τ (infMat D.sp.cm.sig V.gram (θ τ) (b : GA D V)) (v τ : M.H τ)) ∧ ∀ U ∈ Mult θ M J χ, U w = rTr V (b : GA D V) (U v) := by
  intro D θ V Sp M J χ hθ v b
  classical
  let g : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ := fun τ => infMat D.sp.cm.sig V.gram (θ τ) (b : GA D V)
  have hg : ∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := fun τ =>
    GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V (b : GA D V) τ
  have hsm : ∀ τ, M.rep τ (g τ) (v τ : M.H τ) ∈ M.sm τ := fun τ =>
    GlobalTheory.SmoothStable.rep_mem_sm D V Sp M τ (g τ) (hg τ) _ (v τ).2
  have hb : GlobalTheory.AdelicScalar.realElt θ V g = (b : GA D V) := by
    have hR := (GlobalTheory.SmoothForms.RealPts.realPoints D).2 θ hθ V
    refine hR.2.2.1 _ (GlobalTheory.RealLift.prodAt_mem θ V _ g) _ b.2 fun τ => ?_
    have e := GlobalTheory.RealLift.infMat_prodAt hθ V (u := g) hg τ _ (Finset.nodup_toList Finset.univ)
    rw [if_pos (Finset.mem_toList.2 (Finset.mem_univ _))] at e
    exact e
  refine ⟨fun τ => ⟨_, hsm τ⟩, fun τ => rfl, fun U hU => ?_⟩
  rw [GlobalTheory.RealEquiv.mult_realElt D V Sp θ M J χ U hU g hg v _ (fun τ => rfl), hb]

end GlobalTheory.ChainOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PartialNormalizingFactorProductAnalyticNeZero
section
noncomputable section

namespace GlobalTheory.LFun

open NumberField IsDedekindDomain

section Ext

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem one_lt_re_dv_arg {a i : ℕ} (hi : i ∈ Finset.range a) {s : ℂ} (hs : 0 < s.re) :
    1 < (2 * s + a - i : ℂ).re := by
  have : (i : ℝ) + 1 ≤ a := by exact_mod_cast Finset.mem_range.1 hi
  simp
  linarith

theorem dv_ne_zero_of_re_pos (a b : ℕ) (v : HeightOneSpectrum (𝓞 F)) {s : ℂ} (hs : 0 < s.re) :
    dv E a b v s ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun i hi =>
    inv_ne_zero ((converges_etaFam (E := E) ∅ (b + i) (one_lt_re_dv_arg hi hs)).1 v (Set.notMem_empty v))

theorem dSfun_ne_zero_of_re_pos (S : Set (HeightOneSpectrum (𝓞 F))) (a b : ℕ) {s : ℂ} (hs : 0 < s.re) :
    dSfun E S a b s ≠ 0 := by
  rw [dSfun_eq S a b hs]
  exact Finset.prod_ne_zero_iff.2 fun i hi => (converges_etaFam S (b + i) (one_lt_re_dv_arg hi hs)).ne_zero

theorem differentiableOn_dSfun (S : Set (HeightOneSpectrum (𝓞 F))) (a b : ℕ) :
    DifferentiableOn ℂ (dSfun E S a b) {s | 0 < s.re} := by
  have h : DifferentiableOn ℂ (fun s : ℂ => ∏ i ∈ Finset.range a, etaL E S (b + i) (2 * s + a - i))
      {s | 0 < s.re} := by
    refine DifferentiableOn.fun_finsetProd fun i hi => ?_
    refine (bounded_etaFam (E := E) S (b + i)).differentiableOn.comp
      (f := fun s : ℂ => 2 * s + a - i) (by fun_prop) fun s hs => ?_
    simpa only [zero_add, Set.mem_ofPred_eq] using one_lt_re_dv_arg hi hs
  exact h.congr fun s hs => dSfun_eq S a b hs

end Ext

end GlobalTheory.LFun

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem dSfun_analytic_ne_zero : ∀ (D : D7) (S : Set (FinPl D)) (a b : ℕ), AnalyticOnNhd ℂ (GlobalTheory.LFun.dSfun (F := D.host.F) D.host.E S a b) (rightOf 0) ∧ ∀ s : ℂ, 0 < s.re → GlobalTheory.LFun.dSfun (F := D.host.F) D.host.E S a b s ≠ 0 ∧ (∀ v : FinPl D, GlobalTheory.LFun.dv D.host.E a b v s ≠ 0) ∧ HasProd (fun v : {v : FinPl D // v ∉ S} => GlobalTheory.LFun.dv D.host.E a b v.1 s) (GlobalTheory.LFun.dSfun (F := D.host.F) D.host.E S a b s) := fun _ S a b =>
  ⟨(GlobalTheory.LFun.differentiableOn_dSfun S a b).analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re),
    fun _ hs => ⟨GlobalTheory.LFun.dSfun_ne_zero_of_re_pos S a b hs, fun v => GlobalTheory.LFun.dv_ne_zero_of_re_pos a b v hs,
      (GlobalTheory.LFun.hasProd_dv S a b hs).multipliable.hasProd⟩⟩

end GlobalTheory.Core.Rk.IP

end
end

