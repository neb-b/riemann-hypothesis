module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryMatchingLatticesMatchesSphericalOps
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0107
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceHyperspecialStableLatticeEqMultiple
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarVolumes.BridgeA
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MeasUpq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0355
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0654
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1044
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardFramesMatchCompletedLatticesAtPrime
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

namespace GlobalTheory.LatMatch

section Abstract
variable {R : Type} [CommRing R] [Nontrivial R]

theorem card_eq_of_inv {a b : ℕ} (A : Matrix (Fin a) (Fin b) R) (B : Matrix (Fin b) (Fin a) R)
    (h1 : A * B = 1) (h2 : B * A = 1) : a = b := by
  let e : (Fin b → R) ≃ₗ[R] (Fin a → R) := LinearEquiv.ofLinear (Matrix.toLin' A) (Matrix.toLin' B)
    (by rw [← Matrix.toLin'_mul, h1, Matrix.toLin'_one]) (by rw [← Matrix.toLin'_mul, h2, Matrix.toLin'_one])
  have := e.finrank_eq
  simpa using this.symm

end Abstract

theorem nontrivial_R (D : D7) : Nontrivial (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) := by
  haveI : Nontrivial (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 D.host.F)
    exact (Formalism.UG.evalV D.host.F ⟨P, hP.isPrime,
      Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField D.host.F)⟩).toRingHom.domain_nontrivial
  exact (Algebra.TensorProduct.includeLeft_injective (R := D.host.F) (S := D.host.F)
    (A := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (B := D.host.E) (algebraMap D.host.F D.host.E).injective).nontrivial


set_option maxHeartbeats 4000000 in
theorem frames_match_lattices : ∀ {D : D7} {V V' : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (Q : principalLevelFrame.RowPsi V n) (Q' : principalLevelFrame.RowPsi V' n), StdPsi hF Q → StdPsi hF Q' → ∀ (P : Pl D.host.E) (e f : Formalism.L2.Theta.AE D), IsPrimeIdem P e f → V'.rank = V.rank ∧ ∃ (J : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (J' : Matrix (Fin V.rank) (Fin V'.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)), J * J' = 1 ∧ J' * J = 1 ∧ (∀ κ, finMat D.sp.cm.sig V'.gram (Q'.ψ κ) * J = J * finMat D.sp.cm.sig V.gram (Q.ψ κ)) ∧ ∀ y, finPart D f • y ∈ Formalism.L2.NTheta.LamHat V ↔ finPart D f • J.mulVec y ∈ Formalism.L2.NTheta.LamHat V' := by
  intro D V V' n hF Q Q' hQ hQ' P e f hP
  haveI := nontrivial_R D
  obtain ⟨⟨β, β', hb1, hb2, hK⟩, hU⟩ := hQ
  obtain ⟨⟨γ, γ', hc1, hc2, hK'⟩, hU'⟩ := hQ'
  have hr : V.rank = n := card_eq_of_inv β β' hb1 hb2
  have hr' : V'.rank = n := card_eq_of_inv γ γ' hc1 hc2
  refine ⟨hr'.trans hr.symm, ?_⟩
  let X : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) := γ * β'
  let X' : Matrix (Fin V.rank) (Fin V'.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) := β * γ'
  have hX1 : X * X' = 1 := by
    show γ * β' * (β * γ') = 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc β' β γ', hb2, Matrix.one_mul, hc1]
  have hX2 : X' * X = 1 := by
    show β * γ' * (γ * β') = 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc γ' γ β', hc2, Matrix.one_mul, hb1]
  have hconj : ∀ κ, finMat D.sp.cm.sig V'.gram (Q'.ψ κ) * X = X * finMat D.sp.cm.sig V.gram (Q.ψ κ) := by
    intro κ
    rw [hK' κ, hK κ]
    show _ * (γ * β') = γ * β' * _
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc γ' γ β', hc2, Matrix.one_mul, ← Matrix.mul_assoc β' β, hb2, Matrix.one_mul]
  obtain ⟨-, -, T3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
  have hff : f * f = f := (T3 P e f hP).1
  set φ := finPart D f with hφdef
  have hφ : φ * φ = φ := by rw [hφdef, ← map_mul, hff]
  have hφint : φ ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D φ hφ
  have sm : ∀ (W : HSp D), ∀ a ∈ intAE D, ∀ y ∈ Formalism.L2.NTheta.LamHat W, a • y ∈ Formalism.L2.NTheta.LamHat W :=
    fun W a ha y hy => GlobalTheory.LatDual.smul_mem_lamHat W a ha y hy
  have nsm : ∀ (W : HSp D) (N : ℕ), ∀ y ∈ Formalism.L2.NTheta.LamHat W, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • y ∈ Formalism.L2.NTheta.LamHat W := by
    intro W N y hy
    rw [Nat.cast_smul_eq_nsmul]
    exact AddSubgroup.nsmul_mem _ hy N
  obtain ⟨N1, hN1, hB1⟩ := _root_.GlobalTheory.LatMatch.mulVec_lamHat_bound V V' X
  obtain ⟨N2, hN2, hB2⟩ := _root_.GlobalTheory.LatMatch.mulVec_lamHat_bound V' V X'
  let hom : (Fin V.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) →+ (Fin V'.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) :=
    (DistribSMul.toAddMonoidHom _ φ).comp (Matrix.mulVecLin X).toAddMonoidHom
  have hhom : ∀ y, hom y = φ • X.mulVec y := fun y => rfl
  let M : AddSubgroup (Fin V'.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) := (Formalism.L2.NTheta.LamHat V).map hom
  have hM : ∀ z, z ∈ M ↔ ∃ y ∈ Formalism.L2.NTheta.LamHat V, φ • X.mulVec y = z := fun z => by
    simp only [M, AddSubgroup.mem_map, hhom]
  have c1 : ∀ a ∈ intAE D, ∀ z ∈ M, a • z ∈ M := by
    intro a ha z hz
    obtain ⟨y, hy, rfl⟩ := (hM z).1 hz
    refine (hM _).2 ⟨a • y, sm V a ha y hy, ?_⟩
    rw [Matrix.mulVec_smul, smul_comm]
  have c2 : ∀ z ∈ M, φ • z = z := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := (hM z).1 hz
    rw [smul_smul, hφ]
  have c3 : ∃ N : ℕ, 0 < N ∧ (∀ y ∈ Formalism.L2.NTheta.LamHat V', ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • (φ • y) ∈ M) ∧
      ∀ z ∈ M, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • z ∈ Formalism.L2.NTheta.LamHat V' := by
    refine ⟨N1 * N2, Nat.mul_pos hN1 hN2, fun y hy => ?_, fun z hz => ?_⟩
    · refine (hM _).2 ⟨((N1 : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • (((N2 : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • X'.mulVec y), nsm V N1 _ (hB2 y hy), ?_⟩
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hX1, Matrix.one_mulVec]
      simp only [smul_smul, Nat.cast_mul]
      congr 1
      ring
    · obtain ⟨y, hy, rfl⟩ := (hM z).1 hz
      have h1 := nsm V' N2 _ (sm V' φ hφint _ (hB1 y hy))
      convert h1 using 1
      simp only [Matrix.mulVec_smul, smul_smul, Nat.cast_mul]
      congr 1
      ring
  have c4 : ∀ g : GA D V', g ∈ KsphC V' ∅ → SuppF V' f g → ∀ z ∈ M,
      (finMat D.sp.cm.sig V'.gram g).mulVec z ∈ M := by
    intro g hg _ z hz
    obtain ⟨y, hy, rfl⟩ := (hM z).1 hz
    obtain ⟨κ, hκ⟩ := Q'.onto g hg.1
    have hκU : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n := (hU' κ).2 (by rw [hκ]; exact hg)
    have hk : Q.ψ κ ∈ KsphC V ∅ := (hU κ).1 hκU
    refine (hM _).2 ⟨(finMat D.sp.cm.sig V.gram (Q.ψ κ)).mulVec y, (hk.2.1 y).1 hy, ?_⟩
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hconj κ, hκ]
  have hcore : ∃ c : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), IsUnit c ∧ ∀ z, z ∈ M ↔ (φ • z = z ∧ c • z ∈ Formalism.L2.NTheta.LamHat V') := by
    rcases hP with ⟨hI, hfe⟩ | ⟨hfe, hpl, hint⟩
    · have h := GlobalTheory.T.splitPlace_hyperspecialStable_lattice_eq_multiple V' P e hI M
      rw [← hfe] at h
      exact h c1 c2 c3 c4
    · rw [← hfe] at hpl hint
      exact _root_.GlobalTheory.InertLatMult.lattice_eq_mult V' P f hpl hint M c1 c2 c3 c4
  obtain ⟨c, ⟨u, rfl⟩, hcM⟩ := hcore
  refine ⟨(u : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • X, (↑u⁻¹ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • X', ?_, ?_, ?_, ?_⟩
  · rw [Matrix.smul_mul (u : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) X, Matrix.mul_smul X (↑u⁻¹ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) X', smul_smul, hX1, Units.mul_inv, one_smul]
  · rw [Matrix.smul_mul (↑u⁻¹ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) X', Matrix.mul_smul X' (u : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) X, smul_smul, hX2, Units.inv_mul, one_smul]
  · intro κ
    rw [Matrix.mul_smul, Matrix.smul_mul, hconj κ]
  · intro y
    have e1 : φ • (((u : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • X).mulVec y) = (u : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • (φ • X.mulVec y) := by
      rw [Matrix.smul_mulVec, smul_comm]
    rw [e1]
    constructor
    · intro h
      have hz : φ • X.mulVec y ∈ M := (hM _).2 ⟨φ • y, h, by rw [Matrix.mulVec_smul, smul_smul, hφ]⟩
      exact ((hcM _).1 hz).2
    · intro h
      have hz : φ • X.mulVec y ∈ M := (hcM _).2 ⟨by rw [smul_smul, hφ], h⟩
      obtain ⟨y', hy', hyy⟩ := (hM _).1 hz
      have := congrArg X'.mulVec hyy
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hX2,
        Matrix.one_mulVec, Matrix.one_mulVec] at this
      rw [← this]
      exact sm V φ hφint y' hy'

end GlobalTheory.LatMatch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardMeasureUnitaryPQEqVolumeSmulCompactDual
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow

noncomputable section

namespace GlobalTheory.LowRow.CompactDualScale

theorem omegaDensity_smul {P Q : ℕ} {μ : Measure (UpqT P Q)} {c : ENNReal} (a : ENNReal) (ha : a ≠ ⊤)
    (h : OmegaDensity μ c) : OmegaDensity (a • μ) (a * c) := by
  obtain ⟨lam, hlam, hl⟩ := h
  refine ⟨lam, hlam, ?_⟩
  refine (ENNReal.Tendsto.const_mul hl (Or.inr ha)).congr fun r => ?_
  rw [Measure.smul_apply, smul_eq_mul, mul_div_assoc]

theorem omegaDensity_unique {P Q : ℕ} {μ : Measure (UpqT P Q)} {c c' : ENNReal}
    (h : OmegaDensity μ c) (h' : OmegaDensity μ c') : c = c' := by
  obtain ⟨lam, hlam, hl⟩ := h
  obtain ⟨lam', hlam', hl'⟩ := h'
  rw [Formalism.IndefR.Eqv.MU.omegaLeb_unique hlam hlam'] at hl'
  exact tendsto_nhds_unique hl hl'

theorem isMinf_eq_volU_smul_cd : ∀ (cd : CDHaar) (p q : ℕ) (m : Measure (UpqT p q)), Lev.IsMinf m →
    m = ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU (p + q)) • cd.cd p q := by
  intro cd p q m hm
  obtain ⟨c, hc0, hctop, hpq, hN⟩ := cd.trick p q
  haveI := cd.haar (p + q) 0
  haveI := cd.prob (p + q)
  haveI := cd.haar p q
  have hmain := ReciprocityTheory.ChartRestriction.DS.PolarCoordinateComparison.omegaDensity_main (N := p + q) (cd.cd (p + q) 0)
  have hc := omegaDensity_unique hN hmain
  have hV : 0 < ReciprocityTheory.ChartRestriction.DS.volU (p + q) := ReciprocityTheory.ChartRestriction.DS.PolarCoordinateComparison.volU_pos (p + q)
  have hκ : (0 : ℝ) < 2 ^ ((p + q) * (p + q - 1) / 2) := by positivity
  have hmul : ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU (p + q)) * c = Formalism.L2.Theta.minfDensity (p + q) := by
    rw [hc, ← ENNReal.ofReal_mul hV.le, Formalism.L2.Theta.minfDensity]
    have e : ReciprocityTheory.ChartRestriction.DS.volU (p + q) * (1 / (2 ^ ((p + q) * (p + q - 1) / 2) * ReciprocityTheory.ChartRestriction.DS.volU (p + q)))
        = ((2 : ℝ) ^ ((p + q) * (p + q - 1) / 2))⁻¹ := by
      field_simp
    rw [e, ENNReal.ofReal_inv_of_pos hκ, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  have hV0 : ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU (p + q)) ≠ 0 := (ENNReal.ofReal_pos.2 hV).ne'
  have hm' : Lev.IsMinf (ENNReal.ofReal (ReciprocityTheory.ChartRestriction.DS.volU (p + q)) • cd.cd p q) := by
    refine ⟨Measure.IsHaarMeasure.smul _ hV0 ENNReal.ofReal_ne_top, ?_⟩
    rw [← hmul]
    exact omegaDensity_smul _ ENNReal.ofReal_ne_top hpq
  exact Formalism.IndefR.Eqv.MU.isMinf_unique hm' hm

end GlobalTheory.LowRow.CompactDualScale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubgroupAverageLinearTranslateConst
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.AvgLin

theorem avg_linear_translate_const : ∀ (H : Type) [Group H] (u v : H → ℂ) (c : ℂ) (g : H), (rStab u).index ≠ 0 → (rStab v).index ≠ 0 → avg (u + v) = avg u + avg v ∧ avg (c • u) = c * avg u ∧ avg (fun x => u (g * x)) = avg u ∧ avg (fun _ : H => c) = c := by
  intro H _ u v c g hu hv
  set S : Subgroup H := rStab u ⊓ rStab v with hS
  have hSi : S.index ≠ 0 := Subgroup.index_inf_ne_zero hu hv
  haveI : S.FiniteIndex := ⟨hSi⟩
  haveI : (rStab u).FiniteIndex := ⟨hu⟩
  have hSu : S ≤ rStab u := inf_le_left
  have hSv : S ≤ rStab v := inf_le_right
  have hSuv : S ≤ rStab (u + v) := by
    intro k hk x
    simp only [Pi.add_apply]
    rw [hSu hk x, hSv hk x]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [_root_.GlobalTheory.BCT.avg_eq_of_le_rStab H (u + v) S hSuv hSi, _root_.GlobalTheory.BCT.avg_eq_of_le_rStab H u S hSu hSi, _root_.GlobalTheory.BCT.avg_eq_of_le_rStab H v S hSv hSi,
      ← mul_add]
    congr 1
    simp only [Pi.add_apply]
    exact finsum_add_distrib (Set.toFinite _) (Set.toFinite _)
  · have hc : rStab u ≤ rStab (c • u) := by
      intro k hk x
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hk x]
    rw [_root_.GlobalTheory.BCT.avg_eq_of_le_rStab H (c • u) (rStab u) hc hu, _root_.GlobalTheory.BCT.avg_eq_of_le_rStab H u (rStab u) le_rfl hu]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_finsum]
    ring
  · have ht : rStab u ≤ rStab (fun x => u (g * x)) := by
      intro k hk x
      simp only
      rw [← mul_assoc, hk (g * x)]
    rw [_root_.GlobalTheory.BCT.avg_eq_of_le_rStab H _ (rStab u) ht hu, _root_.GlobalTheory.BCT.avg_eq_of_le_rStab H u (rStab u) le_rfl hu]
    congr 1
    have key : ∀ q : H ⧸ rStab u, u (g * q.out) = u (g • q).out := by
      intro q
      have : g • q = (QuotientGroup.mk (g * q.out) : H ⧸ rStab u) := by
        conv_lhs => rw [← QuotientGroup.out_eq' q]
        rfl
      rw [this]
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (rStab u) (g * q.out)
      rw [hh, h.2]
    simp_rw [key]
    exact finsum_comp_equiv (MulAction.toPerm g : Equiv.Perm (H ⧸ rStab u)) (f := fun q => u q.out)
  · have htop : (⊤ : Subgroup H) ≤ rStab (fun _ : H => c) := by
      intro k _ x
      rfl
    rw [_root_.GlobalTheory.BCT.avg_eq_of_le_rStab H _ ⊤ htop (by simp)]
    simp only [Subgroup.index_top, Nat.cast_one, inv_one, one_mul]
    rw [finsum_eq_single (fun _ => c) (1 : H ⧸ (⊤ : Subgroup H))]
    intro x hx
    exact absurd (QuotientGroup.subsingleton_quotient_top.elim x 1) hx

end GlobalTheory.AvgLin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubgroupAverageProdMulEqMul
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.AvgProd

lemma apply_out_rStab {H : Type} [Group H] (u : H → ℂ) (x : H) :
    u ((x : H ⧸ rStab u).out) = u x := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (rStab u) x
  rw [hk]
  have hk' : ∀ y, u (y * (k : H)) = u y := k.2
  exact hk' x

theorem avg_prod : ∀ (H H' : Type) [Group H] [Group H'] (u : H → ℂ) (v : H' → ℂ), (rStab u).index ≠ 0 →
    (rStab v).index ≠ 0 → avg (fun x : H × H' => u x.1 * v x.2) = avg u * avg v := by
  intro H H' _ _ u v hu hv
  set S : Subgroup (H × H') := (rStab u).prod (rStab v) with hS
  have hle : S ≤ rStab (fun x : H × H' => u x.1 * v x.2) := by
    intro p hp
    rw [hS, Subgroup.mem_prod] at hp
    have ha : ∀ y, u (y * p.1) = u y := hp.1
    have hb : ∀ y, v (y * p.2) = v y := hp.2
    intro x
    simp only [Prod.fst_mul, Prod.snd_mul]
    rw [ha x.1, hb x.2]
  have hSi : S.index = (rStab u).index * (rStab v).index := Subgroup.index_prod _ _
  have hS0 : S.index ≠ 0 := by rw [hSi]; exact mul_ne_zero hu hv
  rw [_root_.GlobalTheory.BCT.avg_eq_of_le_rStab _ _ S hle hS0]
  haveI : (rStab u).FiniteIndex := ⟨hu⟩
  haveI : (rStab v).FiniteIndex := ⟨hv⟩
  haveI : S.FiniteIndex := ⟨hS0⟩
  letI : Fintype (H ⧸ rStab u) := Fintype.ofFinite _
  letI : Fintype (H' ⧸ rStab v) := Fintype.ofFinite _
  letI : Fintype ((H × H') ⧸ S) := Fintype.ofFinite _
  let f : (H × H') ⧸ S → (H ⧸ rStab u) × (H' ⧸ rStab v) :=
    fun q => ((q.out.1 : H ⧸ rStab u), (q.out.2 : H' ⧸ rStab v))
  have hf : Function.Bijective f := by
    constructor
    · intro q q' h
      simp only [f, Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      rw [QuotientGroup.eq] at h1 h2
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq]
      exact (Subgroup.mem_prod (H := rStab u) (K := rStab v)).2 ⟨by simpa using h1, by simpa using h2⟩
    · rintro ⟨a, b⟩
      induction a using QuotientGroup.induction_on with | H x => ?_
      induction b using QuotientGroup.induction_on with | H y => ?_
      refine ⟨((x, y) : (H × H') ⧸ S), ?_⟩
      have h := QuotientGroup.out_eq' ((x, y) : (H × H') ⧸ S)
      rw [QuotientGroup.eq] at h
      replace h := (Subgroup.mem_prod (H := rStab u) (K := rStab v)).1 h
      simp only [f, Prod.mk.injEq]
      rw [QuotientGroup.eq, QuotientGroup.eq]
      exact ⟨by simpa using h.1, by simpa using h.2⟩
  have hsum : ∑ᶠ q : (H × H') ⧸ S, (fun x : H × H' => u x.1 * v x.2) q.out =
      (∑ᶠ a : H ⧸ rStab u, u a.out) * ∑ᶠ b : H' ⧸ rStab v, v b.out := by
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.sum_mul_sum,
      ← Fintype.sum_prod_type']
    refine Fintype.sum_bijective f hf _ _ ?_
    intro q
    simp only [f, apply_out_rStab]
  rw [hsum]
  unfold avg
  rw [hSi]
  push_cast
  rw [mul_inv]
  ring

end GlobalTheory.AvgProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonEtaleCohomologyGenericFibreHenselian
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.GenFibreLine

theorem genericFibre_subsingleton : ∀ (q : ℕ) [NeZero q] (T : Type) [CommRing T] [IsDomain T] [IsLocalRing T], AIC T → IsUnit (q : T) → ∀ (A : Type) [CommRing A] [Algebra (Polynomial T) A] [Algebra T A] [IsScalarTower T (Polynomial T) A], SH A → GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap (Polynomial T) A) → ∀ n i : ℤ, 2 ≤ n → Subsingleton (Ht q (sp (TensorProduct T (FractionRing T) A)) n i) := by
  intro q _ T _ _ _ hA hq A _ _ _ _ _ hind n i hn
  haveI : IsAlgClosed (FractionRing T) := GlobalTheory.isAlgClosed_fractionRing_of_AIC T hA
  have hqK : IsUnit (q : FractionRing T) := by simpa using hq.map (algebraMap T (FractionRing T))
  have h2 := GlobalTheory.isIndEtale_tensorProduct_left (Polynomial T) A
    (TensorProduct T (Polynomial T) (FractionRing T)) hind
  let eX : TensorProduct (Polynomial T) (TensorProduct T (Polynomial T) (FractionRing T)) A ≃+*
      TensorProduct T (FractionRing T) A :=
    (Algebra.TensorProduct.comm (Polynomial T) _ A).toRingEquiv.trans
      ((Algebra.TensorProduct.cancelBaseChange T (Polynomial T) (Polynomial T) A (FractionRing T)).toRingEquiv.trans
        (Algebra.TensorProduct.comm T A (FractionRing T)).toRingEquiv)
  let eK : Polynomial (FractionRing T) ≃+* TensorProduct T (Polynomial T) (FractionRing T) :=
    (polyEquivTensor T (FractionRing T)).toRingEquiv.trans
      (Algebra.TensorProduct.comm T (FractionRing T) (Polynomial T)).toRingEquiv
  obtain ⟨J, _, _, D, t, s, hs, hst⟩ := h2
  let c : Cocone D := ⟨CommRingCat.of (TensorProduct T (FractionRing T) A),
    s ≫ (Functor.const J).map (CommRingCat.ofHom (eX : _ →+* _))⟩
  have hc : IsColimit c := hs.ofIsoColimit (Cocone.ext eX.toCommRingCatIso (fun j => rfl))
  have hqA : IsUnit (q : c.pt) := by
    simpa using hq.map (algebraMap T (TensorProduct T (FractionRing T) A))
  suffices h0 : ∀ x : Ht q (sp (TensorProduct T (FractionRing T) A)) n i, x = 0 from
    ⟨fun x y => by rw [h0 x, h0 y]⟩
  intro x
  obtain ⟨j, z, hz⟩ := (GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity q D c hc n i).1 x hqA
  let g : TensorProduct T (Polynomial T) (FractionRing T) →+* D.obj j := (t.app j).hom
  letI : Algebra (Polynomial (FractionRing T)) (D.obj j) := (g.comp eK.toRingHom).toAlgebra
  haveI : Algebra.Etale (Polynomial (FractionRing T)) (D.obj j) := by
    rw [← RingHom.etale_algebraMap]
    exact RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective eK.bijective) (hst j).1
  haveI := GlobalTheory.T.tateTwistCohomology_subsingleton_etale_over_polynomial_algClosed q (FractionRing T) (D.obj j) hqK n i hn
  rw [← hz, Subsingleton.elim z 0, map_zero]

end GlobalTheory.EtC.GenFibreLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThLInvolutive
section
open NumberField IsDedekindDomain Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC
open scoped Classical TensorProduct
open GlobalTheory.BCT

namespace GlobalTheory.BCT.TwistInvol

theorem cj_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (w : Pl E) (x : w.adicCompletion E) :
    cj w (cj w x) = x := by
  unfold cj
  split_ifs with h
  · obtain ⟨hc, he⟩ := h.choose_spec
    have hd : DenseRange (algebraMap E (w.adicCompletion E)) := HeightOneSpectrum.denseRange_algebraMap E w
    refine hd.induction_on (p := fun x => h.choose (h.choose x) = x) x
      (isClosed_eq (hc.comp hc) continuous_id) fun y => ?_
    rw [he, he, IsCMField.complexConj_apply_apply]
  · rfl

theorem thL_involutive : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (g : GLw n w),
    thL n w (thL n w g) = g := by
  intro E _ _ _ n w g
  unfold thL
  split_ifs
  · rfl
  · exact GlobalTheory.ThetaPull.thetaGL_thetaGL _ (cj_cj w) g

end GlobalTheory.BCT.TwistInvol
end

