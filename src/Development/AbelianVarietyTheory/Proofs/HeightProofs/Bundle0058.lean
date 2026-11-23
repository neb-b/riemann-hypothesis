module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.ConclOfInputs4
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0013
public import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0056
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0050
public import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ModulusPosOfThirdHypothesis

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFormFamilyHypothesesChangedSecondNorm
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

namespace GlobalTheory.NormMove

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (n : SecNorm B) {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

abbrev xT (X : PJ D B P j) : PJ D n.base P j := PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X

abbrev sT (S : Scal B) : Scal n.base := scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S

def gT (G : GlobalFamilyData X ka wL wF) : GlobalFamilyData (xT n X) ka wL wF where
  N := G.N
  w := G.w
  del := G.del
  th' := G.th'
  rz := G.rz
  alz := G.alz
  th0 := G.th0
  zc := G.zc
  rq := G.rq
  th := G.th
  iet := G.iet
  et := G.et
  mx := G.mx

section Structural

set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local irreducible]
  _root_.NumberField.RingOfIntegers _root_.CommRing.toCommSemiring _root_.NumberField.instCommRingRingOfIntegers _root_.AddCommGroup.toAddCommMonoid
  _root_.Submodule.span _root_.Set.range _root_.Submodule.map _root_.RingHom.id
  _root_.Semiring.toNonAssocSemiring _root_.instHSMul _root_.LinearMap.instSMul _root_.DistribMulAction.toDistribSMul
  _root_.CommRing.toCommMonoid _root_.LinearMap.id _root_.SetLike.instMembership _root_.Submodule.setLike
  _root_.Real.instLE _root_.Real.log _root_.Nat.cast _root_.Real.instNatCast
  _root_.instHMul _root_.Real.instMul _root_.instHSub _root_.Real.instSub
  Formalism.MainNotions.WeightFamilies.Wt.size _root_.One.toOfNat1 _root_.Real.instOne _root_.Semifield.toDivisionSemiring
  _root_.Field.toSemifield _root_.Complex.instSemiring _root_.instHDiv _root_.Real.instDivInvMonoid
  _root_.Finset.sum _root_.Real.instAddCommMonoid _root_.Finset.univ _root_.NumberField.Embeddings.instFintypeRingHom
  _root_.Complex.instField _root_.Fintype.card _root_.instHPow _root_.NPow.toPow
  _root_.Ring.toAddGroupWithOne _root_.instMulNat _root_.instOfNatNat _root_.Fin.instOfNat
  Formalism.BasicNotions.Ranks.f Formalism.BasicNotions.Ranks.r _root_.instLTNat Formalism.MainNotions.Gaps.EtaleWeightGaps.etWt
  _root_.Zero.toOfNat0 _root_.SubNegZeroMonoid.toNegZeroClass _root_.SubtractionMonoid.toSubNegZeroMonoid _root_.AddCommGroup.toDivisionAddCommMonoid
  _root_.instDistribOfSemiring _root_.Algebra.toModule _root_.LinearMap.instFunLike _root_.instMulZeroClassOfSemiring
  Formalism.MainNotions.WeightFamilies.PPv _root_.instHAdd _root_.Real.instAdd _root_.Set.instMembership
  _root_.Set.instInsert _root_.Set.instSingletonSet _root_.instOfNatAtLeastTwo Formalism.BasicNotions.Scale.L
  _root_.Real.instMax _root_.Module.finrank _root_.Rat.semiring _root_.Rat.commSemiring
  _root_.DivisionRing.toRatAlgebra _root_.Field.toDivisionRing _root_.abs _root_.Real.lattice
  _root_.Real.instAddGroup _root_.Int.cast _root_.Real.instIntCast _root_.NumberField.discr
  _root_.IntermediateField.toField _root_.Rat.instField
  _root_.IntermediateField.module' _root_.instSMulOfMul _root_.Rat.instMul Formalism.MainNotions.WeightAlgebra.lamStar
  Formalism.MainNotions.WeightAlgebra.Zb Formalism.MainNotions.Gaps.EtaleWeightGaps.PageGq Formalism.MainNotions.Gaps.EtaleWeightGaps.ShareRd _root_.Submodule.addCommMonoid
  _root_.Submodule.module _root_.FractionRing _root_.Localization.AtPrime _root_.MvPolynomial
  Formalism.MainNotions.Gaps.EtaleWeightGaps.Idx _root_.NumberField.RingOfIntegers.instAlgebra_1 _root_.IsFractionRing _root_.IsDedekindDomain.HeightOneSpectrum.adicCompletion.instField
  _root_.ValuationSubring.instSetLike _root_.IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers _root_.SubsemiringClass.toCommSemiring _root_.NonAssocRing.toNonAssocSemiring
  _root_.CommRing.toNonAssocCommRing _root_.AddMonoidAlgebra.commSemiring _root_.Nat.instMulZeroClass _root_.Finsupp.instAddCommMonoid
  _root_.Nat.instAddCommMonoid Formalism.DV.gaussIdeal _root_.ValuationSubring.instCommRingSubtypeMem _root_.Ideal
  _root_.AddMonoidAlgebra.semiring _root_.Finsupp.instAddMonoid _root_.Nat.instAddMonoid _root_.AddMonoidAlgebra.commRing
  _root_.Ideal.primeCompl _root_.OreLocalization.oreSetComm _root_.CommSemiring.toCommMonoid _root_.Semiring.toModule
  _root_.Semiring.toMonoidWithZero _root_.MulZeroOneClass.toMulZeroClass _root_.MonoidWithZero.toMulZeroOneClass _root_.Monoid.toMulAction
  _root_.NSMul.toSMul _root_.instAddNat _root_.OreLocalization.smul _root_.Monoid.toMulOneClass
  _root_.OreLocalization.npow _root_.Nat.unaryCast _root_.OreLocalization _root_.OreLocalization.instMonoidWithZero
  _root_.OreLocalization.instAddCommMonoidOreLocalization _root_.AddGroupWithOne.toAddGroup _root_.SubNegMonoid.sub' _root_.OreLocalization.instAddMonoid
  _root_.OreLocalization.instNegOreLocalization _root_.ZSMul.toSMul _root_.instOfNat _root_.instNatCastInt
  _root_.Int.castDef _root_.OreLocalization.instSemiring _root_.OreLocalization.instAddGroupOreLocalization _root_.TensorProduct
  _root_.IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion _root_.Algebra.id _root_.nonZeroDivisors _root_.DivInvMonoid.div'
  _root_.OreLocalization.inv' _root_.zpowRec _root_.npowRec _root_.ZPow.toPow
  _root_.NNRat.castRec _root_.OreLocalization.instRing _root_.GroupWithZero.toDivInvMonoid _root_.OreLocalization.instGroupWithZeroNonZeroDivisors
  _root_.NNRat _root_.Rat.castRec _root_.NNRat.cast _root_.NNRat.num
  _root_.NNRat.den _root_.OreLocalization.instDivisionRingNonZeroDivisors _root_.Rat.cast _root_.TensorProduct.addCommMonoid
  _root_.RingHom.toAlgebra _root_.IsFractionRing.lift _root_.ValuationSubring.instAlgebraSubtypeMem _root_.RingHom.comp
  _root_.OreLocalization.numeratorRingHom _root_.RingHom.instFunLike _root_.AddMonoidAlgebra.algebra _root_.TensorProduct.leftModule
  _root_.instAddTensorProduct._aux_1 _root_.Algebra.TensorProduct.instCommSemiring _root_.Algebra.TensorProduct.leftAlgebra _root_.instZeroTensorProduct._aux_1
  _root_.TensorProduct.leftHasSMul _root_.Nat.instMonoid _root_.Nat.instSemiring _root_.AddCommMonoid.toNatModule
  _root_.TensorProduct.instModule _root_.LinearMap.addCommMonoid _root_.LinearMap.module _root_.TensorProduct.tmul
  _root_.AddCommMonoidWithOne.toAddCommMonoid _root_.NonAssocSemiring.toAddCommMonoidWithOne _root_.npowRecAuto _root_.NonAssocSemiring.toMulZeroOneClass
  _root_.Algebra.TensorProduct.instNonAssocSemiring _root_.Ring.toAddCommGroup _root_.TensorProduct.Neg.aux _root_.TensorProduct.neg
  _root_.Int.instMonoid _root_.Int.instSemiring _root_.AddCommGroup.toIntModule _root_.AddCommGroupWithOne.toAddCommMonoidWithOne
  _root_.NonAssocRing.toAddCommGroupWithOne _root_.Ring.toNonAssocRing _root_.AddCommGroupWithOne.toAddGroupWithOne _root_.Algebra.TensorProduct.instSemiring
  _root_.Algebra.TensorProduct.includeLeftRingHom _root_.Set.ofPred Formalism.MainNotions.WeightFamilies.dimY Formalism.MainNotions.WeightAlgebra.wadd
  Formalism.MainNotions.WeightAlgebra.wsmul _root_.Fin.fintype Formalism.MainNotions.Gaps.EtaleWeightGaps.a0 _root_.Finset.prod
  _root_.MvPolynomial.X _root_.Algebra.TensorProduct.includeRight _root_.Algebra.TensorProduct.instAlgebra _root_.Fin.succ
  _root_.Real.instMonoid Formalism.MainNotions.Gaps.EtaleWeightGaps.ShareRhoP _root_.Submodule.hasQuotient _root_.Submodule.addCommGroup
  _root_.Submodule.comap _root_.Submodule.subtype _root_.Submodule.restrictScalars _root_.AddMonoid.toAddZeroClass
  _root_.iInf _root_.Submodule.instInfSet Formalism.MainNotions.WeightFamilies.rho _root_.Pi.addCommMonoid
  _root_.Pi.Function.module Formalism.MainNotions.WeightFamilies.dualZ _root_.Pi.instZero _root_.ZeroMemClass.zero
  _root_.IntermediateField.instSetLike Formalism.MainNotions.WeightFamilies.trF Formalism.MainNotions.WeightFamilies.hform Formalism.MainNotions.WeightFamilies.c1
  _root_.LinearMap.ker _root_.Submodule.Quotient.addCommMonoid _root_.Submodule.Quotient.module Formalism.MainNotions.WeightAlgebra.cc
  _root_.Real.instZero Formalism.MainNotions.WeightFamilies.PP0v _root_.Real.instPow Formalism.MainNotions.WeightFamilies.RRv
  Formalism.BasicNotions.Host.rdE Formalism.MainNotions.WeightAlgebra.PO _root_.LinearIndependent _root_.Localization.Away
  _root_.Submonoid.powers _root_.Subalgebra.instSetLike _root_.Algebra.adjoin Formalism.MainNotions.Gaps.EtaleWeightGaps.addL
  _root_.IsLocalization.Away.invSelf _root_.IsLocalization.Away Formalism.MainNotions.Gaps.EtaleWeightGaps.wt0 _root_.Subalgebra.toSemiring
  _root_.Subalgebra.moduleLeft _root_.Subalgebra.toRing _root_.Submodule.instSMul _root_.Submodule.smul
  _root_.Ideal.span Formalism.MainNotions.Gaps.EtaleWeightGaps.frMap _root_.Submodule.instTop _root_.Submodule.Quotient.addMonoid._aux_1
  _root_.Subalgebra.instMulActionSubtypeMem _root_.Quotient.mk'' _root_.Submodule.quotientRel _root_.Submodule.Quotient.instSMul'
  _root_.Submodule.Quotient.addCommGroup._aux_1 _root_.Submodule.Quotient.addCommGroup._aux_3 _root_.Quotient.map' _root_.Submodule.module'
  _root_.Subalgebra.algebra _root_.Subalgebra.instSMulSubtypeMem _root_.AddCommSemigroup.toAddCommMagma _root_.AddCommMonoid.toAddCommSemigroup
  _root_.LinearMap.comp _root_.LinearMap.restrictScalars _root_.Submodule.mkQ _root_.LinearMap.codRestrict
  _root_.LinearMap.domRestrict _root_.Submodule.instPartialOrder _root_.Set.image _root_.Set.instMax
  _root_.instSubNat _root_.EReal _root_.instPartialOrderEReal _root_.instZeroEReal
  _root_.instTopEReal _root_.instInfSetEReal _root_.Real.toEReal _root_.EReal.toReal
  _root_.instLENat _root_.FiniteDimensional _root_.Ideal.instHasQuotient_1 _root_.Subalgebra.toCommRing
  _root_.Ideal.Quotient.ring._aux_1 _root_.Submodule.Quotient.mk _root_.Ideal.Quotient.ring._aux_6 _root_.Ideal.Quotient.ring._aux_14
  _root_.Ideal.Quotient.ring._aux_23 _root_.Ideal.instHasQuotient _root_.Ideal.Quotient.ring _root_.Ideal.Quotient.mk
  Formalism.MainNotions.Gaps.EtaleWeightGaps.IsGen _root_.Submodule.Quotient.addCommGroup _root_.AddMonoidHom.instFunLike _root_.QuotientAddGroup.instHasQuotientAddSubgroup
  _root_.Submodule.toAddSubgroup _root_.QuotientAddGroup.Quotient.addGroup _root_.AddMonoidHom.instAddCommGroup _root_.QuotientAddGroup.lift
  _root_.smulAddHom Formalism.MainNotions.Gaps.EtaleWeightGaps.Pts _root_.instBotEReal Formalism.MainNotions.Gaps.EtaleWeightGaps.ep
  _root_.Classical.choose _root_.EReal.instMul _root_.instAddCommMonoidWithOneEReal Formalism.MainNotions.Gaps.EtaleWeightGaps.toE
  Formalism.MainNotions.Gaps.EtaleWeightGaps.ord _root_.AlgHom.funLike _root_.Ideal.Quotient.mkₐ _root_.EReal.instSubNegZeroMonoid
  Formalism.MainNotions.Gaps.EtaleWeightGaps.ordV _root_.WithTop _root_.Module.compHom Formalism.MainNotions.Gaps.EtaleWeightGaps.ballO
  _root_.Submodule.instPowNat _root_.Subalgebra.toCommSemiring _root_.Finsupp.sum _root_.OreLocalization.instModuleOfIsScalarTower
  Formalism.MainNotions.Gaps.EtaleWeightGaps.Tay.hs _root_.OreLocalization.instCommRing _root_.OreLocalization.instAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps.Tay.loc
  _root_.IsLocalization _root_.Localization _root_.OreLocalization.instCommSemiring _root_.Algebra.TensorProduct.instCommRing
  _root_.MvPowerSeries.instSemiring _root_.MvPowerSeries.instAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps.Tay.tens _root_.IsLocalization.AtPrime
  Formalism.MainNotions.Gaps.EtaleWeightGaps.Tay.pol _root_.AddMonoidAlgebra.nonAssocSemiring _root_.Finsupp.instAddZeroClass Formalism.MainNotions.Gaps.EtaleWeightGaps.Tay.IsTay
  Formalism.MainNotions.Gaps.EtaleWeightGaps.Tay.IsCst _root_.WithTop.instPreorder _root_.ConditionallyCompleteLattice.toConditionallyCompletePartialOrder _root_.Int.instConditionallyCompleteLinearOrder
  _root_.WithTop.some _root_.Int.instNegInt _root_.ENat _root_.Module.length
  _root_.instTopENat _root_.Summable _root_.Real.pseudoMetricSpace _root_.ENat.toNat
  Formalism.BasicNotions.lw _root_.SummationFilter.unconditional _root_.tsum Formalism.MainNotions.Gaps.EtaleWeightGaps.fdeg
  Formalism.MainNotions.WeightAlgebra.g0

def qT {G : GlobalFamilyData X ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G la) : LocalPointData (gT n G) la where
  y := Q.y
  g0 := Q.g0
  c := Q.c

variable (G : GlobalFamilyData X ka wL wF) (S : Scal B)

set_option maxHeartbeats 4000000 in
theorem shareRhoR_iff (T d : ℕ) : ShareRhoR (gT n G) (sT n S) T d ↔ ShareRhoR G S T d := Iff.rfl

set_option maxHeartbeats 4000000 in
theorem inBasis_iff (la : HeightOneSpectrum (𝓞 B.KO)) : InBasis (gT n G) la ↔ InBasis G la := Iff.rfl

set_option maxHeartbeats 4000000 in
theorem inContainMR_iff (la : HeightOneSpectrum (𝓞 B.KO)) (CRm : ℝ) (T : ℕ) (c : ℝ) :
    InContainMR (gT n G) la (sT n S) CRm T c ↔ InContainMR G la S CRm T c := Iff.rfl

variable {G}

set_option maxHeartbeats 4000000 in
theorem inCurve_iff {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G la) : (qT n Q).InCurve ↔ Q.InCurve := Iff.rfl

set_option maxHeartbeats 4000000 in
theorem inTie_iff {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G la) : (qT n Q).InTie (sT n S) ↔ Q.InTie S := Iff.rfl

set_option maxHeartbeats 4000000 in
theorem inLift_iff {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G la) (T : ℕ) : (qT n Q).InLift T ↔ Q.InLift T := Iff.rfl

set_option maxHeartbeats 4000000 in
theorem heights_iff (Qf : ∀ la, LocalPointData G la) (Gc PH Prw Pet : ℝ) :
    Heights (fun la => qT n (Qf la)) Gc PH Prw Pet ↔ Heights Qf Gc PH Prw Pet := Iff.rfl

end Structural

variable (G : GlobalFamilyData X ka wL wF) (S : Scal B)

set_option maxHeartbeats 4000000 in
theorem tiedW_iff (Gc Prw : ℝ) : (gT n G).TiedW (sT n S) Gc Prw ↔ G.TiedW S Gc Prw := Iff.rfl

set_option maxHeartbeats 4000000 in
theorem tiedTh_iff (Gc : ℝ) : (gT n G).TiedTh (sT n S) Gc ↔ G.TiedTh S Gc := Iff.rfl

set_option maxHeartbeats 4000000 in
theorem tiedEt_iff (large₂ : SizeData₂ D) (Cf Af : ℝ) : (gT n G).TiedEt large₂ Cf Af ↔ G.TiedEt large₂ Cf Af := Iff.rfl

set_option maxHeartbeats 4000000 in
theorem combBound_iff (c : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) :
    CombBound (gT n G) (sT n S) c nus ↔ CombBound G S c nus := Iff.rfl

variable {G} in
theorem inLiftC_of {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G la) (Gc Prw : ℝ) (T : ℕ) (h : Q.InLiftC S Gc Prw T) :
    (qT n Q).InLiftC (sT n S) Gc Prw T := fun a b c =>
  (inLift_iff n Q T).2 (h ((tiedW_iff n G S Gc Prw).1 a) ((inCurve_iff n Q).1 b) ((inTie_iff n S Q).1 c))


set_option maxHeartbeats 4000000 in
theorem famIn_move (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR : ℝ) (Tn : ℕ) (Gc PH Prw Pet Pd : ℝ)
    (h : FamIn large₂ K H Ch Ah Cq Aq C2 A2 CR S Tn G Gc PH Prw Pet Pd) :
    FamIn large₂ K H Ch Ah Cq Aq C2 A2 CR (sT n S) Tn (gT n G) Gc PH Prw Pet Pd := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := h
  exact ⟨(tiedW_iff n G S Gc Prw).2 a1, (tiedTh_iff n G S Gc).2 a2, (tiedEt_iff n G large₂ _ _).2 a3, a4, a5, a6, a7,
    (shareRhoR_iff n G S _ _).2 a8, a9, a10, fun la => (inBasis_iff n G la).2 (a11 la),
    fun la => (inContainMR_iff n G S la _ _ _).2 (a12 la)⟩


set_option maxHeartbeats 4000000 in
theorem ptIn_move (Tn : ℕ) (c Gc PH Prw Pet : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ)
    (h : PtIn S Tn G c Gc PH Prw Pet nus) : PtIn (sT n S) Tn (gT n G) c Gc PH Prw Pet nus := by
  obtain ⟨a1, Qf, a2, a3, a4, a5⟩ := h
  exact ⟨(combBound_iff n G S c nus).2 a1, fun la => qT n (Qf la), fun la => (inCurve_iff n (Qf la)).2 (a2 la),
    fun la => (inTie_iff n S (Qf la)).2 (a3 la), fun la => inLiftC_of n S (Qf la) Gc Prw Tn (a4 la),
    (heights_iff n Qf Gc PH Prw Pet).2 a5⟩


set_option maxHeartbeats 4000000 in
set_option linter.unusedVariables false in
theorem exists_famIn_ptIn : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) (n : SecNorm B) (G : GlobalFamilyData X ka wL wF) (Gc PH Prw Pet Pd c : ℝ), FamIn large₂ K H Ch Ah Cq Aq C2 A2 CR S Tn G Gc PH Prw Pet Pd → PtIn S Tn G c Gc PH Prw Pet nus → ∃ G' : GlobalFamilyData (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X) ka wL wF, FamIn large₂ K H Ch Ah Cq Aq C2 A2 CR (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S) Tn G' Gc PH Prw Pet Pd ∧ PtIn (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S) Tn G' c Gc PH Prw Pet nus :=
  fun _ _ _ _ _ large₂ K H Ch Ah Cq Aq C2 A2 CR _ S _ _ _ Tn _ _ _ nus n G Gc PH Prw Pet Pd c hF hP =>
    ⟨gT n G, famIn_move n G S large₂ K H Ch Ah Cq Aq C2 A2 CR Tn Gc PH Prw Pet Pd hF, ptIn_move n G S Tn c Gc PH Prw Pet nus hP⟩

end GlobalTheory.NormMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.IndexBoundConstantLePagePolynomialOfRunCondition
section
set_option autoImplicit false

namespace GlobalTheory.FinalJoin

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

theorem indexBound_threeTerm_constant_le_real (n m4 u r C Z : ℝ) (hZ : 2000 ≤ Z) (hC : 1 ≤ C) (hn0 : 0 ≤ n) (hn : n ≤ C * Z ^ 4)
    (hm0 : 0 ≤ m4) (hm : m4 ≤ Z) (hu1 : 1 ≤ u) (hu : u ^ 4 ≤ 16 * Z ^ 5) (hr : r ≤ Z) :
    max (16200 * Real.pi * n * m4 * u ^ 4) (max (u ^ 4 * n + 2 * u ^ 3) (r * u ^ 3)) ≤ C * Z ^ 12 := by
  have hZ1 : (1 : ℝ) ≤ Z := by linarith
  have hZ0 : (0 : ℝ) ≤ Z := by linarith
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have hu0 : (0 : ℝ) ≤ u := by linarith
  have h34 : u ^ 3 ≤ 16 * Z ^ 5 := (pow_le_pow_right₀ hu1 (by norm_num)).trans hu
  have hZ2 : (4000000 : ℝ) ≤ Z ^ 2 := by nlinarith
  have hW0 : 0 ≤ C * Z ^ 10 := by positivity
  have hW : 4000000 * (C * Z ^ 10) ≤ C * Z ^ 12 := by
    calc 4000000 * (C * Z ^ 10) ≤ Z ^ 2 * (C * Z ^ 10) := mul_le_mul_of_nonneg_right hZ2 hW0
      _ = C * Z ^ 12 := by ring
  have hk : ∀ k : ℕ, k ≤ 10 → Z ^ k ≤ C * Z ^ 10 := fun k hk =>
    (pow_le_pow_right₀ hZ1 hk).trans (le_mul_of_one_le_left (by positivity) hC)
  refine max_le ?_ (max_le ?_ ?_)
  · have hpi : Real.pi ≤ 4 := Real.pi_le_four
    have hpi0 : 0 ≤ Real.pi := Real.pi_pos.le
    calc 16200 * Real.pi * n * m4 * u ^ 4 ≤ 16200 * 4 * (C * Z ^ 4) * Z * (16 * Z ^ 5) := by gcongr
      _ = 1036800 * (C * Z ^ 10) := by ring
      _ ≤ C * Z ^ 12 := by linarith
  · have a1 : u ^ 4 * n ≤ (16 * Z ^ 5) * (C * Z ^ 4) := by gcongr
    have a2 : C * Z ^ 9 ≤ C * Z ^ 10 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hZ1 (by norm_num)) hC0
    have a3 := hk 5 (by norm_num)
    have a4 : (16 * Z ^ 5) * (C * Z ^ 4) = 16 * (C * Z ^ 9) := by ring
    linarith
  · have a1 : r * u ^ 3 ≤ Z * (16 * Z ^ 5) := by gcongr
    have a3 := hk 6 (by norm_num)
    have a4 : Z * (16 * Z ^ 5) = 16 * Z ^ 6 := by ring
    linarith

theorem indexBoundConstant_le_pagePolynomial_of_runConditions : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), InR D j → PageRun large₂ X H C2 A2 CT ka wL wF Tn nP nW h0 → flipOneThree D nW ≤ WeightFamilies.PPv D large₂ C2 A2 := by
  intro D B P j X large₂ H C2 A2 CT ka wL wF Tn nP nW h0 _ hP
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hnW, -, -, -, -, -, -, -, -, -, -, -, -, -, hd⟩ := hP.hyp.2.1
  rw [hP.tie.1] at hd
  have hA : 12 ≤ A2 := hP.tie.2.2.2.2.2
  obtain ⟨hC, hCZ, -, -, -, -, -, -, h12, -⟩ := hd
  have e : Zb D large₂ = zBase large₂ := rfl
  rw [e] at hCZ h12
  have hZ : 2000 ≤ zBase large₂ := by
    have h1 : (1000 : ℝ) ^ 20 ≤ C2 ^ 20 := pow_le_pow_left₀ (by norm_num) hC 20
    have h2 : (2000 : ℝ) ≤ 1000 ^ 20 := by norm_num
    linarith
  have hL : 1 ≤ large₂.sc.L := by
    unfold Scale.L; exact Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hfr : (D.R.f : ℝ) * D.R.r ≤ zBase large₂ := by
    unfold zBase
    exact le_mul_of_one_le_right (by positivity) hL
  have hm1 : (1 : ℝ) ≤ (D.R.m : ℝ) := by
    have : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
    exact_mod_cast this
  have hr1 : (1 : ℝ) ≤ (D.R.r : ℝ) := by
    have : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
    exact_mod_cast this
  have hf8 : (8 : ℝ) ≤ (D.R.f : ℝ) := by exact_mod_cast D.eight_le_f
  have hf : (D.R.f : ℝ) ≤ zBase large₂ := (le_mul_of_one_le_right (by positivity) hr1).trans hfr
  have hr : (D.R.r : ℝ) ≤ zBase large₂ := (le_mul_of_one_le_left (by positivity) (by linarith)).trans hfr
  have hm : (D.R.m : ℝ) ^ 4 ≤ zBase large₂ := (lift_index_pow_four_le_degree hP.page).trans hf
  have hu1 : 1 ≤ 2 * (D.R.f : ℝ) * (D.R.m : ℝ) := by nlinarith
  have hu : (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 4 ≤ 16 * zBase large₂ ^ 5 := by
    calc (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 4 = 16 * ((D.R.f : ℝ) ^ 4 * (D.R.m : ℝ) ^ 4) := by ring
      _ ≤ 16 * (zBase large₂ ^ 4 * zBase large₂) := by gcongr
      _ = 16 * zBase large₂ ^ 5 := by ring
  have key := indexBound_threeTerm_constant_le_real (nW : ℝ) ((D.R.m : ℝ) ^ 4) (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) (D.R.r : ℝ) C2 (zBase large₂) hZ
    (by linarith) (Nat.cast_nonneg _) (hnW.trans h12) (by positivity) hm hu1 hu hr
  have hZA : zBase large₂ ^ (12 : ℕ) ≤ zBase large₂ ^ A2 := by
    calc zBase large₂ ^ (12 : ℕ) = zBase large₂ ^ ((12 : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ zBase large₂ ^ A2 := Real.rpow_le_rpow_of_exponent_le (by linarith) (by exact_mod_cast hA)
  unfold flipOneThree WeightFamilies.PPv
  exact key.trans (mul_le_mul_of_nonneg_left hZA (by linarith))

end GlobalTheory.FinalJoin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.OrthogonalLowerDegreeKernelTranslatesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthogonal_lowerDegree_kernel_translates : ∀ {n : ℕ} (ε : Fin n → Bool) (i : ℕ) (p κ : KG ε → ℂ), κ ∈ lowV ε i → (∀ q ∈ lowV ε i, ∫ k, q k * p k ∂(muK ε) = 0) → ∀ k : KG ε, ∫ x, star (p x) * κ (x⁻¹ * k) ∂(muK ε) = 0 := by
  first | exact @GlobalTheory.KFourier.orth_translate_lowV | exact GlobalTheory.KFourier.orth_translate_lowV | (intros; apply GlobalTheory.KFourier.orth_translate_lowV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.PageRunSqLeRdAndEightLeRank
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

namespace GlobalTheory.FinalJoin

theorem pageRun_sq_le_rd_and_eight_le_rank : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), InR D j → PageRun large₂ X H C2 A2 CT ka wL wF Tn nP nW h0 → (D.R.f : ℝ) ^ 2 ≤ D.host.rdE ∧ 8 ≤ D.R.r := by
  intro D B P j X large₂ H C2 A2 CT ka wL wF Tn nP nW h0 _ h
  obtain ⟨Q, _, hS, -, -⟩ := h.page
  have h1 := host_f_sq_le_rd Q
  rw [hostSize_f, hostSize_rd] at h1
  refine ⟨h1, ?_⟩
  have hm4 := host_m_pow_four_le_f hS
  rw [hostSize_f] at hm4
  have hm2 := D.R.two_le_m
  have h16 : 16 ≤ D.R.f := by
    have : 2 ^ 4 ≤ D.R.m ^ 4 := Nat.pow_le_pow_left hm2 4
    omega
  have h2 := D.R.f_le_k
  unfold Ranks.f Ranks.n at *
  unfold Ranks.r
  omega

end GlobalTheory.FinalJoin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.SecNormOfNetIn
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

namespace GlobalTheory.FinalJoin

theorem secNorm_of_netIn : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (K : KAdm) (ka : WeightFamilies.Wt D j) (Pd : ℝ), NetIn large₂ B j ka K Pd → ∃ n : SecNorm B, SupBoundByL2AtWeight large₂ n.base j ka K.CG K.AG ∧ DeepHerm (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X) ka ∧ DeepLogD (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 X) ka Pd := by
  intro D B P j X large₂ K ka Pd h
  obtain ⟨Nt, σ₀, hM, hL, hP, hI, hd⟩ := h
  refine ⟨⟨(Nt.Bp hM hL).l2NormAlt, (Nt.Bp hM hL).l2Norm_nonneg_bis, (Nt.Bp hM hL).l2Norm_eq_zero_iff, (Nt.Bp hM hL).l2Norm_smul_alt,
    (Nt.Bp hM hL).l2Norm_add_le', (Nt.Bp hM hL).l2Norm_le_supNorm_alt⟩, NetNorms.sup_L2_bound_of_net Nt hM hL large₂ _ _ hP, ?_, ?_⟩
  · exact NetNorms.deepHermNet P Nt hM hL _
  · exact NetNorms.deepLogDNet P Nt hM hL (PJ.tol2NormAlt _ _ _ _ _ _ X) σ₀ Pd hI hd

end GlobalTheory.FinalJoin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ThreeLeDFOfPageRun
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FinalJoin

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

theorem three_le_DF_of_SetC {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {large₂ : SizeData₂ D} {X : PJ D B P j}
    {CK C1 A1 : ℝ} {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} {h0 : ℝ}
    (h : SetC large₂ X CK C1 A1 ka wL wF T nP nW h0) : 3 ≤ DF wL := by
  have hh := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hL, -, -, hT, -, h40, hnW, -⟩ := hh
  have hp : 0 < (D.R.sigW j).1 := by
    have := D.R.m_add_three_le_k
    show 0 < D.R.k + j - 1
    omega
  have hτ : Nonempty D.what₂.Tau := by
    rw [← Fintype.card_pos_iff, D.what₂.card_Tau]
    have hm := D.R.two_le_m
    have hf := D.R.m_le_f
    unfold Ranks.f Ranks.n
    omega
  obtain ⟨τ⟩ := hτ
  set i : Fin (D.R.sigW j).1 := ⟨(D.R.sigW j).1 - 1, by omega⟩ with hi
  have hi1 : i.1 + 1 = (D.R.sigW j).1 := by simp only [hi]; omega
  have h2 := two_T_sq_le_last h τ i hi1
  have h3 := hL.2.1 τ i
  have hn : ¬ i.1 + 1 < (D.R.sigW j).1 := by omega
  rw [if_neg hn] at h3
  unfold gapZ at h3
  rw [dite_eq_right hn] at h3
  have hTp : (0 : ℤ) < (Tp D j T : ℤ) := by unfold Tp; positivity
  rw [Int.fdiv_eq_ediv_of_nonneg _ hTp.le] at h3
  have h4 : (3 : ℤ) ≤ ((ka.aP τ i : ℤ) - ((WeightFamilies.dimY D j : ℤ) + 2) * nW - 2 * D.R.r) / (Tp D j T : ℤ) := by
    rw [Int.le_ediv_iff_mul_le hTp]
    unfold Tp
    have e1 : (2 * (T : ℤ) ^ 2) ≤ (ka.aP τ i : ℤ) := by exact_mod_cast h2
    have e2 : ((WeightFamilies.dimY D j : ℤ) + 2) * nW + 2 * D.R.r ≤ T := by exact_mod_cast hnW
    have e3 : 40 * ((WeightFamilies.dimY D j : ℤ) + 2) ≤ T := by exact_mod_cast h40
    have e4 : (0 : ℤ) ≤ (WeightFamilies.dimY D j : ℤ) := Int.natCast_nonneg _
    have e5 : (80 : ℤ) ≤ T := by linarith
    have e6 : 80 * (T : ℤ) ≤ (T : ℤ) ^ 2 := by nlinarith
    push_cast
    linarith
  have h5 : 3 ≤ wL.aP τ i := by
    rw [← h3] at h4; exact_mod_cast h4
  unfold WeightAlgebra.DF degP
  calc 3 ≤ wL.aP τ i := h5
    _ ≤ ∑ i, wL.aP τ i := Finset.single_le_sum (f := fun i => wL.aP τ i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    _ ≤ (∑ i, wL.aP τ i) + ∑ i, wL.aM τ i := Nat.le_add_right _ _
    _ ≤ _ := Finset.single_le_sum (f := fun τ => (∑ i, wL.aP τ i) + ∑ i, wL.aM τ i) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ τ)

theorem three_le_DF_of_pageRun : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), InR D j → PageRun large₂ X H C2 A2 CT ka wL wF Tn nP nW h0 → 3 ≤ DF wL :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => three_le_DF_of_SetC h.hyp.2.1

end GlobalTheory.FinalJoin
end
end

