module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0609
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0038
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0053
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0445
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0613
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0607
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0067
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0608
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2814
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1603
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0423
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0424
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0588
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0485
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0518
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0056

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KerPolarizationProjectionStableUnderStabilizerCo
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.SquareAgree.KerStabCpt
theorem stabilizer_compact_mem_ker_polarizationProjection : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Γ.W Bs.emb, ∀ Φ ∈ kerPD ψ θ A₁ B Bs Γ cB p', om' (1, k) Φ ∈ kerPD ψ θ A₁ B Bs Γ cB p' := by
  intro hPr D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hT Pi rf rl p p' hM k hk Φ hΦ
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hO.psi ▸ hT.base.std
  obtain ⟨γ, hγ, h1, hK⟩ := _root_.GlobalTheory.CompactLine.exists_line_in_kInf_skew D.host.F D.host.E D.sp.cm.sig Bs _ Γ.W _ _ hT.base hT.geo.hW k hk
  rw [← h1]
  have hAlg : Φ ∈ GlobalTheory.ThK.PolData Bs Γ.M' := by
    rw [← algD_eq_polData]
    exact ((mem_kerPD hstd θ A₁ B Bs Γ cB p' Φ).1 hΦ).1
  refine _root_.GlobalTheory.T.stabilizer_of_K_exponential_line hPr D.host.F D.host.E D.sp.cm.sig Bs _ _ Γ.V' Γ.W Γ.M' _ _ om' _ _ _ _ (isPair_small' hT) γ hγ hK
    (kerPD ψ θ A₁ B Bs Γ cB p') (fun Ψ hΨ Ψ₁ hΨ₁ hd => ?_) Φ hΦ hAlg
  rw [← algD_eq_polData] at hΨ₁
  exact _root_.GlobalTheory.T.ker_polarizationProjection_stable_under_stabilizer_lie hPr D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hT Pi rf rl p p' hM
    γ hγ Ψ hΨ Ψ₁ hΨ₁ hd
end GlobalTheory.SquareAgree.KerStabCpt
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_polarizationProjection_stable_under_stabilizer_compact : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Γ.W Bs.emb, ∀ Φ ∈ kerPD ψ θ A₁ B Bs Γ cB p', om' (1, k) Φ ∈ kerPD ψ θ A₁ B Bs Γ cB p' := by
  first | exact @_root_.GlobalTheory.SquareAgree.KerStabCpt.stabilizer_compact_mem_ker_polarizationProjection | exact _root_.GlobalTheory.SquareAgree.KerStabCpt.stabilizer_compact_mem_ker_polarizationProjection | (intros; apply _root_.GlobalTheory.SquareAgree.KerStabCpt.stabilizer_compact_mem_ker_polarizationProjection <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MovedVacuumJetAlgebraicCombination
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section
namespace GlobalTheory.MovedJet
open GlobalTheory.Grid (neg sgn ofSgn)
open MvPolynomial
end GlobalTheory.MovedJet
namespace GlobalTheory.MovedJet
open GlobalTheory.Grid (neg sgn ofSgn)
open MvPolynomial
end GlobalTheory.MovedJet
namespace GlobalTheory.MovedJet
open GlobalTheory.Grid (neg sgn ofSgn)
open MvPolynomial
theorem jet_moved_vacuum_algebraic : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∀ k : FVar D WW.rank A.rank →₀ ℕ, ∃ (n : ℕ) (c : Fin n → ℂ) (k' : Fin n → FVar D WW.rank A.rank →₀ ℕ),
        (∀ p, IsAlgebraic ℚ (c p)) ∧ (∀ p, Finsupp.mapDomain Prod.fst (k' p) = Finsupp.mapDomain Prod.fst k) ∧
        pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.ω t (γ, γ') X.vac) (MvPolynomial.monomial k 1) 0 = ∑ p, c p * pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.vac) (MvPolynomial.monomial (k' p) 1) 0 := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ _ hX t γ hγ a _ γ' hγ' a' _ _ _ k
  have hI := hX.is
  have hθ : IsInfFam W.θ := hI.isVac.2.inf
  have hom := hI.weil t
  set u : D.what₂.Tau → Matrix (Fin A.rank) (Fin A.rank) ℂ := fun τ => compAt W.θ τ (Formalism.L2.Theta.mt A γ) with hu
  set hm : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ :=
    fun τ => (compAt W.θ τ (Formalism.L2.Theta.mt WW γ')).map (starRingEnd ℂ) with hhm
  set H : D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ := fun τ => Matrix.conjTranspose (hm τ) with hH
  set U : D.what₂.Tau → Matrix (Fin A.rank) (Fin A.rank) ℂ := fun τ => Matrix.conjTranspose (u τ) with hU
  set Q := GlobalTheory.CompactHowe.substF H U (MvPolynomial.monomial k 1) with hQdef
  have hHm : hm * H = fun _ => 1 := funext fun τ =>
    map_conj_mul_conjT (mul_conjT_of_unitary (conjT_mul_compAt hθ hX.stdW.1 γ' τ))
  have hUm : u * U = fun _ => 1 := funext fun τ => mul_conjT_of_unitary (conjT_mul_compAt hθ hX.std.1 γ τ)
  have hQ : GlobalTheory.CompactHowe.substF hm u Q = MvPolynomial.monomial k 1 := by
    rw [hQdef, GlobalTheory.CompactHowe.substF_mul, hHm, hUm, substF_one]
  have hact := om_pureTensorO_vac hX t γ γ' Q
  have hjet : pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.ω t (γ, γ') X.vac)
        (MvPolynomial.monomial k 1) 0 =
      pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac Q 0 := by
    rw [← hQ]
    change pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B
      ((X.ω t).toSgn true ((ofSgn true A).symm γ, γ') X.vac) _ 0 = _
    rw [← hact.2]
    exact hom.om_aut _ (GlobalTheory.SquareComm.ofSgn_symm_mem_GQ true hγ) γ' hγ' _ hact.1
  have hHalg : ∀ τ a b, IsAlgebraic ℚ (H τ a b) := by
    intro τ a b
    have e : H τ a b = compAt W.θ τ (Formalism.L2.Theta.mt WW γ') b a := by
      simp [hH, hhm, Matrix.conjTranspose_apply]
    rw [e]
    exact isAlgebraic_compAt_of_mem_GQ hθ hγ' τ b a
  have hUalg : ∀ τ a b, IsAlgebraic ℚ (U τ a b) := by
    intro τ a b
    have e : U τ a b = starRingEnd ℂ (compAt W.θ τ (Formalism.L2.Theta.mt A γ) b a) := by
      simp [hU, hu, Matrix.conjTranspose_apply]
    rw [e]
    exact isAlgebraic_conj (isAlgebraic_compAt_of_mem_GQ hθ hγ τ b a)
  let e := Q.support.equivFin
  refine ⟨Q.support.card, fun p => AddMonoidAlgebra.coeff Q (e.symm p).1, fun p => (e.symm p).1, fun p => ?_, fun p => ?_, ?_⟩
  · exact (GlobalTheory.SubstCoeff.coeff_substF_monomial_continuous_algebraic k (e.symm p).1).2 H U hHalg hUalg
  · exact GlobalTheory.CompactHowe.mapDomain_fst_eq_of_coeff_substF_ne_zero H U k (e.symm p).1
      (MvPolynomial.mem_support_iff.1 (e.symm p).2)
  · rw [hjet]
    calc pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac Q 0
        = ∑ x ∈ Q.support, AddMonoidAlgebra.coeff Q x *
            pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac (MvPolynomial.monomial x 1) 0 := by
          conv_lhs => rw [Q.as_sum]
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum, Finset.sum_apply]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [show MvPolynomial.monomial x (AddMonoidAlgebra.coeff Q x) = AddMonoidAlgebra.coeff Q x • MvPolynomial.monomial x 1 by
            rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], map_smul, Pi.smul_apply, smul_eq_mul]
      _ = _ := by
          rw [← Finset.sum_coe_sort]
          exact (Equiv.sum_comp e.symm (fun x : Q.support => AddMonoidAlgebra.coeff Q x.1 *
            pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B X.vac (MvPolynomial.monomial x.1 1) 0)).symm
end GlobalTheory.MovedJet
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moved_vacuum_jet_algebraic_combination : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∀ k : FVar D WW.rank A.rank →₀ ℕ, ∃ (n : ℕ) (c : Fin n → ℂ) (k' : Fin n → FVar D WW.rank A.rank →₀ ℕ),
        (∀ p, IsAlgebraic ℚ (c p)) ∧ (∀ p, Finsupp.mapDomain Prod.fst (k' p) = Finsupp.mapDomain Prod.fst k) ∧
        pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.ω t (γ, γ') X.vac) (MvPolynomial.monomial k 1) 0 = ∑ p, c p * pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.vac) (MvPolynomial.monomial (k' p) 1) 0 := by
  first | exact @_root_.GlobalTheory.MovedJet.jet_moved_vacuum_algebraic | exact _root_.GlobalTheory.MovedJet.jet_moved_vacuum_algebraic | (intros; apply _root_.GlobalTheory.MovedJet.jet_moved_vacuum_algebraic <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PlacewisePureTensorFinitePlaces
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
open scoped Classical
namespace GlobalTheory.PlacePureFin
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.FinDecomp
theorem placewise_pure_tensor_finite_places : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (W W₁ X : HSp D) (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
    (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F W.rank W₁.rank) (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F W.rank W₁.rank),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ (hJ : Γ.W.J = D.host.xi0 • (X.gramᵀ).submatrix e e), ∀ g ∈ GfC X,
    ∃ hv : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F) → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J,
      (∀ v, hv v ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Γ.W (GlobalTheory.AdelicU.evFin D.host.F v)) ∧
      (∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)))
        (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M.vac v) →
        ∃ φ₁ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ,
          (∀ v, φ₁ v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ᶠ v in Filter.cofinite, φ₁ v = Γ.M.vac v) ∧
          (∀ v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin D.host.F v) (om (1, hv v)) (φ v) (φ₁ v)) ∧
          om (1, GlobalTheory.TripleRead.toUX X e hJ g) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ₁) ∧
      ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank)))
        (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M'.vac v) →
        ∃ φ₁ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ,
          (∀ v, φ₁ v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ᶠ v in Filter.cofinite, φ₁ v = Γ.M'.vac v) ∧
          (∀ v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin D.host.F v) (om' (1, hv v)) (φ v) (φ₁ v)) ∧
          om' (1, GlobalTheory.TripleRead.toUX X e hJ g) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ₁ := by
  intro hP D W W₁ X e Bs Γ Xc om om' R Rf hM hJ g hg
  have hT := hM.triple
  let h : UA D.sp.cm.sig Γ.W.J := GlobalTheory.TripleRead.toUX X e hJ g
  have harch : ∀ u : AF D.host.F, At (evI D.host.F) u → u • (mat h - 1) = 0 := GlobalTheory.T.finiteUnitaryPoint_darboux_trivial_archimedean D X e hJ g hg
  obtain ⟨S₀, hS₀⟩ := _root_.GlobalTheory.T.spherical_vector_fixes_vacua hP _ _ _ Bs _ _ Γ Xc om om' hT
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.idempotentCut_unitaryPoint_stabilizes_lattices _ _ _ Bs _ _ Γ hT.geo h
  have hfixB : ∀ (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F))) (e : AF D.host.F) (he : e * e = e), S₀ ∪ S₁ ⊆ S →
      (∀ w ∈ S, ∀ u : AF D.host.F, At (evFin D.host.F w) u → u * e = 0) →
      (∀ w ∉ S, ∀ u : AF D.host.F, At (evFin D.host.F w) u → u * e = 0 ∨ u * e = u) →
      (∀ (f : SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank))) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), _ → ℂ),
        (∀ w, φ w ∈ GlobalTheory.WeilM.SB _) → (∀ w ∉ S, φ w = Γ.M.vac w) → om (1, loc e he h) (pure f φ) = pure f φ) ∧
      (∀ (f : SInf D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank))) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), _ → ℂ),
        (∀ w, φ w ∈ GlobalTheory.WeilM.SB _) → (∀ w ∉ S, φ w = Γ.M'.vac w) → om' (1, loc e he h) (pure f φ) = pure f φ) := by
    intro S e he hS hin hout
    obtain ⟨hl, hl'⟩ := hS₁ S e he (Finset.subset_union_right.trans hS) hout
    refine hS₀ S (Finset.subset_union_left.trans hS) (loc e he h) ?_ ?_ hl hl'
    · intro u hu; rw [mat_loc, phi_sub_one, smul_comm, harch u hu, smul_zero]
    · intro w hw u hu; rw [mat_loc, phi_sub_one, smul_smul, hin w hw u hu, zero_smul]
  refine ⟨fun v => loc (idem _ v) (idem_mul_self v) h, fun v u hu => ?_, fun f φ hSB hvac => ?_, fun f φ hSB hvac => ?_⟩
  · show u • (mat (loc (idem _ v) (idem_mul_self v) h) - 1) = 0
    rw [mat_loc, phi_sub_one, smul_smul, mul_idem_of_evFin hu, zero_smul]
  · exact side Γ.M Bs.ψ hT.geo.hM om h (fun v hh hhv φ hφ => GlobalTheory.T.weilRepresentationLocality_unitaryGroupW_pairVW _ _ _ Bs _ _ Γ Xc om om' hT v hh hhv φ hφ)
      (S₀ ∪ S₁) (fun S e he hS hin hout => (hfixB S e he hS hin hout).1) f φ hSB hvac
  · exact side Γ.M' Bs.ψ hT.geo.hM' om' h (fun v hh hhv φ hφ => GlobalTheory.T.weilRepresentation_localAtFinitePlace_unitaryGroupW _ _ _ Bs _ _ Γ Xc om om' hT v hh hhv φ hφ)
      (S₀ ∪ S₁) (fun S e he hS hin hout => (hfixB S e he hS hin hout).2) f φ hSB hvac
end GlobalTheory.PlacePureFin
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_pure_tensor_placewise_finite : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (W W₁ X : HSp D) (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
    (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F W.rank W₁.rank) (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F W.rank W₁.rank),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ (hJ : Γ.W.J = D.host.xi0 • (X.gramᵀ).submatrix e e), ∀ g ∈ GfC X,
    ∃ hv : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F) → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J,
      (∀ v, hv v ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Γ.W (GlobalTheory.AdelicU.evFin D.host.F v)) ∧
      (∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)))
        (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M.vac v) →
        ∃ φ₁ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ,
          (∀ v, φ₁ v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ᶠ v in Filter.cofinite, φ₁ v = Γ.M.vac v) ∧
          (∀ v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin D.host.F v) (om (1, hv v)) (φ v) (φ₁ v)) ∧
          om (1, GlobalTheory.TripleRead.toUX X e hJ g) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ₁) ∧
      ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank)))
        (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M'.vac v) →
        ∃ φ₁ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ,
          (∀ v, φ₁ v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ᶠ v in Filter.cofinite, φ₁ v = Γ.M'.vac v) ∧
          (∀ v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin D.host.F v) (om' (1, hv v)) (φ v) (φ₁ v)) ∧
          om' (1, GlobalTheory.TripleRead.toUX X e hJ g) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ₁ := by
  first | exact @_root_.GlobalTheory.PlacePureFin.placewise_pure_tensor_finite_places | exact _root_.GlobalTheory.PlacePureFin.placewise_pure_tensor_finite_places | (intros; apply _root_.GlobalTheory.PlacePureFin.placewise_pure_tensor_finite_places <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PolarizationMatchSquareKappa
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.SquareAgree
theorem polarization_match_square_kappa : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ g ∈ GfC X, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf ΦD Φ₀D → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs Γ Xc R Rf (om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW 1, kapX X e hO.JX g) ΦD) (om' (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ 1, kapX X e hO.JX g) Φ₀D) := by
  classical
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB _ _ hO hT R Rf hM Pi rf rl p p' _ g hg ΦD _ Φ₀D _ hPM
  rw [conjU_one_eq, conjU_one_eq]
  have hinf := GlobalTheory.T.archimedeanSupported_smul_transposeGram_finite_sub_one D X e hO.JX g hg
  obtain ⟨S₀, hS₀⟩ := _root_.GlobalTheory.T.spherical_vector_fixes_vacua hP _ _ _ Bs _ _ Γ Xc om om' hT
  obtain ⟨T₀, hXT, hOn⟩ := hPM
  obtain ⟨S, l, k, hTS, hl, hprod, hkinf, hkS, hkV, hkV'⟩ := GlobalTheory.T.exists_adelicUnitary_prod_localPoints_mul_latticeStabilizer _ _ _ Bs _ _ Γ hT.geo _ hinf (T₀ ∪ S₀)
  have ext : ∀ U : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)), GlobalTheory.ThK.PolynomialMatching.PolMatchOn Bs Γ Xc R Rf (T₀ ∪ U) ΦD Φ₀D := by
    intro U
    induction U using Finset.induction_on with
    | empty => rw [Finset.union_empty]; exact hOn
    | insert v U hv ih =>
      rw [Finset.union_insert]
      by_cases hvX : v ∈ Xc.T
      · rw [Finset.insert_eq_of_mem (Finset.mem_union_left _ (hXT hvX))]
        exact ih
      · exact GlobalTheory.ThK.PolynomialMatching.polMatchOn_insert _ _ _ Bs _ _ Γ Xc R Rf v (hM.fin.sph v hvX).1 _ _ _ ih
  have hOnS : GlobalTheory.ThK.PolynomialMatching.PolMatchOn Bs Γ Xc R Rf S ΦD Φ₀D := by
    have := ext S
    rwa [Finset.union_eq_right.2 (Finset.union_subset_left hTS)] at this
  have hU := hS₀ S (Finset.union_subset_right hTS) k hkinf hkS hkV hkV'
  have hOnK : GlobalTheory.ThK.PolynomialMatching.PolMatchOn Bs Γ Xc R Rf S (om (1, k) ΦD) (om' (1, k) Φ₀D) := by
    obtain ⟨m, m', f, φ, f', φ', hφ, hφ', hΦ, hΦ', hsum⟩ := hOnS
    refine ⟨m, m', f, φ, f', φ', hφ, hφ', ?_, ?_, hsum⟩
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [hΦ, map_sum]
        exact Finset.sum_congr rfl fun i _ => hU.1 (f i) (φ i) (hφ i).2.1 (hφ i).2.2
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [hΦ', map_sum]
        exact Finset.sum_congr rfl fun j _ => hU.2 (f' j) (φ' j) (hφ' j).2.1 (hφ' j).2.2
  have split : ∀ (x y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J) Φ, om (1, x * y) Φ = om (1, x) (om (1, y) Φ) := by
    intro x y Φ
    rw [show ((1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.V.J), x * y) = (1, x) * (1, y) by simp, map_mul, Module.End.mul_apply]
  have split' : ∀ (x y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J) Φ, om' (1, x * y) Φ = om' (1, x) (om' (1, y) Φ) := by
    intro x y Φ
    rw [show ((1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.V'.J), x * y) = (1, x) * (1, y) by simp, map_mul, Module.End.mul_apply]
  have key : ∀ l' : List (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F) × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J),
      (∀ x ∈ l', x.1 ∈ S ∧ x.2 ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Γ.W (GlobalTheory.AdelicU.evFin D.host.F x.1)) →
      GlobalTheory.ThK.PolynomialMatching.PolMatchOn Bs Γ Xc R Rf S (om (1, (l'.map Prod.snd).prod * k) ΦD)
        (om' (1, (l'.map Prod.snd).prod * k) Φ₀D) := by
    intro l'
    induction l' with
    | nil => intro _; simpa using hOnK
    | cons x l' ih =>
      intro hx
      have h1 := hx x List.mem_cons_self
      have h2 := ih fun y hy => hx y (List.mem_cons_of_mem _ hy)
      simp only [List.map_cons, List.prod_cons, mul_assoc]
      rw [split, split']
      exact _root_.GlobalTheory.T.polynomial_matching_induction hP _ _ _ Bs _ _ Γ Xc om om' R Rf hM S x.1 h1.1 x.2 h1.2 _ _ h2
  rw [hprod]
  exact ⟨S, hXT.trans (Finset.subset_union_left.trans hTS), key l hl⟩
end GlobalTheory.SquareAgree
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaKCosetCountFormula
section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SumSize GlobalTheory.SumCount
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw
namespace GlobalTheory.CosCount
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
theorem card_kCosets_theta : _root_.GlobalTheory.FunPr.ThetaLocalInputs → CosK := by
  intro _
  refine ⟨0, fun CF _ => ⟨0, fun ε C hC => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ _ => ?_⟩⟩⟩
  intro Φ
  have hL := s.core.lev
  have hde := GlobalTheory.RowClaim.Test.pde_ne_q s
  have hQ := GlobalTheory.LiftLower.Q_base hL
  have hsub : (ch.S.supp A.μ0 Φ).Subsingleton := supp_subsingleton hL ch.S.toGridChoice A.μ0 Φ hde hQ
  have h1 : ((ch.S.supp A.μ0 Φ).ncard : ℝ) ≤ 1 := by
    haveI : Finite (ch.S.supp A.μ0 Φ) := hsub.finite.to_subtype
    exact_mod_cast Set.ncard_le_one_iff_subsingleton.mpr hsub
  have hb : 1 ≤ large₂.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _)
  have hX := ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.sig_nonneg ch.G
  have hlog : 0 ≤ Real.log large₂.sc.b := Real.log_nonneg hb
  have ha : 0 ≤ (D.R.m : ℝ) * aOne ch.G C large₂.sc.b := by
    unfold aOne
    have : (0 : ℝ) ≤ C := hC
    positivity
  exact h1.trans (Real.one_le_exp ha)
end GlobalTheory.CosCount
end
end

section
open GlobalTheory.SumCount GlobalTheory.SumSize
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_kCoset_count_formula : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.SumCount.CosK := by
  first | exact @_root_.GlobalTheory.CosCount.card_kCosets_theta | exact _root_.GlobalTheory.CosCount.card_kCosets_theta | (intros; apply _root_.GlobalTheory.CosCount.card_kCosets_theta <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedCharactersLinearlyIndependent
section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
namespace GlobalTheory.RowTest
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem twist_linear_independence_test (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hL : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal) : GlobalTheory.RowClaim.LinK := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc a u => ?_⟩⟩
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.T.twisted_theta_lift_automorphic hP hL large₂ hS ch hch CF hsc a u
  exact ⟨h1, _root_.GlobalTheory.RowBplus.bplusConv_col ch.W ch.M hch.vol ch.ξ _ (col_mem ch a) _ h2⟩
end GlobalTheory.RowTest
end
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_characters_linearly_independent : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.LinK := by
  first | exact @_root_.GlobalTheory.RowTest.twist_linear_independence_test | exact _root_.GlobalTheory.RowTest.twist_linear_independence_test | (intros; apply _root_.GlobalTheory.RowTest.twist_linear_independence_test <;> assumption)
end
end

