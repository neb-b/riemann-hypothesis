module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0549
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0038
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0146
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0564
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0469
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKFiniteIteratedCompactAverageApprox
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0534
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0586
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaFunctionInfiniteRationalLaw
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0017
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0474
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1468
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0560
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0036
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SquaresAgreeLineDerivativeIsDerivation
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.SquareAgree.LineDerFun
end GlobalTheory.SquareAgree.LineDerFun
open GlobalTheory.SquareAgree.LineDerFun in
theorem GlobalTheory.SquareAgree.LineDerFun.lineDerivation_isDerivation_of_datum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ τ, ∀ Y ∈ lieAt X τ, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Ψ ∈ algD Γ.M Bs.ψ Bs.emb,
    (∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hO.JX (oneP θ X τ Y t)) ΦD x) (Ψ x) 0) → ∀ Φ Φ',
    IsDatum Γ.M ψ cA ΦD Φ → IsDatum Γ.M ψ cA Ψ Φ' → IsDer θ X (fun h => ωA (1, h)) τ Y Φ Φ' := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ _ hO hT τ Y hY ΦD hΦD Ψ hΨ hD Φ Φ'
    hDat hDat'
  obtain ⟨γ, hγ, hγt⟩ := GlobalTheory.KapXLine.exists_line D θ X τ Y hθ hY e Γ.W hO.JX
  obtain ⟨δ, hδ⟩ := _root_.GlobalTheory.OscLie.exists_lie_deriv_pol Bs Γ Xc om om' hT γ hγ
  obtain ⟨m, f, φ, hf, rfl⟩ := algebraicDatum_eq_sum_pureTensors_vacua Γ.M Bs.ψ Bs.emb hΦD
  have hstd : ∀ i, ∀ᶠ v in Filter.cofinite,
      φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers D.host.F} 1 :=
    fun i => ((hf i).2.2.and hT.geo.hM.std).mono fun v h => h.1.trans h.2
  have hder : ∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) x)
      ((∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (δ (f i)) (φ i)) x) 0 := by
    intro x
    have e1 : (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) x) =
        fun t => ∑ i, om (1, γ (Multiplicative.ofAdd t)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) x := by
      funext t
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_apply]
    rw [e1, Finset.sum_apply]
    exact HasDerivAt.fun_sum fun i _ =>
      (hδ _ (hf i).1).2 _ (GlobalTheory.ThK.EvUniqInf.rest_pure (f i) (φ i) (hf i).2.1 (hstd i)) x
  have hΨe : Ψ = ∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (δ (f i)) (φ i) := by
    funext x
    have h1 := hD x
    simp only [← hγt] at h1
    exact h1.unique (hder x)
  intro z
  obtain ⟨u, rfl⟩ := cA.surjective z
  have hs : IsStd ψ := hO.psi ▸ hT.base.std
  have hg : Γ.M.IsGood ψ := hO.psi ▸ hT.geo.hM
  have hw : Γ.M.IsWeil ψ Xc.β (Xc.β / Xc.α) om := hO.psi ▸ hT.weil
  have key := _root_.GlobalTheory.T.theta_sum_differentiable_along_line hP Γ.M ψ Xc.β (Xc.β / Xc.α) om hT.base.cm hs hg hw γ hγ m f (fun i => δ (f i)) φ
    (fun i => (hf i).2) (fun i => (hδ _ (hf i).1).2) u
  have e2 : (fun t : ℝ => ωA (1, oneP θ X τ Y t) Φ (cA u)) = fun t : ℝ =>
      GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho ψ u (om (1, γ (Multiplicative.ofAdd t)) (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)))) := by
    funext t
    have h1 := (hO.weilA _ Φ hDat 1 (oneP θ X τ Y t)).2 u
    rw [conjugateUnitaryAdelicIso_map_one, ← hγt t] at h1
    exact h1.symm
  rw [e2, ← hDat'.2 u, hΨe]
  exact key
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
theorem _root_.GlobalTheory.T.squares_agree_line_derivative_isDerivation : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ τ, ∀ Y ∈ lieAt X τ, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Ψ ∈ algD Γ.M Bs.ψ Bs.emb,
    (∀ x, HasDerivAt (fun t : ℝ => om (1, kapX X e hO.JX (oneP θ X τ Y t)) ΦD x) (Ψ x) 0) → ∀ Φ Φ',
    IsDatum Γ.M ψ cA ΦD Φ → IsDatum Γ.M ψ cA Ψ Φ' → IsDer θ X (fun h => ωA (1, h)) τ Y Φ Φ' := by
  first | exact @_root_.GlobalTheory.SquareAgree.LineDerFun.lineDerivation_isDerivation_of_datum | exact _root_.GlobalTheory.SquareAgree.LineDerFun.lineDerivation_isDerivation_of_datum | (intros; apply _root_.GlobalTheory.SquareAgree.LineDerFun.lineDerivation_isDerivation_of_datum <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLineVectorAnnihilation
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
namespace GlobalTheory.LineKillV
theorem line_vector_annihilated : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Γ.V, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Φ₁D ∈ algD Γ.M Bs.ψ Bs.emb,
    (∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) ΦD x) (Φ₁D x) 0) → ∀ Φ₁,
    IsDatum Γ.M ψ cA Φ₁D Φ₁ → p Φ₁ = 0 := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTr Pi rf rl p p' hm γ hγ ΦD hΦD
    Φ₁D hΦ₁D hder Φ₁ hΦ₁
  have hψ : Bs.ψ = ψ := hO.psi
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hψ ▸ hTr.base.std
  obtain ⟨Y, γs, hY, hγs, hγsY, hprod⟩ := _root_.GlobalTheory.ConjLineSplit.line_eq_prod D θ hθ W Γ.V hO.JW γ hγ
  obtain ⟨Ψ, hΨ, hΨd, hsum⟩ := _root_.GlobalTheory.T.line_derivative_splits hP _ _ _ Bs _ _ _ _ Γ.M _ _ om _ _ _ _
    (GlobalTheory.ThK.RealUniq.isPair_V hTr) _ γs hγs γ hγ hprod ΦD hΦD Φ₁D hder
  obtain ⟨Φ, hΦalg, hΦ⟩ := hO.algA' ΦD hΦD
  choose Φ' hΦ'alg hΦ' using fun τ => hO.algA' (Ψ τ) (hΨ τ)
  have hder' : ∀ τ, IsDer θ W (fun g => ωA (g, 1)) τ (Y τ) Φ (Φ' τ) := by
    intro τ z
    obtain ⟨u, rfl⟩ := cA.surjective z
    have h1 := hΨd τ u
    have e1 : (fun t : ℝ => GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho Bs.ψ u (om (γs τ (Multiplicative.ofAdd t), 1) ΦD))) =
        fun t : ℝ => ωA (oneP θ W τ (Y τ) t, 1) Φ (cA u) := by
      funext t
      have h2 := (hO.weilA ΦD Φ hΦ (oneP θ W τ (Y τ) t) 1).2 u
      rw [GlobalTheory.KapXLine.kapX_one, ← hγsY τ t] at h2
      rw [hψ]; exact h2
    have e2 : GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho Bs.ψ u (Ψ τ)) = Φ' τ (cA u) := by
      rw [hψ]; exact (hΦ' τ).2 u
    rw [e1, e2] at h1
    exact h1
  have hp : ∀ τ, p (Φ' τ) = 0 := fun τ =>
    hm.mapA.invl τ (Y τ) (hY τ) Φ hΦalg (Φ' τ) (hΦ'alg τ) (hder' τ)
  have hsumD : IsDatum Γ.M ψ cA Φ₁D (((Finset.univ : Finset D.what₂.Tau).toList.map Φ').sum) := by
    rw [hsum]; exact isDatum_list_sum hstd _ Ψ Φ' hΦ'
  rw [IsDatum.fun_eq Γ.M ψ cA cA.surjective hΦ₁ hsumD, map_list_sum, List.map_map]
  exact List.sum_eq_zero fun x hx => by
    obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hx
    exact hp τ
end GlobalTheory.LineKillV
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
theorem _root_.GlobalTheory.T.theta_line_vector_annihilation : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Γ.V, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Φ₁D ∈ algD Γ.M Bs.ψ Bs.emb,
    (∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) ΦD x) (Φ₁D x) 0) → ∀ Φ₁,
    IsDatum Γ.M ψ cA Φ₁D Φ₁ → p Φ₁ = 0 := by
  first | exact @_root_.GlobalTheory.LineKillV.line_vector_annihilated | exact _root_.GlobalTheory.LineKillV.line_vector_annihilated | (intros; apply _root_.GlobalTheory.LineKillV.line_vector_annihilated <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistCuspFormApproxWeighted
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
noncomputable section
open scoped ENNReal
theorem GlobalTheory.CuspApproxAll.cusp_form_approx_weighted : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (φ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → ∀ (A : ℕ) (ε : ℝ), 0 < ε → ∃ (n : ℕ) (F : Fin n → N.Maps) (v : Fin n → Formalism.IndefR.Links.SmT N.M), (∀ l, F l ∈ N.Cusp θ) ∧ ∀ g, ‖φ g - ∑ l, F l (v l) g‖ * GlobalTheory.Grow.quotHeight N.V g ^ A ≤ ε := by
  intro D θ hθ hP N φ hφ A ε hε
  obtain ⟨hA, hc, -⟩ := id hφ
  obtain ⟨U, hU, hlev⟩ := hA.level
  obtain ⟨d, C, hC⟩ := hP.cuspDecaySobolev D θ hθ N.V U hU 0 A
  have hφg : GlobalTheory.CuspApproxAll.Good θ N.V φ := ⟨GlobalTheory.Size.rapidDecSm_of_cuspForm hP.cuspRapidDecay hθ hA hc, hc⟩
  have hη : 0 < ε / ((C : ℝ) + 1) := div_pos hε (by positivity)
  obtain ⟨e, he, hgrow⟩ := _root_.GlobalTheory.KAvgApprox.approx_avgList D θ hθ N φ hφg.1 (Finset.univ : Finset D.what₂.Tau).toList (Finset.nodup_toList _) d _ hη
  obtain ⟨n, F, v, hF, hFlev, hsum⟩ := _root_.GlobalTheory.T.twist_cusp_average_k_finite_decomposition D θ hθ hP N φ hφ U hU hlev e he
    (Finset.univ : Finset D.what₂.Tau).toList (fun τ => Finset.mem_toList.2 (Finset.mem_univ τ))
  rw [hsum] at hgrow
  refine ⟨n, F, v, hF, fun g => ?_⟩
  set ψ : GA D N.V → ℂ := φ - ∑ j, F j (v j) with hψ
  have hsg : GlobalTheory.CuspApproxAll.Good θ N.V (∑ j, F j (v j)) :=
    Finset.sum_induction _ (GlobalTheory.CuspApproxAll.Good θ N.V) (fun _ _ => GlobalTheory.CuspApproxAll.good_add)
      (GlobalTheory.CuspApproxAll.good_zero θ N.V) fun j _ => GlobalTheory.CuspApproxAll.good_value hP.cuspRapidDecay hθ N (hF j) (v j)
  have hg : GlobalTheory.CuspApproxAll.Good θ N.V ψ := by
    have := GlobalTheory.CuspApproxAll.good_add hφg (GlobalTheory.CuspApproxAll.good_smul (-1) hsg)
    rwa [neg_one_smul, ← sub_eq_add_neg] at this
  have hψlev : ∀ k ∈ U, k ∈ GfC N.V → ∀ x, ψ (x * k) = ψ x := fun k hk hk' x => by
    simp only [hψ, Pi.sub_apply, Finset.sum_apply, hlev k hk hk' x, hFlev _ k hk hk' x]
  have h1 := hC ψ hg.1.toIsAutFun hψlev hg.1.smooth (GlobalTheory.CuspApproxAll.growthSob_zero_ne_top hg.1) hg.2
  have h2 : decaySize N.V A ψ ≤ ENNReal.ofReal ε := by
    have h4 : (C : ℝ≥0∞) * growthSob θ N.V d 0 ψ ≤ C * ENNReal.ofReal (ε / ((C : ℝ) + 1)) := by gcongr
    refine h1.trans (h4.trans ?_)
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith [NNReal.coe_nonneg C]
  have h3 : ENNReal.ofReal (‖ψ g‖ * quotHeight N.V g ^ A) ≤ ENNReal.ofReal ε := (le_iSup (fun x => ENNReal.ofReal (‖ψ x‖ * quotHeight N.V x ^ A)) g).trans h2
  rw [ENNReal.ofReal_le_ofReal_iff hε.le] at h3
  simpa [hψ, Finset.sum_apply] using h3
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_cusp_form_approx_weighted : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (φ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → ∀ (A : ℕ) (ε : ℝ), 0 < ε → ∃ (n : ℕ) (F : Fin n → N.Maps) (v : Fin n → Formalism.IndefR.Links.SmT N.M), (∀ l, F l ∈ N.Cusp θ) ∧ ∀ g, ‖φ g - ∑ l, F l (v l) g‖ * GlobalTheory.Grow.quotHeight N.V g ^ A ≤ ε := by
  first | exact @_root_.GlobalTheory.CuspApproxAll.cusp_form_approx_weighted | exact _root_.GlobalTheory.CuspApproxAll.cusp_form_approx_weighted | (intros; apply _root_.GlobalTheory.CuspApproxAll.cusp_form_approx_weighted <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistJetKappaSplitMove
section
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
noncomputable section
namespace GlobalTheory.SplitMoveKappa
theorem jetKappa_split_move : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ : ℂ), GlobalTheory.MovedKappaEx.JetKap ch p x y κ →
    ∀ (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∀ (s : FinPt ch.G p.small) (s' : FinPt ch.G p.big),
    SuppAt e _ (s : GA D (ch.G.V p.small)) → SuppAt e _ (s' : GA D (ch.G.V p.big)) →
    ∃ x₀ y₀ : (Formalism.L2.Theta.AE D)ˣ,
      (∃ a : Formalism.L2.Theta.AE D, (x₀ : Formalism.L2.Theta.AE D) = e * a + (1 - e) ∨ (x₀ : Formalism.L2.Theta.AE D) = cA D e * a + (1 - cA D e)) ∧
      (∃ b : Formalism.L2.Theta.AE D, (y₀ : Formalism.L2.Theta.AE D) = e * b + (1 - e) ∨ (y₀ : Formalism.L2.Theta.AE D) = cA D e * b + (1 - cA D e)) ∧
      ∃ ζ : ℂ, (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) ∧ ∃ r : ℝ, 0 < r ∧
        GlobalTheory.MovedKappaEx.JetKap ch p (s * x) (s' * y)
          ((r : ℂ) * ζ * ((((ch.G.chrT p x₀)⁻¹ * ch.G.chrS p y₀ : Circle)) : ℂ) * κ) := by
  intro hP hI D Γ _ _ Pl0 T A Ks _ _ _ R ch hch p hp x y κ hκ e he s s' hs hs'
  obtain ⟨x₀, y₀, hx₀, hy₀, ζ, ⟨n, hn, hζ⟩, r, hr, hread⟩ := _root_.GlobalTheory.T.twist_splitMoveFrames_jets hP hI ch hch p hp x y e he s s' hs hs'
  have hC := ch.S.Z.crv
  have he0 := ch.S.Z.e0_is p hp
  have hsd := _root_.GlobalTheory.T.twisted_moved_series_decomposition hP hI ch hch p hp x y
  have hsd' := _root_.GlobalTheory.T.twisted_moved_series_decomposition hP hI ch hch p hp (s * x) (s' * y)
  have hG := (GlobalTheory.InducedType.induced_type D).1
  have he0ne : ch.S.Z.e0 p ≠ 0 := by
    intro h
    have hn := he0.2.2.1
    rw [h] at hn
    have h0 : Formalism.MainNotions.TaylorLogMetric.normSq D (tor0 D D.host.ccK ch.S.Z.δ) (Formalism.MainNotions.StandardLatticesGL3.La0 D (tor0 D D.host.ccK ch.S.Z.δ) (ch.G.pS p).rank (ch.G.pT p).rank) (0 : Formalism.MainNotions.TaylorLogMetric.VC D (ch.G.pS p).rank (ch.G.pT p).rank → ℂ) = 0 := by
      simp [Formalism.MainNotions.TaylorLogMetric.normSq]
    rw [h0] at hn
    exact pow_ne_zero _ (GlobalTheory.ConjJet.thetaZeroNormSq_ne_zero_cmLattice D hG D.host.ccK ch.S.Z.δ _ hC ch.S.Z.pt0) hn.symm
  have hK0 : Formalism.MainNotions.StandardLatticesGL3.KLat D (tor0 D D.host.ccK ch.S.Z.δ) (Formalism.MainNotions.StandardLatticesGL3.La0 D (tor0 D D.host.ccK ch.S.Z.δ) (ch.G.pS p).rank (ch.G.pT p).rank) :=
    Or.inr ⟨_, _, GlobalTheory.NormSum.VacInt.sd_std D _, GlobalTheory.NormSum.VacInt.sd_std D _, rfl⟩
  have hK1 : Formalism.MainNotions.StandardLatticesGL3.KLat D (tor0 D D.host.ccK ch.S.Z.δ) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) := Or.inr ⟨_, _, hsd.1, hsd.2, rfl⟩
  have hK2 : Formalism.MainNotions.StandardLatticesGL3.KLat D (tor0 D D.host.ccK ch.S.Z.δ) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p (s * x) (s' * y)) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p (s * x) (s' * y))) := Or.inr ⟨_, _, hsd'.1, hsd'.2, rfl⟩
  obtain ⟨-, -, -, htrip⟩ := GlobalTheory.ThetaTriple.klat_triples D D.host.ccK ch.S.Z.δ hC (ch.G.pS p).rank (ch.G.pT p).rank
  obtain ⟨μ, hμ⟩ := htrip _ _ _ hK0 hK1 hK2 _ he0.1 he0ne
  have hμ8 : μ ^ 8 = 1 := hμ.2.2.2.2.2.2.2.2.1
  have hμI := hμ.2.2.2.2.2.2.2.2.2
  refine ⟨x₀, y₀, hx₀, hy₀, ζ * μ, ⟨8 * n, by omega, by rw [mul_pow, pow_mul', hζ, pow_mul, hμ8, one_pow, one_pow, one_mul]⟩, r, hr, ?_⟩
  have hd := _root_.GlobalTheory.MovedDict.Entire.differentiable_moved_operator_eval hP hI ch hch p hp x y
  have h1 := hread (fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (Formalism.MainNotions.StandardLatticesGL3.La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z) (hd.const_mul κ) hκ
  intro k
  rw [om_toPair_mul, h1 k]
  congr 3
  refine congrArg _ (funext fun z => ?_)
  have hs1 : (fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (Formalism.MainNotions.StandardLatticesGL3.La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z) =
      κ • Iop D (tor0 D D.host.ccK ch.S.Z.δ) (Formalism.MainNotions.StandardLatticesGL3.La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) := rfl
  rw [hs1, GlobalTheory.InertSign.Iop_smul, hμI]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring
end GlobalTheory.SplitMoveKappa
end
end

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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_jetKappa_split_move : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ : ℂ), GlobalTheory.MovedKappaEx.JetKap ch p x y κ →
    ∀ (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∀ (s : FinPt ch.G p.small) (s' : FinPt ch.G p.big),
    SuppAt e _ (s : GA D (ch.G.V p.small)) → SuppAt e _ (s' : GA D (ch.G.V p.big)) →
    ∃ x₀ y₀ : (Formalism.L2.Theta.AE D)ˣ,
      (∃ a : Formalism.L2.Theta.AE D, (x₀ : Formalism.L2.Theta.AE D) = e * a + (1 - e) ∨ (x₀ : Formalism.L2.Theta.AE D) = cA D e * a + (1 - cA D e)) ∧
      (∃ b : Formalism.L2.Theta.AE D, (y₀ : Formalism.L2.Theta.AE D) = e * b + (1 - e) ∨ (y₀ : Formalism.L2.Theta.AE D) = cA D e * b + (1 - cA D e)) ∧
      ∃ ζ : ℂ, (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) ∧ ∃ r : ℝ, 0 < r ∧
        GlobalTheory.MovedKappaEx.JetKap ch p (s * x) (s' * y)
          ((r : ℂ) * ζ * ((((ch.G.chrT p x₀)⁻¹ * ch.G.chrS p y₀ : Circle)) : ℂ) * κ) := by
  first | exact @_root_.GlobalTheory.SplitMoveKappa.jetKappa_split_move | exact _root_.GlobalTheory.SplitMoveKappa.jetKappa_split_move | (intros; apply _root_.GlobalTheory.SplitMoveKappa.jetKappa_split_move <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WeilProjectionKInftyInvariant
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open scoped ComplexConjugate
noncomputable section
namespace GlobalTheory.KInvData
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {W W₁ X : HSp D} {A : Fr W} {A₁ : Fr W₁} {B : Fr X}
  {α β : (AE D)ˣ →* Circle} {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} {ν₁ : Measure (GA D W₁)} {𝓕₁ : Set (GA D W₁)}
  {ωA : WRep W X} {ωB : WRep W₁ X} {e : Fin X.rank ≃ Fin (W.rank + W₁.rank)}
  {Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E} {Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank}
  {Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E} {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W}
  {om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W}
  {cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X}
  {cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X}
  {Pi : ModuleCat.{0} ℂ} {rf : GA D X → Module.End ℂ Pi}
  {rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi} {p : (WO W X → ℂ) →ₗ[ℂ] Pi}
theorem projection_kInfty_invariant : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Γ.V Bs.emb, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Φ Φ₁,
    IsDatum Γ.M ψ cA ΦD Φ → IsDatum Γ.M ψ cA (om (k, 1) ΦD) Φ₁ → p Φ₁ = p Φ := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ _ hO hT Pi rf rl p p' hm k hk ΦD hΦD Φ Φ₁
    h0 h1
  have hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hO.psi ▸ hT.base.std
  obtain ⟨U, hUf, hUle, hΦU, hUst⟩ := _root_.GlobalTheory.T.kFinite_algebra_closed_under_derivation hP _ _ _ Bs _ _ Γ Xc om om' hT ΦD hΦD
  obtain ⟨l, hl, rfl⟩ := _root_.GlobalTheory.T.kInfinity_action_prod_lines hP D θ W Bs Γ.V _ _ hO.JW hθ hT.base hT.geo.hV k hk
  haveI := hUf
  have key : ∀ l : List (D.what₂.Tau × Matrix (Fin W.rank) (Fin W.rank) ℂ),
      (∀ q ∈ l, q.2 ∈ lieAt W q.1 ∧ ∀ t : ℝ,
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW (oneP θ W q.1 q.2 t) ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Γ.V Bs.emb) →
      ∀ x ∈ U, om ((l.map fun q => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW (oneP θ W q.1 q.2 1)).prod, 1) x ∈ U ∧
        ∀ Φ Φ₁, IsDatum Γ.M ψ cA x Φ →
          IsDatum Γ.M ψ cA (om ((l.map fun q => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW (oneP θ W q.1 q.2 1)).prod, 1) x) Φ₁ →
          p Φ₁ = p Φ := by
    intro l
    induction l with
    | nil =>
      intro _ x hx
      simp only [List.map_nil, List.prod_nil, Prod.mk_one_one, map_one, Module.End.one_apply]
      exact ⟨hx, fun Φ Φ₁ h0 h1 => by rw [GlobalTheory.SquareAgree.CoinvPass.isDatum_unique cA.surjective h1 h0]⟩
    | cons q l ih =>
      intro hl x hx
      obtain ⟨hx1, hx2⟩ := ih (fun q' hq' => hl q' (List.mem_cons_of_mem _ hq')) x hx
      obtain ⟨hq1, hq2⟩ := hl q List.mem_cons_self
      have e : om ((List.map (fun q => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW (oneP θ W q.1 q.2 1)) (q :: l)).prod, 1) x =
          om (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW (oneP θ W q.1 q.2 1), 1)
            (om ((l.map fun q => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 hO.JW (oneP θ W q.1 q.2 1)).prod, 1) x) := by
        rw [List.map_cons, List.prod_cons, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul]
      rw [e]
      refine ⟨hUst _ (hq2 1) _ hx1, fun Φ Φ₁ h0 h1 => ?_⟩
      obtain ⟨Ψ, -, hΨ⟩ := hO.algA' _ (hUle hx1)
      rw [line_step hθ hψ hO hm.mapA hq1 U hUle (fun t z hz => hUst _ (hq2 t) z hz) hx1 hΨ h1, hx2 Φ Ψ h0 hΨ]
  exact (key l hl ΦD hΦU).2 Φ Φ₁ h0 h1
end GlobalTheory.KInvData
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
theorem _root_.GlobalTheory.T.weil_projection_kInfty_invariant : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Γ.V Bs.emb, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Φ Φ₁,
    IsDatum Γ.M ψ cA ΦD Φ → IsDatum Γ.M ψ cA (om (k, 1) ΦD) Φ₁ → p Φ₁ = p Φ := by
  first | exact @_root_.GlobalTheory.KInvData.projection_kInfty_invariant | exact _root_.GlobalTheory.KInvData.projection_kInfty_invariant | (intros; apply _root_.GlobalTheory.KInvData.projection_kInfty_invariant <;> assumption)
end
end

