module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1618
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1571
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0294
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0460
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0327
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridParameterRegularCardEqRankFormula
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0468
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RealQuotientBottomInvariantsEquiv
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.RealQuotBot.real_quotient_invariants_equiv : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (A A' WW : HSp D) (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (a b : D.what₂.Tau → ℚ)
    (had : A.rank + A'.rank = WW.rank),
    (∀ τ, Formalism.UG.HasSignature (gramAt D A τ) A.rank 0) → (∀ τ, Formalism.UG.HasSignature (gramAt D A' τ) A'.rank 0) →
    (∀ τ, Formalism.UG.HasSignature (gramAt D WW τ) WW.rank 0) →
    (∃ α β, GlobalTheory.SquareComm.IsTriple A A' WW α β ∧ ∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
  ∀ (Pr : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr),
    Function.Surjective q → Function.Surjective q' →
    (∀ α β, GlobalTheory.SquareComm.IsTriple A A' WW α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
      (∃ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ FA FA' FW α β ωA ωB Pi rf rl p p') ∧
      ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ FA FA' FW α β ωA ωB Pi rf rl p p' →
        ∃ (Pf : ModuleCat.{0} ℂ) (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi),
          (∀ x, ∃ f, GlobalTheory.SquareComm.IsFinF ψ θ true FA FW f ∧ r f = x) ∧
          (∀ x, ∃ f, GlobalTheory.SquareComm.IsFinF ψ θ false FA' FW f ∧ r' f = x) ∧
          (∀ f, GlobalTheory.SquareComm.IsFinF ψ θ true FA FW f → ∀ P, p (GlobalTheory.SquareComm.fockF ψ θ true FA FW f P) = e (q P ⊗ₜ r f)) ∧
          ∀ f, GlobalTheory.SquareComm.IsFinF ψ θ false FA' FW f → ∀ P,
            p' (GlobalTheory.SquareComm.fockF ψ θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) →
    Nontrivial Pr ∧ ∃ (n₀ : D.what₂.Tau → ℕ) (σ : (D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ) → Module.End ℂ Pr),
    (∀ (g : D.what₂.Tau → Matrix.unitaryGroup (Fin A.rank) ℂ) (P : PolF D WW.rank A.rank),
      q (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin A.rank) (Fin A.rank) ℂ)) P) =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin A.rank) (Fin A.rank) ℂ)) • q P) ∧
    (∀ (g : D.what₂.Tau → Matrix.unitaryGroup (Fin A'.rank) ℂ) (P : PolF D WW.rank A'.rank),
      q' (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) P) =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) • q' P) ∧
    (∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin WW.rank) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := D.what₂.Tau) A.rank WW.rank n₀,
      q (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ).map (starRingEnd ℂ)) P) =
        σ (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) (q P)) ∧
    (∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin WW.rank) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := D.what₂.Tau) A'.rank WW.rank n₀,
      q' (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) P) =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) • σ (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) (q' P)) := by
  intro hH hP hK hLM D ψ θ hψ hθ A A' WW FA FA' FW a b had hsA hsA' hsW hex Pr q q' hq hq' hfac
  obtain ⟨α, β, hT, hE⟩ := hex
  obtain ⟨⟨ωA, ωB, Pi, rf, rl, p, p', hm⟩, hfac2⟩ := hfac α β hT hE
  obtain ⟨Pf, r, r', e, hr, hr', hpA, hpB⟩ := hfac2 _ _ _ _ _ _ _ hm
  have hPi : Nontrivial Pi := hm.irred.1
  have hall : ¬ ∀ z : Pr ⊗[ℂ] Pf, z = 0 := by
    intro h
    obtain ⟨z, hz⟩ := exists_ne (0 : Pi)
    exact hz (by rw [← e.apply_symm_apply z, h (e.symm z), map_zero])
  have hPr : Nontrivial Pr := by
    by_contra hc
    rw [not_nontrivial_iff_subsingleton] at hc
    exact hall fun z => by
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul x y => rw [Subsingleton.elim x 0, TensorProduct.zero_tmul]
      | add u v hu hv => rw [hu, hv, add_zero]
  have hPf : Nontrivial Pf := by
    by_contra hc
    rw [not_nontrivial_iff_subsingleton] at hc
    exact hall fun z => by
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul x y => rw [Subsingleton.elim y 0, TensorProduct.tmul_zero]
      | add u v hu hv => rw [hu, hv, add_zero]
  obtain ⟨y, hy⟩ := exists_ne (0 : Pf)
  obtain ⟨f, hf, hfy⟩ := hr y
  obtain ⟨f', hf', hfy'⟩ := hr' y
  have hf0 : f ≠ 0 := by rintro rfl; exact hy (by rw [← hfy, map_zero])
  have canc : ∀ x x' : Pr, e (x ⊗ₜ y) = e (x' ⊗ₜ y) → x = x' := by
    intro x x' h
    by_contra hne
    have h2 : (x - x') ⊗ₜ[ℂ] y = 0 := by
      rw [TensorProduct.sub_tmul]; exact sub_eq_zero.2 (e.injective h)
    exact GlobalTheory.RealQuotBot.tmul_ne_zero (sub_ne_zero.2 hne) hy h2
  have sA := fun τ => _root_.GlobalTheory.DefiniteFrame.frame_signs_pos D A FA τ (hsA τ)
  have sA' := fun τ => _root_.GlobalTheory.DefiniteFrame.frame_signs_pos D A' FA' τ (hsA' τ)
  have sW := fun τ => _root_.GlobalTheory.DefiniteFrame.frame_signs_pos D WW FW τ (hsW τ)
  obtain ⟨hTA, hcoA, -⟩ := GlobalTheory.RealQuot.oriented_maps D ψ θ hθ true A WW FA FW β (β / α) ωA b (fun τ => b τ - a τ) hm.weilA
    (fun τ => ⟨(hE τ).2, GlobalTheory.RealQuot.hasInfExp_div D α β τ (a τ) (b τ) (hE τ).1 (hE τ).2⟩) Pi rf rl p hm.mapA
  obtain ⟨hTB, hcoB, -⟩ := GlobalTheory.RealQuot.oriented_maps D ψ θ hθ false A' WW FA' FW α (α / β) ωB a (fun τ => a τ - b τ) hm.weilB
    (fun τ => ⟨(hE τ).1, GlobalTheory.RealQuot.hasInfExp_div D β α τ (b τ) (a τ) (hE τ).2 (hE τ).1⟩) Pi rf rl p' hm.mapB
  obtain ⟨n₀, hn₀⟩ := _root_.GlobalTheory.WeightNat.weight_nat D ψ θ A A' WW FA FW a b α β ωA hθ hsA hsW hT hE hm.weilA ⟨f, hf, hf0⟩
  have kA : GlobalTheory.RealQuot.coinv true FA FW (fun τ => b τ - a τ) ≤ LinearMap.ker q := by
    intro P hP
    have h := hcoA f hf P hP
    rw [hpA f hf P, hfy] at h
    rw [LinearMap.mem_ker]
    refine canc _ _ ?_
    rw [h, TensorProduct.zero_tmul, map_zero]
  have kB : GlobalTheory.RealQuot.coinv false FA' FW (fun τ => a τ - b τ) ≤ LinearMap.ker q' := by
    intro P hP
    have h := hcoB f' hf' P hP
    rw [hpB f' hf' P, hfy'] at h
    rw [LinearMap.mem_ker]
    refine canc _ _ ?_
    rw [h, TensorProduct.zero_tmul, map_zero]
  have hrel : ∀ P P', q P = q' P' → ∀ τ, ∀ Y ∈ lieAt WW τ,
      q (GlobalTheory.RealQuot.actT true FA FW b τ Y P) = q' (GlobalTheory.RealQuot.actT false FA' FW a τ Y P') := by
    intro P P' hPP τ Y hY
    have h1 := hTA f hf τ Y hY P
    have h2 := hTB f' hf' τ Y hY P'
    rw [hpA f hf, hpA f hf, hfy] at h1
    rw [hpB f' hf', hpB f' hf', hfy'] at h2
    refine canc _ _ ?_
    rw [h1, h2, hPP]
  have hrow := _root_.GlobalTheory.RowTransport.row_transport D A A' WW FA FA' FW b a n₀ Pr q q' sA sA' sW
    (fun τ => by
      have hc : ((A.rank : ℚ) + (A'.rank : ℚ)) = (WW.rank : ℚ) := by exact_mod_cast had
      rw [hn₀ τ, hc]) hrel
  have hdet : ∀ κ : D.what₂.Tau → Matrix.unitaryGroup (Fin WW.rank) ℂ,
      GlobalTheory.MinorFrame.detChar n₀ (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) ≠ 0 := by
    intro κ
    unfold GlobalTheory.MinorFrame.detChar
    exact Finset.prod_ne_zero_iff.2 fun τ _ => pow_ne_zero _ (GlobalTheory.RealQuotBot.det_unitary_ne_zero (κ τ))
  let σ : (D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ) → Module.End ℂ Pr := fun κ =>
    if h : LinearMap.ker q ≤ LinearMap.ker (q ∘ₗ (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ).map (starRingEnd ℂ))).toLinearMap) then
      (LinearMap.ker q).liftQ _ h ∘ₗ (q.quotKerEquivOfSurjective hq).symm.toLinearMap else 0
  have hσ : ∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin WW.rank) ℂ) P,
      σ (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) (q P) =
        q (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ).map (starRingEnd ℂ)) P) := by
    intro κ P
    have hk : LinearMap.ker q ≤ LinearMap.ker (q ∘ₗ (GlobalTheory.MinorFrame.rowSub
        (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ).map (starRingEnd ℂ))).toLinearMap) := by
      intro P₀ hP₀
      rw [LinearMap.mem_ker] at hP₀ ⊢
      have h := hrow κ P₀ 0 (by rw [hP₀, map_zero])
      rw [map_zero, map_zero] at h
      exact (smul_eq_zero.1 h.symm).resolve_left (hdet κ)
    have e1 : (q.quotKerEquivOfSurjective hq).symm (q P) = Submodule.Quotient.mk P := by
      rw [LinearEquiv.symm_apply_eq, LinearMap.quotKerEquivOfSurjective_apply_mk]
    simp only [σ, dif_pos hk, LinearMap.comp_apply, LinearEquiv.coe_coe, e1, Submodule.liftQ_apply, AlgHom.toLinearMap_apply]
  refine ⟨hPr, n₀, σ, ?_, ?_, ?_, ?_⟩
  · exact _root_.GlobalTheory.LieInt.colSub_unitary_of_coinv D true A WW FA FW (fun τ => b τ - a τ) n₀ Pr q sA sW (fun τ => by simp only [if_true]; exact hn₀ τ) kA
  · exact _root_.GlobalTheory.LieInt.colSub_unitary_of_coinv D false A' WW FA' FW (fun τ => a τ - b τ) n₀ Pr q' sA' sW
      (fun τ => by simp only [Bool.false_eq_true, if_false]; rw [hn₀ τ]; ring) kB
  · intro κ P _
    rw [hσ]
  · intro κ P' _
    obtain ⟨P, hP⟩ := hq (q' P')
    rw [hrow κ P P' hP, ← hP, hσ]
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_quotient_bottom_invariants_equiv : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
  ∀ (A A' WW : HSp D) (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW) (a b : D.what₂.Tau → ℚ)
    (had : A.rank + A'.rank = WW.rank),
    (∀ τ, Formalism.UG.HasSignature (gramAt D A τ) A.rank 0) → (∀ τ, Formalism.UG.HasSignature (gramAt D A' τ) A'.rank 0) →
    (∀ τ, Formalism.UG.HasSignature (gramAt D WW τ) WW.rank 0) →
    (∃ α β, GlobalTheory.SquareComm.IsTriple A A' WW α β ∧ ∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
  ∀ (Pr : ModuleCat.{0} ℂ) (q : PolF D WW.rank A.rank →ₗ[ℂ] Pr) (q' : PolF D WW.rank A'.rank →ₗ[ℂ] Pr),
    Function.Surjective q → Function.Surjective q' →
    (∀ α β, GlobalTheory.SquareComm.IsTriple A A' WW α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
      (∃ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ FA FA' FW α β ωA ωB Pi rf rl p p') ∧
      ∀ ωA ωB Pi rf rl p p', GlobalTheory.SquareComm.IsMatch ψ θ FA FA' FW α β ωA ωB Pi rf rl p p' →
        ∃ (Pf : ModuleCat.{0} ℂ) (r : (WO A WW → ℂ) →ₗ[ℂ] Pf) (r' : (WO A' WW → ℂ) →ₗ[ℂ] Pf) (e : Pr ⊗[ℂ] Pf ≃ₗ[ℂ] Pi),
          (∀ x, ∃ f, GlobalTheory.SquareComm.IsFinF ψ θ true FA FW f ∧ r f = x) ∧
          (∀ x, ∃ f, GlobalTheory.SquareComm.IsFinF ψ θ false FA' FW f ∧ r' f = x) ∧
          (∀ f, GlobalTheory.SquareComm.IsFinF ψ θ true FA FW f → ∀ P, p (GlobalTheory.SquareComm.fockF ψ θ true FA FW f P) = e (q P ⊗ₜ r f)) ∧
          ∀ f, GlobalTheory.SquareComm.IsFinF ψ θ false FA' FW f → ∀ P,
            p' (GlobalTheory.SquareComm.fockF ψ θ false FA' FW f P) = e (q' P ⊗ₜ r' f)) →
    Nontrivial Pr ∧ ∃ (n₀ : D.what₂.Tau → ℕ) (σ : (D.what₂.Tau → Matrix (Fin WW.rank) (Fin WW.rank) ℂ) → Module.End ℂ Pr),
    (∀ (g : D.what₂.Tau → Matrix.unitaryGroup (Fin A.rank) ℂ) (P : PolF D WW.rank A.rank),
      q (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin A.rank) (Fin A.rank) ℂ)) P) =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin A.rank) (Fin A.rank) ℂ)) • q P) ∧
    (∀ (g : D.what₂.Tau → Matrix.unitaryGroup (Fin A'.rank) ℂ) (P : PolF D WW.rank A'.rank),
      q' (GlobalTheory.MinorFrame.colSub (fun τ => (g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) P) =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (g τ : Matrix (Fin A'.rank) (Fin A'.rank) ℂ)) • q' P) ∧
    (∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin WW.rank) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := D.what₂.Tau) A.rank WW.rank n₀,
      q (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ).map (starRingEnd ℂ)) P) =
        σ (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) (q P)) ∧
    (∀ (κ : D.what₂.Tau → Matrix.unitaryGroup (Fin WW.rank) ℂ), ∀ P ∈ GlobalTheory.MinorFrame.inv (ι := D.what₂.Tau) A'.rank WW.rank n₀,
      q' (GlobalTheory.MinorFrame.rowSub (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) P) =
        GlobalTheory.MinorFrame.detChar n₀ (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) • σ (fun τ => (κ τ : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) (q' P)) := by
  first | exact @_root_.GlobalTheory.RealQuotBot.real_quotient_invariants_equiv | exact _root_.GlobalTheory.RealQuotBot.real_quotient_invariants_equiv | (intros; apply _root_.GlobalTheory.RealQuotBot.real_quotient_invariants_equiv <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RealWeilRepresentationSchurScalar
section
section
open scoped Matrix
noncomputable section
open MeasureTheory Complex
open scoped Real RealInnerProductSpace ComplexConjugate FourierTransform SchwartzMap
namespace GlobalTheory.RealWeil.SchurSchwartz
variable {l : Type} [Fintype l]
end GlobalTheory.RealWeil.SchurSchwartz
namespace GlobalTheory.RealWeil.SchurSchwartz
variable {l : Type} [Fintype l]
theorem weil_schwartz_schur_lemma : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (l : Type) [Fintype l] (U : GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l),
    (∀ (w : l ⊕ l → ℝ) (h h₁ : GlobalTheory.RealWeil.Sch l), ⇑h₁ = GlobalTheory.RealWeil.rhoFun w ⇑h →
      ⇑(U h₁) = GlobalTheory.RealWeil.rhoFun w ⇑(U h)) →
    (∀ h : GlobalTheory.RealWeil.Sch l, ∫⁻ x, ‖U h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) →
    ∃ a : ℂ, ‖a‖ = 1 ∧ ∀ h, U h = a • h := by
  intro _ l _ U hc hU
  by_cases h0 : ∃ (g : Sch l) (y : EuclideanSpace ℝ l), g y ≠ 0
  · obtain ⟨g, y0, hg⟩ := h0
    have hb := conj_mul_eq U hc hU g g y0
    rw [Complex.conj_mul', Complex.conj_mul'] at hb
    have h2 : ‖U g y0‖ ^ 2 = ‖g y0‖ ^ 2 := by exact_mod_cast hb
    have hnb : ‖U g y0‖ = ‖g y0‖ := by
      first
        | exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h2
        | exact pow_left_injective₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero h2
        | nlinarith [norm_nonneg (U g y0), norm_nonneg (g y0)]
    have hb0 : U g y0 ≠ 0 := by
      intro h
      apply hg
      rw [← norm_eq_zero, ← hnb, h, norm_zero]
    have hcb : conj (U g y0) ≠ 0 := (map_ne_zero _).2 hb0
    refine ⟨conj (g y0 / U g y0), ?_, fun f => ?_⟩
    · rw [Complex.norm_conj, norm_div, hnb, div_self (norm_ne_zero_iff.2 hg)]
    · ext x
      have e1 := conj_mul_eq U hc hU f (trS (y0 - x) g) x
      have hxy : x + (y0 - x) = y0 := by abel
      rw [hc (trPt (y0 - x)) g (trS (y0 - x) g) (coe_trS _ _), coe_trS, rhoFun_trPt, rhoFun_trPt, hxy] at e1
      have e2 := congrArg conj e1
      simp only [map_mul, Complex.conj_conj] at e2
      rw [SchwartzMap.smul_apply, smul_eq_mul, map_div₀, div_mul_eq_mul_div, eq_div_iff hcb, e2, mul_comm]
  · push_neg at h0
    refine ⟨1, by simp, fun h => ?_⟩
    ext x
    rw [h0 (U h) x, one_smul, h0 h x]
end GlobalTheory.RealWeil.SchurSchwartz
end
end

section
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_weil_representation_schur_scalar : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (l : Type) [Fintype l] (U : GlobalTheory.RealWeil.Sch l →ₗ[ℂ] GlobalTheory.RealWeil.Sch l),
    (∀ (w : l ⊕ l → ℝ) (h h₁ : GlobalTheory.RealWeil.Sch l), ⇑h₁ = GlobalTheory.RealWeil.rhoFun w ⇑h →
      ⇑(U h₁) = GlobalTheory.RealWeil.rhoFun w ⇑(U h)) →
    (∀ h : GlobalTheory.RealWeil.Sch l, ∫⁻ x, ‖U h x‖ₑ ^ 2 = ∫⁻ x, ‖h x‖ₑ ^ 2) →
    ∃ a : ℂ, ‖a‖ = 1 ∧ ∀ h, U h = a • h := by
  first | exact @_root_.GlobalTheory.RealWeil.SchurSchwartz.weil_schwartz_schur_lemma | exact _root_.GlobalTheory.RealWeil.SchurSchwartz.weil_schwartz_schur_lemma | (intros; apply _root_.GlobalTheory.RealWeil.SchurSchwartz.weil_schwartz_schur_lemma <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SeparatingFamilyExtendsByTwistedRow
section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.SepRows GlobalTheory.PairLift GlobalTheory.ChainFr GlobalTheory.Chain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.RowArrow
variable {D : D7}
end GlobalTheory.RowArrow
open GlobalTheory.RowArrow in
theorem GlobalTheory.RowArrow.separatingFamily_extends_by_twisted_row : _root_.GlobalTheory.FunPr.ThetaLocalInputs → PairEx → RowModels → RowStep := by
  intro pr hE _ D _ hS T L μ0 hL sc hc G W M hM i hi S S' MA MB e e' cA cB
  obtain ⟨X, hX, -, -, h3, h4, h5⟩ :=
    GlobalTheory.RealPlaceTheta.exists_record_theta_all pr.discreteSeriesCover pr.harishChandraModules
  have I := GlobalTheory.PairLift.inputs_of_chosenSeries pr.discreteSeriesCover pr.harishChandraModules pr.cuspRapidDecay pr.casselmanWallach D X hX
  have hP := GlobalTheory.PairLift.RuleLift.pairLifts D X I (GlobalTheory.PairLift.cuspAll_of_lowAll D X I
    (GlobalTheory.PairLift.lowAll_of_lowFock D X I (GlobalTheory.LowerMembersRule.lowFock D X I)))
  have rA : (Node.grid i 0).InRange D.R.m := ⟨hi.le, Nat.zero_le _⟩
  have rB : (Node.grid (i + 1) 0).InRange D.R.m := ⟨hi, Nat.zero_le _⟩
  obtain ⟨FA, a1, a2⟩ := exists_frame _ _ _ (W.onb_is _ rA)
  obtain ⟨FB, b1, b2⟩ := exists_frame _ _ _ (W.onb_is _ rB)
  have b3 : (frSgn true FB).cart = G.cartS W.cart (.chi i 0) := funext fun τ => by
    rw [cart_frSgn, b1]; rfl
  have b4 : (frSgn true FB).onb = G.onS W.onb (.chi i 0) := b2
  have hR : ∀ τ, PairPar (GlobalTheory.SignedHC.flip (S' τ)) (S τ)
      (att (GlobalTheory.Grid.cen D τ (D.R.m - i)) (GlobalTheory.Grid.rkV D (i + 1) 0)) (att (GlobalTheory.Grid.cen D τ (D.R.m - i)) (GlobalTheory.Grid.rkV D i 0)) :=
    fun τ => by
      rw [e, e', hc, parRow_eq, parRow_eq]
      exact GlobalTheory.GridParD.pairPar_X D hS i 0 τ hi (Nat.zero_le _)
  have hη : ∀ τ, HasInfExp D L.eta τ (1 / 2) := fun τ =>
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta
      (StepVac.hasInfQ_tau (a := fun _ => 1 / 2) ⟨_, fun _ => by norm_num, L.C.isEta.inf⟩) τ
  have hχ : ∀ τ, HasInfExp D (G.ch.chi (D.R.m - i)) τ (GlobalTheory.Grid.cen D τ (D.R.m - i)) := fun τ =>
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun τ => GlobalTheory.Grid.cen D τ (D.R.m - i)) (G.ch.chi_eq _ (by omega) (by omega))
      ⟨_, fun τ => by simp only [cen_eq, hc]; push_cast; rfl, G.ch.inf _ (by omega) (by omega)⟩ τ
  have hω : IsWeilExp W.ψ (GlobalTheory.Grid.sgn true (G.V (.grid (i + 1) 0))) (G.V (.grid i 0))
      (fun τ => att (GlobalTheory.Grid.cen D τ (D.R.m - i)) (GlobalTheory.Grid.rkV D (i + 1) 0))
      (fun τ => att (GlobalTheory.Grid.cen D τ (D.R.m - i)) (GlobalTheory.Grid.rkV D i 0)) (W.om (.chi i 0)) := by
    refine ⟨_, _, W.om_is (.chi i 0) rB, fun τ => ⟨?_, ?_⟩⟩
    · have r : (G.pS (.chi i 0)).rank = GlobalTheory.Grid.rkV D (i + 1) 0 := (node_isV G hL rB).rank
      rw [GridData.chrS, r]
      exact exp_att (hχ τ) (hη τ) _
    · have r : (G.pT (.chi i 0)).rank = GlobalTheory.Grid.rkV D i 0 := (node_isV G hL rA).rank
      rw [GridData.chrT, r]
      exact exp_att (hχ τ) (hη τ) _
  have hv := (W.vac_is i hi).2
  have v0 : IsVacF W.ψ W.θ (frSgn true FB) FA (W.vac i) := ⟨hv.theta, fun τ => by rw [b3, a1]; exact hv.fock τ⟩
  have n0 : W.vac i ≠ 0 := fun h => by
    obtain ⟨⟨p, hp⟩, h2⟩ := hv.norm
    have := h2 p hp
    simp [nrm2, h] at this
  have v1 : ∀ κ, IsVacF W.ψ W.θ (frSgn true FB) FA (W.cosVec i κ) := fun κ => by
    obtain ⟨u, hu, h⟩ := W.cosVec_is
    have th := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is (h i hi κ) hv.theta
    have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hu
    refine ⟨th, fun τ => ?_⟩
    rw [b3, a1]
    exact GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt W.ψ_std.1.1 W.θ_is ho.infPart_eq ho.conj.infPart_eq (h i hi κ) hv.theta th
      (hv.fock τ)
  obtain ⟨hν, h𝓕⟩ := (hM.row i hi.le).haar_fund
  obtain ⟨It, hIt⟩ := lifts_neg h3 h4 h5 hP hE W.θ_is W.ψ_std MA MB hR FA FB (cA.trans a1.symm) (cB.trans b1.symm) hω v0 n0 hν h𝓕
  refine ⟨It, fun F hF κ => ?_⟩
  obtain ⟨F', hF', h⟩ := hIt _ (v1 κ) F hF
  have ef : ∀ P, ptF W.ψ W.θ (frSgn true FB) FA (W.cosVec i κ) P = W.fock (.chi i 0) (W.cosVec i κ) P := fun P => by
    unfold ptF
    rw [b3, b4, a1, a2]
    rfl
  simp only [ef] at h
  exact ⟨F', hF', fun P v => ⟨fun g => (h P v g).1, funext fun g => (h P v g).2⟩⟩
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separating_family_extend_by_twist : _root_.GlobalTheory.FunPr.ThetaLocalInputs → PairEx → RowModels → RowStep := by
  first | exact @_root_.GlobalTheory.RowArrow.separatingFamily_extends_by_twisted_row | exact _root_.GlobalTheory.RowArrow.separatingFamily_extends_by_twisted_row | (intros; apply _root_.GlobalTheory.RowArrow.separatingFamily_extends_by_twisted_row <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SeparatingFamilyHasModels
section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SignedHC
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SepRows
theorem separating_family_has_models : _root_.GlobalTheory.FunPr.ThetaLocalInputs → CoreModels := fun h => coreModels_of_upq h.discreteSeriesUpqExists
end GlobalTheory.SepRows
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_separating_models : _root_.GlobalTheory.FunPr.ThetaLocalInputs → CoreModels := by
  first | exact @_root_.GlobalTheory.SepRows.separating_family_has_models | exact _root_.GlobalTheory.SepRows.separating_family_has_models | (intros; apply _root_.GlobalTheory.SepRows.separating_family_has_models <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SeparatingModelsOfSeparatingData
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.SepRows
open Matrix
theorem separating_models_of_separating_data : _root_.GlobalTheory.FunPr.ThetaLocalInputs → RowModels := by
  intro hP D _ _ T L μ0 _ sc hsc G W M _ i hi
  have hDS := hP.discreteSeriesUpqExists
  classical
  rcases Nat.eq_zero_or_pos i with rfl | hi1
  ·
    rw [parRow_zero]
    have hV : (G.V (.grid 0 0)).SigOK := D.sp.Y_sig (min 0 D.R.m)
    refine exists_model_of_enum hDS hV (W.onb (.grid 0 0)) (W.cart (.grid 0 0)) (fun τ => ?_)
      (W.onb_is (.grid 0 0) ⟨Nat.zero_le _, Nat.zero_le _⟩)
    obtain ⟨lam, ε, hE, hH, -, hq⟩ := GlobalTheory.ChainModels.goodPar_parB D (min 0 D.R.m) (min_le_right _ _) τ
    have e : parB (Ptw D) (min 0 D.R.m) τ = parB (Ptw D) 0 τ := by rw [Nat.zero_min]
    rw [e] at hE
    exact ⟨lam, ε, hE, hH, hq⟩
  · rw [hsc]
    have hX : (Node.grid i 0).InRange D.R.m := ⟨hi, Nat.zero_le _⟩
    have hv := G.isV hX (fun j e => by cases e; omega)
    refine exists_model_of_enum hDS hv.sigOK (W.onb (.grid i 0)) (W.cart (.grid i 0)) (fun τ => ?_) (W.onb_is _ hX)
    obtain ⟨hr, hc, hm⟩ := GlobalTheory.GridJoin.dualPar_shift_counts (if Odd (i + 0) then -(1 / 2) else 0)
      (GlobalTheory.GridParDCount.isRegular_parD D 1 τ hi (Nat.zero_le D.R.m))
    have hc' : (parRow D 1 i τ).card = (G.V (.grid i 0)).rank :=
      hc.trans ((GlobalTheory.GridParDCount.card_parD D 1 τ hi (Nat.zero_le _)).trans hv.rank.symm)
    obtain ⟨lam, ε, hE, hcount⟩ := GlobalTheory.GridJoin.exists_isEnum_of_regular hr hc'
    refine ⟨lam, ε, hE, isHCParam_dual_parV D i 0 τ lam ε hv.rank hE, ?_⟩
    rw [hcount, hv.sig]
    exact hm.trans (GlobalTheory.SignedHC.Model.nMinus_parD _ i 0)
end GlobalTheory.SepRows
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_models_of_separating_data : _root_.GlobalTheory.FunPr.ThetaLocalInputs → RowModels := by
  first | exact @_root_.GlobalTheory.SepRows.separating_models_of_separating_data | exact _root_.GlobalTheory.SepRows.separating_models_of_separating_data | (intros; apply _root_.GlobalTheory.SepRows.separating_models_of_separating_data <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaPairLiftCuspidalOfHypotheses
section
section
namespace GlobalTheory.PairLift
theorem thetaPairLift_cuspidal_of_hypotheses : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal := fun h =>
  liftsCuspidal_of_functoriality h.discreteSeriesCover h.harishChandraModules h.cuspRapidDecay h.casselmanWallach
end GlobalTheory.PairLift
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_thetaLift_cuspidal : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal := by
  first | exact @_root_.GlobalTheory.PairLift.thetaPairLift_cuspidal_of_hypotheses | exact _root_.GlobalTheory.PairLift.thetaPairLift_cuspidal_of_hypotheses | (intros; apply _root_.GlobalTheory.PairLift.thetaPairLift_cuspidal_of_hypotheses <;> assumption)
end
end

