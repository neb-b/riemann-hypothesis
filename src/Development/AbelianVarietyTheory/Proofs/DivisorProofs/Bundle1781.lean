module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1660
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1367
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1368
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1379
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1377
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1580
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1405
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1760
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsINeZeroKind
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1749
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1643
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1665
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1682
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumTransportCmPreservesAdmissibleForms
section
noncomputable section

open scoped TensorProduct Matrix ENNReal Classical
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.WeilAdmCM

variable {F : Type} [Field F] [NumberField F]

theorem std_fin (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (x : F) :
    ψ (pairA F 0 (algebraMap F (Af F) x)) =
      Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ F x : ℚ) : ℂ)) :=
  _root_.GlobalTheory.StdFinRat.std_fin_rat F ψ hψ x

theorem std_beta (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) :
    ∃ β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ,
      (∀ a, ψ (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0) : AdeleRing (𝓞 F) F) =
        Complex.exp (2 * Real.pi * Complex.I * β a)) ∧ ∀ a, a ≠ 0 → ∃ b, β (a * b) ≠ 0 :=
  _root_.GlobalTheory.StdBeta.stdBeta F ψ hψ

theorem fixed_invariant_compactSupport (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (κ : Type) [Fintype κ]
    (M : AddSubgroup ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)))
    (hM : IsOpen (M : Set ((κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)))) :
    ∃ (U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)) (K : Set (κ → FiniteAdeleRing (𝓞 F) F)),
      IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧ IsCompact (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∧
      IsCompact K ∧ ∀ Φ : (κ → AF F) → ℂ, (∀ m ∈ M, GlobalTheory.WeilM.schr ψ (GlobalTheory.WeilAdm.finE2 F m) Φ = Φ) →
        (∀ x, ∀ u ∈ U, Φ (x + GlobalTheory.WeilAdm.finE F u) = Φ x) ∧ ∀ x, (fun i => (x i).2) ∉ K → Φ x = 0 :=
  GlobalTheory.WeilAdm.fixed_schroedinger_invariant_compactSupport_bounded_annihilator ψ
    (fun O hO => GlobalTheory.ScalarAnnih.exists_compact_annihilator_finiteAdeles_traceChar F ψ hψ.1 (std_fin ψ hψ) O hO) κ M hM

theorem realcont (ps : AddChar (AF F) ℂ) (hψ : IsStd ps) (κ : Type) [Fintype κ]
    (L : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) ≃ₗ[ℝ]
      ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))
    (A : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →ₗ[ℂ] SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
    (C : ℝ≥0∞) (hC : C ≠ ⊤) (hA : ∀ f, ∫⁻ z, ‖A f z‖ₑ ^ 2 ≤ C * ∫⁻ z, ‖f z‖ₑ ^ 2)
    (hI : ∀ v (f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ), ⇑f' = GlobalTheory.WeilAdm.schrInf F ps v ⇑f →
      ⇑(A f') = GlobalTheory.WeilAdm.schrInf F ps (L v) ⇑(A f)) :
    Continuous A := by
  obtain ⟨β, hβ1, hnd⟩ := std_beta ps hψ
  obtain ⟨n, Q, P, hQP⟩ := _root_.GlobalTheory.WeilAdm.RealModel.exists_model F ps β hβ1 hnd κ
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.lintegral_sq_comp_linearEquiv_mixed F κ n Q
  let CQ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) Q
  let CQi := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) Q.symm
  have hCQ : ∀ f, ⇑(CQ f) = ⇑f ∘ ⇑Q := fun f => SchwartzMap.compCLMOfContinuousLinearEquiv_apply ℂ Q f
  have hCQi : ∀ g, ⇑(CQi g) = ⇑g ∘ ⇑Q.symm := fun g => SchwartzMap.compCLMOfContinuousLinearEquiv_apply ℂ Q.symm g
  have hQQ : ∀ f, CQi (CQ f) = f := fun f => by
    ext z; rw [hCQi, hCQ]; simp
  have hQQ' : ∀ g, CQ (CQi g) = g := fun g => by
    ext z; rw [hCQ, hCQi]; simp
  let A' : GlobalTheory.RealWeil.Sch (Fin n) →ₗ[ℂ] GlobalTheory.RealWeil.Sch (Fin n) := CQ.toLinearMap ∘ₗ A ∘ₗ CQi.toLinearMap
  have hA'apply : ∀ g, A' g = CQ (A (CQi g)) := fun g => rfl
  let L' : (Fin n ⊕ Fin n → ℝ) ≃ₗ[ℝ] (Fin n ⊕ Fin n → ℝ) := P.trans (L.trans P.symm)
  have hbound : ∀ g, ∫⁻ x, ‖A' g x‖ₑ ^ 2 ≤ C * ∫⁻ x, ‖g x‖ₑ ^ 2 := by
    intro g
    have e1 : ∫⁻ x, ‖A' g x‖ₑ ^ 2 = c * ∫⁻ z, ‖A (CQi g) z‖ₑ ^ 2 := by
      rw [← hc]
      simp only [hA'apply, hCQ, Function.comp_apply]
    have e2 : ∫⁻ x, ‖g x‖ₑ ^ 2 = c * ∫⁻ z, ‖CQi g z‖ₑ ^ 2 := by
      rw [← hc]
      simp only [hCQi, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
    rw [e1, e2, ← mul_assoc, mul_comm C c, mul_assoc]
    exact mul_le_mul' le_rfl (hA _)
  have hint : ∀ w (g g' : GlobalTheory.RealWeil.Sch (Fin n)), ⇑g' = GlobalTheory.RealWeil.rhoFun w ⇑g →
      ⇑(A' g') = GlobalTheory.RealWeil.rhoFun (L' w) ⇑(A' g) := by
    intro w g g' hg
    have h1 : ⇑(CQi g') = GlobalTheory.WeilAdm.schrInf F ps (P w) ⇑(CQi g) := by
      have := congrArg (fun u => u ∘ ⇑Q.symm) (hQP w ⇑(CQi g))
      simp only [Function.comp_assoc, ContinuousLinearEquiv.self_comp_symm, Function.comp_id] at this
      rw [this, hCQi, hg, ← hCQ, hQQ']
    have h2 := hI (P w) (CQi g) (CQi g') h1
    have hL' : P (L' w) = L (P w) := P.apply_symm_apply _
    have h3 : ⇑(A (CQi g')) = GlobalTheory.WeilAdm.schrInf F ps (P (L' w)) ⇑(A (CQi g)) := by
      rw [h2]
      exact congrArg (fun v => GlobalTheory.WeilAdm.schrInf F ps v ⇑(A (CQi g))) hL'.symm
    calc ⇑(A' g') = ⇑(A (CQi g')) ∘ ⇑Q := hCQ _
      _ = GlobalTheory.WeilAdm.schrInf F ps (P (L' w)) ⇑(A (CQi g)) ∘ ⇑Q := congrArg (· ∘ ⇑Q) h3
      _ = GlobalTheory.RealWeil.rhoFun (L' w) (⇑(A (CQi g)) ∘ ⇑Q) := hQP _ _
      _ = GlobalTheory.RealWeil.rhoFun (L' w) ⇑(A' g) := congrArg (GlobalTheory.RealWeil.rhoFun (L' w)) (hCQ _).symm
  have hcont : Continuous A' :=
    _root_.GlobalTheory.RealWeil.continuous_of_dRho_intertwine_of_L2_bound (Fin n) L' A' C hC hbound (_root_.GlobalTheory.RealWeil.DRhoTransfer.dRho_intertwine (Fin n) L'.toLinearMap A' C hC hbound hint)
  have hAeq : ⇑A = fun f => CQi (A' (CQ f)) := by
    funext f
    rw [hA'apply, hQQ, hQQ]
  rw [hAeq]
  exact CQi.continuous.comp (hcont.comp CQ.continuous)


open GlobalTheory.WeilAdm in
set_option maxHeartbeats 1000000 in
theorem weilAdmissible_of_heisenberg_unitary (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (κ : Type) [Fintype κ]
    (B : ((κ → AF F) × (κ → AF F)) ≃ₗ[AF F] ((κ → AF F) × (κ → AF F)))
    (O : Module.End ℂ ((κ → AF F) → ℂ))
    (hpres : ∀ φ ∈ GlobalTheory.WeilM.schA F κ, O φ ∈ GlobalTheory.WeilM.schA F κ)
    (himpl : ∀ w, ∀ φ ∈ GlobalTheory.WeilM.schA F κ, O (GlobalTheory.WeilM.schr ψ w φ) = GlobalTheory.WeilM.schr ψ (B w) (O φ))
    (hunit : ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ φ ∈ GlobalTheory.WeilM.schA F κ, ∫⁻ x, ‖O φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) :
    ∀ l ∈ (GlobalTheory.WeilM.adeleClass F).adm κ, l ∘ₗ O ∈ (GlobalTheory.WeilM.adeleClass F).adm κ := by
  intro l hl g hg
  obtain ⟨M, hMo, hM⟩ := GlobalTheory.WeilAdm.pureA_fixed_fin F ψ hψ.1 κ g hg
  obtain ⟨M', hM'o, hM'⟩ := GlobalTheory.WeilAdm.fintrans F κ B M hMo
  obtain ⟨U, K, hUo, hUc, hK, hfix⟩ := fixed_invariant_compactSupport ψ hψ κ M' hM'o
  obtain ⟨R, hRsb, hdec⟩ := GlobalTheory.WeilAdm.eq_sum_pureA_coset_indicator F κ U K hUo hUc hK
  obtain ⟨L, hL⟩ := GlobalTheory.WeilAdm.infLin_main F κ B
  obtain ⟨μ, hμ, C, c, hC, hc0, hcT, hpure, hslice⟩ := GlobalTheory.WeilAdm.HaarSplit.haar_pure_slice_bounds F κ g hg U hUo
  have hpA : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      GlobalTheory.WeilM.pureA F f g ∈ GlobalTheory.WeilM.schA F κ := fun f => Submodule.subset_span ⟨f, g, hg, rfl⟩
  have hfixed : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, ∀ m ∈ M',
      GlobalTheory.WeilM.schr ψ (finE2 F m) (O (GlobalTheory.WeilM.pureA F f g)) = O (GlobalTheory.WeilM.pureA F f g) := by
    intro f m hm
    obtain ⟨m0, hm0, hB⟩ := hM' m hm
    rw [← hB, ← himpl _ _ (hpA f), hM m0 hm0]
  have hs : ∀ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (r : κ → FiniteAdeleRing (𝓞 F) F),
      ∃ s : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, ∀ z,
        s z = slice F (O (GlobalTheory.WeilM.pureA F f g)) r z :=
    fun f r => exists_schwartz_slice _ (hpres _ (hpA f)) r
  choose sl hsl using hs
  let A : (κ → FiniteAdeleRing (𝓞 F) F) →
      (SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →ₗ[ℂ] SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) :=
    fun r =>
    { toFun := fun f => sl f r
      map_add' := fun f f' => by
        ext z
        rw [SchwartzMap.add_apply, hsl, hsl, hsl, show ⇑(f + f') = ⇑f + ⇑f' from funext fun _ => rfl, pureA_add, map_add (f := _)]
        rfl
      map_smul' := fun a f => by
        ext z
        rw [SchwartzMap.smul_apply, hsl, hsl, show ⇑(a • f) = a • ⇑f from funext fun _ => rfl, pureA_smul, map_smul]
        rfl }
  have hA : ∀ r f, ⇑(A r f) = slice F (O (GlobalTheory.WeilM.pureA F f g)) r := fun r f => funext (hsl f r)
  have hcont : ∀ r, Continuous (A r) := by
    intro r
    refine realcont ψ hψ κ L (A r) (C / c) (ENNReal.div_ne_top hC hc0) (fun f => ?_) (fun v f f' hf => ?_)
    · have h1 := hslice _ (hpres _ (hpA f)) (hfix _ (hfixed f)).1 r
      rw [hunit μ hμ _ (hpA f)] at h1
      have h2 := h1.trans (hpure f)
      rw [hA, ← ENNReal.mul_div_right_comm, ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hcT), mul_comm]
      exact h2
    · rw [hA, hA, hf, pureA_schrInf, himpl _ _ (hpA f), hL, slice_schr]
  have hT : ∀ r ∈ R, ∃ T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      l (GlobalTheory.WeilM.pureA F f (Set.indicator {y | y - r ∈ U} fun _ => (1 : ℂ))) = T f :=
    fun r hr => hl _ (hRsb r hr)
  choose T hT using hT
  refine ⟨∑ r ∈ R.attach, (T r.1 r.2).comp ⟨A r.1, hcont r.1⟩, fun f => ?_⟩
  have hΦ := hdec (O (GlobalTheory.WeilM.pureA F f g)) (hfix _ (hfixed f)).1 (hfix _ (hfixed f)).2
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.comp_apply, hΦ, map_sum, ContinuousLinearMap.sum_apply, ← Finset.sum_attach R]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← hA, hT r.1 r.2]
  rfl

end GlobalTheory.WeilAdmCM

namespace GlobalTheory.WeilAdmCM

theorem transport_adm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om →
              ∀ p, ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ om p ∈ (adeleClass F).adm κ := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ0 hξσ χS χT hcS hcT hrS hrT ω hω JA JB ξ hJA hJB κ _ co hco om htr p l hl
  have hP : (∀ p, ∀ φ ∈ schA F κ, om p φ ∈ schA F κ) ∧
      ∀ p w, ∀ φ ∈ schA F κ, om p (co.rho B.ψ w φ) = co.rho B.ψ (actAB (cA σ) p w) (om p φ) :=
    GlobalTheory.T.transportedWeilDatum_CM_preserves_schwartz_heisenberg F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hξσ χS χT hcS hcT hrS hrT ω hω JA JB ξ hJA hJB κ co hco om htr
  have hU : IsUnitaryOn (adeleClass F) om :=
    _root_.GlobalTheory.WeilAdmCMUnit.isUnitaryOn_transport F E σ B hB nS nT JS JT hS hT ξ₀ hξ0 hξσ χS χT hcS hcT hrS hrT ω hω JA JB ξ hJA hJB κ co hco om htr
  refine weilAdmissible_of_heisenberg_unitary B.ψ hB.std κ (co.e.symm.trans ((GlobalTheory.WeilAdm.actLin _ p).trans co.e)) (om p) (hP.1 p)
    (fun w φ hφ => ?_) (fun μ hμ φ hφ => hU μ hμ p φ hφ) l hl
  have h := hP.2 p (co.e.symm w) φ hφ
  simp only [GlobalTheory.WeilM.Darboux.rho, LinearEquiv.apply_symm_apply] at h
  exact h

end GlobalTheory.WeilAdmCM

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityTensorModelVW
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram blkU conjU UB)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple UAt ratU mat Acts SInf)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.LFun
open ValuativeRel

noncomputable section
namespace GlobalTheory.WeilLocalityVW

theorem comm_off {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : Chars F E) (om : Rep σ Γ.V Γ.W) (om' : Rep σ Γ.V' Γ.W)
    (hTr : IsTriple Bs Γ X om om') (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (k : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.W.J)
    (hk : k ∈ UAt σ Γ.W (evFin F v)) (u : AF F) (hu : evFin F v u = 0) (p q : Fin a × Fin (a + a') → AF F)
    (Φ : (Fin a × Fin (a + a') → AF F) → ℂ) (hΦ : Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a'))) :
    om (1, k) (GlobalTheory.WeilM.schr Bs.ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr Bs.ψ (u • p, u • q) (om (1, k) Φ) := by
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil
  set w := Γ.M.co.e.symm (p, q) with hw
  have he : Γ.M.co.e (u • w) = (u • p, u • q) := by
    rw [LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]
  have h0 : u • (mat k - 1) = 0 := hk u hu
  have hact : GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ)
      ((1, k) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V.J × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.W.J) (u • w) = u • w := by
    have h1 : (u • w) * (mat k)ᵀ - u • w = w * (u • (mat k - 1))ᵀ := by
      rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.transpose_sub, Matrix.transpose_one, Matrix.mul_sub,
        Matrix.mul_one, Matrix.smul_mul, smul_sub]
    rw [h0, Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at h1
    simp only [GlobalTheory.WeilM.actAB]
    simpa [mat] using h1
  have h2 := hW.impl (1, k) (u • w) Φ hΦ
  simp only [GlobalTheory.WeilM.Darboux.rho, he, hact] at h2
  exact h2

theorem liftV_one_mul {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (b : AF F) :
    GlobalTheory.LatVac.liftV v 1 * b = GlobalTheory.LatVac.liftV v (evFin F v b) := by
  refine Prod.ext ?_ ?_
  · exact zero_mul _
  · change GlobalTheory.AdelicU.singleFin v 1 * b.2 = GlobalTheory.AdelicU.singleFin v (evFin F v b)
    apply GlobalTheory.AdelicU.af_ext
    intro w
    rw [map_mul]
    by_cases hw : w = v
    · subst hw
      rw [GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self, one_mul]
      rfl
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw, GlobalTheory.AdelicU.evalV_singleFin_ne hw, zero_mul]

theorem schr_trans {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ]
    (w : κ → AF F) (Φ : (κ → AF F) → ℂ) : GlobalTheory.WeilM.schr ψ (w, 0) Φ = fun y => Φ (y + w) := by
  funext y
  simp [GlobalTheory.WeilM.schr]

theorem locality : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : Chars F E) (om : Rep σ Γ.V Γ.W) (om' : Rep σ Γ.V' Γ.W), IsTriple Bs Γ X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ k ∈ UAt σ Γ.W (evFin F v), ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), Acts (evFin F v) (om (1, k)) φ φ₁ := by
  intro F E _ _ _ _ _ σ a a' Bs Γ X om om' hTr v k hk φ hφ
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil
  set T := om (1, k) with hTdef
  have hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), T Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun Φ hΦ => hW.pres (1, k) Φ hΦ
  have hcomm : ∀ u : AF F, evFin F v u = 0 → ∀ p q : Fin a × Fin (a + a') → AF F,
      ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')),
        T (GlobalTheory.WeilM.schr Bs.ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr Bs.ψ (u • p, u • q) (T Φ) :=
    fun u hu p q Φ hΦ => comm_off Bs Γ X om om' hTr v k hk u hu p q Φ hΦ
  have hfib := GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise v Bs.ψ T hTr.base.std (GlobalTheory.PsiNontrivAt.exists_psiAt_ne_one Bs.ψ hTr.base.std) hkeep
    (fun μ hμ Φ hΦ => hW.unit μ hμ (1, k) Φ hΦ) hcomm
  have htr : ∀ u : AF F, evFin F v u = 0 → ∀ p : Fin a × Fin (a + a') → AF F,
      ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), T (fun y => Φ (y + u • p)) = fun y => T Φ (y + u • p) := by
    intro u hu p Φ hΦ
    have h := hcomm u hu p 0 Φ hΦ
    rw [smul_zero, schr_trans, schr_trans] at h
    exact h
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (Fin a × Fin (a + a')) v
  refine ⟨fun t => (R 0)⁻¹ * T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)), ?_, ?_⟩
  · have h4 := GlobalTheory.LatVac.restrict_liftV_mem_SB v _ (hkeep _ (hR φ hφ).2)
    exact (GlobalTheory.WeilM.SB _).smul_mem (R 0)⁻¹ h4
  · intro r hr
    funext y
    set u : AF F := 1 - GlobalTheory.LatVac.liftV v 1 with hudef
    have hu : evFin F v u = 0 := by simp [hudef, GlobalTheory.LatVac.evFin_liftV]
    set p : Fin a × Fin (a + a') → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i)) with hpdef
    have hyp : y + u • (-y) = p := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef]
      rw [← liftV_one_mul]
      ring
    have hpat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) p := by
      intro u' hu'
      funext i
      exact GlobalTheory.LatVac.at_liftV v _ u' hu'
    set Φ₀ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R with hΦ₀
    set Φ₁ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r with hΦ₁
    set Φ₂ : (Fin a × Fin (a + a') → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
    have hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _ := (hR φ hφ).2
    have hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _ := Submodule.smul_mem _ _ (GlobalTheory.SchwartzTranslation.schA_add_const _ _ hm₀)
    have hfz : ∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → (Φ₁ - Φ₂) (y + z) = 0 := by
      intro z hz
      have e1 : r (y + z) = r y := hr.1 y z hz
      have e2 : y + z + u • (-y) = p + z := by rw [← hyp]; abel
      have hpz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (p + z) := fun u' hu' => by
        rw [smul_add, hpat u' hu', hz u' hu', add_zero]
      have e3 : R (p + z) = R 0 := by simpa using (hR φ hφ).1 0 (p + z) hpz
      have e4 : (fun i => evFin F v ((y + z + u • (-y)) i)) = fun i => evFin F v ((y + z) i) := by
        funext i
        simp [hu]
      simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
      rw [e4, e2, e3, e1]
      field_simp
      ring
    have h0 := hfib (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hfz
    rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
    have h2 : T Φ₂ y = (r y / R 0) * T Φ₀ p := by
      rw [hΦ₂, map_smul, htr u hu (-y) Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hyp]
    rw [h0, h2]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, hpdef]
    field_simp

end GlobalTheory.WeilLocalityVW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupV
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace GlobalTheory.WeilLocality

theorem comm_off : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J), x ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.V' (evFin F v) →
    ∀ u : AF F, evFin F v u = 0 → ∀ p q : Fin a' × Fin (a + a') → AF F,
    ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')),
      om' (x, 1) (GlobalTheory.WeilM.schr Bs.ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr Bs.ψ (u • p, u • q) (om' (x, 1) Φ) := by
  intro F E _ _ _ _ _ σ a a' Bs Γ X om om' hTr v x hx u hu p q Φ hΦ
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil'
  set w := Γ.M'.co.e.symm (p, q) with hw
  have he : Γ.M'.co.e (u • w) = (u • p, u • q) := by
    rw [LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]
  have h0 : u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x - 1) = 0 := hx u hu
  have hact : GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) ((x, 1) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J × GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.W.J) (u • w) = u • w := by
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x * (u • w) - u • w = (u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x - 1)) * w := by
      rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_smul, smul_sub]
    rw [h0, Matrix.zero_mul, sub_eq_zero] at h1
    simp only [GlobalTheory.WeilM.actAB]
    simpa [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat] using h1
  have h2 := hW.impl (x, 1) (u • w) Φ hΦ
  simp only [GlobalTheory.WeilM.Darboux.rho, he, hact] at h2
  exact h2

theorem liftV_one_mul {F : Type} [Field F] [NumberField F] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (b : AF F) :
    GlobalTheory.LatVac.liftV v 1 * b = GlobalTheory.LatVac.liftV v (evFin F v b) := by
  refine Prod.ext ?_ ?_
  · exact zero_mul _
  · change GlobalTheory.AdelicU.singleFin v 1 * b.2 = GlobalTheory.AdelicU.singleFin v (evFin F v b)
    apply GlobalTheory.AdelicU.af_ext
    intro w
    rw [map_mul]
    by_cases hw : w = v
    · subst hw
      rw [GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self, one_mul]
      rfl
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw, GlobalTheory.AdelicU.evalV_singleFin_ne hw, zero_mul]

theorem schr_trans {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) {κ : Type} [Fintype κ]
    (w : κ → AF F) (Φ : (κ → AF F) → ℂ) : GlobalTheory.WeilM.schr ψ (w, 0) Φ = fun y => Φ (y + w) := by
  funext y
  simp [GlobalTheory.WeilM.schr]

theorem locality : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (x : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ Γ.V'.J), x ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.V' (evFin F v) →
    ∃ S : ((Fin a' × Fin (a + a') → Fv F v) → ℂ) → (Fin a' × Fin (a + a') → Fv F v) → ℂ,
      ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v), S φ ∈ GlobalTheory.WeilM.SB _ ∧
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin F v) (om' (x, 1)) φ (S φ) := by
  intro F E _ _ _ _ _ σ a a' Bs Γ X om om' hTr v x hx
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil'
  set T := om' (x, 1) with hTdef
  have hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')), T Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun Φ hΦ => hW.pres (x, 1) Φ hΦ
  have hcomm := comm_off Bs Γ X om om' hTr v x hx
  have hfib := GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise v Bs.ψ T hTr.base.std (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace Bs.ψ hTr.base.std) hkeep (fun μ hμ Φ hΦ => hW.unit μ hμ (x, 1) Φ hΦ) hcomm
  have htr : ∀ u : AF F, evFin F v u = 0 → ∀ p : Fin a' × Fin (a + a') → AF F,
      ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a' × Fin (a + a')), T (fun y => Φ (y + u • p)) = fun y => T Φ (y + u • p) := by
    intro u hu p Φ hΦ
    have h := hcomm u hu p 0 Φ hΦ
    rw [smul_zero, schr_trans, schr_trans] at h
    exact h
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin a' × Fin (a + a')) v
  refine ⟨fun φ t => (R 0)⁻¹ * T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)),
    fun φ hφ => ⟨?_, ?_⟩⟩
  · have h4 := GlobalTheory.T.adelicSchwartz_restrict_finitePlace_mem_schwartzBruhat v _ (hkeep _ (hR φ hφ).2)
    exact (GlobalTheory.WeilM.SB _).smul_mem (R 0)⁻¹ h4
  · intro r hr
    funext y
    set u : AF F := 1 - GlobalTheory.LatVac.liftV v 1 with hudef
    have hu : evFin F v u = 0 := by simp [hudef, GlobalTheory.LatVac.evFin_liftV]
    set p : Fin a' × Fin (a + a') → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i)) with hpdef
    have hyp : y + u • (-y) = p := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef]
      rw [← liftV_one_mul]
      ring
    have hpat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) p := by
      intro u' hu'
      funext i
      exact GlobalTheory.LatVac.at_liftV v _ u' hu'
    set Φ₀ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R with hΦ₀
    set Φ₁ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r with hΦ₁
    set Φ₂ : (Fin a' × Fin (a + a') → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
    have hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _ := (hR φ hφ).2
    have hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _ := Submodule.smul_mem _ _ (_root_.GlobalTheory.SchwartzTranslation.schA_add_const _ _ hm₀)
    have hfz : ∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → (Φ₁ - Φ₂) (y + z) = 0 := by
      intro z hz
      have e1 : r (y + z) = r y := hr.1 y z hz
      have e2 : y + z + u • (-y) = p + z := by rw [← hyp]; abel
      have hpz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (p + z) := fun u' hu' => by
        rw [smul_add, hpat u' hu', hz u' hu', add_zero]
      have e3 : R (p + z) = R 0 := by simpa using (hR φ hφ).1 0 (p + z) hpz
      have e4 : (fun i => evFin F v ((y + z + u • (-y)) i)) = fun i => evFin F v ((y + z) i) := by
        funext i
        simp [hu]
      simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
      rw [e4, e2, e3, e1]
      field_simp
      ring
    have h0 := hfib (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hfz
    rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
    have h2 : T Φ₂ y = (r y / R 0) * T Φ₀ p := by
      rw [hΦ₂, map_smul, htr u hu (-y) Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hyp]
    rw [h0, h2]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, hpdef]
    field_simp
    ring

end GlobalTheory.WeilLocality
end
end

