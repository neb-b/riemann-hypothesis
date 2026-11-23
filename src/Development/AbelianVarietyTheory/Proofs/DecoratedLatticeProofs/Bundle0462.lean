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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0458
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduesOfCompletionAtPrimeWithUniformizer
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStdFr
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandBesselPeriodInvariantProof
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleUnif
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0344
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleUnfoldingStepAtGluedFinitePlace
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0369
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAdeleIdempotentOfFMulSelf
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0451
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0380
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatPeriodEqIntegralEvaluationPeriods
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainTwistPlacesSplitUnramifiedQuotients
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ChainTw.TwPlaces

variable {D : D7}

theorem absNorm_under_of_ne {w w' : HeightOneSpectrum (𝓞 D.host.E)} (h : w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F))
    (hne : w ≠ w') : Ideal.absNorm (w.under (𝓞 D.host.F)).asIdeal = Ideal.absNorm w.asIdeal := by
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.AdelicU.existsUnique_splitPrime_eq (GlobalTheory.AdelicU.isCMExt_host D) hne rfl h.symm
  rw [← GlobalTheory.LFun.SplitChart.absNorm_splitPrime τ, hτ]

theorem conjPrime_ne_of_mem {P : Finset (Pl D.host.E)} {e : AE D} (h : IsIdemSum e P) {PP : Pl D.host.E} (hPP : PP ∈ P) :
    GlobalTheory.IdemSupport.cP PP ≠ PP := by
  classical
  have hinj := GlobalTheory.LevelPlaces.under_injOn h
  obtain ⟨⟨es, hes, rfl⟩, h0⟩ := h
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  intro hc
  have hd : ∀ Q ∈ P, GlobalTheory.IdemSupport.IsDelta Φ Q (es Q) := fun Q hQ =>
    GlobalTheory.IdemSupport.delta_of_isIdemAt hΦ (hes Q hQ)
  have e1 : Φ (∑ Q ∈ P, es Q) PP = 1 := by
    rw [GlobalTheory.LevelPlaces.ev_sum, Finset.sum_eq_single PP (fun Q hQ hQP => (hd Q hQ).2.2 PP (Ne.symm hQP))
      (fun h => absurd hPP h), (hd PP hPP).2.1]
  have e2 : Φ (cA D (∑ Q ∈ P, es Q)) PP = 1 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, GlobalTheory.LevelPlaces.ev_sum, Finset.sum_eq_single PP ?_ (fun h => absurd hPP h)]
    · have := (GlobalTheory.IdemSupport.delta_conj hΦ (hd PP hPP)).2.1
      rwa [hc] at this
    · intro Q hQ hQP
      refine (GlobalTheory.IdemSupport.delta_conj hΦ (hd Q hQ)).2.2 PP fun hQc => hQP ?_
      have hv : Q.under (𝓞 D.host.F) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) := by rw [← GlobalTheory.IdemSupport.under_cP Q, ← hQc]
      exact hinj (Finset.mem_coe.2 hQ) (Finset.mem_coe.2 hPP) hv
  have e3 := GlobalTheory.IdemSupport.ev_mul (Φ := Φ) (∑ Q ∈ P, es Q) (cA D (∑ Q ∈ P, es Q)) PP
  rw [h0, GlobalTheory.IdemSupport.ev_zero, e1, e2, one_mul] at e3
  exact zero_ne_one e3

theorem exists_fin_of_mem {m i : ℕ} (hi : i ∈ Finset.Icc 1 m) : ∃ k : Fin m, (k : ℕ) + 1 = i := by
  rw [Finset.mem_Icc] at hi
  exact ⟨⟨i - 1, by omega⟩, by simp; omega⟩

end GlobalTheory.ChainTw.TwPlaces


open GlobalTheory.ChainTw.TwPlaces in
theorem GlobalTheory.ChainTw.twist_places : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → (∀ v, v ∈ c.S ↔ v ∈ w.S₀ ∨ ∃ PP ∈ w.Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v) ∧ (∀ PP ∈ w.Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∉ w.S₀) ∧ Set.InjOn (fun PP : Pl D.host.E => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) w.Q ∧ (∀ PP ∈ w.Q, Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) ∧ Ideal.absNorm ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)).asIdeal = Ideal.absNorm PP.asIdeal ∧ ∃ PP' : Pl D.host.E, PP' ≠ PP ∧ (∀ P : Pl D.host.E, P.under (𝓞 D.host.F) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ↔ P = PP ∨ P = PP') ∧ Ideal.absNorm PP'.asIdeal = Ideal.absNorm PP.asIdeal ∧ ∀ i ∈ Finset.Icc 1 D.R.m, ∀ j ∈ Finset.Icc 1 D.R.m, GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ j)⁻¹) PP' = (GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ j)⁻¹) PP)⁻¹) ∧ ∀ i ∈ Finset.Icc 1 D.R.m, ∀ j ∈ Finset.Icc 1 D.R.m, GlobalTheory.LFun.UnrOff (F := D.host.F) (c.μ i * (c.μ j)⁻¹) w.S₀ := by
  intro D c w hw
  classical
  obtain ⟨e, he⟩ := hw.com.split
  have hinj : Set.InjOn (fun PP : Pl D.host.E => (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) (c.Pg : Set (Pl D.host.E)) :=
    GlobalTheory.LevelPlaces.under_injOn he
  have hQ : ∀ PP ∈ w.Q, PP ∈ c.Pg := fun PP h => hw.union ▸ Finset.mem_union_right _ h
  have hPg : ∀ PP ∈ w.Pg, PP ∈ c.Pg := fun PP h => hw.union ▸ Finset.mem_union_left _ h
  have hS : ∀ v, v ∈ c.S ↔ v ∈ w.S₀ ∨ ∃ PP ∈ w.Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = v := by
    intro v
    simp only [Com.S, Twist.S₀, Finset.coe_image, Set.mem_image, Finset.mem_coe, Finset.mem_image, hw.union,
      Finset.mem_union]
    constructor
    · rintro ⟨PP, h | h, rfl⟩
      · exact Or.inl ⟨PP, h, rfl⟩
      · exact Or.inr ⟨PP, h, rfl⟩
    · rintro (⟨PP, h, rfl⟩ | ⟨PP, h, rfl⟩)
      · exact ⟨PP, Or.inl h, rfl⟩
      · exact ⟨PP, Or.inr h, rfl⟩
  have hnot : ∀ PP ∈ w.Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∉ w.S₀ := by
    intro PP hPP h
    simp only [Twist.S₀, Finset.coe_image, Set.mem_image, Finset.mem_coe] at h
    obtain ⟨PP₀, h0, he0⟩ := h
    have := hinj (Finset.mem_coe.2 (hPg PP₀ h0)) (Finset.mem_coe.2 (hQ PP hPP)) he0
    subst this
    exact Finset.disjoint_left.1 hw.disj h0 hPP
  have hsplit : ∀ PP ∈ c.Pg, Formalism.DivisionValues.conjPl PP ≠ PP := fun PP h => by
    rw [GlobalTheory.LevelPlaces.conjPl_eq_cP]; exact conjPrime_ne_of_mem he h
  have hres : ∀ PP ∈ w.Q, ∀ i ∈ Finset.Icc 1 D.R.m, ∀ j ∈ Finset.Icc 1 D.R.m,
      GlobalTheory.LFun.UnrAt (F := D.host.F) (c.μ i * (c.μ j)⁻¹) PP := by
    intro PP hPP i hi j hj
    obtain ⟨a, rfl⟩ := exists_fin_of_mem hi
    obtain ⟨b, rfl⟩ := exists_fin_of_mem hj
    obtain ⟨Ha, hca, hra⟩ := hw.com.res a
    obtain ⟨Hb, hcb, hrb⟩ := hw.com.res b
    have ra := hra PP (hQ PP hPP)
    have rb := hrb PP (hQ PP hPP)
    rw [hw.chiQ _ PP hPP, inv_inv] at ra rb
    exact GlobalTheory.T.heckeCharUnramifiedAt_quotient_same_residual D _ _ Ha Hb PP _ hca hcb ra rb
  have hre : ∀ i ∈ Finset.Icc 1 D.R.m, ∀ j ∈ Finset.Icc 1 D.R.m, ResEta D (c.μ i * (c.μ j)⁻¹) 0 := by
    intro i hi j hj
    obtain ⟨-, ⟨η, hη⟩, hi'⟩ := hw.com.chars.2.2.2.2 i hi
    obtain ⟨-, -, hj'⟩ := hw.com.chars.2.2.2.2 j hj
    refine ⟨⟨η, hη⟩, fun η' hη' a => ?_⟩
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hi' η' hη' a, hj' η' hη' a]
    simp
  refine ⟨hS, hnot, hinj.mono fun x hx => Finset.mem_coe.2 (hQ x (Finset.mem_coe.1 hx)), fun PP hPP => ?_, ?_⟩
  · have hne : Formalism.DivisionValues.conjPl PP ≠ PP := hsplit PP (hQ PP hPP)
    have hu : (Formalism.DivisionValues.conjPl PP).under (𝓞 D.host.F) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) := ParInv.under_conjPl PP
    refine ⟨GlobalTheory.LFun.ConjPlace.isSplit_of_ne hne.symm rfl hu, absNorm_under_of_ne hu.symm hne.symm,
      Formalism.DivisionValues.conjPl PP, hne, fun P => ⟨fun h => ?_, ?_⟩, ParInv.absNorm_conjPl' PP, fun i hi j hj => ?_⟩
    · rcases GlobalTheory.GridPlaces.eq_or_eq_conjP h with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (h1.trans (ParInv.conjP_eq_conjPl' PP))
    · rintro (rfl | rfl)
      · rfl
      · exact hu
    · exact (GlobalTheory.T.unramified_conjugate_place_inverse_uniformizer_value D _ (hre i hi j hj) PP _ hu.symm hne.symm (hres PP hPP i hi j hj)).2
  · intro i hi j hj W hW
    by_cases hWS : W.under (𝓞 D.host.F) ∈ c.S
    · rcases (hS _).1 hWS with h | ⟨PP, hPP, hPPW⟩
      · exact absurd h hW
      · rcases GlobalTheory.GridPlaces.eq_or_eq_conjP hPPW.symm with h1 | h1
        · rw [h1]; exact hres PP hPP i hi j hj
        · have hne := hsplit PP (hQ PP hPP)
          rw [h1, ParInv.conjP_eq_conjPl']
          exact (GlobalTheory.T.unramified_conjugate_place_inverse_uniformizer_value D _ (hre i hi j hj) PP _ (ParInv.under_conjPl PP).symm hne.symm
            (hres PP hPP i hi j hj)).1
    · obtain ⟨a, rfl⟩ := exists_fin_of_mem hi
      obtain ⟨b, rfl⟩ := exists_fin_of_mem hj
      have hW' : W ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) := hWS
      exact (hw.com.unr a W hW').mul (hw.com.unr b W hW').inv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletionSmallIntegersInPrimeDense
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.SymBridge.ComplDense

theorem small_in_prime_and_dense : ∀ (E : Type) [Field E] [NumberField E] (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (PP : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ), GlobalTheory.SymBridge.IsCompl PP q ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → (∀ z : 𝓞 E, valuation k (ι z) < 1 → z ∈ PP.asIdeal) ∧ ∀ y : k, y ∈ 𝒪[k] → ∃ z : 𝓞 E, valuation k (y - ι z) < 1 := by
  intro E _ _ k _ _ _ _ PP q ι ϖ h hu
  refine ⟨fun z hz => (GlobalTheory.SymBridge.ComplRes.mem_P_iff h hu z).mpr hz, fun y hy => ?_⟩
  obtain ⟨i, -, hv⟩ := GlobalTheory.SymBridge.ComplRes.exists_rep_one h hu y ((Valuation.mem_integer_iff _ _).mp hy)
  refine ⟨(i : 𝓞 E), ?_⟩
  have e : ι (((i : ℕ) : 𝓞 E) : E) = (i : k) := by simp
  rw [e]
  exact lt_of_le_of_lt hv (GlobalTheory.SymBridge.ComplRes.v_unif_lt_one hu)

end GlobalTheory.SymBridge.ComplDense
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandLeftInvariantBesselSecond
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

noncomputable section

namespace GlobalTheory.DStepCell.LeftSecond

variable {D : D7}

theorem contAut_translate {V : HSp D} {f : GA D V → ℂ} (h : GA D V) (hf : IsContAut V f) : IsContAut V (rTrans h f) :=
  ⟨fun γ hγ x => by simp only [rTrans, mul_assoc, hf.1 γ hγ], hf.2.comp (continuous_mul_const h)⟩

theorem contAut_of_mem_multT {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {J : Set (GA D V)}
    {χ : GA D V → ℂ} {G : SmT M →ₗ[ℂ] (GA D V → ℂ)} (hG : G ∈ MultT θ M J χ) (x : SmT M) : IsContAut V (G x) := by
  have hadd : ∀ {f g : GA D V → ℂ}, IsContAut V f → IsContAut V g → IsContAut V (f + g) := fun hf hg =>
    ⟨fun γ hγ x => by simp only [Pi.add_apply, hf.1 γ hγ x, hg.1 γ hγ x], hf.2.add hg.2⟩
  have hsmul : ∀ {f : GA D V → ℂ}, IsContAut V f → ∀ c : ℂ, IsContAut V (c • f) := fun hf c =>
    ⟨fun γ hγ x => by simp only [Pi.smul_apply, hf.1 γ hγ x], hf.2.const_smul c⟩
  obtain ⟨T, hT, rfl⟩ := hG
  induction hT using Submodule.span_induction generalizing x with
  | mem T hT =>
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      rw [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
      exact hsmul ⟨(hT.aut v).left, (hT.aut v).cont⟩ r
    | add x y hx hy => rw [map_add (f := _)]; exact hadd hx hy
  | zero =>
    have h0 : IsContAut V (0 : GA D V → ℂ) := ⟨fun _ _ _ => rfl, continuous_const⟩
    simpa using h0
  | add T₁ T₂ _ _ h₁ h₂ => rw [map_add (f := _), LinearMap.add_apply]; exact hadd (h₁ x) (h₂ x)
  | smul c T _ h => rw [map_smul, LinearMap.smul_apply]; exact hsmul (h x) c

theorem theta_comb {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {P : Pl D → Prop}
    {e : WO S T →₀ ℂ} (he : CombAt P e) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (comb ψ S T e f) :=
  (GlobalTheory.HeisComb.main D ψ S T).2.2.1 e f hf
    ((GlobalTheory.DisjComb.main D ψ hψ S T P (fun _ => False) (fun _ _ h => h)).2.1 e he).1 hψ

theorem integ_left_second : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ r ∈ besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o, ∀ q₁ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f q₁ (r * q₂) = integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ := by
  intro D c v t w hc hv ht hF _ _ _ _ _ _ j σ h Ψ₁ Ψ₂ h₁ h₂ φ hφ G x a _ f hf r hr q₁ q₂
  have hΦ₁ := theta_comb hc.std (hv.atG j).1 (theta_comb hc.std (hF.atQ j).1 h₁.1)
  have hΦ₂ := theta_comb hc.std (hv.atG (j + 1)).1 (theta_comb hc.std (hF.atQ (j + 1)).1 h₂.1)
  obtain ⟨J, χ, hle⟩ := ht.CC (j + 1 + 1) (by omega)
  have hfc : IsContAut (c.V (j + 1 + 1)) f := hf ▸ contAut_translate _ (contAut_of_mem_multT (hle G.2) x)
  unfold integ
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun g _ => congrArg (w.ε j α g * ·) ?_
  exact (_root_.GlobalTheory.FinPl.HandInvPf.handInv D c.ψ σ (c.B j (σ + 1) h) (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (t.sBF j (σ + 1) h)
    (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) _ _ hΦ₁ hΦ₂ (φ α) (hv.ram j _ (hφ α)).1 g q₁ q₂).2 f hfc r hr

end GlobalTheory.DStepCell.LeftSecond

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandLeftInvariantFourierJacobiFir
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DStepCell

namespace GlobalTheory.DStepCell.LeftOne

theorem vac_empty_comb {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {P : Pl D → Prop}
    {e : WO S T →₀ ℂ} (he : CombAt P e) {LS : Lat S} {LT : Lat T} {f : WO S T → ℂ}
    (hf : Vac ψ S T LS LT (fun _ => False) f) : Vac ψ S T LS LT (fun _ => False) (comb ψ S T e f) :=
  ((GlobalTheory.DisjComb.main D ψ hψ S T P (fun _ => False) (fun _ _ h => h)).2.1 e he).2 LS LT f hf

theorem vac_empty {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D}
    {LS : Lat S} {LT : Lat T} (hS : IsSelfDualC S LS) (hT : IsSelfDualC T LT) {f : WO S T → ℂ}
    (hf : Vac ψ S T LS LT (fun _ => True) f) : Vac ψ S T LS LT (fun _ => False) f := by
  have h := (GlobalTheory.DisjComb.main D ψ hψ S T (fun _ => True) (fun _ => False) (fun _ _ h => h)).2.2.2.2 LS LT f hS hT
  have e : (fun p : Pl D => True ∨ False) = fun _ => True := by funext p; simp
  rw [e] at h
  exact (h.1 hf).2

theorem main : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t), c.Is → v.Is → t.Is → VForm v w → WeilOK (t := t) v → OffLaw v w → GSupp (t := t) v → QFin v w → ContrLaw D → FlatLaw D → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m) Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (fun _ => True) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (fun _ => True) Ψ₂ → ∀ φ : t.Ch j → GA D (c.X j) → ℂ, (∀ α, φ α ∈ v.RamAd j) → ∀ (G : t.CC (j + 1 + 1)) x, ∀ a ∈ GinfC _, ∀ f, f = rTrans (a * v.b (j + 1 + 1)) (G.1 x) → ∀ r ∈ jacGrp (c.jac j (σ + 1) h).d, ∀ q₁ q₂, integ v w j σ h Ψ₁ Ψ₂ φ f (r * q₁) q₂ = integ v w j σ h Ψ₁ Ψ₂ φ f q₁ q₂ := by
  intro D c v t w hc hv _ hF _ _ _ _ _ _ j σ h Ψ₁ Ψ₂ h₁ h₂ φ hφ G x a _ f _ r hr q₁ q₂
  have s0 := hv.sd j (by omega)
  have s1 := hv.sd (j + 1) (by omega)
  have s2 := hv.sd (j + 1 + 1) (by omega)
  have t₁ := (vac_empty_comb hc.std (hv.atG j).1 (vac_empty_comb hc.std (hF.atQ j).1 (vac_empty hc.std s0 s1 h₁))).1
  have t₂ := (vac_empty_comb hc.std (hv.atG (j + 1)).1
    (vac_empty_comb hc.std (hF.atQ (j + 1)).1 (vac_empty hc.std s1 s2 h₂))).1
  unfold integ
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun g _ => ?_
  have key := (_root_.GlobalTheory.FinPl.HandInvPf.handInv D c.ψ σ _ _ _ (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) _ _ t₁ t₂ (φ α)
    (hv.ram j (φ α) (hφ α)).1 g q₁ q₂).1 r hr
  exact congrArg (fun z => w.ε j α g * (c.B (j + 1 + 1) σ (idx_step h)).per c.ψ z (rTrans q₂ f)) key

end GlobalTheory.DStepCell.LeftOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleUnfoldingStepAtGluedFinitePlaceStatement
section
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleUnfoldingStep_at_glued_finite_place : ∀ D : D7, GlobalTheory.FinPl.VertexGlued D := by
  first | exact @GlobalTheory.FinPl.Vertex.vertexGlued | exact GlobalTheory.FinPl.Vertex.vertexGlued | (intros; apply GlobalTheory.FinPl.Vertex.vertexGlued <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsChartPointRightTranslateStabilizerSplitPla
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.DiaChart

theorem decoratedLattice_unitScale_functional_keeps_frames {X : Formalism.L2.Col.Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y}
    (p : PtY (X := X) (n := n) ST SG Q y) (P : ST) (c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) (P' : HeightOneSpectrum (𝓞 X.E)) :
    ptFr (p.mv (Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco)).1.1 P' = ptFr p.1.1 P' := by
  by_cases h : (∀ (P₁ : Q) (x : Formalism.L2.Col.Sp X.E n), p.1.1.1.2 P₁ x ∈ (Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco).1.at P₁.1 ↔
      x ∈ Formalism.L2.Col.stdAt X.E n P₁.1) ∧ p.1.2 ∈ y.ys (Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco).1.N
  · have e : p.mv (Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco) =
        ⟨(⟨(Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco, p.1.1.1.2), h.1⟩, p.1.2), h.2⟩ := dif_pos h
    rw [e]
    unfold ptFr
    rfl
  · have e : p.mv (Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco) = p := dif_neg h
    rw [e]

theorem finM_mul' {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (g h : GA D V) :
    finM V hn (g * h) = finM V hn g * finM V hn h := by
  subst hn
  exact GlobalTheory.AdForm.RdLaw.finM_mul V g h

theorem ptOf_gl_dia : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 →
    ∀ g : 𝓀[k]ˣ → GL (Fin ((I.rec7 l Z).sp.X j).rank) k, (∀ s, g s • Q j i = s • Q j i) →
      ∀ b (c : {c // A.chOf j c = b}), ∃ e : 𝓀[k]ˣ ≃ ((I.atT l u a).Fv v)ˣ, ∀ s,
        ∃ z : TC.GA B (B.R.N j),
          z.1 = finM _ (rankN (I.rec7 l Z) j hj) (A.h j b c * (β j i).gl (g s)) ∧
          TC.PtOf (z * A.kb j b) (extTo I.SQ (((I.atIn u a).A j).diaPt v (e s) c.1).1.1) := by
  intro B X I hOk hPins l Z u a Ch A hA k _ _ _ _ ι p β Q L hStd j hj i v hv g hg b c
  obtain ⟨c, rfl⟩ := c
  obtain ⟨-, ρ, hρ⟩ := GlobalTheory.FinPl.SplitPt.resField_equiv (I.rec7 l Z) k (p i) v.1 hv
  refine ⟨(Units.mapEquiv ρ.toMulEquiv).toEquiv, fun s => ?_⟩
  obtain ⟨δ, hδ, huni, hint, hint'⟩ := GlobalTheory.AdForm.frameGl_int I hOk hPins l Z u a k ι p β Q L hStd j hj i v hv (g s) s (hg s)
  have htriv := _root_.GlobalTheory.AdForm.FrameTriv.frame_trivial_off I hOk hPins l Z u a k ι p β Q L hStd j hj i v hv (g s) δ hδ
  have hrow := GlobalTheory.AdForm.lastRow_inv_frame I hOk hPins l Z u a k ι p β Q L hStd j hj i v hv ρ hρ (g s) s (hg s) δ hδ hint'
  have hR := hA.reads j hj
  let y : TC.GA B (B.R.N j) := ((A.K j hj (A.chOf j c)).y ⟨c, rfl⟩).1
  refine ⟨y * δ, ?_, ?_⟩
  · rw [Units.val_mul, hδ, finM_mul', (hA.h j hj _ ⟨c, rfl⟩).2]
    rfl
  · obtain ⟨p0, hk0, hN0⟩ := hR.k_std (A.chOf j c)
    have hkc := hk0.lat
    rw [hN0] at hkc
    refine GlobalTheory.Mem.Col2.DilPt.isPointOf_last_coordinate_dilation_one_prime_alt _ _ _ _ _ _ _ y δ (A.kb j (A.chOf j c)) (extTo I.SQ ((I.stp u a j).rep c).1.1) _
      ⟨v.1, v.2⟩ ((Units.mapEquiv ρ.toMulEquiv) s) _ (hR.pt c) hk0.uni huni hkc hint hint' htriv
      (fun r r' hr => hR.k_T (A.chOf j c) ⟨v.1, v.2⟩ r r' hr) (fun r r' hr => hrow r r' hr) ?_ ?_
    · rw [extTo_deco, extTo_deco]
      exact GlobalTheory.Mem.Col2.TwAtStd.diaPt_deco B X I u a j ⟨v.1, v.2⟩ _ c
    · funext P'
      rw [extTo_fr, extTo_fr]
      exact decoratedLattice_unitScale_functional_keeps_frames ((I.stp u a j).rep c) ⟨v.1, v.2⟩ _ P'.1

end GlobalTheory.AdForm.DiaChart

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRedIffIsPat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Core.Mi ValuativeRel
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevZero

theorem exists_red_iff_isPat : ∀ {D : D7} {c : Comm D} {v : VCom c} (G : GLoc v) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt G.q.e PP → ∀ g : GL (Fin D.R.r) (Formalism.L2.DIV.kP PP), (∃ x, GlobalTheory.LevZero.Red G PP x g) ↔ GlobalTheory.SymRes.IsPat D.R.rS D.R.k g := by
  intro D c v G PP hidem g
  obtain ⟨π', h1, h2, -⟩ := GlobalTheory.FinPl.SplitPt.exists_lift_isRed D G.k G.q PP hidem
  have hr : D.R.r = D.R.k + (G.s + 1) := by
    have := G.hs
    unfold Ranks.r
    omega
  have hρ : D.R.rS = G.S.ρ := by
    have := G.hs
    have := G.S.odd
    unfold Ranks.rS
    omega
  let π : 𝓞 D.host.E →+* G.k :=
    (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype).comp (oToS D.host.F D.host.E)
  have hπ : ∀ z : 𝓞 D.host.E, π z = (GlobalTheory.LocMod.ofSplit G.q).pr (z : D.host.E) := fun z =>
    h1 (incA D (z : D.host.E))
  have h : GlobalTheory.FunObj.Comparison₂.IsRed (Ideal.Quotient.mk PP.asIdeal) π :=
    ⟨h2.field, fun z => h2.int _, fun z => (iff_of_eq (congrArg (· = 0) (resS_oToS (F := D.host.F) PP z).symm)).trans (h2.ker _)⟩
  have := GlobalTheory.SymRes.exists_red_iff_isPat PP.asIdeal π h hr G.S g
  simp only [hπ] at this
  rw [hρ]
  exact this

end GlobalTheory.LevZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRowFormReadingLevelFormLastSpaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rowForm_reading_levelForm_lastSpace : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {F : FamIn (I.rec7 l Z).what₂.LL G Pl0 T (I.rec7 l Z).R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (I.rec7 l Z).what₂.LL] (R : RealDat (I.rec7 l Z) F Ks) (g : GlobalTheory.Fam.Geo (I.rec7 l Z)) (c₀ : ℕ → ℂ), PinX I l Z R.ψ R.θ g.x g.vac c₀ → ∀ j : SmT R.MX →ₗ[ℂ] (FrP (I.rec7 l Z) → ℂ), GlobalTheory.Core.Rk.Top.IsJ u R.MX j → ∀ (P : LevelP R.Pg (I.rec7 l Z).R.r ℂ) (t : T) (a : I.ι), ∀ (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (K : ClassesAtPrimes (D := (I.rec7 l Z)) (u := u) (I.fm l u a) bad) (eW : (I.per l u a).Wrow ≃ₗ[ℂ] ((I.fm l u a).clsP → FrP (I.rec7 l Z) → ℂ)), I.ReadsP a K.lev.Lb K.lev.U K.lev.chi (fun c => (K.y c).1) K.lat (fun c s => (K.stabI c s).1) → (∀ z c (y : FrP (I.rec7 l Z)) y', y'.1 = y.1 → eW z c y = z c y') → g.bT ∈ GfC _ → LevG K g.bT (levS _ R.βX (datXP R P t)) (levChi _ R.βX (datXP R P t)) → ∀ f : CXP R P t, ∃ G', ReadsG K eW j g.bT G' f.1 := by
  first | exact @GlobalTheory.AdForm.exists_readsG_of_level | exact GlobalTheory.AdForm.exists_readsG_of_level | (intros; apply GlobalTheory.AdForm.exists_readsG_of_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatPeriodEqIntegralEvaluationPeriodsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatPeriod_eq_integral_evaluationPeriods : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ), IsContAut B.A φ → RapidDec J.W G → IsThetaFunO ψ B.V J.W Φ → ∀ h, Integrable (fun u : UX D ρ => J.perAll ψ B s.om₀ φ (rTrans (J.d.levi u.1 * h) G) (evalBF s (s.om (1, (J.d.levi u.1 * h)) Φ))) s.vU.ν ∧ J.perAll ψ B s.om₀ φ (rTrans h G) (flatBF s (s.om (1, h) Φ)) = ∫ u : UX D ρ, J.perAll ψ B s.om₀ φ (rTrans (J.d.levi u.1 * h) G) (evalBF s (s.om (1, (J.d.levi u.1 * h)) Φ)) ∂s.vU.ν := by
  first | exact @GlobalTheory.FlatEval.perAll_flat_eq_integral | exact GlobalTheory.FlatEval.perAll_flat_eq_integral | (intros; apply GlobalTheory.FlatEval.perAll_flat_eq_integral <;> assumption)
end

