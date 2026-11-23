module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationDarbouxCoordinates
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0846
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0856
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0844
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1360
public import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumCompactVacuumReadsDetCharacter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0966
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionFundamentalDomainInnerProductBasic

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationDarbouxCoordinatesStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_darboux_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (ψ : AddChar (AF F) ℂ) (m n : ℕ) (JA : Matrix (Fin m) (Fin m) E) (JB : Matrix (Fin n) (Fin n) E) (ξ : AF F ⊗[F] E) (κ : Type) [Fintype κ]
    (co : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ξ ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) κ)
    (om : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB) →* Module.End ℂ ((κ → AF F) → ℂ)),
    (∀ p w, ∀ φ ∈ schA F κ, om p (co.rho ψ w φ) = co.rho ψ (actAB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p w) (om p φ)) →
    ∃ M : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) × UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB) → ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)),
      (∀ p h, ∀ φ ∈ schA F κ,
        om p (schr ψ (GlobalTheory.WeilL2Words.archPair F (M p h)) φ) = schr ψ (GlobalTheory.WeilL2Words.archPair F h) (om p φ)) ∧
      ∀ h, Continuous fun p => M p h := by
  first | exact @GlobalTheory.ArchTransportDir.archDir_transport | exact GlobalTheory.ArchTransportDir.archDir_transport | (intros; apply GlobalTheory.ArchTransportDir.archDir_transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationL2Isometry
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.WeilL2Isometry

open MeasureTheory GlobalTheory.WeilAdm.HaarSplit
open scoped ENNReal Classical

theorem l2A_eq_of_isUnitaryOn : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] {G : Type} [Group G]
    (om : G →* Module.End ℂ ((κ → AF F) → ℂ)), (∀ p, ∀ φ ∈ schA F κ, om p φ ∈ schA F κ) → IsUnitaryOn (adeleClass F) om →
    ∃ μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 F) F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧
      ∀ p, ∀ Φ ∈ schA F κ, GlobalTheory.WeilL2Words.l2A F μ (om p Φ) = GlobalTheory.WeilL2Words.l2A F μ Φ := by
  intro F _ _ κ _ G _ om hpres hU
  haveI := volume_isAddHaar F κ
  haveI : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  letI mY : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  letI mA : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → AdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI : SigmaCompactSpace (κ → FiniteAdeleRing (𝓞 F) F) := sigmaCompactSpace_of_locallyCompact_secondCountable
  set ν : Measure (κ → FiniteAdeleRing (𝓞 F) F) := Measure.addHaar with hν
  haveI : SFinite ν := inferInstance
  haveI : MeasurableAdd (κ → mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd
  haveI : MeasurableAdd (κ → FiniteAdeleRing (𝓞 F) F) := ContinuousAdd.measurableAdd
  haveI hνH : ν.IsAddHaarMeasure := by rw [hν]; infer_instance
  haveI : ((MeasureTheory.MeasureSpace.volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hμH : Measure.IsAddHaarMeasure (((MeasureTheory.MeasureSpace.volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν).map (splitE F κ)) :=
    (splitE F κ).isAddHaarMeasure_map _ (continuous_splitE F κ) (continuous_splitE_symm F κ)
  let em : ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) ≃ᵐ (κ → AdeleRing (𝓞 F) F) :=
    (Homeomorph.mk (splitE F κ).toEquiv (continuous_splitE F κ) (continuous_splitE_symm F κ)).toMeasurableEquiv
  have hint : ∀ h : (κ → AdeleRing (𝓞 F) F) → ℝ≥0∞,
      ∫⁻ x, h x ∂(((MeasureTheory.MeasureSpace.volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν).map (splitE F κ)) = ∫⁻ p, h (splitE F κ p) ∂((MeasureTheory.MeasureSpace.volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν) :=
    fun h => lintegral_map_equiv h em
  have key : ∀ Ψ ∈ GlobalTheory.WeilM.schA F κ,
      GlobalTheory.WeilL2Words.l2A F ν Ψ = ∫⁻ x, ‖Ψ x‖ₑ ^ 2 ∂(((MeasureTheory.MeasureSpace.volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν).map (splitE F κ)) := by
    intro Ψ hΨ
    rw [hint]
    have hHm : Measurable fun p => ‖Ψ (splitE F κ p)‖ₑ ^ 2 :=
      (continuous_comp_splitE F κ Ψ hΨ).measurable.enorm.pow_const 2
    rw [lintegral_prod_symm _ hHm.aemeasurable]
    rfl
  refine ⟨ν, hνH, fun p Φ hΦ => ?_⟩
  rw [key _ (hpres p Φ hΦ), key _ hΦ]
  exact hU _ hμH p Φ hΦ

end GlobalTheory.WeilL2Isometry
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationRealMovesFrameDetChar
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealMove

theorem muVal_mul {D : D7} {V : HSp D} {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ} (h : Formalism.L2.Pj.MuVal V χ mu)
    (g g' : GA D V) : mu (g * g') = mu g * mu g' := by
  obtain ⟨x, hx⟩ := h.1 g
  obtain ⟨x', hx'⟩ := h.1 g'
  have hxx : IsDetRoot V (g * g') (x * x') := by
    unfold IsDetRoot at *
    rw [map_mul, Units.val_mul, Units.val_mul, Matrix.det_mul, map_mul]
    rw [mul_mul_mul_comm, ← hx, ← hx']
  rw [h.2 _ _ hxx, h.2 _ _ hx, h.2 _ _ hx', map_mul, Circle.coe_mul]

theorem frMove_mul {D : D7} (θ : InfFam D) (W : HSp D) (X : Data D.host.E W.rank) (hX : IsMod W rfl X)
    (u v : GA D W) (x : Frame X.Ψ W.rank) :
    frMove θ W rfl X (u * v) x = frMove θ W rfl X u (frMove θ W rfl X v x) := by
  funext τ
  have hτ : ∃ ρ, τ.1 = tauE D ρ := (hX.psi τ.1).1 τ.2
  have e : realM θ (Formalism.L2.Theta.mt W (u * v)) τ.1 =
      realM θ (Formalism.L2.Theta.mt W u) τ.1 * realM θ (Formalism.L2.Theta.mt W v) τ.1 := by
    unfold realM
    rw [dite_eq_left hτ, dite_eq_left hτ, dite_eq_left hτ, GlobalTheory.UnitaryChar.compAt_mt_mul]
  show (Matrix.reindex (finCongr rfl) (finCongr rfl) (realM θ (Formalism.L2.Theta.mt W (u * v)) τ.1) * mat x τ :
      Matrix (Fin W.rank) (Fin W.rank) ℂ) =
    Matrix.reindex (finCongr rfl) (finCongr rfl) (realM θ (Formalism.L2.Theta.mt W u) τ.1) *
      (Matrix.reindex (finCongr rfl) (finCongr rfl) (realM θ (Formalism.L2.Theta.mt W v) τ.1) * mat x τ)
  rw [e, ← Matrix.mul_assoc]
  simp

theorem om_real_reads : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsPair ψ θ V W χV χW om → ∀ mu : GA D W → ℂ, Formalism.L2.Pj.MuVal W χV mu → ∀ (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsMod W hr X → IsSympl X bas → ∀ (x : Frame X.Ψ r), IsONFr X x → ∀ (f : WO V W → ℂ) (φ : TF V.rank g), IsThetaFunO ψ V W f → Reads θ V W hr X bas idx f φ x → ∀ u ∈ GinfC W, Reads θ V W hr X bas idx (om (1, u) f) (mu u • φ) (frMove θ W hr X u x) := by
  intro D ψ θ V W χV χW om hP mu hmu r g hr X bas idx hX hS x hx f φ hf hR
  subst hr
  have hstd := hP.weil.std
  obtain ⟨X', m, hq', hq, bas', idx', hs, -, -, -, -, -, -, hfr⟩ :=
    GlobalTheory.T.orthonormal_frame_reading_eq_conjugate_datum_theta D ψ θ V W g X bas idx hstd hP.inf hP.even hP.std hX hS
  set C : GlobalTheory.Ker.Ctx V W := ⟨ψ, hstd, θ, hP.inf, X', m, g, X.p0, hq', bas', idx', hs, hP.even⟩ with hC
  obtain ⟨⟨B, hB⟩, hBx⟩ := hfr x hx
  obtain ⟨hIsB, hinv, -, -, -, -, -, hmv, hTh⟩ := hBx B hB
  have hfe : f = C.Th (C.xB B) φ := (hTh f φ hR.1).1 ⟨hf, hR⟩
  have hON : ∀ u, IsONFr X (frMove θ W rfl X u x) := fun u => (hmv u).1
  have hpres : ∀ u : GA D W, IsThetaFunO ψ V W (om (1, u) f) := fun u => hP.weil.om_pres _ _ hf
  have hc : ∀ u : GA D W, ∃ c : ℂ, u ∈ GinfC W → ‖c‖ = 1 ∧
      Reads θ V W rfl X bas idx (om (1, u) f) (c • φ) (frMove θ W rfl X u x) := by
    intro u
    by_cases hu : u ∈ GinfC W
    swap
    · exact ⟨1, fun h => absurd h hu⟩
    obtain ⟨c, hc1, hc⟩ := GlobalTheory.Ker.RealScalar.om_real_Th D V W C om (GlobalTheory.Ker.isWeak_of_datum hP.weil) 1 (one_mem _)
      u hu B hIsB
    refine ⟨c, fun _ => ⟨hc1, ?_⟩⟩
    have h1 := hc φ hR.1
    rw [← hfe] at h1
    obtain ⟨-, -, -, -, -, -, -, -, hTh'⟩ := (hfr _ (hON u)).2 _ (hmv u).2
    have h2 := ((hTh' (C.Th (C.xB (C.mvB u B)) φ) φ hR.1).2 rfl).2
    have h3 := (_root_.GlobalTheory.AdTh.reads_linear_injective D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS _ (hON u)
      _ _ _ _ h2 h2).1 c 0
    rw [zero_smul, zero_smul, add_zero, add_zero] at h3
    rw [h1]
    exact h3
  choose c hc using hc
  by_cases hφ : φ = 0
  · intro u hu
    have := (hc u hu).2
    rw [hφ, smul_zero] at this ⊢
    exact this
  obtain ⟨G, hG⟩ := _root_.GlobalTheory.AdTh.inner_of_reads D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS
  obtain ⟨K, hK0, hK⟩ := (hG x x hx hx).2.2 φ hR.1 hφ
  obtain ⟨μ, 𝓕, hμ⟩ := (GlobalTheory.Ker.ScalarProduct.ip_basic D V W C).1
  have hmul : ∀ u ∈ GinfC W, ∀ v ∈ GinfC W, c (u * v) = c u * c v := by
    intro u hu v hv
    have h1 := hK _ _ (hON (u * v)) (hON u) _ _ _ _ (hpres _) (hpres _) (hc _ (mul_mem hu hv)).2 (hc u hu).2 μ 𝓕 hμ
    have hR1 : Reads θ V W rfl X bas idx f ((1 : ℂ) • φ) x := by rwa [one_smul]
    have h2 := hK _ _ (hON v) hx _ _ _ _ (hpres _) hf (hc v hv).2 hR1 μ 𝓕 hμ
    have h3 := GlobalTheory.WeilInner.om_inner D ψ V W χV χW om hP.weil μ 𝓕 hμ (1, u) _ _ (hpres v) hf
    have h4 : om (1, u * v) f = om (1, u) (om (1, v) f) := by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    rw [h4, h3, h2, frMove_mul θ W X hX, (hG _ _ (hON v) hx).2.1 u, map_one, mul_one] at h1
    have h5 : c v = c (u * v) * conj (c u) :=
      mul_right_cancel₀ (mul_ne_zero hK0 (hG _ _ (hON v) hx).1) h1
    have h6 : c u * conj (c u) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, (hc u hu).1]; simp
    rw [h5]
    linear_combination (-c (u * v)) * h6
  have hmu0 : ∀ u, mu u ≠ 0 := fun u h => by
    have := hmu.norm u
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hcart := (GlobalTheory.FrameCplx.cplx_of_frame D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS x _
    hx hinv).1
  have hone := GlobalTheory.UnitaryChar.char_eq_one D θ W hP.inf _ hcart (fun u => c u / mu u)
    (fun u hu v hv => by
      show c (u * v) / mu (u * v) = c u / mu u * (c v / mu v)
      rw [hmul u hu v hv, muVal_mul hmu, mul_div_mul_comm])
    (fun k hk hks => by
      have h1 := _root_.GlobalTheory.AdTh.RealCompact.om_compact_reads D ψ θ V W χV χW om hP mu hmu W.rank g rfl X bas idx hX hS x _ hx hinv f φ hf hR k hk hks
      have h2 := (_root_.GlobalTheory.AdTh.reads_linear_injective D ψ θ V W W.rank g rfl X bas idx hstd hP.inf hP.std hP.even hX hS _ (hON k)
        _ _ _ _ (hc k hk).2 h1).2.1 rfl
      have h3 : c k = mu k := smul_left_injective ℂ hφ h2
      show c k / mu k = 1
      rw [h3, div_self (hmu0 k)])
  intro u hu
  have h : c u = mu u := (div_eq_one_iff_eq (hmu0 u)).1 (hone u hu)
  rw [← h]
  exact (hc u hu).2

end GlobalTheory.RealMove
end

