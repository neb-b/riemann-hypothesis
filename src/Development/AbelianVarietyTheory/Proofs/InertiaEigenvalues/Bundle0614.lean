module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0609
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0583
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0600
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0462
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0611
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0505
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoAnnihilatorOfIntegralLocalDuality
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0525
public import Formalism.LocalToGlobal.IndefiniteReal.LinksW
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealSideCharacterMatch
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0610

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BasisDvdTauPowLPowAinfStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.basis_dvd_tauPow_lPow_ainf : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ) (Y : Matrix (Fin d) (Fin d) (Ainf l)), IsUnit (Y.map (inclW l)) → (∀ y, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) y ↔ ∃ c : Fin d → bk.S, y = Y *ᵥ fun a => bk.ev (c a)) → ∃ (k : ℕ) (S' : Matrix (Fin d) (Fin d) (Ainf l)), Y * S' = ((l : Ainf l) ^ k * τ ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) := by
  first | exact @GlobalTheory.BSP.HeightSprime.main | exact GlobalTheory.BSP.HeightSprime.main | (intros; apply GlobalTheory.BSP.HeightSprime.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimAtAuxiliaryPrimePlaces
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.InertiaEigenvalues.DimAtQD

theorem main : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (i : D.nd.Loc),
    EmbeddingTypeJumps.AtQD i → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw), Formalism.WeaklyAdmissibleFiltrations.BlochKatoDim (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 :=
  fun _ _ D i _ w hw C =>
    by
      classical
      haveI := (D.nbr i w hw).Kw.2
      haveI := C.LL.2
      exact @GlobalTheory.BlochKatoTied.blochKatoDim_of_tied (D.nd.l i) _ (D.loc (D.nd.l i)) (D.locA (D.nd.l i)) (D.locT (D.nd.l i)) (D.nbr i w hw).Kw C.LL _

end GlobalTheory.InertiaEigenvalues.DimAtQD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimFormulaAllLocalSituations
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem blochKatoDim_at_every_local_situation : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.adm12 D := by
  intro D l _ K LL _
  exact _root_.GlobalTheory.BlochKatoTied.blochKatoDim_of_tied l (D.loc l) (D.locA l) (D.locT l) K LL

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoExactAnnihilatorsPeriodDatum
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BlochKatoAnn

section Abstract

variable {k Z Z' : Type} [Field k] [AddCommGroup Z] [Module k Z] [AddCommGroup Z'] [Module k Z']
  [FiniteDimensional k Z] [FiniteDimensional k Z']

def rorth (β : Z →ₗ[k] Z' →ₗ[k] k) (W : Submodule k Z) : Submodule k Z' :=
  (W.map β).dualCoannihilator

theorem mem_rorth (β : Z →ₗ[k] Z' →ₗ[k] k) (W : Submodule k Z) (b : Z') :
    b ∈ rorth β W ↔ ∀ a ∈ W, β a b = 0 := by
  unfold rorth
  rw [Submodule.mem_dualCoannihilator]
  constructor
  · intro h a ha
    exact h _ ⟨a, ha, rfl⟩
  · rintro h _ ⟨a, ha, rfl⟩
    exact h a ha

theorem finrank_rorth (β : Z →ₗ[k] Z' →ₗ[k] k) (W : Submodule k Z) (hW : LinearMap.ker β ≤ W) :
    finrank k (rorth β W) + finrank k W = finrank k Z' + finrank k (LinearMap.ker β) := by
  have h1 := Subspace.finrank_add_finrank_dualCoannihilator_eq (W.map β)
  have h2 := LinearMap.finrank_range_add_finrank_ker (β.domRestrict W)
  have h3 : LinearMap.range (β.domRestrict W) = W.map β := by
    rw [LinearMap.range_domRestrict]
  have h4 : LinearMap.ker (β.domRestrict W) = (LinearMap.ker β).comap W.subtype := by
    rw [LinearMap.ker_domRestrict]
  have h5 : finrank k ((LinearMap.ker β).comap W.subtype) = finrank k (LinearMap.ker β) :=
    (Submodule.comapSubtypeEquivOfLe hW).finrank_eq
  rw [h3, h4, h5] at h2
  unfold rorth
  linarith

theorem rorth_top (β : Z →ₗ[k] Z' →ₗ[k] k) : rorth β ⊤ = LinearMap.ker β.flip := by
  ext b
  rw [mem_rorth, LinearMap.mem_ker]
  constructor
  · intro h
    ext a
    exact h a trivial
  · intro h a _
    have := LinearMap.congr_fun h a
    simpa using this

theorem exact_ann (β : Z →ₗ[k] Z' →ₗ[k] k) (W : Submodule k Z) (W' : Submodule k Z')
    (hW : LinearMap.ker β ≤ W) (hW' : LinearMap.ker β.flip ≤ W')
    (hort : ∀ a ∈ W, ∀ b ∈ W', β a b = 0)
    (hdim : finrank k W + finrank k W' = finrank k Z + finrank k (LinearMap.ker β.flip)) :
    rorth β W = W' ∧ rorth β.flip W' = W := by
  have hT := finrank_rorth β ⊤ (le_top)
  rw [rorth_top, finrank_top] at hT
  have hA := finrank_rorth β W hW
  have hB := finrank_rorth β.flip W' hW'
  have l1 : W' ≤ rorth β W := fun b hb => (mem_rorth β W b).2 fun a ha => hort a ha b hb
  have l2 : W ≤ rorth β.flip W' := fun a ha => (mem_rorth β.flip W' a).2 fun b hb => by
    rw [LinearMap.flip_apply]; exact hort a ha b hb
  constructor
  · exact (Submodule.eq_of_le_of_finrank_eq l1 (by omega)).symm
  · exact (Submodule.eq_of_le_of_finrank_eq l2 (by omega)).symm

end Abstract

end GlobalTheory.BlochKatoAnn

namespace GlobalTheory.BlochKatoAnn

section Concrete

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O]
    [Algebra O LL]

theorem galoisCoboundaries_le_continuousCocycles (A : GRep G Qp LL O) : B1 A.ρ ≤ continuousCocycles A.ρ := by
  rintro _ ⟨x, rfl⟩
  refine ⟨?_, fun g h => ?_⟩
  · have : (cob A.ρ x : G → A.V) = fun g => A.ρ g x + (-x) := by
      funext g
      simp [cob, sub_eq_add_neg]
    rw [this]
    exact (A.cont x).add continuous_const
  · simp only [cob, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, map_mul,
      Module.End.mul_apply, map_sub]
    abel

theorem B1_le_Z1f (A : GRep G Qp LL O) : B1 A.ρ ≤ finiteCocycles PD A.ρ := by
  intro c hc
  refine ⟨galoisCoboundaries_le_continuousCocycles A hc, ?_⟩
  obtain ⟨x, rfl⟩ := hc
  refine ⟨x ⊗ₜ[Qp] (1 : B), fun g => ?_⟩
  simp [cob, actVB, sub_tmul]

theorem blochKatoFiniteCocycles_le_continuousCocycles (A : GRep G Qp LL O) : finiteCocycles PD A.ρ ≤ continuousCocycles A.ρ := fun _ h => h.1

theorem finite_continuous_cocycles_localGaloisRep (A : GRep G Qp LL O) (h : Module.Finite LL (H1V A.ρ)) :
    FiniteDimensional LL (continuousCocycles A.ρ) := by
  haveI : FiniteDimensional LL (B1 A.ρ) := LinearMap.finiteDimensional_range (cob A.ρ)
  have hK : FiniteDimensional LL ((B1 A.ρ).comap (continuousCocycles A.ρ).subtype) :=
    Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe (galoisCoboundaries_le_continuousCocycles A)).symm
  show Module.Finite LL (continuousCocycles A.ρ)
  rw [Module.finite_def]
  apply Submodule.fg_of_fg_map_of_fg_inf_ker ((B1 A.ρ).comap (continuousCocycles A.ρ).subtype).mkQ
  · rw [Submodule.map_top, Submodule.range_mkQ]
    exact Module.finite_def.1 h
  · rw [top_inf_eq, Submodule.ker_mkQ]
    exact Module.Finite.iff_fg.1 hK

theorem finrank_H1V (A : GRep G Qp LL O) [FiniteDimensional LL (continuousCocycles A.ρ)] :
    finrank LL (H1V A.ρ) + finrank LL (B1 A.ρ) = finrank LL (continuousCocycles A.ρ) := by
  have e := Submodule.finrank_quotient_add_finrank ((B1 A.ρ).comap (continuousCocycles A.ρ).subtype)
  rw [(Submodule.comapSubtypeEquivOfLe (galoisCoboundaries_le_continuousCocycles A)).finrank_eq] at e
  exact e

theorem finrank_H1fV (A : GRep G Qp LL O) [FiniteDimensional LL (continuousCocycles A.ρ)] :
    finrank LL (FiniteCohomology PD A.ρ) + finrank LL (B1 A.ρ) =
      finrank LL ((finiteCocycles PD A.ρ).comap (continuousCocycles A.ρ).subtype) := by
  have eW := (Submodule.comapSubtypeEquivOfLe (blochKatoFiniteCocycles_le_continuousCocycles PD A))
  haveI : FiniteDimensional LL (finiteCocycles PD A.ρ) := Module.Finite.equiv eW
  have e := Submodule.finrank_quotient_add_finrank ((B1 A.ρ).comap (finiteCocycles PD A.ρ).subtype)
  rw [(Submodule.comapSubtypeEquivOfLe (B1_le_Z1f PD A)).finrank_eq] at e
  rw [eW.finrank_eq]
  exact e

end Concrete

end GlobalTheory.BlochKatoAnn

namespace GlobalTheory.BlochKatoAnn

theorem bkA_exact_annihilators : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
      ∀ K : FinExt l, bkACore (P.PD K) := by
  intro hTD hEC l _ P AI hT K
  intro LL _ _ _ O _ _ hO A A' m hdr hdual
  have hdual' : IsDual1 (P.PD K) A'.ρ A.ρ m.flip := by
    obtain ⟨h1, h2, h3, h4⟩ := hdual
    refine ⟨fun g y x => ?_, fun y hy => h3 y hy, fun x hx => h2 x hx, h4.symm⟩
    simp only [LinearMap.flip_apply]
    exact h1 g x y
  obtain ⟨hdrd, hfd⟩ := _root_.GlobalTheory.TateDualTied.main l P AI hT K
  have hdr' : IsDR (P.PD K) A'.ρ := hdrd LL O hO A A' m hdr hdual
  have hfil := hfd LL O hO A A' m hdr hdual
  obtain ⟨hH1fin, hH1⟩ := GlobalTheory.T.finrank_H1_dual_pair hTD hEC l P K LL O hO A A' m hdual
  obtain ⟨hH1fin', -⟩ := GlobalTheory.T.finrank_H1_dual_pair hTD hEC l P K LL O hO A' A m.flip hdual'
  obtain ⟨-, hf⟩ := GlobalTheory.T.finrank_H1f_de_rham l P AI hT K LL O hO A hdr
  obtain ⟨-, hf'⟩ := GlobalTheory.T.finrank_H1f_de_rham l P AI hT K LL O hO A' hdr'
  have hort := GlobalTheory.T.cup_product_finite_classes_coboundary l P AI hT K LL O hO A A' m hdr hdual
  obtain ⟨β, hβ, hl, hr⟩ := GlobalTheory.T.tateDuality_degreeOne_continuous_cocycles hTD l P K LL O hO A A' m hdual
  haveI := finite_continuous_cocycles_localGaloisRep A hH1fin
  haveI := finite_continuous_cocycles_localGaloisRep A' hH1fin'
  have hkl : LinearMap.ker β = (B1 A.ρ).comap (continuousCocycles A.ρ).subtype := by
    ext a
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, ← hl a]
    constructor
    · intro h b
      rw [h]
      rfl
    · intro h
      ext b
      exact h b
  have hkr : LinearMap.ker β.flip = (B1 A'.ρ).comap (continuousCocycles A'.ρ).subtype := by
    ext b
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, ← hr b]
    constructor
    · intro h a
      have := LinearMap.congr_fun h a
      simpa using this
    · intro h
      ext a
      simpa using h a
  have hW : LinearMap.ker β ≤ (finiteCocycles (P.PD K) A.ρ).comap (continuousCocycles A.ρ).subtype := by
    rw [hkl]
    exact Submodule.comap_mono (B1_le_Z1f (P.PD K) A)
  have hW' : LinearMap.ker β.flip ≤ (finiteCocycles (P.PD K) A'.ρ).comap (continuousCocycles A'.ρ).subtype := by
    rw [hkr]
    exact Submodule.comap_mono (B1_le_Z1f (P.PD K) A')
  have horth : ∀ a ∈ (finiteCocycles (P.PD K) A.ρ).comap (continuousCocycles A.ρ).subtype,
      ∀ b ∈ (finiteCocycles (P.PD K) A'.ρ).comap (continuousCocycles A'.ρ).subtype, β a b = 0 := by
    intro a ha b hb
    rw [hβ]
    exact hort a.1 ha b.1 hb
  have eZ := finrank_H1V A
  have eW := finrank_H1fV (P.PD K) A
  have eW' := finrank_H1fV (P.PD K) A'
  have eKl : finrank LL (LinearMap.ker β) = finrank LL (B1 A.ρ) := by
    rw [hkl]
    exact (Submodule.comapSubtypeEquivOfLe (galoisCoboundaries_le_continuousCocycles A)).finrank_eq
  have eKr : finrank LL (LinearMap.ker β.flip) = finrank LL (B1 A'.ρ) := by
    rw [hkr]
    exact (Submodule.comapSubtypeEquivOfLe (galoisCoboundaries_le_continuousCocycles A')).finrank_eq
  have hdV := hdual.2.2.2
  unfold IsDR at hdr hdr'
  rw [← hdV] at hdr'
  have hdim : finrank LL ((finiteCocycles (P.PD K) A.ρ).comap (continuousCocycles A.ρ).subtype) +
      finrank LL ((finiteCocycles (P.PD K) A'.ρ).comap (continuousCocycles A'.ρ).subtype) =
      finrank LL (continuousCocycles A.ρ) + finrank LL (LinearMap.ker β.flip) := by
    rw [eKr]
    zify at eZ eW eW' hH1 hfil hdr hdr' ⊢
    linarith
  obtain ⟨h1, h2⟩ := exact_ann β _ _ hW hW' horth hdim
  constructor
  · intro a ha
    change (⟨a, ha⟩ : continuousCocycles A.ρ) ∈ (finiteCocycles (P.PD K) A.ρ).comap (continuousCocycles A.ρ).subtype ↔ _
    rw [← h2, mem_rorth]
    constructor
    · intro h b hb
      have := h ⟨b, hb.1⟩ hb
      rw [LinearMap.flip_apply, hβ] at this
      exact this
    · intro h b hb
      rw [LinearMap.flip_apply, hβ]
      exact h b.1 hb
  · intro b hb
    change (⟨b, hb⟩ : continuousCocycles A'.ρ) ∈ (finiteCocycles (P.PD K) A'.ρ).comap (continuousCocycles A'.ρ).subtype ↔ _
    rw [← h1, mem_rorth]
    constructor
    · intro h a ha
      have := h ⟨a, ha.1⟩ ha
      rw [hβ] at this
      exact this
    · intro h a ha
      rw [hβ]
      exact h a.1 ha

end GlobalTheory.BlochKatoAnn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalAllPrimesOfBlochKato
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BlochKatoLocalOfHyp

theorem bkAll_of_blochKatoLocal (hBK : GlobalTheory.Published.BlochKatoLocal) (hTD : Formalism.GaloisCohomology.LocalTateDualityK)
    (hEC : Formalism.GaloisCohomology.LocalEulerCharK) (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (hT : LocTied l P AI) (K : FinExt l) : Formalism.MainNotions.LocalSituation.bkAll (P.PD K) := by
  obtain ⟨hDim, hRat, hInt⟩ := hBK l P AI hT K
  have hA : bkACore (P.PD K) := GlobalTheory.T.blochKatoAnnihilator_of_rationalLocalDuality l P K hRat
  have hB : bkBCore (P.PD K) := _root_.GlobalTheory.BKIntDescent.bkBCore_of_integralDuality l P K hInt
  exact ⟨hA, _root_.GlobalTheory.bkADim_of_dimFormula l P K hDim, GlobalTheory.BKRightExact.bkARightExact_of_tied l P AI hT K, hB,
    _root_.GlobalTheory.BKFinLevel.bkC_of_bkA_bkB hTD hEC l P AI hT K hA hB⟩

theorem blochKatoLocal_allPrimes_of_blochKato : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : Formalism.BasicNotions.D7, Formalism.MainNotions.LocalSituation.Conclusion5 D := by
  intro hBK hTD hEC D l _ K
  exact bkAll_of_blochKatoLocal hBK hTD hEC l (D.loc l) (D.locA l) (D.locT l) K

end GlobalTheory.BlochKatoLocalOfHyp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassPresFormsFiniteGroupHeckeOperators
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PresHecke

open Formalism.IndefR.Bridge GlobalTheory.CharChange

section Raw

variable {G Γ : Type} [Group G] [Group Γ] {ι : Γ →* G}
variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ}
variable {I : Type} {inR : I → Prop} {isT isLoc : I → G → Prop}

theorem keepsDcRaw (P : ClassPres ι S σ ρ J χ) (hx : I → G) (hA : I → Finset G)
    (hok : ∀ i, inR i → isT i (hx i) ∧ (∀ a ∈ hA i, isLoc i a) ∧ IsDC J (hx i) (hA i))
    (hloc : ∀ i, inR i → ∃ Lc : Subgroup G, (∀ x, isLoc i x → x ∈ Lc) ∧
      (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ x ∈ Lc, Commute k₂ x) ∧
      ∀ k : J, (k : G) ∈ Lc → χ k = 1)
    (i : I) (hi : inR i) : Keeps P (dcL (W := W) (hA i)) := by
  obtain ⟨Lc, hL1, hL2, hL3⟩ := hloc i hi
  intro F hF hv
  refine ⟨dcOp_mem (hok i hi).2.2 Lc (fun a ha => hL1 _ ((hok i hi).2.1 a ha)) hL2 hL3 hF, fun h => ?_⟩
  exact InRg.sum _ _ fun a _ => hv _


open Classical in
def opRaw (P : ClassPres ι S σ ρ J χ) (hχ : ∀ k, ∃ b : K, σ b = (χ k : ℂ))
    (hρ : ∀ γ x, ∃ x', P.coef x' = ρ γ (P.coef x)) (hx : I → G) (hA : I → Finset G)
    (hok : ∀ i, inR i → isT i (hx i) ∧ (∀ a ∈ hA i, isLoc i a) ∧ IsDC J (hx i) (hA i))
    (hloc : ∀ i, inR i → ∃ Lc : Subgroup G, (∀ x, isLoc i x → x ∈ Lc) ∧
      (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ x ∈ Lc, Commute k₂ x) ∧
      ∀ k : J, (k : G) ∈ Lc → χ k = 1)
    (one : I → Prop) (i : I) : Module.End K S.Forms :=
  if hi : inR i then trE P hχ hρ (keepsDcRaw P hx hA hok hloc i hi) else if one i then 1 else 0

def heckeRaw (P : ClassPres ι S σ ρ J χ) (hχ : ∀ k, ∃ b : K, σ b = (χ k : ℂ))
    (hρ : ∀ γ x, ∃ x', P.coef x' = ρ γ (P.coef x)) (hx : I → G) (hA : I → Finset G)
    (hok : ∀ i, inR i → isT i (hx i) ∧ (∀ a ∈ hA i, isLoc i a) ∧ IsDC J (hx i) (hA i))
    (hloc : ∀ i, inR i → ∃ Lc : Subgroup G, (∀ x, isLoc i x → x ∈ Lc) ∧
      (∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ x ∈ Lc, Commute k₂ x) ∧
      ∀ k : J, (k : G) ∈ Lc → χ k = 1)
    (one : I → Prop) : HeckeTie ι P (opRaw P hχ hρ hx hA hok hloc one) inR isT isLoc where
  hx := hx
  hA := hA
  hx_ok i hi := (hok i hi).1
  hA_loc i hi := (hok i hi).2.1
  chi_loc i hi k hk := by
    obtain ⟨Lc, hL1, _, hL3⟩ := hloc i hi
    exact hL3 k (hL1 _ hk)
  hDC i hi := (hok i hi).2.2
  op_eq i hi f := by
    unfold opRaw
    rw [dite_eq_left hi, ext_trE]
    rfl

end Raw

end GlobalTheory.PresHecke

namespace GlobalTheory

open Formalism.IndefR.Bridge GlobalTheory.CharChange GlobalTheory.PresHecke

theorem sideReal_ofPres : ∀ {G Γ : Type} [Group G] [Group Γ] (ι : Γ →* G) {I : Type} (c : Bridge.CoefDatG Γ) (l : Bridge.LevDatG G) (isT isLoc : I → G → Prop) {K : Type} [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (S : CSD K) {G0 : Type} [Group G0] (inR : I → Prop) (P : Bridge.ClassPres ι S σ c.ρ l.J l.χ), (∀ q, ∃ a : K, σ a = ((l.ch q : ℂˣ) : ℂ)) → (∀ γ x, ∃ x', P.coef x' = c.ρ γ (P.coef x)) → ∀ (red : l.Q →* G0), Function.Surjective red → (∀ q : l.Q, red q = 1 ↔ (q : G) ∈ l.J) → ∀ (hx : I → G) (hA : I → Finset G), (∀ i, inR i → isT i (hx i) ∧ (∀ a ∈ hA i, isLoc i a) ∧ Bridge.IsDC l.J (hx i) (hA i)) → (∀ i, inR i → ∃ Lc : Subgroup G, (∀ x, isLoc i x → x ∈ Lc) ∧ (∀ k ∈ l.J, ∃ k₁ ∈ l.J, ∃ k₂ ∈ l.J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ x ∈ Lc, Commute k₂ x) ∧ ∀ k : l.J, (k : G) ∈ Lc → l.χ k = 1) → ∀ one : I → Prop, ∃ (act : Representation K G0 S.Forms) (op : I → Module.End K S.Forms) (B : Bridge.SideRealG ι ⟨c, l, isT, isLoc⟩ σ S act op inR), B.pres = P ∧ B.act_tie.red = red ∧ ∀ i, ¬ inR i → (one i → op i = 1) ∧ (¬ one i → op i = 0) := by
  intro G Γ _ _ ι I c l isT isLoc K _ _ _ σ S G0 _ inR P hσ hρ red hsurj hker hx hA hok hloc one
  have hχ : ∀ k : l.J, ∃ b : K, σ b = (l.χ k : ℂ) := fun k => by rw [← l.ch_J]; exact hσ _
  exact ⟨actNew P hχ hρ red hsurj l.J_le hker l.ch l.ch_J hσ,
    opRaw P hχ hρ hx hA hok hloc one,
    ⟨P, actTieNew P hχ hρ red hsurj l.J_le hker l.ch l.ch_J hσ, heckeRaw P hχ hρ hx hA hok hloc one⟩,
    rfl, rfl, fun i hi => ⟨fun ho => by simp [opRaw, hi, ho], fun ho => by simp [opRaw, hi, ho]⟩⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCocycleOfSemistableCoboundary
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.CocycStLemma

theorem tmul_one_injective {F V B : Type} [Field F] [AddCommGroup V] [Module F V] [Ring B] [Algebra F B]
    [Nontrivial B] : Function.Injective (fun v : V => v ⊗ₜ[F] (1 : B)) := by
  have hinj : Function.Injective (Algebra.linearMap F B) := (algebraMap F B).injective
  obtain ⟨f, hf⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F B)
    (LinearMap.ker_eq_bot.mpr hinj)
  intro v w h
  have h2 := congrArg (fun x => TensorProduct.rid F V (LinearMap.lTensor V f x)) h
  have h1 : f 1 = 1 := by
    have := LinearMap.congr_fun hf 1
    simpa using this
  simpa [h1] using h2

end GlobalTheory.CocycStLemma

theorem GlobalTheory.cocycle_of_st_coboundary : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [ContinuousAdd V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), (∀ v : V, Continuous fun g => ρ g v) → ∀ (z : V ⊗[ℚ_[l]] Bst P) (c : ↥(GK K) → V), (∀ g, c g ⊗ₜ[ℚ_[l]] (1 : Bst P) = stRep P ρ g z - z) → c ∈ continuousCocycles ρ := by
  intro l _ P AI T K V _ _ _ _ _ _ _ ρ hρ z c hc
  refine ⟨?_, ?_⟩
  · obtain ⟨b, hb⟩ := _root_.GlobalTheory.cocycle_dies_dR_of_dies_st l P AI T K V ρ c z hc
    refine _root_.GlobalTheory.ContDR.cont_dR l P AI T K V ρ hρ 0 Fin.elim0 Fin.elim0 (fun i => Fin.elim0 i) b c ?_
    intro g
    simp [hb g]
  · intro g h
    haveI : Nontrivial P.R.B := nontrivial_B P
    haveI : Nontrivial (Bst P) := inferInstance
    apply GlobalTheory.CocycStLemma.tmul_one_injective (F := ℚ_[l]) (B := Bst P)
    simp only [add_tmul]
    rw [hc, hc g, map_mul, Module.End.mul_apply]
    have e : stRep P ρ g (c h ⊗ₜ[ℚ_[l]] (1 : Bst P)) = ρ g (c h) ⊗ₜ[ℚ_[l]] (1 : Bst P) := by
      rw [stRep_tmul, map_one]
    rw [← e, hc h, map_sub]
    abel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallineLatticePeriodsOnDiscStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_crystalline_lattice_periods_on_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (P : LocPrime l) (AI : LocAinf l P), IsStd P AI → ∀ (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (L : Lattice (O := ℤ_[l]) ρ), (∀ x, Continuous fun g => ρ g x) → IsCrys (P.PD K) ρ → ∀ (d : ℕ) (b : Module.Basis (Fin d) ℤ_[l] ↥L.T), Nonempty (Seed bk d (fun g => LinearMap.toMatrix b b (actT L g)) τ) := by
  first | exact @GlobalTheory.SeedExists.exists_seed | exact GlobalTheory.SeedExists.exists_seed | (intros; apply GlobalTheory.SeedExists.exists_seed <;> assumption)
end

