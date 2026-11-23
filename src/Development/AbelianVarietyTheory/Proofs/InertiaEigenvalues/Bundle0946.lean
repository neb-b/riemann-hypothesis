module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0798
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0902
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0944
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0908
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0911
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0942
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0014
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneCuspidalUnitaryCharEquivApplySymm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0376
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0650
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatVectorEqGaussSumSmulCentralTranslate
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0940
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftEigenformIsEigenform
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0945
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0918
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0796
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0695
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0645
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0713
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdjointComp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegrableContAut
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeOfMemPartW
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralFlipVacuumEqMultipleOfTranslateMean
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries


set_option maxHeartbeats 1600000 in
open MeasureTheory GlobalTheory.VacUnique GlobalTheory.FockCompare in
theorem eq_smul_vacuum {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {S T : HSp D} {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hΛS : IsSelfDualC S ΛS) (hΛT : IsSelfDualC T ΛT) {f f' : WO S T → ℂ}
    (hf : IsVacO ψ θ S T sS sT ΛS ΛT f) (hth : IsThetaFunO ψ S T f')
    (hlat' : IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True) f')
    (hfock : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f') : ∃ a : ℂ, f' = a • f := by
  classical
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hΛS hΛT
  have hden := GlobalTheory.T.scaled_finite_matrix_mem_lattice D S T ΛS ΛT
    (GlobalTheory.ProjXCols.selfDual_isFullLattice S ΛS hΛS)
    (GlobalTheory.ProjXCols.selfDual_isFullLattice T ΛT hΛT)
  have hlat := hf.2.lat
  have hinf := fun u => latO_inf (u := u) S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
    fun _ => True
  generalize latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) = Λ
    at h1 h2 h3 hden hlat hlat' hinf
  choose ε hε1 hε2 using h3 f hlat
  have det : ∀ (g g' : WO S T → ℂ) (c : ℂ), IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' →
      IsLatVac (heisO ψ S T) Λ g → IsLatVac (heisO ψ S T) Λ g' →
      (∀ z, g' (iotaW σ T S z) = c * g (iotaW σ T S z)) → g' = c • g := by
    intro g g' c hg hg' hl hl' hz
    funext w
    obtain ⟨γ, z, u, hu, rfl⟩ := exists_decomp h h2 w
    rw [Pi.smul_apply, smul_eq_mul, hg.quasi, hg'.quasi, apply_real_add h hψ (hinf u hu) (hε2 u hu g hl),
      apply_real_add h hψ (hinf u hu) (hε2 u hu g' hl'), hz]
    ring
  obtain ⟨⟨p, hp⟩, hn⟩ := hf.2.norm
  have n1 : nrm2 p.1 p.2 f = 1 := hn p hp
  have hne : (fun z : RW T S => f (iotaW σ T S z)) ≠ 0 := by
    intro h0
    have e := det f f 0 hf.2.theta hf.2.theta hlat hlat fun z => by rw [zero_mul]; exact congrFun h0 z
    rw [e] at n1
    simp [nrm2] at n1
  obtain ⟨j1, j2, j3, j4⟩ := _root_.GlobalTheory.RealSymplForm.form_alt_inv_def D S T sS sT hS hT
  have hsp : Submodule.span ℝ (Set.range (infRat S T)) = ⊤ := by
    have := span_piW_ratW_eq_top D θ σ h T S
    simpa only [piW_ratW hθ] using this
  have a1 := _root_.GlobalTheory.VacUnique.Ann.vacuum_annihilation D θ σ h ψ hψ S T sS sT f hf.2.theta hf.2.fock
  have a2 := _root_.GlobalTheory.VacUnique.Ann.vacuum_annihilation D θ σ h ψ hψ S T sS sT f' hth hfock
  let c : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ := fun v =>
    if hv : finRat S T (-v) ∈ Λ then ψ (-symplOH S T (ratW T S v) (finRat S T (-v))) * ε _ hv else 1
  have hc : ∀ v, ‖c v‖ = 1 := fun v => by
    simp only [c]
    split_ifs with hv
    · rw [norm_mul, hψ.1.2.1]
      rcases hε1 _ hv with e | e <;> rw [e] <;> simp
    · exact norm_one
  have law : ∀ g : WO S T → ℂ, IsThetaFunO ψ S T g → IsLatVac (heisO ψ S T) Λ g →
      ∀ v ∈ Λ.comap (finRat S T), ∀ z, g (iotaW σ T S (z + infRat S T v)) =
        c v * Complex.exp (-(Real.pi * Complex.I) * (omO S T z (infRat S T v) : ℂ)) * g (iotaW σ T S z) := by
    intro g hg hl v hv z
    have hv' : finRat S T (-v) ∈ Λ := (Λ.comap (finRat S T)).neg_mem hv
    rw [apply_add_infRat h hψ hg v (hε2 _ hv' g hl) z, ← j2]
    simp only [c, dif_pos hv']
  have hli := _root_.GlobalTheory.VacuumLine.not_linearIndependent (RW T S) (jO S T sS sT) (omO S T) j1 j2 j3 j4 (Matrix (Fin T.rank) (Fin S.rank) D.host.E)
    (infRat S T) (infRat_injective S T) hsp (Λ.comap (finRat S T))
    (fun x => by
      obtain ⟨N, hN, hx⟩ := hden x
      exact ⟨N, hN, by rwa [AddSubgroup.mem_comap, AddMonoidHom.map_nsmul]⟩)
    (_root_.GlobalTheory.RatSelfDual.finRat_mem_iff D S T ψ Λ hψ hinf h1 h2 hden) c hc
    ![fun z => f (iotaW σ T S z), fun z => f' (iotaW σ T S z)]
    (fun k => by fin_cases k; exacts [a1.1, a2.1]) (fun k => by fin_cases k; exacts [a1.2, a2.2])
    (fun k => by fin_cases k; exacts [law f hf.2.theta hlat, law f' hth hlat'])
  rw [LinearIndependent.pair_iff' hne] at hli
  push_neg at hli
  obtain ⟨a, ha⟩ := hli
  exact ⟨a, det f f' a hf.2.theta hth hlat hlat' fun z => (congrFun ha z).symm⟩

end GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

theorem moved_vacuum_eq_mean : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (m : ℕ) (eT : AE D) (z : GA D V), IsIdemSum eT T → Odd m → Nat.Coprime m (GlobalTheory.Tow.badN D) → (∀ PP ∈ T, ((m : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → z ∈ GfC V → Formalism.L2.Theta.mt V z = flipElt eT m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → ∃ (lam : ℂ) (Y : Finset (WO V W)), (∀ y ∈ Y, IsHalf (cA D eT) y ∧ m • y ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) ∧ (∀ y ∈ Y, ∀ y' ∈ Y, y - y' ∈ latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True) → y = y') ∧ Y.card = flipIdx V W T m ∧ om (z⁻¹, 1) f₀ = lam • ∑ y ∈ Y, heisO ψ V W y f₀ := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T m eT z hT hm hcop hmT hz hmt
  obtain ⟨Y, hY1, hY2, hY3, hYc⟩ := _root_.GlobalTheory.FlipReps.flip_reps D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T m eT hT hm hcop hmT
  set G := ∑ y ∈ Y, heisO ψ V W y f₀ with hG
  obtain ⟨hGth, hGf⟩ := _root_.GlobalTheory.ConjHalfVac.sum_conj_half_vac D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T m eT hT hm hcop hmT Y fun y hy => (hY1 y hy).1
  obtain ⟨hfix2, hfixh⟩ := _root_.GlobalTheory.FlipFixSum.flip_fix D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T m eT hT hm hcop hmT Y hY1 hY2 hY3
  have hne := _root_.GlobalTheory.VacTransNe.sum_heisO_conjHalf_ne_zero D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T m eT hT hm hcop hmT Y hY1 hY2 hY3
  have hW := hP.1.weil

  have hmove : ∀ u : WO V W, actO V W z 1 (flipElt eT m • u) = u := by
    intro u
    have e := GlobalTheory.AdelicLatMove.actO_actO_inv V W z 1 u
    have e2 : actO V W z⁻¹ 1⁻¹ u = flipElt eT m • u := by
      simp only [actO, inv_inv, hmt]
      have h1 : Formalism.L2.Theta.mt W (1 : GA D W)⁻¹ = 1 := by
        rw [inv_one]; unfold Formalism.L2.Theta.mt; rw [map_one]; rfl
      rw [h1, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
    rw [← e2]; exact e
  set H := om (z, 1) G with hH
  have hHth : IsThetaFunO ψ V W H := hW.om_pres _ _ hGth
  have hHh : ∀ u, heisO ψ V W u H = om (z, 1) (heisO ψ V W (flipElt eT m • u) G) := by
    intro u
    rw [hW.om_heis z 1 _ G hGth, hmove]
  have hzf : z ∈ GfC V := hz
  have hHf : ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) (sW τ)) H := by
    intro τ z'
    have c1 : compAt θ τ (Formalism.L2.Theta.mt W (1 : GA D W)) = 1 :=
      GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ W (one_mem _) τ
    have c2 : compAt θ τ (Formalism.L2.Theta.mt V z⁻¹) = 1 :=
      GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ V (inv_mem hzf) τ
    have e1 := GlobalTheory.OrientedHeis.om_dRho hW hP.1.inf z 1 τ z' hGth
    have e2 := GlobalTheory.OrientedHeis.om_dRho hW hP.1.inf z 1 τ (cplxO (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) (sW τ) z') hGth
    rw [c1, c2, Matrix.one_mul, Matrix.mul_one] at e1 e2
    have h0 := hGf τ z'
    unfold annih at h0 ⊢
    rw [hH, ← e1, ← e2, ← map_smul, ← map_add (f := _), h0, map_zero]
  have hHl : IsLatVac (heisO ψ V W) (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) (fun _ => True)) H := by
    refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
    · rw [hHh, hfix2 u hu]
    · rw [hHh, hfixh e he u hu hh]
  obtain ⟨c, hc⟩ := eq_smul_vacuum hP.2.2.2.2.2.2.2.2.1 hP.1.inf (fun τ => GlobalTheory.SmoothVac.isCartanInv_one V hP.1.std τ)
    hP.2.2.2.2.2.2.2.1 hP.2.2.2.2.1 hP.2.2.2.2.2.1 hP.2.2.2.2.2.2.2.2 hHth hHl hHf
  have hback : om (z⁻¹, 1) H = G := by
    rw [hH, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, one_mul, ← Prod.one_eq_mk, map_one,
      Module.End.one_apply]
  have hGc : G = c • om (z⁻¹, 1) f₀ := by rw [← hback, hc, map_smul]
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hne (by rw [← hG, hGc, zero_smul])
  refine ⟨c⁻¹, Y, hY1, hY2, hYc, ?_⟩
  rw [← hG, hGc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
end GlobalTheory.LevelSeries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSetupPinnedCh
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab toAb IsGlobalArtin)
open Formalism.L2.Host (embLL0)

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeriesTie.ComplexCh

variable {D : D7}

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

open GlobalTheory.SeriesTie.Complex (eGc levOf castG levOf_mem levOf_chi)

theorem exists_setup_ch (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (F3 : Face3 D A3) (hC : Rl.Char3 F3)
    (hW : GlobalTheory.Published.WeilRepresentationUnitaryPair)
    (hS0c : ∀ i, ∀ P ∈ D.ntw.S0 i, ∀ P', Formalism.BasicNotions.IsConjPl D.host P P' → P' ∈ D.ntw.S0 i)
    (hS02 : ∀ i, placesOver D.host.E 2 ⊆ ↑(D.ntw.S0 i))
    (hS0A : ∀ i P, P ∉ D.ntw.S0 i → FractionalIdeal.count D.host.E P D.host.AA = 0)
    (hδ : ∃ art : Ideles D.host.E →* Gab D.host.E D.nd.Om, IsGlobalArtin art ∧ ∀ i b,
      ∃ (κ : FractionRing (D.ntw.O0 i) →+* Qbar (D.ntw.l i)) (ι : Qbar (D.ntw.l i) ≃+* ℂ),
        (∀ x, ι (κ ((if b then D.ntw.emb0 i else D.ntw.emb0b i) x)) = embLL0 D x) ∧
        GlobalTheory.GalChar.IsGal art κ ι (Rl.C.delAt (D.ntw.l i)) (fun _ => 0) (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)))
    (hcard : ∀ i k, Cardinal.mk (FractionRing (D.ntw.Ok i k)) ≤ Cardinal.continuum)
    (hspl : (Ideal.primesOver (Ideal.span {(D.host.pde : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E ∧
      (Ideal.primesOver (Ideal.span {(D.host.pde' : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E)
    (hq : D.host.pde ≠ D.host.q ∧ D.host.pde' ≠ D.host.q)
    (ch : D.ntw.Tw → Set (PlE D.host)) (hch1 : ∀ i, IsChoice (D := D) (ch i))
    (hch2 : ∀ i, {P : Pl D.host.E | ∃ t, P ∈ Rl.Q t ∧ P ∈ D.ntw.pD i} ⊆ ch i) :
    ∃ ρ : Setup D.ntw, ρ.Good ∧ RealPin Rl cG ρ ∧ ρ.LevelOf D.nexp ∧ ρ.ch = ch ∧
      ∀ i, ρ.bad i = GlobalTheory.SeriesTie.normProd (D.ntw.S0 i) := by
  classical
  obtain ⟨art, hart, hδ⟩ := hδ
  choose κ ι hκι hG using hδ
  obtain ⟨κA, hκ1, hκ2, hκ3⟩ := GlobalTheory.CharTransport.exists_hom D
  let rc : Recip D D.nd.Om := ⟨κA, art⟩
  have hrc : rc.Good := ⟨hκ1, hκ2, hκ3, hart⟩
  obtain ⟨e, ek, he1, he2, he3⟩ := _root_.GlobalTheory.EmbExt.exists_side_embeddings D D.nd D.ntw (fun i b => (ι i b).toRingHom.comp (κ i b)) hκι hcard
  choose F hF hFstd hFψ hFθ hFsT hFBS hFBT hFΛS hFΛT hFβS hFβT hFf hFlS hFlT using _root_.GlobalTheory.FrameOfReal.exists_frame_real D Γ Pl0 I0 T A3 Ks Rl F3 hC
  let f : ∀ i, Bool → (D.ntw.O0 i →+* ℂ) := fun i b =>
    ((e i b).comp (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)))).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i))
  have hfi : ∀ i b, Function.Injective (f i b) := fun i b =>
    ((e i b).injective.comp (IsFractionRing.injective (D.ntw.O i) (FractionRing (D.ntw.O i)))).comp (D.ntw.O_inj i)
  let de : D.ntw.Tw → Bool → Twist D Circle := fun i b =>
    twistOf rc (f i b) (ch i) (D.ntw.pD i) (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i))
  have hde : ∀ i b, (de i b).Good := fun i b => _root_.GlobalTheory.DeltaGood.twistOf_delta_good D rc hrc i (ch i) (hch1 i) (f i b) (hfi i b) b
  have hpl : ∀ i b, PlacesOK Rl.Pg (de i b).Q := fun i _ =>
    _root_.GlobalTheory.SeriesTie.PlacesGood.placesOK D Γ Pl0 I0 T A3 Ks Rl A3.A.μ0 hC.lev hspl hq i (ch i) (hch1 i)
  have hB := fun i j b => _root_.GlobalTheory.SeriesTie.BaseGood.base_good D Γ Pl0 I0 T A3 Ks Rl F3 hC j (F j) (hF j) (de i b) (hde i b) (hpl i b)
  choose w mu hwp hwm hBg using hB
  let P : D.ntw.Tw → ∀ j : Fin D.R.m, Bool → LevelP Rl.Pg (Wc D j).rank ℂ := fun i j b =>
    ⟨(levOf (eGc Rl cG j) D.nexp.U ((Units.map (e i b).toMonoidHom).comp (D.nexp.psiU i b))).1,
      (levOf (eGc Rl cG j) D.nexp.U ((Units.map (e i b).toMonoidHom).comp (D.nexp.psiU i b))).2⟩
  let B : D.ntw.Tw → ∀ j : Fin D.R.m, Bool → Base (Vc D j) (Wc D j) := fun i j b =>
    ⟨(hF j).rank_le, F j, ⟨Rl.Pg, P i j b, mu i j b⟩, de i b, w i j b, Rl.mu0 ((j : ℕ) + 1), Rl.eta⟩
  have hBG : ∀ i j b, (B i j b).Good := fun i j b => hBg i j b (P i j b)
  have hom : ∀ i j b (χ : (AE D)ˣ →* Circle), ∃ ω : PairRep (Vc D j) (Wc D j),
      ∀ t : Twist D Circle, t.Good → t.chi = χ → (B i j b).IsWeil χ ω := by
    intro i j b χ
    by_cases h : ∃ t : Twist D Circle, t.Good ∧ t.chi = χ
    · obtain ⟨t, ht, rfl⟩ := h
      obtain ⟨ω, hω⟩ := _root_.GlobalTheory.WeilTwistExists.exists_isWeil D _ _ (B i j b) hW (hBG i j b) (hFstd j) t ht
      exact ⟨ω, fun _ _ _ => hω⟩
    · exact ⟨1, fun t ht h' => absurd ⟨t, ht, h'⟩ h⟩
  choose om hom using hom
  have hcl : ∀ i j b (t : Twist D Circle), ∃ (m : ℕ) (h : Fin m → GA D (Vc D j)),
      IsClassSystem (Vc D j) ((B i j b).levJ t) h := fun i j b t =>
    exists_isClassSystem (B i j b) (hBG i j b).frame t
  choose m rep hrep using hcl
  let ρ : Setup D.ntw :=
    { rc := rc
      ch := ch
      bad := fun i => ∏ P ∈ D.ntw.S0 i, Ideal.absNorm P.asIdeal
      e := e
      ek := ek
      B := B
      om := om
      Cl := fun i j b t => Fin (m i j b t)
      rep := rep
      β := fun j P => DetBases.std _ _ _
      eG := fun _ j _ => eGc Rl cG j }
  refine ⟨ρ, ?_, ?_, ?_, rfl, fun _ => rfl⟩
  · exact
      { rc := hrc
        ch := hch1
        bad_ne := fun i => Finset.prod_ne_zero_iff.2 fun P _ h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
        goodSetup_bad_mem_badPlaces := fun i P hP => by
          obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun Q : Pl D.host.E => Ideal.absNorm Q.asIdeal) hP
          change ((∏ P ∈ D.ntw.S0 i, Ideal.absNorm P.asIdeal : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
          rw [hc, Nat.cast_mul]
          exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
        goodSetup_badPlaces_conj := hS0c
        goodSetup_placesOverTwo_subset := hS02
        goodSetup_count_eq_zero_off_badPlaces := hS0A
        e_LL0 := he1
        ek_e := fun i b k x => he2 i b k x
        base := hBG
        latS := fun _ j _ => hFlS j
        latT := fun _ j _ => hFlT j
        Pg := fun _ _ _ P hP => _root_.GlobalTheory.TypePlacesOver.mem_placesOver D Γ Pl0 I0 T A3 Ks Rl F3 hC P hP
        delta := fun _ _ _ => rfl
        weil := fun i j b t ht => hom i j b t.chi t ht rfl
        classes := fun i j b t _ _ => hrep i j b t }
  · exact
      { psi := fun _ j _ => hFψ j
        inf := fun _ j _ => hFθ j
        cartT := fun _ j _ => hFsT j
        onbS := fun _ j _ τ => hFBS j τ
        onbT := fun _ j _ => hFBT j
        latS := fun _ j _ => hFΛS j
        latT := fun _ j _ => hFΛT j
        frS := fun _ j _ => hFβS j
        frT := fun _ j _ => hFβT j
        vac := fun _ j _ => hFf j
        Pg := fun _ _ _ => rfl
        grp := fun _ j _ g P h h' a c => rfl
        mu0 := fun _ _ _ => rfl
        eta := fun _ _ _ => rfl
        delta := fun i j b => by
          exact _root_.GlobalTheory.SeriesTie.charOf_psiAt_chrEq D rc i (κ i b) (ι i b) (Rl.C.delAt (D.ntw.l i)) (D.ntw.delta i) b hrc (D.ntw.delta_open i) (hG i b)
            (f i b) (fun y hy => he3 i b y hy) (ch i) (D.ntw.pD i)
        deltaPl := fun i t P hP hPD => hch2 i ⟨t, hP, hPD⟩
        ap := fun i j b τ => hwp i j b τ
        am := fun i j b τ => hwm i j b τ }
  · exact
      { U_eq := fun i j b g => levOf_mem (eGc Rl cG j) D.nexp.U ((Units.map (e i b).toMonoidHom).comp (D.nexp.psiU i b)) g
        psiU_eq := fun i j b u hu => congrArg Units.val
          (levOf_chi (eGc Rl cG j) D.nexp.U ((Units.map (e i b).toMonoidHom).comp (D.nexp.psiU i b)) u hu) }

end GlobalTheory.SeriesTie.ComplexCh

end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links
  Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TwInputs.SetupPinCh

end GlobalTheory.TwInputs.SetupPinCh

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeChoiceFlatVectorFactoredForm
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.FlatConj

theorem flatVec_factored_form : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∃ (z : GA D (Vc D i)) (B : ℂ) (ε : ℤ) (r : ℕ) (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ), IsCentAt i (R.Q t) z ∧ (∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → τ B = B) ∧ (∀ PP ∈ R.Q t, (ψP PP).IsPrimitive) ∧ ∀ t' : T0, R.Q t' = R.Q t → ∀ f', IsFlatVec R i t' f' → ∃ s : (AE D)ˣ, f' = (B * (∏ PP ∈ R.Q t, GlobalTheory.FlatConj.gaussP PP (ψP PP) (R.xiR t' PP) r) ^ ε * ((R.xi t' s : Circle) : ℂ)) • R.ωP i t' (z, 1) (R.vP i t') :=
  _root_.GlobalTheory.FlatForm.flat_eq_gauss_smul_om

end GlobalTheory.FlatConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftRowsInjectiveAndTypePropertiesOfNonvanishing
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.DownLift

theorem liftRows_injective_and_typeProperties_of_nonvanishing : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → GlobalTheory.RawLift.RallisConv D → (∀ i t, NonVan R i t) → GlobalTheory.LiftRows.LiftInj R ∧ ∀ i t, TypeNZ R i t ∧ GoodMem R i t ∧ DownEig R i t ∧ UnrCorr R i t (fun _ => True) ∧ Saturated R i t := by
  intro hDec hHowe D G _ _ Pl0 T A Ks _ _ _ R F hG hFull hRallis hNV
  have hLaws : GlobalTheory.RawLift.Laws R F :=
    ⟨hG.core.lev, hG.core.grp, hG.core.fam, hG.core.models, hG.core.thP⟩
  have hTop5 := GlobalTheory.RawLift.rawLift_main hDec D G Pl0 T A Ks R F hLaws hFull hRallis
  have hEig : ∀ i t, DownEig R i t := GlobalTheory.DownEigen.downEig hHowe D G Pl0 T A Ks R F hG hFull
  have hGF : ∀ i t, GenFin R i t := GlobalTheory.DownLift.GenFinite.genFin hHowe D G Pl0 T A Ks R F hG hFull
  have hGI : ∀ i t, GenInf R i t := GlobalTheory.GenReal.genInf D G Pl0 T A Ks R F hG hFull
  have hGM : ∀ i t, GoodMem R i t := GlobalTheory.GoodLift.goodMem_of_given D G Pl0 T A Ks R F hG hFull
  have hNC : ∀ i t, GoodNoChi R i t := GlobalTheory.GoodTypeNoChi.goodNoChi D G Pl0 T A Ks R F hG hFull
  have hPar : ∀ i t, ParamsEx R i t := GlobalTheory.DownLift.Params.paramsEx hDec D G Pl0 T A Ks R F hG hFull
  have hIn : ∀ i t, UnrCorr R i t (fun w => Formalism.IndefR.Lev.IsConjPl w w) := GlobalTheory.DownInert.unrCorr_inert hHowe D G Pl0 T A Ks R F hG hFull
  have hSp : ∀ i t, UnrCorr R i t (fun w => ¬ Formalism.IndefR.Lev.IsConjPl w w) := GlobalTheory.SplitCorr.unrCorr_split D G Pl0 T A Ks R F hG hFull
  have hTNZ : ∀ i t, TypeNZ R i t := fun i t =>
    GlobalTheory.DownLift.typeNZ_of_nonVan_gen D G Pl0 T A Ks R F hG hFull i t (hNV i t) (hGI i t) (hGF i t) (hNC i t) (hGM i t)
  have hU : ∀ i t, UnrCorr R i t (fun _ => True) := by
    intro i t h hh s c y hy h1 h2 B B' hB hB' w hw _
    by_cases hc : Formalism.IndefR.Lev.IsConjPl w w
    · exact hIn i t h hh s c y hy h1 h2 B B' hB hB' w hw hc
    · exact hSp i t h hh s c y hy h1 h2 B B' hB hB' w hw hc
  refine ⟨GlobalTheory.LiftInjProof.liftInj_of_typeNZ D G Pl0 T A Ks R F hG hFull
      (fun i => ⟨hTNZ i A.μ0, hEig i A.μ0, hSp i A.μ0, hIn i A.μ0, hPar i A.μ0⟩), fun i t => ?_⟩
  refine ⟨hTNZ i t, hGM i t, hEig i t, hU i t, ?_⟩
  exact GlobalTheory.DownLift.Sat.saturated hDec hHowe D G Pl0 T A Ks R F hG hFull i t (hTNZ i t) (hEig i t) (hGM i t)
    ((hTop5.2 i t).1) (hU i t) (hPar i t)

end GlobalTheory.DownLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergPartialLTendstoNeZeroAtOneStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankinSelberg_partialL_tendsto_ne_zero_at_one : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a b : ℕ) (σ : CG E a) (σ' : CG E b), 1 ≤ a → 1 ≤ b → σ.IsUnitary → σ'.IsUnitary → (⟨a, σ⟩ : Σ a, CG E a) ≠ ⟨b, σ'⟩ → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T σ → UnrOutside T σ' → ∃ z : ℂ, z ≠ 0 ∧ Tendsto (fun x : ℝ => ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (𝓝[>] 1) (𝓝 z) := by
  first | (exact @GlobalTheory.RSNonvan.tendsto_partialL_ne_zero) | (exact GlobalTheory.RSNonvan.tendsto_partialL_ne_zero) | (intros; apply GlobalTheory.RSNonvan.tendsto_partialL_ne_zero  <;> assumption)
end

