module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0008
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThU
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0745
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0695
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteStabFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0378
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0834
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0763
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0840
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0900
public import GroundTheory.GlobalFields.TateThesis.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0852
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0919
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0872
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0848
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0849
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0851
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0839

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivialPartInBaseChange
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.MuBlockLoc

theorem placesOver_finite (D : D7) (k : Fin 2) : (placesOver D.host.E (D.host.g k)).Finite := by
  have hne : Ideal.span {((D.host.g k : ℕ) : 𝓞 D.host.E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (D.host.g_prime k).ne_zero
  refine (Ideal.finite_factors hne).subset fun v hv => ?_
  exact Ideal.dvd_span_singleton.mpr hv

theorem mem_isoInf (D : D7) (Pa : List (Part D.naut.CG)) (p : Part D.naut.CG) (hp : p ∈ Pa) (hd : 1 ≤ p.d)
    (τ : D.host.E →+* ℂ) :
    (D.naut.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - (0 : ℂ))) ≤ isoInf D.nd D.naut Pa τ := by
  unfold isoInf
  refine le_trans ?_ (List.single_le_sum (by intro x _; exact Multiset.zero_le x) _ (List.mem_map.2 ⟨p, hp, rfl⟩))
  refine List.single_le_sum (by intro x _; exact Multiset.zero_le x) _ (List.mem_map.2 ⟨(0 : ℂ), ?_, rfl⟩)
  simp
  exact ⟨0, hd, by simp⟩

theorem mu_ralg (D : D7) (Rw : RowSide D) (j : ℕ) (σ : D.what₂.FT) (π : D.nbc.AU j) (μ : D.naut.CG 1)
    (hA : LiftAt D Rw j σ π μ) : D.naut.ralg μ := by
  obtain ⟨a, ha⟩ := GlobalTheory.LocalInv.r_odd D.R
  have hnV : (D.R.nV : ℂ) = 2 * (a : ℂ) + 1 + D.R.t := by
    show ((D.R.r + D.R.t : ℕ) : ℂ) = _
    rw [ha]; push_cast; ring
  have ht1 : 1 ≤ D.R.t := D.R.t_odd.pos
  have hq : ∀ (τ : D.host.E →+* ℂ) (s : ℂ), D.naut.infG D.naut.etaTinv τ = {s} →
      (∀ x ∈ isoInf D.nd D.naut [⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩] τ, ∃ k : ℤ, x = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2) →
      ∀ z ∈ D.naut.infG μ τ, ∃ k : ℤ, z + s + ((D.R.t : ℂ) - 1) / 2 = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2 := by
    intro τ s hs hx z hz
    have hle := mem_isoInf D [⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩] ⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩
      (List.mem_singleton_self _) ht1 τ
    dsimp only at hle
    rw [D.naut.infG_tw _ _ τ s hs, Multiset.map_map] at hle
    obtain ⟨k, hk⟩ := hx _ (Multiset.mem_of_le hle (Multiset.mem_map_of_mem _ hz))
    exact ⟨k, by rw [← hk]; simp⟩
  refine (D.naut.ralg_def _).2 fun φ => ?_
  obtain ⟨z0, hz0⟩ := Multiset.card_eq_one.mp (D.naut.infG_card μ φ)
  refine ⟨by rw [hz0]; exact Multiset.nodup_singleton z0, fun z hz => ?_⟩
  obtain ⟨τ, hτ | hτ⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.emb_cases D φ
  · have e : φ = GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ := hτ
    subst e
    have hx : ∀ x ∈ isoInf D.nd D.naut [⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩] (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ),
        ∃ k : ℤ, x = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2 := fun x hx =>
      (D.nbc.infW_alg j (D.nbc.wtAU j π) _).2 x (by rw [(hA.inf τ).1]; exact Multiset.mem_add.2 (Or.inr hx))
    obtain ⟨k, hk⟩ := hq _ _ (hA.eta τ).1 hx z hz
    refine ⟨k + a + 1, ?_⟩
    rw [hnV] at hk
    push_cast
    linear_combination hk
  · have e : φ = GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ := hτ
    subst e
    have hx : ∀ x ∈ isoInf D.nd D.naut [⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩] (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ),
        ∃ k : ℤ, x = (k : ℂ) + ((D.R.nV : ℂ) - 1) / 2 := fun x hx =>
      (D.nbc.infW_alg j (D.nbc.wtAU j π) _).2 x (by rw [(hA.inf τ).2]; exact Multiset.mem_add.2 (Or.inr hx))
    obtain ⟨k, hk⟩ := hq _ _ (hA.eta τ).2 hx z hz
    refine ⟨k + a, ?_⟩
    rw [hnV] at hk
    push_cast
    linear_combination hk

end GlobalTheory.MuBlockLoc

namespace GlobalTheory.MuBlockLoc

end GlobalTheory.MuBlockLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedPlaceInnerProductClassSumRows
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
  Formalism.IndefR.RecTie Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.CoefDuty GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option maxHeartbeats 1000000

namespace GlobalTheory.FormInner

theorem ipVia_apply {H N : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [AddCommGroup N] [Module ℂ N]
    (e : H →ₗ[ℂ] N) (he : Function.Injective e) (u v : H) : ipVia e (e u) (e v) = ⟪u, v⟫_ℂ := by
  unfold ipVia
  split_ifs with h
  · rw [he h.1.choose_spec, he h.2.choose_spec]
  · exact absurd ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩ h

section Gen

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3} {X0 : BaseLevelRowSide D}

theorem classSum_of_ad (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (hM : R.toRealDat.IsModels)
    (hB : ∀ i, IsBaseFrame (Vc D i) (R.βV i) (R.ΛV i) 1) {M : MtFam D} (ad : MtAd Y M) (hrat : ∀ i, RatFrame (ad.PV i))
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (i : Fin D.R.m) (hX : IsBounded (M μ (i.1 + 1) (by omega) (by omega)).J) :
    ClassSum (M μ (i.1 + 1) (by omega) (by omega)) := by
  classical
  set t := Y.tupT μ
  have hHV := hM.HV i t
  have hcV := hM.cV i
  have hrange : ∀ x : D.what₂.Mt μ (i.1 + 1), ∃ h, R.toRealDat.extV i t h = (Y.IL.jMt μ hμ i x).1 := fun x =>
    ((Y.IL.jMt μ hμ i x).2.1 : _)
  choose hv hhv using hrange
  let Fm : D.what₂.Mt μ (i.1 + 1) → Bridge.Gf (Vc D i) → (R.cV i).W := fun x => (R.HV i t).e (hv x)
  have hFm : ∀ x, Fm x ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ (levEnv _ (R.βV i) (R.datVt i t)).J
      (levEnv _ (R.βV i) (R.datVt i t)).χ := fun x => hHV.2.1 ▸ LinearMap.mem_range_self _ _
  have hread : ∀ x g, ad.eW μ hμ i ((M μ (i.1 + 1) (by omega) (by omega)).real x g) = Fm x (frameEquiv (ad.PV i) g) := by
    intro x g
    rw [ad.read, ← hhv]
    show (R.cV i).ρ ((ad.PV i).ψ g)⁻¹ (Fm x ((finHom (Vc D i)).rangeRestrict ((ad.PV i).ψ g))) = _
    rw [hcV.1 _ ((GfC (Vc D i)).inv_mem ((ad.PV i).into g))]
    rfl
  have hip : ∀ x x' : D.what₂.Mt μ (i.1 + 1), inner ℂ x x' = (((RealDat.nP F.lv2 false)⁻¹ : ℝ) : ℂ) *
      Bridge.adInner (Bridge.ratF (Vc D i)) (levEnv _ (R.βV i) (R.datVt i t)).J (R.B.L i t).pres.y (Fm x) (Fm x') := by
    intro x x'
    rw [Y.tied.lift.mt μ hμ i x x']
    show (((RealDat.nP F.lv2 false)⁻¹ : ℝ) : ℂ) * ipVia (R.toRealDat.extV i t) (Y.IL.jMt μ hμ i x).1 (Y.IL.jMt μ hμ i x').1 = _
    rw [← hhv, ← hhv, ipVia_apply _ (Y.hinj i t), hHV.2.2]
  have hnP : 0 < (RealDat.nP F.lv2 false)⁻¹ := by
    unfold RealDat.nP
    exact inv_pos.2 (Nat.cast_pos.2 Nat.card_pos)
  exact classSum_of_read (M μ (i.1 + 1) (by omega) (by omega)) (Bridge.ratF (Vc D i)) (frameEquiv (ad.PV i))
    (R.cV i).coef.ρ _ (levEnv _ (R.βV i) (R.datVt i t)).χ (ad.eW μ hμ i) Fm (R.B.L i t).pres.y (R.B.L i t).pres.reps
    (ratF_injective _) (RatFrame.iff (hrat i)) (fun δ a b => hcV.2.1 _ a b)
    ⟨{1}, fun κ hκ => ⟨1, by simp, by simpa using comap_le_Umax (ad.std i) (hB i) (R.datVt i t) hκ⟩⟩ hX hFm
    hread _ hnP hip (fun _ => GlobalTheory.InvFormBdd.exists_isInvForm _ _ _)

theorem classSum_of_std (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (hM : R.toRealDat.IsModels)
    (hB : ∀ i, IsBaseFrame (Vc D i) (R.βV i) (R.ΛV i) 1) {M : MtFam D} (ad : MtAd Y M) (hV : ∀ i, GlobalTheory.StdFrame.OrthFrame (Vc D i))
    (μ : D.what₂.Tup) (hμ : Used0 D μ) (i : Fin D.R.m) (hX : IsBounded (M μ (i.1 + 1) (by omega) (by omega)).J) :
    ClassSum (M μ (i.1 + 1) (by omega) (by omega)) := by
  classical
  set t := Y.tupT μ
  have hHV := hM.HV i t
  have hcV := hM.cV i
  have hrange : ∀ x : D.what₂.Mt μ (i.1 + 1), ∃ h, R.toRealDat.extV i t h = (Y.IL.jMt μ hμ i x).1 := fun x =>
    ((Y.IL.jMt μ hμ i x).2.1 : _)
  choose hv hhv using hrange
  let Fm : D.what₂.Mt μ (i.1 + 1) → Bridge.Gf (Vc D i) → (R.cV i).W := fun x => (R.HV i t).e (hv x)
  have hFm : ∀ x, Fm x ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ (levEnv _ (R.βV i) (R.datVt i t)).J
      (levEnv _ (R.βV i) (R.datVt i t)).χ := fun x => hHV.2.1 ▸ LinearMap.mem_range_self _ _
  have hread : ∀ x g, ad.eW μ hμ i ((M μ (i.1 + 1) (by omega) (by omega)).real x g) = Fm x (frameEquiv (ad.PV i) g) := by
    intro x g
    rw [ad.read, ← hhv]
    show (R.cV i).ρ ((ad.PV i).ψ g)⁻¹ (Fm x ((finHom (Vc D i)).rangeRestrict ((ad.PV i).ψ g))) = _
    rw [hcV.1 _ ((GfC (Vc D i)).inv_mem ((ad.PV i).into g))]
    rfl
  have hip : ∀ x x' : D.what₂.Mt μ (i.1 + 1), inner ℂ x x' = (((RealDat.nP F.lv2 false)⁻¹ : ℝ) : ℂ) *
      Bridge.adInner (Bridge.ratF (Vc D i)) (levEnv _ (R.βV i) (R.datVt i t)).J (R.B.L i t).pres.y (Fm x) (Fm x') := by
    intro x x'
    rw [Y.tied.lift.mt μ hμ i x x']
    show (((RealDat.nP F.lv2 false)⁻¹ : ℝ) : ℂ) * ipVia (R.toRealDat.extV i t) (Y.IL.jMt μ hμ i x).1 (Y.IL.jMt μ hμ i x').1 = _
    rw [← hhv, ← hhv, ipVia_apply _ (Y.hinj i t), hHV.2.2]
  have hnP : 0 < (RealDat.nP F.lv2 false)⁻¹ := by
    unfold RealDat.nP
    exact inv_pos.2 (Nat.cast_pos.2 Nat.card_pos)
  exact classSum_of_frame (M μ (i.1 + 1) (by omega) (by omega)) (Bridge.ratF (Vc D i)) (frameEquiv (ad.PV i))
    (R.cV i).coef.ρ _ (levEnv _ (R.βV i) (R.datVt i t)).χ (ad.eW μ hμ i) Fm (R.B.L i t).pres.y (R.B.L i t).pres.reps
    (ratF_injective _) (finite_stab_frame (hV i) (ad.std i)) (fun δ a b => hcV.2.1 _ a b)
    (comap_le_Umax (ad.std i) (hB i) (R.datVt i t)) hX hFm
    hread _ hnP hip

theorem classSum_twisted_std (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (hM : R.toRealDat.IsModels)
    (hB : ∀ i, IsBaseFrame (Vc D i) (R.βV i) (R.ΛV i) 1) {M : MtFam D} (ad : MtAd Y M) (hV : ∀ i, GlobalTheory.StdFrame.OrthFrame (Vc D i))
    {tup : D.what₂.Tup → Fin D.R.m → Formalism.L2.Host.HChar D.host.E} {Q : D.what₂.places.Pl → Finset (PlE D.host)}
    (hin : MtInput D M tup Q) (v : D.what₂.places.Pl) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hv : TwistedAt D v) :
    ClassSum (M (D.what₂.muTw v) j h1 h2) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  have hμ : Used0 D (D.what₂.muTw v) := Or.inr ⟨v, ((D.what₂.muAt_or v).resolve_left hv).symm⟩
  exact classSum_of_std Y hM hB ad hV _ hμ ⟨k, by omega⟩
    ⟨{1}, fun κ hκ => ⟨1, by simp, by simpa using level_le_Umax hin v ⟨k, by omega⟩ hκ⟩⟩

end Gen

theorem orthFrame_of_vStd {D : D7} (i : Fin D.R.m) (h : Formalism.IndefR.FWT.VStd D i) : GlobalTheory.StdFrame.OrthFrame (Vc D i) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.StdFrameCounterexample.vstd_iff i).1 h
  refine ⟨fun a b => (congrFun (congrFun h1 a) b).trans Matrix.one_apply, fun a => ?_⟩
  have := (h2 (Pi.single a 1)).2 fun b => by
    rw [Pi.single_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  simpa [Pi.single_apply] using this

theorem sumTw_rows : OverRows fun _ _ _ _ w Z _ _ z _ Y => ∀ (M : MtFam (w.st Z).toD7) tup Q, MtAd Y M → MtInput (w.st Z).toD7 M tup Q → SumTw (w.st Z).toD7 M := by
  refine (GlobalTheory.Mem.Top.evG_of_ev GlobalTheory.Mem.StdSize.vstd_size_ev).imp fun K _ _ _ _ hK =>
    GlobalTheory.Mem.Top.GroupRetwisting.lg_all K fun B f T hO _ w _ Z Wt hX z p0 Y _ _ _ _ _ M tup Q a hin v hv j h1 h2 => ?_
  obtain ⟨hV, -⟩ := hK (w.st Z) hO
  obtain ⟨hB, hM⟩ : (∀ i, Formalism.IndefR.Lev.IsBaseFrame (Formalism.IndefR.Links.Vc (w.st Z).toD7 i) (z.R.βV i) (z.R.ΛV i) 1) ∧
      z.R.toRealDat.IsModels := by
    refine ⟨fun i => ?_, z.pins.char.base.models⟩
    obtain ⟨c, hc⟩ := z.pins.char.base.lev.βV i
    rwa [one_pow] at hc
  exact classSum_twisted_std Y hM hB a (fun i => orthFrame_of_vStd i (hV i)) hin v j h1 h2 hv

end GlobalTheory.FormInner

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedWhittakerIntegralEqEulerProductSchurSums
section
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.RSCell

theorem exists_isUnifV : ∀ (E : Type) [Field E] [NumberField E], ∃ ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ, ∀ w, IsUnifV E w (ϖ w : w.adicCompletion E) := by
  intro E _ _
  refine ⟨fun w => GroundTheory.Global.uniformizerUnit w, fun w => ?_⟩
  have h := GroundTheory.Global.valued_uniformizerUnit_zpow w 1
  rw [zpow_one] at h
  exact h


set_option maxHeartbeats 4000000 in
theorem lintegral_unfolded_eq : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CG E a), 1 ≤ a → π.IsUnitary →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T π →
    ∃ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin a → ℂˣ) (ℓ : Fin a) (Φ : (Fin a → Cinf E) → ℂ)
      (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (π₀ : CuspSub E a) (ω : HChar E) (φ : Sm E a),
      (ℓ : ℕ) + 1 = a ∧
      (∀ w, Finset.univ.val.map (α w) = sat π w) ∧ CG.mk π₀ = π ∧ ω.IsUnitary ∧ π₀.HasCentChar ω ∧
      (φ ∈ π₀.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π₀) ∧ φ ≠ 0 ∧
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ ∧
      (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧ Φ ≠ 0 ∧
      ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕₀ : Set (GA E a)), IsFundamentalDomain (GlobalTheory.CellDec.NE E a) 𝓕₀ μ →
        ∃ H : ℝ → ℝ, ContinuousWithinAt H (Set.Ioi 1) 1 ∧ 0 < H 1 ∧ ∀ x : ℝ, 1 < x → 0 < H x ∧
          ∫⁻ g in 𝓕₀, ‖GlobalTheory.RSTheta.rsPsi ℓ (GlobalTheory.JSW.whit φ.1) (GlobalTheory.JSW.whit φ.1) Φ J η g (g.val ℓ)‖ₑ * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ =
            ENNReal.ofReal (H x) * GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
              (fun w i => ((α w i : ℂˣ) : ℂ)) x := by
  intro E _ _ _ a π ha hπ T hT
  obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
  obtain ⟨α, π₀, ω, hα, hmk, hωu, hω, hπ₀, hsat⟩ := GlobalTheory.T.exists_cuspRep_bump_data_satake_unitary E (m + 1) π hπ T hT
  obtain ⟨ϖ, hϖ⟩ := exists_isUnifV E
  obtain ⟨F, hF, l₀, hl₀, ⟨U, hUo, hU⟩, hK, hW0, ⟨C, hC, hCp⟩, hprof⟩ := GlobalTheory.T.exists_shifted_vector_shintani_formula_ramified E m T π₀ hπ₀ α hsat ϖ hϖ
  have hSm : F ∈ Sm E (m + 1) := (GlobalTheory.MSpanDecay.mspanR_le_goodSub hπ₀ hF : GlobalTheory.MSpanDecay.Good F).mem_Sm
  let φ : Sm E (m + 1) := ⟨F, hSm⟩
  have hFc : Continuous F := by
    refine GlobalTheory.CuspRep.ContAut.continuous_of_isOpen_stab E (m + 1) φ
      (GlobalTheory.CuspRep.isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (hUo.mem_nhds U.one_mem) fun k hk => ?_))
    exact Subtype.ext (funext fun g => hU k hk g)
  obtain ⟨hWc, hWN⟩ := _root_.GlobalTheory.JSW.WhitNorm.continuous_whit_and_norm_mul E (m + 1) F hFc (_root_.GlobalTheory.JSW.mspanR_left_invariant E (m + 1) π₀ F hF)
  obtain ⟨Φ, J, hΦs, hΦc, hΦr, hΦreal, hΦ1, hJ0, horb⟩ := GlobalTheory.T.exists_archimedeanBump_ideal_rowOrbit E (m + 1) (Fin.last m) T U hUo
  have hWU : ∀ u ∈ U, ∀ g, GlobalTheory.JSW.whit F (g * finGL E (m + 1) u) = GlobalTheory.JSW.whit F g := fun u hu g => by
    rw [GlobalTheory.JSW.whit_mul_right]
    exact congrArg (fun f => GlobalTheory.JSW.whit f g) (funext fun z => hU u hu z)
  have hWK : ∀ k ∈ GlobalTheory.CellDec.US E (m + 1) T, GeneralLinearGroup.map (pInf E) k = 1 →
      (∀ w ∈ T, GlobalTheory.CellDec.compV E (m + 1) w k = 1) → ∀ g, GlobalTheory.JSW.whit F (g * k) = GlobalTheory.JSW.whit F g :=
    fun k hk h1 h2 g => by
      rw [GlobalTheory.JSW.whit_mul_right]
      exact congrArg (fun f => GlobalTheory.JSW.whit f g) (funext fun z => hK k hk h1 h2 z)
  let αc : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin (m + 1) → ℂ := fun w i => ((α w i : ℂˣ) : ℂ)
  have hpw := GlobalTheory.T.cell_identity_rankinSelberg_torus_translate E m T ϖ hϖ αc F l₀ U Φ J hl₀ hWU hWK hWN hprof hΦr hJ0
    (fun y hy => (horb y hy).imp fun κ hκ => ⟨hκ.1, hκ.2.2⟩)
  obtain ⟨K, hKc, hKp⟩ := GlobalTheory.T.cell_decomposition_lattice_integral_unfolding E m T ϖ hϖ F l₀ U Φ J C hC hl₀ hWU hWK hWN hCp hΦc hΦr hJ0 horb
  obtain ⟨hBc, hBN, hBtop⟩ := _root_.GlobalTheory.RSCellB.bInt_continuous_invariant_finite E (m + 1) (Fin.last m) (by simp) F Φ J (Pi.single (Fin.last m) 1) hWc hWN
    hΦs.continuous hΦr
  have hΦ1' : Φ (Pi.single (Fin.last m) 1) ≠ 0 := fun h => by rw [h] at hΦ1; simp at hΦ1
  have hone := _root_.GlobalTheory.RSCell.bInt_tl_last_ne_zero E m T ϖ F Φ J l₀ hl₀ hW0 hΦ1'
  refine ⟨α, Fin.last m, Φ, J, Pi.single (Fin.last m) 1, π₀, ω, φ, by simp, hα, hmk, hωu, hω, Or.inr hF, ?_, hΦs,
    hΦc, hΦr, hΦreal, fun h => hΦ1' (congrFun h _), ?_⟩
  · intro h
    apply hW0
    have e : F = 0 := congrArg Subtype.val h
    rw [e]
    simp [GlobalTheory.JSW.whit, GroundTheory.Automorphic.FourierWhittaker.whittaker]
  intro μ _ 𝓕₀ h𝓕

  obtain ⟨B, hBdef⟩ : ∃ B : ℝ → GA E (m + 1) → ℝ, B = fun x g =>
      (GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * g)).toReal :=
    ⟨_, rfl⟩
  have hB1 : Continuous (Function.uncurry B) := by
    have h1 : Continuous fun p : ℝ × GA E (m + 1) => (p.1, GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * p.2) :=
      continuous_fst.prodMk (continuous_const.mul continuous_snd)
    have h2' := hBc.comp h1
    have h2 : Continuous fun p : ℝ × GA E (m + 1) => GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) p.1
        (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * p.2) := h2'
    have h3 := ENNReal.continuousOn_toReal.comp_continuous h2 fun p => hBtop _ _
    subst hBdef
    exact h3
  have hBg : ∀ (x : ℝ) (h : GA E (m + 1) → GA E (m + 1)), Continuous h →
      Continuous fun g => GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (h g) := by
    intro x h hh
    have h2 := hBc.comp (continuous_const.prodMk hh : Continuous fun g => (x, h g))
    exact h2
  have hB2 : ∀ x g, 0 ≤ B x g := fun _ _ => by rw [hBdef]; exact ENNReal.toReal_nonneg
  have hB3 : ∀ x, 0 < B x 1 := fun x => by
    rw [hBdef]
    refine ENNReal.toReal_pos ?_ (hBtop _ _)
    rw [mul_one]
    exact hone x
  have hB4 : ∀ x, ∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, B x (u * g) = B x g := fun x u hu g => by
    rw [hBdef]
    beta_reduce
    have e : GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * (u * g) =
        (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * u * (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1)⁻¹) * (GlobalTheory.CellDec.tl (m + 1) ϖ l₀.1 * g) := by
      group
    rw [e, hBN x _ (GlobalTheory.CellDec.tl_conj_mem ϖ l₀.1 hu)]
  have hB5 : ∃ K : Set (GA E (m + 1)), IsCompact K ∧ ∀ x g, g ∈ GlobalTheory.CellDec.C0 E (m + 1) T → B x g ≠ 0 →
      ∃ u ∈ GlobalTheory.CellDec.NA E (m + 1), u * g ∈ K :=
    ⟨K, hKc, fun x g hg h => hKp x g hg fun h0 => h (by rw [hBdef]; simp only; rw [h0]; rfl)⟩
  obtain ⟨hI, hIc⟩ := _root_.GlobalTheory.RSLocalPart.lintegral_cell_pos_lt_top_continuous E (m + 1) μ T 𝓕₀ h𝓕 B hB1 hB2 hB3 hB4 hB5
  have hd : 0 < GlobalTheory.CellDec.dinv (m + 1) l₀.1 := by
    unfold GlobalTheory.CellDec.dinv
    refine Finset.prod_pos fun w _ => zpow_pos ?_ _
    have := NumberField.HeightOneSpectrum.one_lt_absNorm w
    unfold Formalism.UG.qV
    exact_mod_cast (zero_lt_one.trans this)

  have key : ∀ x : ℝ, ∫⁻ g in 𝓕₀, GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x g ∂μ =
      GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal) αc x *
        (ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l₀.1) *
          ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) T, ENNReal.ofReal (B x g) ∂μ) := by
    intro x
    have hmeas : ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) T, Measurable fun g =>
        GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) := fun l =>
      (hBg x _ (continuous_const.mul continuous_id)).measurable
    have hnm : NullMeasurableSet (𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) T) μ :=
      h𝓕.nullMeasurableSet.inter (GlobalTheory.CellDec.isOpen_adelicUnipotentTimesIntegralOutsideSet E (m + 1) T).measurableSet.nullMeasurableSet
    have hmx : Measurable fun g => GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x g :=
      (hBg x (fun g => g) continuous_id).measurable
    rw [GlobalTheory.CellDec.cell_lintegral μ T ϖ hϖ 𝓕₀ h𝓕 _ hmx
      (hBN x), ← _root_.GlobalTheory.RSCellSum.tsum_cellProd_sub_eq_eulD E (m + 1) T αc x l₀, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun l => ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have e1 : ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) T, ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l.1) *
          GlobalTheory.RSCell.bInt (Fin.last m) F Φ J (Pi.single (Fin.last m) 1) x (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) ∂μ =
        ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) T, ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l₀.1) *
          ENNReal.ofReal (B x g) * GlobalTheory.RSCell.cellProd T αc x (l.1 - l₀.1) ∂μ := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_restrict_mem₀ hnm] with g hg
      rw [hpw x g hg.2 l, hBdef, ENNReal.ofReal_toReal (hBtop _ _)]
    have hm2 : Measurable fun g => ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l₀.1) * ENNReal.ofReal (B x g) := by
      rw [hBdef]
      exact measurable_const.mul (ENNReal.measurable_ofReal.comp (ENNReal.measurable_toReal.comp (hmeas l₀)))
    rw [e1, lintegral_mul_const _ hm2, mul_comm, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine ⟨fun x => (ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l₀.1) *
    ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) T, ENNReal.ofReal (B x g) ∂μ).toReal, ?_, ?_, fun x _ => ⟨?_, ?_⟩⟩
  · have e : (fun x => (ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l₀.1) *
        ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) T, ENNReal.ofReal (B x g) ∂μ).toReal) =
        fun x => GlobalTheory.CellDec.dinv (m + 1) l₀.1 * (∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) T, ENNReal.ofReal (B x g) ∂μ).toReal := by
      funext x
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hd.le]
    rw [e]
    exact (continuous_const.mul hIc).continuousWithinAt
  · exact ENNReal.toReal_pos (mul_ne_zero (ENNReal.ofReal_pos.2 hd).ne' (hI 1).1.ne')
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hI 1).2.ne)
  · exact ENNReal.toReal_pos (mul_ne_zero (ENNReal.ofReal_pos.2 hd).ne' (hI x).1.ne')
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hI x).2.ne)
  · rw [ENNReal.ofReal_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hI x).2.ne), mul_comm]
    exact key x

end GlobalTheory.RSCell
end
end

