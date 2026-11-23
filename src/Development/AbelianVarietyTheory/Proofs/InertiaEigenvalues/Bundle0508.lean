module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0332
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0472
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0470
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0436
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0351
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0358
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0491
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBetaUniqueModEPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0404
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0379
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0369
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0386
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0483

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleComparisonPiWachLatticeClosedWeak
section
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology

namespace GlobalTheory.WeakClosed

variable {l : ℕ} [Fact l.Prime]

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

theorem hausdorff_tilt_witt : letI := cbTop l; T2Space (Cb l) := by
  letI := cbValued l
  infer_instance

theorem ring_cb : letI := cbTop l; IsTopologicalRing (Cb l) := by
  letI := cbValued l
  infer_instance

theorem jD_piN_closed : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL), IsCrys ((D.loc l).PD K) T.ρ → ∃ τ : TopologicalSpace (TW (RW LL) T), letI := τ; T2Space (TW (RW LL) T) ∧ IsTopologicalAddGroup (TW (RW LL) T) ∧ (∀ b : TW (RW LL) T, Continuous (fun g : ↥(GK K) => TWact ((D.locA l).gRW LL (g : GQ l)) T g b)) ∧ Continuous (fun t : ↥T.L.T => (1 : RW LL) ⊗ₜ[↥(OL LL)] t) ∧ IsClosed (((F l).E K s LL h).tie.jD T '' (aN ((HW l).W K s LL h) T letπ : Set (((HW l).W K s LL h).DD T))) := by
  intro D HW F l _ K s LL h T _
  haveI := LL.2
  haveI : Module.Free ℤ_[l] ↥(OL LL) :=
    (GlobalTheory.Per.integers_completeDVR l LL).elim fun _ h => h.2.2.2.1
  haveI : Module.Finite ℤ_[l] ↥(OL LL) :=
    (GlobalTheory.Per.integers_completeDVR l LL).elim fun _ h => h.2.2.2.2.1
  obtain ⟨d, ⟨b⟩⟩ : ∃ d : ℕ, Nonempty (LatB T d) := GlobalTheory.Cyc.exists_basis_lat (R := ℤ_[l]) T
  let bO := Module.finBasis ℤ_[l] ↥(OL LL)
  letI τ := twTop T b
  letI tW : TopologicalSpace (WCb l) := wTop l
  letI := cbTop l
  haveI := hausdorff_tilt_witt (l := l)
  haveI := ring_cb (l := l)
  haveI : T2Space (WCb l) := GlobalTheory.WeakTop.t2Space_wittVector_product
  haveI : IsTopologicalRing (WCb l) := GlobalTheory.WeakTop.isTopologicalRing_witt
  letI := zlMod T
  haveI := zlTower T
  have hc : Continuous (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b) := continuous_induced_dom
  haveI hT2 : T2Space (TW (RW LL) T) :=
    T2Space.of_injective_continuous (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b).injective hc
  haveI hAG : IsTopologicalAddGroup (TW (RW LL) T) :=
    Topology.IsInducing.topologicalAddGroup (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b) ⟨rfl⟩
  refine ⟨τ, hT2, hAG, GlobalTheory.T.continuous_galois_orbit_wittTensorLatticeWeakTopology (D.locA l) T b, GlobalTheory.T.continuous_one_tmul_latB T b, ?_⟩
  obtain ⟨r, y, hy⟩ := _root_.GlobalTheory.NL.WkRange.jD_aN_eq_range ((F l).E K s LL h) T
  rw [hy]
  letI := aTop (K := K) bO
  haveI := GlobalTheory.T.compactSpace_aTop' (K := K) bO
  refine (isCompact_range ?_).isClosed
  refine continuous_finsetSum _ fun i _ => ?_
  exact (GlobalTheory.T.continuous_wittCbInclusion_smul_weakTopology ((F l).E K s LL h) T b bO (y i)).comp (continuous_apply i)

end GlobalTheory.WeakClosed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBaseEqOfClosedDiscExtendsNormLeOne
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem exists_toDisc_eq_of_extends_norm_le_one : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type)
    [CommRing A] (s : bk.S →+* A) (ι : Type), TopBasis s bk.J ι → ∀ ρ : ℝ≥0, 0 < ρ → ρ < 1 →
    ∀ y : Disc l (s X) ρ, (∀ ρ₁ : ℝ≥0, ρ₁ < 1 → ∃ (ρ' : ℝ≥0) (R : Disc l (s X) ρ' →+* Disc l (s X) ρ)
      (y' : Disc l (s X) ρ'), ρ₁ ≤ ρ' ∧ ρ ≤ ρ' ∧ ρ' < 1 ∧ IsDiscMap (l := _) (u := _) (ρ := _) (RingHom.id A) R ∧ R y' = y ∧ ‖y'‖ ≤ 1) →
    ∃ a, toDisc l (s X) ρ a = y := by
  intro l _ K bk A _ s ι TB ρ hρ hρ1 y hy
  have hj : ∀ ρ' : ℝ≥0, 0 < ρ' → ∃ j : bk.DS ρ' →+* Disc l (s X) ρ', IsDiscMap (l := _) (u := _) (ρ := _) s j := fun ρ' h =>
    GlobalTheory.T.exists_closedDiscExtension_of_pow_dvd l bk.S A s X (s X) ρ' ρ' 1 h (by rw [pow_one]) (by rw [pow_one])
  obtain ⟨j, hjd⟩ := hj ρ hρ
  obtain ⟨cD, hc1, -, hc3, hc4, -, hc6, -, -⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A s ι TB ρ hρ hρ1 j hjd

  have hz : ∀ i, ∃ z : bk.S, toDisc l (X : bk.S) ρ z = cD i y := by
    intro i
    apply GlobalTheory.T.disc_bounded_function_isPowerSeries l K bk ρ hρ hρ1
    intro ρ₁ hρ₁
    obtain ⟨ρ', R, y', h1, h2, h3, hR, hRy, hy'⟩ := hy ρ₁ hρ₁
    have hρ' : 0 < ρ' := hρ.trans_le h2
    obtain ⟨j', hj'd⟩ := hj ρ' hρ'
    obtain ⟨cD', hc1', -, hc3', -⟩ := GlobalTheory.T.closedDisc_coefficients_topologicallyFree l K bk A s ι TB ρ' hρ' h3 j' hj'd
    obtain ⟨RS, hRS⟩ := GlobalTheory.T.exists_closedDiscExtension_of_pow_dvd l bk.S bk.S (RingHom.id _) X X ρ' ρ 1 hρ (by simp) (by simpa using h2)
    refine ⟨ρ', RS, cD' i y', h1, h2, h3, hRS, ?_, (hc3' i y').trans hy'⟩

    have htor : ∀ z : bk.DS ρ, l • z = 0 → z = 0 := fun z hz => by
      rw [nsmul_eq_mul] at hz
      exact (isUnit_l_disc l (X : bk.S) ρ).mul_right_eq_zero.1 hz
    have hF : Continuous ((RS : bk.DS ρ' →+ bk.DS ρ).comp (cD' i)) :=
      AddMonoidHomClass.continuous_of_bound _ 1 fun x => by
        show ‖RS (cD' i x)‖ ≤ 1 * ‖x‖
        rw [one_mul]; exact (hRS.norm_le _).trans (hc3' i x)
    have hG : Continuous ((cD i).comp (R : Disc l (s X) ρ' →+ Disc l (s X) ρ)) :=
      AddMonoidHomClass.continuous_of_bound _ 1 fun x => by
        show ‖cD i (R x)‖ ≤ 1 * ‖x‖
        rw [one_mul]; exact (hc3 i _).trans (hR.norm_le x)
    have key := (GlobalTheory.T.closedDiscGaugeCompletion_basic_properties l A (s X) ρ').2.2.1 (bk.DS ρ) htor _ _ hF hG fun a => by
      show RS (cD' i (toDisc l (s X) ρ' a)) = cD i (R (toDisc l (s X) ρ' a))
      rw [hc1', hRS.ext, hR.ext, hc1]; rfl
    rw [← hRy]
    exact DFunLike.congr_fun key y'
  choose z hz using hz

  haveI : IsAdicComplete bk.J bk.S := bk.complete
  have hfin : ∀ n : ℕ, {i | z i ∉ bk.J ^ n}.Finite := by
    intro n
    obtain ⟨r, hr, hr'⟩ := (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk bk.S (RingHom.id _) Unit (TopBasis.self bk.J) ρ hρ hρ1).2.1 n
    refine (Filter.mem_cofinite.1 (hc4 y (Metric.closedBall_mem_nhds 0 hr))).subset fun i hi h => hi ?_
    have h' : ‖toDisc l (X : bk.S) ρ (z i)‖ ≤ r := by
      rw [hz i]; simpa using h
    have := hr' (z i) h'
    rwa [Ideal.map_id] at this
  obtain ⟨a, ha⟩ := (_root_.GlobalTheory.BSP.TopBasis.basic_facts bk.S A s bk.J ι TB bk.complete.toIsHausdorff).2.2.2.1 z hfin
  refine ⟨a, ?_⟩
  have h0 : ‖y - toDisc l (s X) ρ a‖ ≤ 0 := hc6 _ 0 le_rfl fun i => by
    rw [map_sub, hc1, ha, hz, sub_self, norm_zero]
  exact (sub_eq_zero.1 (norm_le_zero_iff.1 h0)).symm

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBcrisTensorLatticeEquivPeriodRing
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 10000000

namespace GlobalTheory.BKGal.CrisTensor

theorem mem_finiteCocycles_iff_bcrisTensor_coboundary {l : ℕ} [Fact l.Prime] {LL : FinExt l} (T : QLat LL) (Pl : LocPrime l)
    (hpow : ∀ v : T.V, ∃ n : ℕ, (l : ↥LL.1) ^ n • v ∈ T.L.T)
    (β : TW (OB l ↥(OL LL)) T ≃ₗ[↥(OL LL)] T.V ⊗[ℚ_[l]] Pl.R.B)
    (h1 : ∀ x : ↥T.L.T, β ((1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x) = (x : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.B))
    (h2 : ∀ g b, β (actB (sQ l) T g b) = actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (β b))
    (c : Gl l → T.V) (hc : c ∈ continuousCocycles T.ρ) :
    c ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ ↔ ∃ b, IsCobOf (sQ l) T b c := by
  have hl : ∀ n : ℕ, (l : ↥LL.1) ^ n ≠ 0 := fun n =>
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have key : ∀ (b : TW (OB l ↥(OL LL)) T) (g : Gl l) (n : ℕ),
      β ((l : ↥(OL LL)) ^ n • (actB (sQ l) T g b - b)) =
        (l : ↥LL.1) ^ n • (actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (β b) - β b) := by
    intro b g n
    have e1 := β.map_smul ((l : ↥(OL LL)) ^ n) (actB (sQ l) T g b - b)
    have e2 : β (actB (sQ l) T g b - b) = actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (β b) - β b :=
      (map_sub β _ _).trans (congrArg (· - β b) (h2 g b))
    have e3 : (((l : ↥(OL LL)) ^ n : ↥(OL LL)) : ↥LL.1) = (l : ↥LL.1) ^ n := by simp
    rw [← e3, ← e2]
    exact e1
  have kx : ∀ (g : Gl l) (n : ℕ) (x : ↥T.L.T), (x : T.V) = (l : ↥LL.1) ^ n • c g →
      β ((1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x) = (l : ↥LL.1) ^ n • (c g ⊗ₜ[ℚ_[l]] (1 : Pl.R.B)) := by
    intro g n x hx
    rw [h1, hx]
    exact (TensorProduct.smul_tmul' _ _ _).symm
  constructor
  · rintro ⟨-, y, hy⟩
    obtain ⟨b, rfl⟩ := β.surjective y
    refine ⟨b, fun g n x hx => β.injective ?_⟩
    exact (kx g n x hx).trans ((congrArg (fun z => (l : ↥LL.1) ^ n • z) (hy g)).trans (key b g n).symm)
  · rintro ⟨b, hb⟩
    refine ⟨hc, β b, fun g => ?_⟩
    obtain ⟨n, hn⟩ := hpow (c g)
    have h3 := (kx g n ⟨_, hn⟩ rfl).symm.trans ((congrArg β (hb g n ⟨_, hn⟩ rfl)).trans (key b g n))
    have h4 := congrArg (fun z => ((l : ↥LL.1) ^ n)⁻¹ • z) h3
    simpa only [inv_smul_smul₀ (hl n)] using h4

theorem exists_equiv : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∃ β : TW (OB l ↥(OL LL)) T ≃ₗ[↥(OL LL)] T.V ⊗[ℚ_[l]] Pl.R.B, (∀ x : ↥T.L.T, β ((1 : OB l ↥(OL LL)) ⊗ₜ[↥(OL LL)] x) = (x : T.V) ⊗ₜ[ℚ_[l]] (1 : Pl.R.B)) ∧ (∀ g b, β (actB (sQ l) T g b) = actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (β b)) ∧ (∀ b, β (TWmap (frobOB l ↥(OL LL)) T b) = φVB (LL := ↥LL.1) (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (β b)) ∧ ∀ c ∈ continuousCocycles T.ρ, (c ∈ finiteCocycles (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ ↔ ∃ b, IsCobOf (sQ l) T b c) := by
  intro l _ LL T Pl AI hS
  obtain ⟨Ti⟩ := hS
  have hz : ∀ z : ℤ_[l], Ti.eB (algebraMap ℚ_[l] Pl.R.B (z : ℚ_[l])) = algebraMap ℤ_[l] (Per.Bcris l) z :=
    fun z => (Ti.zB z).trans (GlobalTheory.RingIface.aB_zl l z).symm
  exact ⟨linEquiv T Ti.eB hz, linEquiv_one T Ti.eB hz, linEquiv_act T Ti.eB hz Ti.actB,
    linEquiv_frob T Ti.eB hz Ti.frob,
    mem_finiteCocycles_iff_bcrisTensor_coboundary T Pl (exists_pow_smul_mem T) _ (linEquiv_one T Ti.eB hz) (linEquiv_act T Ti.eB hz Ti.actB)⟩

end GlobalTheory.BKGal.CrisTensor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBetaLimitBdRPlusDeRhamFrame
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim

theorem exists_beta_limit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (N d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (F : Frame bk N d ρ), F.IsDR → ∃ B : Matrix (Fin d) (Fin d) (Per.BdRp l), ∀ m : ℕ, ∃ (k : ℕ) (β : Matrix (Fin d) (Fin d) bk.S), F.IsBeta m k β ∧ ∀ i j, aDp l (bk.ev (β i j)) - (l : Per.BdRp l) ^ k * B i j ∈ Per.FilP l m := by
  intro l _ K bk N d ρ F hF
  choose k β hβ using hF
  have mono : ∀ {m n : ℕ}, m ≤ n → ∀ {k' : ℕ} {β' : Matrix (Fin d) (Fin d) bk.S}, F.IsBeta n k' β' → F.IsBeta m k' β' :=
    fun h _ _ hb => ⟨hb.1, fun g i j => (pow_dvd_pow _ h).trans (hb.2 g i j)⟩
  obtain ⟨ζ, e, h0, -, h1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : e.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps e := ⟨he, fun hh => h1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  obtain ⟨hfil, -, hcomp, -⟩ := GlobalTheory.MemLoc.filtration_eq_xi_pow l e hE
  obtain ⟨v, hv⟩ := (isUnit_l_BdRp l).exists_left_inv
  have hvk : ∀ a : ℕ, v ^ a * (l : Per.BdRp l) ^ a = 1 := fun a => by rw [← mul_pow, hv, one_pow]
  set X : ℕ → Fin d → Fin d → Per.BdRp l := fun n i j => aDp l (bk.ev (β n i j)) with hX
  set x : ℕ → Fin d → Fin d → Per.BdRp l := fun n i j => v ^ k n * X n i j with hx
  have cauchy : ∀ m n, m ≤ n → ∀ i j, x n i j - x m i j ∈ Per.FilP l m := by
    intro m n hmn i j
    have h := _root_.GlobalTheory.BKLim.beta_unique l K bk m N d ρ F (k m) (k n) (β m) (β n) (hβ m) (mono hmn (hβ n)) i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h
    have h2 : bk.ev bk.E ^ m ∣ bk.ev ((l : bk.S) ^ k n * β m i j - (l : bk.S) ^ k m * β n i j) := by
      rw [← map_pow]; exact map_dvd bk.ev h
    have h3 := ((_root_.GlobalTheory.AinfEPow.ePow_facts l K bk m).2.2.1 _).2 h2
    simp only [map_sub, map_mul, map_pow, map_natCast] at h3
    have h4 := Ideal.mul_mem_left (Per.FilP l m) (-(v ^ k n * v ^ k m)) h3
    convert h4 using 1
    simp only [hx, hX]
    linear_combination (v ^ k m * aDp l (bk.ev (β m i j))) * hvk (k n) - (v ^ k n * aDp l (bk.ev (β n i j))) * hvk (k m)
  have hmem : ∀ (n : ℕ) (y : Per.BdRp l), y ∈ (Ideal.span {aDp l (xi e)} ^ n • ⊤ : Submodule (Per.BdRp l) (Per.BdRp l)) ↔
      y ∈ Per.FilP l n := by
    intro n y
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hfil]
  have lim : ∀ i j, ∃ L : Per.BdRp l, ∀ n, x n i j - L ∈ Per.FilP l n := by
    intro i j
    obtain ⟨L, hL⟩ := hcomp.toIsPrecomplete.prec (f := fun n => x n i j) (fun {m n} hmn => by
      rw [SModEq.sub_mem, hmem, ← neg_sub]
      exact (Per.FilP l m).neg_mem (cauchy m n hmn i j))
    exact ⟨L, fun n => (hmem n _).1 (SModEq.sub_mem.1 (hL n))⟩
  choose B hB using lim
  refine ⟨Matrix.of B, fun m => ⟨k m, β m, hβ m, fun i j => ?_⟩⟩
  have h := Ideal.mul_mem_left (Per.FilP l m) ((l : Per.BdRp l) ^ k m) (hB i j m)
  convert h using 1
  simp only [Matrix.of_apply, hx, hX]
  linear_combination (-(aDp l (bk.ev (β m i j)))) * hvk (k m)

end GlobalTheory.BKLim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinHomOfUniformizerFrame
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem BK.X_pow_eq_sub {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) :
    ∃ q : bk.S, (X : bk.S) ^ bk.Ep.natDegree = bk.E - (l : bk.S) * q := by
  have h : Polynomial.C (l : Wq l bk.a) ∣ bk.Ep - Polynomial.X ^ bk.Ep.natDegree := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro i
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    rcases lt_trichotomy i bk.Ep.natDegree with hi | rfl | hi
    · rw [if_neg hi.ne, sub_zero]; exact bk.dvd_coeff i hi
    · rw [if_pos rfl, bk.monic.coeff_natDegree, sub_self]; exact dvd_zero _
    · rw [if_neg hi.ne', sub_zero, Polynomial.coeff_eq_zero_of_natDegree_lt hi]; exact dvd_zero _
  obtain ⟨q, hq⟩ := h
  refine ⟨(q : bk.S), ?_⟩
  have := congrArg (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) hq
  simp only [map_sub, map_pow, map_mul, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X,
    Polynomial.coe_C, map_natCast] at this
  linear_combination -this

theorem isHausdorff_quot {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] (P : Obj l R) (d : P.A)
    (hd : P.I = Ideal.span {d}) : IsHausdorff ((JJ P).map (Ideal.Quotient.mk P.I)) (P.A ⧸ P.I) := by
  have hinv := P.inv
  rw [hd] at hinv
  have hnzd : d ∈ nonZeroDivisors P.A := _root_.GlobalTheory.BSP.mem_nonZeroDivisors_of_invertible_span_singleton P.A d hinv
  obtain ⟨N, hN⟩ := P.bdd
  have hbdd : ∀ (x : P.A) (m : ℕ), (l : P.A) ^ m * x ∈ Ideal.span {d} →
      (l : P.A) ^ N * x ∈ Ideal.span {d} := by
    intro x m hx
    rw [← hd, ← Ideal.Quotient.eq_zero_iff_mem] at hx ⊢
    rw [map_mul, map_pow, map_natCast] at hx ⊢
    exact hN _ ⟨m, hx⟩
  have hc := P.complete
  rw [hd] at hc
  refine ⟨fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [Ideal.Quotient.eq_zero_iff_mem, hd]
  refine GlobalTheory.T.mem_span_singleton_of_bounded_torsion_of_adic_limit l P.A d N hnzd hbdd hc x fun n => ?_
  have h1 := hy n
  simp only [SModEq.zero, smul_eq_mul, Ideal.mul_top] at h1
  rw [← Ideal.map_pow, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at h1
  obtain ⟨y, hy, hyx⟩ := h1
  rw [Ideal.Quotient.eq, hd, Ideal.mem_span_singleton'] at hyx
  obtain ⟨z, hz⟩ := hyx
  refine ⟨-z, ?_⟩
  have e : x - d * -z = y := by linear_combination hz
  rw [e]
  rw [JJ, hd] at hy
  exact hy

theorem exists_lift_coeff_zero {l : ℕ} [Fact l.Prime] {k B : Type} [CommRing k] [CharP k l] [PerfectRing k l]
    [CommRing B] (f0 : WittVector l k →+* B) (hl : f0 (l : WittVector l k) = 0) :
    ∃ ψ : k →+* B, ∀ w : WittVector l k, ψ (w.coeff 0) = f0 w := by
  have hsurj : Function.Surjective (WittVector.constantCoeff : WittVector l k →+* k) :=
    fun x => ⟨WittVector.teichmuller l x, by simp [WittVector.constantCoeff_apply]⟩
  have hker : ∀ a ∈ RingHom.ker (WittVector.constantCoeff : WittVector l k →+* k), f0 a = 0 := by
    intro a ha
    rw [WittVector.ker_constantCoeff, Ideal.mem_span_singleton'] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, hl, mul_zero]
  refine ⟨(Ideal.Quotient.lift _ f0 hker).comp (RingHom.quotientKerEquivOfSurjective hsurj).symm.toRingHom,
    fun w => ?_⟩
  have e : (RingHom.quotientKerEquivOfSurjective hsurj).symm (w.coeff 0) = Ideal.Quotient.mk _ w := by
    rw [RingEquiv.symm_apply_eq]; rfl
  show Ideal.Quotient.lift _ f0 hker ((RingHom.quotientKerEquivOfSurjective hsurj).symm (w.coeff 0)) = _
  rw [e, Ideal.Quotient.lift_mk]

theorem pow_mem_of_eq_sub {A S : Type} [CommRing A] [CommRing S] {I J : Ideal A} (hIJ : I ≤ J) {l : ℕ}
    (hl : (l : A) ∈ J) (τ : S →+* A ⧸ I) {x E q : S} {e : ℕ} {v : A} (hq : x ^ e = E - (l : S) * q)
    (hE : τ E = 0) (hx : τ x = Ideal.Quotient.mk I v) : v ^ e ∈ J := by
  have a2 := congrArg τ hq
  rw [map_pow, map_sub, map_mul, map_natCast, hx, hE] at a2
  obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective (τ q)
  have h1 : Ideal.Quotient.mk I (v ^ e + (l : A) * t) = 0 := by
    rw [map_add (f := _), map_pow, map_mul, map_natCast, ht, a2]
    ring
  have h2 := hIJ (Ideal.Quotient.eq_zero_iff_mem.1 h1)
  have h3 : (l : A) * t ∈ J := Ideal.mul_mem_right _ _ hl
  simpa using J.sub_mem h2 h3

theorem sub_mem_map_of_mk_eq {A : Type} [CommRing A] {I J : Ideal A} (hIJ : I ≤ J) (a : A) (y : A ⧸ I)
    (h : Ideal.Quotient.mk J a = Ideal.Quotient.factor hIJ y) :
    Ideal.Quotient.mk I a - y ∈ J.map (Ideal.Quotient.mk I) := by
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq] at h
  rw [← map_sub]
  exact Ideal.mem_map_of_mem _ h

theorem quot_comp_eq {W A : Type} [CommRing W] [CommRing A] {I J : Ideal A}
    (hH : IsHausdorff (J.map (Ideal.Quotient.mk I)) (A ⧸ I)) (σ : W⟦X⟧ →+* A) (τ : W⟦X⟧ →+* A ⧸ I)
    {v : A} {e : ℕ} (hve : v ^ e ∈ J) (hσX : σ X = v) (hτX : τ X = Ideal.Quotient.mk I v)
    (hC : ∀ w, Ideal.Quotient.mk I (σ (C w)) = τ (C w)) : (Ideal.Quotient.mk I).comp σ = τ := by
  refine ringHom_ext_of_sep _ _ hC ?_ ?_
  · rw [RingHom.comp_apply, hσX, hτX]
  · intro y hy
    refine hH.haus y fun n => ?_
    simp only [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    obtain ⟨c, hc⟩ := hy (e * n)
    rw [hc, RingHom.comp_apply, hσX, pow_mul, ← map_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_map_of_mem _ hve) n)

theorem mem_of_comp_eq {S A : Type} [CommRing S] [CommRing A] {I : Ideal A} (σ : S →+* A)
    (τ : S →+* A ⧸ I) (heq : (Ideal.Quotient.mk I).comp σ = τ) {E : S} (hE : τ E = 0) (a : S)
    (ha : a ∈ Ideal.span {E}) : σ a ∈ I := by
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← RingHom.comp_apply, heq, map_mul, hE, mul_zero]

theorem natCast_mem_map_quot {A : Type} [CommRing A] {I J : Ideal A} {l : ℕ} (h : (l : A) ∈ J) :
    (l : A ⧸ I) ∈ J.map (Ideal.Quotient.mk I) := by
  have := Ideal.mem_map_of_mem (Ideal.Quotient.mk I) h
  rwa [map_natCast] at this

theorem exists_hom_of_frame : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Obj l ↥(OL K)) (d v : C.A),
    IsFrame bk C d v → C.D.δ v = 0 → ∃ g : Hom bk.prism C, BK.hf (bk := bk) g X = v := by
  intro l _ K bk P d v hF hδ
  obtain ⟨hd, hv⟩ := hF
  obtain ⟨τ, hτ⟩ : ∃ τ : bk.S →+* P.A ⧸ P.I,
      τ = P.str.comp (bk.str.symm.toRingHom.comp (Ideal.Quotient.mk (Ideal.span {bk.E}))) := ⟨_, rfl⟩
  have hτX : τ X = Ideal.Quotient.mk P.I v := by rw [hτ]; exact hv.symm
  have hτE : τ bk.E = 0 := by
    rw [hτ]
    show P.str (bk.str.symm (Ideal.Quotient.mk (Ideal.span {bk.E}) bk.E)) = 0
    rw [Ideal.Quotient.mk_singleton_self, map_zero, map_zero]
  set J : Ideal P.A := JJ P with hJ
  have hIJ : P.I ≤ J := le_sup_right
  have hlJ : (l : P.A) ∈ J := Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  obtain ⟨f0, hf0⟩ : ∃ f0 : Wq l bk.a →+* P.A ⧸ J,
      f0 = ((Ideal.Quotient.factor hIJ).comp τ).comp PowerSeries.C := ⟨_, rfl⟩
  have hl0 : f0 (l : Wq l bk.a) = 0 := by
    rw [map_natCast, ← map_natCast (Ideal.Quotient.mk J) l]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hlJ
  obtain ⟨ψ, hψ⟩ := exists_lift_coeff_zero f0 hl0
  obtain ⟨ω, hω⟩ := _root_.GlobalTheory.exists_wittVector_lift_of_isAdicComplete l (Fq l bk.a) P.A J hlJ P.complete ψ
  obtain ⟨q, hq⟩ := bk.X_pow_eq_sub
  generalize bk.Ep.natDegree = e at hq
  have hve : v ^ e ∈ J := pow_mem_of_eq_sub hIJ hlJ τ hq hτE hτX
  obtain ⟨σ, hσC, hσX⟩ := _root_.GlobalTheory.PowerSeriesEval.exists_ringHom_powerSeries (Wq l bk.a) P.A J P.complete ω v _ hve
  have hσδ := _root_.GlobalTheory.sdelta_of_rank_one l bk.a P.A P.D J hlJ P.complete.toIsHausdorff σ _ (by rw [hσX]; exact hve)
    (by rw [hσX]; exact hδ)
  have hH := isHausdorff_quot P d hd
  have hlJ' := natCast_mem_map_quot (I := P.I) hlJ
  have hωC : (Ideal.Quotient.mk P.I).comp ω = τ.comp PowerSeries.C := by
    refine _root_.GlobalTheory.wittVector_ringHom_eq_of_sub_mem l (Fq l bk.a) (P.A ⧸ P.I) (J.map (Ideal.Quotient.mk P.I)) hlJ' hH _ _ ?_
    intro w
    refine sub_mem_map_of_mk_eq hIJ (ω w) (τ (PowerSeries.C w)) ((hω w).trans ((hψ w).trans ?_))
    rw [hf0]
    simp only [RingHom.comp_apply]
  have heq : (Ideal.Quotient.mk P.I).comp σ = τ :=
    quot_comp_eq hH σ τ hve hσX hτX fun w =>
      (congrArg (Ideal.Quotient.mk P.I) (hσC w)).trans (RingHom.congr_fun hωC w)
  refine ⟨{ f := σ, f_δ := fun a => hσδ a, f_I := mem_of_comp_eq σ τ heq hτE, f_str := ?_ }, hσX⟩
  intro r a h
  have h' : Ideal.Quotient.mk (Ideal.span {bk.E}) a = bk.str r := h
  have h2 := RingHom.congr_fun heq a
  rw [hτ] at h2
  refine h2.trans ?_
  show P.str (bk.str.symm (Ideal.Quotient.mk (Ideal.span {bk.E}) a)) = P.str r
  exact congrArg P.str ((congrArg bk.str.symm h').trans (bk.str.symm_apply_apply r))

end GlobalTheory.BSP
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHodgeBasisAtEmbeddingStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hodge_basis_at_embedding : ∀ (l : ℕ) [Fact l.Prime] (K L : FinExt l) (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (C : Core l), Fits T C → ∀ (ξ : Ainf l), Ideal.span {ξ} = RingHom.ker (Per.θ l) → ∀ (a : ℕ) (r : ↥(GK K) →* GL (Fin a) ↥L.1) (R : Representation ↥L.1 ↥(GK K) (Fin a → ↥L.1)), (∀ g v, R g v = (r g).val *ᵥ v) → Formalism.MainNotions.N.IsDR (P.PD K) R → ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (σ : GQ l), (∀ x : ↥K.1, σ ((τ x : ↥L.1) : Om l) = (x : Om l)) → ∃ (K' : FinExt l) (H : Hodge C ξ (fun g => (r g).val.map fun x => σ (x : Om l)) K'), K.1 ≤ K'.1 ∧ ∀ n : ℤ, ((Finset.univ.filter fun i => (H.p i : ℤ) - H.q = n).card : ℤ) = multV (P.PD K) R τ n := by
  first | (exact @GlobalTheory.HodgeAt.exists_hodge_at_embedding) | (exact GlobalTheory.HodgeAt.exists_hodge_at_embedding) | (intros; apply GlobalTheory.HodgeAt.exists_hodge_at_embedding  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisActionCyclotomicPowerStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_action_cyclotomic_power : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (g : GQ l), ∃ s : ZMod a, ∀ w : Wq l a, Per.σA g (wA l a w) = wA l a ((sigma l a ^ s.val) w) := by
  first | exact @GlobalTheory.BKReal.gal_wA_pow | exact GlobalTheory.BKReal.gal_wA_pow | (intros; apply GlobalTheory.BKReal.gal_wA_pow <;> assumption)
end

