module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepFockVectorSphericalOffS
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0780
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0804
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.StandardHermitianSpace
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockCoefficientExtremalEqDiscreteSeries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0640
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0948
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0484
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0117
public import Formalism.LocalToGlobal.IndefiniteReal.LiftGoodPartComplexEqRange

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftFockVectorsSphericalPrincipalFixed
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

noncomputable section

namespace GlobalTheory.ThPFock

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem redFn_of_mem_prin (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) {κ : GA D (Vc D i)}
    (hκ : κ ∈ prin (Vc D i) (R.βV i) (R.Pg ∪ R.Q t)) :
    κ ∈ GfC (Vc D i) ∧ finE (Vc D i) κ ∈ UA D.sp.cm (Vc D i).gram ∧ finE (Vc D i) κ ∈ St (R.βV i) ∧
      ∀ PP ∈ R.Pg ∪ R.Q t, redFn (R.βV i) PP (finE (Vc D i) κ) = 1 := by
  have h := mem_levA.1 hκ
  have hP : (prinDat (Vc D i) (R.Pg ∪ R.Q t)).P.H = ⊥ := by
    rfl
  obtain ⟨h1, h2, h3⟩ := (GlobalTheory.PrincipalLevel.mem_lev_whole _ _ _ rfl rfl hP _).1 h.2
  exact ⟨h.1, h1, h2, h3⟩

theorem is_lift_of_mem_principal_congruence (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) {κ : GA D (Vc D i)}
    (hκ : κ ∈ prin (Vc D i) (R.βV i) (R.Pg ∪ R.Q t)) : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) 1 κ := by
  obtain ⟨h0, h1, h2, h3⟩ := redFn_of_mem_prin R i t hκ
  refine ⟨h0, mem_parLev.2 ⟨h1, h2, fun PP hPP => ?_, fun PP hPP => ?_⟩, ?_⟩
  · rw [h3 PP (Finset.mem_union_left _ hPP)]
    exact Subgroup.one_mem _
  · rw [h3 PP (Finset.mem_union_right _ hPP)]
    exact Subgroup.one_mem _
  · funext PP
    show upperLeftBlock _ (redFn (R.βV i) PP.1 (finE (Vc D i) κ)) = 1
    rw [h3 PP.1 (Finset.mem_union_left _ PP.2)]
    exact blockDiagonalExtendByOnePrimeField_one _ _

theorem levChi_flag_of_mem_prin (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) {κ : GA D (Vc D i)}
    (hκ : κ ∈ prin (Vc D i) (R.βV i) (R.Pg ∪ R.Q t)) : levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ = 1 := by
  obtain ⟨-, -, -, h3⟩ := redFn_of_mem_prin R i t hκ
  have e : levFn (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) κ) = levFn (R.βV i) (flagL (R.datVt i t)) 1 := by
    have hr : rTup (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) κ) = rTup (R.βV i) (flagL (R.datVt i t)) 1 := by
      funext PP
      show upperLeftBlock _ (redFn (R.βV i) PP.1 (finE (Vc D i) κ)) = upperLeftBlock _ (redFn (R.βV i) PP.1 1)
      rw [h3 PP.1 (Finset.mem_union_left _ PP.2), redFn_one]
    unfold levFn
    rw [hr]
    congr 1
    · congr 1
      exact Finset.prod_congr rfl fun PP hPP => Finset.prod_congr rfl fun c _ => by
        rw [h3 PP (Finset.mem_union_left _ hPP), redFn_one]
    · exact Finset.prod_congr rfl fun PP hPP => by
        rw [h3 PP (Finset.mem_union_right _ hPP), redFn_one]
  have h1 := GlobalTheory.RawLift.LevelFix.levChi_flag_one R i t
  unfold levChi at h1 ⊢
  rw [e]
  rw [(finE (Vc D i)).map_one] at h1
  exact h1

theorem is_lift_one_principal_level (R : RealDat D A Ks) (i : Fin D.R.m) : IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) 1 1 :=
  ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _, by rw [map_one]; exact rTup_one⟩

end GlobalTheory.ThPFock


open GlobalTheory.ThPFock in
theorem GlobalTheory.ThPFock.fock_sph_prin : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t P, (∀ τ, IsCartanInv (gramAt D (Wc D i) τ) (cart (R.MW i (sg0 D A)) τ)) ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ptP i t P) ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsSphOff R.ψ (Vc D i) (Wc D i) (GlobalTheory.AdelicU.frameLat (Vc D i)) (GlobalTheory.AdelicU.frameLat (Wc D i)) (under (R.Pg ∪ R.Q t)) (R.ptP i t P) ∧ ∀ κ ∈ prin (Vc D i) (R.βV i) (R.Pg ∪ R.Q t), R.ωP i t (κ, 1) (R.ptP i t P) = R.ptP i t P := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t P
  have hC := hG.core
  have hθ : IsInfFam R.θ := hC.models.inf
  have hψ : IsStdChar D R.ψ (-1) := (hC.thP.ωP i t).std
  have cS : ∀ τ, IsCartanInv (gramAt D (Vc D i) τ) 1 := fun τ => GlobalTheory.RawLift.isCartanInv_one_of_onb (hC.models.BV i τ)
  have cT : ∀ τ, IsCartanInv (gramAt D (Wc D i) τ) (cart (R.MW i (sg0 D A)) τ) :=
    fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart (R.MW i (sg0 D A)) τ
  have hpt : ∀ φ, IsThetaFunO R.ψ (Vc D i) (Wc D i) (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1)
      (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) (R.vP i t) φ) := hC.thP.pt_theta i t
  have hvθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hC.thP.pt_theta i t 1
    unfold RealDat.ptP pureTensorO at this
    rwa [GlobalTheory.AdTh.VecFock.pureTensorL_one] at this
  have hvv : ∀ τ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i (sg0 D A)) τ)) (R.vP i t) :=
    GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ (fun _ => 1) _ _ _ _ _ _ _ _ _ _ (hC.thP.vP i t) hvθ
  refine ⟨cT, ?_, ?_, ?_⟩
  · exact GlobalTheory.FockSph.isFockVec_pureTensorO hψ hθ cS cT (R.BV i) (onb (R.MW i (sg0 D A))) hvθ hvv P
  · obtain ⟨hvac, e, he, hth⟩ := hC.thP.vP i t
    have hV : (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) = (GlobalTheory.AdelicU.frameLat (Vc D i) : Set _) := by
      rw [GlobalTheory.IndefiniteRowSideFullHecke.StandardHermitianSpace.baseLat_eq hC.lev i, GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]
    have hW : (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) = (GlobalTheory.AdelicU.frameLat (Wc D i) : Set _) := by
      rw [← GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]
      obtain ⟨c, -, -, -, h1, h2⟩ := hC.lev.βW i
      ext x
      constructor
      · intro hx
        simpa using h2 x hx
      · intro hx
        simpa using h1 x hx
    have hle : latO (Vc D i) (Wc D i) (GlobalTheory.AdelicU.frameLat (Vc D i) : Set _) (GlobalTheory.AdelicU.frameLat (Wc D i) : Set _)
        (fun v => v ∉ under (R.Pg ∪ R.Q t)) ≤ latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True := by
      rw [hV, hW]
      exact GlobalTheory.PlaceTensor.latO_mono fun _ _ => trivial
    have hz : ∀ u ∈ latO (Vc D i) (Wc D i) (GlobalTheory.AdelicU.frameLat (Vc D i) : Set _) (GlobalTheory.AdelicU.frameLat (Wc D i) : Set _)
        (fun v => v ∉ under (R.Pg ∪ R.Q t)), ∀ a b, cA D (cA D e) * u a b = 0 ∧ cA D e * u a b = 0 := by
      intro u hu a b
      obtain ⟨h1, h2⟩ := GlobalTheory.FockSph.idemSum_mul_of (P := fun v => v ∉ under (R.Pg ∪ R.Q t)) he
        (fun PP hPP hn => hn (Finset.mem_image_of_mem _ hPP)) hu a b
      rw [Formalism.L2.Theta.cA_cA]
      exact ⟨h1, h2⟩
    have hlat := hvac.2.lat
    have fix : ∀ u ∈ latO (Vc D i) (Wc D i) (GlobalTheory.AdelicU.frameLat (Vc D i) : Set _) (GlobalTheory.AdelicU.frameLat (Wc D i) : Set _)
        (fun v => v ∉ under (R.Pg ∪ R.Q t)), heisO R.ψ (Vc D i) (Wc D i) u (R.vacP i) = R.vacP i →
        heisO R.ψ (Vc D i) (Wc D i) u (R.ptP i t P) = R.ptP i t P := fun u hu h0 =>
      GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) hθ (fun _ => 1) (cart (R.MW i (sg0 D A)))
        (R.BV i) (onb (R.MW i (sg0 D A))) (R.vP i t) hpt u (GlobalTheory.VacGood.infPart_latO (hle hu))
        (GlobalTheory.Hk3.heisO_fix_thetaAt_off R.ψ (Vc D i) (Wc D i) (cA D e) _ 1 (R.vacP i) _ (R.vP i t) hth u
          (fun a b => ⟨(hz u hu a b).2, (hz u hu a b).1⟩) h0) P
    exact ⟨fun u hu => fix (2 • u) (AddSubgroup.nsmul_mem _ hu 2) (hlat.1 u (hle hu)),
      fun e' he' u hu hh => fix u hu (hlat.2 e' he' u (hle hu) hh)⟩
  · intro κ hκ
    have hl := is_lift_of_mem_principal_congruence R i t hκ
    have hv : R.ωP i t (κ, 1) (R.vP i t) = (1 : ℂ) • R.vP i t := by
      rw [_root_.GlobalTheory.VecInv.omega_lifts_vP R hC.lev hC.models.inf hC.thP.ωP hC.thP.vP i t 1 κ 1 hl (is_lift_one_principal_level R i),
        levChi_flag_of_mem_prin R i t hκ, inv_one]
    have := GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i t) hθ
      (hC.thP.ωP i t) _ _ _ _ _ hpt κ hl.1 1 (Subgroup.one_mem _) 1 hv P
    exact this.trans (one_smul ℂ _)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftPairingLowestWeightSchurPolarisation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

namespace GlobalTheory.CoefSchur

theorem sesq_eq_of_diag {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F G : E →ₗ[ℂ] E →ₗ⋆[ℂ] ℂ) (h : ∀ x, F x x = G x x) : F = G := by
  have h0 : ∀ x, (F - G) x x = 0 := fun x => by simp [h x]
  suffices hD : ∀ x y, (F - G) x y = 0 by
    ext x y
    have := hD x y
    simpa [sub_eq_zero] using this
  intro x y
  have h1 := h0 (x + y)
  have h2 := h0 (x + Complex.I • y)
  simp only [map_add (f := _), LinearMap.add_apply, LinearMap.map_smulₛₗ,
    LinearMap.smul_apply, smul_eq_mul, h0, Complex.conj_I, mul_zero, add_zero, zero_add] at h1 h2
  have hI := Complex.I_sq
  linear_combination (-(Complex.I) / 2 * Complex.I) * h1 + (Complex.I / 2) * h2 + ((F - G) x y) * hI

theorem schur_sesq {G : Type*} [Group G] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [Nontrivial E] (ρ : G →* Module.End ℂ E)
    (hu : ∀ h x y, ⟪ρ h x, ρ h y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hirr : ∀ U : Submodule ℂ E, (∀ h, Submodule.map (ρ h) U ≤ U) → U = ⊥ ∨ U = ⊤)
    (B : E →ₗ[ℂ] E →ₗ⋆[ℂ] ℂ) (hB : ∀ h x y, B (ρ h x) (ρ h y) = B x y) :
    ∃ c : ℂ, ∀ x y, B x y = c * ⟪y, x⟫_ℂ := by
  classical
  let b := stdOrthonormalBasis ℂ E
  let A : E →ₗ[ℂ] E := ∑ i, (B.flip (b i)).smulRight (b i)
  have hA : ∀ x y, B x y = ⟪y, A x⟫_ℂ := by
    intro x y
    conv_lhs => rw [← b.sum_repr' y]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [A, map_sum, inner_sum, inner_smul_right, inner_conj_symm, mul_comm]
  have hcomm : ∀ h x, A (ρ h x) = ρ h (A x) := by
    intro h x
    apply ext_inner_left ℂ
    intro y
    have hy : ρ h (ρ h⁻¹ y) = y := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    calc ⟪y, A (ρ h x)⟫_ℂ = B (ρ h x) y := (hA _ _).symm
      _ = B (ρ h x) (ρ h (ρ h⁻¹ y)) := by rw [hy]
      _ = B x (ρ h⁻¹ y) := hB _ _ _
      _ = ⟪ρ h⁻¹ y, A x⟫_ℂ := hA _ _
      _ = ⟪ρ h (ρ h⁻¹ y), ρ h (A x)⟫_ℂ := (hu _ _ _).symm
      _ = ⟪y, ρ h (A x)⟫_ℂ := by rw [hy]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue A
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hinv : ∀ h, Submodule.map (ρ h) (Module.End.eigenspace A c) ≤ Module.End.eigenspace A c := by
    rintro h _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hx
    rw [Module.End.mem_eigenspace_iff, hcomm, hx, map_smul]
  have htop : Module.End.eigenspace A c = ⊤ := by
    rcases hirr _ hinv with h | h
    · exfalso
      have hmem : v ∈ Module.End.eigenspace A c := Module.End.mem_eigenspace_iff.mpr hv.apply_eq_smul
      rw [h, Submodule.mem_bot] at hmem
      exact hv.2 hmem
    · exact h
  refine ⟨c, fun x y => ?_⟩
  have hx : x ∈ Module.End.eigenspace A c := htop ▸ Submodule.mem_top
  rw [Module.End.mem_eigenspace_iff] at hx
  rw [hA, hx, inner_smul_right]

end GlobalTheory.CoefSchur

namespace GlobalTheory.CoefSchur

section
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {μ : Measure (WO S T)} {𝓧 : Set (WO S T)}

theorem integrable_mul_conj (hW : IsWeilDatumO ψ S T χS χT om) (hC : IsCovolOne (ratL T S) μ 𝓧)
    {a b : WO S T → ℂ} (ha : IsThetaFunO ψ S T a) (hb : IsThetaFunO ψ S T b) :
    Integrable (fun x => a x * (starRingEnd ℂ) (b x)) (μ.restrict 𝓧) := by
  refine (GlobalTheory.RawLift.FockCoef.integrable_pair hW hC hb ha).congr
    (Filter.Eventually.of_forall fun x => ?_)
  show star (b x) * a x = a x * (starRingEnd ℂ) (b x)
  rw [starRingEnd_apply, mul_comm]

theorem thetaFunctionPairing_weilAction_invariant (hW : IsWeilDatumO ψ S T χS χT om) (hC : IsCovolOne (ratL T S) μ 𝓧)
    (p : GA D S × GA D T) {a b : WO S T → ℂ} (ha : IsThetaFunO ψ S T a)
    (hb : IsThetaFunO ψ S T b) : l2 μ 𝓧 (om p a) (om p b) = l2 μ 𝓧 a b := by
  have key : ∀ f g : WO S T → ℂ, l2 μ 𝓧 f g = GlobalTheory.RawLift.thetaIP μ 𝓧 g f := by
    intro f g
    simp only [l2, Lift.pet, GlobalTheory.RawLift.thetaIP]
    congr 1
    funext x
    rw [starRingEnd_apply, mul_comm]
  rw [key, key, GlobalTheory.WeilPairing.thetaInner_weilRep D ψ S T χS χT om μ 𝓧 hW hC p b a hb ha]

noncomputable def thetaForm (hW : IsWeilDatumO ψ S T χS χT om) (hC : IsCovolOne (ratL T S) μ 𝓧)
    {E : Type*} [AddCommGroup E] [Module ℂ E] (a b : E →ₗ[ℂ] (WO S T → ℂ))
    (ha : ∀ x, IsThetaFunO ψ S T (a x)) (hb : ∀ y, IsThetaFunO ψ S T (b y)) :
    E →ₗ[ℂ] E →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => l2 μ 𝓧 (a x) (b y))
    (fun x x' y => by
      simp only [map_add (f := _), l2, Lift.pet, Pi.add_apply, add_mul]
      exact integral_add (integrable_mul_conj hW hC (ha x) (hb y))
        (integrable_mul_conj hW hC (ha x') (hb y)))
    (fun c x y => by
      simp only [map_smul, l2, Lift.pet, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
      exact integral_const_mul c _)
    (fun x y y' => by
      simp only [map_add (f := _), l2, Lift.pet, Pi.add_apply, mul_add]
      exact integral_add (integrable_mul_conj hW hC (ha x) (hb y))
        (integrable_mul_conj hW hC (ha x) (hb y')))
    (fun c x y => by
      simp only [map_smul, l2, Lift.pet, Pi.smul_apply, smul_eq_mul, map_mul]
      rw [← integral_const_mul]
      congr 1
      funext z
      ring)

theorem thetaForm_apply (hW : IsWeilDatumO ψ S T χS χT om) (hC : IsCovolOne (ratL T S) μ 𝓧)
    {E : Type*} [AddCommGroup E] [Module ℂ E] (a b : E →ₗ[ℂ] (WO S T → ℂ))
    (ha : ∀ x, IsThetaFunO ψ S T (a x)) (hb : ∀ y, IsThetaFunO ψ S T (b y)) (x y : E) :
    thetaForm hW hC a b ha hb x y = l2 μ 𝓧 (a x) (b y) := rfl

end

end GlobalTheory.CoefSchur

namespace GlobalTheory.CoefSchur

theorem realElt_one {D : D7} (θ : InfFam D) (hθ : IsInfFam θ) (T : HSp D) :
    realElt θ T 1 = 1 := by
  classical
  obtain ⟨L, -, hL2, -, -, -, hLat, -, -⟩ := GlobalTheory.RealLift.exists_real_lift D θ T hθ
  have h1UH : ∀ τ, (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ) ∈ Formalism.QuantumDeterminants.UH (gramAt D T τ) := by
    intro τ; simp [Formalism.QuantumDeterminants.UH]
  have h1UG : (1 : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) ∈ GlobalTheory.HolDict.UG (gramAt D T) :=
    fun τ => h1UH τ
  have hL1 : L 1 = 1 := by
    have := hL2 1 h1UG 1 h1UG
    rw [mul_one] at this
    exact mul_left_cancel (a := L 1) (by rw [mul_one]; exact this.symm)
  have hat : ∀ τ, atTau θ T τ 1 = 1 := by
    intro τ; rw [hLat τ 1 (h1UH τ), Pi.mulSingle_one, hL1]
  simp [realElt, hat]

theorem thetaLiftPairing_lowestWeight_schur_polarisation_alt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ (Sp : D.what₂.Tau → SPar) (M : DSModel T Sp), ∀ (μ : Measure (WO S T)) (𝓧 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓧 → ∀ c : CoefA S, c.Is → ∀ pt : PolF D T.rank S.rank →ₗ[ℂ] (WO S T → ℂ), (∀ P, IsThetaFunO ψ S T (pt P)) → ∀ (Δ : PolF D T.rank S.rank) (io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D T.rank S.rank), IsIoW θ M c om (fun P => pt P) Δ io → (∀ w : c.W, ∃ N : ℂ, ∀ g : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ, (∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D T ρ)) → ∀ (e e' : ∀ ρ, lowT M ρ), l2 μ 𝓧 (om (1, realElt θ T g) (pt (io (PiTensorProduct.tprod ℂ e) w))) (pt (io (PiTensorProduct.tprod ℂ e') w)) = N * (∏ ρ, ⟪((e' ρ : M.sm ρ) : M.H ρ), M.rep ρ (g ρ) ((e ρ : M.sm ρ) : M.H ρ)⟫_ℂ)) → ∀ g : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ, (∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D T ρ)) → ∀ (e e' : ∀ ρ, lowT M ρ) (w w' : c.W), l2 μ 𝓧 (om (1, realElt θ T g) (pt (io (PiTensorProduct.tprod ℂ e) w))) (pt (io (PiTensorProduct.tprod ℂ e') w')) = l2 μ 𝓧 (pt Δ) (pt Δ) * (∏ ρ, ⟪((e' ρ : M.sm ρ) : M.H ρ), M.rep ρ (g ρ) ((e ρ : M.sm ρ) : M.H ρ)⟫_ℂ) * ⟪w', w⟫_ℂ := by
  intro D ψ θ S T χS χT om hθ hW Sp M μ 𝓧 hC c hc pt hpt Δ io hio hN g hg e e' w w'
  obtain ⟨hio1, -, v₀, w₀, hv₀, hw₀, hΔ⟩ := hio
  haveI : Nontrivial c.W := hc.2.2.2.1
  have hr1 := realElt_one θ hθ T
  have hom1 : om (1, realElt θ T 1) = 1 := by rw [hr1]; exact map_one om
  have hth : ∀ p P, IsThetaFunO ψ S T (om p (pt P)) := fun p P => hW.om_pres p _ (hpt P)
  let b₀ : c.W →ₗ[ℂ] (WO S T → ℂ) := pt.comp (io (PiTensorProduct.tprod ℂ v₀))
  let B := thetaForm hW hC b₀ b₀ (fun _ => hpt _) (fun _ => hpt _)
  have hBinf : ∀ u ∈ GinfC S, ∀ x y, B (c.ρ u x) (c.ρ u y) = B x y := by
    intro u hu x y
    have hio1' : ∀ (x : LowT M) (w : c.W), om (u, 1) (pt (io x w)) = pt (io x (c.ρ u w)) := hio1 u hu
    simp only [B, thetaForm_apply, b₀, LinearMap.comp_apply]
    rw [← hio1', ← hio1']
    exact thetaFunctionPairing_weilAction_invariant hW hC _ (hpt _) (hpt _)
  have hBinv : ∀ h x y, B (c.ρ h x) (c.ρ h y) = B x y := by
    intro h x y
    obtain ⟨L, -, -, -, -, -, -, hdec, -⟩ := GlobalTheory.RealLift.exists_real_lift D θ S hθ
    obtain ⟨a, ha, u, hu, rfl⟩ := hdec h
    rw [map_mul, Module.End.mul_apply, Module.End.mul_apply, hc.1 a ha, Module.End.one_apply,
      Module.End.one_apply]
    exact hBinf u hu x y
  obtain ⟨lam, hlam⟩ := schur_sesq c.ρ hc.2.1 hc.2.2.2.2 B hBinv
  have hlam0 : lam = l2 μ 𝓧 (pt Δ) (pt Δ) := by
    have := hlam w₀ w₀
    simp only [B, thetaForm_apply, b₀, LinearMap.comp_apply, hΔ] at this
    rw [this, inner_self_eq_norm_sq_to_K, hw₀]; simp
  have hP0 : ∏ ρ, ⟪((v₀ ρ : M.sm ρ) : M.H ρ), M.rep ρ ((1 : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) ρ) ((v₀ ρ : M.sm ρ) : M.H ρ)⟫_ℂ = 1 := by
    apply Finset.prod_eq_one
    intro ρ _
    have hfr : M.fr ρ * (1 : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) ρ * (M.fr ρ)⁻¹ = 1 := by
      rw [Pi.one_apply, mul_one]
      exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit ρ))
    have hσ : M.σ ρ 1 = 1 := (M.ds ρ).2.2.1.1.1
    rw [DSModel.rep, hfr, hσ, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K, hv₀ ρ]; simp
  have h1mem : ∀ ρ, (1 : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D T ρ) := by
    intro ρ; simp [Formalism.QuantumDeterminants.UH]
  have hdiag : ∀ x : c.W, ∀ g : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ,
      (∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D T ρ)) → ∀ e e' : ∀ ρ, lowT M ρ,
      l2 μ 𝓧 (om (1, realElt θ T g) (pt (io (PiTensorProduct.tprod ℂ e) x)))
        (pt (io (PiTensorProduct.tprod ℂ e') x)) = l2 μ 𝓧 (pt Δ) (pt Δ) *
        (∏ ρ, ⟪((e' ρ : M.sm ρ) : M.H ρ), M.rep ρ (g ρ) ((e ρ : M.sm ρ) : M.H ρ)⟫_ℂ) * ⟪x, x⟫_ℂ := by
    intro x g hg e e'
    obtain ⟨N, hNx⟩ := hN x
    have h1 := hNx 1 h1mem v₀ v₀
    rw [hP0, mul_one, hom1, Module.End.one_apply] at h1
    have hBx : B x x = N := h1
    rw [hlam, hlam0] at hBx
    rw [hNx g hg e e', ← hBx]; ring
  let F : c.W →ₗ[ℂ] c.W →ₗ⋆[ℂ] ℂ := thetaForm hW hC
    ((om (1, realElt θ T g)).comp (pt.comp (io (PiTensorProduct.tprod ℂ e))))
    (pt.comp (io (PiTensorProduct.tprod ℂ e'))) (fun _ => hth _ _) (fun _ => hpt _)
  let G : c.W →ₗ[ℂ] c.W →ₗ⋆[ℂ] ℂ := (l2 μ 𝓧 (pt Δ) (pt Δ) *
    ∏ ρ, ⟪((e' ρ : M.sm ρ) : M.H ρ), M.rep ρ (g ρ) ((e ρ : M.sm ρ) : M.H ρ)⟫_ℂ) • (innerₛₗ ℂ).flip
  have hFG := sesq_eq_of_diag F G (fun x => by
    simp only [F, G, thetaForm_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.flip_apply, smul_eq_mul]
    exact hdiag x g hg e e')
  have := LinearMap.congr_fun₂ hFG w w'
  simp only [F, G, thetaForm_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.flip_apply, smul_eq_mul] at this
  exact this

end GlobalTheory.CoefSchur
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopVectorMemExtraProjection
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopLevelP

theorem toMap_shift {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) {Dm : Type} [AddCommGroup Dm] [Module ℂ Dm]
    (pr : c.W →ₗ[ℂ] Dm →ₗ[ℂ] ℂ) (κ : GA D V) (hκ : κ ∈ GfC V) (a : ℂ) (ha : a ≠ 0)
    (f f' : Bridge.Gf V → c.W) (hy : ∀ h, f' h = a⁻¹ • f (h * (finHom V).rangeRestrict κ)) (v : Dm) (h : GA D V) :
    c.toMap pr f' v h = a⁻¹ * c.toMap pr f v (h * κ) := by
  have h1 := GlobalTheory.ThetaProjEquiv.ext_shift c hc κ hκ a ha f f' hy h
  show pr (c.ext f' h) v = a⁻¹ * pr (c.ext f (h * κ)) v
  rw [← h1, map_smul, Pi.smul_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel_left₀ ha]

theorem toMap_eigen {D : D7} {V : HSp D} (c : CoefA V) (hc : c.Is) {Dm : Type} [AddCommGroup Dm] [Module ℂ Dm]
    (pr : c.W →ₗ[ℂ] Dm →ₗ[ℂ] ℂ) (κ : GA D V) (hκ : κ ∈ GfC V) (a : ℂ) (ha : a ≠ 0) (b : ℂ)
    (f : Bridge.Gf V → c.W) (hy : ∀ h, (b • f) h = a⁻¹ • f (h * (finHom V).rangeRestrict κ)) (v : Dm) (h : GA D V) :
    a⁻¹ * c.toMap pr f v (h * κ) = b * c.toMap pr f v h :=
  (toMap_shift c hc pr κ hκ a ha f (b • f) hy v h).symm.trans
    (congrFun (LinearMap.congr_fun ((c.toMap pr).map_smul b f) v) h)

theorem mem_multT_withP {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S)
    (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (P : LevelP L.Pg L.r ℂ) (u : SmT M →ₗ[ℂ] (GA D V → ℂ))
    (hu : u ∈ MultT θ M (levS V β (flag1L L)) (levChi V β (flag1L L)))
    (hP : ∀ p : P.H, ∃ κ, IsLevelLift V β L p.1 κ ∧ ∀ v h,
      (levChi V β (flagL L) κ)⁻¹ * u v (h * κ) = ((P.chi p : ℂˣ) : ℂ) * u v h) :
    u ∈ MultT θ M (levS V β (withP L P)) (levChi V β (withP L P)) := by
  have hm := (GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 ((mem_multT _ _ _ _ _).1 hu)
  rw [mem_multT, GlobalTheory.MultMem.mem_mult_iff]
  refine ⟨hm.aut, hm.cusp, fun v k hk g => ?_, hm.equiv, hm.cont⟩
  have hT : HasType V β (flag1L L) (PiTensorProduct.lift.symm u v) := fun k hk g => hm.lev v k hk g
  refine IsPLevel.hasType (V := V) (β := β) (L := L) (P := P) ⟨hT, fun p => ?_⟩ k hk g
  obtain ⟨κ, hl, hκ⟩ := hP p
  funext h
  exact (level_action_spec hT ⟨κ, hl⟩ κ hl h).trans (hκ (PiTensorProduct.tprod ℂ v) h)

section Package

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem exists_lift_eigen (hred : R.grp_red_R) (hj : R.models_jX) (hc : R.models_cX) (t : T0) (g : G)
    (x : (A.fam.R t).S.Forms) (a : D.what₂.LL) (hx : (A.fam.R t).r g x = a • x) :
    ∃ κ, IsLevelLift D.sp.X' R.βX (R.datXt t) (R.eG g) κ ∧ ∀ v h,
      (levChi D.sp.X' R.βX (flagL (R.datXt t)) κ)⁻¹ * R.cX.toMap R.prX ((R.HX t).e (R.jX t x)) v (h * κ) =
        D.what₂.embLL a * R.cX.toMap R.prX ((R.HX t).e (R.jX t x)) v h := by
  refine (GlobalTheory.FormAction.act_eq_translate R hred hj t g x).imp fun κ hκ => ⟨hκ.1, ?_⟩
  have h3 : R.jX t ((A.fam.R t).r g x) = D.what₂.embLL a • R.jX t x :=
    (congrArg (R.jX t) hx).trans ((R.jX t).map_smulₛₗ a x)
  have h4 : (R.HX t).e (R.jX t ((A.fam.R t).r g x)) = D.what₂.embLL a • (R.HX t).e (R.jX t x) :=
    (congrArg (R.HX t).e h3).trans ((R.HX t).e.map_smul _ _)
  exact toMap_eigen R.cX hc R.prX κ hκ.1.1 _ (levChi_ne_zero (V := D.sp.X') (β := R.βX) (flagL (R.datXt t)) κ) _ _
    fun h => (congrFun h4 h).symm.trans (hκ.2 h)

theorem mem_CXP_of_good (hred : R.grp_red_R) (hj : R.models_jX) (hc : R.models_cX) (hirr : ∀ χ ∈ A.fam.X, IsAbsIrrChar χ)
    (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (t : T0) (x : (A.fam.R t).S.Forms)
    (hx : x ∈ Formalism.IndefR.Cx.BlockGood.goodR (A.fam.R t) (A.fam.lvl P ψ))
    (hu : R.cX.toMap R.prX ((R.HX t).e (R.jX t x)) ∈
      MultT R.θ R.MX (levS _ R.βX (R.datXt t)) (levChi _ R.βX (R.datXt t))) :
    R.cX.toMap R.prX ((R.HX t).e (R.jX t x)) ∈ CXP R (levPOf R.eG D.what₂.embLL P ψ) t := by
  rw [Formalism.IndefR.CxPass.LevelOperators.goodR_eq] at hx
  refine mem_multT_withP R.θ R.MX R.βX (R.datXt t) (levPOf R.eG D.what₂.embLL P ψ) _ hu fun p => ?_
  have hq : R.eG.symm p.1 ∈ P := p.2
  have ha := Formalism.IndefR.CxPass.LevelOperators.opF_goodAt_type (A.fam.R t).r A.fam.X hirr P ψ ⟨_, hq⟩ x hx
  refine (exists_lift_eigen R hred hj hc t (R.eG.symm p.1) x _ ha).imp fun κ hκ => ⟨?_, hκ.2⟩
  exact ⟨hκ.1.1, hκ.1.2.1, hκ.1.2.2.trans (R.eG.apply_symm_apply p.1)⟩

end Package

end GlobalTheory.TopLevelP

end
end

