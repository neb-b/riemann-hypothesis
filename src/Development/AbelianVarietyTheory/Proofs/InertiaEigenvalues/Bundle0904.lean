module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0894
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0832
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0899
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0800
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0793
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0897
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0878
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0885
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0898
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilRepresentationEtaleOfQuadraticField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleOrbitalFourierRankOneTransfer
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0611
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergGLnGLmUnfoldingToMirabolic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0857
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0828
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0895

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharacterisationTransferMovedReadings
section
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
  IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.Unframe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def rhoEquiv {K M G : Type} [Field K] [AddCommGroup M] [Module K M] [Group G] (ρ : G →* (M →ₗ[K] M)) (g : G) : M ≃ₗ[K] M :=
  LinearEquiv.ofLinearMap (ρ g) (ρ g⁻¹) (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)

theorem rho_rho {K M G : Type} [Field K] [AddCommGroup M] [Module K M] [Group G] (ρ : G →* (M →ₗ[K] M)) (g g' : G) (x : M) :
    ρ g (ρ g' x) = ρ (g * g') x := by rw [map_mul]; rfl

theorem rho_inv {K M G : Type} [Field K] [AddCommGroup M] [Module K M] [Group G] (ρ : G →* (M →ₗ[K] M)) (g : G) (x : M) :
    ρ g (ρ g⁻¹ x) = x := by rw [rho_rho, mul_inv_cancel, map_one]; rfl

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (Rl : RealDat3 D A3 Ks) (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → Γ)

abbrev realDatMovedReadingsKeepScalars : RealDat3 D A3 Ks := ⟨moveR Rl.toRealDat w, Rl.plI, Rl.SF, Rl.phs, Rl.lam3⟩

variable (kap : ℝ) (lam : type_of% Rl.lam3)

abbrev fullHeckeRealDatMovedReadings : RealDat3 D A3 Ks := (realDatMovedReadingsKeepScalars Rl w).updS kap lam

variable {Rl w kap lam}


set_option maxHeartbeats 4000000 in
theorem heckeCharacterisation_transfer_movedReadings {F : Face3 D A3} (h : Rl.Char3 F) (hs : (fullHeckeRealDatMovedReadings Rl w kap lam).IsScal F) : (fullHeckeRealDatMovedReadings Rl w kap lam).Char3 F := by
  obtain ⟨h1, h2, h5, hi, h6, h7, h8, f1, f2, f3, -, ht, hp, ha⟩ := h
  refine ⟨h1, ⟨h2.1, h2.2, h2.3, h2.4, h2.5⟩, ?_, ⟨hi.1, hi.2, hi.3, hi.4, hi.5⟩, ?_, ?_, ?_, f1, f2, f3, hs,
    ⟨ht.1, ht.2, ht.3, ht.4, ht.5⟩, fun i => ⟨(hp i).1, fun hc x => ?_⟩, ha⟩
  · exact ⟨h5.1, h5.2, h5.3, h5.4, h5.5, h5.6, h5.7, h5.8⟩
  · exact ⟨h6.1, h6.2, h6.3, h6.4, h6.5, h6.6, h6.7, h6.8, h6.9, h6.10, h6.11, h6.12, h6.13, h6.14, h6.15, h6.16, h6.17,
      h6.18, h6.19, h6.20, h6.21⟩
  · exact ⟨h7.1, h7.2, h7.3, h7.4, h7.5, h7.6, h7.7, h7.8, h7.9, h7.10, h7.11⟩
  · exact ⟨h8.1, h8.2, h8.3, h8.4, h8.5, h8.6, h8.7⟩
  · obtain ⟨c, hc1, hc2⟩ := hc
    obtain ⟨y, hy⟩ := (hp i).2 ⟨c, hc1, fun x => (hc2 x).elim fun y hy => ⟨(Rl.FW i).ρ (w i (sg0 D A3.A)) y, hy⟩⟩ x
    exact ⟨(Rl.FW i).ρ (w i (sg0 D A3.A))⁻¹ y, (congrArg ((Rl.FW i).j (sg0 D A3.A)) (rho_inv _ _ y)).trans hy⟩

variable {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) (w)

abbrev moveS : NX.RatDat D.ntw :=
  { S with
    A := fun n => moveForms (S.A n) fun σ =>
      (YS.fi (NX.idxOf D n)).eG.symm (w (NX.idxOf D n) σ * (w (NX.idxOf D n) (sg0 D A3.A))⁻¹) }

variable {w} (kap lam) (hw : ∀ i σ, w i σ ∈ Subgroup.center Γ) (hst : ∀ i, (Rl.FW i).MKStable)

def moveIso (i : Fin D.R.m) : NX.FormsIso ((moveS w YS).A ((i : ℕ) + 1)) ((fullHeckeRealDatMovedReadings Rl w kap lam).FW i) where
  eK := (YS.fi i).eK
  eK_LL := (YS.fi i).eK_LL
  e := (YS.fi i).e.trans (rhoEquiv (Rl.FW i).ρ (w i (sg0 D A3.A))⁻¹)
  eG := (YS.fi i).eG
  eW := (YS.fi i).eW
  wk x := ((YS.fi i).wk x).trans ⟨(hst i _ _).1, fun h => by
    rw [← rho_inv (Rl.FW i).ρ (w i (sg0 D A3.A)) ((YS.fi i).e x)]
    exact (hst i _ _).1 h⟩
  mkK x := ((YS.fi i).mkK x).trans ⟨(hst i _ _).2, fun h => by
    rw [← rho_inv (Rl.FW i).ρ (w i (sg0 D A3.A)) ((YS.fi i).e x)]
    exact (hst i _ _).2 h⟩
  rho g x := by
    change (Rl.FW i).ρ (w i (sg0 D A3.A))⁻¹ ((YS.fi i).e ((S.A _).ρ g x)) =
      (Rl.FW i).ρ ((YS.fi i).eG g) ((Rl.FW i).ρ (w i (sg0 D A3.A))⁻¹ ((YS.fi i).e x))
    rw [(YS.fi i).rho, rho_rho, rho_rho, Subgroup.mem_center_iff.1 (inv_mem (hw i _))]
  chi := (YS.fi i).chi
  j σ x := by
    change (Rl.FW i).j σ ((Rl.FW i).ρ (w i σ) ((Rl.FW i).ρ (w i (sg0 D A3.A))⁻¹ ((YS.fi i).e x))) =
      (YS.fi i).eW σ ((S.A _).j σ ((S.A _).ρ ((YS.fi (NX.idxOf D ((i : ℕ) + 1))).eG.symm
        (w (NX.idxOf D ((i : ℕ) + 1)) σ * (w (NX.idxOf D ((i : ℕ) + 1)) (sg0 D A3.A))⁻¹)) x))
    rw [NX.idxOf_succ, ← (YS.fi i).j, (YS.fi i).rho, MulEquiv.apply_symm_apply, rho_rho]

def moveYS : NX.NExpRealS (fullHeckeRealDatMovedReadings Rl w kap lam) cG (moveS w YS) where
  fi := moveIso kap lam YS hw hst
  geq := YS.geq
  rho := YS.rho
  chi := YS.chi
  eF := YS.eF
  bsup := YS.bsup
  act := YS.act

theorem j_moveYS (i : Fin D.R.m) (x : S.WL ((i : ℕ) + 1)) :
    ((fullHeckeRealDatMovedReadings Rl w kap lam).FW i).j (sg0 D A3.A) (((moveYS kap lam YS hw hst).fi i).e x) =
      (Rl.FW i).j (sg0 D A3.A) ((YS.fi i).e x) :=
  congrArg ((Rl.FW i).j (sg0 D A3.A)) (rho_inv _ _ _)

def moveH (H : NX.NExpRealH Rl cG S YS) : NX.NExpRealH (fullHeckeRealDatMovedReadings Rl w kap lam) cG (moveS w YS) (moveYS kap lam YS hw hst) where
  hL := H.hL
  hs := H.hs
  cHk := H.cHk
  cHk_zero := H.cHk_zero
  cHk_unit := H.cHk_unit
  cHk_pow := H.cHk_pow
  hkEq := H.hkEq

theorem reads_move {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} (h : GlobalTheory.ExportPin.Reads Rl cG S YS hL) :
    GlobalTheory.ExportPin.Reads (fullHeckeRealDatMovedReadings Rl w kap lam) cG (moveS w YS) (moveYS kap lam YS hw hst) hL := by
  intro i k P h1 h2 h3 α R h4 h5 x
  rw [j_moveYS, j_moveYS]
  exact h i k P h1 h2 h3 α R h4 h5 x

variable (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)

theorem realRd_move {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ) :
    realRd (moveYS kap lam YS hw hst) v₀ hρ i j b ν = realRd YS v₀ hρ i j b ν := by
  have key : ∀ x : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1),
      evK (moveYS kap lam YS hw hst) v₀ hρ i j b x = evK YS v₀ hρ i j b x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | add x y hx hy => exact (map_add _ _ _).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ _ _).symm)
    | tmul a f =>
      exact congrArg (fun y => ρ.e i b a • (Rl.HW j (sg0 D A3.A)).e y (v₀ j _)) (j_moveYS kap lam YS hw hst j (Subtype.val f))
  exact LinearMap.ext fun f => congrArg (ν⁻¹ • ·) (key _)

theorem ratRow_move {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) :
    RatRow (moveYS kap lam YS hw hst) v₀ hρ i j b ↔ RatRow YS v₀ hρ i j b :=
  exists_congr fun ν => and_congr Iff.rfl (by rw [realRd_move])

variable {YS v₀}

theorem rd_move (Z : ExportTie YS v₀) :
    (fun i j b => realRd (moveYS kap lam YS hw hst) v₀ Z.good i j b (Z.ν i j b) : Rds D.nexp Z.ρ) = Z.rd :=
  funext fun i => funext fun j => funext fun b => realRd_move kap lam YS hw hst v₀ Z.good i j b _

end GlobalTheory.Unframe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HoweDualityCompactPairRealPlacesIrreducible
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.HoweIrrCompact

section FockLin
variable {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool)

theorem fockT_zero : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ε ε' (0 : Matrix (Fin b) (Fin b) ℂ) = 0 := by
  simp [GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT]

theorem fockT_add (Y Y' : Matrix (Fin b) (Fin b) ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ε ε' (Y + Y') = GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ε ε' Y + GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ε ε' Y' := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem fockT_smul (c : ℂ) (Y : Matrix (Fin b) (Fin b) ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ε ε' (c • Y) = c • GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ε ε' Y := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

end FockLin

theorem howe_irr : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (M : Submodule ℂ ((R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank)), (∀ ψ ∈ M, (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (ψ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (ψ w')))) → (∀ ψ ∈ M, ∀ (τ : D.what₂.Tau) (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ → ∀ ψ' : ((R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank), (∀ w z, HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t (ψ w)) z) (R.ptP i t (ψ' w) z) 0) → ψ' ∈ M) → M ≠ ⊥ → ∀ φ : ((R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank), (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (φ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (φ w'))) → φ ∈ M := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hFull i t M hMeq hMlie hM0 φ hφ
  classical
  have hC := hG.core
  obtain ⟨-, -, hinj⟩ := GlobalTheory.CoefActIo.thetaVector_laws (i := i) hC t
  obtain ⟨w, BS, r, hact, hU, hsurj, hε⟩ := _root_.GlobalTheory.RealPtsFock.real_points_fock D G Pl0 T A Ks R F hG hFull i t
  set ρ' : ↥(GinfC (Vc D i)) →* Module.End ℂ (R.cV i).W := (R.cV i).ρ.comp (GinfC (Vc D i)).subtype with hρ'
  have eqv : ∀ ψ : (R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank,
      (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (ψ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (ψ w'))) →
      ∀ (k : ↥(GinfC (Vc D i))) (w' : (R.cV i).W), ψ (ρ' k w') = GlobalTheory.ExportSeries.fockGL (Wc D i).rank w BS (r k) (ψ w') := by
    intro ψ hψ k w'
    apply hinj
    rw [← hact k (ψ w')]
    exact hψ k k.2 w'
  have hirr : ∀ U : Submodule ℂ (R.cV i).W, (∀ k, U.map (ρ' k) ≤ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hUk
    refine (hC.models.cV i).2.2.2.2 U fun h => ?_
    have e := GlobalTheory.AutMult.toInf_mul_toFin (V := Vc D i) h
    have h1 : (R.cV i).ρ h = ρ' (GlobalTheory.AutMult.toInf (Vc D i) h) := by
      calc (R.cV i).ρ h = (R.cV i).ρ ((GlobalTheory.AutMult.toInf (Vc D i) h : GA D (Vc D i)) * GlobalTheory.AutMult.toFin (Vc D i) h) := by rw [e]
        _ = ρ' (GlobalTheory.AutMult.toInf (Vc D i) h) := by
          rw [map_mul, (hC.models.cV i).1 _ (GlobalTheory.AutMult.toFin (Vc D i) h).2, mul_one]
          rfl
    rw [h1]
    exact hUk _
  have hlie : ∀ ψ ∈ M, ∀ (τ : D.what₂.Tau) (Z : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ),
      GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin (Vc D i).rank => true) (fun j : Fin (Wc D i).rank => decide ((j : ℕ) < w.p τ)) Z ∘ₗ ψ ∈ M := by
    intro ψ hψ τ
    obtain ⟨κ, hκ⟩ := _root_.GlobalTheory.FockLieW.hasDerivAt_fockVector D G Pl0 T A Ks R F hG hFull i t τ
    have hε' : (R.MW i (sg0 D A)).ε τ = fun j : Fin (Wc D i).rank => decide ((j : ℕ) < w.p τ) := funext (hε τ)
    set fr := (R.MW i (sg0 D A)).fr τ with hfr
    have base : ∀ Y ∈ lieAt (Wc D i) τ,
        GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin (Vc D i).rank => true) ((R.MW i (sg0 D A)).ε τ) (fr * Y * fr⁻¹) ∘ₗ ψ ∈ M := by
      intro Y hY
      have h1 : (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin (Vc D i).rank => true) ((R.MW i (sg0 D A)).ε τ) (fr * Y * fr⁻¹) + κ Y • (1 : Module.End ℂ (PolF D (Wc D i).rank (Vc D i).rank))) ∘ₗ ψ ∈ M :=
        hMlie ψ hψ τ Y hY _ fun w' z => by
          simpa using hκ Y hY (ψ w') z
      have h2 : κ Y • ψ ∈ M := M.smul_mem _ hψ
      have h3 := M.sub_mem h1 h2
      convert h3 using 1
      ext x
      simp
    have hsp := _root_.GlobalTheory.LieSpanConj.span_conj_lieAt_eq_top D (Wc D i) τ fr ((R.MW i (sg0 D A)).fr_unit τ)
    intro Z
    have hZ : Z ∈ Submodule.span ℂ {Z : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ | ∃ Y ∈ lieAt (Wc D i) τ, Z = fr * Y * fr⁻¹} := by
      rw [hsp]; exact Submodule.mem_top
    rw [← hε']
    induction hZ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨Y, hY, rfl⟩ := hx
      exact base Y hY
    | zero =>
      rw [fockT_zero, LinearMap.zero_comp]; exact M.zero_mem
    | add x y _ _ hx hy =>
      rw [fockT_add, LinearMap.add_comp]; exact M.add_mem hx hy
    | smul c x _ hx =>
      rw [fockT_smul, LinearMap.smul_comp]; exact M.smul_mem c hx
  exact _root_.GlobalTheory.HoweCompactAlg.mem_of_equivariant D (Vc D i).rank (Wc D i).rank w BS ↥(GinfC (Vc D i)) r hU hsurj (R.cV i).W ρ' hirr M
    (fun ψ hψ => eqv ψ (hMeq ψ hψ)) hlie hM0 φ (eqv φ hφ)

end GlobalTheory.HoweIrrCompact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedReadOfTrivialTwistCoboundaryOnSubgroStatement
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnramified_read_of_trivialTwist_coboundary_on_subgroup : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (lam : ↥(OL C.LL)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (a : ℕ) (I : Subgroup (Br.G D.nbr i w hw))
    (z' : Br.G D.nbr i w hw → ↥(latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ 1)).T ⊗[↥(OL C.LL)] ↥(Xq ↥C.LL.1 lam a)),
    tableLineDegreeTwo.IsUnr (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ 1)) ↥(Xq ↥C.LL.1 lam a) (chiT C θ 1) I z' →
    (fun g => iotaC ↥C.LL.1 lam a (z' g)) ∈ Z1urD (latC C (locOC C (chiRatO D.nd i 1))) I := by
  first | exact @GlobalTheory.UseLoc.Cases.readU_unr | exact GlobalTheory.UseLoc.Cases.readU_unr | (intros; apply GlobalTheory.UseLoc.Cases.readU_unr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetRallisFourierMatchingOfWeilField
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem fourierMatch_of_weilField : WeilField → ∀ r, FourierMatch r := fun h =>
  _root_.GlobalTheory.JR.fourierMatch_of_weil (_root_.GlobalTheory.JR.weilEt_of_weilField h) _root_.GlobalTheory.JR.RankOneTransfer.rankOne _root_.GlobalTheory.JR.gammaOne_holds

end GlobalTheory.JR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolynomialMemSpanLiftedMaps
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.FockIsotypic

theorem isotypic_split : ∀ {G W H : Type} [Group G] [AddCommGroup W] [Module ℂ W] [Nontrivial W] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (act : G →* Module.End ℂ H), (∀ g (x y : H), inner ℂ x y = 0 → inner ℂ (act g x) (act g y) = 0) → ∀ (ρ : G →* Module.End ℂ W), (∀ U : Submodule ℂ W, (∀ g, U.map (ρ g) ≤ U) → U = ⊥ ∨ U = ⊤) → ∀ x : H, ∃ q ∈ Submodule.span ℂ {q | ∃ (φ : W →ₗ[ℂ] H) (w : W), (∀ g w', φ (ρ g w') = act g (φ w')) ∧ q = φ w}, ∃ E : Submodule ℂ H, (∀ g, ∀ e ∈ E, act g e ∈ E) ∧ (∀ φ : H →ₗ[ℂ] W, (∀ g, ∀ e ∈ E, φ (act g e) = ρ g (φ e)) → ∀ e ∈ E, φ e = 0) ∧ x - q ∈ E := _root_.GlobalTheory.schur_isotypic_splitting

theorem fis_fockSubst : ∀ (D : D7) (m n : ℕ) (p : D.what₂.Tau → ℕ) (U : GlobalTheory.ExportSeries.GLR D n), (∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin n) ℂ) → ∀ P Q : PolF D m n, GlobalTheory.FockIsotypic.fis (GlobalTheory.ExportSeries.fockSubst p U P) (GlobalTheory.ExportSeries.fockSubst p U Q) = GlobalTheory.FockIsotypic.fis P Q := GlobalTheory.T.fischerInnerForm_fockSubstitution_unitary_invariant

theorem om_ptP_fock : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T) (u : GA D (Vc D i)), u ∈ GinfC (Vc D i) → ∃ (p : D.what₂.Tau → ℕ) (c : ℂ) (U : GlobalTheory.ExportSeries.GLR D (Vc D i).rank), (∀ τ, (U τ).val ∈ Matrix.unitaryGroup (Fin (Vc D i).rank) ℂ) ∧ ∀ P : PolF D (Wc D i).rank (Vc D i).rank, R.ωP i t (u, 1) (R.ptP i t P) = R.ptP i t (c • GlobalTheory.ExportSeries.fockSubst p U P) := _root_.GlobalTheory.RealFockActionFree.om_ptP_inf

theorem totalDegree_aeval_le {σ κ : Type} (f : σ → MvPolynomial κ ℂ) (hf : ∀ v, (f v).totalDegree ≤ 1)
    (P : MvPolynomial σ ℂ) : (MvPolynomial.aeval f P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine MvPolynomial.totalDegree_finsetSum_le fun s hs => ?_
  rw [MvPolynomial.aeval_monomial]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have h0 : (algebraMap ℂ (MvPolynomial κ ℂ) (AddMonoidAlgebra.coeff P s)).totalDegree = 0 :=
    MvPolynomial.totalDegree_C _
  rw [h0, zero_add]
  refine le_trans ?_ (MvPolynomial.le_totalDegree hs)
  unfold Finsupp.prod Finsupp.sum
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  refine Finset.sum_le_sum fun i _ => ?_
  refine (MvPolynomial.totalDegree_pow _ _).trans ?_
  calc s i * (f i).totalDegree ≤ s i * 1 := Nat.mul_le_mul_left _ (hf i)
    _ = s i := mul_one _

theorem totalDegree_fockSubst_le {D : D7} {m n : ℕ} (p : D.what₂.Tau → ℕ) (U : GlobalTheory.ExportSeries.GLR D n)
    (P : PolF D m n) : (GlobalTheory.ExportSeries.fockSubst p U P).totalDegree ≤ P.totalDegree := by
  unfold GlobalTheory.ExportSeries.fockSubst
  refine totalDegree_aeval_le _ (fun v => ?_) P
  split_ifs
  all_goals
    refine MvPolynomial.totalDegree_finsetSum_le fun b _ => ?_
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]

theorem decomp : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T), ∀ (P : PolF D (Wc D i).rank (Vc D i).rank), ∃ Q ∈ Submodule.span ℂ {Q : PolF D (Wc D i).rank (Vc D i).rank | ∃ (φ : (R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) (w : (R.cV i).W), (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (φ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (φ w'))) ∧ Q = φ w}, ∃ E : Submodule ℂ (PolF D (Wc D i).rank (Vc D i).rank), FiniteDimensional ℂ E ∧ (∀ u ∈ GinfC (Vc D i), ∀ P₁ ∈ E, ∀ P₂ : PolF D (Wc D i).rank (Vc D i).rank, R.ptP i t P₂ = R.ωP i t (u, 1) (R.ptP i t P₁) → P₂ ∈ E) ∧ (∀ φ : PolF D (Wc D i).rank (Vc D i).rank →ₗ[ℂ] Module.Dual ℂ (R.cV i).W →ₗ[ℂ] ℂ, (∀ u ∈ GinfC (Vc D i), ∀ P₁ ∈ E, ∀ P₂ : PolF D (Wc D i).rank (Vc D i).rank, R.ptP i t P₂ = R.ωP i t (u, 1) (R.ptP i t P₁) → ∀ l, φ P₂ l = φ P₁ (l ∘ₗ (R.cV i).ρ u)) → ∀ P₁ ∈ E, φ P₁ = 0) ∧ P - Q ∈ E := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hgiv _ i t P
  have hC := hgiv.core
  have hinj : Function.Injective (R.ptP i t) := (GlobalTheory.CoefActIo.thetaVector_laws (i := i) hC t).2.2
  have hcV : (R.cV i).Is := hC.models.cV i
  haveI : Nontrivial (R.cV i).W := hcV.2.2.2.1
  choose p c U hU hω using fun g : GinfC (Vc D i) => om_ptP_fock D G Pl0 T A Ks R F hC i t g.1 g.2
  let actL : GinfC (Vc D i) → Module.End ℂ (PolF D (Wc D i).rank (Vc D i).rank) :=
    fun g => c g • (GlobalTheory.ExportSeries.fockSubst (p g) (U g)).toLinearMap
  have hact : ∀ g Q, R.ptP i t (actL g Q) = R.ωP i t (g.1, 1) (R.ptP i t Q) := fun g Q => (hω g Q).symm
  have hmul : ∀ g h Q, actL (g * h) Q = actL g (actL h Q) := fun g h Q => hinj (by
    have e : (((g * h : GinfC (Vc D i)) : GA D (Vc D i)), (1 : GA D (Wc D i))) = ((g : GA D (Vc D i)), 1) * ((h : GA D (Vc D i)), 1) := by
      simp
    rw [hact, hact, hact, e, map_mul, Module.End.mul_apply])
  have hone : ∀ Q, actL 1 Q = Q := fun Q => hinj (by
    have e : (((1 : GinfC (Vc D i)) : GA D (Vc D i)), (1 : GA D (Wc D i))) = 1 := by simp
    rw [hact, e, map_one, Module.End.one_apply])
  let S : Submodule ℂ (PolF D (Wc D i).rank (Vc D i).rank) :=
    MvPolynomial.restrictTotalDegree (FVar D (Wc D i).rank (Vc D i).rank) ℂ P.totalDegree
  have hS : ∀ g, ∀ Q ∈ S, actL g Q ∈ S := fun g Q hQ => by
    rw [MvPolynomial.mem_restrictTotalDegree] at hQ ⊢
    exact (MvPolynomial.totalDegree_smul_le _ _).trans ((totalDegree_fockSubst_le _ _ _).trans hQ)
  letI : InnerProductSpace.Core ℂ S := fisCore S
  letI : NormedAddCommGroup S := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  letI : InnerProductSpace ℂ S := InnerProductSpace.ofCore _
  let actS : GinfC (Vc D i) →* Module.End ℂ S :=
    { toFun := fun g => (actL g).restrict (hS g)
      map_one' := LinearMap.ext fun x => Subtype.ext (hone x.1)
      map_mul' := fun g h => LinearMap.ext fun x => Subtype.ext (hmul g h x.1) }
  have hconf : ∀ g (x y : S), inner ℂ x y = 0 → inner ℂ (actS g x) (actS g y) = 0 := by
    intro g x y h
    change fis (actL g y.1) (actL g x.1) = 0
    change fis y.1 x.1 = 0 at h
    simp only [actL, LinearMap.smul_apply, AlgHom.toLinearMap_apply]
    rw [fis_smul_left, fis_smul_right, fis_fockSubst _ _ _ _ _ (hU g), h, mul_zero, mul_zero]
  let ρ' : GinfC (Vc D i) →* Module.End ℂ (R.cV i).W := (R.cV i).ρ.comp (GinfC (Vc D i)).subtype
  have hirr : ∀ W' : Submodule ℂ (R.cV i).W, (∀ g, W'.map (ρ' g) ≤ W') → W' = ⊥ ∨ W' = ⊤ :=
    fun W' hW => hcV.2.2.2.2 W' fun h => by
      obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D _).1 h
      rw [map_mul, hcV.1 k hk, mul_one]
      exact hW ⟨a, ha⟩
  obtain ⟨q, hq, E, hEst, hEs, hxE⟩ :=
    isotypic_split actS hconf ρ' hirr ⟨P, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 le_rfl⟩
  refine ⟨q.1, ?_, E.map S.subtype, inferInstance, ?_, ?_, ⟨_, hxE, rfl⟩⟩
  · refine Submodule.span_mono ?_ (Submodule.apply_mem_span_image_of_mem_span S.subtype hq)
    rintro _ ⟨_, ⟨φ, w, hφ, rfl⟩, rfl⟩
    refine ⟨S.subtype ∘ₗ φ, w, fun u hu w' => ?_, rfl⟩
    have e := congrArg Subtype.val (hφ ⟨u, hu⟩ w')
    show R.ptP i t (φ (ρ' ⟨u, hu⟩ w')).1 = R.ωP i t (u, 1) (R.ptP i t (φ w').1)
    rw [e]
    exact hact ⟨u, hu⟩ _
  · rintro u hu _ ⟨e, he, rfl⟩ P₂ h
    have e2 : P₂ = actL ⟨u, hu⟩ e.1 := hinj (h.trans (hact ⟨u, hu⟩ e.1).symm)
    exact ⟨actS ⟨u, hu⟩ e, hEst _ e he, e2.symm⟩
  · intro φ' hφ'
    let ev := Module.evalEquiv ℂ (R.cV i).W
    let φ : S →ₗ[ℂ] (R.cV i).W := ev.symm.toLinearMap ∘ₗ φ' ∘ₗ S.subtype
    have hφe : ∀ x : S, ev (φ x) = φ' x.1 := fun x => ev.apply_symm_apply _
    have key : ∀ g, ∀ e ∈ E, φ (actS g e) = ρ' g (φ e) := by
      intro g e he
      apply ev.injective
      rw [hφe]
      ext l
      have h1 := hφ' g.1 g.2 e.1 ⟨e, he, rfl⟩ (actL g e.1) (hact g e.1) l
      change φ' (actL g e.1) l = _
      rw [h1, ← hφe e]
      rfl
    rintro _ ⟨e, he, rfl⟩
    rw [Submodule.subtype_apply, ← hφe e, hEs φ key e he, map_zero]

end GlobalTheory.FockIsotypic

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergGLnGLmUnfoldingToMirabolicStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.rankinSelbergGLnGLm_unfolding_to_mirabolic : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m r : ℕ) (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure],
    ∃ c : ℝ, 0 < c ∧ ∀ (π : CuspSub E (m + r + 1 + 1)) (π' : CuspSub E (m + 1)), π.IsUnitary → π'.IsUnitary →
    ∀ (φ : GA E (m + r + 1 + 1) → ℂ) (φ' : GA E (m + 1) → ℂ), φ ∈ GlobalTheory.JSW.mspanR π → φ' ∈ GlobalTheory.JSW.mspanR π' →
    ∀ F ∈ GroundTheory.Automorphic.GJMatrix.schwartzBruhatPi (K := E) (ι := Fin (m + 1)), ∀ 𝓕 𝓕₀ : Set (GA E (m + 1)),
    IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ → IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
    ∀ x : ℝ, ∫⁻ h in 𝓕₀, ‖GlobalTheory.JSW.whit φ (GroundTheory.Automorphic.FourierWhittaker.blockGL (by omega : m + 1 ≤ m + r + 1 + 1) h)‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs h ^ (x - ((r : ℝ) + 1))) ∂μ ≠ ⊤ → ∫⁻ h in 𝓕₀, ‖GlobalTheory.JSW.whit φ' h‖ₑ ^ 2 * ‖GroundTheory.Automorphic.GJMatrix.adelicFourierPi E F (GlobalTheory.ZEul.lastRow h)‖ₑ * ENNReal.ofReal (GlobalTheory.RSnm.detAbs h ^ x) ∂μ ≠ ⊤ →
      IntegrableOn (GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x) 𝓕₀ μ ∧
      ∫ h in 𝓕, GlobalTheory.RSnm.rsIntegrand (m + 1) (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' (x : ℂ) h ∂μ =
        (c : ℂ) * ∫ h in 𝓕₀, GlobalTheory.RSnmUnf.uIntNM (by omega : m + 1 ≤ m + r + 1 + 1) F φ φ' x h ∂μ := by
  first | (exact @GlobalTheory.RSnmUnfold.rs_unfold) | (exact GlobalTheory.RSnmUnfold.rs_unfold) | (intros; apply GlobalTheory.RSnmUnfold.rs_unfold  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepresentationOfIntegralMatricesEqInvTwistedCharStatement
section
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representationOfIntegralMatrices_eq_inv_twistedChar_smul : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (N : Br.G D.nbr i w hw →* Matrix (Fin k) (Fin k) ↥(OL C.LL)) (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ) (g : Br.G D.nbr i w hw),
    repV C N g = ((tableLineDegreeTwo.charL (LL := ↥C.LL.1) (chiT C θ 1) g)⁻¹ : (↥C.LL.1)ˣ).val • repV C (twistM N θ) g := by
  first | exact @GlobalTheory.UseLoc.Cases.repV_eq_inv_smul_twist | exact GlobalTheory.UseLoc.Cases.repV_eq_inv_smul_twist | (intros; apply GlobalTheory.UseLoc.Cases.repV_eq_inv_smul_twist <;> assumption)
end

