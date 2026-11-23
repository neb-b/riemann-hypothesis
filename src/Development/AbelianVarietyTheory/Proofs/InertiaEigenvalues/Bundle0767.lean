module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0670
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0285
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0448
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0679
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0680
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPlaceModelPlaceMap
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetReducedBlockEqResidueDet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0763
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0845
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0844
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0214

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchrodingerHyperplaneAveragesVanish
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.HypAvg

theorem residueEquiv : ∀ (D : D7) (v : FinPl D) (PP : Pl D.host.E) (red : OI v →+* kP PP), Function.Surjective red → (∀ a : OI v, red a = 0 ↔ Valued.v (a : Fv D.host.F v) < 1) → ∃ ρk : IsLocalRing.ResidueField (OI v) ≃+* kP PP, ∀ a : OI v, ρk (IsLocalRing.residue (OI v) a) = red a := by
  intro D v PP red hs hk
  have hker : RingHom.ker red = IsLocalRing.maximalIdeal (OI v) := by
    ext a
    rw [RingHom.mem_ker, hk]
    exact (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (Fv D.host.F v) _))).symm
  exact ⟨(Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hs), fun a => rfl⟩

theorem exists_blockGL : ∀ (O : Type) [CommRing O] [IsLocalRing O] (r t n : ℕ) (hn : r + t = n) (M : Matrix (Fin r) (Fin r) O) (g₀ : GL (Fin r) (IsLocalRing.ResidueField O)), M.map (IsLocalRing.residue O) = (g₀ : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)) → ∃ h : GL (Fin n) O, (h : Matrix (Fin n) (Fin n) O) = (Matrix.fromBlocks M 0 0 (1 : Matrix (Fin t) (Fin t) O)).submatrix (rowIx hn).symm (rowIx hn).symm := by
  intro O _ _ r t n hn M g₀ hM
  have hd : IsLocalRing.residue O M.det = (g₀ : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O)).det := by
    rw [← hM, RingHom.map_det]; rfl
  have hdet : IsUnit ((Matrix.fromBlocks M 0 0 (1 : Matrix (Fin t) (Fin t) O)).submatrix (rowIx hn).symm
      (rowIx hn).symm).det := by
    rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one,
      ← IsLocalRing.residue_ne_zero_iff_isUnit, hd, ← Matrix.GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  exact ⟨Matrix.nonsingInvUnit _ hdet, rfl⟩

theorem ell_heisO_omegaInv : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.thP_ωP → ∀ (i : Fin D.R.m) (t : T) (ℓ : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] ℂ) (κ : GA D (Vc D i)) (c : ℂ), c ≠ 0 → (∀ φ', IsThetaFunO R.ψ (Vc D i) (Wc D i) φ' → ℓ (R.ωP i t (κ, 1) φ') = c * ℓ φ') → ∀ (u : WO (Vc D i) (Wc D i)) (f : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ℓ (heisO R.ψ (Vc D i) (Wc D i) u (R.ωP i t (κ⁻¹, 1) f)) = c⁻¹ * ℓ (heisO R.ψ (Vc D i) (Wc D i) (actO (Vc D i) (Wc D i) κ 1 u) f) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hω i t ℓ κ c hc hsc u f hf
  have hW := hω i t
  have e1 : actO (Vc D i) (Wc D i) κ⁻¹ 1 (actO (Vc D i) (Wc D i) κ 1 u) = u := by
    simpa using GlobalTheory.SplitHecke.actO_inv_actO (S := Vc D i) (T := Wc D i) κ 1 u
  have e2 := hW.om_heis κ⁻¹ 1 (actO (Vc D i) (Wc D i) κ 1 u) f hf
  rw [e1] at e2
  rw [← e2]
  have hth := hW.om_pres (κ⁻¹, 1) _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hW.std hf (actO (Vc D i) (Wc D i) κ 1 u))
  have e3 := hsc _ hth
  have e4 : R.ωP i t (κ, 1) (R.ωP i t (κ⁻¹, 1) (heisO R.ψ (Vc D i) (Wc D i) (actO (Vc D i) (Wc D i) κ 1 u) f)) =
      heisO R.ψ (Vc D i) (Wc D i) (actO (Vc D i) (Wc D i) κ 1 u) f := by
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_one]
    show R.ωP i t 1 _ = _
    rw [map_one]; rfl
  rw [e4] at e3
  rw [e3, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem actO_sigma : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsIdemOf φ e → ∀ (σ : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v) → WO (Vc D i) (Wc D i)), (∀ X, IsHalf (cA D e) (σ X) ∧ coR R i φ (σ X) = X) → ∀ (κ : GA D (Vc D i)) (M : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r ⊕ Fin D.R.t) (Fv D.host.F v)), ((grpCo φ (Vc D i) (frCo φ (R.βV i)) κ : GL (Fin (Vc D i).rank) (Fv D.host.F v)) : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (Fv D.host.F v)) = M.submatrix (rowIx (rank_V i)).symm (rowIx (rank_V i)).symm → ∀ X, actO (Vc D i) (Wc D i) κ 1 (σ X) = σ (M * X) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL i v φ e he σ hσ κ M hM X
  have sdV := _root_.GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βV i)
  have sdW := _root_.GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βW i)
  obtain ⟨hco, hact⟩ := GlobalTheory.PlaceTensor.adjCo_isCoord D (Vc D i) (Wc D i) _ _ sdV sdW v φ e he (frCo φ (R.βV i))
    (frCo φ (R.βW i))
  have hhalf : IsHalf (cA D e) (actO (Vc D i) (Wc D i) κ 1 (σ X)) := GlobalTheory.SplitHecke.isHalf_actO κ 1 (hσ X).1
  apply hco.2.1.injOn hhalf (hσ (M * X)).1
  have h1 := hact κ⁻¹ 1 (σ X)
  simp only [inv_inv, inv_one] at h1
  have hg1 : grpCo φ (Wc D i) (frCo φ (R.βW i)) 1 = 1 := by
    unfold grpCo; simp
  have key : ∀ y, adjCo φ (Vc D i) (Wc D i) (frCo φ (R.βV i)) (frCo φ (R.βW i)) y =
      (coR R i φ y).submatrix (rowIx (rank_V i)).symm (finCongr (rank_weight_component_eq i)).symm := by
    intro y
    unfold coR co
    rw [Matrix.submatrix_submatrix]
    ext j k
    simp
  rw [h1, GlobalTheory.PlaceTensor.AdjCoord.grpCo_inv, inv_inv, hg1, Units.val_one, Matrix.mul_one, key (σ (M * X)),
    (hσ _).2, key (σ X), (hσ X).2, hM, Matrix.submatrix_mul_equiv]

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem liftsV (R : RealDat D A Ks) (h : R.toLevCh.Is A.μ0) (i : Fin D.R.m) (t : T) :
    LiftsExist (Vc D i) (R.βV i) (R.datVt i t) := by
  obtain ⟨c, hc⟩ := h.βV i
  refine _root_.GlobalTheory.ParahoricLift.liftsExist _ _ _ _ _ hc (fun PP hP PP' hP' => ?_)
    (GlobalTheory.LevelRamif.ramif_at_levels D T R.toLevCh A.μ0 h t i).1
  obtain ⟨k, hk⟩ := (h.Pg PP).1 hP
  rcases hP' with hP' | hP'
  · obtain ⟨k', hk'⟩ := (h.Pg PP').1 hP'
    exact GlobalTheory.ProjectedLift.not_isConjPl R.C.P hk hk'
  · intro hc
    obtain ⟨q, hq, hm, hne⟩ := GlobalTheory.LevelRamif.exists_prime_mem (h.Q_pl t) hP'
    exact GlobalTheory.LevelRamif.not_two_primes PP' hq (D.host.g_prime k) (hne k) hm
      (GlobalTheory.LevelRamif.natCast_mem_conj hc (GlobalTheory.LevelRamif.typePrime_mem hk))

theorem termAt (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) (hω : R.thP_ωP) (i : Fin D.R.m) (t : T)
    (PP : Pl D.host.E) (hPP : PP ∈ R.Pg) {v : FinPl D} (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D) (he : IsIdemOf φ e)
    (red : OI v →+* kP PP) (ρk : IsLocalRing.ResidueField (OI v) ≃+* kP PP)
    (hρ : ∀ a : OI v, ρk (IsLocalRing.residue (OI v) a) = red a) (hAct : ActAt R i t PP φ e red)
    {Sb : Finset (FinPl D)} (hv : v ∈ Sb)
    (σ : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v) → WO (Vc D i) (Wc D i))
    (hσ : ∀ X, IsHalf (cA D e) (σ X) ∧ coR R i φ (σ X) = X)
    (ℓ : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] ℂ) (hℓ : InvForm R.ψ (Vc D i) (Wc D i) e ℓ)
    (f : WO (Vc D i) (Wc D i) → ℂ) (hf : IsThetaFunO R.ψ (Vc D i) (Wc D i) f) (a' : Fin D.R.r → kP PP)
    (lift : GL (Fin D.R.r) (IsLocalRing.ResidueField (OI v)) → Matrix (Fin D.R.r) (Fin D.R.r) (OI v))
    (hlift : ∀ g, (lift g).map (IsLocalRing.residue (OI v)) =
      (g : Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (OI v))))
    (g : G) (hg : mirC R i ⟨PP, hPP⟩ a' false 1 g ≠ 0) :
    ∃ κ : GA D (Vc D i), IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ ∧ SuppIn Sb (Vc D i) κ ∧
      ∀ X, mirC R i ⟨PP, hPP⟩ a' false 1 g * (levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ *
          ℓ (heisO R.ψ (Vc D i) (Wc D i) (σ X) (R.ωP i t (κ⁻¹, 1) f)) =
        ℓ (heisO R.ψ (Vc D i) (Wc D i) (σ ((Matrix.fromBlocks
          (lift (Matrix.GeneralLinearGroup.map ρk.symm.toRingHom (R.eG g ⟨PP, hPP⟩))) 0 0
          (1 : Matrix (Fin D.R.t) (Fin D.R.t) (OI v))).map (algebraMap (OI v) (Fv D.host.F v)) * X)) f) := by
  classical
  have hc : (∀ PP' : R.Pg, PP' ≠ ⟨PP, hPP⟩ → R.eG g PP' = 1) ∧
      ∀ x, a' ⬝ᵥ x = 0 → ((R.eG g ⟨PP, hPP⟩ : GL (Fin D.R.r) (kP PP)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)).mulVec x = x := by
    by_contra hc
    exact hg (by unfold mirC; rw [if_neg (by simpa using hc)])
  have hm : mirC R i ⟨PP, hPP⟩ a' false 1 g =
      ((R.chi ((i : ℕ) + 1) PP (Matrix.GeneralLinearGroup.det (R.eG g ⟨PP, hPP⟩)) : ℂˣ) : ℂ) := by
    unfold mirC; rw [if_pos (by simpa using hc), zpow_one]
  set g₀ := Matrix.GeneralLinearGroup.map ρk.symm.toRingHom (R.eG g ⟨PP, hPP⟩) with hg₀
  obtain ⟨hh, hhv⟩ := exists_blockGL (OI v) D.R.r D.R.t _ (rank_V i) (lift g₀) g₀ (hlift g₀)
  obtain ⟨κ, hSupp, hGf, hSt, hgrp, hred, hoth, hsc⟩ := hAct hh
  have hlr : (lift g₀).map red = ((R.eG g ⟨PP, hPP⟩ : GL (Fin D.R.r) (kP PP)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)) := by
    ext j k
    have e1 := congrFun (congrFun (hlift g₀) j) k
    simp only [Matrix.map_apply] at e1 ⊢
    rw [← hρ, e1, hg₀]
    simp [Matrix.GeneralLinearGroup.map]
  have hredM : ((redFn (R.βV i) PP (finE (Vc D i) κ) : GL (Fin (Vc D i).rank) (kP PP)) :
      Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (kP PP)) =
      (Matrix.fromBlocks ((R.eG g ⟨PP, hPP⟩ : GL (Fin D.R.r) (kP PP)) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP)) 0 0
        (1 : Matrix (Fin D.R.t) (Fin D.R.t) (kP PP))).submatrix (rowIx (rank_V i)).symm (rowIx (rank_V i)).symm := by
    rw [hred]
    show (hh : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (OI v)).map red = _
    rw [hhv, ← Matrix.submatrix_map, Matrix.fromBlocks_map, hlr, Matrix.map_zero _ (map_zero red),
      Matrix.map_zero _ (map_zero red), Matrix.map_one _ (map_zero red) (map_one red)]
  obtain ⟨hLift, hchi⟩ := _root_.GlobalTheory.LiftDiag.lift_diag D G Pl0 T A Ks R i t PP hPP g hc.1 κ hGf hSt hredM hoth
  refine ⟨κ, hLift, suppIn_of_suppAt he hv hSupp, fun X => ?_⟩
  have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map red hh) =
      Matrix.GeneralLinearGroup.det (R.eG g ⟨PP, hPP⟩) := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, ← hred, hredM,
      Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
  set c : ℂ := ((R.chi ((i : ℕ) + 1) PP (Matrix.GeneralLinearGroup.det (R.eG g ⟨PP, hPP⟩)) : ℂˣ) : ℂ) with hcdef
  have hc0 : c ≠ 0 := Units.ne_zero _
  have key := ell_heisO_omegaInv D G Pl0 T A Ks R hω i t ℓ κ c hc0
    (fun φ' hφ' => by rw [hsc ℓ hℓ φ' hφ', hdet]) (σ X) f hf
  have hco := actO_sigma D G Pl0 T A Ks R hL i v φ e he σ hσ κ
    ((Matrix.fromBlocks (lift g₀) 0 0 (1 : Matrix (Fin D.R.t) (Fin D.R.t) (OI v))).map
      (algebraMap (OI v) (Fv D.host.F v))) (by
        rw [hgrp]
        show (hh : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) (OI v)).map (algebraMap (OI v) (Fv D.host.F v)) = _
        rw [hhv, Matrix.submatrix_map]) X
  rw [key, hco, hchi, hm, inv_one, mul_one, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]

theorem avg_schrodinger_hyperplane : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.thP_ωP → ∀ (i : Fin D.R.m) (t : T) (PP : Pl D.host.E), PP ∈ R.Pg → ∀ (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsProjAt φ PP → IsIdemOf φ e → ∀ (red : OI v →+* kP PP), Function.Surjective red → (∀ a : OI v, red a = 0 ↔ Valued.v (a : Fv D.host.F v) < 1) → ActAt R i t PP φ e red → ∀ (Sb : Finset (FinPl D)), v ∈ Sb → ∀ (σ : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v) → WO (Vc D i) (Wc D i)), (∀ X, IsHalf (cA D e) (σ X) ∧ coR R i φ (σ X) = X) → ∀ (ℓ : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] ℂ), InvForm R.ψ (Vc D i) (Wc D i) e ℓ → ∀ (f : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) f → CleanIn R i t Sb f → ∀ a : Fin D.R.r → IsLocalRing.ResidueField (OI v), a ≠ 0 → ∀ (lift : GL (Fin D.R.r) (IsLocalRing.ResidueField (OI v)) → Matrix (Fin D.R.r) (Fin D.R.r) (OI v)), (∀ g, (lift g).map (IsLocalRing.residue (OI v)) = (g : Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (OI v)))) → ∀ X : Matrix (Fin D.R.r ⊕ Fin D.R.t) (Fin D.R.r) (Fv D.host.F v), ∑ᶠ g ∈ {g : GL (Fin D.R.r) (IsLocalRing.ResidueField (OI v)) | ∀ w, a ⬝ᵥ w = 0 → (g : Matrix (Fin D.R.r) (Fin D.R.r) (IsLocalRing.ResidueField (OI v))).mulVec w = w}, ℓ (heisO R.ψ (Vc D i) (Wc D i) (σ ((Matrix.fromBlocks (lift g) 0 0 (1 : Matrix (Fin D.R.t) (Fin D.R.t) (OI v))).map (algebraMap (OI v) (Fv D.host.F v)) * X)) f) = 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R hL hω i t PP hPP v φ e hproj he red hsurj hker hAct Sb hv σ hσ ℓ hℓ f hf hclean a ha
    lift hlift X
  classical
  obtain ⟨ρk, hρ⟩ := residueEquiv D v PP red hsurj hker
  have ha' : (fun j => ρk (a j)) ≠ 0 := fun h => ha (funext fun j => ρk.injective (by simpa using congrFun h j))
  have hOver : Over PP v := ((GlobalTheory.SplitIdemDict.idem_dictionary D).2 v φ PP hproj).1
  choose κ₀ hκ₀ using fun g : G => liftsV R hL i t (R.eG g)
  have hG := fun (g : G) (hg : mirC R i ⟨PP, hPP⟩ (fun j => ρk (a j)) false 1 g ≠ 0) =>
    termAt R hL hω i t PP hPP φ e he red ρk hρ hAct hv σ hσ ℓ hℓ f hf (fun j => ρk (a j)) lift hlift g hg
  let κ : G → GA D (Vc D i) := fun g =>
    if hg : mirC R i ⟨PP, hPP⟩ (fun j => ρk (a j)) false 1 g ≠ 0 then (hG g hg).choose else κ₀ g
  have hκ : ∀ g (hg : mirC R i ⟨PP, hPP⟩ (fun j => ρk (a j)) false 1 g ≠ 0), κ g = (hG g hg).choose :=
    fun g hg => dif_pos hg
  have hLifts : IsLifts R i t κ := fun g => by
    by_cases hg : mirC R i ⟨PP, hPP⟩ (fun j => ρk (a j)) false 1 g ≠ 0
    · rw [hκ g hg]; exact (hG g hg).choose_spec.1
    · have : κ g = κ₀ g := dif_neg hg
      rw [this]; exact hκ₀ g
  have hSupp : ∀ g, mirC R i ⟨PP, hPP⟩ (fun j => ρk (a j)) false 1 g ≠ 0 → SuppIn Sb (Vc D i) (κ g) :=
    fun g hg => by rw [hκ g hg]; exact (hG g hg).choose_spec.2.1
  have h0 := hclean ⟨PP, hPP⟩ (fun j => ρk (a j)) ha' false 1 (Or.inl rfl) ⟨v, hv, hOver⟩ κ hLifts hSupp
  have h1 := congrArg (fun φ' => ℓ (heisO R.ψ (Vc D i) (Wc D i) (σ X) φ')) h0
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [avgW, GlobalTheory.SplitScalar.heisO_sum, GlobalTheory.SplitScalar.heisO_smul, map_sum, map_smul, smul_eq_mul] at h1
  set Fn : GL (Fin D.R.r) (IsLocalRing.ResidueField (OI v)) → ℂ := fun g =>
    ℓ (heisO R.ψ (Vc D i) (Wc D i) (σ ((Matrix.fromBlocks (lift g) 0 0 (1 : Matrix (Fin D.R.t) (Fin D.R.t) (OI v))).map
      (algebraMap (OI v) (Fv D.host.F v)) * X)) f) with hFn
  rw [← _root_.GlobalTheory.DownLift.GenSplit.mirC_hyperplane_reindex D G Pl0 T A Ks R i PP hPP v ρk a Fn, finsum_mem_def, finsum_eq_sum_of_fintype]
  have hz : heisO R.ψ (Vc D i) (Wc D i) (σ X) (0 : WO (Vc D i) (Wc D i) → ℂ) = 0 := by
    funext w; simp [heisO]
  rw [hz, map_zero] at h1
  refine (Finset.sum_congr rfl fun g _ => ?_).trans h1
  by_cases hg : mirC R i ⟨PP, hPP⟩ (fun j => ρk (a j)) false 1 g ≠ 0
  · rw [Set.indicator_of_mem (show g ∈ {g : G | mirC R i ⟨PP, hPP⟩ (fun j => ρk (a j)) false 1 g ≠ 0} from hg), hκ g hg]
    exact ((hG g hg).choose_spec.2.2 X).symm
  · rw [Set.indicator_of_notMem (show g ∉ {g : G | mirC R i ⟨PP, hPP⟩ (fun j => ρk (a j)) false 1 g ≠ 0} from hg)]
    rw [not_not.1 hg, zero_mul, zero_mul]

end GlobalTheory.DownLift.HypAvg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameTwistFamilySpecializationGood
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.ExportSeries.SpecGood

variable {D : D7}

theorem infPart_eq_zero_of_isIdemAt : ∀ (D : D7) (P : Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e P → infPart D e = 0 := by
  intro D P e h
  obtain ⟨⟨h1, h2, v, ε, ⟨α, rfl, -⟩, h3⟩, -⟩ := h
  have k1 := congrArg (infPart D) h1
  have k2 := congrArg (infPart D) h2
  have k3 := congrArg (infPart D) h3
  simp only [RingHom.map_mul, RingHom.map_add (f := _), RingHom.map_zero] at k1 k2 k3
  have k4 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
    simp [infPart, Algebra.TensorProduct.algebraMap_apply]
    show (0 : Ainf D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    exact TensorProduct.zero_tmul _ _
  rw [k4] at k3
  linear_combination -k1 + infPart D e * k3 - k2

theorem finUnit_of_res (P : Pl D.host.E) (hP : Formalism.L2.NTheta.IsIdemAt (idemAt P) P) (x : (AE D)ˣ)
    (h1 : (1 - idemAt P) * (x : AE D) = 1 - idemAt P)
    (hx : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (v : (kP P)ˣ)
    (hv : resS D.host.F P ⟨_, hx⟩ = v) :
    infPart D (x : AE D) = 1 ∧ finPart D (x : AE D) ∈ intAE D ∧ finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D := by
  obtain ⟨ι, i1, i2, -⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  refine ⟨?_, _root_.GlobalTheory.ExportSeries.finPart_mem_intAE_of_unit_residue D ι i1 i2 P (idemAt P) (_root_.GlobalTheory.ExportSeries.idem_apply_eq_zero_of_ne D ι i1 i2 P _ hP) x h1 hx v hv⟩
  have := congrArg (infPart D) h1
  rwa [RingHom.map_mul, RingHom.map_sub, RingHom.map_one, infPart_eq_zero_of_isIdemAt D P _ hP, sub_zero, one_mul] at this

variable {C A : Type} [AddCommGroup C] [CommGroup A]

theorem idemAt_mul_idem {Q : Finset (Pl D.host.E)} (h : SplitSet Q) {P : Pl D.host.E} (hP : P ∈ Q) :
    idemAt P * idem Q = idemAt P :=
  GlobalTheory.PlaceModelSum.mul_sum_orth (fun a ha => (h.isIdemAt ha).1) (fun a ha b hb hab => h.mul_eq_zero ha hb hab) hP

theorem idemAt_mul_conj_idem {Q : Finset (Pl D.host.E)} (h : SplitSet Q) {P : Pl D.host.E} (hP : P ∈ Q) :
    idemAt P * cA D (idem Q) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [idem, map_sum, Finset.mul_sum]
  exact Finset.sum_eq_zero fun j hj => h.mul_conj hP hj

theorem delQ_eq_one {u : UnivTwist D C} {Q : Finset (Pl D.host.E)} {x : (AE D)ˣ} (hx : ∀ P ∈ Q, u.del P x = 1) :
    u.delQ Q x = 1 := by
  ext PP
  exact congrArg Multiplicative.toAdd (hx PP.1 PP.2)


open Classical in
theorem spec_good (D : D7) (C A : Type) [AddCommGroup C] [CommGroup A] (u : UnivTwist D C) (Q : Finset (Pl D.host.E))
    (χ : Multiplicative (↥Q → C) →* A) (h : u.Good Q) : (u.spec Q χ).Good := by
  have cc := GlobalTheory.DualPairCheck.cA_cA (D := D)
  refine ⟨?_, ?_, ?_, h.1, ?_, ?_⟩
  · haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.isTopRing (F := D.host.F) (E := D.host.E)
    let H : Subgroup (AE D)ˣ := ⨅ P : ↥Q, (u.del P.1).ker
    have hH : IsOpen (H : Set (AE D)ˣ) := by
      rw [Subgroup.coe_iInf]
      exact isOpen_iInter_of_finite fun P => (h.2 P.1 P.2).isOpen
    refine Subgroup.isOpen_mono (fun x hx => ?_) hH
    rw [Subgroup.mem_iInf] at hx
    show χ (u.delQ Q x) = 1
    rw [delQ_eq_one fun P hP => hx ⟨P, hP⟩, map_one]
  · intro x
    show χ (u.delQ Q _) = 1
    rw [delQ_eq_one fun P hP => (h.2 P hP).rat x, map_one]
  · intro a
    show χ (u.delQ Q _) = 1
    rw [h.delQ_real a, map_one]
  · intro x h1 h2 h3 h4
    show χ (u.delQ Q x) = 1
    replace h4 : (idem Q + cA D (idem Q)) * (x : AE D) = idem Q + cA D (idem Q) := h4
    refine (congrArg χ (delQ_eq_one fun P hP => ?_)).trans (map_one χ)
    refine (h.2 P hP).unram x h1 h2 h3 ?_
    show (idem {P} + cA D (idem {P})) * (x : AE D) = idem {P} + cA D (idem {P})
    have e1 : idem ({P} : Finset (Pl D.host.E)) = idemAt P := Finset.sum_singleton _ _
    rw [e1]
    have k1 := idemAt_mul_idem h.1 hP
    have k2 := idemAt_mul_conj_idem h.1 hP
    have k3 : cA D (idemAt P) * idem Q = 0 := by
      have := congrArg (cA D) k2
      rwa [RingHom.map_mul, cc, RingHom.map_zero] at this
    have k4 : cA D (idemAt P) * cA D (idem Q) = cA D (idemAt P) := by
      rw [← RingHom.map_mul, k1]
    linear_combination (idemAt P + cA D (idemAt P)) * h4 + (1 - (x : AE D)) * (k1 + k2 + k3 + k4)
  · intro PP hPP x h1 hx v hv
    show χ (u.delQ Q x) = (u.spec Q χ).res PP v
    rw [show (u.spec Q χ).res PP = χ.comp ((AddMonoidHom.toMultiplicative (AddMonoidHom.single (fun _ : ↥Q => C) ⟨PP, hPP⟩)).comp
      (u.kap PP)) from dif_pos hPP, MonoidHom.comp_apply]
    have hfu := finUnit_of_res PP (h.1.isIdemAt hPP) x h1 hx v hv
    refine congrArg χ ?_
    ext ⟨P', hP'⟩
    by_cases hne : P' = PP
    · subst hne
      have := (h.2 P' hP').res P' (Finset.mem_singleton_self _) x h1 hx v hv
      simp [UnivTwist.delQ, this]
    · have hd : u.del P' x = 1 := by
        refine (h.2 P' hP').unram x hfu.1 hfu.2.1 hfu.2.2 ?_
        show (idem {P'} + cA D (idem {P'})) * (x : AE D) = idem {P'} + cA D (idem {P'})
        have e1 : idem ({P'} : Finset (Pl D.host.E)) = idemAt P' := Finset.sum_singleton _ _
        rw [e1]
        have z1 : idemAt P' * idemAt PP = 0 := h.1.mul_eq_zero hP' hPP (Ne.symm hne)
        have z2 : idemAt PP * cA D (idemAt P') = 0 := h.1.mul_conj hPP hP'
        linear_combination (idemAt P' + cA D (idemAt P')) * h1 + ((x : AE D) - 1) * (z1 + z2)
      simp [UnivTwist.delQ, hd, Pi.single_apply, hne]
      intro e
      exact absurd (congrArg Subtype.val e) hne

end GlobalTheory.ExportSeries.SpecGood
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionLevelAndSchrodingerBoundedSupport
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (FinPl idem SplitProj IsIdemOf IsProjAt adjCo grpCo frCo)
open GlobalTheory.DownLift.GenSplit

noncomputable section

namespace GlobalTheory.DownLift.GenSplit.SupportBound

open GlobalTheory.SplitScalar

variable {D : D7}

theorem exists_pow_le {v : FinPl D} {ϖ : OI v} (hϖ : Irreducible ϖ) {c d : Fv D.host.F v} (hc : c ≠ 0) (hd : d ≠ 0) :
    ∃ N : ℕ, Valued.v (algebraMap (OI v) (Fv D.host.F v) (ϖ ^ N)) ≤ Valued.v c ∧
      Valued.v (algebraMap (OI v) (Fv D.host.F v) (ϖ ^ N)) ≤ Valued.v d := by
  have h1 : Valued.v (algebraMap (OI v) (Fv D.host.F v) ϖ) < 1 := by
    refine lt_of_le_of_ne ϖ.2 fun h => hϖ.not_isUnit ?_
    exact HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.2 h
  have h2 : min (Valued.v c) (Valued.v d) ≠ 0 := by
    rcases min_choice (Valued.v c) (Valued.v d) with h | h <;> rw [h]
    · exact (Valuation.ne_zero_iff _).2 hc
    · exact (Valuation.ne_zero_iff _).2 hd
  obtain ⟨N, hN⟩ := exists_pow_lt₀ h1 (Units.mk0 _ h2)
  refine ⟨N, ?_, ?_⟩ <;> rw [map_pow, map_pow]
  · exact hN.le.trans (min_le_left _ _)
  · exact hN.le.trans (min_le_right _ _)

theorem rdQ_ne_zero {v : FinPl D} (φ : SplitProj D v) {x : D.host.E} (hx : x ≠ 0) : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ x ≠ 0 := by
  have h : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ x * GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ x⁻¹ = 1 := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ
    rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hx]
    exact map_one φ
  exact left_ne_zero_of_mul_eq_one h

theorem map_nsmul_of_add {A B : Type} [AddGroup A] [AddGroup B] {κ : A → B} (h : ∀ x y, κ (x + y) = κ x + κ y) (k : ℕ)
    (x : A) : κ (k • x) = k • κ x :=
  map_nsmul (AddMonoidHom.mk' κ h) k x

theorem symplO_nsmul (S T : HSp D) (k : ℕ) (x y : WO S T) : symplO S T (k • x) y = symplO S T x (k • y) := by
  rw [← Nat.cast_smul_eq_nsmul (AE D), symplO_smul, map_natCast, Nat.cast_smul_eq_nsmul]

theorem level_and_support : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (v : FinPl D) (φ : SplitProj D v) (e : Formalism.L2.Theta.AE D), IsIdemOf φ e → ∀ (ϖ : OI v), Irreducible ϖ → ∀ f, IsThetaFunO ψ S T f → ∃ N : ℕ, (∀ z ∈ halfPow φ S T (frCo φ βS) (frCo φ βT) e ϖ N, heisO ψ S T z f = f) ∧ ∀ ℓ, InvForm ψ S T e ℓ → ∀ x, IsHalf (cA D e) x → ℓ (heisO ψ S T x f) ≠ 0 → Bdd ϖ N (adjCo φ S T (frCo φ βS) (frCo φ βT) x) := by
  intro D ψ hψ S T ΛS ΛT βS βT hS hT hfS hfT v φ e he ϖ hϖ f hf
  obtain ⟨U, hU, hUf⟩ := hf.level
  obtain ⟨k, hk, hkU⟩ := (GlobalTheory.LatLevel.level_of_generators D S T _ _ hS hT
    (GlobalTheory.LatFinGen.latO_finitely_generated D S T _ _ hS hT)).1 U hU
  obtain ⟨hd, -, -⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT
  obtain ⟨-, a, -, ha0, -, himg⟩ := GlobalTheory.SplitLatticeHalves.splitLattice D S T ΛS ΛT βS βT hS hT hfS hfT v φ e he
  obtain ⟨⟨hadd, hbij, -⟩, -⟩ := GlobalTheory.PlaceTensor.adjCo_isCoord D S T ΛS ΛT hS hT v φ e he (frCo φ βS) (frCo φ βT)
  have hst := @idem_smul_mem D S T ΛS ΛT _ he.1.1
  have he' := isSplitIdem_conj he.1
  have hb := rdQ_ne_zero φ (star_ne_zero.2 ha0)
  generalize GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.rdQ φ (star a) = b at hb himg
  generalize (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) = Λ at *
  haveI : CharZero (Fv D.host.F v) := algebraRat.charZero _
  have hk0 : (k : Fv D.host.F v) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hkv : Valued.v (k : Fv D.host.F v) ≠ 0 := (Valuation.ne_zero_iff _).2 hk0
  obtain ⟨N, hN1, hN2⟩ := exists_pow_le hϖ (mul_ne_zero hk0 hb) (mul_ne_zero hk0 (inv_ne_zero hb))
  refine ⟨N, fun z hz => ?_, fun ℓ hℓ x hx hne i j => ?_⟩
  · have hy : (k : Fv D.host.F v)⁻¹ • adjCo φ S T (frCo φ βS) (frCo φ βT) z ∈
        {y : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) | ∀ i j, Valued.v (y i j) ≤ Valued.v b} := by
      intro i j
      obtain ⟨o, ho⟩ := hz.2 i j
      rw [Matrix.smul_apply, ho, smul_eq_mul, map_mul, map_mul, map_mul, map_inv₀, inv_mul_le_iff₀ (zero_lt_iff.2 hkv),
        ← Valuation.map_mul _ (k : Fv D.host.F v)]
      exact (mul_le_of_le_one_right' o.2).trans hN1
    rw [← himg] at hy
    obtain ⟨t, ⟨ht, hth⟩, hty⟩ := hy
    have : z = k • t := by
      refine hbij.injOn hz.1 (isHalf_nsmul hth k) ?_
      rw [map_nsmul_of_add hadd, hty, ← Nat.cast_smul_eq_nsmul (Fv D.host.F v), smul_smul, mul_inv_cancel₀ hk0, one_smul]
    exact hUf z (this ▸ hkU t ht) (half_fin he' hz.1)
  · have hkx : k • x ∈ Λ := by
      by_contra hn
      obtain ⟨l, hl, hlh, hl1⟩ := exists_dual_half he' hd (by rw [GlobalTheory.DualPairCheck.cA_cA]; exact hst)
        (isHalf_nsmul hx k) hn
      rw [GlobalTheory.DualPairCheck.cA_cA] at hlh
      have hlk := isHalf_nsmul hlh k
      have h2 := hℓ _ hlk _ (GlobalTheory.FinTranslate.isTheta_heisO_fin hψ.1 (half_fin he' hx) hf)
      rw [heisO_comm, hUf _ (hkU l hl) (half_fin he.1 hlk), map_smul, smul_eq_mul, symplO_nsmul] at h2
      exact hl1 (mul_right_cancel₀ hne (h2.trans (one_mul _).symm))
    have hy : adjCo φ S T (frCo φ βS) (frCo φ βT) (k • x) ∈
        {y : Matrix (Fin S.rank) (Fin T.rank) (Fv D.host.F v) | ∀ i j, Valued.v (y i j) ≤ Valued.v b} := by
      rw [← himg]
      exact ⟨_, ⟨hkx, isHalf_nsmul hx k⟩, rfl⟩
    have h3 := hy i j
    rw [map_nsmul_of_add hadd, Matrix.smul_apply, nsmul_eq_mul] at h3
    refine ⟨⟨algebraMap (OI v) (Fv D.host.F v) (ϖ ^ N) * adjCo φ S T (frCo φ βS) (frCo φ βT) x i j, ?_⟩, rfl⟩
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul]
    refine (mul_le_mul_left hN2 _).trans ?_
    rw [← Valuation.map_mul, mul_right_comm, Valuation.map_mul, map_inv₀]
    exact mul_inv_le_one_of_le₀ h3 zero_le'

end GlobalTheory.DownLift.GenSplit.SupportBound

end
end

