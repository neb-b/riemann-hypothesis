module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinPlace
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0035
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0030
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuBesselLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocalL2AllOfDictionary
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EquivPf

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinAt
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.MainNotions.S.Pv.Frames Formalism.L2.S.Pv.AmpNZTie
open Formalism.BasicNotions Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ) (hB : WuBessel C)

def fcAt (u u' : D.what₂.Word) (τ : D.what₂.Tau) (a b : X.B.H (vOf X τ)) (ξ : X.Vloc u (vOf X τ))
    (ξ' : X.Vloc u' (vOf X τ)) (c : ℂ) (g : Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS) :
    X.Vloc u' (vOf X τ) →L[ℂ] X.Vloc u (vOf X τ) :=
  Formalism.L2.SG.Pf.CarrierT.coef0 X C u u' τ a b ξ ξ' c
    (torS (muT D) D.R.k D.R.rS * g * torS (muT D)⁻¹ D.R.k D.R.rS)

theorem gStd_eq (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    gStd (kaB D) (gB C τ γ) = trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) γ := by
  unfold Qc Qic Qcs Qics
  rw [pl_vOf, ← torS_conj]
  simp only [gB, trG, Matrix.mul_assoc]

theorem measurable_trG {τ : D.what₂.Tau} {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ} (h2 : Q * Qi = 1) :
    Measurable (fun γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) =>
      (Matrix.of.symm (trG Q Qi γ) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) :=
  (Formalism.L2.SG.Pf.WuBL.trG_closedEmb' (Formalism.L2.SG.Pf.Choice.n_eq' X) _ h2).measurable

theorem muStd_eq (τ : D.what₂.Tau) (μRv : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))) :
    muStd (kaB D) (muRB C τ μRv) =
      μRv.map (fun x => Matrix.of.symm (trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) x)) := by
  have hQ := (C.isT τ).2.1
  have hQc : Qc X C (vOf X τ) * Qic X C (vOf X τ) = 1 := (transpC X C (vOf X τ)).2.1
  unfold muStd muRB
  rw [← cAE_coe, ← cjE_coe (inv_pos.mpr (kaB_pos D)) one_pos,
    Measure.map_map (cAE D.R.k D.R.rS).measurable (measurable_trG hQ),
    Measure.map_map (cjE (k := D.R.k) (r := D.R.rS) (inv_pos.mpr (kaB_pos D)) one_pos).measurable
      ((cAE D.R.k D.R.rS).measurable.comp (measurable_trG hQ))]
  congr 1
  funext x
  show cjT D.R.k D.R.rS (kaB D)⁻¹ 1 (cA D.R.k D.R.rS (Matrix.of.symm (trG (C.Q τ) (C.Qi τ) x))) = _
  funext i j
  show cj D.R.k D.R.rS (kaB D)⁻¹ 1 (Matrix.of (cA D.R.k D.R.rS (Matrix.of.symm (trG (C.Q τ) (C.Qi τ) x)))) i j = _
  rw [of_cA, ← gStd_eq C τ x]
  rfl

theorem fcAt_eq (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hW : GoodW D τ u u' θ (locW C u u' τ)) (hA : GoodS D (lamD D τ) (locS hB u u' τ))
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u') (a b : X.B.H (vOf X τ)) (ξ : X.Vloc u (vOf X τ))
    (ξ' : X.Vloc u' (vOf X τ)) (c : ℂ) :
    fcAt C u u' τ a b ξ ξ' c = fun g => c • stdF (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT')
      (kaB D) (Formalism.MainNotions.S.Pv.BetaCut.coefM (sigB X (C.Q τ) (C.Qi τ) τ) a b ξ ξ') g := by
  funext g
  unfold fcAt Formalism.L2.SG.Pf.CarrierT.coef0
  rw [torS_conjI]
  rfl

theorem lamPl_ne (cO : ℝ) (scl κ : ℂ) (D : D7) (θ : ℝ) (κ₀ : ENNReal) (hcO : cO ≠ 0) (hscl : scl ≠ 0) (hκ : κ ≠ 0)
    (h0 : κ₀ ≠ 0) (h1 : κ₀ ≠ ⊤) (hk0 : kapN D θ ≠ 0) : lamPl cO scl κ D θ κ₀ ≠ 0 := by
  unfold lamPl
  have hs := tN_toReal_ne D θ κ₀ h0 h1 hk0
  refine inv_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (inv_ne_zero ?_) hscl) hκ) ?_)
  · exact_mod_cast hcO
  · exact_mod_cast hs

theorem pinAt (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hW : GoodW D τ u u' θ (locW C u u' τ)) (hA : GoodS D (lamD D τ) (locS hB u u' τ))
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u') (a b : X.B.H (vOf X τ)) (ξ : X.Vloc u (vOf X τ))
    (ξ' : X.Vloc u' (vOf X τ)) (c : ℂ) (hc0 : c ≠ 0) (κ : ℂ) (hκ : κ ≠ 0)
    (hAmp : ∀ (γ : MatKR D.R.k D.R.rS) (μR νR : Measure (Mt D.R.k D.R.rS)) (ν : Measure (PairSp D.R.k D.R.rS)),
      Formalism.MainNotions.S.Pv.AmpDD.CellData (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT')
        (locW C u u' τ).μG γ μR νR ν →
      OrbInt (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT')
        (Formalism.MainNotions.S.Pv.BetaCut.coefM (sigB X (C.Q τ) (C.Qi τ) τ) a b ξ ξ') γ ν = κ • (locS hB u u' τ).J νR γ)
    (κ₀ : ENNReal) (h0 : κ₀ ≠ 0) (h1 : κ₀ ≠ ⊤) (hN : Formalism.FourierDecayAlt.D.muN D.R.k D.R.rS = haarLie (Nset D.R.k D.R.rS) κ₀)
    (hWc : μWc X C u (vOf X τ) = (C.muW u τ).map (cjT D.R.k D.R.rS (kaB D)⁻¹ 1))
    (hWc' : μWc X C u' (vOf X τ) = (C.muW u' τ).map (cjT D.R.k D.R.rS (kaB D)⁻¹ 1))
    (hcO : cOf hB u τ ≠ 0) (hscl : sclOf hB u u' τ ≠ 0)
    (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ))))
    (νB : Measure (PairSp D.R.k D.R.rS))
    (hcell : Formalism.MainNotions.S.Pv.AmpDD.CellData (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT')
      (locW C u u' τ).μG (gB C τ γ) (muRB C τ μRv) (ν.map (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ)) νB)
    (hG : AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      (innerSL ℂ ((locS hB u u' τ).Φ' (Matrix.of x))).smulRight
        ((locS hB u u' τ).Φ (trG (C.Q τ) (C.Qi τ) γ * Matrix.of x))) (ν.map (Formalism.L2.SG.Pf.LocJEq.Smap C τ γ)))
    (hcut : ∃ θ', Formalism.FourierDecayAlt.D.IsNormCut (baseOf X C u u' (vOf X τ)) (trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) γ)
        (μRv.map (fun x => Matrix.of.symm (trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) x))) θ' ∧
      Integrable (fun p => θ' p • Formalism.FourierDecayAlt.D.orbIntegrand (baseOf X C u u' (vOf X τ))
        (trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) γ) (fcAt C u u' τ a b ξ ξ' c) p)
        (baseOf X C u u' (vOf X τ)).μSS) :
    (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ));
      Jv ν (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) γ) =
      (lamPl (cOf hB u τ) (sclOf hB u u' τ) κ D θ κ₀ * c⁻¹) •
        Formalism.FourierDecayAlt.D.orbJ (baseOf X C u u' (vOf X τ)) (trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) γ)
          (μRv.map (fun x => Matrix.of.symm (trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) x)))
          (fcAt C u u' τ a b ξ ξ' c) := by
  have hk0 : kapN D θ ≠ 0 := Formalism.L2.SG.AmpOrbPf.kapN_ne_zero hW
  have hl := lamPl_ne (cOf hB u τ) (sclOf hB u u' τ) κ D θ κ₀ hcO hscl hκ h0 h1 hk0
  rw [fcAt_eq C hB u u' τ hW hA hT hT' a b ξ ξ' c] at hcut ⊢
  rw [← gStd_eq C τ γ, ← muStd_eq C τ μRv] at hcut ⊢
  obtain ⟨θ', hθ', hint⟩ := hcut
  have hcut' : ∃ θ', Formalism.FourierDecayAlt.D.IsNormCut (baseOf X C u u' (vOf X τ)) (gStd (kaB D) (gB C τ γ))
        (muStd (kaB D) (muRB C τ μRv)) θ' ∧
      Integrable (fun p => θ' p • Formalism.FourierDecayAlt.D.orbIntegrand (baseOf X C u u' (vOf X τ)) (gStd (kaB D) (gB C τ γ))
        (stdF (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') (kaB D)
          (Formalism.MainNotions.S.Pv.BetaCut.coefM (sigB X (C.Q τ) (C.Qi τ) τ) a b ξ ξ')) p)
        (baseOf X C u u' (vOf X τ)).μSS := by
    refine ⟨θ', hθ', ?_⟩
    have h : Integrable (c • (fun p => θ' p • Formalism.FourierDecayAlt.D.orbIntegrand (baseOf X C u u' (vOf X τ)) (gStd (kaB D) (gB C τ γ))
          (stdF (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') (kaB D)
            (Formalism.MainNotions.S.Pv.BetaCut.coefM (sigB X (C.Q τ) (C.Qi τ) τ) a b ξ ξ')) p)) (baseOf X C u u' (vOf X τ)).μSS := by
      refine hint.congr (Filter.Eventually.of_forall fun p => ?_)
      exact (congrArg (fun Y => θ' p • Y) (Formalism.L2.SG.Pf.Carrier.CarPin.orbIntegrand_smul (baseOf X C u u' (vOf X τ))
        (gStd (kaB D) (gB C τ γ)) (stdF (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT')
          (kaB D) (Formalism.MainNotions.S.Pv.BetaCut.coefM (sigB X (C.Q τ) (C.Qi τ) τ) a b ξ ξ')) c p)).trans (smul_comm _ _ _)
    exact (integrable_smul_iff hc0 _).mp h
  have hP := pinPlace C hB u u' τ hW hA hT hT' _ κ hAmp κ₀ h0 h1 hN hWc hWc' γ μRv ν νB hcell hG hcut'
  have hS := Formalism.L2.SG.Pf.Carrier.CarPin.orbJ_smulF (baseOf X C u u' (vOf X τ)) (gStd (kaB D) (gB C τ γ))
    (muStd (kaB D) (muRB C τ μRv)) (stdF (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT')
      (kaB D) (Formalism.MainNotions.S.Pv.BetaCut.coefM (sigB X (C.Q τ) (C.Qi τ) τ) a b ξ ξ')) hc0
  refine Eq.trans ?_ (congrArg (fun Y => (lamPl (cOf hB u τ) (sclOf hB u u' τ) κ D θ κ₀ * c⁻¹) • Y) hS.symm)
  refine Eq.trans ?_ (congrArg (fun Y => (lamPl (cOf hB u τ) (sclOf hB u u' τ) κ D θ κ₀ * c⁻¹) • c • Y) hP.symm)
  have key : ∀ (a b d : ℂ) (Y : X.Vloc u' (vOf X τ) →L[ℂ] X.Vloc u (vOf X τ)), a • b • d • Y = (a * b * d) • Y :=
    fun a b d Y => by rw [smul_smul, smul_smul]
  refine Eq.trans ?_ (key _ _ _ _).symm
  have e1 : lamPl (cOf hB u τ) (sclOf hB u u' τ) κ D θ κ₀ * c⁻¹ * c * (lamPl (cOf hB u τ) (sclOf hB u u' τ) κ D θ κ₀)⁻¹
      = 1 := by field_simp
  rw [e1, one_smul]

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocFactorAll
section
noncomputable section

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.Pf.LocF

open Formalism.MainNotions.S Formalism.L2.SG.Pf.Choice Formalism.L2.SG.Pf.WuDec Formalism.QuantumDeterminants Matrix


variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in
theorem locFactor_all (hD : SDictAll) {D : D7} {X : HidaSetting D} {θ : ℝ} (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D)
    (C : Choice X θ) : LocFactor C :=
  locFactor_of local_continuity_all Formalism.L2.SG.Pf.EquivPf.local_equivalence_all local_reproduction_all (local_l2_all_of_dictionary hD) hG C

theorem local_dictionary_all : SDictAll := by
  intro D X θ C u τ γ
  obtain ⟨h1, h2, hgQ, hcol⟩ := C.isT τ
  have hc : ∀ a : Fin D.R.rS, frS D ^ (D.R.rS - (a : ℕ)) ≠ 0 := fun a => pow_ne_zero _ (frS_ne D)
  have hd : ∀ a : Fin D.R.rS, (star (frS D ^ (D.R.rS - (a : ℕ))))⁻¹ ≠ 0 := fun a => by
    rw [Ne, inv_eq_zero, star_eq_zero]; exact hc a
  have hzB := (Formalism.L2.SG.Pf.zTr C u τ).1
  obtain ⟨-, -, hNg, hHg, hnorm, -⟩ := place_facts X u (vOf X τ)
  have hQQ : ∀ Y : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ,
      C.Qi τ * (C.Q τ * Y) = Y := fun Y => by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  constructor
  · rintro ⟨h', hh', m', hm', hsm⟩
    have hhU : h' ∈ UH (Hpk D.R.k D.R.rS) := hh'.1
    have hmU : m' ∈ UH (Hpk D.R.k D.R.rS) := hm'.1
    set H' := toUJn (C.Q τ * h' * C.Qi τ) (cond_tr h2 hgQ hhU) with hH'
    set M' := toUJn (C.Q τ * m' * C.Qi τ) (cond_tr h2 hgQ hmU) with hM'
    obtain ⟨hfe, hff, hfz⟩ := Formalism.L2.SG.Pf.EquivPf.fix_loc (n_eq' X) (X.B.I.ε (vOf X τ)) (C.Q τ) (C.Qi τ) h1 h2 hgQ
      (fun a => rv X.B.I (vOf X τ) (X.eR a)) (fun a => rv X.B.I (vOf X τ) (X.fR a)) _ _ hc hd
      (fun a => (hcol a a rfl).1) (fun a => (hcol a a rfl).2) (rv X.B.I (vOf X τ) (X.zR u)) hh'
    have hHfix : H' ∈ Hfix X u (vOf X τ) := ⟨hfe, hff, hfz⟩
    have hMN : M' ∈ Nloc X u (vOf X τ) :=
      Formalism.L2.SG.Pf.EquivPf.inN_loc (n_eq' X) (X.B.I.ε (vOf X τ)) (C.Q τ) (C.Qi τ) h1 h2 hgQ (fun a => rv X.B.I (vOf X τ) (X.eR a)) _ hc
        (fun a => (hcol a a rfl).1) (rv X.B.I (vOf X τ) (X.zR u)) hzB hm'
    have hγ : γ = H' * M' := by
      apply Subtype.ext; apply Units.ext
      show uMat γ = uMat H' * uMat M'
      rw [uMat_toUJn, uMat_toUJn]
      have : uMat γ = C.Q τ * (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) γ) * C.Qi τ := by
        show uMat γ = C.Q τ * (C.Qi τ * uMat γ * C.Q τ) * C.Qi τ
        simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
        rw [Matrix.mul_assoc, h2, Matrix.mul_one]
      rw [this, hsm]
      simp only [← Matrix.mul_assoc]
      rw [Matrix.mul_assoc (C.Q τ * h') (C.Qi τ) (C.Q τ), h1, Matrix.mul_one]
    refine ⟨H' * M' * H'⁻¹, hnorm H' hHfix M' hMN, H', ?_, ?_⟩
    · rw [Hloc_eq]; exact hHfix
    · rw [hγ]; group
  · rintro ⟨m, hm, h, hh, rfl⟩
    rw [Hloc_eq] at hh
    have hhi : h⁻¹ ∈ Hfix X u (vOf X τ) := hHg.2.2 h hh
    have hm2 : h⁻¹ * m * h ∈ Nloc X u (vOf X τ) := by
      have := hnorm h⁻¹ hhi m hm
      rwa [inv_inv] at this
    obtain ⟨hhe, hhf, hhz⟩ := hh
    have hUW := Formalism.L2.SG.Pf.EquivPf.uw_loc (n_eq' X) (X.B.I.ε (vOf X τ)) (C.Q τ) (C.Qi τ) h1 h2 hgQ
      (fun a => rv X.B.I (vOf X τ) (X.eR a)) (fun a => rv X.B.I (vOf X τ) (X.fR a)) _ _
      (fun a => (hcol a a rfl).1) (fun a => (hcol a a rfl).2) (rv X.B.I (vOf X τ) (X.zR u)) h.2 hhe hhf hhz
    have hNs := Formalism.L2.SG.Pf.EquivPf.nset_loc (n_eq' X) (X.B.I.ε (vOf X τ)) (C.Q τ) (C.Qi τ) h1 h2 hgQ
      (fun a => rv X.B.I (vOf X τ) (X.eR a)) _ hc (fun a => (hcol a a rfl).1) (rv X.B.I (vOf X τ) (X.zR u)) (h⁻¹ * m * h).2 hm2
    refine ⟨_, hUW, _, hNs, ?_⟩
    show C.Qi τ * uMat (m * h) * C.Q τ = C.Qi τ * uMat h * C.Q τ * (C.Qi τ * uMat (h⁻¹ * m * h) * C.Q τ)
    have e3 : m * h = h * (h⁻¹ * m * h) := by group
    rw [e3, Formalism.L2.SG.WuDecayPf.uMat_mul' h]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc (C.Qi τ * uMat h) (C.Q τ) (C.Qi τ), h2, Matrix.mul_one]


variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in
theorem locFactor_holds {D : D7} {X : HidaSetting D} {θ : ℝ} (hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D)
    (C : Choice X θ) : LocFactor C :=
  locFactor_all local_dictionary_all hG C

end Formalism.L2.SG.Pf.LocF
end
end

