module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1725
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1320
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1700
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1568
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1554
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1551
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1542
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1738
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1585
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBijectionRightInverse
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1737
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1734
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1735
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2ATransportGramTranspose
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.WeilL2Transport

theorem l2A_transport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
    ∃ μ : @MeasureTheory.Measure (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧
      ∀ p, ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, GlobalTheory.WeilL2Words.l2A D.host.F μ (om p Φ) = GlobalTheory.WeilL2Words.l2A D.host.F μ Φ := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ _ co hrat ω hω om hom
  refine GlobalTheory.WeilL2Isometry.l2A_eq_of_isUnitaryOn D.host.F κ om ?_
    (_root_.GlobalTheory.WeilUnitaryTransport.isUnitaryOn_transport D ψ hψ S T χS χT hS hT rS rT JA JB ξ hA hB κ co hrat ω hω om hom)
  rintro ⟨a, b⟩ Φ hΦ
  obtain ⟨g, h, hh, hg⟩ := _root_.GlobalTheory.WeilPairPartner.pair_partner D S T JA JB ξ hA hB a b
  exact (hom a b g h hh hg Φ hΦ).1

end GlobalTheory.WeilL2Transport

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviConjScalarIdeleUnipotentCoordinates
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
open Formalism.UG (cT bc)
open GlobalTheory.ResidueEisenstein.ModConj

noncomputable section

namespace GlobalTheory.ResidueEisenstein.LeviConj

open GlobalTheory.SphEis GlobalTheory.SphEis.UnipCrd

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cT_smul' (s : AF F ⊗[F] E →+* AF F ⊗[F] E) {p q : Type} (a : AF F ⊗[F] E) (M : Matrix p q (AF F ⊗[F] E)) :
    cT s (a • M) = s a • cT s M := by
  ext i k; simp [cT]

theorem det_conj_mul_det (s : AF F ⊗[F] E →+* AF F ⊗[F] E) {k : ℕ} (M K : Matrix (Fin k) (Fin k) (AF F ⊗[F] E))
    (hK : IsUnit K.det) (h : cT s M * K * M = K) : s M.det * M.det = 1 := by
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul] at hd
  have e : (cT s M).det = s M.det := by
    rw [cT, Matrix.det_transpose]; exact (RingHom.map_det s M).symm
  rw [e] at hd
  apply hK.mul_right_cancel
  rw [one_mul]; nth_rewrite 2 [← hd]; ring


open GlobalTheory.SphEis.UnipCrd in
theorem crd_conj_scalar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), GlobalTheory.SphEis.Fr σ J C D Z J₀ → ∀ (g : GAd σ J) (l : (AF F ⊗[F] E)ˣ) (γ : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), (matHom _ σ J g).1 * adMat F C = (l : AF F ⊗[F] E) • adMat F C → (matHom _ σ J g).1 * adMat F D = adMat F D * γ → ∃ δ : GL (Fin m) (AF F ⊗[F] E), absE F E (Matrix.GeneralLinearGroup.det δ) = 1 ∧ δ.1 * adMat F J₀⁻¹ * cT (sigR (AF F) σ) δ.1 = adMat F J₀⁻¹ ∧ ∀ u b c, GlobalTheory.SphEis.Crd σ J C D Z J₀ u b c → GlobalTheory.SphEis.Crd σ J C D Z J₀ (g * u * g⁻¹) ((l : AF F ⊗[F] E) • (b * δ.1)) (((l : AF F ⊗[F] E) * sigR (AF F) σ (l : AF F ⊗[F] E)) • c) := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF g l γ hC hD
  set s := sigR (AF F) σ with hs
  set G := (matHom _ σ J g).1 with hG
  have hU : cT s G * adMat F J * G = adMat F J := g.2
  have pres : ∀ {p q : ℕ} (X : Matrix (Fin n) (Fin p) (AF F ⊗[F] E)) (Y : Matrix (Fin n) (Fin q) (AF F ⊗[F] E)),
      cT s (G * X) * adMat F J * (G * Y) = cT s X * adMat F J * Y := by
    intro p q X Y
    rw [Formalism.UG.cT_mul]
    calc cT s X * cT s G * adMat F J * (G * Y) = cT s X * (cT s G * adMat F J * G) * Y := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU]
  have g0 : ∀ {p q : ℕ} (X : Matrix (Fin n) (Fin p) E) (Y : Matrix (Fin n) (Fin q) E), cT (σ : E →+* E) X * J * Y = 0 →
      cT s (adMat F X) * adMat F J * adMat F Y = 0 := by
    intro p q X Y h; have := gr_adMat (F := F) σ J X Y; rw [h] at this; simpa [gr] using this
  have hcd : cT s (adMat F C) * adMat F J * adMat F D = 1 := by
    have := gr_adMat (F := F) σ J C D; rw [hF.cd] at this; simpa [gr] using this
  have hzz : cT s (adMat F Z) * adMat F J * adMat F Z = adMat F J₀ := by
    have := gr_adMat (F := F) σ J Z Z; rw [hF.zz] at this; simpa [gr] using this
  have hcz := g0 C Z hF.cz
  have hdz := g0 D Z hF.dz
  have linv : (l : AF F ⊗[F] E) * ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = 1 := Units.mul_inv l
  have sinv : s (l : AF F ⊗[F] E) * s ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = 1 := by rw [← map_mul, linv, map_one]
  have ssl : ∀ x, s (s x) = x := sigR_invol σ hF.cm

  have hγ : γ = s ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • 1 := by
    have e := pres (adMat F C) (adMat F D)
    rw [hC, hD, hcd, GlobalTheory.ResidueEisenstein.LeviConj.cT_smul', Matrix.smul_mul, Matrix.smul_mul, ← Matrix.mul_assoc, hcd,
      Matrix.one_mul] at e
    calc γ = (s ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * s (l : AF F ⊗[F] E)) • γ := by rw [mul_comm, sinv, one_smul]
      _ = _ := by rw [← smul_smul, e]

  have hcgz : cT s (adMat F C) * adMat F J * (G * adMat F Z) = 0 := by
    have e := pres (adMat F C) (adMat F Z)
    rw [hC, hcz, GlobalTheory.ResidueEisenstein.LeviConj.cT_smul', Matrix.smul_mul, Matrix.smul_mul] at e
    calc _ = (s ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * s (l : AF F ⊗[F] E)) •
          (cT s (adMat F C) * adMat F J * (G * adMat F Z)) := by rw [mul_comm, sinv, one_smul]
      _ = 0 := by rw [← smul_smul, e, smul_zero]
  have cTγ : cT s γ = ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • 1 := by
    rw [hγ, GlobalTheory.ResidueEisenstein.LeviConj.cT_smul', ssl, Formalism.UG.cT_one]
  have hdgz : cT s (adMat F D) * adMat F J * (G * adMat F Z) = 0 := by
    have e := pres (adMat F D) (adMat F Z)
    rw [hD, hdz, Formalism.UG.cT_mul, cTγ, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.smul_mul] at e
    calc _ = ((l : AF F ⊗[F] E) * ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E)) •
          (cT s (adMat F D) * adMat F J * (G * adMat F Z)) := by rw [linv, one_smul]
      _ = 0 := by rw [← smul_smul, e, smul_zero]
  have hsum : adMat F C * (cT s (adMat F D) * adMat F J) + adMat F Z * (adMat F J₀⁻¹ * (cT s (adMat F Z) * adMat F J))
      + adMat F D * (cT s (adMat F C) * adMat F J) = 1 := by
    have := congrArg (fun M => adMat F M) hF.sum
    simp only [adMat, Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at this
    rw [cT_adMat, cT_adMat, cT_adMat]
    simpa only [adMat] using this
  obtain ⟨δ₀, hδ₀⟩ : ∃ X, X = adMat F J₀⁻¹ * (cT s (adMat F Z) * adMat F J * (G * adMat F Z)) := ⟨_, rfl⟩
  have hGZ : G * adMat F Z = adMat F Z * δ₀ := by
    calc G * adMat F Z = (adMat F C * (cT s (adMat F D) * adMat F J) + adMat F Z * (adMat F J₀⁻¹ * (cT s (adMat F Z) * adMat F J))
      + adMat F D * (cT s (adMat F C) * adMat F J)) * (G * adMat F Z) := by rw [hsum, Matrix.one_mul]
      _ = _ := by
        simp only [Matrix.add_mul, Matrix.mul_assoc]
        simp only [← Matrix.mul_assoc (cT s (adMat F D)), ← Matrix.mul_assoc (cT s (adMat F C)),
          ← Matrix.mul_assoc (cT s (adMat F Z))]
        rw [hdgz, hcgz, Matrix.mul_zero, Matrix.mul_zero, zero_add, add_zero, hδ₀]
  have hδu : cT s δ₀ * adMat F J₀ * δ₀ = adMat F J₀ := by
    have e := pres (adMat F Z) (adMat F Z)
    rw [hGZ, hzz, Formalism.UG.cT_mul] at e
    calc cT s δ₀ * adMat F J₀ * δ₀ = cT s δ₀ * (cT s (adMat F Z) * adMat F J * adMat F Z) * δ₀ := by rw [hzz]
      _ = _ := by rw [← e]; simp only [Matrix.mul_assoc]

  have hu0 : IsUnit J₀.det := isUnit_iff_ne_zero.mpr hF.herm₀.2
  have jj : adMat F J₀⁻¹ * adMat F J₀ = 1 := by
    rw [adMat, adMat, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hu0, Matrix.map_one _ (map_zero _) (map_one _)]
  have jj' : adMat F J₀ * adMat F J₀⁻¹ = 1 := by
    rw [adMat, adMat, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hu0, Matrix.map_one _ (map_zero _) (map_one _)]
  have hJ0 : cT s (adMat F J₀) = adMat F J₀ := by
    rw [cT_adMat]; congr 1; ext i k; simp [Formalism.UG.cT, hF.herm₀.1]
  have hJ0i : cT s (adMat F J₀⁻¹) = adMat F J₀⁻¹ := by
    rw [cT_adMat, cT_inv_herm σ J₀ hF.herm₀]
  have hK : IsUnit (adMat F J₀).det := by
    rw [show (adMat F J₀).det = inclR (F := F) (AF F) J₀.det from (RingHom.map_det _ _).symm]; exact hu0.map _
  obtain ⟨δi, hδi⟩ : ∃ X, X = adMat F J₀⁻¹ * cT s δ₀ * adMat F J₀ := ⟨_, rfl⟩
  have hl : δi * δ₀ = 1 := by
    rw [hδi, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT s δ₀), hδu, jj]
  have hr : δ₀ * δi = 1 := mul_eq_one_comm.mp hl
  let δ : GL (Fin m) (AF F ⊗[F] E) := ⟨δi, δ₀, hl, hr⟩
  have hδval : δ.1 = δi := rfl
  have hiu : cT s δi * adMat F J₀ * δi = adMat F J₀ := by
    calc cT s δi * adMat F J₀ * δi = cT s δi * (cT s δ₀ * adMat F J₀ * δ₀) * δi := by rw [hδu]
      _ = cT s (δ₀ * δi) * adMat F J₀ * (δ₀ * δi) := by rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hr, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  have cTδi : cT s δi = adMat F J₀ * δ₀ * adMat F J₀⁻¹ := by
    rw [hδi, Formalism.UG.cT_mul, Formalism.UG.cT_mul, hJ0, hJ0i, cT_cT σ hF.cm, Matrix.mul_assoc]
  have key : δ₀ * adMat F J₀⁻¹ = adMat F J₀⁻¹ * cT s δi := by
    rw [cTδi, ← Matrix.mul_assoc, ← Matrix.mul_assoc, jj, Matrix.one_mul]
  refine ⟨δ, ?_, ?_, ?_⟩
  · have h1 := GlobalTheory.ResidueEisenstein.LeviConj.det_conj_mul_det s δi (adMat F J₀) hK hiu
    have hu : GlobalTheory.Doubling.conjUnit σ (Matrix.GeneralLinearGroup.det δ) * Matrix.GeneralLinearGroup.det δ = 1 := by
      ext
      show sigR (AF F) σ _ * _ = 1
      exact h1
    have h2 := congrArg (absE F E) hu
    rw [map_mul, GlobalTheory.Doubling.absE_conjUnit, map_one, ← sq] at h2
    exact (pow_eq_one_iff_of_nonneg (by positivity) two_ne_zero).1 h2
  · rw [hδval, Matrix.mul_assoc, ← key, hδi]
    calc adMat F J₀⁻¹ * cT s δ₀ * adMat F J₀ * (δ₀ * adMat F J₀⁻¹)
        = adMat F J₀⁻¹ * (cT s δ₀ * adMat F J₀ * δ₀) * adMat F J₀⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hδu, jj, Matrix.one_mul]
  · intro u b c hu
    set Gi := (matHom _ σ J g⁻¹).1 with hGi
    have hGiG : Gi * G = 1 := by
      rw [hGi, hG, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
    have iC : Gi * adMat F C = ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • adMat F C := by
      have e : adMat F C = ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • (G * adMat F C) := by
        rw [hC, smul_smul, Units.inv_mul, one_smul]
      conv_lhs => rw [e]
      rw [Matrix.mul_smul, ← Matrix.mul_assoc, hGiG, Matrix.one_mul]
    have iZ : Gi * adMat F Z = adMat F Z * δi := by
      have e : adMat F Z = G * adMat F Z * δi := by rw [hGZ, Matrix.mul_assoc, hr, Matrix.mul_one]
      conv_lhs => rw [e]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hGiG, Matrix.one_mul]
    have hGD : G * adMat F D = s ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • adMat F D := by
      rw [hD, hγ, Matrix.mul_smul, Matrix.mul_one]
    have iD : Gi * adMat F D = s (l : AF F ⊗[F] E) • adMat F D := by
      have e : adMat F D = s (l : AF F ⊗[F] E) • (G * adMat F D) := by
        rw [hGD, smul_smul, sinv, one_smul]
      conv_lhs => rw [e]
      rw [Matrix.mul_smul, ← Matrix.mul_assoc, hGiG, Matrix.one_mul]
    have hplus : adMat F Z * GlobalTheory.SphEis.plus σ J₀ ((l : AF F ⊗[F] E) • (b * δi)) =
        s (l : AF F ⊗[F] E) • (G * (adMat F Z * GlobalTheory.SphEis.plus σ J₀ b)) := by
      simp only [GlobalTheory.SphEis.plus]
      rw [GlobalTheory.ResidueEisenstein.LeviConj.cT_smul', Formalism.UG.cT_mul, ← Matrix.mul_assoc G, hGZ, Matrix.mul_smul, Matrix.mul_smul]
      congr 1
      rw [← hs, ← Matrix.mul_assoc (adMat F J₀⁻¹), ← key]; simp only [Matrix.mul_assoc]
    have hm : (matHom _ σ J (g * u * g⁻¹)).1 = G * (matHom _ σ J u).1 * Gi := by
      rw [map_mul, map_mul, Units.val_mul, Units.val_mul]
    refine ⟨?_, ?_, ?_⟩
    · rw [hm]
      calc G * (matHom _ σ J u).1 * Gi * adMat F C
          = ((l⁻¹ : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • (G * ((matHom _ σ J u).1 * adMat F C)) := by
            rw [Matrix.mul_assoc, iC, Matrix.mul_smul, Matrix.mul_assoc]
        _ = adMat F C := by rw [hu.onC, hC, smul_smul, Units.inv_mul, one_smul]
    · rw [hm, hδval]
      calc G * (matHom _ σ J u).1 * Gi * adMat F Z = G * ((matHom _ σ J u).1 * adMat F Z) * δi := by
            rw [Matrix.mul_assoc, iZ, ← Matrix.mul_assoc, Matrix.mul_assoc G]
        _ = _ := by
            rw [hu.onZ, Matrix.mul_add, ← Matrix.mul_assoc G (adMat F C), hGZ, hC, Matrix.add_mul, Matrix.mul_assoc,
              hr, Matrix.mul_one, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
    · rw [hm, hδval, hplus]
      calc G * (matHom _ σ J u).1 * Gi * adMat F D
          = s (l : AF F ⊗[F] E) • (G * ((matHom _ σ J u).1 * adMat F D)) := by
            rw [Matrix.mul_assoc, iD, Matrix.mul_smul, Matrix.mul_assoc]
        _ = s (l : AF F ⊗[F] E) • (G * adMat F D - G * (adMat F Z * GlobalTheory.SphEis.plus σ J₀ b) + G * (adMat F C * c)) := by
            rw [hu.onD, Matrix.mul_add, Matrix.mul_sub]
        _ = _ := by
            rw [hGD, ← Matrix.mul_assoc G (adMat F C), hC]
            simp only [smul_add, smul_sub, smul_smul, sinv, one_smul, Matrix.smul_mul, Matrix.mul_smul]
            rw [mul_comm (s (l : AF F ⊗[F] E))]

end GlobalTheory.ResidueEisenstein.LeviConj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormEqZeroOfKillsProductSchwartzBruhat
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BoxSpan

theorem boxFun_mem_SB' {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] {κ κ' : Type}
    {φ₁ : (κ → k) → ℂ} {φ₂ : (κ' → k) → ℂ} (h₁ : φ₁ ∈ SB (κ → k)) (h₂ : φ₂ ∈ SB (κ' → k)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → k) := by
  have cl : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inl := continuous_pi fun i => continuous_apply _
  have cr : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inr := continuous_pi fun i => continuous_apply _
  refine ⟨(h₁.1.comp_continuous cl).mul (h₂.1.comp_continuous cr), ?_⟩
  let e := (Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ'))
  refine HasCompactSupport.intro ((h₁.2.prod h₂.2).image e.symm.continuous) fun x hx => ?_
  have hx' : e x ∉ tsupport φ₁ ×ˢ tsupport φ₂ := fun h => hx ⟨e x, h, e.symm_apply_apply x⟩
  rw [Homeomorph.sumArrowHomeomorphProdArrow_apply, Set.mem_prod, not_and_or] at hx'
  simp only [boxFun]
  rcases hx' with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

theorem schr_boxFun {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ κ' : Type} [Fintype κ]
    [Fintype κ'] (w : (κ ⊕ κ' → R) × (κ ⊕ κ' → R)) (φ₁ : (κ → R) → ℂ) (φ₂ : (κ' → R) → ℂ) :
    schr ψ w (boxFun φ₁ φ₂) = boxFun (schr ψ (w.1 ∘ Sum.inl, w.2 ∘ Sum.inl) φ₁)
      (schr ψ (w.1 ∘ Sum.inr, w.2 ∘ Sum.inr) φ₂) := by
  funext x
  simp only [schr, boxFun, dotProduct, Fintype.sum_sum_type, Function.comp_apply, Pi.add_apply]
  rw [show (∑ i, x (Sum.inl i) * w.2 (Sum.inl i)) + (∑ i, x (Sum.inr i) * w.2 (Sum.inr i)) +
      ⅟(2 : R) * ((∑ i, w.1 (Sum.inl i) * w.2 (Sum.inl i)) + (∑ i, w.1 (Sum.inr i) * w.2 (Sum.inr i))) =
      ((∑ i, x (Sum.inl i) * w.2 (Sum.inl i)) + ⅟(2 : R) * (∑ i, w.1 (Sum.inl i) * w.2 (Sum.inl i))) +
      ((∑ i, x (Sum.inr i) * w.2 (Sum.inr i)) + ⅟(2 : R) * (∑ i, w.1 (Sum.inr i) * w.2 (Sum.inr i))) by ring,
    AddChar.map_add_eq_mul]
  rw [show (x + w.1) ∘ Sum.inl = x ∘ Sum.inl + w.1 ∘ Sum.inl from rfl,
    show (x + w.1) ∘ Sum.inr = x ∘ Sum.inr + w.1 ∘ Sum.inr from rfl]
  ring

end GlobalTheory.BoxSpan


open GlobalTheory.BoxSpan in
theorem GlobalTheory.BoxSpan.boxSpan_ker : ∀ (F : Type) [Field F] [NumberField F] (v : Pl (F := F)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (ψ : AddChar (Fv F v) ℂ), Continuous ψ → ψ ≠ 1 →
    ∀ Λ : ((κ ⊕ κ' → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
      (∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ' → Fv F v), Λ (boxFun φ₁ φ₂) = 0) → ∀ Φ ∈ SB (κ ⊕ κ' → Fv F v), Λ Φ = 0 := by
  intro F _ _ v κ κ' _ _ ψ hψ h1 Λ hΛ Φ hΦ
  classical
  let N : Submodule ℂ ((κ ⊕ κ' → Fv F v) → ℂ) := Submodule.span ℂ
    {f | ∃ φ₁ ∈ SB (κ → Fv F v), ∃ φ₂ ∈ SB (κ' → Fv F v), f = boxFun φ₁ φ₂}
  have hN : N ≤ SB (κ ⊕ κ' → Fv F v) := by
    refine Submodule.span_le.2 ?_
    rintro f ⟨φ₁, h₁, φ₂, h₂, rfl⟩
    exact boxFun_mem_SB' h₁ h₂
  have hS : ∀ w, ∀ φ ∈ N, schr ψ w φ ∈ N := by
    intro w
    let Lw : ((κ ⊕ κ' → Fv F v) → ℂ) →ₗ[ℂ] ((κ ⊕ κ' → Fv F v) → ℂ) :=
      { toFun := schr ψ w
        map_add' := fun f g => by funext x; simp [schr, mul_add]
        map_smul' := fun c f => by funext x; simp [schr]; ring }
    have : N ≤ N.comap Lw := by
      refine Submodule.span_le.2 ?_
      rintro f ⟨φ₁, h₁, φ₂, h₂, rfl⟩
      show schr ψ w (boxFun φ₁ φ₂) ∈ N
      rw [schr_boxFun]
      exact Submodule.subset_span ⟨_, GlobalTheory.SchrSBFin.schr_mem_SB v ψ hψ _ _ h₁, _,
        GlobalTheory.SchrSBFin.schr_mem_SB v ψ hψ _ _ h₂, rfl⟩
    exact fun φ hφ => this hφ
  let i₁ := Set.indicator {x : κ → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} (1 : (κ → Fv F v) → ℂ)
  let i₂ := Set.indicator {x : κ' → Fv F v | ∀ k, x k ∈ v.adicCompletionIntegers F} (1 : (κ' → Fv F v) → ℂ)
  have h0 : boxFun i₁ i₂ ∈ N := Submodule.subset_span
    ⟨i₁, GlobalTheory.StdVacuum.indicator_mem_SB v, i₂, GlobalTheory.StdVacuum.indicator_mem_SB v, rfl⟩
  have hne : boxFun i₁ i₂ ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [boxFun, i₁, i₂, Set.indicator, zero_mem] at this
  have hall := GlobalTheory.SchrIrred.schr_irreducible v ψ hψ h1 N hN hS _ h0 hne
  have hk : N ≤ LinearMap.ker Λ := by
    refine Submodule.span_le.2 ?_
    rintro f ⟨φ₁, h₁, φ₂, h₂, rfl⟩
    exact hΛ φ₁ h₁ φ₂ h₂
  rw [← hall] at hΦ
  exact hk hΦ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorInverseLocal
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

noncomputable section

namespace GlobalTheory.LocOpInv

theorem pure_mem {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ)
    (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (hSB : ∀ v, φ v ∈ SB (κ → Fv F v))
    (hstd : ∀ᶠ v in cofinite, φ v = stdInd F κ v) : pure f φ ∈ schA F κ :=
  GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd

theorem stdInd_mem_SB_ne {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl (F := F)) :
    stdInd F κ v ∈ SB (κ → Fv F v) ∧ stdInd F κ v ≠ 0 := by
  refine ⟨GlobalTheory.StdVacuum.indicator_mem_SB v, fun h => ?_⟩
  have h0 := congrFun h 0
  rw [stdInd, Set.indicator_of_mem (show (0 : κ → Fv F v) ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}
    from fun i => zero_mem _)] at h0
  exact one_ne_zero h0

theorem isLocOp_inv : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]
    (e : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsLocOp e →
    Set.BijOn e (schA F κ : Set ((κ → AF F) → ℂ)) (schA F κ : Set ((κ → AF F) → ℂ)) →
    ∃ e' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ), IsLocOp e' ∧ ∀ Φ ∈ schA F κ, e' (e Φ) = Φ := by
  classical
  intro F _ _ κ _ e he hbij
  obtain ⟨ei, ev, hSB, hstd, hloc⟩ := he
  have hne : ∀ v, ev v (stdInd F κ v) ≠ 0 := fun v h =>
    (stdInd_mem_SB_ne v).2 (GlobalTheory.T.restricted_tensor_local_operators e ei ev hSB hstd hloc hbij.injOn v _ (stdInd_mem_SB_ne v).1 h)
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.FrechetOpenMapping.schwartz_exists_inverse _ _ ei (GlobalTheory.T.bijective_infinite_part_of_restricted_product e ei ev hSB hstd hloc hbij hne)

  have hbv : ∀ v, Function.Bijective ((ev v).restrict (p := SB (κ → Fv F v)) (q := SB (κ → Fv F v)) (hSB v)) := by
    intro v
    refine ⟨?_, ?_⟩
    · refine (injective_iff_map_eq_zero _).2 fun ψ hψ => ?_
      exact Subtype.ext (GlobalTheory.T.restricted_tensor_local_operators e ei ev hSB hstd hloc hbij.injOn v ψ.1 ψ.2 (congrArg Subtype.val hψ))
    · intro χ
      obtain ⟨ψ, hψ, h⟩ := GlobalTheory.T.local_operators_product_compatible e ei ev hSB hstd hloc hbij.surjOn hne v χ.1 χ.2
      exact ⟨⟨ψ, hψ⟩, Subtype.ext h⟩
  let Lv : ∀ v, SB (κ → Fv F v) ≃ₗ[ℂ] SB (κ → Fv F v) := fun v => LinearEquiv.ofBijective _ (hbv v)
  have hCv : ∀ v, ∃ C : Submodule ℂ ((κ → Fv F v) → ℂ), IsCompl (SB (κ → Fv F v)) C := fun v =>
    Submodule.exists_isCompl _
  choose Cv hCv using hCv
  let ev' : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ := fun v =>
    (SB (κ → Fv F v)).subtype ∘ₗ ((Lv v).symm : SB (κ → Fv F v) →ₗ[ℂ] SB (κ → Fv F v)) ∘ₗ
      Submodule.linearProjOfIsCompl _ _ (hCv v)
  have hev'1 : ∀ v, ∀ ψ (hψ : ψ ∈ SB (κ → Fv F v)), ev' v ψ = ((Lv v).symm ⟨ψ, hψ⟩ : SB _) := by
    intro v ψ hψ
    simp only [ev', LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_coe]
    have hp : Submodule.linearProjOfIsCompl _ _ (hCv v) ψ = ⟨ψ, hψ⟩ :=
      Submodule.linearProjOfIsCompl_apply_left (hCv v) ⟨ψ, hψ⟩
    rw [hp]
  have hev'SB : ∀ v, ∀ ψ ∈ SB (κ → Fv F v), ev' v ψ ∈ SB (κ → Fv F v) := fun v ψ hψ => by
    rw [hev'1 v ψ hψ]; exact Subtype.property _
  have hevev' : ∀ v, ∀ ψ ∈ SB (κ → Fv F v), ev v (ev' v ψ) = ψ := by
    intro v ψ hψ
    rw [hev'1 v ψ hψ]
    have := congrArg Subtype.val ((Lv v).apply_symm_apply ⟨ψ, hψ⟩)
    exact this
  have hev'std : ∀ᶠ v in cofinite, ev' v (stdInd F κ v) = stdInd F κ v := by
    filter_upwards [hstd] with v hv
    have h1 := (stdInd_mem_SB_ne (κ := κ) v).1
    rw [hev'1 v _ h1]
    have : (Lv v) ⟨stdInd F κ v, h1⟩ = ⟨stdInd F κ v, h1⟩ := Subtype.ext hv
    rw [← this, LinearEquiv.symm_apply_apply]

  let Le : schA F κ ≃ₗ[ℂ] schA F κ := LinearEquiv.ofBijective ((e.restrict (p := schA F κ) (q := schA F κ)
    fun Φ hΦ => hbij.mapsTo hΦ)) ⟨fun a b h => Subtype.ext (hbij.injOn a.2 b.2 (congrArg Subtype.val h)), fun b => by
      obtain ⟨a, ha, h⟩ := hbij.surjOn b.2
      exact ⟨⟨a, ha⟩, Subtype.ext h⟩⟩
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (schA F κ)
  let e' : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) :=
    (schA F κ).subtype ∘ₗ (Le.symm : schA F κ →ₗ[ℂ] schA F κ) ∘ₗ Submodule.linearProjOfIsCompl _ _ hC
  have he'e : ∀ Φ ∈ schA F κ, e' (e Φ) = Φ := by
    intro Φ hΦ
    have h1 : e Φ ∈ schA F κ := hbij.mapsTo hΦ
    simp only [e', LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, LinearEquiv.coe_coe]
    have hp : Submodule.linearProjOfIsCompl _ _ hC (e Φ) = ⟨e Φ, h1⟩ :=
      Submodule.linearProjOfIsCompl_apply_left hC ⟨e Φ, h1⟩
    rw [hp]
    have : Le ⟨Φ, hΦ⟩ = ⟨e Φ, h1⟩ := rfl
    rw [← this, LinearEquiv.symm_apply_apply]
  refine ⟨e', ⟨S, ev', hev'SB, hev'std, fun f φ hφ hφs => ?_⟩, he'e⟩
  have hφ' : ∀ v, ev' v (φ v) ∈ SB (κ → Fv F v) := fun v => hev'SB v _ (hφ v)
  have hφ's : ∀ᶠ v in cofinite, ev' v (φ v) = stdInd F κ v := by
    filter_upwards [hφs, hev'std] with v h1 h2
    rw [h1, h2]
  have hΨ : pure (S f) (fun v => ev' v (φ v)) ∈ schA F κ := pure_mem (S f) _ hφ' hφ's
  have hE : e (pure (S f) fun v => ev' v (φ v)) = pure f φ := by
    rw [hloc _ _ hφ' hφ's, hS]
    congr 1
    funext v
    exact hevev' v _ (hφ v)
  rw [← hE, he'e _ hΨ]

end GlobalTheory.LocOpInv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestTypeEqualityOfEvaluationVectorStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowestTypeEquality_of_evaluationVector : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ (U : Subgroup G) χ ξR ω φ, KerDat R i (R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver R (R.mu v) (ownAt D v)) ω φ → ∀ (Λ : GenLat D.host.E (Vc D i).rank) (h : GA D (Vc D i)), SplitOffBad (Vc D i) (badN D * (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M) h → (∀ w, w ∈ Λ.La ↔ (fun b => star (w b)) ∈ Bridge.hLat (Vc D i) (fin (Vc D i) h)) → ∀ (N : ℕ) (x₀ : Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (P : MvPolynomial (LtN (T.Q.Dw ((i : ℕ) + 1)) (Vc D i).rank) T.Q.c.F) (x : U → Fin (Vc D i).rank → (T.Q.Dw ((i : ℕ) + 1)).La) (f : U → (recB hT.p.toLawsCore).Cusp ((i : ℕ) + 1) (κ i)) (y : VsV D i (O i).c'.F), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → Λ.LevOK N (T.dδ ((i : ℕ) + 1) (Vc D i).rank).l₂.M → AdmX (l := T.Q.l) true x₀ → P ∈ harmL (Dw := T.Q.Dw ((i : ℕ) + 1)) T.Q.c Λ (wtA (κ i)) → (∀ u : U, IsRightMul (ℓ u) x₀ (x u) ∧ AdmX (l := T.Q.l) true (x u) ∧ IsShortRule (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.dδ ((i : ℕ) + 1) (Vc D i).rank) Λ N (x u) P ((f u).1 : T.R ((i : ℕ) + 1))) → (O i).io y = MvPolynomial.map (incF T.J.toCore.Q.c (O i).c' (O i).hle) P → ∀ (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) (c : D.what₂.LL), (∀ PP ∈ R.Pg, (y₀ PP).rank = (Wc D i).rank) → ∀ φ', VecOf R i (placesOver R (R.mu v) (ownAt D v)) (omegaFree R i (placesOver R (R.mu v) (ownAt D v)) ξR y₀) φ' → ∀ u : U, (∀ w₀ : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, (∀ ρ, ((w₀ ρ : (R.MW i (sg0 D A)).sm ρ)) = v₀ i (sg0 D A) ρ) → adForm R i (cuspTo hT.p fw i (f u)) (fun ρ => w₀ ρ) = D.what₂.embLL c • actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u : G)⁻¹)) (singleSeries R i ω φ' h ((O i).c0' y) w₀)) → ∀ w : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ, adForm R i (cuspTo hT.p fw i (f u)) (fun ρ => w ρ) = D.what₂.embLL c • actL (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG ((u : G)⁻¹)) (singleSeries R i ω φ' h ((O i).c0' y) w) := by
  first | exact @GlobalTheory.EvalLowType.lowType_of_eval | exact GlobalTheory.EvalLowType.lowType_of_eval | (intros; apply GlobalTheory.EvalLowType.lowType_of_eval <;> assumption)
end

