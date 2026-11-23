module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0038
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0010
public import Formalism.PeriodIntegrals.Bundle0016
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0058
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.CoefWeightedLocHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.SettingExistsOfGap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocUniqGen
public import Formalism.LocalToGlobal.SiegelLatticeTheory.BesselDiscreteSeries.DecInfPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocScalarPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.HaarCompactGrowth.IsHaarOnUWsetOfIsHaarOnOfUnivEqOne
public import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocFactorCR
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.Choice
open scoped InnerProductSpace ENNReal
open Matrix

namespace Formalism.L2.SG.Pf.LocF

section Gen

open Classical

variable {k r : ℕ}

def toUJn {n : ℕ} {ε : Fin n → Bool} (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε) : Formalism.REAL.UJ ε :=
  ⟨⟨M, Formalism.REAL.Jm ε * Mᴴ * Formalism.REAL.Jm ε,
    (mul_eq_one_comm_of_card_eq (Fin n) (Fin n) ℂ rfl).mp (by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hM, Formalism.REAL.Jm_mul_self]),
    by rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Mᴴ, hM, Formalism.REAL.Jm_mul_self]⟩, hM⟩

theorem uMat_toUJn {n : ℕ} {ε : Fin n → Bool} (M : Matrix (Fin n) (Fin n) ℂ)
    (hM : Mᴴ * Formalism.REAL.Jm ε * M = Formalism.REAL.Jm ε) : uMat (toUJn M hM) = M := rfl

theorem cond_tr {n : ℕ} {ε : Fin n → Bool} {Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} (h2 : Q * Qi = 1) (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.QuantumDeterminants.Hpk k r)
    {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hm : m ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    (Q * m * Qi)ᴴ * Formalism.REAL.Jm ε * (Q * m * Qi) = Formalism.REAL.Jm ε := by
  have hm' : mᴴ * Formalism.QuantumDeterminants.Hpk k r * m = Formalism.QuantumDeterminants.Hpk k r := hm
  have hq := qiHqi ε h2 hg
  calc (Q * m * Qi)ᴴ * Formalism.REAL.Jm ε * (Q * m * Qi) = Qiᴴ * (mᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * m) * Qi := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [hg, hm', hq]

def wTg {n : ℕ} {ε : Fin n → Bool} {V : Type} [Zero V] (Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ)
    (Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ) (W : Formalism.REAL.UJ ε → V)
    (m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : V :=
  if h : ∃ γ : Formalism.REAL.UJ ε, uMat γ = Q * m * Qi then W h.choose else 0

theorem wTg_eq {n : ℕ} {ε : Fin n → Bool} {V : Type} [Zero V] {Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} (W : Formalism.REAL.UJ ε → V)
    {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (γ : Formalism.REAL.UJ ε) (hγ : uMat γ = Q * m * Qi) :
    wTg Q Qi W m = W γ := by
  have hex : ∃ γ : Formalism.REAL.UJ ε, uMat γ = Q * m * Qi := ⟨γ, hγ⟩
  unfold wTg
  rw [dite_eq_left hex]
  congr 1
  apply Subtype.ext; apply Units.ext
  exact hex.choose_spec.trans hγ.symm

theorem continuousOn_wTg {n : ℕ} {ε : Fin n → Bool} {V : Type} [TopologicalSpace V] [Zero V]
    {Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ} {Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} (h2 : Q * Qi = 1)
    (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.QuantumDeterminants.Hpk k r) {W : Formalism.REAL.UJ ε → V} (hW : Continuous W) :
    ContinuousOn (wTg Q Qi W) (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) := by
  rw [continuousOn_iff_continuous_domRestrict]
  set G : Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) → Formalism.REAL.UJ ε := fun p => toUJn (Q * p.1 * Qi) (cond_tr h2 hg p.2)
  have hG : Continuous G := by
    apply Continuous.subtype_mk
    rw [Units.continuous_iff]
    constructor
    · show Continuous fun p : Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) => Q * p.1 * Qi
      exact (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
    · show Continuous fun p : Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) =>
        Formalism.REAL.Jm ε * (Q * p.1 * Qi)ᴴ * Formalism.REAL.Jm ε
      exact (continuous_const.matrix_mul (((continuous_const.matrix_mul continuous_subtype_val).matrix_mul
        continuous_const).matrix_conjTranspose)).matrix_mul continuous_const
  have : (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)).domRestrict (wTg Q Qi W) = W ∘ G := by
    funext p
    show wTg Q Qi W p.1 = W (G p)
    exact wTg_eq W (G p) (uMat_toUJn _ _)
  rw [this]
  exact hW.comp hG

end Gen

section Rep

open Classical Formalism.L2.SG.Pf.WFL

variable {k r : ℕ}

theorem reprod_gen {n : ℕ} (hn : n = 2 * r + k + 1) (ε : Fin n → Bool) {Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ}
    {Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} (h1 : Qi * Q = 1) (h2 : Q * Qi = 1)
    (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.QuantumDeterminants.Hpk k r)
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H)
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (W : Formalism.REAL.UJ ε → V)
    (hWr : ∀ x, Integrable (fun g => (((fdegOf (Formalism.REAL.muG ε) σ w : ℝ) : ℂ) * star ⟪w, σ (uMat g) w⟫_ℂ) •
        W (x * g)) (Formalism.REAL.muG ε) ∧
      ∫ g, (((fdegOf (Formalism.REAL.muG ε) σ w : ℝ) : ℂ) * star ⟪w, σ (uMat g) w⟫_ℂ) • W (x * g)
        ∂(Formalism.REAL.muG ε) = W x) :
    ∀ x' ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r),
      Integrable (fun g : Formalism.QuantumDeterminants.Mt k r =>
        eFun ((Formalism.REAL.muG ε).map (fun γ => Matrix.of.symm (Formalism.L2.SG.RealObj.trG Q Qi γ))) (fun M => σ (Q * M * Qi)) w
          (Matrix.of g) • wTg Q Qi W (x' * Matrix.of g))
        ((Formalism.REAL.muG ε).map (fun γ => Matrix.of.symm (Formalism.L2.SG.RealObj.trG Q Qi γ))) ∧
      rconv ((Formalism.REAL.muG ε).map (fun γ => Matrix.of.symm (Formalism.L2.SG.RealObj.trG Q Qi γ)))
        (eFun ((Formalism.REAL.muG ε).map (fun γ => Matrix.of.symm (Formalism.L2.SG.RealObj.trG Q Qi γ))) (fun M => σ (Q * M * Qi)) w)
        (wTg Q Qi W) x' = wTg Q Qi W x' := by
  subst hn
  have hCP : CayPair ε Q Qi := ⟨hg, qi_eq rfl ε h2 hg⟩
  have hmap : (fun γ : Formalism.REAL.UJ ε => Matrix.of.symm (Formalism.L2.SG.RealObj.trG Q Qi γ)) = cM Qi Q := rfl
  rw [hmap]
  intro x' hx'
  set x : Formalism.REAL.UJ ε := toUJn (Q * x' * Qi) (cond_tr h2 hg hx') with hxdef
  have hx'eq : (Matrix.of (cM Qi Q x) : Matrix _ _ ℂ) = x' := by
    show Qi * uMat x * Q = x'
    rw [uMat_toUJn]
    simp only [← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have hWc : ∀ γ : Formalism.REAL.UJ ε, wTg Q Qi W (Matrix.of (cM Qi Q γ)) = W γ := by
    intro γ
    refine wTg_eq W γ ?_
    show uMat γ = Q * (Qi * uMat γ * Q) * Qi
    simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
    rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  obtain ⟨hint, hval⟩ := hWr x
  have embG := cM_measEmb (ε := ε) (A := Qi) (B := Q) (A' := Q) (B' := Qi) h2 h2
  have hfd := fdegH_map hCP σ w
  have hσg : ∀ g : Formalism.REAL.UJ ε, σ (Q * (Matrix.of (cM Qi Q g) : Matrix _ _ ℂ) * Qi) = σ (uMat g) := by
    intro g
    show σ (Q * (Qi * uMat g * Q) * Qi) = σ (uMat g)
    congr 1; simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]; rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  have hprod : ∀ g : Formalism.REAL.UJ ε, (Matrix.of (cM Qi Q x) : Matrix _ _ ℂ) * Matrix.of (cM Qi Q g) =
      Matrix.of (cM Qi Q (x * g)) := fun g => cMprod hCP _ x g
  have hpt : ∀ g : Formalism.REAL.UJ ε, eFun ((Formalism.REAL.muG ε).map (cM Qi Q)) (fun M => σ (Q * M * Qi)) w
      (Matrix.of (cM Qi Q g)) • wTg Q Qi W (x' * Matrix.of (cM Qi Q g)) =
      (((fdegOf (Formalism.REAL.muG ε) σ w : ℝ) : ℂ) * star ⟪w, σ (uMat g) w⟫_ℂ) • W (x * g) := by
    intro g
    simp only [eFun]
    rw [hfd, hσg, ← hx'eq, hprod, hWc]
  refine ⟨?_, ?_⟩
  · exact embG.integrable_map_iff.mpr (hint.congr (ae_of_all _ fun g => (hpt g).symm))
  · unfold rconv
    rw [embG.integral_map, integral_congr_ae (ae_of_all _ hpt), hval, ← hx'eq, hWc]

end Rep

section Steps

variable {D : D7} {X : HidaSetting D} {θ : ℝ}

theorem local_continuity_all : ContAll := by
  intro D X θ C u τ
  exact continuousOn_wTg (C.isT τ).2.1 (C.isT τ).2.2.1 (X.Wloc_cont u _)


variable [Fact Formalism.L2.SG.SplitPrimeNormLemmas.CoefWeightedLoc] in
theorem local_reproduction_all : ReprodAll := by
  intro D hG X θ C u τ
  obtain ⟨μS, νl, Cc, hQ⟩ := Formalism.L2.SG.Pf.WuDec.quotAll_of Formalism.L2.SG.Closed.QuotProdK_holds
    Formalism.L2.SG.Pf.WFL.locHNProps_holds Formalism.L2.SG.Closed.NUnimodLoc_holds D X u
  have hR := Formalism.L2.SG.Pf.WuDec.locReprodStep_of Formalism.L2.SG.Pf.WuDec.local_scalar_reduction D hG X u μS νl Cc hQ (vOf X τ)
  exact reprod_gen (n_eq' X) (X.B.I.ε (vOf X τ)) (C.isT τ).1 (C.isT τ).2.1 (C.isT τ).2.2.1 (X.B.σ (vOf X τ))
    (X.B.w (vOf X τ)) (X.Wloc u (vOf X τ)) hR

end Steps

end Formalism.L2.SG.Pf.LocF
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.MuNEqHaarLie
section
noncomputable section

open Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.MainNotions.S.Pv.Frames

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

variable {k r : ℕ}

theorem torS_eq (δ : ℝ) :
    Formalism.L2.SG.LocWSOf.torS (-Complex.I * (δ : ℂ)) k r = (Complex.I ^ r)⁻¹ • (tT k r * dM k r δ 1) := by
  unfold Formalism.L2.SG.LocWSOf.torS tT dM
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
  congr 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  have hI0 : Complex.I ≠ 0 := Complex.I_ne_zero
  by_cases h1 : i.val < r
  · simp only [dT, Formalism.MainNotions.FrameBoundFromBesselTorus.tV, Formalism.MainNotions.FrameBoundFromBesselTorus.tF, h1, if_true, one_mul]
    obtain ⟨n, hn⟩ : ∃ n, r = i.val + n := ⟨r - i.val, by omega⟩
    have hn' : r - i.val = n := by omega
    have hIr : Complex.I ^ r = Complex.I ^ i.val * Complex.I ^ n := by rw [← pow_add, ← hn]
    rw [hn', hIr, ← Complex.inv_I]
    push_cast
    field_simp
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hI0)]
  · by_cases h2 : r + k < i.val
    · have h2' : ¬ (i.val ≤ r + k) := by omega
      simp only [dT, Formalism.MainNotions.FrameBoundFromBesselTorus.tV, Formalism.MainNotions.FrameBoundFromBesselTorus.tF, h1, h2, h2', if_true, if_false, one_mul]
      obtain ⟨n, hn⟩ : ∃ n, r = (2 * r + k - i.val) + n := ⟨r - (2 * r + k - i.val), by omega⟩
      have hn' : r - (2 * r + k - i.val) = n := by omega
      have hIr : Complex.I ^ r = Complex.I ^ (2 * r + k - i.val) * Complex.I ^ n := by rw [← pow_add, ← hn]
      rw [hn', hIr]
      simp only [star_pow, star_mul', star_neg, Complex.star_def, Complex.conj_I, Complex.conj_ofReal, neg_neg]
      push_cast
      rw [mul_pow]
      field_simp
    · have h2' : i.val ≤ r + k := by omega
      simp only [dT, Formalism.MainNotions.FrameBoundFromBesselTorus.tV, h1, h2, h2', if_true, if_false]
      push_cast
      rw [mul_one, inv_mul_cancel₀ (pow_ne_zero _ hI0)]

theorem torS_inv_eq (δ : ℝ) (hδ : 0 < δ) :
    Formalism.L2.SG.LocWSOf.torS (-Complex.I * (δ : ℂ))⁻¹ k r = (Complex.I ^ r) • (dMi k r δ 1 * tTi k r) := by
  have hδc : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have hI0 : Complex.I ≠ 0 := Complex.I_ne_zero
  unfold Formalism.L2.SG.LocWSOf.torS tTi dMi
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
  congr 1
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases h1 : i.val < r
  · simp only [dT, Formalism.MainNotions.FrameBoundFromBesselTorus.tV, Formalism.MainNotions.FrameBoundFromBesselTorus.tF, h1, if_true, one_mul]
    obtain ⟨n, hn⟩ : ∃ n, r = i.val + n := ⟨r - i.val, by omega⟩
    have hn' : r - i.val = n := by omega
    have hIr : Complex.I ^ r = Complex.I ^ i.val * Complex.I ^ n := by rw [← pow_add, ← hn]
    rw [hn', hIr, star_pow, Complex.star_def, Complex.conj_I, ← Complex.inv_I]
    push_cast
    field_simp
    rw [div_pow, div_pow, one_pow]
    field_simp
  · by_cases h2 : r + k < i.val
    · have h2' : ¬ (i.val ≤ r + k) := by omega
      simp only [dT, Formalism.MainNotions.FrameBoundFromBesselTorus.tV, Formalism.MainNotions.FrameBoundFromBesselTorus.tF, h1, h2, h2', if_true, if_false, one_mul]
      obtain ⟨n, hn⟩ : ∃ n, r = (2 * r + k - i.val) + n := ⟨r - (2 * r + k - i.val), by omega⟩
      have hn' : r - (2 * r + k - i.val) = n := by omega
      have hIr : Complex.I ^ r = Complex.I ^ (2 * r + k - i.val) * Complex.I ^ n := by rw [← pow_add, ← hn]
      rw [hn', hIr]
      simp only [star_pow, star_inv₀, star_mul', star_neg, Complex.star_def, Complex.conj_I, Complex.conj_ofReal,
        neg_neg, inv_inv]
      rw [← Complex.inv_I]
      push_cast
      rw [inv_pow]
      field_simp
      rw [div_pow, one_pow, mul_pow]
      field_simp
    · have h2' : i.val ≤ r + k := by omega
      simp only [dT, Formalism.MainNotions.FrameBoundFromBesselTorus.tV, h1, h2, h2', if_true, if_false]
      push_cast
      rw [star_pow, Complex.star_def, Complex.conj_I, ← Complex.inv_I]
      field_simp
      rw [div_pow, one_pow]
      field_simp

theorem nLeft_holds : Formalism.MainNotions.MeasFS.NLeft := fun k r κ h0 h1 a ha =>
  (Formalism.MainNotions.BridgeCSB.haarLieN k r κ h0 h1).2.2.2 a ha

theorem muN_eq_haarLie (k r : ℕ) :
    ∃ κ₀ : ENNReal, κ₀ ≠ 0 ∧ κ₀ ≠ ⊤ ∧ Formalism.FourierDecayAlt.D.muN k r = haarLie (Nset k r) κ₀ := by
  have hH := Formalism.MainNotions.MeasFS.haar_lie_measure_on_nilpotent (k := k) (r := r) nLeft_holds 1 one_ne_zero ENNReal.one_ne_top
  have hM := Formalism.FourierDecayAlt.Final.d_muNHaar k r
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r (Nset k r) _ _ (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r) hH
    hM.conc hM.left hM.finite_compact
  refine ⟨(c : ENNReal), fun h => hM.ne_zero ?_, ENNReal.coe_ne_top, ?_⟩
  · rw [hc, ENNReal.coe_eq_zero.mp h, zero_smul]
  · rw [hc, show ((c : ENNReal)) = (c : ENNReal) * 1 from (mul_one _).symm, haarLie_smul, ENNReal.smul_def]

def kaB (D : Formalism.BasicNotions.D7) : ℝ := D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ))

theorem kaB_pos (D : Formalism.BasicNotions.D7) : 0 < kaB D := by
  have hka : 0 < D.host.ka := by
    have hrd : 0 < D.host.rdE := by
      unfold Formalism.BasicNotions.Host.rdE
      exact Real.rpow_pos_of_pos (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero D.host.E)) _
    unfold Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v
    exact div_pos Real.pi_pos (by linarith)
  have hg0 : (0 : ℝ) < D.host.g 0 := by exact_mod_cast (D.host.g_prime 0).pos
  have hg1 : (0 : ℝ) < D.host.g 1 := by exact_mod_cast (D.host.g_prime 1).pos
  exact div_pos hka (mul_pos hg0 hg1)

theorem muT_eq (D : Formalism.BasicNotions.D7) : Formalism.L2.SG.LocWSOf.muT D = -Complex.I * (((kaB D)⁻¹ : ℝ) : ℂ) := by
  have hka : 0 < D.host.ka := by
    have hrd : 0 < D.host.rdE := by
      unfold Formalism.BasicNotions.Host.rdE
      exact Real.rpow_pos_of_pos (abs_pos.mpr (by exact_mod_cast NumberField.discr_ne_zero D.host.E)) _
    unfold Formalism.BasicNotions.Host.ka Formalism.BasicNotions.Host.v
    exact div_pos Real.pi_pos (by linarith)
  have hkac : (D.host.ka : ℂ) ≠ 0 := by exact_mod_cast hka.ne'
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  unfold Formalism.L2.SG.LocWSOf.muT Formalism.L2.SG.LocWSOf.cfS Formalism.L2.SG.LocWSOf.frS kaB
  push_cast
  field_simp

theorem torS_muT (D : Formalism.BasicNotions.D7) (k r : ℕ) :
    Formalism.L2.SG.LocWSOf.torS (Formalism.L2.SG.LocWSOf.muT D) k r = (Complex.I ^ r)⁻¹ • (tT k r * dM k r (kaB D)⁻¹ 1) := by
  rw [muT_eq, torS_eq]

theorem torS_muT_inv (D : Formalism.BasicNotions.D7) (k r : ℕ) :
    Formalism.L2.SG.LocWSOf.torS (Formalism.L2.SG.LocWSOf.muT D)⁻¹ k r = (Complex.I ^ r) • (dMi k r (kaB D)⁻¹ 1 * tTi k r) := by
  rw [muT_eq, torS_inv_eq _ (inv_pos.mpr (kaB_pos D))]

theorem torS_conj (D : Formalism.BasicNotions.D7) (k r : ℕ) (M : Mx k r) :
    Formalism.L2.SG.LocWSOf.torS (Formalism.L2.SG.LocWSOf.muT D)⁻¹ k r * M * Formalism.L2.SG.LocWSOf.torS (Formalism.L2.SG.LocWSOf.muT D) k r =
      gStd (kaB D) M := by
  rw [torS_muT, torS_muT_inv, gStd]
  have hI : (Complex.I ^ r) ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hI, mul_inv_cancel₀ hI, one_smul]
  simp only [cj, Matrix.mul_assoc]

theorem torS_conjI (D : Formalism.BasicNotions.D7) (k r : ℕ) (M : Mx k r) :
    Formalism.L2.SG.LocWSOf.torS (Formalism.L2.SG.LocWSOf.muT D) k r * M * Formalism.L2.SG.LocWSOf.torS (Formalism.L2.SG.LocWSOf.muT D)⁻¹ k r =
      tT k r * cjI k r (kaB D)⁻¹ 1 M * tTi k r := by
  rw [torS_muT, torS_muT_inv]
  have hI : (Complex.I ^ r) ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hI, mul_inv_cancel₀ hI, one_smul]
  simp only [cjI, Matrix.mul_assoc]

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

