module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanCoefficientNonzero.Development
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0025
public import Formalism.FormalDegreeBessel.FormalDegreeRatio.UnitaryWeylNormalHolds
public import Formalism.FormalDegreeBessel.Bundle0002

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanCoefficientNonzero.Factor
section
open MeasureTheory
open scoped InnerProductSpace ENNReal

noncomputable section

namespace PI.BICNZ

open Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.MainNotions.S.Pv.BetaCut

theorem sf_of_haar {k r : ℕ} {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : Formalism.FourierDecayAlt.B.IsHaarOn U μ) : SigmaFinite μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  infer_instance

theorem itD_const_mul (a : ℂ) (f : ℝ → ℂ) (n : ℕ) :
    iteratedDeriv n (fun y => a * f y) = fun y => a * iteratedDeriv n f y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    exact deriv_const_mul_field' a

theorem oneMinusDD_prod (c : ℂ) (f g : ℝ → ℂ) (t₁ t₂ : ℝ) :
    oneMinusDD (fun a b => c * f a * g b) t₁ t₂ =
      c * (f t₁ - iteratedDeriv 2 f t₁) * (g t₂ - iteratedDeriv 2 g t₂) := by
  have e3 : ∀ (K : ℂ) (u : ℝ → ℂ) (t : ℝ), iteratedDeriv 2 (fun x => K * u x) t = K * iteratedDeriv 2 u t := by
    intro K u t
    rw [itD_const_mul]
  have e1 : ∀ x, iteratedDeriv 2 (fun y => c * f x * g y) t₂ = c * f x * iteratedDeriv 2 g t₂ := fun x =>
    e3 (c * f x) g t₂
  have e2 : (fun x => c * f x * g t₂ - iteratedDeriv 2 (fun y => c * f x * g y) t₂) =
      fun x => (c * (g t₂ - iteratedDeriv 2 g t₂)) * f x := by
    funext x
    rw [e1]
    ring
  show (c * f t₁ * g t₂ - iteratedDeriv 2 (fun y => c * f t₁ * g y) t₂) -
    iteratedDeriv 2 (fun x => c * f x * g t₂ - iteratedDeriv 2 (fun y => c * f x * g y) t₂) t₁ = _
  rw [e2, e3, e3]
  ring

theorem chi_eq_zero {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) {t : ℝ} (ht : t ≤ 0) : D.χ t = 0 := by
  by_contra hne
  have hs : t ∈ tsupport D.χ := subset_tsupport _ hne
  have := (D.χ_supp hs).1
  linarith

theorem chi_hasCompactSupport {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) : HasCompactSupport D.χ :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) (D.χ_supp.trans Set.Ioo_subset_Icc_self)

theorem regBracket_eq {k r : ℕ} {Wp Wq H : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (D : RealPlaceData k r Wp Wq) (σ : Mat k r → (H →L[ℂ] H)) (v v' : H) (ξ : Wp) (ξ' : Wq)
    (d : ℝ) (p : SS k r)
    (hΦ : ∀ t : ℝ × ℝ, 0 < t.1 → 0 < t.2 →
      Ph D (coefM σ v v' ξ ξ') (coefM σ v v' ξ ξ') (dilation₂ t p) =
        (d : ℂ)⁻¹ * Lf D σ v ξ (p.1.1, conjM (aDil k r t.1) p.1.2) *
          Rf D σ v' ξ' (p.2.1, conjM (aDil k r t.2) p.2.2)) :
    regBracket D (coefM σ v v' ξ ξ') (coefM σ v v' ξ ξ') p =
      fun a b => (d : ℂ)⁻¹ * H1 D σ v ξ p.1 a * H2 D σ v' ξ' p.2 b := by
  funext a b
  simp only [regBracket, H1, H2]
  by_cases ha : 0 < a
  · by_cases hb : 0 < b
    · have h := hΦ (a, b) ha hb
      dsimp only at h
      rw [h]
      have hk : (a * b) ^ kap k r = a ^ kap k r * b ^ kap k r := by
        first
        | exact mul_pow a b _
        | exact Real.mul_rpow ha.le hb.le
      rw [hk]
      simp only [Complex.ofReal_mul]
      ring
    · have h0 : D.χ b = 0 := chi_eq_zero D (not_lt.mp hb)
      simp [h0]
  · have h0 : D.χ a = 0 := chi_eq_zero D (not_lt.mp ha)
    simp [h0]

theorem hasCompactSupport_left_profile {k r : ℕ} {Wp Wq H : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (D : RealPlaceData k r Wp Wq) (σ : Mat k r → (H →L[ℂ] H)) (v : H) (ξ : Wp) (x : Mt k r × Mt k r) :
    HasCompactSupport (H1 D σ v ξ x) := by
  have h1 : HasCompactSupport (fun t : ℝ => D.χ t * t ^ kap k r) := (chi_hasCompactSupport D).mul_right
  have h2 : HasCompactSupport (fun t : ℝ => ((D.χ t * t ^ kap k r : ℝ) : ℂ)) := h1.comp_left Complex.ofReal_zero
  exact h2.mul_right (f' := fun t : ℝ => Lf D σ v ξ (x.1, conjM (aDil k r t) x.2))

theorem hasCompactSupport_right_profile {k r : ℕ} {Wp Wq H : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (D : RealPlaceData k r Wp Wq) (σ : Mat k r → (H →L[ℂ] H)) (v' : H) (ξ' : Wq) (x : Mt k r × Mt k r) :
    HasCompactSupport (H2 D σ v' ξ' x) := by
  have h1 : HasCompactSupport (fun t : ℝ => D.χ t * t ^ kap k r) := (chi_hasCompactSupport D).mul_right
  have h2 : HasCompactSupport (fun t : ℝ => ((D.χ t * t ^ kap k r : ℝ) : ℂ)) := h1.comp_left Complex.ofReal_zero
  exact h2.mul_right (f' := fun t : ℝ => Rf D σ v' ξ' (x.1, conjM (aDil k r t) x.2))

theorem ae_inSS {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : RealPlaceData k r Wp Wq) :
    ∀ᵐ p ∂((D.μW.prod D.μN).prod (D.μW'.prod D.μN)), D.inSS p := by
  haveI := sf_of_haar D.haarW
  haveI := sf_of_haar D.haarN
  haveI := sf_of_haar D.haarW'
  have hW : ∀ᵐ x ∂D.μW, Matrix.of x ∈ UWset k r D.z := by
    rw [ae_iff]
    exact D.haarW.conc
  have hN : ∀ᵐ x ∂D.μN, Matrix.of x ∈ Nset k r := by
    rw [ae_iff]
    exact D.haarN.conc
  have hW' : ∀ᵐ x ∂D.μW', Matrix.of x ∈ UWset k r D.z' := by
    rw [ae_iff]
    exact D.haarW'.conc
  have h1 : ∀ᵐ q ∂(D.μW.prod D.μN), Matrix.of q.1 ∈ UWset k r D.z ∧ Matrix.of q.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hW).and (Measure.quasiMeasurePreserving_snd.ae hN)
  have h2 : ∀ᵐ q ∂(D.μW'.prod D.μN), Matrix.of q.1 ∈ UWset k r D.z' ∧ Matrix.of q.2 ∈ Nset k r :=
    (Measure.quasiMeasurePreserving_fst.ae hW').and (Measure.quasiMeasurePreserving_snd.ae hN)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae h1, Measure.quasiMeasurePreserving_snd.ae h2]
    with p hp1 hp2
  exact ⟨hp1.1, hp1.2, hp2.1, hp2.2⟩

theorem exp_split (t₁ t₂ a b : ℝ) :
    Complex.exp (Complex.I * (((1 : ℝ) * t₁ * a - (1 : ℝ) * t₂ * b : ℝ) : ℂ)) =
      Complex.exp (Complex.I * ((a * t₁ : ℝ) : ℂ)) * Complex.exp (Complex.I * ((-b * t₂ : ℝ) : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem betaFactor_of (hP : PhiAt) (hL : LeftProfileContDiffTwo) (hR : RightProfileContDiffTwo) : BetaFactor := by
  intro k r Wp Wq _ _ _ _ _ _ D ε lm H _ _ _ σ hHC hDS
  obtain ⟨d, hd, hΦ⟩ := hP k r Wp Wq D ε lm H σ hHC hDS
  refine ⟨d, hd, fun v v' ξ ξ' hv hv' => ?_⟩
  haveI := sf_of_haar D.haarW
  haveI := sf_of_haar D.haarN
  haveI := sf_of_haar D.haarW'
  have hpt : ∀ p : SS k r, D.inSS p →
      ((((1 + (1 : ℝ) ^ 2 * lam k r D.z (Matrix.of p.1.2) ^ 2)⁻¹ *
        (1 + (1 : ℝ) ^ 2 * lam k r D.z' (Matrix.of p.2.2) ^ 2)⁻¹ : ℝ) : ℂ) *
      ∫ t : ℝ × ℝ, oneMinusDD (regBracket D (coefM σ v v' ξ ξ') (coefM σ v v' ξ ξ') p) t.1 t.2 *
        Complex.exp (Complex.I * (((1 : ℝ) * t.1 * lam k r D.z (Matrix.of p.1.2) -
          (1 : ℝ) * t.2 * lam k r D.z' (Matrix.of p.2.2) : ℝ) : ℂ))) =
      (d : ℂ)⁻¹ * I1 D σ v ξ p.1 * I2 D σ v' ξ' p.2 := by
    intro p hp
    set a := lam k r D.z (Matrix.of p.1.2) with ha
    set b := lam k r D.z' (Matrix.of p.2.2) with hb
    have hreg := regBracket_eq D σ v v' ξ ξ' d p (fun t h1 h2 => hΦ v v' ξ ξ' p hp t h1 h2)
    have hA : ContDiff ℝ 2 (H1 D σ v ξ p.1) := hL k r Wp Wq D ε lm H σ hHC hDS v ξ hv p.1 hp.1 hp.2.1
    have hB : ContDiff ℝ 2 (H2 D σ v' ξ' p.2) := hR k r Wp Wq D ε lm H σ hHC hDS v' ξ' hv' p.2 hp.2.2.1 hp.2.2.2
    have iA := Formalism.FourierDecayAlt.P.integration_by_parts_regularised (H1 D σ v ξ p.1) hA (hasCompactSupport_left_profile D σ v ξ p.1) a
    have iB := Formalism.FourierDecayAlt.P.integration_by_parts_regularised (H2 D σ v' ξ' p.2) hB (hasCompactSupport_right_profile D σ v' ξ' p.2) (-b)
    have hsplit : (∫ t : ℝ × ℝ, oneMinusDD (regBracket D (coefM σ v v' ξ ξ') (coefM σ v v' ξ ξ') p) t.1 t.2 *
        Complex.exp (Complex.I * (((1 : ℝ) * t.1 * a - (1 : ℝ) * t.2 * b : ℝ) : ℂ))) =
        (d : ℂ)⁻¹ * ((∫ s : ℝ, (H1 D σ v ξ p.1 s - iteratedDeriv 2 (H1 D σ v ξ p.1) s) *
            Complex.exp (Complex.I * ((a * s : ℝ) : ℂ))) *
          (∫ s : ℝ, (H2 D σ v' ξ' p.2 s - iteratedDeriv 2 (H2 D σ v' ξ' p.2) s) *
            Complex.exp (Complex.I * ((-b * s : ℝ) : ℂ)))) := by
      rw [hreg]
      have e : ∀ t : ℝ × ℝ, oneMinusDD (fun a' b' => (d : ℂ)⁻¹ * H1 D σ v ξ p.1 a' * H2 D σ v' ξ' p.2 b') t.1 t.2 *
          Complex.exp (Complex.I * (((1 : ℝ) * t.1 * a - (1 : ℝ) * t.2 * b : ℝ) : ℂ)) =
          (d : ℂ)⁻¹ * (((H1 D σ v ξ p.1 t.1 - iteratedDeriv 2 (H1 D σ v ξ p.1) t.1) *
              Complex.exp (Complex.I * ((a * t.1 : ℝ) : ℂ))) *
            ((H2 D σ v' ξ' p.2 t.2 - iteratedDeriv 2 (H2 D σ v' ξ' p.2) t.2) *
              Complex.exp (Complex.I * ((-b * t.2 : ℝ) : ℂ)))) := by
        intro t
        rw [oneMinusDD_prod, exp_split]
        ring
      simp_rw [e]
      rw [integral_const_mul, Measure.volume_eq_prod]
      congr 1
      exact integral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (fun s => (H1 D σ v ξ p.1 s - iteratedDeriv 2 (H1 D σ v ξ p.1) s) *
            Complex.exp (Complex.I * ((a * s : ℝ) : ℂ)))
        (fun s => (H2 D σ v' ξ' p.2 s - iteratedDeriv 2 (H2 D σ v' ξ' p.2) s) *
            Complex.exp (Complex.I * ((-b * s : ℝ) : ℂ)))
    rw [hsplit, iA, iB]
    unfold I1 I2
    rw [← ha, ← hb]
    have h1 : (1 + a ^ 2 : ℝ) ≠ 0 := by positivity
    have h2 : (1 + b ^ 2 : ℝ) ≠ 0 := by positivity
    have hw : ((1 + (1 : ℝ) ^ 2 * a ^ 2)⁻¹ * (1 + (1 : ℝ) ^ 2 * b ^ 2)⁻¹) * ((1 + a ^ 2) * (1 + (-b) ^ 2)) = (1 : ℝ) := by
      rw [neg_sq, one_pow, one_mul, one_mul]
      field_simp
    have hw' : ((((1 + (1 : ℝ) ^ 2 * a ^ 2)⁻¹ * (1 + (1 : ℝ) ^ 2 * b ^ 2)⁻¹ : ℝ) : ℂ)) *
        (((1 + a ^ 2 : ℝ) : ℂ) * ((1 + (-b) ^ 2 : ℝ) : ℂ)) = 1 := by
      exact_mod_cast hw
    linear_combination ((d : ℂ)⁻¹ * (∫ t : ℝ, H1 D σ v ξ p.1 t * Complex.exp (Complex.I * ((a * t : ℝ) : ℂ))) *
      (∫ t : ℝ, H2 D σ v' ξ' p.2 t * Complex.exp (Complex.I * ((-b * t : ℝ) : ℂ)))) * hw'
  unfold betaInf betaInfTau RealPlaceData.μSS
  refine (integral_congr_ae (g := fun p : SS k r => (d : ℂ)⁻¹ * (I1 D σ v ξ p.1 * I2 D σ v' ξ' p.2)) ?_).trans ?_
  · filter_upwards [ae_inSS D] with p hp
    rw [← mul_assoc]
    exact hpt p hp
  · rw [integral_const_mul, mul_assoc]
    congr 1
    exact integral_prod_mul (μ := D.μW.prod D.μN) (ν := D.μW'.prod D.μN) (I1 D σ v ξ) (I2 D σ v' ξ')

end PI.BICNZ
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanCoefficientNonzero.InnerInvOfDS
section
open MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace PI.BICNZ

open Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.MainNotions.S.Pv.BetaCut

section rep

variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem rep_of_DS {ε : Fin (2 * r + k + 1) → Bool} {lm : Fin (2 * r + k + 1) → ℝ} {σ : Mat k r → (H →L[ℂ] H)}
    (h : PI.UpqRep.IsDSHpk k r ε lm σ) :
    σ 1 = 1 ∧ (∀ a ∈ UH (Hpk k r), ∀ b ∈ UH (Hpk k r), σ (a * b) = (σ a).comp (σ b)) ∧
      ∀ a ∈ UH (Hpk k r), ∀ v : H, ‖σ a v‖ = ‖v‖ := by
  obtain ⟨P, ⟨⟨_, hPJ⟩, hPU⟩, hDS⟩ := h
  obtain ⟨_, _, ⟨⟨h1, hmul⟩, hiso, _⟩, _⟩ := hDS
  have hsP : P.conjTranspose * P = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hPU
  have hPP : P * P.conjTranspose = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hPU
  have hinv : P⁻¹ = P.conjTranspose := Matrix.inv_eq_left_inv hsP
  have conj : ∀ x : Mat k r, P⁻¹ * (P * x * P.conjTranspose) * P = x := by
    intro x
    rw [hinv]
    calc P.conjTranspose * (P * x * P.conjTranspose) * P = (P.conjTranspose * P) * x * (P.conjTranspose * P) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [hsP, Matrix.one_mul, Matrix.mul_one]
  have hmem : ∀ a ∈ UH (Hpk k r), P * a * P.conjTranspose ∈ PI.UpqRep.UJset ε := by
    intro a ha
    have ha' : a.conjTranspose * Hpk k r * a = Hpk k r := ha
    show (P * a * P.conjTranspose).conjTranspose * PI.UpqRep.Jm ε * (P * a * P.conjTranspose) = PI.UpqRep.Jm ε
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc P * (a.conjTranspose * P.conjTranspose) * PI.UpqRep.Jm ε * (P * a * P.conjTranspose)
        = P * (a.conjTranspose * (P.conjTranspose * PI.UpqRep.Jm ε * P) * a) * P.conjTranspose := by simp only [Matrix.mul_assoc]
      _ = P * Hpk k r * P.conjTranspose := by rw [hPJ]; exact congrArg (fun m => P * m * P.conjTranspose) ha'
      _ = (P * P.conjTranspose) * PI.UpqRep.Jm ε * (P * P.conjTranspose) := by
        rw [show Hpk k r = P.conjTranspose * PI.UpqRep.Jm ε * P from hPJ.symm]; simp only [Matrix.mul_assoc]
      _ = PI.UpqRep.Jm ε := by rw [hPP, Matrix.one_mul, Matrix.mul_one]
  refine ⟨?_, ?_, ?_⟩
  · have h1' : σ (P⁻¹ * 1 * P) = 1 := h1
    rwa [Matrix.mul_one, hinv, hsP] at h1'
  · intro a ha b hb
    have e : P * a * P.conjTranspose * (P * b * P.conjTranspose) = P * (a * b) * P.conjTranspose := by
      calc P * a * P.conjTranspose * (P * b * P.conjTranspose) = P * a * (P.conjTranspose * P) * b * P.conjTranspose := by simp only [Matrix.mul_assoc]
        _ = P * (a * b) * P.conjTranspose := by rw [hsP, Matrix.mul_one, Matrix.mul_assoc P a b]
    have := hmul _ (hmem a ha) _ (hmem b hb)
    simp only [e, conj] at this
    exact this
  · intro a ha v
    have := hiso _ (hmem a ha) v
    simp only [conj] at this
    exact this

private theorem isUnit_det_of_mem_UH_Hpk' {a : Mat k r} (ha : a ∈ UH (Hpk k r)) : IsUnit a.det := by
  have ha' : a.conjTranspose * Hpk k r * a = Hpk k r := ha
  have h1 : (a.conjTranspose * Hpk k r * a).det = (Hpk k r).det := by rw [ha']
  have h2 : (Hpk k r).det * (Hpk k r).det = 1 := by
    rw [← Matrix.det_mul, Formalism.QuantumDeterminants.GBasic.Hpk_sq, Matrix.det_one]
  rw [Matrix.det_mul, Matrix.det_mul] at h1
  refine isUnit_iff_ne_zero.mpr fun h0 => ?_
  rw [h0, mul_zero] at h1
  rw [← h1, zero_mul] at h2
  exact zero_ne_one h2

theorem inner_inv_of_DS {ε : Fin (2 * r + k + 1) → Bool} {lm : Fin (2 * r + k + 1) → ℝ} {σ : Mat k r → (H →L[ℂ] H)}
    (h : PI.UpqRep.IsDSHpk k r ε lm σ) {a : Mat k r} (ha : a ∈ UH (Hpk k r)) (u w : H) :
    ⟪u, σ a⁻¹ w⟫_ℂ = ⟪σ a u, w⟫_ℂ := by
  obtain ⟨h1, hmul, hiso⟩ := rep_of_DS h
  have hinvm : a⁻¹ ∈ UH (Hpk k r) := Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv ha
  have hc : σ a (σ a⁻¹ w) = w := by
    have := hmul a ha a⁻¹ hinvm
    rw [Matrix.mul_nonsing_inv a (isUnit_det_of_mem_UH_Hpk' ha), h1] at this
    rw [← ContinuousLinearMap.comp_apply, ← this]
    rfl
  let L : H →ₗᵢ[ℂ] H := { toLinearMap := (σ a : H →ₗ[ℂ] H), norm_map' := hiso a ha }
  calc ⟪u, σ a⁻¹ w⟫_ℂ = ⟪L u, L (σ a⁻¹ w)⟫_ℂ := (L.inner_map_map _ _).symm
    _ = ⟪σ a u, w⟫_ℂ := by
      change ⟪σ a u, σ a (σ a⁻¹ w)⟫_ℂ = _
      rw [hc]

end rep

section hs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem sum_basis_inner (T : Wq →L[ℂ] Wq) (ξ' : Wq) :
    ∑ i, star ⟪ξ', stdOrthonormalBasis ℂ Wq i⟫_ℂ * ⟪ξ', T (stdOrthonormalBasis ℂ Wq i)⟫_ℂ = ⟪ξ', T ξ'⟫_ℂ := by
  symm
  calc ⟪ξ', T ξ'⟫_ℂ = ⟪ξ', T (∑ i, ⟪stdOrthonormalBasis ℂ Wq i, ξ'⟫_ℂ • stdOrthonormalBasis ℂ Wq i)⟫_ℂ := by
        rw [(stdOrthonormalBasis ℂ Wq).sum_repr' ξ']
    _ = _ := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, inner_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, inner_smul_right, ← inner_conj_symm (stdOrthonormalBasis ℂ Wq i) ξ']
      rfl

theorem hsInner_rank1 (T : Wq →L[ℂ] Wq) (U : Wp →L[ℂ] Wp) (α β : ℂ) (ξ : Wp) (ξ' : Wq) :
    hsInner (U.comp (((innerSL ℂ ξ').smulRight (α • ξ)).comp T)) ((innerSL ℂ ξ').smulRight (β • ξ)) =
      α * star β * ⟪ξ, U ξ⟫_ℂ * ⟪ξ', T ξ'⟫_ℂ := by
  rw [← sum_basis_inner T ξ']
  have e : ∀ x y : Wq, innerSL ℂ x y = ⟪x, y⟫_ℂ := fun _ _ => rfl
  simp only [hsInner, hsVec, PiLp.inner_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, e, map_smul, inner_smul_left, inner_smul_right,
    starRingEnd_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end hs

private theorem mul_mem_UH_Hpk_archimedean_coefficient_nonzero {k r : ℕ} {a b : Mat k r} (ha : a ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) :
    a * b ∈ UH (Hpk k r) := by
  have ha' : a.conjTranspose * Hpk k r * a = Hpk k r := ha
  have hb' : b.conjTranspose * Hpk k r * b = Hpk k r := hb
  show (a * b).conjTranspose * Hpk k r * (a * b) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc b.conjTranspose * a.conjTranspose * Hpk k r * (a * b) = b.conjTranspose * (a.conjTranspose * Hpk k r * a) * b := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

private theorem aDil_mem_gv {k r : ℕ} {t : ℝ} (ht : 0 < t) : aDil k r t ∈ UH (Hpk k r) := by
  show (aDil k r t).conjTranspose * Hpk k r * aDil k r t = Hpk k r
  have hs : ∀ x : ℝ, star (x : ℂ) = x := fun x => Complex.conj_ofReal x
  ext i j
  unfold aDil
  rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.star_apply]
  unfold Formalism.QuantumDeterminants.Hpk
  beta_reduce
  have hi := i.isLt
  have hj := j.isLt
  by_cases h1 : i.val < r ∧ i.val + j.val = 2 * r + k
  · have e : j.val - (r + k) = r - i.val := by omega
    have hj1 : ¬ j.val < r := by omega
    have hj2 : ¬ j.val ≤ r + k := by omega
    have hne : t ^ (r - i.val) ≠ 0 := pow_ne_zero _ ht.ne'
    rw [if_pos h1, if_pos h1.1, if_neg hj1, if_neg hj2, hs, e, mul_one, ← Complex.ofReal_mul,
      mul_inv_cancel₀ hne, Complex.ofReal_one]
  · by_cases h2 : j.val < r ∧ i.val + j.val = 2 * r + k
    · have e : i.val - (r + k) = r - j.val := by omega
      have hi1 : ¬ i.val < r := by omega
      have hi2 : ¬ i.val ≤ r + k := by omega
      have hne : t ^ (r - j.val) ≠ 0 := pow_ne_zero _ ht.ne'
      rw [if_neg h1, if_pos h2, if_pos h2.1, if_neg hi1, if_neg hi2, hs, e, mul_one,
        ← Complex.ofReal_mul, inv_mul_cancel₀ hne, Complex.ofReal_one]
    · by_cases h3 : r ≤ i.val ∧ i.val ≤ r + k ∧ i = j
      · have hij : i = j := h3.2.2
        subst hij
        have hi1 : ¬ i.val < r := by omega
        rw [if_neg h1, if_neg h2, if_pos h3, if_neg hi1, if_pos h3.2.1]
        simp
      · rw [if_neg h1, if_neg h2, if_neg h3, mul_zero, zero_mul]

theorem phiAt_of (hS : Formalism.FourierDecayAlt.ThreeDimData.SchurH) : PhiAt := by
  intro k r Wp Wq _ _ _ _ _ _ D ε lm H _ _ _ σ hlm hDS
  have hG := D.haarG
  haveI : IsFiniteMeasureOnCompacts D.μG := ⟨hG.finite_compact⟩
  have hHaar : PI.BesselPeriodGGP.IsHaarOn (UH (Hpk k r)) D.μG :=
    ⟨inferInstance, hG.ne_zero, hG.conc, hG.left⟩
  obtain ⟨d, hd, hSch⟩ := hS k r ε lm H σ D.μG hlm hDS hHaar
  refine ⟨d, hd, ?_⟩
  intro v v' ξ ξ' p hp t ht1 ht2
  obtain ⟨h11, h12, h21, h22⟩ := hp
  obtain ⟨-, hmul, -⟩ := rep_of_DS hDS
  have hq12 : Matrix.of (conjM (aDil k r t.1) p.1.2) ∈ UH (Hpk k r) :=
    mul_mem_UH_Hpk_archimedean_coefficient_nonzero (mul_mem_UH_Hpk_archimedean_coefficient_nonzero (aDil_mem_gv ht1) h12.1) (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv (aDil_mem_gv ht1))
  have hq22 : Matrix.of (conjM (aDil k r t.2) p.2.2) ∈ UH (Hpk k r) :=
    mul_mem_UH_Hpk_archimedean_coefficient_nonzero (mul_mem_UH_Hpk_archimedean_coefficient_nonzero (aDil_mem_gv ht2) h22.1) (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv (aDil_mem_gv ht2))
  have hB : (Matrix.of (conjM (aDil k r t.2) p.2.2) * Matrix.of p.2.1) ∈ UH (Hpk k r) := mul_mem_UH_Hpk_archimedean_coefficient_nonzero hq22 h21.1
  have hC : (Matrix.of (conjM (aDil k r t.1) p.1.2) * Matrix.of p.1.1) ∈ UH (Hpk k r) := mul_mem_UH_Hpk_archimedean_coefficient_nonzero hq12 h11.1
  have hCi := Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hC
  have hae : ∀ᵐ g ∂D.μG, Matrix.of g ∈ UH (Hpk k r) := ae_iff.mpr hG.conc
  have key : ∀ᵐ g ∂D.μG, hsInner (rho D (dilation₂ t p) (coefM σ v v' ξ ξ') (Matrix.of g))
      (coefM σ v v' ξ ξ' (Matrix.of g)) =
      (⟪σ (Matrix.of (conjM (aDil k r t.1) p.1.2) * Matrix.of p.1.1) v, σ (Matrix.of g) (σ (Matrix.of (conjM (aDil k r t.2) p.2.2) * Matrix.of p.2.1) v')⟫_ℂ * star ⟪v, σ (Matrix.of g) v'⟫_ℂ) *
        (⟪ξ, D.π (Matrix.of p.1.1) ξ⟫_ℂ * ⟪ξ', D.π' (Matrix.of p.2.1)⁻¹ ξ'⟫_ℂ) := by
    filter_upwards [hae] with g hg
    have e : (Matrix.of p.1.1)⁻¹ * (Matrix.of (conjM (aDil k r t.1) p.1.2))⁻¹ * Matrix.of g * Matrix.of (conjM (aDil k r t.2) p.2.2) * Matrix.of p.2.1 =
        (Matrix.of (conjM (aDil k r t.1) p.1.2) * Matrix.of p.1.1)⁻¹ * Matrix.of g * (Matrix.of (conjM (aDil k r t.2) p.2.2) * Matrix.of p.2.1) := by
      rw [Matrix.mul_inv_rev]
      simp only [Matrix.mul_assoc]
    have hσ : σ ((Matrix.of (conjM (aDil k r t.1) p.1.2) * Matrix.of p.1.1)⁻¹ * Matrix.of g * (Matrix.of (conjM (aDil k r t.2) p.2.2) * Matrix.of p.2.1)) =
        (σ (Matrix.of (conjM (aDil k r t.1) p.1.2) * Matrix.of p.1.1)⁻¹).comp ((σ (Matrix.of g)).comp (σ (Matrix.of (conjM (aDil k r t.2) p.2.2) * Matrix.of p.2.1))) := by
      rw [hmul _ (mul_mem_UH_Hpk_archimedean_coefficient_nonzero hCi hg) _ hB, hmul _ hCi _ hg, ContinuousLinearMap.comp_assoc]
    change hsInner ((D.π (Matrix.of p.1.1)).comp (((innerSL ℂ ξ').smulRight
        (⟪v, σ ((Matrix.of p.1.1)⁻¹ * (Matrix.of (conjM (aDil k r t.1) p.1.2))⁻¹ * Matrix.of g * Matrix.of (conjM (aDil k r t.2) p.2.2) * Matrix.of p.2.1) v'⟫_ℂ • ξ)).comp
        (D.π' (Matrix.of p.2.1)⁻¹))) ((innerSL ℂ ξ').smulRight (⟪v, σ (Matrix.of g) v'⟫_ℂ • ξ)) = _
    rw [hsInner_rank1, e, hσ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      inner_inv_of_DS hDS hC]
    ring
  unfold Ph
  rw [integral_congr_ae key, integral_mul_const, (hSch (σ (Matrix.of (conjM (aDil k r t.2) p.2.2) * Matrix.of p.2.1) v') (σ (Matrix.of (conjM (aDil k r t.1) p.1.2) * Matrix.of p.1.1) v) v' v).2]
  simp only [Lf, Rf]
  ring

end PI.BICNZ
end
end

