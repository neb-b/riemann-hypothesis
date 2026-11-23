module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1228
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import ReciprocityTheory.SemistableReduction.Bundle0025
public import ReciprocityTheory.SemistableReduction.Bundle0007
public import ReciprocityTheory.SemistableReduction.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GaussAbsMulSupportFinite
public import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1233
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0201
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1216
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
public import Formalism.HarderNarasimhan.StatementPl
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrameLaws
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineSignMulSelf
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD

noncomputable section

namespace GlobalTheory.HoweD.CCRSig

variable {W : Type} [DecidableEq W] {P Q R S : W → ℕ}

def unitAtS (j : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) (z : ℂ) : ∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ :=
  Pi.single j.1 (Matrix.single j.2.1 j.2.2 z)

theorem sum_unitAtS [Fintype W] (j k : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) (z z' : ℂ) :
    (∑ w, ∑ a, ∑ b, lineSign a b * unitAtS j z w a b * star (unitAtS k z' w a b)) =
      if j = k then lineSign j.2.1 j.2.2 * z * star z' else 0 := by
  obtain ⟨w0, a0, b0⟩ := j
  obtain ⟨w1, a1, b1⟩ := k
  rw [Finset.sum_eq_single w0]
  · by_cases hw : w1 = w0
    · subst hw
      simp only [unitAtS, Pi.single_eq_same]
      rw [Finset.sum_eq_single a0, Finset.sum_eq_single b0]
      · by_cases ha : a0 = a1
        · subst ha
          by_cases hb : b0 = b1
          · subst hb; simp
          · have : (⟨w1, a0, b0⟩ : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) ≠ ⟨w1, a0, b1⟩ := by
              intro h; simp at h; exact hb h
            simp [this, hb, Ne.symm hb]
        · have : (⟨w1, a0, b0⟩ : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) ≠ ⟨w1, a1, b1⟩ := by
            intro h; simp at h; exact ha h.1
          simp [this, ha, Ne.symm ha]
      · intro b _ hb; simp [Ne.symm hb]
      · simp
      · intro a _ ha; simp [Ne.symm ha]
      · simp
    · have : (⟨w0, a0, b0⟩ : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) ≠ ⟨w1, a1, b1⟩ := by
        intro h; exact hw (congrArg Sigma.fst h).symm
      simp [unitAtS, hw, this]
  · intro w _ hw; simp [unitAtS, hw]
  · simp

theorem sum_unitAtS_eq [Fintype W] (c : ∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) :
    c = ∑ j : (Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)), unitAtS j (c j.1 j.2.1 j.2.2) := by
  funext w a b
  simp only [Finset.sum_apply, Matrix.sum_apply, Fintype.sum_sigma, unitAtS]
  rw [Finset.sum_eq_single w]
  · simp only [Pi.single_eq_same]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single a, Finset.sum_eq_single b]
    · simp
    · intro b' _ hb; simp [Matrix.single_apply, hb]
    · simp
    · intro a' _ ha; simp [Matrix.single_apply, ha]
    · simp
  · intro w' _ hw; simp [Pi.single_eq_of_ne' hw]
  · simp

end GlobalTheory.HoweD.CCRSig

namespace GlobalTheory.HoweD.CCRSig

variable {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [DecidableEq W] {P Q R S : W → ℕ}

theorem lineSign_cases {P Q R S : ℕ} (a : Ix P Q) (b : Ix R S) : (lineSign a b : ℂ) = 1 ∨ (lineSign a b : ℂ) = -1 := by
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign]

theorem lineSign_mul_self {P Q R S : ℕ} (a : Ix P Q) (b : Ix R S) : lineSign a b * lineSign a b = 1 := by
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign]

theorem comm_expand (A A' B B' : Module.End ℂ V) (c u v : ℂ) :
    -(c • (A + u • A')) * (c • (B - v • B')) - (c • (B - v • B')) * -(c • (A + u • A')) =
      -((c * c) • ((A * B - B * A) - v • (A * B' - B' * A) + u • (A' * B - B * A') - (u * v) • (A' * B' - B' * A'))) := by
  simp only [neg_mul, mul_neg, smul_mul_assoc, mul_smul_comm, mul_add, add_mul, mul_sub, sub_mul]
  module

theorem inv_sq : (2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ * (2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ =
    (8 * (Real.pi : ℂ))⁻¹ := by
  have h : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) = 2 * (Real.pi : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast; ring
  rw [← mul_inv]
  congr 1
  linear_combination 4 * h

def ccrM (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V)
    (j : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) : Module.End ℂ V :=
  (2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ •
    (H (unitAtS j 1) - (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAtS j Complex.I))

def ccrD (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V)
    (j : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) : Module.End ℂ V :=
  -((2 * ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ))⁻¹ •
    (H (unitAtS j 1) + (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAtS j Complex.I)))

theorem ccrM_comm [Fintype W] (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V)
    (hc : ∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1)
    (j k : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) : ccrM H j * ccrM H k = ccrM H k * ccrM H j := by
  have h11 := hc (unitAtS j 1) (unitAtS k 1)
  have h1i := hc (unitAtS j 1) (unitAtS k Complex.I)
  have hi1 := hc (unitAtS j Complex.I) (unitAtS k 1)
  have hii := hc (unitAtS j Complex.I) (unitAtS k Complex.I)
  rw [sum_unitAtS] at h11 h1i hi1 hii
  by_cases hjk : j = k
  · rw [hjk]
  · simp only [if_neg hjk, Complex.zero_im, Complex.ofReal_zero, mul_zero, zero_smul, sub_eq_zero] at h11 h1i hi1 hii
    unfold ccrM
    have c : Commute (H (unitAtS j 1) - (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAtS j Complex.I))
        (H (unitAtS k 1) - (lineSign k.2.1 k.2.2 * Complex.I) • H (unitAtS k Complex.I)) :=
      Commute.sub_left (Commute.sub_right h11 (Commute.smul_right h1i _))
        (Commute.smul_left (Commute.sub_right hi1 (Commute.smul_right hii _)) _)
    exact ((c.smul_left _).smul_right _).eq

theorem ccrD_ccrM_comm [Fintype W] (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V)
    (hc : ∀ c c', H c * H c' - H c' * H c =
      ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1)
    (j k : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) :
    ccrD H j * ccrM H k - ccrM H k * ccrD H j = if j = k then 1 else 0 := by
  unfold ccrD ccrM
  rw [comm_expand, hc, hc, hc, hc, sum_unitAtS, sum_unitAtS, sum_unitAtS, sum_unitAtS,
    inv_sq]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  by_cases h : j = k
  · subst h
    simp only [if_true, smul_smul, ← sub_smul, ← add_smul, ← neg_smul]
    conv_rhs => rw [← one_smul ℂ (1 : Module.End ℂ V)]
    congr 1
    rcases lineSign_cases j.2.1 j.2.2 with h | h
    · rw [h]; simp; field_simp; linear_combination (-8 : ℂ) * Complex.I_sq
    · rw [h]; simp; field_simp; linear_combination (-8 : ℂ) * Complex.I_sq
  · simp [h]

theorem unitAtS_re_im (j : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) (z : ℂ) :
    unitAtS j z = ((z.re : ℝ) : ℂ) • unitAtS j 1 + ((z.im : ℝ) : ℂ) • unitAtS j Complex.I := by
  funext w
  by_cases hw : w = j.1
  · subst hw
    simp only [unitAtS, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, Matrix.smul_single, ← Matrix.single_add, smul_eq_mul,
      mul_one, Complex.re_add_im]
  · simp [unitAtS, Pi.single_eq_of_ne hw]

theorem heis_expanccrD [Fintype W] (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V)
    (hadd : ∀ c c', H (c + c') = H c + H c') (hsmul : ∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c)
    (c : ∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) :
    H c = ∑ j : (Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)),
      ((((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefM (c j.1 j.2.1 j.2.2) (lineSign j.2.1 j.2.2)) • ccrM H j +
        (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefD (c j.1 j.2.1 j.2.2) (lineSign j.2.1 j.2.2)) • ccrD H j) := by
  have h0 : H 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  let H' : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →+ Module.End ℂ V := ⟨⟨H, h0⟩, hadd⟩
  have hsum : H c = ∑ j : (Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)), H (unitAtS j (c j.1 j.2.1 j.2.2)) := by
    conv_lhs => rw [sum_unitAtS_eq c]
    exact map_sum H' _ _
  rw [hsum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [unitAtS_re_im, hadd, hsmul, hsmul]
  have hs : ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    exact_mod_cast this.ne'
  have he := lineSign_mul_self j.2.1 j.2.2
  unfold ccrM ccrD GlobalTheory.CCRFock.coefM GlobalTheory.CCRFock.coefD
  generalize ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) = s at hs ⊢
  generalize lineSign j.2.1 j.2.2 = e at he ⊢
  generalize H (unitAtS j 1) = A
  generalize H (unitAtS j Complex.I) = B
  generalize ((c j.1 j.2.1 j.2.2).re : ℂ) = x
  generalize ((c j.1 j.2.1 j.2.2).im : ℂ) = y
  have hI := Complex.I_mul_I
  match_scalars
  · field_simp
    ring
  · field_simp
    linear_combination (2 * y * e * e) * hI - 2 * y * he

end GlobalTheory.HoweD.CCRSig

namespace GlobalTheory.HoweD


open GlobalTheory.HoweD.CCRSig in
theorem ccr_fock_ops_sig : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {W : Type} [Fintype W] [DecidableEq W] {P Q R S : W → ℕ} (H : (∀ w : W, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) → Module.End ℂ V), (∀ c c', H (c + c') = H c + H c') → (∀ (r : ℝ) c, H ((r : ℂ) • c) = (r : ℂ) • H c) → (∀ c c', H c * H c' - H c' * H c = ((4 * Real.pi : ℂ) * Complex.I * ((∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im : ℂ)) • 1) → ∃ m D : (Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) → Module.End ℂ V, (∀ i j, m i * m j = m j * m i) ∧ (∀ i j, D i * m j - m j * D i = if i = j then 1 else 0) ∧ (∀ (j : Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)) (f₀ : V), H (Pi.single j.1 (Matrix.single j.2.1 j.2.2 1)) f₀ + (lineSign j.2.1 j.2.2 * Complex.I) • H (Pi.single j.1 (Matrix.single j.2.1 j.2.2 Complex.I)) f₀ = 0 → D j f₀ = 0) ∧ ∀ c, H c = ∑ j : (Σ w : W, Ix (P w) (Q w) × Ix (R w) (S w)), ((((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefM (c j.1 j.2.1 j.2.2) (lineSign j.2.1 j.2.2)) • m j + (((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) * GlobalTheory.CCRFock.coefD (c j.1 j.2.1 j.2.2) (lineSign j.2.1 j.2.2)) • D j) := by
  intro V _ _ W _ _ P Q R S H hadd hsmul hc
  refine ⟨ccrM H, ccrD H, ccrM_comm H hc, ccrD_ccrM_comm H hc, fun j f₀ h => ?_, heis_expanccrD H hadd hsmul⟩
  have h' : H (unitAtS j 1) f₀ + (lineSign j.2.1 j.2.2 * Complex.I) • H (unitAtS j Complex.I) f₀ = 0 := h
  simp only [GlobalTheory.HoweD.CCRSig.ccrD, LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.add_apply, h', smul_zero, neg_zero]

end GlobalTheory.HoweD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogGaussAbsSupportFinite
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open Polynomial (nthRootsFinset)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.HSFinPart

theorem log_gaussAbs_support_finite {E : Type} [Field E] [NumberField E] {σ : Type}
    (g : MvPolynomial σ E) :
    (Function.support fun v : FinitePlace E => Real.log (gaussAbs v g)).Finite :=
  ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.gaussAbs_support_finite g

theorem finPart_props : ∀ (E : Type) [Field E] [NumberField E] (σ τ : Type),
    (∀ g : MvPolynomial σ E, g ≠ 0 → {v : FinitePlace E | gaussAbs v g ≠ 1}.Finite ∧
      ∀ v : FinitePlace E, 0 < gaussAbs v g) ∧
    (∀ (g : MvPolynomial σ E) (g' : MvPolynomial τ E), g ≠ 0 → g' ≠ 0 →
      (∀ v : FinitePlace E, gaussAbs v g' ≤ gaussAbs v g) → finPart g' ≤ finPart g) ∧
    ∀ (g : MvPolynomial σ E) (m : σ →₀ ℕ), g.coeff m ≠ 0 →
      -mean E (fun s => Real.log ‖s (g.coeff m)‖) ≤ finPart g := by
  intro E _ _ σ τ
  have hd : (0 : ℝ) < (Module.finrank ℚ E : ℝ) := by
    exact_mod_cast Module.finrank_pos
  refine ⟨fun g hg => ⟨?_, fun v => gauss_abs_pos_of_ne_zero v g hg⟩, ?_, ?_⟩
  · exact ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.gaussAbs_mulSupport_finite g hg
  · intro g g' hg hg' hle
    unfold finPart
    refine div_le_div_of_nonneg_right ?_ hd.le
    exact finsum_le_finsum' (log_gaussAbs_support_finite g') (log_gaussAbs_support_finite g)
      (fun v => Real.log_le_log (gauss_abs_pos_of_ne_zero v g' hg') (hle v))
  · intro g m hm
    have hg : g ≠ 0 := by
      rintro rfl; exact hm (by simp)
    set c := g.coeff m with hc
    have h1 : ∑ᶠ v : FinitePlace E, Real.log (v c) ≤ ∑ᶠ v : FinitePlace E, Real.log (gaussAbs v g) :=
      finsum_le_finsum'
        ((FinitePlace.hasFiniteMulSupport hm).subset (by
          intro v hv h1; apply hv; simp only at h1 ⊢; rw [h1, Real.log_one]))
        (log_gaussAbs_support_finite g)
        (fun v => Real.log_le_log (FinitePlace.pos_iff.mpr hm) (coeff_le_gauss_abs v g m))
    rw [ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.finsum_log_norm c hm] at h1
    unfold mean finPart
    rw [sum_log_norm_embedding_eq c hm, ← neg_div]
    exact div_le_div_of_nonneg_right h1 hd.le

end GlobalTheory.HSFinPart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapLine
section
set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.HSChoice

namespace GlobalTheory.PencilDisc

def line {F R : Type} [CommRing F] [CommRing R] [Algebra F R] {D N : ℕ} (u : Fin D → Fin N → R) (a b : Fin N → R)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) : Polynomial R :=
  aeval (join (fun i j => Polynomial.C (u i j)) fun j => Polynomial.C (a j) + Polynomial.C (b j) * Polynomial.X) f

def disc {F R : Type} [CommRing F] [CommRing R] [Algebra F R] {D N : ℕ} (δ : ℕ) (u : Fin D → Fin N → R) (a b : Fin N → R)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) : R :=
  Polynomial.resultant (line u a b f) (Polynomial.derivative (line u a b f)) δ (δ - 1)

theorem map_line {F R S : Type} [CommRing F] [CommRing R] [CommRing S] [Algebra F R] [Algebra F S] {D N : ℕ}
    (φ : R →ₐ[F] S) (u : Fin D → Fin N → R) (a b : Fin N → R) (f : MvPolynomial (Fin (D + 1) × Fin N) F) :
    (line u a b f).map (φ : R →+* S) = line (fun i j => φ (u i j)) (fun j => φ (a j)) (fun j => φ (b j)) f := by
  have h : (Polynomial.mapAlgHom φ).comp
      (aeval (join (fun i j => Polynomial.C (u i j)) fun j => Polynomial.C (a j) + Polynomial.C (b j) * Polynomial.X)) =
      aeval (join (fun i j => Polynomial.C (φ (u i j))) fun j => Polynomial.C (φ (a j)) + Polynomial.C (φ (b j)) * Polynomial.X) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨i, j⟩
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [join]
    · simp [join]
  exact congrArg (fun g : MvPolynomial (Fin (D + 1) × Fin N) F →ₐ[F] Polynomial S => g f) h

theorem map_disc {F R S : Type} [CommRing F] [CommRing R] [CommRing S] [Algebra F R] [Algebra F S] {D N : ℕ}
    (φ : R →ₐ[F] S) (δ : ℕ) (u : Fin D → Fin N → R) (a b : Fin N → R) (f : MvPolynomial (Fin (D + 1) × Fin N) F) :
    φ (disc δ u a b f) = disc δ (fun i j => φ (u i j)) (fun j => φ (a j)) (fun j => φ (b j)) f := by
  rw [disc, disc, ← map_line φ, Polynomial.derivative_map, ← AlgHom.coe_toRingHom, ← Polynomial.resultant_map_map]

end GlobalTheory.PencilDisc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRankNormalForm
section
open ValuativeRel Matrix

namespace GlobalTheory

theorem rank_frame_exists :
    ∀ (K : Type) [Field K] (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]
      (X : Matrix A D K), ∃ (H : Matrix (Fin X.rank) A K) (Q : Matrix D (Fin X.rank) K),
        H * X * Q = 1 := by
  intro K _ A D _ _ _ _ X
  classical
  let V := LinearMap.range X.mulVecLin
  let b : Module.Basis (Fin X.rank) K V := Module.finBasis K V
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (p := V) b.equivFun.toLinearMap
  have hpre : ∀ i, ∃ v : D → K, X *ᵥ v = ((b i : V) : A → K) := fun i => by
    obtain ⟨v, hv⟩ := LinearMap.mem_range.mp (b i).2
    exact ⟨v, hv⟩
  choose q hq using hpre
  refine ⟨LinearMap.toMatrix' g, Matrix.of fun d i => q i d, ?_⟩
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_single_one,
    Matrix.one_mulVec]
  have hcol : (Matrix.of fun d i => q i d).col j = q j := by
    ext d; simp [Matrix.col]
  rw [hcol, hq j, LinearMap.toMatrix'_mulVec]
  have := congrArg (fun f => f (b j)) hg
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
    LinearEquiv.coe_coe] at this
  rw [this]
  ext k
  rw [Module.Basis.equivFun_self]
  simp [Pi.single_apply, Finsupp.single_apply, eq_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemL2OfContinuousAutomorphic
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefiniteSqInt

theorem memL2_of_continuous_definite : ∀ {D : D7} (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)),
    GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsDefiniteSpace V → GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel V K → Links.IsMeasDef V K μ 𝓕 →
    ∀ u : GA D V → ℂ, Continuous u → (∀ γ ∈ GQ V, ∀ h, u (γ * h) = u h) → GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GQ V) μ u := by
  intro D V K μ 𝓕 hV _ hμ u hu hinv
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hT.2.2.2.2.2.2
  have := hμ.1.1
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.Mem.AnisoQuotient.exists_compact D V
    (GlobalTheory.BesselConvDefinite.isAniso_of_isDefinite V hV.1 hV.2)
  have hcov' : ∀ g : GA D V, ∃ γ ∈ GQ V, γ * g ∈ C := fun g => by
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov g
    exact ⟨γ⁻¹, inv_mem hγ, by rwa [inv_mul_cancel_left]⟩
  refine (GlobalTheory.AutomorphicL2Unitary.memL2_iff_fundamental_domain hμ.2).2 ⟨hinv, (memLp_two_iff_integrable_sq_norm hu.aestronglyMeasurable).2 ?_⟩
  simpa only [← _root_.norm_pow] using (GlobalTheory.integrableOn_fundamentalDomain_of_cocompact _ (GQ V) C hC hcov' μ
    inferInstance 𝓕 hμ.2 (fun g => u g ^ 2) (hu.pow 2) fun γ hγ g => by rw [hinv γ hγ]).norm

end GlobalTheory.DefiniteSqInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSmallSectionBallOfMulPowSection
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr

namespace GlobalTheory.VolBr.MpDiv

theorem mem_Bl_of_mul_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ s : X.functionField, s ∈ P.H 0 1 → s ≠ 0 → ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (N m : ℕ) (f : X.functionField), f ∈ P.H N 0 → f * s ^ m ∈ P.Bl N m 2 → f ∈ P.Bl N 0 (2 * Real.exp (δ * N + C * m)) := by
  intro k _ X _ p D hX P s hs hs0 δ hδ
  obtain ⟨ρ, hρ, H⟩ := _root_.GlobalTheory.VolBr.max_principle_global k X p D hX P s hs hs0 δ hδ
  refine ⟨max 0 (-Real.log ρ), le_max_left _ _, fun N m f hf hfs => ?_⟩
  set C : ℝ := max 0 (-Real.log ρ) with hC
  have key := H N f (2 * Real.exp (C * m)) hf (fun σ y hy => ?_)
  · have e : Real.exp (δ * N) * (2 * Real.exp (C * m)) = 2 * Real.exp (δ * N + C * m) := by
      rw [Real.exp_add]; ring
    rwa [e] at key
  · obtain ⟨hp1, hp2⟩ := _root_.GlobalTheory.VolBr.NuPow.pow_mem_H_and_nu_pow k X p P 0 1 s hs m
    have hm := (_root_.GlobalTheory.VolBr.NuMul.mul_mem_H_and_nu_mul k X p P N 0 _ _ f (s ^ m) hf hp1).2 σ y
    rw [hp2 σ y] at hm
    simp only [mul_zero, add_zero, mul_one, zero_add] at hm
    have h2 := hfs.2 σ y
    rw [hm] at h2
    have hn : 0 ≤ P.nu N 0 σ y f := by unfold Pair.nu; positivity
    have h1 : 1 ≤ Real.exp C * P.nu 0 1 σ y s := by
      have : Real.exp (-Real.log ρ) ≤ Real.exp C := Real.exp_le_exp.2 (le_max_right _ _)
      rw [Real.exp_neg, Real.exp_log hρ] at this
      calc (1 : ℝ) = ρ⁻¹ * ρ := (inv_mul_cancel₀ hρ.ne').symm
        _ ≤ Real.exp C * P.nu 0 1 σ y s :=
          mul_le_mul this hy hρ.le (Real.exp_pos _).le
    have h3 : 1 ≤ Real.exp (C * m) * P.nu 0 1 σ y s ^ m := by
      rw [mul_comm C, Real.exp_nat_mul, ← mul_pow]
      exact one_le_pow₀ h1
    calc P.nu N 0 σ y f ≤ P.nu N 0 σ y f * (Real.exp (C * m) * P.nu 0 1 σ y s ^ m) :=
          le_mul_of_one_le_right hn h3
      _ = Real.exp (C * m) * (P.nu N 0 σ y f * P.nu 0 1 σ y s ^ m) := by ring
      _ ≤ Real.exp (C * m) * 2 := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = 2 * Real.exp (C * m) := mul_comm _ _

end GlobalTheory.VolBr.MpDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefBigBaseChange
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSCore

theorem nef_big_baseChange : ∀ (F : Type) [Field F] [NumberField F] (X : Data F) (E : Type) [Field E] [NumberField E] [Algebra F E], IsNef F X.LA → IsBig F X.LA → IsNef E (X.baseChange E).LA ∧ IsBig E (X.baseChange E).LA := by
  intro F _ _ X E _ _ _ hn hb
  exact ⟨GlobalTheory.HilbertSamuel.Geo.isNef_baseChange X.toGeo E hn, GlobalTheory.HilbertSamuel.Geo.isBig_baseChange X.toGeo E hb⟩

end GlobalTheory.HSCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RdIndepOfLawsM
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory


set_option maxHeartbeats 1000000 in
theorem rdIndep_of_lawsM : ∀ (D : D7) (T : Core D), LawsM T → ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ →
    RdIndep (T.Q.Xo j) T.Q.c (T.U j) σ := by
  intro D T h j hj σ hσ
  exact ReciprocityTheory.ChartRestriction.G.PullbackSections.rdIndep_laws T.Q.c GlobalTheory.abelianSchemeLaws_all.2.secBaseChangeAny GlobalTheory.abelianSchemeLaws_all.2.secTwist (T.U j) σ (h.evalWD j hj)
    (GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.abelianSchemeLaws_all.1.secBaseChange _ _ _ _ (T.Q.Xo j) T.Q.c)
    (h.unf j hj σ hσ)

end GlobalTheory
end

