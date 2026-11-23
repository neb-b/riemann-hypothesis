module

public import Mathlib
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0153
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncatedGaussianIntegralUniformPosSemidef
section
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder

namespace GlobalTheory.TruncGauss

noncomputable def qf {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (w : V n) : ℂ :=
  ∑ j, ∑ l, A j l * w j * (starRingEnd ℂ) (w l)

theorem qf_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (w : V n) :
    qf (A + B) w = qf A w + qf B w := by
  simp only [qf, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem qf_smul {n : ℕ} (c : ℂ) (A : Matrix (Fin n) (Fin n) ℂ) (w : V n) :
    qf (c • A) w = c * qf A w := by
  simp only [qf, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem qf_one {n : ℕ} (w : V n) : qf (1 : Matrix (Fin n) (Fin n) ℂ) w = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [qf, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring

theorem qf_re_nonneg {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosSemidef) (w : V n) :
    0 ≤ (qf H w).re := by
  have h := hH.dotProduct_mulVec_nonneg (fun j => (starRingEnd ℂ) (w j))
  have e : star (fun j => (starRingEnd ℂ) (w j)) ⬝ᵥ (H.mulVec (fun j => (starRingEnd ℂ) (w j))) = qf H w := by
    simp only [qf, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [Complex.star_def, Complex.conj_conj]; ring
  rw [e] at h
  exact (Complex.le_def.mp h).1

theorem isCompact_bdd (n : ℕ) (C : ℝ) :
    IsCompact {H : Matrix (Fin n) (Fin n) ℂ | ∀ j l, ‖H j l‖ ≤ C} := by
  have h : IsCompact (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
      closedBall (0 : ℂ) C) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 C
  have e : {H : Matrix (Fin n) (Fin n) ℂ | ∀ j l, ‖H j l‖ ≤ C} =
      (Set.pi Set.univ fun _ : Fin n => Set.pi Set.univ fun _ : Fin n =>
      closedBall (0 : ℂ) C : Set (Matrix (Fin n) (Fin n) ℂ)) := by
    ext H
    show _ ↔ ∀ j ∈ Set.univ, ∀ l ∈ Set.univ, H j l ∈ closedBall (0 : ℂ) C
    simp [mem_closedBall, dist_zero_right]
  rw [e]; exact h

theorem exists_det_bound (n : ℕ) (C : ℝ) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ H : Matrix (Fin n) (Fin n) ℂ, (∀ j l, ‖H j l‖ ≤ C) → ‖H.det‖ ≤ K := by
  obtain ⟨K, hK⟩ := (isCompact_bdd n C).exists_bound_of_continuousOn
    (continuous_id.matrix_det).continuousOn
  refine ⟨max K 0, le_max_right _ _, fun H hH => (hK H hH).trans (le_max_left _ _)⟩

theorem exists_det_shift (n : ℕ) (C r : ℝ) (hr : 0 < r) : ∃ η : ℝ, 0 < η ∧
    ∀ H : Matrix (Fin n) (Fin n) ℂ, (∀ j l, ‖H j l‖ ≤ C) →
      ‖(H + (η : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det - H.det‖ < r := by
  have hev : ∀ᶠ t : ℝ in 𝓝 0, ∀ H ∈ {H : Matrix (Fin n) (Fin n) ℂ | ∀ j l, ‖H j l‖ ≤ C},
      ‖(H + (t : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det - H.det‖ < r := by
    refine (isCompact_bdd n C).eventually_forall_of_forall_eventually fun H _ => ?_
    have hc : Continuous fun z : ℝ × Matrix (Fin n) (Fin n) ℂ =>
        ‖(z.2 + (z.1 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det - z.2.det‖ := by
      fun_prop
    have h0 : ‖(H + ((0 : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det - H.det‖ = 0 := by simp
    have := hc.continuousAt (x := ((0 : ℝ), H))
    exact this.eventually (gt_mem_nhds (by simpa [h0] using hr))
  obtain ⟨t, ht, htpos⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)) (a := 0))).exists
  exact ⟨t, htpos, fun H hH => ht H hH⟩

theorem qf_smul_one_re {n : ℕ} (c : ℝ) (w : V n) :
    (qf ((c : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) w).re = c * ‖w‖ ^ 2 := by
  rw [qf_smul, qf_one, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem qf_shift_re {n : ℕ} (m η : ℝ) (H : Matrix (Fin n) (Fin n) ℂ) (w : V n) :
    (qf ((m : ℂ) • (H + (η : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))) w).re =
      m * ((qf H w).re + η * ‖w‖ ^ 2) := by
  rw [qf_smul, qf_add, qf_smul, qf_one, Complex.re_ofReal_mul, Complex.add_re,
    ← Complex.ofReal_mul, Complex.ofReal_re]

theorem trunc_lower {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosSemidef) (η δ : ℝ)
    (hη : 0 < η) (hδ : 0 < δ) (m : ℕ) (hm : 1 ≤ m) :
    Real.pi ^ n / (H + (η : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det.re
        - Real.exp (-(m * η * δ ^ 2 / 2)) * (2 * Real.pi / η) ^ n ≤
      (m : ℝ) ^ n * ∫ w in ball (0 : V n) δ,
        Real.exp (-(m * ((qf H w).re + η * ‖w‖ ^ 2))) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  set Hη := H + (η : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) with hHη
  have hηpd : ((η : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef :=
    Matrix.PosDef.one.smul (a := η) hη
  have hHηpd : Hη.PosDef := Matrix.PosDef.posSemidef_add hH hηpd
  have hMpd : ((m : ℂ) • Hη).PosDef := hHηpd.smul (a := (m : ℝ)) hm0
  set b : ℝ := m * η / 2 with hb
  have hb0 : 0 < b := by positivity
  have hGpd : ((b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef := Matrix.PosDef.one.smul (a := b) hb0
  obtain ⟨hfi, hfint⟩ := _root_.GlobalTheory.GaussHerm.integral_exp_neg_herm n _ hMpd
  obtain ⟨hgi, hgint⟩ := _root_.GlobalTheory.GaussHerm.integral_exp_neg_herm n _ hGpd
  set f : V n → ℝ := fun w => Real.exp (-(m * ((qf H w).re + η * ‖w‖ ^ 2))) with hf
  set g : V n → ℝ := fun w => Real.exp (-(b * ‖w‖ ^ 2)) with hg
  have ef : (fun w : V n => Real.exp (-(∑ j, ∑ l, ((m : ℂ) • Hη) j l * w j *
      (starRingEnd ℂ) (w l)).re)) = f := by
    funext w; exact congrArg (fun x => Real.exp (-x)) (qf_shift_re m η H w)
  have eg : (fun w : V n => Real.exp (-(∑ j, ∑ l, ((b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) j l *
      w j * (starRingEnd ℂ) (w l)).re)) = g := by
    funext w; exact congrArg (fun x => Real.exp (-x)) (qf_smul_one_re b w)
  rw [ef] at hfi hfint
  rw [eg] at hgi hgint
  have hD : ((m : ℂ) • Hη).det.re = (m : ℝ) ^ n * Hη.det.re := by
    rw [Matrix.det_smul, Fintype.card_fin, show ((m : ℂ)) ^ n = (((m : ℝ) ^ n : ℝ) : ℂ) by push_cast; rfl,
      Complex.re_ofReal_mul]
  have hGd : ((b : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det.re = b ^ n := by
    rw [Matrix.det_smul, Fintype.card_fin, Matrix.det_one, mul_one, ← Complex.ofReal_pow,
      Complex.ofReal_re]
  rw [hD] at hfint
  rw [hGd] at hgint
  have hDpos : 0 < Hη.det.re := by
    have := hHηpd.det_pos
    exact (Complex.lt_def.mp this).1

  have hsplit := integral_add_compl (s := ball (0 : V n) δ) measurableSet_ball hfi
  have htail : ∫ w in (ball (0 : V n) δ)ᶜ, f w ≤ Real.exp (-(m * η * δ ^ 2 / 2)) * ∫ w, g w := by
    rw [← integral_const_mul]
    refine (setIntegral_mono_on hfi.integrableOn (hgi.const_mul _).integrableOn
      measurableSet_ball.compl fun w hw => ?_).trans
      (setIntegral_le_integral (hgi.const_mul _) (Eventually.of_forall fun w => by positivity))
    have hw' : δ ≤ ‖w‖ := by simpa [mem_ball, dist_zero_right] using hw
    have hq := qf_re_nonneg H hH w
    simp only [hf, hg]
    rw [← Real.exp_add, Real.exp_le_exp]
    have h1 : δ ^ 2 ≤ ‖w‖ ^ 2 := pow_le_pow_left₀ hδ.le hw' 2
    have h2 : 0 ≤ (m : ℝ) * η := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 h2, mul_nonneg hm0.le hq]
  have hmain : (m : ℝ) ^ n * ∫ w in ball (0 : V n) δ, f w =
      Real.pi ^ n / Hη.det.re - (m : ℝ) ^ n * ∫ w in (ball (0 : V n) δ)ᶜ, f w := by
    rw [eq_sub_iff_add_eq, ← mul_add, hsplit, hfint]
    field_simp
  have hT : (m : ℝ) ^ n * (Real.exp (-(m * η * δ ^ 2 / 2)) * ∫ w, g w) =
      Real.exp (-(m * η * δ ^ 2 / 2)) * (2 * Real.pi / η) ^ n := by
    rw [hgint, hb]
    field_simp
    have h1 : η ^ n * η⁻¹ ^ n = 1 := by rw [← mul_pow, mul_inv_cancel₀ hη.ne', one_pow]
    have h2 : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by rw [← mul_pow]; norm_num
    linear_combination (-((m : ℝ) ^ n * Real.pi ^ n * (1 / 2 : ℝ) ^ n * 2 ^ n)) * h1 -
      ((m : ℝ) ^ n * Real.pi ^ n) * h2
  show _ ≤ (m : ℝ) ^ n * ∫ w in ball (0 : V n) δ, f w
  rw [hmain, ← hT]
  have := mul_le_mul_of_nonneg_left htail (pow_nonneg hm0.le n)
  linarith

theorem trunc_gauss : ∀ (n : ℕ) (C ε : ℝ), 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ δ : ℝ, 0 < δ →
    ∀ᶠ m : ℕ in atTop, ∀ H : Matrix (Fin n) (Fin n) ℂ, H.PosSemidef → (∀ j l, ‖H j l‖ ≤ C) →
      1 ≤ (H.det.re / Real.pi ^ n + ε) * (m : ℝ) ^ n * ∫ w in ball (0 : V n) δ,
        Real.exp (-(m * ((∑ j, ∑ l, H j l * w j * (starRingEnd ℂ) (w l)).re + η * ‖w‖ ^ 2))) := by
  intro n C ε hε
  set P : ℝ := Real.pi ^ n with hPdef
  have hP : 0 < P := pow_pos Real.pi_pos n
  set r : ℝ := ε * P / 2 with hrdef
  have hr : 0 < r := by positivity
  obtain ⟨K, hK0, hK⟩ := exists_det_bound n C
  obtain ⟨η, hη, hηd⟩ := exists_det_shift n C r hr
  refine ⟨η, hη, fun δ hδ => ?_⟩
  set A : ℝ := K / P + ε with hAdef
  have hA : 0 < A := by positivity
  set K2 : ℝ := K + r with hK2def
  have hK2 : 0 < K2 := by positivity
  have hs : 0 < r / K2 / A := by positivity
  have hT : Tendsto (fun m : ℕ => Real.exp (-(m * η * δ ^ 2 / 2)) * (2 * Real.pi / η) ^ n)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => (m : ℝ) * (η * δ ^ 2 / 2)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity)
    have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).mul_const ((2 * Real.pi / η) ^ n)
    rw [zero_mul] at h2
    refine h2.congr fun m => ?_
    simp only [Function.comp_apply]
    congr 2
    ring
  filter_upwards [hT.eventually (gt_mem_nhds hs), eventually_ge_atTop 1] with m hm hm1
  intro H hH hC
  have hl := trunc_lower H hH η δ hη hδ m hm1
  show 1 ≤ _ * _ * ∫ w in ball (0 : V n) δ, Real.exp (-(m * ((qf H w).re + η * ‖w‖ ^ 2)))
  set I := ∫ w in ball (0 : V n) δ, Real.exp (-(m * ((qf H w).re + η * ‖w‖ ^ 2)))
  set T := Real.exp (-(m * η * δ ^ 2 / 2)) * (2 * Real.pi / η) ^ n with hTdef
  have hT0 : 0 ≤ T := by positivity
  set d := H.det.re with hddef
  set D := (H + (η : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).det.re with hDdef
  have hd0 : 0 ≤ d := by
    have := (Complex.le_def.mp hH.det_nonneg).1
    simpa using this
  have hdK : d ≤ K := (Complex.re_le_norm _).trans (hK H hC)
  have hDd : D - d < r := by
    have := (Complex.re_le_norm _).trans_lt (hηd H hC)
    rw [Complex.sub_re] at this; exact this
  have hDpos : 0 < D := by
    have hηpd : ((η : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosDef :=
      Matrix.PosDef.one.smul (a := η) hη
    exact (Complex.lt_def.mp (Matrix.PosDef.posSemidef_add hH hηpd).det_pos).1
  have e1 : (d / P + ε) * (P / D) = (d + ε * P) / D := by field_simp
  have e2 : r / K2 ≤ r / D := div_le_div_of_nonneg_left hr.le hDpos (by linarith)
  have e3 : 1 + r / D ≤ (d + ε * P) / D := by
    rw [le_div_iff₀ hDpos, add_mul, div_mul_cancel₀ _ hDpos.ne']
    linarith
  have e4 : (d / P + ε) * T ≤ A * T :=
    mul_le_mul_of_nonneg_right (by have := div_le_div_of_nonneg_right hdK hP.le; linarith) hT0
  have e5 : A * T < r / K2 := by
    have := (lt_div_iff₀ hA).mp hm
    linarith
  have e6 : (d / P + ε) * (P / D - T) ≤ (d / P + ε) * ((m : ℝ) ^ n * I) :=
    mul_le_mul_of_nonneg_left hl (by positivity)
  rw [mul_assoc]
  rw [mul_sub, e1] at e6
  linarith

end GlobalTheory.TruncGauss
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TsumLatticePairUnitQuotientRegroup
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwo.Regroup

variable {F : Type} [Field F] [NumberField F]

theorem unit_mul_mem {I : FractionalIdeal (𝓞 F)⁰ F} (ε : (𝓞 F)ˣ) {a : F} (ha : a ∈ I) :
    ((ε : 𝓞 F) : F) * a ∈ I := by
  have : (ε : 𝓞 F) • a ∈ (I : Submodule (𝓞 F) F) := Submodule.smul_mem _ _ ha
  rwa [Algebra.smul_def] at this

theorem unit_eq_one {ε : (𝓞 F)ˣ} {b : F} (hb : b ≠ 0) (h : ((ε : 𝓞 F) : F) * b = b) : ε = 1 := by
  have h1 : ((ε : 𝓞 F) : F) = 1 := mul_right_cancel₀ hb (h.trans (one_mul b).symm)
  apply Units.ext
  apply RingOfIntegers.ext
  simpa using h1

variable (𝔞 𝔟 : Frac F)

theorem mk_eq {p q : LatPair 𝔞 𝔟} (ε : (𝓞 F)ˣ) (h1 : q.1.1 = ((ε : 𝓞 F) : F) * p.1.1)
    (h2 : q.1.2 = ((ε : 𝓞 F) : F) * p.1.2) : Quotient.mk (latRel 𝔞 𝔟) p = Quotient.mk _ q :=
  Quotient.sound (Exists.intro ε ⟨h1, h2⟩)

theorem mkU_eq {I : FractionalIdeal (𝓞 F)⁰ F} {x y : NZ I} (ε : (𝓞 F)ˣ) (h : y.1 = ((ε : 𝓞 F) : F) * x.1) :
    Quotient.mk (unitRel I) x = Quotient.mk _ y :=
  Quotient.sound (Exists.intro ε h)

def leftPt (c : Quotient (unitRel (latM 𝔞))) : LatPair 𝔞 𝔟 :=
  ⟨(c.out.1, 0), c.out.2.1, ((𝔟 : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F).zero_mem, fun h => c.out.2.2 (congrArg Prod.fst h)⟩

def rightPt (c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F))) (a : {a : F // a ∈ latM 𝔞}) : LatPair 𝔞 𝔟 :=
  ⟨(a.1, c.out.1), a.2, c.out.2.1, fun h => c.out.2.2 (congrArg Prod.snd h)⟩

def regroupMap : Quotient (unitRel (latM 𝔞)) ⊕
    (Σ _ : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)), {a : F // a ∈ latM 𝔞}) → Quotient (latRel 𝔞 𝔟)
  | Sum.inl c => Quotient.mk _ (leftPt 𝔞 𝔟 c)
  | Sum.inr s => Quotient.mk _ (rightPt 𝔞 𝔟 s.1 s.2)

theorem regroupMap_injective : Function.Injective (regroupMap 𝔞 𝔟) := by
  rintro (c | ⟨c, a⟩) (c' | ⟨c', a'⟩) h
  · obtain ⟨ε, h1, -⟩ := Quotient.exact h
    congr 1
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    exact mkU_eq ε h1
  · obtain ⟨ε, -, h2⟩ := Quotient.exact h
    exact absurd (h2.trans (mul_zero _)) c'.out.2.2
  · obtain ⟨ε, -, h2⟩ := Quotient.exact h
    dsimp only [leftPt, rightPt] at h2
    have := congrArg (fun x => (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * x) h2
    simp only [← mul_assoc, unit_inv_mul, one_mul, mul_zero] at this
    exact absurd this.symm c.out.2.2
  · obtain ⟨ε, h1, h2⟩ := Quotient.exact h
    have hc : c = c' := by
      rw [← Quotient.out_eq c, ← Quotient.out_eq c']
      exact mkU_eq ε h2
    subst hc
    have hε : ε = 1 := unit_eq_one c.out.2.2 h2.symm
    subst hε
    have ha : a' = a := Subtype.ext (by simpa [rightPt] using h1)
    subst ha
    rfl

theorem regroupMap_surjective : Function.Surjective (regroupMap 𝔞 𝔟) := by
  intro q
  induction q using Quotient.inductionOn with
  | h p =>
  obtain ⟨⟨a, b⟩, ha, hb, hne⟩ := p
  by_cases hb0 : b = 0
  · subst hb0
    have ha0 : a ≠ 0 := fun h => hne (by simp [h])
    obtain ⟨ε, hε⟩ : (unitRel (latM 𝔞)).r ⟨a, ha, ha0⟩ (Quotient.mk (unitRel (latM 𝔞)) ⟨a, ha, ha0⟩).out :=
      Quotient.exact (Quotient.out_eq _).symm
    exact ⟨Sum.inl (Quotient.mk _ ⟨a, ha, ha0⟩), (mk_eq 𝔞 𝔟 ε hε (mul_zero _).symm).symm⟩
  · obtain ⟨ε, hε⟩ : (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)).r ⟨b, hb, hb0⟩
        (Quotient.mk (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) ⟨b, hb, hb0⟩).out :=
      Quotient.exact (Quotient.out_eq _).symm
    exact ⟨Sum.inr ⟨Quotient.mk _ ⟨b, hb, hb0⟩, ⟨_, unit_mul_mem ε ha⟩⟩, (mk_eq 𝔞 𝔟 ε rfl hε).symm⟩

theorem g_out {g : F × F → ℂ}
    (hg : ∀ (ε : (𝓞 F)ˣ) (a b : F), g (((ε : 𝓞 F) : F) * a, ((ε : 𝓞 F) : F) * b) = g (a, b))
    (p : LatPair 𝔞 𝔟) : g (Quotient.mk (latRel 𝔞 𝔟) p).out.1 = g p.1 := by
  obtain ⟨ε, h1, h2⟩ : (latRel 𝔞 𝔟).r (Quotient.mk (latRel 𝔞 𝔟) p).out p := Quotient.exact (Quotient.out_eq _)
  have : p.1 = (((ε : 𝓞 F) : F) * (Quotient.mk (latRel 𝔞 𝔟) p).out.1.1,
      ((ε : 𝓞 F) : F) * (Quotient.mk (latRel 𝔞 𝔟) p).out.1.2) := Prod.ext h1 h2
  rw [this, hg]

end GlobalTheory.HeckeTwo.Regroup

theorem GlobalTheory.HeckeTwo.Regroup.tsum_latRel_regroup : ∀ (F : Type) [Field F] [NumberField F] (𝔞 𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (g : F × F → ℂ), (∀ (ε : (NumberField.RingOfIntegers F)ˣ) (a b : F), g (((ε : NumberField.RingOfIntegers F) : F) * a, ((ε : NumberField.RingOfIntegers F) : F) * b) = g (a, b)) → Summable (fun c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟) => g c.out.1) → Summable (fun c : Quotient (GlobalTheory.HeckeTwo.unitRel (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞)) => g (c.out.1, 0)) ∧ (∀ c : Quotient (GlobalTheory.HeckeTwo.unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)), Summable (fun a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞} => g (a.1, c.out.1))) ∧ Summable (fun c : Quotient (GlobalTheory.HeckeTwo.unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)) => ∑' a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞}, g (a.1, c.out.1)) ∧ ∑' c : Quotient (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latRel 𝔞 𝔟), g c.out.1 = ∑' c : Quotient (GlobalTheory.HeckeTwo.unitRel (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞)), g (c.out.1, 0) + ∑' c : Quotient (GlobalTheory.HeckeTwo.unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)), ∑' a : {a : F // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞}, g (a.1, c.out.1) := by
  intro F _ _ 𝔞 𝔟 g hg hs
  open GlobalTheory.HeckeTwo.Regroup in
  let e := Equiv.ofBijective _ ⟨regroupMap_injective 𝔞 𝔟, regroupMap_surjective 𝔞 𝔟⟩
  let h : Quotient (unitRel (latM 𝔞)) ⊕
      (Σ _ : Quotient (unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)), {a : F // a ∈ latM 𝔞}) → ℂ :=
    Sum.elim (fun c => g (c.out.1, 0)) (fun s => g (s.2.1, s.1.out.1))
  have hfe : (fun c : Quotient (latRel 𝔞 𝔟) => g c.out.1) ∘ e = h := by
    funext x
    rcases x with c | ⟨c, a⟩
    · exact GlobalTheory.HeckeTwo.Regroup.g_out 𝔞 𝔟 hg _
    · exact GlobalTheory.HeckeTwo.Regroup.g_out 𝔞 𝔟 hg _
  have hsh : Summable h := hfe ▸ (e.summable_iff).2 hs
  have hl : Summable (h ∘ Sum.inl) := hsh.comp_injective Sum.inl_injective
  have hr : Summable (h ∘ Sum.inr) := hsh.comp_injective Sum.inr_injective
  have hr' : Summable (fun s : (Σ _ : Quotient (unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)),
      {a : F // a ∈ latM 𝔞}) => g (s.2.1, s.1.out.1)) := hr
  refine ⟨hl, fun c => hr'.sigma_factor c, hr'.sigma, ?_⟩
  rw [← e.tsum_eq, show (∑' x, g (e x).out.1) = ∑' x, h x from congrArg tsum hfe, hl.tsum_sum hr]
  exact congrArg₂ (· + ·) rfl hr'.tsum_sigma
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedHarishChandraInductionGLIsTwistedClassFun
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem gal_id_eq {F : Type} [Field F] (n : ℕ) (y : GL (Fin n) F) : gal (RingHom.id F) n y = y := by
  ext i j; simp [gal]

theorem hcTw_twisted_class {F : Type} [Field F] (t : F →+* F) (a b n : ℕ) (α : GL (Fin a) F → ℂ)
    (β : GL (Fin b) F → ℂ) (x y : GL (Fin n) F) :
    hcTw t a b α β n (y⁻¹ * x * gal t n y) = hcTw t a b α β n x := by
  unfold hcTw
  congr 1
  have h : ∀ z : GL (Fin n) F, z⁻¹ * (y⁻¹ * x * gal t n y) * gal t n z
      = (y * z)⁻¹ * x * gal t n (y * z) := by
    intro z; simp only [map_mul, mul_inv_rev]; group
  simp_rw [h]
  exact finsum_comp_equiv (Equiv.mulLeft y)
    (f := fun w : GL (Fin n) F => if InPar a (w⁻¹ * x * gal t n w) then
      α (tlG a (w⁻¹ * x * gal t n w)) * β (brG a b (w⁻¹ * x * gal t n w)) else 0)

theorem hc_isCl {F : Type} [Field F] (a b n : ℕ) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) :
    IsCl (hc a b α β n) := by
  intro x y
  have := hcTw_twisted_class (RingHom.id F) a b n α β x y
  rw [gal_id_eq] at this
  exact this

theorem psiG_isCl {F : Type} [Field F] (S : F[X] → ℂ) (n : ℕ) : IsCl (psiG S n) := by
  intro x y
  unfold psiG
  let e : (Fin n → F) ≃ₗ[F] (Fin n → F) :=
    LinearEquiv.ofLinear (Matrix.toLin' ((y⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
      (Matrix.toLin' ((y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F))
      (by rw [← Matrix.toLin'_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.toLin'_one])
  have he : e.conj (Matrix.toLin' ((x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) =
      Matrix.toLin' (((y⁻¹ * x * y : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) := by
    rw [LinearEquiv.conj_apply, Units.val_mul, Units.val_mul, Matrix.toLin'_mul, Matrix.toLin'_mul]
    rfl
  rw [← he, psi_conj]

theorem chG_isCl {F : Type} [Field F] (S : F[X] → ℂ) (n : ℕ) : IsCl (chG S n) := by
  intro x y
  unfold chG
  congr 1
  have := Matrix.charpoly_units_conj (y⁻¹ : GL (Fin n) F) (x : Matrix (Fin n) (Fin n) F)
  rw [← this, Units.val_mul, Units.val_mul]
  congr 2
  rw [← Matrix.coe_units_inv, inv_inv]

theorem twisted_class_main : ∀ (F : Type) [Field F] [Finite F], ∀ (t : F →+* F) (a b n : ℕ) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ), (∀ x y, hcTw t a b α β n (y⁻¹ * x * gal t n y) = hcTw t a b α β n x) ∧ IsCl (hc a b α β n) ∧ ∀ S : F[X] → ℂ, IsCl (psiG S n) ∧ IsCl (chG S n) := by
  intro F _ _ t a b n α β
  exact ⟨fun x y => hcTw_twisted_class t a b n α β x y, hc_isCl a b n α β,
    fun S => ⟨psiG_isCl S n, chG_isCl S n⟩⟩

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDetIsTA
section
open NumberField Matrix GlobalTheory.AdLat GlobalTheory.UCls

noncomputable section
namespace GlobalTheory
open IsDedekindDomain
open scoped TensorProduct

theorem isTA_det_of_isUA {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {r : ℕ}
    (c : E ≃ₐ[F] E) (G : Matrix (Fin r) (Fin r) E) (g : Matrix (Fin r) (Fin r) (RA F E))
    (hG : G.det ≠ 0) (hg : IsUA c G g) : IsTA c g.det := by
  set σ := sg (FiniteAdeleRing (𝓞 F) F) c with hσ
  set G' : Matrix (Fin r) (Fin r) (RA F E) := G.map (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E) with hG'
  have hM : gᵀ * G' * g.map σ = G' := by
    ext a b
    have h := hg.2 (Pi.single a 1) (Pi.single b 1)
    simp only [hermA, Matrix.mulVec_single_one] at h
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    convert h using 1
    · rfl
    · simp [G', Pi.single_apply, apply_ite σ]
  have hdet := congrArg Matrix.det hM
  have hs : (g.map σ).det = σ g.det := by
    rw [show g.map σ = (σ : RA F E →+* RA F E).mapMatrix g from rfl, ← RingHom.map_det]; rfl
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hs] at hdet
  have hG'det : G'.det = (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ G.det := by
    rw [hG', show G.map (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E) =
      ((Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E) : E →+* RA F E).mapMatrix G from rfl,
      ← RingHom.map_det]; rfl
  have hu : IsUnit G'.det := by
    rw [hG'det]
    refine IsUnit.of_mul_eq_one ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ G.det⁻¹) ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_inv_cancel₀ hG]
    rfl
  unfold IsTA
  have : g.det * σ g.det * G'.det = 1 * G'.det := by
    rw [one_mul]; convert hdet using 1; ring
  exact hu.mul_right_cancel this

theorem unitary_det_isTA : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (g : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), G.det ≠ 0 → IsUA (IsCMField.complexConj E) G g → IsTA (IsCMField.complexConj E) g.det :=
  fun _ _ _ _ _ _ _ hG hg => isTA_det_of_isUA _ _ _ hG hg

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeCoordinateBoxLeHadamardStatement
section
open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.volume_coordinateBox_le_hadamard : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (K : Type) [Fintype K] (w : K → V) (t : ℝ), 0 ≤ t → Fintype.card K = Module.finrank ℝ V → MeasureTheory.volume {y : V | ∃ c : K → ℝ, (∀ k, |c k| ≤ t) ∧ y = ∑ k, c k • w k} ≤ ENNReal.ofReal ((2 * t) ^ Fintype.card K * ∏ k, ‖w k‖) := by
  first | exact @GlobalTheory.CoordBox.volume_coordBox_le | exact GlobalTheory.CoordBox.volume_coordBox_le | (intros; apply GlobalTheory.CoordBox.volume_coordBox_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassEisensteinNonholomorphicIdentity
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory

theorem wB_nonhol_correction : ∀ (N : ℕ) (y : Fin 2 → ZMod N) (τ : ℍ), ((Real.pi / τ.im : ℝ) : ℂ) / (2 * Real.pi * Complex.I) ^ 2 - wB N y τ = -(G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 + wp N y τ) := by
  intro N y τ
  rw [wB, gN, G2s]
  push_cast
  ring

end GlobalTheory
end

