module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTensorUniversalProperty
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0418
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0406
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0428
public import Development.AbelianVarietyTheory.Definitions.Divisors.PullbackBijectiveDegreesOneTwo
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0422
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0423
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0326
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0366
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0414

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinSeriesLatticeDifferentiableOn
section
open scoped nonZeroDivisors
open Metric Complex

namespace GlobalTheory

open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization

theorem eisTerm_at_zero_eq {F : Type} [Field F] [NumberField F] (k : ℕ) (z : Emb F → ℂ) (p : F × F) :
    eisTerm k 0 z p = (∏ τ, latPt z p τ)⁻¹ ^ k := by
  simp [eisTerm]

theorem norm_latPt_le_two_mul_of_near {F : Type} [Field F] [NumberField F] {z z₀ : Emb F → ℂ} {r : ℝ}
    (hr : ∀ τ, 2 * r ≤ (z₀ τ).im) (hz : ‖z - z₀‖ < r) (p : F × F) (τ : Emb F) :
    ‖latPt z₀ p τ‖ ≤ 2 * ‖latPt z p τ‖ := by
  have h1 : ‖z τ - z₀ τ‖ < r := lt_of_le_of_lt (norm_le_pi_norm (z - z₀) τ) hz
  have h2 : r ≤ (z τ).im := by
    have h3 := abs_im_le_norm (z τ - z₀ τ)
    rw [sub_im] at h3
    have h4 := (abs_le.1 (h3.trans h1.le)).1
    linarith [hr τ]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have e : latPt z₀ p τ = latPt z p τ + 2 * (Real.pi : ℂ) * I * ((τ p.2 : ℝ) : ℂ) * (z₀ τ - z τ) := by
    simp only [latPt]; ring
  have hn : ∀ w : ℂ, ‖2 * (Real.pi : ℂ) * I * w‖ = 2 * Real.pi * ‖w‖ := by
    intro w
    rw [norm_mul, norm_mul, norm_mul, norm_I, Complex.norm_real, Real.norm_of_nonneg hpi.le]
    norm_num
  have hlow : 2 * Real.pi * (|τ p.2| * r) ≤ ‖latPt z p τ‖ := by
    rw [latPt, hn]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine le_trans ?_ (abs_im_le_norm _)
    simp only [add_im, ofReal_im, mul_im, ofReal_re, zero_mul, add_zero, zero_add]
    rw [abs_mul, abs_of_pos (lt_of_lt_of_le (lt_of_le_of_lt (norm_nonneg _) hz) h2)]
    exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  have hup : ‖2 * (Real.pi : ℂ) * I * ((τ p.2 : ℝ) : ℂ) * (z₀ τ - z τ)‖ ≤ 2 * Real.pi * (|τ p.2| * r) := by
    rw [show 2 * (Real.pi : ℂ) * I * ((τ p.2 : ℝ) : ℂ) * (z₀ τ - z τ) = 2 * (Real.pi : ℂ) * I * (((τ p.2 : ℝ) : ℂ) * (z₀ τ - z τ)) by ring, hn, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_sub_rev]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1.le (abs_nonneg _)) (by positivity)
  rw [e]
  linarith [norm_add_le (latPt z p τ) (2 * (Real.pi : ℂ) * I * ((τ p.2 : ℝ) : ℂ) * (z₀ τ - z τ))]

theorem norm_eisTerm_zero_le_of_near {F : Type} [Field F] [NumberField F] {z z₀ : Emb F → ℂ} {r : ℝ}
    (hz₀ : z₀ ∈ upperHalf F) (hr : ∀ τ, 2 * r ≤ (z₀ τ).im) (hz : ‖z - z₀‖ < r) (k : ℕ) {p : F × F} (hp : p ≠ 0) :
    ‖eisTerm k 0 z p‖ ≤ (2 ^ Fintype.card (Emb F)) ^ k * ‖eisTerm k 0 z₀ p‖ := by
  rw [eisTerm_at_zero_eq, eisTerm_at_zero_eq, norm_pow, norm_pow, norm_inv, norm_inv, norm_prod, norm_prod, ← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ k
  have hA : 0 < ∏ τ, ‖latPt z₀ p τ‖ :=
    Finset.prod_pos fun τ _ => norm_pos_iff.2 (latPt_ne_zero hz₀ hp τ)
  have hAB : ∏ τ, ‖latPt z₀ p τ‖ ≤ 2 ^ Fintype.card (Emb F) * ∏ τ, ‖latPt z p τ‖ := by
    rw [← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod₀ (fun τ _ => norm_nonneg _) fun τ _ => norm_latPt_le_two_mul_of_near hr hz p τ
  have h2 : (0 : ℝ) < 2 ^ Fintype.card (Emb F) := by positivity
  have hB : 0 < ∏ τ, ‖latPt z p τ‖ := by
    by_contra h
    push_neg at h
    nlinarith
  rw [inv_le_comm₀ hB (by positivity), mul_inv, inv_inv]
  calc (2 ^ Fintype.card (Emb F))⁻¹ * ∏ τ, ‖latPt z₀ p τ‖ ≤ (2 ^ Fintype.card (Emb F))⁻¹ * (2 ^ Fintype.card (Emb F) * ∏ τ, ‖latPt z p τ‖) :=
        mul_le_mul_of_nonneg_left hAB (by positivity)
    _ = ∏ τ, ‖latPt z p τ‖ := by field_simp

theorem eisSum_zero_differentiableOn :
    ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : Frac F) (k : ℕ),
      (∀ z ∈ upperHalf F, Summable (eisClass 𝔞 𝔟 k 0 z)) →
      DifferentiableOn ℂ (eisSum 𝔞 𝔟 k 0) (upperHalf F) := by
  intro F _ _ _ 𝔞 𝔟 k hs z₀ hz₀
  obtain ⟨r, hr0, hr⟩ : ∃ r : ℝ, 0 < r ∧ ∀ τ, 2 * r ≤ (z₀ τ).im := by
    rcases isEmpty_or_nonempty (Emb F) with h | h
    · exact ⟨1, one_pos, fun τ => (IsEmpty.false τ).elim⟩
    · refine ⟨(Finset.univ.inf' Finset.univ_nonempty fun τ => (z₀ τ).im) / 2, ?_, fun τ => ?_⟩
      · exact half_pos ((Finset.lt_inf'_iff _).2 fun τ _ => hz₀ τ)
      · have := Finset.inf'_le (fun τ => (z₀ τ).im) (Finset.mem_univ τ)
        linarith
  have hsub : ball z₀ r ⊆ upperHalf F := by
    intro z hz τ
    rw [mem_ball, dist_eq_norm] at hz
    have h1 : ‖z τ - z₀ τ‖ < r := lt_of_le_of_lt (norm_le_pi_norm (z - z₀) τ) hz
    have h3 := abs_im_le_norm (z τ - z₀ τ)
    rw [sub_im] at h3
    have h4 := (abs_le.1 (h3.trans h1.le)).1
    linarith [hr τ]
  have hdiff : ∀ c : Quotient (latRel 𝔞 𝔟), DifferentiableOn ℂ (fun z => eisClass 𝔞 𝔟 k 0 z c) (ball z₀ r) := by
    intro c z hz
    have hp : c.out.1 ≠ 0 := c.out.2.2.2
    have e : (fun z => eisClass 𝔞 𝔟 k 0 z c) = fun z => (∏ τ, latPt z c.out.1 τ)⁻¹ ^ k := by
      funext z; exact eisTerm_at_zero_eq k z c.out.1
    rw [e]
    have hP : Differentiable ℂ (fun z : Emb F → ℂ => ∏ τ, latPt z c.out.1 τ) := by
      unfold latPt; fun_prop
    have hne : ∏ τ, latPt z c.out.1 τ ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun τ _ => latPt_ne_zero (hsub hz) hp τ
    exact ((hP z).inv hne).pow k |>.differentiableWithinAt
  have hbd : ∀ c : Quotient (latRel 𝔞 𝔟), ∀ z ∈ ball z₀ r,
      ‖eisClass 𝔞 𝔟 k 0 z c‖ ≤ (2 ^ Fintype.card (Emb F)) ^ k * ‖eisClass 𝔞 𝔟 k 0 z₀ c‖ := by
    intro c z hz
    rw [mem_ball, dist_eq_norm] at hz
    exact norm_eisTerm_zero_le_of_near hz₀ hr hz k c.out.2.2.2
  have hsum : Summable fun c => (2 ^ Fintype.card (Emb F) : ℝ) ^ k * ‖eisClass 𝔞 𝔟 k 0 z₀ c‖ :=
    (summable_norm_iff.2 (hs z₀ hz₀)).mul_left _
  have h := GlobalTheory.differentiableOn_tsum_of_norm_le (Emb F → ℂ) (Quotient (latRel 𝔞 𝔟)) (ball z₀ r)
    (fun c z => eisClass 𝔞 𝔟 k 0 z c) _ isOpen_ball hdiff hsum hbd
  exact (h.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr0))).differentiableWithinAt

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTensorUniversalPropertyStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTensor_universal_property : ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → (∀ {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J'), ∃! u : K ⟶ K', τ.Compat ν f g u) ∧ (I.IsStrictlyGE 0 → J.IsStrictlyGE 0 → K.IsStrictlyGE 0) ∧ ∀ {K' : Cx R} (u : K ⟶ K'), ∃ ν : Pair I J K', τ.Compat ν (𝟙 I) (𝟙 J) u := by
  first | (exact @GlobalTheory.EtC.Pair.isTensor_universal) | (exact GlobalTheory.EtC.Pair.isTensor_universal) | (intros; apply GlobalTheory.EtC.Pair.isTensor_universal  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaDecompositionAdmissibleFamily
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.IwaFam

open Matrix

lemma det_one_add_vmv {R : Type} [CommRing R] {n : ℕ} (a b : Fin n → R) :
    (1 + Matrix.vecMulVec a b).det = 1 + b ⬝ᵥ a := by
  have h := Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Unit) a b
  have e : Matrix.replicateCol Unit a * Matrix.replicateRow Unit b = Matrix.vecMulVec a b := by
    ext i j; simp [Matrix.mul_apply, Matrix.vecMulVec_apply]
  rwa [e] at h

variable {k F : Type} [Field k] [Field F] [Algebra k F]

lemma val_det_le_one (v : Place k F) {n : ℕ} (M : Matrix (Fin n) (Fin n) F)
    (h : ∀ i j, v.1 (M i j) ≤ 1) : v.1 M.det ≤ 1 := by
  let M' : Matrix (Fin n) (Fin n) v.O := Matrix.of fun i j => ⟨M i j, (Valuation.mem_valuationSubring_iff _ _).2 (h i j)⟩
  have e : v.O.subtype M'.det = M.det := by rw [RingHom.map_det]; rfl
  rw [← e]; exact (Valuation.mem_valuationSubring_iff _ _).1 M'.det.2

lemma eq_one_of_mul {a b : WithZero (Multiplicative ℤ)} (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : b = 1 :=
  le_antisymm hb (calc 1 = a * b := h.symm
    _ ≤ b := mul_le_of_le_one_left' ha)

lemma val_sign (v : Place k F) {n : ℕ} (σ : Equiv.Perm (Fin n)) : v.1 ((Equiv.Perm.sign σ : ℤ) : F) = 1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

lemma exists_u (v : Place k F) {r : ℕ} (y : Fin (r+1) → F) (hy : y ≠ 0) :
    ∃ u : Matrix (Fin (r+1)) (Fin (r+1)) F, Unimod v u ∧ ∀ a : Fin r, (u *ᵥ y) a.succ = 0 := by
  obtain ⟨-, -, -, -, -, -, hmax, -⟩ := _root_.GlobalTheory.Nef.ord_calculus k F v
  obtain ⟨i, hi, -, -, hle⟩ := hmax (r+1) y hy
  set c : Fin (r+1) → F := fun j => if j = i then 0 else y j / y i with hc
  set u0 : Matrix (Fin (r+1)) (Fin (r+1)) F := 1 + Matrix.vecMulVec (-c) (Pi.single i 1) with hu0
  have hcle : ∀ j, v.1 (c j) ≤ 1 := by
    intro j; simp only [hc]; split_ifs
    · simp
    · rw [Valuation.map_div]
      exact div_le_one_of_le₀ (hle j) zero_le'
  have hu0y : ∀ j, (u0 *ᵥ y) j = y j - c j * y i := by
    intro j
    simp only [hu0, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
    simp [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.single_apply, ite_mul]
    ring
  refine ⟨u0.submatrix (Equiv.swap 0 i) id, ⟨?_, ?_⟩, ?_⟩
  · intro a b
    simp only [Matrix.submatrix_apply, id, hu0, Matrix.add_apply, Matrix.vecMulVec_apply]
    refine Valuation.map_add_le _ ?_ ?_
    · rw [Matrix.one_apply]; split_ifs <;> simp
    · rw [Pi.neg_apply, Valuation.map_mul, Valuation.map_neg]
      refine mul_le_one' (hcle _) ?_
      rw [Pi.single_apply]; split_ifs <;> simp
  · rw [Matrix.det_permute, det_one_add_vmv, Valuation.map_mul, val_sign]
    simp [hc]
  · intro a
    show (u0 *ᵥ y) (Equiv.swap 0 i a.succ) = 0
    have hne : Equiv.swap 0 i a.succ ≠ i := by
      intro h
      have := congrArg (Equiv.swap 0 i) h
      rw [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
      exact Fin.succ_ne_zero a this
    rw [hu0y]; simp only [hc, if_neg hne]; field_simp; ring

lemma exists_h {n : ℕ} (x : Fin (n+1) → F) (hx : x ≠ 0) :
    ∃ h : Matrix (Fin (n+1)) (Fin (n+1)) F, h.det ≠ 0 ∧ ∀ a, h a 0 = x a := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hc; push_neg at hc; exact hx (funext hc)
  refine ⟨(1 + Matrix.vecMulVec (x - Pi.single i 1) (Pi.single i 1)).submatrix id (Equiv.swap 0 i), ?_, ?_⟩
  · rw [Matrix.det_permute', det_one_add_vmv]
    simp [hi]
    split_ifs <;> simp
  · intro a
    simp [Matrix.submatrix_apply, Matrix.one_apply, Matrix.vecMulVec_apply]
    split_ifs <;> simp_all

lemma unimod_ae [IsAlgClosed k] [CharZero k] (hF : IsFF k F) {n : ℕ} (h : Matrix (Fin n) (Fin n) F) (hd : h.det ≠ 0) :
    {v : Place k F | ¬ Unimod v h}.Finite := by
  have fin1 : ∀ c : F, {v : Place k F | ¬ v.1 c ≤ 1}.Finite := by
    intro c
    by_cases hc : c = 0
    · simp [hc]
    · exact (_root_.GlobalTheory.Nef.finite_support_and_sum_ord_eq_zero k F hF c hc).1.subset fun v hv h1 => hv (le_of_eq h1)
  refine ((_root_.GlobalTheory.Nef.finite_support_and_sum_ord_eq_zero k F hF _ hd).1.union (Set.finite_iUnion fun p : Fin n × Fin n => fin1 (h p.1 p.2))).subset ?_
  intro v hv
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_iUnion]
  by_contra hc; push_neg at hc
  exact hv ⟨fun i j => hc.2 (i, j), hc.1⟩

lemma unimod_pull {E : Type} [Field E] [Algebra k E] [Algebra F E] (ρ : Place k E → Place k F) (hρ : IsRes ρ)
    (p : Place k E) {n : ℕ} (u : Matrix (Fin n) (Fin n) F) (hu : Unimod (ρ p) u) :
    Unimod p (u.map (algebraMap F E)) := by
  refine ⟨fun i j => (hρ p _).2 (hu.1 i j), ?_⟩
  have e : (u.map (algebraMap F E)).det = algebraMap F E u.det := (RingHom.map_det _ _).symm
  have hd0 : u.det ≠ 0 := fun h0 => by
    have := hu.2; rw [h0, Valuation.map_zero] at this; exact zero_ne_one this
  have h1 : p.1 (algebraMap F E u.det) ≤ 1 := (hρ p _).2 hu.2.le
  have h2 : p.1 (algebraMap F E u.det⁻¹) ≤ 1 := (hρ p _).2 (by rw [map_inv₀, hu.2, inv_one])
  have h3 : p.1 (algebraMap F E u.det⁻¹) * p.1 (algebraMap F E u.det) = 1 := by
    rw [← Valuation.map_mul, ← map_mul, inv_mul_cancel₀ hd0, map_one, Valuation.map_one]
  rw [e]; exact eq_one_of_mul h2 h1 h3

lemma ordVec_pull {E : Type} [Field E] [Algebra k E] [Algebra F E] (ρ : Place k E → Place k F) (hρ : IsRes ρ)
    {n : ℕ} (u g h : Place k F → Matrix (Fin n) (Fin n) F) (hu : ∀ v, Unimod v (u v)) (p : Place k E) (w : Fin n → E) :
    ordVec p (pullAd ρ (fun v => u v * g v * h v) p *ᵥ w) = ordVec p (pullAd ρ g p *ᵥ ((h (ρ p)).map (algebraMap F E) *ᵥ w)) := by
  obtain ⟨-, -, -, -, -, -, -, -, hnrm, -⟩ := _root_.GlobalTheory.Nef.ord_calculus k E p
  simp only [pullAd, Matrix.map_mul]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  simp only [ordVec, hnrm _ _ _ (unimod_pull ρ hρ p _ (hu (ρ p)))]

end GlobalTheory.IwaFam


open Matrix in
theorem GlobalTheory.iwasawa_family : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (r : ℕ) (g : Place k F → Matrix (Fin (r + 1)) (Fin (r + 1)) F), admitted g → ∀ x : Fin (r + 1) → F, x ≠ 0 → ∃ (h : Matrix (Fin (r + 1)) (Fin (r + 1)) F) (u : Place k F → Matrix (Fin (r + 1)) (Fin (r + 1)) F), h.det ≠ 0 ∧ (∀ v, Unimod v (u v)) ∧ (∀ (v : Place k F) (i : Fin r), (u v * g v * h) i.succ 0 = 0) ∧ admitted (fun v => u v * g v * h) ∧ admitted (fun v => (u v * g v * h).submatrix Fin.succ Fin.succ) ∧ deg g = degLine g x + deg (fun v => (u v * g v * h).submatrix Fin.succ Fin.succ) ∧ ∑ᶠ v, ord v ((u v * g v * h) 0 0) = degLine g x ∧ ∀ b : ℝ, LinesLE g b → LinesLE (fun v => u v * g v * h) b := by
  intro k F _ _ _ _ _ hF r g hg x hx
  obtain ⟨h, hdet, hcol⟩ := GlobalTheory.IwaFam.exists_h x hx
  have hy : ∀ v, g v *ᵥ x ≠ 0 := fun v h0 => (hg.1 v) (Matrix.exists_mulVec_eq_zero_iff.1 ⟨x, hx, h0⟩)
  choose u hu hz using fun v => GlobalTheory.IwaFam.exists_u v (g v *ᵥ x) (hy v)
  have hcol0 : ∀ v a, (u v * g v * h) a 0 = (u v *ᵥ (g v *ᵥ x)) a := by
    intro v a
    rw [Matrix.mulVec_mulVec, Matrix.mul_apply]
    simp only [hcol]
    rfl
  have hz' : ∀ v (i : Fin r), (u v * g v * h) i.succ 0 = 0 := fun v i => by rw [hcol0]; exact hz v i
  have hdetA : ∀ v, (u v * g v * h).det = (u v * g v * h) 0 0 * ((u v * g v * h).submatrix Fin.succ Fin.succ).det := by
    intro v
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    simp [hz', Fin.succAbove_zero]
  have hdu : ∀ v, (u v).det ≠ 0 := fun v h0 => by
    have := (hu v).2; rw [h0, Valuation.map_zero] at this; exact zero_ne_one this
  have hdA : ∀ v, (u v * g v * h).det ≠ 0 := fun v => by
    rw [Matrix.det_mul, Matrix.det_mul]; exact mul_ne_zero (mul_ne_zero (hdu v) (hg.1 v)) hdet
  have h00 : ∀ v, (u v * g v * h) 0 0 ≠ 0 := fun v h0 => hdA v (by rw [hdetA, h0, zero_mul])
  have hdS : ∀ v, ((u v * g v * h).submatrix Fin.succ Fin.succ).det ≠ 0 := fun v h0 => hdA v (by rw [hdetA, h0, mul_zero])

  have hov : ∀ v, ordVec v (g v *ᵥ x) = ord v ((u v * g v * h) 0 0) := by
    intro v
    obtain ⟨-, -, -, -, -, -, hmax, -, hnrm, -⟩ := _root_.GlobalTheory.Nef.ord_calculus k F v
    have hzne : u v *ᵥ (g v *ᵥ x) ≠ 0 := fun h0 => hdu v (Matrix.exists_mulVec_eq_zero_iff.1 ⟨_, hy v, h0⟩)
    obtain ⟨i, hi, -, hoi, -⟩ := hmax _ _ hzne
    have hi0 : i = 0 := by
      induction i using Fin.cases with
      | zero => rfl
      | succ j => exact absurd (hz v j) hi
    subst hi0
    have e1 : ordVec v (g v *ᵥ x) = ordVec v (u v *ᵥ (g v *ᵥ x)) := by
      simp only [ordVec, hnrm _ _ _ (hu v)]
    rw [e1, hoi, hcol0]

  have hpt : ∀ v, ord v (g v).det + ord v h.det = ord v ((u v * g v * h) 0 0) + ord v ((u v * g v * h).submatrix Fin.succ Fin.succ).det := by
    intro v
    obtain ⟨hmul, -, -, hord1, -⟩ := _root_.GlobalTheory.Nef.ord_calculus k F v
    have e1 := hmul _ _ (h00 v) (hdS v)
    rw [← hdetA, Matrix.det_mul, Matrix.det_mul, hmul _ _ (mul_ne_zero (hdu v) (hg.1 v)) hdet,
      hmul _ _ (hdu v) (hg.1 v), (hord1 _ (hdu v)).1 (hu v).2, zero_add] at e1
    exact e1
  have fg : (Function.support fun v => ord v (g v).det).Finite := (_root_.GlobalTheory.Nef.lineFin k F hF _ g hg).1
  have fh : (Function.support fun v : Place k F => ord v h.det).Finite := by
    refine (_root_.GlobalTheory.Nef.finite_support_and_sum_ord_eq_zero k F hF _ hdet).1.subset fun v hv h1 => hv ?_
    exact ((_root_.GlobalTheory.Nef.ord_calculus k F v).2.2.2.1 _ hdet).1 h1
  have fc : (Function.support fun v => ord v ((u v * g v * h) 0 0)).Finite := by
    refine ((_root_.GlobalTheory.Nef.lineFin k F hF _ g hg).2 x hx).1.subset fun v hv h1 => hv ?_
    show ord v ((u v * g v * h) 0 0) = 0
    rw [← hov, ordVec, h1]; simp
  have fd : (Function.support fun v => ord v ((u v * g v * h).submatrix Fin.succ Fin.succ).det).Finite := by
    refine ((fg.union fh).union fc).subset fun v hv => ?_
    by_contra hc
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hc hv
    have := hpt v
    rw [hc.1.1, hc.1.2, hc.2] at this
    exact hv (by linarith)
  have hline : ∑ᶠ v, ord v ((u v * g v * h) 0 0) = degLine g x := by
    unfold degLine; exact finsum_congr fun v => (hov v).symm
  refine ⟨h, u, hdet, hu, hz', ⟨hdA, ?_⟩, ⟨hdS, ?_⟩, ?_, hline, ?_⟩
  · refine ((hg.2).union (GlobalTheory.IwaFam.unimod_ae hF h hdet)).subset fun v hv => ?_
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc hv
    obtain ⟨-, -, -, -, -, -, -, -, -, hprod⟩ := _root_.GlobalTheory.Nef.ord_calculus k F v
    exact hv ((hprod _ _ _ ((hprod _ _ _ (hu v) hc.1).1) hc.2).1)
  · refine ((hg.2).union (GlobalTheory.IwaFam.unimod_ae hF h hdet)).subset fun v hv => ?_
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc hv
    obtain ⟨-, -, -, -, -, -, -, -, -, hprod⟩ := _root_.GlobalTheory.Nef.ord_calculus k F v
    have hA := (hprod _ _ _ ((hprod _ _ _ (hu v) hc.1).1) hc.2).1
    refine hv ⟨fun i j => hA.1 i.succ j.succ, ?_⟩
    have e := hA.2
    rw [hdetA, Valuation.map_mul] at e
    exact GlobalTheory.IwaFam.eq_one_of_mul (hA.1 0 0)
      (GlobalTheory.IwaFam.val_det_le_one v _ fun i j => hA.1 i.succ j.succ) e
  · unfold deg
    rw [← hline, ← finsum_add_distrib fc fd, ← add_zero (∑ᶠ v, ord v (g v).det), ← (_root_.GlobalTheory.Nef.finite_support_and_sum_ord_eq_zero k F hF _ hdet).2,
      ← finsum_add_distrib fg fh]
    exact finsum_congr hpt
  · intro b hb E _ _ _ _ _ ρ hρ w hw
    let h' := h.map (algebraMap F E)
    have hne : h' *ᵥ w ≠ 0 := fun h0 => by
      have e : h'.det = algebraMap F E h.det := (RingHom.map_det _ _).symm
      exact (map_ne_zero _).2 hdet (e ▸ Matrix.exists_mulVec_eq_zero_iff.1 ⟨w, hw, h0⟩)
    have e : degLine (pullAd ρ fun v => u v * g v * h) w = degLine (pullAd ρ g) (h' *ᵥ w) := by
      unfold degLine
      exact finsum_congr fun p => GlobalTheory.IwaFam.ordVec_pull ρ hρ u g (fun _ => h) hu p w
    rw [e]
    exact hb E ρ hρ _ hne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JoinedMapsAgreeCohomologyZeroOneInstancesStatement
section
open CategoryTheory GlobalTheory.CxCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.joinedMapsAgreeCohomologyZeroOne_instances : JoinedOne.{1,1} ∧ JoinedOne.{1,0} ∧ JoinedOne.{0,0} := by
  first | exact @GlobalTheory.CxCoh.joinedOne_inst | exact GlobalTheory.CxCoh.joinedOne_inst | (intros; apply GlobalTheory.CxCoh.joinedOne_inst <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KahlerFormsOverSubalgebraStandardOpenIffPowSmul
section
set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD.OmLoc

variable {k K : Type} [Field k] [Field K] [Algebra k K]

theorem pow_smul_d_mem (B : Subalgebra k K) {f v : K} (hf : f ∈ B) (M : ℕ) (hw : v * f ^ M ∈ B) :
    (f ^ (M + M)) • ι1 (D k K v) ∈ omB k K B 1 := by
  have hD : ∀ u ∈ B, ι1 (D k K u) ∈ omB k K B 1 := by
    intro u hu
    apply Submodule.subset_span
    refine ⟨1, B.one_mem, fun _ => u, fun _ => hu, ?_⟩
    rw [one_smul, ExteriorAlgebra.ιMulti_apply]
    simp
  have hc : ∀ c ∈ B, ∀ a ∈ omB k K B 1, c • a ∈ omB k K B 1 := fun c hc a ha =>
    ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K B 1 1).2.1 a ha).2.2.2 c hc
  have key : (f ^ (M + M)) • ι1 (D k K v) =
      f ^ M • ι1 (D k K (v * f ^ M)) - (v * f ^ M) • ι1 (D k K (f ^ M)) := by
    rw [Derivation.leibniz, map_add (f := _), map_smul, map_smul, smul_add, smul_smul, smul_smul, pow_add,
      mul_comm (f ^ M) v]
    abel
  rw [key]
  exact sub_mem (hc _ (pow_mem hf M) _ (hD _ hw)) (hc _ hw _ (hD _ (pow_mem hf M)))

end GlobalTheory.PD.OmLoc

namespace GlobalTheory

theorem omB_iff_pow_smul : ∀ (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F] [Algebra k K]
    [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F), IsFinCover k K x →
    ∀ (I : Finset (Fin (d + 1))) (i : Fin (d + 1)), i ∈ I → ∀ (q : ℕ) (y : DR k K),
      y ∈ omB k K (rB k K x I) q ↔
        ∃ N : ℕ, (algebraMap F K (∏ j ∈ I, x j / x i) ^ N) • y ∈ omB k K (rB k K x {i}) q := by
  intro k _ _ F K _ _ _ _ _ _ d x h I i hi q y
  set f := algebraMap F K (∏ j ∈ I, x j / x i) with hfdef
  obtain ⟨hmono1, -⟩ := GlobalTheory.T.finite_cover_ring_localization_chart k F K d x h {i} i (Finset.mem_singleton_self i)
  obtain ⟨-, hloc⟩ := GlobalTheory.T.finite_cover_ring_localization_chart k F K d x h I i hi
  have hBB' : rB k K x {i} ≤ rB k K x I := hmono1 I (Finset.singleton_subset_iff.2 hi)
  have hfB : f ∈ rB k K x {i} := by
    have hz : (∏ j ∈ I, x j / x i) ∈ rA k x {i} :=
      Subalgebra.prod_mem _ fun j _ => Algebra.subset_adjoin ⟨i, Finset.mem_singleton_self i, j, rfl⟩
    show IsIntegral (rA k x {i}) f
    exact isIntegral_algebraMap (R := rA k x {i}) (A := K) (x := ⟨_, hz⟩)
  have hf0 : f ≠ 0 :=
    (map_ne_zero (algebraMap F K)).2 (Finset.prod_ne_zero_iff.2 fun j _ => div_ne_zero (h.pd.ne j) (h.pd.ne i))
  have hfinv : f⁻¹ ∈ rB k K x I :=
    (hloc _).2 ⟨1, by rw [pow_one, inv_mul_cancel₀ hf0]; exact Subalgebra.one_mem _⟩
  have hsmul : ∀ (C : Subalgebra k K) (p : ℕ), ∀ c ∈ C, ∀ a ∈ omB k K C p, c • a ∈ omB k K C p :=
    fun C p c hc a ha => ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K C p p).2.1 a ha).2.2.2 c hc
  constructor
  · intro hy
    have hQc : ∀ (p : ℕ) (c : K) (z : DR k K), c ∈ rB k K x I →
        (∃ N : ℕ, f ^ N • z ∈ omB k K (rB k K x {i}) p) → ∃ N : ℕ, f ^ N • (c • z) ∈ omB k K (rB k K x {i}) p := by
      rintro p c z hc ⟨N, hN⟩
      obtain ⟨M, hM⟩ := (hloc c).1 hc
      refine ⟨M + N, ?_⟩
      have e : f ^ (M + N) • (c • z) = (c * f ^ M) • (f ^ N • z) := by
        rw [smul_smul, smul_smul]; congr 1; ring
      rw [e]
      exact hsmul _ p _ hM _ hN
    have hQmul : ∀ (p p' : ℕ) (a b : DR k K), (∃ N : ℕ, f ^ N • a ∈ omB k K (rB k K x {i}) p) →
        (∃ N : ℕ, f ^ N • b ∈ omB k K (rB k K x {i}) p') →
        ∃ N : ℕ, f ^ N • (a * b) ∈ omB k K (rB k K x {i}) (p + p') := by
      rintro p p' a b ⟨N, hN⟩ ⟨N', hN'⟩
      refine ⟨N + N', ?_⟩
      have e : f ^ (N + N') • (a * b) = (f ^ N • a) * (f ^ N' • b) := by
        rw [pow_add, mul_smul, smul_mul_assoc, mul_smul_comm]
      rw [e]
      exact (GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x {i}) p p').1 _ hN _ hN'
    have hQ1 : ∀ v ∈ rB k K x I, ∃ N : ℕ, f ^ N • ι1 (D k K v) ∈ omB k K (rB k K x {i}) 1 := by
      intro v hv
      obtain ⟨M, hM⟩ := (hloc v).1 hv
      exact ⟨M + M, GlobalTheory.PD.OmLoc.pow_smul_d_mem _ hfB M hM⟩
    have hQm : ∀ (n : ℕ) (v : Fin n → K), (∀ j, v j ∈ rB k K x I) →
        ∃ N : ℕ, f ^ N • ExteriorAlgebra.ιMulti K n (fun j => D k K (v j)) ∈ omB k K (rB k K x {i}) n := by
      intro n
      induction n with
      | zero =>
        intro v _
        refine ⟨0, ?_⟩
        rw [pow_zero, one_smul, ExteriorAlgebra.ιMulti_zero_apply]
        exact ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x {i}) 0 0).2.2.2 1).2 ⟨1, Subalgebra.one_mem _, (map_one _).symm⟩
      | succ n ih =>
        intro v hv
        rw [ExteriorAlgebra.ιMulti_succ_apply]
        have := hQmul 1 n _ _ (hQ1 (v 0) (hv 0)) (ih (fun j => v j.succ) fun j => hv j.succ)
        rw [Nat.add_comm 1 n] at this
        exact this
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨b, hb, v, hv, rfl⟩ := hz
      exact hQc q b _ hb (hQm q v hv)
    | zero => exact ⟨0, by rw [smul_zero]; exact zero_mem _⟩
    | add a c _ _ ha hc =>
      obtain ⟨N₁, h₁⟩ := ha
      obtain ⟨N₂, h₂⟩ := hc
      refine ⟨N₁ + N₂, ?_⟩
      rw [smul_add]
      apply add_mem
      · rw [pow_add, mul_comm, mul_smul]
        exact hsmul _ q _ (pow_mem hfB _) _ h₁
      · rw [pow_add, mul_smul]
        exact hsmul _ q _ (pow_mem hfB _) _ h₂
    | smul r a _ ha =>
      obtain ⟨N, hN⟩ := ha
      exact ⟨N, by rw [smul_comm]; exact Submodule.smul_mem _ r hN⟩
  · rintro ⟨N, hN⟩
    have := hsmul _ q (f⁻¹ ^ N) (pow_mem hfinv N) _
      ((GlobalTheory.T.kahlerFormsOverSubalgebra_closure_properties k K (rB k K x {i}) q q).2.2.1 _ hBB' hN)
    rwa [smul_smul, ← mul_pow, inv_mul_cancel₀ hf0, one_pow, one_smul] at this

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NaturalSectionsLinearExtension
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natural_sections_linear_extension : ∀ (R : Type) [CommRing R] (P : PSh) (G : Shv R), Injective G → ∀ {A B : Shv R} (f : A ⟶ B), Mono f → ∀ (ψ : ∀ V : Scheme.{0}, P.obj (op V) → Sec A V →ₗ[ULift.{1} R] Sec G V), (∀ (V W : Scheme.{0}) (w : W ⟶ V) (x : P.obj (op V)) (a : Sec A V), Sec.res w (ψ V x a) = ψ W (P.map w.op x) (Sec.res w a)) → ∃ χ : ∀ V : Scheme.{0}, P.obj (op V) → Sec B V →ₗ[ULift.{1} R] Sec G V, (∀ (V W : Scheme.{0}) (w : W ⟶ V) (x : P.obj (op V)) (b : Sec B V), Sec.res w (χ V x b) = χ W (P.map w.op x) (Sec.res w b)) ∧ ∀ (V : Scheme.{0}) (x : P.obj (op V)) (a : Sec A V), χ V x (Sec.map f a) = ψ V x a := by
  first | (exact @GlobalTheory.natFam_extend_of_injective) | (exact GlobalTheory.natFam_extend_of_injective) | (intros; apply GlobalTheory.natFam_extend_of_injective  <;> assumption)
end

