module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2609
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2584
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2595
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2583
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0582
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1507
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1529
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1537
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBlockSumSelfDualTraceSkewForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2606
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedLinePotentialHessianDetOwnRow
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2

theorem card_row_sub (s : ℕ) (i : Fin s) : Fintype.card {j : Low s // j.1.2 = i} = s - 1 - i := by
  rw [← Fin.card_Ioi, ← Fintype.card_coe]
  refine Fintype.card_congr
    { toFun := fun j => ⟨j.1.1.1, by simpa [Finset.mem_Ioi, ← j.2] using j.1.2⟩
      invFun := fun c => ⟨⟨(c.1, i), Finset.mem_Ioi.mp c.2⟩, rfl⟩
      left_inv := ?_
      right_inv := ?_ }
  · rintro ⟨⟨⟨b, a⟩, h⟩, rfl⟩; rfl
  · rintro ⟨c, hc⟩; rfl

noncomputable def rowEquiv {ι : Type} (m : ι → ℕ) (τ : ι) (i : Fin (m τ)) :
    {j : Low (m τ) // j.1.2 = i} ≃ {j : Cell m // j.root = ⟨τ, i⟩} :=
  Equiv.ofBijective (fun b => ⟨⟨τ, b.1⟩, by simp [Cell.root, b.2]⟩) (by
    constructor
    · rintro ⟨b, hb⟩ ⟨b', hb'⟩ h
      simp only [Subtype.mk.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
      exact Subtype.ext h
    · rintro ⟨⟨σ, l⟩, h⟩
      simp only [Cell.root, Sigma.mk.inj_iff] at h
      obtain ⟨rfl, h2⟩ := h
      exact ⟨⟨l, eq_of_heq h2⟩, rfl⟩)

theorem add_sum_coord_apply {n : ℕ} {B : Type} [Fintype B] (e : B → Fin n) (he : Function.Injective e)
    (z : V n) (t : B → ℂ) (k : Fin n) :
    (z + ∑ a, t a • coordVec (e a)) k = z k + ∑ a, if k = e a then t a else 0 := by
  simp [coordVec, Finset.sum_apply, PiLp.single_apply, Pi.single_apply, mul_ite]

end GlobalTheory.FlagCell2

namespace GlobalTheory.FlagCell2

theorem quad_pos {B : Type} [Fintype B] [DecidableEq B] (Q : Matrix (Option B) (Option B) ℂ) (hQ : Q.PosDef)
    (z : B → ℂ) : 0 < ∑ a, ∑ b, Option.elim a 1 z * Q a b * star (Option.elim b 1 z) := by
  have hv : (fun a => star (Option.elim a 1 z)) ≠ 0 := by
    intro h; have := congrFun h none; simp at this
  have := hQ.dotProduct_mulVec_pos hv
  convert this using 1
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_star, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring
end GlobalTheory.FlagCell2

namespace GlobalTheory.FlagCell2

theorem row_levi_det_of (hR : ∀ (n : ℕ) (B : Type) [Fintype B] [DecidableEq B] (e : B → Fin n), Function.Injective e → ∀ (Q : Matrix (Option B) (Option B) ℂ), Q.IsHermitian → ∀ (u : V n → ℝ) (z : V n), ContDiffAt ℝ 2 u z → (∀ t : B → ℂ, u (z + ∑ a, t a • coordVec (e a)) = Real.log ((∑ a, ∑ b, Option.elim a 1 (fun a => z (e a) + t a) * Q a b * star (Option.elim b 1 (fun b => z (e b) + t b))).re)) → ∀ q : ℂ, q = ∑ a, ∑ b, Option.elim a 1 (fun a => z (e a)) * Q a b * star (Option.elim b 1 (fun b => z (e b))) → q ≠ 0 → ∀ a b : B, leviForm u z (coordVec (e a)) (coordVec (e b)) = Q (some a) (some b) / q - (∑ c, Q (some a) c * star (Option.elim c 1 (fun c => z (e c)))) * (∑ c, Option.elim c 1 (fun c => z (e c)) * Q c (some b)) / q ^ 2) (hD : ∀ (B : Type) [Fintype B] [DecidableEq B] (Q : Matrix (Option B) (Option B) ℂ) (z z' : B → ℂ) (q : ℂ), q = ∑ a, ∑ b, Option.elim a 1 z * Q a b * Option.elim b 1 z' → q ≠ 0 → (Matrix.of fun a b : B => Q (some a) (some b) / q - (∑ c, Q (some a) c * Option.elim c 1 z') * (∑ c, Option.elim c 1 z * Q c (some b)) / q ^ 2).det = Q.det / q ^ (Fintype.card B + 1)) (hQ : ∀ (s : ℕ) (G : Matrix (Fin s) (Fin s) ℂ), G.PosDef → ∀ (y : Low s → ℂ) (i : Fin s), ∃ Q : Matrix (Option {j : Low s // j.1.2 = i}) (Option {j : Low s // j.1.2 = i}) ℂ, Q.PosDef ∧ Q.det * leadMinor (upU y * G * (upU y)ᴴ) i = G.det ∧ ∀ y' : Low s → ℂ, (∀ j : Low s, j.1.2 < i → y' j = y j) → grD (upU y' * G * (upU y')ᴴ) i = (∑ a, ∑ b, Option.elim a 1 (fun a => y' a.1) * Q a b * star (Option.elim b 1 (fun b => y' b.1))).re) (ι : Type) [Fintype ι] (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (w : V n) (x : Root m) (hG : (G (bsL ε w) x.1).PosDef) (hs : MContDiffAt 2 (fun v => G v x.1) (bsL ε w)) : Fintype.card {j : Cell m // j.root = x} = m x.1 - 1 - x.2 ∧ (Matrix.of fun a b : {j : Cell m // j.root = x} => -leviForm (cellPot ε G x) w (coordVec (ε.symm (.inr a.1))) (coordVec (ε.symm (.inr b.1)))).det = (((G (bsL ε w) x.1).det.re / (leadMinor (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2).re / grD (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2 ^ ((m x.1 - 1 - x.2 : ℕ) + 1) : ℝ) : ℂ) := by
  obtain ⟨τ, i⟩ := x
  have hsm := GlobalTheory.CellPotSmooth.cellPot_contDiffAt ι m n d ε G w ⟨τ, i⟩ hG hs
  have hcard : Fintype.card {j : Cell m // j.root = ⟨τ, i⟩} = m τ - 1 - i := by
    rw [← Fintype.card_congr (rowEquiv m τ i), card_row_sub]
  refine ⟨hcard, ?_⟩
  simp only at hG hs hsm ⊢
  let e : {j : Low (m τ) // j.1.2 = i} → Fin n := fun b => ε.symm (.inr ⟨τ, b.1⟩)
  have he : Function.Injective e := by
    intro b b' h
    have := ε.symm.injective h
    simp only [Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at this
    exact Subtype.ext this
  set y : Low (m τ) → ℂ := fun s => fb ε w ⟨τ, s⟩ with hy
  obtain ⟨Q, hQpd, hQdet, hQg⟩ := hQ (m τ) (G (bsL ε w) τ) hG y i
  set q : ℂ := ∑ a, ∑ b, Option.elim a 1 (fun a => w (e a)) * Q a b * star (Option.elim b 1 (fun b => w (e b))) with hq
  have hqpos : 0 < q := quad_pos Q hQpd _
  have hgr : grD (upM (fb ε w) τ * G (bsL ε w) τ * (upM (fb ε w) τ)ᴴ) i = q.re := hQg y (fun _ _ => rfl)
  have hqre : q = ((grD (upM (fb ε w) τ * G (bsL ε w) τ * (upM (fb ε w) τ)ᴴ) i : ℝ) : ℂ) := by
    rw [hgr]; exact Complex.ext rfl (by simp [(Complex.pos_iff.mp hqpos).2])
  have hq0 : q ≠ 0 := hqpos.ne'
  have hstar : ∀ c : Option {j : Low (m τ) // j.1.2 = i}, star (Option.elim c 1 (fun c => w (e c))) = Option.elim c 1 (fun c => star (w (e c))) := by
    intro c; cases c <;> simp
  have hres : ∀ t : {j : Low (m τ) // j.1.2 = i} → ℂ, (fun v => -cellPot ε G ⟨τ, i⟩ v) (w + ∑ a, t a • coordVec (e a)) = Real.log ((∑ a, ∑ b, Option.elim a 1 (fun a => w (e a) + t a) * Q a b * star (Option.elim b 1 (fun b => w (e b) + t b))).re) := by
    intro t
    set w' := w + ∑ a, t a • coordVec (e a) with hw'
    have hb : bsL ε w' = bsL ε w := by
      ext c
      simp only [bsL_apply, hw', add_sum_coord_apply e he]
      rw [Finset.sum_eq_zero]
      · simp
      intro a _
      rw [ite_eq_right]
      simp [e]
    have hf : ∀ s : Low (m τ), fb ε w' ⟨τ, s⟩ = y s + if h : s.1.2 = i then t ⟨s, h⟩ else 0 := by
      intro s
      simp only [fb, hy, hw', add_sum_coord_apply e he]
      congr 1
      split_ifs with h
      · rw [Finset.sum_eq_single ⟨s, h⟩]
        · simp [e]
        · intro b _ hb
          rw [ite_eq_right]
          intro h'
          exact hb (he (show e ⟨s, h⟩ = e b from h')).symm
        · simp
      · refine Finset.sum_eq_zero fun b _ => ?_
        rw [ite_eq_right]
        intro h'
        have := ε.symm.injective h'
        simp only [e, Sum.inr.injEq, Sigma.mk.inj_iff, heq_eq_eq, true_and] at this
        exact h (this ▸ b.2)
    have hfa : ∀ a : Option {j : Low (m τ) // j.1.2 = i}, Option.elim a 1 (fun a => fb ε w' ⟨τ, a.1⟩) = Option.elim a 1 (fun a => w (e a) + t a) := by
      rintro (_ | b)
      · rfl
      · simp only [Option.elim, hf, dite_eq_left b.2]
        rfl
    simp only [cellPot, neg_neg]
    rw [hb, show upM (fb ε w') τ = upU (fun s => fb ε w' ⟨τ, s⟩) from rfl,
      hQg _ (fun j hj => by rw [hf, dite_eq_right (ne_of_lt hj)]; simp)]
    simp only [hfa]
  have hR' := hR n {j : Low (m τ) // j.1.2 = i} e he Q hQpd.1 (fun v => -cellPot ε G ⟨τ, i⟩ v) w hsm.1.neg hres q hq hq0
  have hD' := hD {j : Low (m τ) // j.1.2 = i} Q (fun a => w (e a)) (fun b => star (w (e b))) q (by rw [hq]; simp only [hstar]) hq0
  rw [← Matrix.det_submatrix_equiv_self (rowEquiv m τ i)]
  have hM : (Matrix.of fun a b : {j : Cell m // j.root = ⟨τ, i⟩} => -leviForm (cellPot ε G ⟨τ, i⟩) w (coordVec (ε.symm (.inr a.1))) (coordVec (ε.symm (.inr b.1)))).submatrix (rowEquiv m τ i) (rowEquiv m τ i) = Matrix.of fun a b : {j : Low (m τ) // j.1.2 = i} => Q (some a) (some b) / q - (∑ c, Q (some a) c * Option.elim c 1 (fun b => star (w (e b)))) * (∑ c, Option.elim c 1 (fun a => w (e a)) * Q c (some b)) / q ^ 2 := by
    ext a b
    have := hR' a b
    simp only [leviForm_neg, ContinuousLinearMap.neg_apply, hstar] at this
    rw [Matrix.submatrix_apply, Matrix.of_apply, Matrix.of_apply, ← this]
    rfl
  rw [hM, hD', card_row_sub]
  have hQd := hQpd.det_pos
  have hGd := hG.det_pos
  obtain ⟨hQr, hQi⟩ := Complex.pos_iff.mp hQd
  obtain ⟨hGr, hGi⟩ := Complex.pos_iff.mp hGd
  have h1 : Q.det = (Q.det.re : ℂ) := Complex.ext rfl (by simp [hQi])
  have h2 : (G (bsL ε w) τ).det = ((G (bsL ε w) τ).det.re : ℂ) := Complex.ext rfl (by simp [hGi])
  have hQdet' : Q.det * leadMinor (upM (fb ε w) τ * G (bsL ε w) τ * (upM (fb ε w) τ)ᴴ) i = (G (bsL ε w) τ).det := hQdet
  have hQ0 : (Q.det.re : ℂ) ≠ 0 := by exact_mod_cast hQr.ne'
  have hL : leadMinor (upM (fb ε w) τ * G (bsL ε w) τ * (upM (fb ε w) τ)ᴴ) i = (((G (bsL ε w) τ).det.re / Q.det.re : ℝ) : ℂ) := by
    rw [h1, h2] at hQdet'
    push_cast
    rw [eq_div_iff hQ0, mul_comm]
    exact hQdet'
  rw [hL, Complex.ofReal_re]
  conv_lhs => rw [h1, hqre]
  have hgpos : 0 < grD (upM (fb ε w) τ * G (bsL ε w) τ * (upM (fb ε w) τ)ᴴ) i := hsm.2
  push_cast
  have : ((G (bsL ε w) τ).det.re : ℂ) ≠ 0 := by exact_mod_cast hGr.ne'
  have : (grD (upM (fb ε w) τ * G (bsL ε w) τ * (upM (fb ε w) τ)ᴴ) i : ℂ) ≠ 0 := by exact_mod_cast hgpos.ne'
  field_simp

end GlobalTheory.FlagCell2

namespace GlobalTheory.FlagCell2

theorem row_levi_det (ι : Type) [Fintype ι] (m : ι → ℕ) (n d : ℕ) (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ)
    (w : V n) (x : Root m) (hG : (G (bsL ε w) x.1).PosDef) (hs : MContDiffAt 2 (fun v => G v x.1) (bsL ε w)) :
    Fintype.card {j : Cell m // j.root = x} = m x.1 - 1 - x.2 ∧ (Matrix.of fun a b : {j : Cell m // j.root = x} => -leviForm (cellPot ε G x) w (coordVec (ε.symm (.inr a.1))) (coordVec (ε.symm (.inr b.1)))).det = (((G (bsL ε w) x.1).det.re / (leadMinor (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2).re / grD (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2 ^ ((m x.1 - 1 - x.2 : ℕ) + 1) : ℝ) : ℂ) :=
  row_levi_det_of GlobalTheory.LogHermHess.leviForm_log_herm GlobalTheory.det_schur_bilinear_entry GlobalTheory.FlagCell2.exists_posDef_grD ι m n d ε G w x hG hs

end GlobalTheory.FlagCell2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramIsHermitianL2EqDoubleSum
section
set_option autoImplicit false

noncomputable section

open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix

namespace GlobalTheory.HSAmp

set_option autoImplicit false in
open Filter Topology MeasureTheory in
open scoped ComplexOrder Matrix in
private lemma ofReal_norm_sum_mul_sq_eq_double_sum_conj {ι : Type} [Fintype ι] (c w : ι → ℂ) :
    ((‖∑ i, c i * w i‖ ^ 2 : ℝ) : ℂ) =
      ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * (w i * (starRingEnd ℂ) (w j)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]
  ring


set_option autoImplicit false in
open Filter Topology MeasureTheory in
open scoped ComplexOrder Matrix in
theorem _root_.GlobalTheory.HSAmp.gram_isHermitian_and_l2_eq_quadratic_form (S : Type) (Y : S → Type)
    [∀ σ, MeasurableSpace (Y σ)] (ι : Type) [Fintype ι]
    [DecidableEq ι] (μ : ∀ σ, Measure (Y σ)) (v : ∀ σ, Y σ → ι → ℂ)
    (h : _root_.GlobalTheory.HSAmp.IsFam μ v) :
    (_root_.GlobalTheory.HSAmp.gram μ v).IsHermitian ∧ ∀ c : ι → ℂ,
      (∀ σ, Integrable (_root_.GlobalTheory.HSAmp.cmb v c σ) (μ σ)) ∧
      0 ≤ _root_.GlobalTheory.HSAmp.l2 μ v c ∧
      (_root_.GlobalTheory.HSAmp.l2 μ v c : ℂ) =
        ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * _root_.GlobalTheory.HSAmp.gram μ v i j := by
  haveI : Fintype S := @Fintype.ofFinite S h.finite
  have hint := h.integrable
  have hterm : ∀ (c : ι → ℂ) (σ : S), Integrable (fun y => ∑ i, ∑ j,
      c i * (starRingEnd ℂ) (c j) * (v σ y i * (starRingEnd ℂ) (v σ y j))) (μ σ) :=
    fun c σ => integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ => (hint σ i j).const_mul _
  refine ⟨?_, fun c => ⟨fun σ => ?_, ?_, ?_⟩⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, _root_.GlobalTheory.HSAmp.gram, Matrix.of_apply,
      finsum_eq_sum_of_fintype]
    rw [star_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Complex.star_def, ← integral_conj]
    congr 1 with y
    simp [mul_comm]
  · refine (hterm c σ).re.congr (ae_of_all _ fun y => ?_)
    simp only [_root_.GlobalTheory.HSAmp.cmb]
    rw [← ofReal_norm_sum_mul_sq_eq_double_sum_conj c (v σ y)]
    exact Complex.ofReal_re _
  · unfold _root_.GlobalTheory.HSAmp.l2
    exact finsum_nonneg fun σ => integral_nonneg fun y => by
      simp only [_root_.GlobalTheory.HSAmp.cmb]
      positivity
  · unfold _root_.GlobalTheory.HSAmp.l2 _root_.GlobalTheory.HSAmp.gram
    simp only [Matrix.of_apply, finsum_eq_sum_of_fintype]
    have key : ∀ σ, ((∫ y, _root_.GlobalTheory.HSAmp.cmb v c σ y ∂μ σ : ℝ) : ℂ) =
        ∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * ∫ y, v σ y i * (starRingEnd ℂ) (v σ y j) ∂μ σ := by
      intro σ
      simp only [_root_.GlobalTheory.HSAmp.cmb]
      rw [← integral_complex_ofReal,
        integral_congr_ae (ae_of_all _ fun y => ofReal_norm_sum_mul_sq_eq_double_sum_conj c (v σ y)),
        integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
          (hint σ i j).const_mul _]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ fun j _ => (hint σ i j).const_mul _]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_const_mul]
    rw [Complex.ofReal_sum]
    simp only [key, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

end GlobalTheory.HSAmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridSquareSkewSumSpaceIsSkewHermitianSelfDual
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open scoped nonZeroDivisors

namespace GlobalTheory.SkewLat

theorem hasSig_blk {a b d : ℕ} (e : Fin a ⊕ Fin b ≃ Fin d) (GA : Matrix (Fin a) (Fin a) ℂ) (GB : Matrix (Fin b) (Fin b) ℂ)
    {pa qa pb qb : ℕ} {κ : ℝ} (hκ : 0 < κ) (hA : Formalism.UG.HasSignature GA pa qa) (hB : Formalism.UG.HasSignature GB pb qb) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig ((κ : ℂ) • blk e GA GB) (pa + pb) (qa + qb) :=
  _root_.GlobalTheory.SigBlockSum.hasSig_smul_blk e GA GB hκ hA hB

theorem isCartan_blk {a b d : ℕ} (e : Fin a ⊕ Fin b ≃ Fin d) (GA sA : Matrix (Fin a) (Fin a) ℂ)
    (GB sB : Matrix (Fin b) (Fin b) ℂ) {κ : ℝ} (hκ : 0 < κ) (hA : IsCartanInv GA sA) (hB : IsCartanInv GB sB) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan ((κ : ℂ) • blk e GA GB) ((blk e sA sB).map conj) :=
  _root_.GlobalTheory.CartanBlocks.isCartan_blk e GA sA GB sB hκ hA hB

theorem star_mem_AA {D : D7} {c : D.host.E} (hc : c ∈ D.host.AAbar) : star c ∈ D.host.AA :=
  _root_.GlobalTheory.star_mem_AA_of_mem_AAbar hc

theorem isLattice_pairLat {E : Type} [Field E] [NumberField E] {a b d : ℕ} {𝔞 : FractionalIdeal (𝓞 E)⁰ E} (h𝔞 : 𝔞 ≠ 0)
    {ΛA : Submodule (𝓞 E) (Fin a → E)} {ΛB : Submodule (𝓞 E) (Fin b → E)} (hA : Submodule.IsLattice E ΛA)
    (hB : Submodule.IsLattice E ΛB) (e : Fin a ⊕ Fin b ≃ Fin d) :
    Submodule.IsLattice E (pairLat (scLat 𝔞 ΛA) (scLat 𝔞 ΛB) e) :=
  _root_.GlobalTheory.SkewLat.pairLat_scLat_isLattice h𝔞 hA hB e

theorem scLat_isFull {E : Type} [Field E] [NumberField E] {n : ℕ}
    {𝔞 : FractionalIdeal (𝓞 E)⁰ E} (h𝔞 : 𝔞 ≠ 0)
    {M : Submodule (𝓞 E) (Fin n → E)} (hM : Submodule.IsFullLattice E M) :
    Submodule.IsFullLattice E (scLat 𝔞 M) := by
  haveI := GlobalTheory.SkewLat.PairLatLattice.scLat_isLattice h𝔞 hM.toIsLattice
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (FractionalIdeal.coeToSubmodule_ne_bot.mpr h𝔞)
  have ha' : a ∈ 𝔞 := ha
  refine ⟨?_⟩
  apply eq_top_iff.mpr
  intro x _
  have hle : Submodule.span E (M : Set (Fin n → E)) ≤ Submodule.span E (scLat 𝔞 M : Set (Fin n → E)) := by
    apply Submodule.span_le.mpr
    intro y hy
    have hay : a • y ∈ scLat 𝔞 M := by
      intro c hc
      have hca : c * a ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) := by
        rw [← inv_mul_cancel₀ h𝔞]
        exact FractionalIdeal.mul_mem_mul hc ha'
      obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp hca
      rw [smul_smul, ← hr, algebraMap_smul]
      exact M.smul_mem r hy
    have := (Submodule.span E (scLat 𝔞 M : Set (Fin n → E))).smul_mem a⁻¹ (Submodule.subset_span hay)
    simpa [smul_smul, inv_mul_cancel₀ ha0] using this
  apply hle
  rw [Submodule.IsFullLattice.span_eq_top (self := hM)]
  trivial

theorem pairLat_isFull {E : Type} [Field E] [NumberField E] {a b d : ℕ}
    {M : Submodule (𝓞 E) (Fin a → E)} {N : Submodule (𝓞 E) (Fin b → E)}
    (hM : Submodule.IsFullLattice E M) (hN : Submodule.IsFullLattice E N)
    (e : Fin a ⊕ Fin b ≃ Fin d) : Submodule.IsFullLattice E (pairLat M N e) := by
  haveI := GlobalTheory.SkewLat.PairLatLattice.pairLat_isLattice hM.toIsLattice hN.toIsLattice e
  let φ : (Fin d → E) ≃ₗ[E] (Fin a → E) × (Fin b → E) :=
    (LinearEquiv.funCongrLeft E E e).trans (LinearEquiv.sumArrowLequivProdArrow _ _ E E)
  refine ⟨?_⟩
  apply eq_top_iff.mpr
  intro x _
  have hle : Submodule.span E ((M.prod N : Submodule (𝓞 E) ((Fin a → E) × (Fin b → E))) : Set _) ≤
      (Submodule.span E (pairLat M N e : Set (Fin d → E))).comap φ.symm.toLinearMap := by
    apply Submodule.span_le.mpr
    intro y hy
    apply Submodule.subset_span
    change φ.symm y ∈ pairLat M N e
    rw [mem_pairLat]
    simpa [φ, LinearEquiv.sumArrowLequivProdArrow, Equiv.sumArrowEquivProdArrow] using hy
  have hx : φ x ∈ Submodule.span E ((M.prod N : Submodule (𝓞 E) ((Fin a → E) × (Fin b → E))) : Set _) := by
    rw [GlobalTheory.SkewLat.PairLatLattice.prod_span_eq_top hM hN]
    trivial
  simpa using hle hx

theorem dual_pairLat {D : D7} (hc : ∀ c ∈ D.host.AAbar, star c ∈ D.host.AA) (A B : HSp D)
    {ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)} {ΛB : Submodule (𝓞 D.host.E) (Fin B.rank → D.host.E)}
    (hA : IsSelfDualC A ΛA) (hB : IsSelfDualC B ΛB) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) (y : Fin d → D.host.E) :
    y ∈ pairLat (scLat D.host.AA ΛA) (scLat D.host.AA ΛB) e ↔ ∀ x ∈ pairLat (scLat D.host.AA ΛA) (scLat D.host.AA ΛB) e,
      ∀ o : 𝓞 D.host.E, IsIntegral ℤ (Algebra.trace ℚ D.host.E (o * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e) y x)) :=
  _root_.GlobalTheory.SkewLat.pairLat_trace_selfDual hc A B hA hB e y

theorem I_smul_skewGram_map {D : D7} (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) (τ : D.what₂.Tau)
    (φ : D.host.E →+* ℂ) (hφ : ∀ x, φ x = conj (tauE D τ x)) :
    Complex.I • (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e).map φ =
      (((tauE D τ D.host.xi0).im : ℝ) : ℂ) • blk e (gramAt D A τ) (gramAt D B τ) := by
  have hre : (tauE D τ D.host.xi0).re = 0 := by
    have h := congrArg Complex.re (GlobalTheory.FockCompare.tauE_star τ D.host.xi0)
    rw [GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D, map_neg, Complex.neg_re, Complex.conj_re] at h
    linarith
  have hx : φ D.host.xi0 = -((((tauE D τ D.host.xi0).im : ℝ) : ℂ) * Complex.I) := by
    rw [hφ]; apply Complex.ext <;> simp [hre]
  have hg : ∀ (S : HSp D) (k l : Fin S.rank), φ (S.gram l k) = tauE D τ (S.gram k l) := fun S k l => by
    rw [hφ, ← GlobalTheory.FockCompare.tauE_star]
    have h1 : S.gramᴴ = S.gram := Matrix.ext fun a b => S.herm.eq _ _
    have h2 := congrFun (congrFun h1 k) l
    rw [Matrix.conjTranspose_apply] at h2
    rw [h2]
  ext k l
  obtain ⟨k, rfl⟩ := e.surjective k
  obtain ⟨l, rfl⟩ := e.surjective l
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_apply_apply, map_mul, hx]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rcases k with k | k <;> rcases l with l | l <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.transpose_apply, Matrix.zero_apply, map_zero, mul_zero, hg, Formalism.BasicNotions.TH.gramAt, Matrix.map_apply]
  all_goals linear_combination (-(((tauE D τ D.host.xi0).im : ℝ) : ℂ) * tauE D τ (HSpace.gram _ _ _)) * hI


open GlobalTheory.SkewLat in
theorem bigSpace_isSkew : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (W : G.Weil)
    (i j : Fin D.R.m) (e : Num G i j) (B : Base D.host.F D.host.E) (τf : InfinitePlace D.host.F → D.what₂.Tau),
    (∀ w x, (B.emb w).1 x = conj (tauE D (τf w) x)) →
    ∃ (Λ : Submodule (𝓞 D.host.E) (Fin ((spW G i j).rank + (spW₁ G i j).rank) → D.host.E))
      (bas : ∀ v : HeightOneSpectrum (𝓞 D.host.F), GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Fv D.host.F v)),
      Spc.IsSkew D.sp.cm.sig B
        (Spc.mk (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e) Λ (fun w => (blk e (W.cart (.grid (i : ℕ) ((j : ℕ) + 1)) (τf w)) (W.cart (.grid ((i : ℕ) + 1) (j : ℕ)) (τf w))).map conj) bas)
        ((spW G i j).rank + (spW₁ G i j).rank - ((D.R.m - j - 1) / 2 + (D.R.m - j) / 2))
        ((D.R.m - j - 1) / 2 + (D.R.m - j) / 2) := by
  intro D T L sc G μ₀ hL W i j e B τf hB
  have hi := i.2
  have hj := j.2
  have hrV : Node.InRange D.R.m (.grid (i : ℕ) ((j : ℕ) + 1)) := ⟨by omega, by omega⟩
  have hrV₁ : Node.InRange D.R.m (.grid ((i : ℕ) + 1) (j : ℕ)) := ⟨by omega, by omega⟩
  have hV := GlobalTheory.FunObj.node_isV G hL hrV
  have hV₁ := GlobalTheory.FunObj.node_isV G hL hrV₁
  have hcm := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm).1
  have hAA : D.host.AA ≠ 0 := fun h => by
    have := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
    rw [h, mul_zero, zero_mul, zero_mul] at this
    exact zero_ne_one this
  set Λ := pairLat (scLat D.host.AA (G.Λ (.grid (i : ℕ) ((j : ℕ) + 1)))) (scLat D.host.AA (G.Λ (.grid ((i : ℕ) + 1) (j : ℕ)))) e
    with hΛ
  have hlat : Submodule.IsLattice D.host.E Λ := isLattice_pairLat hAA hV.sd.1 hV₁.sd.1 e
  have hfull : Submodule.IsFullLattice D.host.E Λ :=
    pairLat_isFull (scLat_isFull hAA (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ hV.sd))
      (scLat_isFull hAA (GlobalTheory.ProjXCols.selfDual_isFullLattice _ _ hV₁.sd)) e
  have hex : ∀ v : B.P, ∃ β, GlobalTheory.AdelicU.IsSplitBasis (B.τ v) Λ β := fun v => GlobalTheory.AdelicU.exists_isSplitBasis (B.τ v) Λ hcm
  classical
  refine ⟨Λ, fun v => if h : v ∈ B.P then (hex ⟨v, h⟩).choose else 1, ?skew, ?sig, hfull, ?dual, ?cartan, ?bas⟩
  case skew =>
    intro k l
    obtain ⟨k, rfl⟩ := e.surjective k
    obtain ⟨l, rfl⟩ := e.surjective l
    have hg : ∀ (S : HSp D) (a b : Fin S.rank), star (S.gram a b) = S.gram b a := fun S a b => by
      have h1 : S.gramᴴ = S.gram := Matrix.ext fun a b => S.herm.eq _ _
      have h2 := congrFun (congrFun h1 b) a
      rwa [Matrix.conjTranspose_apply] at h2
    show star (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e (e l) (e k)) = -GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e (e k) (e l)
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram, Matrix.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk, Matrix.reindex_apply,
      Matrix.submatrix_apply, Equiv.symm_apply_apply, star_mul', GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D]
    rcases k with k | k <;> rcases l with l | l <;>
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, Matrix.transpose_apply, Matrix.zero_apply, star_zero, mul_zero, neg_zero, hg, neg_mul]
  case sig =>
    intro w
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (Complex.I • (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e).map (B.emb w).1) _ _
    rw [I_smul_skewGram_map _ _ e (τf w) (B.emb w).1 (hB w)]
    have hA := hV.sigOK (tauE D (τf w))
    have hA₁ := hV₁.sigOK (tauE D (τf w))
    rw [hV.sig] at hA
    rw [hV₁.sig] at hA₁
    have h := hasSig_blk e (gramAt D (spV G i j) (τf w)) (gramAt D (spV₁ G i j) (τf w)) (Formalism.L2.Theta.xi_zero_im_pos D (τf w)) hA hA₁
    have hsum := h.1
    have hd : Fintype.card (Fin (spV G i j).rank ⊕ Fin (spV₁ G i j).rank) =
        Fintype.card (Fin ((spW G i j).rank + (spW₁ G i j).rank)) := Fintype.card_congr e
    simp only [Fintype.card_sum, Fintype.card_fin] at hd
    have h1 := hV.rank
    have h2 := hV₁.rank
    simp only [Node.rank, Node.neg] at h1 h2 h hsum
    convert h using 2 <;> omega
  case dual => exact fun y => dual_pairLat (fun c hc => star_mem_AA hc) _ _ hV.sd hV₁.sd e y
  case cartan =>
    intro w
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (Complex.I • (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram (spV G i j) (spV₁ G i j) e).map (B.emb w).1) _
    rw [I_smul_skewGram_map _ _ e (τf w) (B.emb w).1 (hB w)]
    exact isCartan_blk e _ _ _ _ (Formalism.L2.Theta.xi_zero_im_pos D (τf w)) (W.cart_is _ hrV (τf w)) (W.cart_is _ hrV₁ (τf w))
  case bas =>
    intro v
    show GlobalTheory.AdelicU.IsSplitBasis (B.τ v) Λ (if h : (v : HeightOneSpectrum (𝓞 D.host.F)) ∈ B.P then (hex ⟨v, h⟩).choose else 1)
    rw [dite_eq_left v.2]
    exact (hex v).choose_spec

end GlobalTheory.SkewLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureFiniteEtaleOriginKeyLemmaEssFinitStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralClosure_finiteEtale_originKeyLemma_essFiniteType : ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (ρ : Localization.AtPrime QA →+* A), ρ.comp (algebraMap A (Localization.AtPrime QA)) = RingHom.id A →
      RingHom.ker ρ = Ideal.span {algebraMap (Polynomial A) (Localization.AtPrime QA) Polynomial.X} →
    ∀ (q : ℕ), 0 < q → IsUnit (q : A) →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
      GlobalTheory.KeyOriginNoeth.Good A (Localization.AtPrime QA) DA ρ →
      GlobalTheory.KeyOriginNoeth.ClosureFiniteEtale A (Localization.AtPrime QA) DA := by
  first | (exact @GlobalTheory.GoodEtale.closure_finiteEtale) | (exact GlobalTheory.GoodEtale.closure_finiteEtale) | (intros; apply GlobalTheory.GoodEtale.closure_finiteEtale  <;> assumption)
end

