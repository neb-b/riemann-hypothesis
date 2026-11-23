module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Chapter
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0145
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0148
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffEisensteinSeriesTwistedHeckeUHeckeV
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

theorem eis_U_pair (j l : ℕ) (c t : ℂ) (a b : ℤ → ℂ) (hl : l.Prime)
    (ha : ∀ x : ℤ, (l : ℤ) ∣ x → a x = 0) (hb : ∀ y, b (l * y) = t * b y) (n : ℕ) (hn : n ≠ 0) :
    eis j c a b (l * n) = t * eis j c a b n := by
  have hl0 : l ≠ 0 := hl.ne_zero
  have hln : l * n ≠ 0 := mul_ne_zero hl0 hn
  simp only [eis, hln, hn, if_false]
  rw [Finset.mul_sum]
  symm
  refine Finset.sum_bij_ne_zero (fun p _ _ => (p.1, l * p.2)) ?_ ?_ ?_ ?_
  · intro p hp _
    rw [Nat.mem_divisorsAntidiagonal] at hp ⊢
    refine ⟨?_, hln⟩
    rw [← hp.1]; ring
  · intro p _ _ q _ _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 (Nat.eq_of_mul_eq_mul_left hl.pos h.2)
  · intro q hq hne
    rw [Nat.mem_divisorsAntidiagonal] at hq
    have h1 : ¬ l ∣ q.1 := by
      intro hd
      apply hne
      rw [ha q.1 (by exact_mod_cast hd)]; ring
    have h2 : l ∣ q.2 := by
      have : l ∣ q.1 * q.2 := by rw [hq.1]; exact dvd_mul_right _ _
      exact (hl.dvd_mul.mp this).resolve_left h1
    obtain ⟨y, hy⟩ := h2
    refine ⟨(q.1, y), ?_, ?_, ?_⟩
    · rw [Nat.mem_divisorsAntidiagonal]
      refine ⟨?_, hn⟩
      have h := hq.1
      rw [hy] at h
      have : l * (q.1 * y) = l * n := by rw [← h]; ring
      exact Nat.eq_of_mul_eq_mul_left hl.pos this
    · intro h0
      apply hne
      have : b (q.2 : ℤ) = t * b (y : ℤ) := by rw [hy]; push_cast; exact hb _
      rw [this]
      simp only at h0
      linear_combination h0
    · ext <;> simp [hy]
  · intro p _ _
    simp only
    push_cast
    rw [hb]; ring

theorem eis_V_pair (j l : ℕ) (c t : ℂ) (a b : ℤ → ℂ) (hl : l.Prime)
    (ha : ∀ x, a (l * x) = t * a x) (n : ℕ) (hn : n ≠ 0) :
    eis j c (fun x => if (l : ℤ) ∣ x then a x else 0) b n = t * (l : ℂ) ^ (j - 1) * Vo l (eis j c a b) n := by
  have hl0 : l ≠ 0 := hl.ne_zero
  by_cases hd : l ∣ n
  · obtain ⟨m, rfl⟩ := hd
    have hm : m ≠ 0 := by rintro rfl; simp at hn
    simp only [Vo, dvd_mul_right, if_true, Nat.mul_div_cancel_left m hl.pos]
    simp only [eis, hn, hm, if_false]
    rw [Finset.mul_sum]
    symm
    refine Finset.sum_bij_ne_zero (fun p _ _ => (l * p.1, p.2)) ?_ ?_ ?_ ?_
    · intro p hp _
      rw [Nat.mem_divisorsAntidiagonal] at hp ⊢
      refine ⟨?_, hn⟩
      rw [← hp.1]; ring
    · intro p _ _ q _ _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Nat.eq_of_mul_eq_mul_left hl.pos h.1) h.2
    · intro q hq hne
      rw [Nat.mem_divisorsAntidiagonal] at hq
      have h1 : l ∣ q.1 := by
        by_contra h
        apply hne
        have : ¬ (l : ℤ) ∣ (q.1 : ℤ) := by exact_mod_cast h
        simp [this]
      obtain ⟨x, hx⟩ := h1
      refine ⟨(x, q.2), ?_, ?_, ?_⟩
      · rw [Nat.mem_divisorsAntidiagonal]
        refine ⟨?_, hm⟩
        have h := hq.1
        rw [hx] at h
        have : l * (x * q.2) = l * m := by rw [← h]; ring
        exact Nat.eq_of_mul_eq_mul_left hl.pos this
      · intro h0
        apply hne
        have hdv : (l : ℤ) ∣ (q.1 : ℤ) := by rw [hx]; push_cast; exact dvd_mul_right _ _
        simp only [hdv, if_true]
        have : a (q.1 : ℤ) = t * a (x : ℤ) := by rw [hx]; push_cast; exact ha _
        rw [this, hx]
        simp only at h0
        push_cast
        rw [mul_pow]
        linear_combination h0
      · ext <;> simp [hx]
    · intro p _ _
      have hdv : (l : ℤ) ∣ ((l * p.1 : ℕ) : ℤ) := by push_cast; exact dvd_mul_right _ _
      simp only [hdv, if_true]
      push_cast
      rw [ha, mul_pow]; ring
  · have h0 : Vo l (eis j c a b) n = 0 := by simp [Vo, hd]
    rw [h0, mul_zero]
    simp only [eis, hn, if_false]
    refine Finset.sum_eq_zero fun q hq => ?_
    rw [Nat.mem_divisorsAntidiagonal] at hq
    have : ¬ (l : ℤ) ∣ (q.1 : ℤ) := by
      intro h
      apply hd
      have h' : l ∣ q.1 := by exact_mod_cast h
      rw [← hq.1]; exact dvd_mul_of_dvd_left h' _
    simp [this]

theorem eis_U_V (j l : ℕ) (c t : ℂ) (a b : ℤ → ℂ) : l.Prime → ((∀ x : ℤ, (l : ℤ) ∣ x → a x = 0) → (∀ y, b (l * y) = t * b y) → ∀ n, n ≠ 0 → eis j c a b (l * n) = t * eis j c a b n) ∧ (1 ≤ j → (∀ x, a (l * x) = t * a x) → ∀ n, n ≠ 0 → eis j c (fun x => if (l : ℤ) ∣ x then a x else 0) b n = t * (l : ℂ) ^ (j - 1) * Vo l (eis j c a b) n) :=
  fun hl => ⟨fun ha hb n hn => eis_U_pair j l c t a b hl ha hb n hn,
    fun _ ha n hn => eis_V_pair j l c t a b hl ha n hn⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeVOperatorRaisesLevel
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

def scaleH (l : ℕ) (hl : 0 < l) (τ : ℍ) : ℍ :=
  UpperHalfPlane.mk ((l : ℂ) * τ) (by simp; positivity)

lemma coe_sl_apply (g : SL(2, ℤ)) (z : ℍ) :
    ((g • z : ℍ) : ℂ) = (((g 0 0 : ℤ) : ℂ) * z + ((g 0 1 : ℤ) : ℂ)) / (((g 1 0 : ℤ) : ℂ) * z + ((g 1 1 : ℤ) : ℂ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]; simp

lemma denom_sl_ne (g : SL(2, ℤ)) (z : ℍ) : ((g 1 0 : ℤ) : ℂ) * z + ((g 1 1 : ℤ) : ℂ) ≠ 0 := by
  have h2 := UpperHalfPlane.denom_ne_zero g z
  simpa [UpperHalfPlane.denom] using h2

theorem Vo_level : ∀ (k L l : ℕ) (χ : ℤ → ℂ) (a : ℕ → ℂ), 0 < l →
    (MF k L χ a → MF k (L * l) χ (Vo l a)) ∧ (CF k L χ a → CF k (L * l) χ (Vo l a)) := by
  intro k L l χ a hl
  have key : MF k L χ a → MF k (L * l) χ (Vo l a) := by
    rintro ⟨hP, hI⟩
    obtain ⟨hP', hq⟩ := _root_.GlobalTheory.EisM.Vo_polyB_qs l a hl hP
    refine ⟨hP', ?_⟩
    intro γ hγ τ
    obtain ⟨m, hm⟩ := hγ
    have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
      have := γ.2; rw [Matrix.det_fin_two] at this; exact this
    let γ' : SL(2, ℤ) := ⟨!![γ 0 0, (l : ℤ) * γ 0 1; (L : ℤ) * m, γ 1 1], by
      rw [Matrix.det_fin_two_of]; rw [hm] at hdet; push_cast at hdet; linear_combination hdet⟩
    have h1 : ((L : ℕ) : ℤ) ∣ γ' 1 0 := ⟨m, by simp [γ']⟩
    have hl' : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
    have hc : ((γ 1 0 : ℤ) : ℂ) = (L : ℂ) * l * m := by rw [hm]; push_cast; ring
    have e1 : γ' • scaleH l hl τ = scaleH l hl (γ • τ) := by
      apply UpperHalfPlane.ext
      rw [coe_sl_apply]
      simp only [scaleH, UpperHalfPlane.coe_mk, coe_sl_apply]
      have hd := denom_sl_ne γ τ
      rw [hc] at hd ⊢
      simp only [γ', Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons]
      push_cast
      have hd2 : (L : ℂ) * m * (l * (τ : ℂ)) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by
        convert hd using 1; ring
      field_simp
    rw [hq (γ • τ) (scaleH l hl (γ • τ)) rfl, hq τ (scaleH l hl τ) rfl, ← e1, hI γ' h1]
    simp only [γ', Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, scaleH, UpperHalfPlane.coe_mk]
    rw [hc]; push_cast; ring_nf
  refine ⟨key, ?_⟩
  rintro ⟨hM, C, hC⟩
  refine ⟨key hM, C, fun τ => ?_⟩
  obtain ⟨_, hq⟩ := _root_.GlobalTheory.EisM.Vo_polyB_qs l a hl hM.1
  rw [hq τ (scaleH l hl τ) rfl]
  have him : (scaleH l hl τ).im = l * τ.im := by
    change ((l:ℂ) * (τ:ℂ)).im = (l:ℝ) * (τ:ℂ).im
    simp
  have hle : τ.im ≤ (scaleH l hl τ).im := by
    rw [him]; have : (1 : ℝ) ≤ l := by exact_mod_cast hl
    nlinarith [τ.im_pos]
  calc ‖qs a (scaleH l hl τ)‖ ^ 2 * τ.im ^ k ≤ ‖qs a (scaleH l hl τ)‖ ^ 2 * (scaleH l hl τ).im ^ k := by
        gcongr
    _ ≤ C := hC _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepletedNewformPrim
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
noncomputable section

namespace GlobalTheory.EisM

theorem depleted_newform_prim : ∀ (k r : ℕ) (g : Newform k), 1 ≤ k → 2 ≤ r → ∃ χ : DirichletCharacter ℂ (g.M * (g.M * r) ^ 2), Prim k _ χ (fun n => if n.Coprime (g.M * r) then g.a n else 0) ∧ ∀ d : ℕ, d.Coprime (g.M * (g.M * r) ^ 2) → χ d = g.χ d := by
  intro k r g _ hr
  have hM := g.pos
  have hLpos : 0 < g.M * r := Nat.mul_pos hM (by omega)
  have hdvd : g.M ∣ g.M * (g.M * r) ^ 2 := dvd_mul_right _ _
  have hLN : g.M * r ∣ g.M * (g.M * r) ^ 2 := (dvd_pow_self _ two_ne_zero).mul_left g.M
  have hcop : ∀ n : ℕ, n.Coprime (g.M * (g.M * r) ^ 2) ↔ n.Coprime (g.M * r) := by
    intro n
    constructor
    · intro h; exact h.coprime_dvd_right hLN
    · intro h
      exact Nat.Coprime.mul_right (h.coprime_dvd_right (dvd_mul_right _ _)) (Nat.Coprime.pow_right 2 h)
  set χ : DirichletCharacter ℂ (g.M * (g.M * r) ^ 2) := DirichletCharacter.changeLevel hdvd g.χ with hχdef
  have hχZ : ∀ d : ℤ, IsCoprime d ((g.M * (g.M * r) ^ 2 : ℕ) : ℤ) → ch χ d = g.χ (d : ZMod g.M) := by
    intro d hd
    exact DirichletCharacter.changeLevel_eq_cast_of_dvd' g.χ hdvd hd
  have hχN : ∀ d : ℕ, d.Coprime (g.M * (g.M * r) ^ 2) → χ d = g.χ d := by
    intro d hd
    have := hχZ d (Nat.isCoprime_iff_coprime.2 hd)
    simpa [ch] using this
  refine ⟨χ, ?_, hχN⟩

  have hcf0 := ((gamma1_char_elementary k g.M g.χ hM).2 g.f g.char).2
  have htw := _root_.GlobalTheory.EisM.CharTwist.cf_twist k g.M (g.M * r) g.χ (1 : DirichletCharacter ℂ (g.M * r)) (coef g.f) hLpos hcf0
  have hseq : (fun n : ℕ => (1 : DirichletCharacter ℂ (g.M * r)) n * coef g.f n) =
      (fun n => if n.Coprime (g.M * r) then g.a n else 0) := by
    funext n
    by_cases h : n.Coprime (g.M * r)
    · rw [if_pos h, MulChar.one_apply ((ZMod.isUnit_iff_coprime n _).2 h), one_mul]; rfl
    · rw [if_neg h, MulChar.map_nonunit _ (fun hu => h ((ZMod.isUnit_iff_coprime n _).1 hu)), zero_mul]
  rw [hseq] at htw
  have hlin := (_root_.GlobalTheory.EisM.mf_linear k (g.M * (g.M * r) ^ 2) (fun d => ch g.χ d * ch (1 : DirichletCharacter ℂ (g.M * r)) d ^ 2)).2.2.2.1
    (ch χ) _ ?_ htw.1
  swap
  · intro d hd
    have hdL : IsCoprime d ((g.M * r : ℕ) : ℤ) := hd.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.2 hLN)
    rw [hχZ d hd]
    simp only [ch]
    rw [← ZMod.coe_unitOfIsCoprime d hdL, MulChar.one_apply_coe, one_pow, mul_one]
  refine ⟨⟨hlin, htw.2⟩, ?_, ?_, ?_⟩
  · have h1 : (1 : ℕ).Coprime (g.M * r) := Nat.coprime_one_left _
    simp only [if_pos h1]
    exact g.one
  · intro n hn
    have : ¬ n.Coprime (g.M * r) := fun h => hn ((hcop n).2 h)
    simp only [if_neg this]
  · intro q hq hqN
    have hqL : q.Coprime (g.M * r) := (Nat.Prime.coprime_iff_not_dvd hq).2 (fun h => hqN (h.trans hLN))
    have hqM : ¬ q ∣ g.M := fun h => hqN (h.trans hdvd)
    have hchq : ch χ (q : ℤ) = g.χ (q : ZMod g.M) := by
      rw [hχZ (q : ℤ) (Nat.isCoprime_iff_coprime.2 ((hcop q).2 hqL))]; simp
    have heig := g.eig q hq hqM
    funext n
    simp only [To, Vo, hchq, if_pos hqL]
    by_cases hn : n.Coprime (g.M * r)
    · have hn1 : 1 ≤ n := by
        rcases Nat.eq_zero_or_pos n with h0 | h0
        · subst h0; rw [Nat.coprime_zero_left] at hn; nlinarith
        · exact h0
      have hqn : (q * n).Coprime (g.M * r) := Nat.Coprime.mul_left hqL hn
      rw [if_pos hqn, if_pos hn]
      have e := heig n hn1
      by_cases hd : q ∣ n
      · have hnq : (n / q).Coprime (g.M * r) := hn.coprime_dvd_left (Nat.div_dvd_of_dvd hd)
        rw [if_pos hd, if_pos hnq]
        rw [if_pos hd] at e
        exact e
      · rw [if_neg hd]
        rw [if_neg hd] at e
        exact e
    · have hqn : ¬ (q * n).Coprime (g.M * r) := fun h => hn (Nat.Coprime.coprime_mul_left h)
      rw [if_neg hqn, if_neg hn, mul_zero]
      by_cases hd : q ∣ n
      · have hnq : ¬ (n / q).Coprime (g.M * r) := by
          intro h
          apply hn
          rw [← Nat.mul_div_cancel' hd]
          exact Nat.Coprime.mul_left hqL h
        rw [if_pos hd, if_neg hnq]; simp
      · rw [if_neg hd]; simp

end GlobalTheory.EisM

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondMatrixMulCommModGamma1CapGamma0Statement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.StabHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diamondMatrix_mul_comm_mod_gamma1CapGamma0 : ∀ (N l d d' : ℕ) (σ σ' : SL(2, ℤ)), IsDiam N l d σ → IsDiam N l d' σ' → ∃ g : SL(2, ℤ), g ∈ Gam N l ∧ σ' * σ = g * (σ * σ') := by
  first | exact @GlobalTheory.KZ.isDiam_mul_comm_mod_Gam | exact GlobalTheory.KZ.isDiam_mul_comm_mod_Gam | (intros; apply GlobalTheory.KZ.isDiam_mul_comm_mod_Gam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DirichletCharFiniteFourierTransformProperties
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

noncomputable section

namespace GlobalTheory.EisM

theorem hat_eq_sum_std {N : ℕ} [NeZero N] (φ : ZMod N → ℂ) (d : ℤ) :
    hat φ d = ∑ y : ZMod N, φ y * ZMod.stdAddChar (y * (d : ZMod N)) := by
  unfold hat
  have step : ∀ i ∈ Finset.range N, φ (i : ZMod N) * cexp (2 * π * Complex.I * ((i : ℂ) * (d : ℂ)) / N)
      = φ (i : ZMod N) * ZMod.stdAddChar ((i : ZMod N) * (d : ZMod N)) := by
    intro i _
    congr 1
    have : ((i : ZMod N)) * (d : ZMod N) = (((i : ℤ) * d : ℤ) : ZMod N) := by push_cast; rfl
    rw [this, ZMod.stdAddChar_coe]
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl step]
  refine Finset.sum_nbij' (fun i => (i : ZMod N)) (fun y => y.val) ?_ ?_ ?_ ?_ ?_
  · intro i _; simp
  · intro y _; simp [ZMod.val_lt]
  · intro i hi; simp only [Finset.mem_coe, Finset.mem_range] at hi; simp [ZMod.val_cast_of_lt hi]
  · intro y _; simp
  · intro i _; rfl

theorem hat_add_period {N : ℕ} [NeZero N] (φ : ZMod N → ℂ) (x : ℤ) : hat φ (x + N) = hat φ x := by
  rw [hat_eq_sum_std, hat_eq_sum_std]
  push_cast
  simp

theorem hat_mul_unit {N : ℕ} [NeZero N] (θ : DirichletCharacter ℂ N) (d x : ℤ) (hd : IsUnit (d : ZMod N)) :
    hat θ (x * d) = ch θ⁻¹ d * hat θ x := by
  have h := gaussSum_mulShift_eq θ ((ZMod.stdAddChar (N := N)).mulShift (x : ZMod N)) hd.unit
  simp only [gaussSum, AddChar.mulShift_apply, IsUnit.unit_spec] at h
  rw [hat_eq_sum_std, hat_eq_sum_std]
  unfold ch
  calc ∑ y : ZMod N, θ y * ZMod.stdAddChar (y * ((x * d : ℤ) : ZMod N))
      = ∑ y : ZMod N, θ y * ZMod.stdAddChar ((x : ZMod N) * ((d : ZMod N) * y)) := by
        refine Fintype.sum_congr _ _ (fun y => ?_); push_cast; ring_nf
    _ = θ⁻¹ (d : ZMod N) * ∑ y : ZMod N, θ y * ZMod.stdAddChar ((x : ZMod N) * y) := h
    _ = _ := by
        congr 1; refine Fintype.sum_congr _ _ (fun y => ?_); ring_nf

theorem hat_zero_of_ne_one {N : ℕ} [NeZero N] (θ : DirichletCharacter ℂ N) (h : θ ≠ 1) : hat θ 0 = 0 := by
  rw [hat_eq_sum_std]
  simp only [Int.cast_zero, mul_zero, AddChar.map_zero_eq_one, mul_one]
  exact MulChar.sum_eq_zero_of_ne_one h

theorem isUnit_of_isCoprime {N : ℕ} (d : ℤ) (h : IsCoprime d N) : IsUnit (d : ZMod N) := by
  obtain ⟨a, b, hab⟩ := h
  have : ((a * d + b * N : ℤ) : ZMod N) = 1 := by rw [hab]; simp
  push_cast at this
  rw [ZMod.natCast_self, mul_zero, add_zero] at this
  exact IsUnit.of_mul_eq_one (a : ZMod N) (by rw [mul_comm]; exact this)

theorem hat_prime_one {l : ℕ} [Fact l.Prime] (x : ℤ) :
    hat (1 : DirichletCharacter ℂ l) x = (if (l : ℤ) ∣ x then (l : ℂ) else 0) - 1 := by
  classical
  rw [hat_eq_sum_std]
  have hterm : ∀ y : ZMod l, (1 : DirichletCharacter ℂ l) y * ZMod.stdAddChar (y * (x : ZMod l))
      = ZMod.stdAddChar (y * (x : ZMod l)) - if y = 0 then 1 else 0 := by
    intro y
    by_cases hy : y = 0
    · subst hy; rw [MulChar.map_zero]; simp
    · rw [MulChar.one_apply (isUnit_iff_ne_zero.mpr hy)]; simp [hy]
  rw [Fintype.sum_congr _ _ hterm, Finset.sum_sub_distrib, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar l)]
  simp [ZMod.card, ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem hat_prime_ne_one {l : ℕ} [Fact l.Prime] (ψ : DirichletCharacter ℂ l) (hψ : ψ ≠ 1) :
    hat ψ 1 ≠ 0 ∧ ∀ x, hat ψ x = hat ψ 1 * ch ψ⁻¹ x := by
  constructor
  · have h := gaussSum_mul_gaussSum_eq_card hψ (ZMod.isPrimitive_stdAddChar l)
    rw [hat_eq_sum_std]
    intro h0
    simp only [Int.cast_one, mul_one] at h0
    rw [gaussSum, h0, zero_mul, ZMod.card] at h
    exact (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) h.symm
  · intro x
    by_cases hx : (x : ZMod l) = 0
    · have h1 : hat ψ x = 0 := by
        rw [hat_eq_sum_std, hx]
        simp only [mul_zero, AddChar.map_zero_eq_one, mul_one]
        exact MulChar.sum_eq_zero_of_ne_one hψ
      rw [h1]; unfold ch; rw [hx, MulChar.map_zero, mul_zero]
    · have := hat_mul_unit ψ x 1 (isUnit_iff_ne_zero.mpr hx)
      rw [one_mul] at this
      rw [this, mul_comm]

theorem stdAddChar_nat_mul_int {M : ℕ} [NeZero M] (a : ZMod M) (x : ℤ) :
    (ZMod.stdAddChar (a * (x : ZMod M)) : ℂ) = cexp (2 * π * Complex.I * ((a.val : ℂ) * x) / M) := by
  have : a * (x : ZMod M) = (((a.val : ℤ) * x : ℤ) : ZMod M) := by push_cast; simp
  rw [this, ZMod.stdAddChar_coe]; push_cast; ring_nf

theorem hat_mul_coprime (N l : ℕ) (θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l)
    (φ : DirichletCharacter ℂ (N * l)) (hN : 0 < N) (hl : 0 < l) (hc : N.Coprime l)
    (hφ : ∀ d : ℤ, ch φ d = ch θ d * ch ψ d) (x : ℤ) :
    hat φ x = ch θ l * ch ψ N * (hat θ x * hat ψ x) := by
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨hl.ne'⟩
  haveI : NeZero (N * l) := ⟨(Nat.mul_pos hN hl).ne'⟩
  let f : ZMod N × ZMod l → ZMod (N * l) := fun p => ((p.1.val * l + p.2.val * N : ℕ) : ZMod (N * l))
  have hcN : ∀ k : ℕ, ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N) (k : ZMod (N * l)) = (k : ZMod N) :=
    fun k => map_natCast _ k
  have hcl : ∀ k : ℕ, ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l) (k : ZMod (N * l)) = (k : ZMod l) :=
    fun k => map_natCast _ k
  have hlu : IsUnit (l : ZMod N) := (ZMod.unitOfCoprime l hc.symm).isUnit
  have hNu : IsUnit (N : ZMod l) := (ZMod.unitOfCoprime N hc).isUnit
  have hinj : Function.Injective f := by
    intro p q hpq
    have h1 := congrArg (ZMod.castHom (Dvd.intro l rfl : N ∣ N * l) (ZMod N)) hpq
    have h2 := congrArg (ZMod.castHom (Dvd.intro_left N rfl : l ∣ N * l) (ZMod l)) hpq
    simp only [f, hcN, hcl] at h1 h2
    push_cast at h1 h2
    simp only [ZMod.natCast_self, mul_zero, add_zero, zero_add, ZMod.natCast_zmod_val] at h1 h2
    exact Prod.ext (hlu.mul_right_cancel h1) (hNu.mul_right_cancel h2)
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, by simp [ZMod.card]⟩
  rw [hat_eq_sum_std, hat_eq_sum_std, hat_eq_sum_std, ← Fintype.sum_bijective f hbij _ _ (fun _ => rfl),
    Finset.sum_mul_sum, ← Finset.univ_product_univ, Finset.sum_product, Finset.mul_sum]
  refine Fintype.sum_congr _ _ (fun a => ?_)
  rw [Finset.mul_sum]
  refine Fintype.sum_congr _ _ (fun b => ?_)
  have hf : f (a, b) = (((a.val * l + b.val * N : ℕ) : ℤ) : ZMod (N * l)) := by simp [f]
  have hval : φ (f (a, b)) = θ a * θ l * (ψ b * ψ N) := by
    have := hφ ((a.val * l + b.val * N : ℕ) : ℤ)
    unfold ch at this
    rw [hf, this]
    push_cast
    simp only [ZMod.natCast_self, mul_zero, add_zero, zero_add, ZMod.natCast_zmod_val, map_mul]
  have he : (ZMod.stdAddChar (f (a, b) * (x : ZMod (N * l))) : ℂ)
      = ZMod.stdAddChar (a * (x : ZMod N)) * ZMod.stdAddChar (b * (x : ZMod l)) := by
    have : f (a, b) * (x : ZMod (N * l)) = ((((a.val * l + b.val * N : ℕ) : ℤ) * x : ℤ) : ZMod (N * l)) := by
      rw [hf]; push_cast; rfl
    rw [this, ZMod.stdAddChar_coe, stdAddChar_nat_mul_int a x, stdAddChar_nat_mul_int b x, ← Complex.exp_add]
    congr 1
    have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    have hl' : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hl.ne'
    push_cast
    field_simp
  rw [hval, he]
  unfold ch
  simp only [Int.cast_natCast]
  ring

theorem hat_char_props : (∀ (N : ℕ) (θ : DirichletCharacter ℂ N), 0 < N → (∀ x : ℤ, hat θ (x + N) = hat θ x) ∧ (∀ d x : ℤ, IsCoprime d N → hat θ (x * d) = ch θ⁻¹ d * hat θ x) ∧ (θ ≠ 1 → hat θ 0 = 0)) ∧ (∀ (N l : ℕ) (θ : DirichletCharacter ℂ N) (ψ : DirichletCharacter ℂ l) (φ : DirichletCharacter ℂ (N * l)), 0 < N → 0 < l → N.Coprime l → (∀ d : ℤ, ch φ d = ch θ d * ch ψ d) → ∀ x, hat φ x = ch θ l * ch ψ N * (hat θ x * hat ψ x)) ∧ ∀ (l : ℕ) (ψ : DirichletCharacter ℂ l), l.Prime → (ψ ≠ 1 → hat ψ 1 ≠ 0 ∧ ∀ x, hat ψ x = hat ψ 1 * ch ψ⁻¹ x) ∧ (ψ = 1 → ∀ x : ℤ, hat ψ x = (if (l : ℤ) ∣ x then (l : ℂ) else 0) - 1) := by
  refine ⟨?_, ?_, ?_⟩
  · intro N θ hN
    haveI : NeZero N := ⟨hN.ne'⟩
    exact ⟨fun x => hat_add_period _ x, fun d x hd => hat_mul_unit θ d x (isUnit_of_isCoprime d hd),
      hat_zero_of_ne_one θ⟩
  · intro N l θ ψ φ hN hl hc hφ x
    exact hat_mul_coprime N l θ ψ φ hN hl hc hφ x
  · intro l ψ hl
    haveI : Fact l.Prime := ⟨hl⟩
    refine ⟨hat_prime_ne_one ψ, ?_⟩
    rintro rfl x
    exact hat_prime_one x

end GlobalTheory.EisM
end
end

