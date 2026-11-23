module

public import Formalism.HermitianCurvature.StatementTB
public import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff
public import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.OneLevelCoefficients
section
namespace Formalism.FourierDecayAlt.P.OneLevelCoefficients

open Formalism.FourierDecayAlt.TB Finset
open scoped ComplexOrder

variable {E W : Type} [Field E]

lemma exists_reps (L : AddSubgroup E) (S : Finset E) :
    ∃ R : Finset E, (∀ t ∈ S, ∃ t₀ ∈ R, t - t₀ ∈ L) ∧
      (∀ t₀ ∈ R, ∀ t₀' ∈ R, t₀ - t₀' ∈ L → t₀ = t₀') := by
  classical
  have hout : ∀ t : E, (((t : E ⧸ L).out : E) : E ⧸ L) = (t : E ⧸ L) :=
    fun t => QuotientAddGroup.out_eq' _
  refine ⟨S.image (fun t : E => (QuotientAddGroup.mk t : E ⧸ L).out), ?_, ?_⟩
  · intro t ht
    refine ⟨_, Finset.mem_image_of_mem _ ht, ?_⟩
    rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_sub, hout, sub_self]
  · intro a ha b hb hab
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨t', _, rfl⟩ := Finset.mem_image.1 hb
    rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_sub, hout, hout, sub_eq_zero] at hab
    simp only [hab]

lemma budget_step (K r i s c m : ℕ) (hsi : s ≤ i) (hi : i ≤ r + 1)
    (hc : c ≤ 4 * K * (r + 1 - i)) (hm : m ≤ 4 * s) : c + m * K ≤ 4 * K * (r + 1 - (i - s)) := by
  have h1 : r + 1 - (i - s) = (r + 1 - i) + s := by omega
  have h2 : m * K ≤ 4 * K * s := by
    calc m * K ≤ 4 * s * K := Nat.mul_le_mul_right _ hm
      _ = 4 * K * s := by ring
  rw [h1, Nat.mul_add]
  exact Nat.add_le_add hc h2

lemma budget_top (K r i s c m : ℕ) (hsi : s ≤ i) (hi : i ≤ r + 1)
    (hc : c ≤ 4 * K * (r + 1 - i)) (hm : m ≤ 4 * s) : c + m * K ≤ 4 * K * (r + 1) :=
  (budget_step K r i s c m hsi hi hc hm).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))

theorem oneLevel_of_steps : OneLevelOfSteps := by
  intro hSplit hSchur hDiag hOne hMulti E W _ D ep C₄ hG hKer hW hA2 hA13 hEW hP hEL hEB hLat hep
    h4 hv0 hv1 T ε hε σ i hi1 hi hσ w hw
  have hwW : w ∈ D.Wall := (Finset.mem_filter.1 hw).1
  have hwc : D.cnt w ≤ 4 * D.K * (D.r + 1 - i) := (Finset.mem_filter.1 hw).2
  have hwt : 0 < D.wt w := hW w
  have he : 0 ≤ D.e i := (hA13 i 1 le_rfl hi1 hi).1.1
  have ha0 : 0 ≤ 3 ^ D.f * ep := by positivity
  have hb0 : 0 ≤ 2 ^ D.f * ep := by positivity

  have hS : ∀ s, 1 ≤ s → s ≤ i → ∀ M : ℝ,
      (∀ w' ∈ D.Wb (D.cnt w + D.K), D.Dg T ε i s w' ≤ M) →
      D.Sf ε i w (Xs T i s) / D.wt w ≤ (1 + 3 ^ D.f * ep) * M := by
    intro s hs hsi M hM
    have hN : D.cnt w + D.K ≤ D.Ntop := by
      have := budget_top D.K D.r i s (D.cnt w) 1 hsi hi hwc (by omega)
      simpa [Data.Ntop] using this
    have h := hSchur E W D ep hG hKer hW hA2 hEL hLat T ε hε i s hs hsi hi w hwW hN M hM
    have h2 := hM w (Finset.mem_filter.2 ⟨hwW, Nat.le_add_right _ _⟩)
    calc D.Sf ε i w (Xs T i s) / D.wt w ≤ D.Dg T ε i s w + 3 ^ D.f * ep * M := h
      _ ≤ M + 3 ^ D.f * ep * M := by linarith
      _ = (1 + 3 ^ D.f * ep) * M := by ring

  have h1 : D.Sf ε i w (Xs T i 1) / D.wt w ≤
      (1 + 3 ^ D.f * ep) * ((1 + D.e i) * ((1 + 2 ^ D.f * ep) * σ (i - 1) ^ 2)) := by
    apply hS 1 le_rfl hi1
    intro w' hw'
    have hw'W : w' ∈ D.Wall := (Finset.mem_filter.1 hw').1
    have hw'c : D.cnt w' ≤ D.cnt w + D.K := (Finset.mem_filter.1 hw').2
    obtain ⟨R, hR1, hR2⟩ := exists_reps (D.La (i - 1 + 1) 1) (T.Sg (i - 1 + 1) 1)
    have hd := hDiag E W D hG hKer hW hA13 T ε hε i 1 le_rfl hi1 hi w' R hR1
    have hii : i - 1 + 1 = i := by omega
    rw [hii] at hd hR2
    have hT : D.cnt w + 2 * D.K ≤ 4 * D.K * (D.r + 1) :=
      budget_top D.K D.r i 1 (D.cnt w) 2 hi1 hi hwc (by omega)
    have hB : D.cnt w + 2 * D.K ≤ 4 * D.K * (D.r + 1 - (i - 1)) :=
      budget_step D.K D.r i 1 (D.cnt w) 2 hi1 hi hwc (by omega)
    have hN : D.cnt w' + D.K ≤ D.Ntop := by
      simp only [Data.Ntop]; omega
    have hlow : ∀ w'' ∈ D.Wb (D.cnt w' + D.K),
        D.N0 ε (i - 1) w'' (T.X (i - 1)) (D.Kr (i - 1)) ≤ σ (i - 1) ^ 2 := by
      intro w'' hw''
      refine (hσ (i - 1) (by omega)).2 w'' (Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hw'').1, ?_⟩)
      have := (Finset.mem_filter.1 hw'').2
      simp only [Data.budget]; omega
    have ho := hOne E W D ep hG hKer hW hA13 hEW hP hLat T ε hε i hi1 hi w' hw'W hN R hR2
      (σ (i - 1) ^ 2) hlow
    have hw0 := hlow w' (Finset.mem_filter.2 ⟨hw'W, Nat.le_add_right _ _⟩)
    calc D.Dg T ε i 1 w' ≤ _ := hd
      _ ≤ _ := ho
      _ ≤ (1 + D.e i) * (σ (i - 1) ^ 2 + 2 ^ D.f * ep * σ (i - 1) ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ = (1 + D.e i) * ((1 + 2 ^ D.f * ep) * σ (i - 1) ^ 2) := by ring

  have h2 : ∀ s, 2 ≤ s → s ≤ i → D.Sf ε i w (Xs T i s) / D.wt w ≤
      (1 + 3 ^ D.f * ep) * (C₄ ^ (D.f * s) * (∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') *
        ((1 + D.e i) * σ (i - s) ^ 2)) := by
    intro s hs hsi
    apply hS s (by omega) hsi
    intro w' hw'
    have hw'W : w' ∈ D.Wall := (Finset.mem_filter.1 hw').1
    have hw'c : D.cnt w' ≤ D.cnt w + D.K := (Finset.mem_filter.1 hw').2
    obtain ⟨R, hR1, hR2⟩ := exists_reps (D.La (i - s + 1) s) (T.Sg (i - s + 1) s)
    have hd := hDiag E W D hG hKer hW hA13 T ε hε i s (by omega) hsi hi w' R hR1
    have hT : D.cnt w + (s + 2) * D.K ≤ 4 * D.K * (D.r + 1) :=
      budget_top D.K D.r i s (D.cnt w) (s + 2) hsi hi hwc (by omega)
    have hB : D.cnt w + (s + 2) * D.K ≤ 4 * D.K * (D.r + 1 - (i - s)) :=
      budget_step D.K D.r i s (D.cnt w) (s + 2) hsi hi hwc (by omega)
    have hsK : (s + 2) * D.K = D.K + (s + 1) * D.K := by ring
    have hN : D.cnt w' + (s + 1) * D.K ≤ D.Ntop := by
      simp only [Data.Ntop]; omega
    have hlow : ∀ w'' ∈ D.Wb (D.cnt w' + (s + 1) * D.K),
        D.N0 ε (i - s) w'' (T.X (i - s)) (D.Kr (i - s)) ≤ σ (i - s) ^ 2 := by
      intro w'' hw''
      refine (hσ (i - s) (by omega)).2 w'' (Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hw'').1, ?_⟩)
      have := (Finset.mem_filter.1 hw'').2
      simp only [Data.budget]; omega
    have hm := hMulti E W D C₄ hG hKer hW hA13 hEB h4 hv0 T ε hε i s hs hsi hi w' hw'W hN
      (hv1 _ _ (by omega) (by omega) (by omega)) R hR2 (σ (i - s) ^ 2) hlow
    exact hd.trans hm

  have hsplit := hSplit E W D hG hKer T ε hε i hi1 w
  have hIcc : Icc 1 i = insert 1 (Icc 2 i) := by
    ext s; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have hnot : (1 : ℕ) ∉ Icc 2 i := by simp
  have hfirst : √(D.Q T ε i w) ≤ ∑ s ∈ Icc 1 i, √(D.Sf ε i w (Xs T i s) / D.wt w) := by
    have : ∀ x : ℝ, √(x / D.wt w) = √x / √(D.wt w) := fun x => Real.sqrt_div' x hwt.le
    simp only [Data.Q, this, ← Finset.sum_div]
    exact div_le_div_of_nonneg_right hsplit (Real.sqrt_nonneg _)
  refine hfirst.trans ?_
  rw [hIcc, Finset.sum_insert hnot]
  apply add_le_add
  · have hσ0 : 0 ≤ σ (i - 1) := (hσ (i - 1) (by omega)).1
    refine (Real.sqrt_le_sqrt h1).trans (le_of_eq ?_)
    have : (1 + 3 ^ D.f * ep) * ((1 + D.e i) * ((1 + 2 ^ D.f * ep) * σ (i - 1) ^ 2)) =
        (1 + 3 ^ D.f * ep) * (1 + 2 ^ D.f * ep) * (1 + D.e i) * σ (i - 1) ^ 2 := by ring
    rw [this, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq hσ0,
      Real.sqrt_mul' _ (by linarith : 0 ≤ 1 + D.e i)]
  · apply Finset.sum_le_sum
    intro s hs
    rw [Finset.mem_Icc] at hs
    have hσ0 : 0 ≤ σ (i - s) := (hσ (i - s) (by omega)).1
    refine (Real.sqrt_le_sqrt (h2 s hs.1 hs.2)).trans (le_of_eq ?_)
    have : (1 + 3 ^ D.f * ep) * (C₄ ^ (D.f * s) * (∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') *
        ((1 + D.e i) * σ (i - s) ^ 2)) =
        (1 + 3 ^ D.f * ep) * (1 + D.e i) * C₄ ^ (D.f * s) *
          (∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') * σ (i - s) ^ 2 := by ring
    rw [this, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq hσ0]

lemma coef (D : Data E W) (Θ C₄ C₀ a e : ℝ) (hΘ : 1 ≤ Θ) (h4 : 1 ≤ C₄) (h0 : 2 * C₄ ≤ C₀)
    (hf : 1 ≤ D.f) (hS : D.SizesBelow Θ) (ha0 : 0 ≤ a) (ha : a ≤ 1) (_he0 : 0 ≤ e) (he : e ≤ 1)
    (i s : ℕ) (hs : 2 ≤ s) (hsi : s ≤ i) (hi : i ≤ D.r + 1) :
    √((1 + a) * (1 + e) * C₄ ^ (D.f * s) * ∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') ≤
      ((C₀ / Θ) ^ D.f) ^ (s - 1) := by
  have hΘ0 : 0 < Θ := by linarith
  set q : ℝ := (Θ ^ D.f)⁻¹ with hq
  have hq0 : 0 ≤ q := by positivity
  have hC0 : 0 ≤ C₀ := by linarith
  have hP : ∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s' ≤ (q ^ 2) ^ (s - 1) := by
    calc ∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s' ≤ ∏ _s' ∈ Ico 1 s, q ^ 2 := by
          apply Finset.prod_le_prod₀ (fun s' _ => hS.1 _ _)
          intro s' hs'
          rw [Finset.mem_Ico] at hs'
          exact hS.2 _ _ (by omega) hs'.1 (by omega)
      _ = (q ^ 2) ^ (s - 1) := by simp
  have hP0 : 0 ≤ ∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s' := Finset.prod_nonneg fun s' _ => hS.1 _ _
  have hR : ((C₀ / Θ) ^ D.f) ^ (s - 1) = (C₀ ^ D.f) ^ (s - 1) * q ^ (s - 1) := by
    rw [div_pow, div_eq_mul_inv, mul_pow]
  have hpow : 4 * C₄ ^ (D.f * s) ≤ ((C₀ ^ D.f) ^ (s - 1)) ^ 2 := by
    have e1 : ((C₀ ^ D.f) ^ (s - 1)) ^ 2 = C₀ ^ (D.f * (s - 1) * 2) := by
      rw [← pow_mul, ← pow_mul, mul_assoc]
    have e2 : (2 * C₄) ^ (D.f * (s - 1) * 2) ≤ C₀ ^ (D.f * (s - 1) * 2) :=
      pow_le_pow_left₀ (by linarith) h0 _
    have hn : 1 ≤ D.f * (s - 1) := Nat.mul_pos hf (by omega)
    have e3 : (4 : ℝ) ≤ 2 ^ (D.f * (s - 1) * 2) := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (D.f * (s - 1) * 2) := pow_le_pow_right₀ (by norm_num) (by omega)
    have e4 : C₄ ^ (D.f * s) ≤ C₄ ^ (D.f * (s - 1) * 2) := by
      apply pow_le_pow_right₀ h4
      have : s ≤ (s - 1) * 2 := by omega
      calc D.f * s ≤ D.f * ((s - 1) * 2) := Nat.mul_le_mul_left _ this
        _ = D.f * (s - 1) * 2 := by ring
    rw [e1]
    refine le_trans ?_ e2
    rw [mul_pow]
    exact mul_le_mul e3 e4 (by positivity) (by positivity)
  rw [hR]
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have h1 : (1 + a) * (1 + e) ≤ 4 := by nlinarith
  have hc : 0 ≤ C₄ ^ (D.f * s) := by positivity
  calc (1 + a) * (1 + e) * C₄ ^ (D.f * s) * ∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s'
      ≤ 4 * C₄ ^ (D.f * s) * (q ^ 2) ^ (s - 1) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right h1 hc) hP hP0 (by positivity)
    _ ≤ ((C₀ ^ D.f) ^ (s - 1)) ^ 2 * (q ^ 2) ^ (s - 1) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = ((C₀ ^ D.f) ^ (s - 1) * q ^ (s - 1)) ^ 2 := by
        rw [mul_pow, ← pow_mul q, ← pow_mul q, mul_comm 2 (s - 1)]

lemma size_le_one (D : Data E W) (Θ : ℝ) (hΘ : 1 ≤ Θ) (hS : D.SizesBelow Θ) :
    ∀ b s, 1 ≤ b → 1 ≤ s → b + s ≤ D.r + 2 → D.vol b s ≤ 1 := by
  intro b s hb hs hbs
  refine (hS.2 b s hb hs hbs).trans ?_
  have h1 : (Θ ^ D.f)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hΘ)
  have h0 : 0 ≤ (Θ ^ D.f)⁻¹ := by positivity
  exact pow_le_one₀ h0 h1

lemma small (r f : ℕ) (C C₀ Θ : ℝ) (hΘ : 0 < Θ) (h0 : 0 ≤ C₀) (h : C₀ ≤ C)
    (hs : (r : ℝ) * (C / Θ) ^ f ≤ 1) : (r : ℝ) * (C₀ / Θ) ^ f ≤ 1 := by
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg r)) hs
  exact pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right h hΘ.le) f

theorem X0 (T : Tower E) : T.X 0 = {[]} := by
  ext p
  rw [T.isTower 0 p, Finset.mem_singleton]
  constructor
  · rintro ⟨hl, hb⟩
    cases p with
    | nil => rfl
    | cons a q =>
      have := (hb 0 (by simp)).1
      simp [level] at hl
      simp at this
      omega
  · rintro rfl
    simp [level]

theorem Q0 (D : Data E W) (T : Tower E) (ε : ℝ) (w : W) :
    D.Q T ε 0 w = (D.gram ε 0 w [] []).re / D.wt w := by
  simp [Data.Q, Data.Sf, X0, D.K0]

lemma gram_diag (D : Data E W) (hG : D.GramPSD) (ε : ℝ) (hε : 0 < ε) (i : ℕ) (w : W) (p : Pt E) :
    0 ≤ (D.gram ε i w p p).re := by
  have h := hG ε hε i w {p}
  have := Matrix.PosSemidef.diag_nonneg h (i := ⟨p, by simp⟩)
  have h2 : 0 ≤ D.gram ε i w p p := by simpa using this
  exact (Complex.le_def.1 h2).1

end Formalism.FourierDecayAlt.P.OneLevelCoefficients

namespace Formalism.FourierDecayAlt.P

theorem levelInequalityOfSteps : Formalism.FourierDecayAlt.TB.OneLevelOfSteps := OneLevelCoefficients.oneLevel_of_steps

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PointwiseStabiliserParametrisationBijective
section
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Formalism.FourierDecayAlt.P.S3x1

open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3

section Blocks

variable {A : Type} {r k : ℕ}

variable [CommRing A]

variable {P : Matrix (Fin k) (Fin k) A → Prop}

theorem uni_unit {n : ℕ} {u : Matrix (Fin n) (Fin n) A} (hu : IsUpUni u) : IsUnit u.det := by
  rw [isUpUni_det A hu]; exact isUnit_one

end Blocks

end Formalism.FourierDecayAlt.P.S3x1




namespace Formalism.FourierDecayAlt.P.S3x1

open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3

section Count

theorem card_lt_pairs (n : ℕ) : Nat.card {p : Fin n × Fin n // p.1 < p.2} = n * (n - 1) / 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type_right]
  have h : ∀ j : Fin n, ∑ i : Fin n, (if i < j then 1 else 0) = (j : ℕ) := by
    intro j
    rw [← Finset.card_filter]
    have e : Finset.filter (fun i : Fin n => i < j) Finset.univ = Finset.Iio j := by ext i; simp
    rw [e, Fin.card_Iio]
  simp_rw [h]
  rw [Fin.sum_univ_eq_sum_range (fun i => i) n, Finset.sum_range_id]

variable {A : Type} [CommRing A]

def uniEquiv (n : ℕ) : {u : Matrix (Fin n) (Fin n) A // IsUpUni u} ≃ ({p : Fin n × Fin n // p.1 < p.2} → A) where
  toFun u := fun p => u.1 p.1.1 p.1.2
  invFun f := ⟨Matrix.of fun i j => if h : i < j then f ⟨(i, j), h⟩ else if i = j then 1 else 0, by
    constructor
    · intro i j hij
      have hij' : j < i := hij
      simp [not_lt.2 hij'.le, hij'.ne']
    · intro a; simp⟩
  left_inv u := by
    apply Subtype.ext
    ext i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h]
    · subst h; simp [u.2.2 i]
    · have : u.1 i j = 0 := u.2.1 h
      simp [not_lt.2 h.le, h.ne', this]
  right_inv f := by
    funext p
    obtain ⟨⟨i, j⟩, h⟩ := p
    have h' : i < j := h
    simp [h']

theorem card_uni (K : Type) [Field K] [Fintype K] (n : ℕ) :
    Nat.card {u : Matrix (Fin n) (Fin n) K // IsUpUni u} = Fintype.card K ^ (n * (n - 1) / 2) := by
  rw [Nat.card_congr (uniEquiv n), Nat.card_fun, card_lt_pairs, Nat.card_eq_fintype_card]

noncomputable def upUniGEquiv (n : ℕ) : upUniG A n ≃ {u : Matrix (Fin n) (Fin n) A // IsUpUni u} where
  toFun g := ⟨g.1.1, g.2⟩
  invFun u := ⟨Matrix.GeneralLinearGroup.mk'' u.1 (uni_unit u.2), u.2⟩
  left_inv g := Subtype.ext (Units.ext rfl)
  right_inv u := rfl

variable {r k : ℕ}

def mk (a : Matrix (Fin r) (Fin r) A) (b : Matrix (Fin r) (Mid k) A) (c : Matrix (Fin r) (Fin r) A)
    (m : Matrix (Mid k) (Mid k) A) (e : Matrix (Mid k) (Fin r) A) (f : Matrix (Fin r) (Fin r) A) :
    Matrix (Idx r k) (Idx r k) A :=
  Matrix.fromBlocks a (Matrix.fromCols b c) 0 (Matrix.fromBlocks m e 0 f)

section mk
variable (a : Matrix (Fin r) (Fin r) A) (b : Matrix (Fin r) (Mid k) A) (c : Matrix (Fin r) (Fin r) A)
    (m : Matrix (Mid k) (Mid k) A) (e : Matrix (Mid k) (Fin r) A) (f : Matrix (Fin r) (Fin r) A)
end mk

end Count

end Formalism.FourierDecayAlt.P.S3x1

namespace Formalism.FourierDecayAlt.P.S3x1

open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni upUniG isUpUni_mul isUpUni_inv isUpUni_one isUpUni_det)
open Formalism.FourierDecayAlt.S3

section Count2

variable {A : Type} [CommRing A] {r k : ℕ}

theorem prod_gl (q k : ℕ) : ∏ i : Fin k, (q ^ k - q ^ (i : ℕ)) =
    q ^ (k * (k - 1) / 2) * ∏ i ∈ Icc 1 k, (q ^ i - 1) := by
  rw [Fin.prod_univ_eq_prod_range (fun i => q ^ k - q ^ i) k, ← Finset.sum_range_id,
    ← Finset.prod_pow_eq_pow_sum]
  have h1 : ∏ i ∈ Icc 1 k, (q ^ i - 1) = ∏ i ∈ range k, (q ^ (k - i) - 1) := by
    refine Finset.prod_nbij' (fun i => k - i) (fun i => k - i) ?_ ?_ ?_ ?_ ?_
    · intro a ha; simp only [Finset.mem_Icc, Finset.mem_range] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Icc, Finset.mem_range] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Icc, Finset.mem_range] at ha ⊢; omega
    · intro a ha; simp only [Finset.mem_Icc, Finset.mem_range] at ha ⊢; omega
    · intro a ha
      simp only [Finset.mem_Icc] at ha
      have : k - (k - a) = a := by omega
      rw [this]
  rw [h1, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i hi => ?_
  have hi' : i ≤ k := (Finset.mem_range.1 hi).le
  rw [Nat.mul_sub, ← pow_add, Nat.add_sub_cancel' hi', mul_one]

end Count2

end Formalism.FourierDecayAlt.P.S3x1





open Formalism.FourierDecayAlt.P.S3x1 in
theorem Formalism.FourierDecayAlt.P.gamma_factor_product : Formalism.FourierDecayAlt.S3.GammaProduct := by
  intro K _ _ k
  rw [Matrix.card_GL_field, Nat.card_congr (upUniGEquiv k), card_uni, prod_gl]

end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RealPowerIdentities
section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology

namespace Formalism.FourierDecayAlt.P

namespace RealPowerIdentities

theorem inv_pow_triangle_mul_rpow_half {T : ℝ} (hT : 0 < T) (m : ℕ) :
    (T ^ (m * (m + 1) / 2))⁻¹ * T ^ ((m : ℝ) / 2) = T ^ (-((m : ℝ) ^ 2) / 2) := by
  have h2 : (2 : ℕ) ∣ m * (m + 1) := (Nat.even_mul_succ_self m).two_dvd
  have hc : ((m * (m + 1) / 2 : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) + 1) / 2 := by
    rw [Nat.cast_div h2 (by norm_num)]
    push_cast
    ring
  rw [← Real.rpow_natCast, hc, ← Real.rpow_neg hT.le, ← Real.rpow_add hT]
  congr 1
  ring

theorem rpow_half_mul_pow_triangle {Z : ℝ} (hZ : 0 < Z) {m : ℕ} (hm : 1 ≤ m) :
    Z ^ ((m : ℝ) / 2) * Z ^ (m * (m - 1) / 2) = Z ^ ((m : ℝ) ^ 2 / 2) := by
  have h2 : (2 : ℕ) ∣ m * (m - 1) := (Nat.even_mul_pred_self m).two_dvd
  have hc : ((m * (m - 1) / 2 : ℕ) : ℝ) = (m : ℝ) * ((m : ℝ) - 1) / 2 := by
    rw [Nat.cast_div h2 (by norm_num)]
    push_cast [Nat.cast_sub hm]
    ring
  rw [← Real.rpow_natCast, hc, ← Real.rpow_add hZ]
  congr 1
  ring

end RealPowerIdentities

open RealPowerIdentities in
theorem germExpansionOfTestFunction : Formalism.FourierDecayAlt.A6.GermPhiAssemble := by
  intro hOsc hSt hInv hMod K _ _ _ R ψ hd hn m hm γ hγ L₀ Λ₀ Q hL₀ hΛ₀ hQc hQu
  obtain ⟨L₁, Λ₁, hL₁, hΛ₁, V₁, hV₁, hO⟩ := hOsc K R ψ hd hn m hm L₀ Λ₀ Q hL₀ hΛ₀ hQc hQu
  have hQ'c : IsCompact ((fun d : K => (-1) ^ m * d) '' Q) :=
    hQc.image (continuous_const.mul continuous_id)
  have hQ'u : ∀ d ∈ (fun d : K => (-1) ^ m * d) '' Q, IsUnit d := by
    rintro _ ⟨d, hdQ, rfl⟩
    exact (isUnit_one.neg.pow m).mul (hQu d hdQ)
  obtain ⟨V₂, hV₂, hS⟩ := hSt K R ψ hd hn m hm γ hγ L₁ Λ₁ _ hL₁ hΛ₁ hQ'c hQ'u
  refine ⟨V₁ ∩ V₂, Filter.inter_mem hV₁ hV₂, ?_⟩
  intro Φ hΦ t c ht hc
  have hD : ((c * t ^ m : Kˣ) : K) ∈ Q := by simpa using hc
  obtain ⟨A, hA, hAz, hAo⟩ := hO Φ hΦ (c * t ^ m) hD
  obtain ⟨Λ, hΛ, hinv⟩ := hInv K R ψ hd hn m L₁ Λ₁ hL₁ hΛ₁ A ((t⁻¹ : Kˣ) : K)
    (((-1) ^ m * (c * t ^ m) : Kˣ) : K) hA
  have hD' : (((-1) ^ m * (c * t ^ m) : Kˣ) : K) ∈ (fun d : K => (-1) ^ m * d) '' Q :=
    ⟨_, hD, by simp⟩
  have hDeq : ((-1) ^ m * (c * t ^ m) : Kˣ) = (-t) ^ m * c := by
    rw [neg_pow t m]
    ac_rfl
  have hT : 0 < modK R (t : K) := (hMod K R ψ hd t t).1
  rw [hAo t c ht.1 rfl Λ hΛ hinv, hS t _ A ht.2 hD' hA Λ hΛ hinv]
  unfold germSum
  rw [← mul_assoc, ← Complex.ofReal_mul, inv_pow_triangle_mul_rpow_half hT m]
  congr 1
  refine finsum_congr fun z => ?_
  by_cases hz : z ^ (m + 1) = (-1) ^ m * (c * t ^ m)
  · have hZ : 0 < modK R (z : K) := (hMod K R ψ hd z z).1
    rw [if_pos hz, if_pos (hz.trans hDeq), hAz z hz]
    unfold germCoef
    rw [← rpow_half_mul_pow_triangle hZ hm]
    push_cast
    ring
  · rw [if_neg hz, if_neg (fun h => hz (h.trans hDeq.symm))]

end Formalism.FourierDecayAlt.P
end

