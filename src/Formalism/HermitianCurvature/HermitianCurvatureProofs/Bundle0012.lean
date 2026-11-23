module

public import Mathlib
public import Formalism.HermitianCurvature.StatementTB
public import Formalism.HermitianCurvature.MemParahoricTimesPrincipalCongruenceIff
public import Formalism.HermitianCurvature.ThetaExistenceInductiveFromPieces
public import Formalism.HermitianCurvature.Bundle0002
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0007

@[expose] public section

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FormDomination
section
namespace Formalism.FourierDecayAlt.P.FormDomination

open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data

open scoped ComplexOrder

theorem form_nonneg {α : Type} (Y : Finset α) (k g : α → α → ℂ) (hk : PSDOn Y k)
    (hg : PSDOn Y g) : 0 ≤ (∑ a ∈ Y, ∑ b ∈ Y, k a b * g a b).re := by
  have H := (Matrix.PosSemidef.hadamard hk hg).dotProduct_mulVec_nonneg (fun _ => (1 : ℂ))
  have e : star (fun _ : Y => (1 : ℂ)) ⬝ᵥ
      ((Matrix.hadamard (Matrix.of fun x y : Y => k x y) (Matrix.of fun x y : Y => g x y)).mulVec
        (fun _ => (1 : ℂ))) = ∑ a ∈ Y, ∑ b ∈ Y, k a b * g a b := by
    simp only [dotProduct, Matrix.mulVec, Matrix.hadamard_apply, Matrix.of_apply, Pi.star_apply,
      star_one, one_mul, mul_one]
    rw [← Finset.sum_coe_sort Y]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_coe_sort Y]
  rw [e] at H
  exact (Complex.le_def.1 H).1

theorem form_dom {α ι : Type} (Y : Finset α) (R : Finset ι) (c : ℝ) (k g : α → α → ℂ)
    (Th : ι → α → α → ℂ)
    (h : PSDOn Y (fun a b => (c : ℂ) * k a b - ∑ t ∈ R, Th t a b)) (hg : PSDOn Y g) :
    ∑ t ∈ R, (∑ a ∈ Y, ∑ b ∈ Y, Th t a b * g a b).re ≤
      c * (∑ a ∈ Y, ∑ b ∈ Y, k a b * g a b).re := by
  have H := form_nonneg Y _ g h hg
  have e : ∑ a ∈ Y, ∑ b ∈ Y, ((c : ℂ) * k a b - ∑ t ∈ R, Th t a b) * g a b =
      (c : ℂ) * ∑ a ∈ Y, ∑ b ∈ Y, k a b * g a b -
        ∑ t ∈ R, ∑ a ∈ Y, ∑ b ∈ Y, Th t a b * g a b := by
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    congr 1
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
  rw [e, Complex.sub_re, Complex.re_ofReal_mul] at H
  rw [← Complex.re_sum]
  linarith

theorem prob_le {α : Type} (S : Finset α) (θ g : α → ℝ) (hθ : IsProb S θ) (M : ℝ)
    (hg : ∀ a ∈ S, g a ≤ M) : ∑ a ∈ S, θ a * g a ≤ M := by
  calc ∑ a ∈ S, θ a * g a ≤ ∑ a ∈ S, θ a * M :=
        Finset.sum_le_sum fun a ha => mul_le_mul_of_nonneg_left (hg a ha) (hθ.1 a)
    _ = M := by rw [← Finset.sum_mul, hθ.2.2, one_mul]

theorem prob_nonneg {α : Type} (S : Finset α) (θ g : α → ℝ) (hθ : IsProb S θ)
    (hg : ∀ a ∈ S, 0 ≤ g a) : 0 ≤ ∑ a ∈ S, θ a * g a :=
  Finset.sum_nonneg fun a ha => mul_nonneg (hθ.1 a) (hg a ha)

variable {E W : Type} [Field E] (D : Data E W)

theorem baseGram_nonneg (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ} (hε : 0 < ε) (k : ℕ) (w : W)
    (Y : Finset (Pt E)) (κ : Pt E → Pt E → ℂ) (hκ : PSDOn Y κ) : 0 ≤ D.N0 ε k w Y κ :=
  div_nonneg (form_nonneg Y κ _ hκ (hG ε hε k w Y)) (hW w).le

theorem sum_baseGram_le (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ} (hε : 0 < ε) (k : ℕ) (w : W)
    (Y : Finset (Pt E)) (R : Finset E) (c : ℝ) (κ : Pt E → Pt E → ℂ)
    (Th : E → Pt E → Pt E → ℂ)
    (h : PSDOn Y (fun a b => (c : ℂ) * κ a b - ∑ t ∈ R, Th t a b)) :
    ∑ t ∈ R, D.N0 ε k w Y (Th t) ≤ c * D.N0 ε k w Y κ := by
  unfold Data.N0
  rw [← Finset.sum_div, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right (form_dom Y R c κ _ Th h (hG ε hε k w Y)) (hW w).le

theorem mean_dom (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ} (hε : 0 < ε) (k : ℕ)
    (S : Finset W) (θ : W → ℝ) (hθ : IsProb S θ)
    (Y : Finset (Pt E)) (R : Finset E) (c : ℝ) (hc : 0 ≤ c) (κ : Pt E → Pt E → ℂ)
    (Th : E → Pt E → Pt E → ℂ)
    (h : PSDOn Y (fun a b => (c : ℂ) * κ a b - ∑ t ∈ R, Th t a b)) (M : ℝ)
    (hM : ∀ w' ∈ S, D.N0 ε k w' Y κ ≤ M) :
    ∑ t ∈ R, ∑ w' ∈ S, θ w' * D.N0 ε k w' Y (Th t) ≤ c * M := by
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  refine prob_le S θ _ hθ _ fun w' hw' => ?_
  exact (sum_baseGram_le D hG hW hε k w' Y R c κ Th h).trans (mul_le_mul_of_nonneg_left (hM w' hw') hc)

end Formalism.FourierDecayAlt.P.FormDomination

namespace Formalism.FourierDecayAlt.P

open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data Formalism.FourierDecayAlt.P.FormDomination

open Classical

theorem longBlockStep : Formalism.FourierDecayAlt.TB.MultiStep := by
  intro E W _ D C₄ hG hK hW hA hB hC hv T ε hε i s hs hsi hi w hw hcnt hvol R hR M hM
  obtain ⟨θ, hθ, hest⟩ := hB ε hε i s hs hsi hi w hw hcnt hvol
  obtain ⟨⟨he0, he1⟩, -, -, hdom⟩ := hA i s (by omega) hsi hi
  have hY : ∀ h ∈ T.X (i - s), level h = i - s := fun h hh => ((T.isTower _ _).1 hh).1
  have hc : 0 ≤ C₄ ^ (D.f * s) * (∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') :=
    mul_nonneg (pow_nonneg (by linarith) _) (Finset.prod_nonneg fun s' _ => hv _ _)
  have hd := hdom R hR (T.X (i - s)) hY
  have hd' : PSDOn (T.X (i - s)) (fun a b => (((1 + D.e i : ℝ)) : ℂ) * D.Kr (i - s) a b -
      ∑ t ∈ R, D.Th i s t a b) := by
    push_cast; exact hd
  calc ∑ t₀ ∈ R, ∑ t ∈ (T.Sg (i - s + 1) s).filter (fun t => t - t₀ ∈ D.La (i - s + 1) s),
            (D.Nst ε i s w (T.X (i - s)) (D.Th i s t₀) t t).re
      ≤ ∑ t₀ ∈ R, C₄ ^ (D.f * s) * (∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') *
          ∑ w' ∈ D.Wb (D.cnt w + (s + 1) * D.K),
            θ w' * D.N0 ε (i - s) w' (T.X (i - s)) (D.Th i s t₀) := by
        refine Finset.sum_le_sum fun t₀ _ => ?_
        refine hest (T.X (i - s)) hY _ (hK.2 i s t₀ _) t₀ _ fun t ht => ?_
        rw [Finset.mem_filter] at ht
        exact ⟨fun h0 => T.zero_not_mem _ _ (h0 ▸ ht.1), ht.2⟩
    _ = C₄ ^ (D.f * s) * (∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') *
          ∑ t₀ ∈ R, ∑ w' ∈ D.Wb (D.cnt w + (s + 1) * D.K),
            θ w' * D.N0 ε (i - s) w' (T.X (i - s)) (D.Th i s t₀) := by
        rw [Finset.mul_sum]
    _ ≤ C₄ ^ (D.f * s) * (∏ s' ∈ Ico 1 s, D.vol (i - s + 1) s') * ((1 + D.e i) * M) :=
        mul_le_mul_of_nonneg_left
          (mean_dom D hG hW hε (i - s) _ θ hθ _ R (1 + D.e i) (by linarith) _ _ hd' M hM) hc

theorem singleBlockStep : Formalism.FourierDecayAlt.TB.OneStep := by
  intro E W _ D ep hG hK hW hA hWv hP hL T ε hε i hi1 hi w hw hcnt R hR M hM
  obtain ⟨θ, hθ, hest⟩ := hWv ε hε i hi1 hi w hw hcnt
  obtain ⟨⟨he0, he1⟩, -, -, hdom⟩ := hA i 1 le_rfl hi1 hi
  have hii : i - 1 + 1 = i := Nat.sub_add_cancel hi1
  rw [hii] at hdom
  have hY : ∀ h ∈ T.X (i - 1), level h = i - 1 := fun h hh => ((T.isTower _ _).1 hh).1
  have hep : 0 ≤ ep := by simpa using hL.1 i hi1 hi ∅ (by simp)
  have hd := hdom R hR (T.X (i - 1)) hY
  have hd' : PSDOn (T.X (i - 1)) (fun a b => (((1 + D.e i : ℝ)) : ℂ) * D.Kr (i - 1) a b -
      ∑ t ∈ R, D.Th i 1 t a b) := by
    push_cast; exact hd
  have h1e : 0 ≤ 1 + D.e i := by linarith

  set g : Finset (Fin D.f) → E → ℝ := fun A t₀ => ∑ w' ∈ D.Wb (D.cnt w + D.K),
    θ A w' * D.N0 ε (i - 1) w' (T.X (i - 1)) (D.Th i 1 t₀) with hg
  have hg0 : ∀ A t₀, 0 ≤ g A t₀ := fun A t₀ =>
    prob_nonneg _ _ _ (hθ A) fun w' _ => baseGram_nonneg D hG hW hε _ _ _ _ (hK.2 i 1 t₀ _)
  have hstep : ∀ t₀ ∈ R, ∑ t ∈ (T.Sg i 1).filter (fun t => t - t₀ ∈ D.La i 1),
      (D.Nst ε i 1 w (T.X (i - 1)) (D.Th i 1 t₀) t t).re ≤
        D.N0 ε (i - 1) w (T.X (i - 1)) (D.Th i 1 t₀) + ep * ∑ A, g A t₀ := by
    intro t₀ _
    have hpsd := hK.2 i 1 t₀ (T.X (i - 1))
    obtain ⟨h0, hl⟩ := hest (T.X (i - 1)) hY _ hpsd
    have hbound : ∀ L : Finset E, (∀ l ∈ L, l ∈ D.Lad i ∧ l ≠ 0) →
        ∑ l ∈ L, ‖D.Nhat ε i w (T.X (i - 1)) (D.Th i 1 t₀) l‖ ≤ ep * ∑ A, g A t₀ := by
      intro L hLm
      have hG0 : 0 ≤ ∑ A, g A t₀ := Finset.sum_nonneg fun A _ => hg0 A t₀
      have h1 : ∀ l ∈ L, ‖D.Nhat ε i w (T.X (i - 1)) (D.Th i 1 t₀) l‖ ≤
          max (D.maj (D.szD i) l) 0 * ∑ A, g A t₀ := by
        intro l hl'
        obtain ⟨A, hA'⟩ := hl l (hLm l hl').1 (hLm l hl').2
        calc ‖D.Nhat ε i w (T.X (i - 1)) (D.Th i 1 t₀) l‖ ≤ D.maj (D.szD i) l * g A t₀ := hA'
          _ ≤ max (D.maj (D.szD i) l) 0 * g A t₀ :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (hg0 A t₀)
          _ ≤ max (D.maj (D.szD i) l) 0 * ∑ A, g A t₀ :=
              mul_le_mul_of_nonneg_left
                (Finset.single_le_sum (f := fun A => g A t₀) (fun A _ => hg0 A t₀)
                  (Finset.mem_univ A)) (le_max_right _ _)
      have h2 : ∑ l ∈ L, max (D.maj (D.szD i) l) 0 ≤ ep := by
        have h3 := hL.1 i hi1 hi (L.filter fun l => 0 ≤ D.maj (D.szD i) l)
          (fun l hl' => hLm l (Finset.mem_filter.1 hl').1)
        rw [Finset.sum_filter] at h3
        refine le_trans (le_of_eq (Finset.sum_congr rfl fun l _ => ?_)) h3
        split_ifs with hh
        · exact max_eq_left hh
        · exact max_eq_right (not_le.1 hh).le
      calc ∑ l ∈ L, ‖D.Nhat ε i w (T.X (i - 1)) (D.Th i 1 t₀) l‖
          ≤ ∑ l ∈ L, max (D.maj (D.szD i) l) 0 * ∑ A, g A t₀ := Finset.sum_le_sum h1
        _ = (∑ l ∈ L, max (D.maj (D.szD i) l) 0) * ∑ A, g A t₀ := by rw [Finset.sum_mul]
        _ ≤ ep * ∑ A, g A t₀ := mul_le_mul_of_nonneg_right h2 hG0
    have hp := hP ε hε i hi1 hi w (T.X (i - 1)) hY _ hpsd t₀ _ hbound
      ((T.Sg i 1).filter (fun t => t - t₀ ∈ D.La i 1)) (fun t ht => by
        rw [Finset.mem_filter] at ht
        exact ⟨fun h0 => T.zero_not_mem _ _ (h0 ▸ ht.1), ht.2⟩)
    rw [h0, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (baseGram_nonneg D hG hW hε _ _ _ _ hpsd)] at hp
    exact hp
  have hsumG : ∑ t₀ ∈ R, ∑ A, g A t₀ ≤ 2 ^ D.f * ((1 + D.e i) * M) := by
    rw [Finset.sum_comm]
    calc ∑ A : Finset (Fin D.f), ∑ t₀ ∈ R, g A t₀
        ≤ ∑ _A : Finset (Fin D.f), (1 + D.e i) * M :=
          Finset.sum_le_sum fun A _ =>
            mean_dom D hG hW hε (i - 1) _ (θ A) (hθ A) _ R (1 + D.e i) h1e _ _ hd' M hM
      _ = 2 ^ D.f * ((1 + D.e i) * M) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast; ring
  calc ∑ t₀ ∈ R, ∑ t ∈ (T.Sg i 1).filter (fun t => t - t₀ ∈ D.La i 1),
            (D.Nst ε i 1 w (T.X (i - 1)) (D.Th i 1 t₀) t t).re
      ≤ ∑ t₀ ∈ R, (D.N0 ε (i - 1) w (T.X (i - 1)) (D.Th i 1 t₀) + ep * ∑ A, g A t₀) :=
        Finset.sum_le_sum hstep
    _ = ∑ t₀ ∈ R, D.N0 ε (i - 1) w (T.X (i - 1)) (D.Th i 1 t₀) +
          ep * ∑ t₀ ∈ R, ∑ A, g A t₀ := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (1 + D.e i) * D.N0 ε (i - 1) w (T.X (i - 1)) (D.Kr (i - 1)) +
          ep * (2 ^ D.f * ((1 + D.e i) * M)) :=
        add_le_add (sum_baseGram_le D hG hW hε (i - 1) w _ R (1 + D.e i) _ _ hd')
          (mul_le_mul_of_nonneg_left hsumG hep)
    _ = (1 + D.e i) * (D.N0 ε (i - 1) w (T.X (i - 1)) (D.Kr (i - 1)) + 2 ^ D.f * ep * M) := by
        ring

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LocalVolumePositivity
section
namespace Formalism.FourierDecayAlt.P

open Finset Formalism.FourierDecayAlt.S3

namespace LocalVolumePositivity

variable {P : Type} [Fintype P] {B : MassData P}

theorem unit_level_volume_pos (hP : B.Pos) : 0 < B.unitLevelVolume := by
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  unfold MassData.unitLevelVolume
  exact mul_pos xU0 (prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.2.2.2.2.2.2)

theorem pos_μK (hP : B.Pos) : 0 < B.μK := by
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  unfold MassData.μK
  exact mul_pos xKo (prod_pos fun p _ => (hp p).2.2.2.2.2.1)

theorem pos_μKpp (hP : B.Pos) : 0 < B.μKpp := by
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  unfold MassData.μKpp
  exact mul_pos xKo (prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.1)

theorem pos_MM (hP : B.Pos) : 0 < B.MM := by
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  unfold MassData.MM
  exact mul_pos xMo (prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.2.2.2.2.2.1)

theorem pos_μSpp (hP : B.Pos) : 0 < B.μSpp := by
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  unfold MassData.μSpp
  exact mul_pos xSo (prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.2.2.2.1)

theorem pos_μSpp' (hP : B.Pos) : 0 < B.μSpp' := by
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  unfold MassData.μSpp'
  exact mul_pos xSo' (prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.2.2.2.2.1)

theorem gamma_product_pos (hP : B.Pos) : 0 < B.Gam1 := by
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  unfold MassData.Gam1
  exact prod_pos fun p _ => by unfold MassData.ga; exact div_pos (hp p).2.1 (hp p).2.2.1

theorem pos_tt (hP : B.Pos) : 0 < B.tt := by
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  unfold MassData.tt
  exact prod_pos fun p _ => add_pos one_pos (div_pos (by norm_num) (hp p).1)

end LocalVolumePositivity

open LocalVolumePositivity

theorem middle_level_volume_index : KnatGamma := by
  intro P _ B hP hI p
  obtain ⟨qg, qglk, quk, qnn, qgg, qKp, qKn, qKpp, qSp, qSp', qSpp, qSpp', qMp, qU⟩ := hP.1 p
  obtain ⟨h1, h2⟩ := hI p
  rw [div_eq_iff qKp.ne'] at h2
  rw [h2, h1]
  unfold MassData.ga
  field_simp

theorem column_identity : Columns := by
  intro P _ B hP hV hL hM hC
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  obtain ⟨_, hNa1, hNa1'⟩ := hV
  obtain ⟨hLS, hLSpp, hLS', hLSpp'⟩ := hL
  obtain ⟨hρ, hNaN, hρ', hNaN'⟩ := hM
  obtain ⟨hdd, hG1, hdd', hG1'⟩ := hC
  have eN : B.volN = 1 / B.μN := by rw [eq_div_iff xN.ne', ← hNaN, hNa1]
  have eN' : B.volN' = 1 / B.μN' := by rw [eq_div_iff xN'.ne', ← hNaN', hNa1']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hρ, eN, hLS]; field_simp
  · rw [hdd, ← hG1, hρ]; field_simp
  · unfold MassData.c0; rw [hdd, hLSpp, eN]; field_simp
  · rw [hρ', eN', hLS']; field_simp
  · rw [hdd', ← hG1', hρ']; field_simp
  · unfold MassData.c0'; rw [hdd', hLSpp', eN']; field_simp

theorem local_ratio_product : LocalProduct := by
  intro P _ B hP hO hT hI
  have hP0 := hP
  have hG1 := gamma_product_pos hP
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  have hMo : B.Mo = B.μKo ^ 2 / (B.μSo * B.μSo') * B.localVolumeArchimedean := by
    rw [← hO]; field_simp
  have hM : ∏ p, B.Mp p = (∏ p, B.localVolumeAtPlace p) * (∏ p, B.μKp p) * (∏ p, B.μKnatp p) /
      ((∏ p, B.μSp p) * ∏ p, B.μSp' p) := by
    rw [← prod_mul_distrib, ← prod_mul_distrib, ← prod_mul_distrib, ← prod_div_distrib]
    refine prod_congr rfl fun p _ => ?_
    obtain ⟨qg, qglk, quk, qnn, qgg, qKp, qKn, qKpp, qSp, qSp', qSpp, qSpp', qMp, qU⟩ := hp p
    have h := (hT p).1
    rw [div_eq_iff qU.ne'] at h
    rw [h]; field_simp
  have hKn : ∏ p, B.μKnatp p = B.Gam1 * ∏ p, B.μKppp p := by
    unfold MassData.Gam1; rw [← prod_mul_distrib]
    exact prod_congr rfl fun p _ => middle_level_volume_index P B hP0 hI p
  have hSp : ∏ p, B.μSp p = B.Gam1 * ∏ p, B.μSppp p := by
    unfold MassData.Gam1; rw [← prod_mul_distrib]
    exact prod_congr rfl fun p _ => (hT p).2.1
  have hSp' : ∏ p, B.μSp' p = B.Gam1 * ∏ p, B.μSppp' p := by
    unfold MassData.Gam1; rw [← prod_mul_distrib]
    exact prod_congr rfl fun p _ => (hT p).2.2
  have a1 : 0 < ∏ p, B.localVolumeAtPlace p := prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.2.2.2.2.2.2
  have a2 : 0 < ∏ p, B.μKp p := prod_pos fun p _ => (hp p).2.2.2.2.2.1
  have a3 : 0 < ∏ p, B.μKppp p := prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.1
  have a4 : 0 < ∏ p, B.μSppp p := prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.2.2.2.1
  have a5 : 0 < ∏ p, B.μSppp' p := prod_pos fun p _ => (hp p).2.2.2.2.2.2.2.2.2.2.2.1
  unfold MassData.MM MassData.unitLevelVolume MassData.μK MassData.μKpp MassData.μSpp MassData.μSpp' MassData.μKnat MassData.μS MassData.μS'
  rw [hM, hMo, hKn, hSp, hSp']
  constructor <;> field_simp <;> ring

theorem jacobian_natural_measure_constant : JacobianConstant := by
  intro P _ B hP hJ hNu
  have hU := unit_level_volume_pos hP
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  rw [hJ, hNu]
  field_simp

theorem form_signature_bound : SigBound := by
  intro P _ B hP hF hK hMs hD hA hJ hNu hI
  have hP0 := hP
  have hU := unit_level_volume_pos hP
  have hμK := pos_μK hP
  have hMM := pos_MM hP
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  obtain ⟨hKV, hKt⟩ := hK
  have hc0 : 0 < B.c0 := by unfold MassData.c0; exact div_pos (mul_pos xvN xvH) xpi
  have hc0' : 0 < B.c0' := by unfold MassData.c0'; exact div_pos (mul_pos xvN' xvH') xpi'
  have he1 : 0 ≤ B.e1 := xsd.trans hD
  have hAA : 0 < B.AA := by
    unfold MassData.AA; exact div_pos (mul_pos (mul_pos xB xC) (div_pos hMM xZZ)) hμK
  have hJc := jacobian_natural_measure_constant P B hP0 hJ hNu
  have hIntN : B.IntN ≤ B.volZZ / B.unitLevelVolume * B.Coo⁻¹ * (1 / B.deg) := by
    rw [hJc]
    exact mul_le_mul_of_nonneg_left hI (mul_nonneg (div_nonneg xZZ.le hU.le) (inv_nonneg.mpr xC.le))
  have hKt2 : B.KtopV ≤ (1 + B.δ) * B.IntN / (B.c0 * B.c0') := by
    rw [le_div_iff₀ (mul_pos hc0 hc0')]
    calc B.KtopV * (B.c0 * B.c0') = B.Smod := by unfold MassData.Smod; ring
      _ ≤ _ := hA
  have hEA : 0 ≤ B.e1 * B.AA := mul_nonneg he1 hAA.le
  calc B.Sig = B.ρ0 * B.KV := hF
    _ ≤ B.ρ0 * (B.e1 * B.n0c * B.KtopV) := by
        apply mul_le_mul_of_nonneg_left _ xr.le
        calc B.KV ≤ B.supdens * B.n0c * B.KtopV := hKV
          _ ≤ B.e1 * B.n0c * B.KtopV :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hD xn0.le) hKt
    _ = B.e1 * B.AA * B.KtopV := by rw [← hMs]; ring
    _ ≤ B.e1 * B.AA * ((1 + B.δ) * B.IntN / (B.c0 * B.c0')) :=
        mul_le_mul_of_nonneg_left hKt2 hEA
    _ ≤ B.e1 * B.AA * ((1 + B.δ) * (B.volZZ / B.unitLevelVolume * B.Coo⁻¹ * (1 / B.deg)) /
          (B.c0 * B.c0')) := by
        apply mul_le_mul_of_nonneg_left _ hEA
        apply div_le_div_of_nonneg_right _ (mul_pos hc0 hc0').le
        exact mul_le_mul_of_nonneg_left hIntN (by linarith)
    _ = _ := by
        unfold MassData.AA
        have := hc0.ne'; have := hc0'.ne'
        field_simp

theorem mass_formula_constant_one : MainTheorem := by
  intro P _ B hP h2A hF hK hMs hD hA hJ hNu hI hV hL hM hC hO hT hIx
  have hSB := form_signature_bound P B hP hF hK hMs hD hA hJ hNu hI
  obtain ⟨_, cd, cc, _, cd', cc'⟩ := column_identity P B hP hV hL hM hC
  obtain ⟨hLP, _⟩ := local_ratio_product P B hP hO hT hIx
  have htt := pos_tt hP
  have hG1 := gamma_product_pos hP
  have hμK := pos_μK hP
  have hKpp := pos_μKpp hP
  have hSpp := pos_μSpp hP
  have hSpp' := pos_μSpp' hP
  have hU := unit_level_volume_pos hP
  obtain ⟨hp, xKo, xSo, xSo', xMo, xU0, xH, xH', xHpp, xHpp', xN, xN', xZZ, xPP, xal, xG, xHa, xHa', xNa, xNa', xB, xvH, xvH', xvN, xvN', xC, xdeg, xpi, xpi', xr, xr', xd, xd', xn0, xsd, xδ⟩ := hP
  have hGS : B.GS = B.tt * B.Gam1 * B.Sig := by
    unfold MassData.GS; rw [hF, cd]; field_simp
  have key : B.tt * B.Gam1 * ((1 + B.δ) * B.e1 * (B.c0 * B.c0')⁻¹ * B.volB * (B.MM / B.unitLevelVolume) /
      (B.μK * B.deg)) = (1 + B.δ) * B.e1 * B.tt * (B.d * B.d' / B.Dstar) := by
    have e1 : B.MM / B.unitLevelVolume = B.μKpp / (B.Gam1 * B.μSpp * B.μSpp') * B.μK := by
      rw [← hLP]; field_simp
    have e2 : (B.c0)⁻¹ = B.d * B.μSpp / B.volHa := by rw [← cc, one_div]
    have e3 : (B.c0')⁻¹ = B.d' * B.μSpp' / B.volHa' := by rw [← cc', one_div]
    have e4 : B.volB = B.volHa * B.volHa' / B.volG := by rw [eq_div_iff xG.ne']; exact hV.1
    unfold MassData.Dstar
    rw [mul_inv, e1, e2, e3, e4]
    field_simp
  refine ⟨hGS, ?_, ?_⟩
  · rw [hGS, ← key]
    exact mul_le_mul_of_nonneg_left hSB (mul_pos htt hG1).le
  · calc B.Kgs2 ≤ B.tt * B.Gam1 * B.Sig := h2A
      _ ≤ _ := by
        rw [← key]
        exact mul_le_mul_of_nonneg_left hSB (mul_pos htt hG1).le

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PartialMeansOrthogonal
section
open Formalism.FourierDecayAlt.A6

namespace Formalism.FourierDecayAlt.P

namespace A6x1

theorem norm_sq_sum_orth {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {A : Type}
    [Fintype A] (P : A → E) (e₁ : A → ℂ) (he : ∀ ρ, ‖e₁ ρ‖ = 1)
    (h : ∀ ρ ρ', ρ ≠ ρ' → inner ℂ (P ρ) (P ρ') = 0) :
    ‖∑ ρ, e₁ ρ • P ρ‖ ^ 2 = ∑ ρ, ‖P ρ‖ ^ 2 := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), sum_inner, map_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [inner_sum, Finset.sum_eq_single ρ]
  · rw [inner_self_eq_norm_sq (𝕜 := ℂ), norm_smul, he ρ, one_mul]
  · intro ρ' _ hne
    rw [inner_smul_left, inner_smul_right, h ρ ρ' (Ne.symm hne), mul_zero, mul_zero]
  · intro hρ
    exact absurd (Finset.mem_univ ρ) hρ

end A6x1

theorem doubleMeanSplit : Formalism.FourierDecayAlt.A6.MeanSplit := by
  intro E _ _ A B _ _ u e₁ e₂
  rw [Fintype.sum_prod_type, mul_inv, mul_smul]
  congr 1
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [smul_comm, Finset.smul_sum (r := e₁ ρ)]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_smul]

theorem partialMeansOrthogonal : Formalism.FourierDecayAlt.A6.POrth := by
  intro E _ _ A B _ _ u e₂ h ρ ρ' hne
  simp only [inner_smul_left, inner_smul_right, sum_inner, inner_sum]
  simp [h ρ ρ' _ _ hne]

theorem orthogonalMeanNorm : Formalism.FourierDecayAlt.A6.OrthNorm := by
  intro E _ _ A _ P e₁ he h
  rw [norm_smul, mul_pow, A6x1.norm_sq_sum_orth P e₁ he h, norm_inv, Complex.norm_natCast]

theorem averageBoundOfSteps : Formalism.FourierDecayAlt.A6.AvgBoundAssemble := by
  intro hM hP hO E _ _ A B _ _ u T e₁ e₂ hT he h
  rw [hM E A B u e₁ e₂]
  have h1 := hO E A (fun ρ => (Fintype.card B : ℂ)⁻¹ • ∑ b, e₂ b • u (ρ, b)) e₁ he
    (hP E A B u e₂ h)
  have h2 := hT ((Fintype.card A : ℂ)⁻¹ •
    ∑ ρ, e₁ ρ • ((Fintype.card B : ℂ)⁻¹ • ∑ b, e₂ b • u (ρ, b)))
  calc _ ≤ ‖(Fintype.card A : ℂ)⁻¹ •
        ∑ ρ, e₁ ρ • ((Fintype.card B : ℂ)⁻¹ • ∑ b, e₂ b • u (ρ, b))‖ ^ 2 := by
        gcongr
    _ = _ := by rw [h1]; ring

theorem averageBound : Formalism.FourierDecayAlt.A6.AvgBound :=
  averageBoundOfSteps doubleMeanSplit partialMeansOrthogonal orthogonalMeanNorm

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.WordLiftInduction
section
namespace Formalism.FourierDecayAlt.P.WordLiftInduction

open Finset Polynomial Formalism.FourierDecayAlt.F7

section

variable {R M : Type} [Ring R] [Algebra ℂ R] [AddCommGroup M] [Module ℂ M] [Module R M]
  [IsScalarTower ℂ R M]

end

end Formalism.FourierDecayAlt.P.WordLiftInduction

namespace Formalism.FourierDecayAlt.P

open Finset Polynomial Formalism.FourierDecayAlt.F7

end Formalism.FourierDecayAlt.P
end

