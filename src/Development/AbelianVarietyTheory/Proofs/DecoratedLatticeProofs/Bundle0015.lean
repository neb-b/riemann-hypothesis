module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotRedOfMem
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassCurvePointOfLatticeAddOfGeneric
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IteratedDepthOneLevelCharOfOneRowFirstBlockStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iteratedDepthOneLevel_char_of_one_row_first_block : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : Type) [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (P : TypeDatum (k := k) (a := r)) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ) (r₀ : r) (h : (P.iter t μ hμ j).J), (∀ a b, a ≠ Sum.inl r₀ → (h : GL (Ix r t j) k).val a b = (1 : Matrix (Ix r t j) (Ix r t j) k) a b) → (h : GL (Ix r t j) k).val (Sum.inl r₀) (Sum.inl r₀) = 1 → ∃ g : P.J, (g : GL r k).val = (h : GL (Ix r t j) k).val.submatrix Sum.inl Sum.inl ∧ (P.iter t μ hμ j).lam h = P.lam g := by
  have det_eq_one_of_row {k n : Type} [Field k] [Fintype n] [DecidableEq n]
      (M : Matrix n n k) (i : n)
      (h : ∀ a b, a ≠ i → M a b = (1 : Matrix n n k) a b)
      (hii : M i i = 1) : M.det = 1 := by
    have e : M = 1 + replicateCol Unit (Pi.single i (1 : k)) *
        replicateRow Unit (M i - Pi.single i (1 : k)) := by
      ext a b
      by_cases ha : a = i
      · subst ha
        by_cases hb : b = a
        · subst hb
          simp [Matrix.mul_apply, hii]
        · simp [Matrix.mul_apply, hb, Ne.symm hb]
      · simp [Matrix.mul_apply, h a b ha, Pi.single_apply, ha]
    rw [e, det_one_add_replicateCol_mul_replicateRow]
    simp [hii]
  intro k _ _ _ _ r t _ _ _ _ P μ hμ j r₀
  induction j with
  | zero =>
    intro h _ _
    exact ⟨⟨(reGL (ixZero r t)).symm h, h.2⟩, rfl, rfl⟩
  | succ j ih =>
    intro h h1 h2
    let Q := P.iter t μ hμ j
    let h' : Q.stepJ t := ⟨(reGL (ixSucc r t j)).symm h, h.2⟩
    have eh' : (h' : GL (Ix r t j ⊕ t) k).val =
        (h : GL (Ix r t (j + 1)) k).val.submatrix (ixSucc r t j) (ixSucc r t j) := rfl
    let c := Q.corner h'
    have ec : ∀ a b, (c : GL (Ix r t j) k).val a b =
        (h : GL (Ix r t (j + 1)) k).val (ixSucc r t j (.inl a)) (ixSucc r t j (.inl b)) := by
      intro a b
      rw [Q.corner_val]
      rfl
    have hne : ∀ a, a ≠ Sum.inl r₀ → ixSucc r t j (.inl a) ≠ Sum.inl r₀ := by
      intro a ha e
      apply ha
      have : (Sum.inl a : Ix r t j ⊕ t) = Sum.inl (Sum.inl r₀) :=
        (ixSucc r t j).injective (e.trans rfl)
      exact Sum.inl_injective this
    have c1 : ∀ a b, a ≠ Sum.inl r₀ →
        (c : GL (Ix r t j) k).val a b = (1 : Matrix (Ix r t j) (Ix r t j) k) a b := by
      intro a b ha
      rw [ec, h1 _ _ (hne a ha), Matrix.one_apply, Matrix.one_apply]
      simp [(ixSucc r t j).injective.eq_iff]
    have c2 : (c : GL (Ix r t j) k).val (Sum.inl r₀) (Sum.inl r₀) = 1 := by
      rw [ec]
      exact h2
    obtain ⟨g, hg, hl⟩ := ih c c1 c2
    refine ⟨g, ?_, ?_⟩
    · rw [hg]
      ext x y
      exact ec _ _
    · have d1 : Matrix.GeneralLinearGroup.det (c : GL (Ix r t j) k) = 1 := Units.ext (by
        rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
        exact det_eq_one_of_row _ _ c1 c2)
      have d2 : Matrix.GeneralLinearGroup.det (h' : GL (Ix r t j ⊕ t) k) = 1 := Units.ext (by
        rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, eh', det_submatrix_equiv_self]
        exact det_eq_one_of_row _ _ h1 h2)
      have e0 : (P.iter t μ hμ (j + 1)).lam h = (Q.step t (μ (j + 1)) (hμ _)).lam h' := rfl
      rw [e0, Q.step_lam _ _ h' c (Q.corner_val h'), ← hl, d1, d2]
      simp [Q]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormWeierstrassPSubEqOne
section
open Formalism.L2.Th1.F GlobalTheory.Klein
open scoped ComplexConjugate BigOperators

namespace GlobalTheory.Klein.DiffUnit

variable {p : ℕ} [Fact p.Prime]

end GlobalTheory.Klein.DiffUnit

namespace GlobalTheory.Klein
open DiffUnit

open scoped ComplexConjugate BigOperators in
variable {p : ℕ} [Fact p.Prime] in
private lemma padicComplex_norm_add_le_of_norm_le {x y : ℂ_[p]} {a : ℝ} (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ a) :
    ‖x + y‖ ≤ a :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

open scoped ComplexConjugate BigOperators in
variable {p : ℕ} [Fact p.Prime] in
private lemma padicComplex_norm_sub_le_of_norm_le {x y : ℂ_[p]} {a : ℝ} (hx : ‖x‖ ≤ a) (hy : ‖y‖ ≤ a) :
    ‖x - y‖ ≤ a := by
  rw [sub_eq_add_neg]
  exact padicComplex_norm_add_le_of_norm_le hx (by rwa [norm_neg])

open scoped ComplexConjugate BigOperators in
variable {p : ℕ} [Fact p.Prime] in
private lemma padicComplex_norm_mul_le_of_norm_le_one {x y : ℂ_[p]} {a : ℝ} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ a) :
    ‖x * y‖ ≤ a := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans hy

open scoped ComplexConjugate BigOperators in
variable {p : ℕ} [Fact p.Prime] in
private lemma padicComplex_norm_ofNat_le_one (n : ℕ) [n.AtLeastTwo] : ‖(OfNat.ofNat n : ℂ_[p])‖ ≤ 1 := by
  have := IsUltrametricDist.norm_natCast_le_one ℂ_[p] (OfNat.ofNat n)
  rwa [Nat.cast_ofNat] at this

open scoped ComplexConjugate BigOperators in
variable {p : ℕ} [Fact p.Prime] in
private lemma norm_sub_eq_one_of_discriminant_relations (hp2 : ‖(2 : ℂ_[p])‖ = 1)
    {X₁ X₂ S T Y₁ Y₂ b c D : ℂ_[p]} (hX₁ : ‖X₁‖ ≤ 1) (hX₂ : ‖X₂‖ ≤ 1) (hS : ‖S‖ ≤ 1)
    (hT : ‖T‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) (hD : ‖D‖ = 1) (hne : X₁ - X₂ ≠ 0)
    (hA : (Y₁ - Y₂) ^ 2 = (X₁ - X₂) ^ 2 * (4 * (S + X₁ + X₂) + b))
    (hB : (Y₁ + Y₂) ^ 2 = (X₁ - X₂) ^ 2 * (4 * (T + X₁ + X₂) + b))
    (hsym : (X₁ - X₂) ^ 2 * (S + T - 2 * X₂) =
      (6 * X₂ ^ 2 + b * X₂ + c / 2) * (X₁ - X₂) + Y₂ ^ 2)
    (hdisc : 4 * D = Y₂ ^ 2 * (36 * (12 * X₂ + b) * (6 * X₂ ^ 2 + b * X₂ + c / 2)
        - 108 * Y₂ ^ 2 - (12 * X₂ + b) ^ 3) +
      (6 * X₂ ^ 2 + b * X₂ + c / 2) ^ 2 * ((12 * X₂ + b) ^ 2 - 32 * (6 * X₂ ^ 2 + b * X₂ + c / 2))) :
    ‖X₁ - X₂‖ = 1 := by
  have hc2 : ‖c / 2‖ ≤ 1 := by rw [norm_div, hp2, div_one]; exact hc
  set d := X₁ - X₂ with hd
  set H := 6 * X₂ ^ 2 + b * X₂ + c / 2 with hH
  set K := 12 * X₂ + b with hK
  have h1 : ‖d‖ ≤ 1 := padicComplex_norm_sub_le_of_norm_le hX₁ hX₂
  refine le_antisymm h1 (not_lt.1 fun hlt => ?_)
  have hdpos : 0 < ‖d‖ := norm_pos_iff.2 hne
  have hfour : ∀ {W : ℂ_[p]}, ‖W‖ ≤ 1 → ‖4 * (W + X₁ + X₂) + b‖ ≤ 1 := fun hW =>
    padicComplex_norm_add_le_of_norm_le (padicComplex_norm_mul_le_of_norm_le_one (padicComplex_norm_ofNat_le_one 4)
      (padicComplex_norm_add_le_of_norm_le (padicComplex_norm_add_le_of_norm_le hW hX₁) hX₂)) hb
  have hsq : ∀ {Y W : ℂ_[p]}, Y ^ 2 = d ^ 2 * W → ‖W‖ ≤ 1 → ‖Y‖ ≤ ‖d‖ := fun {Y W} hY hW => by
    have : ‖Y‖ ^ 2 ≤ ‖d‖ ^ 2 := by
      rw [← norm_pow, hY, norm_mul, norm_pow]
      exact mul_le_of_le_one_right (by positivity) hW
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this
  have hm := hsq hA (hfour hS)
  have hp := hsq hB (hfour hT)
  have hY₂ : ‖Y₂‖ ≤ ‖d‖ := by
    have h2 : 2 * Y₂ = (Y₁ + Y₂) - (Y₁ - Y₂) := by ring
    have := padicComplex_norm_sub_le_of_norm_le hp hm
    rwa [← h2, norm_mul, hp2, one_mul] at this
  have hX₂' : ‖2 * X₂‖ ≤ 1 := padicComplex_norm_mul_le_of_norm_le_one (padicComplex_norm_ofNat_le_one 2) hX₂
  have hHd : ‖H‖ ≤ ‖d‖ := by
    have heq : H * d = d ^ 2 * (S + T - 2 * X₂) - Y₂ ^ 2 := by linear_combination -hsym
    have hST : ‖S + T - 2 * X₂‖ ≤ 1 := padicComplex_norm_sub_le_of_norm_le (padicComplex_norm_add_le_of_norm_le hS hT) hX₂'
    have : ‖H‖ * ‖d‖ ≤ ‖d‖ * ‖d‖ := by
      rw [← norm_mul, heq]
      refine padicComplex_norm_sub_le_of_norm_le ?_ ?_
      · rw [norm_mul, norm_pow]
        nlinarith [norm_nonneg (S + T - 2 * X₂), sq_nonneg ‖d‖]
      · rw [norm_pow]
        nlinarith [norm_nonneg Y₂]
    exact le_of_mul_le_mul_right this hdpos
  have hK1 : ‖K‖ ≤ 1 :=
    padicComplex_norm_add_le_of_norm_le (padicComplex_norm_mul_le_of_norm_le_one (padicComplex_norm_ofNat_le_one 12) hX₂) hb
  have hH1 : ‖H‖ ≤ 1 := hHd.trans h1
  have hα : ‖Y₂ ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg Y₂]
  have hH2 : ‖H ^ 2‖ < 1 := by
    rw [norm_pow]; nlinarith [norm_nonneg H]
  have hP : ‖36 * K * H - 108 * Y₂ ^ 2 - K ^ 3‖ ≤ 1 :=
    padicComplex_norm_sub_le_of_norm_le (padicComplex_norm_sub_le_of_norm_le
      (padicComplex_norm_mul_le_of_norm_le_one (padicComplex_norm_mul_le_of_norm_le_one (padicComplex_norm_ofNat_le_one 36) hK1) hH1)
      (padicComplex_norm_mul_le_of_norm_le_one (padicComplex_norm_ofNat_le_one 108) hα.le))
      (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hK1)
  have hQ : ‖K ^ 2 - 32 * H‖ ≤ 1 :=
    padicComplex_norm_sub_le_of_norm_le (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hK1)
      (padicComplex_norm_mul_le_of_norm_le_one (padicComplex_norm_ofNat_le_one 32) hH1)
  have hlt4 : ‖4 * D‖ < 1 := by
    rw [hdisc]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) hP).trans_lt hα
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) hQ).trans_lt hH2
  have h4 : ‖4 * D‖ = 1 := by
    rw [norm_mul, hD, show (4 : ℂ_[p]) = 2 * 2 by norm_num, norm_mul, hp2]
    norm_num
  linarith

open scoped ComplexConjugate BigOperators in
variable {p : ℕ} [Fact p.Prime] in
private lemma padicComplex_norm_two_eq_one_of_ne_two (h : p ≠ 2) : ‖(2 : ℂ_[p])‖ = 1 := by
  have h1 : ‖algebraMap ℚ_[p] ℂ_[p] 2‖ = ‖(2 : ℚ_[p])‖ := norm_algebraMap' _ _
  rw [map_ofNat] at h1
  rw [h1]
  have h2 : ‖(2 : ℚ_[p])‖ = ‖((2 : ℤ) : ℤ_[p])‖ := by
    rw [PadicInt.norm_def, PadicInt.coe_intCast]; norm_num
  rw [h2]
  refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => h ?_)
  rw [PadicInt.norm_int_lt_one_iff_dvd] at hlt
  have : p ∣ 2 := by exact_mod_cast hlt
  exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this


open scoped ComplexConjugate BigOperators in
variable {p : ℕ} [Fact p.Prime] in
theorem _root_.GlobalTheory.Klein.norm_weierstrassP_sub_eq_one (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p])
    (L : PeriodPair) (r : ℂ)
    (hG : _root_.GlobalTheory.Klein.Good ι L r) (u v : ℂ) (hu : _root_.GlobalTheory.Klein.Red ι L r u)
    (hv : _root_.GlobalTheory.Klein.Red ι L r v)
    (h₁ : _root_.GlobalTheory.Klein.Red ι L r (u + v))
    (h₂ : _root_.GlobalTheory.Klein.Red ι L r (u - v)) :
    ‖ι (L.weierstrassP u - L.weierstrassP v)‖ = 1 := by
  obtain ⟨hp, h12r, hc, -, hΔ⟩ := hG
  obtain ⟨hu, hXu⟩ := hu
  obtain ⟨hv, hXv⟩ := hv
  obtain ⟨hs, hS⟩ := h₁
  obtain ⟨ht, hT⟩ := h₂
  have hne : L.weierstrassP u ≠ L.weierstrassP v := by
    rw [Ne, _root_.GlobalTheory.weierstrassP_eq_iff L hu hv]
    rintro (h | h)
    exacts [ht h, hs h]
  have hd : L.weierstrassP u - L.weierstrassP v ≠ 0 := sub_ne_zero.2 hne
  have hA := (_root_.GlobalTheory.weierstrassP_add L hu hv hne).1
  have hnv : -v ∉ L.lattice := fun h => hv (by simpa using neg_mem h)
  have hne' : L.weierstrassP u ≠ L.weierstrassP (-v) := by rwa [PeriodPair.weierstrassP_neg]
  have hB := (_root_.GlobalTheory.weierstrassP_add L hu hnv hne').1
  rw [PeriodPair.weierstrassP_neg, PeriodPair.derivWeierstrassP_neg, ← sub_eq_add_neg,
    sub_neg_eq_add] at hB
  have hsym := _root_.GlobalTheory.weierstrassP_add_add_sub L hu hv hne
  have hY := L.derivWeierstrassP_sq v hv
  set x₁ := L.weierstrassP u
  set x₂ := L.weierstrassP v
  set s := L.weierstrassP (u + v)
  set t := L.weierstrassP (u - v)
  set y₁ := L.derivWeierstrassP u
  set y₂ := L.derivWeierstrassP v
  have cA : (y₁ - y₂) ^ 2 = ((x₁ - r) - (x₂ - r)) ^ 2 *
      (4 * ((s - r) + (x₁ - r) + (x₂ - r)) + 12 * r) := by
    rw [hA]; field_simp; ring
  have cB : (y₁ + y₂) ^ 2 = ((x₁ - r) - (x₂ - r)) ^ 2 *
      (4 * ((t - r) + (x₁ - r) + (x₂ - r)) + 12 * r) := by
    rw [hB]; field_simp; ring
  have cS : ((x₁ - r) - (x₂ - r)) ^ 2 * ((s - r) + (t - r) - 2 * (x₂ - r)) =
      (6 * (x₂ - r) ^ 2 + 12 * r * (x₂ - r) + (12 * r ^ 2 - L.g₂) / 2) * ((x₁ - r) - (x₂ - r)) +
        y₂ ^ 2 := by
    have e : s = (6 * x₂ ^ 2 - L.g₂ / 2) / (x₁ - x₂) + y₂ ^ 2 / (x₁ - x₂) ^ 2 - t + 2 * x₂ := by
      linear_combination hsym
    rw [e]; field_simp; ring
  have cD : 4 * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) =
      y₂ ^ 2 * (36 * (12 * (x₂ - r) + 12 * r) *
          (6 * (x₂ - r) ^ 2 + 12 * r * (x₂ - r) + (12 * r ^ 2 - L.g₂) / 2)
        - 108 * y₂ ^ 2 - (12 * (x₂ - r) + 12 * r) ^ 3) +
      (6 * (x₂ - r) ^ 2 + 12 * r * (x₂ - r) + (12 * r ^ 2 - L.g₂) / 2) ^ 2 *
        ((12 * (x₂ - r) + 12 * r) ^ 2 -
          32 * (6 * (x₂ - r) ^ 2 + 12 * r * (x₂ - r) + (12 * r ^ 2 - L.g₂) / 2)) := by
    rw [hY]; ring
  have key := norm_sub_eq_one_of_discriminant_relations (padicComplex_norm_two_eq_one_of_ne_two hp) hXu hXv hS hT h12r hc
    hΔ (Y₁ := ι y₁) (Y₂ := ι y₂)
    (by rw [← map_sub]; exact (map_ne_zero ι).2 (by rwa [sub_sub_sub_cancel_right]))
    (by simpa only [map_sub, map_mul, map_add (f := _), map_pow, map_ofNat, map_div₀] using congrArg ι cA)
    (by simpa only [map_sub, map_mul, map_add (f := _), map_pow, map_ofNat, map_div₀] using congrArg ι cB)
    (by simpa only [map_sub, map_mul, map_add (f := _), map_pow, map_ofNat, map_div₀] using congrArg ι cS)
    (by simpa only [map_sub, map_mul, map_add (f := _), map_pow, map_ofNat, map_div₀] using congrArg ι cD)
  rwa [← map_sub, sub_sub_sub_cancel_right] at key

end GlobalTheory.Klein
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricChainLastTwoStepsRootOfUnityStatement
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoricChain_last_two_steps_root_of_unity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s : ℕ) (κ t : Type) [Fintype κ] [DecidableEq κ] [Fintype t] [DecidableEq t] (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ), (∀ j, IsUnram (η j)) → ∀ g : GL (XIx κ t (s + 1) ⊕ Fin 0) k, g ∈ ((twistChain s t κ δ hδ η).lev (s + 1) 0 rfl).J → ∃ c : ℂ, (∃ n : ℕ, 0 < n ∧ c ^ n = 1) ∧ (∀ h x₀ y, (twistChain s t κ δ hδ η).Psi h (g.val.toBlocks₁₁ * x₀) (g.val.toBlocks₁₁ *ᵥ y) = c * (twistChain s t κ δ hδ η).Psi h x₀ y) ∧ ∀ (ψ : AddChar k Circle) (ε : k) (w : kˣ) (y : XIx κ t (s + 1) → k) x, (twistChain s t κ δ hδ η).xiTop (box _ w) ψ ν ε (Submodule.Quotient.mk y) (x * g.val.toBlocks₁₁) = c * (twistChain s t κ δ hδ η).xiTop (box _ w) ψ ν ε (Submodule.Quotient.mk (g.val.toBlocks₁₁ *ᵥ y)) x := by
  exact @GlobalTheory.LevelLaw.last_steps_law
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReductionSetSubgroup
section
open Formalism.L2.Th1.F GlobalTheory.Klein
open scoped ComplexConjugate BigOperators

namespace GlobalTheory.Klein

private theorem ultra_add_le {K : Type*} [NormedField K] [IsUltrametricDist K] {x y : K} {C : ℝ}
    (hx : ‖x‖ ≤ C) (hy : ‖y‖ ≤ C) : ‖x + y‖ ≤ C :=
  (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)

private theorem mul_le_of {K : Type*} [NormedField K] {x y : K} {C D : ℝ}
    (hx : ‖x‖ ≤ C) (hy : ‖y‖ ≤ D) : ‖x * y‖ ≤ C * D := by
  rw [norm_mul]
  exact mul_le_mul hx hy (norm_nonneg _) ((norm_nonneg _).trans hx)

private theorem cubic_le {K : Type*} [NormedField K] [IsUltrametricDist K] {x k₂ k₁ k₀ : K} {ρ : ℝ}
    (h2 : ‖(2 : K)‖ = 1) (hρ : 1 ≤ ρ) (hx : ‖x‖ ≤ ρ) (hk₂ : ‖k₂‖ ≤ 1) (hk₁ : ‖k₁‖ ≤ 1) (hk₀ : ‖k₀‖ ≤ 1) :
    ‖2 * 2 * (x * x * x) + k₂ * (x * x) + k₁ * x + k₀‖ ≤ ρ * ρ * ρ := by
  have h1 : 1 ≤ ρ * ρ := by nlinarith
  refine ultra_add_le (ultra_add_le (ultra_add_le ?_ ?_) ?_) ?_
  · simpa using mul_le_of (mul_le_of h2.le h2.le) (mul_le_of (mul_le_of hx hx) hx)
  · exact (mul_le_of hk₂ (mul_le_of hx hx)).trans (by nlinarith)
  · exact (mul_le_of hk₁ hx).trans (by nlinarith)
  · exact hk₀.trans (by nlinarith)

private theorem le_of_mul_self_le_mul_self' {x y : ℝ} (h : x * x ≤ y * y) (hy : 0 ≤ y) : x ≤ y :=
  (abs_le_of_sq_le_sq' (by simpa only [sq] using h) hy).2

theorem chord_norm_le_one {K : Type*} [NormedField K] [IsUltrametricDist K] {a b A B X k₂ k₁ k₀ : K}
    (h2 : ‖(2 : K)‖ = 1) (ha : 1 < ‖a‖) (hb : ‖b‖ ≤ 1) (hk₂ : ‖k₂‖ ≤ 1) (hk₁ : ‖k₁‖ ≤ 1) (hk₀ : ‖k₀‖ ≤ 1)
    (hA : A ^ 2 = 4 * a ^ 3 + k₂ * a ^ 2 + k₁ * a + k₀)
    (hB : B ^ 2 = 4 * b ^ 3 + k₂ * b ^ 2 + k₁ * b + k₀)
    (hX : 4 * (a - b) ^ 2 * X = (A - B) ^ 2 - (4 * (a + b) + k₂) * (a - b) ^ 2) : ‖X‖ ≤ 1 := by
  set ρ := ‖a‖ with hρ
  have haa : ‖a‖ ≤ ρ := le_rfl
  have hab : ‖a - b‖ = ρ := by
    rw [sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg]; linarith),
      norm_neg, max_eq_left (by linarith)]
  have hA' : ‖A‖ * ‖A‖ ≤ ρ * ρ * ρ := by
    rw [← norm_mul, show A * A = 2 * 2 * (a * a * a) + k₂ * (a * a) + k₁ * a + k₀ by
      linear_combination hA]
    exact cubic_le h2 ha.le haa hk₂ hk₁ hk₀
  have hB' : ‖B‖ * ‖B‖ ≤ 1 * 1 * 1 := by
    rw [← norm_mul, show B * B = 2 * 2 * (b * b * b) + k₂ * (b * b) + k₁ * b + k₀ by
      linear_combination hB]
    exact cubic_le h2 le_rfl hb hk₂ hk₁ hk₀
  have h1 : 1 ≤ ρ * ρ := by nlinarith
  have hρρ : ρ ≤ ρ * ρ := by nlinarith
  have hA1 : ‖A‖ ≤ ρ * ρ := by
    exact le_of_mul_self_le_mul_self' (hA'.trans (by nlinarith)) (by linarith)
  have hB1 : ‖B‖ ≤ 1 := by
    exact le_of_mul_self_le_mul_self' (hB'.trans (by norm_num)) (by linarith)
  have hN : 2 * 2 * ((a - b) * (a - b)) * X =
      2 * 2 * b * (a * (a + b)) + 2 * k₂ * b * a + k₁ * (a + b) + 2 * k₀ + 2 * B * (-A) := by
    linear_combination hX + hA + hB
  have hs : ‖a + b‖ ≤ ρ := ultra_add_le haa (by linarith)
  have hn : ‖2 * 2 * b * (a * (a + b)) + 2 * k₂ * b * a + k₁ * (a + b) + 2 * k₀ + 2 * B * (-A)‖
      ≤ ρ * ρ := by
    refine ultra_add_le (ultra_add_le (ultra_add_le (ultra_add_le ?_ ?_) ?_) ?_) ?_
    · simpa using mul_le_of (mul_le_of (mul_le_of h2.le h2.le) hb) (mul_le_of haa hs)
    · exact (mul_le_of (mul_le_of (mul_le_of h2.le hk₂) hb) haa).trans (by linarith)
    · exact (mul_le_of hk₁ hs).trans (by linarith)
    · exact (mul_le_of h2.le hk₀).trans (by linarith)
    · exact (mul_le_of (mul_le_of h2.le hB1) ((norm_neg A).le.trans hA1)).trans (by linarith)
  rw [← hN, norm_mul, norm_mul, norm_mul, norm_mul, h2, hab] at hn
  by_contra hc
  push_neg at hc
  nlinarith

theorem norm_two_of_ne {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) : ‖(2 : ℂ_[p])‖ = 1 := by
  have h : ‖((2 : ℕ) : ℚ_[p])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]
    exact (Nat.coprime_primes Fact.out Nat.prime_two).2 hp
  have e : (2 : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] ((2 : ℕ) : ℚ_[p]) := by
    rw [map_natCast]; norm_num
  rw [e, norm_algebraMap', h]

variable {p : ℕ} [Fact p.Prime]

theorem Red.neg {ι : ℂ ≃+* ℂ_[p]} {L : PeriodPair} {r z : ℂ} (h : Red ι L r z) : Red ι L r (-z) :=
  ⟨fun h' => h.1 (by simpa using h'), by rw [L.weierstrassP_neg]; exact h.2⟩

theorem Red.add_lattice {ι : ℂ ≃+* ℂ_[p]} {L : PeriodPair} {r z ω : ℂ} (h : Red ι L r z)
    (hω : ω ∈ L.lattice) : Red ι L r (z + ω) :=
  ⟨fun h' => h.1 ((L.lattice.add_mem_iff_left hω).1 h'), by
    have e : L.weierstrassP (z + ω) = L.weierstrassP z := L.weierstrassP_add_coe z ⟨ω, hω⟩
    rw [e]; exact h.2⟩

theorem Red.add_of_not {ι : ℂ ≃+* ℂ_[p]} {L : PeriodPair} {r u w : ℂ} (hg : Good ι L r)
    (hu : ¬ Red ι L r u) (hw : Red ι L r w) : Red ι L r (u + w) := by
  by_cases hL : u ∈ L.lattice
  · rw [add_comm]; exact hw.add_lattice hL
  have ha : 1 < ‖ι (L.weierstrassP u - r)‖ := not_le.1 fun h => hu ⟨hL, h⟩
  have hne : L.weierstrassP u ≠ L.weierstrassP w := fun h => by
    rw [h] at ha; exact absurd hw.2 (not_le.2 ha)
  refine ⟨fun h => hu ?_, ?_⟩
  · have := hw.neg.add_lattice h
    rwa [show -w + (u + w) = u by ring] at this
  obtain ⟨hp, hk₂, hk₁, hk₀, -⟩ := hg
  have hs := (GlobalTheory.weierstrassP_add L hL hw.1 hne).1
  have e1 := L.derivWeierstrassP_sq u hL
  have e2 := L.derivWeierstrassP_sq w hw.1
  have hd := sub_ne_zero.2 hne
  have key : ∀ x y : ℂ, y ^ 2 = 4 * x ^ 3 - L.g₂ * x - L.g₃ →
      ι y ^ 2 = 4 * ι (x - r) ^ 3 + ι (12 * r) * ι (x - r) ^ 2 + ι (12 * r ^ 2 - L.g₂) * ι (x - r)
        + ι (4 * r ^ 3 - L.g₂ * r - L.g₃) := fun x y h => by
    have : y ^ 2 = 4 * (x - r) ^ 3 + (12 * r) * (x - r) ^ 2 + (12 * r ^ 2 - L.g₂) * (x - r)
        + (4 * r ^ 3 - L.g₂ * r - L.g₃) := by linear_combination h
    rw [← map_pow, this, map_add (f := _), map_add (f := _), map_add (f := _), map_mul ι 4, map_mul ι (12 * r),
      map_mul ι _ (x - r), map_pow, map_pow, map_ofNat]
  refine chord_norm_le_one (norm_two_of_ne hp) ha hw.2 hk₂ hk₁ hk₀ (key _ _ e1) (key _ _ e2) ?_
  have : 4 * ((L.weierstrassP u - r) - (L.weierstrassP w - r)) ^ 2 * (L.weierstrassP (u + w) - r)
      = (L.derivWeierstrassP u - L.derivWeierstrassP w) ^ 2
        - (4 * ((L.weierstrassP u - r) + (L.weierstrassP w - r)) + 12 * r)
          * ((L.weierstrassP u - r) - (L.weierstrassP w - r)) ^ 2 := by
    rw [hs]; field_simp; ring
  have := congrArg ι this
  simpa only [map_mul, map_sub, map_add (f := _), map_pow, map_ofNat] using this

theorem not_red_addSubgroup : ∀ (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (r : ℂ), Good ι L r → (∀ z, Red ι L r z → Red ι L r (-z)) ∧ (∀ z, Red ι L r z → ∀ ω ∈ L.lattice, Red ι L r (z + ω)) ∧ (∀ u w, ¬ Red ι L r u → Red ι L r w → Red ι L r (u + w)) ∧ ∃ G : AddSubgroup ℂ, (∀ z, z ∈ G ↔ ¬ Red ι L r z) ∧ ∀ ω ∈ L.lattice, ω ∈ G := by
  intro p _ ι L r hg
  refine ⟨fun z h => h.neg, fun z h ω hω => h.add_lattice hω, fun u w hu hw => Red.add_of_not hg hu hw, ?_⟩
  have hneg : ∀ {z : ℂ}, ¬ Red ι L r z → ¬ Red ι L r (-z) := fun hz h => hz (by simpa using h.neg)
  refine ⟨{ carrier := {z | ¬ Red ι L r z}
            add_mem' := fun {u v} hu hv h => hu ?_
            zero_mem' := not_red_of_mem ι L r L.lattice.zero_mem
            neg_mem' := hneg }, fun z => Iff.rfl, fun ω hω => not_red_of_mem ι L r hω⟩
  have := Red.add_of_not hg (hneg hv) h
  rwa [show -v + (u + v) = u by ring] at this

end GlobalTheory.Klein
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricPositionLevelCharacterEqOneSingleRow
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

noncomputable section
namespace GlobalTheory

theorem lam_purerow : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (ϖ : kˣ) (ρ κ l : ℕ) (P : TypeDatum k (Fin κ ⊕ Fin l)), GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsSymLevel ψ ϖ ρ P → ∀ (i₀ : Fin l) (g : P.J), (∀ a b, a ≠ Sum.inr i₀ → (g : GL (Fin κ ⊕ Fin l) k).val a b = (1 : Matrix (Fin κ ⊕ Fin l) (Fin κ ⊕ Fin l) k) a b) → (∀ i : Fin l, i.val = i₀.val + 1 → (g : GL (Fin κ ⊕ Fin l) k).val (Sum.inr i₀) (Sum.inr i) = 0) → P.lam g = 1 := by
  intro k _ _ _ _ ψ ϖ ρ κ l P hP i₀ g h1 h2
  have hs : simpleSum (g : GL (Fin κ ⊕ Fin l) k) = 0 := by
    unfold simpleSum
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hij
    · by_cases hi : i = i₀
      · subst hi; exact h2 j hij
      · have hne : i ≠ j := by
          intro e; subst e; omega
        rw [h1 _ _ (by simpa using hi)]
        simp [hne]
    · rfl
  have hu : superSum Fin.val (g : GL (Fin κ ⊕ Fin l) k).val.toBlocks₁₁ = 0 := by
    unfold superSum
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    split_ifs with hab
    · have hne : a ≠ b := by
        intro e; subst e; omega
      rw [Matrix.toBlocks₁₁]
      simp only [Matrix.of_apply]
      rw [h1 _ _ (by simp)]
      simp [hne]
    · rfl
  apply Units.ext
  rw [hP.2 g, hs, hu]
  simp

end GlobalTheory
end
end

