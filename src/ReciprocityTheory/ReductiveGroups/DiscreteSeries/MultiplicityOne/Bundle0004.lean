module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0001
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDichoA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.Bundle0002
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSchurGA

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDicho
section
noncomputable section

open MeasureTheory ComplexConjugate
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open ConjugateHilbertSpace

theorem schurDichotomy : SchurDichotomy := by
  intro G _ _ _ _ _ μ _ _ _ H _ _ _ _ θ ρ hθc hθm hθθ hmap hρ1 hρm hiso hcont hsq hirr
  classical
  have hθ1 : θ 1 = 1 := by
    have h := hθm 1 1
    rw [one_mul] at h
    exact mul_left_cancel (a := θ 1) (by rw [mul_one]; exact h.symm)
  have hθinv : ∀ a, θ a⁻¹ = (θ a)⁻¹ := by
    intro a
    apply eq_inv_of_mul_eq_one_left
    rw [← hθm, mul_inv_cancel, hθ1]
  have hθmp : MeasurePreserving θ μ μ := ⟨hθc.measurable, hmap⟩
  have hR : Formalism.MainNotions.BridgeCSchur.SqRep μ ρ := ⟨hρ1, hρm, hiso, hcont, hsq⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : G → (Cj H →L[ℂ] Cj H),
      ∀ g v, τ g v = toCj (ρ (θ g)⁻¹ (ofCj v)) :=
    ⟨fun g => opCj (ρ (θ g)⁻¹), fun g v => opCj_apply _ _⟩
  have hcoef : ∀ g (v w : Cj H), ⟪w, τ g v⟫_ℂ = ⟪ofCj v, ρ (θ g) (ofCj w)⟫_ℂ := by
    intro g v w
    rw [inner_def, hτ]
    have h := hR.inner_left (θ g)⁻¹ (ofCj v) (ofCj w)
    rw [inv_inv] at h
    exact h
  have hT : Formalism.MainNotions.BridgeCSchur.SqRep μ τ := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · ext v
      simp only [hτ, hθ1, inv_one, hρ1]
      rfl
    · intro a b
      ext v
      simp only [ContinuousLinearMap.comp_apply, hτ]
      rw [hθm, mul_inv_rev, hρm]
      rfl
    · intro g v
      rw [hτ]
      exact hiso _ _
    · intro v
      have e : (fun g => τ g v) = fun g => toCj (ρ (θ g)⁻¹ (ofCj v)) := funext fun g => hτ g v
      rw [e]
      exact (hcont (ofCj v)).comp hθc.inv
    · intro v w
      have e : (fun g => ⟪w, τ g v⟫_ℂ) = fun g => ⟪ofCj v, ρ (θ g) (ofCj w)⟫_ℂ :=
        funext fun g => hcoef g v w
      rw [e]
      exact (hsq (ofCj w) (ofCj v)).comp_measurePreserving hθmp
  have hirrT : ∀ S : Submodule ℂ (Cj H), IsClosed (S : Set (Cj H)) →
      (∀ g, ∀ v ∈ S, τ g v ∈ S) → S = ⊥ ∨ S = ⊤ := by
    intro S hS hSi
    let S' : Submodule ℂ H :=
      { carrier := {x | toCj x ∈ S}
        add_mem' := fun ha hb => S.add_mem ha hb
        zero_mem' := S.zero_mem
        smul_mem' := fun c x hx => by
          have h2 := S.smul_mem (conj c) (show toCj x ∈ S from hx)
          rw [smul_def, Complex.conj_conj] at h2
          show toCj (c • x) ∈ S
          exact h2 }
    have hS'c : IsClosed (S' : Set H) := hS.preimage (eCj (H := H)).symm.continuous
    have hS'i : ∀ h, ∀ x ∈ S', ρ h x ∈ S' := by
      intro h x hx
      have h2 := hSi (θ h⁻¹) (toCj x) hx
      rw [hτ, hθθ, inv_inv] at h2
      exact h2
    rcases hirr S' hS'c hS'i with h | h
    · left
      rw [eq_bot_iff]
      intro v hv
      have h3 : ofCj v ∈ S' := hv
      rw [h, Submodule.mem_bot] at h3
      exact h3
    · right
      rw [eq_top_iff]
      intro v _
      have h3 : ofCj v ∈ S' := by rw [h]; trivial
      exact h3
  by_cases hne : ∃ U : Cj H ≃ₗᵢ[ℂ] H, ∀ g v, U (τ g v) = ρ g (U v)
  · right
    obtain ⟨U, hU⟩ := hne
    refine ⟨((eCj (H := H)).symm.trans U : H ≃ₗᵢ⋆[ℂ] H), ?_, ?_⟩
    · intro g x y
      calc ⟪y, ρ (θ g) x⟫_ℂ = ⟪toCj x, τ g (toCj y)⟫_ℂ := (hcoef g (toCj y) (toCj x)).symm
        _ = ⟪U (toCj x), U (τ g (toCj y))⟫_ℂ := (U.inner_map_map _ _).symm
        _ = ⟪U (toCj x), ρ g (U (toCj y))⟫_ℂ := by rw [hU]
    · intro h v
      have h2 := hU (θ h)⁻¹ (toCj v)
      rw [hτ, hθinv, hθθ, inv_inv] at h2
      exact h2
  · left
    intro x y x' y'
    have h0 := Formalism.MainNotions.BridgeCSchur.schur_orth_ineq hT hR hirrT hirr hne (toCj y) (toCj x) x' y'
    have e : (fun g => ⟪y, ρ (θ g) x⟫_ℂ * star ⟪y', ρ g x'⟫_ℂ) =
        fun g => ⟪toCj x, τ g (toCj y)⟫_ℂ * star ⟪y', ρ g x'⟫_ℂ :=
      funext fun g => congrArg (· * star ⟪y', ρ g x'⟫_ℂ) (hcoef g (toCj y) (toCj x)).symm
    exact (congrArg (fun f => ∫ g, f g ∂μ) e).trans h0

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JFrameA
section
noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def frameMat (k : ℕ) (u : Fin (k + 1) → ℂ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := fun i j =>
  if i = Fin.last k then
    (if j = Fin.last k then u (Fin.last k)
      else u (Fin.last k) * (((‖u (Fin.last k)‖)⁻¹ : ℝ) : ℂ) * star (u j))
  else if j = Fin.last k then u i
  else (if i = j then 1 else 0) + u i * star (u j) * (((1 + ‖u (Fin.last k)‖)⁻¹ : ℝ) : ℂ)

theorem frameMat_col (k : ℕ) (u : Fin (k + 1) → ℂ) (i : Fin (k + 1)) :
    frameMat k u i (Fin.last k) = u i := by
  by_cases h : i = Fin.last k
  · subst h; simp [frameMat]
  · simp [frameMat, h]

theorem frameMat_star_mul_self (t : ℂ) : star t * t = ((‖t‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_mul']
  push_cast
  ring

section
variable (k : ℕ) (u : Fin (k + 1) → ℂ)

theorem frameMat_cc (x i : Fin k) : frameMat k u x.castSucc i.castSucc =
    (if x = i then 1 else 0) + u x.castSucc * star (u i.castSucc) * (((1 + ‖u (Fin.last k)‖)⁻¹ : ℝ) : ℂ) := by
  simp [frameMat, (Fin.castSucc_lt_last x).ne, (Fin.castSucc_lt_last i).ne, Fin.castSucc_inj]

theorem frameMat_lc (i : Fin k) : frameMat k u (Fin.last k) i.castSucc =
    u (Fin.last k) * (((‖u (Fin.last k)‖)⁻¹ : ℝ) : ℂ) * star (u i.castSucc) := by
  simp [frameMat, (Fin.castSucc_lt_last i).ne]

theorem frameMat_cl (x : Fin k) : frameMat k u x.castSucc (Fin.last k) = u x.castSucc := by
  simp [frameMat, (Fin.castSucc_lt_last x).ne]

theorem frameMat_ll : frameMat k u (Fin.last k) (Fin.last k) = u (Fin.last k) := by
  simp [frameMat]

end

theorem frameMat_star_ofReal (x : ℝ) : star ((x : ℝ) : ℂ) = (x : ℂ) := by
  rw [Complex.star_def, Complex.conj_ofReal]

theorem frameMat_unitary (k : ℕ) (u : Fin (k + 1) → ℂ)
    (hu : ∑ l : Fin k, star (u l.castSucc) * u l.castSucc = star (u (Fin.last k)) * u (Fin.last k) - 1) :
    (frameMat k u)ᴴ * Hb k * frameMat k u = Hb k := by
  set t := u (Fin.last k) with ht
  set n : ℝ := ‖t‖ with hn
  set c : ℝ := (1 + n)⁻¹ with hc
  set m : ℝ := n⁻¹ with hm
  have ht2 : star t * t = (n : ℂ) ^ 2 := by rw [frameMat_star_mul_self]; push_cast; rfl
  have hreal : (∑ l : Fin k, ‖u l.castSucc‖ ^ 2 : ℝ) = n ^ 2 - 1 := by
    have h1 := hu
    simp only [frameMat_star_mul_self] at h1
    exact_mod_cast h1
  have hn1 : 1 ≤ n ^ 2 := by
    have : 0 ≤ (∑ l : Fin k, ‖u l.castSucc‖ ^ 2 : ℝ) := Finset.sum_nonneg (fun _ _ => by positivity)
    linarith
  have hnpos : 0 < n := by
    have : 0 ≤ n := norm_nonneg _
    rcases this.eq_or_lt with h | h
    · rw [← h] at hn1; norm_num at hn1
    · exact h
  have key : (2 : ℂ) * (c : ℂ) + ((n : ℂ) ^ 2 - 1) * (c : ℂ) ^ 2 - (n : ℂ) ^ 2 * (m : ℂ) ^ 2 = 0 := by
    have : (2 * c + (n ^ 2 - 1) * c ^ 2 - n ^ 2 * m ^ 2 : ℝ) = 0 := by
      rw [hc, hm]; field_simp; ring
    exact_mod_cast this
  have key2 : (1 : ℂ) + ((n : ℂ) ^ 2 - 1) * (c : ℂ) - (n : ℂ) ^ 2 * (m : ℂ) = 0 := by
    have : (1 + (n ^ 2 - 1) * c - n ^ 2 * m : ℝ) = 0 := by
      rw [hc, hm]; field_simp; ring
    exact_mod_cast this
  have hne : ∀ x : Fin k, (Fin.last k = x.castSucc) = False :=
    fun x => eq_false (fun h => Fin.castSucc_ne_last x h.symm)
  have hne' : ∀ x : Fin k, (x.castSucc = Fin.last k) = False :=
    fun x => eq_false (Fin.castSucc_ne_last x)
  ext i j
  rw [Matrix.mul_apply]
  simp only [Hb, Matrix.mul_diagonal, Matrix.conjTranspose_apply, Fin.sum_univ_castSucc]
  cases i using Fin.lastCases with
  | last =>
    cases j using Fin.lastCases with
    | last =>
      simp only [frameMat_ll, frameMat_cl, Matrix.diagonal_apply, hne', if_true, if_false, mul_one]
      rw [hu]; ring
    | cast j =>
      simp only [frameMat_ll, frameMat_cl, frameMat_lc, frameMat_cc, Matrix.diagonal_apply, hne, hne', if_true, if_false, mul_one,
        ← ht, ← hn, ← hc, ← hm]
      have hpt : ∀ x : Fin k, star (u x.castSucc) * ((if x = j then (1 : ℂ) else 0) +
          u x.castSucc * star (u j.castSucc) * (c : ℂ)) =
          (if x = j then star (u j.castSucc) else 0) + star (u x.castSucc) * u x.castSucc *
            (star (u j.castSucc) * (c : ℂ)) := by
        intro x; split_ifs with h <;> [subst h; skip] <;> ring
      rw [Finset.sum_congr rfl (fun x _ => hpt x)]
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.sum_mul, hu,
        star_mul, frameMat_star_ofReal, star_star]
      linear_combination (star (u j.castSucc)) * key2 +
        (star (u j.castSucc) * (c : ℂ) - star (u j.castSucc) * (m : ℂ)) * ht2
  | cast i =>
    cases j using Fin.lastCases with
    | last =>
      simp only [frameMat_ll, frameMat_cl, frameMat_lc, frameMat_cc, Matrix.diagonal_apply, hne, hne', if_true, if_false, mul_one,
        ← ht, ← hn, ← hc, ← hm]
      have hpt : ∀ x : Fin k, star ((if x = i then (1 : ℂ) else 0) +
          u x.castSucc * star (u i.castSucc) * (c : ℂ)) * u x.castSucc =
          (if x = i then u i.castSucc else 0) + star (u x.castSucc) * u x.castSucc *
            (u i.castSucc * (c : ℂ)) := by
        intro x; split_ifs with h <;> [subst h; skip] <;> simp only [star_add, star_mul, frameMat_star_ofReal, star_star,
          star_one, star_zero] <;> ring
      rw [Finset.sum_congr rfl (fun x _ => hpt x)]
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.sum_mul, hu,
        star_mul, frameMat_star_ofReal, star_star]
      linear_combination (u i.castSucc) * key2 +
        (u i.castSucc * (c : ℂ) - u i.castSucc * (m : ℂ)) * ht2
    | cast j =>
      simp only [frameMat_ll, frameMat_cl, frameMat_lc, frameMat_cc, Matrix.diagonal_apply, hne, hne', if_true, if_false, mul_one,
        Fin.castSucc_inj, ← ht, ← hn, ← hc, ← hm]
      have hpt : ∀ x : Fin k, star ((if x = i then (1 : ℂ) else 0) +
          u x.castSucc * star (u i.castSucc) * (c : ℂ)) * ((if x = j then (1 : ℂ) else 0) +
          u x.castSucc * star (u j.castSucc) * (c : ℂ)) =
          (if x = i then (if i = j then 1 else 0) + u i.castSucc * star (u j.castSucc) * (c : ℂ) else 0) +
          (if x = j then star (u j.castSucc) * u i.castSucc * (c : ℂ) else 0) +
          star (u x.castSucc) * u x.castSucc * (u i.castSucc * star (u j.castSucc) * (c : ℂ) ^ 2) := by
        intro x; split_ifs <;> subst_vars <;> first
          | exact (‹¬ _ = _› rfl).elim
          | (simp only [star_add, star_mul, frameMat_star_ofReal, star_star, star_one, star_zero]; ring)
      rw [Finset.sum_congr rfl (fun x _ => hpt x)]
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, ← Finset.sum_mul, hu,
        star_mul, frameMat_star_ofReal, star_star]
      linear_combination (u i.castSucc * star (u j.castSucc)) * key +
        (u i.castSucc * star (u j.castSucc) * (c : ℂ) ^ 2 - u i.castSucc * star (u j.castSucc) * (m : ℂ) ^ 2) * ht2

def frameCoef (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if r ≤ i.val ∧ i.val ≤ r + k then (if i.val = r + k then -1 else 1) else 0

theorem frame_wI_val (k r : ℕ) (j : Fin (k + 1)) : (wI k r j).val = r + j.val := rfl

theorem frame_Hpk_mul (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j * z j = if j = i then frameCoef k r i * z i else 0 := by
  by_cases hij : j = i
  · subst hij
    rw [if_pos rfl]
    by_cases hj : j.val < r ∨ r + k < j.val
    · rw [hz j hj, mul_zero, mul_zero]
    · congr 1
      unfold Hpk frameCoef
      split_ifs <;> first | rfl | (exfalso; omega) | simp_all
  · rw [if_neg hij]
    by_cases hj : j.val < r ∨ r + k < j.val
    · rw [hz j hj, mul_zero]
    · have hv : j.val ≠ i.val := fun h => hij (Fin.ext h)
      unfold Hpk
      split_ifs <;> first | (exfalso; omega) | simp_all | simp

theorem frame_herm (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) :
    herm (Hpk k r) z z = ∑ l : Fin k, star (z (wI k r l.castSucc)) * z (wI k r l.castSucc) -
      star (z (wI k r (Fin.last k))) * z (wI k r (Fin.last k)) := by
  have hrow : ∀ i, (Hpk k r *ᵥ z) i = frameCoef k r i * z i := by
    intro i
    show ∑ j, Hpk k r i j * z j = _
    rw [Finset.sum_congr rfl (fun j _ => frame_Hpk_mul k r z hz i j)]
    simp
  show ∑ i, star (z i) * (Hpk k r *ᵥ z) i = _
  simp only [hrow]
  have hinj : Function.Injective (wI k r) := by
    intro a b h
    have h' := congrArg Fin.val h
    rw [frame_wI_val, frame_wI_val] at h'
    exact Fin.ext (by omega)
  have hsub : ∑ i, star (z i) * (frameCoef k r i * z i) =
      ∑ i ∈ Finset.univ.image (wI k r), star (z i) * (frameCoef k r i * z i) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have hn : ¬ (r ≤ i.val ∧ i.val ≤ r + k) := by
      rintro ⟨h1, h2⟩
      exact hi (Finset.mem_image.2 ⟨⟨i.val - r, by omega⟩, Finset.mem_univ _,
        Fin.ext (by rw [frame_wI_val]; simp; omega)⟩)
    simp [frameCoef, hn]
  have hc1 : ∀ l : Fin k, frameCoef k r (wI k r l.castSucc) = 1 := by
    intro l
    have hl := l.isLt
    have h1 : r ≤ r + (l : ℕ) ∧ r + (l : ℕ) ≤ r + k := by omega
    have h3 : (l : ℕ) ≠ k := by omega
    simp [frameCoef, frame_wI_val, h1, h3]
  have hc2 : frameCoef k r (wI k r (Fin.last k)) = -1 := by
    simp [frameCoef, frame_wI_val]
  rw [hsub, Finset.sum_image (fun a _ b _ h => hinj h), Fin.sum_univ_castSucc]
  simp only [hc1, hc2, one_mul, neg_one_mul, mul_neg, sub_eq_add_neg]

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvCharA
section
noncomputable section

open Matrix
open scoped ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.InvChr

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section hpk
variable (k r : ℕ)

theorem Hpk_out {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = 2 * r + k - i.val then 1 else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem Hpk_mid {i : Fin (2 * r + k + 1)} (h : ¬(i.val < r ∨ r + k < i.val)) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = i.val then (if i.val = r + k then -1 else 1) else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem Hpk_mulVec (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = if i.val < r ∨ r + k < i.val then v ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -v i else v i := by
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [if_pos h]
    simp only [mulVec, dotProduct, Hpk_out k r h]
    have e : ∀ j : Fin (2 * r + k + 1), (if j.val = 2 * r + k - i.val then (1 : ℂ) else 0) * v j =
        if j = ⟨2 * r + k - i.val, by omega⟩ then v j else 0 := by
      intro j
      by_cases hj : j.val = 2 * r + k - i.val
      · rw [if_pos hj, if_pos (Fin.ext hj), one_mul]
      · rw [if_neg hj, if_neg (fun e => hj (congrArg Fin.val e)), zero_mul]
    simp only [e, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  · rw [if_neg h]
    simp only [mulVec, dotProduct, Hpk_mid k r h]
    have e : ∀ j : Fin (2 * r + k + 1),
        (if j.val = i.val then (if i.val = r + k then (-1 : ℂ) else 1) else 0) * v j =
        if j = i then (if i.val = r + k then (-1 : ℂ) else 1) * v j else 0 := by
      intro j
      by_cases hj : j = i
      · subst hj
        simp
      · rw [if_neg (fun e => hj (Fin.ext e)), if_neg hj, zero_mul]
    simp only [e, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    split_ifs <;> simp

theorem Hpk_mulVec_mulVec (v : Fin (2 * r + k + 1) → ℂ) : Hpk k r *ᵥ (Hpk k r *ᵥ v) = v := by
  funext i
  have hi := i.isLt
  rw [Hpk_mulVec]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [if_pos h, Hpk_mulVec]
    split_ifs with h3 h4
    all_goals first
      | (congr 1
         apply Fin.ext
         show 2 * r + k - (2 * r + k - i.val) = i.val
         omega)
      | (exfalso
         have h3' : ¬(2 * r + k - i.val < r ∨ r + k < 2 * r + k - i.val) := h3
         omega)
  · rw [if_neg h, Hpk_mulVec, if_neg h]
    split_ifs <;> simp

theorem mat_eq_of_mulVec' {A B : Mat k r} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  ext i j
  have e := congrFun (h (Pi.single j 1)) i
  simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte] at e
  exact e

theorem Hpk_sq : Hpk k r * Hpk k r = 1 := by
  exact mat_eq_of_mulVec' k r (fun v => by rw [← mulVec_mulVec, Hpk_mulVec_mulVec, one_mulVec])

end hpk

section wb
variable {k r : ℕ}

end wb

section cc
variable {k r : ℕ}

def isW (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val ≤ r + k

section cc

variable (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)

def cc (v : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ :=
  embWb k r γ *ᵥ (fun i => conj (((embWb k r γ)⁻¹ *ᵥ v) i))

variable {γ}
variable (hE : IsUnit (embWb k r γ).det)
include hE

theorem gbar_mul (g g' : Mat k r) : gbar k r γ (g * g') = gbar k r γ g * gbar k r γ g' := by
  unfold gbar
  have h1 : (embWb k r γ)⁻¹ * embWb k r γ = 1 := nonsing_inv_mul _ hE
  have h2 : embWb k r γ * (embWb k r γ)⁻¹ = 1 := mul_nonsing_inv _ hE
  have h1' : ∀ X : Mat k r, (embWb k r γ)⁻¹ * (embWb k r γ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have h2' : ∀ X : Mat k r, embWb k r γ * ((embWb k r γ)⁻¹ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hB : (embWb k r γ)⁻¹ * (g * g') * embWb k r γ =
      ((embWb k r γ)⁻¹ * g * embWb k r γ) * ((embWb k r γ)⁻¹ * g' * embWb k r γ) := by
    simp only [Matrix.mul_assoc, h2']
  rw [hB, Matrix.map_mul]
  simp only [Matrix.mul_assoc, h1']

theorem gbar_one : gbar k r γ 1 = 1 := by
  unfold gbar
  have h1 : (embWb k r γ)⁻¹ * embWb k r γ = 1 := nonsing_inv_mul _ hE
  have h2 : embWb k r γ * (embWb k r γ)⁻¹ = 1 := mul_nonsing_inv _ hE
  have hm1 : (1 : Mat k r).map (starRingEnd ℂ) = 1 := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.one_apply, h]
  simp only [Matrix.mul_one, h1, hm1, h2]

theorem gbar_inv (A : Mat k r) (hA : IsUnit A.det) : gbar k r γ A⁻¹ = (gbar k r γ A)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← gbar_mul hE, Matrix.mul_nonsing_inv _ hA, gbar_one hE]

end cc

end cc

end ReciprocityTheory.ChartRestriction.DS.Mult1.InvChr
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JSchurG
section
namespace ReciprocityTheory.ChartRestriction.DS.Mult1

theorem stSchurG : StSchurG := by
  intro k r Wp _ _ _ D X _ hX
  letI := X.hN
  letI := X.hI
  letI := X.hC

  haveI : Nontrivial X.Hs := ⟨⟨X.w, 0, fun h => by
    have hw := X.w_norm
    rw [h, norm_zero] at hw
    exact zero_ne_one hw⟩⟩
  obtain ⟨d, hd, h⟩ := schur_GV D.haarG X.rep X.irr (fun v w => hX v w)
  exact ⟨d, hd, fun v w v' w' => h v w v' w'⟩

end ReciprocityTheory.ChartRestriction.DS.Mult1
end

