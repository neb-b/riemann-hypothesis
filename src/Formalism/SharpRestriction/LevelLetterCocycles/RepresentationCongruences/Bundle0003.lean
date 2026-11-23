module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.TsumThree
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0001
public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Bundle0002

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.FinalStep0
section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

theorem lift_le (l : ℕ) [Fact l.Prime] (hl : 11 ≤ l) (h η H M : ℕ) (h1 : 1 ≤ h) (hη : 20 * η ≤ h)
    (hH : H ≤ h + η) (hM : M ≤ h) (jumps : Finset ℤ)
    (hj : ∀ u ∈ jumps, -(M : ℤ) ≤ u ∧ u ≤ h) :
    let J : Finset ℤ :=
      ((jumps ×ˢ Finset.Icc (1 : ℤ) M).image (fun p : ℤ × ℤ => p.1 + p.2)).filter (fun j => j ≠ 0) ∪
        Finset.Icc (1 : ℤ) M
    let aS : ℕ := M / (l - 1) + 1
    let eW : ℕ := ⌊(H : ℝ) * l / ((l : ℝ) - 1) ^ 2 + 3 + Real.logb l ((H : ℝ) + 1)⌋₊
    let eU : ℕ := (∑ j ∈ J, padicValInt l j) + aS + padicValNat l aS.factorial
    ((2 * eW + eU : ℕ) : ℝ) ≤ 71 / 10 * (h : ℝ) / l + 71 / 10 + 2 * Real.logb l (2 * (h : ℝ)) := by
  intro J aS eW eU
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  have hl1 : (1 : ℝ) < l := by linarith
  have hxm : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  have hxi0 : 0 ≤ (l : ℝ)⁻¹ := by positivity
  have hyi0 : 0 ≤ ((l : ℝ) - 1)⁻¹ := inv_nonneg.2 hxm.le
  have hyi10 : ((l : ℝ) - 1)⁻¹ ≤ 1 / 10 := Formalism.MainNotions.N.FrobeniusPowerSeries.NumericInequalities.p_le hl'
  have hyix : ((l : ℝ) - 1)⁻¹ ≤ 11 / 10 * (l : ℝ)⁻¹ := Formalism.MainNotions.N.FrobeniusPowerSeries.NumericInequalities.p_le_u hl'
  have hsq : (l : ℝ) / ((l : ℝ) - 1) ^ 2 ≤ 121 / 100 * (l : ℝ)⁻¹ := Formalism.MainNotions.N.FrobeniusPowerSeries.NumericInequalities.q_le hl'
  have hsq0 : 0 ≤ (l : ℝ) / ((l : ℝ) - 1) ^ 2 := by positivity
  have hH1 : H + 1 ≤ 2 * h := by omega
  have hHr : (H : ℝ) ≤ h + η := by exact_mod_cast hH
  have hMr : (M : ℝ) ≤ h := by exact_mod_cast hM
  have hηr : (20 : ℝ) * η ≤ h := by exact_mod_cast hη
  have hH1r : (H : ℝ) + 1 ≤ 2 * (h : ℝ) := by exact_mod_cast hH1
  have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hlogH0 : 0 ≤ Real.logb l ((H : ℝ) + 1) := Real.logb_nonneg hl1 (by linarith)
  have hlogH : Real.logb l ((H : ℝ) + 1) ≤ Real.logb l (2 * (h : ℝ)) :=
    Real.logb_le_logb_of_le hl1 (by linarith) hH1r
  have hW : (eW : ℝ) ≤ (H : ℝ) * ((l : ℝ) / ((l : ℝ) - 1) ^ 2) + 3 + Real.logb l ((H : ℝ) + 1) := by
    have h0 : 0 ≤ (H : ℝ) * l / ((l : ℝ) - 1) ^ 2 + 3 + Real.logb l ((H : ℝ) + 1) := by
      have : 0 ≤ (H : ℝ) * l / ((l : ℝ) - 1) ^ 2 := by positivity
      linarith
    calc (eW : ℝ) ≤ (H : ℝ) * l / ((l : ℝ) - 1) ^ 2 + 3 + Real.logb l ((H : ℝ) + 1) :=
          Nat.floor_le h0
      _ = (H : ℝ) * ((l : ℝ) / ((l : ℝ) - 1) ^ 2) + 3 + Real.logb l ((H : ℝ) + 1) := by ring
  have hHsq : (H : ℝ) * ((l : ℝ) / ((l : ℝ) - 1) ^ 2) ≤ ((h : ℝ) + η) * (121 / 100 * (l : ℝ)⁻¹) :=
    mul_le_mul hHr hsq hsq0 (by positivity)
  have hηxi : (20 * (η : ℝ)) * (l : ℝ)⁻¹ ≤ (h : ℝ) * (l : ℝ)⁻¹ := mul_le_mul_of_nonneg_right hηr hxi0
  have hl1n : ((l - 1 : ℕ) : ℝ) = (l : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ l), Nat.cast_one]
  have hA : (aS : ℝ) ≤ (M : ℝ) * ((l : ℝ) - 1)⁻¹ + 1 := by
    have hd : ((M / (l - 1) : ℕ) : ℝ) ≤ (M : ℝ) / ((l - 1 : ℕ) : ℝ) := Nat.cast_div_le
    rw [hl1n, div_eq_mul_inv] at hd
    have he : (aS : ℝ) = ((M / (l - 1) : ℕ) : ℝ) + 1 := by
      show ((M / (l - 1) + 1 : ℕ) : ℝ) = ((M / (l - 1) : ℕ) : ℝ) + 1
      rw [Nat.cast_add, Nat.cast_one]
    linarith
  have hF : (padicValNat l aS.factorial : ℝ) ≤ (aS : ℝ) * ((l : ℝ) - 1)⁻¹ := by
    have hfa := padicValNat_factorial_le_div_sub_one' l aS
    rwa [div_eq_mul_inv] at hfa
  have hFA : (aS : ℝ) * ((l : ℝ) - 1)⁻¹ ≤ ((M : ℝ) * ((l : ℝ) - 1)⁻¹ + 1) * ((l : ℝ) - 1)⁻¹ :=
    mul_le_mul_of_nonneg_right hA hyi0
  have hyy : ((l : ℝ) - 1)⁻¹ * ((l : ℝ) - 1)⁻¹ ≤ 11 / 100 * (l : ℝ)⁻¹ := by
    have hq := mul_le_mul_of_nonneg_right hyi10 hyi0
    linarith
  have hMyy : (M : ℝ) * (((l : ℝ) - 1)⁻¹ * ((l : ℝ) - 1)⁻¹) ≤ (h : ℝ) * (11 / 100 * (l : ℝ)⁻¹) :=
    mul_le_mul hMr hyy (mul_self_nonneg _) (Nat.cast_nonneg h)
  have hMy : (M : ℝ) * ((l : ℝ) - 1)⁻¹ ≤ (h : ℝ) * (11 / 10 * (l : ℝ)⁻¹) :=
    mul_le_mul hMr hyix hyi0 (Nat.cast_nonneg h)
  have hhy : (h : ℝ) * ((l : ℝ) - 1)⁻¹ ≤ (h : ℝ) * (11 / 10 * (l : ℝ)⁻¹) :=
    mul_le_mul_of_nonneg_left hyix (Nat.cast_nonneg h)
  have hJsub : J ⊆ Finset.Ico (-(M : ℤ)) (-(M : ℤ) + (M : ℤ)) ∪
      Finset.Ico (1 : ℤ) (1 + ((h + M : ℕ) : ℤ)) := by
    intro j hjJ
    rcases Finset.mem_union.1 hjJ with hA' | hB'
    · obtain ⟨hA1, hne⟩ := Finset.mem_filter.1 hA'
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hA1
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.1 hp
      obtain ⟨ht1, ht2⟩ := Finset.mem_Icc.1 hp2
      obtain ⟨hu1, hu2⟩ := hj p.1 hp1
      rw [Finset.mem_union, Finset.mem_Ico, Finset.mem_Ico]
      push_cast
      omega
    · obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hB'
      rw [Finset.mem_union, Finset.mem_Ico, Finset.mem_Ico]
      push_cast
      omega
  have hw1 := sum_padicValInt_window_le l (-(M : ℤ)) M M (by
    intro i hi
    rw [Finset.mem_Ico] at hi
    exact ⟨by omega, abs_le.2 ⟨by omega, by omega⟩⟩)
  have hw2 := sum_padicValInt_window_le l (1 : ℤ) (h + M) (h + M) (by
    intro i hi
    rw [Finset.mem_Ico] at hi
    push_cast at hi ⊢
    exact ⟨by omega, abs_le.2 ⟨by omega, by omega⟩⟩)
  have hdisj : Disjoint (Finset.Ico (-(M : ℤ)) (-(M : ℤ) + (M : ℤ)))
      (Finset.Ico (1 : ℤ) (1 + ((h + M : ℕ) : ℤ))) := by
    rw [Finset.disjoint_left]
    intro x hx hy
    rw [Finset.mem_Ico] at hx hy
    omega
  have hle : ∑ j ∈ J, padicValInt l j ≤
      ∑ j ∈ Finset.Ico (-(M : ℤ)) (-(M : ℤ) + (M : ℤ)), padicValInt l j +
        ∑ j ∈ Finset.Ico (1 : ℤ) (1 + ((h + M : ℕ) : ℤ)), padicValInt l j := by
    rw [← Finset.sum_union hdisj]
    exact Finset.sum_le_sum_of_subset hJsub
  have hler : ((∑ j ∈ J, padicValInt l j : ℕ) : ℝ) ≤
      ((∑ j ∈ Finset.Ico (-(M : ℤ)) (-(M : ℤ) + (M : ℤ)), padicValInt l j : ℕ) : ℝ) +
        ((∑ j ∈ Finset.Ico (1 : ℤ) (1 + ((h + M : ℕ) : ℤ)), padicValInt l j : ℕ) : ℝ) := by
    exact_mod_cast hle
  have hcM : ((h + M : ℕ) : ℝ) = (h : ℝ) + M := Nat.cast_add h M
  rw [hcM, div_eq_mul_inv] at hw2
  rw [div_eq_mul_inv] at hw1
  have hU : ((2 * eW + eU : ℕ) : ℝ) = 2 * (eW : ℝ) + ((∑ j ∈ J, padicValInt l j : ℕ) : ℝ) +
      (aS : ℝ) + (padicValNat l aS.factorial : ℝ) := by
    show ((2 * eW + ((∑ j ∈ J, padicValInt l j) + aS + padicValNat l aS.factorial) : ℕ) : ℝ) = _
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  rw [hU]
  have hgoal : (71 : ℝ) / 10 * (h : ℝ) / l = 71 / 10 * ((h : ℝ) * (l : ℝ)⁻¹) := by ring
  rw [hgoal]
  have hhx : 0 ≤ (h : ℝ) * (l : ℝ)⁻¹ := mul_nonneg (Nat.cast_nonneg h) hxi0
  linarith [hW, hHsq, hηxi, hlogH, hler, hw1, hw2, hA, hF, hFA, hMyy, hMy, hhy, hyi10]

theorem step0 (l : ℕ) (hl : 11 ≤ l) (b w S η : ℕ) (hb : 1 ≤ b) (hηb : 20 * η ≤ b) (hSb : 20 * S ≤ b)
    (hwb : 20 * w ≤ b) (hsm : (b : ℝ) / 4 < 40 * Sg l (b + η + S) w S η) :
    71 / 10 * ((b + η + S : ℕ) : ℝ) / l + 71 / 10 + 2 * Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) ≤
      160 * Sg l (b + η + S) w S η := by
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  have hl1 : (1 : ℝ) < l := by linarith
  have hX : ((b + η + S : ℕ) : ℝ) = (b : ℝ) + η + S := by push_cast; ring
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hηr : (20 : ℝ) * η ≤ b := by exact_mod_cast hηb
  have hSr : (20 : ℝ) * S ≤ b := by exact_mod_cast hSb
  have hη0 : (0 : ℝ) ≤ η := Nat.cast_nonneg η
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg S
  have hX1 : (1 : ℝ) ≤ ((b + η + S : ℕ) : ℝ) := by rw [hX]; linarith
  have hL : 0 ≤ Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) := Real.logb_nonneg hl1 (by linarith)
  have hE : Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) + 1 ≤ Sg l (b + η + S) w S η := by
    unfold Sg
    have e1 : 0 ≤ ((b + η + S : ℕ) : ℝ) / (l : ℝ) ^ 2 := by positivity
    have e2 : 0 ≤ ((w : ℝ) + S + η) / l := by positivity
    linarith
  have hdiv : 71 / 10 * ((b + η + S : ℕ) : ℝ) / l ≤ 71 / 10 * ((b + η + S : ℕ) : ℝ) / 11 := by
    gcongr
  linarith

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LogbNn
section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.CaseA

lemma sg_eq (l h w S η : ℕ) : Sg l h w S η =
    (h:ℝ) * ((l:ℝ)⁻¹) ^ 2 + (w:ℝ) * (l:ℝ)⁻¹ + (S:ℝ) * (l:ℝ)⁻¹ + (η:ℝ) * (l:ℝ)⁻¹ +
      Real.logb l (2 * (h:ℝ)) + 1 := by
  unfold Sg
  ring

lemma logb_nn (l h : ℕ) (hl : 11 ≤ l) (h1 : 1 ≤ h) : 0 ≤ Real.logb l (2 * (h:ℝ)) := by
  apply Real.logb_nonneg
  · have : (11 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  · have : (1 : ℝ) ≤ h := by exact_mod_cast h1
    linarith

lemma sg_ge (l h w S η : ℕ) (hl : 11 ≤ l) (h1 : 1 ≤ h) :
    0 ≤ (h:ℝ) * ((l:ℝ)⁻¹) ^ 2 ∧ 0 ≤ (w:ℝ) * (l:ℝ)⁻¹ ∧ 0 ≤ (S:ℝ) * (l:ℝ)⁻¹ ∧
      0 ≤ (η:ℝ) * (l:ℝ)⁻¹ ∧ 0 ≤ Real.logb l (2 * (h:ℝ)) ∧
      Real.logb l (2 * (h:ℝ)) + 1 + (η:ℝ) * (l:ℝ)⁻¹ ≤ Sg l h w S η ∧ 1 ≤ Sg l h w S η := by
  have hlg := logb_nn l h hl h1
  have a1 : 0 ≤ (h:ℝ) * ((l:ℝ)⁻¹) ^ 2 := by positivity
  have a2 : 0 ≤ (w:ℝ) * (l:ℝ)⁻¹ := by positivity
  have a3 : 0 ≤ (S:ℝ) * (l:ℝ)⁻¹ := by positivity
  have a4 : 0 ≤ (η:ℝ) * (l:ℝ)⁻¹ := by positivity
  rw [sg_eq]
  refine ⟨a1, a2, a3, a4, hlg, by linarith, by linarith⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries.CaseA
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.QuotientDistinguishedTorsionFree
section
namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open PowerSeries Formalism.MainNotions.N.FrobeniusPowerSeries

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

noncomputable def wdeg (g : O⟦X⟧) : ℕ := (g.map (IsLocalRing.residue O)).order.toNat

def IsDist (g : O⟦X⟧) : Prop := g.map (IsLocalRing.residue O) ≠ 0

theorem exists_weierstrass_substitution (g : O⟦X⟧) (hg : IsDist g) (hD : 1 ≤ wdeg g) :
    ∃ h : O⟦X⟧ →ₐ[O] O⟦X⟧, h X = g ∧ Function.Injective h ∧
      ∀ f : O⟦X⟧, ∃! c : Fin (wdeg g) → O⟦X⟧, f = ∑ i : Fin (wdeg g), X ^ (i : ℕ) * h (c i) := by
  have hg0 : constantCoeff g ∈ IsLocalRing.maximalIdeal O := WeierD.constantCoeff_mem (g := g) hD
  obtain ⟨h, hX⟩ := WeierS.exists_algHom_X_eq hg0
  refine ⟨h, hX, WeierD.injective (g := g) hg hD h hX, fun f => ?_⟩
  obtain ⟨c, hc⟩ := WeierD.exists_decomp (g := g) hg hD h hX f
  exact ⟨c, hc, fun c' hc' => WeierD.decomp_unique (g := g) hg h hX c' c (hc'.symm.trans hc)⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ThetaAtRoot
section
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open PowerSeries

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

private theorem exists_eq_C_constantCoeff_add_X_mul {A : Type*} [CommRing A] (f : A⟦X⟧) :
    ∃ f' : A⟦X⟧, f = C (constantCoeff f) + X * f' := by
  obtain ⟨f', hf'⟩ :=
    (PowerSeries.X_dvd_iff).mpr (show constantCoeff (f - C (constantCoeff f)) = 0 by simp)
  exact ⟨f', by linear_combination hf'⟩

private theorem ringHom_eq_of_eq_on_C_X_of_pow_dvd_eq_zero {A B : Type*} [CommRing A] [CommRing B]
    (ψ₁ ψ₂ : A⟦X⟧ →+* B) (hC : ∀ a, ψ₁ (C a) = ψ₂ (C a)) (hX : ψ₁ X = ψ₂ X)
    (hsep : ∀ d : B, (∀ n : ℕ, ψ₁ X ^ n ∣ d) → d = 0) (f : A⟦X⟧) : ψ₁ f = ψ₂ f := by
  have key : ∀ n : ℕ, ∀ g : A⟦X⟧, ψ₁ X ^ n ∣ ψ₁ g - ψ₂ g := by
    intro n
    induction n with
    | zero => intro g; simp
    | succ n ih =>
      intro g
      obtain ⟨g', hg'⟩ := exists_eq_C_constantCoeff_add_X_mul g
      obtain ⟨r, hr⟩ := ih g'
      have e1 : ψ₁ g = ψ₁ (C (constantCoeff g)) + ψ₁ X * ψ₁ g' := by
        calc ψ₁ g = ψ₁ (C (constantCoeff g) + X * g') := by rw [← hg']
          _ = _ := by rw [map_add (f := _), map_mul]
      have e2 : ψ₂ g = ψ₂ (C (constantCoeff g)) + ψ₂ X * ψ₂ g' := by
        calc ψ₂ g = ψ₂ (C (constantCoeff g) + X * g') := by rw [← hg']
          _ = _ := by rw [map_add (f := _), map_mul]
      exact ⟨r, by linear_combination e1 - e2 + hC (constantCoeff g) + ψ₂ g' * hX + ψ₁ X * hr⟩
  exact sub_eq_zero.mp (hsep _ (fun n => key n f))

theorem theta_at_root (l : ℕ) [Fact l.Prime] (hl : ((l : ℕ) : O) ∈ IsLocalRing.maximalIdeal O)
    (φ₀ γ : O⟦X⟧ →ₐ[O] O⟦X⟧) (hφ₀ : φ₀ X = (1 + X) ^ l - 1) (hc : ∀ f, φ₀ (γ f) = γ (φ₀ f))
    (χ : O) (h0 : constantCoeff (γ X) = 0) (h1 : coeff 1 (γ X) = χ)
    (hχ : χ - 1 ∈ Ideal.span {((l : ℕ) : O)})
    (x₀ : O) (hx₀ : x₀ ≠ 0) (hroot : (1 + x₀) ^ l = 1)
    (Q : O⟦X⟧) (hQ : X * Q = (1 + X) ^ l - 1) (u : O⟦X⟧) (hu : IsUnit u) (θ : O⟦X⟧)
    (hθ : γ (u * Q) = u * Q * θ) :
    θ - C χ ∈ Ideal.span {X - C x₀} := by
  have hxm : x₀ ∈ IsLocalRing.maximalIdeal O :=
    Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.mem_max l hl hroot
  obtain ⟨I, hI⟩ : ∃ I : Ideal O⟦X⟧, I = Ideal.span {X - C x₀} := ⟨_, rfl⟩
  rw [← hI]
  have hXI : X - C x₀ ∈ I := by rw [hI]; exact Ideal.mem_span_singleton_self _
  have hπX : Ideal.Quotient.mk I X = Ideal.Quotient.mk I (C x₀) := Ideal.Quotient.eq.mpr hXI
  have hinj : ∀ a b : O, Ideal.Quotient.mk I (C a) = Ideal.Quotient.mk I (C b) → a = b := by
    intro a b hab
    have h' : C (a - b) ∈ Ideal.span {X - C x₀} := by
      rw [map_sub, ← hI]; exact Ideal.Quotient.eq.mp hab
    exact sub_eq_zero.mp (Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.uniq hxm h')
  have hsurj : ∀ p : O⟦X⟧, ∃ c : O, Ideal.Quotient.mk I p = Ideal.Quotient.mk I (C c) := by
    intro p
    obtain ⟨c, q, hpq⟩ := Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.decomp hxm p
    refine ⟨c, Ideal.Quotient.eq.mpr ?_⟩
    rw [hpq, add_sub_cancel_right]
    exact I.mul_mem_right q hXI
  have hsep : ∀ d : O⟦X⟧ ⧸ I, (∀ n : ℕ, Ideal.Quotient.mk I X ^ n ∣ d) → d = 0 := by
    intro d hd
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective d
    obtain ⟨c, hc'⟩ := hsurj p
    rw [hc'] at hd ⊢
    have hmem : ∀ n : ℕ, c ∈ Ideal.span {x₀} ^ n := by
      intro n
      obtain ⟨r, hr⟩ := hd n
      obtain ⟨p', rfl⟩ := Ideal.Quotient.mk_surjective r
      obtain ⟨e, he⟩ := hsurj p'
      have h2 : Ideal.Quotient.mk I (C c) = Ideal.Quotient.mk I (C (x₀ ^ n * e)) := by
        rw [hr, hπX, he]; simp only [map_mul, map_pow]
      rw [hinj _ _ h2, Ideal.span_singleton_pow]
      exact (Ideal.span {x₀ ^ n}).mul_mem_right e (Ideal.mem_span_singleton_self _)
    have hne : Ideal.span {x₀} ≠ ⊤ := by
      rw [Ne, Ideal.span_singleton_eq_top]
      exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal x₀).mp hxm)
    have hc0 : c ∈ ⨅ n : ℕ, Ideal.span {x₀} ^ n := Ideal.mem_iInf.mpr hmem
    rw [Ideal.iInf_pow_eq_bot_of_isDomain (Ideal.span {x₀}) hne, Ideal.mem_bot] at hc0
    rw [hc0, map_zero, map_zero]
  have hπφX : Ideal.Quotient.mk I (φ₀ X) = 0 := by
    have h3 : Ideal.Quotient.mk I (φ₀ X) = Ideal.Quotient.mk I (C ((1 + x₀) ^ l - 1)) := by
      rw [hφ₀]; simp only [map_sub, map_pow, map_add (f := _), map_one, hπX]
    rw [h3, hroot, sub_self, map_zero, map_zero]
  have hφπ : ∀ f, Ideal.Quotient.mk I (φ₀ f) = Ideal.Quotient.mk I (C (constantCoeff f)) := by
    intro f
    obtain ⟨f', hf'⟩ := exists_eq_C_constantCoeff_add_X_mul f
    calc Ideal.Quotient.mk I (φ₀ f)
        = Ideal.Quotient.mk I (φ₀ (C (constantCoeff f) + X * f')) := by rw [← hf']
      _ = _ := by
        simp only [map_add (f := _), map_mul, Formalism.MainNotions.N.FrobeniusPowerSeries.LTA.alg_C, hπφX, zero_mul, add_zero]
  obtain ⟨g1, hg1⟩ := (PowerSeries.X_dvd_iff).mpr h0
  have hg1χ : constantCoeff g1 = χ := by
    rw [← h1, hg1]
    show constantCoeff g1 = coeff (0 + 1) (X * g1)
    rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  obtain ⟨t, ht⟩ := exists_eq_C_constantCoeff_add_X_mul g1
  obtain ⟨e, he⟩ := hsurj t
  have hπg1 : Ideal.Quotient.mk I g1 = Ideal.Quotient.mk I (C (χ + x₀ * e)) := by
    rw [ht, hg1χ]; simp only [map_add (f := _), map_mul, hπX, he]
  have hπg : Ideal.Quotient.mk I (γ X) = Ideal.Quotient.mk I (C (x₀ * (χ + x₀ * e))) := by
    rw [hg1, map_mul, hπg1, hπX]; simp only [map_mul]
  have hry : (1 + x₀ * (χ + x₀ * e)) ^ l = 1 := by
    have h4 : Ideal.Quotient.mk I (γ (φ₀ X)) = 0 := by
      rw [← hc X, hφπ, h0, map_zero, map_zero]
    have h5 : Ideal.Quotient.mk I (γ (φ₀ X))
        = Ideal.Quotient.mk I (C ((1 + x₀ * (χ + x₀ * e)) ^ l - 1)) := by
      rw [hφ₀]; simp only [map_sub, map_pow, map_add (f := _), map_one, hπg]
    have h6 := hinj ((1 + x₀ * (χ + x₀ * e)) ^ l - 1) 0 (by rw [← h5, h4, map_zero, map_zero])
    exact sub_eq_zero.mp h6
  have hχm : χ - 1 ∈ IsLocalRing.maximalIdeal O :=
    (Ideal.span_singleton_le_iff_mem _).mpr hl hχ
  have hw : χ - 1 + x₀ * e ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.maximalIdeal O).add_mem hχm ((IsLocalRing.maximalIdeal O).mul_mem_right e hxm)
  have hyx : x₀ * (χ + x₀ * e) = x₀ :=
    Formalism.MainNotions.N.FrobeniusPowerSeries.LTB.root_eq l hx₀ hroot hry hw (by ring)
  have hχe : χ + x₀ * e = 1 := mul_left_cancel₀ hx₀ (by rw [hyx, mul_one])
  have hπg1' : Ideal.Quotient.mk I g1 = 1 := by rw [hπg1, hχe, map_one, map_one]
  have hπgX : Ideal.Quotient.mk I (γ X) = Ideal.Quotient.mk I X := by
    rw [hπg, hyx, hπX]
  have hγπ : ∀ f, Ideal.Quotient.mk I (γ f) = Ideal.Quotient.mk I f := by
    intro f
    exact (ringHom_eq_of_eq_on_C_X_of_pow_dvd_eq_zero (Ideal.Quotient.mk I) ((Ideal.Quotient.mk I).comp γ.toRingHom)
      (fun a => by
        show _ = Ideal.Quotient.mk I (γ (C a))
        rw [Formalism.MainNotions.N.FrobeniusPowerSeries.LTA.alg_C])
      hπgX.symm hsep f).symm
  obtain ⟨Q0, hQ0c, hQ0⟩ := Formalism.MainNotions.N.FrobeniusPowerSeries.LTA.exists_GL_latBasis_of_isSplitEquiv (O := O) l
  have hQQ0 : Q = Q0 := mul_left_cancel₀ PowerSeries.X_ne_zero (hQ.trans hQ0)
  have hQne : Q ≠ 0 := by
    intro hQz
    have hl0 : ((l : ℕ) : O) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
    apply hl0
    rw [← hQ0c, ← hQQ0, hQz, map_zero]
  have hγQ : γ (X * Q) = X * g1 * γ Q := by rw [map_mul, hg1]
  have hγQ' : γ (X * Q) = X * Q * φ₀ g1 := by
    rw [hQ, ← hφ₀, ← hc X, hg1, map_mul]
  have hg1Q : g1 * γ Q = Q * φ₀ g1 :=
    mul_left_cancel₀ PowerSeries.X_ne_zero (by linear_combination hγQ' - hγQ)
  have hkey : Q * (g1 * u * θ) = Q * (γ u * φ₀ g1) := by
    have e3 : γ (u * Q) = γ u * γ Q := map_mul _ _ _
    linear_combination (-g1) * hθ + g1 * e3 + γ u * hg1Q
  have hkey' : g1 * u * θ = γ u * φ₀ g1 := mul_left_cancel₀ hQne hkey
  have hk : Ideal.Quotient.mk I (g1 * u * θ) = Ideal.Quotient.mk I (γ u * φ₀ g1) := by
    rw [hkey']
  simp only [map_mul] at hk
  rw [hγπ, hφπ, hg1χ, hπg1', one_mul] at hk
  exact Ideal.Quotient.eq.mp ((hu.map (Ideal.Quotient.mk I)).mul_left_cancel hk)

end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

