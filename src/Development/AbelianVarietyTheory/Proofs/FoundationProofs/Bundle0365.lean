module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0362
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0164
public import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0355
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0344

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AmiceRiemannSumCongrDiracCoefficients
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

namespace GlobalTheory.KZ.Cmp.RiemannDirac

variable {l : ℕ} [Fact l.Prime]

theorem norm_tval_sub_tval_le (F : PowerSeries (Qbar l)) (hF : ∀ n, ‖F.coeff n‖ ≤ 1) {z : Qbar l} (hz : ‖z - 1‖ ≤ 1)
    {M N : ℕ} (h : M ≤ N) : ‖tval F N z - tval F M z‖ ≤ ‖z - 1‖ ^ M := by
  unfold tval
  rw [← Finset.sum_Ico_eq_sub _ h]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun n hn => ?_
  rw [norm_mul, norm_pow]
  exact (mul_le_of_le_one_left (by positivity) (hF n)).trans
    (pow_le_pow_of_le_one (norm_nonneg _) hz (Finset.mem_Ico.1 hn).1)

theorem sum_root_pow {r : ℕ} {ξ : Qbar l} (hξ : IsPrimitiveRoot ξ (l ^ r)) {x : ℕ} (hx : x < l ^ r) (j : ℕ) :
    ∑ k ∈ Finset.range (l ^ r), ξ ^ (l ^ r - (k * x) % l ^ r) * (ξ ^ k) ^ j =
      if x = j % l ^ r then ((l : ℕ) : Qbar l) ^ r else 0 := by
  have hpos : 0 < l ^ r := pow_pos (Fact.out : l.Prime).pos r
  rw [← mass_dirac hξ hx (Nat.mod_lt j hpos)]
  unfold mass
  refine Finset.sum_congr rfl fun k _ => ?_
  have hy : j % l ^ r < l ^ (3 * r) :=
    (Nat.mod_lt j hpos).trans_le (Nat.pow_le_pow_right (Fact.out : l.Prime).pos (by omega))
  have h1 : (ξ ^ k) ^ (l ^ r) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]
  rw [tval_dirac hy, ← pow_eq_pow_mod j h1]

theorem norm_mass_sub_le {F : PowerSeries (Qbar l)} {a : ℕ → Qbar l} {N r : ℕ} {ξ : Qbar l} (hN : l ^ (3 * r) ≤ N)
    (hF : ∀ n, ‖F.coeff n‖ ≤ 1) (ht : ∀ y : Qbar l, tval F N y = ∑ j ∈ Finset.range N, a j * y ^ j)
    (hξ : IsPrimitiveRoot ξ (l ^ r)) {x : ℕ} (hx : x < l ^ r) :
    ‖mass F r ξ x - ∑ j ∈ Finset.range N, a j * (if x = j % l ^ r then ((l : ℕ) : Qbar l) ^ r else 0)‖ ≤
      ‖((l : ℕ) : Qbar l) ^ (2 * r)‖ := by
  have hn : ‖ξ‖ = 1 := by
    have h1 := congrArg norm hξ.pow_eq_one
    rw [norm_pow, norm_one] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)).1 h1
  have e : ∑ j ∈ Finset.range N, a j * (if x = j % l ^ r then ((l : ℕ) : Qbar l) ^ r else 0) =
      ∑ k ∈ Finset.range (l ^ r), ξ ^ (l ^ r - (k * x) % l ^ r) * tval F N (ξ ^ k) := by
    simp_rw [ht, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← sum_root_pow hξ hx j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [e, mass, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun k _ => ?_
  have h1 : (ξ ^ k) ^ (l ^ r) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hξ.pow_eq_one, one_pow]
  rw [← mul_sub, norm_mul, norm_pow ξ, hn, one_pow, one_mul, norm_sub_rev]
  exact (norm_tval_sub_tval_le F hF (GlobalTheory.AmiceDist.norm_sub_one_le h1) hN).trans
    (GlobalTheory.AmiceDist.norm_sub_one_pow_three_le h1)

theorem norm_term_sub_le (φ : DirichletCharacter (Qbar l) l) (e : ℕ) {r : ℕ} (hr : 1 ≤ r) (j : ℕ) :
    ‖∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x),
        φ (x : ZMod l) * ((x : Qbar l) ^ e) * (if x = j % l ^ r then ((l : ℕ) : Qbar l) ^ r else 0) -
      (l : Qbar l) ^ r * (φ (j : ZMod l) * (j : Qbar l) ^ e)‖ ≤ ‖((l : ℕ) : Qbar l) ^ (2 * r)‖ := by
  have hpos : 0 < l ^ r := pow_pos (Fact.out : l.Prime).pos r
  have hd : l ∣ l ^ r := dvd_pow_self l (by omega)
  simp_rw [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · have hc : ((j % l ^ r : ℕ) : ZMod l) = (j : ZMod l) := by
      rw [← ZMod.natCast_mod (j % l ^ r) l, Nat.mod_mod_of_dvd _ hd, ZMod.natCast_mod]
    obtain ⟨c, hc'⟩ := ((Nat.mod_modEq j (l ^ r)).pow e).symm.dvd
    have h2 : ((j % l ^ r : ℕ) : Qbar l) ^ e - (j : Qbar l) ^ e = (l : Qbar l) ^ r * (c : Qbar l) := by
      have := congrArg (Int.cast : ℤ → Qbar l) hc'
      simpa only [Int.cast_sub, Int.cast_natCast, Nat.cast_pow, Int.cast_mul, Int.cast_pow] using this
    have h3 : φ ((j % l ^ r : ℕ) : ZMod l) * ((j % l ^ r : ℕ) : Qbar l) ^ e * (l : Qbar l) ^ r -
        (l : Qbar l) ^ r * (φ (j : ZMod l) * (j : Qbar l) ^ e) =
        (l : Qbar l) ^ (2 * r) * (φ (j : ZMod l) * (c : Qbar l)) := by
      rw [hc]
      linear_combination (φ (j : ZMod l) * (l : Qbar l) ^ r) * h2
    rw [h3, norm_mul, norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (mul_le_one₀ (φ.norm_le_one _) (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one _ _))
  · have h1 : l ∣ j := by
      rw [Finset.mem_filter, Finset.mem_range] at h
      by_contra h0
      exact h ⟨Nat.mod_lt j hpos, fun h' => h0 ((Nat.dvd_mod_iff hd).1 h')⟩
    rw [(ZMod.natCast_eq_zero_iff j l).2 h1, MulChar.map_zero]
    simp only [zero_mul, mul_zero, sub_zero, norm_zero, norm_nonneg]

theorem rSum_cg : ∀ (l : ℕ) [Fact l.Prime] (φ : DirichletCharacter (Qbar l) l) (e : ℕ) (F : PowerSeries (Qbar l))
    (a : ℕ → Qbar l) (N r : ℕ) (ξ : Qbar l), 1 ≤ r → l ^ (3 * r) ≤ N → (∀ n, ‖F.coeff n‖ ≤ 1) → (∀ j, ‖a j‖ ≤ 1) →
    (∀ y : Qbar l, tval F N y = ∑ j ∈ Finset.range N, a j * y ^ j) → IsPrimitiveRoot ξ (l ^ r) →
    Cg (2 * r) (rSum φ e F r ξ)
      ((l : Qbar l) ^ r * ∑ j ∈ Finset.range N, a j * (φ (j : ZMod l) * (j : Qbar l) ^ e)) := by
  intro l _ φ e F a N r ξ hr hN hF ha ht hξ
  have h1 : ‖rSum φ e F r ξ - ∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ e) *
      ∑ j ∈ Finset.range N, a j * (if x = j % l ^ r then ((l : ℕ) : Qbar l) ^ r else 0)‖ ≤ ‖((l : ℕ) : Qbar l) ^ (2 * r)‖ := by
    rw [rSum, ← Finset.sum_sub_distrib]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun x hx => ?_
    rw [← mul_sub, norm_mul, norm_mul, norm_pow (x : Qbar l)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (mul_le_one₀ (φ.norm_le_one _) (by positivity)
      (pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ _)))).trans
      (norm_mass_sub_le hN hF ht hξ (Finset.mem_range.1 (Finset.mem_filter.1 hx).1))
  have h2 : ‖(∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ e) *
      ∑ j ∈ Finset.range N, a j * (if x = j % l ^ r then ((l : ℕ) : Qbar l) ^ r else 0)) -
      (l : Qbar l) ^ r * ∑ j ∈ Finset.range N, a j * (φ (j : ZMod l) * (j : Qbar l) ^ e)‖ ≤ ‖((l : ℕ) : Qbar l) ^ (2 * r)‖ := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun j _ => ?_
    have e1 : (∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ e) *
        (a j * (if x = j % l ^ r then ((l : ℕ) : Qbar l) ^ r else 0))) -
        (l : Qbar l) ^ r * (a j * (φ (j : ZMod l) * (j : Qbar l) ^ e)) =
        a j * (∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x),
          φ (x : ZMod l) * ((x : Qbar l) ^ e) * (if x = j % l ^ r then ((l : ℕ) : Qbar l) ^ r else 0) -
          (l : Qbar l) ^ r * (φ (j : ZMod l) * (j : Qbar l) ^ e)) := by
      rw [mul_sub, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun x _ => by ring
      · ring
    rw [e1, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (ha j)).trans (norm_term_sub_le φ e hr j)
  unfold Cg
  rw [← sub_add_sub_cancel]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h2)

end GlobalTheory.KZ.Cmp.RiemannDirac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterTwistedSumCongrGaussSumDirac
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

noncomputable section

namespace GlobalTheory.KZ.Cmp.ChD

variable {l : ℕ} [Fact l.Prime]

theorem sum_units_eq_sum {N : ℕ} [NeZero N] (ψ : DirichletCharacter (Qbar l) N) (f : ZMod N → Qbar l) :
    ∑ b : (ZMod N)ˣ, ψ b * f b = ∑ a : ZMod N, ψ a * f a := by
  refine Fintype.sum_of_injective (fun b : (ZMod N)ˣ => (b : ZMod N)) Units.val_injective _ _ ?_ (fun b => rfl)
  intro a ha
  have : ¬ IsUnit a := fun hu => ha ⟨hu.unit, rfl⟩
  rw [MulChar.map_nonunit ψ this, zero_mul]

theorem norm_apply_unit_le_one {N : ℕ} [NeZero N] (ψ : DirichletCharacter (Qbar l) N) (b : (ZMod N)ˣ) :
    ‖ψ b‖ ≤ 1 := by
  have h : (ψ b) ^ (Fintype.card (ZMod N)ˣ) = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
  have h1 := congrArg norm h
  rw [norm_pow, norm_one] at h1
  exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) Fintype.card_ne_zero).1 h1).le

theorem sum_units_char_pow (m : ℕ) (hm : 1 ≤ m) (z : Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m))
    (hz : IsPrimitiveRoot z (l ^ m)) (hψ : ψ.IsPrimitive) (j : ℕ) :
    ∑ b : (ZMod (l ^ m))ˣ, ψ b * (z ^ (b : ZMod (l ^ m)).val) ^ j = ψ⁻¹ (j : ZMod (l ^ m)) * gSum m z ψ := by
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have key := GlobalTheory.EisM.sum_primChar_mul_rootPow_mod_pow (Qbar l) l m m z ψ (Fact.out) hm le_rfl hz hψ (j : ℤ)
  simp only [Nat.sub_self, pow_zero, one_dvd, if_true, one_mul, Int.ediv_one, Int.cast_natCast] at key
  rw [sum_units_eq_sum ψ (fun a => (z ^ a.val) ^ j)]
  unfold gSum
  rw [sum_units_eq_sum ψ (fun a => z ^ a.val)]
  have e1 : ∑ a : ZMod (l ^ m), ψ a * (z ^ a.val) ^ j =
      ∑ r : ZMod (l ^ m), ψ ((r.val : ℕ) : ZMod (l ^ m)) * z ^ ((r.val : ℤ) * (j : ℤ)) := by
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [ZMod.natCast_zmod_val, ← Nat.cast_mul, zpow_natCast, pow_mul]
  rw [e1, key, mul_comm]

theorem chSum_gauss : ∀ (l : ℕ) [Fact l.Prime] (F : PowerSeries (Qbar l)) (a : ℕ → Qbar l) (N m : ℕ) (z : Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m)), 1 ≤ m → l ^ (3 * m) ≤ N → (∀ n, ‖F.coeff n‖ ≤ 1) → (∀ y : Qbar l, tval F N y = ∑ j ∈ Finset.range N, a j * y ^ j) → IsPrimitiveRoot z (l ^ m) → ψ.IsPrimitive → Cg (2 * m) (chSum F m z ψ) (gSum m z ψ * ∑ j ∈ Finset.range N, a j * ψ⁻¹ (j : ZMod (l ^ m))) := by
  intro l _ F a N m z ψ hm hN hF htv hz hψ
  have hl := (Fact.out : l.Prime)
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hex : gSum m z ψ * ∑ j ∈ Finset.range N, a j * ψ⁻¹ (j : ZMod (l ^ m)) =
      ∑ b : (ZMod (l ^ m))ˣ, ψ b * tval F N (z ^ (b : ZMod (l ^ m)).val) := by
    simp_rw [htv, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e : ∑ b : (ZMod (l ^ m))ˣ, ψ b * (a j * (z ^ (b : ZMod (l ^ m)).val) ^ j) =
        a j * ∑ b : (ZMod (l ^ m))ˣ, ψ b * (z ^ (b : ZMod (l ^ m)).val) ^ j := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e, sum_units_char_pow m hm z ψ hz hψ j]
    ring
  unfold Cg
  rw [hex]
  unfold chSum
  rw [← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun b _ => ?_
  rw [← mul_sub, norm_mul]
  refine (mul_le_of_le_one_left (norm_nonneg _) (norm_apply_unit_le_one ψ b)).trans ?_
  have hy : (z ^ (b : ZMod (l ^ m)).val) ^ (l ^ m) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hz.pow_eq_one, one_pow]
  have hy1 := GlobalTheory.AmiceDist.norm_sub_one_le hy
  have hy3 := GlobalTheory.AmiceDist.norm_sub_one_pow_three_le hy
  unfold tval
  rw [← Finset.sum_range_add_sum_Ico _ hN, sub_add_cancel_left, norm_neg]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun n hn => ?_
  rw [norm_mul, norm_pow]
  exact (mul_le_of_le_one_left (by positivity) (hF n)).trans
    ((pow_le_pow_of_le_one (norm_nonneg _) hy1 (Finset.mem_Ico.1 hn).1).trans hy3)

end GlobalTheory.KZ.Cmp.ChD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductUnramifiedClassesVanishes
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.UnrCup

theorem ident_c {l : ℕ} [Fact l.Prime] (ar as ars bs bt bst : Fin 2 → Qbar l) (P M N : Matrix (Fin 2) (Fin 2) (Qbar l)) (e : Qbar l)
    (key : om (P *ᵥ as) (M *ᵥ (N *ᵥ bt)) = e * om as (N *ᵥ bt)) :
    (e * om as (N *ᵥ bt) + om ar (M *ᵥ bst)) - (om ars (M *ᵥ (N *ᵥ bt)) + om ar (M *ᵥ bs)) =
      om ar (M *ᵥ (bst - (bs + N *ᵥ bt))) - om (ars - (ar + P *ᵥ as)) (M *ᵥ (N *ᵥ bt)) := by
  simp only [om, Matrix.mulVec_sub, Matrix.mulVec_add, Pi.sub_apply, Pi.add_apply] at *
  linear_combination -key

theorem inv_ine : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (n : ℕ) (V : R2 Ω l) (H I : Subgroup (G ℚ Ω)) (a : G ℚ Ω → Fin 2 → Qbar l), (∀ s i j, mat V s i j ∈ c.O) → I ≤ H → (∀ s ∈ H, ∀ i ∈ I, s⁻¹ * i * s ∈ I) → Coc1 c n V H a → (∀ i ∈ I, Cv n (a i) 0) → ∀ s ∈ H, ∀ i ∈ I, Cv n (a (s * i)) (a s) ∧ Cv n (mat V i *ᵥ a s) (a s) := by
  intro l _ Ω _ _ c n V H I a hint hIH hconj ha ha0
  have hVn : ∀ g i j, ‖mat V g i j‖ ≤ 1 := fun g i j => CupCob.norm_le_one_of_mem c (hint g i j)
  have small : ∀ g, ∀ i ∈ I, ∀ j, ‖(mat V g *ᵥ a i) j‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := fun g i hi =>
    CupCob.mulVec_le _ _ (hVn g) (fun k => by have := ha0 i hi k; unfold Cg at this; simpa using this)
  have first : ∀ s ∈ H, ∀ i ∈ I, Cv n (a (s * i)) (a s) := by
    intro s hs i hi j
    have h1 := ha.2.2 s hs i (hIH hi) j
    unfold Cg at h1 ⊢
    have e : a (s * i) j - a s j = (a (s * i) j - (a s + mat V s *ᵥ a i) j) + (mat V s *ᵥ a i) j := by
      simp only [Pi.add_apply]; ring
    rw [e]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 (small s i hi j))
  intro s hs i hi
  refine ⟨first s hs i hi, fun j => ?_⟩
  have hi' : s⁻¹ * i * s ∈ I := hconj s hs i hi
  have e1 : i * s = s * (s⁻¹ * i * s) := by group
  have h1 := ha.2.2 i (hIH hi) s hs j
  have h2 := first s hs _ hi' j
  have h3 := ha0 i hi j
  unfold Cg at h1 h2 h3 ⊢
  rw [e1] at h1
  have e : (mat V i *ᵥ a s) j - a s j = -(a (s * (s⁻¹ * i * s)) j - (a i + mat V i *ᵥ a s) j) - (a i j - (0 : Fin 2 → Qbar l) j) + (a (s * (s⁻¹ * i * s)) j - a s j) := by
    simp only [Pi.add_apply, Pi.zero_apply]; ring
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((CupCob.nsub_le_max _ _).trans (max_le (by rw [norm_neg]; exact h1) h3)) h2)

theorem cup_coc : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (n : ℕ) (W : R2 Ω l) (H : Subgroup (G ℚ Ω)) (a b : G ℚ Ω → Fin 2 → Qbar l), (∀ s i j, mat W s i j ∈ c.O) → dt W ^ 2 = 1 → Coc1 c n W H a → Coc1 c n (dual1 W) H b → ∀ r ∈ H, ∀ s ∈ H, ∀ t ∈ H, Cg n (eps l r * cup W a b s t + cup W a b r (s * t)) (cup W a b (r * s) t + cup W a b r s) := by
  intro l _ Ω _ _ c n W H a b hint hdet ha hb r hr s hs t ht
  have hDm := CupCob.dual_representation_integral c W hdet hint
  have hDn : ∀ g i j, ‖mat (dual1 W) g i j‖ ≤ 1 := fun g i j => CupCob.norm_le_one_of_mem c (hDm g i j)
  have key := CupCob.om_key W hdet r (a s) (mat (dual1 W) s *ᵥ b t)
  unfold Cg
  simp only [cup]
  rw [CupCob.mat_dual1_mul W r s (b t), ident_c (a r) (a s) (a (r * s)) (b s) (b t) (b (s * t)) (mat W r)
    (mat (dual1 W) r) (mat (dual1 W) s) (eps l r) key]
  refine (CupCob.nsub_le_max _ _).trans (max_le ?_ ?_)
  · exact CupCob.om_le_right _ _ (fun i => CupCob.norm_le_one_of_mem c (ha.2.1 r i))
      (CupCob.mulVec_le _ _ (hDn r) (fun i => hb.2.2 s hs t ht i))
  · exact CupCob.om_le_left _ _ (fun i => ha.2.2 r hr s hs i) (CupCob.mulVec_le _ _ (hDn r)
      (CupCob.mulVec_le _ _ (hDn s) (fun i => CupCob.norm_le_one_of_mem c (hb.2.1 t i))))

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem cg_add {n : ℕ} {a b a' b' : Qbar l} (h : Cg n a b) (h' : Cg n a' b') : Cg n (a + a') (b + b') := by
  unfold Cg at *
  have e : a + a' - (b + b') = (a - b) + (a' - b') := by ring
  rw [e]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h h')

theorem cv_sub {n : ℕ} {a b a' b' : Fin 2 → Qbar l} (h : Cv n a b) (h' : Cv n a' b') : Cv n (a - a') (b - b') := by
  intro i
  unfold Cg at *
  have e : (a - a') i - (b - b') i = (a i - b i) - (a' i - b' i) := by simp only [Pi.sub_apply]; ring
  rw [e]; exact (CupCob.nsub_le_max _ _).trans (max_le (h i) (h' i))

theorem isIntegralCoboundaryTwoModPow_add (c : Coef l) (n : ℕ) (H : Subgroup (G ℚ Ω)) (ξ ξ' : G ℚ Ω → G ℚ Ω → Qbar l)
    (h : Cob2 c n H ξ) (h' : Cob2 c n H ξ') : Cob2 c n H (fun s t => ξ s t + ξ' s t) := by
  obtain ⟨u, hu, hui, hu'⟩ := h
  obtain ⟨v, hv, hvi, hv'⟩ := h'
  refine ⟨fun s => u s + v s, hu.add hv, fun s => add_mem (hui s) (hvi s), fun s hs t ht => ?_⟩
  have := cg_add (hu' s hs t ht) (hv' s hs t ht)
  convert this using 1; ring

theorem isIntegralCocycleOneModPow_sub (c : Coef l) (n : ℕ) (V : R2 Ω l) (H : Subgroup (G ℚ Ω)) (a a' : G ℚ Ω → Fin 2 → Qbar l)
    (h : Coc1 c n V H a) (h' : Coc1 c n V H a') : Coc1 c n V H (fun s => a s - a' s) := by
  refine ⟨h.1.sub h'.1, fun s i => sub_mem (h.2.1 s i) (h'.2.1 s i), fun s hs t ht => ?_⟩
  have := cv_sub (h.2.2 s hs t ht) (h'.2.2 s hs t ht)
  intro i
  convert this i using 2
  simp only [Pi.sub_apply, Pi.add_apply, Matrix.mulVec_sub]; ring

theorem isIntegralCocycleOneModPow_coboundary (c : Coef l) (n : ℕ) (V : R2 Ω l) (H : Subgroup (G ℚ Ω)) (x : Fin 2 → Qbar l)
    (hV : Continuous fun s => mat V s) (hint : ∀ s i j, mat V s i j ∈ c.O) (hx : ∀ i, x i ∈ c.O) :
    Coc1 c n V H (fun s => mat V s *ᵥ x - x) := by
  refine ⟨(hV.matrix_mulVec continuous_const).sub continuous_const |>.continuousOn,
    fun s i => sub_mem (CupCob.mulVec_mem c _ _ (hint s) hx i) (hx i), fun s _ t _ i => ?_⟩
  have e : (mat V (s * t) *ᵥ x - x) i = ((mat V s *ᵥ x - x) + mat V s *ᵥ (mat V t *ᵥ x - x)) i := by
    simp only [mat, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, Matrix.mulVec_sub, Pi.add_apply, Pi.sub_apply]; ring
  unfold Cg; dsimp only; rw [e, sub_self, norm_zero]; exact norm_nonneg _

theorem om_cg (c : Coef l) (n : ℕ) (A A' B B' : Fin 2 → Qbar l) (M : Matrix (Fin 2) (Fin 2) (Qbar l))
    (hA : ∀ i, A i ∈ c.O) (hB' : ∀ i, B' i ∈ c.O) (hM : ∀ i j, M i j ∈ c.O)
    (h1 : Cv n A' A) (h2 : Cv n B' B) : Cg n (om A' (M *ᵥ B')) (om A (M *ᵥ B)) := by
  have hMn : ∀ i j, ‖M i j‖ ≤ 1 := fun i j => CupCob.norm_le_one_of_mem c (hM i j)
  unfold Cg
  have e : om A' (M *ᵥ B') - om A (M *ᵥ B) = om (A' - A) (M *ᵥ B') + om A (M *ᵥ (B' - B)) := by
    simp only [om, Matrix.mulVec_sub, Pi.sub_apply]; ring
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · exact CupCob.om_le_left _ _ (fun i => h1 i) (CupCob.mulVec_le _ _ hMn (fun i => CupCob.norm_le_one_of_mem c (hB' i)))
  · exact CupCob.om_le_right _ _ (fun i => CupCob.norm_le_one_of_mem c (hA i))
      (CupCob.mulVec_le _ _ hMn (fun i => by simpa [Cg] using h2 i))

theorem mat_dual1_cont (W : R2 Ω l) (hW : Continuous W) (hdet : dt W ^ 2 = 1) :
    Continuous fun s => mat (dual1 W) s := by
  have hM : Continuous fun s => mat W s := Units.continuous_val.comp hW
  have : (fun s => mat (dual1 W) s) = fun s => (eps l s * (mat W s).det) • mat W s := funext (CupCob.mat_dual1 W hdet)
  rw [this]
  exact (CupCob.eps_cont.mul hM.matrix_det).smul hM

theorem cup_unr_cob_of_vanish [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (W : R2 Ω l) (q : Pl) (B : ValuationSubring Ω)
    (a b : G ℚ Ω → Fin 2 → Qbar l) (hW : Continuous W) (hint : ∀ s i j, mat W s i j ∈ c.O) (hdet : dt W ^ 2 = 1)
    (hB : IsPlaceOver B q) (hl : ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal)
    (ha : Coc1 c n W (Dec (F := ℚ) B) a) (hb : Coc1 c n (dual1 W) (Dec (F := ℚ) B) b)
    (ha0 : ∀ i ∈ Ine (F := ℚ) B, Cv n (a i) 0) (hb0 : ∀ i ∈ Ine (F := ℚ) B, Cv n (b i) 0) :
    Cob2 c n (Dec (F := ℚ) B) (cup W a b) := by
  set D := Dec (F := ℚ) B with hD
  set I := Ine (F := ℚ) B with hI
  have hID : I ≤ D := Ine_le_Dec B
  have hconj : ∀ s ∈ D, ∀ i ∈ I, s⁻¹ * i * s ∈ I := fun s hs i hi => by
    have := conj_mem_Ine (D.inv_mem hs) hi
    simpa using this
  have hDm : ∀ s i j, mat (dual1 W) s i j ∈ c.O := CupCob.dual_representation_integral c W hdet hint
  have hia := inv_ine l Ω c n W D I a hint hID hconj ha ha0
  have hib := inv_ine l Ω c n (dual1 W) D I b hDm hID hconj hb hb0
  have hξint : ∀ s t, cup W a b s t ∈ c.O := fun s t =>
    CupCob.om_mem c _ _ (ha.2.1 s) (CupCob.mulVec_mem c _ _ (hDm s) (hb.2.1 t))
  have hepsI : ∀ i ∈ I, eps l i = 1 := fun i hi => by
    have h := cyc_eq_one_of_mem_Ine (F := ℚ) (l := l) hl hB hi
    show ((cycBar ℚ Ω l i : (Qbar l)ˣ) : Qbar l) = 1
    rw [show cycBar ℚ Ω l i = cyc ℚ Ω l i from rfl, h]; rfl
  have hbiI : ∀ s ∈ D, ∀ t ∈ D, ∀ i ∈ I, Cg n (cup W a b (s * i) t) (cup W a b s t) ∧
      Cg n (cup W a b s (t * i)) (cup W a b s t) := by
    intro s hs t ht i hi
    constructor
    · simp only [cup]
      rw [CupCob.mat_dual1_mul W s i (b t)]
      exact om_cg c n _ _ _ _ _ (ha.2.1 s) (fun j => CupCob.mulVec_mem c _ _ (hDm i) (hb.2.1 t) j) (hDm s)
        (hia s hs i hi).1 (hib t ht i hi).2
    · simp only [cup]
      exact om_cg c n _ _ _ _ _ (ha.2.1 s) (hb.2.1 _) (hDm s) (fun j => by simp [Cg]) (hib t ht i hi).1
  have hcont : ContinuousOn (fun p : G ℚ Ω × G ℚ Ω => cup W a b p.1 p.2) ((D : Set (G ℚ Ω)) ×ˢ (D : Set (G ℚ Ω))) := by
    have h1 : ContinuousOn (fun p : G ℚ Ω × G ℚ Ω => a p.1) ((D : Set (G ℚ Ω)) ×ˢ (D : Set (G ℚ Ω))) :=
      ha.1.comp continuousOn_fst (fun p hp => hp.1)
    have h2 : ContinuousOn (fun p : G ℚ Ω × G ℚ Ω => b p.2) ((D : Set (G ℚ Ω)) ×ˢ (D : Set (G ℚ Ω))) :=
      hb.1.comp continuousOn_snd (fun p hp => hp.2)
    have hm : ∀ i j, ContinuousOn (fun p : G ℚ Ω × G ℚ Ω => mat (dual1 W) p.1 i j) ((D : Set (G ℚ Ω)) ×ˢ (D : Set (G ℚ Ω))) :=
      fun i j => (((continuous_apply j).comp (continuous_apply i)).comp ((mat_dual1_cont W hW hdet).comp continuous_fst)).continuousOn
    have h1' := continuousOn_pi.1 h1
    have h2' := continuousOn_pi.1 h2
    have h3' : ∀ i, ContinuousOn (fun p : G ℚ Ω × G ℚ Ω => mat (dual1 W) p.1 i 0 * b p.2 0 + mat (dual1 W) p.1 i 1 * b p.2 1)
        ((D : Set (G ℚ Ω)) ×ˢ (D : Set (G ℚ Ω))) := fun i => ((hm i 0).mul (h2' 0)).add ((hm i 1).mul (h2' 1))
    have e : (fun p : G ℚ Ω × G ℚ Ω => cup W a b p.1 p.2) = fun p => a p.1 0 * (mat (dual1 W) p.1 1 0 * b p.2 0 + mat (dual1 W) p.1 1 1 * b p.2 1) - a p.1 1 * (mat (dual1 W) p.1 0 0 * b p.2 0 + mat (dual1 W) p.1 0 1 * b p.2 1) := by
      funext p; simp only [cup, om, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [e]
    exact ((h1' 0).mul (h3' 1)).sub ((h1' 1).mul (h3' 0))
  obtain ⟨K, hIK, hKD, hKo, hepsK, hbiK⟩ := _root_.GlobalTheory.Ord2.OpenInv.open_inv l Ω n D I (cup W a b) (isClosed_Dec B) hID hcont hepsI hbiI
  obtain ⟨φ, m, hm, hφm, hd⟩ := GlobalTheory.T.exists_frobenius_pow_inv_mul_mem_open_subgroup Ω q B K hB hIK hKo
  obtain ⟨d, hdo, hdK⟩ := hd (l ^ n) (pow_pos (Fact.out : l.Prime).pos n)
  exact GlobalTheory.T.cob2_of_cocycle_cong_of_invariant l Ω c n D K φ m d (cup W a b) hm hφm hdo hdK hepsK hξint
    (cup_coc l Ω c n W D a b hint hdet ha hb) hbiK

theorem cup_unr_cob : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (W : R2 Ω l) (q : Pl) (B : ValuationSubring Ω) (a b : G ℚ Ω → Fin 2 → Qbar l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → dt W ^ 2 = 1 → IsPlaceOver B q → ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → Coc1 c n W (Dec (F := ℚ) B) a → Coc1 c n (dual1 W) (Dec (F := ℚ) B) b → Cob1 c n W (Ine (F := ℚ) B) a → Cob1 c n (dual1 W) (Ine (F := ℚ) B) b → Cob2 c n (Dec (F := ℚ) B) (cup W a b) := by
  intro _ l _ Ω _ _ _ c n W q B a b hW hint hdet hB hl ha hb ⟨x, hx, hax⟩ ⟨y, hy, hby⟩
  have hDm : ∀ s i j, mat (dual1 W) s i j ∈ c.O := CupCob.dual_representation_integral c W hdet hint
  have hMc : Continuous fun s => mat W s := Units.continuous_val.comp hW
  set a0 : G ℚ Ω → Fin 2 → Qbar l := fun s => mat W s *ᵥ x - x with ha0def
  set b0 : G ℚ Ω → Fin 2 → Qbar l := fun s => mat (dual1 W) s *ᵥ y - y with hb0def
  have ha0 : Coc1 c n W (Dec (F := ℚ) B) a0 := isIntegralCocycleOneModPow_coboundary c n W _ x hMc hint hx
  have hb0 : Coc1 c n (dual1 W) (Dec (F := ℚ) B) b0 := isIntegralCocycleOneModPow_coboundary c n (dual1 W) _ y (mat_dual1_cont W hW hdet) hDm hy
  have ha1 := isIntegralCocycleOneModPow_sub c n W _ a a0 ha ha0
  have hb1 := isIntegralCocycleOneModPow_sub c n (dual1 W) _ b b0 hb hb0
  have hsplit : cup W a b = fun s t => (cup W a0 b s t + cup W (fun s => a s - a0 s) b0 s t) +
      cup W (fun s => a s - a0 s) (fun s => b s - b0 s) s t := by
    funext s t; simp only [cup, om, Matrix.mulVec_sub, Pi.sub_apply]; ring
  have triv : ∀ (V : R2 Ω l) (z : Fin 2 → Qbar l), (∀ i, z i ∈ c.O) → Cob1 c n V (Dec (F := ℚ) B) (fun s => mat V s *ᵥ z - z) :=
    fun V z hz => ⟨z, hz, fun s _ i => by unfold Cg; rw [sub_self, norm_zero]; exact norm_nonneg _⟩
  have c1 := CupCob.cup_cob l Ω c n W _ a0 b hW hint hdet ha0 hb (Or.inl (triv W x hx))
  have c2 := CupCob.cup_cob l Ω c n W _ _ b0 hW hint hdet ha1 hb0 (Or.inr (triv (dual1 W) y hy))
  have c3 := cup_unr_cob_of_vanish c n W q B _ _ hW hint hdet hB hl ha1 hb1
    (fun i hi j => by
      have := hax i hi j; unfold Cg at this ⊢; simp only [Pi.sub_apply, Pi.zero_apply, sub_zero]; exact this)
    (fun i hi j => by
      have := hby i hi j; unfold Cg at this ⊢; simp only [Pi.sub_apply, Pi.zero_apply, sub_zero]; exact this)
  rw [hsplit]
  exact isIntegralCoboundaryTwoModPow_add c n _ _ _ (isIntegralCoboundaryTwoModPow_add c n _ _ _ c1 c2) c3

end GlobalTheory.Ord2.UnrCup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CyclotomicDvdOfAevalPrimitiveRootInertiaFixed
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

namespace GlobalTheory.RecOne.CycDvd

theorem apply_eq_pow (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (s : G ℚ Ω)
    {t : Ω} (ht : t ^ (l ^ n) = 1) : s t = t ^ ((cycMod ℚ Ω l n s : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)).val := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero (l : Ω) := ⟨by exact_mod_cast (Fact.out : l.Prime).ne_zero⟩
  have h1 := cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) t ht
  have h2 : (cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s)).val.toZModPow n =
      ((cycMod ℚ Ω l n s : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) := by
    simp [cycMod, cycZ]
  rw [h2] at h1
  exact h1

theorem exists_Ine_apply_eq (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) (n : ℕ) {z μ : Ω} (hz : IsPrimitiveRoot z (l ^ n))
    (hμ : IsPrimitiveRoot μ (l ^ n)) : ∃ s ∈ Ine (F := ℚ) A, s z = μ := by
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  haveI : NeZero (l ^ n) := ⟨hpos.ne'⟩
  obtain ⟨i, hi, hcop, rfl⟩ := (hz.isPrimitiveRoot_iff).1 hμ
  obtain ⟨⟨s, hs⟩, hsu⟩ := GlobalTheory.InertiaPowers.cycMod_Ine_surjective l Ω A hA n (ZMod.unitOfCoprime i hcop)
  refine ⟨s, hs, ?_⟩
  have hsu' : cycMod ℚ Ω l n s = ZMod.unitOfCoprime i hcop := hsu
  rw [apply_eq_pow l Ω n s hz.pow_eq_one, hsu', ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi]

theorem cyclotomic_dvd : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (n : ℕ) (z : A), IsPrimitiveRoot (z : Ω) (l ^ n) → ∀ R : Polynomial (fixA A), Polynomial.aeval z R = 0 → Polynomial.cyclotomic (l ^ n) (fixA A) ∣ R := by
  intro l _ Ω _ _ _ A hO n z hz R hR
  classical
  have hA : A.valuation (l : Ω) < 1 := by
    obtain ⟨v, hv, hl⟩ := hO
    have h1 := (hv ((l : ℕ) : 𝓞 ℚ)).2 hl
    simpa using h1
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  let f : fixA A →+* Ω := A.subtype.comp (fixA A).subtype
  have hf : Function.Injective f := Subtype.val_injective.comp Subtype.val_injective
  have h0 : Polynomial.eval₂ f (z : Ω) R = 0 := by
    have := Polynomial.hom_eval₂ R (algebraMap (fixA A) A) A.subtype z
    rw [← Polynomial.aeval_def, hR, map_zero] at this
    exact this.symm
  have hroot : ∀ μ ∈ primitiveRoots (l ^ n) Ω, (R.map f).eval μ = 0 := by
    intro μ hμ
    obtain ⟨s, hs, rfl⟩ := exists_Ine_apply_eq l Ω A hA n hz ((mem_primitiveRoots hpos).1 hμ)
    have e := Polynomial.hom_eval₂ R f (s : Ω →+* Ω) (z : Ω)
    have e2 : (s : Ω →+* Ω).comp f = f := RingHom.ext fun a => a.2 s hs
    rw [h0, map_zero, e2] at e
    rw [Polynomial.eval_map]
    exact e.symm
  rw [← Polynomial.map_dvd_map f hf (Polynomial.cyclotomic.monic _ _), Polynomial.map_cyclotomic,
    Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hz]
  refine Finset.prod_dvd_of_coprime ?_ ?_
  · intro a _ b _ hab
    exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.2 hab).isUnit
  · intro μ hμ
    exact Polynomial.dvd_iff_isRoot.2 (hroot μ hμ)

end GlobalTheory.RecOne.CycDvd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCocycleLocalConditionsStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cocycle_local_conditions : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (c : Coef l), (∀ s i j, mat W s i j ∈ c.O) → (∃ g, (mat W g - 1).det ≠ 0) → (∀ m : ℕ, ∃ (n : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l), Coc1 c n W ⊤ z ∧ (∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z a) 0) ∧ (∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ Cob1 c n W (Ine (F := ℚ) B) z) ∧ (∃ x ∈ c.O, ∀ s ∈ Dec (F := ℚ) A, Cg n (z s 1) (mat W s 1 1 * x - x)) ∧ ¬ Cob1 c n W ⊤ (fun s => ((l : ℕ) : Qbar l) ^ m • z s)) → ∀ m : ℕ, ∃ x : DivSel c W S A, l ^ m • x ≠ 0 := by
  first | exact @GlobalTheory.Ord2.Unbounded.divSel_unbounded | exact GlobalTheory.Ord2.Unbounded.divSel_unbounded | (intros; apply GlobalTheory.Ord2.Unbounded.divSel_unbounded <;> assumption)
end

