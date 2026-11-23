module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0569
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0571
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0503
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0357
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0360
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0537
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0559

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectorValueHighestWeightVector
section
open GlobalTheory.LeviCut

namespace GlobalTheory.LeviCut.StepScalarProof

variable {V : Type} [AddCommGroup V] [Module ℚ V]

theorem adj_apply' (x S : Module.End ℚ V) : adj x S = x * S - S * x := by
  simp [adj]

theorem H_pow (F H : Module.End ℚ V) (v : V) (n : ℕ)
    (hHF : H * F - F * H = -(F + F)) (hv : H v = (n : ℚ) • v) :
    ∀ i : ℕ, H ((F ^ i) v) = ((n : ℚ) - 2 * i) • (F ^ i) v := by
  have h1 : H * F = F * H - (F + F) := by
    calc H * F = (H * F - F * H) + F * H := by abel
      _ = F * H - (F + F) := by rw [hHF]; abel
  intro i
  induction i with
  | zero => simp [hv]
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply, ← Module.End.mul_apply (f := H), h1]
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, ih, map_smul]
    push_cast
    module

theorem E_pow (E F H : Module.End ℚ V) (v : V) (n : ℕ)
    (hEF : E * F - F * E = H) (hHF : H * F - F * H = -(F + F)) (hE : E v = 0) (hv : H v = (n : ℚ) • v) :
    ∀ i : ℕ, E ((F ^ (i + 1)) v) = (((i : ℚ) + 1) * ((n : ℚ) - i)) • (F ^ i) v := by
  have h1 : E * F = F * E + H := by
    calc E * F = (E * F - F * E) + F * E := by abel
      _ = F * E + H := by rw [hEF]; abel
  have hH := H_pow F H v n hHF hv
  intro i
  induction i with
  | zero =>
    rw [pow_one, ← Module.End.mul_apply (f := E), h1]
    simp [hE, hv]
  | succ i ih =>
    rw [pow_succ', Module.End.mul_apply, ← Module.End.mul_apply (f := E), h1]
    simp only [LinearMap.add_apply, Module.End.mul_apply, ih, map_smul, hH]
    rw [← Module.End.mul_apply (f := F), ← pow_succ']
    push_cast
    module

theorem adjE_pow (E F H T : Module.End ℚ V) (v : V) (n : ℕ)
    (hEF : E * F - F * E = H) (hHF : H * F - F * H = -(F + F)) (hE : E v = 0) (hv : H v = (n : ℚ) • v)
    (hT : ∀ k : ℕ, 0 < k → T ((F ^ k) v) = 0) :
    ∀ k : ℕ, (∀ i, k < i → (((adj E) ^ k) T) ((F ^ i) v) = 0) ∧
      (((adj E) ^ k) T) ((F ^ k) v) =
        ((-1 : ℚ) ^ k * (k.factorial : ℚ) * ∏ t ∈ Finset.range k, ((n : ℚ) - t)) • T v := by
  have hEp := E_pow E F H v n hEF hHF hE hv
  intro k
  induction k with
  | zero =>
    refine ⟨fun i hi => ?_, by simp⟩
    simpa using hT i hi
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hstep : ∀ y, (((adj E) ^ (k + 1)) T) y = E ((((adj E) ^ k) T) y) - (((adj E) ^ k) T) (E y) := by
      intro y
      rw [pow_succ', Module.End.mul_apply, adj_apply']
      simp [Module.End.mul_apply]
    refine ⟨fun i hi => ?_, ?_⟩
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [hstep, hEp, map_smul, ih1 i' (by omega), ih1 (i' + 1) (by omega)]
      simp
    · rw [hstep, hEp, map_smul, ih1 (k + 1) (by omega), ih2, smul_smul, Finset.prod_range_succ,
        Nat.factorial_succ]
      simp only [map_zero, zero_sub]
      rw [← neg_smul]
      congr 1
      push_cast
      ring

theorem phi_adjF_pow (F : Module.End ℚ V) (φ : V →ₗ[ℚ] ℚ) (hφ : ∀ x, φ (F x) = 0) :
    ∀ (k : ℕ) (S : Module.End ℚ V) (y : V), φ ((((adj F) ^ k) S) y) = (-1 : ℚ) ^ k * φ (S ((F ^ k) y)) := by
  intro k
  induction k with
  | zero => intro S y; simp
  | succ k ih =>
    intro S y
    rw [pow_succ, Module.End.mul_apply, ih, adj_apply']
    simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, hφ, zero_sub]
    rw [← Module.End.mul_apply (f := F), ← pow_succ', pow_succ]
    ring

theorem partial_sum (n j : ℕ) :
    ∀ K : ℕ, ((n : ℚ) + j + 1) * ∑ k ∈ Finset.range (K + 1),
        (-1 : ℚ) ^ k * (j.factorial : ℚ) * (∏ t ∈ Finset.range k, ((n : ℚ) - t)) / ((k + j + 1).factorial : ℚ) =
      1 + (-1 : ℚ) ^ K * (j.factorial : ℚ) * (∏ t ∈ Finset.range (K + 1), ((n : ℚ) - t)) /
        ((K + j + 1).factorial : ℚ) := by
  intro K
  induction K with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, pow_zero, Finset.prod_range_zero, one_mul, Finset.prod_range_one,
      Nat.cast_zero, sub_zero]
    rw [Nat.factorial_succ j]
    have h : (j.factorial : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  | succ K ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have e1 : K + 1 + j + 1 = (K + j + 1) + 1 := by ring
    rw [e1, Nat.factorial_succ (K + j + 1), Finset.prod_range_succ _ (K + 1)]
    have h : ((K + j + 1).factorial : ℚ) ≠ 0 := by positivity
    push_cast
    generalize ((K + j + 1).factorial : ℚ) = f at h ⊢
    generalize (∏ t ∈ Finset.range (K + 1), ((n : ℚ) - t)) = P
    field_simp
    ring

theorem stepScalar : StepScalar := by
  intro V _ _ E F H T v φ n K j hEF hHF hE hv hnK hφ hT
  have hA := adjE_pow E F H T v n hEF hHF hE hv hT
  have hB := phi_adjF_pow F φ hφ
  have hterm : ∀ k : ℕ, φ ((((adj F) ^ k * (adj E) ^ k) T) v) =
      (k.factorial : ℚ) * (∏ t ∈ Finset.range k, ((n : ℚ) - t)) * φ (T v) := by
    intro k
    rw [Module.End.mul_apply, hB, (hA k).2, map_smul, smul_eq_mul]
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
    simp
  have hP : ∏ t ∈ Finset.range (K + 1), ((n : ℚ) - t) = 0 :=
    Finset.prod_eq_zero (i := n) (Finset.mem_range.2 (by omega)) (sub_self _)
  have hS := partial_sum n j K
  simp only [hP, mul_zero, zero_div, add_zero] at hS
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [proj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, smul_eq_mul,
    hterm]
  have hc : ∀ k : ℕ, coef j k * ((k.factorial : ℚ) * (∏ t ∈ Finset.range k, ((n : ℚ) - t)) * φ (T v)) =
      (-1 : ℚ) ^ k * (j.factorial : ℚ) * (∏ t ∈ Finset.range k, ((n : ℚ) - t)) / ((k + j + 1).factorial : ℚ) *
        φ (T v) := by
    intro k
    have h1 : (k.factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((k + j + 1).factorial : ℚ) ≠ 0 := by positivity
    simp only [coef]
    field_simp
  simp only [hc, ← Finset.sum_mul]
  rw [mul_comm, ← mul_assoc, hS, one_mul]

end GlobalTheory.LeviCut.StepScalarProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOneProjectorWeightZeroInvariance
section
open GlobalTheory.LeviCut

namespace GlobalTheory.LeviCut

namespace RankOnePf

variable {W : Type} [AddCommGroup W] [Module ℚ W]

theorem rankOne_H_X_pow (X H : Module.End ℚ W) (hHX : ∀ w, H (X w) = X (H w) + (2 : ℚ) • X w)
    (k : ℕ) (w : W) : H ((X ^ k) w) = (X ^ k) (H w) + ((2 * k : ℕ) : ℚ) • (X ^ k) w := by
  induction k generalizing w with
  | zero => simp
  | succ k ih =>
    simp only [pow_succ, Module.End.mul_apply]
    rw [ih, hHX, map_add (f := _), map_smul]
    push_cast
    module

theorem rankOne_H_Y_pow (Y H : Module.End ℚ W) (hHY : ∀ w, H (Y w) = Y (H w) - (2 : ℚ) • Y w)
    (k : ℕ) (w : W) : H ((Y ^ k) w) = (Y ^ k) (H w) - ((2 * k : ℕ) : ℚ) • (Y ^ k) w := by
  induction k generalizing w with
  | zero => simp
  | succ k ih =>
    simp only [pow_succ, Module.End.mul_apply]
    rw [ih, hHY, map_sub, map_smul]
    push_cast
    module

theorem rankOne_X_Y_pow (X Y H : Module.End ℚ W) (hXY : ∀ w, X (Y w) = Y (X w) + H w)
    (hHY : ∀ w, H (Y w) = Y (H w) - (2 : ℚ) • Y w) (k : ℕ) (w : W) :
    X ((Y ^ (k + 1)) w) = (Y ^ (k + 1)) (X w) + ((k + 1 : ℕ) : ℚ) • (Y ^ k) (H w)
      - (((k + 1) * k : ℕ) : ℚ) • (Y ^ k) w := by
  induction k generalizing w with
  | zero => simp [hXY]
  | succ k ih =>
    have h1 : (Y ^ (k + 1 + 1)) w = (Y ^ (k + 1)) (Y w) := by
      rw [pow_succ Y (k + 1), Module.End.mul_apply]
    rw [h1, ih, hXY, hHY]
    simp only [map_add (f := _), map_sub, map_smul, pow_succ, Module.End.mul_apply]
    push_cast
    module

theorem rankOne_coef_succ (n : ℕ) :
    coef 0 (n + 1) * (((n + 1) * (n + 1 + 1) : ℕ) : ℚ) = - coef 0 n := by
  have h1 : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  simp only [coef, Nat.factorial_succ, add_zero, Nat.factorial_zero]
  push_cast
  field_simp
  ring

end RankOnePf

end GlobalTheory.LeviCut

namespace GlobalTheory.LeviCut


open RankOnePf in
theorem rankOne : RankOne := by
  intro W _ _ N K D hG hB o q ho hq hoq T hoT hqT
  have hqo : q ≠ o := Ne.symm hoq
  have hH : ∀ x, (D o o - D q q) x = D o o x - D q q x := fun x => rfl
  have hHT : (D o o - D q q) T = 0 := by rw [hH, hoT, hqT, sub_zero]
  have hXY : ∀ w, D o q (D q o w) = D q o (D o q w) + (D o o - D q q) w := by
    intro w
    have e := LinearMap.congr_fun (hG o q q o ho hq hq ho) w
    rw [if_pos (rfl : q = q), if_pos (rfl : o = o)] at e
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at e
    rw [hH]
    exact sub_eq_iff_eq_add'.mp e
  have hHX : ∀ w, (D o o - D q q) (D o q w) = D o q ((D o o - D q q) w) + (2 : ℚ) • D o q w := by
    intro w
    have e1 := LinearMap.congr_fun (hG o o o q ho ho ho hq) w
    rw [if_pos (rfl : o = o), if_neg hqo] at e1
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply, sub_zero] at e1
    have e2 := LinearMap.congr_fun (hG q q o q hq hq ho hq) w
    rw [if_neg hqo, if_pos (rfl : q = q)] at e2
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply, zero_sub, LinearMap.neg_apply] at e2
    rw [hH, hH, map_sub, sub_eq_iff_eq_add'.mp e1, sub_eq_iff_eq_add'.mp e2]
    module
  have hHY : ∀ w, (D o o - D q q) (D q o w) = D q o ((D o o - D q q) w) - (2 : ℚ) • D q o w := by
    intro w
    have e1 := LinearMap.congr_fun (hG o o q o ho ho hq ho) w
    rw [if_neg hoq, if_pos (rfl : o = o)] at e1
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply, zero_sub, LinearMap.neg_apply] at e1
    have e2 := LinearMap.congr_fun (hG q q q o hq hq hq ho) w
    rw [if_pos (rfl : q = q), if_neg hoq] at e2
    simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.zero_apply, sub_zero] at e2
    rw [hH, hH, map_sub, sub_eq_iff_eq_add'.mp e1, sub_eq_iff_eq_add'.mp e2]
    module
  constructor
  ·
    have hterm : ∀ m : ℕ, D o q ((D q o ^ (m + 1)) ((D o q ^ (m + 1)) T)) =
        (D q o ^ (m + 1)) ((D o q ^ (m + 1 + 1)) T) +
          (((m + 1) * (m + 1 + 1) : ℕ) : ℚ) • (D q o ^ m) ((D o q ^ (m + 1)) T) := by
      intro m
      have hx : D o q ((D o q ^ (m + 1)) T) = (D o q ^ (m + 1 + 1)) T := by
        rw [pow_succ' (D o q) (m + 1), Module.End.mul_apply]
      rw [rankOne_X_Y_pow _ _ _ hXY hHY, rankOne_H_X_pow _ _ hHX, hHT, map_zero, zero_add, hx,
        map_smul]
      push_cast
      module
    have hsum : ∀ n : ℕ, D o q (∑ k ∈ Finset.range (n + 1), coef 0 k • (D q o ^ k) ((D o q ^ k) T)) =
        coef 0 n • (D q o ^ n) ((D o q ^ (n + 1)) T) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, map_add (f := _), ih, map_smul, hterm n]
        have hc := rankOne_coef_succ n
        rw [show coef 0 n = -(coef 0 (n + 1) * (((n + 1) * (n + 1 + 1) : ℕ) : ℚ)) by rw [hc, neg_neg]]
        module
    have hXK : (D o q ^ (K + 1)) T = 0 := by
      refine hB o ho q hq ((2 * (K + 1) : ℕ) : ℤ) _ ?_ (by push_cast; omega)
      have h := rankOne_H_X_pow _ _ hHX (K + 1) T
      rw [hHT, map_zero, zero_add, hH] at h
      rw [Int.cast_natCast]
      exact h
    have hp : proj K 0 (D o q) (D q o) T =
        ∑ k ∈ Finset.range (K + 1), coef 0 k • (D q o ^ k) ((D o q ^ k) T) := by
      simp only [proj, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
    rw [hp, hsum K, hXK, map_zero, smul_zero]
  ·
    intro hXT
    have hYterm : ∀ k : ℕ, D o q ((D q o ^ (k + 1)) T) = -((((k + 1) * k : ℕ) : ℚ)) • (D q o ^ k) T := by
      intro k
      rw [rankOne_X_Y_pow _ _ _ hXY hHY, hXT, hHT, map_zero, map_zero, smul_zero, add_zero, zero_sub,
        neg_smul]
    have hYK : (D q o ^ (K + 1)) T = 0 := by
      refine hB q hq o ho ((2 * (K + 1) : ℕ) : ℤ) _ ?_ (by push_cast; omega)
      have h := rankOne_H_Y_pow _ _ hHY (K + 1) T
      rw [hHT, map_zero, zero_sub, hH] at h
      rw [Int.cast_natCast, ← neg_sub, h, neg_neg]
    have hdesc : ∀ d i : ℕ, i + d = K → (D q o ^ (i + 1)) T = 0 := by
      intro d
      induction d with
      | zero =>
        intro i hi
        rw [add_zero] at hi
        subst hi
        exact hYK
      | succ d ih =>
        intro i hi
        have h2 := ih (i + 1) (by omega)
        have h3 := hYterm (i + 1)
        rw [h2, map_zero] at h3
        rcases smul_eq_zero.mp h3.symm with h | h
        · exfalso
          have : ((((i + 1 + 1) * (i + 1) : ℕ) : ℚ)) ≠ 0 := by positivity
          exact this (neg_eq_zero.mp h)
        · exact h
    have := hdesc K 0 (by omega)
    simpa using this

end GlobalTheory.LeviCut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFibreClassEqZeroOfSmulPullbackEqZero
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem isClosedImmersion_of_isPullback_surj {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'}
    (hσ : Function.Surjective σ) {Y Y' : Scheme.{0}} {q : Y ⟶ Sp R} {q' : Y' ⟶ Sp R'} {χ : Y' ⟶ Y}
    (k : IsPullback χ q' q (spMap σ)) : IsClosedImmersion χ := by
  have : IsClosedImmersion (spMap σ) := IsClosedImmersion.spec_of_surjective _ hσ
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) k.flip this

theorem tmul_pull_eq_zero : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)) (Y Y' Y₀ : Scheme.{0}) (q : Y ⟶ Sp R) (q' : Y' ⟶ Sp R') (q₀ : Y₀ ⟶ Sp R₀) (χ : Y' ⟶ Y) (χ₀ : Y₀ ⟶ Y) (k : IsPullback χ q' q (spMap σ)) (k₀ : IsPullback χ₀ q₀ q (spMap σ₀)) (ψ : Y ⟶ X) (ψ' : Y' ⟶ X') (ψ₀ : Y₀ ⟶ X₀) (w : ψ ≫ s = q ≫ spMap (RingHom.id R)) (w' : ψ' ≫ s' = q' ≫ spMap (RingHom.id R')) (w₀ : ψ₀ ≫ s₀ = q₀ ≫ spMap (RingHom.id R₀)), ψ' ≫ φ = χ ≫ ψ → ψ₀ ≫ φ₀ = χ₀ ≫ ψ → SmallExt t σ σ₀ → Flat s → Flat q → CohomZeroIsConstants (OAff q') → ∀ (u : HO1 s₀) (y : HO1 s), TMul h₀.w t u y → pullHO1 w y = 0 → pullHO1 w₀ u = 0 := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ Y Y' Y₀ q q' q₀ χ χ₀ k k₀ ψ ψ' ψ₀ w w' w₀
    _hψ' hψ₀ hE _hs hq hC u y hT hy
  obtain ⟨hσ, hker, hσ₀, hker₀⟩ := hE
  haveI : IsClosedImmersion χ := isClosedImmersion_of_isPullback_surj hσ k
  haveI : IsClosedImmersion χ₀ := isClosedImmersion_of_isPullback_surj hσ₀ k₀
  haveI : IsClosedImmersion φ₀ := isClosedImmersion_of_isPullback_surj hσ₀ h₀
  have ht : σ t = 0 := by rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self t
  obtain ⟨f, c, hcf, hcy, hred⟩ := hT

  have h1 : (pairPull w).pull1 y = 0 := by
    have e := isPullO_pullHO1 w y
    unfold IsPullO at e
    rw [e, hy, map_zero]
  rw [← hcy, CoefMap.pullCohomologyOne_class, GlobalTheory.CatCoh.H1.mk_eq_zero] at h1
  obtain ⟨g, hg⟩ := h1
  obtain ⟨f₁, hf₁⟩ : ∃ f₁ : C1 (OPair ψ q), ∀ T T' (a : T ⟶ T'),
      f₁ T T' a = (pairPull w).α T' (f _ _ ((pairPull w).G.map a)) := ⟨_, fun _ _ _ ↦ rfl⟩
  have hg' : ∀ (T T' : (Pair ψ)ᵒᵖ) (a : T ⟶ T'), g T' - mp (OPair ψ q) a (g T) = t • f₁ T T' a := by
    intro T T' a
    have e := congrFun (congrFun (congrFun hg T) T') a
    rw [amitsur_d0_apply, CoefMap.pullCocycleOne_apply] at e
    rw [e, hf₁, hcf, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, (pairPull w).smul, RingHom.id_apply]

  let gb : C0 (pairFst ψ ⋙ OPre χ q') := fun T ↦ preα χ q q' ((pairFst ψ).obj T) (g T)
  have hgb : d0 _ gb = 0 := by
    funext T T' a
    rw [amitsur_d0_apply]
    have nat : preα χ q q' _ (mp (OAff q) ((pairFst ψ).map a) (g T)) =
        mp (OPre χ q') ((pairFst ψ).map a) (preα χ q q' _ (g T)) := (preCoef k.w).naturality _ _
    change preα χ q q' _ (g T') - mp (OPre χ q') ((pairFst ψ).map a) (preα χ q q' _ (g T)) = 0
    rw [← nat]
    change preα χ q q' _ (g T') - preα χ q q' _ (mp (OPair ψ q) a (g T)) = 0
    have sm : ∀ U (r0 : R) b, preα χ q q' U (r0 • b) = σ r0 • preα χ q q' U b := (preCoef k.w).smul
    rw [← map_sub, hg', sm, ht, zero_smul]
  obtain ⟨r', hr', -⟩ := (_root_.GlobalTheory.AbCoh.pair_pre_bijective R' X Y Y' ψ χ q').2.2 hC gb hgb
  obtain ⟨r, rfl⟩ := hσ r'
  have hsec := GlobalTheory.T.surjective_deformation_affine_sections R R' R₀ t σ σ₀ Y Y' Y₀ q q' q₀ χ χ₀ k k₀ ⟨hσ, hker, hσ₀, hker₀⟩ hq
  have hex : ∀ T : (Pair ψ)ᵒᵖ, ∃ e, g T - algebraMap R _ r = t • e := by
    intro T
    refine ((hsec ((pairFst ψ).obj T)).2.1 _).1 ?_
    have e : preα χ q q' ((pairFst ψ).obj T) (algebraMap R ((OPair ψ q).obj T) r) =
        algebraMap R' ((pairFst ψ ⋙ OPre χ q').obj T) (σ r) :=
      SemiHom.map_algebraMap ((preCoef k.w).smul _) r
    rw [map_sub, e]
    exact sub_eq_zero.2 (hr' T)
  choose g₁ hg₁ using hex
  have hkill : ∀ (T T' : (Pair ψ)ᵒᵖ) (a : T ⟶ T'),
      t • (f₁ T T' a - (g₁ T' - mp (OPair ψ q) a (g₁ T))) = 0 := by
    intro T T' a
    rw [smul_sub, smul_sub, ← map_smul (mp (OPair ψ q) a), ← hg₁ T', ← hg₁ T, map_sub, AlgHom.commutes,
      ← hg' T T' a]
    abel

  obtain ⟨c₀, hc₀, hc₀'⟩ :=
    (_root_.GlobalTheory.AbCoh.red_preimage_pairs R R₀ σ₀ X X₀ Y Y₀ s s₀ q q₀ φ₀ χ₀ h₀.w ψ ψ₀ w w₀ hψ₀ inferInstance).1 f u hred
  have hz : (CoefMap.restrict (OAff q₀) (pairFst ψ ⋙ preAff χ₀)).pull1 (pullHO1 w₀ u) = 0 := by
    rw [← hc₀', GlobalTheory.CatCoh.H1.mk_eq_zero]
    refine ⟨fun T ↦ preα χ₀ q q₀ ((pairFst ψ).obj T) (g₁ T), ?_⟩
    funext T T' a
    rw [hc₀, amitsur_d0_apply, ← hf₁]
    have e1 := ((hsec ((pairFst ψ).obj T')).2.2.2 _).2 (hkill T T' a)
    rw [map_sub, map_sub, sub_eq_zero] at e1
    have nat : preα χ₀ q q₀ _ (mp (OAff q) ((pairFst ψ).map a) (g₁ T)) =
        mp (OPre χ₀ q₀) ((pairFst ψ).map a) (preα χ₀ q q₀ _ (g₁ T)) := (preCoef k₀.w).naturality _ _
    change _ - mp (OPre χ₀ q₀) ((pairFst ψ).map a) (preα χ₀ q q₀ _ (g₁ T)) = _
    rw [← nat]
    exact e1.symm
  exact (_root_.GlobalTheory.AbCoh.pair_pre_bijective R₀ X Y Y₀ ψ χ₀ q₀).1.1 (hz.trans (map_zero _).symm)

end GlobalTheory.AbCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShEqvTw
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem sh_eqv_tw : ∀ (q : ℕ) (i : ℤ) (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B), SH A → SH B → IsUnit (q : A) → Eqv _ (spMap φ) (tw q i) := by
  intro q i A B _ _ φ hA hB hq
  obtain ⟨hAl, _⟩ := hA
  obtain ⟨hBl, _⟩ := hB
  obtain ⟨ζ⟩ := GlobalTheory.T.nonempty_cyclotomicPrimitiveRoots_of_strictlyHenselian q A ⟨hAl, ‹_›⟩ hq
  let S : Scheme.{0} := Spec (CommRingCat.of A)
  let ζS : Prim q Γ(S, ⊤) := Prim.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ζ
  have hgen := GlobalTheory.T.tateTwist_isFreeRankOne_on_generatorSection q i S ζS
  have hac : ∀ (C : Type) [CommRing C], SH C → AcycF (ZMod q) (sch.obj (Spec (CommRingCat.of C))) (tw q i) :=
    fun C _ hC n hn => GlobalTheory.T.strictlyHenselianLocalRing_acyclic_every_sheaf (ZMod q) C hC (tw q i) n hn
  refine GlobalTheory.T.etaleCohomologyEquiv_of_locallyConstant_bijective (ZMod q) (tw q i) S (twGen i ζS) hgen S (Spec (CommRingCat.of B)) (𝟙 S)
    (Spec.map (CommRingCat.ofHom φ)) (hac A ⟨hAl, ‹_›⟩) (hac B ⟨hBl, ‹_›⟩) ?_
  have cA := GlobalTheory.T.locallyConstant_spec_localRing_const_bijective (ZMod q) A
  have cB := GlobalTheory.T.locallyConstant_spec_localRing_const_bijective (ZMod q) B
  have hcomp : (fun φ' : LocallyConstant S (ZMod q) => φ'.comap (Spec.map (CommRingCat.ofHom φ)).base.hom) ∘
      (fun c : ZMod q => LocallyConstant.const S c) = fun c => LocallyConstant.const _ c := by
    funext c; ext x; rfl
  refine (Function.Bijective.of_comp_iff _ cA).1 ?_
  rw [hcomp]
  exact cB
end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonInvariantDifferentialsOfEtale
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace PDivGroup

theorem subsingleton_omega_of_isEt : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (G : PDivGroup p k), G.IsEt → Subsingleton G.omega ∧ Subsingleton G.dual.dual.omega := by
  intro p _ k _ _ _ G hG
  have hp : (p : k) = 0 := CharP.cast_eq_zero k p
  have h1 : Subsingleton G.omega := by
    refine ⟨fun v w => ?_⟩
    have hz : ∀ u : G.omega, u = 0 := fun u => Subtype.ext (funext fun n => by
      haveI := hG n
      obtain ⟨a, ha⟩ := AugCot.d_surjective _ (u.1 n)
      obtain ⟨b, rfl⟩ := _root_.GlobalTheory.exists_pow_char_eq_of_isReduced_finite p k (G.A n) a
      rw [← ha]
      exact dUnit_pow_prime hp b)
    rw [hz v, hz w]
  refine ⟨h1, ?_⟩
  have hinj : Function.Injective (omegaMap G G.dual.dual G.bidual.hom) := by
    refine Function.LeftInverse.injective (g := omegaMap G.dual.dual G G.bidual.inv) fun x => ?_
    rw [← LinearMap.comp_apply, ← omegaMap_comp, Iso.inv_hom_id, omegaMap_id, LinearMap.id_apply]
  exact hinj.subsingleton

end PDivGroup

end GlobalTheory
end
end

