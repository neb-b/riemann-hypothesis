module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0536
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0527
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastAtEmbeddingRingOps
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)

namespace GlobalTheory.QFam.SzSum

section

variable {l : ℕ} [hl : Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]}

theorem sz_zero (r : ℝ) : Sz l lam r 0 := by
  refine ⟨zero_mem _, ?_⟩
  have : (⟨0, zero_mem _⟩ : algebraicClosure ℚ ℂ) = 0 := rfl
  rw [this, map_zero, norm_zero]
  positivity

theorem sz_add {r : ℝ} {x y : ℂ} (hx : Sz l lam r x) (hy : Sz l lam r y) : Sz l lam r (x + y) := by
  obtain ⟨hx, hx'⟩ := hx
  obtain ⟨hy, hy'⟩ := hy
  refine ⟨add_mem hx hy, ?_⟩
  have : (⟨x + y, add_mem hx hy⟩ : algebraicClosure ℚ ℂ) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
  rw [this, map_add (f := _)]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx' hy')

theorem sz_neg {r : ℝ} {x : ℂ} (hx : Sz l lam r x) : Sz l lam r (-x) := by
  obtain ⟨hx, hx'⟩ := hx
  refine ⟨neg_mem hx, ?_⟩
  have : (⟨-x, neg_mem hx⟩ : algebraicClosure ℚ ℂ) = -⟨x, hx⟩ := rfl
  rwa [this, map_neg, norm_neg]

theorem sz_sub {r : ℝ} {x y : ℂ} (hx : Sz l lam r x) (hy : Sz l lam r y) : Sz l lam r (x - y) := by
  rw [sub_eq_add_neg]
  exact sz_add hx (sz_neg hy)

theorem sz_mul {r s : ℝ} {x y : ℂ} (hx : Sz l lam r x) (hy : Sz l lam s y) : Sz l lam (r + s) (x * y) := by
  obtain ⟨hx, hx'⟩ := hx
  obtain ⟨hy, hy'⟩ := hy
  refine ⟨mul_mem hx hy, ?_⟩
  have : (⟨x * y, mul_mem hx hy⟩ : algebraicClosure ℚ ℂ) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [this, map_mul, norm_mul, Real.rpow_add (by exact_mod_cast hl.out.pos)]
  exact mul_le_mul hx' hy' (norm_nonneg _) (by positivity)

theorem sz_mono {r s : ℝ} {x : ℂ} (h : r ≤ s) (hx : Sz l lam r x) : Sz l lam s x := by
  obtain ⟨hx, hx'⟩ := hx
  exact ⟨hx, hx'.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hl.out.one_lt.le) h)⟩

theorem sz_int (n : ℤ) : Sz l lam 0 (n : ℂ) := by
  refine ⟨intCast_mem _ n, ?_⟩
  have : (⟨(n : ℂ), intCast_mem _ n⟩ : algebraicClosure ℚ ℂ) = (n : algebraicClosure ℚ ℂ) := Subtype.ext (by simp)
  rw [this, map_intCast, Real.rpow_zero]
  exact IsUltrametricDist.norm_intCast_le_one _ n

theorem sz_sum {κ : Type*} (t : Finset κ) {r : ℝ} {x : κ → ℂ} (h : ∀ k ∈ t, Sz l lam r (x k)) :
    Sz l lam r (∑ k ∈ t, x k) :=
  Finset.sum_induction x (Sz l lam r) (fun _ _ => sz_add) (sz_zero r) h

end

theorem sz_ring : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), (∀ r : ℝ, Sz l lam r 0) ∧ (∀ (r : ℝ) (x y : ℂ), Sz l lam r x → Sz l lam r y → Sz l lam r (x + y) ∧ Sz l lam r (x - y)) ∧ (∀ (r s : ℝ) (x y : ℂ), Sz l lam r x → Sz l lam s y → Sz l lam (r + s) (x * y)) ∧ (∀ (r s : ℝ) (x : ℂ), r ≤ s → Sz l lam r x → Sz l lam s x) ∧ (∀ n : ℤ, Sz l lam 0 (n : ℂ)) ∧ (∀ (κ : Type) (t : Finset κ) (r : ℝ) (x : κ → ℂ), (∀ k ∈ t, Sz l lam r (x k)) → Sz l lam r (∑ k ∈ t, x k)) :=
  fun _ _ _ => ⟨sz_zero, fun _ _ _ hx hy => ⟨sz_add hx hy, sz_sub hx hy⟩, fun _ _ _ _ hx hy => sz_mul hx hy,
    fun _ _ _ h hx => sz_mono h hx, sz_int, fun _ t _ _ h => sz_sum t h⟩

end GlobalTheory.QFam.SzSum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastBasicProperties
section
noncomputable section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F

namespace GlobalTheory.SzRules

variable {l : ℕ} [hl : Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]}

theorem norm_natCast_eq (n : ℕ) : ‖(n : ℂ_[l])‖ = ‖(n : ℚ_[l])‖ := by
  have h : (n : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (n : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']

theorem norm_le_one_of_isIntegral {y : ℂ_[l]} (hy : IsIntegral ℤ y) : ‖y‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.IntegralNormAtMostOne.norm_le_one_of_isIntegral
  | exact _root_.GlobalTheory.IntegralNormAtMostOne.norm_le_one_of_isIntegral
  | (apply _root_.GlobalTheory.IntegralNormAtMostOne.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralNormAtMostOne.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralNormAtMostOne.norm_le_one_of_isIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralNormAtMostOne.norm_le_one_of_isIntegral ..)

theorem mem_of_natCast_mul {n : ℕ} (hn : n ≠ 0) {x : ℂ} (h : (n : ℂ) * x ∈ algebraicClosure ℚ ℂ) :
    x ∈ algebraicClosure ℚ ℂ := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have := div_mem h (natCast_mem (algebraicClosure ℚ ℂ) n)
  rwa [mul_div_cancel_left₀ _ hn'] at this

theorem norm_natCast_mul (n : ℕ) {x : ℂ} (hx : x ∈ algebraicClosure ℚ ℂ) (h : (n : ℂ) * x ∈ algebraicClosure ℚ ℂ) :
    ‖lam ⟨(n : ℂ) * x, h⟩‖ = ‖(n : ℚ_[l])‖ * ‖lam ⟨x, hx⟩‖ := by
  have : (⟨(n : ℂ) * x, h⟩ : algebraicClosure ℚ ℂ) = (n : algebraicClosure ℚ ℂ) * ⟨x, hx⟩ := rfl
  rw [this, map_mul, map_natCast, norm_mul, norm_natCast_eq]

theorem sz_of_isIntegral (n : ℕ) (x : ℂ) (hn : ¬ l ∣ n) (h : IsIntegral ℤ ((n : ℂ) * x)) : Sz l lam 0 x := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero _)
  have hm : (n : ℂ) * x ∈ algebraicClosure ℚ ℂ := mem_algebraicClosure_iff'.2 h.tower_top
  have hx := mem_of_natCast_mul hn0 hm
  refine ⟨hx, ?_⟩
  have h1 : IsIntegral ℤ (⟨(n : ℂ) * x, hm⟩ : algebraicClosure ℚ ℂ) :=
    (isIntegral_algHom_iff (algebraicClosure ℚ ℂ).val.toRingHom.toIntAlgHom Subtype.val_injective).1 h
  have h2 : ‖lam ⟨(n : ℂ) * x, hm⟩‖ ≤ 1 :=
    norm_le_one_of_isIntegral (by convert map_isIntegral_int lam h1; exact Subsingleton.elim _ _)
  have h3 : ‖(n : ℚ_[l])‖ = 1 := by
    rw [Padic.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd hl.out).2 hn
  have h4 := norm_natCast_mul (lam := lam) n hx hm
  rw [h3, one_mul] at h4
  rw [Real.rpow_zero, ← h4]
  exact h2

theorem sz_add {r : ℝ} {x y : ℂ} (hx : Sz l lam r x) (hy : Sz l lam r y) : Sz l lam r (x + y) := by
  obtain ⟨hx, hx'⟩ := hx
  obtain ⟨hy, hy'⟩ := hy
  refine ⟨add_mem hx hy, ?_⟩
  have : (⟨x + y, add_mem hx hy⟩ : algebraicClosure ℚ ℂ) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
  rw [this, map_add (f := _)]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx' hy')

theorem sz_mul {r₁ r₂ : ℝ} {x y : ℂ} (hx : Sz l lam r₁ x) (hy : Sz l lam r₂ y) :
    Sz l lam (r₁ + r₂) (x * y) := by
  obtain ⟨hx, hx'⟩ := hx
  obtain ⟨hy, hy'⟩ := hy
  refine ⟨mul_mem hx hy, ?_⟩
  have : (⟨x * y, mul_mem hx hy⟩ : algebraicClosure ℚ ℂ) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [this, map_mul, norm_mul, Real.rpow_add (by exact_mod_cast hl.out.pos)]
  exact mul_le_mul hx' hy' (norm_nonneg _) (by positivity)

theorem sz_mono {r r' : ℝ} {x : ℂ} (h : r ≤ r') (hx : Sz l lam r x) : Sz l lam r' x := by
  obtain ⟨hx, hx'⟩ := hx
  exact ⟨hx, hx'.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hl.out.one_lt.le) h)⟩

theorem sz_neg {r : ℝ} {x : ℂ} (hx : Sz l lam r x) : Sz l lam r (-x) := by
  obtain ⟨hx, hx'⟩ := hx
  refine ⟨neg_mem hx, ?_⟩
  have : (⟨-x, neg_mem hx⟩ : algebraicClosure ℚ ℂ) = -⟨x, hx⟩ := rfl
  rwa [this, map_neg, norm_neg]

theorem sz_prime_mul (r : ℝ) (x : ℂ) : Sz l lam r ((l : ℂ) * x) ↔ Sz l lam (r + 1) x := by
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
  constructor
  · rintro ⟨h, h'⟩
    have hx := mem_of_natCast_mul hl.out.ne_zero h
    refine ⟨hx, ?_⟩
    rw [norm_natCast_mul l hx h, Padic.norm_p, inv_mul_le_iff₀ hl0] at h'
    rw [Real.rpow_add_one hl0.ne', mul_comm]
    exact h'
  · rintro ⟨hx, h'⟩
    have h : (l : ℂ) * x ∈ algebraicClosure ℚ ℂ := mul_mem (natCast_mem _ l) hx
    refine ⟨h, ?_⟩
    rw [norm_natCast_mul l hx h, Padic.norm_p, inv_mul_le_iff₀ hl0]
    rw [Real.rpow_add_one hl0.ne', mul_comm] at h'
    exact h'

theorem sz_of_sq {r : ℝ} {x : ℂ} (h : Sz l lam r (x ^ 2)) : Sz l lam (r / 2) x := by
  obtain ⟨h, h'⟩ := h
  have hl0 : (0 : ℝ) < l := by exact_mod_cast hl.out.pos
  have hx : x ∈ algebraicClosure ℚ ℂ :=
    mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (by norm_num : 0 < 2) (mem_algebraicClosure_iff.1 h))
  refine ⟨hx, ?_⟩
  have : (⟨x ^ 2, h⟩ : algebraicClosure ℚ ℂ) = ⟨x, hx⟩ ^ 2 := rfl
  rw [this, map_pow, norm_pow] at h'
  have e : (l : ℝ) ^ r = ((l : ℝ) ^ (r / 2)) ^ 2 := by
    rw [sq, ← Real.rpow_add hl0]; congr 1; ring
  rw [e] at h'
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h'

theorem main : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]), (∀ (n : ℕ) (x : ℂ), ¬ l ∣ n → IsIntegral ℤ ((n : ℂ) * x) → Sz l lam 0 x) ∧ (∀ (r : ℝ) (x y : ℂ), Sz l lam r x → Sz l lam r y → Sz l lam r (x + y)) ∧ (∀ (r r' : ℝ) (x y : ℂ), Sz l lam r x → Sz l lam r' y → Sz l lam (r + r') (x * y)) ∧ (∀ (r r' : ℝ) (x : ℂ), r ≤ r' → Sz l lam r x → Sz l lam r' x) ∧ (∀ (r : ℝ) (x : ℂ), Sz l lam r x → Sz l lam r (-x)) ∧ (∀ (r : ℝ) (x : ℂ), Sz l lam r ((l : ℂ) * x) ↔ Sz l lam (r + 1) x) ∧ (∀ (r : ℝ) (x y : ℂ), Sz l lam r (x ^ 2) → y = x → Sz l lam (r / 2) y) :=
  fun _ _ _ => ⟨sz_of_isIntegral, fun _ _ _ => sz_add, fun _ _ _ _ => sz_mul, fun _ _ _ => sz_mono, fun _ _ => sz_neg,
    sz_prime_mul, fun _ _ _ h e => e ▸ sz_of_sq h⟩

end GlobalTheory.SzRules
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastOfForallRatGt
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
open GlobalTheory.LatVal (Sz)
open GlobalTheory.CMVal (latDisc)

namespace GlobalTheory.QFam

theorem sz_of_forall_rat_gt : ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]),
    ∀ (r : ℝ) (x : ℂ), (∀ q : ℚ, r < q → Sz l lam q x) → Sz l lam r x := by
  intro l hl lam r x h
  obtain ⟨q₀, hq₀⟩ := exists_rat_gt r
  obtain ⟨hx, -⟩ := h q₀ hq₀
  refine ⟨hx, ?_⟩
  by_contra hc
  rw [not_le] at hc
  have hl1 : (1 : ℝ) < (l : ℝ) := by exact_mod_cast hl.out.one_lt
  have hl0 : (0 : ℝ) < (l : ℝ) := lt_trans one_pos hl1
  have ht : 0 < ‖lam ⟨x, hx⟩‖ := lt_trans (Real.rpow_pos_of_pos hl0 r) hc
  have h1 : r < Real.logb l ‖lam ⟨x, hx⟩‖ := (Real.lt_logb_iff_rpow_lt hl1 ht).2 hc
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn h1
  obtain ⟨_, hle⟩ := h q hq1
  exact absurd ((Real.lt_logb_iff_rpow_lt hl1 ht).1 hq2) (not_lt.2 hle)

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingToOrderedCechDegreeTwoMemCocyclesTwo
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CechPoset

variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)

def triVal (c : CC F 2) (X : (NE κ)ᵒᵖ) (s : Finset κ) : F.obj X :=
  if h : s.card = 2 + 1 ∧ s ⊆ sub X then
    mp F (homOf (a := ne s (card_nonempty ⟨s, h.1⟩)) (b := X) h.2) (c ⟨s, h.1⟩)
  else 0

variable {F}

theorem hom_eq {a b : (NE κ)ᵒᵖ} (f g : a ⟶ b) : f = g := Subsingleton.elim _ _

theorem triVal_eq (c : CC F 2) (X : (NE κ)ᵒᵖ) {s : Finset κ} (hs : s.card = 2 + 1) (h : s ⊆ sub X) :
    mp F (homOf (a := ne s (card_nonempty ⟨s, hs⟩)) (b := X) h) (c ⟨s, hs⟩) = triVal F c X s := by
  unfold triVal; rw [dite_eq_left ⟨hs, h⟩]

theorem triVal_map (c : CC F 2) {X Y : (NE κ)ᵒᵖ} (f : X ⟶ Y) {s : Finset κ} (h : s ⊆ sub X) :
    mp F f (triVal F c X s) = triVal F c Y s := by
  unfold triVal
  by_cases hs : s.card = 2 + 1
  · rw [dite_eq_left ⟨hs, h⟩, dite_eq_left ⟨hs, h.trans (sub_subset f)⟩, ← mp_comp]
    congr 1
  · rw [dite_eq_right (fun h' => hs h'.1), dite_eq_right (fun h' => hs h'.1), map_zero]

theorem alternatingToOrderedCechDegreeTwo_apply_triple (c : CC F 2) {a b d : (NE κ)ᵒᵖ} (f : a ⟶ b) (g : b ⟶ d) :
    e2 F c a b d f g = if mn d < mn b ∧ mn b < mn a then -triVal F c d {mn d, mn b, mn a} else 0 := by
  unfold e2
  simp only [LinearMap.pi_apply]
  split_ifs with h
  · simp only [LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [← triVal_eq c d (card_three h.1 h.2) (triple_subset f g)]
    rfl
  · rfl

end GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset
variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] {F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R}

theorem triVal_eq' (c : CC F 2) {X : (NE κ)ᵒᵖ} (s : {s : Finset κ // s.card = 2 + 1})
    (f : ne s.1 (card_nonempty s) ⟶ X) : mp F f (c s) = triVal F c X s.1 := by
  obtain ⟨s, hs⟩ := s
  rw [← triVal_eq c X hs (sub_subset f), hom_eq f (homOf (sub_subset f))]

theorem triVal_rel (c : CC F 2) (hc : δ F 2 c = 0) (X : (NE κ)ᵒᵖ) {w x y z : κ}
    (h1 : w < x) (h2 : x < y) (h3 : y < z) (hs : ({w, x, y, z} : Finset κ) ⊆ sub X) :
    triVal F c X {x, y, z} - triVal F c X {w, y, z} + triVal F c X {w, x, z} - triVal F c X {w, x, y} = 0 := by
  have ht : ({w, x, y, z} : Finset κ).card = 2 + 1 + 1 := by
    rw [Finset.card_insert_of_notMem (by simp [h1.ne, (h1.trans h2).ne, (h1.trans (h2.trans h3)).ne]),
      Finset.card_insert_of_notMem (by simp [h2.ne, (h2.trans h3).ne]), Finset.card_pair h3.ne]
  have e := congrArg (mp F (homOf (a := ne _ (card_nonempty ⟨_, ht⟩)) (b := X) hs))
    (congrFun hc ⟨_, ht⟩)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [δ_apply, map_sum, Pi.zero_apply, map_zero] at e
  have e' : ∑ i ∈ ({w, x, y, z} : Finset κ), GlobalTheory.cubeSign ({w, x, y, z} : Finset κ) i •
      triVal F c X (({w, x, y, z} : Finset κ).erase i) = 0 := by
    rw [← e, ← Finset.sum_coe_sort]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, ← mp_comp, triVal_eq']
  rw [Finset.sum_insert (by simp [h1.ne, (h1.trans h2).ne, (h1.trans (h2.trans h3)).ne]),
    Finset.sum_insert (by simp [h2.ne, (h2.trans h3).ne]), Finset.sum_pair h3.ne] at e'
  have hwx := h1.ne; have hwy := (h1.trans h2).ne; have hwz := (h1.trans (h2.trans h3)).ne
  have hxy := h2.ne; have hxz := (h2.trans h3).ne; have hyz := h3.ne
  simp only [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, h1, h2, h3, h1.trans h2,
    h1.trans (h2.trans h3), h2.trans h3, lt_irrefl, not_lt_of_gt, if_true, if_false] at e'
  simp only [Finset.insert_empty, Finset.card_empty, Finset.card_singleton,
    Finset.card_pair hwx, Finset.card_insert_of_notMem (show w ∉ ({x, y} : Finset κ) by simp [hwx, hwy]),
    Finset.card_pair hxy] at e'
  rw [Finset.erase_insert (by simp [hwx, hwy, hwz]),
    Finset.erase_insert_of_ne hwx, Finset.erase_insert (by simp [hxy, hxz]),
    Finset.erase_insert_of_ne hwy, Finset.erase_insert_of_ne hxy,
    Finset.erase_insert (by simp [hyz]),
    Finset.erase_insert_of_ne hwz, Finset.erase_insert_of_ne hxz,
    Finset.erase_insert_of_ne hyz, Finset.erase_singleton] at e'
  norm_num at e'
  linear_combination e'

end GlobalTheory.CechPoset

namespace GlobalTheory.CechPoset
variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] {F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R}

theorem alternatingToOrderedCechDegreeTwo_map_apply (c : CC F 2) {a b d g : (NE κ)ᵒᵖ} (f : a ⟶ b) (f' : b ⟶ d) (f'' : d ⟶ g) :
    mp F f'' (e2 F c a b d f f') =
      if mn d < mn b ∧ mn b < mn a then -triVal F c g {mn d, mn b, mn a} else 0 := by
  rw [alternatingToOrderedCechDegreeTwo_apply_triple]
  split_ifs
  · rw [map_neg, triVal_map c f'' (triple_subset f f')]
  · exact map_zero _

theorem e2_mem_Z2_of_delta_eq_zero (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (c : CC F 2) (hc : δ F 2 c = 0) :
    e2 F c ∈ Z2 F := by
  intro a b d g φ ψ χ
  have hab := mn_le_of_hom φ; have hbd := mn_le_of_hom ψ; have hdg := mn_le_of_hom χ
  have hs : ({mn g, mn d, mn b, mn a} : Finset κ) ⊆ sub g := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact mn_mem g
    · exact sub_subset χ (mn_mem d)
    · exact sub_subset (ψ ≫ χ) (mn_mem b)
    · exact sub_subset (φ ≫ ψ ≫ χ) (mn_mem a)
  have hrel : mn g < mn d → mn d < mn b → mn b < mn a →
      triVal F c g {mn d, mn b, mn a} - triVal F c g {mn g, mn b, mn a} +
        triVal F c g {mn g, mn d, mn a} - triVal F c g {mn g, mn d, mn b} = 0 :=
    fun h1 h2 h3 => triVal_rel c hc g h1 h2 h3 hs
  rw [alternatingToOrderedCechDegreeTwo_map_apply, alternatingToOrderedCechDegreeTwo_apply_triple, alternatingToOrderedCechDegreeTwo_apply_triple, alternatingToOrderedCechDegreeTwo_apply_triple]
  generalize mn a = xa at *
  generalize mn b = xb at *
  generalize mn d = xd at *
  generalize mn g = xg at *
  rcases hdg.lt_or_eq with h1 | rfl <;> rcases hbd.lt_or_eq with h2 | rfl <;>
    rcases hab.lt_or_eq with h3 | rfl <;>
    simp_all [lt_irrefl, not_lt_of_ge, le_of_lt]
  rw [if_pos (h2.trans h3), if_pos (h1.trans h2)]
  linear_combination -hrel
end GlobalTheory.CechPoset
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppEqOfFactor
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.SectionsPinch

theorem app_eq_of_factor {X Y : Scheme.{0}} {A : CommRingCat.{0}} (κ : Spec A ⟶ Y) [IsOpenImmersion κ]
    (j : X ⟶ Y) (O : X.Opens) (q : A ⟶ Γ(X, O)) (hO : j ⁻¹ᵁ κ.opensRange = O)
    (hfac : O.ι ≫ j = (O.toSpecΓ ≫ Spec.map q) ≫ κ) :
    j.app κ.opensRange ≫ X.presheaf.map (homOfLE hO.ge).op =
      κ.appLE κ.opensRange ⊤ (fun x _ ↦ ⟨x, rfl⟩) ≫ (Scheme.ΓSpecIso A).hom ≫ q := by
  have key : ∀ (f g : O.toScheme ⟶ Y), f = g → ∀ e e',
      f.appLE κ.opensRange ⊤ e = g.appLE κ.opensRange ⊤ e' := by
    rintro f g rfl e e'; rfl
  have hle' : ⊤ ≤ (O.ι ≫ j) ⁻¹ᵁ κ.opensRange := fun x _ ↦
    (hO.ge x.2 : _)
  rw [← cancel_mono O.topIso.inv]
  have lhs : (j.app κ.opensRange ≫ X.presheaf.map (homOfLE hO.ge).op) ≫ O.topIso.inv =
      (O.ι ≫ j).appLE κ.opensRange ⊤ hle' := by
    show j.appLE κ.opensRange O hO.ge ≫ O.topIso.inv = _
    rw [← Scheme.Hom.appLE_comp_appLE O.ι j κ.opensRange O ⊤ hO.ge (fun x _ ↦ x.2)]
    congr 1
    rw [Scheme.Opens.topIso_inv]
    exact (Scheme.Opens.ι_appLE O O ⊤ _).symm
  rw [lhs, key _ _ hfac hle' (hfac ▸ hle')]
  simp only [Category.assoc]
  rw [← Scheme.ΓSpecIso_naturality_assoc, ← Scheme.Opens.toSpecΓ_appTop]
  rw [← Scheme.Hom.appLE_comp_appLE O.toSpecΓ (Spec.map q ≫ κ) κ.opensRange ⊤ ⊤
      (fun x _ ↦ ⟨_, rfl⟩) le_top,
    ← Scheme.Hom.appLE_comp_appLE (Spec.map q) κ κ.opensRange ⊤ ⊤ (fun x _ ↦ ⟨x, rfl⟩) le_top,
    Category.assoc]
  have top : ∀ {P Q : Scheme.{0}} (f : P ⟶ Q) (e : ⊤ ≤ f ⁻¹ᵁ ⊤), f.appLE ⊤ ⊤ e = f.appTop :=
    fun f _ ↦ Scheme.Hom.appLE_eq_app (f := f) (U := ⊤)
  rw [← top (Spec.map q) le_top, ← top O.toSpecΓ le_top]

end GlobalTheory.SectionsPinch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AreaTauPair
section
noncomputable section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F

namespace GlobalTheory.WpFam.LatConst

theorem area_tauPair (τ : ℍ) : area (tauPair τ) = τ.im := by
  have h1 : (tauPair τ).ω₁ = (τ : ℂ) := rfl
  have h2 : (tauPair τ).ω₂ = 1 := rfl
  rw [area, h1, h2]
  simp [abs_of_pos τ.im_pos]

theorem wEta_one (τ : ℍ) : wEta (tauPair τ) 1 = EisensteinSeries.G2 τ := by
  have h1 : (tauPair τ).ω₁ = (τ : ℂ) := rfl
  have h2 : (tauPair τ).ω₂ = 1 := rfl
  have h := (etaEisenstein (tauPair τ)).2
  rw [h1, h2] at h
  rw [h, one_mul, ← LegendreModelEllipticTorsion.tsum_e2Summand]
  refine tsum_congr fun m => ?_
  rw [EisensteinSeries.e2Summand]
  refine tsum_congr fun n => ?_
  simp [EisensteinSeries.eisSummand, zpow_ofNat]

theorem main : ∀ τ : ℍ, s2 (tauPair τ) = G2s τ ∧ area (tauPair τ) = τ.im := by
  intro τ
  refine ⟨?_, area_tauPair τ⟩
  have h := etaSplit (tauPair τ) 1
  rw [wEta_one, area_tauPair] at h
  rw [G2s, h]
  simp

end GlobalTheory.WpFam.LatConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AzumayaFreeRankSqEquivMatrixOverLocalStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.azumaya_free_rank_sq_equiv_matrix_over_local : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [IsLocalRing A] [Algebra ℤ_[ℓ] A]
    [Module.Finite ℤ_[ℓ] A] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ]
    (n : ℕ), Module.finrank A Λ = n ^ 2 → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A) := by
  first | (exact @GlobalTheory.AzumayaLocal.azumaya_local_matrix) | (exact GlobalTheory.AzumayaLocal.azumaya_local_matrix) | (intros; apply GlobalTheory.AzumayaLocal.azumaya_local_matrix  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousConeDescendsEtaleSurjectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousCone_descends_etale_surjective : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G) (W V : Scheme.{0}) (r : W ⟶ S) (f : V ⟶ W), Etale f → Surjective f → ∀ (P : MorphismProperty Scheme.{0}) [P.IsStableUnderBaseChange] [P.IsMultiplicative], P f → (∀ (Z : Scheme.{0}) (π : Z ⟶ V), P π → ContCone R F ((bc (sch.map (π ≫ f ≫ r))).mapCone c)) → ContCone R F ((bc (sch.map r)).mapCone c) := by
  first | (exact @GlobalTheory.EtC.contCone_of_etale_surjective) | (exact GlobalTheory.EtC.contCone_of_etale_surjective) | (intros; apply GlobalTheory.EtC.contCone_of_etale_surjective <;> assumption)
end

