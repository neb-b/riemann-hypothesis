module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
public import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0209
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0530

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechCocycleCohomologousPosetOneCocycle
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option autoImplicit false

namespace GlobalTheory.CechPoset.CechPosetH1Surjective

open GlobalTheory.CechPoset

variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R)

theorem hom_eq {a b : (NE κ)ᵒᵖ} (φ ψ : a ⟶ b) : φ = ψ :=
  Quiver.Hom.unop_inj (Subsingleton.elim _ _)

noncomputable def V (f : Z1 F) (b : (NE κ)ᵒᵖ) (x : κ) : F.obj b :=
  if hx : x ∈ sub b then
    f.1 (ne {x} (Finset.singleton_nonempty x)) b
      (homOf (show ({x} : Finset κ) ⊆ sub b from Finset.singleton_subset_iff.2 hx))
  else 0

variable {F}

theorem V_res (f : Z1 F) {a b : (NE κ)ᵒᵖ} (φ : a ⟶ b) {x : κ} (hx : x ∈ sub a) :
    mp F φ (V F f a x) = V F f b x - f.1 a b φ := by
  unfold V
  rw [dite_eq_left hx, dite_eq_left (sub_subset φ hx)]
  have e := Z1.comp f (homOf (a := ne {x} (Finset.singleton_nonempty x)) (b := a)
    (Finset.singleton_subset_iff.2 hx)) φ
  rw [hom_eq (_ ≫ φ) (homOf (a := ne {x} (Finset.singleton_nonempty x)) (b := b)
    (Finset.singleton_subset_iff.2 (sub_subset φ hx)))] at e
  rw [e]
  ring

noncomputable def zc (f : Z1 F) : CC F 1 := fun t =>
  V F f (ne t.1 (card_nonempty t)) (t.1.min' (card_nonempty t)) -
    V F f (ne t.1 (card_nonempty t)) (t.1.max' (card_nonempty t))

theorem zc_res (f : Z1 F) (s : {s : Finset κ // s.card = 1 + 1}) (b : (NE κ)ᵒᵖ)
    (h : sub (ne s.1 (card_nonempty s)) ⊆ sub b) :
    mp F (homOf h) (zc f s) = V F f b (s.1.min' (card_nonempty s)) - V F f b (s.1.max' (card_nonempty s)) := by
  unfold zc
  rw [map_sub, V_res f (homOf h) (x := s.1.min' (card_nonempty s)) (Finset.min'_mem _ _),
    V_res f (homOf h) (x := s.1.max' (card_nonempty s)) (Finset.max'_mem _ _)]
  ring

theorem pair_min_max {s : Finset κ} {x y : κ} (hs : s = {x, y}) (h : x < y) (hne : s.Nonempty) :
    s.min' hne = x ∧ s.max' hne = y := by
  subst hs
  constructor
  · exact le_antisymm (Finset.min'_le _ _ (by simp)) (Finset.le_min' _ _ _ (by
      intro z hz; simp at hz; rcases hz with rfl | rfl
      · exact le_rfl
      · exact h.le))
  · exact le_antisymm (Finset.max'_le _ _ _ (by
      intro z hz; simp at hz; rcases hz with rfl | rfl
      · exact h.le
      · exact le_rfl)) (Finset.le_max' _ _ (by simp))

theorem exists_triple {s : Finset κ} (h : s.card = 3) : ∃ a b c, a < b ∧ b < c ∧ s = {a, b, c} := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.1 h
  rcases lt_or_gt_of_ne hxy with h1 | h1 <;> rcases lt_or_gt_of_ne hxz with h2 | h2 <;>
    rcases lt_or_gt_of_ne hyz with h3 | h3
  all_goals first
    | exact absurd (h1.trans h3) (not_lt.2 h2.le)
    | exact absurd (h2.trans h3) (not_lt.2 h1.le)
    | exact absurd (h1.trans h2) (not_lt.2 h3.le)
    | exact absurd (h3.trans h1) (not_lt.2 h2.le)
    | exact absurd (h2.trans h1) (not_lt.2 h3.le)
    | exact absurd (h3.trans h2) (not_lt.2 h1.le)
    | (refine ⟨x, y, z, ?_, ?_, ?_⟩; assumption; assumption; ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto)
    | (refine ⟨x, z, y, ?_, ?_, ?_⟩; assumption; assumption; ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto)
    | (refine ⟨y, x, z, ?_, ?_, ?_⟩; assumption; assumption; ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto)
    | (refine ⟨y, z, x, ?_, ?_, ?_⟩; assumption; assumption; ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto)
    | (refine ⟨z, x, y, ?_, ?_, ?_⟩; assumption; assumption; ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto)
    | (refine ⟨z, y, x, ?_, ?_, ?_⟩; assumption; assumption; ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; try tauto)

end GlobalTheory.CechPoset.CechPosetH1Surjective

namespace GlobalTheory.CechPoset.CechPosetH1Surjective
open GlobalTheory.CechPoset
variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] {F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R}

theorem erase3 {a b c : κ} (hab : a < b) (hbc : b < c) :
    ({a, b, c} : Finset κ).erase a = {b, c} ∧ ({a, b, c} : Finset κ).erase b = {a, c} ∧
      ({a, b, c} : Finset κ).erase c = {a, b} := by
  have hac := hab.trans hbc
  refine ⟨?_, ?_, ?_⟩ <;> ext w <;> simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] <;>
    constructor
  all_goals first
    | (rintro ⟨hw, h | h | h⟩ <;> first | exact absurd h hw | (subst h; simp))
    | (rintro (h | h) <;> subst h <;> simp [hab.ne, hab.ne', hbc.ne, hbc.ne', hac.ne, hac.ne'])

theorem sign3 {a b c : κ} (hab : a < b) (hbc : b < c) :
    GlobalTheory.cubeSign ({a, b, c} : Finset κ) a = 1 ∧ GlobalTheory.cubeSign ({a, b, c} : Finset κ) b = -1 ∧
      GlobalTheory.cubeSign ({a, b, c} : Finset κ) c = 1 := by
  have hac := hab.trans hbc
  refine ⟨?_, ?_, ?_⟩ <;> simp [GlobalTheory.cubeSign, Finset.filter_insert, Finset.filter_singleton, hab, hbc, hac,
    not_lt.2 hab.le, not_lt.2 hbc.le, not_lt.2 hac.le, Finset.card_pair hab.ne]

theorem part2 (f : Z1 F) : f.1 - e1 F (zc f) = d0 F (fun a => V F f a (mn a)) := by
  funext a b φ
  simp only [Pi.sub_apply, amitsur_d0_apply]
  rw [V_res f φ (mn_mem a)]
  by_cases h : mn b < mn a
  · have e : e1 F (zc f) a b φ = -(mp F (homOf (a := ne {mn b, mn a} (Finset.insert_nonempty _ _)) (b := b)
        (pair_subset φ)) (zc f ⟨{mn b, mn a}, Finset.card_pair h.ne⟩)) := by
      simp [e1, h]
    have z := zc_res f ⟨{mn b, mn a}, Finset.card_pair h.ne⟩ b (pair_subset φ)
    obtain ⟨h1, h2⟩ := pair_min_max (s := ({mn b, mn a} : Finset κ)) rfl h (Finset.insert_nonempty _ _)
    rw [h1, h2] at z
    rw [e]
    linear_combination z
  · have e : e1 F (zc f) a b φ = 0 := by simp [e1, h]
    have e' : mn b = mn a := le_antisymm (mn_le_of_hom φ) (not_lt.1 h)
    rw [e, e']
    ring

end GlobalTheory.CechPoset.CechPosetH1Surjective

namespace GlobalTheory.CechPoset.CechPosetH1Surjective
open GlobalTheory.CechPoset
variable {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] {F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R}

def term3 {M : Type} [AddCommGroup M] (W : κ → M) (a b c x : κ) : M :=
  GlobalTheory.cubeSign ({a, b, c} : Finset κ) x • (if x = a then W b - W c else if x = b then W a - W c else W a - W b)

theorem sum3 {M : Type} [AddCommGroup M] (W : κ → M) {a b c : κ} (hab : a < b) (hbc : b < c) :
    ∑ x ∈ ({a, b, c} : Finset κ), term3 W a b c x = 0 := by
  have hac := hab.trans hbc
  rw [Finset.sum_insert (by simp [hab.ne, hac.ne]), Finset.sum_insert (by simp [hbc.ne]),
    Finset.sum_singleton]
  obtain ⟨s1, s2, s3⟩ := sign3 hab hbc
  simp only [term3, if_pos rfl, if_neg hab.ne', if_neg hac.ne', if_neg hbc.ne', s1, s2, s3, one_smul, neg_smul]
  norm_num

theorem part1 (f : Z1 F) : δ F 1 (zc f) = 0 := by
  funext t
  rw [δ_apply]
  obtain ⟨s, hs⟩ := t
  obtain ⟨a, b, c, hab, hbc, rfl⟩ := exists_triple (s := s) (by rw [hs])
  have hac := hab.trans hbc
  obtain ⟨e1', e2', e3'⟩ := erase3 hab hbc
  refine (Finset.sum_congr rfl
    (g := fun i : ({a, b, c} : Finset κ) => term3 (V F f (ne {a, b, c} (card_nonempty ⟨_, hs⟩))) a b c i.1)
    fun i _ => ?_).trans ?_
  · have z := zc_res f (GlobalTheory.Cube.eraseIdx ⟨{a, b, c}, hs⟩ i) (ne _ (card_nonempty ⟨_, hs⟩))
      (Finset.erase_subset i.1 _)
    rw [z]
    obtain ⟨x, hx⟩ := i
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · obtain ⟨h1, h2⟩ := pair_min_max (s := (GlobalTheory.Cube.eraseIdx ⟨{x, b, c}, hs⟩ ⟨x, by simp⟩).1) e1' hbc
        (card_nonempty _)
      rw [h1, h2, term3, if_pos rfl]
    · obtain ⟨h1, h2⟩ := pair_min_max (s := (GlobalTheory.Cube.eraseIdx ⟨{a, x, c}, hs⟩ ⟨x, by simp⟩).1) e2' hac
        (card_nonempty _)
      rw [h1, h2, term3, if_neg hab.ne', if_pos rfl]
    · obtain ⟨h1, h2⟩ := pair_min_max (s := (GlobalTheory.Cube.eraseIdx ⟨{a, b, x}, hs⟩ ⟨x, by simp⟩).1) e3' hab
        (card_nonempty _)
      rw [h1, h2, term3, if_neg hac.ne', if_neg hbc.ne']
  · refine (Finset.sum_coe_sort ({a, b, c} : Finset κ)
      (term3 (V F f (ne {a, b, c} (card_nonempty ⟨_, hs⟩))) a b c)).trans ?_
    exact sum3 _ hab hbc

end GlobalTheory.CechPoset.CechPosetH1Surjective


open GlobalTheory.CechPoset.CechPosetH1Surjective in
theorem GlobalTheory.CechPoset.exists_cech_cocycle_cohomologous : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R]
    (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (f : Z1 F),
    ∃ z : CC F 1, δ F 1 z = 0 ∧ ∃ g : C0 F, f.1 - e1 F z = d0 F g :=
  fun F f => ⟨zc f, part1 f, fun a => V F f a (mn a), part2 f⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsColReduced
section
open GlobalTheory.FinGL Formalism.L2.DIV Module

namespace GlobalTheory.FinGL.Bruhat

variable {F : Type} [Field F] {n : ℕ}

theorem perm_eq_of_le (τ : Equiv.Perm (Fin n)) (h : ∀ b, τ b ≤ b) (b : Fin n) : τ b = b := by
  have hs : ∑ i : Fin n, (τ i : ℕ) = ∑ i : Fin n, (i : ℕ) := Equiv.sum_comp τ (fun i => (i : ℕ))
  have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (f := fun i : Fin n => (τ i : ℕ))
    (g := fun i : Fin n => (i : ℕ)) (fun i _ => h i)).1 hs b (Finset.mem_univ b)
  exact Fin.ext this

def mono (m : Equiv.Perm (Fin n) × (Fin n → Fˣ)) : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun a c => if a = m.1 c then (m.2 c : F) else 0

theorem mul_mono (A : Matrix (Fin n) (Fin n) F) (m : Equiv.Perm (Fin n) × (Fin n → Fˣ)) (a c : Fin n) :
    (A * mono m) a c = A a (m.1 c) * m.2 c := by
  simp [mono, Matrix.mul_apply]

theorem mono_mul (A : Matrix (Fin n) (Fin n) F) (m : Equiv.Perm (Fin n) × (Fin n → Fˣ)) (a c : Fin n) :
    (mono m * A) a c = m.2 (m.1.symm a) * A (m.1.symm a) c := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (m.1.symm a)]
  · simp [mono]
  · intro k _ hk
    have : a ≠ m.1 k := fun h => hk (by rw [h, Equiv.symm_apply_apply])
    simp [mono, this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mono_unique {m m' : Equiv.Perm (Fin n) × (Fin n → Fˣ)} {u u' : GL (Fin n) F} (hu : u ∈ unip F n)
    (hu' : u' ∈ unip F n)
    (h : (u : Matrix (Fin n) (Fin n) F) * mono m = mono m' * (u' : Matrix (Fin n) (Fin n) F)) : m = m' := by
  have key : ∀ b, (m.2 b : F) = m'.2 (m'.1.symm (m.1 b)) *
      (u' : Matrix (Fin n) (Fin n) F) (m'.1.symm (m.1 b)) b := by
    intro b
    have h1 := congrFun (congrFun h (m.1 b)) b
    rwa [mul_mono, mono_mul, unip_diag hu, one_mul] at h1
  have hle : ∀ b, (m.1.trans m'.1.symm) b ≤ b := by
    intro b
    by_contra hlt
    have hlt' : b < m'.1.symm (m.1 b) := not_le.1 hlt
    apply (m.2 b).ne_zero
    rw [key b, unip_lower hu' hlt', mul_zero]
  have hfix : ∀ b, m'.1.symm (m.1 b) = b := fun b => perm_eq_of_le _ hle b
  refine Prod.ext (Equiv.ext fun b => ?_) (funext fun b => Units.ext ?_)
  · have := congrArg m'.1 (hfix b)
    rwa [Equiv.apply_symm_apply] at this
  · rw [key b, hfix b, unip_diag hu', mul_one]

theorem mem_unip_of {A : Matrix (Fin n) (Fin n) F} (hl : ∀ i j, j < i → A i j = 0) (hd : ∀ i, A i i = 1) :
    ∃ u ∈ unip F n, (u : Matrix (Fin n) (Fin n) F) = A := by
  have hdet : A.det ≠ 0 := by
    rw [Matrix.det_of_upperTriangular (fun i j hij => hl i j hij)]
    simp [hd]
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A hdet, ⟨fun i j hij => hl i j hij, hd⟩, rfl⟩

theorem exists_col_reduced (g : GL (Fin n) F) :
    ∃ u ∈ unip F n, ∃ σ : Equiv.Perm (Fin n),
      (∀ c, ((g * u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) (σ c) c ≠ 0) ∧
      ∀ a c, σ c < a → ((g * u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a c = 0 := by
  classical
  let P : ℕ → Prop := fun N => ∃ u ∈ unip F n, ∃ f : Fin n → ℕ, ∑ c, f c = N ∧
    ∀ a c : Fin n, f c ≤ a.val → ((g * u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a c = 0
  have hex : ∃ N, P N := ⟨_, 1, Subgroup.one_mem _, fun _ => n, rfl,
    fun a c h => absurd a.2 (not_lt.2 h)⟩
  obtain ⟨u, hu, f, hf, hz⟩ := Nat.find_spec hex
  have hpos : ∀ c, 0 < f c := by
    intro c
    by_contra h0
    have h1 : (((g * u)⁻¹ * (g * u) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) c c = 1 := by
      rw [inv_mul_cancel, Units.val_one, Matrix.one_apply_eq]
    rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_zero] at h1
    · exact zero_ne_one h1
    · intro k _
      rw [hz k c (by omega), mul_zero]
  have hmin : ∀ v ∈ unip F n,
      (∀ a c : Fin n, f c ≤ a.val → ((g * v : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a c = 0) →
      ∀ c, ∃ a : Fin n, a.val + 1 = f c ∧ ((g * v : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) a c ≠ 0 := by
    intro v hv hzv c
    by_contra hcon
    push_neg at hcon
    have hlt : ∑ k, Function.update f c (f c - 1) k < Nat.find hex := by
      rw [← hf]
      refine Finset.sum_lt_sum (fun k _ => ?_) ⟨c, Finset.mem_univ _, ?_⟩
      · by_cases hk : k = c
        · subst hk; simp
        · rw [Function.update_of_ne hk]
      · have := hpos c
        rw [Function.update_self]; omega
    refine Nat.find_min hex hlt ⟨v, hv, _, rfl, fun a k hk => ?_⟩
    by_cases hkc : k = c
    · subst hkc
      rw [Function.update_self] at hk
      by_cases h2 : f k ≤ a.val
      · exact hzv a k h2
      · exact hcon a (by omega)
    · rw [Function.update_of_ne hkc] at hk
      exact hzv a k hk
  choose s hs hsne using hmin u hu hz
  have hinj : ∀ k c, k < c → s k ≠ s c := by
    intro k c hkc he
    have hfe : f k = f c := by rw [← hs k, ← hs c, he]
    set H := ((g * u : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hH
    obtain ⟨t, ht, htv⟩ := mem_unip_of (A := Matrix.transvection k c (-(H (s c) c / H (s c) k)))
      (fun i j hij => by
        have h1 : ¬ (k = i ∧ c = j) := by
          rintro ⟨rfl, rfl⟩; exact absurd hkc (not_lt.2 hij.le)
        simp [Matrix.transvection, Matrix.one_apply_ne (ne_of_gt hij), Matrix.single_apply, h1])
      (fun i => by
        have h1 : ¬ (k = i ∧ c = i) := by
          rintro ⟨rfl, h⟩; exact absurd h (ne_of_gt hkc)
        simp [Matrix.transvection, Matrix.single_apply, h1])
    have hval : ((g * (u * t) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
        H * Matrix.transvection k c (-(H (s c) c / H (s c) k)) := by
      rw [← mul_assoc, Units.val_mul, htv]
    obtain ⟨a, ha, hane⟩ := hmin (u * t) (Subgroup.mul_mem _ hu ht) (fun a j hj => by
      rw [hval]
      by_cases hjc : j = c
      · subst hjc
        rw [Matrix.mul_transvection_apply_same, hz a j hj, hz a k (hfe ▸ hj)]
        simp
      · rw [Matrix.mul_transvection_apply_of_ne _ _ _ _ hjc]
        exact hz a j hj) c
    have hac : a = s c := Fin.ext (by have := hs c; omega)
    apply hane
    have hk0 : H (s c) k ≠ 0 := he ▸ hsne k
    rw [hval, Matrix.mul_transvection_apply_same, hac]
    field_simp
    ring
  have hinj' : Function.Injective s := by
    intro k c he
    rcases lt_trichotomy k c with h | h | h
    · exact absurd he (hinj k c h)
    · exact h
    · exact absurd he.symm (hinj c k h)
  refine ⟨u, hu, Equiv.ofBijective s (Finite.injective_iff_bijective.1 hinj'), hsne, fun a c h => hz a c ?_⟩
  have h1 : (s c).val < a.val := h
  have := hs c
  omega

theorem exists_decomp (g : GL (Fin n) F) : ∃ m : Equiv.Perm (Fin n) × (Fin n → Fˣ), ∃ u ∈ unip F n, ∃ u' ∈ unip F n,
    (g : Matrix (Fin n) (Fin n) F) = (u : Matrix (Fin n) (Fin n) F) * mono m * (u' : Matrix (Fin n) (Fin n) F) := by
  obtain ⟨v, hv, σ, hne, hz⟩ := exists_col_reduced g
  set H := ((g * v : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hH
  obtain ⟨u, hu, huv⟩ := mem_unip_of (A := Matrix.of fun a b => H a (σ.symm b) / H b (σ.symm b))
    (fun i j hij => by
      rw [Matrix.of_apply, hz i _ (by simpa using hij), zero_div])
    (fun i => by
      have := hne (σ.symm i)
      rw [Equiv.apply_symm_apply] at this
      rw [Matrix.of_apply, div_self this])
  refine ⟨(σ, fun c => Units.mk0 _ (hne c)), u, hu, v⁻¹, Subgroup.inv_mem _ hv, ?_⟩
  have h1 : (u : Matrix (Fin n) (Fin n) F) * mono (σ, fun c => Units.mk0 _ (hne c)) = H := by
    ext a c
    rw [mul_mono, huv]
    simp [div_mul_cancel₀ _ (hne c)]
  rw [h1, hH, ← Units.val_mul, mul_inv_cancel_right]

theorem bruhat : ∀ (F : Type) [Field F] (n : ℕ) (g : GL (Fin n) F), ∃! m : Equiv.Perm (Fin n) × (Fin n → Fˣ), ∃ u ∈ unip F n, ∃ u' ∈ unip F n, (g : Matrix (Fin n) (Fin n) F) = (u : Matrix (Fin n) (Fin n) F) * (Matrix.of fun a c => if a = m.1 c then (m.2 c : F) else 0) * (u' : Matrix (Fin n) (Fin n) F) := by
  intro F _ n g
  obtain ⟨m, u, hu, u', hu', h⟩ := exists_decomp g
  refine ⟨m, ⟨u, hu, u', hu', h⟩, ?_⟩
  rintro m' ⟨v, hv, v', hv', h'⟩
  have h2 : (v : Matrix (Fin n) (Fin n) F) * mono m' * v' = u * mono m * u' := h'.symm.trans h
  refine mono_unique (u := u⁻¹ * v) (u' := u' * v'⁻¹) (Subgroup.mul_mem _ (Subgroup.inv_mem _ hu) hv)
    (Subgroup.mul_mem _ hu' (Subgroup.inv_mem _ hv')) ?_
  have h3 := congrArg (fun X => ((u⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * X *
    ((v'⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) h2
  simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, Units.inv_mul_cancel_left] at h3
  simp only [Units.val_mul, Matrix.mul_assoc]
  exact h3

end GlobalTheory.FinGL.Bruhat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteLocalGeomDomain
section
open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.SepRing


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
theorem isDomain_tensor_of_reg (k K S : Type) [Field k] [Field K] [Algebra k K]
    [FiniteDimensional k K] [IsPurelyInseparable k K] [CommRing S] [IsLocalRing S]
    [IsNoetherianRing S] [Algebra k S]
    (hreg : ∀ (𝔫 : Ideal (S ⊗[k] K)) [𝔫.IsPrime], IsRegularLocalRing (Localization.AtPrime 𝔫)) :
    IsDomain (K ⊗[k] AdicCompletion (maximalIdeal S) S) := by
  have hinj : Function.Injective (algebraMap S (S ⊗[k] K)) :=
    Algebra.TensorProduct.includeLeft_injective (R := k) (S := k) (A := S) (B := K)
      (algebraMap k K).injective
  have hker : RingHom.ker (algebraMap S (S ⊗[k] K)) ≤ maximalIdeal S := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    rw [hinj (hx.trans (map_zero _).symm)]
    exact zero_mem _
  obtain ⟨𝔫, h𝔫max, h𝔫⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := S ⊗[k] K)
    (maximalIdeal S) hker
  haveI := h𝔫max.isPrime
  obtain ⟨S', _, e, -⟩ := GlobalTheory.CompletionFactor.exists_ringEquiv_completion_prod S (S ⊗[k] K)
    (Localization.AtPrime 𝔫) 𝔫 h𝔫
  haveI : IsRegularLocalRing (Localization.AtPrime 𝔫) := hreg 𝔫
  haveI : IsRegularLocalRing (AdicCompletion (maximalIdeal (Localization.AtPrime 𝔫))
      (Localization.AtPrime 𝔫)) := GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion _
  haveI hdom : IsDomain (AdicCompletion (maximalIdeal (Localization.AtPrime 𝔫))
      (Localization.AtPrime 𝔫)) := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain _
  let f : K ⊗[k] AdicCompletion (maximalIdeal S) S ≃+* _ :=
    (Algebra.TensorProduct.comm k K (AdicCompletion (maximalIdeal S) S)).toRingEquiv.trans
    ((Algebra.TensorProduct.cancelBaseChange k S (AdicCompletion (maximalIdeal S) S)
      (AdicCompletion (maximalIdeal S) S) K).symm.toRingEquiv.trans e)
  have hS' : Subsingleton S' := by
    have hid : IsIdempotentElem (f.symm (0, 1)) := by
      show f.symm (0,1) * f.symm (0,1) = f.symm (0,1)
      rw [← map_mul]; simp
    rcases GlobalTheory.T.idempotent_tensor_eq_zero_or_one_of_isPurelyInseparable' k K (AdicCompletion (maximalIdeal S) S) (f.symm (0, 1)) hid with h | h
    · have h2 := congrArg (fun z => (f z).2) h
      simp at h2
      exact subsingleton_of_zero_eq_one h2.symm
    · have h2 := congrArg (fun z => (f z).1) h
      simp at h2
  exact Function.Injective.isDomain ((RingHom.fst _ _).comp f.toRingHom) (by
    intro x y hxy
    apply f.injective
    exact Prod.ext hxy (Subsingleton.elim _ _))

end GlobalTheory.SepRing

namespace GlobalTheory.SepRing


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
theorem exists_complete_local_geomDomain : ∀ (k k' : Type) [Field k] [CommRing k'] [IsDomain k']
    [Algebra k k'], Module.Finite k k' → ∃ (C : Type) (_ : CommRing C) (_ : IsLocalRing C)
    (_ : IsNoetherianRing C) (_ : Algebra k C), IsAdicComplete (maximalIdeal C) C ∧
    Nonempty (k' →ₐ[k] ResidueField C) ∧ ∀ (K : Type) [Field K] [Algebra k K],
    FiniteDimensional k K → IsPurelyInseparable k K → IsDomain (K ⊗[k] C) := by
  intro k k' _ _ _ _ hfin
  haveI : Algebra.FiniteType k k' := inferInstance
  obtain ⟨r, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp this
  have hk' : IsField k' :=
    (Algebra.IsIntegral.isField_iff_isField (algebraMap k k').injective).mp (Field.toIsField k)
  letI : Field k' := hk'.toField
  let 𝔪 : Ideal (MvPolynomial (Fin r) k) := RingHom.ker φ.toRingHom
  haveI h𝔪 : 𝔪.IsMaximal := RingHom.ker_isMaximal_of_surjective φ.toRingHom hφ
  let S := Localization.AtPrime 𝔪
  haveI : IsNoetherianRing S := IsLocalization.isNoetherianRing 𝔪.primeCompl S inferInstance
  refine ⟨AdicCompletion (maximalIdeal S) S, inferInstance, inferInstance,
    GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion S _, inferInstance, inferInstance, ?_, ?_⟩
  · let C := AdicCompletion (maximalIdeal S) S
    let g : MvPolynomial (Fin r) k →ₐ[k] ResidueField C :=
      IsScalarTower.toAlgHom k (MvPolynomial (Fin r) k) (ResidueField C)
    have hg : ∀ a ∈ 𝔪, g a = 0 := by
      intro a ha
      have h1 : algebraMap (MvPolynomial (Fin r) k) S a ∈ maximalIdeal S := by
        rw [← Localization.AtPrime.map_eq_maximalIdeal]; exact Ideal.mem_map_of_mem _ ha
      have h2 : algebraMap S C (algebraMap _ S a) ∈ maximalIdeal C := by
        rw [AdicCompletion.maximalIdeal_eq_map]; exact Ideal.mem_map_of_mem _ h1
      show algebraMap _ (ResidueField C) a = 0
      rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin r) k) C (ResidueField C),
        IsScalarTower.algebraMap_apply (MvPolynomial (Fin r) k) S C]
      exact (residue_eq_zero_iff _).mpr h2
    exact ⟨(Ideal.Quotient.liftₐ 𝔪 g hg).comp
      (Ideal.quotientKerAlgEquivOfSurjective hφ).symm.toAlgHom⟩
  · intro K _ _ hK hpi
    exact isDomain_tensor_of_reg k K S (fun 𝔫 _ => _root_.GlobalTheory.isRegularLocalRing_atPrime_localization_tensor k K r 𝔪 𝔫)

end GlobalTheory.SepRing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorSquareKerOfSurjectiveStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sum_ιMulti_of_exteriorSquare_map_eq_zero : ∀ (R : Type) [CommRing R] (W M H : Type) [AddCommGroup W] [Module R W] [AddCommGroup M] [Module R M] [AddCommGroup H] [Module R H] (i : W →ₗ[R] M) (p : M →ₗ[R] H), Function.Surjective p → Function.Exact i p → ∀ t : ⋀[R]^2 M, exteriorPower.map 2 p t = 0 → ∃ (n : ℕ) (a : Fin n → M) (w : Fin n → W), t = ∑ k, exteriorPower.ιMulti R 2 ![a k, i (w k)] := by
  first | exact @GlobalTheory.exteriorSquare_ker_of_surjective | exact GlobalTheory.exteriorSquare_ker_of_surjective | (intros; apply GlobalTheory.exteriorSquare_ker_of_surjective <;> assumption)
end

