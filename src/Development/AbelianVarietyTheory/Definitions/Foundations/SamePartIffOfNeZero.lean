module

public import Mathlib
public import Formalism.CyclotomicNorms.StatementT

@[expose] public section

noncomputable section
open Polynomial Classical
namespace GlobalTheory.BadShare

def SamePart {k : Type} [Field k] (l : ℕ) (x y : k) : Prop := Formalism.CyclotomicNorms.primeToPart l x = Formalism.CyclotomicNorms.primeToPart l y

def BB (g N l : ℕ) : Prop := l ∈ Formalism.CyclotomicNorms.BB N g

variable (g : ℕ) [Fact g.Prime]

def sqSet (N : ℕ) : Finset (ZMod g)[X] :=
  (Finset.univ.image fun c : Fin N → ZMod g => (X ^ N + ∑ i : Fin N, C (c i) * X ^ (i : ℕ) : (ZMod g)[X])).filter
    fun f => Squarefree f ∧ f.coeff 0 ≠ 0

def degType (f : (ZMod g)[X]) : Multiset ℕ := (UniqueFactorizationMonoid.normalizedFactors f).map natDegree

def torusCard (f : (ZMod g)[X]) : ℕ := ((degType g f).map fun d => g ^ d - 1).prod

def mass (N : ℕ) (A : (ZMod g)[X] → Prop) : ℝ := ∑ f ∈ (sqSet g N).filter A, ((torusCard g f : ℝ))⁻¹

def RootsApart (N : ℕ) (f : (ZMod g)[X]) : Prop :=
  ∀ l : ℕ, l.Prime → ¬ BB g N l → ∀ x ∈ f.aroots (AlgebraicClosure (ZMod g)), ∀ y ∈ f.aroots (AlgebraicClosure (ZMod g)),
    SamePart l x y → x = y

def RootsAvoid (c : (ZMod g)ˣ) (f : (ZMod g)[X]) : Prop :=
  ∀ l : ℕ, l.Prime → l ≠ g → ∀ x ∈ f.aroots (AlgebraicClosure (ZMod g)),
    ¬ SamePart l x (algebraMap (ZMod g) (AlgebraicClosure (ZMod g)) (c : ZMod g))

def HasDiv (a : ℕ) (f : (ZMod g)[X]) : Prop := ∃ h : (ZMod g)[X], h ∣ f ∧ h.natDegree = a

def HasPrimeFactor (N : ℕ) (f : (ZMod g)[X]) : Prop :=
  ∃ h : (ZMod g)[X], Irreducible h ∧ h ∣ f ∧ h.natDegree.Prime ∧ N < 2 * h.natDegree ∧ h.natDegree + 3 ≤ N

def Good {ι : Type} {m : ℕ} (N : ℕ) (ch : ι → Fin m → (ZMod g)ˣ) (F : ι → (ZMod g)[X]) : Prop :=
  Formalism.CyclotomicNorms.IsGood N g F ch ∧ Formalism.CyclotomicNorms.IsGood N g F fun v j => (ch v j)⁻¹

def goodSet {ι : Type} [Fintype ι] {m : ℕ} (N : ℕ) (ch : ι → Fin m → (ZMod g)ˣ) : Finset (ι → (ZMod g)[X]) :=
  (Fintype.piFinset fun _ : ι => sqSet g N).filter (Good g N ch)

def badBound (g f m N q : ℝ) : ℝ :=
  3 * f / g + 23 * f * Real.log g / Real.sqrt g + 2 * f * m * (1 / (4 * q) + (1 + Real.log N) / (g - 1)) +
    N / 2 * (7 / 8 : ℝ) ^ f + Real.exp (-(f / (10 * Real.log N)))


open Polynomial Classical in
variable (g : ℕ) [Fact g.Prime] in
theorem _root_.GlobalTheory.BadShare.bb_iff {g N l : ℕ} :
    _root_.GlobalTheory.BadShare.BB g N l ↔
      l = g ∨ (l.Prime ∧ ∃ d : ℕ, 1 ≤ d ∧ d ≤ N ∧ g ^ d < l ^ (4 * padicValNat l (g ^ d - 1))) := by
  unfold _root_.GlobalTheory.BadShare.BB _root_.Formalism.CyclotomicNorms.BB _root_.Formalism.CyclotomicNorms.Exc
  simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨d, h1, h2, hp, hq⟩
    exact ⟨hp, d, h1, h2, hq⟩
  · rintro ⟨hp, d, h1, h2, hq⟩
    exact ⟨d, h1, h2, hp, hq⟩

theorem bb_of_dvd {g N l d : ℕ} (hl : l.Prime) (h1 : 1 ≤ d) (h2 : d ≤ N) (h0 : g ^ d - 1 ≠ 0) (h3 : l ∣ g ^ d - 1)
    (h4 : g ^ d < l ^ 4) : BB g N l := by
  haveI := Fact.mk hl
  refine bb_iff.2 (Or.inr ⟨hl, d, h1, h2, h4.trans_le (Nat.pow_le_pow_right hl.pos ?_)⟩)
  have hval : 1 ≤ padicValNat l (g ^ d - 1) := by
    rw [Nat.padicValNat_def]
    exact one_le_multiplicity_of_dvd h0 h3
  omega

section part
variable {k : Type} [Field k] {l : ℕ}

open Polynomial Classical in
variable (g : ℕ) [Fact g.Prime] in
private theorem pow_eq_pow_of_modEq_orderOf' {G : Type*} [Monoid G] {x : G} {a b : ℕ}
    (h : a ≡ b [MOD orderOf x]) : x ^ a = x ^ b := by
  rw [← pow_mod_orderOf, show a % orderOf x = b % orderOf x from h, pow_mod_orderOf]


open Polynomial Classical in
variable (g : ℕ) [Fact g.Prime] in
variable {k : Type} [Field k] {l : ℕ} in
theorem _root_.GlobalTheory.BadShare.eq_of_pow_eq {M a : ℕ} (hM : M.Coprime l) {x y : k} (hx : x ^ M = 1)
    (hy : y ^ M = 1) (hM0 : M ≠ 0) (h : x ^ (l ^ a) = y ^ (l ^ a)) : x = y := by
  haveI : NeZero M := ⟨hM0⟩
  have hs : l ^ a * ((l ^ a : ℕ) : ZMod M)⁻¹.val ≡ 1 [MOD M] := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_one]
    exact ZMod.coe_mul_inv_eq_one _ (hM.symm.pow_left a)
  have key : ∀ z : k, z ^ M = 1 → (z ^ (l ^ a)) ^ ((l ^ a : ℕ) : ZMod M)⁻¹.val = z := by
    intro z hz
    rw [← pow_mul]
    conv_rhs => rw [← pow_one z]
    exact pow_eq_pow_of_modEq_orderOf' (hs.of_dvd (orderOf_dvd_of_pow_eq_one hz))
  rw [← key x hx, ← key y hy, h]

open Polynomial Classical in
variable (g : ℕ) [Fact g.Prime] in
private theorem primeToPart_pow_prime_pow_eq_of_factorization_le {G : Type*} [Monoid G] {l : ℕ} (hl : l.Prime) {x : G}
    (hx : IsOfFinOrder x) {a : ℕ} (ha : (orderOf x).factorization l ≤ a) :
    _root_.Formalism.CyclotomicNorms.primeToPart l x ^ (l ^ a) = x ^ (l ^ a) := by
  unfold _root_.Formalism.CyclotomicNorms.primeToPart
  set n := orderOf x with hndef
  set v := n.factorization l with hvdef
  set m := n / l ^ v with hmdef
  have hn : n ≠ 0 := hx.orderOf_pos.ne'
  have hm : m ≠ 0 := (Nat.ordCompl_pos l hn).ne'
  have hcop : Nat.Coprime (l ^ v) m := (Nat.coprime_ordCompl hl hn).pow_left v
  have hnm : l ^ v * m = n := Nat.ordProj_mul_ordCompl_eq_self n l
  haveI : NeZero m := ⟨hm⟩
  have hinv : l ^ v * ((l ^ v : ℕ) : ZMod m)⁻¹.val ≡ 1 [MOD m] := by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, ZMod.natCast_zmod_val, Nat.cast_one]
    exact ZMod.coe_mul_inv_eq_one _ hcop
  rw [← pow_mul]
  apply pow_eq_pow_of_modEq_orderOf'
  rw [← hndef, ← hnm, ← Nat.modEq_and_modEq_iff_modEq_mul hcop]
  refine ⟨?_, ?_⟩
  · have h1 : l ^ v ∣ l ^ a := pow_dvd_pow l ha
    exact (Nat.modEq_zero_iff_dvd.2 (Dvd.dvd.mul_left h1 _)).trans (Nat.modEq_zero_iff_dvd.2 h1).symm
  · simpa only [one_mul] using hinv.mul_right (l ^ a)

open Polynomial Classical in
variable (g : ℕ) [Fact g.Prime] in
private theorem primeToPart_pow_orderOf_div_prime_pow_eq_one {G : Type*} [Monoid G] (l : ℕ) (x : G) :
    _root_.Formalism.CyclotomicNorms.primeToPart l x ^ (orderOf x / l ^ (orderOf x).factorization l) = 1 := by
  unfold _root_.Formalism.CyclotomicNorms.primeToPart
  rw [← pow_mul, ← orderOf_dvd_iff_pow_eq_one]
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self (orderOf x) l]
  exact mul_dvd_mul_right (dvd_mul_right _ _) _


open Polynomial Classical in
variable (g : ℕ) [Fact g.Prime] in
variable {k : Type} [Field k] {l : ℕ} in
theorem _root_.GlobalTheory.BadShare.samePart_iff (hl : l.Prime) {x y : k} (hx : IsOfFinOrder x) (hy : IsOfFinOrder y) :
    _root_.GlobalTheory.BadShare.SamePart l x y ↔ ∃ a : ℕ, x ^ (l ^ a) = y ^ (l ^ a) := by
  unfold _root_.GlobalTheory.BadShare.SamePart
  constructor
  · intro h
    refine ⟨max ((orderOf x).factorization l) ((orderOf y).factorization l), ?_⟩
    rw [← primeToPart_pow_prime_pow_eq_of_factorization_le hl hx (le_max_left _ _),
      ← primeToPart_pow_prime_pow_eq_of_factorization_le hl hy (le_max_right _ _), h]
  · rintro ⟨a, h⟩
    have hab : x ^ (l ^ max a (max ((orderOf x).factorization l) ((orderOf y).factorization l))) =
        y ^ (l ^ max a (max ((orderOf x).factorization l) ((orderOf y).factorization l))) := by
      obtain ⟨c, hc⟩ : l ^ a ∣ l ^ max a (max ((orderOf x).factorization l) ((orderOf y).factorization l)) :=
        pow_dvd_pow l (le_max_left _ _)
      rw [hc, pow_mul, pow_mul, h]
    have hcx : (orderOf x / l ^ (orderOf x).factorization l).Coprime l :=
      (Nat.coprime_ordCompl hl hx.orderOf_pos.ne').symm
    have hcy : (orderOf y / l ^ (orderOf y).factorization l).Coprime l :=
      (Nat.coprime_ordCompl hl hy.orderOf_pos.ne').symm
    refine _root_.GlobalTheory.BadShare.eq_of_pow_eq
      (a := max a (max ((orderOf x).factorization l) ((orderOf y).factorization l))) (Nat.Coprime.mul_left hcx hcy) ?_ ?_
      (mul_ne_zero (Nat.ordCompl_pos l hx.orderOf_pos.ne').ne' (Nat.ordCompl_pos l hy.orderOf_pos.ne').ne') ?_
    · rw [pow_mul, primeToPart_pow_orderOf_div_prime_pow_eq_one, one_pow]
    · rw [mul_comm, pow_mul, primeToPart_pow_orderOf_div_prime_pow_eq_one, one_pow]
    · rw [primeToPart_pow_prime_pow_eq_of_factorization_le hl hx (le_trans (le_max_left _ _) (le_max_right _ _)),
        primeToPart_pow_prime_pow_eq_of_factorization_le hl hy (le_trans (le_max_right _ _) (le_max_right _ _)), hab]

end part

variable {g}


open Polynomial Classical in
variable (g : ℕ) [Fact g.Prime] in
variable {g} in
theorem _root_.GlobalTheory.BadShare.root_ne_zero {f : (ZMod g)[X]} (h0 : f.coeff 0 ≠ 0) {x : AlgebraicClosure (ZMod g)}
    (hx : x ∈ f.aroots (AlgebraicClosure (ZMod g))) : x ≠ 0 := by
  rintro rfl
  rw [mem_aroots] at hx
  apply h0
  have h := hx.2
  rw [← coeff_zero_eq_aeval_zero'] at h
  exact (map_eq_zero_iff _ (algebraMap (ZMod g) (AlgebraicClosure (ZMod g))).injective).mp h

open Polynomial Classical in
variable (g : ℕ) [Fact g.Prime] in
private theorem isOfFinOrder_of_ne_zero_algebraicClosure_zmod {g : ℕ} [Fact g.Prime]
    {x : AlgebraicClosure (ZMod g)} (hx : x ≠ 0) : IsOfFinOrder x := by
  have hint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  haveI := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite (IntermediateField.adjoin (ZMod g) {x}) := Module.finite_of_finite (ZMod g)
  let y : IntermediateField.adjoin (ZMod g) {x} := ⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩
  have hy : y ≠ 0 := fun h => hx (by simpa [y] using congrArg Subtype.val h)
  obtain ⟨n, hn, hpow⟩ := (isOfFinOrder_of_finite (Units.mk0 y hy)).exists_pow_eq_one
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, ?_⟩
  have := congrArg (fun u : (IntermediateField.adjoin (ZMod g) {x})ˣ =>
    ((u : IntermediateField.adjoin (ZMod g) {x}) : AlgebraicClosure (ZMod g))) hpow
  simpa [y] using this


open Polynomial Classical in
variable (g : ℕ) [Fact g.Prime] in
variable {g} in
theorem _root_.GlobalTheory.BadShare.samePart_iff_of_ne_zero {l : ℕ} (hl : l.Prime) {x y : AlgebraicClosure (ZMod g)} (hx : x ≠ 0)
    (hy : y ≠ 0) : _root_.GlobalTheory.BadShare.SamePart l x y ↔ ∃ a : ℕ, x ^ (l ^ a) = y ^ (l ^ a) :=
  _root_.GlobalTheory.BadShare.samePart_iff hl (isOfFinOrder_of_ne_zero_algebraicClosure_zmod hx)
    (isOfFinOrder_of_ne_zero_algebraicClosure_zmod hy)


open Polynomial Classical in
variable (g : ℕ) [Fact g.Prime] in
variable {g} in
theorem _root_.GlobalTheory.BadShare.rootsAvoid_iff {c : (ZMod g)ˣ} {f : (ZMod g)[X]} (h0 : f.coeff 0 ≠ 0) :
    _root_.GlobalTheory.BadShare.RootsAvoid g c f ↔ ∀ l : ℕ, l.Prime → l ≠ g → ∀ x ∈ f.aroots (AlgebraicClosure (ZMod g)), ∀ a : ℕ,
      x ^ (l ^ a) ≠ (algebraMap (ZMod g) (AlgebraicClosure (ZMod g)) (c : ZMod g)) ^ (l ^ a) := by
  have hc : algebraMap (ZMod g) (AlgebraicClosure (ZMod g)) (c : ZMod g) ≠ 0 :=
    (_root_.map_ne_zero _).mpr c.ne_zero
  unfold _root_.GlobalTheory.BadShare.RootsAvoid
  refine forall_congr' fun l => forall_congr' fun hl => forall_congr' fun _ => forall_congr' fun x =>
    forall_congr' fun hx => ?_
  rw [_root_.GlobalTheory.BadShare.samePart_iff_of_ne_zero hl (_root_.GlobalTheory.BadShare.root_ne_zero h0 hx) hc, not_exists]

theorem sqSet_eq_monicOf (N : ℕ) : sqSet g N =
    (Finset.univ.image fun c : Fin N → ZMod g => Formalism.CyclotomicNorms.monicOf c).filter fun f => Squarefree f ∧ f.coeff 0 ≠ 0 := rfl


open Polynomial Classical in
variable (g : ℕ) [Fact g.Prime] in
variable {g} in
theorem _root_.GlobalTheory.BadShare.mem_sqSet {N : ℕ} {f : (ZMod g)[X]} :
    f ∈ _root_.GlobalTheory.BadShare.sqSet g N ↔ f.Monic ∧ f.natDegree = N ∧ Squarefree f ∧ f.coeff 0 ≠ 0 := by
  unfold _root_.GlobalTheory.BadShare.sqSet
  simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨c, rfl⟩, hs, h0⟩
    have hlt := degree_sum_fin_lt c
    refine ⟨monic_X_pow_add hlt, ?_, hs, h0⟩
    rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
  · rintro ⟨hm, hd, hs, h0⟩
    refine ⟨⟨fun i => f.coeff i, ?_⟩, hs, h0⟩
    rw [Fin.sum_univ_eq_sum_range (fun i => C (f.coeff i) * X ^ i) N, ← hd]
    exact hm.as_sum.symm


open Polynomial Classical in
variable (g : ℕ) [Fact g.Prime] in
variable {g} in
theorem _root_.GlobalTheory.BadShare.good_iff {ι : Type} {m N : ℕ} {ch : ι → Fin m → (ZMod g)ˣ} {F : ι → (ZMod g)[X]} :
    _root_.GlobalTheory.BadShare.Good g N ch F ↔ (∀ v, F v ∈ _root_.GlobalTheory.BadShare.sqSet g N) ∧
      (∀ v, _root_.GlobalTheory.BadShare.RootsApart g N (F v)) ∧
      (∀ v j, _root_.GlobalTheory.BadShare.RootsAvoid g (ch v j) (F v) ∧ _root_.GlobalTheory.BadShare.RootsAvoid g (ch v j)⁻¹ (F v)) ∧
      (¬ ∃ a : ℕ, 1 ≤ a ∧ 2 * a ≤ N ∧ ∀ v, _root_.GlobalTheory.BadShare.HasDiv g a (F v)) ∧
      ∃ v, _root_.GlobalTheory.BadShare.HasPrimeFactor g N (F v) := by
  unfold _root_.GlobalTheory.BadShare.Good
  constructor
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6⟩, ⟨-, -, -, h4', -, -⟩⟩
    refine ⟨fun v => _root_.GlobalTheory.BadShare.mem_sqSet.2 ⟨(h1 v).1, (h1 v).2.1, h2 v, (h1 v).2.2⟩,
      fun v l hl hB x hx y hy hxy => h3 l hl hB v x hx y hy hxy,
      fun v j => ⟨fun l hl hlg x hx => h4 l hl hlg v j x hx, fun l hl hlg x hx => h4' l hl hlg v j x hx⟩, ?_, ?_⟩
    · rintro ⟨a, ha1, ha2, hall⟩
      obtain ⟨v, hv⟩ := h5 a ha1 ha2
      exact hv (hall v)
    · obtain ⟨v, q, hq⟩ := h6
      exact ⟨v, q, hq⟩
  · rintro ⟨h1, h2, h3, h4, v, hv⟩
    have hA : ∀ w, (F w).Monic ∧ (F w).natDegree = N ∧ (F w).coeff 0 ≠ 0 := fun w =>
      ⟨(_root_.GlobalTheory.BadShare.mem_sqSet.1 (h1 w)).1, (_root_.GlobalTheory.BadShare.mem_sqSet.1 (h1 w)).2.1,
        (_root_.GlobalTheory.BadShare.mem_sqSet.1 (h1 w)).2.2.2⟩
    have hS : ∀ w, Squarefree (F w) := fun w => (_root_.GlobalTheory.BadShare.mem_sqSet.1 (h1 w)).2.2.1
    have hD : ∀ a : ℕ, 1 ≤ a → 2 * a ≤ N → ∃ w, ¬∃ q : (ZMod g)[X], q ∣ F w ∧ q.natDegree = a := by
      intro a ha1 ha2
      by_contra hc
      push_neg at hc
      exact h4 ⟨a, ha1, ha2, hc⟩
    exact ⟨⟨hA, hS, fun l hl hB w => h2 w l hl hB, fun l hl hlg w j => (h3 w j).1 l hl hlg, hD, v, hv⟩,
      ⟨hA, hS, fun l hl hB w => h2 w l hl hB, fun l hl hlg w j => (h3 w j).2 l hl hlg, hD, v, hv⟩⟩


open Polynomial Classical in
variable (g : ℕ) [Fact g.Prime] in
variable {g} in
theorem _root_.GlobalTheory.BadShare.mem_goodSet_iff_good {ι : Type} [Fintype ι] {m N : ℕ} {ch : ι → Fin m → (ZMod g)ˣ}
    {F : ι → (ZMod g)[X]} : F ∈ _root_.GlobalTheory.BadShare.goodSet g N ch ↔ _root_.GlobalTheory.BadShare.Good g N ch F := by
  rw [_root_.GlobalTheory.BadShare.goodSet, Finset.mem_filter, Fintype.mem_piFinset]
  exact ⟨fun h => h.2, fun h => ⟨(_root_.GlobalTheory.BadShare.good_iff.1 h).1, h⟩⟩


open Polynomial Classical in
variable (g : ℕ) [Fact g.Prime] in
variable {g} in
theorem _root_.GlobalTheory.BadShare.torusCard_irreducible {f : (ZMod g)[X]} (hf : Irreducible f) :
    _root_.GlobalTheory.BadShare.torusCard g f = g ^ f.natDegree - 1 := by
  unfold _root_.GlobalTheory.BadShare.torusCard _root_.GlobalTheory.BadShare.degType
  rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hf, Multiset.map_singleton, Multiset.map_singleton,
    Multiset.prod_singleton, natDegree_eq_of_degree_eq degree_normalize]


open Polynomial Classical in
variable (g : ℕ) [Fact g.Prime] in
variable {g} in
theorem _root_.GlobalTheory.BadShare.torusCard_mul {f h : (ZMod g)[X]} (hf : f ≠ 0) (hh : h ≠ 0) :
    _root_.GlobalTheory.BadShare.torusCard g (f * h) = _root_.GlobalTheory.BadShare.torusCard g f * _root_.GlobalTheory.BadShare.torusCard g h := by
  unfold _root_.GlobalTheory.BadShare.torusCard _root_.GlobalTheory.BadShare.degType
  rw [UniqueFactorizationMonoid.normalizedFactors_mul hf hh, Multiset.map_add (f := _), Multiset.map_add (f := _), Multiset.prod_add]


open Polynomial Classical in
variable (g : ℕ) [Fact g.Prime] in
variable {g} in
theorem _root_.GlobalTheory.BadShare.mass_nonneg (N : ℕ) (A : (ZMod g)[X] → Prop) : 0 ≤ _root_.GlobalTheory.BadShare.mass g N A :=
  Finset.sum_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)


open Polynomial Classical in
variable (g : ℕ) [Fact g.Prime] in
variable {g} in
theorem _root_.GlobalTheory.BadShare.mass_mono {N : ℕ} {A B : (ZMod g)[X] → Prop}
    (h : ∀ f ∈ _root_.GlobalTheory.BadShare.sqSet g N, A f → B f) :
    _root_.GlobalTheory.BadShare.mass g N A ≤ _root_.GlobalTheory.BadShare.mass g N B := by
  unfold _root_.GlobalTheory.BadShare.mass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro f hf
    rw [Finset.mem_filter] at hf ⊢
    exact ⟨hf.1, h f hf.1 hf.2⟩
  · intro f _ _
    exact inv_nonneg.mpr (Nat.cast_nonneg _)

end GlobalTheory.BadShare
