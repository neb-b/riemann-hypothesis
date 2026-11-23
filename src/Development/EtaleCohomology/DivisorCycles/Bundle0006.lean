module

public import Development.EtaleCohomology.DivisorCycles.Bundle0001

@[expose] public section

-- bundled from Development.EtaleCohomology.DivisorCycles.GenSpecProof
section
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div

namespace LateralTheory.DivDb.GenSpecProof
open LateralTheory.DivDb Finset

variable {C : Type} [Field C] {N n : ℕ}

theorem mem_periodic (π : Equiv.Perm (Fin n)) (k : Fin n) : k ∈ Function.periodicPts π :=
  Function.mk_mem_periodicPts (orderOf_pos π) (by
    show (π^[orderOf π]) k = k
    rw [Equiv.Perm.iterate_eq_pow, pow_orderOf_eq_one]; rfl)

theorem mp_pos (π : Equiv.Perm (Fin n)) (k : Fin n) : 0 < Function.minimalPeriod π k :=
  Function.minimalPeriod_pos_of_mem_periodicPts (mem_periodic π k)

theorem orbit_eq (π : Equiv.Perm (Fin n)) (k : Fin n) :
    (univ.filter (fun m => π.SameCycle k m)) =
      (range (Function.minimalPeriod π k)).image (fun s => (π^[s]) k) := by
  ext m
  simp only [mem_filter, mem_univ, true_and, mem_image, mem_range]
  constructor
  · intro h
    obtain ⟨i, hi⟩ := h.exists_nat_pow_eq
    refine ⟨i % Function.minimalPeriod π k, Nat.mod_lt _ (mp_pos π k), ?_⟩
    rw [Function.iterate_mod_minimalPeriod_eq, Equiv.Perm.iterate_eq_pow, hi]
  · rintro ⟨s, -, rfl⟩
    rw [Equiv.Perm.iterate_eq_pow]
    exact Equiv.Perm.sameCycle_pow_right.2 (Equiv.Perm.SameCycle.refl _ _)

theorem injOn_orbit (π : Equiv.Perm (Fin n)) (k : Fin n) :
    Set.InjOn (fun s => (π^[s]) k) ↑(range (Function.minimalPeriod π k)) := by
  intro a ha b hb h
  exact Function.iterate_injOn_Iio_minimalPeriod (by simpa using ha) (by simpa using hb) h

theorem card_orbit (π : Equiv.Perm (Fin n)) (k : Fin n) :
    (univ.filter (fun m => π.SameCycle k m)).card = Function.minimalPeriod π k := by
  rw [orbit_eq, card_image_of_injOn (injOn_orbit π k), card_range]

theorem prod_orbit (π : Equiv.Perm (Fin n)) (k : Fin n) (τ : Fin n → C) :
    ∏ s ∈ range (Function.minimalPeriod π k), τ ((π^[s]) k) =
      ∏ m ∈ univ.filter (fun m => π.SameCycle k m), τ m := by
  rw [orbit_eq, prod_image (injOn_orbit π k)]

theorem filt_eq (π : Equiv.Perm (Fin n)) {i k : Fin n} (h : π.SameCycle i k) :
    univ.filter (fun m => π.SameCycle i m) = univ.filter (fun m => π.SameCycle k m) := by
  ext m
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩

theorem tp {p : Fin n → Mat C N} (hp : Sys p) (τ : Fin n → C) (k : Fin n) :
    (∑ j, τ j • p j) * p k = τ k • p k := by
  rw [Finset.sum_mul, Finset.sum_eq_single k]
  · rw [smul_mul_assoc, (hp.1.idem k).eq]
  · intro j _ hj; rw [smul_mul_assoc, hp.1.ortho hj, smul_zero]
  · simp

theorem xpow {p : Fin n → Mat C N} {x : Mat C N} {π : Equiv.Perm (Fin n)}
    (hx : ∀ j, x * p j = p (π j) * x) (m : ℕ) (k : Fin n) :
    x ^ m * p k = p ((π^[m]) k) * x ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_assoc, ih, ← mul_assoc, hx, mul_assoc, ← pow_succ',
      Function.iterate_succ_apply']

theorem ypow {p : Fin n → Mat C N} {x : Mat C N} {π : Equiv.Perm (Fin n)} (hp : Sys p)
    (hx : ∀ j, x * p j = p (π j) * x) (τ : Fin n → C) (m : ℕ) (k : Fin n) :
    (x * ∑ j, τ j • p j) ^ m * p k = (∏ s ∈ range m, τ ((π^[s]) k)) • (x ^ m * p k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_assoc, ih, mul_smul_comm, xpow hx, prod_range_succ,
      ← smul_smul, pow_succ', mul_assoc x (x ^ m), xpow hx]
    congr 1
    rw [← mul_assoc, mul_assoc x, tp hp, mul_smul_comm, smul_mul_assoc]
    simp only [mul_assoc]

theorem split {p : Fin n → Mat C N} (hp : Sys p) (O : Finset (Fin n)) (v : Fin N → C)
    (hs : ∀ k, k ∉ O → p k *ᵥ v = 0) (M : Mat C N) : M *ᵥ v = ∑ k ∈ O, (M * p k) *ᵥ v := by
  have h1 : M *ᵥ v = ∑ k, (M * p k) *ᵥ v := by
    conv_lhs => rw [← mul_one M, ← hp.1.complete, Finset.mul_sum]
    rw [Matrix.sum_mulVec]
  rw [h1, ← Finset.sum_subset (subset_univ O)]
  intro k _ hk; rw [← mulVec_mulVec, hs k hk, mulVec_zero]

theorem powv (y : Mat C N) (l : C) (v : Fin N → C) (h : y *ᵥ v = l • v) (m : ℕ) :
    (y ^ m) *ᵥ v = l ^ m • v := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, ← mulVec_mulVec, h, mulVec_smul, ih, smul_smul, pow_succ']

theorem root_of (M : Mat C N) (β : C) (v : Fin N → C) (hv : v ≠ 0) (h : M *ᵥ v = β • v) :
    M.charpoly.IsRoot β := by
  rw [Polynomial.IsRoot.def, eval_charpoly, ← exists_mulVec_eq_zero_iff]
  refine ⟨v, hv, ?_⟩
  rw [sub_mulVec, h]
  ext a
  simp [Matrix.scalar_apply]

theorem eig {p : Fin n → Mat C N} {x : Mat C N} {π : Equiv.Perm (Fin n)} (hp : Sys p)
    (hxu : IsUnit x) (hx : ∀ j, x * p j = p (π j) * x) (τ : Fin n → C) (hτ : ∀ j, τ j ≠ 0)
    (i : Fin n) (l : C) (v : Fin N → C) (hv : v ≠ 0) (hy : (x * ∑ j, τ j • p j) *ᵥ v = l • v)
    (hs : ∀ k, ¬ π.SameCycle i k → p k *ᵥ v = 0) :
    ∃ β : C, β ≠ 0 ∧ (x ^ (univ.filter (fun m => π.SameCycle i m)).card).charpoly.IsRoot β ∧
      l ^ (univ.filter (fun m => π.SameCycle i m)).card =
        (∏ k ∈ univ.filter (fun m => π.SameCycle i m), τ k) * β := by
  have hs' : ∀ k, k ∉ univ.filter (fun m => π.SameCycle i m) → p k *ᵥ v = 0 :=
    fun k hk => hs k (by simpa using hk)
  have hQ : (∏ k ∈ univ.filter (fun m => π.SameCycle i m), τ k) ≠ 0 :=
    prod_ne_zero_iff.2 fun k _ => hτ k
  have hk : ∀ k ∈ univ.filter (fun m => π.SameCycle i m),
      (x * ∑ j, τ j • p j) ^ (univ.filter (fun m => π.SameCycle i m)).card * p k =
        (∏ k ∈ univ.filter (fun m => π.SameCycle i m), τ k) •
          (x ^ (univ.filter (fun m => π.SameCycle i m)).card * p k) := by
    intro k hk
    have hik : π.SameCycle i k := by simpa using hk
    rw [ypow hp hx]
    congr 1
    rw [filt_eq π hik, card_orbit, prod_orbit]
  have key : (∏ k ∈ univ.filter (fun m => π.SameCycle i m), τ k) •
      (x ^ (univ.filter (fun m => π.SameCycle i m)).card *ᵥ v) =
        l ^ (univ.filter (fun m => π.SameCycle i m)).card • v := by
    rw [← powv _ _ _ hy, split hp _ v hs' (x ^ _),
      split hp _ v hs' ((x * ∑ j, τ j • p j) ^ _), smul_sum]
    refine sum_congr rfl fun k hk' => ?_
    rw [hk k hk', smul_mulVec]
  have hxc := hxu.pow (univ.filter (fun m => π.SameCycle i m)).card
  have hl : l ^ (univ.filter (fun m => π.SameCycle i m)).card ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at key
    have h2 := (smul_eq_zero.1 key).resolve_left hQ
    exact hv ((mulVec_injective_iff_isUnit.2 hxc) (by rw [h2, mulVec_zero]))
  refine ⟨_, div_ne_zero hl hQ, root_of _ _ v hv ?_, by field_simp⟩
  rw [div_eq_inv_mul, ← smul_smul, ← key, smul_smul, inv_mul_cancel₀ hQ, one_smul]

theorem GenSpec_of : GenSpec := by
  intro C _ N n p x π hp hxu hx
  classical
  refine ⟨⋃ a : Fin (n + 1), ⋃ b : Fin (n + 1), Set.image2 (fun β β' => β' ^ (a : ℕ) / β ^ (b : ℕ))
    (↑(x ^ (a : ℕ)).charpoly.roots.toFinset) (↑(x ^ (b : ℕ)).charpoly.roots.toFinset), ?_, ?_⟩
  · exact Set.finite_iUnion fun a => Set.finite_iUnion fun b =>
      (Finset.finite_toSet _).image2 _ (Finset.finite_toSet _)
  intro τ hτ hml i j hij l v w hv hw hyv hyw hsv hsw
  obtain ⟨β, hβ0, hβr, hβ⟩ := eig hp hxu hx τ hτ i l v hv hyv hsv
  obtain ⟨β', hβ0', hβr', hβ'⟩ := eig hp hxu hx τ hτ j l w hw hyw hsw
  have hO : (univ.filter (fun m => π.SameCycle i m)).Nonempty := ⟨i, mem_filter.2 ⟨mem_univ _, Equiv.Perm.SameCycle.refl _ _⟩⟩
  have hO' : (univ.filter (fun m => π.SameCycle j m)).Nonempty := ⟨j, mem_filter.2 ⟨mem_univ _, Equiv.Perm.SameCycle.refl _ _⟩⟩
  have hd : Disjoint (univ.filter (fun m => π.SameCycle i m)) (univ.filter (fun m => π.SameCycle j m)) := by
    rw [Finset.disjoint_left]
    intro m h1 h2
    simp only [mem_filter, mem_univ, true_and] at h1 h2
    exact hij (h1.trans h2.symm)
  have hc : ∀ O : Finset (Fin n), O.card < n + 1 := fun O =>
    Nat.lt_succ_of_le ((card_le_univ O).trans (by simp))
  refine hml _ _ hO hO' hd (β' ^ (univ.filter (fun m => π.SameCycle i m)).card /
    β ^ (univ.filter (fun m => π.SameCycle j m)).card) ?_ ?_
  · refine Set.mem_iUnion.2 ⟨⟨_, hc (univ.filter (fun m => π.SameCycle i m))⟩, Set.mem_iUnion.2
      ⟨⟨_, hc (univ.filter (fun m => π.SameCycle j m))⟩, Set.mem_image2_of_mem ?_ ?_⟩⟩
    · simp only [Finset.mem_coe, Multiset.mem_toFinset]
      exact (Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).2 hβr
    · simp only [Finset.mem_coe, Multiset.mem_toFinset]
      exact (Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).2 hβr'
  · rw [div_mul_eq_mul_div, eq_div_iff (pow_ne_zero _ hβ0), ← mul_pow, ← hβ, ← pow_mul,
      ← mul_pow, mul_comm β', ← hβ', ← pow_mul, mul_comm]

end LateralTheory.DivDb.GenSpecProof
end

-- bundled from Development.EtaleCohomology.DivisorCycles.GradePf
section
open Matrix PositivityTheory.AutomorphicGaloisHodgeTate.Div Polynomial
namespace LateralTheory.DivDb.GradePf

section
variable {C : Type} [Field C] {N n : ℕ}

noncomputable def adX (X : Mat C N) : Module.End C (Mat C N) :=
  LinearMap.mulLeft C X - LinearMap.mulRight C X

lemma adX_apply (X Y : Mat C N) : adX X Y = X * Y - Y * X := by
  simp [adX]

lemma pow_mem (f : Module.End C (Mat C N)) (g : Submodule C (Mat C N))
    (hf : ∀ Y ∈ g, f Y ∈ g) (k : ℕ) : ∀ Y ∈ g, (f ^ k) Y ∈ g := by
  induction k with
  | zero => intro Y hY; simpa using hY
  | succ k ih => intro Y hY; rw [pow_succ', Module.End.mul_apply]; exact hf _ (ih Y hY)

lemma aeval_mem (f : Module.End C (Mat C N)) (g : Submodule C (Mat C N))
    (hf : ∀ Y ∈ g, f Y ∈ g) (q : C[X]) : ∀ Y ∈ g, aeval f q Y ∈ g := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    intro Y hY; simp only [map_add (f := _), LinearMap.add_apply]; exact g.add_mem (hp Y hY) (hq Y hY)
  | monomial k a =>
    intro Y hY
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact g.smul_mem _ (pow_mem f g hf k Y hY)

lemma pow_eig (f : Module.End C (Mat C N)) (Z : Mat C N) (c : C) (h : f Z = c • Z) (k : ℕ) :
    (f ^ k) Z = c ^ k • Z := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, map_smul, h, smul_smul, pow_succ]

lemma aeval_eig (f : Module.End C (Mat C N)) (Z : Mat C N) (c : C) (h : f Z = c • Z) (q : C[X]) :
    aeval f q Z = q.eval c • Z := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, hp, hq, eval_add, add_smul]
  | monomial k a =>
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, pow_eig f Z c h, smul_smul,
      eval_monomial]

lemma lac_key [CharZero C] {e : Fin n → C} (hL : IsLac e) {i j k l : Fin n} (hij : i ≠ j)
    (h : e i - e j = e k - e l) : k = i ∧ l = j := by
  have inj := isLac_inj hL
  have h' : e i + e l = e k + e j := by linear_combination h
  by_contra hne
  have hki : k ≠ i := by
    intro hk; rw [hk] at h'
    exact hne ⟨hk, inj (by linear_combination h')⟩
  have hlj : l ≠ j := by
    intro hl; rw [hl] at h'
    exact hne ⟨(inj (by linear_combination h')).symm, hl⟩
  have hkl : k ≠ l := by
    intro hk; rw [hk] at h; exact hij (inj (by linear_combination h))
  by_cases hil : i = l
  · subst hil
    by_cases hkj : k = j
    · subst hkj
      exact hki (inj (mul_left_cancel₀ (two_ne_zero (α := C)) (by linear_combination -h')))
    · have := hL {i} {k, j} (by simp) (by simp)
        (by simp [Finset.disjoint_left]; exact ⟨hki.symm, hij⟩)
      apply this
      rw [Finset.card_pair hkj, Finset.sum_pair hkj]; simp; linear_combination h'
  · by_cases hkj : k = j
    · subst hkj
      have := hL {i, l} {k} (by simp) (by simp)
        (by simp [Finset.disjoint_left]; exact ⟨hij, hlj⟩)
      apply this
      rw [Finset.card_pair hil, Finset.sum_pair hil]; simp; linear_combination h'
    · have := hL {i, l} {k, j} (by simp) (by simp)
        (by simp [Finset.disjoint_left]; exact ⟨⟨hki.symm, hij⟩, hkl.symm, hlj⟩)
      apply this
      rw [Finset.card_pair hil, Finset.sum_pair hil, Finset.card_pair hkj, Finset.sum_pair hkj]
      rw [h']
end

end LateralTheory.DivDb.GradePf

namespace LateralTheory.DivDb
open LateralTheory.DivDb.GradePf

theorem Grade_of : Grade := by
  intro C _ _ N n p e g hS hL hg Y hY i j hij
  set X := ∑ i, e i • p i with hXdef
  have hco := hS.1
  have hid : ∀ k, p k * p k = p k := fun k => hco.idem k
  have hor : ∀ k l, k ≠ l → p k * p l = 0 := fun k l h => hco.ortho h
  have hsum : ∑ k, p k = 1 := hco.complete
  have hXp : ∀ k, X * p k = e k • p k := by
    intro k; rw [hXdef, Finset.sum_mul]; simp only [smul_mul_assoc]
    rw [Finset.sum_eq_single k]
    · rw [hid]
    · intro b _ hb; rw [hor b k hb, smul_zero]
    · simp
  have hpX : ∀ k, p k * X = e k • p k := by
    intro k; rw [hXdef, Finset.mul_sum]; simp only [mul_smul_comm]
    rw [Finset.sum_eq_single k]
    · rw [hid]
    · intro b _ hb; rw [hor k b (Ne.symm hb), smul_zero]
    · simp
  have hdec : Y = ∑ kl : Fin n × Fin n, p kl.1 * Y * p kl.2 := by
    have : (∑ k, p k) * Y * (∑ l, p l) = ∑ kl : Fin n × Fin n, p kl.1 * Y * p kl.2 := by
      rw [Finset.sum_mul, Finset.sum_mul, Fintype.sum_prod_type]; simp_rw [Finset.mul_sum]
    rw [← this, hsum, one_mul, mul_one]
  have heig : ∀ kl : Fin n × Fin n, adX X (p kl.1 * Y * p kl.2) = (e kl.1 - e kl.2) • (p kl.1 * Y * p kl.2) := by
    intro kl
    rw [adX_apply, ← mul_assoc, ← mul_assoc, hXp, mul_assoc (p kl.1 * Y), hpX]
    simp [sub_smul, smul_mul_assoc, mul_smul_comm]
  have hstab : ∀ Z ∈ g, adX X Z ∈ g := fun Z hZ => by rw [adX_apply]; exact hg Z hZ
  let q : C[X] := ∏ kl ∈ (Finset.univ : Finset (Fin n × Fin n)).erase (i, j), (Polynomial.X - Polynomial.C (e kl.1 - e kl.2))
  have hq : aeval (adX X) q Y = q.eval (e i - e j) • (p i * Y * p j) := by
    conv_lhs => rw [hdec]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp_rw [aeval_eig (adX X) _ _ (heig _)]
    rw [Finset.sum_eq_single (i, j)]
    · intro b _ hb
      have : q.eval (e b.1 - e b.2) = 0 := by
        simp only [q, eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hb, Finset.mem_univ _⟩) (by simp)
      rw [this, zero_smul]
    · simp
  have hq0 : q.eval (e i - e j) ≠ 0 := by
    simp only [q, eval_prod]
    rw [Finset.prod_ne_zero_iff]
    intro kl hkl
    simp only [eval_sub, eval_X, eval_C]
    intro h0
    have := lac_key hL hij (sub_eq_zero.mp h0)
    exact (Finset.mem_erase.mp hkl).1 (Prod.ext this.1 this.2)
  have hm := g.smul_mem (q.eval (e i - e j))⁻¹ (aeval_mem (adX X) g hstab q Y hY)
  rwa [hq, smul_smul, inv_mul_cancel₀ hq0, one_smul] at hm

end LateralTheory.DivDb
end

-- bundled from Development.EtaleCohomology.DivisorCycles.MatUnitsOf
section
open Matrix

namespace LateralTheory.DivDb.MatrixUnitConstruction
open LateralTheory.DivDb

variable {C : Type} [Field C] {N n : ℕ}

def Pr (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N) (i j : Fin n) (x y : Mat C N) : Prop :=
  x ∈ A ∧ y ∈ A ∧ p i * x * p j = x ∧ p j * y * p i = y ∧ x * y = p i ∧ y * x = p j

def rel (A : Subalgebra C (Mat C N)) (p : Fin n → Mat C N) (i j : Fin n) : Prop := ∃ x y, Pr A p i j x y

section
variable {A : Subalgebra C (Mat C N)} {p : Fin n → Mat C N}

lemma idem (hp : Sys p) (i : Fin n) : p i * p i = p i := (hp.1.idem i).eq

lemma idemL (hp : Sys p) (i : Fin n) (X : Mat C N) : p i * (p i * X) = p i * X := by
  rw [← mul_assoc, idem hp i]

lemma sand_left (hp : Sys p) {i j : Fin n} {x : Mat C N} (h : p i * x * p j = x) : p i * x = x := by
  conv_lhs => rw [← h]
  simp only [mul_assoc, idemL hp i]
  simpa only [mul_assoc] using h

lemma sand_right (hp : Sys p) {i j : Fin n} {x : Mat C N} (h : p i * x * p j = x) : x * p j = x := by
  conv_lhs => rw [← h]
  rw [mul_assoc (p i * x), idem hp j, h]

lemma pr_ne (hp : Sys p) {i j : Fin n} {x y : Mat C N} (h : Pr A p i j x y) : x ≠ 0 := by
  rintro rfl
  exact hp.2 i (by rw [← h.2.2.2.2.1, zero_mul])

lemma pr_symm {i j : Fin n} {x y : Mat C N} (h : Pr A p i j x y) : Pr A p j i y x :=
  ⟨h.2.1, h.1, h.2.2.2.1, h.2.2.1, h.2.2.2.2.2, h.2.2.2.2.1⟩

lemma pr_refl (hp : Sys p) (hc : Corner A p) (i : Fin n) : Pr A p i i (p i) (p i) :=
  ⟨hc.1 i, hc.1 i, by rw [idem hp i, idem hp i], by rw [idem hp i, idem hp i], idem hp i, idem hp i⟩

lemma pr_trans (hp : Sys p) {i j k : Fin n} {x y x' y' : Mat C N} (h : Pr A p i j x y)
    (h' : Pr A p j k x' y') : Pr A p i k (x * x') (y' * y) := by
  refine ⟨A.mul_mem h.1 h'.1, A.mul_mem h'.2.1 h.2.1, ?_, ?_, ?_, ?_⟩
  · rw [← mul_assoc, sand_left hp h.2.2.1, mul_assoc, sand_right hp h'.2.2.1]
  · rw [← mul_assoc, sand_left hp h'.2.2.2.1, mul_assoc, sand_right hp h.2.2.2.1]
  · rw [show x * x' * (y' * y) = x * (x' * y') * y by simp only [mul_assoc], h'.2.2.2.2.1,
      sand_right hp h.2.2.1, h.2.2.2.2.1]
  · rw [show y' * y * (x * x') = y' * (y * x) * x' by simp only [mul_assoc], h.2.2.2.2.2,
      sand_right hp h'.2.2.2.1, h'.2.2.2.2.2]

lemma partner (hp : Sys p) (hc : Corner A p) (hA : NoNil A) {i j : Fin n} {Y : Mat C N}
    (hYA : Y ∈ A) (hYl : p i * Y = Y) (hYr : Y * p j = Y) (hY0 : Y ≠ 0) :
    ∃ w, Pr A p i j Y w := by
  obtain ⟨b, hb, hnil⟩ : ∃ b ∈ A, ¬ IsNilpotent (b * Y) := by
    by_contra h
    push Not at h
    exact hY0 (hA Y hYA h)
  have hwA : p j * b * p i ∈ A := A.mul_mem (A.mul_mem (hc.1 j) hb) (hc.1 i)
  obtain ⟨c, hc1⟩ := hc.2 (Y * b) (A.mul_mem hYA hb) i
  obtain ⟨d, hd1⟩ := hc.2 (b * Y) (A.mul_mem hb hYA) j
  have hYw : Y * (p j * b * p i) = c • p i := by
    rw [← hc1]
    calc Y * (p j * b * p i) = (Y * p j) * b * p i := by simp only [mul_assoc]
      _ = (p i * Y) * b * p i := by rw [hYr, hYl]
      _ = p i * (Y * b) * p i := by simp only [mul_assoc]
  have hwY : (p j * b * p i) * Y = d • p j := by
    rw [← hd1]
    calc p j * b * p i * Y = p j * b * (p i * Y) := by simp only [mul_assoc]
      _ = p j * b * (Y * p j) := by rw [hYl, hYr]
      _ = p j * (b * Y) * p j := by simp only [mul_assoc]
  have e1 : Y * (p j * b * p i) * Y = c • Y := by rw [hYw, smul_mul_assoc, hYl]
  have e2 : Y * (p j * b * p i) * Y = d • Y := by rw [mul_assoc, hwY, mul_smul_comm, hYr]
  have hcd : c = d := by
    by_contra h
    have h3 : (c - d) • Y = 0 := by rw [sub_smul, ← e1, ← e2, sub_self]
    exact hY0 ((smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr h))
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hnil
    refine ⟨2, ?_⟩
    have h0 : Y * b * Y = 0 := by
      have : Y * b * Y = Y * (p j * b * p i) * Y := by
        rw [show Y * (p j * b * p i) * Y = (Y * p j) * b * (p i * Y) by simp only [mul_assoc], hYr, hYl]
      rw [this, e1, zero_smul]
    rw [pow_two, show b * Y * (b * Y) = b * (Y * b * Y) by simp only [mul_assoc], h0, mul_zero]
  refine ⟨c⁻¹ • (p j * b * p i), hYA, A.smul_mem hwA _, ?_, ?_, ?_, ?_⟩
  · rw [hYl, hYr]
  · rw [mul_smul_comm, smul_mul_assoc]
    congr 1
    simp only [mul_assoc, idem hp i, idemL hp j]
  · rw [mul_smul_comm, hYw, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  · rw [smul_mul_assoc, hwY, ← hcd, smul_smul, inv_mul_cancel₀ hc0, one_smul]

lemma oneDim (hp : Sys p) (hc : Corner A p) {i j : Fin n} {x y : Mat C N} (h : Pr A p i j x y)
    {a : Mat C N} (ha : a ∈ A) : ∃ c : C, p i * a * p j = c • x := by
  obtain ⟨c, hc1⟩ := hc.2 (a * p j * y) (A.mul_mem (A.mul_mem ha (hc.1 j)) h.2.1) i
  refine ⟨c, ?_⟩
  have hy : y * p i = y := sand_right hp h.2.2.2.1
  have h1 : p i * a * p j * y = c • p i := by
    calc p i * a * p j * y = p i * a * p j * (y * p i) := by rw [hy]
      _ = p i * (a * p j * y) * p i := by simp only [mul_assoc]
      _ = c • p i := hc1
  calc p i * a * p j = p i * a * p j * p j := by rw [mul_assoc (p i * a) (p j) (p j), idem hp j]
    _ = p i * a * p j * (y * x) := by rw [h.2.2.2.2.2]
    _ = (p i * a * p j * y) * x := by simp only [mul_assoc]
    _ = c • x := by rw [h1, smul_mul_assoc, sand_left hp h.2.2.1]

lemma rel_equiv (hp : Sys p) (hc : Corner A p) : Equivalence (rel A p) := by
  refine ⟨fun i => ⟨_, _, pr_refl hp hc i⟩, ?_, ?_⟩
  · rintro i j ⟨_, _, h⟩
    exact ⟨_, _, pr_symm h⟩
  · rintro i j k ⟨_, _, h⟩ ⟨_, _, h'⟩
    exact ⟨_, _, pr_trans hp h h'⟩

end

open Classical in
theorem MatUnits_of : MatrixUnits₂ := by
  intro C _ N n A p hp hc hA
  have heq := rel_equiv hp hc
  let s : Setoid (Fin n) := ⟨rel A p, heq⟩
  obtain ⟨r, hr, hreq⟩ : ∃ r : Fin n → Fin n, (∀ i, ∃ x y, Pr A p i (r i) x y) ∧
      ∀ i j, rel A p i j → r i = r j :=
    ⟨fun i => (Quotient.mk s i).out, fun i => heq.symm (Quotient.mk_out (s := s) i),
      fun i j h => congrArg Quotient.out (Quotient.sound (s := s) h)⟩
  choose X Y hXY using hr
  have pairE : ∀ i j, rel A p i j → Pr A p i j (X i * Y j) (X j * Y i) := by
    intro i j h
    have h2 := hXY j
    rw [← hreq i j h] at h2
    exact pr_trans hp (hXY i) (pr_symm h2)
  refine ⟨fun i j => if rel A p i j then X i * Y j else 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    by_cases h : rel A p i j
    · simp only [if_pos h]; exact (pairE i j h).1
    · simp only [if_neg h]; exact A.zero_mem
  · intro i
    simp only [if_pos (heq.refl i)]
    exact (hXY i).2.2.2.2.1
  · intro i j
    by_cases h : rel A p i j
    · simp only [if_pos h]; exact (pairE i j h).2.2.1
    · simp only [if_neg h, mul_zero, zero_mul]
  · intro i j hne
    have h : rel A p i j := by
      by_contra h
      simp only [if_neg h] at hne
      exact hne rfl
    simp only [if_pos (heq.symm h)]
    exact pr_ne hp (pairE j i (heq.symm h))
  · intro i j k h1 h2
    have hij : rel A p i j := by
      by_contra h
      simp only [if_neg h] at h1
      exact h1 rfl
    have hjk : rel A p j k := by
      by_contra h
      simp only [if_neg h] at h2
      exact h2 rfl
    have hik := heq.trans hij hjk
    simp only [if_pos hij, if_pos hjk, if_pos hik]
    refine ⟨?_, pr_ne hp (pairE i k hik)⟩
    rw [show X i * Y j * (X j * Y k) = X i * (Y j * X j) * Y k by simp only [mul_assoc],
      (hXY j).2.2.2.2.2, ← hreq i j hij, sand_right hp (hXY i).2.2.1]
  · intro a ha i j
    by_cases h : rel A p i j
    · simp only [if_pos h]; exact oneDim hp hc (pairE i j h) ha
    · refine ⟨0, ?_⟩
      simp only [if_neg h, smul_zero]
      by_contra h'
      obtain ⟨w, hw⟩ := partner (i := i) (j := j) hp hc hA (A.mul_mem (A.mul_mem (hc.1 i) ha) (hc.1 j))
        (by simp only [mul_assoc, idemL hp i]) (by rw [mul_assoc _ (p j), idem hp j]) h'
      exact h ⟨_, _, hw⟩

end LateralTheory.DivDb.MatrixUnitConstruction
end

