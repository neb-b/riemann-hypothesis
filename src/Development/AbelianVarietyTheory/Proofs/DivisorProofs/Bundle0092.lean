module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PerfectionExistsUniqueSubMatrixFrobeniusEq
section
namespace GlobalTheory

open Matrix

theorem sub_apply_bijective_of_iterate_eq_zero {M : Type} [AddCommGroup M] (L : M →+ M) (K : ℕ)
    (hK : ∀ z, (⇑L)^[K] z = 0) : Function.Bijective (fun z => z - L z) := by
  constructor
  · intro a b hab
    have hab' : a - L a = b - L b := hab
    have hfix : L (a - b) = a - b := by
      rw [map_sub]
      rw [sub_eq_sub_iff_sub_eq_sub] at hab'
      exact hab'.symm
    have h1 : ∀ m, (⇑L)^[m] (a - b) = a - b := by
      intro m
      induction m with
      | zero => rfl
      | succ m ih => rw [Function.iterate_succ_apply', ih, hfix]
    exact sub_eq_zero.mp ((h1 K).symm.trans (hK _))
  · intro c
    refine ⟨∑ k ∈ Finset.range K, (⇑L)^[k] c, ?_⟩
    show (∑ k ∈ Finset.range K, (⇑L)^[k] c) - L (∑ k ∈ Finset.range K, (⇑L)^[k] c) = c
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    have hs : ∀ k, L ((⇑L)^[k] c) = (⇑L)^[k + 1] c := fun k =>
      (Function.iterate_succ_apply' (⇑L) k c).symm
    simp only [hs]
    rw [← Finset.sum_sub_distrib, Finset.sum_range_sub', hK, sub_zero]
    rfl

noncomputable def perfLevelOp (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p]
    {ι : Type} [Fintype ι] (Q : Matrix ι ι (Perfection S p)) (n : ℕ) : (ι → S) →+ (ι → S) where
  toFun w := (Q.map (Perfection.coeff S p n)).mulVec fun k => frobenius S p (w k)
  map_zero' := by ext i; simp [Matrix.mulVec, dotProduct]
  map_add' a b := by ext i; simp [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]

theorem perfLevelOp_apply (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p]
    {ι : Type} [Fintype ι] (Q : Matrix ι ι (Perfection S p)) (n : ℕ) (w : ι → S) :
    perfLevelOp p S Q n w = (Q.map (Perfection.coeff S p n)).mulVec fun k => frobenius S p (w k) :=
  rfl

theorem perfLevelOp_coeff (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p]
    {ι : Type} [Fintype ι] (Q : Matrix ι ι (Perfection S p)) (n : ℕ) (x : ι → Perfection S p) :
    (fun i => Perfection.coeff S p n ((x - Q.mulVec (fun k => frobenius (Perfection S p) p (x k))) i))
      = (fun i => Perfection.coeff S p n (x i))
        - perfLevelOp p S Q n (fun i => Perfection.coeff S p n (x i)) := by
  ext i
  simp only [Pi.sub_apply, map_sub, perfLevelOp_apply]
  congr 1
  rw [RingHom.map_mulVec]
  have hc : (Perfection.coeff S p n) ∘ (fun k => frobenius (Perfection S p) p (x k))
      = fun k => frobenius S p (Perfection.coeff S p n (x k)) := by
    funext k
    simp [frobenius_def, map_pow]
  rw [hc]

theorem perfLevelOp_frobenius (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p]
    {ι : Type} [Fintype ι] (Q : Matrix ι ι (Perfection S p)) (n : ℕ) (w : ι → S) :
    (fun i => frobenius S p ((w - perfLevelOp p S Q (n + 1) w) i))
      = (fun i => frobenius S p (w i)) - perfLevelOp p S Q n (fun i => frobenius S p (w i)) := by
  ext i
  simp only [perfLevelOp_apply, Pi.sub_apply, map_sub]
  congr 1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
  congr 1
  ext j
  congr 1
  rw [frobenius_def, Perfection.coeff_pow_p']

theorem perfection_frobenius_solve : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p] (ι : Type) [Fintype ι] (Q : Matrix ι ι (Perfection S p)), (∀ n : ℕ, ∃ K : ℕ, ∀ z : ι → S, (fun w : ι → S => (Q.map (Perfection.coeff S p n)).mulVec fun k => frobenius S p (w k))^[K] z = 0) → ∀ c : ι → Perfection S p, ∃! x : ι → Perfection S p, x - Q.mulVec (fun k => frobenius (Perfection S p) p (x k)) = c := by
  intro p _ S _ _ ι _ Q hnil c
  have bij : ∀ n, Function.Bijective (fun z => z - perfLevelOp p S Q n z) := by
    intro n
    obtain ⟨K, hK⟩ := hnil n
    exact sub_apply_bijective_of_iterate_eq_zero _ K hK
  let z : ℕ → ι → S := fun n => Function.surjInv (bij n).2 (fun i => Perfection.coeff S p n (c i))
  have hz : ∀ n, z n - perfLevelOp p S Q n (z n) = fun i => Perfection.coeff S p n (c i) :=
    fun n => Function.surjInv_eq (bij n).2 _
  have compat : ∀ n k, z (n + 1) k ^ p = z n k := by
    intro n
    have h : (fun k => frobenius S p (z (n + 1) k)) = z n := by
      apply (bij n).1
      show (fun k => frobenius S p (z (n + 1) k))
          - perfLevelOp p S Q n (fun k => frobenius S p (z (n + 1) k)) = z n - perfLevelOp p S Q n (z n)
      rw [← perfLevelOp_frobenius, hz (n + 1), hz n]
      ext i
      simp [frobenius_def, Perfection.coeff_pow_p']
    intro k
    have := congrFun h k
    simpa [frobenius_def] using this
  let x : ι → Perfection S p := fun k => ⟨fun n => z n k, fun n => compat n k⟩
  refine ⟨x, ?_, ?_⟩
  · funext i
    apply Perfection.ext
    intro n
    have h1 := congrFun (perfLevelOp_coeff p S Q n x) i
    have hx : (fun i => Perfection.coeff S p n (x i)) = z n := rfl
    rw [hx, hz n] at h1
    exact h1
  · intro y hy
    funext k
    apply Perfection.ext
    intro n
    have h2 : (fun i => Perfection.coeff S p n (y i)) = z n := by
      apply (bij n).1
      show (fun i => Perfection.coeff S p n (y i))
          - perfLevelOp p S Q n (fun i => Perfection.coeff S p n (y i)) = z n - perfLevelOp p S Q n (z n)
      rw [← perfLevelOp_coeff, hy, hz n]
    exact congrFun h2 k

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermInvariantOfConsSwapAndTail
section
open Equiv

theorem GlobalTheory.perm_invariant_of_cons_swap :
  ∀ (α : Type 1) (n : ℕ) (F : (Fin (n + 2) → α) → ℝ), (∀ (a : α) (L : Fin (n + 1) → α) (e : Equiv.Perm (Fin (n + 1))), F (Fin.cons a fun i => L (e i)) = F (Fin.cons a L)) → (∀ (a b : α) (L : Fin n → α), F (Fin.cons a (Fin.cons b L : Fin (n + 1) → α)) = F (Fin.cons b (Fin.cons a L : Fin (n + 1) → α))) → ∀ (L : Fin (n + 2) → α) (e : Equiv.Perm (Fin (n + 2))), F (fun i => L (e i)) = F L := by
  intro α n F h1 h2
  let S : Subgroup (Equiv.Perm (Fin (n+2))) :=
    { carrier := {σ | ∀ L : Fin (n+2) → α, F (fun i => L (σ i)) = F L}
      mul_mem' := by
        intro σ τ hσ hτ
        have hσ' : ∀ L : Fin (n+2) → α, F (fun i => L (σ i)) = F L := hσ
        have hτ' : ∀ L : Fin (n+2) → α, F (fun i => L (τ i)) = F L := hτ
        show ∀ L : Fin (n+2) → α, F (fun i => L ((σ * τ) i)) = F L
        intro L
        calc F (fun i => L ((σ * τ) i)) = F (fun i => L (σ (τ i))) := rfl
          _ = F (fun j => L (σ j)) := hτ' (fun j => L (σ j))
          _ = F L := hσ' L
      one_mem' := by
        show ∀ L : Fin (n+2) → α, F (fun i => L ((1 : Equiv.Perm (Fin (n+2))) i)) = F L
        intro L; rfl
      inv_mem' := by
        intro σ hσ
        have hσ' : ∀ L : Fin (n+2) → α, F (fun i => L (σ i)) = F L := hσ
        show ∀ L : Fin (n+2) → α, F (fun i => L (σ⁻¹ i)) = F L
        intro L
        calc F (fun i => L (σ⁻¹ i)) = F (fun i => L (σ⁻¹ (σ i))) := (hσ' (fun j => L (σ⁻¹ j))).symm
          _ = F L := by simp }
  have memS : ∀ σ, σ ∈ S ↔ ∀ L : Fin (n+2) → α, F (fun i => L (σ i)) = F L := fun σ => Iff.rfl
  have hfix : ∀ e : Equiv.Perm (Fin (n+1)), Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), e) ∈ S := by
    intro e
    rw [memS]
    intro L
    have hc : (fun i => L (Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), e) i)) = Fin.cons (L 0) (fun i => Fin.tail L (e i)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simp [Equiv.Perm.decomposeFin_symm_apply_succ, Fin.tail]
    rw [hc, h1 (L 0) (Fin.tail L) e, Fin.cons_self_tail]
  have hswap : Equiv.swap (0 : Fin (n+2)) 1 ∈ S := by
    rw [memS]
    intro L
    have e1 : L = Fin.cons (L 0) (Fin.cons (L 1) (fun i => L i.succ.succ) : Fin (n+1) → α) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · refine Fin.cases ?_ (fun k => ?_) j
        · rfl
        · rfl
    have e2 : (fun i => L (Equiv.swap (0 : Fin (n+2)) 1 i)) = Fin.cons (L 1) (Fin.cons (L 0) (fun i => L i.succ.succ) : Fin (n+1) → α) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · refine Fin.cases ?_ (fun k => ?_) j
        · simp
        · have a1 : (k.succ.succ : Fin (n+2)) ≠ 0 := Fin.succ_ne_zero _
          have a2 : (k.succ.succ : Fin (n+2)) ≠ 1 := by
            intro h
            rw [← Fin.succ_zero_eq_one] at h
            exact Fin.succ_ne_zero _ (Fin.succ_injective _ h)
          simp [Equiv.swap_apply_of_ne_of_ne a1 a2]
    rw [e2, ← h2 (L 0) (L 1)]
    exact congrArg F e1.symm
  have hp : ∀ p : Fin (n+2), Equiv.swap (0 : Fin (n+2)) p ∈ S := by
    intro p
    refine Fin.cases ?_ (fun k => ?_) p
    · rw [Equiv.swap_self]; exact S.one_mem
    · have h0 : Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), Equiv.swap (0 : Fin (n+1)) k) 0 = 0 := by simp
      have h1' : Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), Equiv.swap (0 : Fin (n+1)) k) 1 = k.succ := by
        rw [← Fin.succ_zero_eq_one, Equiv.Perm.decomposeFin_symm_apply_succ]
        simp
      have hc := Equiv.swap_apply_apply (Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), Equiv.swap (0 : Fin (n+1)) k)) 0 1
      rw [h0, h1'] at hc
      rw [hc]
      exact S.mul_mem (S.mul_mem (hfix _) hswap) (S.inv_mem (hfix _))
  have hdec : ∀ (p : Fin (n+2)) (e : Equiv.Perm (Fin (n+1))),
      Equiv.Perm.decomposeFin.symm (p, e) = Equiv.swap 0 p * Equiv.Perm.decomposeFin.symm ((0 : Fin (n+2)), e) := by
    intro p e
    ext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [Equiv.Perm.decomposeFin_symm_apply_succ]
  intro L e
  have he : e ∈ S := by
    rw [← Equiv.Perm.decomposeFin.symm_apply_apply e]
    rcases Equiv.Perm.decomposeFin e with ⟨p, e'⟩
    rw [hdec]
    exact S.mul_mem (hp p) (hfix e')
  exact (memS e).1 he L
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicEqOneOfForallPrimeMaximal
section
open PrimeSpectrum

namespace GlobalTheory

variable {R : Type} [CommRing R]

theorem exists_mul_pow_eq_zero_of_forall_isMaximal
    (hR : ∀ P : Ideal R, P.IsPrime → P.IsMaximal) {p : Ideal R} [hp : p.IsPrime] {a : R}
    (ha : a ∈ p) : ∃ t ∉ p, ∃ n : ℕ, t * a ^ n = 0 := by
  by_contra! H
  have hdis : Disjoint ((⊥ : Ideal R) : Set R)
      ((p.primeCompl ⊔ Submonoid.powers a : Submonoid R) : Set R) := by
    rw [Set.disjoint_left]
    rintro x hx hxS
    rw [SetLike.mem_coe, Ideal.mem_bot] at hx
    subst hx
    obtain ⟨y, hy, z, hz, hyz⟩ := Submonoid.mem_sup.mp hxS
    obtain ⟨n, rfl⟩ := hz
    exact H y hy n hyz
  obtain ⟨q, hq, -, hqd⟩ := Ideal.exists_le_prime_disjoint ⊥ _ hdis
  have hqp : q ≤ p := by
    intro x hx
    by_contra hxp
    exact Set.disjoint_left.mp hqd hx
      (Submonoid.mem_sup_left (show x ∈ p.primeCompl from hxp))
  have hqp' := (hR q hq).eq_of_le hp.ne_top hqp
  have haq : a ∉ q := fun h => Set.disjoint_left.mp hqd h
    (Submonoid.mem_sup_right (Submonoid.mem_powers a))
  exact haq (hqp' ▸ ha)

theorem isClopen_basicOpen_of_forall_isMaximal
    (hR : ∀ P : Ideal R, P.IsPrime → P.IsMaximal) (a : R) :
    IsClopen ((basicOpen a : TopologicalSpace.Opens (PrimeSpectrum R)) : Set (PrimeSpectrum R)) := by
  refine ⟨?_, (basicOpen a).isOpen⟩
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  have hax : a ∈ x.asIdeal := by
    simpa [Set.mem_compl_iff, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] using hx
  obtain ⟨t, ht, n, htn⟩ := exists_mul_pow_eq_zero_of_forall_isMaximal hR hax
  refine ⟨(basicOpen t : Set (PrimeSpectrum R)), ?_, (basicOpen t).isOpen, ht⟩
  intro y hy hya
  rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hy hya
  have : t * a ^ n ∈ y.asIdeal := htn ▸ y.asIdeal.zero_mem
  rcases y.isPrime.mem_or_mem this with h | h
  · exact hy h
  · exact hya (y.isPrime.mem_of_pow_mem n h)

theorem exists_isIdempotentElem_mul_of_forall_isMaximal
    (hR : ∀ P : Ideal R, P.IsPrime → P.IsMaximal) (a : R) :
    ∃ e b : R, IsIdempotentElem e ∧ a * b = e ∧ ∀ p : Ideal R, p.IsPrime → a ∉ p → e ∉ p := by
  let c : TopologicalSpace.Clopens (PrimeSpectrum R) :=
    ⟨(basicOpen a : Set (PrimeSpectrum R)), isClopen_basicOpen_of_forall_isMaximal hR a⟩
  let e := (isIdempotentElemEquivClopens (R := R)).symm c
  have he : basicOpen e.1 = basicOpen a := by
    rw [basicOpen_isIdempotentElemEquivClopens_symm]; rfl
  obtain ⟨k, hk⟩ := (basicOpen_le_basicOpen_iff _ _).mp he.le
  have hmem : e.1 ∈ Ideal.span {a} := by
    rw [← e.2.pow_succ_eq k, pow_succ']
    exact Ideal.mul_mem_left _ _ hk
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨e.1, b, e.2, by rw [mul_comm, hb], fun p hp hap => ?_⟩
  have h1 : (⟨p, hp⟩ : PrimeSpectrum R) ∈ basicOpen a := hap
  rw [← he] at h1
  exact h1

theorem free_of_invertible_of_forall_isMaximal
    (hR : ∀ P : Ideal R, P.IsPrime → P.IsMaximal) (M : Type) [AddCommGroup M] [Module R M]
    (hM : Module.Invertible R M) : Module.Free R M := by
  classical
  obtain ⟨S, hS⟩ := ((Module.Invertible.linearEquiv R M).symm 1).exists_finset
  replace hS : 1 = ∑ i ∈ S, i.1 i.2 := by
    simpa [LinearEquiv.symm_apply_eq, Module.Invertible.linearEquiv] using hS
  letI : LinearOrder (Module.Dual R M × M) := IsWellOrder.linearOrder WellOrderingRel
  choose e b he hab hep using
    fun i : Module.Dual R M × M => exists_isIdempotentElem_mul_of_forall_isMaximal hR (i.1 i.2)

  let Q : Module.Dual R M × M → R := fun l => ∏ j ∈ S with j < l, (1 - e j)
  let e' : Module.Dual R M × M → R := fun l => e l * Q l
  have hQi : ∀ l, IsIdempotentElem (Q l) := fun l =>
    Finset.prod_induction _ IsIdempotentElem (fun _ _ h1 h2 => h1.mul h2)
      IsIdempotentElem.one (fun j _ => (he j).one_sub)
  have he'i : ∀ l, IsIdempotentElem (e' l) := fun l => (he l).mul (hQi l)
  have hlt : ∀ k ∈ S, ∀ l ∈ S, k < l → e k * e' l = 0 := by
    intro k hk l _ hkl
    have hmem : k ∈ S.filter (· < l) := Finset.mem_filter.mpr ⟨hk, hkl⟩
    simp only [e', Q]
    rw [← Finset.mul_prod_erase _ _ hmem]
    linear_combination (-(e l * ∏ x ∈ (S.filter (· < l)).erase k, (1 - e x))) * (he k).eq
  have horth : ∀ k ∈ S, ∀ l ∈ S, k ≠ l → e' k * e' l = 0 := by
    intro k hk l hl hkl
    rcases lt_or_gt_of_ne hkl with h | h
    · have := hlt k hk l hl h
      simp only [e'] at this ⊢
      linear_combination Q k * this
    · have := hlt l hl k hk h
      simp only [e'] at this ⊢
      linear_combination Q l * this

  let x : M := ∑ k ∈ S, e' k • k.2
  let φ : Module.Dual R M := ∑ l ∈ S, (b l * e' l) • l.1
  have hφx : φ x = ∑ l ∈ S, e' l := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [φ, x, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
      map_smul, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.sum_eq_single l]
    · have h1 := (he'i l).eq
      have h2 := hab l
      have h3 : e' l * e l = e' l := by
        simp only [e']; linear_combination Q l * (he l).eq
      linear_combination (b l * l.1 l.2) * h1 + e' l * h2 + h3
    · intro k hk hkl
      have := horth l hl k hk (Ne.symm hkl)
      linear_combination (b k * k.1 l.2) * this
    · intro h; exact absurd hl h
  have hsum : ∑ l ∈ S, e' l = 1 - ∏ i ∈ S, (1 - e i) := by
    rw [Finset.prod_one_sub_ordered S e]; ring
  have hunit : IsUnit (1 - ∏ i ∈ S, (1 - e i)) := by
    by_contra hnu
    obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits hnu
    obtain ⟨i, hi, him⟩ : ∃ i ∈ S, i.1 i.2 ∉ m := by
      by_contra! hall
      exact hm.ne_top ((Ideal.eq_top_iff_one _).mpr (hS ▸ Ideal.sum_mem _ hall))
    have hei := hep i m hm.isPrime him
    have h1 : 1 - e i ∈ m := by
      have : e i * (1 - e i) ∈ m := by
        rw [mul_sub, mul_one, (he i).eq, sub_self]; exact m.zero_mem
      exact (hm.isPrime.mem_or_mem this).resolve_left hei
    have hP : ∏ i ∈ S, (1 - e i) ∈ m := by
      rw [← Finset.mul_prod_erase _ _ hi]; exact m.mul_mem_right _ h1
    exact hm.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using m.add_mem hxm hP))
  rw [← hsum, ← hφx] at hunit
  exact .of_equiv <| .symm <| .ofBijective φ (Module.Invertible.bijective_of_surjective <|
    LinearMap.range_eq_top.mp <| Ideal.eq_top_of_isUnit_mem _ ⟨x, rfl⟩ hunit)

theorem pic_eq_one_of_forall_isMaximal :
    ∀ (R : Type) [CommRing R], (∀ P : Ideal R, P.IsPrime → P.IsMaximal) →
      ∀ c : CommRing.Pic R, c = 1 := by
  intro R _ hR c
  have : Subsingleton (CommRing.Pic R) := CommRing.Pic.subsingleton_iff.mpr
    fun M _ _ hM => free_of_invertible_of_forall_isMaximal hR M hM
  exact Subsingleton.elim _ _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicPiIsOfFinOrder
section
open TensorProduct

namespace GlobalTheory

namespace PicPi

variable {ι : Type} {R : ι → Type} [∀ i, CommRing (R i)] [DecidableEq ι]

theorem exists_one_tmul (i : ι) (M : Type) [AddCommGroup M] [Module ((j : ι) → R j) M]
    [Algebra ((j : ι) → R j) (R i)]
    (hA : algebraMap ((j : ι) → R j) (R i) = Pi.evalRingHom R i)
    (z : R i ⊗[(j : ι) → R j] M) : ∃ y : M, (1 : R i) ⊗ₜ y = z := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul r y =>
    refine ⟨(Pi.single i r : (j : ι) → R j) • y, ?_⟩
    rw [← TensorProduct.smul_tmul]
    congr 1
    rw [Algebra.smul_def, hA]
    simp
  | add a b ha hb =>
    obtain ⟨ya, rfl⟩ := ha
    obtain ⟨yb, rfl⟩ := hb
    exact ⟨ya + yb, by rw [TensorProduct.tmul_add]⟩

theorem single_smul_eq_zero (i : ι) (M : Type) [AddCommGroup M] [Module ((j : ι) → R j) M]
    [Algebra ((j : ι) → R j) (R i)]
    (hA : algebraMap ((j : ι) → R j) (R i) = Pi.evalRingHom R i) (y : M)
    (h : (1 : R i) ⊗ₜ[(j : ι) → R j] y = 0) : (Pi.single i 1 : (j : ι) → R j) • y = 0 := by
  let φ : R i →ₗ[(j : ι) → R j] M →ₗ[(j : ι) → R j] M :=
    LinearMap.mk₂ _ (fun r y => (Pi.single i r : (j : ι) → R j) • y)
      (fun r₁ r₂ y => by simp only [Pi.single_add, add_smul])
      (fun s r y => by
        have hs : (Pi.single i (s • r) : (j : ι) → R j) = s * Pi.single i r := by
          ext j
          by_cases hj : j = i
          · subst hj; simp [Algebra.smul_def, hA]
          · simp [hj]
        simp only [hs, mul_smul])
      (fun r y₁ y₂ => smul_add _ _ _)
      (fun s r y => smul_comm _ _ _)
  have := congrArg (TensorProduct.lift φ) h
  simpa [φ] using this

variable [Fintype ι]

theorem eq_one_of_forall (M : CommRing.Pic ((j : ι) → R j))
    (h : ∀ i, CommRing.Pic.mapRingHom (Pi.evalRingHom R i) M = 1) : M = 1 := by
  letI inst : ∀ i, Algebra ((j : ι) → R j) (R i) := fun i => (Pi.evalRingHom R i).toAlgebra
  have hA : ∀ i, algebraMap ((j : ι) → R j) (R i) = Pi.evalRingHom R i := fun i => rfl
  have e : ∀ i, (R i ⊗[(j : ι) → R j] M) ≃ₗ[R i] R i := by
    intro i
    have hi := h i
    rw [← hA i, CommRing.Pic.mapRingHom_algebraMap, CommRing.Pic.mapAlgebra_apply,
      CommRing.Pic.mk_eq_one_iff] at hi
    exact hi.some
  choose m hm using fun i => exists_one_tmul i M (hA i) ((e i).symm 1)
  let m₀ : M := ∑ i, (Pi.single i 1 : (j : ι) → R j) • m i
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton ((j : ι) → R j) M m₀) := by
    intro x
    refine ⟨fun i => e i ((1 : R i) ⊗ₜ x), ?_⟩
    have key : ∀ i, (Pi.single i 1 : (j : ι) → R j) • x =
        (Pi.single i (e i ((1 : R i) ⊗ₜ x)) : (j : ι) → R j) • m i := by
      intro i
      set r := e i ((1 : R i) ⊗ₜ x) with hr
      have h1 : (1 : R i) ⊗ₜ[(j : ι) → R j] x =
          (1 : R i) ⊗ₜ ((Pi.single i r : (j : ι) → R j) • m i) := by
        apply (e i).injective
        rw [← TensorProduct.smul_tmul]
        have h0 : (Pi.single i r : (j : ι) → R j) • (1 : R i) = r := by
          rw [Algebra.smul_def, hA i]; simp
        rw [h0]
        have h5 : (r ⊗ₜ[(j : ι) → R j] m i : R i ⊗[(j : ι) → R j] M) = r • ((1 : R i) ⊗ₜ m i) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [h5, map_smul, hm i, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
      have h2 : (1 : R i) ⊗ₜ[(j : ι) → R j] (x - (Pi.single i r : (j : ι) → R j) • m i) = 0 := by
        rw [TensorProduct.tmul_sub, h1, sub_self]
      have h3 := single_smul_eq_zero i M (hA i) _ h2
      rw [smul_sub, sub_eq_zero, smul_smul] at h3
      rw [h3, ← Pi.single_mul, one_mul]
    rw [LinearMap.toSpanSingleton_apply, Finset.smul_sum]
    have hs : ∀ i, (fun i => e i ((1 : R i) ⊗ₜ x) : (j : ι) → R j) •
        (Pi.single i 1 : (j : ι) → R j) • m i = (Pi.single i 1 : (j : ι) → R j) • x := by
      intro i
      rw [key i, smul_smul]
      congr 1
      ext j
      by_cases hj : j = i
      · subst hj; simp
      · simp [hj]
    rw [Finset.sum_congr rfl (fun i _ => hs i), ← Finset.sum_smul]
    have h1 : ∑ i, (Pi.single i 1 : (j : ι) → R j) = 1 := by
      simpa using Finset.univ_sum_single (1 : (j : ι) → R j)
    rw [h1, one_smul]
  have hbij := Module.Invertible.bijective_of_surjective hsurj
  exact CommRing.Pic.mk_eq_self.symm.trans
    (CommRing.Pic.mk_eq_one_iff.mpr ⟨(LinearEquiv.ofBijective _ hbij).symm⟩)

end PicPi

theorem pic_pi_isOfFinOrder : ∀ (ι : Type) [Finite ι] (R : ι → Type) [∀ i, CommRing (R i)],
    (∀ i (M : CommRing.Pic (R i)), IsOfFinOrder M) →
      ∀ M : CommRing.Pic ((i : ι) → R i), IsOfFinOrder M := by
  intro ι _ R _ hR M
  classical
  haveI := Fintype.ofFinite ι
  have hk : 0 < ∏ i, orderOf (CommRing.Pic.mapRingHom (Pi.evalRingHom R i) M) :=
    Finset.prod_pos fun i _ => (hR i _).orderOf_pos
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨_, hk, ?_⟩
  apply PicPi.eq_one_of_forall
  intro i
  rw [map_pow]
  exact orderOf_dvd_iff_pow_eq_one.mp (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))

end GlobalTheory
end

