module

public import Mathlib
public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0093
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0087

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PatternGroupStatement
section
open ReciprocityTheory.Ty.Fin

noncomputable section

namespace GlobalTheory.CompanionTheory.PatGrp

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι : Type} [Fintype ι] [DecidableEq ι] {Φ : ι → ι → Prop}

def Supp (Φ : ι → ι → Prop) (N : Matrix ι ι K) : Prop := ∀ i j, N i j ≠ 0 → Φ i j

theorem mem_patSet_iff (h : IsPat Φ) (u : GL ι K) :
    u ∈ patSet (K := K) Φ ↔ Supp Φ ((u : Matrix ι ι K) - 1) := by
  unfold patSet
  rw [Set.mem_setOf_eq]
  constructor
  · intro hu i j hN
    by_contra hΦ
    apply hN
    rcases eq_or_ne i j with rfl | hij
    · rw [Matrix.sub_apply, Matrix.one_apply_eq, (hu i i).1 rfl, sub_self]
    · rw [Matrix.sub_apply, Matrix.one_apply_ne hij, (hu i j).2 hij hΦ, sub_zero]
  · intro hS i j
    refine ⟨fun hij => ?_, fun hij hΦ => ?_⟩
    · subst hij
      have h0 : ((u : Matrix ι ι K) - 1) i i = 0 := by
        by_contra hne
        exact h.1 i (hS i i hne)
      rwa [Matrix.sub_apply, Matrix.one_apply_eq, sub_eq_zero] at h0
    · have h0 : ((u : Matrix ι ι K) - 1) i j = 0 := by
        by_contra hne
        exact hΦ (hS i j hne)
      rwa [Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero] at h0

theorem Supp.mul (h : IsPat Φ) {A B : Matrix ι ι K} (hA : Supp Φ A) (hB : Supp Φ B) :
    Supp Φ (A * B) := by
  intro i j hij
  rw [Matrix.mul_apply] at hij
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hij
  exact h.2 i k j (hA i k (left_ne_zero_of_mul hk)) (hB k j (right_ne_zero_of_mul hk))

theorem Supp.add {A B : Matrix ι ι K} (hA : Supp Φ A) (hB : Supp Φ B) : Supp Φ (A + B) := by
  intro i j hij
  by_cases ha : A i j = 0
  · apply hB
    intro hb
    apply hij
    rw [Matrix.add_apply, ha, hb, add_zero]
  · exact hA i j ha

theorem det_one_add (h : IsPat Φ) {N : Matrix ι ι K} (hN : Supp Φ N) : (1 + N).det = 1 := by
  classical
  let b : ι → ℕ := fun i => (Finset.univ.filter fun k => Φ k i).card
  have hb : ∀ i j, Φ i j → b i < b j := by
    intro i j hij
    apply Finset.card_lt_card
    refine (Finset.ssubset_iff_of_subset ?_).2 ⟨i, ?_, ?_⟩
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact h.2 k i j hk hij
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hij
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h.1 i
  have hN0 : ∀ i j, b j ≤ b i → N i j = 0 := by
    intro i j hle
    by_contra hne
    exact absurd (hb i j (hN i j hne)) (not_lt.2 hle)
  have hT : (1 + N).BlockTriangular b := by
    intro i j hlt
    have hij : i ≠ j := by
      rintro rfl
      exact lt_irrefl _ hlt
    rw [Matrix.add_apply, Matrix.one_apply_ne hij, hN0 i j hlt.le, add_zero]
  rw [hT.det]
  refine Finset.prod_eq_one fun a _ => ?_
  have hblk : (1 + N).toSquareBlock b a = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    show (1 + N) i j = (1 : Matrix {a' // b a' = a} {a' // b a' = a} K) ⟨i, hi⟩ ⟨j, hj⟩
    have hNij : N i j = 0 := hN0 i j (by rw [hi, hj])
    rcases eq_or_ne i j with rfl | hij
    · rw [Matrix.add_apply, hNij, add_zero, Matrix.one_apply_eq, Matrix.one_apply_eq]
    · rw [Matrix.add_apply, Matrix.one_apply_ne hij, hNij, add_zero,
        Matrix.one_apply_ne (fun e => hij (congrArg Subtype.val e))]
  rw [hblk, Matrix.det_one]

def patSubgroup (h : IsPat Φ) : Subgroup (GL ι K) :=
  let M : Submonoid (GL ι K) :=
    { carrier := patSet (K := K) Φ
      mul_mem' := by
        intro u v hu hv
        have hu' := (mem_patSet_iff h u).1 hu
        have hv' := (mem_patSet_iff h v).1 hv
        refine (mem_patSet_iff h _).2 ?_
        have e : ((u * v : GL ι K) : Matrix ι ι K) - 1 =
            ((u : Matrix ι ι K) - 1) + ((v : Matrix ι ι K) - 1) +
              ((u : Matrix ι ι K) - 1) * ((v : Matrix ι ι K) - 1) := by
          rw [Units.val_mul]
          noncomm_ring
        rw [e]
        exact (hu'.add hv').add (hu'.mul h hv')
      one_mem' := by
        refine (mem_patSet_iff h _).2 ?_
        intro i j hij
        simp at hij }
  { M with
    inv_mem' := by
      intro u hu
      have hn : orderOf u ≠ 0 := (orderOf_pos u).ne'
      have : u⁻¹ = u ^ (orderOf u - 1) :=
        inv_eq_of_mul_eq_one_right (by rw [mul_pow_sub_one hn, pow_orderOf_eq_one])
      rw [this]
      exact M.pow_mem hu _ }


open Classical in
noncomputable def fill (Φ : ι → ι → Prop) (f : {p : ι × ι // Φ p.1 p.2} → K) : Matrix ι ι K := by
  classical
  exact fun i j => if h : Φ i j then f ⟨(i, j), h⟩ else 0

theorem supp_fill (f : {p : ι × ι // Φ p.1 p.2} → K) : Supp Φ (fill Φ f) := by
  intro i j hij
  by_contra hΦ
  apply hij
  simp [fill, hΦ]

theorem card_patSet (h : IsPat Φ) :
    (patSet (K := K) Φ).ncard = Fintype.card K ^ Nat.card {p : ι × ι // Φ p.1 p.2} := by
  classical
  have hunit : ∀ f : {p : ι × ι // Φ p.1 p.2} → K, IsUnit (1 + fill Φ f).det := fun f => by
    rw [det_one_add h (supp_fill f)]
    exact isUnit_one
  let e : patSet (K := K) Φ ≃ ({p : ι × ι // Φ p.1 p.2} → K) :=
    { toFun := fun u p => (u.1 : Matrix ι ι K) p.1.1 p.1.2
      invFun := fun f => ⟨Matrix.nonsingInvUnit (1 + fill Φ f) (hunit f), by
        refine (mem_patSet_iff h _).2 ?_
        show Supp Φ ((1 + fill Φ f) - 1)
        rw [add_sub_cancel_left]
        exact supp_fill f⟩
      left_inv := fun u => by
        apply Subtype.ext
        apply Units.ext
        show 1 + fill Φ (fun p => (u.1 : Matrix ι ι K) p.1.1 p.1.2) = (u.1 : Matrix ι ι K)
        ext i j
        have hu := (show ∀ i j, (i = j → (u.1 : Matrix ι ι K) i j = 1) ∧
          (i ≠ j → ¬Φ i j → (u.1 : Matrix ι ι K) i j = 0) from u.2) i j
        rw [Matrix.add_apply]
        simp only [fill]
        rcases eq_or_ne i j with rfl | hij
        · rw [Matrix.one_apply_eq, dite_eq_right (h.1 i), add_zero, hu.1 rfl]
        · rw [Matrix.one_apply_ne hij, zero_add]
          by_cases hΦ : Φ i j
          · rw [dite_eq_left hΦ]
          · rw [dite_eq_right hΦ, hu.2 hij hΦ]
      right_inv := fun f => by
        funext p
        show (1 + fill Φ f) p.1.1 p.1.2 = f p
        have hne : p.1.1 ≠ p.1.2 := fun e => h.1 p.1.2 (by have hp := p.2; rw [e] at hp; exact hp)
        rw [Matrix.add_apply, Matrix.one_apply_ne hne, zero_add]
        simp only [fill]
        rw [dite_eq_left p.2] }
  rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card (α := K)]

end GlobalTheory.CompanionTheory.PatGrp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PqBaseChangePolynomial
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Perfection

theorem pq_baseChange_polynomial : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : Type) [CommRing K] [Algebra A K] (i : Polynomial A →ₐ[A] B) (h : Polynomial A), Pf p A → Pf p K → PQ p (i : Polynomial A →+* B) (Ideal.span {h}) → ∃ i₁ : Polynomial K →+* B ⊗[A] K, PQ p i₁ (Ideal.span {h.map (algebraMap A K)}) ∧ (∀ a, i₁ (Polynomial.C a) = (1 : B) ⊗ₜ[A] a) ∧ i₁ Polynomial.X = i Polynomial.X ⊗ₜ[A] (1 : K) := by
  intro p _ A _ B _ _ K _ _ i h hA hK hPQ
  let i₁ : Polynomial K →+* B ⊗[A] K :=
    Polynomial.eval₂RingHom (Algebra.TensorProduct.includeRight : K →ₐ[A] B ⊗[A] K).toRingHom
      (i Polynomial.X ⊗ₜ[A] (1 : K))
  have hC : ∀ a, i₁ (Polynomial.C a) = (1 : B) ⊗ₜ[A] a := by
    intro a
    simp [i₁]
  have hX : i₁ Polynomial.X = i Polynomial.X ⊗ₜ[A] (1 : K) := by
    simp [i₁]
  have hj : ∀ s : Polynomial A, i₁ (Polynomial.mapRingHom (algebraMap A K) s) = i s ⊗ₜ[A] (1 : K) := by
    intro s
    induction s using Polynomial.induction_on with
    | C a =>
      have h1 : i (Polynomial.C a) = algebraMap A B a := by
        rw [← Polynomial.algebraMap_eq]
        exact i.commutes a
      rw [Polynomial.coe_mapRingHom, Polynomial.map_C, hC, h1, Algebra.algebraMap_eq_smul_one,
        Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add f g hf hg =>
      rw [map_add (f := _), map_add (f := _), hf, hg, map_add (f := _), TensorProduct.add_tmul]
    | monomial n a ih =>
      have e : (Polynomial.C a * Polynomial.X ^ (n + 1) : Polynomial A)
          = (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X := by ring
      rw [e, map_mul, map_mul, ih, map_mul]
      have e2 : Polynomial.mapRingHom (algebraMap A K) (Polynomial.X : Polynomial A) = Polynomial.X := by
        simp
      rw [e2, hX, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      simp only [map_mul]
  have hcl : Subring.closure (Set.range (Polynomial.C : K →+* Polynomial K) ∪
      Set.range (Polynomial.mapRingHom (algebraMap A K))) = ⊤ := by
    rw [eq_top_iff]
    intro f _
    induction f using Polynomial.induction_on with
    | C a => exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
    | add f g hf hg => exact Subring.add_mem _ (hf trivial) (hg trivial)
    | monomial n a ih =>
      have e : (Polynomial.C a * Polynomial.X ^ (n + 1) : Polynomial K)
          = (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X := by ring
      rw [e]
      refine Subring.mul_mem _ (ih trivial) (Subring.subset_closure (Or.inr ⟨Polynomial.X, ?_⟩))
      simp
  have hcomp : (Polynomial.C : K →+* Polynomial K).comp (algebraMap A K)
      = (Polynomial.mapRingHom (algebraMap A K)).comp (algebraMap A (Polynomial A)) := by
    ext a
    simp [Polynomial.algebraMap_apply]
  have key := _root_.GlobalTheory.CompanionTheory.PerfectRing.pq_baseChange p A (Polynomial A) B K (Polynomial K) i (Ideal.span {h})
    Polynomial.C (Polynomial.mapRingHom (algebraMap A K)) i₁ hA hK hPQ hcomp hcl hC hj
  refine ⟨i₁, ?_, hC, hX⟩
  rw [Ideal.map_span, Set.image_singleton] at key
  simpa using key

end GlobalTheory.CompanionTheory.Perfection
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDetOppositeNeg
section
open Formalism.REAL

noncomputable section

namespace GlobalTheory.CompanionTheory.CapelliAntipode

theorem unop_ofFn_prod {A : Type*} [Ring A] : ∀ {t : ℕ} (f : Fin t → Aᵐᵒᵖ),
    MulOpposite.unop (List.ofFn f).prod = (List.ofFn fun i => MulOpposite.unop (f i.rev)).prod
  | 0, f => by simp
  | t + 1, f => by
    rw [List.ofFn_succ, List.prod_cons, MulOpposite.unop_mul, unop_ofFn_prod (fun i => f i.succ),
      List.ofFn_succ' (fun i : Fin (t + 1) => MulOpposite.unop (f i.rev)), List.prod_concat]
    simp only [Fin.rev_last, Fin.rev_castSucc]

theorem ofFn_prod_neg {A : Type*} [Ring A] [Algebra ℂ A] : ∀ {t : ℕ} (g : Fin t → A),
    (List.ofFn fun k => -g k).prod = ((-1 : ℂ) ^ t) • (List.ofFn g).prod
  | 0, g => by simp
  | t + 1, g => by
    rw [List.ofFn_succ, List.prod_cons, ofFn_prod_neg (fun k => g k.succ), List.ofFn_succ (f := g),
      List.prod_cons, pow_succ, mul_comm, mul_smul, neg_mul, mul_smul_comm, neg_one_smul]

theorem Tm_op_neg {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (X : Fin n → Fin n → A) (w : ℂ)
    (i j : Fin n) :
    Tm (fun i j => MulOpposite.op (-X i j)) w i j = MulOpposite.op (-(Tm X (-w) i j)) := by
  unfold Tm
  by_cases h : i = j
  · simp [h, MulOpposite.algebraMap_apply, add_comm]
  · simp [h]

theorem arg_rev {t : ℕ} (v : ℂ) (j : Fin t) :
    -(v - (((Fin.rev j : Fin t) : ℕ) : ℂ)) = ((t : ℂ) - 1 - v) - ((j : ℕ) : ℂ) := by
  have hj := j.isLt
  rw [Fin.val_rev, Nat.cast_sub (by omega : (j : ℕ) + 1 ≤ t)]
  push_cast
  ring

theorem unop_term {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (X : Fin n → Fin n → A) (v : ℂ)
    (σ : Equiv.Perm (Fin n)) :
    MulOpposite.unop ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : Aᵐᵒᵖ) *
        (List.ofFn fun k : Fin n =>
          Tm (fun i j => MulOpposite.op (-X i j)) (v - ((k : ℕ) : ℂ)) (id (σ k)) (id k)).prod) =
      ((-1 : ℂ) ^ n) • ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A) *
        (List.ofFn fun j : Fin n =>
          Tm X (((n : ℂ) - 1 - v) - ((j : ℕ) : ℂ)) (σ j.rev) j.rev).prod) := by
  rw [MulOpposite.unop_mul, MulOpposite.unop_intCast, unop_ofFn_prod]
  simp only [Tm_op_neg, MulOpposite.unop_op, id, arg_rev]
  rw [ofFn_prod_neg, smul_mul_assoc, ← Int.cast_comm]

theorem qminor_id_rev {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (X : Fin n → Fin n → A) (w : ℂ) :
    qminor X id (id ∘ (Fin.revPerm : Equiv.Perm (Fin n))) w =
      (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤˣ) : ℤ) : A) *
        ∑ σ : Equiv.Perm (Fin n), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A) *
          (List.ofFn fun j : Fin n => Tm X (w - ((j : ℕ) : ℂ)) (σ j.rev) j.rev).prod := by
  unfold qminor
  rw [Finset.mul_sum]
  refine (Fintype.sum_equiv (Equiv.mulRight (Fin.revPerm : Equiv.Perm (Fin n))) _ _ (fun σ => ?_)).symm
  simp only [Equiv.coe_mulRight, Equiv.Perm.sign_mul, Equiv.Perm.mul_apply, Fin.revPerm_apply,
    Function.comp_apply, id, Units.val_mul, Int.cast_mul]
  rw [← mul_assoc, Int.cast_comm]

theorem unop_qdet_op_neg (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A)
    (hX : GlRel X) (v : ℂ) :
    MulOpposite.unop (qdet (fun i j => MulOpposite.op (-X i j)) v) =
      ((-1 : ℂ) ^ n) • qdet X ((n : ℂ) - 1 - v) := by
  have hs := quantumMinorColSkew_holds A n n X hX id id (Fin.revPerm : Equiv.Perm (Fin n)) ((n : ℂ) - 1 - v)
  rw [qminor_id_rev] at hs
  have hu : (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤˣ) : ℤ) : A) *
      (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤˣ) : ℤ) : A) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have h2 := congrArg (fun x => (((Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin n)) : ℤˣ) : ℤ) : A) * x) hs
  simp only [← mul_assoc, hu, one_mul] at h2
  have h3 : qdet X ((n : ℂ) - 1 - v) = _ := h2.symm
  rw [h3]
  unfold qdet qminor
  rw [Finset.unop_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun σ _ => unop_term X v σ

end GlobalTheory.CompanionTheory.CapelliAntipode
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexAnnihilatorsDuality
section
open Matrix
open scoped Topology

noncomputable section
namespace GlobalTheory.CompanionTheory.IndexDuality

theorem relIndex_le_of_pairing {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
    (b : X → Y → Circle)
    (hl : ∀ x x' y, b (x + x') y = b x y * b x' y)
    (hr : ∀ x y y', b x (y + y') = b x y * b x y')
    (H₀ H : AddSubgroup Y) (R₀ R : AddSubgroup X)
    (hfin : H₀.relIndex H ≠ 0)
    (hann : ∀ x ∈ R₀, ∀ y ∈ H₀, b x y = 1)
    (hsep : ∀ x ∈ R₀, (∀ y ∈ H, b x y = 1) → x ∈ R) :
    R.relIndex R₀ ≠ 0 ∧ R.relIndex R₀ ≤ H₀.relIndex H := by
  classical
  have hQfin : Finite (H ⧸ H₀.addSubgroupOf H) := Nat.finite_of_card_ne_zero hfin
  have hb0 : ∀ x, b x 0 = 1 := by
    intro x
    have h := hr x 0 0
    rw [add_zero] at h
    exact (mul_left_cancel (a := b x 0) (by rw [mul_one]; exact h)).symm
  have hb0' : ∀ y, b 0 y = 1 := by
    intro y
    have h := hl 0 0 y
    rw [add_zero] at h
    exact (mul_left_cancel (a := b 0 y) (by rw [mul_one]; exact h)).symm
  let f : R₀ → H →+ Additive Circle := fun x =>
    { toFun := fun y => Additive.ofMul (b x y)
      map_zero' := by simp [hb0]
      map_add' := fun y y' => by simp [hr] }
  have hker : ∀ x : R₀, ∀ y ∈ H₀.addSubgroupOf H, f x y = 0 := by
    intro x y hy
    rw [AddSubgroup.mem_addSubgroupOf] at hy
    simp [f, hann x x.2 y hy]
  let g : R₀ → (H ⧸ H₀.addSubgroupOf H) →+ Additive Circle := fun x =>
    QuotientAddGroup.lift (H₀.addSubgroupOf H) (f x) (hker x)
  let χ : R₀ → AddChar (H ⧸ H₀.addSubgroupOf H) Circle := fun x =>
    { toFun := fun q => Additive.toMul (g x q)
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun q q' => by simp [map_add (f := _)] }
  have hχ : ∀ (x : R₀) (y : H), χ x (QuotientAddGroup.mk y) = b x y := fun x y => rfl
  let Ψ : R₀ →+ AddChar (H ⧸ H₀.addSubgroupOf H) Circle :=
    { toFun := χ
      map_zero' := by
        ext1 q
        induction q using QuotientAddGroup.induction_on with
        | H y =>
          rw [hχ]
          exact hb0' y
      map_add' := fun x x' => by
        ext1 q
        induction q using QuotientAddGroup.induction_on with
        | H y =>
          rw [hχ]
          change b (x + x') y = (χ x * χ x') (QuotientAddGroup.mk y)
          rw [AddChar.mul_apply, hχ, hχ]
          exact hl x x' y }
  have hkerle : Ψ.ker ≤ R.addSubgroupOf R₀ := by
    intro x hx
    rw [AddMonoidHom.mem_ker] at hx
    rw [AddSubgroup.mem_addSubgroupOf]
    refine hsep x x.2 (fun y hy => ?_)
    have := congrArg (fun φ : AddChar (H ⧸ H₀.addSubgroupOf H) Circle => φ (QuotientAddGroup.mk ⟨y, hy⟩)) hx
    simpa [Ψ, hχ] using this
  have : Fintype (H ⧸ H₀.addSubgroupOf H) := Fintype.ofFinite _
  have hinjC : Function.Injective fun φ : AddChar (H ⧸ H₀.addSubgroupOf H) Circle => Circle.coeHom.compAddChar φ :=
    MonoidHom.compAddChar_injective_right _ Circle.coe_injective
  have : Finite (AddChar (H ⧸ H₀.addSubgroupOf H) Circle) := Finite.of_injective _ hinjC
  have hcardC : Nat.card (AddChar (H ⧸ H₀.addSubgroupOf H) Circle) ≤ H₀.relIndex H := by
    have h1 := Nat.card_le_card_of_injective _ hinjC
    rw [Nat.card_eq_fintype_card (α := AddChar (H ⧸ H₀.addSubgroupOf H) ℂ), AddChar.card_eq,
      ← Nat.card_eq_fintype_card] at h1
    exact h1
  have : Finite (R₀ ⧸ Ψ.ker) := Finite.of_injective _ (QuotientAddGroup.kerLift_injective Ψ)
  have hkerfin : Ψ.ker.index ≤ Nat.card (AddChar (H ⧸ H₀.addSubgroupOf H) Circle) :=
    Nat.card_le_card_of_injective _ (QuotientAddGroup.kerLift_injective Ψ)
  have hker0 : Ψ.ker.index ≠ 0 := AddSubgroup.index_ne_zero_of_finite
  have hdvd := AddSubgroup.index_dvd_of_le hkerle
  have hR0 : (R.addSubgroupOf R₀).index ≠ 0 := fun h0 => hker0 (Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd))
  refine ⟨hR0, ?_⟩
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hker0) hdvd).trans (hkerfin.trans hcardC)

theorem relIndex_annihilator_eq : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (n : ℕ) (A₀ A P₀ P : AddSubgroup (Fin n → k)), IsCompact (A₀ : Set (Fin n → k)) →
    IsOpen (A₀ : Set (Fin n → k)) → IsCompact (A : Set (Fin n → k)) →
    IsOpen (A : Set (Fin n → k)) → A₀ ≤ A → (∀ ξ, ξ ∈ P₀ ↔ ∀ a ∈ A₀, ψ (ξ ⬝ᵥ a) = 1) →
    (∀ ξ, ξ ∈ P ↔ ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1) → P.relIndex P₀ = A₀.relIndex A := by
  intro k _ _ _ _ ψ hψc hψ1 n A₀ A P₀ P hA₀c hA₀o hAc hAo hle hP₀ hP
  have hfin : A₀.relIndex A ≠ 0 :=
    GlobalTheory.CompanionTheory.RelIndex.relIndex_ne_zero_of_isCompact_of_isOpen A A₀ hAc hA₀o hle
  have h1 := relIndex_le_of_pairing (fun ξ a : Fin n → k => ψ (ξ ⬝ᵥ a))
    (fun ξ ξ' a => by simp [add_dotProduct, AddChar.map_add_eq_mul])
    (fun ξ a a' => by simp [dotProduct_add, AddChar.map_add_eq_mul])
    A₀ A P₀ P hfin (fun ξ hξ a ha => (hP₀ ξ).mp hξ a ha) (fun ξ _ h => (hP ξ).mpr h)
  have h2 := relIndex_le_of_pairing (fun a ξ : Fin n → k => ψ (ξ ⬝ᵥ a))
    (fun a a' ξ => by simp [dotProduct_add, AddChar.map_add_eq_mul])
    (fun a ξ ξ' => by simp [add_dotProduct, AddChar.map_add_eq_mul])
    P P₀ A A₀ h1.1 (fun a _ ξ hξ => (hP ξ).mp hξ a ‹_›) (fun a _ h => by
      by_contra hna
      obtain ⟨η, hη, hne⟩ := GlobalTheory.CompanionTheory.CharacterBiduality.exists_annihilator_ne k ψ hψc hψ1 n A₀ hA₀c hA₀o a hna
      exact hne (h η ((hP₀ η).mpr hη)))
  exact le_antisymm h1.2 h2.2

end GlobalTheory.CompanionTheory.IndexDuality
end
end

