module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0046
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0067
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0085
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0070
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0093

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnimodularHermitianRepsCountSucc
section
open PositivityTheory.PfSWUS.Loc

namespace GlobalTheory.CompanionTheory.UnrDens.HenselStep

section Generic

theorem card_of_fibres {α β : Type*} [Finite α] [Finite β] (f : α → β) (c : ℕ)
    (h : ∀ b, Nat.card {a // f a = b} = c) : Nat.card α = Nat.card β * c := by
  classical
  haveI := Fintype.ofFinite β
  rw [Nat.card_congr (Equiv.sigmaFiberEquiv f).symm, Nat.card_sigma]
  simp [h, Nat.card_eq_fintype_card, mul_comm]

theorem card_eq_of_surj {W A B : Type*} (a : W → A) (b : W → B) (ha : Function.Surjective a)
    (hb : Function.Surjective b) (hab : ∀ w w', a w = a w' ↔ b w = b w') :
    Nat.card A = Nat.card B := by
  refine Nat.card_congr (Equiv.ofBijective (fun y => b (Function.surjInv ha y)) ⟨?_, ?_⟩)
  · intro y y' h
    have := (hab _ _).2 h
    simpa [Function.surjInv_eq] using this
  · intro z
    obtain ⟨w, rfl⟩ := hb z
    exact ⟨a w, (hab _ _).1 (Function.surjInv_eq ha _)⟩

end Generic

variable {R : Type} [CommRing R] {a b c : ℕ}

theorem cT_add (σ : R →+* R) (x y : Matrix (Fin a) (Fin b) R) :
    cT σ (x + y) = cT σ x + cT σ y := by
  ext i j; simp [cT]

theorem cT_smul (σ : R →+* R) (r : R) (x : Matrix (Fin a) (Fin b) R) :
    cT σ (r • x) = σ r • cT σ x := by
  ext i j; simp [cT]

theorem cT_mul (σ : R →+* R) (x : Matrix (Fin a) (Fin b) R) (y : Matrix (Fin b) (Fin c) R) :
    cT σ (x * y) = cT σ y * cT σ x := by
  simp [cT, Matrix.map_mul, Matrix.transpose_mul]

theorem cT_cT (σ : R →+* R) (h : ∀ r, σ (σ r) = r) (x : Matrix (Fin a) (Fin b) R) :
    cT σ (cT σ x) = x := by
  ext i j; simp [cT, h]

theorem red_add (ϖ : R) (k : ℕ) (x y : Matrix (Fin a) (Fin b) R) :
    red ϖ k (x + y) = red ϖ k x + red ϖ k y := by
  ext i j; simp [red]

theorem red_mul (ϖ : R) (k : ℕ) (x : Matrix (Fin a) (Fin b) R) (y : Matrix (Fin b) (Fin c) R) :
    red ϖ k (x * y) = red ϖ k x * red ϖ k y := by
  simp [red, Matrix.map_mul]

theorem red_cT (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) (k : ℕ) (x : Matrix (Fin a) (Fin b) R) :
    red ϖ k (cT σ x) = cT (barσ σ ϖ h k) (red ϖ k x) := by
  ext i j; simp [red, cT]

theorem red_surjective (ϖ : R) (k : ℕ) :
    Function.Surjective (red ϖ k : Matrix (Fin a) (Fin b) R → _) := fun t =>
  ⟨fun i j => Function.surjInv Ideal.Quotient.mk_surjective (t i j), by
    ext i j; exact Function.surjInv_eq _ _⟩

theorem red_eq_iff (ϖ : R) (k : ℕ) (M N : Matrix (Fin a) (Fin b) R) :
    red ϖ k M = red ϖ k N ↔ ∃ D : Matrix (Fin a) (Fin b) R, M = N + ϖ ^ k • D := by
  constructor
  · intro h
    have h1 : ∀ i j, ∃ d, M i j = N i j + ϖ ^ k * d := by
      intro i j
      have h2 : Ideal.Quotient.mk (lev ϖ k) (M i j) = Ideal.Quotient.mk (lev ϖ k) (N i j) :=
        congrFun (congrFun h i) j
      obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 h2)
      exact ⟨d, by linear_combination -hd⟩
    choose D hD using h1
    exact ⟨Matrix.of D, by ext i j; simp [hD i j]⟩
  · rintro ⟨D, rfl⟩
    ext i j
    refine Ideal.Quotient.eq.2 (Ideal.mem_span_singleton'.2 ⟨D i j, ?_⟩)
    simp [mul_comm]

theorem smul_cancel {ϖ : R} (hr : IsSMulRegular R ϖ) (k : ℕ) {A B : Matrix (Fin a) (Fin b) R}
    (h : ϖ ^ k • A = ϖ ^ k • B) : A = B := by
  ext i j
  have h1 : ϖ ^ k • A i j = ϖ ^ k • B i j := by
    simpa using congrFun (congrFun h i) j
  exact (hr.pow k) h1

theorem red_smul_iff {ϖ : R} (hr : IsSMulRegular R ϖ) (k : ℕ) (A B : Matrix (Fin a) (Fin b) R) :
    red ϖ (k + 1) (ϖ ^ k • A) = red ϖ (k + 1) (ϖ ^ k • B) ↔ red ϖ 1 A = red ϖ 1 B := by
  rw [red_eq_iff, red_eq_iff]
  constructor
  · rintro ⟨D, hD⟩
    refine ⟨D, smul_cancel hr k ?_⟩
    rw [hD, smul_add, smul_smul, pow_one, pow_succ]
  · rintro ⟨D, rfl⟩
    refine ⟨D, ?_⟩
    rw [smul_add, smul_smul, pow_one, pow_succ]

theorem gram_expand (σ : R →+* R) {r : R} (hc : σ r = r) (S : Matrix (Fin a) (Fin a) R)
    (x y : Matrix (Fin a) (Fin b) R) :
    cT σ (x + r • y) * S * (x + r • y) =
      cT σ x * S * x + r • (cT σ y * S * x + cT σ x * S * y) + (r * r) • (cT σ y * S * y) := by
  rw [cT_add, cT_smul, hc]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]
  abel

theorem lift_iff {σ : R →+* R} {ϖ : R} (hf : σ ϖ = ϖ) (hr : IsSMulRegular R ϖ) {k : ℕ} (hk : 1 ≤ k)
    (S : Matrix (Fin a) (Fin a) R) (T H : Matrix (Fin b) (Fin b) R)
    (x y : Matrix (Fin a) (Fin b) R) (hH : cT σ x * S * x + ϖ ^ k • H = T) :
    red ϖ (k + 1) (cT σ (x + ϖ ^ k • y) * S * (x + ϖ ^ k • y)) = red ϖ (k + 1) T ↔
      red ϖ 1 (cT σ y * S * x + cT σ x * S * y) = red ϖ 1 H := by
  have hc : σ (ϖ ^ k) = ϖ ^ k := by rw [map_pow, hf]
  have hq : red ϖ (k + 1) ((ϖ ^ k * ϖ ^ k) • (cT σ y * S * y)) = 0 := by
    have : red ϖ (k + 1) ((ϖ ^ k * ϖ ^ k) • (cT σ y * S * y)) = red ϖ (k + 1) 0 := by
      refine (red_eq_iff _ _ _ _).2 ⟨ϖ ^ (k - 1) • (cT σ y * S * y), ?_⟩
      rw [smul_smul, zero_add, ← pow_add, ← pow_add]
      congr 2
      omega
    rw [this]
    ext i j; simp [red]
  rw [gram_expand σ hc, red_add, hq, add_zero, ← hH, red_add, red_add]
  rw [add_right_inj, red_smul_iff hr]

section Main

variable {σ : R →+* R} {ϖ : R}

abbrev solSet (σ : R →+* R) (ϖ : R) (S : Matrix (Fin a) (Fin a) R) (T : Matrix (Fin b) (Fin b) R)
    (k : ℕ) : Set (Matrix (Fin a) (Fin b) R) :=
  {x | red ϖ k (cT σ x * S * x) = red ϖ k T}

theorem lev_succ_le_lev (ϖ : R) (k : ℕ) : lev ϖ (k + 1) ≤ lev ϖ k :=
  Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow ϖ (Nat.le_succ k))

def proj (ϖ : R) (k : ℕ) (t : Matrix (Fin a) (Fin b) (R ⧸ lev ϖ (k + 1))) :
    Matrix (Fin a) (Fin b) (R ⧸ lev ϖ k) :=
  t.map (Ideal.Quotient.factor (lev_succ_le_lev ϖ k))

theorem proj_red (ϖ : R) (k : ℕ) (x : Matrix (Fin a) (Fin b) R) :
    proj ϖ k (red ϖ (k + 1) x) = red ϖ k x := by
  ext i j; simp [proj, red]

theorem solSet_succ {S : Matrix (Fin a) (Fin a) R} {T : Matrix (Fin b) (Fin b) R} {k : ℕ}
    {x : Matrix (Fin a) (Fin b) R} (hx : x ∈ solSet σ ϖ S T (k + 1)) : x ∈ solSet σ ϖ S T k := by
  have h1 := congrArg (proj ϖ k) hx
  simp only [proj_red] at h1
  exact h1

def down (σ : R →+* R) (ϖ : R) (S : Matrix (Fin a) (Fin a) R) (T : Matrix (Fin b) (Fin b) R) (k : ℕ)
    (t : red ϖ (k + 1) '' solSet σ ϖ S T (k + 1)) : red ϖ k '' solSet σ ϖ S T k :=
  ⟨proj ϖ k t.1, by
    obtain ⟨x, hx, e⟩ := t.2
    exact ⟨x, solSet_succ hx, by rw [← e, proj_red]⟩⟩

theorem red_diff (hf : σ ϖ = ϖ) (S : Matrix (Fin a) (Fin a) R) (x y : Matrix (Fin a) (Fin b) R) :
    red ϖ 1 (cT σ y * S * x + cT σ x * S * y) =
      cT (barσ σ ϖ hf 1) (red ϖ 1 y) * red ϖ 1 S * red ϖ 1 x +
        cT (barσ σ ϖ hf 1) (red ϖ 1 x) * red ϖ 1 S * red ϖ 1 y := by
  simp only [red_add, red_mul, red_cT σ ϖ hf]

theorem fibre_card {q : ℕ} {ε : ℤ} (h : IsUnrQuad R σ ϖ q ε) {m n : ℕ} (hnm : n ≤ m)
    {S : Matrix (Fin m) (Fin m) R} {T : Matrix (Fin n) (Fin n) R} (hS : IsUnimod σ S)
    (hT : IsUnimod σ T) {k : ℕ} (hk : 1 ≤ k) {x : Matrix (Fin m) (Fin n) R}
    (hx : x ∈ solSet σ ϖ S T k) (s : red ϖ k '' solSet σ ϖ S T k) (hs : s.1 = red ϖ k x) :
    Nat.card {t // down σ ϖ S T k t = s} = q ^ (2 * m * n - n ^ 2) := by
  obtain ⟨D, hD⟩ := (red_eq_iff _ _ _ _).1 hx
  have hH : cT σ x * S * x + ϖ ^ k • (-D) = T := by
    rw [hD, smul_neg]; abel
  have hG : cT σ (cT σ x * S * x) = cT σ x * S * x := by
    rw [cT_mul, cT_mul, cT_cT σ h.inv, hS.1, Matrix.mul_assoc]
  have hherm : cT σ (-D) = -D := by
    apply smul_cancel h.reg k
    have h1 := congrArg (cT σ) hH
    rw [cT_add, cT_smul, map_pow, h.fix_ϖ, hG, hT.1] at h1
    exact add_left_cancel (h1.trans hH.symm)
  have hf := h.fix_ϖ
  have hgram : cT (barσ σ ϖ hf 1) (red ϖ 1 x) * red ϖ 1 S * red ϖ 1 x = red ϖ 1 T := by
    rw [← red_cT σ ϖ hf, ← red_mul, ← red_mul]
    refine (red_eq_iff _ _ _ _).2 ⟨ϖ ^ (k - 1) • D, ?_⟩
    rw [hD, smul_smul, ← pow_add]
    congr 3
    omega
  have hdet : IsUnit (red ϖ 1 T).det := by
    have h1 := hT.2.map (Ideal.Quotient.mk (lev ϖ 1))
    rw [RingHom.map_det] at h1
    exact h1
  have hcard := GlobalTheory.CompanionTheory.UnrDens.GramDiff.card_fibre_gram_differential _ (barσ σ ϖ hf 1) q ε (GlobalTheory.CompanionTheory.UnrDens.resAlg_of_isUnrQuad R σ ϖ q ε h) m n hnm
    (red ϖ 1 S) (red ϖ 1 T) (red ϖ 1 x) (red ϖ 1 (-D))
    (by rw [← red_cT σ ϖ hf, hS.1]) (by rw [← red_cT σ ϖ hf, hT.1]) hdet hgram
    (by rw [← red_cT σ ϖ hf, hherm])
  rw [← hcard]
  symm
  let W := {y : Matrix (Fin m) (Fin n) R //
    red ϖ 1 (cT σ y * S * x + cT σ x * S * y) = red ϖ 1 (-D)}
  refine card_eq_of_surj (W := W)
    (fun w => ⟨red ϖ 1 w.1, by rw [← red_diff hf]; exact w.2⟩)
    (fun w => ⟨⟨red ϖ (k + 1) (x + ϖ ^ k • w.1), x + ϖ ^ k • w.1,
        (lift_iff hf h.reg hk S T (-D) x w.1 hH).2 w.2, rfl⟩, Subtype.ext (by
          show proj ϖ k (red ϖ (k + 1) (x + ϖ ^ k • w.1)) = s.1
          rw [proj_red, hs]
          exact (red_eq_iff _ _ _ _).2 ⟨w.1, rfl⟩)⟩) ?_ ?_ ?_
  · rintro ⟨ybar, hy⟩
    obtain ⟨y, rfl⟩ := red_surjective ϖ 1 ybar
    exact ⟨⟨y, by rw [red_diff hf]; exact hy⟩, rfl⟩
  · rintro ⟨⟨t, x', hx', rfl⟩, ht⟩
    have h1 : red ϖ k x' = red ϖ k x := by
      have h2 : proj ϖ k (red ϖ (k + 1) x') = s.1 := congrArg Subtype.val ht
      rwa [proj_red, hs] at h2
    obtain ⟨y, rfl⟩ := (red_eq_iff _ _ _ _).1 h1
    exact ⟨⟨y, (lift_iff hf h.reg hk S T (-D) x y hH).1 hx'⟩, rfl⟩
  · intro w w'
    rw [Subtype.ext_iff, Subtype.ext_iff, Subtype.ext_iff]
    show red ϖ 1 w.1 = red ϖ 1 w'.1 ↔
      red ϖ (k + 1) (x + ϖ ^ k • w.1) = red ϖ (k + 1) (x + ϖ ^ k • w'.1)
    rw [red_add, red_add, add_right_inj, red_smul_iff h.reg]

end Main

end GlobalTheory.CompanionTheory.UnrDens.HenselStep


open GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.HenselStep in
theorem GlobalTheory.CompanionTheory.UnrDens.solCount_succ : ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ),
    IsUnrQuad R σ ϖ q ε → ∀ (m n : ℕ), n ≤ m → ∀ (S : Matrix (Fin m) (Fin m) R)
    (T : Matrix (Fin n) (Fin n) R), IsUnimod σ S → IsUnimod σ T → ∀ k : ℕ, 1 ≤ k →
    solCount σ ϖ S T (k + 1) = solCount σ ϖ S T k * q ^ (2 * m * n - n ^ 2) := by
  intro R _ σ ϖ q ε h m n hnm S T hS hT k hk
  have hfin : ∀ j, Finite (R ⧸ lev ϖ j) := fun j =>
    Nat.finite_of_card_ne_zero (by
      rw [GlobalTheory.CompanionTheory.UnrDens.card_quot_lev R σ ϖ q ε h j]
      exact pow_ne_zero _ (by have := h.one_lt; omega))
  haveI := hfin k
  haveI := hfin (k + 1)
  haveI : Finite (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) := by unfold Matrix; infer_instance
  haveI : Finite (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ (k + 1))) := by unfold Matrix; infer_instance
  unfold solCount
  refine card_of_fibres (down σ ϖ S T k) _ ?_
  rintro ⟨s, x, hx, rfl⟩
  exact fibre_card h hnm hS hT hk hx _ rfl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitTZpow
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

noncomputable section

namespace GlobalTheory.CompanionTheory.PerfBC

theorem bc_laur : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : Type) [CommRing K] [Algebra A K] (i : A[T;T⁻¹] →ₐ[A] B) (f g : A), Pf p A → Pf p K → PQ p (i : A[T;T⁻¹] →+* B) (Ideal.span {LaurentPolynomial.C f - LaurentPolynomial.T 1 * LaurentPolynomial.C g}) → ∃ i₁ : K[T;T⁻¹] →+* B ⊗[A] K, PQ p i₁ (Ideal.span {LaurentPolynomial.C (algebraMap A K f) - LaurentPolynomial.T 1 * LaurentPolynomial.C (algebraMap A K g)}) ∧ (∀ a, i₁ (LaurentPolynomial.C a) = (1 : B) ⊗ₜ[A] a) ∧ ∀ n : ℤ, i₁ (LaurentPolynomial.T n) = i (LaurentPolynomial.T n) ⊗ₜ[A] (1 : K) := by
  intro p _ A _ B _ _ K _ _ i f g hA hK hPQ
  let j : A[T;T⁻¹] →+* K[T;T⁻¹] :=
    AddMonoidAlgebra.liftNCRingHom ((LaurentPolynomial.C : K →+* K[T;T⁻¹]).comp (algebraMap A K))
      (AddMonoidAlgebra.of K ℤ) (fun _ _ => Commute.all _ _)
  let i₁ : K[T;T⁻¹] →+* B ⊗[A] K :=
    AddMonoidAlgebra.liftNCRingHom
      (Algebra.TensorProduct.includeRight : K →ₐ[A] B ⊗[A] K).toRingHom
      (((Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] K).comp
        (i : A[T;T⁻¹] →+* B)).toMonoidHom.comp (AddMonoidAlgebra.of A ℤ))
      (fun _ _ => Commute.all _ _)
  have hi1 : ∀ (n : ℤ) (k : K), i₁ (AddMonoidAlgebra.single n k) =
      ((1 : B) ⊗ₜ[A] k) * (i (LaurentPolynomial.T n) ⊗ₜ[A] (1 : K)) := by
    intro n k
    exact AddMonoidAlgebra.liftNC_single _ _ n k
  have hj1 : ∀ (n : ℤ) (a : A), j (AddMonoidAlgebra.single n a) =
      LaurentPolynomial.C (algebraMap A K a) * LaurentPolynomial.T n := by
    intro n a
    exact AddMonoidAlgebra.liftNC_single _ _ n a
  have hC : ∀ a, i₁ (LaurentPolynomial.C a) = (1 : B) ⊗ₜ[A] a := by
    intro a
    have h1 := hi1 0 a
    rw [LaurentPolynomial.T_zero, map_one, ← Algebra.TensorProduct.one_def, mul_one] at h1
    exact h1
  have hT : ∀ n : ℤ, i₁ (LaurentPolynomial.T n) = i (LaurentPolynomial.T n) ⊗ₜ[A] (1 : K) := by
    intro n
    have h1 := hi1 n 1
    rw [← Algebra.TensorProduct.one_def, one_mul] at h1
    exact h1
  have hjC : ∀ a, j (LaurentPolynomial.C a) = LaurentPolynomial.C (algebraMap A K a) := by
    intro a
    have h1 := hj1 0 a
    rw [LaurentPolynomial.T_zero, mul_one] at h1
    exact h1
  have hjT : ∀ n : ℤ, j (LaurentPolynomial.T n) = LaurentPolynomial.T n := by
    intro n
    have h1 := hj1 n 1
    rw [map_one, map_one, one_mul] at h1
    exact h1
  have hiC : ∀ a, i (LaurentPolynomial.C a) = algebraMap A B a := by
    intro a
    rw [← AlgHom.commutes i a, LaurentPolynomial.algebraMap_apply, Algebra.algebraMap_self_apply]
  have hcomp : (LaurentPolynomial.C : K →+* K[T;T⁻¹]).comp (algebraMap A K) =
      j.comp (algebraMap A A[T;T⁻¹]) := by
    ext a
    rw [RingHom.comp_apply, RingHom.comp_apply, LaurentPolynomial.algebraMap_apply,
      Algebra.algebraMap_self_apply, hjC]
  have hgen : Subring.closure (Set.range (LaurentPolynomial.C : K →+* K[T;T⁻¹]) ∪ Set.range j) = ⊤ := by
    rw [eq_top_iff]
    intro q _
    refine LaurentPolynomial.induction_on' q ?_ ?_
    · intro a b ha hb
      exact Subring.add_mem _ ha hb
    · intro n a
      exact Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨a, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨LaurentPolynomial.T n, hjT n⟩))
  have hij : ∀ s, i₁ (j s) = i s ⊗ₜ[A] (1 : K) := by
    intro s
    refine LaurentPolynomial.induction_on' s ?_ ?_
    · intro a b ha hb
      rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), TensorProduct.add_tmul]
    · intro n a
      rw [map_mul, map_mul, hjC, hjT, map_mul, hC, hT, hiC, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, mul_one, ← Algebra.smul_def, TensorProduct.smul_tmul,
        ← Algebra.algebraMap_eq_smul_one]
  have hmap : (Ideal.span {LaurentPolynomial.C f - LaurentPolynomial.T 1 * LaurentPolynomial.C g} :
      Ideal A[T;T⁻¹]).map j = Ideal.span {(LaurentPolynomial.C (algebraMap A K f) -
        LaurentPolynomial.T 1 * LaurentPolynomial.C (algebraMap A K g))} := by
    rw [Ideal.map_span, Set.image_singleton, map_sub, map_mul, hjC, hjC, hjT]
  refine ⟨i₁, ?_, hC, hT⟩
  rw [← hmap]
  exact _root_.GlobalTheory.CompanionTheory.PerfectRing.pq_baseChange p A A[T;T⁻¹] B K K[T;T⁻¹] i _ LaurentPolynomial.C j i₁ hA hK hPQ hcomp hgen
    hC hij

end GlobalTheory.CompanionTheory.PerfBC
end
end

