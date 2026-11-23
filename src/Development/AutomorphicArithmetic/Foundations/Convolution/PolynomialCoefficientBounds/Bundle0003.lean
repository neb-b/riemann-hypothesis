module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.AffineCharacterGenerators.Generators
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.ChebBd
section
open MvPolynomial Filter Topology PositivityTheory.Rg.Fx
open scoped ContDiff

theorem UpperTheory.ConvolutionTheory.FX.cheb_bound :
    ∀ (η : ℝ) (m : ℕ), 0 < η → η ≤ 1 → (∀ a ∈ Set.Icc 0 η, |cheb η m a| ≤ 1) ∧ (∀ a ∈ Set.Icc (0 : ℝ) 1, |cheb η m a| ≤ (4 / η) ^ m) ∧ ∃ q : Polynomial ℝ, q.natDegree ≤ m ∧ ∀ a, q.eval a = cheb η m a := by
  intro η m hη hη1
  have hA : ∀ a ∈ Set.Icc 0 η, |cheb η m a| ≤ 1 := by
    intro a ha
    unfold cheb
    refine (UpperTheory.ConvolutionTheory.FX.cheb_facts m _).1 ?_
    have h0 : 0 ≤ 2 * a / η := div_nonneg (by linarith [ha.1]) hη.le
    have h2 : 2 * a / η ≤ 2 := by
      rw [div_le_iff₀ hη]; linarith [ha.2]
    rw [abs_le]; constructor <;> linarith
  refine ⟨hA, ?_, ?_⟩
  · intro a ha
    by_cases h : a ≤ η
    · refine (hA a ⟨ha.1, h⟩).trans (one_le_pow₀ ?_)
      rw [le_div_iff₀ hη]; linarith
    · have h : η < a := lt_of_not_ge h
      have h2 : 2 ≤ 2 * a / η := by
        rw [le_div_iff₀ hη]; linarith
      have h3 : 2 * (2 * a / η) ≤ 4 / η := by
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right (by linarith [ha.2]) hη.le
      unfold cheb
      refine ((UpperTheory.ConvolutionTheory.FX.cheb_facts m _).2 (by linarith)).2.trans ?_
      exact pow_le_pow_left₀ (by linarith) (by linarith) m
  · refine ⟨(Polynomial.Chebyshev.T ℝ (m : ℤ)).comp
      (Polynomial.C (2 / η) * Polynomial.X + Polynomial.C (-1)), ?_, ?_⟩
    · refine Polynomial.natDegree_comp_le.trans ?_
      rw [Polynomial.Chebyshev.natDegree_T, Int.natAbs_natCast]
      calc m * _ ≤ m * 1 := Nat.mul_le_mul_left m Polynomial.natDegree_linear_le
        _ = m := Nat.mul_one m
    · intro a
      unfold cheb
      rw [Polynomial.eval_comp]
      congr 1
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.CoeffL1NormNonneg
section
open MvPolynomial Filter Topology

private noncomputable def coeffL1Norm {ι : Type} (p : MvPolynomial ι ℂ) : ℝ :=
  ∑ α ∈ p.support, ‖p.coeff α‖

private theorem coeffL1Norm_nonneg {ι : Type} (p : MvPolynomial ι ℂ) : 0 ≤ coeffL1Norm p :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

private theorem coeffL1Norm_mul {ι : Type} (p q : MvPolynomial ι ℂ) :
    coeffL1Norm (p * q) ≤ coeffL1Norm p * coeffL1Norm q := (UpperTheory.ConvolutionTheory.FX.coeffL1_submultiplicative_facts ι p q).2.1

private theorem coeffL1Norm_C_mul {ι : Type} (c : ℂ) (p : MvPolynomial ι ℂ) :
    coeffL1Norm (C c * p) = ‖c‖ * coeffL1Norm p := (UpperTheory.ConvolutionTheory.FX.coeffL1_submultiplicative_facts ι p p).2.2.1 c

private theorem coeffL1Norm_sum {ι κ : Type} (s : Finset κ) (f : κ → MvPolynomial ι ℂ) :
    coeffL1Norm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, coeffL1Norm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coeffL1Norm]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h : coeffL1Norm (f a + ∑ i ∈ s, f i) ≤ coeffL1Norm (f a) + coeffL1Norm (∑ i ∈ s, f i) :=
      (UpperTheory.ConvolutionTheory.FX.coeffL1_submultiplicative_facts ι _ _).1
    linarith

private theorem gen_inv {τ : Type} {n : ℕ} (w : τ → Equiv.Perm (Fin n))
    (g : MvPolynomial (τ × Fin n) ℂ) :
    rename (fun ti : τ × Fin n => (ti.1, w ti.1 ti.2))
      (aeval (fun ti : τ × Fin n => rename (fun j => (ti.1, j)) (esymm (Fin n) ℂ (ti.2 + 1))) g)
    = aeval (fun ti : τ × Fin n => rename (fun j => (ti.1, j)) (esymm (Fin n) ℂ (ti.2 + 1))) g := by
  rw [← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext ti
  conv_rhs => rw [← rename_esymm (Fin n) ℂ (ti.2 + 1) (w ti.1)]
  rw [rename_rename, rename_rename]
  rfl

theorem UpperTheory.ConvolutionTheory.FX.generators0 :
    ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (n : ℕ), ∃ K : ℝ, ∀ (k : ℕ) (P : MvPolynomial (τ × Fin n) ℂ), P.totalDegree ≤ k → (∀ w : τ → Equiv.Perm (Fin n), rename (fun ti : τ × Fin n => (ti.1, w ti.1 ti.2)) P = P) → ∃ G : MvPolynomial (τ × Fin n) ℂ, aeval (fun ti : τ × Fin n => rename (fun j => (ti.1, j)) (esymm (Fin n) ℂ (ti.2 + 1))) G = P ∧ G.totalDegree ≤ k ∧ (∑ α ∈ (G).support, ‖(G).coeff α‖) ≤ K ^ (k + 1) * (∑ α ∈ (P).support, ‖(P).coeff α‖) := by
  intro τ _ _ n
  obtain ⟨K, hK, hred⟩ := UpperTheory.ConvolutionTheory.FX.gen_reduce τ n
  choose G hG hGb using hred
  choose F hF using fun β : τ × Fin n → Fin n => UpperTheory.ConvolutionTheory.FX.gen_fund τ n (fun u => (β u : ℕ))
  set M : ℝ := ∑ β, coeffL1Norm (F β) with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => coeffL1Norm_nonneg _
  have hFM : ∀ β, coeffL1Norm (F β) ≤ M := fun β =>
    Finset.single_le_sum (f := fun β => coeffL1Norm (F β)) (fun _ _ => coeffL1Norm_nonneg _) (Finset.mem_univ β)
  clear_value M
  refine ⟨K + M, fun k P hP hinv => ?_⟩
  set N : ℕ := Fintype.card (τ → Equiv.Perm (Fin n)) with hN
  have hN1 : 1 ≤ N := Fintype.card_pos
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hmon : ∀ α, aeval (fun ti : τ × Fin n => rename (fun j => (ti.1, j)) (esymm (Fin n) ℂ (ti.2 + 1)))
      (∑ β, G α β * F β) = ∑ w : τ → Equiv.Perm (Fin n),
        rename (fun ti : τ × Fin n => (ti.1, w ti.1 ti.2)) (monomial α (1 : ℂ)) := by
    intro α
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hG α, map_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_mul, hF, map_sum, gen_inv, Finset.mul_sum]
    exact Finset.sum_comm
  have hP' : P = ∑ α ∈ P.support, C (P.coeff α) * monomial α (1 : ℂ) := by
    conv_lhs => rw [P.as_sum]
    simp only [C_mul_monomial, mul_one]
  have hE : aeval (fun ti : τ × Fin n => rename (fun j => (ti.1, j)) (esymm (Fin n) ℂ (ti.2 + 1)))
      (C (N : ℂ)⁻¹ * ∑ α ∈ P.support, C (P.coeff α) * ∑ β, G α β * F β) = P := by
    have h1 : ∑ w : τ → Equiv.Perm (Fin n),
        rename (fun ti : τ × Fin n => (ti.1, w ti.1 ti.2)) P = C (N : ℂ) * P := by
      simp only [hinv, Finset.sum_const, Finset.card_univ, ← hN, nsmul_eq_mul, map_natCast]
    have h2 : ∑ α ∈ P.support, C (P.coeff α) * ∑ w : τ → Equiv.Perm (Fin n),
        rename (fun ti : τ × Fin n => (ti.1, w ti.1 ti.2)) (monomial α (1 : ℂ)) = C (N : ℂ) * P := by
      rw [← h1]
      conv_rhs => rw [hP']
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_mul, rename_C, Finset.mul_sum]
      exact Finset.sum_comm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, map_sum]
    simp only [map_mul (aeval _) (C _), hmon, aeval_C, algebraMap_eq]
    rw [h2, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hNC, C_1, one_mul]
  obtain ⟨G', h1, h2, h3⟩ := UpperTheory.ConvolutionTheory.FX.gen_trunc τ n k _ (by rw [hE]; exact hP)
  refine ⟨G', h1.trans hE, h2, h3.trans ?_⟩
  change coeffL1Norm _ ≤ _
  have hb : ∀ α ∈ P.support, coeffL1Norm (∑ β, G α β * F β) ≤ (K + M) ^ (k + 1) := by
    intro α hα
    have hd : α.degree ≤ k := (le_totalDegree hα).trans hP
    calc _ ≤ ∑ β, coeffL1Norm (G α β * F β) := coeffL1Norm_sum _ _
      _ ≤ ∑ β, coeffL1Norm (G α β) * M := Finset.sum_le_sum fun β _ =>
          (coeffL1Norm_mul _ _).trans (mul_le_mul_of_nonneg_left (hFM β) (coeffL1Norm_nonneg _))
      _ = (∑ β, coeffL1Norm (G α β)) * M := by rw [Finset.sum_mul]
      _ ≤ K ^ α.degree * M := mul_le_mul_of_nonneg_right (hGb α) hM0
      _ ≤ K ^ k * M := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hK hd) hM0
      _ ≤ (K + M) ^ k * (K + M) :=
          mul_le_mul (pow_le_pow_left₀ (by linarith) (by linarith) k) (by linarith) hM0
            (pow_nonneg (by linarith) k)
      _ = _ := (pow_succ _ _).symm
  have hn : ‖(N : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_natCast]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast hN1)
  rw [coeffL1Norm_C_mul]
  refine (mul_le_of_le_one_left (coeffL1Norm_nonneg _) hn).trans ((coeffL1Norm_sum _ _).trans ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun α hα => ?_
  rw [coeffL1Norm_C_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right (hb α hα) (norm_nonneg _)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.ExistsFinMap
section
open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

private theorem exists_fin_map {α : Type} (s : Multiset α) (n : ℕ) (h : Multiset.card s = n) :
    ∃ x : Fin n → α, Finset.univ.val.map x = s := by
  induction s using Quotient.inductionOn with
  | h l =>
    have h' : l.length = n := by simpa using h
    subst h'
    exact ⟨l.get, by rw [Fin.univ_val_map, List.ofFn_get]; rfl⟩

private theorem esymm_surj (n : ℕ) (y : Fin n → ℂ) :
    ∃ x : Fin n → ℂ, ∀ i : Fin n, aeval x (esymm (Fin n) ℂ (i + 1)) = y i := by
  set q : Polynomial ℂ :=
    ∑ j : Fin n, Polynomial.C ((-1) ^ (n - j) * y j.rev) * Polynomial.X ^ (j : ℕ) with hq
  have hqd : q.degree < n := Polynomial.degree_sum_fin_lt _
  set p : Polynomial ℂ := Polynomial.X ^ n + q with hp
  have hm : p.Monic := Polynomial.monic_X_pow_add hqd
  have hd : p.natDegree = n := by
    apply Polynomial.natDegree_eq_of_degree_eq_some
    rw [hp, Polynomial.degree_add_eq_left_of_degree_lt, Polynomial.degree_X_pow]
    rwa [Polynomial.degree_X_pow]
  have hc : Multiset.card p.roots = p.natDegree := IsAlgClosed.card_roots_eq_natDegree
  obtain ⟨x, hx⟩ := exists_fin_map p.roots n (hc.trans hd)
  refine ⟨x, fun i => ?_⟩
  rw [aeval_esymm_eq_multiset_esymm, hx]
  have hi := i.2
  have h1 := Polynomial.coeff_eq_esymm_roots_of_card hc (k := (i.rev : ℕ)) (by rw [hd]; exact i.rev.2.le)
  have e : n - (i.rev : ℕ) = i + 1 := by rw [Fin.val_rev]; omega
  have h2 : p.coeff (i.rev : ℕ) = (-1) ^ ((i : ℕ) + 1) * y i := by
    rw [hp, Polynomial.coeff_add, Polynomial.coeff_X_pow, if_neg i.rev.2.ne, zero_add, hq,
      Polynomial.finsetSum_coeff, Finset.sum_eq_single i.rev]
    · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl, e, Fin.rev_rev]
    · intro b _ hb
      rw [Polynomial.coeff_C_mul_X_pow, if_neg (fun h => hb (Fin.ext h.symm))]
    · simp
  rw [hd, e, hm.leadingCoeff, one_mul, h2] at h1
  exact (mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) h1).symm

theorem UpperTheory.ConvolutionTheory.FX.blockE_inj :
    ∀ (τ : Type) [Fintype τ] [DecidableEq τ] (n : ℕ), Function.Injective (aeval (blockE (τ := τ) (n := n)) : MvPolynomial (τ × Fin n) ℂ →ₐ[ℂ] MvPolynomial (τ × Fin n) ℂ) := by
  intro τ _ _ n G H hGH
  apply MvPolynomial.funext
  intro y
  choose x hx using fun t : τ => esymm_surj n (fun i => y (t, i))
  have key : ∀ P : MvPolynomial (τ × Fin n) ℂ,
      aeval (fun ti : τ × Fin n => x ti.1 ti.2) (aeval (blockE (τ := τ) (n := n)) P) = eval y P := by
    intro P
    have hf : (fun ti : τ × Fin n => aeval (fun ti : τ × Fin n => x ti.1 ti.2) (blockE ti)) = y := by
      funext ⟨t, i⟩
      rw [blockE, aeval_rename]
      exact hx t i
    rw [← AlgHom.comp_apply, comp_aeval, hf]
    rfl
  rw [← key, ← key, hGH]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.LiftSingleAlt
section
open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

private theorem lift_single {ι A : Type} [CommRing A] [Algebra ℂ A] (x : ι → A) (τ : Multiplicative (ι → ℝ) →* A) (v : ι → ℝ)
    (p : MvPolynomial ι ℂ) : lift x τ (AddMonoidAlgebra.single v p) = aeval x p * τ (Multiplicative.ofAdd v) := by
  simp [lift, AddMonoidAlgebra.liftNCRingHom]

private theorem hom_ext {ι A : Type} [CommRing A] (f g : EP ι →+* A)
    (h1 : ∀ c : ℂ, f (AddMonoidAlgebra.single 0 (C c)) = g (AddMonoidAlgebra.single 0 (C c)))
    (h2 : ∀ i, f (AddMonoidAlgebra.single 0 (X i)) = g (AddMonoidAlgebra.single 0 (X i)))
    (h3 : ∀ v, f (AddMonoidAlgebra.single v 1) = g (AddMonoidAlgebra.single v 1)) : f = g := by
  refine AddMonoidAlgebra.ringHom_ext (fun p => ?_) h3
  have : f.comp (AddMonoidAlgebra.singleZeroRingHom) = g.comp AddMonoidAlgebra.singleZeroRingHom :=
    MvPolynomial.ringHom_ext (fun c => h1 c) (fun i => h2 i)
  exact RingHom.congr_fun this p

theorem UpperTheory.ConvolutionTheory.FX.subst :
    PositivityTheory.Rg.Fx.Subst := by
  intro ι ι' _ _ Λ₀ M f
  refine ⟨fun lam => ?_, fun ι'' _ Λ₁ N => ?_⟩
  · refine RingHom.congr_fun (hom_ext ((ev lam).comp (aff Λ₀ M)) _ ?_ ?_ ?_) f
    · intro c
      simp [aff, ev, lift_single, AddMonoidAlgebra.coe_algebraMap]
    · intro i
      simp [aff, ev, lift_single, lin]
    · intro v
      simp only [aff, ev, lift_single, RingHom.comp_apply, map_one, one_mul, affChar, expChar, MonoidHom.coe_mk, OneHom.coe_mk,
        toAdd_ofAdd, aeval_C, Algebra.algebraMap_self, RingHom.id_apply, ← Complex.exp_add]
      congr 1
      simp only [Matrix.vecMul, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul, mul_add, Finset.mul_sum,
        Finset.sum_add_distrib, mul_assoc]
      rw [Finset.sum_comm]
  · refine RingHom.congr_fun (hom_ext ((aff Λ₁ N).comp (aff Λ₀ M)) _ ?_ ?_ ?_) f
    · intro c
      simp [aff, lift_single, AddMonoidAlgebra.coe_algebraMap]
    · intro i
      have e : ∀ p : MvPolynomial ι' ℂ, aeval (fun j => (AddMonoidAlgebra.single 0 (C (Λ₁ j) + lin (N j)) : EP ι'')) p =
          AddMonoidAlgebra.single 0 (aeval (fun j => (C (Λ₁ j) + lin (N j) : MvPolynomial ι'' ℂ)) p) := fun p => by
        induction p using MvPolynomial.induction_on with
        | C a => simp [AddMonoidAlgebra.coe_algebraMap]
        | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, AddMonoidAlgebra.single_add]
        | mul_X p j hp => rw [map_mul, map_mul, hp, aeval_X, aeval_X, AddMonoidAlgebra.single_mul_single, add_zero]
      simp only [aff, lift_single, RingHom.comp_apply, aeval_X, ofAdd_zero, map_one, mul_one, e]
      congr 1
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [lin, map_add (f := _), map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq, Matrix.mul_apply, Complex.ofReal_sum,
        Complex.ofReal_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_assoc, add_assoc]
      rw [Finset.sum_comm (s := (Finset.univ : Finset ι''))]
    · intro v
      simp only [aff, lift_single, RingHom.comp_apply, map_one, one_mul, affChar, expChar, MonoidHom.coe_mk, OneHom.coe_mk,
        toAdd_ofAdd, aeval_C, AddMonoidAlgebra.coe_algebraMap, Function.comp_apply, AddMonoidAlgebra.single_mul_single, zero_add,
        algebraMap_eq, ← C_mul, ← Complex.exp_add, Matrix.vecMul_vecMul]
      congr 3
      simp only [Matrix.vecMul, dotProduct, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul, mul_add, Finset.mul_sum,
        Finset.sum_add_distrib, mul_assoc]
      rw [Finset.sum_comm]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.PieceAdd
section
open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

theorem UpperTheory.ConvolutionTheory.FX.piece_add :
    ∀ (ι : Type) [Fintype ι] (k : ℕ), (∀ f g : EP ι, piece k (f + g) = piece k f + piece k g) ∧ piece k (0 : EP ι) = 0 ∧ ∀ (v : ι → ℝ) (p : MvPolynomial ι ℂ), piece k (AddMonoidAlgebra.single v p : EP ι) = ∑ b ∈ Finset.range (k + 1), homogeneousComponent (k - b) p * (C ((b.factorial : ℂ)⁻¹) * lin v ^ b) := by
  intro ι _ k
  refine ⟨fun f g => ?_, ?_, fun v p => ?_⟩
  · unfold piece
    rw [AddMonoidAlgebra.coeff_add, Finsupp.sum_add_index']
    · intro a; simp
    · intro a b c; simp [add_mul, Finset.sum_add_distrib]
  · unfold piece
    simp
  · unfold piece
    rw [AddMonoidAlgebra.coeff_single, Finsupp.sum_single_index]
    simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.PieceHom
section
open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

theorem UpperTheory.ConvolutionTheory.FX.piece_hom :
    ∀ (ι : Type) [Fintype ι] (f : EP ι) (k : ℕ), (piece k f).IsHomogeneous k := by
  intro ι _ f k
  have hlin : ∀ v : ι → ℝ, (lin v).IsHomogeneous 1 := fun v =>
    IsHomogeneous.sum _ _ _ fun i _ => by
      simpa using (isHomogeneous_C ι ((v i : ℝ) : ℂ)).mul (isHomogeneous_X ℂ i)
  unfold piece Finsupp.sum
  refine IsHomogeneous.sum _ _ _ fun v _ => IsHomogeneous.sum _ _ _ fun b hb => ?_
  have hbk : b ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
  have h := (homogeneousComponent_isHomogeneous (k - b) (f.coeff v)).mul
    ((isHomogeneous_C ι ((b.factorial : ℂ)⁻¹)).mul ((hlin v).pow b))
  have e : k - b + (0 + 1 * b) = k := by omega
  rwa [e] at h
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.PowLeExpEventually
section
open MvPolynomial Filter Topology PositivityTheory.Rg.Fx

private lemma pow_le_exp_eventually (d : ℕ → ℕ) (hd : Tendsto (fun j : ℕ => (d j : ℝ) / j) atTop (𝓝 0))
    (L : ℝ) (hL : 0 < L) : ∀ᶠ j : ℕ in atTop, L ^ (d j + 1) ≤ Real.exp j := by
  have h1 : Tendsto (fun j : ℕ => Real.log L * ((d j : ℝ) / j + 1 / j)) atTop
      (𝓝 (Real.log L * (0 + 0))) :=
    (hd.add tendsto_one_div_atTop_nhds_zero_nat).const_mul _
  have h2 := h1.eventually (gt_mem_nhds (show Real.log L * (0 + 0) < 1 by simp))
  filter_upwards [h2, eventually_gt_atTop 0] with j hj hj0
  have hjp : (0 : ℝ) < j := by exact_mod_cast hj0
  have h3 : Real.log L * ((d j : ℝ) + 1) ≤ j := by
    have : Real.log L * ((d j : ℝ) / j + 1 / j) = Real.log L * ((d j : ℝ) + 1) / j := by ring
    rw [this, div_lt_one hjp] at hj
    exact hj.le
  calc L ^ (d j + 1) = Real.exp (Real.log L * ((d j : ℝ) + 1)) := by
        rw [← Real.rpow_def_of_pos hL]
        rw [← Real.rpow_natCast]; push_cast; rfl
    _ ≤ _ := Real.exp_le_exp.2 h3

private lemma err_bound2 (p : ℕ) (hp : 0 < p) (c₁ cq a₀ : ℝ) (h0 : 0 < a₀) (h1 : a₀ ≤ 1)
    (A η : ℝ) (hA : A = |c₁ + cq + 1| + 1) (hηp : 0 < η) (hη : η ≤ a₀ * Real.exp (-(p * A))) (j : ℕ) (F : ℝ)
    (hF : Real.exp ((c₁ + cq + 2 + Real.log (4 / a₀)) * j) ≤ F) :
    Real.exp ((cq + 1) * j) * (η / a₀) ^ (j / p) *
      (Real.exp (c₁ * j) * (1 + (4 / η) ^ (j / p) / F) +
        (4 / η) ^ (j / p) * Real.exp (-(cq + 2 + Real.log (4 / a₀)) * j)) ≤
      (Real.exp (p * A) + 2) * Real.exp (-j) := by
  have hFp : 0 < F := (Real.exp_pos _).trans_le hF
  set m := j / p with hm
  set g := Real.log (4 / a₀) with hg
  have hq : (η / a₀) ^ m * (4 / η) ^ m = (4 / a₀) ^ m := by
    rw [← mul_pow]; congr 1; field_simp
  have h4 : (4 / a₀) ^ m ≤ Real.exp (g * j) := by
    have : (1 : ℝ) ≤ 4 / a₀ := by rw [le_div_iff₀ h0]; linarith
    calc (4 / a₀) ^ m ≤ (4 / a₀) ^ j := pow_le_pow_right₀ this (Nat.div_le_self _ _)
      _ = Real.exp (g * j) := by
        rw [mul_comm, Real.exp_nat_mul, hg, Real.exp_log (by positivity)]
  have h5 : (η / a₀) ^ m ≤ Real.exp (-(m * p * A)) := by
    have : η / a₀ ≤ Real.exp (-(p * A)) := by rw [div_le_iff₀ h0, mul_comm]; exact hη
    calc _ ≤ Real.exp (-(p * A)) ^ m := by gcongr
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
  have hmp : (j : ℝ) ≤ m * p + p := by
    have := Nat.lt_div_mul_add (a := j) hp
    rw [← hm] at this
    exact_mod_cast this.le
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hA1 : c₁ + cq + 2 ≤ A := by have := le_abs_self (c₁ + cq + 1); linarith
  have t1 : Real.exp ((cq + 1) * j) * (η / a₀) ^ m * Real.exp (c₁ * j) ≤
      Real.exp (p * A) * Real.exp (-j) := by
    refine le_trans (b := Real.exp ((cq + 1) * j) * Real.exp (-(m * p * A)) * Real.exp (c₁ * j))
      (by gcongr) ?_
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    nlinarith [mul_le_mul_of_nonneg_right hmp hA0, mul_le_mul_of_nonneg_right hA1 hj]
  have t2 : Real.exp ((cq + 1) * j) * Real.exp (c₁ * j) * (4 / a₀) ^ m / F ≤ Real.exp (-j) := by
    rw [div_le_iff₀ hFp]
    calc _ ≤ Real.exp ((cq + 1) * j) * Real.exp (c₁ * j) * Real.exp (g * j) := by gcongr
      _ = Real.exp (-j) * Real.exp ((c₁ + cq + 2 + g) * j) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ _ := by gcongr
  have t3 : Real.exp ((cq + 1) * j) * (4 / a₀) ^ m * Real.exp (-(cq + 2 + g) * j) ≤
      Real.exp (-j) := by
    calc _ ≤ Real.exp ((cq + 1) * j) * Real.exp (g * j) * Real.exp (-(cq + 2 + g) * j) := by gcongr
      _ = Real.exp (-j) := by
        rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [← hq] at t2 t3
  calc _ = Real.exp ((cq + 1) * j) * (η / a₀) ^ m * Real.exp (c₁ * j) +
        Real.exp ((cq + 1) * j) * Real.exp (c₁ * j) * ((η / a₀) ^ m * (4 / η) ^ m) / F +
        Real.exp ((cq + 1) * j) * ((η / a₀) ^ m * (4 / η) ^ m) * Real.exp (-(cq + 2 + g) * j) := by
        ring
    _ ≤ _ := by linarith

private lemma solve_bound2 (x a z η a₀ cq K₁ K E : ℝ) (d m j : ℕ) (hx : 0 ≤ x) (hη : 0 < η)
    (hηa : η < a₀) (h1 : a₀ ≤ 1) (ha : a₀ ≤ a) (hz : Real.exp (-cq) ≤ z) (hE : 0 ≤ E)
    (hL : ((|K₁| + 1) * |K| / a₀ + 1) ^ (d + 1) ≤ Real.exp j)
    (h : x * a ^ d * (2 * a / η - 1) ^ m * z ^ j ≤ K₁ * (K ^ (d + 1) * E)) :
    x ≤ Real.exp ((cq + 1) * j) * (η / a₀) ^ m * E := by
  have h0 : 0 < a₀ := hη.trans hηa
  have hb : a₀ / η ≤ 2 * a / η - 1 := by
    rw [div_sub_one hη.ne', div_le_div_iff_of_pos_right hη]; linarith
  have hb0 : 0 < a₀ / η := by positivity
  have hl : x * a₀ ^ (d + 1) * (a₀ / η) ^ m * Real.exp (-cq) ^ j ≤
      x * a ^ d * (2 * a / η - 1) ^ m * z ^ j := by
    have : a₀ ^ (d + 1) ≤ a ^ d :=
      (pow_le_pow_of_le_one h0.le h1 (Nat.le_succ d)).trans (pow_le_pow_left₀ h0.le ha d)
    have h2 : 0 ≤ a := by linarith
    have h3 : 0 ≤ 2 * a / η - 1 := by linarith
    gcongr
  have hr : K₁ * (K ^ (d + 1) * E) ≤ a₀ ^ (d + 1) * Real.exp j * E := by
    have e1 : |K₁| ≤ (|K₁| + 1) ^ (d + 1) :=
      (by linarith : |K₁| ≤ |K₁| + 1).trans
        (le_self_pow₀ (by linarith [abs_nonneg K₁]) (Nat.succ_ne_zero d))
    calc K₁ * (K ^ (d + 1) * E) ≤ |K₁ * (K ^ (d + 1) * E)| := le_abs_self _
      _ = |K₁| * |K| ^ (d + 1) * E := by
        rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg hE, mul_assoc]
      _ ≤ (|K₁| + 1) ^ (d + 1) * |K| ^ (d + 1) * E := by gcongr
      _ = a₀ ^ (d + 1) * ((|K₁| + 1) * |K| / a₀) ^ (d + 1) * E := by
        rw [← mul_pow, ← mul_pow]; congr 2; field_simp
      _ ≤ a₀ ^ (d + 1) * ((|K₁| + 1) * |K| / a₀ + 1) ^ (d + 1) * E := by
        gcongr; linarith
      _ ≤ _ := by gcongr
  have h6 := (hl.trans h).trans hr
  have hpos : 0 < a₀ ^ (d + 1) * (a₀ / η) ^ m * Real.exp (-cq) ^ j := by positivity
  have e2 : (η / a₀) ^ m * (a₀ / η) ^ m = 1 := by
    rw [← mul_pow]
    have : η / a₀ * (a₀ / η) = 1 := by field_simp
    rw [this, one_pow]
  have e3 : Real.exp ((cq + 1) * j) * Real.exp (-cq) ^ j = Real.exp j := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  refine le_of_mul_le_mul_right ?_ hpos
  calc _ = x * a₀ ^ (d + 1) * (a₀ / η) ^ m * Real.exp (-cq) ^ j := by ring
    _ ≤ a₀ ^ (d + 1) * Real.exp j * E := h6
    _ = a₀ ^ (d + 1) * (Real.exp ((cq + 1) * j) * Real.exp (-cq) ^ j) *
        ((η / a₀) ^ m * (a₀ / η) ^ m) * E := by rw [e2, e3, mul_one]
    _ = _ := by ring

theorem UpperTheory.ConvolutionTheory.FX.exponents2 :
    ∀ (d : ℕ → ℕ), Tendsto (fun j : ℕ => (d j : ℝ) / j) atTop (𝓝 0) →
    (∀ B : ℝ, ∀ᶠ j : ℕ in atTop, Real.exp (B * j) ≤ (d j).factorial) →
    ∀ (p : ℕ), 0 < p → ∀ (c₁ cq a₀ : ℝ), 0 < a₀ → a₀ ≤ 1 → ∃ η₀ : ℝ, 0 < η₀ ∧ η₀ < a₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → ∃ N : ℝ,
    ∀ (I : Type) [Fintype I] (a : I → ℝ) (ζ : I → ℂ), (∀ i, η < a i) → (∀ i, ζ i ≠ 0) →
    Function.Injective (fun i => (a i, ζ i)) → ∀ (c : ℕ → I → ℂ) (c' : I → ℂ),
    (∀ i, Tendsto (fun j => c j i) atTop (𝓝 (c' i))) →
    (∀ s₀ : ℕ, ∃ K : ℝ, ∀ᶠ j : ℕ in atTop, ∀ s ≤ s₀, ∀ s' ≤ s₀,
    ‖∑ i, c j i * (a i : ℂ) ^ d j * (cheb η (j / p + s) (a i) : ℂ) * ζ i ^ (j + s')‖ ≤
    K ^ (d j + 1) * (Real.exp (c₁ * j) * (1 + (4 / η) ^ (j / p) / (d j).factorial) + (4 / η) ^ (j / p) * Real.exp (-N * j))) →
    ∀ i, a₀ ≤ a i → Real.exp (-cq) ≤ ‖ζ i‖ → c' i = 0 := by
  intro d hd hfac p hp c₁ cq a₀ h0 h1
  obtain ⟨A, hA⟩ : ∃ A, A = |c₁ + cq + 1| + 1 := ⟨_, rfl⟩
  have hη₀a : a₀ * Real.exp (-(p * A)) < a₀ := by
    have hA0 : 0 < A := by rw [hA]; positivity
    have hp' : (0 : ℝ) < p := by exact_mod_cast hp
    have : Real.exp (-(p * A)) < 1 := Real.exp_lt_one_iff.2 (by nlinarith [mul_pos hp' hA0])
    nlinarith
  refine ⟨a₀ * Real.exp (-(p * A)), by positivity, hη₀a, ?_⟩
  intro η hηp hη
  have hηa : η < a₀ := hη.trans_lt hη₀a
  refine ⟨cq + 2 + Real.log (4 / a₀), ?_⟩
  intro I _ a ζ ha hζ0 hinj c c' hc hbd i hi hζ
  obtain ⟨s₀, K₁, hsep⟩ := UpperTheory.ConvolutionTheory.FX.separate0 η hηp I a ζ ha hζ0 hinj
  obtain ⟨K, hK⟩ := hbd s₀
  have hev : ∀ᶠ j : ℕ in atTop, ‖c j i‖ ≤ (Real.exp (p * A) + 2) * Real.exp (-j) := by
    filter_upwards [hK, hfac (c₁ + cq + 2 + Real.log (4 / a₀)),
      pow_le_exp_eventually d hd ((|K₁| + 1) * |K| / a₀ + 1) (by positivity)] with j hj hF hL
    have h := hsep (j / p) j (fun i => c j i * (a i : ℂ) ^ d j) _ hj i
    have hai : 0 ≤ a i := by linarith
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hai] at h
    exact (solve_bound2 _ _ _ η a₀ cq K₁ K _ _ _ _ (norm_nonneg _) hηp hηa h1 hi hζ
      (by positivity) hL h).trans (err_bound2 p hp c₁ cq a₀ h0 h1 A η hA hηp hη j _ hF)
  have hlim : Tendsto (fun j : ℕ => (Real.exp (p * A) + 2) * Real.exp (-j)) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul
      (Real.exp (p * A) + 2)
    simpa using this
  exact tendsto_nhds_unique (hc i) (squeeze_zero_norm' hev hlim)
end

