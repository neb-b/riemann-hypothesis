module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyLeftMulBasis
section
open Polynomial

namespace GlobalTheory.TraceDetSplit

theorem det_aeval_prod {K : Type} [Field K] {n : ℕ} (N : Matrix (Fin n) (Fin n) K) (s : Multiset K) :
    (aeval N (s.map fun r => X - C r).prod).det
      = (-1) ^ (n * s.card) * (s.map N.charpoly.eval).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
    have h1 : (aeval N (X - C r)).det = (-1) ^ n * N.charpoly.eval r := by
      have e : Matrix.scalar (Fin n) r - N = -(N - algebraMap K (Matrix (Fin n) (Fin n) K) r) := by
        rw [neg_sub, Matrix.algebraMap_eq_diagonal]
        rfl
      rw [Matrix.eval_charpoly, e, Matrix.det_neg, Fintype.card_fin, map_sub, aeval_X, aeval_C,
        ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, map_mul, Matrix.det_mul, ih, h1]
    ring

theorem det_aeval {E : Type} [Field E] {n : ℕ} (N : Matrix (Fin n) (Fin n) E) (p : E[X])
    (hp : p.Monic) :
    (aeval N p).det = (-1) ^ (n * p.natDegree) * resultant p N.charpoly := by
  classical
  let φ := algebraMap E (AlgebraicClosure E)
  apply φ.injective
  have hp' : (p.map φ).Monic := hp.map φ
  have hs : (p.map φ).Splits := IsAlgClosed.splits _
  have hd : (p.map φ).natDegree = p.natDegree := natDegree_map φ
  have key : φ.mapMatrix (aeval N p) = aeval (N.map φ) (p.map φ) := by
    rw [aeval_map_algebraMap]
    exact (Polynomial.aeval_algHom_apply
      (AlgHom.mapMatrix (m := Fin n) (Algebra.ofId E (AlgebraicClosure E))) N p).symm
  rw [RingHom.map_det, key, map_mul, map_pow, map_neg, map_one, ← resultant_map_map,
    ← Matrix.charpoly_map]
  conv_lhs => rw [hs.eq_prod_roots_of_monic hp']
  rw [det_aeval_prod, ← hs.natDegree_eq_card_roots, hd, ← hd,
    resultant_eq_prod_eval _ _ _ (by rw [Matrix.charpoly_natDegree_eq_dim, Matrix.charpoly_natDegree_eq_dim]) hs,
    hp'.leadingCoeff, one_pow, one_mul]

theorem det_trace_monic {E A : Type} [Field E] [CommRing A] [Algebra E A] {n : ℕ} (g : A)
    (e : Fin n → A) (q : Fin n → E[X]) (hd : ∀ k, (q k).natDegree = k) (hm : ∀ k, (q k).Monic) :
    (Matrix.of fun k l : Fin n => Algebra.trace E A (g ^ (k : ℕ) * e l)).det
      = (Matrix.of fun k l : Fin n => Algebra.trace E A (aeval g (q k) * e l)).det := by
  classical
  have hM : (Matrix.of fun k l : Fin n => Algebra.trace E A (aeval g (q k) * e l)) =
      (Matrix.of fun k j : Fin n => (q k).coeff (j : ℕ)) *
        Matrix.of fun k l : Fin n => Algebra.trace E A (g ^ (k : ℕ) * e l) := by
    ext k l
    simp only [Matrix.of_apply, Matrix.mul_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [aeval_eq_sum_range' (n := n) (by rw [hd k]; exact k.isLt), Finset.sum_mul, map_sum,
      ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_assoc, map_smul, smul_eq_mul]
  have hC : (Matrix.of fun k j : Fin n => (q k).coeff (j : ℕ)).det = 1 := by
    rw [Matrix.det_of_isLowerTriangular]
    · refine Finset.prod_eq_one fun k _ => ?_
      simp only [Matrix.of_apply]
      have := (hm k).coeff_natDegree
      rwa [hd k] at this
    · intro i j hij
      simp only [Matrix.of_apply]
      apply coeff_eq_zero_of_natDegree_lt
      rw [hd i]
      exact hij
  rw [hM, Matrix.det_mul, hC, one_mul]

theorem charpoly_leftMul_basis {E A : Type} [Field E] [CommRing A] [Algebra E A]
    [Module.Finite E A] {n : ℕ} (g : A) (w : Module.Basis (Fin n) E A) :
    (Algebra.leftMulMatrix w g).charpoly = (LinearMap.mulLeft E g).charpoly := by
  rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix]
  rfl

theorem trace_mul_eq {E A : Type} [Field E] [CommRing A] [Algebra E A] {n : ℕ} (x : Fin n → A)
    (h : A) (w : Module.Basis (Fin n) E A) :
    (Matrix.of fun k l : Fin n => Algebra.trace E A (x k * h * w l))
      = (Matrix.of fun k l : Fin n => Algebra.trace E A (x k * w l)) * Algebra.leftMulMatrix w h := by
  ext k l
  simp only [Matrix.of_apply, Matrix.mul_apply, Algebra.leftMulMatrix_eq_repr_mul]
  conv_lhs => rw [mul_assoc, ← w.sum_repr (h * w l)]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_smul_comm, map_smul, smul_eq_mul, mul_comm]

end GlobalTheory.TraceDetSplit


open GlobalTheory.TraceDetSplit in
theorem GlobalTheory.det_trace_pow_prod : ∀ (E A₁ A₂ : Type) [Field E] [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂] [Module.Finite E A₁] [Module.Finite E A₂] (g₁ : A₁) (g₂ : A₂) (a b : ℕ) (u : Module.Basis (Fin a) E A₁) (w : Module.Basis (Fin b) E A₂), ((LinearMap.mulLeft E g₁).charpoly * (LinearMap.mulLeft E g₂).charpoly).Separable → ∃ ε : E, ε * ε = 1 ∧ (Matrix.of fun k l : Fin (a + b) => Algebra.trace E (A₁ × A₂) ((g₁, g₂) ^ (k : ℕ) * Fin.addCases (fun i => (u i, 0)) (fun j => (0, w j)) l)).det = ε * resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly * (Matrix.of fun k l : Fin a => Algebra.trace E A₁ (g₁ ^ (k : ℕ) * u l)).det * (Matrix.of fun k l : Fin b => Algebra.trace E A₂ (g₂ ^ (k : ℕ) * w l)).det := by
  intro E A₁ A₂ _ _ _ _ _ _ _ g₁ g₂ a b u w _
  classical
  have hdeg₁ : (LinearMap.mulLeft E g₁).charpoly.natDegree = a := by
    rw [LinearMap.charpoly_natDegree, Module.finrank_eq_card_basis u, Fintype.card_fin]
  have hCH : aeval g₁ (LinearMap.mulLeft E g₁).charpoly = 0 := by
    have h := LinearMap.aeval_self_charpoly (LinearMap.mulLeft E g₁)
    have h2 : aeval (LinearMap.mulLeft E g₁) (LinearMap.mulLeft E g₁).charpoly =
        Algebra.lmul E A₁ (aeval g₁ (LinearMap.mulLeft E g₁).charpoly) :=
      Polynomial.aeval_algHom_apply (Algebra.lmul E A₁) g₁ _
    rw [h2] at h
    simpa using LinearMap.congr_fun h 1
  let q : Fin (a + b) → E[X] := fun k =>
    if (k : ℕ) < a then X ^ (k : ℕ) else X ^ ((k : ℕ) - a) * (LinearMap.mulLeft E g₁).charpoly
  have hd : ∀ k, (q k).natDegree = k := by
    intro k
    by_cases hk : (k : ℕ) < a
    · simp [q, hk]
    · simp only [q, hk, if_false]
      rw [(monic_X_pow _).natDegree_mul (LinearMap.charpoly_monic _), natDegree_X_pow, hdeg₁]
      omega
  have hm : ∀ k, (q k).Monic := by
    intro k
    by_cases hk : (k : ℕ) < a
    · simp only [q, hk, if_true]
      exact monic_X_pow _
    · simp only [q, hk, if_false]
      exact (monic_X_pow _).mul (LinearMap.charpoly_monic _)
  refine ⟨(-1) ^ (a * b), by rw [← mul_pow, neg_one_mul, neg_neg, one_pow], ?_⟩
  rw [det_trace_monic (g₁, g₂) _ q hd hm]
  let M := Matrix.of fun k l : Fin (a + b) => Algebra.trace E (A₁ × A₂)
    (aeval (g₁, g₂) (q k) * Fin.addCases (fun i => ((u i, 0) : A₁ × A₂)) (fun j => (0, w j)) l)
  let T₁ := Matrix.of fun k l : Fin a => Algebra.trace E A₁ (g₁ ^ (k : ℕ) * u l)
  let T₂ := Matrix.of fun k l : Fin b => Algebra.trace E A₂ (g₂ ^ (k : ℕ) * w l)
  let S := Matrix.of fun k l : Fin b =>
    Algebra.trace E A₂ (g₂ ^ (k : ℕ) * aeval g₂ (LinearMap.mulLeft E g₁).charpoly * w l)
  have hblock : M.submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks T₁ (Matrix.of fun i j => M (Fin.castAdd b i) (Fin.natAdd a j)) 0 S := by
    ext (i | i) (l | l)
    · simp [M, T₁, q, Algebra.trace_prod_apply, aeval_prod_apply]
    · simp [M]
    · simp [M, q, Algebra.trace_prod_apply, aeval_prod_apply, hCH]
    · simp [M, S, q, Algebra.trace_prod_apply, aeval_prod_apply, mul_assoc]
  have hS : S = T₂ * Algebra.leftMulMatrix w (aeval g₂ (LinearMap.mulLeft E g₁).charpoly) :=
    trace_mul_eq (fun k : Fin b => g₂ ^ (k : ℕ)) _ w
  have hres : (Algebra.leftMulMatrix w (aeval g₂ (LinearMap.mulLeft E g₁).charpoly)).det =
      (-1) ^ (b * a) * resultant (LinearMap.mulLeft E g₁).charpoly (LinearMap.mulLeft E g₂).charpoly := by
    rw [← Polynomial.aeval_algHom_apply, det_aeval _ _ (LinearMap.charpoly_monic _),
      charpoly_leftMul_basis, hdeg₁]
  calc M.det = (M.submatrix finSumFinEquiv finSumFinEquiv).det :=
        (Matrix.det_submatrix_equiv_self _ _).symm
    _ = T₁.det * S.det := by rw [hblock, Matrix.det_fromBlocks_zero₂₁]
    _ = _ := by
      rw [hS, Matrix.det_mul, hres]
      ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyMulLeftSeparableOfAdjoinEqTop
section
open Polynomial

namespace GlobalTheory

theorem charpoly_mulLeft_separable_of_adjoin_eq_top : ∀ (E A : Type) [Field E] [CharZero E] [CommRing A]
    [Algebra E A] [Module.Finite E A] (y : A), Algebra.adjoin E ({y} : Set A) = ⊤ → IsReduced A →
    (LinearMap.mulLeft E y).charpoly.Separable := by
  intro E A _ _ _ _ _ y htop hred
  have hint : IsIntegral E y := Algebra.IsIntegral.isIntegral y
  let pb := PowerBasis.ofAdjoinEqTop hint htop
  have hfin : Module.finrank E A = (minpoly E y).natDegree := pb.finrank
  have hmin : minpoly E (LinearMap.mulLeft E y) = minpoly E y := by
    have h := minpoly.algHom_eq (Algebra.lmul E A) (Algebra.lmul_injective (R := E) (A := A)) y
    rw [← h]
    rfl
  have hdvd : minpoly E y ∣ (LinearMap.mulLeft E y).charpoly :=
    hmin ▸ LinearMap.minpoly_dvd_charpoly _
  have heq : (LinearMap.mulLeft E y).charpoly = minpoly E y :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (LinearMap.charpoly_monic _) hdvd
      (by rw [LinearMap.charpoly_natDegree, hfin])
  rw [heq]
  have hsq : Squarefree (minpoly E y) := (minpoly.isRadical E y).squarefree (minpoly.ne_zero hint)
  exact PerfectField.separable_iff_squarefree.mpr hsq

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyNilpotentAddScalar
section
open Polynomial

namespace GlobalTheory

theorem charpoly_nilpotent_add_scalar : ∀ (k : Type) [Field k] (n : ℕ) (N : Matrix (Fin n) (Fin n) k) (c : k), IsNilpotent N → (N + Matrix.scalar (Fin n) c).charpoly = (X - C c) ^ n := by
  intro k _ n N c hN
  have hc : N.charpoly = X ^ n := by
    have := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hN
    rw [Fintype.card_fin] at this
    exact sub_eq_zero.mp this.eq_zero
  have h1 := Matrix.charpoly_sub_scalar (N + Matrix.scalar (Fin n) c) c
  rw [add_sub_cancel_right, hc] at h1
  have hXC : ((X : k[X]) + C c).comp (X - C c) = X := by simp
  calc (N + Matrix.scalar (Fin n) c).charpoly
      = ((N + Matrix.scalar (Fin n) c).charpoly.comp (X + C c)).comp (X - C c) := by
        rw [comp_assoc, hXC, comp_X]
    _ = (X - C c) ^ n := by rw [← h1]; simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeDualRep
section
noncomputable section

namespace GlobalTheory.MonoConj

def dualRep {Γ k : Type} [Group Γ] [CommRing k] {a : ℕ} (r : Γ →* GL (Fin a) k) : Γ →* GL (Fin a) k where
  toFun g := ⟨((r g⁻¹ : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).transpose,
    ((r g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).transpose, by
      rw [← Matrix.transpose_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
        Matrix.transpose_one], by
      rw [← Matrix.transpose_mul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
        Matrix.transpose_one]⟩
  map_one' := by
    apply Units.ext
    simp
  map_mul' g h := by
    apply Units.ext
    simp [mul_inv_rev, Matrix.transpose_mul]

theorem coe_dualRep {Γ k : Type} [Group Γ] [CommRing k] {a : ℕ} (r : Γ →* GL (Fin a) k) (g : Γ) :
    ((dualRep r g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
      ((r g⁻¹ : GL (Fin a) k) : Matrix (Fin a) (Fin a) k).transpose := rfl

end GlobalTheory.MonoConj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffAevalOneAddXPowSubOneNeZero
section
open scoped BigOperators

namespace GlobalTheory

private lemma one_add_X_pow_prime_pow_sub_one {k : Type} [Field k] (l : ℕ) [Fact l.Prime] [CharP k l]
    (m : ℕ) : (1 + Polynomial.X : Polynomial k) ^ (l ^ m) - 1 = Polynomial.X ^ (l ^ m) := by
  rw [add_pow_char_pow, one_pow, add_sub_cancel_left]

private lemma coeff_zero_aeval_of_coeff_zero_eq_zero {k σ : Type} [Field k] (g : σ → Polynomial k)
    (hg : ∀ q, (g q).coeff 0 = 0) (p : MvPolynomial σ k) :
    (MvPolynomial.aeval g p).coeff 0 = p.coeff 0 := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr => simp [hp, hr]
  | mul_X p q hp =>
    classical
    rw [map_mul, MvPolynomial.aeval_X, Polynomial.mul_coeff_zero, hg, mul_zero,
      MvPolynomial.coeff_mul_X']
    simp

theorem coeff_aeval_one_add_X_pow_sub_one_ne_zero :
    ∀ (k σ : Type) [Field k] [Fintype σ] (l M : ℕ) [Fact l.Prime] [CharP k l] (D u : MvPolynomial σ k) (n e : σ → ℕ), u.coeff 0 ≠ 0 → D - u * ∏ q, MvPolynomial.X q ^ n q ∈ Ideal.span (Set.range fun q : σ => (MvPolynomial.X q : MvPolynomial σ k) ^ (l ^ M)) → ∑ q, n q * l ^ e q < l ^ M → (MvPolynomial.aeval (fun q => (1 + Polynomial.X : Polynomial k) ^ (l ^ e q) - 1) D).coeff (∑ q, n q * l ^ e q) ≠ 0 := by
  intro k σ _ _ l M _ _ D u n e hu hD hlt
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hgX : ∀ q, ((1 + Polynomial.X : Polynomial k) ^ (l ^ e q) - 1) = Polynomial.X ^ (l ^ e q) :=
    fun q => one_add_X_pow_prime_pow_sub_one l (e q)
  simp only [hgX]

  have hideal : ∀ r ∈ Ideal.span (Set.range fun q : σ => (MvPolynomial.X q : MvPolynomial σ k) ^ (l ^ M)),
      (Polynomial.X : Polynomial k) ^ (l ^ M) ∣
        MvPolynomial.aeval (fun q => (Polynomial.X : Polynomial k) ^ (l ^ e q)) r := by
    intro r hr
    have hle : Ideal.span (Set.range fun q : σ => (MvPolynomial.X q : MvPolynomial σ k) ^ (l ^ M)) ≤
        Ideal.comap (MvPolynomial.aeval (fun q => (Polynomial.X : Polynomial k) ^ (l ^ e q)))
          (Ideal.span {(Polynomial.X : Polynomial k) ^ (l ^ M)}) := by
      rw [Ideal.span_le]
      rintro _ ⟨q, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_comap, map_pow, MvPolynomial.aeval_X, ← pow_mul, pow_mul',
        Ideal.mem_span_singleton]
      exact dvd_pow_self _ (pow_pos hl _).ne'
    exact Ideal.mem_span_singleton.mp (hle hr)
  obtain ⟨r, hr, rfl⟩ : ∃ r ∈ Ideal.span (Set.range fun q : σ => (MvPolynomial.X q : MvPolynomial σ k) ^ (l ^ M)),
      D = u * ∏ q, MvPolynomial.X q ^ n q + r := ⟨_, hD, by ring⟩
  rw [map_add (f := _), Polynomial.coeff_add, (Polynomial.X_pow_dvd_iff.mp (hideal r hr)) _ hlt, add_zero,
    map_mul, map_prod]
  simp only [map_pow, MvPolynomial.aeval_X, ← pow_mul, Finset.prod_pow_eq_pow_sum]
  have hsum : ∑ q, l ^ e q * n q = ∑ q, n q * l ^ e q :=
    Finset.sum_congr rfl fun q _ => mul_comm _ _
  rw [hsum, Polynomial.coeff_mul_X_pow', if_pos le_rfl, Nat.sub_self, coeff_zero_aeval_of_coeff_zero_eq_zero _ _ u]
  · exact hu
  · intro q
    rw [Polynomial.coeff_X_pow, if_neg (pow_pos hl _).ne]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffMemOfPowMul
section
namespace GlobalTheory.OrdMul

open MvPolynomial

theorem coeff_mem_of_mul {O : Type} [CommRing O] (I : Ideal O) {ι : Type} (K : Set ι) (q : ι)
    (hq : q ∉ K) (a F : MvPolynomial ι O) (N : ℕ) (h0 : a.coeff 0 = 0)
    (hu : IsUnit (a.coeff (Finsupp.single q 1)))
    (H : ∀ m : ι →₀ ℕ, m.degree < N + 1 → (∀ j ∈ K, m j = 0) → (a * F).coeff m ∈ I) :
    ∀ m : ι →₀ ℕ, m.degree < N → (∀ j ∈ K, m j = 0) → F.coeff m ∈ I := by
  classical

  have key : ∀ n : ℕ, ∀ m : ι →₀ ℕ, m q + 2 * (m.erase q).degree = n → m.degree < N →
      (∀ j ∈ K, m j = 0) → F.coeff m ∈ I := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro m hμ hm hK
      set m' : ι →₀ ℕ := m + Finsupp.single q 1 with hm'
      have hdeg' : m'.degree < N + 1 := by
        rw [hm', map_add (f := _), Finsupp.degree_single]; omega
      have hK' : ∀ j ∈ K, m' j = 0 := by
        intro j hj
        have hqj : q ≠ j := fun h => hq (h ▸ hj)
        simp [hm', hK j hj, Finsupp.single_apply, hqj]
      have hH := H m' hdeg' hK'
      rw [MvPolynomial.coeff_mul] at hH
      have hmem : (Finsupp.single q 1, m) ∈ Finset.HasAntidiagonal.antidiagonal m' := by
        rw [Finset.HasAntidiagonal.mem_antidiagonal, hm']; exact add_comm _ _
      rw [← Finset.add_sum_erase _ _ hmem] at hH
      have hrest : ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal m').erase (Finsupp.single q 1, m),
          a.coeff x.1 * F.coeff x.2 ∈ I := by
        refine Ideal.sum_mem _ (fun x hx => ?_)
        obtain ⟨hne, hx⟩ := Finset.mem_erase.mp hx
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        by_cases hi : x.1 = 0
        · rw [hi, h0, zero_mul]; exact I.zero_mem
        · apply I.mul_mem_left
          have hiq : x.1 ≠ Finsupp.single q 1 := by
            intro h
            apply hne
            refine Prod.ext h ?_
            rw [h, hm', add_comm m] at hx
            exact add_left_cancel hx
          have hxq : x.1 q + x.2 q = m q + 1 := by
            have := congrArg (fun f : ι →₀ ℕ => f q) hx
            simpa [hm'] using this
          have hxe : x.1.erase q + x.2.erase q = m.erase q := by
            have := congrArg (Finsupp.erase q) hx
            simpa [hm', Finsupp.erase_add] using this
          have hD : (x.1.erase q).degree + (x.2.erase q).degree = (m.erase q).degree := by
            rw [← map_add (f := _), hxe]
          have hdx : x.1.degree + x.2.degree = m.degree + 1 := by
            have := congrArg Finsupp.degree hx
            simpa [hm'] using this
          have hd1 : x.1.degree ≠ 0 := fun h => hi ((Finsupp.degree_eq_zero_iff _).mp h)

          have hw : 2 ≤ x.1 q + 2 * (x.1.erase q).degree := by
            by_cases he : x.1.erase q = 0
            · have hs : Finsupp.single q (x.1 q) = x.1 := by
                simpa [he] using Finsupp.single_add_erase q x.1
              have h0' : x.1 q ≠ 0 := by
                intro h; apply hi; rw [← hs, h, Finsupp.single_zero]
              have h1' : x.1 q ≠ 1 := by
                intro h; apply hiq; rw [← hs, h]
              omega
            · have : (x.1.erase q).degree ≠ 0 := fun h => he ((Finsupp.degree_eq_zero_iff _).mp h)
              omega
          refine ih (x.2 q + 2 * (x.2.erase q).degree) (by omega) x.2 rfl (by omega) ?_
          intro j hj
          have h1 := hK' j hj
          rw [← hx] at h1
          simp only [Finsupp.add_apply] at h1
          omega
      have hmain : a.coeff (Finsupp.single q 1) * F.coeff m ∈ I :=
        (Ideal.add_mem_iff_left I hrest).mp hH
      exact (Ideal.unit_mul_mem_iff_mem I hu).mp hmain
  exact fun m hm hK => key _ m rfl hm hK

theorem coeff_mem_of_pow_mul : ∀ (O : Type) [CommRing O] (I : Ideal O) (ι : Type) (K : Set ι) (q : ι), q ∉ K → ∀ (a F : MvPolynomial ι O) (N k : ℕ), a.coeff 0 = 0 → IsUnit (a.coeff (Finsupp.single q 1)) → (∀ m : ι →₀ ℕ, m.degree < N + k → (∀ j ∈ K, m j = 0) → (a ^ k * F).coeff m ∈ I) → ∀ m : ι →₀ ℕ, m.degree < N → (∀ j ∈ K, m j = 0) → F.coeff m ∈ I := by
  intro O _ I ι K q hq a F N k h0 hu H
  induction k generalizing F N with
  | zero =>
    intro m hm hK
    simpa using H m (by simpa using hm) hK
  | succ k ih =>
    refine coeff_mem_of_mul I K q hq a F N h0 hu ?_
    refine ih (a * F) (N + 1) ?_
    intro m hm hK
    have := H m (by omega) hK
    rwa [pow_succ, mul_assoc] at this

end GlobalTheory.OrdMul
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroSmulMemMap
section
namespace GlobalTheory.CoefficientMembership

theorem aeval_mem {O V : Type} [CommRing O] [AddCommGroup V] [Module O V] (T : Module.End O V)
    (Z : Submodule O V) (hZ : ∀ z ∈ Z, T z ∈ Z) (q : Polynomial O) :
    ∀ w ∈ Z, (Polynomial.aeval T q) w ∈ Z := by
  intro w hw
  have hpow : ∀ k : ℕ, (T ^ k) w ∈ Z := by
    intro k
    induction k with
    | zero => simpa using hw
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply]
      exact hZ _ ih
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add (f := _), LinearMap.add_apply]
    exact Z.add_mem hp hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact Z.smul_mem a (hpow n)

theorem coeff_zero_smul_mem_map : ∀ {O V : Type} [inst : CommRing O] [inst_1 : AddCommGroup V] [inst_2 : Module O V] (T : Module.End O V) (Rp : Polynomial O), (Polynomial.aeval T : Polynomial O → Module.End O V) Rp * T = (0 : Module.End O V) → ∀ (Z : Submodule O V), (∀ z ∈ Z, (T : V → V) z ∈ Z) → ∀ w ∈ Z, w ∈ LinearMap.range T → _root_.AddMonoidAlgebra.coeff (M := ℕ) Rp (0 : ℕ) • w ∈ Submodule.map T Z := by
  intro O V _ _ _ T Rp hR Z hZ w hw hwr
  obtain ⟨v, rfl⟩ := hwr
  have key : (Polynomial.aeval T Rp) (T v) =
      T ((Polynomial.aeval T Rp.divX) (T v)) + Rp.coeff 0 • T v := by
    conv_lhs => rw [← Polynomial.X_mul_divX_add Rp]
    rw [map_add (f := _), map_mul, Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.add_apply,
      Module.End.mul_apply, Module.algebraMap_end_apply]
  have h0 : (Polynomial.aeval T Rp) (T v) = 0 := by
    have := congrArg (fun f : Module.End O V => f v) hR
    simpa using this
  rw [h0] at key
  refine Submodule.mem_map.mpr ⟨-(Polynomial.aeval T Rp.divX) (T v),
    Z.neg_mem (aeval_mem T Z hZ _ _ hw), ?_⟩
  rw [map_neg]
  exact neg_eq_of_add_eq_zero_right key.symm

end GlobalTheory.CoefficientMembership
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommuteInvLeft
section
namespace GlobalTheory.CommuteInvLeft

theorem commute_inv_left : ∀ {B : Type} [inst : Ring B] {x xi y : B},
    x * xi = (1 : B) → xi * x = (1 : B) → Commute x y → Commute xi y := by
  intro B _ x xi y h1 h2 h
  have h' : x * y = y * x := h
  show xi * y = y * xi
  calc xi * y = xi * y * (x * xi) := by rw [h1, mul_one]
    _ = xi * (y * x) * xi := by simp only [mul_assoc]
    _ = xi * (x * y) * xi := by rw [h']
    _ = (xi * x) * y * xi := by simp only [mul_assoc]
    _ = y * xi := by rw [h2, one_mul]

end GlobalTheory.CommuteInvLeft
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DerivationMemPow
section
namespace GlobalTheory.DerivationPowerIdeal

theorem derivation_mem_pow {A' : Type} [CommRing A'] {k : Type} [CommRing k] [Algebra k A']
    (I : Ideal A') (D : Derivation k A' A') (n : ℕ) {x : A'} (hx : x ∈ I ^ (n + 1)) :
    D x ∈ I ^ n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [pow_succ' I (n + 1)] at hx
    refine Submodule.mul_induction_on hx ?_ ?_
    · intro a ha b hb
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      refine Ideal.add_mem _ ?_ (Ideal.mul_mem_right _ _ hb)
      rw [pow_succ' I n]
      exact Ideal.mul_mem_mul ha (ih hb)
    · intro a b ha hb
      rw [map_add (f := _)]
      exact Ideal.add_mem _ ha hb

end GlobalTheory.DerivationPowerIdeal
end

