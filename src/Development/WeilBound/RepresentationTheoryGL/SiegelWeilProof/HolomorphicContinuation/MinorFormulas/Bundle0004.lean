module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.DetEqZeroOfRankLt
section
noncomputable section

open MvPolynomial Matrix Module

namespace PositivityTheory.Rg.Sw.SP

namespace NullPf

variable {K : Type*} [Field K]

theorem exists_rows {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] (M : Matrix m n K) {k : ℕ} (hk : k ≤ M.rank) :
    ∃ I : Fin k ↪ m, LinearIndependent K (fun p => M (I p)) := by
  classical
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent K (Set.range M.row)
  have hfin : b.Finite := (Set.finite_range _).subset hbs
  have : Fintype b := hfin.fintype
  have hcard : M.rank = b.toFinset.card := by
    rw [M.rank_eq_finrank_span_row, ← hspan]
    exact finrank_span_set_eq_card hli
  have hkb : k ≤ Fintype.card b := by rw [← Set.toFinset_card]; omega
  let e : Fin k ↪ b := (Fin.castLEEmb hkb).trans (Fintype.equivFin b).symm.toEmbedding
  let sec : b → m := fun v => (hbs v.2).choose
  have hsec : ∀ v : b, M.row (sec v) = v := fun v => (hbs v.2).choose_spec
  have hinj : Function.Injective sec := by
    intro v w h
    apply Subtype.ext
    rw [← hsec v, ← hsec w, h]
  refine ⟨e.trans ⟨sec, hinj⟩, ?_⟩
  have h2 : (fun p => M ((e.trans ⟨sec, hinj⟩) p)) = (fun v : b => (v : n → K)) ∘ e := by
    funext p
    simp only [Function.comp_apply, Function.Embedding.trans_apply, Function.Embedding.coeFn_mk]
    exact hsec (e p)
  rw [h2]
  exact hli.comp e e.injective

theorem exists_minor_ne_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {k : ℕ} (hk : k ≤ M.rank) :
    ∃ I J : Fin k ↪ Fin n, (M.submatrix I J).det ≠ 0 := by
  classical
  obtain ⟨I, hI⟩ := exists_rows M hk
  set R : Matrix (Fin k) (Fin n) K := M.submatrix I id with hR
  have hRrank : R.rank = k := by
    have : LinearIndependent K R.row := hI
    simpa using this.rank_matrix
  have hRt : k ≤ Rᵀ.rank := by rw [rank_transpose, hRrank]
  obtain ⟨J, hJ⟩ := exists_rows Rᵀ hRt
  refine ⟨I, J, ?_⟩
  set T : Matrix (Fin k) (Fin k) K := Rᵀ.submatrix J id with hT
  have hTu : IsUnit T := by
    rw [← linearIndependent_rows_iff_isUnit]
    exact hJ
  have hTeq : T = (M.submatrix I J)ᵀ := by
    ext p q
    simp [T, R, transpose_apply, submatrix_apply]
  have := (Matrix.isUnit_iff_isUnit_det T).1 hTu
  rw [hTeq, det_transpose] at this
  exact this.ne_zero

theorem rank_lt_of_minors {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {k : ℕ}
    (h : ∀ I J : Fin k ↪ Fin n, (M.submatrix I J).det = 0) : M.rank < k := by
  by_contra hc
  obtain ⟨I, J, hIJ⟩ := exists_minor_ne_zero M (not_lt.1 hc)
  exact hIJ (h I J)

theorem rank_add_le' {n : ℕ} (A B : Matrix (Fin n) (Fin n) K) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  calc finrank K (LinearMap.range (A.mulVecLin + B.mulVecLin))
      ≤ finrank K ↥(LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin : Submodule K (Fin n → K)) :=
        Submodule.finrank_mono (LinearMap.range_add_le _ _)
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

theorem det_eq_zero_of_rank_lt {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (h : M.rank < n) : M.det = 0 := by
  by_contra hd
  have := Matrix.rank_of_isUnit M ((Matrix.isUnit_iff_isUnit_det M).2 (Ne.isUnit hd))
  simp at this
  omega

end NullPf

open NullPf in
theorem null : Null := by
  classical
  intro n m hmn N₀
  set S : Set (PAB n) := {x : PAB n | ∃ i j : ℕ, i + j = n - m ∧
        ((i = 0 ∧ j = 0 ∧ x = 1) ∨
         (i = 0 ∧ 0 < j ∧ ∃ (I J : Fin j ↪ Fin n), x = minorPolynomial true I J ^ N₀) ∨
         (0 < i ∧ j = 0 ∧ ∃ (I J : Fin (m + i) ↪ Fin n), x = minorPolynomial false I J ^ N₀) ∨
         (0 < i ∧ 0 < j ∧ ∃ (I J : Fin (m + i) ↪ Fin n) (I' J' : Fin j ↪ Fin n),
            x = minorPolynomial false I J ^ N₀ * minorPolynomial true I' J' ^ N₀))} with hS
  set D : PAB n := Matrix.det (fun p q : Fin n => (X (false, p, q) + X (true, p, q) : PAB n)) with hD
  suffices hrad : D ∈ (Ideal.span S).radical from (Ideal.mem_radical_iff).1 hrad
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := ℂ)]
  intro x hx
  rw [mem_zeroLocus_iff] at hx
  have hgen : ∀ s ∈ S, aeval x s = 0 := fun s hs => hx s (Ideal.subset_span hs)
  set A : Matrix (Fin n) (Fin n) ℂ := fun p q => x (false, p, q) with hA
  set B : Matrix (Fin n) (Fin n) ℂ := fun p q => x (true, p, q) with hB
  have hminor : ∀ (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n),
      aeval x (minorPolynomial b I J) = Matrix.det (fun p q : Fin ρ => x (b, I p, J q)) := by
    intro b ρ I J
    calc aeval x (minorPolynomial b I J) = ((aeval x : PAB n →ₐ[ℂ] ℂ) : PAB n →+* ℂ) (minorPolynomial b I J) := rfl
      _ = _ := by
        have h := RingHom.map_det ((aeval x : PAB n →ₐ[ℂ] ℂ) : PAB n →+* ℂ)
          (Matrix.of fun p q : Fin ρ => (X (b, I p, J q) : PAB n))
        refine h.trans ?_
        congr 1
        ext p q
        simp
  have hpow : ∀ (a : ℂ), a ^ N₀ = 0 → a = 0 := fun a h => ((pow_eq_zero_iff' (M₀ := ℂ)).1 h).1
  have hr : 0 < n - m := by omega

  have hBr : B.rank < n - m := by
    apply rank_lt_of_minors
    intro I J
    have := hgen (minorPolynomial true I J ^ N₀) ⟨0, n - m, by omega, Or.inr (Or.inl ⟨rfl, hr, I, J, rfl⟩)⟩
    rw [map_pow, hminor] at this
    exact hpow _ this
  have hsum : (A + B).rank < n := by
    rcases Nat.eq_zero_or_pos B.rank with h0 | hpos
    · have hAr : A.rank < m + (n - m) := by
        apply rank_lt_of_minors
        intro I J
        have := hgen (minorPolynomial false I J ^ N₀) ⟨n - m, 0, by omega, Or.inr (Or.inr (Or.inl ⟨hr, rfl, I, J, rfl⟩))⟩
        rw [map_pow, hminor] at this
        exact hpow _ this
      have := rank_add_le' A B
      omega
    · obtain ⟨I', J', hIJ'⟩ := exists_minor_ne_zero B (le_refl B.rank)
      have hAr : A.rank < m + (n - m - B.rank) := by
        apply rank_lt_of_minors
        intro I J
        have := hgen (minorPolynomial false I J ^ N₀ * minorPolynomial true I' J' ^ N₀)
          ⟨n - m - B.rank, B.rank, by omega, Or.inr (Or.inr (Or.inr ⟨by omega, hpos, I, J, I', J', rfl⟩))⟩
        rw [map_mul, map_pow, map_pow, hminor, hminor] at this
        rcases mul_eq_zero.1 this with h | h
        · exact hpow _ h
        · exact absurd (hpow _ h) hIJ'
      have := rank_add_le' A B
      omega
  have hdet := det_eq_zero_of_rank_lt (A + B) hsum
  calc aeval x D = ((aeval x : PAB n →ₐ[ℂ] ℂ) : PAB n →+* ℂ) D := rfl
    _ = (A + B).det := by
        have h := RingHom.map_det ((aeval x : PAB n →ₐ[ℂ] ℂ) : PAB n →+* ℂ)
          (Matrix.of fun p q : Fin n => (X (false, p, q) + X (true, p, q) : PAB n))
        refine h.trans ?_
        congr 1
        ext p q
        simp [A, B, Matrix.add_apply]
        rfl
    _ = 0 := hdet

end PositivityTheory.Rg.Sw.SP
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.MinorFormula
section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.SP

open PositivityTheory.Rg.Sw.SP.Mi

variable {n : ℕ}

def alMn (m : ℕ) (b : Bool) : Polynomial ℂ := if b then Polynomial.X else Polynomial.C (m : ℂ) + Polynomial.X

def cMn (s : ℂ) (b : Bool) : ℂ := if b then Complex.I * s else -(Complex.I * s)

def phi (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) : Pm (Polynomial ℂ) ρ →ₐ[Polynomial ℂ] Fm n :=
  rename fun pq => (b, J pq.1, I pq.2)

theorem phi_X (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) (p q : Fin ρ) : phi b I J (X (p, q)) = yv b (J p) (I q) := by
  simp [phi, yv, rename_X]

set_option maxHeartbeats 2000000 in
theorem deriv_part (s : ℂ) (m : ℕ) (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) (p q : Fin ρ) (f : Pm (Polynomial ℂ) ρ) :
    (∑ a : Fin n, ∑ d : Fin n, yv b a (I p) * yv b (J q) d * pderiv (b, a, d) (phi b I J f)) = phi b I J (del p q f) := by
  induction f using MvPolynomial.induction_on with
  | C r =>
    simp [phi, del]
  | add f g hf hg =>
    simp only [map_add (f := _), Derivation.leibniz, mul_add, Finset.sum_add_distrib, hf, hg]
  | mul_X f pq hf =>
    have e : phi b I J (f * X pq) = phi b I J f * yv b (J pq.1) (I pq.2) := by rw [map_mul, phi_X]
    have hdx : del p q (X pq : Pm (Polynomial ℂ) ρ) = X (pq.1, p) * X (q, pq.2) := by simp [del, mkDerivation_X]
    rw [e, Derivation.leibniz (del p q), smul_eq_mul, smul_eq_mul, map_add (f := _), map_mul, map_mul, ← hf, hdx, map_mul,
      phi_X, phi_X, phi_X]
    have hsplit : ∀ a d : Fin n, yv b a (I p) * yv b (J q) d * pderiv (b, a, d) (phi b I J f * yv b (J pq.1) (I pq.2)) =
        yv b (J pq.1) (I pq.2) * (yv b a (I p) * yv b (J q) d * pderiv (b, a, d) (phi b I J f)) +
          phi b I J f * (yv b a (I p) * yv b (J q) d * pderiv (b, a, d) (yv b (J pq.1) (I pq.2))) := by
      intro a d
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      ring
    simp only [hsplit, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hpart : (∑ a : Fin n, ∑ d : Fin n, yv b a (I p) * yv b (J q) d * pderiv (b, a, d) (yv b (J pq.1) (I pq.2))) =
        yv b (J pq.1) (I p) * yv b (J q) (I pq.2) := by
      rw [Finset.sum_eq_single (J pq.1), Finset.sum_eq_single (I pq.2)]
      · simp only [yv, pderiv_X, Pi.single_eq_same, mul_one]
      · intro d _ hd
        simp only [yv, pderiv_X]
        rw [Pi.single_eq_of_ne (fun h => hd (congrArg (fun x : Bool × Fin n × Fin n => x.2.2) h).symm), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
      · intro a _ ha
        refine Finset.sum_eq_zero fun d _ => ?_
        simp only [yv, pderiv_X]
        rw [Pi.single_eq_of_ne (fun h => ha (congrArg (fun x : Bool × Fin n × Fin n => x.2.1) h).symm), mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hpart, add_comm]

set_option maxHeartbeats 2000000 in
theorem opH_phi (s : ℂ) (m : ℕ) (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) (p q : Fin ρ) (f : Pm (Polynomial ℂ) ρ) :
    opH s m b (I p) (J q) (phi b I J f) = (-(cMn s b)) • phi b I J (opE (alMn m b) p q f) := by
  have h := deriv_part s m b I J p q f
  simp only [opH, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.restrictScalars_apply, LinearMap.mulLeft_apply,
    LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.coe_restrictScalars, Derivation.coeFn_coe, opE, map_add, map_mul]
  have hs : (∑ a : Fin n, ∑ d : Fin n, (-(if b = true then Complex.I * s else -(Complex.I * s))) •
      (yv b a (I p) * yv b (J q) d * (pderiv (b, a, d)) (phi b I J f))) =
      (-(if b = true then Complex.I * s else -(Complex.I * s))) • ∑ a : Fin n, ∑ d : Fin n,
        yv b a (I p) * yv b (J q) d * (pderiv (b, a, d)) (phi b I J f) := by
    simp only [Finset.smul_sum]
  have h1 : phi b I J (C (alMn m b)) = C (if b = true then Polynomial.X else Polynomial.C (m : ℂ) + Polynomial.X) := by
    simp only [phi, rename_C, alMn]
  rw [hs, h, ← smul_add, h1, phi_X]
  rfl

theorem foldr_phi (s : ℂ) (m : ℕ) (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) (σ : Equiv.Perm (Fin ρ)) (L : List (Fin ρ))
    (f : Pm (Polynomial ℂ) ρ) :
    (L.foldr (fun k g => opH s m b (I k) (J (σ k)) ∘ₗ g) LinearMap.id) (phi b I J f) =
      (-(cMn s b)) ^ L.length • phi b I J ((L.foldr (fun k g => opE (alMn m b) k (σ k) ∘ₗ g) LinearMap.id) f) := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.foldr_cons, LinearMap.comp_apply, ih, map_smul, opH_phi, smul_smul, List.length_cons, pow_succ]

theorem minorOp_phi (s : ℂ) (m : ℕ) (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) (f : Pm (Polynomial ℂ) ρ) :
    minorOp s m b I J (phi b I J f) = (-(cMn s b)) ^ ρ • phi b I J (detE (alMn m b) f) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [minorOp, detE, LinearMap.sum_apply, LinearMap.smul_apply, foldr_phi, List.length_finRange, map_sum,
    map_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, smul_comm]

theorem iter_phi (s : ℂ) (m : ℕ) (b : Bool) {ρ : ℕ} (I J : Fin ρ ↪ Fin n) (N : ℕ) (f : Pm (Polynomial ℂ) ρ) :
    (minorOp s m b I J)^[N] (phi b I J f) = ((-(cMn s b)) ^ ρ) ^ N • phi b I J ((detE (alMn m b))^[N] f) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ_apply', ih, map_smul, minorOp_phi, smul_smul, Function.iterate_succ_apply', pow_succ,
      mul_comm]

theorem prodId (a : Polynomial ℂ) (c : ℂ) (ρ N : ℕ) :
    Polynomial.C (((-c) ^ ρ) ^ N) * ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ, (a + (l : Polynomial ℂ) - (i : Polynomial ℂ)) =
      Polynomial.C ((c ^ ρ) ^ N) * ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ, (-a - Polynomial.C ((l : ℂ) - i)) := by
  have e : ∀ l i : ℕ, (-a - Polynomial.C ((l : ℂ) - i)) = (-1) * (a + (l : Polynomial ℂ) - (i : Polynomial ℂ)) := by
    intro l i
    simp only [map_sub, map_natCast]
    ring
  simp_rw [e, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  simp only [map_pow, map_neg]
  ring

theorem minorFormula : MinorFormula := by
  intro n s hs m b ρ N I J
  have h1 : (1 : Fm n) = phi b I J 1 := (map_one _).symm
  rw [h1, iter_phi, iter]
  have hc : (∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ,
      (MvPolynomial.C (alMn m b) + (l : Pm (Polynomial ℂ) ρ) - (i : Pm (Polynomial ℂ) ρ))) =
      MvPolynomial.C (∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ, (alMn m b + (l : Polynomial ℂ) - (i : Polynomial ℂ))) := by
    simp [map_prod]
  have hdet : phi b I J ((Xm (Polynomial ℂ) ρ).det) = Matrix.det (fun p q : Fin ρ => yv b (J p) (I q)) := by
    rw [AlgHom.map_det]
    congr 1
    ext p q
    simp [Xm, phi_X]
  rw [hc, map_mul, map_pow, hdet]
  simp only [phi, rename_C]
  rw [Algebra.smul_def, ← mul_assoc]
  congr 1
  rw [MvPolynomial.algebraMap_apply, Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, ← map_mul]
  congr 1
  exact prodId _ _ ρ N

end PositivityTheory.Rg.Sw.SP
end
end

