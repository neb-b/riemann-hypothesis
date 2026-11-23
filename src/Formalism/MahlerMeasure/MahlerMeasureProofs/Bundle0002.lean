module

public import Formalism.MahlerMeasure.Bundle0003
public import Formalism.MahlerMeasure.MahlerMeasureProofs.LevelAct
public import Formalism.MahlerMeasure.MahlerMeasureProofs.Mahler
public import Formalism.SmithDeterminants.TruncationChainBoundNonnegExponents

@[expose] public section

-- bundled from Formalism.MahlerMeasure.MahlerMeasureProofs.GaussRad
section
namespace Formalism.GM

open Finset Polynomial

section

variable {K : Type} [NormedField K]

lemma gaussR_term_le (ρ : NNReal) (P : K[X]) (k : ℕ) :
    ‖P.coeff k‖₊ * ρ ^ k ≤ gaussR ρ P := by
  by_cases hk : k ∈ P.support
  · exact Finset.le_sup (f := fun k => ‖P.coeff k‖₊ * ρ ^ k) hk
  · have h0 : P.coeff k = 0 := by simpa using hk
    simp [h0]

lemma gaussR_le_iff (ρ : NNReal) (P : K[X]) (c : NNReal) :
    gaussR ρ P ≤ c ↔ ∀ k, ‖P.coeff k‖₊ * ρ ^ k ≤ c := ⟨fun h k => (gaussR_term_le ρ P k).trans h, fun h => Finset.sup_le fun k _ => h k⟩

lemma gaussR_attained (ρ : NNReal) (P : K[X]) (hP : P ≠ 0) :
    ∃ k, ‖P.coeff k‖₊ * ρ ^ k = gaussR ρ P := by
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_sup P.support (Polynomial.support_nonempty.2 hP)
    (fun k => ‖P.coeff k‖₊ * ρ ^ k)
  exact ⟨k, hk.symm⟩

lemma gaussR_attained_least (ρ : NNReal) (P : K[X]) (hP : P ≠ 0) :
    ∃ i₀, ‖P.coeff i₀‖₊ * ρ ^ i₀ = gaussR ρ P ∧
      ∀ i < i₀, ‖P.coeff i‖₊ * ρ ^ i < gaussR ρ P := by
  classical
  have h := gaussR_attained ρ P hP
  exact ⟨Nat.find h, Nat.find_spec h, fun i hi => lt_of_le_of_ne (gaussR_term_le ρ P i) (Nat.find_min h hi)⟩

lemma gaussR_pos (ρ : NNReal) (hρ : 0 < ρ) (P : K[X]) (hP : P ≠ 0) : 0 < gaussR ρ P := by
  obtain ⟨k, hk, hk'⟩ := Finset.exists_mem_eq_sup P.support (Polynomial.support_nonempty.2 hP)
    (fun k => ‖P.coeff k‖₊ * ρ ^ k)
  unfold gaussR
  rw [hk']
  exact mul_pos (nnnorm_pos.2 (Polynomial.mem_support_iff.1 hk)) (pow_pos hρ k)

lemma gaussR_zero (ρ : NNReal) : gaussR ρ (0 : K[X]) = 0 := by
  simp [gaussR]

variable [IsUltrametricDist K]

lemma gaussR_mul_le (ρ : NNReal) (P Q : K[X]) :
    gaussR ρ (P * Q) ≤ gaussR ρ P * gaussR ρ Q := by
  rw [gaussR_le_iff]
  intro k
  rw [Polynomial.coeff_mul]
  have h1 : ‖∑ x ∈ Finset.HasAntidiagonal.antidiagonal k, P.coeff x.1 * Q.coeff x.2‖₊ ≤
      (Finset.HasAntidiagonal.antidiagonal k).sup (fun x => ‖P.coeff x.1 * Q.coeff x.2‖₊) :=
    IsUltrametricDist.nnnorm_sum_le_of_forall_le
      (fun x hx => Finset.le_sup (f := fun x => ‖P.coeff x.1 * Q.coeff x.2‖₊) hx)
  obtain ⟨x, hx, hxe⟩ := Finset.exists_mem_eq_sup (Finset.HasAntidiagonal.antidiagonal k) ⟨(0, k), by simp⟩
    (fun x => ‖P.coeff x.1 * Q.coeff x.2‖₊)
  have hk : x.1 + x.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
  calc ‖∑ x ∈ Finset.HasAntidiagonal.antidiagonal k, P.coeff x.1 * Q.coeff x.2‖₊ * ρ ^ k
      ≤ (Finset.HasAntidiagonal.antidiagonal k).sup (fun x => ‖P.coeff x.1 * Q.coeff x.2‖₊) * ρ ^ k :=
        mul_le_mul_of_nonneg_right h1 zero_le
    _ = ‖P.coeff x.1 * Q.coeff x.2‖₊ * ρ ^ k := by rw [hxe]
    _ = (‖P.coeff x.1‖₊ * ρ ^ x.1) * (‖Q.coeff x.2‖₊ * ρ ^ x.2) := by
        rw [nnnorm_mul, ← hk, pow_add]
        ring
    _ ≤ gaussR ρ P * gaussR ρ Q := mul_le_mul' (gaussR_term_le ρ P _) (gaussR_term_le ρ Q _)

lemma le_gaussR_mul (ρ : NNReal) (hρ : 0 < ρ) (P Q : K[X]) :
    gaussR ρ P * gaussR ρ Q ≤ gaussR ρ (P * Q) := by
  by_cases hP : P = 0
  · simp [hP, gaussR_zero]
  by_cases hQ : Q = 0
  · simp [hQ, gaussR_zero]
  obtain ⟨i₀, hi₀, hlt_i⟩ := gaussR_attained_least ρ P hP
  obtain ⟨j₀, hj₀, hlt_j⟩ := gaussR_attained_least ρ Q hQ
  have hgP := gaussR_pos ρ hρ P hP
  have hgQ := gaussR_pos ρ hρ Q hQ
  have hρk : 0 < ρ ^ (i₀ + j₀) := pow_pos hρ _
  have hsplit : (P * Q).coeff (i₀ + j₀) = P.coeff i₀ * Q.coeff j₀ +
      ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (i₀ + j₀)).erase (i₀, j₀), P.coeff x.1 * Q.coeff x.2 := by
    have hmem : ((i₀, j₀) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (i₀ + j₀) :=
      Finset.HasAntidiagonal.mem_antidiagonal.2 rfl
    rw [Polynomial.coeff_mul, Finset.add_sum_erase _ (fun x : ℕ × ℕ => P.coeff x.1 * Q.coeff x.2) hmem]
  have hterm : ∀ x ∈ (Finset.HasAntidiagonal.antidiagonal (i₀ + j₀)).erase (i₀, j₀),
      ‖P.coeff x.1 * Q.coeff x.2‖₊ * ρ ^ (i₀ + j₀) < gaussR ρ P * gaussR ρ Q := by
    intro x hx
    obtain ⟨hne, hx'⟩ := Finset.mem_erase.1 hx
    have hsum : x.1 + x.2 = i₀ + j₀ := Finset.HasAntidiagonal.mem_antidiagonal.1 hx'
    have e : ‖P.coeff x.1 * Q.coeff x.2‖₊ * ρ ^ (i₀ + j₀) =
        (‖P.coeff x.1‖₊ * ρ ^ x.1) * (‖Q.coeff x.2‖₊ * ρ ^ x.2) := by
      rw [nnnorm_mul, ← hsum, pow_add]
      ring
    rw [e]
    by_cases h1 : x.1 < i₀
    · calc (‖P.coeff x.1‖₊ * ρ ^ x.1) * (‖Q.coeff x.2‖₊ * ρ ^ x.2)
          ≤ (‖P.coeff x.1‖₊ * ρ ^ x.1) * gaussR ρ Q := mul_le_mul_of_nonneg_left (gaussR_term_le ρ Q _) zero_le
        _ < gaussR ρ P * gaussR ρ Q := mul_lt_mul_of_pos_right (hlt_i _ h1) hgQ
    · have h2 : x.2 < j₀ := by
        by_contra h
        exact hne (Prod.ext (by omega) (by omega))
      calc (‖P.coeff x.1‖₊ * ρ ^ x.1) * (‖Q.coeff x.2‖₊ * ρ ^ x.2)
          ≤ gaussR ρ P * (‖Q.coeff x.2‖₊ * ρ ^ x.2) := mul_le_mul_of_nonneg_right (gaussR_term_le ρ P _) zero_le
        _ < gaussR ρ P * gaussR ρ Q := mul_lt_mul_of_pos_left (hlt_j _ h2) hgP
  have hsup : ((Finset.HasAntidiagonal.antidiagonal (i₀ + j₀)).erase (i₀, j₀)).sup
      (fun x => ‖P.coeff x.1 * Q.coeff x.2‖₊ * ρ ^ (i₀ + j₀)) < gaussR ρ P * gaussR ρ Q :=
    (Finset.sup_lt_iff (mul_pos hgP hgQ)).2 hterm
  have hrest : ‖∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (i₀ + j₀)).erase (i₀, j₀), P.coeff x.1 * Q.coeff x.2‖₊ *
      ρ ^ (i₀ + j₀) < gaussR ρ P * gaussR ρ Q := by
    refine lt_of_le_of_lt ?_ hsup
    rw [← le_div_iff₀ hρk]
    apply IsUltrametricDist.nnnorm_sum_le_of_forall_le
    intro x hx
    rw [le_div_iff₀ hρk]
    exact Finset.le_sup (f := fun x => ‖P.coeff x.1 * Q.coeff x.2‖₊ * ρ ^ (i₀ + j₀)) hx
  have hmain : ‖P.coeff i₀ * Q.coeff j₀‖₊ * ρ ^ (i₀ + j₀) = gaussR ρ P * gaussR ρ Q := by
    rw [nnnorm_mul, pow_add, ← hi₀, ← hj₀]
    ring
  have h' : ‖∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (i₀ + j₀)).erase (i₀, j₀), P.coeff x.1 * Q.coeff x.2‖₊ *
      ρ ^ (i₀ + j₀) < ‖P.coeff i₀ * Q.coeff j₀‖₊ * ρ ^ (i₀ + j₀) := by
    rw [hmain]
    exact hrest
  have hlt := lt_of_mul_lt_mul_right h' zero_le
  have heq : ‖(P * Q).coeff (i₀ + j₀)‖₊ = ‖P.coeff i₀ * Q.coeff j₀‖₊ := by
    rw [hsplit, IsUltrametricDist.nnnorm_add_eq_max_of_nnnorm_ne_nnnorm hlt.ne', max_eq_left hlt.le]
  calc gaussR ρ P * gaussR ρ Q = ‖(P * Q).coeff (i₀ + j₀)‖₊ * ρ ^ (i₀ + j₀) := by rw [heq, hmain]
    _ ≤ gaussR ρ (P * Q) := gaussR_term_le ρ (P * Q) _

end

theorem gauss_norm_multiplicative : GaussMulRad := fun K _ _ ρ P Q hρ => le_antisymm (gaussR_mul_le ρ P Q) (le_gaussR_mul ρ hρ P Q)

end Formalism.GM
end

-- bundled from Formalism.MahlerMeasure.MahlerMeasureProofs.LevelDecomp
section
namespace Formalism.GM

open MvPolynomial Finset

section
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ}

theorem ld_biHom_of_euler [CharZero k] {a b : ℕ} {g : MvPolynomial σ k}
    (hW : ∑ c, X (w c) * pderiv (w c) g = (a : k) • g)
    (hE : ∑ c, X (e c) * pderiv (e c) g = (b : k) • g) : BiHom w e a b g := by
  classical
  unfold BiHom
  intro m hm
  rw [MvPolynomial.mem_support_iff] at hm
  have hterm : ∀ i : σ, AddMonoidAlgebra.coeff (X i * pderiv i g) m = (m i : k) * AddMonoidAlgebra.coeff g m := by
    intro i
    rw [MvPolynomial.coeff_X_mul']
    split_ifs with hs
    · have hmi : 1 ≤ m i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hs)
      have e1 : m - Finsupp.single i 1 + Finsupp.single i 1 = m :=
        tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hmi)
      have e2 : (((m - Finsupp.single i 1 : σ →₀ ℕ) i : ℕ) : k) + 1 = (m i : k) := by
        rw [Finsupp.tsub_apply, Finsupp.single_eq_same, ← Nat.cast_add_one, Nat.sub_add_cancel hmi]
      rw [MvPolynomial.coeff_pderiv, e1, e2, mul_comm]
    · simp at hs
      simp [hs]
  have key : ∀ (v : Fin r → σ) (n : ℕ), ∑ c, X (v c) * pderiv (v c) g = (n : k) • g → ∑ c, m (v c) = n := by
    intro v n hv
    have hcoef := congrArg (AddMonoidAlgebra.coeff · m) hv
    rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul, smul_eq_mul] at hcoef
    simp only [hterm] at hcoef
    rw [← Finset.sum_mul] at hcoef
    have hc := mul_right_cancel₀ hm hcoef
    exact_mod_cast hc
  exact ⟨key w a hW, key e b hE⟩

end

section fockSec
open Formalism.GM.M

variable {p : ℕ} [Fact p.Prime] {σ : Type}

end fockSec

section
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ}

end

section fockSec
open Formalism.GM.M

variable {p : ℕ} [Fact p.Prime] {σ : Type} {r : ℕ} {w e : Fin r → σ}

end fockSec

end Formalism.GM
end

-- bundled from Formalism.MahlerMeasure.MahlerMeasureProofs.MahlerK
section
namespace Formalism.GM

open Polynomial

theorem mahler_binomial_unit_ball : MahlerK := by
  intro p hp K _ _ h k t₀ hk m
  have : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[p] K).injective
  set P : ℚ[X] := Polynomial.C ((k.factorial : ℚ)⁻¹) *
    (descPochhammer ℚ k).comp (Polynomial.C ((p : ℚ) ^ h) * X + Polynomial.C (t₀ : ℚ)) with hP
  have hmap : P.map (Rat.castHom K) =
      (binK K k).comp (Polynomial.C ((p : K) ^ h) * X + Polynomial.C (t₀ : K)) := by
    rw [hP, binK, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_comp, descPochhammer_map,
      mul_comp, C_comp]
    simp
  rw [← hmap, Polynomial.coeff_map]
  have h1 := mahler_disc_bound p h k t₀ hp.out hk m
  rw [← hP] at h1
  have h2 : ((Rat.castHom K) (P.coeff m)) = algebraMap ℚ_[p] K ((P.coeff m : ℚ) : ℚ_[p]) := by
    rw [map_ratCast]; rfl
  rw [h2, norm_algebraMap', Padic.eq_padicNorm]
  exact_mod_cast h1

end Formalism.GM
end

-- bundled from Formalism.MahlerMeasure.MahlerMeasureProofs.SmithZp
section
namespace Formalism.GM

open Matrix

theorem smith_form_p_adic_integers : SmithZp := by
  intro p _ n M
  classical
  let y : (Fin n → ℤ_[p]) →ₗ[ℤ_[p]] (Fin n → ℤ_[p]) := Matrix.toLin' M
  obtain ⟨S⟩ := Formalism.A.smithExists ℤ_[p] (Fin n → ℤ_[p]) y
  have hfr : Module.finrank ℤ_[p] (Fin n → ℤ_[p]) = n := Module.finrank_fin_fun ℤ_[p]
  let e : Fin (Module.finrank ℤ_[p] (Fin n → ℤ_[p])) ≃ Fin n := finCongr hfr
  let b := S.b.reindex e
  let b' := S.b'.reindex e
  let a : Fin n → ℤ_[p] := S.a ∘ e.symm
  have hy : ∀ j, M.mulVec (b j) = a j • b' j := by
    intro j
    have := S.hy (e.symm j)
    simpa [b, b', a, y, Matrix.toLin'_apply] using this
  let std := Pi.basisFun ℤ_[p] (Fin n)
  let Q := std.toMatrix b
  let P := std.toMatrix b'
  let V := b.toMatrix std
  have hQV : Q * V = 1 := Module.Basis.toMatrix_mul_toMatrix_flip std b
  have hPW : P * (b'.toMatrix std) = 1 := Module.Basis.toMatrix_mul_toMatrix_flip std b'
  have hMQ : M * Q = P * Matrix.diagonal a := by
    ext i j
    have h1 := congrFun (hy j) i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h1
    rw [Matrix.mul_diagonal, Matrix.mul_apply]
    simp only [Q, P, std, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
    rw [h1]; ring
  refine ⟨P, V, a, Matrix.isUnit_det_of_right_inverse hPW, Matrix.isUnit_det_of_left_inverse hQV, ?_⟩
  calc M = M * (Q * V) := by rw [hQV, Matrix.mul_one]
    _ = (M * Q) * V := by rw [Matrix.mul_assoc]
    _ = P * Matrix.diagonal a * V := by rw [hMQ]

end Formalism.GM
end

