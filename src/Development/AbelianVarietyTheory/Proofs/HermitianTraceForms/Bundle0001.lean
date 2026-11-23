module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.DifferentiableToContinuousLinearMap
section
namespace GlobalTheory

open Module

section Defs

variable {R M : Type*} [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]

def isoTransvection (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0) (b : R) : M ≃ₗ[R] M :=
  LinearEquiv.transvection (f := b • h.flip x) (v := x) (by simp [hx])

namespace isoTransvection

variable (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0)

theorem apply (b : R) (v : M) : isoTransvection h x hx b v = v + (b * h v x) • x := rfl

end isoTransvection

namespace isoTransvection

variable (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0)

variable {h}

variable (h)

section Lattice

variable {R₀ : Type*} [CommRing R₀] [Algebra R₀ R] [Module R₀ M] [IsScalarTower R₀ R M]

end Lattice

end isoTransvection

end Defs

section Complex

namespace isoTransvection

variable {W : Type*} [AddCommGroup W] [Module ℂ W] {h : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ} (x : W)
  (hx : h x x = 0)

end isoTransvection

namespace isoTransvection

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] (h : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ) (x : W)
  (hx : h x x = 0)

end isoTransvection

end Complex

section Example

private noncomputable def hyp : (ℂ × ℂ) →ₗ[ℂ] (ℂ × ℂ) →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun u v => u.1 * star v.2 + u.2 * star v.1)
    (by intros; simp; ring) (by intros; simp; ring) (by intros; simp; ring)
    (by intros; simp; ring)

end Example

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.FormPerpVectorMemOfIntegral
section
open scoped BigOperators Nat

namespace GlobalTheory

section Covector

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]

def pairingMatrix (ε : ι → Module.Dual R M) (e' : ι → M) : Matrix ι ι R :=
  Matrix.of fun a' a => ε a (e' a')

def perpVector (ε : ι → Module.Dual R M) (e' : ι → M) (g : M) : M :=
  (pairingMatrix ε e').det • g
    - ∑ a, ∑ a', ((pairingMatrix ε e').adjugate a a' * ε a g) • e' a'


section Integral

variable {A : Type*} [CommRing A] [Algebra A R]

end Integral

end Covector

section Size

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

private theorem seminorm_sum_le {G κ : Type*} [AddCommGroup G] (ν : AddGroupSeminorm G)
    (s : Finset κ) (x : κ → G) {C : ℝ} (hx : ∀ k ∈ s, ν (x k) ≤ C) :
    ν (∑ k ∈ s, x k) ≤ s.card * C := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.card_insert_of_notMem hk]
    have h1 := map_add_le_add ν (x k) (∑ k ∈ s, x k)
    have h2 := hx k (Finset.mem_insert_self _ _)
    have h3 := ih fun j hj => hx j (Finset.mem_insert_of_mem hj)
    push_cast
    linarith

private theorem ringSeminorm_prod_le {κ : Type*} (ν : RingSeminorm R) (h1 : ν 1 ≤ 1)
    (s : Finset κ) (x : κ → R) {C : ℝ} (hx : ∀ k ∈ s, ν (x k) ≤ C) :
    ν (∏ k ∈ s, x k) ≤ C ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h1
  | insert k s hk ih =>
    rw [Finset.prod_insert hk, Finset.card_insert_of_notMem hk, pow_succ']
    have h2 := hx k (Finset.mem_insert_self _ _)
    have h3 := ih fun j hj => hx j (Finset.mem_insert_of_mem hj)
    exact (map_mul_le_mul ν _ _).trans
      (mul_le_mul h2 h3 (apply_nonneg ν _) ((apply_nonneg ν _).trans h2))

theorem ringSeminorm_det_le {ι : Type*} [Fintype ι] [DecidableEq ι] (ν : RingSeminorm R)
    (h1 : ν 1 ≤ 1) (H : Matrix ι ι R) {C : ℝ} (hH : ∀ i j, ν (H i j) ≤ C) :
    ν H.det ≤ (Fintype.card ι)! * C ^ Fintype.card ι := by
  rw [Matrix.det_apply]
  have := seminorm_sum_le ν.toAddGroupSeminorm Finset.univ
    (fun σ : Equiv.Perm ι => Equiv.Perm.sign σ • ∏ i, H (σ i) i) (C := C ^ Fintype.card ι) (by
      intro σ _
      have h := ringSeminorm_prod_le ν h1 Finset.univ (fun i => H (σ i) i) fun i _ => hH _ _
      rw [Finset.card_univ] at h
      change ν _ ≤ _
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
      · rw [hs, one_smul]; exact h
      · rw [hs, Units.neg_smul, one_smul, map_neg_eq_map]; exact h)
  rwa [Finset.card_univ, Fintype.card_perm] at this

theorem ringSeminorm_adjugate_le {n : ℕ} (ν : RingSeminorm R) (h1 : ν 1 ≤ 1)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) R) {C : ℝ} (hH : ∀ i j, ν (H i j) ≤ C)
    (i j : Fin (n + 1)) : ν (H.adjugate i j) ≤ n ! * C ^ n := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  have h := ringSeminorm_det_le ν h1 (H.submatrix j.succAbove i.succAbove) (C := C)
    fun _ _ => hH _ _
  rw [Fintype.card_fin] at h
  rcases neg_one_pow_eq_or R ((j : ℕ) + i) with hs | hs
  · rw [hs, one_mul]; exact h
  · rw [hs, neg_one_mul, map_neg_eq_map]; exact h

theorem seminorm_perpVector_le {p : ℕ} (ν : RingSeminorm R) (h1 : ν 1 ≤ 1)
    (μ : AddGroupSeminorm M) (hsmul : ∀ (x : R) (v : M), μ (x • v) ≤ ν x * μ v)
    (ε : Fin p → Module.Dual R M) (e' : Fin p → M) (g : M) {C r : ℝ}
    (he : ∀ a a', ν (ε a (e' a')) ≤ C) (hg : ∀ a, ν (ε a g) ≤ C)
    (he' : ∀ a, μ (e' a) ≤ r) (hgr : μ g ≤ r) :
    μ (perpVector ε e' g) ≤ (p + 1)! * C ^ p * r := by
  have hdet := ringSeminorm_det_le ν h1 (pairingMatrix ε e') (C := C) fun i j => he j i
  rw [Fintype.card_fin] at hdet
  have hA : μ ((pairingMatrix ε e').det • g) ≤ p ! * C ^ p * r :=
    (hsmul _ _).trans (mul_le_mul hdet hgr (apply_nonneg μ _) ((apply_nonneg ν _).trans hdet))
  have hB : μ (∑ a, ∑ a', ((pairingMatrix ε e').adjugate a a' * ε a g) • e' a')
      ≤ p * (p ! * C ^ p * r) := by
    cases p with
    | zero => simp
    | succ n =>
      have h := seminorm_sum_le μ Finset.univ
        (fun a => ∑ a', ((pairingMatrix ε e').adjugate a a' * ε a g) • e' a')
        (C := ((n + 1 : ℕ) : ℝ) * (n ! * C ^ n * C * r)) (by
          intro a _
          have h' := seminorm_sum_le μ Finset.univ
            (fun a' => ((pairingMatrix ε e').adjugate a a' * ε a g) • e' a')
            (C := n ! * C ^ n * C * r) (by
              intro a' _
              have hadj := ringSeminorm_adjugate_le ν h1 (pairingMatrix ε e') (C := C)
                (fun i j => he j i) a a'
              have hm : ν ((pairingMatrix ε e').adjugate a a' * ε a g) ≤ n ! * C ^ n * C :=
                (map_mul_le_mul ν _ _).trans
                  (mul_le_mul hadj (hg a) (apply_nonneg ν _) ((apply_nonneg ν _).trans hadj))
              exact (hsmul _ _).trans
                (mul_le_mul hm (he' a') (apply_nonneg μ _) ((apply_nonneg ν _).trans hm)))
          rwa [Finset.card_univ, Fintype.card_fin] at h')
      rw [Finset.card_univ, Fintype.card_fin] at h
      refine h.trans (le_of_eq ?_)
      rw [Nat.factorial_succ]; push_cast; ring
  have hsub := map_sub_le_add μ ((pairingMatrix ε e').det • g)
    (∑ a, ∑ a', ((pairingMatrix ε e').adjugate a a' * ε a g) • e' a')
  rw [perpVector, Nat.factorial_succ]
  push_cast
  linarith

end Size

section Degree

open MvPolynomial

variable {S τ : Type*} [CommRing S]

end Degree

section Form

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
  {σ : R →+* R}


end Form

section InnerProduct

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℂ V]

end InnerProduct

section Places

variable {R M T : Type*} [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]

end Places

end GlobalTheory
end

