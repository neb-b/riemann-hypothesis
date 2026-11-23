module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.QuotIntegrableIffCutoff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0086

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.KillingFormDiffCartanInvolution
section
open Matrix MeasureTheory Topology
open scoped Kronecker ContDiff

noncomputable section

namespace GlobalTheory.Tw

section Alg
variable {a b : ℕ} {R : Type} [CommRing R] [StarRing R]

end Alg

variable {a b : ℕ}

theorem isCompact_unitary_GL (n : ℕ) : IsCompact {k : GL (Fin n) ℂ | k.val ∈ unitaryGroup (Fin n) ℂ} := by
  have hU : IsCompact (unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
    have hcl : IsClosed (unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
      have e : (unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) =
          (fun A : Matrix (Fin n) (Fin n) ℂ => A * star A) ⁻¹' {1} := by
        ext A; exact Matrix.mem_unitaryGroup_iff
      rw [e]
      exact isClosed_singleton.preimage (continuous_id.mul continuous_star)
    have hbd : (unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ)) ⊆
        Set.univ.pi fun _ => Set.univ.pi fun _ => Metric.closedBall (0 : ℂ) 1 := by
      intro A hA i _ j _
      have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.1 hA) i) i
      rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
      simp only [Matrix.star_apply, Complex.star_def, Complex.mul_conj] at h
      have h2 : ∑ k, Complex.normSq (A i k) = 1 := by exact_mod_cast h
      have h3 : Complex.normSq (A i j) ≤ 1 :=
        h2 ▸ Finset.single_le_sum (fun k _ => Complex.normSq_nonneg (A i k)) (Finset.mem_univ j)
      rw [Metric.mem_closedBall, dist_zero_right]
      rw [Complex.normSq_eq_norm_sq] at h3
      nlinarith [norm_nonneg (A i j)]
    exact (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1).of_isClosed_subset hcl hbd
  have : CompactSpace (unitaryGroup (Fin n) ℂ) := isCompact_iff_compactSpace.1 hU
  let φ : unitaryGroup (Fin n) ℂ → GL (Fin n) ℂ := fun u =>
    ⟨u.1, star u.1, Unitary.mul_star_self_of_mem u.2, Unitary.star_mul_self_of_mem u.2⟩
  have hφ : Continuous φ :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, continuous_star.comp continuous_subtype_val⟩
  have hr : Set.range φ = {k : GL (Fin n) ℂ | k.val ∈ unitaryGroup (Fin n) ℂ} := by
    ext k
    constructor
    · rintro ⟨u, rfl⟩
      exact u.2
    · intro hk
      exact ⟨⟨k.val, hk⟩, Units.ext rfl⟩
  rw [← hr]
  exact isCompact_range hφ

end GlobalTheory.Tw
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ValIrreducible
section
noncomputable section

namespace GlobalTheory.UnitLemma.Basic

variable {K : UQ} (B : InvAlg K)

variable {K : _root_.GlobalTheory.UnitLemma.UQ} (B : _root_.GlobalTheory.UnitLemma.InvAlg K) in
private theorem sigma_smul_eq_conj_smul (e : K.E) (v : B.A) : B.σ (e • v) = K.c e • B.σ v := by
  rw [Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]


variable {K : _root_.GlobalTheory.UnitLemma.UQ} (B : _root_.GlobalTheory.UnitLemma.InvAlg K) in
theorem _root_.GlobalTheory.UnitLemma.Basic.trace_sigma (u : B.A) :
    Algebra.trace K.E B.A (B.σ u) = K.c (Algebra.trace K.E B.A u) := by
  classical
  set b := Module.finBasis K.E B.A
  let φ : B.A ≃ₗ[K.E] (Fin (Module.finrank K.E B.A) → K.E) :=
    { toFun := fun v i => K.c (b.repr (B.σ v) i)
      map_add' := fun v w => by ext i; simp
      map_smul' := fun e v => by ext i; simp [sigma_smul_eq_conj_smul, K.c_c]
      invFun := fun f => B.σ (∑ i, K.c (f i) • b i)
      left_inv := fun v => by
        simp only [K.c_c, b.sum_repr, B.σ_σ]
      right_inv := fun f => by
        ext i
        simp [B.σ_σ, Finsupp.single_apply, K.c_c] }
  let b' := Module.Basis.ofEquivFun φ
  have hb' (j) : b' j = B.σ (b j) := by
    simp [b', Module.Basis.coe_ofEquivFun, φ, Pi.single_apply, apply_ite B.σ]
  have hrepr (w : B.A) (i) : b'.repr w i = K.c (b.repr (B.σ w) i) := by
    simp [b', φ]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Algebra.trace_eq_matrix_trace b' (B.σ u), Algebra.trace_eq_matrix_trace b u,
    Matrix.trace, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.diag, Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply,
    Algebra.coe_lmul_eq_mul, LinearMap.mul_apply', hb', hrepr, ← map_mul, B.σ_σ]


variable {K : _root_.GlobalTheory.UnitLemma.UQ} (B : _root_.GlobalTheory.UnitLemma.InvAlg K) in
theorem _root_.GlobalTheory.UnitLemma.Basic.herm_smul_left (x y z : B.A) (e : K.E) :
    B.herm x (e • y) z = e * B.herm x y z := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.herm
  rw [mul_smul_comm, smul_mul_assoc, map_smul, smul_eq_mul]


variable {K : _root_.GlobalTheory.UnitLemma.UQ} (B : _root_.GlobalTheory.UnitLemma.InvAlg K) in
theorem _root_.GlobalTheory.UnitLemma.Basic.herm_smul_right (x y z : B.A) (e : K.E) :
    B.herm x y (e • z) = K.c e * B.herm x y z := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.herm
  rw [sigma_smul_eq_conj_smul, mul_smul_comm, map_smul, smul_eq_mul]


variable {K : _root_.GlobalTheory.UnitLemma.UQ} (B : _root_.GlobalTheory.UnitLemma.InvAlg K) in
theorem _root_.GlobalTheory.UnitLemma.Basic.herm_symm (x : B.A) (hx : B.σ x = x) (y z : B.A) :
    B.herm x z y = K.c (B.herm x y z) := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.herm
  rw [← _root_.GlobalTheory.UnitLemma.Basic.trace_sigma, map_mul B.σ, map_mul B.σ, hx, B.σ_σ]
  congr 1
  ring


variable {K : _root_.GlobalTheory.UnitLemma.UQ} (B : _root_.GlobalTheory.UnitLemma.InvAlg K) in
theorem _root_.GlobalTheory.UnitLemma.Basic.herm_mul_left (x u y z : B.A) :
    B.herm x (u * y) z = B.herm x y (B.σ u * z) := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.herm
  rw [map_mul B.σ, B.σ_σ]
  congr 1
  ring


variable {K : _root_.GlobalTheory.UnitLemma.UQ} (B : _root_.GlobalTheory.UnitLemma.InvAlg K) in
theorem _root_.GlobalTheory.UnitLemma.Basic.herm_norm (x u y z : B.A) :
    B.herm (x * (u * B.σ u)) y z = B.herm x (u * y) (u * z) := by
  unfold _root_.GlobalTheory.UnitLemma.InvAlg.herm
  rw [map_mul B.σ]
  congr 1
  ring

end GlobalTheory.UnitLemma.Basic
end
end

