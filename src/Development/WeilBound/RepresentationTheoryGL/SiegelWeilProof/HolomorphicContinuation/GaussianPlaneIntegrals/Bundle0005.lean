module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.Bundle0004

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.CycFFT
section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.FFTSteps.CycF

variable {m n : ℕ} {ε : Fin m → Bool}

theorem coeff_inv (v : Matrix (Rw ε true) (Rw ε true) ℂ) (Q : PX m n) (hQ : act (blk ε true v) Q = Q)
    (μ : VV (Rw ε false) n →₀ ℕ) : sub v (v.map star) ((Th ε Q).coeff μ) = (Th ε Q).coeff μ := by
  classical
  have h1 : act (blk ε true v) Q = ∑ ν ∈ (Th ε Q).support,
      emb ε true (sub v (v.map star) ((Th ε Q).coeff ν)) * emb ε false (monomial ν 1) := by
    conv_lhs => rw [decomp (ε := ε) Q]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl (fun ν _ => ?_)
    rw [map_mul]
    congr 1
    · exact DFunLike.congr_fun (act_emb_same true v) _
    · exact DFunLike.congr_fun (act_emb_other true false (by decide) v) _
  rw [hQ] at h1
  have h2 := congrArg (fun P => AddMonoidAlgebra.coeff (Th ε P) μ) h1
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, th_prod, coeff_sum_monomial] at h2
  by_cases hμ : μ ∈ (Th ε Q).support
  · rw [if_pos hμ] at h2
    exact h2.symm
  · have : AddMonoidAlgebra.coeff (Th ε Q) μ = 0 := notMem_support_iff.1 hμ
    rw [this, map_zero]

end PositivityTheory.Rg.Sw.FFTSteps.CycF

namespace PositivityTheory.Rg.Sw.FFTSteps

open CycF

theorem cycFFT : CycFFT := by
  classical
  intro hF m n ε Q hQ
  have hact : ∀ u : Matrix (Fin m) (Fin m) ℂ, u ∈ Matrix.unitaryGroup (Fin m) ℂ → (∀ a b, ε a ≠ ε b → u a b = 0) →
      act (n := n) u Q = Q := hQ
  have hc : ∀ μ, (Th ε Q).coeff μ ∈ pairAlg (Rw ε true) (Fin n) (Fin n) := fun μ =>
    hF _ _ _ ((Th ε Q).coeff μ) (fun u hu => coeff_inv u Q (hact _ (blk_unitary true u hu) (blk_block true u)) μ)
  obtain ⟨bs, hbs, hspan, hli⟩ := exists_linearIndependent ℂ
    ((fun μ => (Th ε Q).coeff μ) '' ((Th ε Q).support : Set _))
  have hfin : bs.Finite := (((Th ε Q).support.finite_toSet).image _).subset hbs
  letI : Fintype bs := hfin.fintype
  have hmem : ∀ μ ∈ (Th ε Q).support, (Th ε Q).coeff μ ∈
      Submodule.span ℂ (Set.range (fun j : bs => (j : PV (Rw ε true) (Fin n) (Fin n)))) := by
    intro μ hμ
    rw [Subtype.range_coe, hspan]
    exact Submodule.subset_span ⟨μ, hμ, rfl⟩
  have hrep : ∀ μ : (Th ε Q).support, ∃ a : bs → ℂ,
      ∑ j, a j • (j : PV (Rw ε true) (Fin n) (Fin n)) = (Th ε Q).coeff μ.1 := fun μ =>
    (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hmem μ.1 μ.2)
  choose a ha using hrep
  let r : bs → PV (Rw ε false) (Fin n) (Fin n) := fun j => ∑ μ : (Th ε Q).support, a μ j • monomial μ.1 1
  have hQ' : Q = ∑ j : bs, emb ε true (j : PV (Rw ε true) (Fin n) (Fin n)) * emb ε false (r j) := by
    conv_lhs => rw [decomp (ε := ε) Q]
    rw [← Finset.sum_coe_sort (Th ε Q).support]
    simp_rw [← ha]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [r, map_sum, map_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
    exact Finset.sum_comm
  have hr : ∀ j, r j ∈ pairAlg (Rw ε false) (Fin n) (Fin n) := by
    intro j
    refine hF _ _ _ (r j) (fun u hu => ?_)
    have h1 := hact _ (blk_unitary false u hu) (blk_block false u)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hQ', map_sum] at h1
    have h2 : ∀ i : bs, act (blk ε false u) (emb ε true (i : PV (Rw ε true) (Fin n) (Fin n)) * emb ε false (r i)) =
        emb ε true (i : PV (Rw ε true) (Fin n) (Fin n)) * emb ε false (sub u (u.map star) (r i)) := by
      intro i
      rw [map_mul]
      congr 1
      · exact DFunLike.congr_fun (act_emb_other false true (by decide) u) _
      · exact DFunLike.congr_fun (act_emb_same false u) _
    simp_rw [h2] at h1
    have h3 : ∑ i : bs, emb ε true (i : PV (Rw ε true) (Fin n) (Fin n)) *
        emb ε false (sub u (u.map star) (r i) - r i) = 0 := by
      simp only [map_sub, mul_sub, Finset.sum_sub_distrib]
      rw [h1, sub_self]
    have := indep (fun i : bs => (i : PV (Rw ε true) (Fin n) (Fin n))) hli _ h3 j
    exact sub_eq_zero.1 this
  rw [hQ']
  refine Subalgebra.sum_mem _ (fun j _ => Subalgebra.mul_mem _ ?_ ?_)
  · obtain ⟨μ, hμ, hj⟩ := hbs j.2
    apply emb_pairAlg true
    rw [← hj]
    exact hc μ
  · exact emb_pairAlg false (hr j)

end PositivityTheory.Rg.Sw.FFTSteps
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.Imports
section
noncomputable section

open MeasureTheory MvPolynomial Module
open scoped ComplexConjugate ComplexOrder

namespace PositivityTheory.Rg.Sw.FFTSteps

open PosProof

private theorem gip_monomial_self_eq_prod_jr {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
    (m : Sg ι A B →₀ ℕ) :
    gip (monomial m (1 : ℂ)) (monomial m (1 : ℂ)) = ((∏ s : Sg ι A B, jr (m s) : ℝ) : ℂ) := by
  rw [← integral_mon_self m]
  unfold gip
  congr 1
  funext z
  rw [mon_prod]
  have h1 : (eval z) (monomial m (1 : ℂ)) = ∏ s : Sg ι A B, z s ^ m s := by
    rw [eval_monomial, one_mul, Finsupp.prod_fintype]
    intro i
    simp
  rw [h1, star_prod, ← Finset.prod_mul_distrib, Complex.ofReal_sum, ← Finset.sum_neg_distrib,
    Complex.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [hk_diag, star_pow, ← mul_pow]
  have h2 : z s * star (z s) = ((‖z s‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h2]
  push_cast
  ring_nf

private theorem pos_lemma {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
    (d : ι → ℝ) (m : Sg ι A B →₀ ℕ) :
    sub 1 (Matrix.diagonal fun i => (d i : ℂ)) (monomial m (1 : ℂ)) =
      C ((∏ s : Sg ι A B, kap d s ^ m s : ℝ) : ℂ) * monomial m (1 : ℂ) := by
  apply MvPolynomial.funext
  intro z
  rw [PosProof.eval_sub, Phi_diag, eval_mul, eval_C, eval_monomial, eval_monomial, one_mul, one_mul,
    Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp)]
  push_cast
  simp only [mul_pow, Finset.prod_mul_distrib]

private theorem lam_eq_prod_kap_pow {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
    (d : ι → ℝ) (m : Sg ι A B →₀ ℕ) :
    lam d m = ∏ s : Sg ι A B, kap d s ^ m s := by
  classical
  have hP : (0 : ℝ) < ∏ s : Sg ι A B, jr (m s) := Finset.prod_pos fun s _ => jr_pos _
  have h := gip_diag (A := A) (B := B) d (monomial m (1 : ℂ))
  rw [pos_lemma, support_monomial, if_neg one_ne_zero, Finset.sum_singleton, coeff_monomial, if_pos rfl,
    Complex.normSq_one, one_mul] at h
  have h3 : gip (C ((∏ s : Sg ι A B, kap d s ^ m s : ℝ) : ℂ) * monomial m (1 : ℂ)) (monomial m (1 : ℂ)) =
      ((∏ s : Sg ι A B, kap d s ^ m s : ℝ) : ℂ) * ((∏ s : Sg ι A B, jr (m s) : ℝ) : ℂ) := by
    rw [← gip_monomial_self_eq_prod_jr]
    unfold gip
    rw [← integral_const_mul]
    congr 1
    funext z
    rw [eval_mul, eval_C]
    ring
  rw [h3] at h
  have h4 : (∏ s : Sg ι A B, kap d s ^ m s) * (∏ s : Sg ι A B, jr (m s)) =
      lam d m * ∏ s : Sg ι A B, jr (m s) := by
    exact_mod_cast h
  exact (mul_right_cancel₀ hP.ne' h4).symm

private theorem gip_sub_eq_of_unitary_conj_diag {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
    (M U D : Matrix ι ι ℂ) (hU1 : star U * U = 1) (hU2 : U * star U = 1) (hMU : M * U = U * D)
    (f : PV ι A B) :
    gip (sub 1 M f) f = gip (sub 1 D (sub 1 U f)) (sub 1 U f) := by
  have hcont : Continuous fun z : Sg ι A B → ℂ =>
      (eval z) (sub 1 M f) * star ((eval z) f) * Complex.exp (-↑(∑ s : Sg ι A B, ‖z s‖ ^ 2)) :=
    ((continuous_eval _).mul (continuous_star.comp (continuous_eval _))).mul
      (Complex.continuous_exp.comp (Complex.continuous_ofReal.comp
        (continuous_finsetSum _ fun s _ => (continuous_norm.comp (continuous_apply s)).pow 2)).neg)
  unfold gip
  rw [integral_Phi U hU1 hU2 _ hcont]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [PosProof.eval_sub]
  rw [← Phi_mul, ← Phi_mul, hMU, norm_Phi U hU1]

theorem pos : Pos := by
  intro ι A B _ _ _ _ M hM f
  have hH := hM.isHermitian
  have hMe : M = (hH.eigenvectorUnitary : Matrix ι ι ℂ) *
      Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) * star (hH.eigenvectorUnitary : Matrix ι ι ℂ) := by
    conv_lhs => rw [hH.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    rfl
  have hU1 : star (hH.eigenvectorUnitary : Matrix ι ι ℂ) * (hH.eigenvectorUnitary : Matrix ι ι ℂ) = 1 :=
    Unitary.coe_star_mul_self _
  have hU2 : (hH.eigenvectorUnitary : Matrix ι ι ℂ) * star (hH.eigenvectorUnitary : Matrix ι ι ℂ) = 1 := by
    simpa [Unitary.coe_star] using Unitary.coe_mul_star_self hH.eigenvectorUnitary
  have hMU : M * (hH.eigenvectorUnitary : Matrix ι ι ℂ) =
      (hH.eigenvectorUnitary : Matrix ι ι ℂ) * Matrix.diagonal (fun i => (hH.eigenvalues i : ℂ)) := by
    have h := congrArg (· * (hH.eigenvectorUnitary : Matrix ι ι ℂ)) hMe
    rw [h, Matrix.mul_assoc (_ * _), hU1, Matrix.mul_one]
  have hkap : ∀ s : Sg ι A B, 0 ≤ kap hH.eigenvalues s := by
    intro s
    rcases s with s | s
    · simp [kap]
    · simp only [kap, Sum.elim_inr]
      exact hM.eigenvalues_nonneg _
  rw [gip_sub_eq_of_unitary_conj_diag M _ _ hU1 hU2 hMU f, gip_diag]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨?_, trivial, ?_⟩
  · refine Finset.sum_nonneg fun m _ => mul_nonneg (mul_nonneg (Complex.normSq_nonneg _) ?_)
      (Finset.prod_nonneg fun s _ => (jr_pos _).le)
    rw [lam_eq_prod_kap_pow]
    exact Finset.prod_nonneg fun s _ => pow_nonneg (hkap s) _
  · intro hPD hf
    have hkap' : ∀ s : Sg ι A B, 0 < kap hH.eigenvalues s := by
      intro s
      rcases s with s | s
      · simp [kap]
      · simp only [kap, Sum.elim_inr]
        exact hPD.eigenvalues_pos _
    have hinv : sub 1 (star (hH.eigenvectorUnitary : Matrix ι ι ℂ))
        (sub 1 (hH.eigenvectorUnitary : Matrix ι ι ℂ) f) = f := by
      apply MvPolynomial.funext
      intro z
      rw [PosProof.eval_sub, PosProof.eval_sub, ← Phi_mul, hU2, Phi_one]
    have hg : sub 1 (hH.eigenvectorUnitary : Matrix ι ι ℂ) f ≠ 0 := by
      intro hg
      apply hf
      rw [← hinv, hg, map_zero]
    refine Finset.sum_pos (fun m hm => mul_pos (mul_pos (Complex.normSq_pos.2 (mem_support_iff.1 hm)) ?_)
      (Finset.prod_pos fun s _ => jr_pos _)) ?_
    · rw [lam_eq_prod_kap_pow]
      exact Finset.prod_pos fun s _ => pow_pos (hkap' s) _
    · exact Finset.nonempty_iff_ne_empty.2 (by rwa [Ne, MvPolynomial.support_eq_empty])

end PositivityTheory.Rg.Sw.FFTSteps
end
end

