module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOneOfPowEqOneOfCharpoly
section
open Polynomial

namespace GlobalTheory.FinOrd

theorem eq_one_of_pow_eq_one_of_charpoly (K : Type) [Field K] [CharZero K] (N : ℕ)
    (M : Matrix (Fin N) (Fin N) K) (h : ∃ m : ℕ, 0 < m ∧ M ^ m = 1)
    (hc : M.charpoly = (X - 1) ^ N) : M = 1 := by
  obtain ⟨m, hm, hM⟩ := h
  have hpr : Prime (X - 1 : K[X]) := by simpa using prime_X_sub_C (1 : K)

  have hsep : (X ^ m - 1 : K[X]).Separable := by
    simpa using separable_X_pow_sub_C (1 : K) (Nat.cast_ne_zero.2 hm.ne') one_ne_zero
  have h1 : minpoly K M ∣ X ^ m - 1 := minpoly.dvd_iff.2 (by simp [hM])

  have h2 : minpoly K M ∣ (X - 1) ^ N := by
    rw [← hc]; exact minpoly.dvd_iff.2 (Matrix.aeval_self_charpoly M)
  obtain ⟨i, -, hi⟩ := (dvd_prime_pow hpr N).1 h2

  have hsi : ((X - 1 : K[X]) ^ i).Separable := hsep.of_dvd (hi.symm.dvd.trans h1)
  have hle : minpoly K M ∣ X - 1 := by
    rcases hsi.of_pow' with hu | ⟨-, rfl⟩ | rfl
    · exact absurd hu hpr.not_unit
    · simpa using hi.dvd
    · exact hi.dvd.trans (by simp)
  have h0 : Polynomial.aeval M (X - 1 : K[X]) = 0 := minpoly.dvd_iff.1 hle
  simpa [sub_eq_zero] using h0

end GlobalTheory.FinOrd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfEvalNatCastAdd
section
namespace GlobalTheory.EvalNatCastZero

open Polynomial

theorem eq_zero_of_eval_natCast_add {R : Type} [CommRing R]
    (hR : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R)) (n : ℕ) (F : Polynomial R) (hF : F.natDegree ≤ n)
    (m : ℕ) (h : ∀ k : ℕ, Polynomial.eval ((m + k : ℕ) : R) F = 0) : F = 0 := by
  nontriviality R
  induction n generalizing F m with
  | zero =>
    have h0 := h 0
    rw [eq_C_of_natDegree_le_zero hF] at h0 ⊢
    rw [eval_C] at h0
    rw [h0, C_0]
  | succ n ih =>
    have hroot : F.IsRoot (m : R) := by simpa using h 0
    have hfac : (X - C (m : R)) * (F /ₘ (X - C (m : R))) = F :=
      mul_divByMonic_eq_iff_isRoot.2 hroot
    have hdeg : (F /ₘ (X - C (m : R))).natDegree ≤ n := by
      rw [natDegree_divByMonic F (monic_X_sub_C _), natDegree_X_sub_C]
      omega
    have hG : F /ₘ (X - C (m : R)) = 0 := by
      refine ih _ hdeg (m + 1) fun k => ?_
      have h1 := h (k + 1)
      rw [← hfac, eval_mul, eval_sub, eval_X, eval_C] at h1
      have e1 : ((m + (k + 1) : ℕ) : R) - (m : R) = ((k + 1 : ℕ) : R) := by push_cast; ring
      have e2 : m + 1 + k = m + (k + 1) := by ring
      rw [e1] at h1
      rw [e2]
      exact (hR (k + 1) (Nat.succ_ne_zero k)).mul_right_eq_zero.1 h1
    rw [← hfac, hG, mul_zero]

end GlobalTheory.EvalNatCastZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfSumMulEmbeddingsEqZero
section
namespace GlobalTheory


open Module in
theorem eq_zero_of_sum_mul_embeddings_eq_zero (F Ω L : Type) [Field F] [CharZero F] [Field Ω]
    [IsAlgClosed Ω] [Algebra F Ω] [Field L] [Algebra F L] [FiniteDimensional F L] (m : ℕ)
    (e : Fin m → Ω) (he : LinearIndependent F e) (_halg : ∀ t, IsAlgebraic F (e t))
    (a : Fin m → L) (h : ∀ σ : L →ₐ[F] Ω, ∑ t, e t * σ (a t) = 0) : a = 0 := by
  classical
  let b := Module.finBasis F L
  let ε : Fin (Module.finrank F L) ≃ (L →ₐ[F] Ω) :=
    Fintype.equivOfCardEq (by rw [AlgHom.card F L Ω, Fintype.card_fin])
  let E := Algebra.embeddingsMatrixReindex F Ω b ε
  have hE : E.det ≠ 0 := by
    intro h0
    have h1 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two F Ω b ε
    rw [show (Algebra.embeddingsMatrixReindex F Ω b ε).det = 0 from h0] at h1
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h1
    exact Algebra.discr_not_zero_of_basis F b ((map_eq_zero _).mp h1)
  have hEa : ∀ i k, E i k = ε k (b i) := by
    intro i k
    simp [E, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix]
  let v : Fin (Module.finrank F L) → Ω := fun i => ∑ t, (b.repr (a t) i) • e t
  have hv : Matrix.vecMul v E = 0 := by
    funext k
    rw [Matrix.vecMul, dotProduct]
    simp only [Pi.zero_apply, hEa, v]
    have hk := h (ε k)
    rw [← hk]
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [← b.sum_repr (a t), map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, Algebra.smul_def, Algebra.smul_def]
    ring
  have hv0 : v = 0 := Matrix.eq_zero_of_vecMul_eq_zero hE hv
  have hc : ∀ t i, b.repr (a t) i = 0 := by
    intro t i
    have := congrFun hv0 i
    exact (Fintype.linearIndependent_iff.mp he) (fun t => b.repr (a t) i) this t
  funext t
  rw [Pi.zero_apply, ← b.sum_repr (a t)]
  simp [hc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedFrameOfIsotropicColumns
section
namespace GlobalTheory

open Matrix

theorem exists_adapted_frame_of_isotropic_columns :
    ∀ (E : Type) [Field E] (r : ℕ) (Y : Submodule E ((Fin r → E) × (Fin r → E))),
      Module.finrank E Y = r →
      ∀ (C : Matrix (Fin r) (Fin r) E × Matrix (Fin r) (Fin r) E),
        Submodule.span E (Set.range fun j => ((fun a => C.1 a j), (fun a => C.2 a j))) = Y →
        ∀ (s : ℕ) (I : Matrix (Fin r) (Fin s) E), LinearIndependent E I.transpose →
          (∀ j, ((fun a => I a j), (0 : Fin r → E)) ∈ Y) →
          ∃ (t : ℕ) (J : Matrix (Fin r) (Fin s) E) (K : Matrix (Fin r) (Fin t) E)
            (L : Matrix (Fin s) (Fin r) E) (M : Matrix (Fin t) (Fin r) E),
            C.1 * J = I ∧ C.2 * J = 0 ∧ L * J = 1 ∧ L * K = 0 ∧ M * J = 0 ∧ M * K = 1 ∧
              J * L + K * M = 1 := by
  intro E _ r Y _ C hspan s I hI hmem

  have hc : ∀ j, ∃ c : Fin r → E,
      ∑ k, c k • ((fun a => C.1 a k), (fun a => C.2 a k)) = ((fun a => I a j), (0 : Fin r → E)) := by
    intro j
    have := hmem j
    rw [← hspan] at this
    exact (Submodule.mem_span_range_iff_exists_fun E).mp this
  choose c hc using hc
  let J : Matrix (Fin r) (Fin s) E := Matrix.of fun k j => c j k
  have h1 : C.1 * J = I := by
    ext a j
    have := congrFun (congrArg Prod.fst (hc j)) a
    simp only [Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    simp only [Matrix.mul_apply, J, Matrix.of_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have h2 : C.2 * J = 0 := by
    ext a j
    have := congrFun (congrArg Prod.snd (hc j)) a
    simp only [Prod.snd_sum, Prod.smul_snd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] at this
    simp only [Matrix.mul_apply, J, Matrix.of_apply, Matrix.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _

  have hIinj : Function.Injective I.mulVec := Matrix.mulVec_injective_iff.mpr hI
  have hJinj : Function.Injective J.mulVec := by
    intro x y hxy
    apply hIinj
    rw [← h1, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxy]
  let jL : (Fin s → E) →ₗ[E] (Fin r → E) := Matrix.toLin' J
  have hker : LinearMap.ker jL = ⊥ := LinearMap.ker_eq_bot.mpr (by
    intro x y hxy; exact hJinj (by simpa [jL, Matrix.toLin'_apply] using hxy))
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective jL hker
  let Wk := LinearMap.ker g
  let b := Module.finBasis E Wk
  let kL : (Fin (Module.finrank E Wk) → E) →ₗ[E] (Fin r → E) :=
    Wk.subtype ∘ₗ b.equivFun.symm.toLinearMap
  have hgP : ∀ x, g (x - jL (g x)) = 0 := by
    intro x
    rw [map_sub]
    have := LinearMap.congr_fun hg (g x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    rw [this, sub_self]
  let ψ : (Fin r → E) →ₗ[E] Wk :=
    LinearMap.codRestrict Wk (LinearMap.id - jL ∘ₗ g) (fun x => by
      simpa [Wk, LinearMap.mem_ker] using hgP x)
  let mL : (Fin r → E) →ₗ[E] (Fin (Module.finrank E Wk) → E) := b.equivFun.toLinearMap ∘ₗ ψ
  have hJ : J = LinearMap.toMatrix' jL := by simp [jL]
  refine ⟨Module.finrank E Wk, J, LinearMap.toMatrix' kL, LinearMap.toMatrix' g,
    LinearMap.toMatrix' mL, h1, h2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hJ, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]
  · rw [← LinearMap.toMatrix'_comp]
    have : g ∘ₗ kL = 0 := by
      refine LinearMap.ext fun y => ?_
      simp only [LinearMap.comp_apply, LinearMap.zero_apply, kL]
      exact (b.equivFun.symm y).2
    rw [this, map_zero]
  · rw [hJ, ← LinearMap.toMatrix'_comp]
    have : mL ∘ₗ jL = 0 := by
      refine LinearMap.ext fun x => ?_
      simp only [LinearMap.comp_apply, LinearMap.zero_apply, mL]
      have : ψ (jL x) = 0 := by
        apply Subtype.ext
        simp only [ψ, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
          LinearMap.comp_apply, ZeroMemClass.coe_zero]
        have := LinearMap.congr_fun hg x
        simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
        rw [this, sub_self]
      rw [this, map_zero]
    rw [this, map_zero]
  · rw [← LinearMap.toMatrix'_comp]
    have : mL ∘ₗ kL = LinearMap.id := by
      refine LinearMap.ext fun y => ?_
      simp only [LinearMap.comp_apply, LinearMap.id_apply, mL]
      have : ψ (kL y) = b.equivFun.symm y := by
        apply Subtype.ext
        have hk : g (kL y) = 0 := (b.equivFun.symm y).2
        simp only [ψ, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
          LinearMap.comp_apply, hk, map_zero, sub_zero]
        rfl
      rw [this]
      exact b.equivFun.apply_symm_apply y
    rw [this, LinearMap.toMatrix'_id]
  · rw [hJ, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp, ← map_add (f := _),
      ← LinearMap.toMatrix'_id]
    congr 1
    refine LinearMap.ext fun x => ?_
    simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, mL, kL]
    simp only [LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Submodule.coe_subtype, ψ,
      LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
    abel

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdicCoordinatesOfBasisModP
section
namespace GlobalTheory.AdicCoord

theorem eq_zero_of_forall_pow_dvd {R : Type} [CommRing R] (x : R)
    [IsHausdorff (Ideal.span {x}) R] (y : R) (h : ∀ N : ℕ, x ^ N ∣ y) : y = 0 := by
  refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {x}) R) y fun N => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact h N

theorem exists_sum_series {R : Type} [CommRing R] (x : R)
    [IsPrecomplete (Ideal.span {x}) R] (a : ℕ → R) :
    ∃ L : R, ∀ N : ℕ, x ^ N ∣ (∑ k ∈ Finset.range N, x ^ k * a k) - L := by
  have key : ∀ (N : ℕ) (u v : R), u ≡ v [SMOD ((Ideal.span {x}) ^ N • ⊤ : Submodule R R)] ↔
      x ^ N ∣ u - v := by
    intro N u v
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {x}) R)
    (f := fun N => ∑ k ∈ Finset.range N, x ^ k * a k) (by
      intro m n hmn
      rw [key, ← dvd_neg, neg_sub, ← Finset.sum_Ico_eq_sub _ hmn]
      refine Finset.dvd_sum fun k hk => ?_
      exact Dvd.dvd.mul_right (pow_dvd_pow x (Finset.mem_Ico.1 hk).1) _)
  exact ⟨L, fun N => (key N _ _).1 (hL N)⟩

theorem exists_coord : ∀ (p : ℕ) (O EE W RW : Type) [CommRing O] [CommRing EE] [CommRing W] [CommRing RW] [Algebra O EE] [Algebra O RW] (ι : EE →ₐ[O] RW) (c : W →+* RW) (d : ℕ) (o : Fin d → O), (∀ r : RW, ∃! w : Fin d → W, r = ∑ j, o j • c (w j)) → IsAdicComplete (Ideal.span {(p : EE)}) EE → IsAdicComplete (Ideal.span {(p : W)}) W → (∀ e : EE, ∃ e' : Fin d → EE, (∀ j, ι (e' j) ∈ Set.range c) ∧ e - ∑ j, o j • e' j ∈ Ideal.span {(p : EE)}) → ∀ e : EE, ∃ e' : Fin d → EE, (∀ j, ι (e' j) ∈ Set.range c) ∧ e = ∑ j, o j • e' j := by
  intro p O EE W RW _ _ _ _ _ _ ι c d o huniq hE hW hstep e
  choose g hg1 hg2 using hstep
  choose w hw using hg1
  simp only [Ideal.mem_span_singleton] at hg2
  choose h hh using hg2

  have hsep : ∀ r : RW, (∀ N : ℕ, (p : RW) ^ N ∣ r) → r = 0 := by
    intro r hr
    obtain ⟨u, hu, huu⟩ := huniq r
    have hu0 : ∀ j, u j = 0 := by
      intro j
      refine eq_zero_of_forall_pow_dvd (p : W) _ fun N => ?_
      obtain ⟨r', hr'⟩ := hr N
      obtain ⟨u', hu', -⟩ := huniq r'
      have : (fun j => (p : W) ^ N * u' j) = u := by
        apply huu
        rw [hr', hu', Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp
      exact ⟨u' j, by rw [← this]⟩
    rw [hu]
    simp [hu0]
  choose F hF using fun j => exists_sum_series (p : EE) (fun k => g (h^[k] e) j)
  choose V hV using fun j => exists_sum_series (p : W) (fun k => w (h^[k] e) j)
  refine ⟨F, fun j => ⟨V j, ?_⟩, ?_⟩
  · rw [← sub_eq_zero]
    refine hsep _ fun N => ?_
    have h1 := map_dvd ι (hF j N)
    have h2 := map_dvd c (hV j N)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_pow, map_natCast, map_sub, map_sum, map_mul, hw] at h1 h2
    have := dvd_sub h1 h2
    convert this using 1
    ring
  · have hiter : ∀ N : ℕ, e = ∑ j, o j • (∑ k ∈ Finset.range N, (p : EE) ^ k * g (h^[k] e) j)
        + (p : EE) ^ N * h^[N] e := by
      intro N
      induction N with
      | zero => simp
      | succ n ih =>
        have h3 := hh (h^[n] e)
        rw [sub_eq_iff_eq_add] at h3
        rw [Function.iterate_succ_apply']
        simp only [Finset.sum_range_succ, smul_add, Finset.sum_add_distrib]
        have h4 : ∑ j, o j • ((p : EE) ^ n * g (h^[n] e) j)
            = (p : EE) ^ n * ∑ j, o j • g (h^[n] e) j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => (mul_smul_comm _ _ _).symm
        rw [h4]
        linear_combination ih + (p : EE) ^ n * h3
    rw [← sub_eq_zero]
    refine eq_zero_of_forall_pow_dvd (p : EE) _ fun N => ?_
    have h5 : e - ∑ j, o j • F j =
        ∑ j, o j • ((∑ k ∈ Finset.range N, (p : EE) ^ k * g (h^[k] e) j) - F j)
        + (p : EE) ^ N * h^[N] e := by
      simp only [smul_sub, Finset.sum_sub_distrib]
      linear_combination hiter N
    rw [h5]
    refine dvd_add (Finset.dvd_sum fun j _ => ?_) (dvd_mul_right _ _)
    rw [Algebra.smul_def]
    exact Dvd.dvd.mul_left (hF j N) _

end GlobalTheory.AdicCoord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAlgHomTraceEqSumMultTrace
section
namespace GlobalTheory

open Matrix

noncomputable def blockDiagMultAlgHom (k : Type) [Field k] (N : ℕ) (n m : Fin N → ℕ) :
    (Π i, Matrix (Fin (n i)) (Fin (n i)) k) →ₐ[k]
      Matrix (Σ j : (Σ i, Fin (m i)), Fin (n j.1)) (Σ j : (Σ i, Fin (m i)), Fin (n j.1)) k where
  toFun x := blockDiagonal' (fun j : (Σ i, Fin (m i)) => x j.1)
  map_one' := by
    show blockDiagonal' (fun j : (Σ i, Fin (m i)) => (1 : Matrix (Fin (n j.1)) (Fin (n j.1)) k)) = 1
    exact blockDiagonal'_one
  map_mul' x y := by
    simp only [Pi.mul_apply]
    exact blockDiagonal'_mul _ _
  map_zero' := by
    show blockDiagonal' (fun j : (Σ i, Fin (m i)) => (0 : Matrix (Fin (n j.1)) (Fin (n j.1)) k)) = 0
    exact blockDiagonal'_zero
  map_add' x y := by
    simp only [Pi.add_apply]
    exact (blockDiagonal'_add _ _)
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one]
    simp only [Pi.smul_apply, Pi.one_apply]
    rw [show (fun j : (Σ i, Fin (m i)) => r • (1 : Matrix (Fin (n j.1)) (Fin (n j.1)) k))
        = r • (fun j => 1) from rfl, blockDiagonal'_smul]
    congr 1
    exact blockDiagonal'_one

theorem blockDiagMultAlgHom_trace (k : Type) [Field k] (N : ℕ) (n m : Fin N → ℕ)
    (x : Π i, Matrix (Fin (n i)) (Fin (n i)) k) :
    (blockDiagMultAlgHom k N n m x).trace = ∑ i, (m i : k) * (x i).trace := by
  show (blockDiagonal' (fun j : (Σ i, Fin (m i)) => x j.1)).trace = _
  rw [trace_blockDiagonal', Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  show ∑ _y : Fin (m i), (x i).trace = _
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem exists_algHom_trace_eq_sum_mult_trace : ∀ (k : Type) [Field k] (N : ℕ) (n m : Fin N → ℕ) (d : ℕ),
    ∑ i, m i * n i = d → ∃ ρ : (Π i, Matrix (Fin (n i)) (Fin (n i)) k) →ₐ[k] Matrix (Fin d) (Fin d) k,
      ∀ x, (ρ x).trace = ∑ i, (m i : k) * (x i).trace := by
  intro k _ N n m d hd
  have hcard : Fintype.card (Σ j : (Σ i, Fin (m i)), Fin (n j.1)) = d := by
    rw [Fintype.card_sigma, Fintype.sum_sigma, ← hd]
    simp [mul_comm]
  let e := Fintype.equivFinOfCardEq hcard
  refine ⟨(reindexAlgEquiv k k e).toAlgHom.comp (blockDiagMultAlgHom k N n m), fun x => ?_⟩
  rw [← blockDiagMultAlgHom_trace]
  show (reindex e e (blockDiagMultAlgHom k N n m x)).trace = _
  simp only [reindex_apply, trace, diag, submatrix_apply]
  exact Equiv.sum_comp e.symm (fun i => blockDiagMultAlgHom k N n m x i i)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAnalyticSubOneDivOneSubUnitMulExp
section
open Filter Topology

namespace GlobalTheory

theorem one_sub_unit_mul_exp_ne_zero (L : ℝ) (hL : 0 < L) (χ : ℂ) (hχ : ‖χ‖ = 1) (t : ℝ)
    (ht : t ≠ 0) : 1 - χ * Complex.exp (-((L : ℂ) * (t : ℂ))) ≠ 0 := by
  intro h
  have h1 : χ * Complex.exp (-((L : ℂ) * (t : ℂ))) = 1 := (sub_eq_zero.mp h).symm
  have h2 := congrArg norm h1
  rw [norm_mul, hχ, one_mul, Complex.norm_exp, norm_one] at h2
  have h3 : (-((L : ℂ) * (t : ℂ))).re = 0 := by
    have := Real.exp_eq_one_iff _ |>.mp h2
    exact this
  simp at h3
  rcases h3 with h3 | h3
  · exact hL.ne' h3
  · exact ht h3

theorem exists_analytic_sub_one_div_one_sub_unit_mul_exp :
    ∀ (L : ℝ), 0 < L → ∀ χ : ℂ, ‖χ‖ = 1 → ∃ h : ℂ → ℂ, (∀ x : ℝ, 0 < x → AnalyticAt ℂ h (x : ℂ)) ∧ (∀ x : ℝ, 1 < x → h (x : ℂ) = ((x : ℂ) - 1) / (1 - χ * Complex.exp (-((L : ℂ) * ((x : ℂ) - 1))))) ∧ (χ ≠ 1 → h 1 = 0) := by
  intro L hL χ hχ
  by_cases h1 : χ = 1
  · subst h1
    set f : ℂ → ℂ := fun w => 1 - Complex.exp (-((L : ℂ) * w)) with hf
    have hfd : Differentiable ℂ f := by
      rw [hf]; fun_prop
    have hkd : Differentiable ℂ (dslope f 0) := by
      rw [← differentiableOn_univ, Complex.differentiableOn_dslope Filter.univ_mem]
      exact hfd.differentiableOn
    have hk : ∀ w : ℂ, w ≠ 0 → dslope f 0 w = f w / w := by
      intro w hw
      rw [dslope_of_ne _ hw, slope_def_field]
      simp [hf]
    have hk0 : dslope f 0 0 = L := by
      rw [dslope_same]
      have : HasDerivAt f (0 - Complex.exp (-((L : ℂ) * 0)) * (-((L : ℂ) * 1))) 0 :=
        (hasDerivAt_const _ _).sub (((hasDerivAt_id (0 : ℂ)).const_mul (L : ℂ)).neg.cexp)
      rw [this.deriv]; simp
    refine ⟨fun s => (dslope f 0 (s - 1))⁻¹, ?_, ?_, fun h => absurd rfl h⟩
    · intro x _
      have hd : Differentiable ℂ (fun s : ℂ => dslope f 0 (s - 1)) :=
        hkd.comp (differentiable_id.sub_const 1)
      refine (hd.analyticAt _).inv ?_
      by_cases hx : x = 1
      · subst hx
        show dslope f 0 (((1 : ℝ) : ℂ) - 1) ≠ 0
        rw [Complex.ofReal_one, sub_self, hk0]
        exact_mod_cast hL.ne'
      · have hx' : x - 1 ≠ 0 := sub_ne_zero.mpr hx
        have hx'' : (x : ℂ) - 1 ≠ 0 := by exact_mod_cast hx'
        show dslope f 0 ((x : ℂ) - 1) ≠ 0
        rw [hk _ hx'']
        refine div_ne_zero ?_ hx''
        have := one_sub_unit_mul_exp_ne_zero L hL 1 hχ (x - 1) hx'
        simpa [hf] using this
    · intro x hx
      have hx' : x - 1 ≠ 0 := sub_ne_zero.mpr hx.ne'
      have hx'' : (x : ℂ) - 1 ≠ 0 := by exact_mod_cast hx'
      show (dslope f 0 ((x : ℂ) - 1))⁻¹ = _
      rw [hk _ hx'', inv_div, one_mul]
  · refine ⟨fun s => (s - 1) / (1 - χ * Complex.exp (-((L : ℂ) * (s - 1)))), ?_, fun _ _ => rfl,
      fun _ => by simp⟩
    intro x _
    have hd : Differentiable ℂ (fun s : ℂ => 1 - χ * Complex.exp (-((L : ℂ) * (s - 1)))) := by
      fun_prop
    have hn : Differentiable ℂ (fun s : ℂ => s - 1) := by fun_prop
    refine (hn.analyticAt _).div (hd.analyticAt _) ?_
    by_cases hx : x = 1
    · subst hx
      simpa [sub_eq_zero] using fun h => h1 (Eq.symm h)
    · have := one_sub_unit_mul_exp_ne_zero L hL χ hχ (x - 1) (sub_ne_zero.mpr hx)
      simpa using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValsAtApply
section
namespace GlobalTheory.UnitLemma

def valsAt {G : Type} [Group G] {ι : Type} (w : ι → G →* Multiplicative ℤ) {r : ℕ} (e : Fin r → ι) :
    G →* Multiplicative (Fin r → ℤ) :=
  (MulEquiv.funMultiplicative _ ℤ).symm.toMonoidHom.comp (MonoidHom.pi (w ∘ e))

theorem valsAt_apply {G : Type} [Group G] {ι : Type} (w : ι → G →* Multiplicative ℤ) {r : ℕ}
    (e : Fin r → ι) (x : G) (j : Fin r) :
    Multiplicative.toAdd (valsAt w e x) j = Multiplicative.toAdd (w (e j) x) := rfl

end GlobalTheory.UnitLemma
end

