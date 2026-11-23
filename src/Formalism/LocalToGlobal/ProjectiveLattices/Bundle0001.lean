module

public import Mathlib

@[expose] public section

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.AvMono
section
set_option autoImplicit false

noncomputable section

open Polynomial IsLocalRing

namespace Formalism.L2.Pj.AvAlg

variable {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
  [IsDiscreteValuationRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]

theorem mem_adjoin_mod (α : B) (hres : Algebra.adjoin (ResidueField A) {residue B α} = ⊤) (f : A[X])
    (hβ : Irreducible (aeval α f)) :
    ∀ (n : ℕ) (b : B), ∃ s ∈ Algebra.adjoin A {α}, ∃ c : B, b = s + aeval α f ^ n * c := by
  have hra : ∀ G : A[X], residue B (aeval α G) = aeval (residue B α) (G.map (residue A)) := by
    intro G
    rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.hom_eval₂]
    congr 1
    all_goals (ext x; simp only [RingHom.comp_apply]; exact (IsLocalRing.ResidueField.algebraMap_residue x).symm)
  intro n
  induction n with
  | zero => intro b; exact ⟨0, Subalgebra.zero_mem _, b, by simp⟩
  | succ n ih =>
    intro b
    obtain ⟨s, hs, c, rfl⟩ := ih b
    have hc : residue B c ∈ Algebra.adjoin (ResidueField A) {residue B α} := by
      rw [hres]; exact Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hc
    obtain ⟨p, hp⟩ := hc
    obtain ⟨P, rfl⟩ := Polynomial.map_surjective (residue A) IsLocalRing.residue_surjective p
    have hm : c - aeval α P ∈ maximalIdeal B := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hra]
      rw [← hp]
      exact sub_self _
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hβ, Ideal.mem_span_singleton'] at hm
    obtain ⟨c', hc'⟩ := hm
    have hα : aeval α f ∈ Algebra.adjoin A {α} := by
      rw [Algebra.adjoin_singleton_eq_range_aeval]; exact AlgHom.mem_range_self _ f
    have hP : aeval α P ∈ Algebra.adjoin A {α} := by
      rw [Algebra.adjoin_singleton_eq_range_aeval]; exact AlgHom.mem_range_self _ P
    refine ⟨s + aeval α f ^ n * aeval α P, ?_, c', ?_⟩
    · exact Subalgebra.add_mem _ hs (Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hα n) hP)
    · have e : c = aeval α P + c' * aeval α f := by rw [hc']; ring
      rw [e]
      ring

end Formalism.L2.Pj.AvAlg

namespace Formalism.L2.Pj.AvAlg

variable {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
  [IsDiscreteValuationRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]

theorem adjoin_eq_top_of_gen [Module.Finite A B] (hinj : Function.Injective (algebraMap A B)) (α : B)
    (hres : Algebra.adjoin (ResidueField A) {residue B α} = ⊤) (f : A[X]) (hβ : Irreducible (aeval α f)) :
    Algebra.adjoin A {α} = ⊤ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hϖ0 : algebraMap A B ϖ ≠ 0 := by
    rw [map_ne_zero_iff _ hinj]; exact hϖ.ne_zero
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hϖ0 hβ
  have hϖm : ϖ ∈ maximalIdeal A := (IsLocalRing.mem_maximalIdeal ϖ).mpr hϖ.not_isUnit
  have key : (⊤ : Submodule A B) ≤ Subalgebra.toSubmodule (Algebra.adjoin A {α}) ⊔ (maximalIdeal A) • ⊤ := by
    intro b _
    obtain ⟨s, hs, c, hc⟩ := mem_adjoin_mod α hres f hβ e b
    have e1 : b = s + ϖ • ((↑u⁻¹ : B) * c) := by
      rw [hc, Algebra.smul_def, hu]
      congr 1
      rw [mul_comm (↑u : B), mul_assoc, ← mul_assoc (↑u : B), Units.mul_inv, one_mul]
    rw [e1]
    exact Submodule.add_mem_sup ((Subalgebra.mem_toSubmodule _).mpr hs)
      (Submodule.smul_mem_smul hϖm Submodule.mem_top)
  have hfg : (⊤ : Submodule A B).FG := Module.Finite.fg_top
  have hle := Submodule.le_of_le_smul_of_le_jacobson_bot hfg
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge key
  rw [eq_top_iff]
  intro x _
  exact (Subalgebra.mem_toSubmodule _).mp (hle Submodule.mem_top)

end Formalism.L2.Pj.AvAlg

namespace Formalism.L2.Pj.AvAlg

variable {A B : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [CommRing B] [IsDomain B]
  [IsDiscreteValuationRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]

theorem residue_aeval (α : B) (G : A[X]) :
    residue B (aeval α G) = aeval (residue B α) (G.map (residue A)) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.hom_eval₂]
  congr 1
  all_goals (ext x; simp only [RingHom.comp_apply]; exact (IsLocalRing.ResidueField.algebraMap_residue x).symm)

theorem adjoin_residue_gen [Finite (ResidueField B)] :
    ∃ γ : ResidueField B, Algebra.adjoin (ResidueField A) {γ} = ⊤ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ResidueField B)ˣ)
  refine ⟨(g : ResidueField B), ?_⟩
  rw [eq_top_iff]
  intro x _
  by_cases hx : x = 0
  · rw [hx]; exact Subalgebra.zero_mem _
  · obtain ⟨n, hn⟩ := (mem_powers_iff_mem_zpowers.mpr (hg (Units.mk0 x hx)))
    have e : x = (g : ResidueField B) ^ n := by
      rw [← Units.val_pow_eq_pow_val, show g ^ n = Units.mk0 x hx from hn, Units.val_mk0]
    rw [e]
    exact Subalgebra.pow_mem (Algebra.adjoin (ResidueField A) {(g : ResidueField B)})
      (Algebra.subset_adjoin (Set.mem_singleton _)) n

theorem exists_adjoin_eq_top [Module.Finite A B] [Finite (ResidueField A)]
    (hinj : Function.Injective (algebraMap A B)) : ∃ α : B, Algebra.adjoin A {α} = ⊤ := by
  haveI : Finite (ResidueField B) := IsLocalRing.ResidueField.finite_of_finite (R := A) ‹_›
  obtain ⟨γ, hγ⟩ := adjoin_residue_gen (A := A) (B := B)
  obtain ⟨α0, rfl⟩ := IsLocalRing.residue_surjective γ
  have hint : IsIntegral (ResidueField A) (residue B α0) := IsIntegral.of_finite _ _
  have hsep : (minpoly (ResidueField A) (residue B α0)).Separable :=
    PerfectField.separable_of_irreducible (minpoly.irreducible hint)
  have hq0 : aeval (residue B α0) (minpoly (ResidueField A) (residue B α0)) = 0 := minpoly.aeval _ _
  have hq' : aeval (residue B α0) (derivative (minpoly (ResidueField A) (residue B α0))) ≠ 0 :=
    hsep.aeval_derivative_ne_zero hq0
  obtain ⟨P, hP⟩ := Polynomial.map_surjective (residue A) IsLocalRing.residue_surjective
    (minpoly (ResidueField A) (residue B α0))
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hmax := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  have hm : aeval α0 P ∈ maximalIdeal B := by
    rw [← IsLocalRing.residue_eq_zero_iff, residue_aeval, hP, hq0]
  have hd : IsUnit (aeval α0 (derivative P)) := by
    by_contra hnu
    have h3 : aeval α0 (derivative P) ∈ maximalIdeal B := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    rw [← IsLocalRing.residue_eq_zero_iff, residue_aeval, ← Polynomial.derivative_map, hP] at h3
    exact hq' h3
  by_cases h2 : aeval α0 P ∈ Ideal.span {π ^ 2}
  · refine ⟨α0 + π, adjoin_eq_top_of_gen hinj (α0 + π) ?_ P ?_⟩
    · have hr : residue B π = 0 :=
        (IsLocalRing.residue_eq_zero_iff _).mpr (hmax ▸ Ideal.mem_span_singleton_self π)
      rw [map_add (f := _), hr, add_zero]; exact hγ
    · obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp h2
      obtain ⟨k, hk⟩ := Polynomial.binomExpansion (P.map (algebraMap A B)) α0 π
      have e : aeval (α0 + π) P = π * (aeval α0 (derivative P) + π * (t + k)) := by
        simp only [Polynomial.aeval_def, ← Polynomial.eval_map] at ht ⊢
        rw [← Polynomial.derivative_map, hk, ← ht]
        ring
      have hv : IsUnit (aeval α0 (derivative P) + π * (t + k)) := by
        by_contra hnu
        have h1 : aeval α0 (derivative P) + π * (t + k) ∈ maximalIdeal B :=
          (IsLocalRing.mem_maximalIdeal _).mpr hnu
        have h3 : π * (t + k) ∈ maximalIdeal B := by
          rw [hmax]; exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self π)
        have h4 : aeval α0 (derivative P) ∈ maximalIdeal B := by
          simpa using Ideal.sub_mem _ h1 h3
        exact (IsLocalRing.mem_maximalIdeal _).mp h4 hd
      rw [e]
      exact (irreducible_mul_isUnit hv).mpr hπ
  · refine ⟨α0, adjoin_eq_top_of_gen hinj α0 hγ P ?_⟩
    rw [hmax] at hm
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hm
    have hwu : IsUnit w := by
      by_contra hnu
      apply h2
      have h5 : w ∈ maximalIdeal B := (IsLocalRing.mem_maximalIdeal _).mpr hnu
      rw [hmax, Ideal.mem_span_singleton'] at h5
      obtain ⟨v, hv⟩ := h5
      rw [Ideal.mem_span_singleton']
      exact ⟨v, by rw [← hw, ← hv]; ring⟩
    rw [← hw, mul_comm]
    exact (irreducible_mul_isUnit hwu).mpr hπ

end Formalism.L2.Pj.AvAlg
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CompSplitPfC
section
noncomputable section

namespace Formalism.L2.Pj.CompSplitPfC

open TensorProduct

variable {P S : Type} [CommRing P] [IsDomain P] [IsIntegrallyClosed P] [CommRing S] [Algebra P S]
  [Algebra.Etale P S]

theorem cspC_alg (s : S) : algebraMap S (S ⊗[P] FractionRing P) s = s ⊗ₜ (1 : FractionRing P) := rfl

theorem cspC_inj : Function.Injective (algebraMap S (S ⊗[P] FractionRing P)) := by
  have hf : Function.Injective (Algebra.linearMap P (FractionRing P)) :=
    IsFractionRing.injective P (FractionRing P)
  have h2 := Module.Flat.lTensor_preserves_injective_linearMap (M := S)
    (Algebra.linearMap P (FractionRing P)) hf
  have key : ∀ s : S, algebraMap S (S ⊗[P] FractionRing P) s =
      (LinearMap.lTensor S (Algebra.linearMap P (FractionRing P))) ((TensorProduct.rid P S).symm s) := by
    intro s
    rw [cspC_alg, TensorProduct.rid_symm_apply, LinearMap.lTensor_tmul, Algebra.linearMap_apply, map_one]
  intro a b h
  rw [key, key] at h
  exact (TensorProduct.rid P S).symm.injective (h2 h)

theorem cspC_artinian : IsArtinianRing (S ⊗[P] FractionRing P) := by
  haveI : Algebra.Etale (FractionRing P) (FractionRing P ⊗[P] S) := inferInstance
  haveI : Module.Finite (FractionRing P) (FractionRing P ⊗[P] S) :=
    Algebra.FormallyUnramified.finite_of_free (FractionRing P) _
  haveI : IsArtinianRing (FractionRing P ⊗[P] S) := IsArtinianRing.of_finite (FractionRing P) _
  exact Function.Surjective.isArtinianRing (f := (Algebra.TensorProduct.comm P (FractionRing P) S))
    (Algebra.TensorProduct.comm P (FractionRing P) S).surjective

theorem cspC_range (y : S ⊗[P] integralClosure P (FractionRing P)) :
    ∃ s : S, algebraMap S (S ⊗[P] FractionRing P) s =
      Algebra.TensorProduct.map (AlgHom.id P S) (integralClosure P (FractionRing P)).val y := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul s z =>
    obtain ⟨p, hp⟩ := (IsIntegrallyClosed.isIntegral_iff (R := P) (K := FractionRing P)).mp z.2
    refine ⟨p • s, ?_⟩
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Subalgebra.coe_val, cspC_alg, ← hp,
      Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add a b ha hb =>
    obtain ⟨s, hs⟩ := ha
    obtain ⟨s', hs'⟩ := hb
    exact ⟨s + s', by rw [map_add (f := _), map_add (f := _), hs, hs']⟩

theorem cspC_idem_of {r : S ⊗[P] FractionRing P} (hr : IsIdempotentElem r) :
    ∃ s : S, algebraMap S (S ⊗[P] FractionRing P) s = r := by
  have hint : IsIntegral S r := by
    refine ⟨Polynomial.X * (Polynomial.X - Polynomial.C 1), Polynomial.monic_X.mul (Polynomial.monic_X_sub_C 1), ?_⟩
    simp [mul_sub, hr.eq]
  obtain ⟨y, hy⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth (R := P) (S := S)
    (B := FractionRing P)).2 ⟨r, hint⟩
  obtain ⟨s, hs⟩ := cspC_range y
  refine ⟨s, hs.trans ?_⟩
  exact congrArg Subtype.val hy

variable (P) in
include P in
theorem cspC_minimal_unique {q P1 P2 : Ideal S} [hq : q.IsPrime] (h1 : P1 ∈ minimalPrimes S)
    (h2 : P2 ∈ minimalPrimes S) (hq1 : P1 ≤ q) (hq2 : P2 ≤ q) : P1 = P2 := by
  by_contra hne
  let M := Algebra.algebraMapSubmonoid S (nonZeroDivisors P)
  have hP1 : P1.IsPrime := Ideal.minimalPrimes_isPrime h1
  have hP2 : P2.IsPrime := Ideal.minimalPrimes_isPrime h2
  have hM : ∀ I ∈ minimalPrimes S, Disjoint (M : Set S) I := by
    intro I hI
    refine Set.disjoint_left.2 fun m hm hmI => ?_
    have hnzd : m ∈ nonZeroDivisors S := by
      refine mem_nonZeroDivisors_iff_right.2 fun x hx => cspC_inj (P := P) ?_
      have hu := IsLocalization.map_units (S ⊗[P] FractionRing P) (⟨m, hm⟩ : M)
      have h0 : algebraMap S (S ⊗[P] FractionRing P) x * algebraMap S (S ⊗[P] FractionRing P) m = 0 := by
        rw [← map_mul, hx, map_zero]
      rw [map_zero]
      exact (hu.mul_left_eq_zero).1 h0
    exact Set.disjoint_left.1 (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hI) hmI hnzd
  let Q1 := Ideal.map (algebraMap S (S ⊗[P] FractionRing P)) P1
  let Q2 := Ideal.map (algebraMap S (S ⊗[P] FractionRing P)) P2
  have hQ1 : Q1.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M _ P1 hP1 (hM P1 h1)
  have hQ2 : Q2.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M _ P2 hP2 (hM P2 h2)
  have hc1 : Q1.comap (algebraMap S (S ⊗[P] FractionRing P)) = P1 :=
    IsLocalization.under_map_of_isPrime_disjoint M _ hP1 (hM P1 h1)
  have hc2 : Q2.comap (algebraMap S (S ⊗[P] FractionRing P)) = P2 :=
    IsLocalization.under_map_of_isPrime_disjoint M _ hP2 (hM P2 h2)
  have hQne : Q1 ≠ Q2 := fun e => hne (by rw [← hc1, ← hc2, e])
  have := cspC_artinian (P := P) (S := S)
  obtain ⟨r, hr2, hrid, hrall⟩ := IsArtinianRing.exists_not_mem_forall_mem_of_ne Q2
  have hr1 : r ∈ Q1 := hrall Q1 hQ1 hQne
  obtain ⟨s, hs⟩ := cspC_idem_of (P := P) hrid
  have hs1 : s ∈ P1 := by rw [← hc1, Ideal.mem_comap, hs]; exact hr1
  have hs2 : s ∉ P2 := by rw [← hc2, Ideal.mem_comap, hs]; exact hr2
  have hsid : s * s = s := cspC_inj (P := P) (by rw [map_mul, hs, hrid.eq])
  have h0 : (1 - s) * s ∈ P2 := by
    rw [sub_mul, one_mul, hsid, sub_self]
    exact P2.zero_mem
  have h1s : 1 - s ∈ P2 := (hP2.mem_or_mem h0).resolve_right hs2
  have : (1 : S) ∈ q := by
    have := q.add_mem (hq2 h1s) (hq1 hs1)
    rwa [sub_add_cancel] at this
  exact hq.ne_top ((Ideal.eq_top_iff_one _).2 this)

end Formalism.L2.Pj.CompSplitPfC
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.DatMat
section
noncomputable section

namespace Formalism.L2.Pj.DatLin

open Matrix Complex

section Mat

variable {m : Type} [Fintype m] [DecidableEq m]

theorem star_mulVec_dot (A B : Matrix m m ℂ) (u w : m → ℂ) :
    star (A *ᵥ u) ⬝ᵥ (B *ᵥ w) = star u ⬝ᵥ ((Aᴴ * B) *ᵥ w) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

theorem star_dot_self_eq (w : m → ℂ) : star w ⬝ᵥ w = ((∑ i, Complex.normSq (w i) : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self, Complex.star_def]

theorem sum_normSq_pos {w : m → ℂ} (hw : w ≠ 0) : 0 < ∑ i, Complex.normSq (w i) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hw
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ _, Complex.normSq_pos.2 hi⟩

theorem cplx_str_core (H P Q J : Matrix m m ℂ) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hJ2 : J * J = 1) (hJh : Jᴴ = J) (hH : Pᴴ * H * P = J) :
    let K := P * (Complex.I • J) * Q
    (K * K = -1) ∧ (Kᴴ * H * K = H) ∧ (Kᴴ * H = (-Complex.I) • (Qᴴ * Q)) ∧
      K.trace = Complex.I * J.trace := by
  dsimp only
  have hQP' : ∀ X : Matrix m m ℂ, Q * (P * X) = X := fun X => by rw [← Matrix.mul_assoc, hQP, Matrix.one_mul]
  have hJ2' : ∀ X : Matrix m m ℂ, J * (J * X) = X := fun X => by rw [← Matrix.mul_assoc, hJ2, Matrix.one_mul]
  have hPQh' : ∀ X : Matrix m m ℂ, Pᴴ * (Qᴴ * X) = X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hQP, Matrix.conjTranspose_one, Matrix.one_mul]

  have hH' : H = Qᴴ * (J * Q) := by
    have hq : Qᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hPQ, Matrix.conjTranspose_one]
    calc H = (Qᴴ * Pᴴ) * H * (P * Q) := by rw [hq, hPQ, Matrix.one_mul, Matrix.mul_one]
      _ = Qᴴ * ((Pᴴ * H * P) * Q) := by simp only [Matrix.mul_assoc]
      _ = Qᴴ * (J * Q) := by rw [hH]
  have hsI : star Complex.I = -Complex.I := by rw [Complex.star_def, Complex.conj_I]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc, hQP', hJ2', hPQ, Complex.I_mul_I,
      neg_smul, one_smul]
  · rw [hH']
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, hJh, hsI, Matrix.mul_smul, Matrix.smul_mul,
      smul_smul, Matrix.mul_assoc, hQP', hJ2', hPQh']
    rw [mul_neg, Complex.I_mul_I, neg_neg, one_smul]
  · rw [hH']
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, hJh, hsI, Matrix.mul_smul, Matrix.smul_mul,
      smul_smul, Matrix.mul_assoc, hQP', hJ2', hPQh']
  · rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hQP, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul]

theorem exists_cplx_str {n : Type} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (p q : ℕ)
    (e : n ≃ Fin p ⊕ Fin q) (P : GL (Fin p ⊕ Fin q) ℂ)
    (hP : ((P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).map (starRingEnd ℂ))ᵀ * H.reindex e e *
      (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Matrix.fromBlocks 1 0 0 (-1)) :
    ∃ K : Matrix n n ℂ, (∀ u, K *ᵥ (K *ᵥ u) = -u) ∧
      (∀ u w, star (K *ᵥ u) ⬝ᵥ (H *ᵥ (K *ᵥ w)) = star u ⬝ᵥ (H *ᵥ w)) ∧
      (∀ u : n → ℂ, u ≠ 0 → ∃ ρ : ℝ, 0 < ρ ∧ star (K *ᵥ u) ⬝ᵥ (H *ᵥ u) = -(Complex.I * ρ)) ∧
      K.trace = Complex.I * ((p : ℂ) - q) := by
  set P0 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) with hP0
  set Q0 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
    ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) with hQ0
  set J0 : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := Matrix.fromBlocks 1 0 0 (-1) with hJ0
  have hPh : (P0.map (starRingEnd ℂ))ᵀ = P0ᴴ := rfl
  rw [hPh] at hP
  have hPQ0 : P0 * Q0 = 1 := P.mul_inv
  have hQP0 : Q0 * P0 = 1 := P.inv_mul
  have hJJ0 : J0 * J0 = 1 := by
    simp [hJ0, Matrix.fromBlocks_multiply, Matrix.fromBlocks_one]
  set Pn := P0.submatrix e e
  set Qn := Q0.submatrix e e
  set Jn := J0.submatrix e e
  have hPQ : Pn * Qn = 1 := by rw [Matrix.submatrix_mul_equiv, hPQ0, Matrix.submatrix_one_equiv]
  have hQP : Qn * Pn = 1 := by rw [Matrix.submatrix_mul_equiv, hQP0, Matrix.submatrix_one_equiv]
  have hJ2 : Jn * Jn = 1 := by rw [Matrix.submatrix_mul_equiv, hJJ0, Matrix.submatrix_one_equiv]
  have hJh : Jnᴴ = Jn := by
    simp [Jn, hJ0, Matrix.conjTranspose_submatrix, Matrix.fromBlocks_conjTranspose]
  have hH : Pnᴴ * H * Pn = Jn := by
    have hH0 : H = (H.reindex e e).submatrix e e := by
      ext i j; simp [Matrix.reindex_apply]
    rw [hH0, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hP]
  obtain ⟨h1, h2, h3, h4⟩ := cplx_str_core H Pn Qn Jn hPQ hQP hJ2 hJh hH
  refine ⟨Pn * (Complex.I • Jn) * Qn, ?_, ?_, ?_, ?_⟩
  · intro u
    rw [Matrix.mulVec_mulVec, h1, Matrix.neg_mulVec, Matrix.one_mulVec]
  · intro u w
    rw [Matrix.mulVec_mulVec, star_mulVec_dot, ← Matrix.mul_assoc, h2]
  · intro u hu
    refine ⟨∑ i, Complex.normSq ((Qn *ᵥ u) i), sum_normSq_pos ?_, ?_⟩
    · intro h0
      apply hu
      have := congrArg (Pn *ᵥ ·) h0
      simpa [Matrix.mulVec_mulVec, hPQ] using this
    · rw [star_mulVec_dot, h3, Matrix.smul_mulVec, dotProduct_smul, ← star_mulVec_dot, star_dot_self_eq,
        smul_eq_mul, neg_mul]
  · rw [h4]
    congr 1
    have ht : Jn.trace = J0.trace := by
      simp only [Matrix.trace, Matrix.diag, Jn, Matrix.submatrix_apply]
      exact Equiv.sum_comp e (fun i => J0 i i)
    rw [ht, hJ0]
    simp [Matrix.trace, Fintype.sum_sum_type, sub_eq_add_neg]

end Mat

section GlobalTheory

variable {ι n : Type} [Fintype ι] [Fintype n]

def blk (N : ι → Matrix n n ℂ) : (ι → n → ℂ) →ₗ[ℝ] (ι → n → ℂ) where
  toFun u τ := N τ *ᵥ u τ
  map_add' u v := by ext τ : 1; simp [Matrix.mulVec_add]
  map_smul' c u := by
    ext τ i
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [Matrix.mulVec_smul]
    rfl

theorem blk_apply (N : ι → Matrix n n ℂ) (u : ι → n → ℂ) (τ : ι) : blk N u τ = N τ *ᵥ u τ := rfl

theorem blk_comp (N N' : ι → Matrix n n ℂ) : blk N ∘ₗ blk N' = blk (fun τ => N τ * N' τ) := by
  apply LinearMap.ext
  intro u
  funext τ
  simp only [LinearMap.comp_apply, blk_apply, Matrix.mulVec_mulVec]

def blkC (N : ι → Matrix n n ℂ) : (ι → n → ℂ) →ₗ[ℂ] (ι → n → ℂ) where
  toFun u τ := N τ *ᵥ u τ
  map_add' u v := by ext τ : 1; simp [Matrix.mulVec_add]
  map_smul' c u := by ext τ : 1; simp [Matrix.mulVec_smul]

theorem blk_eq_restrict (N : ι → Matrix n n ℂ) : blk N = (blkC N).restrictScalars ℝ := rfl

theorem trace_restrict_complex {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M]
    [IsScalarTower ℝ ℂ M] [Module.Free ℂ M] [Module.Finite ℂ M] (f : M →ₗ[ℂ] M) :
    LinearMap.trace ℝ M (f.restrictScalars ℝ) = 2 * (LinearMap.trace ℂ M f).re := by
  classical
  let c := Module.Free.chooseBasis ℂ M
  rw [LinearMap.trace_eq_matrix_trace ℝ (Complex.basisOneI.smulTower c), LinearMap.trace_eq_matrix_trace ℂ c]
  simp only [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, Module.Basis.smulTower_apply, Module.Basis.smulTower_repr,
    Fintype.sum_prod_type, LinearMap.restrictScalars_apply, LinearMap.map_smul, map_smul, Finsupp.smul_apply,
    smul_eq_mul, Complex.coe_basisOneI_repr, Complex.coe_basisOneI, Fin.sum_univ_two]
  simp [Complex.re_sum, Finset.mul_sum, Finset.sum_add_distrib, two_mul]

theorem trace_blkC [DecidableEq ι] [DecidableEq n] (N : ι → Matrix n n ℂ) :
    LinearMap.trace ℂ _ (blkC N) = ∑ τ, (N τ).trace := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basis fun _ : ι => Pi.basisFun ℂ n)]
  simp [Matrix.trace, LinearMap.toMatrix_apply, Fintype.sum_sigma, blkC, Matrix.mulVec_single_one]

theorem trace_blk [DecidableEq ι] [DecidableEq n] (N : ι → Matrix n n ℂ) :
    LinearMap.trace ℝ _ (blk N) = ∑ τ, 2 * (N τ).trace.re := by
  rw [blk_eq_restrict, trace_restrict_complex, trace_blkC, Complex.re_sum, Finset.mul_sum]

end GlobalTheory

end Formalism.L2.Pj.DatLin
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.GenSpecLocFrM
section
noncomputable section

namespace Formalism.L2.Pj.LocFrM

open TensorProduct

variable {O : Type*} [CommRing O] [IsLocalRing O] {V : Type*} [AddCommGroup V] [Module O V]
  [Module.Free O V] [Module.Finite O V]

theorem range_projective (e : Module.End O V) (he : IsIdempotentElem e) :
    Module.Projective O (LinearMap.range e) := by
  refine Module.Projective.of_split (LinearMap.range e).subtype e.rangeRestrict ?_
  apply LinearMap.ext
  rintro ⟨x, y, rfl⟩
  apply Subtype.ext
  show e (e y) = e y
  exact LinearMap.congr_fun he y

theorem range_free (e : Module.End O V) (he : IsIdempotentElem e) : Module.Free O (LinearMap.range e) := by
  haveI := range_projective e he
  haveI : Module.FinitePresentation O (LinearMap.range e) := Module.finitePresentation_of_projective _ _
  exact Module.free_of_flat_of_isLocalRing

section Split

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

end Split

end Formalism.L2.Pj.LocFrM
end
end

