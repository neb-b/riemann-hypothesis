module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0011
public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PrimRootSubOnePowAssociated
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem primRoot_sub_one_pow_associated {O : Type*} [CommRing O] [IsDomain O] {p : ℕ}
    (hp : p.Prime) {ζ : O} (hζ : IsPrimitiveRoot ζ p) :
    Associated ((ζ - 1) ^ (p - 1)) (p : O) := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  have h := hζ.prod_one_sub_pow_eq_order
  have h2 : Associated (∏ _k ∈ Finset.range n, (ζ - 1)) (∏ k ∈ Finset.range n, (1 - ζ ^ (k + 1))) := by
    refine Associated.prod _ _ _ fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    have hc : (k + 1).Coprime (n + 1) :=
      (Nat.coprime_of_lt_prime (by omega) (by omega) hp).symm
    have := hζ.associated_sub_one_pow_sub_one_of_coprime hc
    rw [← neg_sub (ζ ^ (k + 1)) 1]
    exact this.neg_right
  rw [h, Finset.prod_const, Finset.card_range] at h2
  simpa using h2

end GlobalTheory.CompanionTheory.Ar.HT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProjSumSumEmbeddingsEqTrace
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField

theorem projSum_sum_embeddings_eq_trace (K : Type) [Field K] [CharZero K] (E : Type) [Field E]
    [NumberField E] [Fintype (E →+* K)] (h : Fintype.card (E →+* K) = Module.finrank ℚ E) (y : E) :
    ∑ σ : E →+* K, σ y = ((Algebra.trace ℚ E y : ℚ) : K) := by
  classical
  let L := AlgebraicClosure K
  let f : (E →+* K) → (E →ₐ[ℚ] L) := fun σ => ((algebraMap K L).comp σ).toRatAlgHom
  have hinj : Function.Injective f := by
    intro σ τ hst
    ext x
    apply (algebraMap K L).injective
    have := DFunLike.congr_fun hst x
    simpa [f] using this
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [h, AlgHom.card]
  apply (algebraMap K L).injective
  have ht := trace_eq_sum_embeddings L (K := ℚ) (L := E) (x := y)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_ratCast, ← eq_ratCast (algebraMap ℚ L), ht]
  exact Fintype.sum_bijective f hbij _ _ (fun σ => by simp [f])

theorem projSum_trace_dualInt (E : Type) [Field E] [NumberField E]
    (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    Algebra.trace ℚ E (dualInt E k) = (((RingOfIntegers.basis E).repr 1 k : ℤ) : ℚ) := by
  classical
  have h1 : (1 : E) = ∑ j, (((RingOfIntegers.basis E).repr 1 j : ℤ) : ℚ) • integralBasis E j := by
    have := congrArg (algebraMap (𝓞 E) E) ((RingOfIntegers.basis E).sum_repr 1)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, (algebraMap (𝓞 E) E).map_one] at this
    refine this.symm.trans ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integralBasis_apply, map_zsmul, Int.cast_smul_eq_zsmul]
  have h2 : Algebra.trace ℚ E (dualInt E k) = Algebra.traceForm ℚ E (dualInt E k) 1 := by
    rw [Algebra.traceForm_apply, mul_one]
  rw [h2]
  conv_lhs => rw [h1]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul, dualInt, LinearMap.BilinForm.apply_dualBasis_left]
  simp

theorem sum_eigProj_eq_one (K : Type) [Field K] [CharZero K] (V : Type) [AddCommGroup V]
    [Module K V] (E : Type) [Field E] [NumberField E] (ρ : 𝓞 E →+* Module.End K V)
    [Fintype (E →+* K)] (h : Fintype.card (E →+* K) = Module.finrank ℚ E) :
    ∑ σ : E →+* K, eigProj ρ σ = 1 := by
  classical
  unfold eigProj
  rw [Finset.sum_comm]
  have := congrArg ρ ((RingOfIntegers.basis E).sum_repr 1)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, ρ.map_one] at this
  refine Eq.trans ?_ this
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_smul, projSum_sum_embeddings_eq_trace K E h, projSum_trace_dualInt,
    Rat.cast_intCast, map_zsmul, Int.cast_smul_eq_zsmul]

end GlobalTheory.CompanionTheory.Ar.HT
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RelatedPairsOrbitalTermEq
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT.ProjEig

open Module NumberField

section

variable {E : Type} [Field E] [NumberField E]

theorem trace_dualInt_mul (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) (x : E) :
    Algebra.trace ℚ E (dualInt E k * x) = (integralBasis E).repr x k := by
  classical
  have h : ∀ l, Algebra.trace ℚ E (dualInt E k * integralBasis E l) = if l = k then 1 else 0 := by
    intro l
    have := LinearMap.BilinForm.apply_dualBasis_left (B := Algebra.traceForm ℚ E)
      (traceForm_nondegenerate ℚ E) (integralBasis E) k l
    rw [Algebra.traceForm_apply] at this
    unfold dualInt
    convert this
  conv_lhs => rw [← (integralBasis E).sum_repr x]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.mul_sum, map_sum, mul_smul_comm, map_smul, h]
  simp

theorem mul_dualInt_eq (a : 𝓞 E) (l : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    (a : E) * dualInt E l =
      ∑ k, (((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E k) l : ℤ) : E) *
        dualInt E k := by
  classical
  have h := ((Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E)
    (integralBasis E)).sum_repr ((a : E) * dualInt E l)
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, mul_comm (a : E),
    mul_assoc, trace_dualInt_mul, integralBasis_apply]
  have : (a : E) * algebraMap (𝓞 E) E (RingOfIntegers.basis E k)
      = algebraMap (𝓞 E) E (a * RingOfIntegers.basis E k) := by simp
  rw [this, integralBasis_repr_apply, Algebra.smul_def]
  simp [dualInt]

theorem sum_dualInt_mul :
    ∑ k, dualInt E k * ((RingOfIntegers.basis E k : 𝓞 E) : E) = 1 := by
  classical
  rw [← sub_eq_zero]
  refine (traceForm_nondegenerate ℚ E).1 _ fun y => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Algebra.traceForm_apply, sub_mul, map_sub, one_mul, Finset.sum_mul, map_sum,
    Algebra.trace_eq_matrix_trace (integralBasis E) y, sub_eq_zero, Matrix.trace]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_assoc, trace_dualInt_mul, Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul,
    integralBasis_apply, mul_comm y]

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

theorem mem_eigSp_iff_apply (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) (x : V) :
    x ∈ eigSp ρ σ ↔ ∀ a : 𝓞 E, ρ a x = σ (a : E) • x := by
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

theorem rho_mul_eigProj (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) (a : 𝓞 E) :
    ρ a * eigProj ρ σ = σ (a : E) • eigProj ρ σ := by
  classical
  unfold eigProj
  rw [Finset.mul_sum, Finset.smul_sum]
  have h1 : ∀ k, ρ a * (σ (dualInt E k) • ρ (RingOfIntegers.basis E k)) =
      ∑ l, (σ (dualInt E k) *
        (((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E k) l : ℤ) : K)) •
          ρ (RingOfIntegers.basis E l) := by
    intro k
    rw [mul_smul_comm, ← map_mul]
    conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr (a * RingOfIntegers.basis E k)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_zsmul, mul_smul, Int.cast_smul_eq_zsmul]
  simp_rw [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [smul_smul, ← map_mul, mul_dualInt_eq, map_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul σ, map_intCast, mul_comm]

theorem eigProj_mul_rho_comm (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) (a : 𝓞 E) :
    eigProj ρ σ * ρ a = ρ a * eigProj ρ σ := by
  unfold eigProj
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, ← map_mul, ← map_mul, mul_comm]

end

theorem eigProj_spec : ∀ (K : Type) [Field K] [CharZero K] (V : Type) [AddCommGroup V] [Module K V]
    (E : Type) [Field E] [NumberField E] (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K),
    (∀ x, eigProj ρ σ x ∈ eigSp ρ σ) ∧ (∀ x ∈ eigSp ρ σ, eigProj ρ σ x = x) ∧
    (∀ σ' : E →+* K, σ' ≠ σ → ∀ x ∈ eigSp ρ σ', eigProj ρ σ x = 0) ∧
    ∀ a : 𝓞 E, eigProj ρ σ * ρ a = ρ a * eigProj ρ σ := by
  intro K _ _ V _ _ E _ _ ρ σ
  refine ⟨fun x => ?_, fun x hx => ?_, fun σ' hσ x hx => ?_, eigProj_mul_rho_comm ρ σ⟩
  · rw [mem_eigSp_iff_apply]
    intro a
    rw [← Module.End.mul_apply, rho_mul_eigProj, LinearMap.smul_apply]
  · rw [mem_eigSp_iff_apply] at hx
    unfold eigProj
    rw [LinearMap.sum_apply]
    simp_rw [LinearMap.smul_apply, hx, smul_smul, ← map_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.sum_smul, ← map_sum, sum_dualInt_mul, map_one, one_smul]
  · rw [mem_eigSp_iff_apply] at hx
    obtain ⟨a, ha⟩ : ∃ a : 𝓞 E, σ' (a : E) ≠ σ (a : E) := by
      by_contra hcon
      push Not at hcon
      exact hσ (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext hcon))
    have h1 : eigProj ρ σ (ρ a x) = ρ a (eigProj ρ σ x) := by
      rw [← Module.End.mul_apply, eigProj_mul_rho_comm, Module.End.mul_apply]
    rw [← Module.End.mul_apply (ρ a), rho_mul_eigProj, LinearMap.smul_apply, hx, map_smul,
      ← sub_eq_zero, ← sub_smul, smul_eq_zero] at h1
    exact h1.resolve_left (sub_ne_zero.mpr ha)

end GlobalTheory.CompanionTheory.Ar.HT.ProjEig
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubAndQuotientBundles
section
namespace GlobalTheory.CompanionTheory.Ar.Crv.SubQuot

open GlobalTheory.CompanionTheory.Ar.Crv

variable {K : Type} [Field K] (C : ACurve K)

theorem finite_not_le_one (a : K) : {i | ¬ C.v i a ≤ 1}.Finite := by
  by_cases ha : a = 0
  · subst ha
    simp
  · refine (C.fin a ha).subset ?_
    intro i hi
    simp only [Set.mem_setOf_eq] at hi ⊢
    intro h
    exact hi (le_of_eq h)

theorem finite_not_mapsTo {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V']
    [Module K V'] {n m : ℕ} (b : Module.Basis (Fin n) K V) (b' : Module.Basis (Fin m) K V')
    (f : V →ₗ[K] V') :
    {i | ¬ ∀ x, (∀ q, C.v i (b.repr x q) ≤ 1) → ∀ q, C.v i (b'.repr (f x) q) ≤ 1}.Finite := by
  classical
  refine (Set.finite_iUnion fun q : Fin m => Set.finite_iUnion fun r : Fin n =>
    finite_not_le_one C (b'.repr (f (b r)) q)).subset ?_
  intro i hi
  simp only [Set.mem_setOf_eq] at hi
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  by_contra hcon
  push_neg at hcon
  apply hi
  intro x hx q
  have hx' : f x = ∑ r, b.repr x r • f (b r) := by
    conv_lhs => rw [← b.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_smul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hx', map_sum, Finsupp.finsetSum_apply]
  refine (C.v i).map_sum_le fun r _ => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, (C.v i).map_mul]
  exact mul_le_one' (hx r) (hcon q r)

theorem isBun_sub_quot : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (W : Submodule K V),
    IsBun C L → IsBun C (sub C L W) ∧ IsBun C (quot C L W) := by
  intro K _ C V _ _ _ L W hL
  unfold IsBun at hL ⊢
  obtain ⟨hloc, b0, hb0⟩ := hL
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective W.subtype W.ker_subtype
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective W.mkQ W.range_mkQ
  refine ⟨⟨fun i => ?_, Module.finBasis K W, ?_⟩, ⟨fun i => ?_, Module.finBasis K (V ⧸ W), ?_⟩⟩
  · obtain ⟨b, hb⟩ := hloc i
    obtain ⟨bW, bQ, b', -, hW, -, -, -⟩ := GlobalTheory.T.lattice_basis_adapted_to_subspace K C V i _ b (L i) W hb
    exact ⟨bW, hW⟩
  · refine ((hb0.union (finite_not_mapsTo C (Module.finBasis K W) b0 W.subtype)).union
      (finite_not_mapsTo C b0 (Module.finBasis K W) g)).subset ?_
    intro i hi
    simp only [Set.mem_union, Set.mem_setOf_eq] at hi ⊢
    by_contra hcon
    push_neg at hcon
    obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
    apply hi
    unfold IsLatOf at h1 ⊢
    intro w
    show (w : V) ∈ L i ↔ _
    rw [h1]
    have hgw : g (w : V) = w := by simpa using LinearMap.congr_fun hg w
    constructor
    · intro hw q
      have hq := h3 (w : V) hw q
      rwa [hgw] at hq
    · intro hw q
      exact h2 w hw q
  · obtain ⟨b, hb⟩ := hloc i
    obtain ⟨bW, bQ, b', -, -, hQ, -, -⟩ := GlobalTheory.T.lattice_basis_adapted_to_subspace K C V i _ b (L i) W hb
    exact ⟨bQ, hQ⟩
  · refine ((hb0.union (finite_not_mapsTo C b0 (Module.finBasis K (V ⧸ W)) W.mkQ)).union
      (finite_not_mapsTo C (Module.finBasis K (V ⧸ W)) b0 s)).subset ?_
    intro i hi
    simp only [Set.mem_union, Set.mem_setOf_eq] at hi ⊢
    by_contra hcon
    push_neg at hcon
    obtain ⟨⟨h1, h2⟩, h3⟩ := hcon
    apply hi
    unfold IsLatOf at h1 ⊢
    intro y
    show y ∈ (L i).map W.mkQ.toAddMonoidHom ↔ _
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩ q
      exact h2 x ((h1 x).1 hx) q
    · intro hy
      have hsy : W.mkQ (s y) = y := by simpa using LinearMap.congr_fun hs y
      exact ⟨s y, (h1 (s y)).2 (h3 y hy), hsy⟩

end GlobalTheory.CompanionTheory.Ar.Crv.SubQuot
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SumEmbeddingDualInt
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT.EigDim

open Module NumberField GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.HT.LatBasic

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  {E : Type} [Field E] [NumberField E]

theorem trace_eigProj [FiniteDimensional K V] (ρ : 𝓞 E →+* Module.End K V) (σ : E →+* K) :
    LinearMap.trace K V (eigProj ρ σ) = (finrank K (eigSp ρ σ) : K) :=
  LinearMap.IsProj.trace (p := eigSp ρ σ)
    ⟨fun x => eigProj_mem ρ σ x, fun _ hx => eigProj_of_mem hx⟩

theorem sum_embedding_dualInt [IsAlgClosed K] [CharZero K]
    (k : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    ∑ σ : E →+* K, σ (dualInt E k) = (((RingOfIntegers.basis E).repr 1 k : ℤ) : K) := by
  have h1 : ∑ σ : E →+* K, σ (dualInt E k) = ∑ σ : E →ₐ[ℚ] K, σ (dualInt E k) :=
    Fintype.sum_equiv (RingHom.equivRatAlgHom E K) _ _ fun _ => rfl
  have h2 := repr_eq_trace (E := E) 1 k
  rw [h1, ← trace_eq_sum_embeddings (E := K) (K := ℚ) (L := E)]
  have h3 : ((1 : 𝓞 E) : E) = 1 := map_one (algebraMap (𝓞 E) E)
  rw [h3, mul_one] at h2
  rw [← h2]
  simp

theorem sum_eigProj [IsAlgClosed K] [CharZero K] (ρ : 𝓞 E →+* Module.End K V) :
    ∑ σ : E →+* K, eigProj ρ σ = 1 := by
  unfold eigProj
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, sum_embedding_dualInt]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [← map_one ρ, ← (RingOfIntegers.basis E).sum_repr 1, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, Int.cast_smul_eq_zsmul]

theorem finrank_eigSp_mul :
    ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (V : Type) [AddCommGroup V] [Module K V]
      [FiniteDimensional K V] (E : Type) [Field E] [NumberField E] (ρ : 𝓞 E →+* Module.End K V),
      (∀ a : 𝓞 E, ∃ n : ℤ, LinearMap.trace K V (ρ a) = (n : K)) →
      ∀ σ : E →+* K, Module.finrank K (GlobalTheory.CompanionTheory.Ar.HT.eigSp ρ σ) * Module.finrank ℚ E =
        Module.finrank K V := by
  intro K _ _ _ V _ _ _ E _ _ ρ htr σ
  choose m hm using fun k => htr (RingOfIntegers.basis E k)
  set l : E := ∑ k, (m k : E) * dualInt E k with hl
  have h1 : ∀ τ : E →+* K, (finrank K (eigSp ρ τ) : K) = τ l := by
    intro τ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← trace_eigProj, hl, map_sum]
    unfold eigProj
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hm, map_mul, map_intCast, smul_eq_mul, mul_comm]
  have h2 : ∀ τ : E →+* K, (finrank K (eigSp ρ τ) : E) = l := fun τ =>
    τ.injective (by rw [map_natCast, h1])
  have h3 : ∀ τ : E →+* K, finrank K (eigSp ρ τ) = finrank K (eigSp ρ σ) := fun τ =>
    Nat.cast_injective ((h2 τ).trans (h2 σ).symm)
  have h4 : (finrank K V : K) = ∑ τ : E →+* K, (finrank K (eigSp ρ τ) : K) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← LinearMap.trace_one, ← sum_eigProj ρ, map_sum]
    exact Finset.sum_congr rfl fun τ _ => trace_eigProj ρ τ
  simp_rw [h3] at h4
  rw [Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card, nsmul_eq_mul] at h4
  have h5 : finrank K V = finrank ℚ E * finrank K (eigSp ρ σ) := by exact_mod_cast h4
  rw [h5, mul_comm]

end GlobalTheory.CompanionTheory.Ar.HT.EigDim
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UltrametricDetNormLe
section
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem norm_det_le_pow_card_of_ultrametric :
    ∀ (A : Type) [NormedField A] [IsUltrametricDist A] (I : Type) [Fintype I] [DecidableEq I]
      (M : Matrix I I A) (r : ℝ), 0 ≤ r → (∀ a b, ‖M a b‖ ≤ r) →
      ‖M.det‖ ≤ r ^ Fintype.card I := by
  intro A _ _ I _ _ M r hr hM
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hr _) ?_
  intro σ _
  rw [Units.smul_def, zsmul_eq_mul, norm_mul]
  have h1 : ‖(((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A)‖ ≤ 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have h2 : ‖∏ i, M (σ i) i‖ ≤ r ^ Fintype.card I := by
    rw [norm_prod]
    calc ∏ i, ‖M (σ i) i‖ ≤ ∏ _i : I, r :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hM _ _)
      _ = r ^ Fintype.card I := by simp
  calc _ ≤ 1 * r ^ Fintype.card I :=
        mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

end GlobalTheory.CompanionTheory.Ar.Fl
end

