module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.IsAlgIsoRefl
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualInfinitesimalCharacterRegular
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.InfinitesimalCharacterPullback.HasInfCharPullSub

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.InfAbs
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem multi_cont {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {q : ℕ}
    (μ : (Fin q → V) →ₘₗ[ℝ] ℂ) : Continuous μ := by
  let b := Module.finBasis ℝ V
  have e : (μ : (Fin q → V) → ℂ) = fun x => ∑ r : Fin q → Fin (Module.finrank ℝ V),
      (∏ i, b.coord (r i) (x i)) • μ fun i => b (r i) := by
    funext x
    have h : x = fun i => ∑ j, b.coord j (x i) • b j := funext fun i => (b.sum_repr (x i)).symm
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [h, μ.map_sum]
    simp only [μ.map_smul_univ, RingHom.id_apply]
  rw [e]
  refine continuous_finsetSum _ fun r _ => Continuous.fun_smul ?_ continuous_const
  exact continuous_finsetProd _ fun i _ =>
    (b.coord (r i)).continuous_of_finiteDimensional.comp (continuous_apply i)

private theorem multi_deriv {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] {q : ℕ}
    (μ : (Fin q → V) →ₘₗ[ℝ] ℂ) (c : ℝ → Fin q → V) (c' : Fin q → V)
    (hc : ∀ i, HasDerivAt (fun t => c t i) (c' i) 0) :
    HasDerivAt (fun t => μ (c t)) (∑ i, μ (Function.update (c 0) i (c' i))) 0 := by
  let ν : ContinuousMultilinearMap ℝ (fun _ : Fin q => V) ℂ := ⟨μ, multi_cont μ⟩
  have h := (ν.hasFDerivAt (c 0)).comp_hasDerivAt (0 : ℝ) (hasDerivAt_pi.2 hc)
  rw [ContinuousMultilinearMap.linearDeriv_apply] at h
  exact h

private theorem hp_herm {E : Type} [Field E] {a : ℕ} (Y : Herm E a) : hp (toL Y.1) = Y := by
  apply Subtype.ext
  have h : star Y.1 = Y.1 := Y.2
  rw [hp_val, h, ← two_smul ℝ, smul_smul]
  norm_num

private theorem conj_deriv {E : Type} [Field E] [NumberField E] {a : ℕ} (k : ℝ → Kinf E a)
    (Z : Matrix (Fin a) (Fin a) (Cinf E)) (hZ : star Z = -Z) (h0 : k 0 = 1)
    (hk : HasDerivAt (fun t => toL (k t).1) (toL Z) 0) (Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    HasDerivAt (fun t => toL ((k t).1 * Y * star (k t).1)) (toL (Z * Y - Y * Z)) 0 := by
  open scoped Matrix.Norms.Operator in
  have h1 : HasDerivAt (fun t => (k t).1) Z 0 := hk
  open scoped Matrix.Norms.Operator in
  have h2 : HasDerivAt (fun t => star (k t).1) (star Z) 0 :=
    (hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => (hasDerivAt_pi.1 (hasDerivAt_pi.1 hk j) i).star :
      HasDerivAt (fun t => toL (star (k t).1)) (toL (star Z)) 0)
  open scoped Matrix.Norms.Operator in
  have h := (h1.mul_const Y).mul h2
  simp only [h0, hZ, OneMemClass.coe_one, star_one, mul_one, one_mul, mul_neg, ← sub_eq_add_neg] at h
  exact h

theorem UpperTheory.V.AlgRepEndIrreducible.infAbs :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] [Module ℝ M] [IsScalarTower ℝ ℂ M] (κ : Kinf E a → Module.End ℂ M) (L : Lie E a →ₗ[ℝ] Module.End ℂ M),
      SepDer κ L → ∀ (q : ℕ) (ω : Herm E a [⋀^Fin q]→ₗ[ℝ] M), IsCochain κ ω → InfEq L ω := by
  intro E _ _ _ a M _ _ _ _ κ L hS q ω hω Z hZ Y
  obtain ⟨k, h0, hk⟩ := kCurve E a Z hZ
  rw [← sub_eq_zero]
  by_contra hne
  obtain ⟨l, hl, hd⟩ := hS k Z h0 hk _ hne
  apply hl
  let μ : (Fin q → Lie E a) →ₘₗ[ℝ] ℂ :=
    (l.restrictScalars ℝ).compMultilinearMap (ω.toMultilinearMap.compLinearMap fun _ => hp)
  have hμ : ∀ X : Fin q → Herm E a, μ (fun i => toL (X i).1) = l (ω X) := fun X => by
    change l (ω fun i => hp (toL (X i).1)) = _
    simp only [hp_herm]
  have h1 := multi_deriv μ (fun t i => toL (adHerm (k t) (Y i)).1) (fun i => toL (brH Z hZ (Y i)).1)
    (fun i => conj_deriv k Z hZ h0 hk (Y i).1)
  have h2 : ∀ t, μ (fun i => toL (adHerm (k t) (Y i)).1) = l (κ (k t) (ω Y)) := fun t => by
    rw [hμ, hω]
  simp only [h2] at h1
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, (hd (ω Y)).unique h1, map_sum, sub_eq_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hμ]
  congr 1
  funext j
  by_cases h : j = i
  · subst h; simp only [Function.update_self]
  · simp only [Function.update_of_ne h, h0, adHerm, OneMemClass.coe_one, star_one, mul_one, one_mul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.LieDecomp
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

private theorem scalarDecomp {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : Type} [AddCommGroup N]
    [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N] (l : Cinf E →ₗ[ℝ] N) (x : Cinf E) :
    l x = ∑ τ : E →+* ℂ, coord τ x • ((1 / 2 : ℂ) • (l (atEmb τ 1) - Complex.I • l (atEmb τ Complex.I))) := by
  classical
  have e : x = ∑ w : InfinitePlace E, atEmb w.embedding (x w) := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    refine Finset.sum_congr rfl fun w _ => ?_
    unfold atEmb
    rw [if_pos (by rw [InfinitePlace.mk_embedding])]
    congr 1 <;> simp
  rw [← Finset.sum_fiberwise Finset.univ InfinitePlace.mk]
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [e, map_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := fun h =>
    InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w)
      (InfinitePlace.isReal_iff.2 (ComplexEmbedding.isReal_iff.2 h.symm))
  have hf : (Finset.univ.filter fun τ : E →+* ℂ => InfinitePlace.mk τ = w) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
    ext τ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro h
      have h' : InfinitePlace.mk w.embedding = InfinitePlace.mk τ := by rw [InfinitePlace.mk_embedding, h]
      exact (InfinitePlace.mk_eq_iff.1 h').imp Eq.symm Eq.symm
    · rintro (rfl | rfl)
      · exact InfinitePlace.mk_embedding w
      · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  have e' : atEmb w.embedding (-Complex.I) = -atEmb w.embedding Complex.I := by
    rw [atEmb_eq]; simp
  rw [hf, Finset.sum_pair hne, UpperTheory.V.FieldIso.coord_conj, UpperTheory.V.FieldIso.coord_embedding, atEmb_eq _ (x w),
    map_add, map_smul, map_smul, ← algebraMap_smul ℂ (x w).re, ← algebraMap_smul ℂ (x w).im]
  simp only [atEmb_conj, map_one, Complex.conj_I, e', map_neg]
  have h1 : algebraMap ℝ ℂ (x w).re = (x w + starRingEnd ℂ (x w)) / 2 := by
    rw [Complex.add_conj]; simp
  have h2 : algebraMap ℝ ℂ (x w).im = -(x w - starRingEnd ℂ (x w)) * Complex.I / 2 := by
    rw [Complex.sub_conj]; push_cast
    change ((x w).im : ℂ) = _
    linear_combination ((x w).im : ℂ) * Complex.I_mul_I
  rw [h1, h2]
  match_scalars <;> ring

theorem UpperTheory.V.AlgRepEndIrreducible.lieDecomp :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (N : Type) [AddCommGroup N] [Module ℂ N] [Module ℝ N] [IsScalarTower ℝ ℂ N] (L : Lie E a →ₗ[ℝ] N) (X : Matrix (Fin a) (Fin a) (Cinf E)),
      L (toL X) = ∑ τ : E →+* ℂ, hol τ L (X.map (coord τ)) := by
  intro E _ _ _ a N _ _ _ _ L X
  let L' : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] N := L
  change L' X = _
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, hol_apply, Matrix.map_apply]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact scalarDecomp (L' ∘ₗ Matrix.singleLinearMap ℝ i j) (X i j)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.WtEq
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.AlgRepEndIrreducible
open scoped TensorProduct

theorem UpperTheory.V.AlgRepEndIrreducible.wtEq :
    ∀ (n : ℕ) (ν ν' : Fin n → ℂ), Dom ν → Dom ν' →
      (∀ u : ℂ, ∏ k : Fin n, (u - (k : ℂ) + ν k) = ∏ k : Fin n, (u - (k : ℂ) + ν' k)) → ν = ν' := by
  intro n ν ν' hν hν' hp
  classical
  have key : ∀ μ : Fin n → ℂ, Dom μ → ∀ i : Fin n,
      (Multiset.filter (fun y => ∃ k : ℕ, y - (μ i - (i : ℂ)) = (k : ℂ) + 1)
        (Multiset.map (fun j : Fin n => μ j - (j : ℂ)) Finset.univ.val)).card = (i : ℕ) := by
    intro μ hμ i
    have hP : ∀ j : Fin n, (∃ k : ℕ, μ j - (j : ℂ) - (μ i - (i : ℂ)) = (k : ℂ) + 1) ↔ j < i := by
      intro j
      constructor
      · rintro ⟨k, hk⟩
        by_contra hji
        rcases (not_lt.1 hji).lt_or_eq with hij | hij
        · obtain ⟨m, hm⟩ := hμ i j hij
          have h1 : (((i : ℕ) : ℕ) : ℂ) = ((k + 1 + m + (j : ℕ) : ℕ) : ℂ) := by
            push_cast
            linear_combination hk + hm
          have h2 : (i : ℕ) = k + 1 + m + (j : ℕ) := Nat.cast_injective h1
          have h3 : (i : ℕ) < (j : ℕ) := hij
          omega
        · subst hij
          have h1 : ((k + 1 : ℕ) : ℂ) = ((0 : ℕ) : ℂ) := by
            push_cast
            linear_combination -hk
          have h2 : k + 1 = 0 := Nat.cast_injective h1
          omega
      · intro hji
        obtain ⟨m, hm⟩ := hμ j i hji
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_lt (show (j : ℕ) < (i : ℕ) from hji)
        have hi : ((i : ℕ) : ℂ) = ((j : ℕ) : ℂ) + (d : ℂ) + 1 := by
          exact_mod_cast hd
        refine ⟨m + d, ?_⟩
        push_cast
        linear_combination hm + hi
    rw [Multiset.filter_map, Multiset.card_map]
    have hf : Multiset.filter ((fun y => ∃ k : ℕ, y - (μ i - (i : ℂ)) = (k : ℂ) + 1) ∘
        fun j : Fin n => μ j - (j : ℂ)) Finset.univ.val
          = Multiset.filter (fun j : Fin n => j < i) Finset.univ.val :=
      Multiset.filter_congr (fun j _ => hP j)
    rw [hf]
    calc (Multiset.filter (fun j : Fin n => j < i) Finset.univ.val).card
        = (Finset.univ.filter (fun j : Fin n => j < i)).card := rfl
      _ = (Finset.Iio i).card := by
        congr 1
        ext j
        simp
      _ = (i : ℕ) := Fin.card_Iio i
  have hm : Multiset.map (fun j : Fin n => ν j - (j : ℂ)) Finset.univ.val
      = Multiset.map (fun j : Fin n => ν' j - (j : ℂ)) Finset.univ.val := by
    apply msetSep
    intro u
    rw [Multiset.map_map, Multiset.map_map]
    have e : ∀ μ : Fin n → ℂ, (Multiset.map ((fun x => u + x) ∘ fun j : Fin n => μ j - (j : ℂ))
        Finset.univ.val).prod = ∏ k : Fin n, (u - (k : ℂ) + μ k) := by
      intro μ
      rw [Finset.prod_eq_multiset_prod]
      congr 2
      funext k
      dsimp
      ring
    rw [e, e]
    exact hp u
  funext i
  have hmem : ν' i - (i : ℂ) ∈ Multiset.map (fun j : Fin n => ν j - (j : ℂ)) Finset.univ.val := by
    rw [hm]
    exact Multiset.mem_map.2 ⟨i, by simp, rfl⟩
  obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 hmem
  have h1 := key ν hν j
  have h2 := key ν' hν' i
  rw [← hm, ← hj, h1] at h2
  have hji : j = i := Fin.ext h2
  subst hji
  linear_combination hj
end

