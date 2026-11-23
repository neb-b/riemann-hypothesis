module

public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0012
public import Formalism.GradedWeylDivisibility.StatementD

@[expose] public section

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaLBasis
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem nablaLBasis_of (h : RowActMul) : NablaLBasis := by
  intro R K _ _ _ _ hinj k n ν ι b μ hb g hg
  have hid : ∀ x : MvPolynomial (Fin k × Fin n) K, rowAct K (1 : Matrix (Fin k) (Fin k) K) x = x := by
    intro x
    have e1 : rowAct K (n := n) (1 : Matrix (Fin k) (Fin k) K) = AlgHom.id K _ := by
      apply MvPolynomial.algHom_ext
      intro v
      simp only [rowAct, aeval_X, AlgHom.coe_id, id_eq, Matrix.one_apply]
      rw [Finset.sum_eq_single v.1]
      · simp
      · intro c _ hc
        simp [Ne.symm hc]
      · simp
    rw [e1]
    rfl
  have hinvA : ∀ A : Matrix (Fin k) (Fin k) K, IsUnit A.det → ∀ x : MvPolynomial (Fin k × Fin n) K,
      rowAct K A (rowAct K A⁻¹ x) = x ∧ rowAct K A⁻¹ (rowAct K A x) = x := by
    intro A hA x
    have e1 := congrArg (fun F => F x) (h K k n A A⁻¹)
    have e2 := congrArg (fun F => F x) (h K k n A⁻¹ A)
    simp only [AlgHom.comp_apply] at e1 e2
    rw [Matrix.nonsing_inv_mul A hA] at e1
    rw [Matrix.mul_nonsing_inv A hA] at e2
    exact ⟨e1.trans (hid x), e2.trans (hid x)⟩
  have hφinj : Function.Injective (map (algebraMap R K) : MvPolynomial (Fin k × Fin n) R → _) :=
    MvPolynomial.map_injective _ hinj
  let L : MvPolynomial (Fin k × Fin n) R →ₗ[R] MvPolynomial (Fin k × Fin n) K :=
    ((rowAct K g⁻¹).toLinearMap.restrictScalars R).comp (mapAlgHom (Algebra.ofId R K)).toLinearMap
  have hL : ∀ p, L p = rowAct K g⁻¹ (map (algebraMap R K) p) := fun p => rfl
  have hLinj : Function.Injective L := by
    intro p q hpq
    rw [hL, hL] at hpq
    have e := congrArg (rowAct K g) hpq
    rw [(hinvA g hg _).1, (hinvA g hg _).1] at e
    exact hφinj e
  refine ⟨?_, ?_⟩
  · exact hb.1.map' L (LinearMap.ker_eq_bot.mpr hLinj)
  · have e1 : Set.range (fun i => rowAct K g⁻¹ (map (algebraMap R K) (b i))) = L '' Set.range b := by
      rw [← Set.range_comp]
      rfl
    rw [e1, ← Submodule.map_span, hb.2.1]
    ext F
    unfold nablaL
    rw [Submodule.mem_map, Submodule.mem_comap, Submodule.mem_map]
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p, hp, ?_⟩
      show map (algebraMap R K) p = rowAct K g (L p)
      rw [hL, (hinvA g hg _).1]
    · rintro ⟨p, hp, hpF⟩
      refine ⟨p, hp, ?_⟩
      have e : map (algebraMap R K) p = rowAct K g F := hpF
      rw [hL, e, (hinvA g hg _).2]

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaLKBasis
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

lemma span_map_weightBasis_eq_dualWeyl {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] {k n : ℕ}
    {ν : Fin n → ℕ} {ι : Type} {b : ι → MvPolynomial (Fin k × Fin n) R} {μ : ι → (Fin k → ℕ)}
    (hb : IsWeightBasis R k n ν b μ) :
    Submodule.span K (Set.range fun i => map (algebraMap R K) (b i)) = dualWeyl K k n ν := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hi : b i ∈ dualWeyl R k n ν := hb.2.1 ▸ Submodule.subset_span ⟨i, rfl⟩
    exact dualWeylMap R K (algebraMap R K) k n ν (b i) hi
  · rw [standardMonomialSpanDomain K k n ν, Submodule.span_le]
    rintro f ⟨K', sz, hsz, I, hsh, rfl⟩
    rw [← ldlat_map_bidet (algebraMap R K)]
    have hmem : bideterminant R sz hsz I ∈ Submodule.span R (Set.range b) := by
      rw [hb.2.1, ← hsh]
      exact bidetMem R k n K' sz hsz I
    have h1 := Submodule.mem_map_of_mem (f := (mapAlgHom (Algebra.ofId R K)).toLinearMap) hmem
    rw [Submodule.map_span, ← Set.range_comp] at h1
    exact Submodule.span_le_restrictScalars R K _ h1

theorem nablaLKBasis_of (h1 : RowActMul) (_h2 : SSBasis) : NablaLKBasis := by
  intro R K _ _ _ _ hinj k n ν ι b μ hb g hg
  have hinv : ∀ (A : Matrix (Fin k) (Fin k) K) (P : MvPolynomial (Fin k × Fin n) K),
      P ∈ dualWeyl K k n ν → rowAct K A P ∈ dualWeyl K k n ν := by
    intro A P hP
    unfold dualWeyl at hP ⊢
    rw [Submodule.mem_inf] at hP ⊢
    obtain ⟨hP1, hP2⟩ := hP
    refine ⟨?_, ?_⟩
    · rw [mem_weightedHomogeneousSubmodule] at hP1 ⊢
      have hXw : ∀ v : Fin k × Fin n,
          IsWeightedHomogeneous (colW k n) (rowAct K A (X v)) (colW k n v) := by
        intro v
        simp only [rowAct, aeval_X]
        apply IsWeightedHomogeneous.sum
        intro b _
        have h := (isWeightedHomogeneous_C (colW k n) (A v.1 b)).mul
          (isWeightedHomogeneous_X K (colW k n) (b, v.2))
        simpa [colW] using h
      set_option synthInstance.maxHeartbeats 100000 in
        rw [P.as_sum, map_sum]
      apply IsWeightedHomogeneous.sum
      intro d hd
      rw [← hP1 (mem_support_iff.mp hd), monomial_eq, map_mul, map_finsuppProd, Finsupp.weight_apply]
      simp only [map_pow]
      have hC : rowAct K A (C (AddMonoidAlgebra.coeff P d) : MvPolynomial (Fin k × Fin n) K) = C (AddMonoidAlgebra.coeff P d) := by
        simp [rowAct]
      rw [hC]
      have h := (isWeightedHomogeneous_C (colW k n) (AddMonoidAlgebra.coeff P d)).mul
        (IsWeightedHomogeneous.prod d.support _ _ fun v _ => (hXw v).pow (d v))
      simpa [Finsupp.prod, Finsupp.sum] using h
    · simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hP2 ⊢
      intro l j hlj
      have e := hP2 l j hlj
      simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply] at e ⊢
      let A' : MvPolynomial (Option (Fin k × Fin n)) K →ₐ[K] MvPolynomial (Option (Fin k × Fin n)) K :=
        aeval fun o => o.elim (X none) (fun v => ∑ b : Fin k, C (A v.1 b) * X (some (b, v.2)))
      have h1 : (colAddGen K l j).comp (rowAct K A) = A'.comp (colAddGen K (r := k) l j) := by
        apply MvPolynomial.algHom_ext
        intro v
        by_cases hv : v.2 = j
        · simp [A', colAddGen, rowAct, hv, Finset.mul_sum, Finset.sum_add_distrib, mul_add,
            mul_left_comm]
        · simp [A', colAddGen, rowAct, hv]
      have h2 : (rename (R := K) (some : Fin k × Fin n → Option (Fin k × Fin n))).comp (rowAct K A) =
          A'.comp (rename some) := by
        apply MvPolynomial.algHom_ext
        intro v
        simp [A', rowAct]
      have e1 := congrArg (fun Φ => Φ P) h1
      have e2 := congrArg (fun Φ => Φ P) h2
      simp only [AlgHom.comp_apply] at e1 e2
      rw [e1, e2, ← map_sub, e, map_zero]
  have hli := ldlat_linInd_base (K := K) hinj hb.1
  refine ⟨hli.map' (rowAct K g⁻¹).toLinearMap (LinearMap.ker_eq_bot.mpr fun x y hxy => ?_), ?_⟩
  · have e := congrArg (rowAct K g) hxy
    simpa [ldlat_rowAct_inv_left h1 g hg] using e
  · have e1 : Set.range (fun i => rowAct K g⁻¹ (map (algebraMap R K) (b i))) =
        (rowAct K g⁻¹).toLinearMap '' Set.range (fun i => map (algebraMap R K) (b i)) := by
      rw [← Set.range_comp]
      rfl
    rw [e1, ← Submodule.map_span, span_map_weightBasis_eq_dualWeyl hb]
    apply le_antisymm
    · intro x hx
      rw [Submodule.mem_map] at hx
      obtain ⟨P, hP, rfl⟩ := hx
      exact hinv g⁻¹ P hP
    · intro P hP
      rw [Submodule.mem_map]
      exact ⟨rowAct K g P, hinv g P hP, ldlat_rowAct_inv_right h1 g hg P⟩

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaLLe
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem nabla_weight_le : NablaLLe := by
  intro R K _ _ _ k n ν g hg F hF
  unfold nablaL at hF
  rw [Submodule.mem_comap, Submodule.mem_map] at hF
  obtain ⟨G, hG, hGF⟩ := hF
  have hGF' : map (algebraMap R K) G = rowAct K g F := hGF

  have hGK : map (algebraMap R K) G ∈ dualWeyl K k n ν := by
    unfold dualWeyl at hG ⊢
    rw [Submodule.mem_inf] at hG ⊢
    obtain ⟨hG1, hG2⟩ := hG
    refine ⟨?_, ?_⟩
    · rw [mem_weightedHomogeneousSubmodule] at hG1 ⊢
      intro d hd
      apply hG1
      intro h0
      apply hd
      rw [coeff_map, h0, map_zero]
    · simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hG2 ⊢
      intro l j hlj
      have e := hG2 l j hlj
      have hc : ∀ p : MvPolynomial (Fin k × Fin n) R,
          colAddGen K l j (map (algebraMap R K) p) = map (algebraMap R K) (colAddGen R l j p) := by
        intro p
        induction p using MvPolynomial.induction_on
        · rename_i a
          simp [colAddGen]
        · rename_i p q hp hq
          simp only [map_add (f := _), hp, hq]
        · rename_i p v hp
          simp only [map_mul, hp]
          congr 1
          simp only [colAddGen, map_X, aeval_X]
          split_ifs <;> simp
      simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply] at e ⊢
      rw [hc, ← map_rename, ← map_sub, e, map_zero]

  have hinv : ∀ (A : Matrix (Fin k) (Fin k) K) (P : MvPolynomial (Fin k × Fin n) K),
      P ∈ dualWeyl K k n ν → rowAct K A P ∈ dualWeyl K k n ν := by
    intro A P hP
    unfold dualWeyl at hP ⊢
    rw [Submodule.mem_inf] at hP ⊢
    obtain ⟨hP1, hP2⟩ := hP
    refine ⟨?_, ?_⟩
    · rw [mem_weightedHomogeneousSubmodule] at hP1 ⊢
      have hXw : ∀ v : Fin k × Fin n,
          IsWeightedHomogeneous (colW k n) (rowAct K A (X v)) (colW k n v) := by
        intro v
        simp only [rowAct, aeval_X]
        apply IsWeightedHomogeneous.sum
        intro b _
        have h := (isWeightedHomogeneous_C (colW k n) (A v.1 b)).mul
          (isWeightedHomogeneous_X K (colW k n) (b, v.2))
        simpa [colW] using h
      set_option synthInstance.maxHeartbeats 100000 in
        rw [P.as_sum, map_sum]
      apply IsWeightedHomogeneous.sum
      intro d hd
      rw [← hP1 (mem_support_iff.mp hd), monomial_eq, map_mul, map_finsuppProd, Finsupp.weight_apply]
      simp only [map_pow]
      have hC : rowAct K A (C (AddMonoidAlgebra.coeff P d) : MvPolynomial (Fin k × Fin n) K) = C (AddMonoidAlgebra.coeff P d) := by
        simp [rowAct]
      rw [hC]
      have h := (isWeightedHomogeneous_C (colW k n) (AddMonoidAlgebra.coeff P d)).mul
        (IsWeightedHomogeneous.prod d.support _ _ fun v _ => (hXw v).pow (d v))
      simpa [Finsupp.prod, Finsupp.sum] using h
    · simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hP2 ⊢
      intro l j hlj
      have e := hP2 l j hlj
      simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply] at e ⊢
      let A' : MvPolynomial (Option (Fin k × Fin n)) K →ₐ[K] MvPolynomial (Option (Fin k × Fin n)) K :=
        aeval fun o => o.elim (X none) (fun v => ∑ b : Fin k, C (A v.1 b) * X (some (b, v.2)))
      have h1 : (colAddGen K l j).comp (rowAct K A) = A'.comp (colAddGen K (r := k) l j) := by
        apply MvPolynomial.algHom_ext
        intro v
        by_cases hv : v.2 = j
        · simp [A', colAddGen, rowAct, hv, Finset.mul_sum, Finset.sum_add_distrib, mul_add,
            mul_left_comm]
        · simp [A', colAddGen, rowAct, hv]
      have h2 : (rename (R := K) (some : Fin k × Fin n → Option (Fin k × Fin n))).comp (rowAct K A) =
          A'.comp (rename some) := by
        apply MvPolynomial.algHom_ext
        intro v
        simp [A', rowAct]
      have e1 := congrArg (fun Φ => Φ P) h1
      have e2 := congrArg (fun Φ => Φ P) h2
      simp only [AlgHom.comp_apply] at e1 e2
      rw [e1, e2, ← map_sub, e, map_zero]
  have hid : rowAct K (1 : Matrix (Fin k) (Fin k) K) F = F := by
    have e1 : rowAct K (n := n) (1 : Matrix (Fin k) (Fin k) K) = AlgHom.id K _ := by
      apply MvPolynomial.algHom_ext
      intro v
      simp only [rowAct, aeval_X, AlgHom.coe_id, id_eq, Matrix.one_apply]
      rw [Finset.sum_eq_single v.1]
      · simp
      · intro c _ hc
        simp [Ne.symm hc]
      · simp
    rw [e1]
    rfl
  have e := congrArg (fun Φ => Φ F) (row_action_mul K k n g⁻¹ g)
  simp only [AlgHom.comp_apply] at e
  rw [Matrix.mul_nonsing_inv g hg, hid] at e
  rw [← e, ← hGF']
  exact hinv _ _ hGK

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.RowActDiagWeight
section
open MvPolynomial Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem row_action_diagonal_weight : RowActDiagWeight := by
  intro R _ k n t μ f hf
  have hX : (rowAct R (n := n) (Matrix.diagonal t)) = aeval fun v : Fin k × Fin n => C (t v.1) * X v := by
    unfold rowAct
    congr 1
    funext v
    rw [Finset.sum_eq_single v.1]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  have hwt : ∀ (d : Fin k × Fin n →₀ ℕ) (a : Fin k), Finsupp.weight (rowW k n) d a = ∑ s, d (a, s) := by
    intro d a
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
      Fintype.sum_prod_type]
    simp only [rowW, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  conv_lhs => rw [f.as_sum]
  conv_rhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw : Finsupp.weight (rowW k n) d = μ := hf (mem_support_iff.mp hd)
  have hp : (d.prod fun v e => t v.1 ^ e) = ∏ a, t a ^ μ a := by
    rw [← hw, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [hwt]
    dsimp only
    rw [Finset.prod_pow_eq_pow_sum]
  rw [hX, aeval_monomial, ← hp, smul_eq_C_mul, monomial_eq]
  simp only [mul_pow, Finsupp.prod_mul, map_finsuppProd, map_pow, MvPolynomial.algebraMap_eq]
  ring

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.SSBasis
section
open MvPolynomial

namespace Formalism.GradedWeylDivisibility

open scoped MonomialOrder

theorem semistandard_basis : SSBasis := by
  intro R _ _ k n ν
  have hex : ∀ m : ssIdx k n ν, ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ i, sz i ≤ n)
      (I : ∀ i, Fin (sz i) → Fin k),
      shapeDeg sz = ν ∧ (∀ i, StrictMono (I i)) ∧ bidetExp sz hsz I = m.1 := fun m =>
    sSYTExists k n ν m.1 m.2.2 m.2.1
  choose K sz hsz I hshape hmono hexp using hex
  set b : ssIdx k n ν → MvPolynomial (Fin k × Fin n) R := fun m => bideterminant R (sz m) (hsz m) (I m) with hb
  have hdeg : ∀ m, (colLex k n).degree (b m) = m.1 := fun m =>
    (column_lex_bideterminant R k n (K m) (sz m) (hsz m) (I m) (hmono m)).1.trans (hexp m)
  have hlc : ∀ m, (colLex k n).leadingCoeff (b m) = 1 := fun m =>
    (column_lex_bideterminant R k n (K m) (sz m) (hsz m) (I m) (hmono m)).2
  have hmem : ∀ m, b m ∈ dualWeyl R k n ν := fun m => by
    have := bidetMem R k n (K m) (sz m) (hsz m) (I m)
    rw [hshape m] at this
    exact this
  refine ⟨b, ⟨?_, ?_, ?_⟩, fun m => ⟨hdeg m, hlc m, K m, sz m, hsz m, I m, hshape m, hmono m, rfl⟩⟩
  ·
    refine ldbasis_linearIndependent (colLex k n) b ?_ hlc
    intro m m' h
    exact Subtype.ext ((hdeg m).symm.trans (h.trans (hdeg m')))
  ·
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨m, rfl⟩
      exact hmem m
    · suffices key : ∀ d : (colLex k n).syn, ∀ f ∈ dualWeyl R k n ν,
          (colLex k n).toSyn ((colLex k n).degree f) = d → f ∈ Submodule.span R (Set.range b) by
        intro f hf
        exact key _ f hf rfl
      intro d
      induction d using WellFoundedLT.induction with
      | _ d ih =>
        intro f hf hd
        by_cases hf0 : f = 0
        · rw [hf0]; exact Submodule.zero_mem _
        set m := (colLex k n).degree f with hm
        have hint : Interlaced m := leadInterlaced R k n ν f hf hf0
        have hcol : ∀ t : Fin n, ∑ a : Fin k, m (a, t) = ν t :=
          colSums R k n ν f hf m (((colLex k n).degree_mem_support_iff f).mpr hf0)
        set mi : ssIdx k n ν := ⟨m, hint, hcol⟩ with hmi
        have hbS : b mi ∈ Submodule.span R (Set.range b) := Submodule.subset_span ⟨mi, rfl⟩
        set f' := f - (colLex k n).leadingCoeff f • b mi with hf'
        have hf'mem : f' ∈ dualWeyl R k n ν :=
          Submodule.sub_mem _ hf (Submodule.smul_mem _ _ (hmem mi))
        have hdecomp : f = f' + (colLex k n).leadingCoeff f • b mi := by
          rw [hf']; abel
        rw [hdecomp]
        refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ hbS)
        by_cases h0 : f' = 0
        · rw [h0]; exact Submodule.zero_mem _
        have hlt := lcassem_sub_lt (colLex k n) (f := f) (g := b mi) (hdeg mi) (hlc mi) h0
        exact ih _ (hd ▸ hlt) f' hf'mem rfl
  ·
    intro m
    show IsWeightedHomogeneous (rowW k n) (bideterminant R (sz m) (hsz m) (I m)) (rowWt m.1)
    rw [← hexp m, ldbasis_rowWt_bidetExp]
    exact ldbasis_bidet_rowHom R (sz m) (hsz m) (I m)

end Formalism.GradedWeylDivisibility
end

