module

public import Formalism.GradedWeylDivisibility.StatementD

@[expose] public section

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.BlockActTensor
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem ldtensor_blockAct_comp (K : Type*) [CommRing K] {S : Type*} {k n : ℕ}
    (g : S → Matrix (Fin k) (Fin k) K) (s : S) :
    (blockAct K (n := n) g).comp (blockEmb K (k := k) (n := n) s) =
      (blockEmb K s).comp (rowAct K (g s)) := by
  apply MvPolynomial.algHom_ext
  intro v
  set_option synthInstance.maxHeartbeats 100000 in
    simp [blockEmb, blockAct, rowAct, map_sum, rename_C]

theorem ldtensor_blockAct_blockEmb (K : Type*) [CommRing K] {S : Type*} {k n : ℕ}
    (g : S → Matrix (Fin k) (Fin k) K) (s : S) (F : MvPolynomial (Fin k × Fin n) K) :
    blockAct K g (blockEmb K s F) = blockEmb K s (rowAct K (g s) F) := by
  exact AlgHom.congr_fun (ldtensor_blockAct_comp K g s) F

theorem block_action_tensor : BlockActTensor := by
  intro R K _ _ _ S _ k n g
  refine ⟨fun s F => ldtensor_blockAct_blockEmb K g s F, ?_⟩
  intro M M' hMM' P hP
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨fun s => rowAct K (g s) (F s), fun s => hMM' s (F s) (hF s), ?_⟩
    rw [map_prod]
    exact Finset.prod_congr rfl (fun s _ => ldtensor_blockAct_blockEmb K g s (F s))
  | zero =>
    rw [map_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add (f := _)]
    exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [← algebraMap_smul K a x, map_smul, algebraMap_smul]
    exact Submodule.smul_mem _ a hx

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDbasisLemmas
section
open MvPolynomial

namespace Formalism.GradedWeylDivisibility

open scoped MonomialOrder

theorem ldbasis_linearIndependent {σ R ι : Type*} [CommRing R] (o : MonomialOrder σ)
    (v : ι → MvPolynomial σ R) (hinj : Function.Injective fun i => o.degree (v i))
    (hlc : ∀ i, o.leadingCoeff (v i) = 1) : LinearIndependent R v := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  by_contra hgi
  have htne : (s.filter fun j => g j ≠ 0).Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hgi⟩⟩
  obtain ⟨j, hj, hjmax⟩ :=
    (s.filter fun j => g j ≠ 0).exists_max_image (fun j => o.toSyn (o.degree (v j))) htne
  have hcoeff := congrArg (AddMonoidAlgebra.coeff · (o.degree (v j))) hsum
  rw [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, MvPolynomial.coeff_sum,
    Finset.sum_eq_single j] at hcoeff
  · rw [coeff_smul, smul_eq_mul] at hcoeff
    have hone : (v j).coeff (o.degree (v j)) = 1 := hlc j
    rw [hone, mul_one] at hcoeff
    exact (Finset.mem_filter.mp hj).2 hcoeff
  · intro k hk hkj
    rw [coeff_smul]
    by_cases hgk : g k = 0
    · rw [hgk, zero_smul]
    · have hle := hjmax k (Finset.mem_filter.mpr ⟨hk, hgk⟩)
      have hne : o.degree (v k) ≠ o.degree (v j) := fun h => hkj (hinj h)
      have hlt : o.toSyn (o.degree (v k)) < o.toSyn (o.degree (v j)) :=
        lt_of_le_of_ne hle (fun h => hne (o.toSyn.injective h))
      rw [o.coeff_eq_zero_of_lt hlt, smul_zero]
  · intro hj'
    exact absurd (Finset.mem_filter.mp hj).1 hj'

theorem ldbasis_sum_single_perm {r s : ℕ} (I : Fin s → Fin r) (σ : Equiv.Perm (Fin s)) :
    (∑ q : Fin s, (Pi.single (I (σ q)) 1 : Fin r → ℕ)) = ∑ p : Fin s, Pi.single (I p) 1 := by
  exact Equiv.sum_comp σ (fun p => (Pi.single (I p) 1 : Fin r → ℕ))

theorem ldbasis_initMinor_rowHom (R : Type*) [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n) :
    IsWeightedHomogeneous (rowW r n) (initMinor R (n := n) I hs) (∑ p : Fin s, Pi.single (I p) 1) := by
  unfold initMinor
  rw [Matrix.det_apply]
  apply IsWeightedHomogeneous.sum
  intro σ _
  have hprod : IsWeightedHomogeneous (rowW r n)
      (∏ i, (X (I (σ i), Fin.castLE hs i) : MvPolynomial (Fin r × Fin n) R))
      (∑ p, Pi.single (I p) 1) := by
    rw [← ldbasis_sum_single_perm I σ]
    exact IsWeightedHomogeneous.prod _ _ _ (fun i _ => isWeightedHomogeneous_X R (rowW r n) _)
  intro d hd
  apply hprod
  intro h0
  apply hd
  show AddMonoidAlgebra.coeff ((Equiv.Perm.sign σ) •
    ∏ i, (X (I (σ i), Fin.castLE hs i) : MvPolynomial (Fin r × Fin n) R)) d = 0
  rw [Units.smul_def, coeff_smul, h0, smul_zero]

theorem ldbasis_bidet_rowHom (R : Type*) [CommRing R] {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) :
    IsWeightedHomogeneous (rowW r n) (bideterminant R sz hsz I)
      (∑ k : Fin K, ∑ p : Fin (sz k), Pi.single (I k p) 1) := by
  unfold bideterminant
  exact IsWeightedHomogeneous.prod _ _ _ (fun k _ => ldbasis_initMinor_rowHom R (I k) (hsz k))

theorem ldbasis_rowWt_bidetExp {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) :
    rowWt (bidetExp sz hsz I) = ∑ k : Fin K, ∑ p : Fin (sz k), (Pi.single (I k p) 1 : Fin r → ℕ) := by
  classical
  funext a
  simp only [rowWt, rowDeg, bidetExp, Finsupp.finsetSum_apply, Finset.sum_apply,
    Finsupp.single_apply, Pi.single_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases h : I k p = a
  · subst h
    simp [Prod.ext_iff]
  · simp [Prod.ext_iff, h, Ne.symm h]

end Formalism.GradedWeylDivisibility
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDlatLemmas
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

lemma ldlat_rowAct_one {R : Type*} [CommRing R] {k n : ℕ} :
    rowAct R (n := n) (1 : Matrix (Fin k) (Fin k) R) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro v
  rw [rowAct, aeval_X, AlgHom.id_apply]
  rw [Finset.sum_eq_single v.1 (fun b _ hb => by simp [Matrix.one_apply_ne (Ne.symm hb)]) (by simp)]
  simp

lemma ldlat_rowAct_inv_left (h : RowActMul) {K : Type} [Field K] {k n : ℕ}
    (g : Matrix (Fin k) (Fin k) K) (hg : IsUnit g.det) (x : MvPolynomial (Fin k × Fin n) K) :
    rowAct K g (rowAct K g⁻¹ x) = x := by
  rw [← AlgHom.comp_apply, h K k n g g⁻¹, Matrix.nonsing_inv_mul g hg, ldlat_rowAct_one, AlgHom.id_apply]

lemma ldlat_rowAct_inv_right (h : RowActMul) {K : Type} [Field K] {k n : ℕ}
    (g : Matrix (Fin k) (Fin k) K) (hg : IsUnit g.det) (x : MvPolynomial (Fin k × Fin n) K) :
    rowAct K g⁻¹ (rowAct K g x) = x := by
  rw [← AlgHom.comp_apply, h K k n g⁻¹ g, Matrix.mul_nonsing_inv g hg, ldlat_rowAct_one, AlgHom.id_apply]

lemma ldlat_map_bidet {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {r n K : ℕ}
    (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r) :
    map φ (bideterminant R sz hsz I) = bideterminant S sz hsz I := by
  unfold bideterminant initMinor
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [show (map φ : MvPolynomial (Fin r × Fin n) R → _) = ((map φ : MvPolynomial _ R →+* MvPolynomial _ S)) from rfl,
    RingHom.map_det]
  congr 1
  ext p q
  simp [RingHom.mapMatrix_apply]

lemma ldlat_isWH_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {σ M : Type*}
    [AddCommMonoid M] {w : σ → M} {f : MvPolynomial σ R} {μ : M}
    (hf : IsWeightedHomogeneous w f μ) : IsWeightedHomogeneous w (map φ f) μ := by
  intro m hm
  apply hf
  intro h0
  apply hm
  rw [coeff_map, h0, map_zero]

lemma ldlat_linInd_field {F K : Type*} [Field F] [Field K] [Algebra F K] {σ ι : Type*}
    {v : ι → MvPolynomial σ F} (hv : LinearIndependent F v) :
    LinearIndependent K (fun i => map (algebraMap F K) (v i)) := by
  rw [linearIndependent_iff'] at hv ⊢
  intro s c hsum i hi
  let B := Module.Free.chooseBasis F K
  apply B.ext_elem
  intro j
  have key : ∑ i ∈ s, (B.repr (c i) j) • v i = 0 := by
    ext m
    have h1 := congrArg (AddMonoidAlgebra.coeff · m) hsum
    simp only [coeff_sum, coeff_smul, coeff_map, smul_eq_mul] at h1 ⊢
    change _ = 0 at h1 ⊢
    have h2 := congrArg (fun x => B.repr x j) h1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zero, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.coe_zero,
      Pi.zero_apply] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm (c i), ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  have := hv s (fun i => B.repr (c i) j) key i hi
  simpa using this

lemma ldlat_linInd_base {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    (hinj : Function.Injective (algebraMap R K)) {σ ι : Type*} {b : ι → MvPolynomial σ R}
    (hb : LinearIndependent R b) : LinearIndependent K (fun i => map (algebraMap R K) (b i)) := by
  letI : Algebra (FractionRing R) K := (IsFractionRing.lift hinj).toAlgebra
  have h1 : LinearIndependent R (fun i => map (algebraMap R (FractionRing R)) (b i)) := by
    have := hb.map' (mapAlgHom (Algebra.ofId R (FractionRing R))).toLinearMap (by
      rw [LinearMap.ker_eq_bot]
      intro x y hxy
      exact map_injective _ (IsFractionRing.injective R (FractionRing R)) hxy)
    exact this
  have h2 : LinearIndependent (FractionRing R) (fun i => map (algebraMap R (FractionRing R)) (b i)) :=
    (LinearIndependent.iff_fractionRing R (FractionRing R)).mp h1
  have h3 := ldlat_linInd_field (K := K) h2
  have hc : (algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R)) = algebraMap R K := by
    ext r
    simp [RingHom.algebraMap_toAlgebra, IsFractionRing.lift_algebraMap]
  convert h3 using 2 with i
  rw [map_map, hc]

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDrowLemmas
section
open MvPolynomial Finset

noncomputable section

namespace Formalism.GradedWeylDivisibility

lemma ldrow_rowAct_diag_eq {R : Type*} [CommRing R] {k n : ℕ} (t : Fin k → R) :
    rowAct R (n := n) (Matrix.diagonal t) = aeval fun v : Fin k × Fin n => C (t v.1) * X v := by
  unfold rowAct
  congr 1
  funext v
  simp [Matrix.diagonal_apply, apply_ite C, ite_mul]

lemma ldrow_prod_rowDeg {R : Type*} [CommRing R] {k n : ℕ} (t : Fin k → R) (u : Fin k × Fin n →₀ ℕ) :
    (u.prod fun v e => t v.1 ^ e) = ∏ a : Fin k, t a ^ rowDeg u a := by
  classical
  rw [Finsupp.prod_fintype _ _ (fun v => pow_zero _), Fintype.prod_prod_type]
  refine Finset.prod_congr rfl (fun a _ => ?_)
  show ∏ y, t a ^ u (a, y) = _
  rw [Finset.prod_pow_eq_pow_sum]
  rfl

lemma ldrow_aeval_monomial {R : Type*} [CommRing R] {k n : ℕ} (t : Fin k → R)
    (u : Fin k × Fin n →₀ ℕ) (c : R) :
    aeval (fun v : Fin k × Fin n => C (t v.1) * X v) (monomial u c) =
      monomial u (c * ∏ a : Fin k, t a ^ rowDeg u a) := by
  rw [aeval_monomial, monomial_eq]
  simp only [mul_pow, Finsupp.prod_mul]
  have hC : (u.prod fun v e => (C (t v.1) : MvPolynomial (Fin k × Fin n) R) ^ e) =
      C (∏ a : Fin k, t a ^ rowDeg u a) := by
    rw [← ldrow_prod_rowDeg]
    simp only [Finsupp.prod, map_prod, map_pow]
  rw [hC, algebraMap_eq, map_mul]
  ring

lemma ldrow_coeff_rowAct_diag {R : Type*} [CommRing R] {k n : ℕ} (t : Fin k → R)
    (f : MvPolynomial (Fin k × Fin n) R) (m : Fin k × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (rowAct R (Matrix.diagonal t) f) m = AddMonoidAlgebra.coeff f m * ∏ a : Fin k, t a ^ rowDeg m a := by
  rw [ldrow_rowAct_diag_eq]
  induction f using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [ldrow_aeval_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h
      rfl
    · simp
  | add p q hp hq =>
    rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, add_mul]

lemma ldrow_weight_rowW {k n : ℕ} (m : Fin k × Fin n →₀ ℕ) (a : Fin k) :
    Finsupp.weight (rowW k n) m a = rowDeg m a := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype m (fun i c => c • rowW k n i) (fun i => zero_smul ℕ _),
    Finset.sum_apply,
    Fintype.sum_prod_type]
  unfold rowDeg
  rw [Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl (fun s _ => ?_)
    simp [rowW]
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro s _
    simp [rowW, Pi.single_apply, Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_univ a) h

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaLTwMem
section
open MvPolynomial

namespace Formalism.GradedWeylDivisibility

theorem nabla_twist_mem : NablaLTwMem := by
  intro R K _ _ _ m lam g hg F
  have hd : g.det ≠ 0 := hg.ne_zero
  unfold nablaLTw nablaL
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨G, hG, rfl⟩
    rw [Submodule.mem_comap] at hG
    change g.det ^ lam (Fin.last m) • rowAct K g (g.det ^ (-(lam (Fin.last m))) • G) ∈ _
    rw [map_smul, smul_smul, ← zpow_add₀ hd, add_neg_cancel, zpow_zero, one_smul]
    exact hG
  · intro hF
    refine ⟨g.det ^ (lam (Fin.last m)) • F, ?_, ?_⟩
    · rw [Submodule.mem_comap]
      change rowAct K g (g.det ^ (lam (Fin.last m)) • F) ∈ _
      rw [map_smul]
      exact hF
    · change g.det ^ (-(lam (Fin.last m))) • g.det ^ (lam (Fin.last m)) • F = F
      rw [smul_smul, ← zpow_add₀ hd, neg_add_cancel, zpow_zero, one_smul]

end Formalism.GradedWeylDivisibility
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaLTwist
section
open MvPolynomial

namespace Formalism.GradedWeylDivisibility

theorem ldtwist_map_rowAct {K L : Type*} [CommRing K] [CommRing L] (φ : K →+* L) {k n : ℕ}
    (g : Matrix (Fin k) (Fin k) K) (F : MvPolynomial (Fin k × Fin n) K) :
    map φ (rowAct K g F) = rowAct L (g.map φ) (map φ F) := by
  induction F using MvPolynomial.induction_on
  · rename_i a
    simp [rowAct]
  · rename_i p q hp hq
    simp only [map_add (f := _), hp, hq]
  · rename_i p v hp
    simp only [map_mul, hp]
    congr 1
    simp [rowAct, Matrix.map_apply]

end Formalism.GradedWeylDivisibility
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.RowActMul
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem row_action_mul : RowActMul := by
  intro R _ k n g h
  apply MvPolynomial.algHom_ext
  intro v
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [AlgHom.comp_apply, rowAct, aeval_X, map_sum, map_mul, aeval_C, Matrix.mul_apply,
    MvPolynomial.algebraMap_eq, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.SSIdxFinite
section
open MvPolynomial

namespace Formalism.GradedWeylDivisibility

theorem ldbasis_ssIdx_subset_Iic (k n : ℕ) (ν : Fin n → ℕ) :
    ssIdx k n ν ⊆ Set.Iic (Finsupp.equivFunOnFinite.symm (fun v : Fin k × Fin n => ν v.2)) := by
  intro m hm
  simp only [ssIdx, Set.mem_setOf_eq] at hm
  rw [Set.mem_Iic]
  intro v
  obtain ⟨a, t⟩ := v
  show m (a, t) ≤ ν t
  rw [← hm.2 t]
  exact Finset.single_le_sum (f := fun a' => m (a', t)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)

theorem semistandard_index_finite : SSIdxFinite := by
  intro k n ν
  exact (Set.finite_Iic _).subset (ldbasis_ssIdx_subset_Iic k n ν)

end Formalism.GradedWeylDivisibility
end

