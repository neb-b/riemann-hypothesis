module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1133
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1342
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousConjFin
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0019

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.ExistsQdetEqPowAddSumCoeffMemSpan
section
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct

private theorem UpperTheory.coeff_mem_span_range_of_polynomial_eq {A : Type} [Ring A] [Algebra ℂ A] (f : ℂ → A) (q : ℕ → A)
    (m : ℕ) (hf : ∀ u : ℂ, f u = ∑ k ∈ Finset.range m, u ^ k • q k) :
    ∀ k < m, q k ∈ Submodule.span ℂ (Set.range f) := by
  intro k hk
  set V : Matrix (Fin m) (Fin m) ℂ := Matrix.vandermonde (fun i : Fin m => ((i : ℕ) : ℂ)) with hV
  have hdet : IsUnit V.det := by
    rw [isUnit_iff_ne_zero, hV, Matrix.det_vandermonde_ne_zero_iff]
    intro i j hij
    exact Fin.ext (by simpa using hij)
  have hWV : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V hdet
  have h1 : ∀ i : Fin m, f ((i : ℕ) : ℂ) = ∑ j : Fin m, V i j • q j := by
    intro i
    rw [hf, ← Fin.sum_univ_eq_sum_range (fun j => ((i : ℕ) : ℂ) ^ j • q j) m]
    simp [hV, Matrix.vandermonde_apply]
  have key : ∑ i : Fin m, V⁻¹ ⟨k, hk⟩ i • f ((i : ℕ) : ℂ) = q k := by
    simp_rw [h1, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    have h2 : ∀ j : Fin m, ∑ i : Fin m, V⁻¹ ⟨k, hk⟩ i * V i j = (V⁻¹ * V) ⟨k, hk⟩ j := by
      intro j
      rw [Matrix.mul_apply]
    simp_rw [h2, hWV, Matrix.one_apply]
    simp
  rw [← key]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))

private theorem UpperTheory.coeff_mul_add_natDegree_le {A : Type} [Ring A] {p q : Polynomial A} {m k : ℕ}
    (hp : p.natDegree ≤ m) (hq : q.natDegree ≤ k) :
    (p * q).coeff (m + k) = p.coeff m * q.coeff k := by
  rw [Polynomial.coeff_mul]
  refine Finset.sum_eq_single (m, k) ?_ ?_
  · rintro ⟨i, j⟩ h₁ h₂
    have h₃ : i + j = m + k := Finset.HasAntidiagonal.mem_antidiagonal.mp h₁
    by_cases H : m < i
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp H), zero_mul]
    · have hj : k < j := by
        by_contra H'
        apply h₂
        simp only [Prod.mk.injEq]
        omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hq hj), mul_zero]
  · intro h
    exact (h (by simp)).elim

private theorem UpperTheory.natDegree_list_prod_le_and_leading_coeff {A : Type} [Ring A] (l : List (Polynomial A))
    (hl : ∀ p ∈ l, p.natDegree ≤ 1) :
    l.prod.natDegree ≤ l.length ∧ l.prod.coeff l.length = (l.map fun p => p.coeff 1).prod := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp : p.natDegree ≤ 1 := hl p (by simp)
    obtain ⟨h1, h2⟩ := ih (fun q hq => hl q (by simp [hq]))
    refine ⟨?_, ?_⟩
    · rw [List.prod_cons, List.length_cons]
      calc (p * l.prod).natDegree ≤ p.natDegree + l.prod.natDegree := Polynomial.natDegree_mul_le
        _ ≤ 1 + l.length := add_le_add hp h1
        _ = l.length + 1 := Nat.add_comm _ _
    · rw [List.prod_cons, List.length_cons, List.map_cons, List.prod_cons, ← h2,
        Nat.add_comm l.length 1, UpperTheory.coeff_mul_add_natDegree_le hp h1]

theorem UpperTheory.exists_qdet_eq_pow_add_sum_coeff_mem_span :
    ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A), ∃ c : ℕ → A, (∀ k, c k ∈ Submodule.span ℂ (Set.range (Formalism.REAL.qdet X))) ∧ ∀ u : ℂ, Formalism.REAL.qdet X u = algebraMap ℂ A (u ^ n) + ∑ k ∈ Finset.range n, u ^ k • c k := by
  intro A _ _ n X
  classical
  let F : Fin n → Fin n → Polynomial A := fun a b =>
    (if a = b then Polynomial.X - Polynomial.C (algebraMap ℂ A ((b : ℕ) : ℂ)) else 0) +
      Polynomial.C (X a b)
  let Q : Equiv.Perm (Fin n) → Polynomial A := fun σ => (List.ofFn fun k => F (σ k) k).prod
  let P : Polynomial A :=
    ∑ σ : Equiv.Perm (Fin n), Polynomial.C (((Equiv.Perm.sign σ : ℤ) : A)) * Q σ
  have hF : ∀ a b, (F a b).natDegree ≤ 1 := by
    intro a b
    simp only [F]
    split_ifs
    · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · exact Polynomial.natDegree_X_sub_C_le _
      · simp
    · simp
  have hF1 : ∀ a b, (F a b).coeff 1 = if a = b then 1 else 0 := by
    intro a b
    simp only [F]
    split_ifs <;> simp [Polynomial.coeff_X, Polynomial.coeff_C]
  have hQ : ∀ σ, (Q σ).natDegree ≤ n ∧ (Q σ).coeff n = if σ = 1 then 1 else 0 := by
    intro σ
    have h := UpperTheory.natDegree_list_prod_le_and_leading_coeff (List.ofFn fun k => F (σ k) k) (by
      intro p hp
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hp
      exact hF _ _)
    rw [List.length_ofFn] at h
    refine ⟨h.1, ?_⟩
    rw [h.2, List.map_ofFn]
    split_ifs with hs
    · subst hs
      apply List.prod_eq_one
      intro x hx
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
      simp [hF1]
    · obtain ⟨k, hk⟩ : ∃ k, σ k ≠ k := by
        by_contra hc
        push_neg at hc
        exact hs (Equiv.Perm.ext fun k => by simpa using hc k)
      apply List.prod_eq_zero
      exact List.mem_ofFn.mpr ⟨k, by simp [hF1, hk]⟩
  have hPdeg : P.natDegree ≤ n := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun σ _ => ?_)
    refine (Polynomial.natDegree_mul_le).trans ?_
    simpa using (hQ σ).1
  have hQ2 : ∀ σ, (Q σ).coeff n = if σ = 1 then 1 else 0 := fun σ => (hQ σ).2
  have hPn : P.coeff n = 1 := by
    simp only [P, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, hQ2]
    simp
  have heval : ∀ u : ℂ, Formalism.REAL.qdet X u = P.eval₂ (RingHom.id A) (algebraMap ℂ A u) := by
    intro u
    let ψ := Polynomial.eval₂RingHom' (RingHom.id A) (algebraMap ℂ A u)
      (fun a => Algebra.commute_algebraMap_right u a)
    show _ = ψ P
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [P, Q, map_sum, map_mul, map_list_prod, List.map_ofFn]
    simp only [Formalism.REAL.qdet, Formalism.REAL.qminor]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    congr 1
    · simp [ψ]
    · congr 1
      refine congrArg List.ofFn (funext fun k => ?_)
      simp only [Function.comp_apply, F, Formalism.REAL.Tm, ψ, id]
      split_ifs <;> simp [map_sub]
  have hterm : ∀ (u : ℂ) (i : ℕ),
      (RingHom.id A) (P.coeff i) * algebraMap ℂ A u ^ i = u ^ i • P.coeff i := by
    intro u i
    rw [RingHom.id_apply, ← map_pow, Algebra.smul_def, Algebra.commutes]
  refine ⟨P.coeff, ?_, ?_⟩
  · intro k
    by_cases hk : k < n + 1
    · refine UpperTheory.coeff_mem_span_range_of_polynomial_eq (Formalism.REAL.qdet X) P.coeff (n + 1) (fun u => ?_) k hk
      rw [heval, Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hPdeg)]
      exact Finset.sum_congr rfl (fun i _ => hterm u i)
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      exact Submodule.zero_mem _
  · intro u
    rw [heval, Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hPdeg), Finset.sum_range_succ,
      hPn, add_comm (∑ i ∈ Finset.range n, _)]
    congr 1
    · simp
    · exact Finset.sum_congr rfl (fun i _ => hterm u i)
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.FiniteDimensionalSpanAdjoinApplyOfCommutingAlgeb
section
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct

private theorem UpperTheory.adjoin_apply_mem_of_invariant_submodule {V : Type} [AddCommGroup V] [Module ℂ V]
    (g : Set (Module.End ℂ V)) (U : Submodule ℂ V) (hU : ∀ b ∈ g, ∀ u ∈ U, b u ∈ U) :
    ∀ z ∈ Algebra.adjoin ℂ g, ∀ u ∈ U, z u ∈ U := by
  intro z hz
  induction hz using Algebra.adjoin_induction with
  | mem x hx => exact hU x hx
  | algebraMap r =>
    intro u hu
    rw [Module.algebraMap_end_apply]
    exact U.smul_mem r hu
  | add x y _ _ hx hy =>
    intro u hu
    exact U.add_mem (hx u hu) (hy u hu)
  | mul x y _ _ hx hy =>
    intro u hu
    exact hx _ (hy u hu)

theorem UpperTheory.finiteDimensional_span_adjoin_apply_of_commuting_algebraic :
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (s : Set (Module.End ℂ V)) (v : V), (∀ a ∈ s, ∀ b ∈ s, a * b = b * a) → FiniteDimensional ℂ (Submodule.span ℂ s) → (∀ a ∈ s, ∃ P : Polynomial ℂ, P ≠ 0 ∧ Polynomial.aeval a P v = 0) →
        FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ V => z v) '' (Algebra.adjoin ℂ s : Subalgebra ℂ (Module.End ℂ V)))) := by
  intro V _ _ s v hcomm hfin hpoly
  classical
  let U : Set (Module.End ℂ V) → Submodule ℂ V := fun g =>
    Submodule.span ℂ ((fun z : Module.End ℂ V => z v) ''
      (Algebra.adjoin ℂ g : Subalgebra ℂ (Module.End ℂ V)))
  have hUinv : ∀ g : Set (Module.End ℂ V), ∀ b ∈ g, ∀ w ∈ U g, b w ∈ U g := by
    intro g b hb w hw
    have hle : U g ≤ (U g).comap b := by
      rw [Submodule.span_le]
      rintro _ ⟨z, hz, rfl⟩
      show b (z v) ∈ U g
      exact Submodule.subset_span ⟨b * z, Subalgebra.mul_mem _ (Algebra.subset_adjoin hb) hz, rfl⟩
    exact hle hw
  have hvU : ∀ g : Set (Module.End ℂ V), v ∈ U g :=
    fun g => Submodule.subset_span ⟨1, Subalgebra.one_mem _, rfl⟩
  have hind : ∀ t : Finset (Module.End ℂ V), (↑t : Set (Module.End ℂ V)) ⊆ s →
      FiniteDimensional ℂ (U ↑t) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro _
      have hle : U ↑(∅ : Finset (Module.End ℂ V)) ≤ Submodule.span ℂ {v} := by
        rw [Submodule.span_le]
        rintro _ ⟨z, hz, rfl⟩
        exact UpperTheory.adjoin_apply_mem_of_invariant_submodule _ _ (by simp) z hz v (Submodule.mem_span_singleton_self v)
      exact Submodule.finiteDimensional_of_le hle
    | insert a t hat ih =>
      intro hts
      rw [Finset.coe_insert, Set.insert_subset_iff] at hts
      haveI := ih hts.2
      obtain ⟨P, hP0, hPv⟩ := hpoly a hts.1
      set Q := Polynomial.C (P.leadingCoeff)⁻¹ * P with hQ
      have hQm : Q.Monic := Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one
        (inv_mul_cancel₀ (Polynomial.leadingCoeff_ne_zero.mpr hP0))
      have hac : ∀ z ∈ Algebra.adjoin ℂ (↑t : Set (Module.End ℂ V)), Commute a z := fun z hz =>
        Algebra.commute_of_mem_adjoin_of_forall_mem_commute hz
          (fun b hb => hcomm a hts.1 b (hts.2 hb))
      have hker : ∀ w ∈ U ↑t, Polynomial.aeval a Q w = 0 := by
        intro w hw
        have hle : U ↑t ≤ LinearMap.ker (Polynomial.aeval a Q) := by
          rw [Submodule.span_le]
          rintro _ ⟨z, hz, rfl⟩
          have hc : Commute z (Polynomial.aeval a Q) :=
            Algebra.commute_of_mem_adjoin_singleton_of_commute
              (Polynomial.aeval_mem_adjoin_singleton ℂ a) (hac z hz).symm
          show Polynomial.aeval a Q (z v) = 0
          rw [← Module.End.mul_apply, ← hc.eq, Module.End.mul_apply, hQ, map_mul,
            Polynomial.aeval_C, Module.End.mul_apply, hPv, map_zero, map_zero]
        exact hle hw
      have hred : ∀ w ∈ U ↑t, (a ^ Q.natDegree) w =
          -∑ j ∈ Finset.range Q.natDegree, Q.coeff j • (a ^ j) w := by
        intro w hw
        have h0 := hker w hw
        simp only [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, hQm.coeff_natDegree,
          one_smul, LinearMap.add_apply, LinearMap.sum_apply,
          LinearMap.smul_apply] at h0
        rw [eq_neg_iff_add_eq_zero, add_comm]
        simpa using h0
      let U' : Submodule ℂ V := ⨆ i : Fin Q.natDegree, (U ↑t).map (a ^ (i : ℕ))
      have hpow : ∀ j, ∀ w ∈ U ↑t, (a ^ j) w ∈ U' := by
        intro j
        induction j using Nat.strong_induction_on with
        | _ j ihj =>
          intro w hw
          by_cases hj : j < Q.natDegree
          · exact Submodule.mem_iSup_of_mem (⟨j, hj⟩ : Fin Q.natDegree)
              (Submodule.mem_map_of_mem hw)
          · have hsplit : (a ^ j) w = (a ^ (j - Q.natDegree)) ((a ^ Q.natDegree) w) := by
              rw [← Module.End.mul_apply, ← pow_add, Nat.sub_add_cancel (not_lt.mp hj)]
            set_option synthInstance.maxHeartbeats 100000 in
              rw [hsplit, hred w hw, map_neg, map_sum]
            refine U'.neg_mem (U'.sum_mem (fun i hi => ?_))
            rw [map_smul, ← Module.End.mul_apply, ← pow_add]
            refine U'.smul_mem _ (ihj _ ?_ w hw)
            have := Finset.mem_range.mp hi
            omega
      have hU'a : ∀ u ∈ U', a u ∈ U' := by
        intro u hu
        refine Submodule.iSup_induction _ (motive := fun u => a u ∈ U') hu (fun i x hx => ?_) ?_
          (fun x y hx hy => ?_)
        · obtain ⟨w, hw, rfl⟩ := hx
          show a ((a ^ (i : ℕ)) w) ∈ U'
          rw [← Module.End.mul_apply, ← pow_succ']
          exact hpow _ w hw
        · simp
        · show a (x + y) ∈ U'
          rw [map_add (f := _)]
          exact U'.add_mem hx hy
      have hU'b : ∀ b ∈ (↑t : Set (Module.End ℂ V)), ∀ u ∈ U', b u ∈ U' := by
        intro b hb u hu
        refine Submodule.iSup_induction _ (motive := fun u => b u ∈ U') hu (fun i x hx => ?_) ?_
          (fun x y hx hy => ?_)
        · obtain ⟨w, hw, rfl⟩ := hx
          show b ((a ^ (i : ℕ)) w) ∈ U'
          have hcb : Commute (a ^ (i : ℕ)) b := (hac b (Algebra.subset_adjoin hb)).pow_left _
          rw [← Module.End.mul_apply, ← hcb.eq, Module.End.mul_apply]
          exact hpow _ _ (hUinv _ b hb w hw)
        · simp
        · show b (x + y) ∈ U'
          rw [map_add (f := _)]
          exact U'.add_mem hx hy
      have hle : U ↑(insert a t) ≤ U' := by
        rw [Submodule.span_le]
        rintro _ ⟨z, hz, rfl⟩
        refine UpperTheory.adjoin_apply_mem_of_invariant_submodule _ U' ?_ z hz v ?_
        · intro b hb
          rw [Finset.coe_insert] at hb
          rcases hb with rfl | hb
          · exact hU'a
          · exact hU'b b hb
        · simpa using hpow 0 v (hvU _)
      exact Submodule.finiteDimensional_of_le hle
  obtain ⟨t, hts, -, hspan, -⟩ := Submodule.exists_finset_span_eq_linearIndepOn ℂ s
  haveI := hind t hts
  refine Submodule.finiteDimensional_of_le (S₂ := U ↑t) ?_
  apply Submodule.span_mono
  apply Set.image_mono
  intro z hz
  refine (Algebra.adjoin_le (fun x hx => ?_)) hz
  apply Algebra.span_le_adjoin ℂ
  rw [hspan]
  exact Submodule.subset_span hx
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.IsIntegralEvalOfMonicMulIsIntegral
section
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct

private theorem coeff_mem_subalgebra_of_eval_mem {R : Type} [CommRing R] [Algebra ℂ R] (S : Subalgebra ℂ R)
    (F : Polynomial R) (h : ∀ u : ℂ, F.eval (algebraMap ℂ R u) ∈ S) (j : ℕ) : F.coeff j ∈ S := by
  classical
  by_cases hj : F.natDegree + 1 ≤ j
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    exact S.zero_mem
  push_neg at hj
  let v : Fin (F.natDegree + 1) → ℂ := fun i => ((i : ℕ) : ℂ)
  have hv : Function.Injective v := fun a b hab => Fin.ext (by simpa [v] using hab)
  let V := Matrix.vandermonde v
  have hdet : IsUnit V.det := isUnit_iff_ne_zero.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hv)
  let c : Fin (F.natDegree + 1) → R := fun k => F.coeff k
  have hval : ∀ i, (V.map (algebraMap ℂ R) *ᵥ c) i = F.eval (algebraMap ℂ R (v i)) := by
    intro i
    rw [Polynomial.eval_eq_sum_range' (n := F.natDegree + 1) (by omega), ← Fin.sum_univ_eq_sum_range]
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.vandermonde_apply, map_pow, c, V]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hv2 : ∀ i, (V.map (algebraMap ℂ R) *ᵥ c) i ∈ S := fun i => (hval i) ▸ h _
  have hinv : (V⁻¹).map (algebraMap ℂ R) * V.map (algebraMap ℂ R) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul V hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hc : c = (V⁻¹).map (algebraMap ℂ R) *ᵥ (V.map (algebraMap ℂ R) *ᵥ c) := by
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hcj : F.coeff j = c ⟨j, hj⟩ := rfl
  rw [hcj, hc]
  generalize V.map (algebraMap ℂ R) *ᵥ c = w at hv2
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  exact S.sum_mem fun i _ => S.mul_mem (S.algebraMap_mem _) (hv2 i)

theorem UpperTheory.isIntegral_eval_of_monic_mul_isIntegral :
    ∀ (R : Type) [CommRing R] [Algebra ℂ R] (P Q : Polynomial R), P.Monic → Q.Monic → (∀ u : ℂ, IsIntegral ℂ ((P * Q).eval (algebraMap ℂ R u))) → ∀ u : ℂ, IsIntegral ℂ (P.eval (algebraMap ℂ R u)) := by
  intro R _ _ P Q hP hQ h u
  classical
  have hcoeff : ∀ j, (P * Q).coeff j ∈ integralClosure ℂ R := coeff_mem_subalgebra_of_eval_mem _ (P * Q) h
  have hlift : P * Q ∈ Polynomial.lifts (algebraMap (integralClosure ℂ R) R) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hcoeff n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift (hP.mul hQ)
  have hPc : ∀ i, P.coeff i ∈ integralClosure ℂ R := by
    intro i
    have hi := Polynomial.isIntegral_coeff_of_dvd q P hqm hP (by rw [hq]; exact dvd_mul_right P Q) i
    exact isIntegral_trans _ hi
  have hmem : P.eval (algebraMap ℂ R u) ∈ integralClosure ℂ R := by
    rw [Polynomial.eval_eq_sum_range]
    exact Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (hPc i)
      (Subalgebra.pow_mem _ (Subalgebra.algebraMap_mem _ u) _)
  exact hmem
end

