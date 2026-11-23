module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle0001
public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.QdetFacts
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.RowCol
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.CapelliIdentity.Bundle0002

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PLieInv
section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace LieInverse

theorem exists_ne_of_ne_one {n : ℕ} (σ : Equiv.Perm (Fin n)) (hσ : σ ≠ 1) (i : Fin n) :
    ∃ j, j ≠ i ∧ σ j ≠ j := by
  by_contra h
  push Not at h
  apply hσ
  have hi : σ i = i := by
    by_contra hne
    have := h (σ i) hne
    exact hne (σ.injective this)
  ext j
  by_cases hj : j = i
  · subst hj; simp [hi]
  · simp [h j hj]

theorem hasDerivAt_det {n : ℕ} (A : ℝ → Matrix (Fin n) (Fin n) ℂ) (Y : Matrix (Fin n) (Fin n) ℂ)
    (h0 : A 0 = 1) (hA : ∀ i j, HasDerivAt (fun t => A t i j) (Y i j) 0) :
    HasDerivAt (fun t => (A t).det) Y.trace 0 := by
  have key : ∀ σ : Equiv.Perm (Fin n), HasDerivAt (fun t => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A t (σ i) i)
      (((Equiv.Perm.sign σ : ℤ) : ℂ) * ∑ i, (∏ j ∈ Finset.univ.erase i, A 0 (σ j) j) * Y (σ i) i) 0 := by
    intro σ
    have := (HasDerivAt.finsetProd (u := Finset.univ) (fun i _ => hA (σ i) i)).const_mul
      ((Equiv.Perm.sign σ : ℤ) : ℂ)
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    simp [Finset.prod_apply]
  have hs := HasDerivAt.sum (u := Finset.univ) (fun σ _ => key σ)
  refine (hs.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)).congr_deriv ?_
  · simp [Matrix.det_apply', Finset.sum_apply]
  · simp only [Finset.mul_sum, smul_eq_mul]
    rw [Finset.sum_comm, Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
    · simp [h0]
    · intro σ _ hσ
      obtain ⟨j, hji, hj⟩ := exists_ne_of_ne_one σ hσ i
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩) (by rw [h0]; exact Matrix.one_apply_ne hj)]
      simp
    · simp

def Sop {ι : Type} {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] (E : ι → Fin n → Fin n → Module.End ℂ M)
    (bar : ι → ι) (τ : ι) (X : Matrix (Fin n) (Fin n) ℂ) : Module.End ℂ M :=
  ∑ a, ∑ b, (X a b • E τ a b + star (X a b) • E (bar τ) a b)

theorem Sop_add {ι : Type} {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M] (E : ι → Fin n → Fin n → Module.End ℂ M)
    (bar : ι → ι) (τ : ι) (X Y : Matrix (Fin n) (Fin n) ℂ) : Sop E bar τ (X + Y) = Sop E bar τ X + Sop E bar τ Y := by
  simp only [Sop, Matrix.add_apply, add_smul, star_add, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by abel

theorem Sop_single {ι : Type} {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
    (E : ι → Fin n → Fin n → Module.End ℂ M) (bar : ι → ι) (τ : ι) (p q : Fin n) (z : ℂ) :
    Sop E bar τ (Matrix.single p q z) = z • E τ p q + star z • E (bar τ) p q := by
  unfold Sop
  rw [Finset.sum_eq_single p, Finset.sum_eq_single q]
  · simp [Matrix.single_apply]
  · intro b _ hb; simp [Matrix.single_apply, hb, Ne.symm hb]
  · simp
  · intro a _ ha
    exact Finset.sum_eq_zero fun b _ => by simp [Matrix.single_apply, ha, Ne.symm ha]
  · simp

end LieInverse

open LieInverse in
theorem lieInv_holds : LieInv := by
  intro n M _ _ ι _ _ Γ _ _ bar κ E ρ hK hG c ξ hξ τ a b
  have hbt : bar τ ≠ τ := hK.ne τ
  have hD : ∀ X : Matrix (Fin n) (Fin n) ℂ, Xᴴ = -X →
      Sop E bar τ X ξ = ((c τ : ℂ) * X.trace + (c (bar τ) : ℂ) * star X.trace) • ξ := by
    intro X hX
    obtain ⟨cv, hc0, hcd, hcoth, hρ⟩ := hG.der τ X hX
    let D : ι → ℂ := fun τ' => if τ' = τ then X.trace else if τ' = bar τ then star X.trace else 0
    have hdet : ∀ τ', HasDerivAt (fun t => (κ τ' (cv t)).det) (D τ') 0 := by
      intro τ'
      by_cases h1 : τ' = τ
      · subst h1
        simp only [D, if_true]
        exact hasDerivAt_det _ X (by rw [hc0, hK.one]) hcd
      · by_cases h2 : τ' = bar τ
        · subst h2
          simp only [D, if_neg h1, if_true]
          have ht : (X.map star).trace = star X.trace := by simp [Matrix.trace, star_sum]
          rw [← ht]
          refine hasDerivAt_det _ _ (by rw [hc0, hK.one]) fun i j => ?_
          simp only [hK.conj, Matrix.map_apply]
          exact (hcd i j).star
        · simp only [D, if_neg h1, if_neg h2]
          have hf : (fun t => (κ τ' (cv t)).det) = fun _ => 1 := by
            funext t; rw [hcoth τ' h1 h2 t, Matrix.det_one]
          rw [hf]; exact hasDerivAt_const _ _
    have h1 : ∀ τ', (κ τ' (cv 0)).det = 1 := fun τ' => by rw [hc0, hK.one, Matrix.det_one]
    have hz : ∀ τ', HasDerivAt (fun t => (κ τ' (cv t)).det ^ c τ') ((c τ' : ℂ) * D τ') 0 := by
      intro τ'
      have := (hasDerivAt_zpow (c τ') ((κ τ' (cv 0)).det) (Or.inl (by rw [h1]; exact one_ne_zero))).comp
        (0 : ℝ) (hdet τ')
      rw [h1, _root_.one_zpow, mul_one] at this
      exact this
    have hχ : HasDerivAt (fun t => ∏ τ', (κ τ' (cv t)).det ^ c τ')
        ((c τ : ℂ) * X.trace + (c (bar τ) : ℂ) * star X.trace) 0 := by
      have := HasDerivAt.finsetProd (u := Finset.univ) (fun τ' _ => hz τ')
      refine (this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => by
        simp [Finset.prod_apply])).congr_deriv ?_
      simp only [h1, _root_.one_zpow, Finset.prod_const_one, one_smul]
      rw [Finset.sum_eq_add_of_mem τ (bar τ) (Finset.mem_univ _) (Finset.mem_univ _) hbt.symm]
      · simp [D, hbt]
      · intro x _ hx; simp [D, hx.1, hx.2]
    rw [← sub_eq_zero]
    apply (Module.forall_dual_apply_eq_zero_iff ℂ _).mp
    intro lam
    have h2 : HasDerivAt (fun t => lam (ρ (cv t) ξ))
        (((c τ : ℂ) * X.trace + (c (bar τ) : ℂ) * star X.trace) * lam ξ) 0 := by
      refine (hχ.mul_const (lam ξ)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
      simp only [hξ, map_smul, smul_eq_mul]
    have hu : lam (Sop E bar τ X ξ) = _ := (hρ ξ lam).unique h2
    rw [map_sub, hu, map_smul, smul_eq_mul, sub_self]
  have hsI : star Complex.I = -Complex.I := Complex.conj_I
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    have hX : (Matrix.single a a Complex.I)ᴴ = -Matrix.single a a Complex.I := by
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Matrix.single_apply]
      split_ifs with h1 h2 h2
      · simp [hsI]
      · exact (h2 ⟨h1.2, h1.1⟩).elim
      · exact (h1 ⟨h2.2, h2.1⟩).elim
      · simp
    have e := hD _ hX
    rw [Sop_single, Matrix.trace_single_eq_same, hsI] at e
    have e' : Complex.I • (E τ a a ξ - E (bar τ) a a ξ - ((c τ - c (bar τ) : ℤ) : ℂ) • ξ) = 0 := by
      simp only [LinearMap.add_apply, LinearMap.smul_apply] at e
      push_cast
      linear_combination (norm := module) e
    rcases smul_eq_zero.mp e' with h | h
    · exact absurd h Complex.I_ne_zero
    · exact sub_eq_zero.mp h
  · rw [if_neg hab]
    have hX1 : (Matrix.single a b (1 : ℂ) + Matrix.single b a (-1))ᴴ =
        -(Matrix.single a b (1 : ℂ) + Matrix.single b a (-1)) := by
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Matrix.add_apply, Matrix.single_apply]
      split_ifs <;> simp_all
    have hX2 : (Matrix.single a b Complex.I + Matrix.single b a Complex.I)ᴴ =
        -(Matrix.single a b Complex.I + Matrix.single b a Complex.I) := by
      ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Matrix.add_apply, Matrix.single_apply]
      split_ifs <;> simp_all
    have e1 := hD _ hX1
    have e2 := hD _ hX2
    rw [Sop_add, Sop_single, Sop_single, Matrix.trace_add, Matrix.trace_single_eq_of_ne _ _ _ hab,
      Matrix.trace_single_eq_of_ne _ _ _ (Ne.symm hab)] at e1 e2
    simp only [LinearMap.add_apply, LinearMap.smul_apply, add_zero, star_zero, mul_zero, zero_smul, hsI,
      star_one, star_neg] at e1 e2
    have e2' : Complex.I • (E τ a b ξ + E τ b a ξ - E (bar τ) a b ξ - E (bar τ) b a ξ) = 0 := by
      linear_combination (norm := module) e2
    have e3 : E τ a b ξ + E τ b a ξ - E (bar τ) a b ξ - E (bar τ) b a ξ = 0 :=
      (smul_eq_zero.mp e2').resolve_left Complex.I_ne_zero
    linear_combination (norm := module) (1 / 2 : ℂ) • e1 + (1 / 2 : ℂ) • e3

end PositivityTheory.Rg.Cz

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PQdetFacts
section
noncomputable section

open Polynomial Formalism.REAL

namespace PositivityTheory.Rg.Cz

namespace QF

open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

section Alg

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem qdet_eq_capelliC {n : ℕ} (E : Fin n → Fin n → A) (x : ℂ) : qdet E x = capelliC E x := by
  simp only [qdet, capelliC, cminor, qminor, Tm, capEntry, id]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [zsmul_eq_mul]
  congr 3
  funext k
  rw [add_comm]

theorem capelliC_negT {n : ℕ} (E : Fin n → Fin n → A) (x : ℂ) :
    capelliC (fun a b => -E b a) x = (-1) ^ n * rminor E id id ((n : ℂ) - 1 - x) := by
  simp only [capelliC, cminor, rminor, id]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have h : (List.ofFn fun j : Fin n => capEntry (fun a b => -E b a) (x - ((j : ℕ) : ℂ)) (σ j) j) =
      (List.ofFn fun j : Fin n => capEntry E ((n : ℂ) - 1 - x - (n : ℂ) + 1 + ((j : ℕ) : ℂ)) j (σ j)).map Neg.neg := by
    rw [List.map_ofFn]
    congr 1
    funext j
    simp only [Function.comp_apply, capEntry]
    by_cases hj : σ j = j
    · rw [if_pos hj, if_pos hj.symm, neg_add, ← map_neg]
      congr 2
      ring
    · rw [if_neg hj, if_neg (Ne.symm hj), neg_add, neg_zero]
  rw [h, List.prod_map_neg, List.length_ofFn, zsmul_eq_mul, zsmul_eq_mul, ← mul_assoc, ← mul_assoc,
    ((Commute.neg_one_left _).pow_left n).eq]

theorem qdet_negT {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) (u : ℂ) :
    qdet (fun a b => -E b a) u = (-1) ^ n * qdet E ((n : ℂ) - 1 - u) := by
  rw [qdet_eq_capelliC, capelliC_negT, qdet_eq_capelliC, capelliC, cminor_eq_rminor E hE]

def tmPoly {n : ℕ} (E : Fin n → Fin n → A) (k : ℕ) (a b : Fin n) : A[X] :=
  (if a = b then X - C (algebraMap ℂ A (k : ℂ)) else 0) + C (E a b)

def qdetPoly {n : ℕ} (E : Fin n → Fin n → A) : A[X] :=
  ∑ σ : Equiv.Perm (Fin n), C ((Equiv.Perm.sign σ : ℤ) : A) *
    (List.ofFn fun k : Fin n => tmPoly E k (σ k) k).prod

def evU (u : ℂ) : A[X] →+* A :=
  eval₂RingHom' (RingHom.id A) (algebraMap ℂ A u) (fun a => (Algebra.commutes u a).symm)

theorem evU_apply (u : ℂ) (p : A[X]) : evU u p = eval₂ (RingHom.id A) (algebraMap ℂ A u) p := rfl

theorem evU_tmPoly {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) (k : ℕ) (a b : Fin n) :
    evU u (tmPoly E k a b) = Tm E (u - (k : ℂ)) a b := by
  rw [evU_apply, tmPoly, Tm]
  split_ifs <;> simp [eval₂_add, eval₂_sub, map_sub]

theorem evU_qdetPoly {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) : evU u (qdetPoly E) = qdet E u := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [qdetPoly, qdet, qminor, id, map_sum, map_mul, map_list_prod, List.map_ofFn, Function.comp_def,
    evU_tmPoly]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [evU_apply, eval₂_C]
  rfl

theorem natDegree_tmPoly_le {n : ℕ} (E : Fin n → Fin n → A) (k : ℕ) (a b : Fin n) :
    (tmPoly E k a b).natDegree ≤ if a = b then 1 else 0 := by
  rw [tmPoly]
  split_ifs with h
  · exact (natDegree_add_le _ _).trans (max_le (natDegree_X_sub_C_le _) (by rw [natDegree_C]; exact zero_le_one))
  · rw [zero_add, natDegree_C]

theorem natDegree_prod_le {n : ℕ} (E : Fin n → Fin n → A) (σ : Equiv.Perm (Fin n)) :
    (List.ofFn fun k : Fin n => tmPoly E k (σ k) k).prod.natDegree ≤
      ∑ k : Fin n, if σ k = k then 1 else 0 := by
  refine (natDegree_list_prod_le _).trans ?_
  rw [List.map_ofFn, List.sum_ofFn]
  exact Finset.sum_le_sum fun k _ => natDegree_tmPoly_le E k (σ k) k

theorem fixed_add_support {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (∑ k : Fin n, if σ k = k then 1 else 0) + σ.support.card = n := by
  rw [Finset.sum_boole, Nat.cast_id]
  have hs : σ.support = Finset.univ.filter (fun k => ¬ σ k = k) := by
    ext k
    simp [Equiv.Perm.mem_support]
  rw [hs, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]

theorem natDegree_prod_ne_one {n : ℕ} (E : Fin n → Fin n → A) {σ : Equiv.Perm (Fin n)} (hσ : σ ≠ 1) :
    (List.ofFn fun k : Fin n => tmPoly E k (σ k) k).prod.natDegree + 2 ≤ n := by
  have h1 := natDegree_prod_le E σ
  have h2 := fixed_add_support σ
  have h3 := Equiv.Perm.two_le_card_support_of_ne_one hσ
  omega

omit [Algebra ℂ A] in
theorem prod_linear (m : ℕ) (c : Fin m → A) :
    (List.ofFn fun k : Fin m => X + C (c k)).prod.natDegree ≤ m ∧
      (List.ofFn fun k : Fin m => X + C (c k)).prod.coeff m = 1 ∧
      ∀ j, j + 1 = m → (List.ofFn fun k : Fin m => X + C (c k)).prod.coeff j = ∑ k, c k := by
  induction m with
  | zero =>
    refine ⟨by simp, by simp, fun j hj => by omega⟩
  | succ m ih =>
    obtain ⟨h1, h2, h3⟩ := ih (fun k => c k.castSucc)
    have e : (List.ofFn fun k : Fin (m + 1) => X + C (c k)).prod =
        (List.ofFn fun k : Fin m => X + C (c k.castSucc)).prod * (X + C (c (Fin.last m))) := by
      rw [List.ofFn_succ', List.concat_eq_append, List.prod_append, List.prod_singleton]
    rw [e]
    have hP : (List.ofFn fun k : Fin m => X + C (c k.castSucc)).prod.coeff (m + 1) = 0 :=
      coeff_eq_zero_of_natDegree_lt (by omega)
    refine ⟨?_, ?_, ?_⟩
    · refine natDegree_mul_le.trans (add_le_add h1 ?_)
      exact (natDegree_add_le _ _).trans (max_le natDegree_X_le (by rw [natDegree_C]; exact zero_le_one))
    · rw [mul_add, coeff_add, coeff_mul_C, coeff_mul_X, h2, hP, zero_mul, add_zero]
    · intro j hj
      obtain rfl : j = m := by omega
      rw [Fin.sum_univ_castSucc, mul_add, coeff_add, coeff_mul_C, h2, one_mul]
      congr 1
      rcases j with _ | j
      · simp
      · rw [coeff_mul_X]
        exact h3 j rfl

theorem tmPoly_diag {n : ℕ} (E : Fin n → Fin n → A) (k : ℕ) (a : Fin n) :
    tmPoly E k a a = X + C (E a a - algebraMap ℂ A (k : ℂ)) := by
  rw [tmPoly, if_pos rfl, C_sub]
  abel

theorem sum_fin_cast (n : ℕ) : ∑ k : Fin n, ((k : ℕ) : ℂ) = (n : ℂ) * ((n : ℂ) - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (i : ℂ)) n]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem natDegree_qdetPoly_le {n : ℕ} (E : Fin n → Fin n → A) : (qdetPoly E).natDegree ≤ n := by
  refine natDegree_sum_le_of_forall_le _ _ fun σ _ => ?_
  refine (natDegree_C_mul_le _ _).trans ((natDegree_prod_le E σ).trans ?_)
  have := fixed_add_support σ
  omega

theorem coeff_qdetPoly_top {n : ℕ} (E : Fin n → Fin n → A) (j : ℕ) (hj : n ≤ j + 1) :
    (qdetPoly E).coeff j = (List.ofFn fun k : Fin n => X + C (E k k - algebraMap ℂ A ((k : ℕ) : ℂ))).prod.coeff j := by
  rw [qdetPoly, Polynomial.finsetSum_coeff, Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
  · simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, C_1, one_mul, Equiv.Perm.one_apply, tmPoly_diag]
  · intro σ _ hσ
    rw [coeff_C_mul]
    have := natDegree_prod_ne_one E hσ
    rw [coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Alg

section Op

variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem coeff_eq_zero_of_evU (r : (Module.End ℂ M)[X]) (h : ∀ u : ℂ, evU u r = 0) (i : ℕ) : r.coeff i = 0 := by
  by_cases hi : i ∈ r.support
  swap
  · exact notMem_support_iff.mp hi
  ext m
  rw [LinearMap.zero_apply]
  refine (Module.forall_dual_apply_eq_zero_iff ℂ _).mp fun φ => ?_
  have hq0 : (∑ e ∈ r.support, monomial e (φ (r.coeff e m))) = 0 := by
    refine Polynomial.funext fun u => ?_
    rw [eval_zero, Polynomial.eval_finsetSum]
    have hu := congrArg (fun T : Module.End ℂ M => φ (T m)) (h u)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [evU_apply, eval₂_eq_sum, Polynomial.sum_def, LinearMap.zero_apply, map_zero, RingHom.id_apply,
      LinearMap.sum_apply, Module.End.mul_apply, ← map_pow, Module.algebraMap_end_apply,
      map_smul, map_sum, smul_eq_mul] at hu
    rw [← hu]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [eval_monomial, mul_comm]
  have hc := congrArg (fun p : ℂ[X] => p.coeff i) hq0
  simp only [Polynomial.finsetSum_coeff, coeff_monomial_apply, coeff_zero, Finset.sum_ite_eq', if_pos hi] at hc
  exact hc

end Op

end QF

open QF ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

theorem qdetFacts_holds : QdetFacts := by
  intro n M _ _ E hE
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u a b
    rw [qdet_eq_capelliC]
    exact (capelliC_central E hE u a b).symm
  · refine ⟨fun i => (qdetPoly E).coeff i, fun u => ?_⟩
    rw [← evU_qdetPoly, evU_apply, eval₂_eq_sum_range' _ (Nat.lt_succ_of_le (natDegree_qdetPoly_le E))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RingHom.id_apply, ← map_pow, ← Algebra.commutes, ← Algebra.smul_def]
  · intro l hl
    have key : ∀ i, (qdetPoly E).coeff i =
        algebraMap ℂ (Module.End ℂ M) ((∏ k : Fin n, (X + C (l k))).coeff i) := by
      intro i
      rw [← coeff_map, ← sub_eq_zero, ← coeff_sub]
      refine coeff_eq_zero_of_evU _ (fun u => ?_) i
      rw [map_sub, evU_qdetPoly, hl u, evU_apply, eval₂_map, RingHom.id_comp, eval₂_at_apply, eval_prod]
      simp only [eval_add, eval_X, eval_C, sub_self]
    cases n with
    | zero => simp
    | succ m =>
      have h1 := key m
      have h2 := (prod_linear (m + 1) fun k => E k k - algebraMap ℂ (Module.End ℂ M) ((k : ℕ) : ℂ)).2.2 m rfl
      have h3 := (prod_linear (m + 1) l).2.2 m rfl
      rw [List.prod_ofFn] at h3
      set_option synthInstance.maxHeartbeats 100000 in
        rw [coeff_qdetPoly_top E m le_rfl, h2, h3, Finset.sum_sub_distrib, sub_eq_iff_eq_add, ← map_sum] at h1
      rw [h1, ← map_add (f := _), sum_fin_cast]
  · unfold GlRel
    intro a b c d
    have h := hE d c b a
    simp only [@eq_comm _ c b, @eq_comm _ a d] at h
    simp only [neg_mul_neg]
    rw [← neg_sub, h]
    split_ifs <;> abel
  · intro l hl u
    rw [qdet_negT E hE, hl]
    have hp : ∏ k : Fin n, (u + (-((n : ℂ) - 1) - l k)) = (-1) ^ n * ∏ k : Fin n, ((n : ℂ) - 1 - u + l k) := by
      rw [show (-1 : ℂ) ^ n = ∏ _k : Fin n, (-1 : ℂ) by simp, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => by ring
    rw [hp, map_mul, map_pow, map_neg, map_one]

end PositivityTheory.Rg.Cz

end
end

