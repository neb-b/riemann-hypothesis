module

public import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.Bundle0001

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PContractA
section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz.CtrX

open PositivityTheory.Rg.Cz

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

def reIx {P Q : Type} (e : P ≃ Q) (ξ : TV n M P) : TV n M Q := fun I => ξ (I ∘ e)

def unc {A B : Type} (f : TV n (TV n M A) B) : TV n M (A ⊕ B) := fun I => f (I ∘ Sum.inr) (I ∘ Sum.inl)

def cur {A B : Type} (g : TV n M (A ⊕ B)) : TV n (TV n M A) B := fun J K => g (Sum.elim K J)

theorem unc_cur {A B : Type} (g : TV n M (A ⊕ B)) : unc (cur g) = g := by
  funext I
  simp only [unc, cur, Sum.elim_comp_inl_inr]

theorem unc_inj {A B : Type} {f g : TV n (TV n M A) B} (h : unc f = unc g) : f = g := by
  funext J K
  have := congrFun h (Sum.elim K J)
  simpa [unc] using this

theorem unc_smul {A B : Type} (c : ℂ) (f : TV n (TV n M A) B) : unc (c • f) = c • unc f := rfl

theorem reIx_smul {P Q : Type} (e : P ≃ Q) (c : ℂ) (ξ : TV n M P) : reIx e (c • ξ) = c • reIx e ξ := rfl

theorem actT_reIx {ι Γ P Q : Type} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] (e : P ≃ Q)
    (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M) (γ : Γ) (ξ : TV n M P) :
    actT (lab ∘ e.symm) κ ρ γ (reIx e ξ) = reIx e (actT lab κ ρ γ ξ) := by
  funext I
  simp only [actT, reIx, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, Function.comp_apply]
  symm
  refine Fintype.sum_equiv (e.arrowCongr (Equiv.refl (Fin n))) _ _ (fun J => ?_)
  have hJ : (e.arrowCongr (Equiv.refl (Fin n)) J) ∘ e = J := by
    funext p
    simp [Equiv.arrowCongr_apply]
  rw [hJ]
  congr 1
  refine Fintype.prod_equiv e _ _ (fun p => ?_)
  simp [Equiv.arrowCongr_apply]

theorem actT_unc {ι Γ A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (la : A → ι) (lb : B → ι)
    (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M) (γ : Γ) (f : TV n (TV n M A) B) :
    actT (Sum.elim la lb) κ ρ γ (unc f) = unc (actT lb κ (actT la κ ρ) γ f) := by
  funext I
  simp only [actT, unc, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, Function.comp_apply, Finset.sum_apply, Pi.smul_apply]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv ((Equiv.sumArrowEquivProdArrow A B (Fin n)).trans (Equiv.prodComm _ _)) _ _ (fun d => ?_)
  simp only [Equiv.trans_apply, Equiv.prodComm_apply, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
  rw [mul_comm]
  rfl

def splitE (m n : ℕ) (h : n ≤ m) : Fin m ≃ Fin (m - n) ⊕ Fin n where
  toFun i := if hi : (i : ℕ) < n then Sum.inr ⟨i, hi⟩ else Sum.inl ⟨i - n, by omega⟩
  invFun := Sum.elim (fun j => ⟨j + n, by omega⟩) (fun j => ⟨j, by omega⟩)
  left_inv i := by
    by_cases hi : (i : ℕ) < n
    · simp [hi]
    · simp only [hi, dite_false, Sum.elim_inl]
      ext; simp; omega
  right_inv x := by
    rcases x with j | j
    · simp
    · simp [j.2]

theorem pm_alt_firstG {m k : ℕ} (τ : Equiv.Perm (Fin m)) (hτ : τ ∈ firstG m k) (x : TV n M (Fin m)) :
    pm τ (alt (firstG m k) x) = ((Equiv.Perm.sign τ : ℤ) : ℂ) • alt (firstG m k) x := by
  have hmem : ∀ σ : Equiv.Perm (Fin m), σ ∈ firstG m k ↔ ∀ j : Fin m, k ≤ (j : ℕ) → σ j = j := by
    intro σ
    simp [firstG]
  have hτ' := (hmem τ).1 hτ
  have hmul : ∀ σ : Equiv.Perm (Fin m), pm τ (pm σ x) = pm (τ * σ) x := by
    intro σ
    funext I
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [alt, LinearMap.sum_apply, map_sum, Finset.smul_sum, LinearMap.smul_apply, map_smul, hmul, smul_smul]
  refine Finset.sum_nbij' (fun σ => τ * σ) (fun σ => τ⁻¹ * σ) ?_ ?_ ?_ ?_ ?_
  · intro σ hσ
    rw [hmem] at hσ ⊢
    intro j hj
    simp [Equiv.Perm.mul_apply, hσ j hj, hτ' j hj]
  · intro σ hσ
    rw [hmem] at hσ ⊢
    intro j hj
    have h1 : τ⁻¹ j = j := by
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact (hτ' j hj).symm
    simp [Equiv.Perm.mul_apply, hσ j hj, h1]
  · intro σ _
    simp
  · intro σ _
    simp
  · intro σ _
    congr 1
    rw [Equiv.Perm.sign_mul]
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h]

theorem cur_anti {m : ℕ} (h : n ≤ m) (η : TV n M (Fin m))
    (hη : ∀ τ ∈ firstG m n, pm τ η = ((Equiv.Perm.sign τ : ℤ) : ℂ) • η) (σ : Equiv.Perm (Fin n)) :
    pm σ (cur (reIx (splitE m n h) η)) = ((Equiv.Perm.sign σ : ℤ) : ℂ) • cur (reIx (splitE m n h) η) := by
  funext J K
  set e := splitE m n h with he
  let S : Equiv.Perm (Fin (m - n) ⊕ Fin n) := Equiv.sumCongr (Equiv.refl _) σ
  let τ : Equiv.Perm (Fin m) := (e.trans S).trans e.symm
  have hτ : τ ∈ firstG m n := by
    simp only [firstG, Finset.mem_filter, Finset.mem_univ, true_and]
    intro j hj
    have hj' : ¬ (j : ℕ) < n := by omega
    have ha : e j = Sum.inl ⟨(j : ℕ) - n, by omega⟩ := by
      simp [he, splitE, hj']
    show e.symm (S (e j)) = j
    rw [ha]
    exact e.symm_apply_eq.2 ha.symm
  have hs : Equiv.Perm.sign τ = Equiv.Perm.sign σ := by
    show Equiv.Perm.sign ((e.symm.symm.trans S).trans e.symm) = _
    rw [Equiv.Perm.sign_symm_trans_trans]
    simp [S, Equiv.Perm.sign_sumCongr]
  have key := congrFun (hη τ hτ) (Sum.elim K J ∘ e)
  simp only [pm, LinearMap.pi_apply, LinearMap.proj_apply, Pi.smul_apply] at key
  simp only [pm, cur, reIx, LinearMap.pi_apply, LinearMap.proj_apply, Pi.smul_apply]
  rw [← hs, ← key]
  congr 1
  funext x
  simp only [Function.comp_apply, τ, Equiv.trans_apply, Equiv.apply_symm_apply, S,
    Equiv.sumCongr_apply, Equiv.refl_apply]
  cases e x <;> rfl

end PositivityTheory.Rg.Cz.CtrX

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PContractD
section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz.CtrX

open PositivityTheory.Rg.Cz

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem antisymmetric_eq_zero_of_not_injective (f : TV n M (Fin n))
    (hf : ∀ σ : Equiv.Perm (Fin n), pm σ f = ((Equiv.Perm.sign σ : ℤ) : ℂ) • f) (J : Fin n → Fin n)
    (hJ : ¬ Function.Injective J) : f J = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hJ
  have h2 : J ∘ ⇑(Equiv.swap i j) = J := by
    funext k
    simp only [Function.comp]
    rcases eq_or_ne k i with rfl | hki
    · simp [hij]
    rcases eq_or_ne k j with rfl | hkj
    · simp [hij]
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have h1 := congrFun (hf (Equiv.swap i j)) J
  have h3 : pm (Equiv.swap i j) f J = f J := by
    show f (J ∘ ⇑(Equiv.swap i j)) = f J
    rw [h2]
  rw [h3, Pi.smul_apply, Equiv.Perm.sign_swap hne] at h1
  have h4 : (2 : ℂ) • f J = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h1]
    simp
  rcases smul_eq_zero.mp h4 with h | h
  · norm_num at h
  · exact h

theorem anti_span (f : TV n M (Fin n))
    (hf : ∀ σ : Equiv.Perm (Fin n), pm σ f = ((Equiv.Perm.sign σ : ℤ) : ℂ) • f) (J : Fin n → Fin n) :
    ∃ c : ℂ, f J = c • f id := by
  by_cases hJ : Function.Injective J
  · have hb : Function.Bijective J := Finite.injective_iff_bijective.mp hJ
    refine ⟨((Equiv.Perm.sign (Equiv.ofBijective J hb) : ℤ) : ℂ), ?_⟩
    have h1 := congrFun (hf (Equiv.ofBijective J hb)) id
    have h3 : pm (Equiv.ofBijective J hb) f id = f J := rfl
    rw [h3, Pi.smul_apply] at h1
    exact h1
  · exact ⟨0, by rw [antisymmetric_eq_zero_of_not_injective f hf J hJ, zero_smul]⟩

theorem actT_anti_id {ι Γ : Type} (τ : ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M) (γ : Γ)
    (f : TV n M (Fin n)) (hf : ∀ σ : Equiv.Perm (Fin n), pm σ f = ((Equiv.Perm.sign σ : ℤ) : ℂ) • f) :
    actT (fun _ : Fin n => τ) κ ρ γ f id = (κ τ γ).det • ρ γ (f id) := by
  set A := κ τ γ with hA
  have hsum : actT (fun _ : Fin n => τ) κ ρ γ f id
      = ∑ J : Fin n → Fin n, (∏ p, A p (J p)) • ρ γ (f J) := by
    simp only [actT, LinearMap.pi_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, id, hA]
  have hperm : ∀ σ : Equiv.Perm (Fin n), f ⇑σ = ((Equiv.Perm.sign σ : ℤ) : ℂ) • f id := by
    intro σ
    have h1 := congrFun (hf σ) id
    rw [Pi.smul_apply] at h1
    exact h1
  have hsub : ∑ J ∈ Finset.univ.image (fun σ : Equiv.Perm (Fin n) => (⇑σ : Fin n → Fin n)),
        (∏ p, A p (J p)) • ρ γ (f J)
      = ∑ J : Fin n → Fin n, (∏ p, A p (J p)) • ρ γ (f J) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro J _ hJ
    have hni : ¬ Function.Injective J := by
      intro hinj
      apply hJ
      rw [Finset.mem_image]
      exact ⟨Equiv.ofBijective J (Finite.injective_iff_bijective.mp hinj), Finset.mem_univ _, rfl⟩
    rw [antisymmetric_eq_zero_of_not_injective f hf J hni, map_zero, smul_zero]
  rw [hsum, ← hsub, Finset.sum_image (fun σ _ τ' _ h => Equiv.coe_fn_injective h)]
  simp_rw [hperm, map_smul, smul_smul]
  rw [← Finset.sum_smul, ← Matrix.det_transpose, Matrix.det_apply']
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  rw [mul_comm]
  rfl

end PositivityTheory.Rg.Cz.CtrX

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PContractE
section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz.CtrX

open PositivityTheory.Rg.Cz

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

def omcGlue {m : ℕ} (j : Fin m) (b : Fin n) (R : {p // p ≠ j} → Fin n) : Fin m → Fin n :=
  fun p => if h : p = j then b else R ⟨p, h⟩

def omcEquiv {m : ℕ} (j : Fin m) : (Fin m → Fin n) ≃ Fin n × ({p // p ≠ j} → Fin n) where
  toFun J := (J j, fun p => J p.1)
  invFun x := omcGlue j x.1 x.2
  left_inv J := by
    funext p
    by_cases h : p = j
    · subst h; simp [omcGlue]
    · simp [omcGlue, h]
  right_inv x := by
    rcases x with ⟨b, R⟩
    simp only [omcGlue, dite_true, Prod.mk.injEq, true_and]
    funext p
    simp [p.2]

theorem omc_sum {m : ℕ} {β : Type} [AddCommMonoid β] (j : Fin m) (h : (Fin m → Fin n) → β) :
    ∑ J, h J = ∑ b, ∑ R, h (omcGlue j b R) := by
  rw [← (omcEquiv (n := n) j).symm.sum_comp, Fintype.sum_prod_type]
  rfl

omit [AddCommGroup M] [Module ℂ M] in
theorem omc_glue_j {m : ℕ} (j : Fin m) (b : Fin n) (R : {p // p ≠ j} → Fin n) : omcGlue j b R j = b := by
  simp [omcGlue]

omit [AddCommGroup M] [Module ℂ M] in
theorem omc_update {m : ℕ} (j : Fin m) (a b : Fin n) (R : {p // p ≠ j} → Fin n) :
    Function.update (omcGlue j b R) j a = omcGlue j a R := by
  funext p
  by_cases hp : p = j
  · subst hp
    simp [omc_glue_j]
  · rw [Function.update_of_ne hp]
    simp [omcGlue, hp]

omit [AddCommGroup M] [Module ℂ M] in
theorem omc_prod {m : ℕ} (j : Fin m) (F : Fin m → Fin n → ℂ) (b : Fin n) (R : {p // p ≠ j} → Fin n) :
    ∏ p, F p (omcGlue j b R p) = F j b * ∏ p : {p // p ≠ j}, F p.1 (R p) := by
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ j]
  simp only [omc_glue_j]
  congr 1
  refine Finset.prod_congr rfl fun p _ => ?_
  simp [omcGlue, p.2]

private theorem Om_apply_eq_sum_update {m : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (j : Fin m)
    (g : TV n M (Fin m)) (I : Fin m → Fin n) :
    Om E j g I = ∑ a, E a (I j) (g (Function.update I j a)) := by
  simp only [Om, lift, eAt, LinearMap.sum_apply, Module.End.mul_apply, LinearMap.pi_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single (I j)]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem actT_const_apply_eq_sum_prod_smul {ι Γ : Type} {m : ℕ} (τ : ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ)
    (ρ : Γ → Module.End ℂ M) (γ : Γ) (g : TV n M (Fin m)) (I : Fin m → Fin n) :
    actT (fun _ : Fin m => τ) κ ρ γ g I = ∑ J, (∏ p, κ τ γ (I p) (J p)) • ρ γ (g J) := by
  simp only [actT, LinearMap.pi_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply]

private theorem sum_smul_R0_sum_E_eq_of_unitary_of_adjoint (K : Matrix (Fin n) (Fin n) ℂ) (E : Fin n → Fin n → Module.End ℂ M)
    (R0 : Module.End ℂ M) (hu : K * Kᴴ = 1)
    (had : ∀ a b, R0 * E a b = (∑ c, ∑ d, (K c a * star (K d b)) • E c d) * R0)
    (i : Fin n) (y : Fin n → M) :
    ∑ b, K i b • R0 (∑ a, E a b (y a)) = ∑ a, ∑ c, K c a • E c i (R0 (y a)) := by
  have h1 : ∀ a b, R0 (E a b (y a)) = ∑ c, ∑ d, (K c a * star (K d b)) • E c d (R0 (y a)) := by
    intro a b
    have h := congrArg (fun T : Module.End ℂ M => T (y a)) (had a b)
    simpa [Module.End.mul_apply, LinearMap.sum_apply, LinearMap.smul_apply] using h
  have h2 : ∀ d, ∑ b, K i b * star (K d b) = if i = d then 1 else 0 := by
    intro d
    have h := congrFun (congrFun hu i) d
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    simpa [Matrix.conjTranspose_apply] using h
  set_option synthInstance.maxHeartbeats 100000 in
    simp_rw [map_sum, h1, Finset.smul_sum, smul_smul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  have h3 : ∀ d (v : M), ∑ b, (K i b * (K c a * star (K d b))) • v
      = (K c a * if i = d then 1 else 0) • v := by
    intro d v
    rw [← Finset.sum_smul, ← h2 d, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp_rw [h3]
  simp [mul_ite]

theorem actT_Om {ι Γ : Type} {m : ℕ} (τ : ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (E : Fin n → Fin n → Module.End ℂ M)
    (ρ : Γ → Module.End ℂ M) (γ : Γ) (hu : κ τ γ * (κ τ γ)ᴴ = 1)
    (had : ∀ a b, ρ γ * E a b = (∑ c, ∑ d, (κ τ γ c a * star (κ τ γ d b)) • E c d) * ρ γ) (j : Fin m)
    (f : TV n M (Fin m)) :
    actT (fun _ : Fin m => τ) κ ρ γ (Om E j f) = Om E j (actT (fun _ : Fin m => τ) κ ρ γ f) := by
  funext I
  rw [actT_const_apply_eq_sum_prod_smul, Om_apply_eq_sum_update]
  simp_rw [Om_apply_eq_sum_update, actT_const_apply_eq_sum_prod_smul]
  set K := κ τ γ with hK
  have hP : ∀ b R, ∏ p, K (I p) (omcGlue j b R p)
      = K (I j) b * ∏ p : {p // p ≠ j}, K (I p.1) (R p) :=
    fun b R => omc_prod j (fun p y => K (I p) y) b R
  have hQ : ∀ a b R, ∏ p, K (Function.update I j a p) (omcGlue j b R p)
      = K a b * ∏ p : {p // p ≠ j}, K (I p.1) (R p) := by
    intro a b R
    rw [show ∏ p, K (Function.update I j a p) (omcGlue j b R p)
        = K (Function.update I j a j) b * ∏ p : {p // p ≠ j}, K (Function.update I j a p.1) (R p)
        from omc_prod j (fun p y => K (Function.update I j a p) y) b R]
    congr 1
    · simp
    · apply Finset.prod_congr rfl
      intro p _
      rw [Function.update_of_ne p.2]
  trans ∑ R : {p // p ≠ j} → Fin n, (∏ p : {p // p ≠ j}, K (I p.1) (R p)) •
      ∑ a, ∑ c, K c a • E c (I j) (ρ γ (f (omcGlue j a R)))
  · conv_lhs => rw [omc_sum j]
    simp only [omc_glue_j, omc_update, hP]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun R _ => ?_
    rw [← sum_smul_R0_sum_E_eq_of_unitary_of_adjoint K E (ρ γ) hu had (I j) (fun a => f (omcGlue j a R)), Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_smul, mul_comm]
  · have hR : ∀ a, E a (I j) (∑ J, (∏ p, K (Function.update I j a p) (J p)) • ρ γ (f J))
        = ∑ b, ∑ R, (K a b * ∏ p : {p // p ≠ j}, K (I p.1) (R p)) •
          E a (I j) (ρ γ (f (omcGlue j b R))) := by
      intro a
      rw [omc_sum j]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hQ, map_sum, map_smul]
    simp only [hR]
    symm
    conv_lhs => rw [Finset.sum_comm]
    conv_lhs =>
      arg 2
      ext b
      rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun R _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_smul, mul_comm]

end PositivityTheory.Rg.Cz.CtrX

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PSemiZero
section
noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace SemiInvariantDeterminant

theorem det_bar {ι Γ : Type} [Group Γ] [TopologicalSpace Γ] {n : ℕ} {bar : ι → ι}
    {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ} (hK : IsKD bar κ) (τ : ι) (γ : Γ) :
    (κ (bar τ) γ).det = star (κ τ γ).det := by
  have e : κ (bar τ) γ = (starRingEnd ℂ).mapMatrix (κ τ γ) := by
    ext i j; exact hK.conj τ γ i j
  rw [e, ← RingHom.map_det]
  rfl

theorem det_mul_star {ι Γ : Type} [Group Γ] [TopologicalSpace Γ] {n : ℕ} {bar : ι → ι}
    {κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ} (hK : IsKD bar κ) (τ : ι) (γ : Γ) :
    (κ τ γ).det * star (κ τ γ).det = 1 := by
  have := congrArg Matrix.det (hK.unit τ γ)
  rwa [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at this

end SemiInvariantDeterminant

open SemiInvariantDeterminant in
theorem semiZero_of (hQ : QdetFacts) (_hW : WallAlg) (hL : LieInv) (hWQ : WallQuot) : SemiZero := by
  intro n hn M _ _ ι _ _ Γ _ _ bar κ E ρ hK hG s φ hφ hS
  obtain ⟨lab, c, ξ, -, hact, I, w, hw, hwξ⟩ := hS
  have hρ : ∀ γ, ρ γ (ξ I) = (∏ τ, (κ τ γ).det ^ c τ) • ξ I := by
    intro γ
    have h := congrFun (hact γ) I
    rw [actT_apply, Pi.smul_apply] at h
    rw [← h, Fintype.sum_unique]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_smul]
    rw [Subsingleton.elim (default : Fin 0 → Fin n) I]
  obtain ⟨N, F, hFgl, -, hFch, hFE, hN⟩ := hWQ n M ι E hG.gl hG.comm (fun _ _ => s) φ (by
    intro τ u
    rw [hφ τ u, Finset.prod_const, Finset.card_univ, Fintype.card_fin])
  have hξN : N.mkQ (ξ I) ≠ 0 := by
    rw [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hN]
    push Not
    exact ⟨w, hw, hwξ⟩
  have htr : ∀ τ', N.mkQ ((∑ a, E τ' a a) (ξ I)) = (∑ a, F τ' a a) (N.mkQ (ξ I)) := by
    intro τ'
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.sum_apply, map_sum]
    exact Finset.sum_congr rfl fun a _ => LinearMap.congr_fun (hFE τ' a a) (ξ I)
  have hc : ∀ τ, c τ = c (bar τ) := by
    intro τ
    have hl := hL n M ι Γ bar κ E ρ hK hG c (ξ I) hρ τ
    have h1 : N.mkQ ((∑ a, E τ a a) (ξ I)) = N.mkQ ((∑ a, E (bar τ) a a) (ξ I)) := by
      rw [htr, htr, (hQ n (M ⧸ N) (F τ) (hFgl τ)).2.2.1 _ (hFch τ),
        (hQ n (M ⧸ N) (F (bar τ)) (hFgl (bar τ))).2.2.1 _ (hFch (bar τ))]
    have h2 : (∑ a, E τ a a) (ξ I) - (∑ a, E (bar τ) a a) (ξ I) =
        ((n : ℂ) * ((c τ - c (bar τ) : ℤ) : ℂ)) • ξ I := by
      rw [LinearMap.sum_apply, LinearMap.sum_apply, ← Finset.sum_sub_distrib]
      simp only [hl, if_true]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    have h3 : ((n : ℂ) * ((c τ - c (bar τ) : ℤ) : ℂ)) • N.mkQ (ξ I) = 0 := by
      rw [← map_smul, ← h2, map_sub, h1, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd (Nat.cast_eq_zero.mp h) (by omega)
      · exact sub_eq_zero.mp (Int.cast_eq_zero.mp h)
    · exact absurd h hξN
  have hχ : ∀ γ, (∏ τ, (κ τ γ).det ^ c τ) = 1 := by
    intro γ
    refine Finset.prod_involution (fun τ _ => bar τ) ?_ ?_ (fun _ _ => Finset.mem_univ _)
      (fun τ _ => hK.invol τ)
    · intro τ _
      rw [det_bar hK, ← hc τ, ← mul_zpow, det_mul_star hK, _root_.one_zpow]
    · intro τ _ _
      exact hK.ne τ
  exact ⟨ξ I, fun γ => by rw [hρ, hχ, one_smul], w, hw, hwξ⟩

end PositivityTheory.Rg.Cz

end
end

