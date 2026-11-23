module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.ExistsAlgHomEndIntertwiningMemAdjoin
section
open scoped BigOperators

private theorem burnside_endomorphism {S A : Type} [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]
    [Ring A] [Algebra ℂ A] [Module A S] [IsScalarTower ℂ A S] [IsSimpleModule A S]
    (t : Module.End ℂ S) : ∃ a : A, ∀ m : S, t m = a • m := by
  classical
  have hb := IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed (A := A) (V := S) ℂ
  let f : Module.End (Module.End A S) S :=
    { toFun := t
      map_add' := t.map_add
      map_smul' := by
        intro d m
        obtain ⟨c, rfl⟩ := hb.2 d
        simp [Module.algebraMap_end_apply] }
  let b := Module.finBasis ℂ S
  obtain ⟨a, ha⟩ := jacobson_density f (Finset.univ.image b)
  refine ⟨a, fun m => ?_⟩
  let u : Module.End ℂ S := Module.toModuleEnd ℂ (S := A) S a
  have : t = u := by
    refine b.ext fun i => ?_
    exact ha (b i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  rw [this]; rfl

private theorem burn_sub {S : Type} [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]
    [Nontrivial S] (R : Subalgebra ℂ (Module.End ℂ S))
    (h : ∀ x : S, x ≠ 0 → Submodule.span ℂ {y | ∃ r ∈ R, y = r x} = ⊤) : R = ⊤ := by
  have hs : IsSimpleModule R S := by
    rw [isSimpleModule_iff]
    refine { eq_bot_or_eq_top := fun N => ?_ }
    by_cases hN : N = ⊥
    · exact Or.inl hN
    right
    obtain ⟨x, hxN, hx⟩ := N.exists_mem_ne_zero_of_ne_bot hN
    rw [eq_top_iff]
    intro y _
    have hy : y ∈ Submodule.span ℂ {y | ∃ r ∈ R, y = r x} := by rw [h x hx]; trivial
    have hle : Submodule.span ℂ {y | ∃ r ∈ R, y = r x} ≤ N.restrictScalars ℂ := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨r, hr, rfl⟩
      exact N.smul_mem (⟨r, hr⟩ : R) hxN
    exact hle hy
  rw [eq_top_iff]
  intro t _
  obtain ⟨a, ha⟩ := burnside_endomorphism (A := R) t
  have : t = (a : Module.End ℂ S) := LinearMap.ext ha
  rw [this]; exact a.2

theorem UpperTheory.exists_algHom_end_intertwining_mem_adjoin :
    ∀ (S X : Type) [AddCommGroup S] [Module ℂ S] [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ S] [FiniteDimensional ℂ X] [Nontrivial S] (M : Set (S →ₗ[ℂ] X)) (P : Set (Module.End ℂ S × Module.End ℂ X)), (⨆ f ∈ M, LinearMap.range f) = ⊤ → (∀ p ∈ P, ∀ f ∈ M, p.2 ∘ₗ f = f ∘ₗ p.1) → (∀ x : S, x ≠ 0 → Submodule.span ℂ {y | ∃ p ∈ P, y = p.1 x} = ⊤) → ∃ c : Module.End ℂ S →ₐ[ℂ] Module.End ℂ X, (∀ t, ∀ f ∈ M, c t ∘ₗ f = f ∘ₗ t) ∧ ∀ t, c t ∈ Algebra.adjoin ℂ (Prod.snd '' P) := by
  intro S X _ _ _ _ _ _ _ M P hM hP hirr
  let Q : Subalgebra ℂ (Module.End ℂ S × Module.End ℂ X) := Algebra.adjoin ℂ P
  let π₁ : (Module.End ℂ S × Module.End ℂ X) →ₐ[ℂ] Module.End ℂ S := AlgHom.fst ℂ _ _
  let π₂ : (Module.End ℂ S × Module.End ℂ X) →ₐ[ℂ] Module.End ℂ X := AlgHom.snd ℂ _ _
  have hcomm : ∀ q ∈ Q, ∀ f ∈ M, q.2 ∘ₗ f = f ∘ₗ q.1 := by
    intro q hq f hf
    induction hq using Algebra.adjoin_induction with
    | mem p hp => exact hP p hp f hf
    | algebraMap r =>
      ext x
      simp [Module.algebraMap_end_apply]
    | add a b _ _ ha hb =>
      ext x
      have h1 := LinearMap.congr_fun ha x
      have h2 := LinearMap.congr_fun hb x
      simp only [LinearMap.comp_apply] at h1 h2
      simp [h1, h2]
    | mul a b _ _ ha hb =>
      ext x
      have h2 := LinearMap.congr_fun hb x
      have h1 := LinearMap.congr_fun ha (b.1 x)
      simp only [LinearMap.comp_apply] at h1 h2
      simp [Module.End.mul_apply, h1, h2]
  let φ : Q →ₐ[ℂ] Module.End ℂ S := π₁.comp Q.val
  let ψ : Q →ₐ[ℂ] Module.End ℂ X := π₂.comp Q.val
  have hinj : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun q hq => ?_
    have h1 : (q : Module.End ℂ S × Module.End ℂ X).1 = 0 := hq
    have h2 : (q : Module.End ℂ S × Module.End ℂ X).2 = 0 := by
      rw [← LinearMap.ker_eq_top, eq_top_iff, ← hM]
      refine iSup₂_le fun f hf => ?_
      rintro _ ⟨x, rfl⟩
      have := LinearMap.congr_fun (hcomm q q.2 f hf) x
      simpa [h1] using this
    exact Subtype.ext (Prod.ext h1 h2)
  have hmap₁ : Q.map π₁ = Algebra.adjoin ℂ (Prod.fst '' P) := AlgHom.map_adjoin π₁ P
  have hmap₂ : Q.map π₂ = Algebra.adjoin ℂ (Prod.snd '' P) := AlgHom.map_adjoin π₂ P
  have htop : Q.map π₁ = ⊤ := by
    refine burn_sub _ fun x hx => ?_
    rw [eq_top_iff, ← hirr x hx]
    refine Submodule.span_mono ?_
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨p.1, hmap₁ ▸ Algebra.subset_adjoin ⟨p, hp, rfl⟩, rfl⟩
  have hsurj : Function.Surjective φ := by
    intro t
    have ht : t ∈ Q.map π₁ := by rw [htop]; trivial
    obtain ⟨q, hq, rfl⟩ := ht
    exact ⟨⟨q, hq⟩, rfl⟩
  let e : Q ≃ₐ[ℂ] Module.End ℂ S := AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩
  have he : ∀ t, ((e.symm t : Q) : Module.End ℂ S × Module.End ℂ X).1 = t := fun t => e.apply_symm_apply t
  refine ⟨ψ.comp (e.symm : Module.End ℂ S →ₐ[ℂ] Q), fun t f hf => ?_, fun t => ?_⟩
  · have := hcomm _ (e.symm t).2 f hf
    rw [he t] at this
    exact this
  · rw [← hmap₂]
    exact ⟨_, (e.symm t).2, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.LinearFormEqMulTraceOfTwistedInvariant
section
open scoped BigOperators

theorem UpperTheory.linearForm_eq_mul_trace_of_twisted_invariant :
    ∀ (P : Type) [AddCommGroup P] [Module ℂ P] [FiniteDimensional ℂ P] (J E : Module.End ℂ P) (l : Module.End ℂ P →ₗ[ℂ] ℂ), LinearMap.trace ℂ P (E * J) = 1 → (∀ a a' b : Module.End ℂ P, a' * J = J * a → l (b * a') = l (a * b)) → ∀ b, l b = l E * LinearMap.trace ℂ P (b * J) := by
  intro P _ _ _ J E l hE h
  have tr : ∀ (η : P →ₗ[ℂ] ℂ) (u : P), LinearMap.trace ℂ P (η.smulRight u) = η u := by
    intro η u
    have h0 := LinearMap.trace_eq_contract_apply ℂ P
      (TensorProduct.tmul ℂ (show Module.Dual ℂ P from η) u)
    have h1 : dualTensorHom ℂ P P (TensorProduct.tmul ℂ (show Module.Dual ℂ P from η) u)
        = η.smulRight u := by
      apply LinearMap.ext
      intro y
      simp [dualTensorHom_apply]
    rw [h1] at h0
    rw [h0]
    simp [contractLeft_apply]
  have key : ∀ (u x : P) (η ξ : P →ₗ[ℂ] ℂ),
      ξ (J x) * l (η.smulRight u) = η (J u) * l (ξ.smulRight x) := by
    intro u x η ξ
    have hc : (η.smulRight (J x)) * J = J * ((η ∘ₗ J).smulRight x) := by
      apply LinearMap.ext
      intro y
      simp [Module.End.mul_apply]
    have h1 := h ((η ∘ₗ J).smulRight x) (η.smulRight (J x)) (ξ.smulRight u) hc
    have e1 : ξ.smulRight u * η.smulRight (J x) = ξ (J x) • η.smulRight u := by
      apply LinearMap.ext
      intro y
      simp [Module.End.mul_apply, smul_smul, mul_comm]
    have e2 : (η ∘ₗ J).smulRight x * ξ.smulRight u = η (J u) • ξ.smulRight x := by
      apply LinearMap.ext
      intro y
      simp [Module.End.mul_apply, smul_smul, mul_comm]
    rw [e1, e2, map_smul, map_smul] at h1
    simpa [smul_eq_mul] using h1
  have hJ : ∃ x, J x ≠ 0 := by
    by_contra hne
    push_neg at hne
    have hJ0 : J = 0 := LinearMap.ext hne
    rw [hJ0] at hE
    simp at hE
  obtain ⟨x₀, hx₀⟩ := hJ
  have hφ : ∃ φ : Module.Dual ℂ P, φ (J x₀) ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact hx₀ ((Module.forall_dual_apply_eq_zero_iff ℂ (J x₀)).1 hne)
  obtain ⟨φ, hφ⟩ := hφ
  obtain ⟨ξ₀, hξ₀⟩ : ∃ ξ₀ : P →ₗ[ℂ] ℂ, ξ₀ (J x₀) = 1 :=
    ⟨(φ (J x₀))⁻¹ • φ, by simp [hφ]⟩
  have rank1 : ∀ (η : P →ₗ[ℂ] ℂ) (u : P),
      l (η.smulRight u) = l (ξ₀.smulRight x₀) * LinearMap.trace ℂ P (η.smulRight u * J) := by
    intro η u
    have e : η.smulRight u * J = (η ∘ₗ J).smulRight u := by
      apply LinearMap.ext
      intro y
      simp [Module.End.mul_apply]
    have hk := key u x₀ η ξ₀
    rw [hξ₀, one_mul] at hk
    rw [e, tr, hk]
    simp [mul_comm]
  have all : ∀ b : Module.End ℂ P,
      l b = l (ξ₀.smulRight x₀) * LinearMap.trace ℂ P (b * J) := by
    intro b
    obtain ⟨t, rfl⟩ := (dualTensorHomEquiv ℂ P P).surjective b
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul η u =>
      have h1 : dualTensorHomEquiv ℂ P P (TensorProduct.tmul ℂ η u)
          = LinearMap.smulRight (show P →ₗ[ℂ] ℂ from η) u := by
        apply LinearMap.ext
        intro y
        simp [dualTensorHomEquiv, dualTensorHom_apply]
      rw [h1]
      exact rank1 η u
    | add s t hs ht =>
      rw [map_add (f := _), map_add (f := _), add_mul, map_add (f := _), mul_add, hs, ht]
  intro b
  have hκ := all E
  rw [hE, mul_one] at hκ
  rw [hκ]
  exact all b
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.ListOfFnProdEqMulUpdateOneOfPairwiseCommute
section
open scoped BigOperators

theorem UpperTheory.list_ofFn_prod_eq_mul_update_one_of_pairwise_commute :
    ∀ (M : Type) [Monoid M] (r : ℕ) (a : Fin r → M), (∀ i j, i ≠ j → Commute (a i) (a j)) → ∀ i, (List.ofFn a).prod = a i * (List.ofFn (Function.update a i 1)).prod ∧ ∀ m : M, (∀ j, j ≠ i → Commute m (a j)) → Commute m (List.ofFn (Function.update a i 1)).prod := by
  intro M _ r a h i
  refine ⟨?_, ?_⟩
  · induction r with
    | zero => exact i.elim0
    | succ r ih =>
      refine Fin.cases ?_ (fun k => ?_) i
      · have h1 : (fun j : Fin r => Function.update a 0 1 j.succ) = fun j => a j.succ := by
          funext j
          rw [Function.update_of_ne (Fin.succ_ne_zero j)]
        rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, h1,
          Function.update_self, one_mul]
      · have h1 : (fun j : Fin r => Function.update a k.succ 1 j.succ)
            = Function.update (fun j : Fin r => a j.succ) k 1 := by
          funext j
          by_cases hj : j = k
          · subst hj
            rw [Function.update_self, Function.update_self]
          · rw [Function.update_of_ne hj,
              Function.update_of_ne (fun e => hj (Fin.succ_injective _ e))]
        have h2 := ih (fun j : Fin r => a j.succ)
          (fun i j hij => h _ _ (fun e => hij (Fin.succ_injective _ e))) k
        rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, h1,
          Function.update_of_ne (Fin.succ_ne_zero k).symm, h2, ← mul_assoc, ← mul_assoc,
          (h 0 k.succ (Fin.succ_ne_zero k).symm).eq]
  · intro m hm
    apply Commute.list_prod_right
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self]
      exact Commute.one_right m
    · rw [Function.update_of_ne hj]
      exact hm j hj
end

-- bundled from Development.AutomorphicArithmetic.TwistedTraces.TracePairingSeparatesEndomorphisms
section
open scoped BigOperators

open TensorProduct in
private lemma traceForm {S : Type} [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]
    (τ : Module.End ℂ S →ₗ[ℂ] ℂ) (hτ : ∀ a b, τ (a * b) = τ (b * a))
    (ξ : Module.Dual ℂ S) (e : S) (h : ξ e = 1) (t : Module.End ℂ S) :
    τ t = LinearMap.trace ℂ S t * τ (dualTensorHom ℂ S S (ξ ⊗ₜ e)) := by
  obtain ⟨u, rfl⟩ := (dualTensorHomEquiv ℂ S S).surjective t
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), add_mul, hx, hy]
  | tmul f x =>
    have hab : (dualTensorHom ℂ S S (f ⊗ₜ x)) =
        (dualTensorHom ℂ S S (ξ ⊗ₜ x)) * (dualTensorHom ℂ S S (f ⊗ₜ e)) := by
      ext y
      simp [dualTensorHom_apply, h]
    have hba : (dualTensorHom ℂ S S (f ⊗ₜ e)) * (dualTensorHom ℂ S S (ξ ⊗ₜ x)) =
        f x • dualTensorHom ℂ S S (ξ ⊗ₜ e) := by
      ext y
      simp [dualTensorHom_apply, smul_smul, mul_comm]
    have hE : dualTensorHomEquiv ℂ S S (f ⊗ₜ x) = dualTensorHom ℂ S S (f ⊗ₜ x) := rfl
    rw [hE, LinearMap.trace_eq_contract_apply, contractLeft_apply, hab, hτ, hba, map_smul,
      smul_eq_mul]

private lemma existsDual (S : Type) [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]
    [Nontrivial S] : ∃ (ξ : Module.Dual ℂ S) (e : S), ξ e = 1 := by
  obtain ⟨e, he⟩ := exists_ne (0 : S)
  have : ∃ f : Module.Dual ℂ S, f e ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact he ((Module.forall_dual_apply_eq_zero_iff ℂ e).1 hc)
  obtain ⟨f, hf⟩ := this
  exact ⟨(f e)⁻¹ • f, e, by simp [hf]⟩

open TensorProduct in
private lemma commuting_idempotent_trace {X : Type} [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] :
    ∀ (r : ℕ) (S : Fin r → Type) [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)]
      [∀ i, FiniteDimensional ℂ (S i)] [∀ i, Nontrivial (S i)]
      (c : ∀ i, Module.End ℂ (S i) →ₐ[ℂ] Module.End ℂ X),
      (∀ i j, i ≠ j → ∀ s t, Commute (c i s) (c j t)) →
      ∀ B : Module.End ℂ X, IsIdempotentElem B → (∀ i s, Commute B (c i s)) →
      ∃ N : ℕ, ∀ t : ∀ i, Module.End ℂ (S i),
        LinearMap.trace ℂ X (B * (List.ofFn fun i => c i (t i)).prod)
          = N * ∏ i, LinearMap.trace ℂ (S i) (t i) := by
  intro r
  induction r with
  | zero =>
    intro S _ _ _ _ c hc B hB hcomm
    refine ⟨Module.finrank ℂ (LinearMap.range B), fun t => ?_⟩
    have := (LinearMap.IsIdempotentElem.isProj_range B hB).trace
    simpa using this
  | succ r ih =>
    intro S _ _ _ _ c hc B hB hcomm
    obtain ⟨ξ, e, h1⟩ := existsDual (S 0)
    set E : Module.End ℂ (S 0) := dualTensorHom ℂ (S 0) (S 0) (ξ ⊗ₜ e) with hEdef
    have hE : IsIdempotentElem E := by
      show E * E = E
      ext y
      simp [hEdef, dualTensorHom_apply, h1]
    have hB' : IsIdempotentElem (B * c 0 E) :=
      IsIdempotentElem.mul_of_commute (hcomm 0 E) hB (hE.map (c 0))
    have hcomm' : ∀ (i : Fin r) (s : Module.End ℂ (S i.succ)),
        Commute (B * c 0 E) (c i.succ s) := fun i s =>
      (hcomm i.succ s).mul_left (hc 0 i.succ (Fin.succ_ne_zero i).symm E s)
    obtain ⟨N, hN⟩ := ih (fun i => S i.succ) (fun i => c i.succ)
      (fun i j hij s t => hc i.succ j.succ (fun h => hij (Fin.succ_injective _ h)) s t)
      (B * c 0 E) hB' hcomm'
    refine ⟨N, fun t => ?_⟩
    rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
    set A : Module.End ℂ X := (List.ofFn fun i : Fin r => c i.succ (t i.succ)).prod with hA
    have hAc : ∀ s, Commute (c 0 s) A := fun s => by
      refine Commute.list_prod_right _ _ ?_
      intro x hx
      obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
      exact hc 0 i.succ (Fin.succ_ne_zero i).symm s _
    let τ : Module.End ℂ (S 0) →ₗ[ℂ] ℂ :=
      (LinearMap.trace ℂ X) ∘ₗ (LinearMap.mulRight ℂ A) ∘ₗ (LinearMap.mulLeft ℂ B) ∘ₗ
        (c 0).toLinearMap
    have hτv : ∀ s, τ s = LinearMap.trace ℂ X (B * c 0 s * A) := fun s => rfl
    have hτ : ∀ a b, τ (a * b) = τ (b * a) := by
      intro a b
      rw [hτv, hτv, map_mul (c 0), map_mul (c 0)]
      have e1 : B * (c 0 a * c 0 b) * A = c 0 a * (B * c 0 b * A) := by
        rw [← mul_assoc B, (hcomm 0 a).eq]
        simp only [mul_assoc]
      have e2 : (B * c 0 b * A) * c 0 a = B * (c 0 b * c 0 a) * A := by
        rw [mul_assoc (B * c 0 b) A, ← (hAc a).eq]
        simp only [mul_assoc]
      rw [e1, LinearMap.trace_mul_comm, e2]
    have key := traceForm τ hτ ξ e h1 (t 0)
    have hN' := hN (fun i => t i.succ)
    rw [← mul_assoc, ← hτv, key, hτv, ← hEdef, hN']
    ring

theorem UpperTheory.trace_pairing_separates_endomorphisms :
    ∀ (r : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] (S : Fin r → Type) [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)] [∀ i, FiniteDimensional ℂ (S i)] [∀ i, Nontrivial (S i)] (c : ∀ i, Module.End ℂ (S i) →ₐ[ℂ] Module.End ℂ X), (∀ i j, i ≠ j → ∀ s t, Commute (c i s) (c j t)) → ∃ N : ℕ, ∀ t : ∀ i, Module.End ℂ (S i), LinearMap.trace ℂ X (List.ofFn fun i => c i (t i)).prod = N * ∏ i, LinearMap.trace ℂ (S i) (t i) := by
  intro r X _ _ _ S _ _ _ _ c hc
  obtain ⟨N, hN⟩ := commuting_idempotent_trace r S c hc 1 IsIdempotentElem.one (fun _ _ => Commute.one_left _)
  exact ⟨N, fun t => by simpa using hN t⟩
end

