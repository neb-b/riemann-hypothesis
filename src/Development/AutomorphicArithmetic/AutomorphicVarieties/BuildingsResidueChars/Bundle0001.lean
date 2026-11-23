module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsAutomorphicFunctionWithValuesOnCosetReps
section
theorem UpperTheory.exists_automorphic_function_with_values_on_coset_reps :
    ∀ (Γ G K A M ι : Type) [Group Γ] [Group G] [Group K] [CommRing A] [AddCommGroup M] [Module A M] (gl : Γ →* G) (j : K →* G) (ρ : Representation A K M) (x : ι → G), (∀ g, ∃ γ i k, g = gl γ * x i * j k) → (∀ i i' γ k, x i' = gl γ * x i * j k → i = i') → (∀ i γ k, gl γ * x i = x i * j k → ρ k = 1) → ∀ v : ι → M, ∃ Φ : G → M, (∀ γ g, Φ (gl γ * g) = Φ g) ∧ (∀ g k, Φ (g * j k) = ρ k⁻¹ (Φ g)) ∧ ∀ i, Φ (x i) = v i := by
  intro Γ G K A M ι _ _ _ _ _ _ gl j ρ x hcov huniq hstab v
  have key : ∀ γ i k γ' i' k', gl γ * x i * j k = gl γ' * x i' * j k' →
      i = i' ∧ ρ k⁻¹ (v i) = ρ k'⁻¹ (v i') := by
    intro γ i k γ' i' k' h
    have e : x i' = gl (γ'⁻¹ * γ) * x i * j (k * k'⁻¹) := by
      calc x i' = (gl γ')⁻¹ * (gl γ' * x i' * j k') * (j k')⁻¹ := by group
        _ = (gl γ')⁻¹ * (gl γ * x i * j k) * (j k')⁻¹ := by rw [h]
        _ = gl (γ'⁻¹ * γ) * x i * j (k * k'⁻¹) := by
          simp only [map_mul, map_inv]
          group
    have hii : i = i' := huniq i i' _ _ e
    subst hii
    refine ⟨rfl, ?_⟩
    have e2 : gl (γ'⁻¹ * γ) * x i = x i * j (k' * k⁻¹) := by
      calc gl (γ'⁻¹ * γ) * x i = (gl (γ'⁻¹ * γ) * x i * j (k * k'⁻¹)) * (j (k * k'⁻¹))⁻¹ := by group
        _ = x i * j (k' * k⁻¹) := by
          rw [← e]
          simp only [map_mul, map_inv]
          group
    have hρ : ρ (k' * k⁻¹) = 1 := hstab i _ _ e2
    have : ρ k⁻¹ = ρ k'⁻¹ := by
      calc ρ k⁻¹ = ρ (k'⁻¹ * (k' * k⁻¹)) := by group
        _ = ρ k'⁻¹ * ρ (k' * k⁻¹) := map_mul _ _ _
        _ = ρ k'⁻¹ := by rw [hρ, mul_one]
    rw [this]
  choose γf iF kF hg using hcov
  refine ⟨fun g => ρ (kF g)⁻¹ (v (iF g)), ?_, ?_, ?_⟩
  · intro γ g
    have h : gl (γf (gl γ * g)) * x (iF (gl γ * g)) * j (kF (gl γ * g)) =
        gl (γ * γf g) * x (iF g) * j (kF g) := by
      rw [← hg (gl γ * g)]
      conv_lhs => rw [hg g]
      simp only [map_mul, mul_assoc]
    exact (key _ _ _ _ _ _ h).2
  · intro g k
    have h : gl (γf (g * j k)) * x (iF (g * j k)) * j (kF (g * j k)) =
        gl (γf g) * x (iF g) * j (kF g * k) := by
      rw [← hg (g * j k)]
      conv_lhs => rw [hg g]
      simp only [map_mul, mul_assoc]
    dsimp only
    rw [(key _ _ _ _ _ _ h).2, mul_inv_rev, map_mul]
    rfl
  · intro i
    have h : gl (γf (x i)) * x (iF (x i)) * j (kF (x i)) = gl 1 * x i * j 1 := by
      rw [← hg (x i), map_one, map_one, one_mul, mul_one]
    dsimp only
    rw [(key _ _ _ _ _ _ h).2, inv_one, map_one]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsEigenvectorOfRoot
section
open Polynomial

theorem UpperTheory.exists_eigenvector_of_root :
    ∀ {L C D W : Type} [Field L] [Field C] [AddCommGroup D] [Module L D] [FiniteDimensional L D] [AddCommGroup W] [Module C W] [FiniteDimensional C W] (s : L →+* C) (j : D →+ W) (S : Module.End L D) (T : Module.End C W), (∀ (a : L) (x : D), j (a • x) = s a • j x) → Submodule.span C (Set.range j) = ⊤ → (∀ x, T (j x) = j (S x)) → ∀ (q : L[X]) (b : C), b ∈ T.charpoly.roots → q.eval₂ s b = 0 → ∃ x : D, x ≠ 0 ∧ aeval S q x = 0 := by
  intro L C D W _ _ _ _ _ _ _ _ s j S T hj hspan hT q b hb hq
  by_contra hcon
  have hinj : Function.Injective (aeval S q) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    exact hcon ⟨x, h0, hx⟩
  have hsurj : Function.Surjective (aeval S q) := LinearMap.injective_iff_surjective.mp hinj
  have hpow : ∀ (n : ℕ) (x : D), (T ^ n) (j x) = j ((S ^ n) x) := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, hT, ih]
  have hcomm : ∀ (p : L[X]) (x : D), aeval T (p.map s) (j x) = j (aeval S p x) := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p r hp hr =>
      intro x
      simp only [Polynomial.map_add (f := _), map_add (f := _), LinearMap.add_apply, hp, hr]
    | monomial n a =>
      intro x
      rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, Module.End.mul_apply,
        Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply, hj, hpow]
  have hsurj' : Function.Surjective (aeval T (q.map s)) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨j x, hcomm q x⟩
  have hinj' : Function.Injective (aeval T (q.map s)) :=
    LinearMap.injective_iff_surjective.mpr hsurj'
  have hroot : T.charpoly.IsRoot b := (mem_roots'.mp hb).2
  have hev : T.HasEigenvalue b := (Module.End.hasEigenvalue_iff_isRoot_charpoly T b).mpr hroot
  obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
  have h1 := Module.End.aeval_apply_of_hasEigenvector (p := q.map s) hv
  rw [eval_map, hq, zero_smul] at h1
  exact hv.2 (hinj' (by rw [h1, map_zero]))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsEquivariantProjectionsOfSumIrreducible
section
open scoped MonoidAlgebra

private theorem ss_proj {R V : Type} [Ring R] [AddCommGroup V] [Module R V]
    [IsSemisimpleModule R V] (s : Finset V) :
    ∃ (κ : Type) (_ : Fintype κ) (S : κ → Submodule R V) (P : κ → V →ₗ[R] V),
      (∀ i, IsAtom (S i)) ∧ (∀ i w, P i w ∈ S i) ∧ ∀ w ∈ s, ∑ i, P i w = w := by
  classical
  obtain ⟨t, e, -, ht⟩ := IsSemisimpleModule.exists_linearEquiv_dfinsupp R V
  let K : Finset t := s.biUnion fun w => (e w).support
  let Q : t → V →ₗ[R] V := fun m =>
    e.symm.toLinearMap ∘ₗ DFinsupp.lsingle (R := R) (M := fun m : t => m.1) m ∘ₗ
      DFinsupp.lapply (R := R) (M := fun m : t => m.1) m ∘ₗ e.toLinearMap
  let j : (m : t) → (m.1 →ₗ[R] V) := fun m =>
    e.symm.toLinearMap ∘ₗ DFinsupp.lsingle (R := R) (M := fun m : t => m.1) m
  have hj : ∀ m, Function.Injective (j m) := fun m =>
    e.symm.injective.comp (DFinsupp.single_injective (β := fun m : t => m.1) (i := m))
  refine ⟨K, inferInstance, fun i => LinearMap.range (j i.1), fun i => Q i.1, ?_, ?_, ?_⟩
  · intro i
    rw [← isSimpleModule_iff_isAtom]
    have := ht i.1
    exact IsSimpleModule.congr (LinearEquiv.ofInjective _ (hj i.1)).symm
  · intro i w
    exact ⟨e w i.1, rfl⟩
  · intro w hw
    rw [Finset.sum_coe_sort K (fun i => Q i w)]
    apply e.injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    have h1 : ∀ i, e (Q i w) = DFinsupp.single i (e w i) := fun i => by simp [Q]
    simp_rw [h1]
    ext1 m
    rw [DFinsupp.finsetSum_apply]
    rw [Finset.sum_eq_single m]
    · simp
    · intro b _ hb
      exact DFinsupp.single_eq_of_ne hb.symm
    · intro hm
      have : e w m = 0 := by
        by_contra h
        exact hm (Finset.mem_biUnion.mpr ⟨w, hw, DFinsupp.mem_support_iff.mpr h⟩)
      simp [this]

section
variable {H W : Type} [Group H] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H W)

private noncomputable def toSub (U : Submodule ℂ W) (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U) :
    Submodule ℂ[H] ρ.asModule where
  carrier := {x | ρ.asModuleEquiv x ∈ U}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, map_add (f := _)] at *
    exact U.add_mem ha hb
  zero_mem' := by simp
  smul_mem' := fun c x hx => by
    simp only [Set.mem_ofPred_eq] at *
    rw [Representation.asModuleEquiv_map_smul]
    exact ρ.asAlgebraHom_mem_of_forall_mem U hU _ hx c

private theorem mem_toSub (U : Submodule ℂ W) (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U) (x : ρ.asModule) :
    x ∈ toSub ρ U hU ↔ ρ.asModuleEquiv x ∈ U := Iff.rfl

private noncomputable def fromSub (N : Submodule ℂ[H] ρ.asModule) : Submodule ℂ W :=
  (N.restrictScalars ℂ).comap ρ.asModuleEquiv.symm.toLinearMap

private theorem mem_fromSub (N : Submodule ℂ[H] ρ.asModule) (x : W) :
    x ∈ fromSub ρ N ↔ ρ.asModuleEquiv.symm x ∈ N := Iff.rfl

private theorem fromSub_inv (N : Submodule ℂ[H] ρ.asModule) (g : H) (u : W)
    (hu : u ∈ fromSub ρ N) : ρ g u ∈ fromSub ρ N := by
  rw [mem_fromSub] at *
  rw [Representation.asModuleEquiv_symm_map_rho]
  exact N.smul_mem _ hu

private theorem from_to (U : Submodule ℂ W) (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U) :
    fromSub ρ (toSub ρ U hU) = U := by
  ext x; simp [mem_fromSub, mem_toSub]

private theorem from_le_iff (A B : Submodule ℂ[H] ρ.asModule) :
    fromSub ρ A ≤ fromSub ρ B ↔ A ≤ B := by
  constructor
  · intro h x hx
    have := @h (ρ.asModuleEquiv x) (by simpa [mem_fromSub] using hx)
    simpa [mem_fromSub] using this
  · intro h x hx
    exact h hx

private theorem from_inj {A B : Submodule ℂ[H] ρ.asModule} (h : fromSub ρ A = fromSub ρ B) :
    A = B :=
  le_antisymm ((from_le_iff ρ A B).mp h.le) ((from_le_iff ρ B A).mp h.ge)

private theorem from_bot : fromSub ρ ⊥ = ⊥ := by
  ext x; simp [mem_fromSub]

private theorem atom_iff (A : Submodule ℂ[H] ρ.asModule) :
    IsAtom A ↔ fromSub ρ A ≠ ⊥ ∧
      ∀ N ≤ fromSub ρ A, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = fromSub ρ A := by
  constructor
  · intro hA
    refine ⟨fun h => hA.1 (from_inj ρ (h.trans (from_bot ρ).symm)), fun N hN hi => ?_⟩
    rw [← from_to ρ N hi] at hN ⊢
    rcases hA.le_iff.mp ((from_le_iff ρ _ _).mp hN) with h | h
    · left; rw [h, from_bot]
    · right; rw [h]
  · rintro ⟨h0, h⟩
    refine ⟨fun hA => h0 (by rw [hA, from_bot]), fun B hB => ?_⟩
    rcases h _ ((from_le_iff ρ _ _).mpr hB.le) (fromSub_inv ρ B) with h | h
    · exact from_inj ρ (h.trans (from_bot ρ).symm)
    · exact absurd (from_inj ρ h) hB.ne

end

theorem UpperTheory.exists_equivariant_projections_of_sum_irreducible :
    ∀ (H W : Type) [Group H] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H W), (∀ x : W, x ∈ ⨆ U : {U : Submodule ℂ W // U ≠ ⊥ ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧ ∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U}, U.1) → ∀ M : Submodule ℂ W, FiniteDimensional ℂ M → ∃ (κ : Type) (_ : Fintype κ) (U : κ → Submodule ℂ W) (P : κ → W →ₗ[ℂ] W), (∀ i, U i ≠ ⊥ ∧ (∀ g, ∀ u ∈ U i, ρ g u ∈ U i) ∧ ∀ N ≤ U i, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U i) ∧ (∀ i w, P i w ∈ U i) ∧ (∀ i g w, P i (ρ g w) = ρ g (P i w)) ∧ ∀ w ∈ M, ∑ i, P i w = w := by
  intro H W _ _ _ ρ hsum M hM
  classical
  have : IsSemisimpleModule ℂ[H] ρ.asModule := by
    apply IsSemisimpleModule.of_sSup_simples_eq_top
    rw [eq_top_iff]
    intro y _
    have hle : (⨆ U : {U : Submodule ℂ W // U ≠ ⊥ ∧ (∀ g, ∀ u ∈ U, ρ g u ∈ U) ∧
        ∀ N ≤ U, (∀ g, ∀ u ∈ N, ρ g u ∈ N) → N = ⊥ ∨ N = U}, U.1) ≤
        fromSub ρ (sSup {m : Submodule ℂ[H] ρ.asModule | IsSimpleModule ℂ[H] m}) := by
      refine iSup_le ?_
      rintro ⟨U, h0, hi, hU⟩
      show U ≤ _
      rw [← from_to ρ U hi, from_le_iff]
      apply le_sSup
      show IsSimpleModule ℂ[H] (toSub ρ U hi)
      rw [isSimpleModule_iff_isAtom, atom_iff, from_to]
      exact ⟨h0, hU⟩
    have := hle (hsum (ρ.asModuleEquiv y))
    simpa [mem_fromSub] using this
  obtain ⟨s, hs⟩ : M.FG := (Submodule.fg_iff_finiteDimensional M).mpr hM
  obtain ⟨κ, hκ, S, P, hS, hP, hsum'⟩ :=
    ss_proj (R := ℂ[H]) (V := ρ.asModule) (s.image ρ.asModuleEquiv.symm)
  let Q : κ → W →ₗ[ℂ] W := fun i =>
    ρ.asModuleEquiv.toLinearMap ∘ₗ (P i).restrictScalars ℂ ∘ₗ ρ.asModuleEquiv.symm.toLinearMap
  have hQ : ∀ i w, Q i w = ρ.asModuleEquiv (P i (ρ.asModuleEquiv.symm w)) := fun _ _ => rfl
  refine ⟨κ, hκ, fun i => fromSub ρ (S i), Q, ?_, ?_, ?_, ?_⟩
  · intro i
    have := (atom_iff ρ (S i)).mp (hS i)
    exact ⟨this.1, fromSub_inv ρ _, this.2⟩
  · intro i w
    rw [mem_fromSub, hQ, LinearEquiv.symm_apply_apply]
    exact hP i _
  · intro i g w
    apply ρ.asModuleEquiv.symm.injective
    rw [Representation.asModuleEquiv_symm_map_rho, hQ, hQ, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply, Representation.asModuleEquiv_symm_map_rho, map_smul]
  · intro w hw
    rw [← hs] at hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      simp_rw [hQ]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, hsum' _ (Finset.mem_image_of_mem _ hx), LinearEquiv.apply_symm_apply]
    | zero => simp
    | add x y _ _ hx hy => simp_rw [map_add (f := _)]; rw [Finset.sum_add_distrib, hx, hy]
    | smul c x _ hx => simp_rw [map_smul]; rw [← Finset.smul_sum, hx]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsFactorDualEmbeddingOfNeZeroTensor
section
open scoped TensorProduct

theorem UpperTheory.exists_factor_dual_embedding_of_ne_zero_tensor :
    ∀ (I : Type) [Finite I] (W : I → Type) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] [∀ i, FiniteDimensional ℂ (W i)] (N : Type) [AddCommGroup N] [Module ℂ N] (Φ : Module.Dual ℂ (⨂[ℂ] i, W i) →ₗ[ℂ] N), Φ ≠ 0 → ∀ y : I, ∃ E : Module.Dual ℂ (W y) →ₗ[ℂ] Module.Dual ℂ (⨂[ℂ] i, W i), Φ ∘ₗ E ≠ 0 ∧ ∀ T : ∀ i, W i →ₗ[ℂ] W i, (∀ i, i ≠ y → T i = LinearMap.id) → ∀ m, E m ∘ₗ PiTensorProduct.map T = E (m ∘ₗ T y) := by
  intro I _ W _ _ _ N _ _ Φ hΦ y
  classical
  have := Fintype.ofFinite I
  have hinv := PiTensorProduct.dualDistrib_dualDistribInvOfBasis_left_inverse
    (R := ℂ) (M := W) (fun i => Module.Free.chooseBasis ℂ (W i))
  have hf : ∃ f : ∀ i, Module.Dual ℂ (W i),
      Φ (PiTensorProduct.dualDistrib (PiTensorProduct.tprod ℂ f)) ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : Φ ∘ₗ PiTensorProduct.dualDistrib = 0 := by
      apply PiTensorProduct.ext
      ext f
      simpa using h f
    apply hΦ
    rw [← LinearMap.comp_id Φ, ← hinv, ← LinearMap.comp_assoc, h0, LinearMap.zero_comp]
  obtain ⟨f, hf⟩ := hf
  refine ⟨PiTensorProduct.dualDistrib ∘ₗ (PiTensorProduct.tprod ℂ).toLinearMap f y, ?_, ?_⟩
  · intro h
    apply hf
    have := LinearMap.congr_fun h (f y)
    simpa using this
  · intro T hT m
    apply PiTensorProduct.ext
    ext w
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
      PiTensorProduct.map_tprod, MultilinearMap.toLinearMap_apply,
      PiTensorProduct.dualDistrib_apply]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : i = y
    · subst hi
      simp
    · simp [Function.update_of_ne hi, hT i hi]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsIntegralClosurePreimageOfIsIntegral
section
open Polynomial in
theorem UpperTheory.exists_integralClosure_preimage_of_isIntegral :
    ∀ (R E k : Type) [CommRing R] [Field E] [IsAlgClosed E] [Algebra R E] [CommRing k] [IsDomain k] (ψ : integralClosure R E →+* k) (x : k), IsIntegral ℤ x → ∃ y, ψ y = x := by
  intro R E k _ _ _ _ _ _ ψ x hx
  classical
  obtain ⟨p, hpm, hpx⟩ := hx
  set q : E[X] := p.map (algebraMap ℤ E) with hq
  have hqm : q.Monic := hpm.map _
  have hqs : q.Splits := IsAlgClosed.splits q
  let lift : E → integralClosure R E := fun a => if h : IsIntegral R a then ⟨a, h⟩ else 0
  have hlift : ∀ a ∈ q.roots, ((lift a : integralClosure R E) : E) = a := by
    intro a ha
    have hr : q.IsRoot a := (mem_roots hqm.ne_zero).1 ha
    have hi : IsIntegral ℤ a := ⟨p, hpm, by
      rw [eval₂_eq_eval_map]
      exact hr⟩
    have hiR : IsIntegral R a := hi.tower_top
    simp [lift, hiR]
  have hfac : p.map (algebraMap ℤ (integralClosure R E)) = (q.roots.map fun a => X - C (lift a)).prod := by
    apply Polynomial.map_injective (algebraMap (integralClosure R E) E) Subtype.val_injective
    rw [Polynomial.map_map, Polynomial.map_multiset_prod, Multiset.map_map]
    have e : (algebraMap (integralClosure R E) E).comp (algebraMap ℤ (integralClosure R E)) = algebraMap ℤ E :=
      RingHom.ext_int _ _
    rw [e, ← hq]
    conv_lhs => rw [hqs.eq_prod_roots_of_monic hqm]
    congr 1
    apply Multiset.map_congr rfl
    intro a ha
    simp only [Function.comp_apply, Polynomial.map_sub, map_X, map_C]
    congr 2
    exact (hlift a ha).symm
  have hk : p.map (algebraMap ℤ k) = (q.roots.map fun a => X - C (ψ (lift a))).prod := by
    have e : ψ.comp (algebraMap ℤ (integralClosure R E)) = algebraMap ℤ k := RingHom.ext_int _ _
    rw [← e, ← Polynomial.map_map, hfac, Polynomial.map_multiset_prod, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    simp
  have h0 : (p.map (algebraMap ℤ k)).eval x = 0 := by
    rw [eval_map]
    exact hpx
  rw [hk, eval_multiset_prod, Multiset.map_map, Multiset.prod_eq_zero_iff] at h0
  obtain ⟨a, _, ha⟩ := Multiset.mem_map.1 h0
  refine ⟨lift a, ?_⟩
  simp only [Function.comp_apply, eval_sub, eval_X, eval_C] at ha
  exact (sub_eq_zero.1 ha).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsLinearPreimageOfSuccessiveApproximation
section
theorem UpperTheory.exists_linear_preimage_of_successive_approximation :
    ∀ (A M ι : Type) [CommRing A] [AddCommGroup M] [Module A M] [Fintype ι] (I : Ideal A) [IsAdicComplete I A] (V : ℕ → Submodule A M) (σ : (ι → A) →ₗ[A] M), Antitone V → (∀ k, (I ^ k • ⊤ : Submodule A M) ≤ V k) → (∀ f, (∀ k, f ∈ V k) → f = 0) → (∀ j, ∀ f ∈ V j, ∃ a : ι → A, (∀ i, a i ∈ I ^ j) ∧ f - σ a ∈ V (j + 1)) → ∀ j, ∀ f ∈ V j, ∃ a : ι → A, (∀ i, a i ∈ I ^ j) ∧ σ a = f := by
  intro A M ι _ _ _ _ I _ V σ hV hI hsep hstep j f hf
  classical
  let a' : ℕ → M → ι → A := fun k g => if h : g ∈ V k then (hstep k g h).choose else 0
  have ha' : ∀ k g, g ∈ V k → (∀ i, a' k g i ∈ I ^ k) ∧ g - σ (a' k g) ∈ V (k + 1) := by
    intro k g h
    simp only [a', dif_pos h]
    exact (hstep k g h).choose_spec
  let r : ℕ → M := fun n => Nat.rec f (fun n g => g - σ (a' (j + n) g)) n
  have hrs : ∀ n, r (n + 1) = r n - σ (a' (j + n) (r n)) := fun n => rfl
  have hr : ∀ n, r n ∈ V (j + n) := by
    intro n
    induction n with
    | zero => exact hf
    | succ n ih =>
      rw [hrs, ← add_assoc]
      exact (ha' _ _ ih).2
  let b : ℕ → ι → A := fun n => a' (j + n) (r n)
  have hb : ∀ n i, b n i ∈ I ^ (j + n) := fun n => (ha' _ _ (hr n)).1
  have hrsum : ∀ N, r N = f - σ (∑ n ∈ Finset.range N, b n) := by
    intro N
    induction N with
    | zero => simp [r]
    | succ N ih =>
      show r N - σ (b N) = f - σ (∑ n ∈ Finset.range (N + 1), b n)
      rw [ih, Finset.sum_range_succ, map_add (f := _)]
      abel
  have hlim : ∀ i, ∃ L : A, ∀ n,
      (∑ k ∈ Finset.range n, b k i) ≡ L [SMOD (I ^ n • ⊤ : Submodule A A)] := by
    intro i
    refine IsPrecomplete.prec (inferInstance : IsPrecomplete I A) ?_
    intro m n hmn
    rw [SModEq.sub_mem, ← neg_sub, Submodule.neg_mem_iff, ← Finset.sum_Ico_eq_sub _ hmn]
    refine Submodule.sum_mem _ (fun k hk => ?_)
    have hmk : m ≤ j + k := by
      have := (Finset.mem_Ico.mp hk).1
      omega
    simpa using Submodule.smul_mem_smul (Ideal.pow_le_pow_right hmk (hb k i))
      (Submodule.mem_top : (1 : A) ∈ (⊤ : Submodule A A))
  choose L hL using hlim
  refine ⟨L, fun i => ?_, ?_⟩
  · have h1 := SModEq.sub_mem.mp (hL i j)
    have h2 : (∑ k ∈ Finset.range j, b k i) ∈ I ^ j :=
      Submodule.sum_mem _ (fun k _ => Ideal.pow_le_pow_right (by omega) (hb k i))
    have h1' : (∑ k ∈ Finset.range j, b k i) - L i ∈ I ^ j := by
      simpa [smul_eq_mul, Ideal.mul_top] using h1
    simpa using Submodule.sub_mem _ h2 h1'
  · have h0 : f - σ L = 0 := by
      apply hsep
      intro N
      have hv : ∀ i, ((∑ n ∈ Finset.range N, b n) - L) i ∈ I ^ N := by
        intro i
        have := SModEq.sub_mem.mp (hL i N)
        simpa [Finset.sum_apply, smul_eq_mul, Ideal.mul_top] using this
      have hσ : σ ((∑ n ∈ Finset.range N, b n) - L) ∈ (I ^ N • ⊤ : Submodule A M) := by
        set v := (∑ n ∈ Finset.range N, b n) - L
        set_option synthInstance.maxHeartbeats 100000 in
          rw [pi_eq_sum_univ v, map_sum]
        refine Submodule.sum_mem _ (fun i _ => ?_)
        rw [map_smul]
        exact Submodule.smul_mem_smul (hv i) Submodule.mem_top
      have e : f - σ L = r N + σ ((∑ n ∈ Finset.range N, b n) - L) := by
        rw [hrsum, map_sub]
        abel
      rw [e]
      exact Submodule.add_mem _ (hV (by omega : N ≤ j + N) (hr N)) (hI N hσ)
    exact (sub_eq_zero.mp h0).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.KrullDimQuotientLeCardOfRadicalParameters
section
open IsLocalRing

theorem UpperTheory.krullDim_quotient_le_card_of_radical_parameters :
    ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] (q : Ideal B) (κ : Type) [Finite κ] (x : κ → B), (∀ k, x k ∈ maximalIdeal B) → (∀ p : Ideal B, p.IsPrime → q ≤ p → (∀ k, x k ∈ p) → maximalIdeal B ≤ p) → ringKrullDim (B ⧸ q) ≤ Nat.card κ := by
  intro B _ _ _ q κ _ x hx h
  classical
  by_cases hq : q = ⊤
  · subst hq
    rw [ringKrullDim_eq_bot_of_subsingleton]
    exact bot_le
  haveI : Nontrivial (B ⧸ q) := Ideal.Quotient.nontrivial_iff.mpr hq
  haveI : IsLocalRing (B ⧸ q) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk q) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  let s : Set (B ⧸ q) := Set.range (fun k => Ideal.Quotient.mk q (x k))
  have hs : s.Finite := Set.finite_range _
  have hmin : maximalIdeal (B ⧸ q) ∈ (Ideal.span s).minimalPrimes := by
    refine ⟨⟨inferInstance, ?_⟩, ?_⟩
    · rw [Ideal.span_le]
      rintro _ ⟨k, rfl⟩
      exact map_nonunit (Ideal.Quotient.mk q) _ (hx k)
    · rintro P ⟨hP, hsP⟩ _
      have h1 : maximalIdeal B ≤ P.comap (Ideal.Quotient.mk q) := by
        refine h _ (Ideal.comap_isPrime _ _) ?_ ?_
        · intro a ha
          rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
          exact P.zero_mem
        · intro k
          exact hsP (Ideal.subset_span ⟨k, rfl⟩)
      intro y hy
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
      apply h1
      rw [mem_maximalIdeal] at hy ⊢
      exact fun hu => hy (hu.map _)
  have h2 := Ideal.height_le_card_of_mem_minimalPrimes_span hs hmin
  have h3 : s.ncard ≤ Nat.card κ := by
    rw [← Set.ncard_univ, show s = (fun k => Ideal.Quotient.mk q (x k)) '' Set.univ from Set.image_univ.symm]
    exact Set.ncard_image_le Set.finite_univ
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  have h4 : (maximalIdeal (B ⧸ q)).height ≤ (Nat.card κ : ℕ∞) := h2.trans (by exact_mod_cast h3)
  exact_mod_cast h4
end

