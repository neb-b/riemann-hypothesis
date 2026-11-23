module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup
public import Mathlib.Topology.Algebra.OpenSubgroup
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Uniform
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsIdempotentDecompositionMixedSpace
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem one_tmul_add_tmul_mul_I_eq_smul_of_sq_eq_one {R : Type} [CommRing R] [Algebra ℝ R] (g : ℂ →ₗ[ℝ] R) (σ z : ℂ)
    (hσ : σ * σ = 1) :
    (1 : ℂ) ⊗ₜ[ℝ] g z + (σ * Complex.I) ⊗ₜ[ℝ] g (z * Complex.I) =
      ((z.re : ℂ) - σ * z.im * Complex.I) •
        ((1 : ℂ) ⊗ₜ[ℝ] g 1 + (σ * Complex.I) ⊗ₜ[ℝ] g Complex.I) := by
  have h1 : g z = z.re • g 1 + z.im • g Complex.I := by
    rw [← map_smul, ← map_smul, ← map_add (f := _)]
    congr 1
    apply Complex.ext <;> simp
  have h2 : g (z * Complex.I) = z.re • g Complex.I + (-z.im) • g 1 := by
    rw [← map_smul, ← map_smul, ← map_add (f := _)]
    congr 1
    apply Complex.ext <;> simp
  have hc : ∀ (c : ℂ) (u : R), c ⊗ₜ[ℝ] u = c • ((1 : ℂ) ⊗ₜ[ℝ] u) := by
    intro c u
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, h2]
  simp only [TensorProduct.tmul_add, TensorProduct.tmul_smul]
  rw [hc (σ * Complex.I) (g 1), hc (σ * Complex.I) (g Complex.I)]
  simp only [← algebraMap_smul ℂ z.re, ← algebraMap_smul ℂ z.im, ← algebraMap_smul ℂ (-z.im)]
  match_scalars <;> simp only [Complex.coe_algebraMap, Complex.ofReal_neg] <;>
    first
    | ring1
    | linear_combination (z.im * σ * σ) * Complex.I_mul_I - z.im * hσ

private theorem idem_lemma_2 (A B : Type) [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] :
    Nonempty (Idem ((A → ℝ) × (B → ℂ)) (A ⊕ (B × Bool))) := by
  let σ : Bool → ℂ := fun s => if s then 1 else -1
  have hσ : ∀ s, σ s * σ s = 1 := by
    intro s
    cases s <;> simp [σ]
  let g : B → ℂ →ₗ[ℝ] ((A → ℝ) × (B → ℂ)) := fun b =>
    (LinearMap.inr ℝ (A → ℝ) (B → ℂ)).comp (LinearMap.single ℝ (fun _ : B => ℂ) b)
  have hg : ∀ b w, g b w = ((0 : A → ℝ), Pi.single b w) := fun b w => rfl
  have hgmul : ∀ b u v, g b u * g b v = g b (u * v) := by
    intro b u v
    rw [hg, hg, hg]
    refine Prod.ext (by simp) (funext fun i => ?_)
    by_cases h : i = b
    · subst h
      simp
    · simp [h]
  have hgmul' : ∀ b b' u v, b ≠ b' → g b u * g b' v = 0 := by
    intro b b' u v hb
    rw [hg, hg]
    refine Prod.ext (by simp) (funext fun i => ?_)
    by_cases h : i = b
    · subst h
      simp [hb]
    · simp [h]
  have hc : ∀ (c : ℂ) (u : (A → ℝ) × (B → ℂ)), c ⊗ₜ[ℝ] u = c • ((1 : ℂ) ⊗ₜ[ℝ] u) := by
    intro c u
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  refine ⟨{
    e := Sum.elim (fun a => (1 : ℂ) ⊗ₜ[ℝ] ((Pi.single a 1, 0) : (A → ℝ) × (B → ℂ)))
      (fun p => (1 / 2 : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] g p.1 1 + (σ p.2 * Complex.I) ⊗ₜ[ℝ] g p.1 Complex.I))
    ch := Sum.elim
      (fun a => (algebraMap ℝ ℂ).comp ((Pi.evalRingHom (fun _ : A => ℝ) a).comp (RingHom.fst _ _)))
      (fun p => if p.2 then (starRingEnd ℂ).comp ((Pi.evalRingHom (fun _ : B => ℂ) p.1).comp (RingHom.snd _ _))
        else (Pi.evalRingHom (fun _ : B => ℂ) p.1).comp (RingHom.snd _ _))
    mul_e := ?_
    orth := ?_
    sum := ?_ }⟩
  · rintro (a | ⟨b, s⟩) x
    · simp only [Sum.elim_inl, RingHom.comp_apply]
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      have hx : x * ((Pi.single a 1, 0) : (A → ℝ) × (B → ℂ)) =
          x.1 a • ((Pi.single a (1 : ℝ), 0) : (A → ℝ) × (B → ℂ)) := by
        refine Prod.ext (funext fun i => ?_) (by simp)
        by_cases h : i = a
        · subst h
          simp
        · simp [h]
      rw [hx, TensorProduct.tmul_smul, algebraMap_smul]
      rfl
    · simp only [Sum.elim_inr]
      rw [mul_smul_comm, mul_add, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]
      simp only [one_mul]
      have hx : ∀ w : ℂ, x * g b w = g b (x.2 b * w) := by
        intro w
        rw [hg, hg]
        refine Prod.ext (by simp) (funext fun i => ?_)
        by_cases h : i = b
        · subst h
          simp
        · simp [h]
      rw [hx, hx, mul_one, one_tmul_add_tmul_mul_I_eq_smul_of_sq_eq_one (g b) (σ s) (x.2 b) (hσ s), smul_comm]
      congr 1
      cases s
      · simp [σ]
        all_goals (apply Complex.ext <;> simp)
      · simp [σ]
        all_goals (apply Complex.ext <;> simp)
  · rintro (a | ⟨b, s⟩) (a' | ⟨b', s'⟩) hne
    · have ha : a ≠ a' := fun h => hne (by rw [h])
      simp only [Sum.elim_inl]
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      have h0 : ((Pi.single a (1 : ℝ), 0) : (A → ℝ) × (B → ℂ)) * (Pi.single a' 1, 0) = 0 := by
        refine Prod.ext (funext fun i => ?_) (by simp)
        by_cases h : i = a
        · subst h
          simp [ha]
        · simp [h]
      rw [h0, TensorProduct.tmul_zero]
    · simp only [Sum.elim_inl, Sum.elim_inr]
      rw [mul_smul_comm, mul_add, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]
      have h0 : ∀ w, ((Pi.single a (1 : ℝ), 0) : (A → ℝ) × (B → ℂ)) * g b' w = 0 := by
        intro w
        rw [hg]
        exact Prod.ext (by simp) (by simp)
      rw [h0, h0]
      simp
    · simp only [Sum.elim_inl, Sum.elim_inr]
      rw [smul_mul_assoc, add_mul, Algebra.TensorProduct.tmul_mul_tmul,
        Algebra.TensorProduct.tmul_mul_tmul]
      have h0 : ∀ w, g b w * ((Pi.single a' (1 : ℝ), 0) : (A → ℝ) × (B → ℂ)) = 0 := by
        intro w
        rw [hg]
        exact Prod.ext (by simp) (by simp)
      rw [h0, h0]
      simp
    · simp only [Sum.elim_inr]
      rw [smul_mul_smul_comm]
      simp only [add_mul, mul_add, Algebra.TensorProduct.tmul_mul_tmul]
      by_cases hb : b = b'
      · subst hb
        have hs : s ≠ s' := fun h => hne (by rw [h])
        have hc2 : ∀ (c d : ℂ) (u : (A → ℝ) × (B → ℂ)), (c * d) ⊗ₜ[ℝ] u = (c * d) • ((1 : ℂ) ⊗ₜ[ℝ] u) :=
          fun c d u => hc _ _
        simp only [hgmul, hc2]
        simp only [mul_one, one_mul, Complex.I_mul_I, map_neg, TensorProduct.tmul_neg]
        cases s <;> cases s' <;> simp only [ne_eq, not_true_eq_false, Bool.false_eq_true,
          not_false_eq_true, Bool.true_eq_false] at hs <;> simp only [σ, if_true, Bool.false_eq_true, if_false] <;>
          match_scalars <;>
          first
          | ring1
          | linear_combination (1 / 4 : ℂ) * Complex.I_mul_I
          | linear_combination (-1 / 4 : ℂ) * Complex.I_mul_I
      · simp only [hgmul' b b' _ _ hb, TensorProduct.tmul_zero, add_zero, smul_zero]
  · rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
    simp only [Sum.elim_inl, Sum.elim_inr, Fintype.sum_bool]
    have hb : ∀ b, (1 / 2 : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] g b 1 + (σ true * Complex.I) ⊗ₜ[ℝ] g b Complex.I) +
        (1 / 2 : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] g b 1 + (σ false * Complex.I) ⊗ₜ[ℝ] g b Complex.I) =
        (1 : ℂ) ⊗ₜ[ℝ] g b 1 := by
      intro b
      rw [hc (σ true * Complex.I), hc (σ false * Complex.I)]
      simp only [σ, if_true, Bool.false_eq_true, if_false]
      module
    simp only [hb]
    rw [← TensorProduct.tmul_sum, ← TensorProduct.tmul_sum, ← TensorProduct.tmul_add,
      Algebra.TensorProduct.one_def]
    congr 1
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp [hg, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [hg, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]

theorem UpperTheory.exists_idempotent_decomposition_mixedSpace :
    ∀ (K : Type) [Field K] [NumberField K], ∃ (ι : Type) (_ : Fintype ι), Nonempty (Idem (mixedSpace K) ι) := by
  intro K _ _
  classical
  exact ⟨_, inferInstance, idem_lemma_2 {w : InfinitePlace K // w.IsReal} {w : InfinitePlace K // w.IsComplex}⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsOpenLevelNormalizedByIntegralFiniteGL
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem exists_normal_open_level_subgroup {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H L : Subgroup G) (hHc : IsCompact (H : Set G)) (hHo : IsOpen (H : Set G))
    (hL : IsOpen (L : Set G)) :
    ∃ L' : Subgroup G, IsOpen (L' : Set G) ∧ L' ≤ L ∧ (∀ k ∈ H, ∀ u ∈ L', k⁻¹ * u * k ∈ L') ∧
      ∃ t : Finset G, ∀ k ∈ H, ∃ c ∈ t, c⁻¹ * k ∈ L' := by
  classical
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hHc
  have hNo : IsOpen ((L.subgroupOf H : Subgroup H) : Set H) := hL.preimage continuous_subtype_val
  haveI : Finite (H ⧸ L.subgroupOf H) := (L.subgroupOf H).quotient_finite_of_isOpen hNo
  haveI : (L.subgroupOf H).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hCo : IsOpen ((L.subgroupOf H).normalCore : Set H) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _
      ((L.subgroupOf H).normalCore_isClosed (Subgroup.isClosed_of_isOpen _ hNo))
  refine ⟨(L.subgroupOf H).normalCore.map H.subtype, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.coe_map]
    exact hHo.isOpenMap_subtype_val _ hCo
  · rintro _ ⟨u, hu, rfl⟩
    have := (L.subgroupOf H).normalCore_le hu
    exact this
  · rintro k hk _ ⟨u, hu, rfl⟩
    refine ⟨(⟨k, hk⟩ : H)⁻¹ * u * ⟨k, hk⟩, ?_, by simp⟩
    have := (Subgroup.normalCore_normal (L.subgroupOf H)).conj_mem u hu ((⟨k, hk⟩ : H)⁻¹)
    simpa using this
  · haveI : Finite (H ⧸ (L.subgroupOf H).normalCore) := Subgroup.finite_quotient_of_finiteIndex
    letI := Fintype.ofFinite (H ⧸ (L.subgroupOf H).normalCore)
    refine ⟨Finset.univ.image (fun q : H ⧸ (L.subgroupOf H).normalCore => ((q.out : H) : G)), ?_⟩
    intro k hk
    refine ⟨(((QuotientGroup.mk ⟨k, hk⟩ : H ⧸ (L.subgroupOf H).normalCore).out : H) : G),
      Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    have := QuotientGroup.eq.1
      (QuotientGroup.out_eq' (QuotientGroup.mk ⟨k, hk⟩ : H ⧸ (L.subgroupOf H).normalCore))
    exact ⟨_, this, by simp⟩

theorem UpperTheory.exists_open_level_normalized_by_integralFiniteGL :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (L : Subgroup (AdelicGLn.FiniteAdelicGL K n)), IsOpen (L : Set (AdelicGLn.FiniteAdelicGL K n)) → ∃ L' : Subgroup (AdelicGLn.FiniteAdelicGL K n), IsOpen (L' : Set (AdelicGLn.FiniteAdelicGL K n)) ∧ L' ≤ L ∧ (∀ k ∈ AdelicGLn.integralFiniteGL K n, ∀ u ∈ L', k⁻¹ * u * k ∈ L') ∧ ∃ t : Finset (AdelicGLn.FiniteAdelicGL K n), ∀ k ∈ AdelicGLn.integralFiniteGL K n, ∃ c ∈ t, c⁻¹ * k ∈ L' := by
  intro K _ _ n L hL
  exact exists_normal_open_level_subgroup _ L (AdelicGLn.isCompact_integralFiniteGL K n)
    (AdelicGLn.isOpen_integralFiniteGL K n) hL
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteDimensionalInfKerAevalMonic
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem aeval_preserves_invariant_submodule {M : Type} [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M)
    (N : Submodule ℂ M) (hN : ∀ x ∈ N, T x ∈ N) (p : Polynomial ℂ) :
    ∀ x ∈ N, Polynomial.aeval T p x ∈ N := by
  intro x hx
  have hpow : ∀ n : ℕ, ∀ y ∈ N, (T ^ n) y ∈ N := by
    intro n
    induction n with
    | zero =>
      intro y hy
      simpa using hy
    | succ n ih =>
      intro y hy
      rw [pow_succ', Module.End.mul_apply]
      exact hN _ (ih y hy)
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add (f := _), LinearMap.add_apply]
    exact N.add_mem hp hq
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact N.smul_mem a (hpow n x hx)

theorem UpperTheory.finiteDimensional_inf_ker_aeval_monic :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (T : Module.End ℂ M) (N : Submodule ℂ M), (∀ x ∈ N, T x ∈ N) → (∀ c : ℂ, FiniteDimensional ℂ ↥(N ⊓ T.eigenspace c)) → ∀ p : Polynomial ℂ, p.Monic → FiniteDimensional ℂ ↥(N ⊓ LinearMap.ker (Polynomial.aeval T p)) := by
  intro M _ _ T N hN hE p hp
  have key : ∀ s : Multiset ℂ, FiniteDimensional ℂ ↥(N ⊓ LinearMap.ker
      (Polynomial.aeval T (s.map (fun a => Polynomial.X - Polynomial.C a)).prod)) := by
    intro s
    induction s using Multiset.induction_on with
    | empty =>
      rw [Multiset.map_zero, Multiset.prod_zero, map_one]
      have h1 : LinearMap.ker (1 : Module.End ℂ M) = ⊥ := LinearMap.ker_id
      rw [h1, inf_bot_eq]
      infer_instance
    | cons a s ih =>
      set q := (s.map (fun a => Polynomial.X - Polynomial.C a)).prod with hq
      rw [Multiset.map_cons, Multiset.prod_cons]
      rw [← Submodule.fg_iff_finiteDimensional] at ih ⊢
      apply Submodule.fg_of_fg_map_of_fg_inf_ker (f := Polynomial.aeval T q)
      · have hle : (N ⊓ LinearMap.ker (Polynomial.aeval T ((Polynomial.X - Polynomial.C a) * q))).map
            (Polynomial.aeval T q) ≤ N ⊓ T.eigenspace a := by
          rintro _ ⟨x, ⟨hxN, hxk⟩, rfl⟩
          refine ⟨aeval_preserves_invariant_submodule T N hN q x hxN, ?_⟩
          show _ ∈ T.eigenspace a
          rw [Module.End.mem_eigenspace_iff]
          change x ∈ LinearMap.ker _ at hxk
          rw [LinearMap.mem_ker, map_mul, Module.End.mul_apply, map_sub, Polynomial.aeval_X,
            Polynomial.aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply, sub_eq_zero] at hxk
          exact hxk
        haveI := hE a
        rw [Submodule.fg_iff_finiteDimensional]
        exact Submodule.finiteDimensional_of_le hle
      · apply Submodule.FG.of_le ih
        rintro x ⟨⟨hxN, -⟩, hxq⟩
        exact ⟨hxN, hxq⟩
  have hsplit := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp IsAlgClosed.card_roots_eq_natDegree
  rw [← hsplit]
  exact key p.roots
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FiniteDimensionalMapOfSeparatelyFinite
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.finiteDimensional_map_of_separately_finite :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (X Y : Type) (S : Submodule ℂ M) (Φ : M →ₗ[ℂ] (X × Y → ℂ)) (V₁ : Submodule ℂ (X → ℂ)) (V₂ : Submodule ℂ (Y → ℂ)), FiniteDimensional ℂ V₁ → FiniteDimensional ℂ V₂ → (∀ m ∈ S, ∀ y, (fun x => Φ m (x, y)) ∈ V₁) → (∀ m ∈ S, ∀ x, (fun y => Φ m (x, y)) ∈ V₂) → FiniteDimensional ℂ (S.map Φ) := by
  intro M _ _ X Y S Φ V₁ V₂ h₁ h₂ hrow hcol
  obtain ⟨T, hT⟩ := exists_finset_eval_eq_zero V₁
  have mem : ∀ g ∈ S.map Φ, ∀ x, (fun y => g (x, y)) ∈ V₂ := by
    rintro g ⟨m, hm, rfl⟩ x
    exact hcol m hm x
  have memr : ∀ g ∈ S.map Φ, ∀ y, (fun x => g (x, y)) ∈ V₁ := by
    rintro g ⟨m, hm, rfl⟩ y
    exact hrow m hm y
  let F : S.map Φ →ₗ[ℂ] (T → V₂) :=
    LinearMap.pi fun t => LinearMap.codRestrict V₂
      ((LinearMap.funLeft ℂ ℂ (fun y : Y => ((t : X), y))).comp (S.map Φ).subtype)
      (fun g => mem g.1 g.2 t)
  have hF : Function.Injective F := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro g hg
    apply Subtype.ext
    funext p
    obtain ⟨x, y⟩ := p
    have h0 := hT (fun x => g.1 (x, y)) (memr g.1 g.2 y) (by
      intro t ht
      have := congrArg (fun v : T → V₂ => ((v ⟨t, ht⟩ : V₂) : Y → ℂ) y) hg
      simpa [F, LinearMap.funLeft] using this)
    simpa using congrFun h0 x
  exact Module.Finite.of_injective F hF
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GenGlRelationsAndCommuteOfIsLie
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem single_comm {R : Type} [CommRing R] {n : ℕ} (i j k m : Fin n) (x y : R) :
    (Matrix.single i j x * Matrix.single k m y : Matrix (Fin n) (Fin n) R) =
      if j = k then Matrix.single i m (x * y) else 0 := by
  split_ifs with h
  · subst h
    exact Matrix.single_mul_single_same _ _ _ _ _
  · ext a b
    simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases hj : j = t
    · subst hj
      simp only [Ne.symm h, false_and, if_false, mul_zero]
    · simp [hj]

private theorem unitMap_comm {R : Type} [CommRing R] [Algebra ℝ R] {n : ℕ} {A : Type} [Ring A] [Algebra ℂ A]
    [Algebra ℝ A] [IsScalarTower ℝ ℂ A] (l : Matrix (Fin n) (Fin n) R →ₗ[ℝ] A) (hl : IsLie l) (i j k m : Fin n)
    (a b : ℂ ⊗[ℝ] R) :
    unitMap l i j a * unitMap l k m b - unitMap l k m b * unitMap l i j a =
      (if j = k then unitMap l i m (a * b) else 0) - (if m = i then unitMap l k j (a * b) else 0) := by
  have hmain : ∀ (c d : ℂ) (x y : R),
      unitMap l i j (c ⊗ₜ x) * unitMap l k m (d ⊗ₜ y) - unitMap l k m (d ⊗ₜ y) * unitMap l i j (c ⊗ₜ x) =
        (if j = k then unitMap l i m ((c ⊗ₜ x) * (d ⊗ₜ y)) else 0) -
          (if m = i then unitMap l k j ((c ⊗ₜ x) * (d ⊗ₜ y)) else 0) := by
    intro c d x y
    simp only [unitMap_tmul, Algebra.TensorProduct.tmul_mul_tmul, smul_mul_smul_comm]
    rw [mul_comm d c, ← smul_sub, hl, single_comm, single_comm, mul_comm y x]
    split_ifs <;> simp [map_sub, smul_sub]
  rw [← sub_eq_zero]
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul c x =>
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul d y => rw [sub_eq_zero]; exact hmain c d x y
    | add b₁ b₂ h₁ h₂ =>
      have h := congrArg₂ (· + ·) h₁ h₂
      simp only [add_zero] at h
      refine Eq.trans ?_ h
      split_ifs <;> simp only [map_add (f := _), mul_add, add_mul] <;> abel
  | add a₁ a₂ h₁ h₂ =>
    have h := congrArg₂ (· + ·) h₁ h₂
    simp only [add_zero] at h
    refine Eq.trans ?_ h
    split_ifs <;> simp only [map_add (f := _), mul_add, add_mul] <;> abel

theorem UpperTheory.gen_glRelations_and_commute_of_isLie :
    ∀ (R : Type) [CommRing R] [Algebra ℝ R] (ι : Type) [Fintype ι] (n : ℕ) (A : Type) [Ring A] [Algebra ℂ A] [Algebra ℝ A] [IsScalarTower ℝ ℂ A] (D : Idem R ι) (l : Matrix (Fin n) (Fin n) R →ₗ[ℝ] A), IsLie l → (∀ τ, Formalism.REAL.GlRel (gen D l τ)) ∧ ∀ τ σ, τ ≠ σ → ∀ i j k m, Commute (gen D l τ i j) (gen D l σ k m) := by
  intro R _ _ ι _ n A _ _ _ _ D l hl
  have idem : ∀ τ, D.e τ * D.e τ = D.e τ := by
    intro τ
    calc D.e τ * D.e τ = D.e τ * ∑ σ, D.e σ := by
          rw [Finset.mul_sum, Finset.sum_eq_single τ]
          · intro σ _ h
            exact D.orth τ σ (Ne.symm h)
          · simp
      _ = D.e τ := by rw [D.sum, mul_one]
  refine ⟨fun τ => ?_, fun τ σ h i j k m => ?_⟩
  · intro a b c d
    simp only [gen]
    rw [unitMap_comm l hl, idem]
  · unfold Commute SemiconjBy
    rw [← sub_eq_zero]
    simp only [gen]
    rw [unitMap_comm l hl, D.orth τ σ h]
    simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.HasModerateGrowthConstantTerm
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.hasModerateGrowth_constantTerm :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (φ : AdelicGLn.AdelicGL K n → ℂ), HasModerateGrowth φ → HasModerateGrowth (constantTerm r φ) := by
  intro K _ _ n r φ ⟨C, N, hφ⟩
  obtain ⟨D, hD, hsub⟩ := exists_isCompact_superset_unipFundamentalDomain (K := K) (n := n) (r := r)
  obtain ⟨M, hM⟩ := CuspidalSpectrum.exists_height_le_of_isCompact (hD.image continuous_unipGL)
  have hc0 : 0 ≤ heightConst K n := le_trans zero_le_one one_le_heightConst
  have hfin : unipMeasure K n r (unipFundamentalDomain K n r) < ⊤ :=
    (measure_mono hsub).trans_lt hD.measure_lt_top
  refine ⟨|C| * (heightConst K n * |M|) ^ N * (unipMeasure K n r).real (unipFundamentalDomain K n r), N, fun g => ?_⟩
  have hg := (height_pos g).le
  have hb : ∀ X ∈ unipFundamentalDomain K n r,
      ‖φ (unipGL X * g)‖ ≤ |C| * (heightConst K n * |M| * AutomorphicForm.height g) ^ N := by
    intro X hX
    have h1 : AutomorphicForm.height (unipGL X * g) ≤ heightConst K n * |M| * AutomorphicForm.height g :=
      (height_mul_le _ _).trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ((hM _ ⟨X, hsub hX, rfl⟩).trans (le_abs_self M)) hc0) hg)
    exact (hφ _).trans (mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (height_pos _).le h1 N)
      (pow_nonneg (height_pos _).le N) (abs_nonneg C))
  refine (norm_setIntegral_le_of_norm_le_const hfin hb).trans (le_of_eq ?_)
  rw [mul_pow (heightConst K n * |M|)]
  ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IntegralUnipFundamentalDomainCompLatticePreservi
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.integral_unipFundamentalDomain_comp_lattice_preserving :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (α : (UPos n r → AdeleRing (𝓞 K) K) ≃ₜ+ (UPos n r → AdeleRing (𝓞 K) K)), (∀ X, α X ∈ unipLattice K n r ↔ X ∈ unipLattice K n r) → ∀ F : (UPos n r → AdeleRing (𝓞 K) K) → ℂ, (∀ ξ ∈ unipLattice K n r, ∀ X, F (ξ + X) = F X) → ∫ X in unipFundamentalDomain K n r, F (α X) ∂unipMeasure K n r = ∫ X in unipFundamentalDomain K n r, F X ∂unipMeasure K n r := by
  intro K _ _ n r α hα F hF
  haveI : TopologicalSpace.MetrizableSpace (UPos n r → AdeleRing (𝓞 K) K) :=
    TopologicalSpace.metrizableSpace_of_t3_secondCountable _
  haveI : (unipMeasure K n r).Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  have hfd : IsAddFundamentalDomain (unipLattice K n r) (unipFundamentalDomain K n r) (unipMeasure K n r) :=
    isAddFundamentalDomain_unipFundamentalDomain
  have hsm := addEquivAddHaarChar_smul_map (unipMeasure K n r) α.symm
  have hpos := addEquivAddHaarChar_pos α.symm
  have hmap : (unipMeasure K n r).map α.symm = (addEquivAddHaarChar α.symm)⁻¹ • unipMeasure K n r := by
    conv_rhs => rw [← hsm]
    rw [smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
  have hqmp : Measure.QuasiMeasurePreserving α.symm (unipMeasure K n r) (unipMeasure K n r) :=
    ⟨α.symm.continuous.measurable.aemeasurable, by rw [hmap]; exact Measure.smul_absolutelyContinuous⟩
  let e : unipLattice K n r → unipLattice K n r := fun g => ⟨α g, (hα g).2 g.2⟩
  have he : Function.Bijective e := by
    refine ⟨fun g h hgh => ?_, fun g => ⟨⟨α.symm g, (hα (α.symm g)).1 (by simpa using g.2)⟩, ?_⟩⟩
    · apply Subtype.ext
      apply α.injective
      exact congrArg Subtype.val hgh
    · apply Subtype.ext
      simp [e]
  have hfd' : IsAddFundamentalDomain (unipLattice K n r) (α.symm ⁻¹' unipFundamentalDomain K n r)
      (unipMeasure K n r) :=
    hfd.preimage_of_equiv hqmp he (fun g x => by
      show α.symm (α g + x) = g + α.symm x
      simp [map_add (f := _)])
  have hmeas := hfd'.measure_eq hfd
  have hpre := addEquivAddHaarChar_smul_preimage (unipMeasure K n r) (X := unipFundamentalDomain K n r) α.symm
  rw [hmeas, unipMeasure_unipFundamentalDomain, ENNReal.smul_def, smul_eq_mul, mul_one,
    ENNReal.coe_eq_one] at hpre
  have hmp : MeasurePreserving α.symm (unipMeasure K n r) (unipMeasure K n r) :=
    ⟨α.symm.continuous.measurable, by rw [hmap, hpre, inv_one, one_smul]⟩
  have key := hmp.setIntegral_preimage_emb α.symm.toHomeomorph.measurableEmbedding
    (fun y => F (α y)) (unipFundamentalDomain K n r)
  simp only [ContinuousAddEquiv.apply_symm_apply] at key
  rw [← key]
  exact hfd'.setIntegral_eq hfd (fun g x => hF g g.2 x)
end

