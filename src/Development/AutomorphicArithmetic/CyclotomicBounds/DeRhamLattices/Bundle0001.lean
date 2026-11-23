module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.AdmissibleLatticesCommensurable
section
theorem _root_.UpperTheory.KN.admissible_lattices_commensurable :
    ∀ {O LL V : Type} [CommRing O] [IsDomain O] [IsNoetherianRing O] [Field LL] [Algebra O LL] [IsFractionRing O LL]
      [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V] (Λ A : Submodule O V), Λ.FG → ∀ c : O, c ≠ 0 →
      ∃ μ : O, μ ≠ 0 ∧ ∀ u ∈ Λ, μ • u ∈ A → ∃ a ∈ A, μ • u = c • a := by
  intro O LL V _ _ _ _ _ _ _ _ _ _ Λ A hΛ c hc
  haveI : IsNoetherian O Λ := isNoetherian_of_fg_of_noetherian Λ hΛ
  let f : ℕ →o Submodule O Λ :=
    ⟨fun n => (A.comap ((c ^ n) • LinearMap.id : V →ₗ[O] V)).comap Λ.subtype, by
      intro m n hmn x hx
      simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.smul_apply,
        LinearMap.id_apply] at hx ⊢
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      rw [pow_add, mul_comm, mul_smul]
      exact A.smul_mem _ hx⟩
  obtain ⟨N, hN⟩ := (monotone_stabilizes_iff_noetherian.mpr inferInstance) f
  refine ⟨c ^ (N + 1), pow_ne_zero _ hc, ?_⟩
  intro u hu hμ
  have h1 : (⟨u, hu⟩ : Λ) ∈ f (N + 1) := hμ
  rw [← hN (N + 1) (Nat.le_succ N)] at h1
  have h2 : c ^ N • u ∈ A := h1
  exact ⟨c ^ N • u, h2, by rw [pow_succ, mul_comm, mul_smul]⟩
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.CoeffEqZeroOfSumTmulLinearIndependentEqZero
section
open TensorProduct

theorem _root_.UpperTheory.KN.coeff_eq_zero_of_sum_tmul_linearIndependent_eq_zero :
    ∀ (K V C ι : Type) [Field K] [AddCommGroup V] [Module K V] [AddCommGroup C] [Module K C] [Fintype ι] (v : ι → V), LinearIndependent K v → ∀ c : ι → C, ∑ i, v i ⊗ₜ[K] c i = 0 → ∀ i, c i = 0 := by
  intro K V C ι _ _ _ _ _ _ v hv c hsum i
  classical
  obtain ⟨f, hf⟩ := LinearMap.exists_extend ((Module.Basis.span hv).coord i)
  have hfv : ∀ j, f (v j) = if j = i then 1 else 0 := by
    intro j
    have h1 : f (v j) = (Module.Basis.span hv).coord i ⟨v j, Submodule.subset_span ⟨j, rfl⟩⟩ := by
      rw [← hf]
      rfl
    rw [h1, ← Module.Basis.span_apply hv j, Module.Basis.coord_apply, Module.Basis.repr_self,
      Finsupp.single_apply]
  have h2 := congrArg (⇑((TensorProduct.lid K C).toLinearMap ∘ₗ TensorProduct.map f LinearMap.id)) hsum
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearEquiv.coe_coe, TensorProduct.lid_tmul, hfv, map_zero] at h2
  simpa using h2
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsLinearEquivQuotientOfLatticeSum
section
theorem _root_.UpperTheory.KN.exists_linearEquiv_quotient_of_lattice_sum :
    ∀ {O V A M : Type} [CommRing O] [AddCommGroup V] [Module O V] [AddCommGroup A] [Module O A] [AddCommGroup M] [Module O M]
      (j : A →ₗ[O] V) (q : A →ₗ[O] M) (B T₁ T₂ : Submodule O V), Function.Injective j → Function.Surjective q →
      (∀ a, j a ∈ B → q a = 0) → (∀ v, v ∈ T₁ ↔ ∃ a, ∃ b ∈ B, v = j a + b) → (∀ v, v ∈ T₂ ↔ ∃ a, q a = 0 ∧ ∃ b ∈ B, v = j a + b) →
      ∃ e : M ≃ₗ[O] (↥T₁ ⧸ T₂.comap T₁.subtype), ∀ (a : A) (y : ↥T₁), e (q a) = Submodule.Quotient.mk y ↔ ∃ a', q a' = q a ∧ ∃ b ∈ B, (y : V) = j a' + b := by
  intro O V A M _ _ _ _ _ _ _ j q B T₁ T₂ _ hq hB h1 h2
  have hj : ∀ a, j a ∈ T₁ := fun a => (h1 _).2 ⟨a, 0, B.zero_mem, by simp⟩
  let p : A →ₗ[O] (↥T₁ ⧸ T₂.comap T₁.subtype) :=
    (T₂.comap T₁.subtype).mkQ ∘ₗ j.codRestrict T₁ hj
  have key : ∀ (a : A) (y : ↥T₁), p a = Submodule.Quotient.mk y ↔
      ∃ a', q a' = q a ∧ ∃ b ∈ B, (y : V) = j a' + b := by
    intro a y
    have h : p a = Submodule.Quotient.mk y ↔ (y : V) - j a ∈ T₂ := by
      rw [eq_comm]
      exact Submodule.Quotient.eq (T₂.comap T₁.subtype)
    rw [h, h2]
    constructor
    · rintro ⟨a', ha', b, hb, hy⟩
      refine ⟨a' + a, by simp [ha'], b, hb, ?_⟩
      rw [map_add (f := _), add_right_comm, ← hy, sub_add_cancel]
    · rintro ⟨a', ha', b, hb, hy⟩
      refine ⟨a' - a, by simp [ha'], b, hb, ?_⟩
      rw [map_sub, hy]
      abel
  have hp : Function.Surjective p := by
    intro z
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    obtain ⟨a, b, hb, hy⟩ := (h1 _).1 y.2
    exact ⟨a, (key a y).2 ⟨a, rfl, b, hb, hy⟩⟩
  have hker : LinearMap.ker q = LinearMap.ker p := by
    ext a
    rw [LinearMap.mem_ker, LinearMap.mem_ker, ← Submodule.Quotient.mk_zero, key]
    constructor
    · intro ha
      exact ⟨0, by simp [ha], 0, B.zero_mem, by simp⟩
    · rintro ⟨a', ha', b, hb, hy⟩
      rw [← ha']
      apply hB
      have : j a' = -b := eq_neg_of_add_eq_zero_left hy.symm
      rw [this]
      exact B.neg_mem hb
  refine ⟨(q.quotKerEquivOfSurjective hq).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans (p.quotKerEquivOfSurjective hp)), fun a y => ?_⟩
  rw [← key]
  have h3 : (q.quotKerEquivOfSurjective hq).symm (q a) = Submodule.Quotient.mk a := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  rw [LinearEquiv.trans_apply, h3]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.ExistsLinearMapSpanBaseChangeOfSemilinear
section
theorem _root_.UpperTheory.KN.exists_linearMap_span_baseChange_of_semilinear :
    ∀ {O O' LL Q : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [CommRing O'] [Field LL] [Algebra O' LL]
      [AddCommGroup Q] [Module O' Q] (f : O →+* O') (fK : FractionRing O →+* LL) {a n : ℕ}
      (Y : Submodule O (Fin a → Fin n → FractionRing O)) (ψ : ↥Y →+ Q),
      Function.Injective (algebraMap O' LL) → (∀ c, fK (algebraMap O (FractionRing O) c) = algebraMap O' LL (f c)) → Y.FG →
      (∀ (c : O) (y : ↥Y), ψ (c • y) = f c • ψ y) →
      ∃ φ : ↥(Submodule.span O' ((fun (y : Fin a → Fin n → FractionRing O) j m => fK (y j m)) '' (Y : Set _))) →ₗ[O'] Q,
        ∀ y : ↥Y, φ ⟨fun j m => fK (y.1 j m), Submodule.subset_span ⟨y.1, y.2, rfl⟩⟩ = ψ y := by
  intro O O' LL Q _ _ _ _ _ _ _ _ f fK a n Y ψ hinj hf hfg hψ
  classical
  haveI : Module.Finite O Y := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Free O Y := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis O Y
  let v : Module.Free.ChooseBasisIndex O Y → Fin a → Fin n → LL := fun i j m => fK ((b i).1 j m)
  have h1 : LinearIndependent O (fun i => fun p : Fin a × Fin n => (b i).1 p.1 p.2) := by
    have h0 : LinearIndependent O (fun i => (b i).1) :=
      b.linearIndependent.map' Y.subtype (Submodule.ker_subtype Y)
    rw [Fintype.linearIndependent_iff] at h0 ⊢
    intro g hg
    apply h0
    funext j m
    have := congrFun hg (j, m)
    simpa [Finset.sum_apply] using this
  have h2 : LinearIndependent (FractionRing O) (fun i => fun p : Fin a × Fin n => (b i).1 p.1 p.2) :=
    (LinearIndependent.iff_fractionRing O (FractionRing O)).mp h1
  have h3 : LinearIndependent LL (fun i => fun p : Fin a × Fin n => fK ((b i).1 p.1 p.2)) := by
    letI := fK.toAlgebra
    exact linearIndependent_algebraMap_comp_iff.mpr h2
  have h4 : LinearIndependent O' v := by
    rw [Fintype.linearIndependent_iff] at h3 ⊢
    intro g hg i
    apply hinj
    rw [map_zero]
    apply h3 (fun i => algebraMap O' LL (g i))
    funext p
    have := congrFun (congrFun hg p.1) p.2
    simpa [Finset.sum_apply, v, Algebra.smul_def] using this
  have hexp : ∀ y : Y, (fun j m => fK (y.1 j m)) = ∑ i, f (b.repr y i) • v i := by
    intro y
    funext j m
    have h := congrArg (fun z : Y => z.1 j m) (b.sum_repr y)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply] at h
    rw [← h]
    simp [Finset.sum_apply, v, Algebra.smul_def, hf]
  have hspan : Submodule.span O' ((fun (y : Fin a → Fin n → FractionRing O) j m => fK (y j m)) '' (Y : Set _))
      = Submodule.span O' (Set.range v) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      have := hexp ⟨y, hy⟩
      simp only at this
      show (fun j m => fK (y j m)) ∈ Submodule.span O' (Set.range v)
      rw [this]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨(b i).1, (b i).2, rfl⟩
  let B := Module.Basis.span h4
  refine ⟨(B.constr O' (fun i => ψ (b i))).comp (LinearEquiv.ofEq _ _ hspan).toLinearMap, fun y => ?_⟩
  have h5 : (LinearEquiv.ofEq _ _ hspan) ⟨fun j m => fK (y.1 j m), Submodule.subset_span ⟨y.1, y.2, rfl⟩⟩
      = ∑ i, f (b.repr y i) • B i := by
    apply Subtype.ext
    simp only [LinearEquiv.coe_ofEq_apply, Submodule.coe_sum, Submodule.coe_smul, B, Module.Basis.span_apply]
    exact hexp y
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, h5, map_sum]
  conv_rhs => rw [← b.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Module.Basis.constr_basis, hψ]
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.FiltrationEqSpanOfEisensteinPowBasisChange
section
theorem _root_.UpperTheory.KN.filtration_eq_span_of_eisensteinPow_basisChange :
    ∀ (R W : Type) [CommRing R] [AddCommGroup W] (act : R →+ (W →+ W)), (∀ (r s : R) (w : W), act (r * s) w = act r (act s w)) → (∀ w : W, act 1 w = w) → ∀ (eD : R), Function.Bijective (act eD) → ∀ (F : ℤ → W → Prop), (∀ (y : W) (j : ℤ), F j y ↔ F (j + 1) (act eD y)) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (β : ℕ) (h b : ι → W) (m m' : Matrix ι ι R), m' * m = 1 → (∀ i, h i = ∑ k, act (eD ^ β * m i k) (b k)) → (∀ v, F 0 v ↔ ∃ d : ι → R, v = ∑ k, act (d k) (b k)) → ∀ w, F (β : ℤ) w ↔ ∃ d : ι → R, w = ∑ i, act (d i) (h i) := by
  intro R W _ _ act hmul hone eD hbij F hF ι _ _ β h b m m' hm hh hF0 w
  have hpow : ∀ (n : ℕ) (y : W), act (eD ^ n) y = (act eD)^[n] y := by
    intro n
    induction n with
    | zero => intro y; simp [hone]
    | succ n ih =>
      intro y
      rw [pow_succ, hmul, ih, Function.iterate_succ_apply]
  have hFn : ∀ (n : ℕ) (y : W), F 0 y ↔ F n ((act eD)^[n] y) := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [ih, hF, Function.iterate_succ_apply', Nat.cast_succ]
  have hinj : Function.Injective (act (eD ^ β)) := by
    intro x y hxy
    rw [hpow, hpow] at hxy
    exact (hbij.iterate β).1 hxy
  have hexp : ∀ d : ι → R,
      ∑ i, act (d i) (h i) = act (eD ^ β) (∑ k, act (∑ i, d i * m i k) (b k)) := by
    intro d
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hh, map_sum, AddMonoidHom.finsetSum_apply, ← hmul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact congrArg (fun r => act r (b k)) (by ring)
  have hspan : ∀ y : W, (∃ d : ι → R, y = ∑ k, act (d k) (b k)) ↔
      ∃ e : ι → R, y = ∑ k, act (∑ i, e i * m i k) (b k) := by
    intro y
    constructor
    · rintro ⟨d, rfl⟩
      refine ⟨fun i => ∑ j, d j * m' j i, ?_⟩
      have hc : ∀ k, ∑ i, (∑ j, d j * m' j i) * m i k = d k := by
        intro k
        calc ∑ i, (∑ j, d j * m' j i) * m i k = ∑ j, d j * (m' * m) j k := by
              simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
              rw [Finset.sum_comm]
          _ = d k := by simp [hm, Matrix.one_apply]
      simp only [hc]
    · rintro ⟨e, rfl⟩
      exact ⟨fun k => ∑ i, e i * m i k, rfl⟩
  obtain ⟨y, rfl⟩ := (hbij.iterate β).2 w
  rw [← hFn β y, hF0, hspan, ← hpow]
  constructor
  · rintro ⟨e, he⟩
    exact ⟨e, by rw [hexp, he]⟩
  · rintro ⟨e, he⟩
    exact ⟨e, hinj (by rw [he, hexp])⟩
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.MemRangeSemilinearOfValuesMemRange
section
theorem _root_.UpperTheory.KN.mem_range_semilinear_of_values_mem_range :
    ∀ (K M N V U I J : Type) [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module ℂ N] [AddCommGroup V] [Module K V] [AddCommGroup U] [Module ℂ U]
      (σ : K →+* ℂ) (jm : M →ₛₗ[σ] N) (ev : N →ₗ[ℂ] (I → U)) (c0 : V →ₛₗ[σ] U) (b : Module.Basis J K V),
      Submodule.span ℂ (Set.range jm) = ⊤ → Function.Injective ev → LinearIndependent ℂ (fun i => c0 (b i)) →
      (∀ m h, ev (jm m) h ∈ Set.range c0) → ∀ f : N, (∀ h, ev f h ∈ Set.range c0) → f ∈ Set.range jm := by
  intro K M N V U I J _ _ _ _ _ _ _ _ _ σ jm ev c0 b hspan hev hli hjm f hf
  classical
  letI : Algebra K ℂ := σ.toAlgebra
  have hσ : ∀ k : K, algebraMap K ℂ k = σ k := fun k => rfl
  obtain ⟨lam, hlam⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K ℂ)
    (LinearMap.ker_eq_bot.mpr (algebraMap K ℂ).injective)
  have lam_mul : ∀ k z, lam (σ k * z) = k * lam z := by
    intro k z
    rw [← hσ, ← Algebra.smul_def, map_smul, smul_eq_mul]
  have lam_one : lam 1 = 1 := by
    have := LinearMap.congr_fun hlam 1
    simpa using this
  let B := Module.Basis.span hli
  obtain ⟨Ψ, hΨ⟩ := LinearMap.exists_extend (B.repr.toLinearMap)
  have hΨb : ∀ j, Ψ (c0 (b j)) = Finsupp.single j 1 := by
    intro j
    have h1 := LinearMap.congr_fun hΨ (B j)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearEquiv.coe_coe,
      B.repr_self] at h1
    rwa [Module.Basis.span_apply] at h1
  have hΨv : ∀ v j, Ψ (c0 v) j = σ (b.repr v j) := by
    intro v j
    conv_lhs => rw [← b.linearCombination_repr v, Finsupp.linearCombination_apply]
    simp [map_finsuppSum, hΨb, Finsupp.single_apply, Finsupp.sum_apply]
    intro h0
    rw [h0, map_zero]
  let R : U →+ V := b.repr.symm.toLinearMap.toAddMonoidHom.comp
    ((Finsupp.mapRange.addMonoidHom lam.toAddMonoidHom).comp Ψ.toAddMonoidHom)
  have hRrepr : ∀ u j, b.repr (R u) j = lam (Ψ u j) := by
    intro u j
    simp [R]
  have KR : ∀ (z : ℂ) (v : V), R (z • c0 v) = lam z • v := by
    intro z v
    apply b.repr.injective
    ext j
    rw [hRrepr, map_smul, Finsupp.smul_apply, hΨv, smul_eq_mul, mul_comm, lam_mul,
      map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  have Rc0 : ∀ v, R (c0 v) = v := by
    intro v
    have := KR 1 v
    rwa [one_smul, lam_one, one_smul] at this
  have hf' : f ∈ Submodule.span ℂ (Set.range jm) := hspan ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hf'
  refine ⟨c.sum fun m a => lam a • m, ?_⟩
  apply hev
  funext h
  obtain ⟨w, hw⟩ := hf h
  have hu : ∀ m, c0 (R (ev (jm m) h)) = ev (jm m) h := by
    intro m
    obtain ⟨v, hv⟩ := hjm m h
    rw [← hv, Rc0]
  have e1 : ev (jm (c.sum fun m a => lam a • m)) h = c.sum fun m a => σ (lam a) • ev (jm m) h := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Finsupp.sum, map_sum, map_smulₛₗ, Finset.sum_apply]
  have e2 : ev (c.sum fun m a => a • jm m) h = c.sum fun m a => a • ev (jm m) h := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Finsupp.sum, map_sum, Finset.sum_apply]
  have e3 : c0 (R (c.sum fun m a => a • ev (jm m) h)) = c.sum fun m a => σ (lam a) • ev (jm m) h := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    conv_lhs => rw [← hu m]
    rw [KR, map_smulₛₗ, hu m]
  rw [e1, ← e3, ← e2, ← hw, Rc0]
end

