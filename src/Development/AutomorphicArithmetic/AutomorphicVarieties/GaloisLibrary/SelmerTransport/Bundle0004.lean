module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0001
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.Bundle0001
public import Mathlib.FieldTheory.KummerExtension

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.KerResAb
section
open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem len_le_pi {R Z M ι : Type} [CommRing R] [AddCommGroup Z] [Module R Z] [AddCommGroup M] [Module R M]
    [Fintype ι] (ev : Z →ₗ[R] (ι → M)) (hev : Function.Injective ev) (W : Submodule R Z) (H : ι → Submodule R M)
    (hW : ∀ z ∈ W, ∀ i, ev z i ∈ H i) : Module.length R W ≤ ∑ i, Module.length R (H i) := by
  rw [← Module.length_pi_of_fintype]
  let φ : W →ₗ[R] (∀ i, H i) := LinearMap.pi fun i =>
    LinearMap.codRestrict (H i) ((LinearMap.proj i).comp (ev.comp W.subtype)) fun z => hW z.1 z.2 i
  refine Module.length_le_of_injective φ fun x y hxy => ?_
  refine Subtype.ext (hev (funext fun i => ?_))
  exact congrArg Subtype.val (congrFun hxy i)

private theorem len_abs {R Z K M ι : Type} [CommRing R] [AddCommGroup Z] [Module R Z] [AddCommGroup M] [Module R M]
    [AddCommGroup K] [Module R K] [Fintype ι] (hM : ∀ m : M, Module.length R (Submodule.span R {m}) ≠ ⊤)
    (ev : Z →ₗ[R] (ι → M)) (hev : Function.Injective ev) (π : Z →ₗ[R] K) (hπ : Function.Surjective π) (a : R)
    (ha : ∀ z, π (a • z) = 0) (H : Submodule R M) (hH : ∀ m, a • m = 0 → m ∈ H) :
    Module.length R K ≤ Fintype.card ι * Module.length R H := by
  have hZ : ∀ z : Z, Module.length R (Submodule.span R {z}) ≠ ⊤ := by
    intro z
    refine ne_top_of_le_ne_top ?_ (len_le_pi ev hev _ (fun i => Submodule.span R {ev z i}) ?_)
    · exact ENat.sum_ne_top.2 fun i _ => hM _
    · intro w hw i
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hw
      rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  have h1 := lenCokerLe R Z hZ a
  have h2 := len_le_pi ev hev (LinearMap.ker (a • (LinearMap.id : Z →ₗ[R] Z))) (fun _ => H) (by
    intro z hz i
    apply hH
    have : a • z = 0 := hz
    have e := congrFun (congrArg ev this) i
    simpa using e)
  have h3 : Module.length R K ≤ Module.length R (Z ⧸ LinearMap.range (a • (LinearMap.id : Z →ₗ[R] Z))) := by
    refine Module.length_le_of_surjective (Submodule.liftQ _ π ?_) ?_
    · rintro _ ⟨z, rfl⟩
      exact ha z
    · intro k
      obtain ⟨z, rfl⟩ := hπ k
      exact ⟨Submodule.Quotient.mk z, rfl⟩
  refine h3.trans (h1.trans (h2.trans ?_))
  simp

theorem UpperTheory.V.Base.kerResAb :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) [IsPrincipalIdealRing R], ContAction ρ → (∀ m : M, Module.length R (Submodule.span R {m}) ≠ ⊤) → (∀ g, ∃ c : R, ∀ m, ρ g m = c • m) →
      ∀ (U' U : Subgroup G) (h : U' ≤ U), (∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ U') → ∀ T : Finset G, (T : Set G) ⊆ U →
      U ≤ (Subgroup.closure (T : Set G) ⊔ U').topologicalClosure →
      Module.length R (LinearMap.ker (resU ρ h)) ≤ T.card * Module.length R (H0U ρ U) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ _ hρ hM hc U' U h hab T hT hU
  choose c hc using hc
  have hρU : ContAction (ρ.comp U.subtype : Representation R U M) :=
    hρ.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  let Z0 : Submodule R (Z1U ρ U) :=
    { carrier := {z | ∀ u : U, u.1 ∈ U' → z.1 u = 0}
      zero_mem' := fun _ _ => rfl
      add_mem' := fun {x y} hx hy u hu => by
        show x.1 u + y.1 u = 0
        rw [hx u hu, hy u hu, add_zero]
      smul_mem' := fun r x hx u hu => by
        show r • x.1 u = 0
        rw [hx u hu, smul_zero] }
  have hcoc : ∀ (z : Z1U ρ U) (u v : U), z.1 (u * v) = z.1 u + ρ u (z.1 v) := fun z u v => z.2.2 u v
  let ev : Z0 →ₗ[R] (T → M) := LinearMap.pi fun t =>
    (LinearMap.proj (⟨t.1, hT t.2⟩ : U)).comp ((Z1U ρ U).subtype.comp Z0.subtype)
  have hev : Function.Injective ev := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    have h1 : z.1.1 1 = 0 := z.2 1 U'.one_mem
    let K : Subgroup U :=
      { carrier := {u | z.1.1 u = 0}
        one_mem' := h1
        mul_mem' := fun {u v} hu hv => by
          have hu' : z.1.1 u = 0 := hu
          have hv' : z.1.1 v = 0 := hv
          show z.1.1 (u * v) = 0
          rw [hcoc, hu', hv', map_zero, add_zero]
        inv_mem' := fun {u} hu => by
          have hu' : z.1.1 u = 0 := hu
          have e := hcoc z.1 u⁻¹ u
          rw [inv_mul_cancel, h1, hu', map_zero, add_zero] at e
          exact e.symm }
    have hK : IsClosed (K : Set U) := isClosed_eq z.1.2.1 continuous_const
    have hle : Subgroup.closure (T : Set G) ⊔ U' ≤ K.map U.subtype := by
      refine sup_le ((Subgroup.closure_le _).2 fun t ht => ?_) fun u hu => ?_
      · exact ⟨⟨t, hT ht⟩, congrFun hz ⟨t, ht⟩, rfl⟩
      · exact ⟨⟨u, h hu⟩, z.2 _ hu, rfl⟩
    refine Subtype.ext (Subtype.ext (funext fun u => ?_))
    have : u ∈ closure (K : Set U) := by
      rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
      exact closure_mono hle (hU u.2)
    rw [hK.closure_eq] at this
    exact this
  let π : Z0 →ₗ[R] LinearMap.ker (resU ρ h) :=
    LinearMap.codRestrict _ ((Submodule.mkQ _).comp Z0.subtype) fun z =>
      (resU_mk_eq_zero ρ h z.1).2 ⟨0, fun u => by rw [z.2 _ u.2]; simp⟩
  have hπ : Function.Surjective π := by
    rintro ⟨x, hx⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨m, hm⟩ := (resU_mk_eq_zero ρ h z).1 hx
    let b : Z1U ρ U := ⟨d0 _ m, coboundaries_le_cocycles _ hρU ⟨m, rfl⟩⟩
    refine ⟨⟨z - b, fun u hu => ?_⟩, Subtype.ext ?_⟩
    · show z.1 u - (ρ u m - m) = 0
      exact sub_eq_zero.2 (hm ⟨u.1, hu⟩)
    · refine (mk_eq_mk ρ U (z - b) z).2 ⟨-m, fun u => ?_⟩
      show z.1 u - (ρ u m - m) - z.1 u = _
      rw [map_neg]
      abel
  obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal (Ideal.span (Set.range fun u : U => c u - 1))).principal
  have hkill : ∀ (u : U) (z : Z0), π ((c u - 1) • z) = 0 := by
    intro u z
    refine Subtype.ext ((Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨z.1.1 u, fun g => ?_⟩))
    show (c u - 1) • z.1.1 g = ρ g (z.1.1 u) - z.1.1 u
    have e0 : u * g = (u * g * u⁻¹ * g⁻¹) * (g * u) := by group
    have e1 : ρ ((u * g * u⁻¹ * g⁻¹ : U) : G) = 1 := by
      have : ρ u * ρ g = ρ g * ρ u := by
        ext m
        simp only [Module.End.mul_apply, hc, smul_smul, mul_comm]
      have e : ((u * g * u⁻¹ * g⁻¹ : U) : G) = u * g * ((u : G)⁻¹ * (g : G)⁻¹) := by
        simp [mul_assoc]
      rw [e, map_mul, map_mul, this, ← map_mul, ← map_mul]
      simp
    have e2 : z.1.1 (u * g) = z.1.1 (g * u) := by
      rw [e0, hcoc, e1, z.2 _ (hab u u.2 g g.2)]
      simp
    rw [hcoc, hcoc, hc u] at e2
    rw [sub_smul, one_smul, eq_sub_of_add_eq' e2]
    abel
  have hamem : a ∈ Ideal.span (Set.range fun u : U => c u - 1) := by
    rw [ha]; exact Submodule.mem_span_singleton_self a
  have key := len_abs hM ev hev π hπ a (fun z => ?_) (H0U ρ U) (fun m hm => ?_)
  · simpa using key
  · refine Submodule.span_induction (p := fun r _ => π (r • z) = 0) ?_ ?_ ?_ ?_ hamem
    · rintro _ ⟨u, rfl⟩
      exact hkill u z
    · simp
    · intro x y _ _ hx hy
      rw [add_smul, map_add (f := _), hx, hy, add_zero]
    · intro r x _ hx
      rw [smul_assoc, map_smul, hx, smul_zero]
  · intro u
    have : c u - 1 ∈ Ideal.span (Set.range fun u : U => c u - 1) := Ideal.subset_span ⟨u, rfl⟩
    rw [ha] at this
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 this
    show ρ u m = m
    have e : (c u - 1) • m = 0 := by rw [← hr, smul_assoc, hm, smul_zero]
    rw [hc, ← sub_eq_zero]
    rw [sub_smul, one_smul] at e
    exact e
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.KerResCyc
section
open ReciprocityTheory.Gal UpperTheory.V.Base

theorem UpperTheory.V.Base.kerResCyc :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M), ContAction ρ → ∀ (U' U : Subgroup G) (h : U' ≤ U) [(U'.subgroupOf U).Normal] (γ : G), γ ∈ U →
      U ≤ (Subgroup.zpowers γ ⊔ U').topologicalClosure →
      (Module.length R (H0U ρ U') ≠ ⊤ → Module.length R (LinearMap.ker (resU ρ h)) ≤ Module.length R (H0U ρ U)) ∧
      ((∀ m ∈ H0U ρ U', ∃ m' ∈ H0U ρ U', ρ γ m' - m' = m) → Function.Injective (resU ρ h)) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ hρ U' U h _ γ hγ hcl
  have memU : ∀ (V : Subgroup G) (m : M), m ∈ H0U ρ V ↔ ∀ g ∈ V, ρ g m = m := by
    intro V m
    simp [H0U, H0, Representation.mem_invariants]
  have hinv : ∀ m ∈ H0U ρ U', ρ γ m ∈ H0U ρ U' := by
    intro m hm
    rw [memU] at hm ⊢
    intro u hu
    have hc := Subgroup.Normal.conj_mem (H := U'.subgroupOf U) ⟨u, h hu⟩
      (by simpa [Subgroup.mem_subgroupOf] using hu) (⟨γ, hγ⟩⁻¹)
    rw [Subgroup.mem_subgroupOf] at hc
    simp only [inv_inv, Subgroup.coe_mul, InvMemClass.coe_inv] at hc
    have e : ρ u (ρ γ m) = ρ γ (ρ (γ⁻¹ * u * γ) m) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
      congr 2
      group
    rw [e, hm _ hc]
  let T : H0U ρ U' →ₗ[R] H0U ρ U' := LinearMap.codRestrict (H0U ρ U')
    ((ρ γ - LinearMap.id) ∘ₗ (H0U ρ U').subtype)
    (fun m => Submodule.sub_mem _ (hinv m m.2) m.2)
  have hT : ∀ m : H0U ρ U', ((T m : H0U ρ U') : M) = ρ γ m - m := fun m => rfl
  obtain ⟨φ, hφ⟩ := kerResGen1 R G M ρ hρ U' U h γ hγ hcl T hT
  refine ⟨fun hfin => ?_, fun hsurj => ?_⟩
  · have hfix : ∀ m : H0U ρ U', T m = 0 → (m : M) ∈ H0U ρ U := by
      intro m hm0
      have hγm : ρ γ m = m := by
        have := congrArg Subtype.val hm0
        rw [hT] at this
        exact sub_eq_zero.mp this
      let S : Subgroup G :=
        { carrier := {g | ρ g m = m}
          mul_mem' := by
            intro a b ha hb
            simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
            rw [hb, ha]
          one_mem' := by simp
          inv_mem' := by
            intro a ha
            simp only [Set.mem_setOf_eq] at *
            calc ρ a⁻¹ m = ρ a⁻¹ (ρ a m) := by rw [ha]
              _ = m := by rw [← Module.End.mul_apply, ← map_mul]; simp }
      have hScl : IsClosed (S : Set G) :=
        IsClosed.preimage (hρ.comp (Continuous.prodMk continuous_id continuous_const))
          (isClosed_singleton (x := (m : M)))
      have hle : Subgroup.zpowers γ ⊔ U' ≤ S :=
        sup_le (Subgroup.zpowers_le.mpr hγm) (fun u hu => (memU U' m).mp m.2 u hu)
      have hUS := hcl.trans (Subgroup.topologicalClosure_minimal _ hle hScl)
      exact (memU U m).mpr fun g hg => hUS hg
    let ι : LinearMap.ker T →ₗ[R] H0U ρ U := LinearMap.codRestrict (H0U ρ U)
      ((H0U ρ U').subtype ∘ₗ (LinearMap.ker T).subtype) (fun m => hfix m m.2)
    have hι : Function.Injective ι := by
      intro a b hab
      have e : ((ι a : H0U ρ U) : M) = ((ι b : H0U ρ U) : M) := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext e)
    calc Module.length R (LinearMap.ker (resU ρ h))
        ≤ Module.length R (H0U ρ U' ⧸ LinearMap.range T) := Module.length_le_of_injective φ hφ
      _ = Module.length R (LinearMap.ker T) :=
        (KStar.Selmer.length_ker_eq_length_coker T hfin).symm
      _ ≤ Module.length R (H0U ρ U) := Module.length_le_of_injective ι hι
  · have hq : ∀ x : H0U ρ U' ⧸ LinearMap.range T, x = 0 := by
      intro x
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [Submodule.Quotient.mk_eq_zero]
      obtain ⟨m', hm', he⟩ := hsurj y y.2
      exact ⟨⟨m', hm'⟩, Subtype.ext (by rw [hT]; exact he)⟩
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    have := @hφ ⟨x, hx⟩ 0 (by rw [hq (φ _), hq (φ 0)])
    rw [Submodule.mem_bot]
    exact congrArg Subtype.val this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LenRoots
section
open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem length_product_polynomial_le (O N : Type) [CommRing O] [AddCommGroup N] [Module O N]
    (f : Module.End O N) (p : ℕ → Polynomial O) (s : Finset ℕ) :
    Module.length O (LinearMap.ker (Polynomial.aeval f (∏ i ∈ s, p i))) ≤
        ∑ i ∈ s, Module.length O (LinearMap.ker (Polynomial.aeval f (p i))) ∧
    Module.length O (N ⧸ LinearMap.range (Polynomial.aeval f (∏ i ∈ s, p i))) ≤
        ∑ i ∈ s, Module.length O (N ⧸ LinearMap.range (Polynomial.aeval f (p i))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have key : ∀ g : Module.End O N, g = 1 →
        Module.length O (LinearMap.ker g) = 0 ∧ Module.length O (N ⧸ LinearMap.range g) = 0 := by
      rintro g rfl
      rw [Module.End.one_eq_id, LinearMap.ker_id, LinearMap.range_id]
      constructor <;> rw [Module.length_eq_zero_iff] <;> infer_instance
    obtain ⟨k1, k2⟩ := key (Polynomial.aeval f (∏ i ∈ (∅ : Finset ℕ), p i))
      (by rw [Finset.prod_empty, map_one])
    rw [Finset.sum_empty, Finset.sum_empty]
    exact ⟨k1.le, k2.le⟩
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, map_mul]
    obtain ⟨h1, h2⟩ := lenComp O N (Polynomial.aeval f (p a)) (Polynomial.aeval f (∏ i ∈ s, p i))
    exact ⟨h1.trans (add_le_add le_rfl ih.1), h2.trans (add_le_add le_rfl ih.2)⟩

theorem UpperTheory.V.Base.lenRoots :
    ∀ (O N : Type) [CommRing O] [IsDomain O] [AddCommGroup N] [Module O N] (n : ℕ) (ζ : O), 0 < n → IsPrimitiveRoot ζ n →
      ∀ f : Module.End O N, f ^ n = 1 →
      Module.length O N ≤ ∑ i ∈ Finset.range n, Module.length O (LinearMap.ker (f - ζ ^ i • (1 : Module.End O N))) ∧
      Module.length O N ≤ ∑ i ∈ Finset.range n, Module.length O (N ⧸ LinearMap.range (f - ζ ^ i • (1 : Module.End O N))) := by
  intro O N _ _ _ _ n ζ hn hζ f hf
  have hprod := X_pow_sub_C_eq_prod hζ hn (one_pow n)
  have hterm : ∀ i, Polynomial.aeval f (Polynomial.X - Polynomial.C (ζ ^ i * 1))
      = f - ζ ^ i • (1 : Module.End O N) := by
    intro i
    simp [Algebra.algebraMap_eq_smul_one, smul_pow]
  have e : Polynomial.aeval f (∏ i ∈ Finset.range n, (Polynomial.X - Polynomial.C (ζ ^ i * 1))) = 0 := by
    rw [← hprod]
    simp [hf]
  have key : ∀ g : Module.End O N, g = 0 →
      Module.length O (LinearMap.ker g) = Module.length O N ∧
      Module.length O (N ⧸ LinearMap.range g) = Module.length O N := by
    rintro g rfl
    rw [LinearMap.ker_zero, LinearMap.range_zero, Module.length_top,
      (Submodule.quotEquivOfEqBot (⊥ : Submodule O N) rfl).length_eq]
    exact ⟨rfl, rfl⟩
  have cong : ∀ g h : Module.End O N, g = h →
      Module.length O (LinearMap.ker g) = Module.length O (LinearMap.ker h) ∧
      Module.length O (N ⧸ LinearMap.range g) = Module.length O (N ⧸ LinearMap.range h) := by
    rintro g h rfl
    exact ⟨rfl, rfl⟩
  obtain ⟨h1, h2⟩ := length_product_polynomial_le O N f (fun i => Polynomial.X - Polynomial.C (ζ ^ i * 1))
    (Finset.range n)
  obtain ⟨k1, k2⟩ := key _ e
  refine ⟨?_, ?_⟩
  · rw [← k1]
    refine h1.trans (le_of_eq (Finset.sum_congr rfl fun i _ => (cong _ _ (hterm i)).1))
  · rw [← k2]
    refine h2.trans (le_of_eq (Finset.sum_congr rfl fun i _ => (cong _ _ (hterm i)).2))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LengthSpanCocycleFinite
section
open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem UpperTheory.V.Base.length_span_cocycle_finite {R N I : Type} [CommRing R] [AddCommGroup N] [Module R N] [Finite I]
    (hN : ∀ m : N, Module.length R (Submodule.span R {m}) ≠ ⊤) (Z : Submodule R (I → N)) (f : Z) :
    Module.length R (Submodule.span R {f}) ≠ ⊤ := by
  classical
  have := Fintype.ofFinite I
  let φ : Submodule.span R {f} →ₗ[R] (Π i : I, Submodule.span R {(f : I → N) i}) :=
    { toFun := fun g i => ⟨((g : Z) : I → N) i, by
        obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp g.2
        rw [← hr]
        exact Submodule.mem_span_singleton.mpr ⟨r, by simp⟩⟩
      map_add' := fun g h => by ext i; simp
      map_smul' := fun r g => by ext i; simp }
  have hφ : Function.Injective φ := by
    intro g h e
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun e i)
  refine ne_top_of_le_ne_top ?_ (Module.length_le_of_injective φ hφ)
  rw [Module.length_pi_of_fintype]
  exact (WithTop.sum_lt_top.mpr fun i _ => (hN _).lt_top).ne

theorem UpperTheory.V.Base.h2Ab :
    ∀ (R Q N : Type) [CommRing R] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q] [AddCommGroup N] [Module R N]
      [TopologicalSpace N] [IsTopologicalAddGroup N] [ContinuousConstSMul R N] [DiscreteTopology N] [IsPrincipalIdealRing R] [Group Q] (σ : Representation R Q N), (∀ a b : Q, a * b = b * a) → (∀ m : N, Module.length R (Submodule.span R {m}) ≠ ⊤) →
      (∀ g, ∃ c : R, ∀ m, σ g m = c • m) → Module.length R (H2 σ) ≤ (Nat.card Q : ℕ∞) ^ 2 * Module.length R (H0 σ) := by
  intro R Q N _ _ _ _ _ _ _ _ _ _ _ _ σ hcomm hN hsc
  classical
  choose c hc using hsc
  set J : Ideal R := Ideal.span (Set.range fun g => c g - 1) with hJ
  set a : R := Submodule.IsPrincipal.generator J with ha
  have haJ : a ∈ J := Submodule.IsPrincipal.generator_mem J
  have hJa : ∀ g, ∃ r : R, c g - 1 = r * a := by
    intro g
    have hmem : c g - 1 ∈ J := Ideal.subset_span ⟨g, rfl⟩
    rw [← Ideal.span_singleton_generator J] at hmem
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hmem
    exact ⟨r, hr.symm⟩
  have hH0 : ∀ m : N, a • m = 0 → m ∈ H0 σ := by
    intro m hm
    rw [H0, Representation.mem_invariants]
    intro g
    obtain ⟨r, hr⟩ := hJa g
    have hz : (c g - 1) • m = 0 := by rw [hr, mul_smul, hm, smul_zero]
    rw [hc, ← sub_eq_zero, ← hz, sub_smul, one_smul]
  have hB : ∀ f : Z2 σ, a • (f : Q × Q → N) ∈ B2 σ := by
    intro f
    set F : Q × Q → N := (f : Q × Q → N) with hF
    obtain ⟨-, hcoc⟩ := f.2
    refine Submodule.span_induction (p := fun x _ => x • F ∈ B2 σ) ?_ ?_ ?_ ?_ haJ
    · rintro _ ⟨g, rfl⟩
      rw [separated_dvr_second_cohomology_mem]
      refine ⟨fun x => F (g, x) - F (x, g), continuous_of_discreteTopology, ?_⟩
      funext ⟨x, y⟩
      have e1 := hcoc g x y
      have e2 := hcoc x g y
      have e3 := hcoc x y g
      rw [hc] at e1 e2 e3
      rw [hcomm x g] at e2
      rw [hcomm y g] at e3
      simp only [d1_apply, hc, Pi.smul_apply]
      have key : c x • (F (g, y) - F (y, g)) - (F (g, x * y) - F (x * y, g)) + (F (g, x) - F (x, g))
            - (c g - 1) • F (x, y)
          = -((c g • F (x, y) - F (g * x, y) + F (g, x * y) - F (g, x))
            - (c x • F (g, y) - F (g * x, y) + F (x, g * y) - F (x, g))
            + (c x • F (y, g) - F (x * y, g) + F (x, g * y) - F (x, y))) := by
        simp only [smul_sub, sub_smul, one_smul]
        abel
      rw [e1, e2, e3] at key
      simpa [sub_eq_zero] using key
    · rw [zero_smul]
      exact zero_mem _
    · intro x y _ _ hx hy
      rw [add_smul]
      exact add_mem hx hy
    · intro r x _ hx
      rw [smul_eq_mul, mul_smul]
      exact Submodule.smul_mem _ r hx
  let Zs := Z2 σ
  let mul : Zs →ₗ[R] Zs := a • LinearMap.id
  have h1 : Module.length R (H2 σ) ≤ Module.length R (Zs ⧸ LinearMap.range mul) := by
    let q := Submodule.liftQ (LinearMap.range mul) (Submodule.mkQ (Submodule.comap Zs.subtype (B2 σ))) (by
      rintro _ ⟨z, rfl⟩
      rw [LinearMap.mem_ker, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      exact hB z)
    refine Module.length_le_of_surjective q ?_
    intro y
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ y
    exact ⟨Submodule.mkQ _ z, rfl⟩
  have h2 := lenCokerLe R Zs (UpperTheory.V.Base.length_span_cocycle_finite hN Zs) a
  have h3 : Module.length R (LinearMap.ker mul) ≤ Module.length R (Q × Q → H0 σ) := by
    let φ : LinearMap.ker mul →ₗ[R] (Q × Q → H0 σ) :=
      { toFun := fun z p => ⟨((z : Zs) : Q × Q → N) p, hH0 _ (by
            have hz : mul (z : Zs) = 0 := LinearMap.mem_ker.mp z.2
            exact congrFun (congrArg Subtype.val hz) p)⟩
        map_add' := fun _ _ => by ext; simp
        map_smul' := fun _ _ => by ext; simp }
    refine Module.length_le_of_injective φ ?_
    intro z w e
    apply Subtype.ext
    apply Subtype.ext
    funext p
    have hp := congrArg Subtype.val (congrFun e p)
    exact hp
  calc Module.length R (H2 σ) ≤ _ := h1
    _ ≤ _ := h2
    _ ≤ _ := h3
    _ = (Nat.card Q : ℕ∞) ^ 2 * Module.length R (H0 σ) := by
      rw [Module.length_pi]
      congr 1
      rw [ENat.card_eq_coe_natCard, Nat.card_prod, pow_two]
      push_cast
      rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.SelBase
section
open ReciprocityTheory.Gal UpperTheory.V.Base

theorem UpperTheory.V.Base.selBase :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (O M' : Type) [CommRing O] [Algebra R O] [IsLocalRing R] [IsLocalRing O] [IsLocalHom (algebraMap R O)] [Module.Free R O]
      [Module.Finite R O] [AddCommGroup M'] [Module O M'] [Module R M'] [IsScalarTower R O M'] [TopologicalSpace M']
      [IsTopologicalAddGroup M'] [ContinuousConstSMul O M'] [DiscreteTopology M'] (ρ' : Representation O G M') (j : M →ₗ[R] M'),
      IsBaseChange O j → (∀ g m, j (ρ g m) = ρ' g (j m)) → ∀ (U : Subgroup G) (𝒟 : Set (Subgroup G)),
      Module.length O (LocSel ρ' U 𝒟) = Module.length R (LocSel ρ U 𝒟) * Module.length O (O ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R O)) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ O M' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ρ' j hb hj U 𝒟
  exact length_of_isBaseChange (isBaseChange_selMap ρ ρ' j hj U hb 𝒟)
end

