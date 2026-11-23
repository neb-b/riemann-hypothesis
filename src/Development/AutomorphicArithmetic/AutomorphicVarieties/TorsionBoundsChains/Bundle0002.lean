module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0061

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.OrbStep
section
open CategoryTheory UpperTheory.V.KH

private theorem UpperTheory.V.KH.stabLe_sub {G X : Type} [Group G] [MulAction G X] {s : ℕ}
    (h : StabLe G X s) (U : SubMulAction G X) : StabLe G U s := by
  intro u
  rw [SubMulAction.stabilizer_of_subMul]
  exact h u

theorem UpperTheory.V.KH.orbStep :
    ∀ (G X : Type) [Group G] [MulAction G X] (A s : ℕ) (x : X), OrbLe G X (A + 1) → StabLe G X s →
      ∃ U V : SubMulAction G X, (∀ y, y ∈ V ↔ y ∉ U) ∧ Nonempty U ∧ MulAction.IsPretransitive G U ∧
        StabLe G U s ∧ StabLe G V s ∧ OrbLe G V A := by
  intro G X _ _ A s x hO hS
  let U : SubMulAction G X :=
    { carrier := MulAction.orbit G x
      smul_mem' := by
        rintro g y ⟨h, rfl⟩
        exact ⟨g * h, mul_smul _ _ _⟩ }
  have hxU : x ∈ U := MulAction.mem_orbit_self x
  refine ⟨U, Uᶜ, fun y => Iff.rfl, ⟨⟨x, hxU⟩⟩, ?_, stabLe_sub hS U, stabLe_sub hS Uᶜ, ?_⟩
  · refine ⟨fun a b => ?_⟩
    obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    obtain ⟨g, rfl⟩ := ha
    obtain ⟨h, rfl⟩ := hb
    refine ⟨h * g⁻¹, Subtype.ext ?_⟩
    change (h * g⁻¹) • g • x = h • x
    rw [smul_smul, inv_mul_cancel_right]
  · have hrel : ∀ a b : (Uᶜ : SubMulAction G X),
        (MulAction.orbitRel G (Uᶜ : SubMulAction G X)) a b ↔ (MulAction.orbitRel G X) a b := by
      intro a b
      rw [SubMulAction.orbitRel_of_subMul]
      rfl
    let f : MulAction.orbitRel.Quotient G (Uᶜ : SubMulAction G X) → MulAction.orbitRel.Quotient G X :=
      Quotient.map (fun a => (a : X)) (fun a b hab => (hrel a b).1 hab)
    let F : Option (MulAction.orbitRel.Quotient G (Uᶜ : SubMulAction G X)) →
        MulAction.orbitRel.Quotient G X := fun o => o.elim (Quotient.mk _ x) f
    have hF : Function.Injective F := by
      have hne : ∀ a : (Uᶜ : SubMulAction G X),
          (Quotient.mk _ (a : X) : MulAction.orbitRel.Quotient G X) ≠ Quotient.mk _ x := by
        intro a hax
        have h1 : (MulAction.orbitRel G X) (a : X) x := Quotient.exact hax
        exact a.2 h1
      rintro (_ | p) (_ | q) hpq
      · rfl
      · induction q using Quotient.inductionOn with
        | h b => exact absurd hpq.symm (hne b)
      · induction p using Quotient.inductionOn with
        | h a => exact absurd hpq (hne a)
      · induction p using Quotient.inductionOn with
        | h a =>
          induction q using Quotient.inductionOn with
          | h b =>
            congr 1
            exact Quotient.sound ((hrel a b).2 (Quotient.exact hpq))
    haveI : Finite (MulAction.orbitRel.Quotient G X) := hO.1
    haveI : Finite (Option (MulAction.orbitRel.Quotient G (Uᶜ : SubMulAction G X))) :=
      Finite.of_injective F hF
    haveI : Finite (MulAction.orbitRel.Quotient G (Uᶜ : SubMulAction G X)) :=
      Finite.of_injective some (Option.some_injective _)
    refine ⟨inferInstance, ?_⟩
    have h2 := Nat.card_le_card_of_injective F hF
    rw [Finite.card_option] at h2
    have h3 := hO.2
    omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.PermEmpty
section
open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.permEmpty :
    ∀ (G X : Type) [Group G] [MulAction G X] [IsEmpty X] (j : ℕ),
      CardLe (groupHomology (permRep G X) j) 1 := by
  intro G X _ _ _ j
  have hC : Subsingleton ((groupHomology.inhomogeneousChains (permRep G X)).X j) := by
    change Subsingleton ((Fin j → G) →₀ (X →₀ ℤ))
    infer_instance
  have hZ : Subsingleton (groupHomology.cycles (permRep G X) j) := by
    refine ⟨fun a b => ?_⟩
    exact (ModuleCat.mono_iff_injective (groupHomology.iCycles (permRep G X) j)).1
      inferInstance (Subsingleton.elim _ _)
  have hH : Subsingleton (groupHomology (permRep G X) j) := by
    refine ⟨fun a b => ?_⟩
    induction a using groupHomology_induction_on with
    | h a =>
      induction b using groupHomology_induction_on with
      | h b => rw [Subsingleton.elim a b]
  haveI := hH
  exact ⟨Finite.of_subsingleton, (Finite.card_le_one_iff_subsingleton).2 hH⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.PermSplit
section
open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.permSplit :
    ∀ (G X : Type) [Group G] [MulAction G X] (U V : SubMulAction G X), (∀ y, y ∈ V ↔ y ∉ U) →
      ∃ (f : permRep G U ⟶ permRep G X) (g : permRep G X ⟶ permRep G V),
        Function.Injective f.hom ∧ Function.Exact f.hom g.hom ∧ Function.Surjective g.hom := by
  intro G X _ _ U V hUV
  let F : (perm G U).IntertwiningMap (perm G X) :=
    { toLinearMap := Finsupp.lmapDomain ℤ ℤ (Subtype.val : U → X)
      isIntertwining' := by
        intro g
        refine LinearMap.ext fun f => ?_
        simp only [LinearMap.comp_apply, perm_apply, Finsupp.lmapDomain_apply]
        rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
        congr 1 }
  let Gm : (perm G X).IntertwiningMap (perm G V) :=
    { toLinearMap := Finsupp.lsubtypeDomain (V : Set X)
      isIntertwining' := by
        intro g
        refine LinearMap.ext fun f => ?_
        ext ⟨y, hy⟩
        change (Finsupp.mapDomain (fun x => g • x) f) y =
          (Finsupp.mapDomain (fun v : V => g • v) (Finsupp.subtypeDomain (· ∈ V) f)) ⟨y, hy⟩
        have hy' : g⁻¹ • y ∈ V := V.smul_mem _ hy
        have e2 : (⟨y, hy⟩ : V) = g • (⟨g⁻¹ • y, hy'⟩ : V) := Subtype.ext (by simp)
        rw [e2, Finsupp.mapDomain_apply_of_injective (MulAction.injective g), Finsupp.subtypeDomain_apply]
        have e1 : y = g • (g⁻¹ • y) := (smul_inv_smul g y).symm
        conv_lhs => rw [e1]
        rw [Finsupp.mapDomain_apply_of_injective (MulAction.injective g)] }
  refine ⟨Rep.ofHom F, Rep.ofHom Gm, ?_, ?_, ?_⟩
  · rw [Rep.hom_ofHom]
    change Function.Injective (Finsupp.mapDomain (Subtype.val : U → X) : (U →₀ ℤ) → (X →₀ ℤ))
    exact Finsupp.mapDomain_injective Subtype.val_injective
  · rw [Rep.hom_ofHom, Rep.hom_ofHom]
    intro y
    change Finsupp.subtypeDomain (· ∈ V) y = 0 ↔
      y ∈ Set.range (Finsupp.mapDomain (Subtype.val : U → X) : (U →₀ ℤ) → (X →₀ ℤ))
    constructor
    · intro hy0
      refine ⟨Finsupp.subtypeDomain (· ∈ U) y, ?_⟩
      ext x
      by_cases hx : x ∈ U
      · rw [show x = ((⟨x, hx⟩ : U) : X) from rfl, Finsupp.mapDomain_apply_of_injective Subtype.val_injective,
          Finsupp.subtypeDomain_apply]
      · rw [Finsupp.mapDomain_notin_range _ _ (by rintro ⟨u, rfl⟩; exact hx u.2)]
        have hxV : x ∈ V := (hUV x).2 hx
        have h1 := DFunLike.congr_fun hy0 ⟨x, hxV⟩
        simp only [Finsupp.subtypeDomain_apply, Finsupp.coe_zero, Pi.zero_apply] at h1
        exact h1.symm
    · rintro ⟨u, rfl⟩
      ext ⟨x, hx⟩
      rw [Finsupp.subtypeDomain_apply, Finsupp.mapDomain_notin_range _ _ ?_]
      · simp
      · rintro ⟨w, rfl⟩
        exact ((hUV _).1 hx) w.2
  · rw [Rep.hom_ofHom]
    intro h
    refine ⟨Finsupp.mapDomain (Subtype.val : V → X) h, ?_⟩
    ext ⟨y, hy⟩
    change Finsupp.mapDomain (Subtype.val : V → X) h ((⟨y, hy⟩ : V) : X) = h ⟨y, hy⟩
    exact Finsupp.mapDomain_apply_of_injective Subtype.val_injective _ _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Subquot
section
open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.subquot :
    ∀ (ι Z H : Type) [Finite ι] [AddCommGroup Z] [AddCommGroup H] (i : Z →+ (ι →₀ ℤ)) (q : Z →+ H)
      (n : ℕ), 1 ≤ n → Function.Injective i → Function.Surjective q → (∀ h : H, n • h = 0) →
      CardLe H (n ^ Nat.card ι) := by
  intro ι Z H _ _ _ i q n hn hi hq hk
  classical
  have := Fintype.ofFinite ι
  let i' : Z →ₗ[ℤ] (ι →₀ ℤ) := i.toIntLinearMap
  have hi' : Function.Injective i' := hi
  have : Module.Finite ℤ Z := Module.Finite.of_injective i' hi'
  have : Module.Free ℤ Z :=
    Module.Free.of_equiv (LinearEquiv.ofInjective i' hi').symm
  have hr : Module.finrank ℤ Z ≤ Nat.card ι := by
    have h := LinearMap.finrank_le_finrank_of_injective hi'
    rwa [Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card] at h
  let b := Module.finBasis ℤ Z
  let f : (Fin (Module.finrank ℤ Z) → Fin n) → H := fun c => ∑ k, (((c k : ℕ) : ℤ)) • q (b k)
  have hn0 : (0 : ℤ) < n := by exact_mod_cast hn
  have hf : Function.Surjective f := by
    intro h
    obtain ⟨z, rfl⟩ := hq h
    refine ⟨fun k => ⟨(b.repr z k % n).toNat, ?_⟩, ?_⟩
    · have h1 := Int.emod_nonneg (b.repr z k) hn0.ne'
      have h2 := Int.emod_lt_of_pos (b.repr z k) hn0
      omega
    · set_option synthInstance.maxHeartbeats 100000 in
        conv_rhs => rw [← b.sum_repr z, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have h1 := Int.emod_nonneg (b.repr z k) hn0.ne'
      rw [map_zsmul]
      simp only [Int.toNat_of_nonneg h1]
      have h3 : (n : ℤ) • q (b k) = 0 := by rw [natCast_zsmul]; exact hk _
      conv_rhs => rw [← Int.emod_add_ediv_mul (b.repr z k) n, add_smul, mul_smul, h3, smul_zero,
        add_zero]
  refine ⟨Finite.of_surjective f hf, (Nat.card_le_card_of_surjective f hf).trans ?_⟩
  rw [Nat.card_fun, Nat.card_fin, Nat.card_fin]
  exact Nat.pow_le_pow_right hn hr
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.TorsSat
section
open CategoryTheory UpperTheory.V.KH

private theorem torsSat_coeff {M ι : Type} [AddCommGroup M] (L : Set M) (v : ι → M)
    (hv : LinearIndependent ℤ v) (x : M) (hx : x ∈ Submodule.span ℤ (Set.range v))
    (n : ℤ) (hn : n ≠ 0) (hnx : n • x ∈ Submodule.span ℤ (Set.range v ∩ L)) :
    x ∈ Submodule.span ℤ (Set.range v ∩ L) := by
  have hS : Set.range v ∩ L = v '' (v ⁻¹' L) := by
    rw [Set.image_preimage_eq_inter_range, Set.inter_comm]
  rw [hS] at hnx ⊢
  rw [Finsupp.mem_span_image_iff_linearCombination] at hnx ⊢
  obtain ⟨d, hd, hdx⟩ := hnx
  rw [← Finsupp.range_linearCombination] at hx
  obtain ⟨c, rfl⟩ := hx
  have hcd : d = n • c := by
    apply hv
    rw [hdx, map_smul]
  refine ⟨c, ?_, rfl⟩
  rw [Finsupp.mem_supported'] at hd ⊢
  intro i hi
  have := hd i hi
  rw [hcd, Finsupp.smul_apply, smul_eq_mul, mul_eq_zero] at this
  exact this.resolve_left hn

private theorem torsSat_mult {M : Type} [AddCommGroup M] (L : Set M) (N : Submodule ℤ M)
    (h : ∀ x ∈ L, ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ N) (x : M) (hx : x ∈ Submodule.span ℤ L) :
    ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ N :=
  _root_.UpperTheory.Reformulated.B.Qi35.torsSat_mult L N h x hx

private theorem torsSat_tors {M : Type} [AddCommGroup M] (N : Submodule ℤ M) (x : M)
    (hx : (Submodule.Quotient.mk x : M ⧸ N) ∈ AddCommGroup.torsion (M ⧸ N)) :
    ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ N := by
  have hx' : IsOfFinAddOrder (Submodule.Quotient.mk x : M ⧸ N) := hx
  obtain ⟨n, hn, h⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.1 hx'
  refine ⟨n, by exact_mod_cast hn.ne', ?_⟩
  rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul, natCast_zsmul]
  exact h

theorem UpperTheory.V.KH.torsSat :
    ∀ (M ι : Type) [AddCommGroup M] [IsAddTorsionFree M] (L : Set M) (v : ι → M) (B : ℕ),
      LinearIndependent ℤ v →
      (∀ x ∈ L, ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ Submodule.span ℤ (Set.range v ∩ L)) →
      CardLe (M ⧸ Submodule.span ℤ (Set.range v)) B → TorsLe (M ⧸ Submodule.span ℤ L) B := by
  intro M ι _ _ L v B hv hL hc
  obtain ⟨hfin, hB⟩ := hc
  choose lift hlift using Submodule.Quotient.mk_surjective (Submodule.span ℤ L)
  let f : AddCommGroup.torsion (M ⧸ Submodule.span ℤ L) → M ⧸ Submodule.span ℤ (Set.range v) :=
    fun t => Submodule.Quotient.mk (lift t.1)
  have hf : Function.Injective f := by
    intro t s hts
    have h1 : lift t.1 - lift s.1 ∈ Submodule.span ℤ (Set.range v) :=
      (Submodule.Quotient.eq _).1 hts
    have h2 : (Submodule.Quotient.mk (lift t.1 - lift s.1) : M ⧸ Submodule.span ℤ L) ∈
        AddCommGroup.torsion (M ⧸ Submodule.span ℤ L) := by
      rw [Submodule.Quotient.mk_sub, hlift, hlift]
      exact sub_mem t.2 s.2
    obtain ⟨n, hn, hnx⟩ := torsSat_tors _ _ h2
    obtain ⟨m, hm, hmx⟩ := torsSat_mult L _ hL _ hnx
    rw [smul_smul] at hmx
    have h3 := torsSat_coeff L v hv _ h1 _ (mul_ne_zero hm hn) hmx
    have h4 : lift t.1 - lift s.1 ∈ Submodule.span ℤ L :=
      Submodule.span_mono Set.inter_subset_right h3
    apply Subtype.ext
    rw [← hlift t.1, ← hlift s.1]
    exact (Submodule.Quotient.eq _).2 h4
  exact ⟨Finite.of_injective f hf, (Nat.card_le_card_of_injective f hf).trans hB⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Transport
section
open CategoryTheory UpperTheory.V.KH

theorem UpperTheory.V.KH.transport :
    (∀ (M N : Type) [AddCommGroup M] [AddCommGroup N] (_ : M ≃+ N) (B : ℕ), TorsLe M B → TorsLe N B) ∧
    (∀ (M N : Type) (_ : M ≃ N) (B : ℕ), CardLe M B → CardLe N B) ∧
    (∀ (M : Type) [AddCommGroup M] (B B' : ℕ), B ≤ B' → TorsLe M B → TorsLe M B') ∧
    (∀ (M : Type) (B B' : ℕ), B ≤ B' → CardLe M B → CardLe M B') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro M N _ _ e B h
    obtain ⟨hfin, hcard⟩ := h
    let f : AddCommGroup.torsion M ≃ AddCommGroup.torsion N :=
      (e : M ≃ N).subtypeEquiv fun x => by
        simp only [SetLike.mem_coe, AddCommGroup.mem_torsion, ← addOrderOf_pos_iff]
        simp
    exact ⟨Finite.of_equiv _ f, (Nat.card_congr f).symm ▸ hcard⟩
  · intro M N e B h
    obtain ⟨hfin, hcard⟩ := h
    exact ⟨Finite.of_equiv _ e, (Nat.card_congr e).symm ▸ hcard⟩
  · intro M _ B B' hB h
    exact ⟨h.1, h.2.trans hB⟩
  · intro M B B' hB h
    exact ⟨h.1, h.2.trans hB⟩
end

