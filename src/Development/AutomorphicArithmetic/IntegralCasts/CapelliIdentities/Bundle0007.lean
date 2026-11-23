module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CoboundaryCriterion
section
theorem UpperTheory.Reformulated.B.CoboundaryCriterion.isCoboundary_of_coprime :
    ∀ {R G M : Type} [inst : CommRing R]
    [inst_1 : Group G] [inst_2 : AddCommGroup M] [inst_3 : _root_.Module R M] (ρ : Representation R G M) {l : ℕ}
    {H C : Type} [inst_4 : Group H] [inst_5 : Group C] [Finite C] (i : H →* G) (f : H →* C),
    (Nat.card C).Coprime l →
      (∀ (m : M), l • m = (0 : M)) →
        ∀ (z : G → M),
          (∀ (g h : G), z (g * h) = z g + ((ρ : G → M →ₗ[R] M) g : M → M) (z h)) →
            (∀ (u : H), (f : H → C) u = (1 : C) → z ((i : H → G) u) = (0 : M)) →
              ∃ (b : M), ∀ (u : H), z ((i : H → G) u) = ((ρ : G → M →ₗ[R] M) ((i : H → G) u) : M → M) b - b := by
  intro R G M _ _ _ _ ρ l H C _ _ _ i f hcop hl z hz hker
  classical
  have hfac : ∀ u v : H, f u = f v → z (i u) = z (i v) := by
    intro u v huv
    have h1 : z (i (v⁻¹ * u)) = 0 := hker _ (by simp [huv])
    have h2 : i u = i v * i (v⁻¹ * u) := by simp
    rw [h2, hz, h1, map_zero, add_zero]
  haveI : Fintype f.range := Fintype.ofFinite _
  obtain ⟨s, hs⟩ : ∃ s : f.range → H, ∀ q, f (s q) = (q : C) :=
    ⟨fun q => q.2.choose, fun q => q.2.choose_spec⟩
  have hcop' : (Nat.card f.range).Coprime l :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_subgroup_dvd_card f.range) hcop
  set n := Nat.card f.range with hn
  set S : M := ∑ q : f.range, z (i (s q)) with hS
  have key : ∀ u : H, S = n • z (i u) + ρ (i u) S := by
    intro u
    have h1 : S = ∑ q : f.range, z (i (s (f.rangeRestrict u * q))) :=
      (Equiv.sum_comp (Equiv.mulLeft (f.rangeRestrict u)) (fun q => z (i (s q)))).symm
    have h2 : ∀ q : f.range,
        z (i (s (f.rangeRestrict u * q))) = z (i u) + ρ (i u) (z (i (s q))) := by
      intro q
      rw [← hz, ← map_mul]
      apply hfac
      simp [hs]
    calc S = ∑ q : f.range, (z (i u) + ρ (i u) (z (i (s q)))) := by
          rw [h1]; exact Finset.sum_congr rfl fun q _ => h2 q
      _ = n • z (i u) + ρ (i u) S := by
          set_option synthInstance.maxHeartbeats 100000 in
            rw [Finset.sum_add_distrib, Finset.sum_const, hS, map_sum, hn, Nat.card_eq_fintype_card,
            Finset.card_univ]
  obtain ⟨a, c, hac⟩ : IsCoprime (n : ℤ) (l : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop'
  refine ⟨-(a • S), fun u => ?_⟩
  have h3 : (n : ℤ) • z (i u) = S - ρ (i u) S := by
    rw [natCast_zsmul, eq_sub_iff_add_eq]; exact (key u).symm
  have h4 : (l : ℤ) • z (i u) = 0 := by rw [natCast_zsmul, hl]
  calc z (i u) = (a * n + c * l) • z (i u) := by rw [hac, one_smul]
    _ = a • (S - ρ (i u) S) := by rw [add_smul, mul_smul, mul_smul, h3, h4, smul_zero, add_zero]
    _ = ρ (i u) (-(a • S)) - -(a • S) := by
        rw [map_neg, map_zsmul, smul_sub]; abel
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CoboundaryOfGenerator
section
namespace UpperTheory.Reformulated.B.CoboundaryOfGenerator

noncomputable def ContAction.{u_1, u_2, u_3}
    {R : Type u_1} [CommRing R] {G : Type u_2} [Group G] [TopologicalSpace G]
    {M : Type u_3} [AddCommGroup M] [Module R M] [TopologicalSpace M]
    (rho : Representation R G M) : Prop :=
  Continuous fun p : G × M => rho p.1 p.2

theorem aux2.{u_1, u_2, u_3}
    {R : Type u_3} [CommRing R] {G : Type u_1} [Group G] [TopologicalSpace G]
    {M : Type u_2} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    (rho : Representation R G M) {f f' : G → M}
    (hf : Continuous f ∧ ∀ g h : G, f (g * h) = f g + rho g (f h))
    (hf' : Continuous f' ∧ ∀ g h : G, f' (g * h) = f' g + rho g (f' h)) :
    Continuous (f + f') ∧ ∀ g h : G, (f + f') (g * h) = (f + f') g + rho g ((f + f') h) := by
  obtain ⟨hc, hf⟩ := hf
  obtain ⟨hc', hf'⟩ := hf'
  refine ⟨hc.add hc', fun g h => ?_⟩
  simp only [Pi.add_apply, hf g h, hf' g h, map_add]
  abel

theorem aux3.{u_1, u_2, u_3}
    {R : Type u_3} [CommRing R] {G : Type u_1} [Group G] [TopologicalSpace G]
    {M : Type u_2} [AddCommGroup M] [Module R M] [TopologicalSpace M]
    (rho : Representation R G M) :
    Continuous (0 : G → M) ∧ ∀ g h : G, (0 : G → M) (g * h) = (0 : G → M) g + rho g ((0 : G → M) h) :=
  ⟨continuous_const, fun _ _ => by simp⟩

theorem aux4.{u_1, u_2, u_3}
    {R : Type u_3} [CommRing R] {G : Type u_1} [Group G] [TopologicalSpace G]
    {M : Type u_2} [AddCommGroup M] [Module R M] [TopologicalSpace M] [ContinuousConstSMul R M]
    (rho : Representation R G M) (c : R) (f : G → M)
    (hf : Continuous f ∧ ∀ g h : G, f (g * h) = f g + rho g (f h)) :
    Continuous (c • f) ∧ ∀ g h : G, (c • f) (g * h) = (c • f) g + rho g ((c • f) h) := by
  obtain ⟨hc, hf⟩ := hf
  refine ⟨hc.const_smul c, fun g h => ?_⟩
  simp only [Pi.smul_apply, hf g h, map_smul, smul_add]

noncomputable def Z1.{u_1, u_2, u_3}
    {R : Type u_1} [CommRing R] {G : Type u_2} [Group G] [TopologicalSpace G]
    {M : Type u_3} [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
    (rho : Representation R G M) : Submodule R (G → M) where
  carrier := {f : G → M | Continuous f ∧ ∀ g h : G, f (g * h) = f g + rho g (f h)}
  add_mem' := aux2 rho
  zero_mem' := aux3 rho
  smul_mem' := aux4 rho

theorem aux6.{u_1, u_2}
    {R : Type u_1} {M : Type u_2} [SMul R M] [TopologicalSpace M] [DiscreteTopology M] :
    ContinuousConstSMul R M :=
  ⟨fun _ => continuous_of_discreteTopology⟩

theorem aux7.{u_1} {R : Type u_1} [CommRing R] : RingHomSurjective (RingHom.id R) :=
  ⟨Function.surjective_id⟩

noncomputable def d0.{u_1, u_2, u_3}
    {R : Type u_1} [CommRing R] {G : Type u_2} [Group G]
    {M : Type u_3} [AddCommGroup M] [Module R M]
    (rho : Representation R G M) : M →ₗ[R] (G → M) :=
  LinearMap.pi fun g => rho g - LinearMap.id

noncomputable def B1.{u_1, u_2, u_3}
    {R : Type u_1} [CommRing R] {G : Type u_2} [Group G]
    {M : Type u_3} [AddCommGroup M] [Module R M]
    (rho : Representation R G M) : Submodule R (G → M) :=
  LinearMap.range (d0 rho)

theorem cobOfGen
    (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] (χ : Γ →* ℤ_[l]ˣ)
    (R M : Type) [CommRing R] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [DiscreteTopology M]
    (ρ : Representation R Γ M) (γ : Γ)
    (hχ : Continuous χ) (hρ : ContAction ρ)
    (hker : ∀ g, χ g = 1 → ∀ m, ρ g m = m)
    (hgen : ∀ g, χ g ∈ (Subgroup.zpowers (χ γ)).topologicalClosure)
    (hsurj : Function.Surjective fun m => ρ γ m - m)
    (z : Γ → M) (hz : z ∈ @Z1 R _ Γ _ _ M _ _ _ inferInstance aux6 ρ)
    (hz0 : ∀ g, χ g = 1 → z g = 0) :
    z ∈ B1 ρ := by
  have hzc : Continuous z := hz.1
  have hzm : ∀ g h : Γ, z (g * h) = z g + ρ g (z h) := hz.2
  obtain ⟨m, hm⟩ := hsurj (z γ)
  have hone : z 1 = 0 := hz0 1 (map_one χ)
  -- The cocycle agrees with the coboundary on a closed subgroup containing γ.
  let S : Subgroup Γ :=
    { carrier := {g | z g = ρ g m - m}
      one_mem' := by
        change z 1 = ρ 1 m - m
        simp [hone]
      mul_mem' := by
        intro a b ha hb
        have ha' : z a = ρ a m - m := ha
        have hb' : z b = ρ b m - m := hb
        change z (a * b) = ρ (a * b) m - m
        rw [hzm, ha', hb', map_mul, map_sub, mul_apply_eq_comp]
        abel
      inv_mem' := by
        intro a ha
        have ha' : z a = ρ a m - m := ha
        change z a⁻¹ = ρ a⁻¹ m - m
        have h1 := hzm a⁻¹ a
        have h2 : ρ a⁻¹ (ρ a m) = m := by
          rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self]
        rw [inv_mul_cancel, hone, ha', map_sub, h2] at h1
        rw [eq_neg_of_add_eq_zero_left h1.symm, neg_sub] }
  have hρm : Continuous fun g : Γ => ρ g m :=
    Continuous.comp (g := fun p : Γ × M => ρ p.1 p.2) (f := fun g : Γ => (g, m)) hρ
      (continuous_id.prodMk continuous_const)
  have hSc : IsClosed (S : Set Γ) := isClosed_eq hzc (hρm.sub continuous_const)
  have himg : IsClosed ((S.map χ : Subgroup ℤ_[l]ˣ) : Set ℤ_[l]ˣ) := by
    rw [Subgroup.coe_map]
    exact (hSc.isCompact.image hχ).isClosed
  have hle : (Subgroup.zpowers (χ γ)).topologicalClosure ≤ S.map χ :=
    Subgroup.topologicalClosure_minimal _
      ((Subgroup.zpowers_le).2 ⟨γ, hm.symm, rfl⟩) himg
  have hall : ∀ g : Γ, g ∈ S := by
    intro g
    obtain ⟨s, hs, hsg⟩ := hle (hgen g)
    have hk : χ (s⁻¹ * g) = 1 := by rw [map_mul, map_inv, hsg, inv_mul_cancel]
    have hmem : s⁻¹ * g ∈ S := by
      change z (s⁻¹ * g) = ρ (s⁻¹ * g) m - m
      rw [hz0 _ hk, hker _ hk, sub_self]
    simpa using S.mul_mem hs hmem
  refine ⟨m, funext fun g => ?_⟩
  exact (hall g).symm

end UpperTheory.Reformulated.B.CoboundaryOfGenerator
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CochainInjectiveExact
section
open CategoryTheory in
private lemma exists_lift {k : Type} [CommRing k] {K L M : CochainComplex (ModuleCat.{0} k) ℕ}
    (u : K ⟶ M) (ι : L ⟶ M) (hι : ∀ m : ℕ, Function.Injective (ι.f m).hom)
    (h : ∀ (m : ℕ) (x : K.X m), ∃ y, (ι.f m).hom y = (u.f m).hom x) :
    ∃ φ : K ⟶ L, ∀ (m : ℕ) (x : K.X m), (ι.f m).hom ((φ.f m).hom x) = (u.f m).hom x := by
  let p : ∀ m : ℕ, K.X m ⟶ L.X m := fun m =>
    ModuleCat.ofHom ((u.f m).hom.codRestrictOfInjective (ι.f m).hom (hι m) (h m))
  have hp : ∀ m : ℕ, p m ≫ ι.f m = u.f m := fun m =>
    ModuleCat.hom_ext (LinearMap.codRestrictOfInjective_comp _ _ _ _)
  refine ⟨{ f := p, comm' := fun i j _ => ?_ }, fun m x => congr($(hp m).hom x)⟩
  haveI : Mono (ι.f j) := (ModuleCat.mono_iff_injective _).2 (hι j)
  rw [← cancel_mono (ι.f j), Category.assoc, Category.assoc, hp, ← ι.comm, ← Category.assoc, hp,
    u.comm]

open CategoryTheory in
private lemma exists_map {k G : Type} [CommRing k] [Group G] [TopologicalSpace G]
    {A B : Rep.{0, 0, 0} k G} (f : A ⟶ B) {KA KB : CochainComplex (ModuleCat.{0} k) ℕ}
    (ιA : KA ⟶ groupCohomology.inhomogeneousCochains A)
    (ιB : KB ⟶ groupCohomology.inhomogeneousCochains B)
    (iB : ∀ m : ℕ, Function.Injective (ιB.f m).hom)
    (hA : ∀ (m : ℕ) (x : (Fin m → G) → A.V), (∃ y, (ιA.f m).hom y = x) ↔ IsLocallyConstant x)
    (hB : ∀ (m : ℕ) (x : (Fin m → G) → B.V), (∃ y, (ιB.f m).hom y = x) ↔ IsLocallyConstant x) :
    ∃ φ : KA ⟶ KB, ∀ (m : ℕ) (x : KA.X m) (t : Fin m → G),
      ((ιB.f m).hom ((φ.f m).hom x) : (Fin m → G) → B.V) t =
        f.hom (((ιA.f m).hom x : (Fin m → G) → A.V) t) := by
  obtain ⟨φ, hφ⟩ := exists_lift (ιA ≫ groupCohomology.cochainsMap (MonoidHom.id G) f) ιB iB
    fun m x => (hB m _).2 (((hA m _).1 ⟨x, rfl⟩).comp f.hom)
  exact ⟨φ, fun m x t => congr_fun (hφ m x) t⟩

theorem UpperTheory.cochain_injective_exact :
    ∀ {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] (A B C : Rep.{0, 0, 0} k G)
        (f : A ⟶ B) (g : B ⟶ C) (KA KB KC : CochainComplex (ModuleCat.{0} k) ℕ)
        (ιA : KA ⟶ groupCohomology.inhomogeneousCochains A)
        (ιB : KB ⟶ groupCohomology.inhomogeneousCochains B)
        (ιC : KC ⟶ groupCohomology.inhomogeneousCochains C),
        Function.Injective f.hom → Function.Exact f.hom g.hom → Function.Surjective g.hom →
        (∀ m : ℕ, Function.Injective (ιA.f m).hom) → (∀ m : ℕ, Function.Injective (ιB.f m).hom) →
        (∀ m : ℕ, Function.Injective (ιC.f m).hom) →
        (∀ (m : ℕ) (x : (Fin m → G) → A.V), (∃ y, (ιA.f m).hom y = x) ↔ IsLocallyConstant x) →
        (∀ (m : ℕ) (x : (Fin m → G) → B.V), (∃ y, (ιB.f m).hom y = x) ↔ IsLocallyConstant x) →
        (∀ (m : ℕ) (x : (Fin m → G) → C.V), (∃ y, (ιC.f m).hom y = x) ↔ IsLocallyConstant x) →
        ∃ (φ : KA ⟶ KB) (ψ : KB ⟶ KC) (w : CategoryTheory.CategoryStruct.comp φ ψ = 0),
          (CategoryTheory.ShortComplex.mk φ ψ w).ShortExact := by
  intro k G _ _ _ A B C f g KA KB KC ιA ιB ιC hf hfg hg iA iB iC hA hB hC
  obtain ⟨φ, hφ⟩ := exists_map f ιA ιB iB hA hB
  obtain ⟨ψ, hψ⟩ := exists_map g ιB ιC iC hB hC
  have w : CategoryTheory.CategoryStruct.comp φ ψ = 0 := by
    ext m : 1
    refine ModuleCat.hom_ext (LinearMap.ext fun x => iC m ?_)
    change (ιC.f m).hom ((ψ.f m).hom ((φ.f m).hom x)) = (ιC.f m).hom 0
    rw [map_zero]
    funext t
    rw [hψ, hφ]
    exact hfg.apply_apply_eq_zero _
  refine ⟨φ, ψ, w, HomologicalComplex.shortExact_of_degreewise_shortExact _ fun m => ?_⟩
  have hm : CategoryTheory.Mono (φ.f m) := by
    refine (ModuleCat.mono_iff_injective _).2 fun a b hab => iA m (funext fun t => hf ?_)
    have hab' : (φ.f m).hom a = (φ.f m).hom b := hab
    rw [← hφ, ← hφ, hab']
  have he : CategoryTheory.Epi (ψ.f m) := by
    refine (ModuleCat.epi_iff_surjective _).2 fun c => ?_
    obtain ⟨b, hb⟩ := (hB m _).2 (((hC m _).1 ⟨c, rfl⟩).comp (Function.surjInv hg))
    refine ⟨b, iC m (funext fun t => ?_)⟩
    refine (hψ m b t).trans ?_
    rw [hb]
    exact Function.surjInv_eq hg _
  refine { exact := ?_, mono_f := hm, epi_g := he }
  refine (CategoryTheory.ShortComplex.moduleCat_exact_iff _).2 fun (b : KB.X m) hb => ?_
  have hb0 : (ψ.f m).hom b = 0 := hb
  have hb' : ∀ t : Fin m → G, ∃ a, f.hom a = ((ιB.f m).hom b : (Fin m → G) → B.V) t := fun t => by
    refine (hfg _).1 ?_
    rw [← hψ, hb0, map_zero]
    rfl
  choose a ha using hb'
  have hla : IsLocallyConstant a := by
    refine IsLocallyConstant.desc a f.hom ?_ hf
    have e : f.hom ∘ a = (ιB.f m).hom b := funext ha
    rw [e]
    exact (hB m _).1 ⟨b, rfl⟩
  obtain ⟨y, hy⟩ := (hA m a).2 hla
  refine ⟨y, iB m (funext fun t => ?_)⟩
  refine (hφ m y t).trans ?_
  rw [hy]
  exact ha t
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CocycleCoboundaryFiniteIndex
section
theorem UpperTheory.Reformulated.B.CocycleCoboundaryFiniteIndex.coboundary_of_vanishing_on_finite_index :
    ∀ {R Q M : Type} [inst : CommRing R] [inst_1 : Group Q]
    [inst_2 : AddCommGroup M] [inst_3 : _root_.Module R M] (π : Representation R Q M) (H : Subgroup Q) (f : Q → M),
    (∀ (g h : Q), f (g * h) = f g + ((π : Q → M →ₗ[R] M) g : M → M) (f h)) →
      (∀ u ∈ H, f u = (0 : M)) →
        IsUnit (↑H.index : R) →
          H.index ≠ (0 : ℕ) → ∃ (m : M), ∀ (g : Q), f g = ((π : Q → M →ₗ[R] M) g : M → M) m - m := by
  intro R Q M _ _ _ _ π H f hf hH hu hn
  classical
  haveI : Fintype (Q ⧸ H) := Subgroup.fintypeOfIndexNeZero hn
  have hconst : ∀ a b : Q, (a : Q ⧸ H) = (b : Q ⧸ H) → f a = f b := by
    intro a b hab
    have hmem : a⁻¹ * b ∈ H := QuotientGroup.eq.mp hab
    have h1 := hf a (a⁻¹ * b)
    rw [mul_inv_cancel_left, hH _ hmem, map_zero, add_zero] at h1
    exact h1.symm
  let F : Q ⧸ H → M := fun x => f x.out
  have hF : ∀ a : Q, F (a : Q ⧸ H) = f a := fun a =>
    hconst _ _ (QuotientGroup.out_eq' _)
  have hstep : ∀ (g : Q) (x : Q ⧸ H), F (g • x) = f g + π g (F x) := by
    intro g x
    induction x using QuotientGroup.induction_on with
    | H a =>
      have h2 : g • (a : Q ⧸ H) = ((g * a : Q) : Q ⧸ H) := rfl
      rw [h2, hF, hF, hf]
  have hcard : Fintype.card (Q ⧸ H) = H.index := by
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  have hsum : ∀ g : Q, ∑ x, F x = (H.index : R) • f g + π g (∑ x, F x) := by
    intro g
    calc ∑ x, F x = ∑ x, F (g • x) := (Equiv.sum_comp (MulAction.toPerm g) F).symm
      _ = ∑ x : Q ⧸ H, (f g + π g (F x)) := Finset.sum_congr rfl fun x _ => hstep g x
      _ = _ := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcard, map_sum,
          Nat.cast_smul_eq_nsmul]
  obtain ⟨c, hc⟩ := hu.exists_left_inv
  refine ⟨-(c • ∑ x, F x), fun g => ?_⟩
  have h3 : (H.index : R) • f g = ∑ x, F x - π g (∑ x, F x) := eq_sub_of_add_eq (hsum g).symm
  calc f g = c • ((H.index : R) • f g) := by rw [smul_smul, hc, one_smul]
    _ = _ := by
      rw [h3, map_neg, map_smul, smul_sub]
      abel
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CocycleMultiplicative
section
noncomputable def UpperTheory.Reformulated.B.CocycleMultiplicative.cT :
    {A : Type} → [inst : CommRing A] → (A →+* A) → {m p : Type} → Matrix m p A → Matrix p m A :=
    fun {A : Type} [CommRing A] (σ : A →+* A) {m p : Type} (M : Matrix m p A) ↦ (M.map (⇑σ : A → A)).transpose

private theorem UpperTheory.Reformulated.B.CocycleMultiplicative.cT_mul {A : Type} [CommRing A] (σ : A →+* A) {n : Type} [Fintype n]
    (P Q : Matrix n n A) :
    UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (P * Q) = UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ Q * UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ P := by
  unfold UpperTheory.Reformulated.B.CocycleMultiplicative.cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

private theorem UpperTheory.Reformulated.B.CocycleMultiplicative.cT_one {A : Type} [CommRing A] (σ : A →+* A) {n : Type} [Fintype n]
    [DecidableEq n] : UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (1 : Matrix n n A) = 1 := by
  unfold UpperTheory.Reformulated.B.CocycleMultiplicative.cT
  rw [Matrix.map_one _ (map_zero σ) (map_one σ), Matrix.transpose_one]

theorem UpperTheory.Reformulated.B.CocycleMultiplicative.aux2 :
    ∀ {A : Type} [inst : CommRing A] {n : Type} [inst_1 : Fintype n] [inst_2 : DecidableEq n] (σ : A →+* A)
      (J : Matrix n n A) {a b : GL n A},
      a ∈ {g : GL n A | UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A) * J * (↑g : Matrix n n A) = J} →
        b ∈ {g : GL n A | UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A) * J * (↑g : Matrix n n A) = J} →
          a * b ∈ {g : GL n A | UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A) * J * (↑g : Matrix n n A) = J} := by
  intro A _ n _ _ σ J a b ha hb
  simp only [Set.mem_setOf_eq] at ha hb ⊢
  rw [Units.val_mul, UpperTheory.Reformulated.B.CocycleMultiplicative.cT_mul]
  calc _ = UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑b : Matrix n n A) *
        (UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑a : Matrix n n A) * J * (↑a : Matrix n n A)) * (↑b : Matrix n n A) := by
        simp only [Matrix.mul_assoc]
    _ = J := by rw [ha, hb]

theorem UpperTheory.Reformulated.B.CocycleMultiplicative.aux3 :
    ∀ {A : Type} [inst : CommRing A] {n : Type} [inst_1 : Fintype n] [inst_2 : DecidableEq n] (σ : A →+* A)
      (J : Matrix n n A), UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑(1 : GL n A) : Matrix n n A) * J * (↑(1 : GL n A) : Matrix n n A) = J := by
  intro A _ n _ _ σ J
  rw [Units.val_one, UpperTheory.Reformulated.B.CocycleMultiplicative.cT_one, Matrix.one_mul, Matrix.mul_one]

theorem UpperTheory.Reformulated.B.CocycleMultiplicative.aux4 :
    ∀ {A : Type} [inst : CommRing A] {n : Type} [inst_1 : Fintype n] [inst_2 : DecidableEq n] (σ : A →+* A)
      (J : Matrix n n A) {g : GL n A},
      g ∈ {g : GL n A | UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A) * J * (↑g : Matrix n n A) = J} →
        g⁻¹ ∈ {g : GL n A | UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A) * J * (↑g : Matrix n n A) = J} := by
  intro A _ n _ _ σ J g hg
  simp only [Set.mem_setOf_eq] at hg ⊢
  have h1 : (↑g : Matrix n n A) * (↑(g⁻¹) : Matrix n n A) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑(g⁻¹) : Matrix n n A) * UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A) = 1 := by
    rw [← UpperTheory.Reformulated.B.CocycleMultiplicative.cT_mul, h1, UpperTheory.Reformulated.B.CocycleMultiplicative.cT_one]
  calc _ = UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑(g⁻¹) : Matrix n n A) *
        (UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A) * J * (↑g : Matrix n n A)) * (↑(g⁻¹) : Matrix n n A) := by
        rw [hg]
    _ = (UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑(g⁻¹) : Matrix n n A) * UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A)) * J *
        ((↑g : Matrix n n A) * (↑(g⁻¹) : Matrix n n A)) := by
        simp only [Matrix.mul_assoc]
    _ = J := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

noncomputable def UpperTheory.Reformulated.B.CocycleMultiplicative.UJ :
    {A : Type} →
      [inst : CommRing A] →
        {n : Type} → [inst_1 : Fintype n] → [inst_2 : DecidableEq n] → (A →+* A) → Matrix n n A → Subgroup (GL n A) :=
    fun {A : Type} [inst : CommRing A] {n : Type} [inst_1 : Fintype n] [inst_2 : DecidableEq n] (σ : A →+* A)
        (J : Matrix n n A) ↦
      { carrier := {g : GL n A | UpperTheory.Reformulated.B.CocycleMultiplicative.cT σ (↑g : Matrix n n A) * J * (↑g : Matrix n n A) = J},
        mul_mem' := @UpperTheory.Reformulated.B.CocycleMultiplicative.aux2 A inst n inst_1 inst_2 σ J, one_mem' := UpperTheory.Reformulated.B.CocycleMultiplicative.aux3 σ J,
        inv_mem' := @UpperTheory.Reformulated.B.CocycleMultiplicative.aux4 A inst n inst_1 inst_2 σ J : Subgroup (GL n A) }

noncomputable def UpperTheory.Reformulated.B.CocycleMultiplicative.UE :
    (E : Type) → [inst : Field E] → [inst_1 : NumberField E] → [NumberField.IsCMField E] → (n : ℕ) → Subgroup (GL (Fin n) E) :=
    fun (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (n : ℕ) ↦
      UpperTheory.Reformulated.B.CocycleMultiplicative.UJ (NumberField.IsCMField.complexConj E).toRingEquiv.toRingHom (1 : Matrix (Fin n) (Fin n) E)

open scoped Matrix.Norms.L2Operator in
private theorem UpperTheory.Reformulated.B.CocycleMultiplicative.norm_of_mem_spectrum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (h : star A * A = 1) {z : ℂ} (hz : z ∈ spectrum ℂ A) : ‖z‖ = (1 : ℝ) := by
  have hu : A ∈ unitary (Matrix (Fin n) (Fin n) ℂ) :=
    ⟨h, mul_eq_one_comm.mp h⟩
  rcases subsingleton_or_nontrivial (Matrix (Fin n) (Fin n) ℂ) with hs | hn
  · exact absurd hz (by simp [spectrum.of_subsingleton])
  · simpa using spectrum.subset_circle_of_unitary hu hz

theorem UpperTheory.Reformulated.B.CocycleMultiplicative.norm_eq_one_of_root :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E] {n : ℕ}
      (γ : ↥(UpperTheory.Reformulated.B.CocycleMultiplicative.UE E n)) (τ : E →+* ℂ),
      ∀ z ∈ (Polynomial.map τ (↑(↑γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E).charpoly).roots, ‖z‖ = (1 : ℝ) := by
  intro E _ _ _ n γ τ z hz
  have hγ := γ.2
  obtain ⟨g, hg⟩ := γ
  simp only at hz
  have hg' : UpperTheory.Reformulated.B.CocycleMultiplicative.cT (NumberField.IsCMField.complexConj E).toRingEquiv.toRingHom
      (↑g : Matrix (Fin n) (Fin n) E) * 1 * (↑g : Matrix (Fin n) (Fin n) E) = 1 := hg
  rw [Matrix.mul_one] at hg'
  have hroot : ((↑g : Matrix (Fin n) (Fin n) E).map τ).charpoly.IsRoot z := by
    rw [Matrix.charpoly_map]
    exact (Polynomial.mem_roots'.mp hz).2
  have hstar : star ((↑g : Matrix (Fin n) (Fin n) E).map τ) =
      (UpperTheory.Reformulated.B.CocycleMultiplicative.cT (NumberField.IsCMField.complexConj E).toRingEquiv.toRingHom
        (↑g : Matrix (Fin n) (Fin n) E)).map τ := by
    ext i j
    simp [UpperTheory.Reformulated.B.CocycleMultiplicative.cT, Matrix.star_apply]
  have hU : star ((↑g : Matrix (Fin n) (Fin n) E).map τ) * (↑g : Matrix (Fin n) (Fin n) E).map τ = 1 := by
    rw [hstar, ← Matrix.map_mul, hg', Matrix.map_one _ (map_zero τ) (map_one τ)]
  exact UpperTheory.Reformulated.B.CocycleMultiplicative.norm_of_mem_spectrum _ hU (Matrix.mem_spectrum_of_isRoot_charpoly hroot)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CommonDenom
section
noncomputable def UpperTheory.Reformulated.B.Qn19.AIC :
    (A : Type) → [CommRing A] → Prop :=
    fun (A : Type) [CommRing A] ↦
      ∀ (p : Polynomial A), p.Monic → (0 : ℕ) < p.natDegree → ∃ (a : A), Polynomial.eval a p = (0 : A)

private theorem UpperTheory.Reformulated.B.Qn19.commonDenom {R L : Type} [CommRing R] [CommRing L] (φ : R →+* L)
    (h : ∀ z : L, ∃ a b : R, IsUnit (φ b) ∧ z * φ b = φ a) (s : Finset L) :
    ∃ b : R, IsUnit (φ b) ∧ ∀ z ∈ s, ∃ a : R, φ a = z * φ b := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert x s _ ih =>
    obtain ⟨b, hb, hs⟩ := ih
    obtain ⟨a, c, hc, hx⟩ := h x
    refine ⟨b * c, by rw [map_mul]; exact hb.mul hc, ?_⟩
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact ⟨a * b, by rw [map_mul, map_mul, ← hx]; ring⟩
    · obtain ⟨d, hd⟩ := hs z hz
      exact ⟨d * c, by rw [map_mul, map_mul, hd]; ring⟩

theorem UpperTheory.Reformulated.B.Qn19.aicFrac :
    ∀ (R L : Type) [inst : CommRing R] [inst_1 : CommRing L] (φ : R →+* L),
      UpperTheory.Reformulated.B.Qn19.AIC R →
        (∀ (z : L), ∃ (a : R) (b : R), IsUnit ((φ : R → L) b) ∧ z * (φ : R → L) b = (φ : R → L) a) → UpperTheory.Reformulated.B.Qn19.AIC L := by
  intro R L _ _ φ hR h p hp hdeg
  obtain ⟨b, hb, hs⟩ := UpperTheory.Reformulated.B.Qn19.commonDenom φ h p.coeffs
  have hmon : (p.scaleRoots (φ b)).Monic := (Polynomial.monic_scaleRoots_iff _).2 hp
  have hlift : p.scaleRoots (φ b) ∈ Polynomial.lifts φ := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [Polynomial.coeff_scaleRoots]
    rcases lt_trichotomy i p.natDegree with hi | hi | hi
    · by_cases h0 : p.coeff i = 0
      · exact ⟨0, by simp [h0]⟩
      · obtain ⟨a, ha⟩ := hs _ (Polynomial.coeff_mem_coeffs h0)
        obtain ⟨k, hk⟩ : ∃ k, p.natDegree - i = k + 1 := ⟨p.natDegree - i - 1, by omega⟩
        exact ⟨a * b ^ k, by rw [map_mul, map_pow, ha, hk]; ring⟩
    · subst hi
      exact ⟨1, by simp [hp.coeff_natDegree]⟩
    · exact ⟨0, by simp [Polynomial.coeff_eq_zero_of_natDegree_lt hi]⟩
  obtain ⟨q, hq, hqd, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hmon
  rw [Polynomial.natDegree_scaleRoots] at hqd
  obtain ⟨a, ha⟩ := hR q hqm (by rw [hqd]; exact hdeg)
  obtain ⟨u, hu⟩ := hb
  refine ⟨(↑u⁻¹ : L) * φ a, ?_⟩
  have h1 : Polynomial.eval (φ a) (p.scaleRoots (φ b)) = 0 := by
    rw [← hq, Polynomial.eval_map, Polynomial.eval₂_hom, ha, map_zero]
  have h2 := Polynomial.scaleRoots_eval_mul p ((↑u⁻¹ : L) * φ a) (φ b)
  have h3 : φ b * ((↑u⁻¹ : L) * φ a) = φ a := by
    rw [← hu, ← mul_assoc, Units.mul_inv, one_mul]
  rw [h3, h1, ← hu] at h2
  exact ((u.isUnit.pow p.natDegree).mul_right_eq_zero).1 h2.symm
end

