module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.IrreducibleParity.Fv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.OrbitalFiberSumOverFibers
section
open MulAction

private theorem conj_memS {G : Type} [Group G] {S : Subgroup G} (hc : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ S)
    {s : G} (hs : s ∈ S) (a : G) : a * s * a⁻¹ ∈ S := by
  have h : a * s * a⁻¹ = (a * s * a⁻¹ * s⁻¹) * s := by group
  rw [h]
  exact S.mul_mem (hc a s) hs

private theorem mem_orb {G : Type} [Group G] (S U : Subgroup G) (x : G) (y : G ⧸ U) :
    y ∈ orbit S (x : G ⧸ U) ↔ ∃ s ∈ S, y = ((s * x : G) : G ⧸ U) := by
  constructor
  · rintro ⟨⟨s, hs⟩, rfl⟩
    exact ⟨s, hs, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, hs⟩, rfl⟩

private theorem sup_act {G : Type} [Group G] {S U : Subgroup G} (hc : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ S)
    {g : G} (hg : g ∈ S ⊔ U) (x : G) {y : G ⧸ U} (hy : y ∈ orbit S (x : G ⧸ U)) :
    g • y ∈ orbit S (x : G ⧸ U) := by
  haveI : S.Normal := ⟨fun n hn a => conj_memS hc hn a⟩
  rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at hg
  obtain ⟨s, hs, u, hu, rfl⟩ := hg
  obtain ⟨s₀, hs₀, rfl⟩ := (mem_orb S U x y).1 hy
  refine (mem_orb S U x _).2 ⟨s * (u * s₀ * x * u⁻¹ * x⁻¹), S.mul_mem hs ?_, ?_⟩
  · convert S.mul_mem (conj_memS hc hs₀ u) (hc u x) using 1
    group
  · rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, smul_eq_mul]
    convert U.inv_mem hu using 1
    group

private theorem phi_out {G : Type} [Group G] (U : Subgroup G) (Φ : G → ℂ) (hΦu : ∀ u ∈ U, ∀ g, Φ (g * u) = Φ g) (g : G) :
    Φ ((g : G ⧸ U).out) = Φ g := by
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U g
  rw [hu, hΦu _ u.2]

theorem UpperTheory.orbitalFiber_sum_over_fibers :
    UpperTheory.V.Z.Sym.Glob.Fib.SumFib := by
  intro Γ G I _ _ _ ι S U' Γ₀ x Φ hc hN hΦl hΦu hT hdisj hcov
  classical
  let Γ' : Subgroup Γ := Subgroup.comap ι (S ⊔ U')
  letI A : MulAction Γ (G ⧸ U') := MulAction.compHom _ ι
  letI B : MulAction Γ' (G ⧸ U') := MulAction.compHom _ (ι.comp Γ'.subtype)
  let k : G ⧸ U' → ℂ := fun y => Φ y.out
  let ki : I → G ⧸ U' → ℂ := fun i => (orbit S (x i : G ⧸ U')).indicator k
  have hsmul : ∀ (h : Γ) (g : G), h • (g : G ⧸ U') = ((ι h * g : G) : G ⧸ U') := fun h g => rfl
  have hk : ∀ g : G, k g = Φ g := phi_out U' Φ hΦu
  have hkinv : ∀ (h : Γ) (y : G ⧸ U'), k (h • y) = k y := by
    intro h y
    refine QuotientGroup.induction_on y fun g => ?_
    rw [hsmul, hk, hk, hΦl]
  have hki_mem : ∀ i y, ki i y ≠ 0 → y ∈ orbit S (x i : G ⧸ U') :=
    fun i y h => Set.mem_of_indicator_ne_zero h
  have hD := @UpperTheory.orbitalFiber_decomposition Γ (G ⧸ U') I _ A Γ₀ k (fun _ => Γ') (fun _ => G ⧸ U')
    (fun _ => inferInstance) (fun _ => B) (fun _ => Γ'.subtype) (fun _ => id) ki hN hkinv
    ?_ (fun _ _ _ => rfl) (fun _ => Function.injective_id) ?_ ?_ ?_ ?_
  · show UpperTheory.V.Z.Sym.gq Γ₀ k = ∑ i, UpperTheory.V.Z.Sym.gq (Γ₀.subgroupOf Γ') (ki i)
    rw [hD, finsum_eq_sum_of_fintype]
    rfl
  · obtain ⟨T, hT⟩ := hT
    refine ⟨T.image (fun g : G => (g : G ⧸ U')), fun y => ?_⟩
    refine QuotientGroup.induction_on y fun g _ => ?_
    obtain ⟨γ, s, hs, u, hu, rfl⟩ := hT g
    refine ⟨γ, (s : G ⧸ U'), Finset.mem_image_of_mem _ hs, ?_⟩
    rw [hsmul, QuotientGroup.eq]
    convert U'.inv_mem hu using 1
    group
  · intro i h y
    have hh : ι h ∈ S ⊔ U' := h.2
    have e : h • y = (ι h) • y := rfl
    have hmem : h • y ∈ orbit S (x i : G ⧸ U') ↔ y ∈ orbit S (x i : G ⧸ U') := by
      rw [e]
      constructor
      · intro hy'
        simpa using sup_act hc (Subgroup.inv_mem _ hh) (x i) hy'
      · intro hy
        exact sup_act hc hh (x i) hy
    show Set.indicator _ k (h • y) = Set.indicator _ k y
    by_cases hy : y ∈ orbit S (x i : G ⧸ U')
    · rw [Set.indicator_apply, Set.indicator_apply, if_pos (hmem.2 hy), if_pos hy]
      exact hkinv (h : Γ) y
    · rw [Set.indicator_apply, Set.indicator_apply, if_neg (mt hmem.1 hy), if_neg hy]
  · intro i y h
    exact (Set.indicator_of_mem (hki_mem i y h) k).symm
  · intro z
    refine QuotientGroup.induction_on z fun g hz => ?_
    obtain ⟨i, γ, s, hs, u, hu, rfl⟩ := hcov g
    have hy : ((s * x i : G) : G ⧸ U') ∈ orbit S (x i : G ⧸ U') := (mem_orb S U' _ _).2 ⟨s, hs, rfl⟩
    have hval : k ((s * x i : G) : G ⧸ U') = k ((ι γ * s * x i * u : G) : G ⧸ U') := by
      rw [hk, hk, hΦu _ hu, mul_assoc (ι γ) s, hΦl]
    refine ⟨i, ((s * x i : G) : G ⧸ U'), γ, ?_, ?_⟩
    · rw [show ki i _ = k _ from Set.indicator_of_mem hy k, hval]
      exact hz
    · show _ = γ • ((s * x i : G) : G ⧸ U')
      rw [hsmul, QuotientGroup.eq]
      convert U'.inv_mem hu using 1
      group
  · intro i j y y' h hy hy' he
    obtain ⟨s, hs, rfl⟩ := (mem_orb S U' _ _).1 (hki_mem i y hy)
    obtain ⟨s', hs', rfl⟩ := (mem_orb S U' _ _).1 (hki_mem j y' hy')
    change ((ι h * (s * x i) : G) : G ⧸ U') = ((s' * x j : G) : G ⧸ U') at he
    rw [QuotientGroup.eq] at he
    obtain ⟨u, hu_mem, hu_eq⟩ : ∃ u ∈ U', (ι h * (s * x i))⁻¹ * (s' * x j) = u := ⟨_, he, rfl⟩
    have hxj : x j = ι h * ((ι h)⁻¹ * s'⁻¹ * ι h * s) * x i * u := by
      rw [← hu_eq]
      group
    have e2 : ι h = s' * x j * u⁻¹ * (x i)⁻¹ * s⁻¹ := by
      rw [← hu_eq]
      group
    have hmid : (ι h)⁻¹ * s'⁻¹ * ι h * s ∈ S :=
      S.mul_mem (by simpa using conj_memS hc (S.inv_mem hs') (ι h)⁻¹) hs
    have key : ∀ X : G, s' * X * u⁻¹ * X⁻¹ * s⁻¹ ∈ S ⊔ U' := by
      intro X
      have e3 : s' * X * u⁻¹ * X⁻¹ * s⁻¹ = s' * (X * u⁻¹ * X⁻¹ * u⁻¹⁻¹) * u⁻¹ * s⁻¹ := by group
      rw [e3]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hs')
        (Subgroup.mem_sup_left (hc _ _))) (Subgroup.mem_sup_right (U'.inv_mem hu_mem)))
        (Subgroup.mem_sup_left (S.inv_mem hs))
    have hij := hdisj i j h _ hmid u hu_mem hxj
    subst hij
    refine ⟨rfl, ⟨h, ?_⟩, rfl⟩
    show ι h ∈ S ⊔ U'
    rw [e2]
    exact key _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.QuadraticTorusFixedVerticesFinite
section
open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PS

private theorem rescale {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] {p : O} (hp : Irreducible p) {x : K} (hx : x ≠ 0) :
    ∃ s : K, s ≠ 0 ∧ ∃ a b : O, algebraMap O K a = s ^ 2 * x ∧ a * b = p ^ 2 := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective O x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at hx
  have hp0 : p ≠ 0 := hp.ne_zero
  have hinj := IsFractionRing.injective O K
  have hP : algebraMap O K p ≠ 0 := (map_ne_zero_iff _ hinj).mpr hp0
  have hB : algebraMap O K b ≠ 0 := (map_ne_zero_iff _ hinj).mpr hb0
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hp
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hp
  set t := (m + n) / 2 with ht
  set r := (m + n) % 2 with hr
  have hN : r + t + t = m + n := by omega
  have hr2 : r ≤ 2 := by omega
  have hO : (↑(u * v) * p ^ r) * (p ^ t * p ^ t) = (↑u * p ^ m) * (↑v * p ^ n) := by
    calc (↑(u * v) * p ^ r) * (p ^ t * p ^ t) = ↑u * ↑v * p ^ (r + t + t) := by
            rw [Units.val_mul]; ring
      _ = (↑u * p ^ m) * (↑v * p ^ n) := by rw [hN]; ring
  have key : algebraMap O K (↑(u * v) * p ^ r) * (algebraMap O K p ^ t * algebraMap O K p ^ t)
      = algebraMap O K (↑u * p ^ m) * algebraMap O K (↑v * p ^ n) := by
    rw [← map_pow, ← map_mul, ← map_mul, ← map_mul, hO]
  refine ⟨algebraMap O K (↑v * p ^ n) / algebraMap O K p ^ t, div_ne_zero hB (pow_ne_zero _ hP),
    ↑(u * v) * p ^ r, ↑(u * v)⁻¹ * p ^ (2 - r), ?_, ?_⟩
  · have hT : algebraMap O K p ^ t * algebraMap O K p ^ t ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ hP) (pow_ne_zero _ hP)
    have e : algebraMap O K (↑(u * v) * p ^ r) = algebraMap O K (↑u * p ^ m) * algebraMap O K (↑v * p ^ n)
        / (algebraMap O K p ^ t * algebraMap O K p ^ t) := by
      rw [eq_div_iff hT, key]
    rw [e]
    field_simp
  · calc ↑(u * v) * p ^ r * (↑(u * v)⁻¹ * p ^ (2 - r))
        = (↑(u * v) * ↑(u * v)⁻¹) * p ^ (r + (2 - r)) := by rw [pow_add]; ring
      _ = p ^ 2 := by rw [Units.mul_inv, one_mul, Nat.add_sub_cancel' hr2]

private theorem rescaleE {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
    [IsFractionRing O K] {τ : K} {p : O} (hp : Irreducible p) {c : (Etau K τ)ˣ} (hc : c ∈ Cint O τ) :
    ∃ s : K, s ≠ 0 ∧ IsIntegral O (s • (c : Etau K τ)) ∧
      IsIntegral O ((algebraMap O K p * s⁻¹) • ((c⁻¹ : (Etau K τ)ˣ) : Etau K τ)) := by
  obtain ⟨hc1, hc2⟩ := hc
  have sq : ∀ u : (Etau K τ)ˣ, (u : Etau K τ) * u =
      algebraMap K (Etau K τ) (QuadraticAlgebra.norm (u : Etau K τ)) * quo u := by
    intro u
    rw [QuadraticAlgebra.algebraMap_norm_eq_mul_star]
    have h1 : star (u : Etau K τ) * star ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ) = 1 := by
      rw [← star_mul, Units.inv_mul, star_one]
    unfold quo
    calc (u : Etau K τ) * u = u * u * (star (u : Etau K τ) * star ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ)) := by
          rw [h1, mul_one]
      _ = u * star (u : Etau K τ) * (u * star ((u⁻¹ : (Etau K τ)ˣ) : Etau K τ)) := by ring
  obtain ⟨N, hNd⟩ : ∃ N, N = QuadraticAlgebra.norm (c : Etau K τ) := ⟨_, rfl⟩
  obtain ⟨N', hNd'⟩ : ∃ N', N' = QuadraticAlgebra.norm ((c⁻¹ : (Etau K τ)ˣ) : Etau K τ) := ⟨_, rfl⟩
  have hNN : N * N' = 1 := by
    rw [hNd, hNd', ← map_mul, Units.mul_inv, map_one]
  have hN : N ≠ 0 := left_ne_zero_of_mul_eq_one hNN
  have sqc := sq c
  have sqd := sq c⁻¹
  rw [← hNd] at sqc
  rw [← hNd'] at sqd
  obtain ⟨s, hs, a, b, ha, hab⟩ := rescale hp hN
  have hab' : algebraMap O K a * algebraMap O K b = algebraMap O K p ^ 2 := by
    rw [← map_mul, hab, map_pow]
  refine ⟨s, hs, ?_, ?_⟩
  · apply IsIntegral.of_pow (n := 2) two_pos
    have e : (s • (c : Etau K τ)) ^ 2 = algebraMap O (Etau K τ) a * quo c := by
      calc (s • (c : Etau K τ)) ^ 2 = algebraMap K (Etau K τ) s ^ 2 * ((c : Etau K τ) * c) := by
            rw [Algebra.smul_def]; ring
        _ = algebraMap K (Etau K τ) s ^ 2 * (algebraMap K (Etau K τ) N * quo c) := by rw [sqc]
        _ = algebraMap O (Etau K τ) a * quo c := by
            rw [algebraMap_etau a, ha, map_mul, map_pow]; ring
    rw [e]
    exact (isIntegral_algebraMap).mul hc1
  · apply IsIntegral.of_pow (n := 2) two_pos
    have hk : (algebraMap O K p * s⁻¹) ^ 2 * N' = algebraMap O K b := by
      field_simp
      linear_combination (-N') * hab' + (algebraMap O K b * N') * ha + (algebraMap O K b * s ^ 2) * hNN
    have e : ((algebraMap O K p * s⁻¹) • ((c⁻¹ : (Etau K τ)ˣ) : Etau K τ)) ^ 2
        = algebraMap O (Etau K τ) b * quo c⁻¹ := by
      calc ((algebraMap O K p * s⁻¹) • ((c⁻¹ : (Etau K τ)ˣ) : Etau K τ)) ^ 2
          = algebraMap K (Etau K τ) (algebraMap O K p * s⁻¹) ^ 2
            * (((c⁻¹ : (Etau K τ)ˣ) : Etau K τ) * ((c⁻¹ : (Etau K τ)ˣ) : Etau K τ)) := by
            rw [Algebra.smul_def]; ring
        _ = algebraMap K (Etau K τ) (algebraMap O K p * s⁻¹) ^ 2
            * (algebraMap K (Etau K τ) N' * quo c⁻¹) := by rw [sqd]
        _ = algebraMap O (Etau K τ) b * quo c⁻¹ := by
            rw [algebraMap_etau b, ← hk]
            simp only [map_mul, map_pow]
            ring
    rw [e]
    exact (isIntegral_algebraMap).mul hc2

private theorem cls_smul {K : Type} [Field K] {τ : K} (S : Set (Etau K τ)) {s : K} (hs : s ≠ 0) :
    cls τ ((s • ·) '' S) = cls τ S := by
  ext T
  simp only [cls, Set.mem_setOf_eq, Set.image_image, smul_smul]
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u * Units.mk0 s hs, by congr 1⟩
  · rintro ⟨u, rfl⟩
    refine ⟨u * (Units.mk0 s hs)⁻¹, ?_⟩
    congr 1
    funext y
    simp [hs]

private theorem exists_finite_representatives_mod_smul_of_fg {O M : Type} [CommRing O] [AddCommGroup M] [Module O M] {m : O}
    (hq : Finite (O ⧸ Ideal.span {m})) (R : Submodule O M) (hR : R.FG) :
    ∃ F : Set M, F.Finite ∧ ∀ x ∈ R, ∃ y ∈ F, ∃ z ∈ R, x - y = m • z := by
  haveI := hq
  obtain ⟨g, rfl⟩ := hR
  have hsurj := Ideal.Quotient.mk_surjective (I := Ideal.span {m})
  refine ⟨Set.range (fun r : (↥g → O ⧸ Ideal.span {m}) =>
    ∑ i : ↥g, Function.surjInv hsurj (r i) • (i : M)), Set.finite_range _, ?_⟩
  intro x hx
  obtain ⟨f, -, rfl⟩ := (Submodule.mem_span_finset).mp hx
  have hk : ∀ i : ↥g, ∃ k : O, k * m = f i - Function.surjInv hsurj (Ideal.Quotient.mk _ (f i)) := by
    intro i
    apply Ideal.mem_span_singleton'.mp
    apply Ideal.Quotient.eq.mp
    rw [Function.surjInv_eq hsurj]
  choose k hk using hk
  refine ⟨_, ⟨fun i => Ideal.Quotient.mk _ (f i), rfl⟩, ∑ i : ↥g, k i • (i : M), ?_, ?_⟩
  · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span i.2)
  · rw [← Finset.sum_coe_sort g, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sub_smul, ← hk i, smul_smul, mul_comm]

theorem UpperTheory.quadraticTorus_fixedVertices_finite :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → (Fv O τ).Finite := by
  intro O K _ _ _ _ _ Δ τ hL hτ
  haveI := hL.frac
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨c0, hc0, hden⟩ := int_denom hL hτ
  have hm : c0 * p ≠ 0 := mul_ne_zero hc0 hp.ne_zero
  obtain ⟨F, hF, hFR⟩ := exists_finite_representatives_mod_smul_of_fg (finite_quot_span hL hm)
    (Subalgebra.toSubmodule (integralClosure O (Etau K τ))) (intE_fg hL hτ)
  have hmemR : ∀ z, z ∈ Subalgebra.toSubmodule (integralClosure O (Etau K τ)) ↔ IsIntegral O z := by
    intro z
    rw [Subalgebra.mem_toSubmodule, mem_integralClosure_iff]
  let 𝒯 : Set (Set (Etau K τ)) := {T | ∃ M : Submodule O (Etau K τ), T = M ∧
    (∀ z ∈ Subalgebra.toSubmodule (integralClosure O (Etau K τ)), (c0 * p) • z ∈ M) ∧
    M ≤ Subalgebra.toSubmodule (integralClosure O (Etau K τ))}
  have h𝒯 : 𝒯.Finite := by
    apply Set.Finite.of_finite_image (f := fun T => T ∩ F)
    · exact (hF.powerset).subset (by rintro _ ⟨T, -, rfl⟩; exact Set.inter_subset_right)
    · have key : ∀ M M' : Submodule O (Etau K τ),
          (∀ z ∈ Subalgebra.toSubmodule (integralClosure O (Etau K τ)), (c0 * p) • z ∈ M) →
          M ≤ Subalgebra.toSubmodule (integralClosure O (Etau K τ)) →
          (∀ z ∈ Subalgebra.toSubmodule (integralClosure O (Etau K τ)), (c0 * p) • z ∈ M') →
          (M : Set (Etau K τ)) ∩ F = (M' : Set (Etau K τ)) ∩ F → (M : Set (Etau K τ)) ⊆ M' := by
        intro M M' hm1 hR1 hm2 he x hx
        obtain ⟨y, hyF, z, hz, hxy⟩ := hFR x (hR1 hx)
        have hy : y ∈ M := by
          have e : y = x - (c0 * p) • z := by rw [← hxy]; abel
          rw [e]
          exact M.sub_mem hx (hm1 z hz)
        have hy2 : y ∈ (M' : Set (Etau K τ)) ∩ F := by
          rw [← he]
          exact ⟨hy, hyF⟩
        have e : x = y + (c0 * p) • z := by rw [← hxy]; abel
        rw [e]
        exact M'.add_mem hy2.1 (hm2 z hz)
      rintro _ ⟨M1, rfl, h1m, h1R⟩ _ ⟨M2, rfl, h2m, h2R⟩ heq
      have heq' : (M1 : Set (Etau K τ)) ∩ F = (M2 : Set (Etau K τ)) ∩ F := heq
      exact Set.Subset.antisymm (key _ _ h1m h1R h2m heq') (key _ _ h2m h2R h1m heq'.symm)
  apply (h𝒯.image (fun T => cls τ T)).subset
  rintro X ⟨S, hS, hω, ⟨c, hc, hgen⟩, rfl⟩
  obtain ⟨s, hs, hsc, hsd⟩ := rescaleE hp hc
  refine ⟨(s • ·) '' S, ?_, cls_smul S hs⟩
  obtain ⟨g, hg⟩ := hS.fg
  have hcomm : ∀ (o : O) (x : Etau K τ), o • (s • x) = s • (o • x) := by
    intro o x
    simp only [Algebra.smul_def]
    ring
  let M : Submodule O (Etau K τ) :=
    { carrier := (s • ·) '' S
      add_mem' := by
        rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩
        refine ⟨u + v, ?_, smul_add s u v⟩
        rw [hg] at hu hv ⊢
        exact Submodule.add_mem _ hu hv
      zero_mem' := ⟨0, by rw [hg]; exact Submodule.zero_mem _, smul_zero s⟩
      smul_mem' := by
        rintro o _ ⟨u, hu, rfl⟩
        refine ⟨o • u, ?_, (hcomm o u).symm⟩
        rw [hg] at hu ⊢
        exact Submodule.smul_mem _ o hu }
  refine ⟨M, rfl, ?_, ?_⟩
  · intro z hz
    have hzi : IsIntegral O z := (hmemR z).mp hz
    have e1 : algebraMap O (Etau K τ) p = (s • (c : Etau K τ)) *
        ((algebraMap O K p * s⁻¹) • ((c⁻¹ : (Etau K τ)ˣ) : Etau K τ)) := by
      rw [smul_mul_smul_comm, Units.mul_inv, algebraMap_etau p, Algebra.algebraMap_eq_smul_one]
      congr 1
      field_simp
    have hy : IsIntegral O (((algebraMap O K p * s⁻¹) • ((c⁻¹ : (Etau K τ)ˣ) : Etau K τ)) * z) :=
      hsd.mul hzi
    obtain ⟨a, b, h1, h2⟩ := hden _ hy
    have e2 : algebraMap O (Etau K τ) c0 *
        (((algebraMap O K p * s⁻¹) • ((c⁻¹ : (Etau K τ)ˣ) : Etau K τ)) * z)
        = algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * ω := by
      rw [algebraMap_etau c0, algebraMap_etau a, algebraMap_etau b]
      ext
      · have h1' := h1
        simp at h1' ⊢
        linear_combination h1'
      · have h2' := h2
        simp at h2' ⊢
        linear_combination h2'
    have e3 : (c0 * p) • z = a • (s • (c : Etau K τ)) + b • (s • (ω * (c : Etau K τ))) := by
      calc (c0 * p) • z = algebraMap O (Etau K τ) c0 * algebraMap O (Etau K τ) p * z := by
            rw [Algebra.smul_def, map_mul]
        _ = (s • (c : Etau K τ)) * (algebraMap O (Etau K τ) c0 *
              (((algebraMap O K p * s⁻¹) • ((c⁻¹ : (Etau K τ)ˣ) : Etau K τ)) * z)) := by
            rw [e1]; ring
        _ = (s • (c : Etau K τ)) * (algebraMap O (Etau K τ) a + algebraMap O (Etau K τ) b * ω) := by
            rw [e2]
        _ = a • (s • (c : Etau K τ)) + b • (s • (ω * (c : Etau K τ))) := by
            rw [Algebra.smul_def a, Algebra.smul_def b, ← mul_smul_comm]
            ring
    rw [e3]
    have m1 : s • (c : Etau K τ) ∈ M := ⟨_, hgen.1, rfl⟩
    have m2 : s • (ω * (c : Etau K τ)) ∈ M := ⟨_, hω _ hgen.1, rfl⟩
    exact M.add_mem (M.smul_mem a m1) (M.smul_mem b m2)
  · rintro _ ⟨w, hw, rfl⟩
    rw [hmemR]
    have e : s • w = (s • (c : Etau K τ)) * (((c⁻¹ : (Etau K τ)ˣ) : Etau K τ) * w) := by
      rw [smul_mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]
    show IsIntegral O (s • w)
    rw [e]
    exact hsc.mul (hgen.2 w hw)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SpanOrdinaryPartEqSupUnitGeneralizedEigenspaces
section
open IsLocalRing UpperTheory.V.Hi UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite

open TensorProduct in
private theorem UpperTheory.pi_scalar_right_tmul {O Ω ι : Type} [CommRing O] [Field Ω] [Algebra O Ω]
    [Fintype ι] [DecidableEq ι] (a : Ω) (v : ι → O) :
    TensorProduct.piScalarRight O Ω Ω ι (a ⊗ₜ v) = a • fun i => algebraMap O Ω (v i) := by
  ext i
  simp [Algebra.smul_def, mul_comm]

private theorem UpperTheory.map_max_gen_eigenspace_of_intertwine {K V W : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] (E : V ≃ₗ[K] W) (f : Module.End K V) (g : Module.End K W)
    (h : ∀ x, g (E x) = E (f x)) (μ : K) :
    (f.maxGenEigenspace μ).map E.toLinearMap = g.maxGenEigenspace μ := by
  have hp : ∀ (k : ℕ) x, ((g - μ • 1) ^ k) (E x) = E (((f - μ • 1) ^ k) x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ← ih]
      simp [h]
  ext y
  obtain ⟨x, rfl⟩ := E.surjective y
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, Module.End.mem_maxGenEigenspace,
    Module.End.mem_maxGenEigenspace]
  simp only [hp, EmbeddingLike.map_eq_zero_iff]

theorem UpperTheory.span_ordinaryPart_eq_sup_unit_generalized_eigenspaces :
    ∀ (O Ω ι : Type) [CommRing O] [IsCNL O] [Field Ω] [IsAlgClosed Ω] [Algebra O Ω] [Fintype ι] (T₀ : Module.End O (ι → O)) (T : Module.End Ω (ι → Ω)), (∀ v, T (fun i => algebraMap O Ω (v i)) = fun i => algebraMap O Ω (T₀ v i)) → ⨆ μ : {μ : Ω // IsIntUnit O μ}, T.maxGenEigenspace μ.1 = Submodule.span Ω ((fun (v : ι → O) i => algebraMap O Ω (v i)) '' (ordPart T₀ : Set (ι → O))) := by
  intro O Ω ι _ hO _ _ _ _ T₀ T hT
  classical
  haveI : IsAdicComplete (maximalIdeal O) O := hO.complete
  have hadm := (UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordAdm_maximalIdeal_and_finite_quotients (R := O) (M := ι → O)).1
  have hex := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.ordExists hadm T₀
  have key := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigOrdInt (K := Ω) hex.1
  set E := TensorProduct.piScalarRight O Ω Ω ι with hE
  have hEt : ∀ (a : Ω) (v : ι → O),
      E (a ⊗ₜ v) = a • fun i => algebraMap O Ω (v i) := UpperTheory.pi_scalar_right_tmul
  have hc : ∀ x, T (E x) = E (T₀.baseChange Ω x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v => rw [LinearMap.baseChange_tmul, hEt, hEt, map_smul, hT]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  have h1 := congrArg (Submodule.map E.toLinearMap) key
  simp only [Submodule.map_iSup, UpperTheory.map_max_gen_eigenspace_of_intertwine E _ T hc] at h1
  rw [iSup_subtype]
  refine Eq.trans ?_ (h1.symm.trans ?_)
  · rfl
  apply le_antisymm
  · rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
      rw [LinearMap.baseChange_tmul, LinearEquiv.coe_coe, hEt]
      refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)
      rw [← hex.2.1]
      exact ⟨v, rfl⟩
    | add x y hx hy => simp only [map_add] at ⊢; exact Submodule.add_mem _ hx hy
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    rw [← hex.2.1] at hv
    obtain ⟨w, rfl⟩ := hv
    refine ⟨_, ⟨(1 : Ω) ⊗ₜ w, rfl⟩, ?_⟩
    rw [LinearMap.baseChange_tmul, LinearEquiv.coe_coe, hEt, one_smul]
end

