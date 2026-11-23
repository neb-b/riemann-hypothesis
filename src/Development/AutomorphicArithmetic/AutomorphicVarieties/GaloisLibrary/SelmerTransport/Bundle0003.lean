module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.LenEigEq
section
open ReciprocityTheory.Gal UpperTheory.V.Base

section

variable {O Q N : Type} [CommRing O] [CommGroup Q] [Fintype Q] [AddCommGroup N] [Module O N]

private noncomputable def prj (π : Representation O Q N) (c : O) (ψ : Q →* Oˣ) : N →ₗ[O] N :=
  c • ∑ g : Q, ((ψ g⁻¹ : Oˣ) : O) • π g

private theorem prj_apply (π : Representation O Q N) (c : O) (ψ : Q →* Oˣ) (x : N) :
    prj π c ψ x = c • ∑ g : Q, ((ψ g⁻¹ : Oˣ) : O) • π g x := by
  simp only [prj, LinearMap.smul_apply, LinearMap.sum_apply]

private theorem prj_mem (π : Representation O Q N) (c : O) (ψ : Q →* Oˣ) (x : N) :
    prj π c ψ x ∈ eig π ψ := by
  rw [mem_eig]
  intro h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [prj_apply, map_smul, smul_comm, map_sum, Finset.smul_sum (r := ((ψ h : Oˣ) : O))]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_
  rw [map_smul, smul_smul, Equiv.coe_mulLeft, ← Units.val_mul, ← map_mul, map_mul π, Module.End.mul_apply]
  congr 3
  rw [mul_inv, mul_inv_cancel_left]

private theorem prj_act (π : Representation O Q N) (c : O) (ψ : Q →* Oˣ) (h : Q) (x : N) :
    prj π c ψ (π h x) = ((ψ h : Oˣ) : O) • prj π c ψ x := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← mem_eig.1 (prj_mem π c ψ x) h, prj_apply, prj_apply, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smul, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]

private theorem prj_self (π : Representation O Q N) {c : O} (hc : c * (Fintype.card Q : O) = 1) (ψ : Q →* Oˣ)
    {x : N} (hx : x ∈ eig π ψ) : prj π c ψ x = x := by
  rw [prj_apply]
  have : ∀ g : Q, ((ψ g⁻¹ : Oˣ) : O) • π g x = x := fun g => by
    rw [mem_eig.1 hx, smul_smul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_smul]
  simp only [this]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul O, smul_smul, hc, one_smul]

private theorem prj_ne [IsDomain O] (π : Representation O Q N) (c : O) {ψ χ : Q →* Oˣ} (hne : ψ ≠ χ)
    {x : N} (hx : x ∈ eig π χ) : prj π c ψ x = 0 := by
  rw [prj_apply]
  have : ∀ g : Q, ((ψ g⁻¹ : Oˣ) : O) • π g x = ((Units.coeHom O).comp (ψ⁻¹ * χ) g) • x := fun g => by
    rw [mem_eig.1 hx, smul_smul]
    simp
  simp only [this]
  rw [← Finset.sum_smul, sum_hom_units_eq_zero, zero_smul, smul_zero]
  intro h
  apply hne
  ext g
  have h1 := DFunLike.congr_fun h g
  have h2 : (ψ g)⁻¹ * χ g = 1 := Units.ext (by simpa using h1)
  rw [inv_mul_eq_one.1 h2]

private theorem sub_prj_mem (π : Representation O Q N) {c : O} (hc : c * (Fintype.card Q : O) = 1) (ψ : Q →* Oˣ)
    (x : N) : prj π c ψ x - x ∈ coeig π ψ := by
  have hx : x = c • ∑ g : Q, ((ψ g⁻¹ : Oˣ) : O) • ((ψ g : Oˣ) : O) • x := by
    have : ∀ g : Q, ((ψ g⁻¹ : Oˣ) : O) • ((ψ g : Oˣ) : O) • x = x := fun g => by
      rw [smul_smul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, one_smul]
    simp only [this]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul O, smul_smul, hc, one_smul]
  have : prj π c ψ x - x = c • ∑ g : Q, ((ψ g⁻¹ : Oˣ) : O) • (π g x - ((ψ g : Oˣ) : O) • x) := by
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [← hx, prj_apply]
  rw [this]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ ?_)
  exact Submodule.mem_iSup_of_mem g ⟨x, rfl⟩

private theorem sum_prj [IsDomain O] [HasEnoughRootsOfUnity O (Monoid.exponent Q)] [Fintype (Q →* Oˣ)]
    (π : Representation O Q N) {c : O} (hc : c * (Fintype.card Q : O) = 1) (x : N) :
    ∑ ψ : Q →* Oˣ, prj π c ψ x = x := by
  simp only [prj_apply]
  rw [← Finset.smul_sum, Finset.sum_comm, Finset.sum_eq_single (1 : Q)]
  · simp only [inv_one, map_one, Units.val_one, one_smul, Module.End.one_apply]
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity, Nat.card_eq_fintype_card,
      ← Nat.cast_smul_eq_nsmul O, smul_smul, hc, one_smul]
  · intro g _ hg
    rw [← Finset.sum_smul]
    obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity Q O (inv_ne_one.2 hg)
    have := sum_hom_units_eq_zero ((Units.coeHom O).comp (MonoidHom.eval g⁻¹ : (Q →* Oˣ) →* Oˣ)) (by
      intro h
      exact hφ (Units.ext (DFunLike.congr_fun h φ)))
    have h2 : ∑ ψ : Q →* Oˣ, ((ψ g⁻¹ : Oˣ) : O) = 0 := this
    rw [h2, zero_smul]
  · simp

end

theorem UpperTheory.V.Base.lenEigEq :
    ∀ (O Q N : Type) [CommRing O] [IsDomain O] [CommGroup Q] [Finite Q] [HasEnoughRootsOfUnity O (Monoid.exponent Q)]
      [Fintype (Q →* Oˣ)] [AddCommGroup N] [Module O N] (π : Representation O Q N), IsUnit (Nat.card Q : O) →
      Module.length O N = ∑ ψ : Q →* Oˣ, Module.length O (eig π ψ) ∧ ∀ ψ : Q →* Oˣ, IsCompl (eig π ψ) (coeig π ψ) := by
  intro O Q N _ _ _ _ _ _ _ _ π hu
  classical
  letI := Fintype.ofFinite Q
  rw [Nat.card_eq_fintype_card] at hu
  obtain ⟨c, hc⟩ := hu.exists_left_inv
  refine ⟨?_, fun ψ => ⟨?_, ?_⟩⟩
  · rw [← Module.length_pi_of_fintype]
    let f : N →ₗ[O] (∀ ψ : Q →* Oˣ, eig π ψ) :=
      LinearMap.pi fun ψ => (prj π c ψ).codRestrict (eig π ψ) (prj_mem π c ψ)
    have hf : ∀ x ψ, ((f x ψ : eig π ψ) : N) = prj π c ψ x := fun _ _ => rfl
    refine (LinearEquiv.ofBijective f ⟨?_, ?_⟩).length_eq
    · intro x y hxy
      rw [← sum_prj π hc x, ← sum_prj π hc y]
      exact Finset.sum_congr rfl fun ψ _ => by rw [← hf, ← hf, hxy]
    · intro y
      refine ⟨∑ χ, (y χ : N), funext fun ψ => Subtype.ext ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hf, map_sum, Finset.sum_eq_single ψ, prj_self π hc ψ (y ψ).2]
      · intro χ _ hχ
        exact prj_ne π c hχ.symm (y χ).2
      · simp
  · rw [Submodule.disjoint_def]
    intro x hx hy
    have hle : coeig π ψ ≤ LinearMap.ker (prj π c ψ) := by
      refine iSup_le fun g => ?_
      rintro _ ⟨z, rfl⟩
      simp [prj_act]
    rw [← prj_self π hc ψ hx]
    exact hle hy
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have : x = prj π c ψ x - (prj π c ψ x - x) := by abel
    rw [this]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left (prj_mem π c ψ x))
      (Submodule.mem_sup_right (sub_prj_mem π hc ψ x))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.SelLocal
section
open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem length_le_of_ker_le {R A B : Type} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] {C : Type} [AddCommGroup C] [Module R C] (f : A →ₗ[R] B)
    (g : LinearMap.ker f →ₗ[R] C) (hg : Function.Injective g) :
    Module.length R A ≤ Module.length R C + Module.length R B := by
  rw [Module.length_eq_add_of_exact (LinearMap.ker f).subtype f.rangeRestrict
    (Submodule.subtype_injective _) f.surjective_rangeRestrict
    (LinearMap.exact_iff.mpr (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]))]
  exact add_le_add (Module.length_le_of_injective g hg)
    (Module.length_le_of_injective (LinearMap.range f).subtype (Submodule.subtype_injective _))

theorem UpperTheory.V.Base.selLocal :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (U' U : Subgroup G) (h : U' ≤ U) (𝒟 : Set (Subgroup G)) (ι : Type) [Fintype ι] (D : ι → Subgroup G), (∀ i, D i ∈ 𝒟) →
      (∀ D' ∈ 𝒟, U ⊓ D' ≤ U' ∨ ∃ i, ∃ u ∈ U, ∀ x ∈ U ⊓ D', u⁻¹ * x * u ∈ D i) →
      Module.length R ((LocSel ρ U' 𝒟).comap (resU ρ h)) ≤ Module.length R (LocSel ρ U 𝒟) + ∑ i, Module.length R (LinearMap.ker (resU ρ (inf_le_inf_right (D i) h))) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ U' U h 𝒟 ι _ D hD hcov
  set X := (LocSel ρ U' 𝒟).comap (resU ρ h) with hX
  have key0 : ∀ x ∈ X, ∀ D' ∈ 𝒟, resU ρ (le_trans inf_le_left h : U' ⊓ D' ≤ U) x = 0 := by
    intro x hx D' hD'
    have e := (mem_locSel.mp (Submodule.mem_comap.mp hx)) D' hD'
    rw [resU_resU] at e
    exact e
  have key : ∀ x ∈ X, ∀ D' ∈ 𝒟,
      resU ρ (inf_le_inf_right D' h) (resU ρ (inf_le_left : U ⊓ D' ≤ U) x) = 0 := by
    intro x hx D' hD'
    rw [resU_resU]
    exact key0 x hx D' hD'
  let f : X →ₗ[R] (∀ i, LinearMap.ker (resU ρ (inf_le_inf_right (D i) h))) :=
    LinearMap.pi fun i => LinearMap.codRestrict _
      ((resU ρ (inf_le_left : U ⊓ D i ≤ U)).comp X.subtype)
      (fun x => LinearMap.mem_ker.mpr (key x.1 x.2 (D i) (hD i)))
  have hmem : ∀ y ∈ LinearMap.ker f, ((y : H1U ρ U)) ∈ LocSel ρ U 𝒟 := by
    intro y hy
    have hy' : ∀ i, resU ρ (inf_le_left : U ⊓ D i ≤ U) (y : H1U ρ U) = 0 := by
      intro i
      simpa [f] using congrArg Subtype.val (congrFun (LinearMap.mem_ker.mp hy) i)
    rw [mem_locSel]
    intro D' hD'
    rcases hcov D' hD' with hle | ⟨i, u, hu, hconj⟩
    · have e := resU_resU ρ (le_inf hle inf_le_right : U ⊓ D' ≤ U' ⊓ D')
        (le_trans inf_le_left h) (y : H1U ρ U)
      rw [key0 _ y.2 D' hD', map_zero] at e
      exact e.symm
    · obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (y : H1U ρ U)
      have h0 := hy' i
      rw [← hz] at h0 ⊢
      rw [resU_mk_eq_zero] at h0 ⊢
      obtain ⟨m, hm⟩ := h0
      refine ⟨ρ u m - z.1 ⟨u, hu⟩, fun v => ?_⟩
      have hvU : (v : G) ∈ U := (Subgroup.mem_inf.mp v.2).1
      have hwD : u⁻¹ * (v : G) * u ∈ D i := hconj v v.2
      have hwU : u⁻¹ * (v : G) * u ∈ U := U.mul_mem (U.mul_mem (U.inv_mem hu) hvU) hu
      have e1 : z.1 ⟨u⁻¹ * (v : G) * u, hwU⟩ = ρ (u⁻¹ * (v : G) * u) m - m :=
        hm ⟨u⁻¹ * (v : G) * u, Subgroup.mem_inf.mpr ⟨hwU, hwD⟩⟩
      have hc := z.2.2
      have c1 := hc ⟨v, hvU⟩ ⟨u, hu⟩
      have c2 := hc ⟨u, hu⟩ ⟨u⁻¹ * (v : G) * u, hwU⟩
      have eq : (⟨v, hvU⟩ * ⟨u, hu⟩ : U) = ⟨u, hu⟩ * ⟨u⁻¹ * (v : G) * u, hwU⟩ :=
        Subtype.ext (by simp [mul_assoc])
      rw [eq, c2, e1] at c1
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype] at c1
      have hr : ρ u (ρ (u⁻¹ * (v : G) * u) m) = ρ v (ρ u m) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      rw [map_sub, hr] at c1
      show z.1 ⟨v, hvU⟩ = _
      rw [eq_sub_of_add_eq c1.symm]
      simp only [map_sub]
      abel
  let g : LinearMap.ker f →ₗ[R] LocSel ρ U 𝒟 :=
    LinearMap.codRestrict _ (X.subtype.comp (LinearMap.ker f).subtype) (fun y => hmem y.1 y.2)
  have hg : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    have e := congrArg Subtype.val hab
    exact e
  have e := length_le_of_ker_le f g hg
  rwa [Module.length_pi_of_fintype] at e
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.SelTransport
section
open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem exists_continuous_mulEquiv_of_map_embedding {G G' : Type} [Group G] [Group G'] [TopologicalSpace G]
    [TopologicalSpace G'] (φ : G' →* G) (hφ : Topology.IsEmbedding φ) (U' : Subgroup G')
    (U : Subgroup G) (h : U'.map φ = U) :
    ∃ e : U' ≃* U, (∀ u' : U', ((e u' : U) : G) = φ u') ∧ Continuous e ∧ Continuous e.symm := by
  have hmem : ∀ u' : U', φ u' ∈ U := fun u' => h ▸ Subgroup.mem_map_of_mem φ u'.2
  let f : U' →* U :=
    { toFun := fun u' => ⟨φ u', hmem u'⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply hφ.injective
    exact congrArg Subtype.val hab
  have hsurj : Function.Surjective f := by
    rintro ⟨g, hg⟩
    rw [← h] at hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
    exact ⟨⟨x, hx⟩, rfl⟩
  let e : U' ≃* U := MulEquiv.ofBijective f ⟨hinj, hsurj⟩
  have he : ∀ u' : U', ((e u' : U) : G) = φ u' := fun _ => rfl
  refine ⟨e, he, ?_, ?_⟩
  · change Continuous (fun u' : U' => (⟨φ u', hmem u'⟩ : U))
    exact (hφ.continuous.comp continuous_subtype_val).subtype_mk _
  · rw [Topology.IsEmbedding.subtypeVal.isInducing.continuous_iff, hφ.isInducing.continuous_iff]
    have hc : (⇑φ ∘ Subtype.val ∘ ⇑e.symm) = (Subtype.val : U → G) := by
      funext u
      have := he (e.symm u)
      rw [e.apply_symm_apply] at this
      exact this.symm
    rw [hc]
    exact continuous_subtype_val

theorem UpperTheory.V.Base.selTransport :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (G' : Type) [Group G'] [TopologicalSpace G'] (φ : G' →* G), Topology.IsEmbedding φ →
      ∀ (U' : Subgroup G') (U : Subgroup G), U'.map φ = U → ∀ 𝒟 : Set (Subgroup G),
      ∃ Φ : LocSel (ρ.comp φ : Representation R G' M) U' (Subgroup.comap φ '' 𝒟) ≃ₗ[R] LocSel ρ U 𝒟,
        ∀ (z' : Z1U (ρ.comp φ : Representation R G' M) U') (z : Z1U ρ U) hz', (∀ (u' : U') (u : U), φ u' = u → z.1 u = z'.1 u') →
          (Φ ⟨Submodule.Quotient.mk z', hz'⟩ : H1U ρ U) = Submodule.Quotient.mk z := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ G' _ _ φ hφ U' U hU 𝒟
  obtain ⟨e, he, hec, hesc⟩ := exists_continuous_mulEquiv_of_map_embedding φ hφ U' U hU
  have key : ∀ g : U, φ ((e.symm g : U') : G') = g := fun g => by
    rw [← he, e.apply_symm_apply]
  let A : Representation R U' M := (ρ.comp φ).comp U'.subtype
  let B : Representation R U M := ρ.comp U.subtype
  let F : H1 B →ₗ[R] H1 A :=
    pairH1DecompositionMap B A e.toMonoidHom hec LinearMap.id continuous_id (fun g m => by
      simp only [A, B, LinearMap.id_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
        MulEquiv.coe_toMonoidHom, he])
  let E : H1 A →ₗ[R] H1 B :=
    pairH1DecompositionMap A B e.symm.toMonoidHom hesc LinearMap.id continuous_id (fun g m => by
      simp only [A, B, LinearMap.id_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
        MulEquiv.coe_toMonoidHom, key])
  have hEF : E ∘ₗ F = LinearMap.id := by
    apply LinearMap.ext
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [E, F, LinearMap.comp_apply, pairH1DecompositionMap, Submodule.mapQ_apply, LinearMap.id_apply]
    congr 1
    apply Subtype.ext
    funext g
    simp [compatiblePairCocycles1]
  have hFE : F ∘ₗ E = LinearMap.id := by
    apply LinearMap.ext
    intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [E, F, LinearMap.comp_apply, pairH1DecompositionMap, Submodule.mapQ_apply, LinearMap.id_apply]
    congr 1
    apply Subtype.ext
    funext g
    simp [compatiblePairCocycles1]
  let L : H1 A ≃ₗ[R] H1 B := LinearEquiv.ofLinear E F hEF hFE
  have hmap : (LocSel (ρ.comp φ : Representation R G' M) U' (Subgroup.comap φ '' 𝒟)).map
      (L : H1 A →ₗ[R] H1 B) = LocSel ρ U 𝒟 := by
    ext x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [Submodule.mem_map_equiv]
    simp only [L, LinearEquiv.ofLinear_symm_apply, F, pairH1DecompositionMap, Submodule.mapQ_apply]
    rw [mk_mem_locSel, mk_mem_locSel]
    constructor
    · intro hyp D hD
      obtain ⟨m, hm⟩ := hyp _ ⟨D, hD, rfl⟩
      refine ⟨m, fun u hu => ?_⟩
      have h1 := hm (e.symm u) (by rw [Subgroup.mem_comap, key]; exact hu)
      simpa [compatiblePairCocycles1, key] using h1
    · rintro hyp D' ⟨D, hD, rfl⟩
      obtain ⟨m, hm⟩ := hyp D hD
      refine ⟨m, fun u' hu' => ?_⟩
      have h1 := hm (e u') (by rw [he]; exact hu')
      rw [he] at h1
      simpa [compatiblePairCocycles1, he] using h1
  refine ⟨L.ofSubmodules _ _ hmap, ?_⟩
  intro z' z hz' hzz
  rw [LinearEquiv.ofSubmodules_apply]
  simp only [L, LinearEquiv.ofLinear_apply, E, pairH1DecompositionMap, Submodule.mapQ_apply]
  congr 1
  apply Subtype.ext
  funext u
  simp only [compatiblePairCocycles1]
  exact (hzz (e.symm u) u (key u)).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.SelTwist
section
open ReciprocityTheory.Gal UpperTheory.V.Base

section

variable {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M]

private noncomputable def h1MapOfAgreeOnSubgroup (ρ ρ' : Representation R G M) (U : Subgroup G)
    (h : ∀ (u : U) m, ρ u m = ρ' u m) : H1U ρ U →ₗ[R] H1U ρ' U :=
  pairH1DecompositionMap _ _ (MonoidHom.id U) continuous_id LinearMap.id continuous_id fun u m => h u m

private theorem sameH1_mk (ρ ρ' : Representation R G M) (U : Subgroup G)
    (h : ∀ (u : U) m, ρ u m = ρ' u m) (z : Z1U ρ U) :
    ∃ z' : Z1U ρ' U, h1MapOfAgreeOnSubgroup ρ ρ' U h (Submodule.Quotient.mk z) = Submodule.Quotient.mk z' ∧
      ∀ u : U, z'.1 u = z.1 u := ⟨_, rfl, fun _ => rfl⟩

private theorem sameH1_involutive (ρ ρ' : Representation R G M) (U : Subgroup G)
    (h : ∀ (u : U) m, ρ u m = ρ' u m) (h' : ∀ (u : U) m, ρ' u m = ρ u m) (x : H1U ρ U) :
    h1MapOfAgreeOnSubgroup ρ' ρ U h' (h1MapOfAgreeOnSubgroup ρ ρ' U h x) = x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

private theorem sameH1_mem_localSelmer (ρ ρ' : Representation R G M) (U : Subgroup G)
    (h : ∀ (u : U) m, ρ u m = ρ' u m) (𝒟 : Set (Subgroup G)) (x : H1U ρ U) (hx : x ∈ LocSel ρ U 𝒟) :
    h1MapOfAgreeOnSubgroup ρ ρ' U h x ∈ LocSel ρ' U 𝒟 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z', e, f⟩ := sameH1_mk ρ ρ' U h z
  rw [e]
  rw [mk_mem_locSel] at hx ⊢
  intro D hD
  obtain ⟨m, hm⟩ := hx D hD
  exact ⟨m, fun u hu => by rw [f, hm u hu, h]⟩

private noncomputable def sameSel (ρ ρ' : Representation R G M) (U : Subgroup G)
    (h : ∀ (u : U) m, ρ u m = ρ' u m) (𝒟 : Set (Subgroup G)) : LocSel ρ U 𝒟 ≃ₗ[R] LocSel ρ' U 𝒟 :=
  LinearEquiv.ofLinear ((h1MapOfAgreeOnSubgroup ρ ρ' U h).restrict (sameH1_mem_localSelmer ρ ρ' U h 𝒟))
    ((h1MapOfAgreeOnSubgroup ρ' ρ U fun u m => (h u m).symm).restrict (sameH1_mem_localSelmer ρ' ρ U _ 𝒟))
    (LinearMap.ext fun x => Subtype.ext (sameH1_involutive ρ' ρ U _ h x.1))
    (LinearMap.ext fun x => Subtype.ext (sameH1_involutive ρ ρ' U h _ x.1))

private theorem sameH1_conjugation_scalar [IsTopologicalGroup G] [DiscreteTopology M] (ρ ρ' : Representation R G M)
    (U : Subgroup G) [U.Normal] (h : ∀ (u : U) m, ρ u m = ρ' u m) (g : G) (c : R)
    (hg : ∀ m, ρ g m = c • ρ' g m) (x : H1U ρ U) :
    h1MapOfAgreeOnSubgroup ρ ρ' U h (conjRep ρ U g x) = c • conjRep ρ' U g (h1MapOfAgreeOnSubgroup ρ ρ' U h x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨z₁, e₁, f₁⟩ := sameH1_mk ρ ρ' U h z
  obtain ⟨z₂, e₂, f₂⟩ := conjU_mk ρ' U g z₁
  obtain ⟨z₃, e₃, f₃⟩ := conjU_mk ρ U g z
  obtain ⟨z₄, e₄, f₄⟩ := sameH1_mk ρ ρ' U h z₃
  rw [conjRep_apply, conjRep_apply, e₁, e₂, e₃, e₄, ← Submodule.Quotient.mk_smul]
  congr 1
  refine Subtype.ext (funext fun u => ?_)
  show z₄.1 u = c • z₂.1 u
  rw [f₄, f₃, f₂, f₁, hg]

end

theorem UpperTheory.V.Base.selTwist :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M) (ρ' : Representation R G M) (θ : G →* Rˣ), (∀ g m, ρ g m = ((θ g : Rˣ) : R) • ρ' g m) →
      ∀ (U : Subgroup G) [U.Normal], (∀ u ∈ U, θ u = 1) → ∀ (𝒟 : Set (Subgroup G)) (h𝒟 : ConjStable 𝒟),
      (∃ Φ : LocSel ρ U 𝒟 ≃ₗ[R] LocSel ρ' U 𝒟, ∀ g x, Φ (selRep ρ U h𝒟 g x) = ((θ g : Rˣ) : R) • selRep ρ' U h𝒟 g (Φ x)) ∧
      ∀ (W : Subgroup G) (φ : W →* Rˣ), Module.length R (selEig ρ U h𝒟 W (θ.comp W.subtype * φ)) = Module.length R (selEig ρ' U h𝒟 W φ) := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ ρ' θ hθ U _ hU 𝒟 h𝒟
  have h : ∀ (u : U) m, ρ u m = ρ' u m := fun u m => by
    rw [hθ, hU u u.2, Units.val_one, one_smul]
  have hΦ : ∀ g x, sameSel ρ ρ' U h 𝒟 (selRep ρ U h𝒟 g x) =
      ((θ g : Rˣ) : R) • selRep ρ' U h𝒟 g (sameSel ρ ρ' U h 𝒟 x) := fun g x =>
    Subtype.ext (sameH1_conjugation_scalar ρ ρ' U h g _ (hθ g) x.1)
  refine ⟨⟨_, hΦ⟩, fun W φ => ?_⟩
  generalize sameSel ρ ρ' U h 𝒟 = Φ at hΦ
  have key : ∀ x, x ∈ selEig ρ U h𝒟 W (θ.comp W.subtype * φ) ↔ Φ x ∈ selEig ρ' U h𝒟 W φ := by
    intro x
    rw [mem_eig, mem_eig]
    refine forall_congr' fun w => ?_
    show selRep ρ U h𝒟 w x = ((θ w * φ w : Rˣ) : R) • x ↔ selRep ρ' U h𝒟 w (Φ x) = ((φ w : Rˣ) : R) • Φ x
    rw [← Φ.injective.eq_iff, hΦ, map_smul, Units.val_mul, mul_smul]
    exact (Units.isUnit (θ w)).smul_left_cancel
  have hmap : (selEig ρ U h𝒟 W (θ.comp W.subtype * φ)).map (Φ : _ →ₗ[R] _) = selEig ρ' U h𝒟 W φ := by
    ext y
    obtain ⟨x, rfl⟩ := Φ.surjective y
    rw [← key]
    exact ⟨fun ⟨x', hx', e⟩ => Φ.injective e ▸ hx', fun hx => ⟨x, hx, rfl⟩⟩
  exact (Φ.ofSubmodules _ _ hmap).length_eq
end

