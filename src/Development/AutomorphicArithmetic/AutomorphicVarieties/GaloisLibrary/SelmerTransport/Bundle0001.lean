module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.CocycleZeroMemInvariants
section
open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem exists_inj_of_ker_eq {R A B C : Type} [CommRing R] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] (p : A →ₗ[R] B) (q : A →ₗ[R] C)
    (hp : Function.Surjective p) (hk : ∀ a, p a = 0 ↔ q a = 0) :
    ∃ φ : B →ₗ[R] C, Function.Injective φ := by
  have hle : LinearMap.ker p ≤ LinearMap.ker q := fun a ha => (hk a).1 ha
  have hle' : LinearMap.ker q ≤ LinearMap.ker p := fun a ha => (hk a).2 ha
  refine ⟨(LinearMap.ker p).liftQ q hle ∘ₗ (p.quotKerEquivOfSurjective hp).symm.toLinearMap, ?_⟩
  rw [LinearMap.coe_comp]
  exact (LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ q hle hle')).comp
    (p.quotKerEquivOfSurjective hp).symm.injective

section

variable {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M]
  [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M]

private theorem cocycle_eq_zero (ρ : Representation R G M) {U' U : Subgroup G} (h : U' ≤ U) {γ : G} (hγ : γ ∈ U)
    (hU : U ≤ (Subgroup.zpowers γ ⊔ U').topologicalClosure) (z : Z1U ρ U)
    (h1 : ∀ u : U, u.1 ∈ U' → z.1 u = 0) (h2 : z.1 ⟨γ, hγ⟩ = 0) (u : U) : z.1 u = 0 := by
  obtain ⟨hcont, hcoc⟩ := (mem_Z1_iff_cocycle _ _).1 z.2
  have hone : z.1 1 = 0 := by
    have e := hcoc 1 1
    simp only [mul_one, map_one, Module.End.one_apply] at e
    simpa using e
  let K : Subgroup U :=
    { carrier := {x | z.1 x = 0}
      mul_mem' := fun {a b} ha hb => by
        show z.1 (a * b) = 0
        rw [hcoc, ha, hb, map_zero, add_zero]
      one_mem' := hone
      inv_mem' := fun {a} ha => by
        show z.1 a⁻¹ = 0
        have e := hcoc a⁻¹ a
        rw [inv_mul_cancel, hone, ha, map_zero, add_zero] at e
        exact e.symm }
  have hS : Subgroup.zpowers γ ⊔ U' ≤ K.map U.subtype := by
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact ⟨⟨γ, hγ⟩, h2, rfl⟩
    · intro x hx
      exact ⟨⟨x, h hx⟩, h1 ⟨x, h hx⟩ hx, rfl⟩
  have hu := hU u.2
  rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe] at hu
  have hV : IsOpen (z.1 ⁻¹' {z.1 u}) := hcont.isOpen_preimage _ (isOpen_discrete _)
  obtain ⟨O, hO, hOV⟩ := isOpen_induced_iff.1 hV
  have huO : u.1 ∈ O := by
    have : u ∈ Subtype.val ⁻¹' O := by rw [hOV]; rfl
    exact this
  obtain ⟨s, hsO, hsS⟩ := mem_closure_iff.1 hu O hO huO
  obtain ⟨⟨s', hs'U⟩, hzs, rfl⟩ := hS hsS
  have hmem : (⟨s', hs'U⟩ : U) ∈ Subtype.val ⁻¹' O := hsO
  rw [hOV] at hmem
  have e : z.1 ⟨s', hs'U⟩ = z.1 u := hmem
  rw [← e]
  exact hzs

private noncomputable def cob (ρ : Representation R G M) (hρ : ContAction ρ) (U : Subgroup G) (m : M) : Z1U ρ U :=
  ⟨d0 (ρ.comp U.subtype : Representation R U M) m, coboundaries_le_cocycles (ρ.comp U.subtype : Representation R U M)
    (Continuous.comp (f := fun p : U × M => ((p.1.1, p.2) : G × M)) hρ (by fun_prop)) ⟨m, rfl⟩⟩

private def Z0 (ρ : Representation R G M) (U' U : Subgroup G) : Submodule R (Z1U ρ U) where
  carrier := {z | ∀ u : U, u.1 ∈ U' → z.1 u = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun {a b} ha hb u hu => by
    show a.1 u + b.1 u = 0
    rw [ha u hu, hb u hu, add_zero]
  smul_mem' := fun c a ha u hu => by
    show c • a.1 u = 0
    rw [ha u hu, smul_zero]

private theorem cocycle_zero_mem_invariants (ρ : Representation R G M) {U' U : Subgroup G} (h : U' ≤ U) [hN : (U'.subgroupOf U).Normal]
    (g : U) (z : Z0 ρ U' U) : z.1.1 g ∈ H0U ρ U' := by
  obtain ⟨hcont, hcoc⟩ := (mem_Z1_iff_cocycle _ _).1 z.1.2
  rw [mem_riemannRochSpace_iff_regularAt_everywhere]
  intro v
  let v' : U := ⟨v.1, h v.2⟩
  have hw : g⁻¹ * v' * g ∈ U'.subgroupOf U := by
    have := hN.conj_mem v' (by rw [Subgroup.mem_subgroupOf]; exact v.2) g⁻¹
    simpa using this
  rw [Subgroup.mem_subgroupOf] at hw
  have hzw : z.1.1 (g⁻¹ * v' * g) = 0 := z.2 _ hw
  have hzv : z.1.1 v' = 0 := z.2 v' v.2
  have e1 := hcoc v' g
  have e2 := hcoc g (g⁻¹ * v' * g)
  rw [show g * (g⁻¹ * v' * g) = v' * g by group, hzw, map_zero, add_zero] at e2
  rw [hzv, zero_add, e2] at e1
  exact e1.symm

end

theorem UpperTheory.V.Base.kerResGen1 :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M), ContAction ρ → ∀ (U' U : Subgroup G) (h : U' ≤ U) [(U'.subgroupOf U).Normal] (γ : G), γ ∈ U →
      U ≤ (Subgroup.zpowers γ ⊔ U').topologicalClosure → ∀ T : H0U ρ U' →ₗ[R] H0U ρ U', (∀ m, (T m : M) = ρ γ m - m) →
      ∃ φ : LinearMap.ker (resU ρ h) →ₗ[R] (H0U ρ U' ⧸ LinearMap.range T), Function.Injective φ := by
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ hρ U' U h hN γ hγ hU T hT
  have hcobv : ∀ (m : M) (u : U), (cob ρ hρ U m).1 u = ρ u m - m := fun m u => rfl
  let ev : Z0 ρ U' U →ₗ[R] H0U ρ U' :=
    { toFun := fun a => ⟨a.1.1 ⟨γ, hγ⟩, cocycle_zero_mem_invariants ρ h ⟨γ, hγ⟩ a⟩
      map_add' := fun a b => rfl
      map_smul' := fun c a => rfl }
  let q : Z0 ρ U' U →ₗ[R] (H0U ρ U' ⧸ LinearMap.range T) := (LinearMap.range T).mkQ ∘ₗ ev
  let p0 : Z0 ρ U' U →ₗ[R] H1U ρ U :=
    (Submodule.comap (Z1U ρ U).subtype (B1 (MonoidHom.comp ρ U.subtype))).mkQ ∘ₗ (Z0 ρ U' U).subtype
  have hp0 : ∀ a, p0 a ∈ LinearMap.ker (resU ρ h) := by
    intro a
    rw [LinearMap.mem_ker]
    refine (resU_mk_eq_zero ρ h a.1).2 ⟨0, fun u => ?_⟩
    rw [map_zero, sub_zero]
    exact a.2 _ u.2
  let p : Z0 ρ U' U →ₗ[R] LinearMap.ker (resU ρ h) := LinearMap.codRestrict _ p0 hp0
  have hp : Function.Surjective p := by
    rintro ⟨x, hx⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨m, hm⟩ := (resU_mk_eq_zero ρ h z).1 (LinearMap.mem_ker.1 hx)
    refine ⟨⟨z - cob ρ hρ U m, fun u hu => ?_⟩, ?_⟩
    · show z.1 u - (cob ρ hρ U m).1 u = 0
      rw [hcobv]
      exact sub_eq_zero.2 (hm ⟨u.1, hu⟩)
    · apply Subtype.ext
      show Submodule.Quotient.mk (z - cob ρ hρ U m) = Submodule.Quotient.mk z
      rw [mk_eq_mk]
      refine ⟨-m, fun u => ?_⟩
      show z.1 u - (cob ρ hρ U m).1 u - z.1 u = ρ u (-m) - -m
      rw [hcobv, map_neg]
      abel
  have hk : ∀ a, p a = 0 ↔ q a = 0 := by
    intro a
    have hpa : p a = 0 ↔ ∃ m : M, ∀ u : U, a.1.1 u - (0 : Z1U ρ U).1 u = ρ u m - m := by
      rw [Subtype.ext_iff]
      show Submodule.Quotient.mk a.1 = (0 : H1U ρ U) ↔ _
      rw [← Submodule.Quotient.mk_zero, mk_eq_mk]
    have hqa : q a = 0 ↔ ∃ n : H0U ρ U', (T n : M) = a.1.1 ⟨γ, hγ⟩ := by
      show Submodule.Quotient.mk (ev a) = 0 ↔ _
      rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
      constructor
      · rintro ⟨n, hn⟩
        exact ⟨n, congrArg Subtype.val hn⟩
      · rintro ⟨n, hn⟩
        exact ⟨n, Subtype.ext hn⟩
    rw [hpa, hqa]
    constructor
    · rintro ⟨m, hm⟩
      have hmH : m ∈ H0U ρ U' := by
        rw [mem_riemannRochSpace_iff_regularAt_everywhere]
        intro v
        have e := hm ⟨v.1, h v.2⟩
        rw [a.2 ⟨v.1, h v.2⟩ v.2] at e
        exact (sub_eq_zero.1 (by simpa using e.symm))
      refine ⟨⟨m, hmH⟩, ?_⟩
      rw [hT]
      simpa using (hm ⟨γ, hγ⟩).symm
    · rintro ⟨n, hn⟩
      rw [hT] at hn
      have hnH := (mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 n.2
      have hv1 : ∀ u : U, u.1 ∈ U' → (a.1 - cob ρ hρ U n.1).1 u = 0 := by
        intro u hu
        show a.1.1 u - (cob ρ hρ U n.1).1 u = 0
        rw [hcobv, a.2 u hu]
        have e := hnH ⟨u.1, hu⟩
        simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype] at e
        simp [e]
      have hv2 : (a.1 - cob ρ hρ U n.1).1 ⟨γ, hγ⟩ = 0 := by
        show a.1.1 ⟨γ, hγ⟩ - (cob ρ hρ U n.1).1 ⟨γ, hγ⟩ = 0
        rw [hcobv, ← hn]
        simp
      refine ⟨n.1, fun u => ?_⟩
      have hz := cocycle_eq_zero ρ h hγ hU (a.1 - cob ρ hρ U n.1) hv1 hv2 u
      have e : a.1.1 u - (cob ρ hρ U n.1).1 u = 0 := hz
      rw [hcobv] at e
      simpa using sub_eq_zero.1 e
  exact exists_inj_of_ker_eq p q hp hk
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ContinuousCocycleMapApply
section
noncomputable section

open ReciprocityTheory.Gal TensorProduct

namespace UpperTheory.V.Base

section Alg

variable {R O ι N N' : Type} [CommRing R] [CommRing O] [Algebra R O] [Fintype ι] [AddCommGroup N] [Module R N]
  [AddCommGroup N'] [Module O N'] [Module R N'] [IsScalarTower R O N']

def coordSum (b : Module.Basis ι R O) (j : N →ₗ[R] N') : (ι → N) →ₗ[R] N' where
  toFun x := ∑ i, b i • j (x i)
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' r x := by simp [Finset.smul_sum, smul_comm r]

theorem coordSum_apply (b : Module.Basis ι R O) (j : N →ₗ[R] N') (x : ι → N) :
    coordSum b j x = ∑ i, b i • j (x i) := rfl

theorem isBaseChange_iff_coordSum (b : Module.Basis ι R O) (j : N →ₗ[R] N') :
    IsBaseChange O j ↔ Function.Bijective (coordSum b j) := by
  classical
  let e : (ι → N) ≃ₗ[R] O ⊗[R] N :=
    (Finsupp.linearEquivFunOnFinite R N ι).symm ≪≫ₗ (TensorProduct.equivFinsuppOfBasisLeft b).symm
  have he : ∀ x, e x = ∑ i, b i ⊗ₜ x i := fun x => by
    simp [e, TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum_fintype]
  unfold IsBaseChange IsTensorProduct
  rw [← Function.Bijective.of_comp_iff _ e.bijective]
  refine iff_of_eq (congrArg _ (funext fun x => ?_))
  simp [he, coordSum_apply]

theorem isBaseChange_restrict (b : Module.Basis ι R O) {j : N →ₗ[R] N'} (hj : IsBaseChange O j)
    (P : Submodule R N) (P' : Submodule O N') (h : ∀ x, coordSum b j x ∈ P' ↔ ∀ i, x i ∈ P)
    (j' : P →ₗ[R] P') (hj' : ∀ x, (j' x : N') = j x) : IsBaseChange O j' := by
  rw [isBaseChange_iff_coordSum b] at hj ⊢
  have e : ∀ x : ι → P, (coordSum b j' x : N') = coordSum b j fun i => x i := fun x => by
    simp [coordSum_apply, hj']
  refine ⟨fun x y hxy => funext fun i => Subtype.ext ?_, fun y => ?_⟩
  · exact congrFun (hj.1 ((e x).symm.trans ((congrArg Subtype.val hxy).trans (e y)))) i
  · obtain ⟨x, hx⟩ := hj.2 y
    exact ⟨fun i => ⟨x i, (h x).1 (hx ▸ y.2) i⟩, Subtype.ext ((e _).trans hx)⟩

theorem length_of_isBaseChange [IsLocalRing R] [IsLocalRing O] [IsLocalHom (algebraMap R O)] [Module.Flat R O]
    {j : N →ₗ[R] N'} (hj : IsBaseChange O j) :
    Module.length O N' =
      Module.length R N * Module.length O (O ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R O)) := by
  rw [← hj.equiv.length_eq, IsLocalRing.length_baseChange]

theorem map_coordSum (b : Module.Basis ι R O) (j : N →ₗ[R] N') (f : N → N) (f' : N' →ₗ[O] N')
    (h : ∀ x, j (f x) = f' (j x)) (x : ι → N) : f' (coordSum b j x) = coordSum b j fun i => f (x i) := by
  simp [coordSum_apply, h]

end Alg

section Coh

variable {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M]
  {O M' : Type} [CommRing O] [Algebra R O] [AddCommGroup M'] [Module O M'] [Module R M'] [IsScalarTower R O M']
  [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul O M']
  (ρ : Representation R G M) (ρ' : Representation O G M') (j : M →ₗ[R] M') (hj : ∀ g m, j (ρ g m) = ρ' g (j m))
  (U : Subgroup G)

def continuousCocycleMap : Z1U ρ U →ₗ[R] Z1U ρ' U where
  toFun z := ⟨fun u => j (z.1 u), (continuous_of_discreteTopology (f := j)).comp z.2.1, fun g h => by
    show j _ = j _ + ρ' g (j _)
    rw [z.2.2, map_add (f := _), ← hj]
    rfl⟩
  map_add' _ _ := Subtype.ext (funext fun _ => map_add j _ _)
  map_smul' _ _ := Subtype.ext (funext fun _ => map_smul j _ _)

theorem continuousCocycleMap_apply (z : Z1U ρ U) (u : U) : (continuousCocycleMap ρ ρ' j hj U z).1 u = j (z.1 u) := rfl

def h1Map : H1U ρ U →ₗ[R] H1U ρ' U :=
  Submodule.liftQ _ (((Submodule.mkQ _).restrictScalars R).comp (continuousCocycleMap ρ ρ' j hj U)) fun z hz => by
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hz
    refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨j m, fun u => ?_⟩)
    have e : z.1 u = ρ u m - m := hm u
    show j (z.1 u) = ρ' u (j m) - j m
    rw [e, map_sub, hj]

theorem h1Map_mk (z : Z1U ρ U) :
    h1Map ρ ρ' j hj U (Submodule.Quotient.mk z) = Submodule.Quotient.mk (continuousCocycleMap ρ ρ' j hj U z) := rfl

theorem h1Map_mem_locSel (𝒟 : Set (Subgroup G)) {x : H1U ρ U} (hx : x ∈ LocSel ρ U 𝒟) :
    h1Map ρ ρ' j hj U x ∈ LocSel ρ' U 𝒟 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [h1Map_mk, mk_mem_locSel]
  intro D hD
  obtain ⟨m, hm⟩ := mk_mem_locSel.1 hx D hD
  exact ⟨j m, fun u hu => by rw [continuousCocycleMap_apply, hm u hu, map_sub, hj]⟩

def selMap (𝒟 : Set (Subgroup G)) : LocSel ρ U 𝒟 →ₗ[R] LocSel ρ' U 𝒟 where
  toFun x := ⟨h1Map ρ ρ' j hj U x, h1Map_mem_locSel ρ ρ' j hj U 𝒟 x.2⟩
  map_add' _ _ := Subtype.ext (by simp)
  map_smul' _ _ := Subtype.ext (by simp)

variable {ι : Type} [Fintype ι] (b : Module.Basis ι R O)

theorem coordSum_z1Map (z : ι → Z1U ρ U) (u : U) :
    (coordSum b (continuousCocycleMap ρ ρ' j hj U) z).1 u = coordSum b j fun i => (z i).1 u := by
  simp [coordSum_apply, continuousCocycleMap_apply]

theorem coordSum_h1Map (z : ι → Z1U ρ U) :
    coordSum b (h1Map ρ ρ' j hj U) (fun i => Submodule.Quotient.mk (z i)) =
      Submodule.Quotient.mk (coordSum b (continuousCocycleMap ρ ρ' j hj U) z) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [coordSum_apply, h1Map_mk, ← Submodule.mkQ_apply, map_sum, map_smul]
  rfl

include hj in
theorem exists_cob_iff (hb : IsBaseChange O j) (p : U → Prop) (z : ι → U → M) :
    (∃ m', ∀ u : U, p u → coordSum b j (fun i => z i u) = ρ' u m' - m') ↔
      ∀ i, ∃ m, ∀ u : U, p u → z i u = ρ u m - m := by
  rw [isBaseChange_iff_coordSum b] at hb
  have e : ∀ (u : U) (m : ι → M), ρ' u (coordSum b j m) - coordSum b j m = coordSum b j fun i => ρ u (m i) - m i :=
    fun u m => by
      rw [map_coordSum b j (ρ u) (ρ' u) (hj u), ← map_sub]
      rfl
  constructor
  · rintro ⟨m', hm⟩ i
    obtain ⟨m, rfl⟩ := hb.2 m'
    exact ⟨m i, fun u hu => congrFun (hb.1 ((hm u hu).trans (e u m))) i⟩
  · intro h
    choose m hm using h
    exact ⟨coordSum b j m, fun u hu => by rw [e]; exact congrArg _ (funext fun i => hm i u hu)⟩

theorem coordSum_z1Map_surjective [DiscreteTopology M'] (hb : IsBaseChange O j) :
    Function.Surjective (coordSum b (continuousCocycleMap ρ ρ' j hj U)) := by
  rw [isBaseChange_iff_coordSum b] at hb
  intro y
  let e := LinearEquiv.ofBijective _ hb
  have he : ∀ m, coordSum b j (e.symm m) = m := e.apply_symm_apply
  refine ⟨fun i => ⟨fun u => e.symm (y.1 u) i,
    (continuous_of_discreteTopology (f := fun m => e.symm m i)).comp y.2.1, fun g h => ?_⟩, ?_⟩
  · have : e.symm (y.1 (g * h)) = e.symm (y.1 g) + fun i => ρ g (e.symm (y.1 h) i) := by
      apply hb.1
      rw [map_add (f := _), ← map_coordSum b j (ρ g) (ρ' g) (hj g), he, he, he]
      exact y.2.2 g h
    exact congrFun this i
  · exact Subtype.ext (funext fun u => (coordSum_z1Map ρ ρ' j hj U b _ u).trans (he _))

include b in
private theorem isBaseChange_h1Map' [DiscreteTopology M'] (hb : IsBaseChange O j) :
    IsBaseChange O (h1Map ρ ρ' j hj U) := by
  rw [isBaseChange_iff_coordSum b]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    choose z hz using fun i => Submodule.Quotient.mk_surjective _ (x i)
    obtain rfl : x = fun i => Submodule.Quotient.mk (z i) := funext fun i => (hz i).symm
    rw [coordSum_h1Map] at hx
    obtain ⟨m', hm'⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 hx)
    funext i
    obtain ⟨m, hm⟩ := (exists_cob_iff ρ ρ' j hj U b hb (fun _ => True) fun i => (z i).1).1
      ⟨m', fun u _ => (coordSum_z1Map ρ ρ' j hj U b z u).symm.trans (hm' u)⟩ i
    exact (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨m, fun u => hm u trivial⟩)
  · intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨z, rfl⟩ := coordSum_z1Map_surjective ρ ρ' j hj U b hb y
    exact ⟨_, coordSum_h1Map ρ ρ' j hj U b z⟩

theorem coordSum_mem_locSel (hb : IsBaseChange O j) (𝒟 : Set (Subgroup G)) (x : ι → H1U ρ U) :
    coordSum b (h1Map ρ ρ' j hj U) x ∈ LocSel ρ' U 𝒟 ↔ ∀ i, x i ∈ LocSel ρ U 𝒟 := by
  choose z hz using fun i => Submodule.Quotient.mk_surjective _ (x i)
  obtain rfl : x = fun i => Submodule.Quotient.mk (z i) := funext fun i => (hz i).symm
  rw [coordSum_h1Map]
  simp only [mk_mem_locSel, coordSum_z1Map]
  rw [forall_comm]
  refine forall_congr' fun D => ?_
  rw [forall_comm]
  exact imp_congr_right fun _ => exists_cob_iff ρ ρ' j hj U b hb (fun u => u.1 ∈ D) fun i => (z i).1


omit [Fintype ι] in
theorem isBaseChange_h1Map [Module.Free R O] [Module.Finite R O] [DiscreteTopology M'] (hb : IsBaseChange O j) :
    IsBaseChange O (h1Map ρ ρ' j hj U) :=
  isBaseChange_h1Map' ρ ρ' j hj U (Module.Free.chooseBasis R O) hb


omit [Fintype ι] in
theorem isBaseChange_selMap [Module.Free R O] [Module.Finite R O] [DiscreteTopology M'] (hb : IsBaseChange O j)
    (𝒟 : Set (Subgroup G)) : IsBaseChange O (selMap ρ ρ' j hj U 𝒟) :=
  isBaseChange_restrict (Module.Free.chooseBasis R O) (isBaseChange_h1Map ρ ρ' j hj U hb) _ _
    (coordSum_mem_locSel ρ ρ' j hj U _ hb 𝒟) _ fun _ => rfl

end Coh

end UpperTheory.V.Base

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.CorInv
section
open ReciprocityTheory.Gal UpperTheory.V.Base

theorem UpperTheory.V.Base.corInv :
    ∀ (R G M : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup M] [Module R M]
      [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [DiscreteTopology M] (ρ : Representation R G M), ContAction ρ → ∀ (U' U : Subgroup G) [U'.Normal] (h : U' ≤ U), IsOpen (U'.subgroupOf U : Set U) →
      ∀ x ∈ invariantsUnderSubgroupH1 ρ U U', U'.relIndex U • x ∈ LinearMap.range (resU ρ h) := by
  classical
  intro R G M _ _ _ _ _ _ _ _ _ _ ρ hρ U' U _ h hopen x hx
  by_cases hfin : U'.relIndex U = 0
  · rw [hfin, zero_smul]
    exact zero_mem _
  haveI : (U'.subgroupOf U).FiniteIndex := ⟨hfin⟩
  haveI : Fintype (U ⧸ U'.subgroupOf U) := Fintype.ofFinite _
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hinv : ∀ g : U, conjU ρ U' g (Submodule.Quotient.mk z) = Submodule.Quotient.mk z :=
    fun g => (Representation.mem_invariants _ _).mp hx g
  have hq : ∀ q : U ⧸ U'.subgroupOf U, ∃ m : M, ∀ u : U',
      ρ (q.out : G) (z.1 (conjHom U' (q.out : G) u)) - z.1 u = ρ u m - m := by
    intro q
    obtain ⟨z', hz1, hz2⟩ := conjU_mk ρ U' (q.out : G) z
    rw [hinv, mk_eq_mk] at hz1
    obtain ⟨m, hm⟩ := hz1
    refine ⟨-m, fun u => ?_⟩
    have e := hm u
    rw [hz2] at e
    rw [map_neg, neg_sub_neg, ← neg_sub ((ρ u) m) m, ← e]
    abel
  choose mq hmq using hq
  let f : U → M := fun g => if hg : (g : G) ∈ U' then z.1 ⟨g, hg⟩ else 0
  have hfc : ContinuousOn f (U'.subgroupOf U : Set U) := by
    rw [continuousOn_iff_continuous_restrict]
    refine (z.2.1.comp (Continuous.subtype_mk
      (continuous_subtype_val.comp continuous_subtype_val)
      (fun g : (U'.subgroupOf U : Set U) => Subgroup.mem_subgroupOf.mp g.2))).congr ?_
    intro g
    simp [f, dif_pos (Subgroup.mem_subgroupOf.mp g.2)]
  have hfcoc : ∀ g ∈ U'.subgroupOf U, ∀ k ∈ U'.subgroupOf U,
      f (g * k) = f g + (ρ.comp U.subtype) g (f k) := by
    intro g hg k hk
    rw [Subgroup.mem_subgroupOf] at hg hk
    have hgk : ((g * k : U) : G) ∈ U' := by
      rw [Subgroup.coe_mul]
      exact U'.mul_mem hg hk
    simp only [f, dif_pos hg, dif_pos hk, dif_pos hgk]
    exact z.2.2 ⟨g, hg⟩ ⟨k, hk⟩
  obtain ⟨F, hFc, hFcoc, ⟨x0, hx0⟩, -⟩ := GlobalTheory.exists_corestriction_cocycle R U M
    (ρ.comp U.subtype) (U'.subgroupOf U) hopen (fun _ => continuous_of_discreteTopology)
    (fun m => hρ.comp (Continuous.prodMk
      (continuous_subtype_val) continuous_const)) f hfc hfcoc
  let Fz : Z1U ρ U := ⟨F, hFc, hFcoc⟩
  refine ⟨Submodule.Quotient.mk Fz, ?_⟩
  obtain ⟨w, hw1, hw2⟩ := resU_mk ρ h Fz
  rw [hw1, ← Submodule.Quotient.mk_smul, mk_eq_mk]
  refine ⟨x0 + ∑ q, mq q, fun u => ?_⟩
  have hterm : ∀ q : U ⧸ U'.subgroupOf U,
      (ρ.comp U.subtype) q.out (f ((q.out)⁻¹ * ⟨(u : G), h u.2⟩ * q.out)) =
        z.1 u + (ρ u (mq q) - mq q) := by
    intro q
    rw [← hmq q u, add_sub_cancel]
    have hmem : (((q.out)⁻¹ * ⟨(u : G), h u.2⟩ * q.out : U) : G) ∈ U' := by
      have e := ‹U'.Normal›.conj_mem u u.2 ((q.out : G)⁻¹)
      simpa [mul_assoc] using e
    simp only [f, dif_pos hmem]
    rfl
  have hcard : Fintype.card (U ⧸ U'.subgroupOf U) = U'.relIndex U := by
    rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
  rw [hw2 u]
  show F ⟨(u : G), h u.2⟩ - _ = _
  rw [hx0 ⟨u, h u.2⟩ (Subgroup.mem_subgroupOf.mpr u.2), finsum_eq_sum_of_fintype,
    Finset.sum_congr rfl (fun q _ => hterm q), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_univ, hcard]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Submodule.coe_smul, Pi.smul_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
    map_add, map_sum]
  rw [show ((U'.relIndex U • z : Z1U ρ U') : U' → M) u = U'.relIndex U • z.1 u from rfl]
  abel
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.ExistsO
section
open ReciprocityTheory.Gal UpperTheory.V.Base

theorem UpperTheory.V.Base.existsO :
    ∀ (l : ℕ) [Fact l.Prime] (n : ℕ) [NeZero n], ∃ O : Subalgebra ℤ_[l] (PadicAlgCl l),
      IsDiscreteValuationRing O ∧ Module.Finite ℤ_[l] O ∧ HasEnoughRootsOfUnity O n := by
  intro l _ n _
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl l) n
  have hζi : IsIntegral ℤ_[l] ζ := (hζ.isIntegral (NeZero.pos n)).tower_top
  let K : IntermediateField ℚ_[l] (PadicAlgCl l) := IntermediateField.adjoin ℚ_[l] {ζ}
  haveI : FiniteDimensional ℚ_[l] K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  obtain ⟨h1, h2, -⟩ := UpperTheory.V.abelian₂.dvr_intClosure l K
  let f : K →ₐ[ℤ_[l]] PadicAlgCl l := K.val.restrictScalars ℤ_[l]
  have hf : Function.Injective f := Subtype.val_injective
  let e := (integralClosure ℤ_[l] K).equivMapOfInjective f hf
  refine ⟨(integralClosure ℤ_[l] K).map f, ?_, ?_, ?_⟩
  · exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  · exact Module.Finite.equiv e.toLinearEquiv
  · have hz : ζ ∈ K := IntermediateField.mem_adjoin_simple_self _ _
    have hmem : ζ ∈ (integralClosure ℤ_[l] K).map f :=
      ⟨⟨ζ, hz⟩, (isIntegral_algHom_iff f hf).1 hζi, rfl⟩
    refine ⟨⟨⟨ζ, hmem⟩, ?_⟩, rootsOfUnity.isCyclic _ _⟩
    exact IsPrimitiveRoot.of_map_of_injective (f := ((integralClosure ℤ_[l] K).map f).val) hζ Subtype.val_injective
end

