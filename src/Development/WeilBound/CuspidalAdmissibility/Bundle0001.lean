module

public import Mathlib
public import GroundTheory.AutomorphicForms.SmoothRep
public import GroundTheory.AutomorphicForms.Bundle0007

@[expose] public section

-- bundled from Development.WeilBound.CuspidalAdmissibility.OccPair
section
open GroundTheory.Automorphic

namespace PositivityTheory.TfC.OccursIff.Pair

theorem conjDual_finite (E : Type) [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E] :
    FiniteDimensional ℂ (E →ₗ⋆[ℂ] ℂ) ∧ Module.finrank ℂ (E →ₗ⋆[ℂ] ℂ) ≤ Module.finrank ℂ E := by
  let b := Module.finBasis ℂ E
  let e : (E →ₗ⋆[ℂ] ℂ) →ₗ[ℂ] (Fin (Module.finrank ℂ E) → ℂ) :=
    { toFun := fun l i => l (b i)
      map_add' := fun l l' => by ext i; simp
      map_smul' := fun c l => by ext i; simp }
  have he : Function.Injective e := fun l l' h => b.ext fun i => congrFun h i
  haveI : FiniteDimensional ℂ (E →ₗ⋆[ℂ] ℂ) := Module.Finite.of_injective e he
  refine ⟨this, ?_⟩
  have h := LinearMap.finrank_le_finrank_of_injective he
  simpa using h

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
theorem act_inv (π : Representation ℂ G Y) (g : G) (z : Y) : π g (π g⁻¹ z) = z := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

theorem leftKer_eq_zero (π : Representation ℂ G Y) (hπi : π.IsIrreducible)
    (C : Y →ₗ[ℂ] Y →ₗ⋆[ℂ] ℂ) (hC : ∀ g x y, C (π g x) (π g y) = C x y) (hC0 : C ≠ 0) :
    ∀ a, C a = 0 → a = 0 := by
  let S : Subrepresentation π := ⟨LinearMap.ker C, fun g a ha => by
    rw [LinearMap.mem_ker] at ha ⊢
    refine LinearMap.ext fun z => ?_
    rw [← act_inv π g z, hC, ha]
    rfl⟩
  rcases hπi.eq_bot_or_eq_top S with h | h
  · intro a ha
    have h1 : a ∈ S.toSubmodule := LinearMap.mem_ker.2 ha
    rw [h] at h1
    exact (Submodule.mem_bot ℂ).1 h1
  · exfalso
    apply hC0
    refine LinearMap.ext fun a => ?_
    have h1 : a ∈ S.toSubmodule := by rw [h]; trivial
    exact LinearMap.mem_ker.1 h1

theorem eq_of_fixed (π : Representation ℂ G Y) (hπ : IsSmooth π) {U : Subgroup G} (hUc : IsCompact (U : Set G))
    (hUo : IsOpen (U : Set G)) (l l' : Y →ₗ⋆[ℂ] ℂ) (hl : ∀ u ∈ U, ∀ z, l (π u z) = l z)
    (hl' : ∀ u ∈ U, ∀ z, l' (π u z) = l' z) (h : ∀ z ∈ fixedVectors π U, l z = l' z) : l = l' := by
  have hk : ∀ m : Y →ₗ⋆[ℂ] ℂ, (∀ u ∈ U, ∀ z, m (π u z) = m z) → coinvariantsKer π U ≤ LinearMap.ker m := by
    intro m hm
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨k, v⟩, rfl⟩
    simp [hm k k.2 v]
  refine LinearMap.ext fun z => ?_
  have hs := sub_fixedProj_mem hπ hUc hUo z
  have e1 : l z = l (fixedProj π hπ hUc hUo z) := by
    rw [← sub_eq_zero, ← map_sub]; exact hk l hl hs
  have e2 : l' z = l' (fixedProj π hπ hUc hUo z) := by
    rw [← sub_eq_zero, ← map_sub]; exact hk l' hl' hs
  rw [e1, e2, h _ (fixedProj π hπ hUc hUo z).2]

theorem admissible_and_equiv (σ : Representation ℂ G X) (π : Representation ℂ G Y)
    (hσ : IsSmooth σ) (hσi : σ.IsIrreducible) (hπ : IsAdmissible π) (hπi : π.IsIrreducible)
    (B : X →ₗ[ℂ] Y →ₗ⋆[ℂ] ℂ) (hB : ∀ g x y, B (σ g x) (π g y) = B x y) (hB0 : B ≠ 0)
    (C : Y →ₗ[ℂ] Y →ₗ⋆[ℂ] ℂ) (hC : ∀ g x y, C (π g x) (π g y) = C x y) (hC0 : C ≠ 0) :
    IsAdmissible σ ∧ Nonempty (σ.Equiv π) := by
  have hker := leftKer_eq_zero π hπi C hC hC0
  have huniq : ∀ a a', C a = C a' → a = a' := fun a a' h =>
    sub_eq_zero.1 (hker _ (by rw [map_sub, h, sub_self]))
  have hex : ∀ x, ∃ a, C a = B x := by
    intro x
    obtain ⟨U, hUc, hUo, hxU⟩ := (isSmooth_iff_forall_exists σ).1 hσ x
    haveI : FiniteDimensional ℂ (fixedVectors π U) := hπ.2 U hUc hUo
    set E := fixedVectors π U with hE
    have hCinv : ∀ a ∈ E, ∀ u ∈ U, ∀ z, C a (π u z) = C a z := by
      intro a ha u hu z
      rw [← hC u a z, ha u hu]
    have hBinv : ∀ u ∈ U, ∀ z, B x (π u z) = B x z := by
      intro u hu z
      rw [← hB u x z, hxU u hu]
    let L : E →ₗ[ℂ] (E →ₗ⋆[ℂ] ℂ) :=
      { toFun := fun a => (C a).comp E.subtype
        map_add' := fun a a' => by ext z; simp
        map_smul' := fun c a => by ext z; simp }
    have hL : Function.Injective L := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro a ha
      have h0 : C a = 0 := eq_of_fixed π hπ.1 hUc hUo (C a) 0 (hCinv a a.2) (fun _ _ _ => rfl)
        (fun z hz => by
          have := LinearMap.congr_fun ha ⟨z, hz⟩
          simpa [L] using this)
      exact Subtype.ext (hker _ h0)
    obtain ⟨hfin, hle⟩ := conjDual_finite E
    have heq : Module.finrank ℂ E = Module.finrank ℂ (E →ₗ⋆[ℂ] ℂ) :=
      le_antisymm (LinearMap.finrank_le_finrank_of_injective hL) hle
    have hsurj : Function.Surjective L := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).1 hL
    obtain ⟨a, ha⟩ := hsurj ((B x).comp E.subtype)
    refine ⟨a, eq_of_fixed π hπ.1 hUc hUo (C a) (B x) (hCinv a a.2) hBinv fun z hz => ?_⟩
    have := LinearMap.congr_fun ha ⟨z, hz⟩
    simpa [L] using this
  choose T0 hT0 using hex
  let T : X →ₗ[ℂ] Y :=
    { toFun := T0
      map_add' := fun x x' => huniq _ _ (by rw [hT0, map_add (f := _), map_add (f := _), hT0, hT0])
      map_smul' := fun c x => huniq _ _ (by rw [hT0, map_smul, map_smul, hT0, RingHom.id_apply]) }
  have hTint : ∀ g x, T (σ g x) = π g (T x) := by
    intro g x
    refine huniq _ _ ?_
    refine LinearMap.ext fun z => ?_
    show C (T0 (σ g x)) z = C (π g (T0 x)) z
    rw [hT0, ← act_inv π g z, hC, act_inv π g z, hT0, ← hB g x (π g⁻¹ z), act_inv π g z]
  let f : Representation.IntertwiningMap σ π := ⟨T, fun g => LinearMap.ext fun x => hTint g x⟩
  obtain ⟨x₀, hx₀⟩ : ∃ x, B x ≠ 0 := by
    by_contra hcon
    exact hB0 (LinearMap.ext fun x => not_not.1 fun hx => hcon ⟨x, hx⟩)
  have hf0 : f ≠ 0 := by
    intro h
    apply hx₀
    have h1 : T0 x₀ = 0 := by
      have := congrArg (fun F : Representation.IntertwiningMap σ π => F x₀) h
      exact this
    rw [← hT0, h1, map_zero]
  haveI := hσi
  haveI := hπi
  rcases Representation.IsIrreducible.bijective_or_eq_zero f with hb | h0
  · refine ⟨⟨hσ, fun U hUc hUo => ?_⟩, ⟨Representation.IntertwiningMap.ofBijective f hb⟩⟩
    haveI : FiniteDimensional ℂ (fixedVectors π U) := hπ.2 U hUc hUo
    exact Module.Finite.of_injective (fixedMap σ f U) (fixedMap_injective σ hb.1)
  · exact absurd h0 hf0

end PositivityTheory.TfC.OccursIff.Pair
end

-- bundled from Development.WeilBound.CuspidalAdmissibility.OccTrace
section
open MeasureTheory GroundTheory.Automorphic

namespace PositivityTheory.TfC.OccursIff.Trace

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G]
  {X : Type} [AddCommGroup X] [Module ℂ X]


omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G] in
theorem orbit_isLocallyConstant (ρ : Representation ℂ G X) (hρ : IsSmooth ρ) (v : X) :
    IsLocallyConstant fun g => ρ g v := by
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  refine ⟨(fun h => g⁻¹ * h) ⁻¹' (stabilizerOf ρ v : Set G), (hρ v).preimage (by fun_prop), ?_, fun h hh => ?_⟩
  · show g⁻¹ * g ∈ stabilizerOf ρ v
    rw [inv_mul_cancel]
    exact one_mem _
  · have hh' : ρ (g⁻¹ * h) v = v := hh
    calc ρ h v = ρ g (ρ (g⁻¹ * h) v) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
      _ = ρ g v := by rw [hh']

omit [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
theorem exists_vec (m : Measure G) [m.IsHaarMeasure] (ρ : Representation ℂ G X) (hρ : IsSmooth ρ) (φ : G → ℂ)
    (hφ : IsLocallyConstant φ) (hφc : HasCompactSupport φ) (v : X) :
    ∃ a : X, ∀ l : Module.Dual ℂ X, l a = ∫ g, φ g * l (ρ g v) ∂m := by
  classical
  have hloc := orbit_isLocallyConstant ρ hρ v
  have hS : ((fun g => ρ g v) '' tsupport φ).Finite := by
    haveI : CompactSpace (tsupport φ) := isCompact_iff_compactSpace.1 hφc
    have h1 := (hloc.comp_continuous (continuous_subtype_val (p := (· ∈ tsupport φ)))).range_finite
    rwa [Set.range_comp, Subtype.range_coe] at h1
  set S := hS.toFinset
  let E : X → Set G := fun s => {g | ρ g v = s}
  have hE : ∀ s, MeasurableSet (E s) := fun s => (hloc.isOpen_fiber s).measurableSet
  have hφi : Integrable φ m := hφ.continuous.integrable_of_hasCompactSupport hφc
  refine ⟨∑ s ∈ S, (∫ g, (E s).indicator φ g ∂m) • s, fun l => ?_⟩
  have hpt : ∀ g, φ g * l (ρ g v) = ∑ s ∈ S, (E s).indicator φ g * l s := by
    intro g
    by_cases hg : φ g = 0
    · simp [hg, Set.indicator_apply]
    · have hgS : ρ g v ∈ S := hS.mem_toFinset.2 ⟨g, subset_tsupport φ hg, rfl⟩
      rw [Finset.sum_eq_single (ρ g v)]
      · simp [E]
      · intro s _ hs
        simp [E, Ne.symm hs]
      · intro h
        exact absurd hgS h
  have hfun : (fun g => φ g * l (ρ g v)) = fun g => ∑ s ∈ S, (E s).indicator φ g * l s := funext hpt
  rw [hfun, integral_finsetSum]
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [map_sum, map_smul, smul_eq_mul, integral_mul_const]
  · intro s _
    exact (hφi.indicator (hE s)).mul_const (l s)

theorem exists_integralOp (m : Measure G) [m.IsHaarMeasure] (ρ : Representation ℂ G X) (hρ : IsAdmissible ρ)
    (φ : G → ℂ) (hφ : IsLocallyConstant φ) (hφc : HasCompactSupport φ) :
    ∃ A : X →ₗ[ℂ] X, (∀ (v : X) (l : Module.Dual ℂ X), Integrable (fun g => φ g * l (ρ g v)) m ∧
      l (A v) = ∫ g, φ g * l (ρ g v) ∂m) ∧ FiniteDimensional ℂ (LinearMap.range A) := by
  classical
  have hint : ∀ v (l : Module.Dual ℂ X), Integrable (fun g => φ g * l (ρ g v)) m := fun v l =>
    (hφ.continuous.mul ((orbit_isLocallyConstant ρ hρ.1 v).comp l).continuous).integrable_of_hasCompactSupport
      hφc.mul_right
  choose A0 hA0 using exists_vec m ρ hρ.1 φ hφ hφc
  have huniq : ∀ a b : X, (∀ l : Module.Dual ℂ X, l a = l b) → a = b := fun a b h =>
    sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff ℂ (a - b)).1 fun l => by rw [map_sub, h, sub_self])
  let A : X →ₗ[ℂ] X :=
    { toFun := A0
      map_add' := fun v v' => huniq _ _ fun l => by
        rw [map_add (f := _), hA0, hA0, hA0, ← integral_add (hint v l) (hint v' l)]
        congr 1
        funext g
        rw [map_add (f := _), map_add (f := _), mul_add]
      map_smul' := fun c v => huniq _ _ fun l => by
        rw [map_smul, hA0, hA0, RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
        congr 1
        funext g
        rw [map_smul, map_smul, smul_eq_mul]
        ring }
  obtain ⟨K, hKc, hK⟩ := exists_forall_mul_left (R := ℂ) (E := ℂ)
    (show φ ∈ locallyConstantCompactSupport G ℂ ℂ from ⟨hφ, hφc⟩)
  refine ⟨A, fun v l => ⟨hint v l, hA0 v l⟩, ?_⟩
  haveI : FiniteDimensional ℂ (fixedVectors ρ (K : Subgroup G)) := hρ.2 K hKc K.isOpen
  refine Submodule.finiteDimensional_of_le (S₂ := fixedVectors ρ (K : Subgroup G)) ?_
  rintro _ ⟨v, rfl⟩ k hk
  refine huniq _ _ fun l => ?_
  have h1 := hA0 v (l ∘ₗ ρ k)
  rw [LinearMap.comp_apply] at h1
  show l (ρ k (A0 v)) = l (A0 v)
  rw [h1, hA0]
  have e : (fun g => φ g * (l ∘ₗ ρ k) (ρ g v)) = fun g => (fun h => φ (k⁻¹ * h) * l (ρ h v)) (k * g) := by
    funext g
    simp only [inv_mul_cancel_left, LinearMap.comp_apply]
    rw [← Module.End.mul_apply, ← map_mul]
  rw [e, integral_mul_left_eq_self (fun h => φ (k⁻¹ * h) * l (ρ h v)) k]
  congr 1
  funext g
  rw [hK k⁻¹ (inv_mem hk) g]

end PositivityTheory.TfC.OccursIff.Trace
end

