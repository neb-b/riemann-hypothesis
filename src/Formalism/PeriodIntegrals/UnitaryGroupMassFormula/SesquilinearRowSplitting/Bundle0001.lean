module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.CoordStep

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.DualFamilyExists
section
open NumberField Module

namespace PI.SRW

theorem dualFamilyExists : CoordStep := by
  intro E V _ _ _ n g hg
  classical
  let b := Basis.span hg
  choose c hc using fun i => LinearMap.exists_extend (b.coord i)
  refine ⟨c, fun i j => ?_⟩
  have hmem : g j ∈ Submodule.span E (Set.range g) := Submodule.subset_span ⟨j, rfl⟩
  have h1 : c i (g j) = b.coord i ⟨g j, hmem⟩ := by
    rw [← hc i]; rfl
  have h2 : (⟨g j, hmem⟩ : Submodule.span E (Set.range g)) = b j := by
    rw [Basis.span_apply]
  rw [h1, h2, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h]

end PI.SRW
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SesquilinearRowSplitting.SesquilinearRepresentation
section
open NumberField Module

namespace PI.SRW

theorem sesquilinearRepresentation : RepStep := by
  intro E V _ _ _ _ _ _ _ _ h hnd Λ hΛ ℓ

  have hsurj : Function.Surjective h := by
    rw [← LinearMap.range_eq_top]
    have hco : (LinearMap.range h).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rw [Submodule.mem_dualCoannihilator] at hy
      rw [Submodule.mem_bot]
      exact hnd.2 y (fun x => hy (h x) ⟨x, rfl⟩)
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := LinearMap.range h), hco,
      Submodule.dualAnnihilator_bot]

  obtain ⟨s, hsΛ, hspan, hli⟩ := exists_linearIndependent E (Λ : Set V)
  classical
  have hs : LinearIndepOn E id s := hli
  let b := Basis.extend hs
  let f : hs.extend (Set.subset_univ s) → E :=
    fun i => if hi : (i : V) ∈ s then ℓ ⟨i, hsΛ hi⟩ else 0
  let φ : V →ₗ[E] E := b.constr E f
  have hφb : ∀ v (hv : v ∈ s), φ v = ℓ ⟨v, hsΛ hv⟩ := by
    intro v hv
    let i : hs.extend (Set.subset_univ s) := ⟨v, Basis.subset_extend hs hv⟩
    calc
      φ v = φ (b i) := congrArg φ (Basis.extend_apply_self hs i).symm
      _ = _ := by simpa only [f, i, dite_eq_left hv] using b.constr_basis E f i

  have hind : ∀ y ∈ Submodule.span (𝓞 E) (s : Set V), ∃ hy : y ∈ Λ, ℓ ⟨y, hy⟩ = φ y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem v hv => exact ⟨hsΛ hv, (hφb v hv).symm⟩
    | zero => exact ⟨zero_mem _, (map_zero ℓ).trans (map_zero φ).symm⟩
    | add u v _ _ hu hv =>
      obtain ⟨hu', eu⟩ := hu
      obtain ⟨hv', ev⟩ := hv
      refine ⟨add_mem hu' hv', ?_⟩
      have e : (⟨u + v, add_mem hu' hv'⟩ : Λ) = ⟨u, hu'⟩ + ⟨v, hv'⟩ := rfl
      rw [e, map_add (f := _), map_add (f := _), eu, ev]
    | smul a u _ hu =>
      obtain ⟨hu', eu⟩ := hu
      refine ⟨Λ.smul_mem a hu', ?_⟩
      have e : (⟨a • u, Λ.smul_mem a hu'⟩ : Λ) = a • ⟨u, hu'⟩ := rfl
      rw [e, map_smul, eu, ← algebraMap_smul E a u, map_smul, Algebra.smul_def, smul_eq_mul]

  have key : ∀ x : Λ, φ x = ℓ x := by
    intro x
    have hxE : (x : V) ∈ Submodule.span E s := by
      rw [hspan]
      exact Submodule.subset_span x.property
    obtain ⟨y, hy, z, hxy⟩ := (IsLocalization.mem_span_iff (nonZeroDivisors (𝓞 E))).mp hxE
    have hzx : (z : 𝓞 E) • (x : V) = y := by
      rw [hxy, ← algebraMap_smul E (z : 𝓞 E), smul_smul, IsLocalization.mk'_spec', map_one,
        one_smul]
    obtain ⟨hyΛ, hℓφ⟩ := hind y hy
    have h1 : ℓ ((z : 𝓞 E) • x) = algebraMap (𝓞 E) E z * ℓ x := by
      rw [map_smul, Algebra.smul_def]
    have h2 : φ ((z : 𝓞 E) • (x : V)) = algebraMap (𝓞 E) E z * φ x := by
      rw [← algebraMap_smul E (z : 𝓞 E) (x : V), map_smul, smul_eq_mul]
    have hzΛ : ((z : 𝓞 E) • x : Λ) = ⟨y, hyΛ⟩ := by
      ext
      exact hzx
    have hne : algebraMap (𝓞 E) E z ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors z.2
    apply mul_left_cancel₀ hne
    rw [← h1, ← h2, hzΛ, hzx, hℓφ]
  obtain ⟨w, hw⟩ := hsurj φ
  exact ⟨w, fun x => by rw [hw, key]⟩

end PI.SRW
end

