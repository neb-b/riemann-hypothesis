module

public import Mathlib
public import GroundTheory.AutomorphicForms.Bundle0021
public import GroundTheory.AutomorphicForms.Bundle0020
public import GroundTheory.LocalFields.LocalFourierHaar
public import GroundTheory.LocalFields.Bundle0009
public import GroundTheory.LocalFields.LocalZetaEpsilon
public import GroundTheory.LocalFields.ExistsUnitFiltrationUnitsLeRangeNormUnits

@[expose] public section

-- bundled from GroundTheory.AutomorphicForms.GL2.GJLeviSupport
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal Parabolic ValuativeRel

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}

theorem exists_bound_of_coeff_ne_zero (hσ : IsSmooth σ) (hc : IsCuspidal σ) (w : W)
    {ℓ : Module.Dual ℂ W} (hℓ : ℓ ∈ smoothVectors (Representation.dual σ)) :
    ∃ N : ℕ, ∀ (μ : Fin n → ℤ) (k₁ k₂ : levi F n β), (k₁ : GL (Fin n) F) ∈ integralGL F n →
      (k₂ : GL (Fin n) F) ∈ integralGL F n →
      ℓ (σ (k₁ * ⟨Cartan.diagPow F n μ, diagPow_mem_levi μ⟩ * k₂) w) ≠ 0 →
      ∃ c : Fin n → ℤ, (∀ i j, β i = β j → c i = c j) ∧ ∀ i, c i ≤ μ i ∧ μ i ≤ c i + N := by
  classical
  let KM : ℕ → Subgroup (levi F n β) := fun m => (congruenceSubgroup F n m).subgroupOf (levi F n β)
  have hKMo : ∀ m, IsOpen (KM m : Set (levi F n β)) := fun m =>
    isOpen_subgroupOf_levi (isOpen_congruenceSubgroup F n m)
  have hKManti : ∀ {m m' : ℕ}, m ≤ m' → KM m' ≤ KM m := fun h x hx =>
    Subgroup.mem_subgroupOf.2 (congruenceSubgroup_antitone F n h (Subgroup.mem_subgroupOf.1 hx))

  obtain ⟨m₀, hm₀⟩ := exists_subgroupOf_congruenceSubgroup_subset
    ((hσ w).mem_nhds (one_mem (stabilizerOf σ w)))
  obtain ⟨m₁, hm₁⟩ := exists_subgroupOf_congruenceSubgroup_subset
    ((mem_smoothVectors.1 hℓ).mem_nhds (one_mem (stabilizerOf (Representation.dual σ) ℓ)))
  set m := max m₀ m₁ with hmdef
  set K := KM m with hKdef
  have hwK : w ∈ fixedVectors σ K := fun k hk => hm₀ (hKManti (le_max_left _ _) hk)
  have hℓK : ∀ k ∈ K, ∀ x, ℓ (σ k x) = ℓ x := mem_fixedVectors_dual.1 fun k hk =>
    hm₁ (hKManti (le_max_right _ _) hk)

  let K₀ : Subgroup (levi F n β) := (integralGL F n).subgroupOf (levi F n β)
  have hK₀c : IsCompact (K₀ : Set (levi F n β)) :=
    isCompact_subgroupOf_levi (isCompact_integralGL F n)
  have : CompactSpace K₀ := isCompact_iff_compactSpace.1 hK₀c
  have hQ : Finite (K₀ ⧸ K.subgroupOf K₀) := by
    refine Subgroup.quotient_finite_of_isOpen _ ?_
    rw [Subgroup.coe_subgroupOf]
    exact (hKMo m).preimage continuous_subtype_val
  have := Fintype.ofFinite (K₀ ⧸ K.subgroupOf K₀)
  let R : Finset (levi F n β) :=
    Finset.univ.image fun q : K₀ ⧸ K.subgroupOf K₀ => ((Quotient.out q : K₀) : levi F n β)
  have hR : ∀ k ∈ K₀, ∃ r ∈ R, σ k w = σ r w := by
    intro k hk
    refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ (QuotientGroup.mk (⟨k, hk⟩ : K₀))), ?_⟩
    exact act_eq_of_mk_eq σ hwK (a := ⟨k, hk⟩)
      (b := Quotient.out (QuotientGroup.mk (⟨k, hk⟩ : K₀) : K₀ ⧸ K.subgroupOf K₀))
      (QuotientGroup.out_eq' _).symm
  have hnorm : ∀ k ∈ K₀, ∀ x ∈ K, k * x * k⁻¹ ∈ K := fun k hk x hx =>
    Subgroup.mem_subgroupOf.2 (by
      simpa using conj_mem_congruenceSubgroup F n (Subgroup.mem_subgroupOf.1 hk)
        (Subgroup.mem_subgroupOf.1 hx))

  let V₂ : Finset W := R.image fun r => σ r w

  have hU : ∀ S : Finset (Fin n), (∃ i j, β i = β j ∧ i ∈ S ∧ j ∉ S) → ∀ x : W,
      ∃ U : Finset (levi F n β), (∀ u ∈ U, (u : GL (Fin n) F) ∈ unipotentRadical F n (splitFun S)) ∧
        x ∈ Submodule.span ℂ {y | ∃ u ∈ U, ∃ z, y = σ u z - z} :=
    fun S hS x => exists_finset_of_isCuspidal hc hS x
  choose! Uf hUf1 hUf2 using hU
  let Uall : Finset (levi F n β) := Finset.univ.biUnion fun S : Finset (Fin n) => V₂.biUnion (Uf S)
  obtain ⟨t, ht⟩ := exists_pow_mul_mem_of_isCompact F n
    (((Uall.image fun u : levi F n β => u.1) ∪ (Uall.image fun u : levi F n β => u.1⁻¹) :
      Finset (GL (Fin n) F)) : Set (GL (Fin n) F)).toFinite.isCompact
  have hbu : ∀ u ∈ Uall, ∀ i j, (uniformizer F : F) ^ t * (u : GL (Fin n) F) i j ∈ 𝒪[F] :=
    fun u hu => ht _ (by simp only [Finset.coe_union, Finset.coe_image, Set.mem_union,
      Set.mem_image, Finset.mem_coe]; exact Or.inl ⟨u, hu, rfl⟩)
  have hbu' : ∀ u ∈ Uall, ∀ i j,
      (uniformizer F : F) ^ t * ((u : GL (Fin n) F)⁻¹ : GL (Fin n) F) i j ∈ 𝒪[F] :=
    fun u hu => ht _ (by simp only [Finset.coe_union, Finset.coe_image, Set.mem_union,
      Set.mem_image, Finset.mem_coe]; exact Or.inr ⟨u, hu, rfl⟩)
  set C : ℤ := ((t + m : ℕ) : ℤ) + 1 with hCdef
  have hC : ((t + m : ℕ) : ℤ) < C := lt_add_one _
  have hC0 : 0 < C := by positivity
  refine ⟨(n * C).toNat, ?_⟩
  intro μ k₁ k₂ hk₁ hk₂ hne
  set a : levi F n β := ⟨Cartan.diagPow F n μ, diagPow_mem_levi μ⟩ with hadef
  have hk₁K : k₁ ∈ K₀ := Subgroup.mem_subgroupOf.2 hk₁
  have hk₂K : k₂ ∈ K₀ := Subgroup.mem_subgroupOf.2 hk₂
  obtain ⟨r₂, hr₂, hr₂v⟩ := hR _ hk₂K
  have hwV : σ r₂ w ∈ V₂ := Finset.mem_image_of_mem _ hr₂
  rcases gap_or_bounded (β := β) μ hC0 with
    ⟨θ, b, ⟨i, hib, hiθ⟩, ⟨j, hjb, hjθ⟩, hgap⟩ | hbd
  ·
    exfalso
    apply hne
    set S : Finset (Fin n) := Finset.univ.filter fun j => β j = b ∧ θ ≤ μ j with hSdef
    have hS : ∃ i j, β i = β j ∧ i ∈ S ∧ j ∉ S :=
      ⟨i, j, hib.trans hjb.symm, by simp [S, hib, hiθ], by simp [S, hjb, not_le.2 hjθ]⟩
    have hsp := hUf2 S hS (σ r₂ w)
    have hker : Submodule.span ℂ {y | ∃ u ∈ Uf S (σ r₂ w), ∃ z, y = σ u z - z} ≤
        LinearMap.ker (ℓ ∘ₗ σ k₁ ∘ₗ σ a) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨u, hu, x, rfl⟩
      have huA : u ∈ Uall := Finset.mem_biUnion.2 ⟨S, Finset.mem_univ _,
        Finset.mem_biUnion.2 ⟨σ r₂ w, hwV, hu⟩⟩
      have huN := hUf1 S hS (σ r₂ w) u hu
      have hconj : a * u * a⁻¹ ∈ K := by
        refine Subgroup.mem_subgroupOf.2 ?_
        have hco : ((a * u * a⁻¹ : levi F n β) : GL (Fin n) F) =
            Cartan.diagPow F n μ * (u : GL (Fin n) F) * (Cartan.diagPow F n μ)⁻¹ := rfl
        rw [hco]
        exact diagPow_conj_mem_congruenceSubgroup hC (apply_eq_or_gap hgap u.2 huN)
          (apply_eq_or_gap hgap ((levi F n β).inv_mem u.2)
            ((unipotentRadical F n _).inv_mem huN)) (hbu u huA) (hbu' u huA)
      have hconj' : k₁ * (a * u * a⁻¹) * k₁⁻¹ ∈ K := hnorm k₁ hk₁K _ hconj
      have h1 : σ k₁ (σ a (σ u x)) = σ (k₁ * (a * u * a⁻¹) * k₁⁻¹) (σ k₁ (σ a x)) := by
        simp only [← Module.End.mul_apply, ← map_mul]
        congr 2
        group
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
        map_sub]
      rw [h1, hℓK _ hconj', sub_self]
    have h0 := hker hsp
    rw [LinearMap.mem_ker] at h0
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hr₂v]
    simpa using h0
  ·
    let cb : α → ℤ := fun b => if h : ∃ k, β k = b then
      ((Finset.univ.filter fun k => β k = b).image μ).min' (by
        obtain ⟨k, hk⟩ := h
        exact ⟨μ k, Finset.mem_image_of_mem _ (by simp [hk])⟩) else 0
    have hcb_le : ∀ k, cb (β k) ≤ μ k := by
      intro k
      simp only [cb, dif_pos (⟨k, rfl⟩ : ∃ j, β j = β k)]
      exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ (by simp))
    have hcb_mem : ∀ j, ∃ k, β k = β j ∧ cb (β j) = μ k := by
      intro j
      simp only [cb, dif_pos (⟨j, rfl⟩ : ∃ k, β k = β j)]
      obtain ⟨k, hk, hkeq⟩ := Finset.mem_image.1
        (Finset.min'_mem ((Finset.univ.filter fun k => β k = β j).image μ) _)
      exact ⟨k, (Finset.mem_filter.1 hk).2, hkeq.symm⟩
    refine ⟨fun j => cb (β j), fun i j h => by simp only [h], fun i => ⟨hcb_le i, ?_⟩⟩
    obtain ⟨k, hk, hkeq⟩ := hcb_mem i
    have h1 := hbd i k hk.symm
    have h2 : (((n * C).toNat : ℕ) : ℤ) = n * C := Int.toNat_of_nonneg (by positivity)
    rw [h2]
    show μ i ≤ cb (β i) + n * C
    rw [hkeq]
    exact h1.le

end GodementJacquet

end GroundTheory.Automorphic
end
end

-- bundled from GroundTheory.AutomorphicForms.GL2.GJZetaDefs
section
noncomputable section

namespace GroundTheory.Automorphic

namespace GodementJacquet

open Matrix GLnLocal ValuativeRel Topology Filter

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

def IsSchwartzBruhat (Φ : Matrix (Fin n) (Fin n) F → ℂ) : Prop :=
  IsLocallyConstant Φ ∧ HasCompactSupport Φ

def absDet (g : GL (Fin n) F) : ℝ :=
  (LocalField.modulus ((g : Matrix (Fin n) (Fin n) F).det) : ℝ)

def detPow (g : GL (Fin n) F) (s : ℂ) : ℂ :=
  (absDet g : ℂ) ^ s


variable (F) in
def qs (s : ℂ) : ℂ :=
  (LocalField.residueCard F : ℂ) ^ (-s)

def ordDet (g : GL (Fin n) F) : ℤ :=
  LocalField.ord ((g : Matrix (Fin n) (Fin n) F).det)

def IsLeviSchwartz {α : Type*} (β : Fin n → α) (Ψ : Matrix (Fin n) (Fin n) F → ℂ) : Prop :=
  ∃ r A : ℕ,
    (∀ X Y : Matrix (Fin n) (Fin n) F, (∀ i j, β i ≠ β j → X i j = 0) →
      (∀ i j, β i ≠ β j → Y i j = 0) →
      (∀ i j, ∃ a ∈ 𝒪[F], Y i j = (uniformizer F : F) ^ r * a) → Ψ (X + Y) = Ψ X) ∧
    (∀ X : Matrix (Fin n) (Fin n) F, (∀ i j, β i ≠ β j → X i j = 0) → Ψ X ≠ 0 →
      ∀ i j, (uniformizer F : F) ^ A * X i j ∈ 𝒪[F])

theorem mem_valBall_iff_exists {r : ℕ} {y : F} :
    y ∈ LocalField.valBall F r ↔ ∃ a ∈ 𝒪[F], y = (uniformizer F : F) ^ r * a := by
  have hϖ : (uniformizer F : F) ≠ 0 := Cartan.uniformizer_ne_zero F
  have hord : LocalField.ord (uniformizer F : F) = 1 :=
    LocalField.ord_uniformizer (irreducible_uniformizer F)
  have hϖr : (uniformizer F : F) ^ r ∈ LocalField.valBall F r := by
    rw [LocalField.mem_valBall_iff_le_ord (pow_ne_zero _ hϖ), LocalField.ord_pow hϖ, hord]
    simp
  constructor
  · intro hy
    by_cases h0 : y = 0
    · exact ⟨0, zero_mem _, by rw [h0, mul_zero]⟩
    refine ⟨y / (uniformizer F : F) ^ r, ?_, by field_simp⟩
    have hne : y / (uniformizer F : F) ^ r ≠ 0 := div_ne_zero h0 (pow_ne_zero _ hϖ)
    rw [← LocalField.mem_valBall_zero_iff, LocalField.mem_valBall_iff_le_ord hne, div_eq_mul_inv,
      LocalField.ord_mul h0 (inv_ne_zero (pow_ne_zero _ hϖ)),
      LocalField.ord_inv (pow_ne_zero _ hϖ), LocalField.ord_pow hϖ, hord]
    have := (LocalField.mem_valBall_iff_le_ord h0).1 hy
    linarith
  · rintro ⟨a, ha, rfl⟩
    have := LocalField.mul_mem_valBall hϖr (LocalField.mem_valBall_zero_iff.2 ha)
    simpa using this

theorem exists_valBall_subset {S : Set (Matrix (Fin n) (Fin n) F)}
    (hS : S ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) F)) :
    ∃ r : ℕ, {Y : Matrix (Fin n) (Fin n) F | ∀ i j, Y i j ∈ LocalField.valBall F r} ⊆ S := by
  classical
  have hS' : S ∈ Filter.pi fun _ : Fin n => 𝓝 (0 : Fin n → F) := by
    rw [← nhds_pi]; exact hS
  obtain ⟨I, t, ht, hIt⟩ := Filter.mem_pi'.1 hS'
  have ht' : ∀ i, t i ∈ Filter.pi fun _ : Fin n => 𝓝 (0 : F) := fun i => by
    rw [← nhds_pi]; exact ht i
  choose J u hu hJu using fun i => Filter.mem_pi'.1 (ht' i)
  have hr : ∀ i j, ∃ r : ℤ, (LocalField.valBall F r : Set F) ⊆ u i j := fun i j => by
    obtain ⟨r, -, hr⟩ := LocalField.hasBasis_nhds_zero_valBall.mem_iff.1 (hu i j)
    exact ⟨r, hr⟩
  choose r hr using hr
  refine ⟨Finset.univ.sup fun p : Fin n × Fin n => (r p.1 p.2).toNat, fun Y hY => hIt ?_⟩
  intro i _
  refine hJu i ?_
  intro j _
  refine hr i j (LocalField.valBall_antitone (by
    have : (r i j).toNat ≤ Finset.univ.sup fun p : Fin n × Fin n => (r p.1 p.2).toNat :=
      Finset.le_sup (f := fun p : Fin n × Fin n => (r p.1 p.2).toNat) (Finset.mem_univ (i, j))
    omega) (hY i j))

theorem exists_valBall_of_isCompact {K : Set (Matrix (Fin n) (Fin n) F)} (hK : IsCompact K) :
    ∃ A : ℕ, ∀ X ∈ K, ∀ i j, X i j ∈ LocalField.valBall F (-(A : ℤ)) := by
  classical
  let U : ℕ → Set (Matrix (Fin n) (Fin n) F) :=
    fun m => {X | ∀ i j, X i j ∈ LocalField.valBall F (-(m : ℤ))}
  have hU : ∀ m, IsOpen (U m) := fun m => by
    have : U m = ⋂ i, ⋂ j, (fun X : Matrix (Fin n) (Fin n) F => X i j) ⁻¹'
        (LocalField.valBall F (-(m : ℤ)) : Set F) := by
      ext X; simp [U]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (LocalField.isOpen_valBall _).preimage ((continuous_apply j).comp (continuous_apply i))
  have hcover : K ⊆ ⋃ m, U m := by
    intro X _
    choose m hm using fun p : Fin n × Fin n => LocalField.exists_mem_valBall_neg_nat (X p.1 p.2)
    refine Set.mem_iUnion.2 ⟨Finset.univ.sup m, fun i j => LocalField.valBall_antitone (by
      have := Finset.le_sup (f := m) (Finset.mem_univ (i, j))
      omega) (hm (i, j))⟩
  have hdir : Directed (· ⊆ ·) U := by
    intro a b
    refine ⟨max a b, fun X hX i j => LocalField.valBall_antitone ?_ (hX i j),
      fun X hX i j => LocalField.valBall_antitone ?_ (hX i j)⟩ <;> omega
  obtain ⟨A, hA⟩ := hK.elim_directed_cover U hU hcover hdir
  exact ⟨A, fun X hX => hA hX⟩

theorem IsSchwartzBruhat.exists_invariant {Φ : Matrix (Fin n) (Fin n) F → ℂ}
    (hΦ : IsSchwartzBruhat Φ) :
    ∃ r A : ℕ,
      (∀ X Y : Matrix (Fin n) (Fin n) F, (∀ i j, ∃ a ∈ 𝒪[F], Y i j = (uniformizer F : F) ^ r * a) →
        Φ (X + Y) = Φ X) ∧
      (∀ X : Matrix (Fin n) (Fin n) F, Φ X ≠ 0 → ∀ i j, (uniformizer F : F) ^ A * X i j ∈ 𝒪[F]) := by
  classical
  obtain ⟨hlc, hcs⟩ := hΦ
  set K := tsupport Φ
  have hK : IsCompact K := hcs

  let L : ℕ → Set (Matrix (Fin n) (Fin n) F) :=
    fun r => {Y | ∀ i j, Y i j ∈ LocalField.valBall F r}
  have hLadd : ∀ r, ∀ Y ∈ L r, ∀ Z ∈ L r, Y + Z ∈ L r := fun r Y hY Z hZ i j =>
    add_mem (hY i j) (hZ i j)
  have hLneg : ∀ r, ∀ Y ∈ L r, -Y ∈ L r := fun r Y hY i j => by
    simpa using neg_mem (hY i j)
  have hLanti : ∀ {r r'}, r ≤ r' → L r' ⊆ L r := fun h Y hY i j =>
    LocalField.valBall_antitone (by exact_mod_cast h) (hY i j)
  have hLopen : ∀ r, IsOpen (L r) := fun r => by
    have : L r = ⋂ i, ⋂ j, (fun X : Matrix (Fin n) (Fin n) F => X i j) ⁻¹'
        (LocalField.valBall F (r : ℤ) : Set F) := by
      ext X; simp [L]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (LocalField.isOpen_valBall _).preimage ((continuous_apply j).comp (continuous_apply i))

  let Wr : ℕ → Set (Matrix (Fin n) (Fin n) F) := fun r => {X | ∀ Y ∈ L r, Φ (X + Y) = Φ X}
  have hWopen : ∀ r, IsOpen (Wr r) := by
    intro r
    rw [isOpen_iff_mem_nhds]
    intro X hX
    have hnhds : {Z | Z - X ∈ L r} ∈ 𝓝 X :=
      ((hLopen r).preimage (continuous_id.sub continuous_const)).mem_nhds (by
        show X - X ∈ L r
        rw [sub_self]
        exact fun i j => zero_mem (LocalField.valBall F (r : ℤ)))
    refine Filter.mem_of_superset hnhds fun Z hZ Y hY => ?_
    have h1 := hX (Z - X + Y) (hLadd r _ hZ _ hY)
    have h2 := hX (Z - X) hZ
    rw [show X + (Z - X + Y) = Z + Y by abel, show X + (Z - X) = Z by abel] at *
    rw [h1, h2]
  have hcover : K ⊆ ⋃ r, Wr r := by
    intro X _
    have hmem : (fun Y => X + Y) ⁻¹' (Φ ⁻¹' {Φ X}) ∈ 𝓝 (0 : Matrix (Fin n) (Fin n) F) := by
      refine (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds ?_
      show Φ ⁻¹' {Φ X} ∈ 𝓝 (X + 0)
      rw [add_zero]
      exact (hlc.isOpen_fiber (Φ X)).mem_nhds rfl
    obtain ⟨r, hr⟩ := exists_valBall_subset hmem
    exact Set.mem_iUnion.2 ⟨r, fun Y hY => hr hY⟩
  have hdir : Directed (· ⊆ ·) Wr := by
    intro a b
    refine ⟨max a b, fun X hX Y hY => hX Y (hLanti (le_max_left a b) hY),
      fun X hX Y hY => hX Y (hLanti (le_max_right a b) hY)⟩
  obtain ⟨r, hr⟩ := hK.elim_directed_cover Wr hWopen hcover hdir
  obtain ⟨A, hA⟩ := exists_valBall_of_isCompact hK
  have hϖ : (uniformizer F : F) ≠ 0 := Cartan.uniformizer_ne_zero F
  refine ⟨r, A, fun X Y hY => ?_, fun X hX i j => ?_⟩
  · have hYL : Y ∈ L r := fun i j => mem_valBall_iff_exists.2 (hY i j)
    by_cases hXK : X ∈ K
    · exact hr hXK Y hYL
    by_cases hXYK : X + Y ∈ K
    · have := hr hXYK (-Y) (hLneg r Y hYL)
      rw [add_neg_cancel_right] at this
      exact this.symm
    · rw [image_eq_zero_of_notMem_tsupport hXK, image_eq_zero_of_notMem_tsupport hXYK]
  · have hXK : X ∈ K := subset_tsupport _ hX
    have h1 := hA X hXK i j
    have h2 : (uniformizer F : F) ^ A ∈ LocalField.valBall F (A : ℤ) :=
      (mem_valBall_iff_exists (r := A)).2 ⟨1, one_mem _, by rw [mul_one]⟩
    have := LocalField.mul_mem_valBall h2 h1
    rw [add_neg_cancel] at this
    exact LocalField.mem_valBall_zero_iff.1 this

theorem detPow_eq_qs_zpow (g : GL (Fin n) F) (s : ℂ) : detPow g s = qs F s ^ ordDet g := by
  have hd : (g : Matrix (Fin n) (Fin n) F).det ≠ 0 := (Matrix.GeneralLinearGroup.det g).ne_zero
  rw [detPow, absDet, qs, ordDet, LocalField.modulus_cpow_eq_qcpow hd, LocalField.qcpow_zpow]
  congr 1
  ring

theorem qs_ne_zero (s : ℂ) : qs F s ≠ 0 := by
  rw [qs]
  exact Complex.cpow_ne_zero_iff.2 (Or.inl (Nat.cast_ne_zero.2 LocalField.residueCard_ne_zero))

theorem norm_qs (s : ℂ) : ‖qs F s‖ = (LocalField.residueCard F : ℝ) ^ (-s.re) := by
  rw [qs, Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero LocalField.residueCard_ne_zero)]
  simp

end GodementJacquet

end GroundTheory.Automorphic
end
end

