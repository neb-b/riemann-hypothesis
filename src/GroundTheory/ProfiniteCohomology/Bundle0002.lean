module

public import Mathlib
public import GroundTheory.ProfiniteCohomology.TorsionDualDefs
public import GroundTheory.ProfiniteCohomology.OpenNormal
public import GroundTheory.ProfiniteCohomology.KummerBasic

@[expose] public section

-- bundled from GroundTheory.ProfiniteCohomology.CharactersDefs
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

section LocallyConstantHom

variable (G : Type*) [Group G] [TopologicalSpace G] (M : Type*) [AddCommGroup M]

def locallyConstantHom : AddSubgroup (Additive G →+ M) where
  carrier := {χ | IsLocallyConstant fun g : G => χ (Additive.ofMul g)}
  zero_mem' := by
    change IsLocallyConstant fun g : G => (0 : Additive G →+ M) (Additive.ofMul g)
    exact IsLocallyConstant.const (0 : M)
  add_mem' {χ ψ} hχ hψ := by
    change IsLocallyConstant fun g : G => (χ + ψ) (Additive.ofMul g)
    exact IsLocallyConstant.add hχ hψ
  neg_mem' {χ} hχ := by
    change IsLocallyConstant fun g : G => (-χ) (Additive.ofMul g)
    exact IsLocallyConstant.neg hχ

def locallyConstantHomQZEquiv : locallyConstantHom G (AddCircle (1 : ℚ)) ≃+ (Additive G →ₜ+ QZ) where
  toFun χ :=
    { toAddMonoidHom := QZ.toAddCircle.symm.toAddMonoidHom.comp χ.1
      continuous_toFun := (IsLocallyConstant.iff_continuous _).1 χ.2 }
  invFun χ := ⟨QZ.toAddCircle.toAddMonoidHom.comp χ.toAddMonoidHom,
    (IsLocallyConstant.iff_continuous (fun x : Additive G => χ x)).2 χ.continuous⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

variable {G} in
@[simp]
theorem locallyConstantHomQZEquiv_apply (χ : locallyConstantHom G (AddCircle (1 : ℚ)))
    (g : Additive G) :
    locallyConstantHomQZEquiv G χ g = QZ.toAddCircle.symm (χ.1 g) :=
  rfl

end LocallyConstantHom

end GroundTheory.ProfCoh
end

-- bundled from GroundTheory.ProfiniteCohomology.Factor
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open Filter Topology

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

theorem exists_openNormalSubgroup_pi_of_isLocallyConstant {ι X : Type*} [Finite ι]
    {f : (ι → G) → X} (hf : IsLocallyConstant f) :
    ∃ U : OpenNormalSubgroup G, ∀ x y : ι → G, (∀ i, (x i)⁻¹ * y i ∈ U) → f x = f y := by

  let O : OpenNormalSubgroup G → Set (ι → G) := fun U =>
    {y | ∀ y' : ι → G, (∀ i, (y i)⁻¹ * y' i ∈ U) → f y' = f y}
  have hO : ∀ U, IsOpen (O U) := by
    intro U
    rw [isOpen_iff_mem_nhds]
    intro y hy
    have hopen : IsOpen ((fun w : ι → G => fun i => (y i)⁻¹ * w i) ⁻¹'
        Set.univ.pi fun _ => (U : Set G)) :=
      (isOpen_set_pi Set.finite_univ fun _ _ => U.toOpenSubgroup.isOpen).preimage
        (continuous_pi fun i => continuous_const.mul (continuous_apply i))
    refine mem_of_superset (hopen.mem_nhds fun i _ => by simp) ?_
    intro w hw y' hy'
    have hw' : ∀ i, (y i)⁻¹ * w i ∈ U := fun i => hw i (Set.mem_univ i)
    have h1 : f y' = f y := hy y' fun i => by
      have := mul_mem (hw' i) (hy' i)
      rwa [mul_assoc, mul_inv_cancel_left] at this
    rw [h1, hy w hw']
  have hcover : Set.univ ⊆ ⋃ U, O U := by
    intro x _
    have hS : (fun w : ι → G => fun i => x i * w i) ⁻¹' (f ⁻¹' {f x}) ∈ 𝓝 (1 : ι → G) :=
      ((hf.isOpen_fiber (f x)).preimage
        (continuous_pi fun i => continuous_const.mul (continuous_apply i))).mem_nhds
        (by simp)
    obtain ⟨U, -, hU⟩ := (OpenNormalSubgroup.hasBasis_nhds_one_pi ι).mem_iff.mp hS
    refine Set.mem_iUnion.mpr ⟨U, fun y' hy' => ?_⟩
    have := hU (show (fun i => (x i)⁻¹ * y' i) ∈ Set.univ.pi fun _ => (U : Set G) from
      fun i _ => hy' i)
    simpa using this
  have hdir : Directed (· ⊆ ·) O := fun U V =>
    ⟨U ⊓ V, fun y hy y' hy' => hy y' fun i => (hy' i).1,
      fun y hy y' hy' => hy y' fun i => (hy' i).2⟩
  obtain ⟨U, hU⟩ := isCompact_univ.elim_directed_cover O hO hcover hdir
  exact ⟨U, fun x y hxy => (hU (Set.mem_univ x) y hxy).symm⟩

theorem exists_openNormalSubgroup_factor_of_isLocallyConstant {ι X : Type*} [Finite ι]
    {f : (ι → G) → X} (hf : IsLocallyConstant f) :
    ∃ (U : OpenNormalSubgroup G) (g : (ι → G ⧸ (U : Subgroup G)) → X),
      f = g ∘ fun x i => (x i : G ⧸ (U : Subgroup G)) := by
  obtain ⟨U, hU⟩ := exists_openNormalSubgroup_pi_of_isLocallyConstant hf
  refine ⟨U, fun q => f fun i => (q i).out, funext fun x => hU _ _ fun i => ?_⟩
  exact QuotientGroup.eq.mp (QuotientGroup.out_eq' (x i : G ⧸ (U : Subgroup G))).symm

theorem exists_openNormalSubgroup_fin_of_isLocallyConstant {n : ℕ} {X : Type*}
    {f : (Fin n → G) → X} (hf : IsLocallyConstant f) :
    ∃ U : OpenNormalSubgroup G, ∀ x y : Fin n → G, (∀ i, (x i)⁻¹ * y i ∈ U) → f x = f y :=
  exists_openNormalSubgroup_pi_of_isLocallyConstant hf

theorem exists_openNormalSubgroup_factor_fin_of_isLocallyConstant {n : ℕ} {X : Type*}
    {f : (Fin n → G) → X} (hf : IsLocallyConstant f) :
    ∃ (U : OpenNormalSubgroup G) (g : (Fin n → G ⧸ (U : Subgroup G)) → X),
      f = g ∘ fun x i => (x i : G ⧸ (U : Subgroup G)) :=
  exists_openNormalSubgroup_factor_of_isLocallyConstant hf

end GroundTheory.ProfCoh
end

-- bundled from GroundTheory.ProfiniteCohomology.KummerFinite
section
namespace GroundTheory.ProfCoh

open Polynomial

section Characters

variable {K : Type*} [Field K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]

def monoidHomRootsOfUnityEquiv (G : Type*) [Group G] (hG : ∀ g : G, g ^ n = 1) :
    (G →* rootsOfUnity n K) ≃ (G →* Kˣ) where
  toFun φ := (rootsOfUnity n K).subtype.comp φ
  invFun ψ := ψ.codRestrict (rootsOfUnity n K) fun g => by
    rw [mem_rootsOfUnity, ← map_pow, hG g, map_one]
  left_inv φ := by ext; rfl
  right_inv ψ := by ext; rfl

lemma card_monoidHom_rootsOfUnity (G : Type*) [CommGroup G] [Finite G]
    (hG : ∀ g : G, g ^ n = 1) : Nat.card (G →* rootsOfUnity n K) = Nat.card G := by
  have : HasEnoughRootsOfUnity K (Monoid.exponent G) :=
    HasEnoughRootsOfUnity.of_dvd K (Monoid.exponent_dvd_of_forall_pow_eq_one hG)
  rw [Nat.card_congr (monoidHomRootsOfUnityEquiv G hG),
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity]

lemma finite_monoidHom_rootsOfUnity (G : Type*) [Group G] [Finite G] :
    Finite (G →* rootsOfUnity n K) :=
  .of_injective _ DFunLike.coe_injective

end Characters

section Finite

variable (K : Type*) [Field K] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]
variable (L : Type*) [Field L] [Algebra K L]


omit [NeZero n] [HasEnoughRootsOfUnity K n] in
lemma kummerGroup_pow_eq_one (x : kummerGroup K n L) : x ^ n = 1 :=
  Subtype.ext (UnitsModPow.pow_eq_one K n x.1)

variable {K n L}


omit [NeZero n] [HasEnoughRootsOfUnity K n] in
lemma exists_eigenvector_of_character [FiniteDimensional K L] (χ : Gal(L/K) →* Kˣ) :
    ∃ β : Lˣ, ∀ σ : Gal(L/K), σ (β : L) = algebraMap K L (χ σ : K) * β := by
  let f : Gal(L/K) → Lˣ := fun σ => Units.map (algebraMap K L : K →* L) (χ σ)
  have hf : groupCohomology.IsMulCocycle₁ f := by
    intro g h
    ext
    simp only [f, map_mul, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, AlgEquiv.smul_units_def,
      AlgEquiv.commutes]
    ring
  obtain ⟨β, hβ⟩ := groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hf
  refine ⟨β, fun σ => ?_⟩
  have := congrArg Units.val (hβ σ)
  simp only [AlgEquiv.smul_units_def, Units.val_div_eq_div_val, Units.coe_map, MonoidHom.coe_coe,
    f] at this
  rw [← this, div_mul_cancel₀ _ β.ne_zero]


omit [NeZero n] [HasEnoughRootsOfUnity K n] in
lemma exists_kummer_eigenvector [FiniteDimensional K L] [IsGalois K L]
    (hexp : Monoid.exponent Gal(L/K) ∣ n) (χ : Gal(L/K) →* Kˣ) :
    ∃ a : Kˣ, ∃ β : L, β ^ n = algebraMap K L a ∧
      ∀ σ : Gal(L/K), σ β = algebraMap K L (χ σ : K) * β := by
  obtain ⟨β, hβ⟩ := exists_eigenvector_of_character χ
  have hfix : ∀ σ : Gal(L/K), σ ((β : L) ^ n) = (β : L) ^ n := by
    intro σ
    rw [map_pow, hβ σ, mul_pow, ← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow,
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hexp σ, map_one, Units.val_one, map_one, one_mul]
  obtain ⟨b, hb⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) _).mpr hfix
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero] at hb
    exact pow_ne_zero n β.ne_zero hb.symm
  exact ⟨Units.mk0 b hb0, β, hb.symm, hβ⟩

variable (K n L)

theorem kummerPairingRight_injective [FiniteDimensional K L] [IsGalois K L] :
    Function.Injective (kummerPairingRight K n L) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨a, ha, α, hα⟩ := exists_rep x
  have hfix : ∀ σ : Gal(L/K), σ α = α := fun σ =>
    (kummerPairing_eq_one_iff σ x ha hα).mp (DFunLike.congr_fun hx σ)
  obtain ⟨b, rfl⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) α).mpr hfix
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_pow (NeZero.ne n)] at hα
    exact (map_ne_zero (algebraMap K L)).mpr a.ne_zero hα.symm
  have hba : (Units.mk0 b hb0) ^ n = a := by
    ext
    simpa using (algebraMap K L).injective (by simpa using hα)
  apply Subtype.ext
  rw [← ha, OneMemClass.coe_one, QuotientGroup.eq_one_iff]
  exact mem_unitsPow.mpr ⟨_, hba⟩

theorem kummerPairingLeft_injective [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (hexp : Monoid.exponent Gal(L/K) ∣ n) :
    Function.Injective (kummerPairingLeft K n L) := by
  let _ : CommGroup Gal(L/K) :=
    { (inferInstance : Group Gal(L/K)) with
      mul_comm := fun a b => (IsMulCommutative.is_comm (M := Gal(L/K))).comm a b }
  have : HasEnoughRootsOfUnity K (Monoid.exponent Gal(L/K)) := HasEnoughRootsOfUnity.of_dvd K hexp
  rw [injective_iff_map_eq_one]
  intro σ hσ
  by_contra hne
  obtain ⟨χ, hχ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity Gal(L/K) K hne
  obtain ⟨a, β, hβ, hχβ⟩ := exists_kummer_eigenvector hexp χ
  have hx : (a : UnitsModPow K n) ∈ kummerGroup K n L := mk_mem_kummerGroup.mpr ⟨β, hβ⟩
  have h1 : σ β = β :=
    (kummerPairing_eq_one_iff σ ⟨_, hx⟩ rfl hβ).mp (DFunLike.congr_fun hσ ⟨_, hx⟩)
  rw [hχβ σ] at h1
  have h2 : algebraMap K L (χ σ : K) = 1 :=
    mul_right_cancel₀ (ne_zero_of_pow_eq_algebraMap hβ) (h1.trans (one_mul β).symm)
  apply hχ
  ext
  simpa using (algebraMap K L).injective (h2.trans (map_one _).symm)

theorem kummerGroup_finite [FiniteDimensional K L] [IsGalois K L] :
    Finite (kummerGroup K n L) :=
  have := finite_monoidHom_rootsOfUnity (K := K) (n := n) Gal(L/K)
  Finite.of_injective _ (kummerPairingRight_injective K n L)

theorem card_kummerGroup [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (hexp : Monoid.exponent Gal(L/K) ∣ n) :
    Nat.card (kummerGroup K n L) = Module.finrank K L := by
  let _ : CommGroup Gal(L/K) :=
    { (inferInstance : Group Gal(L/K)) with
      mul_comm := fun a b => (IsMulCommutative.is_comm (M := Gal(L/K))).comm a b }
  have := kummerGroup_finite K n L
  have := finite_monoidHom_rootsOfUnity (K := K) (n := n) Gal(L/K)
  have := finite_monoidHom_rootsOfUnity (K := K) (n := n) (kummerGroup K n L)
  rw [← IsGalois.card_aut_eq_finrank]
  apply le_antisymm
  · calc Nat.card (kummerGroup K n L) ≤ Nat.card (Gal(L/K) →* rootsOfUnity n K) :=
          Nat.card_le_card_of_injective _ (kummerPairingRight_injective K n L)
      _ = Nat.card Gal(L/K) :=
          card_monoidHom_rootsOfUnity Gal(L/K) (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hexp)
  · calc Nat.card Gal(L/K) ≤ Nat.card (kummerGroup K n L →* rootsOfUnity n K) :=
          Nat.card_le_card_of_injective _ (kummerPairingLeft_injective K n L hexp)
      _ = Nat.card (kummerGroup K n L) :=
          card_monoidHom_rootsOfUnity (kummerGroup K n L) (kummerGroup_pow_eq_one K n L)

theorem kummerPairingLeft_bijective [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (hexp : Monoid.exponent Gal(L/K) ∣ n) :
    Function.Bijective (kummerPairingLeft K n L) := by
  have := kummerGroup_finite K n L
  have := finite_monoidHom_rootsOfUnity (K := K) (n := n) (kummerGroup K n L)
  rw [Nat.bijective_iff_injective_and_card]
  refine ⟨kummerPairingLeft_injective K n L hexp, ?_⟩
  rw [IsGalois.card_aut_eq_finrank, ← card_kummerGroup K n L hexp]
  exact (card_monoidHom_rootsOfUnity (kummerGroup K n L) (kummerGroup_pow_eq_one K n L)).symm

noncomputable def galEquivDual [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (hexp : Monoid.exponent Gal(L/K) ∣ n) :
    Gal(L/K) ≃* (kummerGroup K n L →* rootsOfUnity n K) :=
  MulEquiv.ofBijective _ (kummerPairingLeft_bijective K n L hexp)

end Finite

end GroundTheory.ProfCoh
end

