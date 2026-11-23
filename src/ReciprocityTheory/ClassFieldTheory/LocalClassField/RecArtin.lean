module

public import Mathlib
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecPairDefs
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.PairKEqZeroOfMemNormGrp
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Existence
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0007
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.Bundle0013
public import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne

@[expose] public section

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh Function

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

variable {p K L}

theorem exists_artin_hom (hK : FiniteDimensional ℚ_[p] K) : ∃ Art : Kˣ →* GKab p K, ∀ (a : Kˣ) (g : GK p K), toAbK p K g = Art a →
    ∀ L, IsAbLK p K L → IsRecip p K L a g := by
  classical
  let γ : IntermediateField ℚ_[p] (PadicAlgCl p) → Kˣ → GK p K := fun L a =>
    if h : IsAbLK p K L then (exists_isRecip h a).choose else 1
  have hγ : ∀ L, IsAbLK p K L → ∀ a, IsRecip p K L a (γ L a) := by
    intro L hL a
    simp only [γ, dif_pos hL]
    exact (exists_isRecip hL a).choose_spec
  obtain ⟨f, hf⟩ := exists_hom_GKab hK γ
    (fun L hL a b => IsRecip.unique hL (hγ L hL (a * b)) ((hγ L hL a).mul (hγ L hL b)))
    (fun L L' hL hL' hle a => IsRecip.unique hL (hγ L hL a) ((hγ L' hL' a).of_le hle))
  exact ⟨f, fun a g hg L hL => (hγ L hL a).congr (hf L hL a g hg)⟩

theorem isFrob_of_forall_Kn (hK : FiniteDimensional ℚ_[p] K) (g : GK p K)
    (h : ∀ n, 0 < n → (frobK p K)⁻¹ * g ∈ subG p K (Kn p K n)) : IsFrob p K g := by
  rw [isFrob_iff hK]
  intro ζ m hm hζ
  obtain ⟨n, hn, hζn⟩ := (mem_Kur_iff hK ζ).1 (mem_Kur_of_pow hK hm hζ)
  have h1 : frobK p K ζ = g ζ :=
    (mk_eq_mk_iff (M := Kn p K n) (frobK p K) g).1 (QuotientGroup.eq.2 (h n hn)) ζ hζn
  rw [← h1]
  exact (isFrob_iff hK _).1 (isFrob_frobK hK) ζ m hm hζ

theorem isFrob_of_isRecip (hK : FiniteDimensional ℚ_[p] K) (π : Kˣ) (hπ : vK p K π = 1) (g : GK p K)
    (h : ∀ L, IsAbLK p K L → IsRecip p K L π g) : IsFrob p K g :=
  isFrob_of_forall_Kn hK g fun _ hn =>
    IsRecip.unique (isAbLK_Kn hK hn) (isRecip_uniformiser_Kn hK hn π hπ) (h _ (isAbLK_Kn hK hn))

theorem IsRecip.inv_mul_mem (hK : FiniteDimensional ℚ_[p] K) (hL : IsAbLK p K L) {a b : Kˣ} {g g' : GK p K}
    (h : IsRecip p K L a g) (h' : IsRecip p K L b g') : g⁻¹ * g' ∈ subG p K L ↔ a⁻¹ * b ∈ normGrp p K L := by
  obtain ⟨k, hk⟩ := exists_isRecip hL (a⁻¹ * b)
  have h1 : IsRecip p K L b (g * k) := by
    have := h.mul hk
    rwa [mul_inv_cancel_left] at this
  have h2 : (g * k)⁻¹ * g' ∈ subG p K L := IsRecip.unique hL h1 h'
  rw [← hk.mem_subG_iff hK hL]
  have h3 : g⁻¹ * g' = k * ((g * k)⁻¹ * g') := by group
  rw [h3]
  exact Subgroup.mul_mem_cancel_right _ h2

theorem isArtinK_of_isRecip (hK : FiniteDimensional ℚ_[p] K) (Art : Kˣ →* GKab p K)
    (h : ∀ (a : Kˣ) (g : GK p K), toAbK p K g = Art a → ∀ L, IsAbLK p K L → IsRecip p K L a g) :
    IsArtinK p K Art := by
  have hsurj : ∀ L, IsAbLK p K L → ∀ g : GK p K, ∃ (x : Kˣ) (g' : GK p K), toAbK p K g' = Art x ∧
      g'⁻¹ * g ∈ subG p K L := by
    intro L hL g
    obtain ⟨a, ha⟩ := exists_isRecip_of_gal hK hL g
    obtain ⟨g', hg'⟩ := toAbK_surjective (Art a)
    exact ⟨a, g', hg', IsRecip.unique hL (h a g' hg' L hL) ha⟩
  refine ⟨?_, ?_, (denseRange_GKab_iff hK Art).2 hsurj, ?_, fun L hL => ⟨hsurj L hL, ?_⟩⟩
  · rw [continuous_GKab_iff hK]
    intro L hL x
    have hopen : IsOpen ((fun y : Kˣ => x⁻¹ * y) ⁻¹' (normGrp p K L : Set Kˣ)) :=
      (isOpen_normGrp hK hL.fin hL.le).preimage (continuous_const.mul continuous_id)
    have hx : x ∈ (fun y : Kˣ => x⁻¹ * y) ⁻¹' (normGrp p K L : Set Kˣ) := by
      show x⁻¹ * x ∈ normGrp p K L
      rw [inv_mul_cancel]; exact one_mem _
    filter_upwards [hopen.mem_nhds hx] with y hy g g' hg hg'
    exact (IsRecip.inv_mul_mem hK hL (h x g hg L hL) (h y g' hg' L hL)).2 hy
  · rw [injective_iff_map_eq_one]
    intro a ha
    refine eq_one_of_forall_mem_normGrp hK a fun L hL => ?_
    have h1 : toAbK p K 1 = Art a := by rw [map_one, ha]
    exact ((h a 1 h1 L hL).mem_subG_iff hK hL).1 (one_mem _)
  · intro π hπ g hg
    exact isFrob_of_isRecip hK π hπ g (h π g hg)
  · intro x g hg
    exact (h x g hg L hL).mem_subG_iff hK hL

theorem exists_isArtinK (hK : FiniteDimensional ℚ_[p] K) : ∃ Art : Kˣ →* GKab p K, IsArtinK p K Art := by
  obtain ⟨Art, h⟩ := exists_artin_hom hK
  exact ⟨Art, isArtinK_of_isRecip hK Art h⟩

end ReciprocityTheory.DiscreteGroups.LocalClassField
