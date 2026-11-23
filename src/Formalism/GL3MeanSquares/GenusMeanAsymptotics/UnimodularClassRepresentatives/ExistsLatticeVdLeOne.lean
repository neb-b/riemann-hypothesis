module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0034
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsNearRepresentation
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.VdLeOneOfBasis

@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

omit [NumberField K] [StarRing K] [NumberField F] in
private theorem algebraMap_int_F_to_K_eq_algebraMap_F_K (n : 𝓞 F) :
    algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) n) = algebraMap F K (n : F) := by
  rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K,
    IsScalarTower.algebraMap_apply (𝓞 F) F K, RingOfIntegers.coe_eq_algebraMap]

namespace LocalCell

open LocalSpans idealPowerSpanBounds localizedQuotients WCA

variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K

theorem form_self_star {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (w : V) : star (h w w) = h w w :=
  hs.eq w w

theorem exact_step {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {b x : V}
    (hd : h (x - b) (x - b) ≠ 0) :
    h (b - ((h b (x - b) + h (x - b) b) * (h (x - b) (x - b))⁻¹) • (x - b))
        (b - ((h b (x - b) + h (x - b) b) * (h (x - b) (x - b))⁻¹) • (x - b)) = h b b ∧
      (b - ((h b (x - b) + h (x - b) b) * (h (x - b) (x - b))⁻¹) • (x - b)) - x =
        -(((h (x - b) (x - b))⁻¹ * (h x x - h b b)) • (x - b)) := by
  set w := x - b with hw
  have hx : x = w + b := by rw [hw]; abel
  have e1 : star (h b w) = h w b := hs.eq b w
  have e2 : star (h w b) = h b w := hs.eq w b
  have e3 : star (h w w) = h w w := hs.eq w w
  set d := h w w with hdd
  constructor
  · simp only [map_sub, LinearMap.sub_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
      starRingEnd_apply, RingHom.id_apply, star_mul', star_add, star_inv₀, e1, e2, e3, ← hdd]
    field_simp
    ring
  · have e4 : h x x - h b b = d + (h b w + h w b) := by
      rw [hx]
      simp only [map_add (f := _), LinearMap.add_apply, ← hdd]
      ring
    rw [e4]
    have e5 : d⁻¹ * (d + (h b w + h w b)) = 1 + (h b w + h w b) * d⁻¹ := by
      field_simp
    rw [e5, add_smul, one_smul]
    conv_lhs => rw [hx]
    abel

theorem exists_near_representation (h𝔭 : 𝔭.IsMaximal) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A) {n s : 𝓞 F} {b : V}
    (hb : h b b = κ (ι n)) (hsb : ι s • b ∈ A) {v k : ℕ} {x : V} (hx : InL 𝔭 A 0 x)
    (hε : InI 𝔭 (v + k) (h x x - κ (ι n)))
    (hD : ¬ InI 𝔭 (v + 1) (κ (ι (s * s)) * h (x - b) (x - b))) :
    ∃ y, InL 𝔭 A 0 y ∧ h y y = κ (ι n) ∧ InL 𝔭 A k (y - x) := by
  have hp := h𝔭.isPrime
  have hd : h (x - b) (x - b) ≠ 0 := by
    intro h0
    apply hD
    rw [h0, mul_zero]
    exact Cell.InI.zero hp _
  have hs0 : κ (ι s) ≠ 0 := by
    intro h0
    apply hD
    rw [map_mul, map_mul, h0, zero_mul, zero_mul]
    exact Cell.InI.zero hp _
  obtain ⟨h1, h2⟩ := exact_step hs hd
  set y := b - ((h b (x - b) + h (x - b) b) * (h (x - b) (x - b))⁻¹) • (x - b) with hy
  set w := x - b with hw
  have hsw : InL 𝔭 A 0 (ι s • w) := by
    rw [hw, smul_sub]
    refine InL.sub hp ?_ ((inL_zero_iff hp).2 (le_locF 𝔭 A hsb))
    rw [← algebraMap_smul K (ι s)]
    have := InL.smul hp (InI.int hp (ι s)) hx
    rwa [zero_add] at this
  have hDe : h (ι s • w) (ι s • w) = κ (ι (s * s)) * h w w := form_smul hF h s s w w
  have hD0 : InI 𝔭 0 (κ (ι (s * s)) * h w w) := by
    rw [← hDe]
    exact InL.form hp hF hA hsw hsw
  have hDs : star (κ (ι (s * s)) * h w w) = κ (ι (s * s)) * h w w := by
    rw [← hDe]; exact hs.eq _ _
  have h3 : InI 𝔭 (v + k) (κ (ι s) * (h x x - κ (ι n))) := by
    have := InI.mul hp (InI.int hp (ι s)) hε
    rwa [zero_add] at this
  have h4 := Cell.InI.divK h𝔭 hF hDs hD0 hD h3
  have h5 := InL.smul hp h4 hsw
  rw [add_zero] at h5
  have h6 : InL 𝔭 A k (y - x) := by
    rw [h2, hb]
    apply InL.neg
    have : ((h w w)⁻¹ * (h x x - κ (ι n))) • w =
        ((κ (ι (s * s)) * h w w)⁻¹ * (κ (ι s) * (h x x - κ (ι n)))) • ι s • w := by
      rw [← algebraMap_smul K (ι s), smul_smul]
      congr 1
      rw [map_mul, map_mul]
      field_simp
    rw [this]
    exact h5
  refine ⟨y, ?_, h1.trans hb, h6⟩
  have : y = x + (y - x) := by abel
  rw [this]
  exact hx.add hp (h6.mono (Nat.zero_le _))

theorem exists_F_smul_mem (hF : IsFixF K F) {Λ : Submodule (𝓞 K) V} (hΛ : Submodule.IsFullLattice K Λ)
    (v : V) : ∃ s : 𝓞 F, s ≠ 0 ∧ ι s • v ∈ Λ := by
  obtain ⟨r, hr, hrv⟩ := StabilizerLattices.exists_smul_mem hΛ v
  obtain ⟨s, hs⟩ := (conjO_eq_iff_mem_range hF (conjO K r * r)).1 (by
    rw [map_mul, conjO_conjO, mul_comm])
  refine ⟨s, ?_, ?_⟩
  · rintro rfl
    rw [map_zero] at hs
    rcases mul_eq_zero.1 hs.symm with h0 | h0
    · apply hr
      rw [← conjO_conjO r, h0, map_zero]
    · exact hr h0
  · rw [hs, mul_smul]
    exact Λ.smul_mem _ hrv

theorem exists_near (h𝔭 : 𝔭.IsMaximal) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hL : Submodule.IsFullLattice K A) (hA : Formalism.HermitianLatticesTheory.IsIntegralLat h A) {n : 𝓞 F} (hn : n ≠ 0)
    (hrep : ∃ b : V, h b b = κ (ι n)) :
    ∃ v : ℕ, ∀ k : ℕ, 1 ≤ k → ∀ x, InL 𝔭 A 0 x → InI 𝔭 (v + k) (h x x - κ (ι n)) →
      ∃ y, InL 𝔭 A 0 y ∧ h y y = κ (ι n) ∧ InL 𝔭 A k (y - x) := by
  have hp := h𝔭.isPrime
  obtain ⟨b, hb⟩ := hrep
  obtain ⟨s, hs0, hsb⟩ := exists_F_smul_mem hF hL b
  have hN : 4 * (s * s * n) ≠ 0 :=
    mul_ne_zero (by norm_num) (mul_ne_zero (mul_ne_zero hs0 hs0) hn)
  refine ⟨vF 𝔭 (4 * (s * s * n)), fun k hk x hx hε => ?_⟩
  set v := vF 𝔭 (4 * (s * s * n)) with hv
  by_cases h1 : InI 𝔭 (v + 1) (κ (ι (s * s)) * h (x - b) (x - b))
  · by_cases h2 : InI 𝔭 (v + 1) (κ (ι (s * s)) * h (x - -b) (x - -b))
    · exfalso
      apply localValuationFiltration.notMem_pow_vF h𝔭 hN
      have hmem := integralBasisSpans.congrP_int h𝔭 (v + 1) (ι (4 * (s * s * n))) 0
      rw [Cell.congrP_iff_inI, map_zero, sub_zero, Ideal.Quotient.eq, sub_zero, mem_pow_iff] at hmem
      rw [← hv, ← hmem]
      have h3 : InI 𝔭 (v + 1) (κ (ι (2 * (s * s))) * (h x x - κ (ι n))) := by
        have := InI.mul hp (InI.int hp (ι (2 * (s * s)))) (hε.mono (by omega : v + 1 ≤ v + k))
        rwa [zero_add] at this
      have e : κ (ι (4 * (s * s * n))) = κ (ι (s * s)) * h (x - b) (x - b) +
          κ (ι (s * s)) * h (x - -b) (x - -b) - κ (ι (2 * (s * s))) * (h x x - κ (ι n)) := by
        simp only [map_sub, map_neg, LinearMap.sub_apply, LinearMap.neg_apply, hb, map_mul, map_ofNat]
        ring
      rw [e]
      exact (h1.add hp h2).sub hp h3
    · exact exists_near_representation h𝔭 hF hs hA (b := -b) (by simpa using hb)
        (by rw [smul_neg]; exact A.neg_mem hsb) hx hε h2
  · exact exists_near_representation h𝔭 hF hs hA hb hsb hx hε h1

end LocalCell

theorem exists_exact_near (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsFullLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0)
    (hrep : ∃ b : V, h b b = algebraMap F K (n : F)) :
    ∃ c₀ : ℕ, ∀ k : ℕ, c₀ ≤ k → ∀ x ∈ (locF 𝔭 A₀), CongrP 𝔭 k (h x x) (algebraMap F K (n : F)) →
      ∃ y ∈ (locF 𝔭 A₀), h y y = algebraMap F K (n : F) ∧
        y - x ∈ ((extP K 𝔭) ^ (k - c₀) • (locF 𝔭 A₀) : Submodule (𝓞 K) V) := by
  have hp : 𝔭.IsPrime := h𝔭.isPrime
  have hrep' : ∃ b : V, h b b = algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) n) := by
    rwa [algebraMap_int_F_to_K_eq_algebraMap_F_K]
  have hnear := LocalCell.exists_near (𝔭 := 𝔭) (A := A₀) h𝔭 hF hs hA₀ hA₀i (n := n) hn hrep'
  obtain ⟨v, hv⟩ := hnear
  refine ⟨v + 1, fun k hk x hx hc => ?_⟩
  rw [Cell.congrP_iff_inI] at hc
  obtain ⟨y, hy0, hyy, hyx⟩ := hv (k - v) (by omega) x ((WCA.inL_zero_iff hp).2 hx)
    (by rw [algebraMap_int_F_to_K_eq_algebraMap_F_K, show v + (k - v) = k by omega]; exact hc)
  refine ⟨y, (WCA.inL_zero_iff hp).1 hy0, by rw [hyy, algebraMap_int_F_to_K_eq_algebraMap_F_K], ?_⟩
  exact (WCA.InL.mono (by omega) hyx).mem hp

theorem exists_lattice_vd_le_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {x₀ : V} {n : 𝓞 F} (hx : h x₀ x₀ = algebraMap F K (n : F)) (hn : n ∉ 𝔭) :
    ∃ L₀ : Submodule (𝓞 K) V, Submodule.IsLattice K L₀ ∧ Formalism.HermitianLatticesTheory.IsIntegralLat h L₀ ∧
      x₀ ∈ L₀ ∧ vd h L₀ 𝔭 ≤ 1 := by
  exact Cell.exists_lattice (𝔭 := 𝔭) hK hF hs hd h𝔭 (by rw [algebraMap_int_F_to_K_eq_algebraMap_F_K]; exact hx) hn

end Formalism.HermitianLattices.Ext.L3
