module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.InLZeroIff
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLocalData

@[expose] public section

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.Cell

open LocalSpans idealPowerSpanBounds localizedQuotients WCA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

variable {𝔭 : Ideal (𝓞 F)} {A : Submodule (𝓞 K) V}

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "κ" => algebraMap (𝓞 K) K

theorem congrP_iff_inI {k : ℕ} {a b : K} : CongrP 𝔭 k a b ↔ InI 𝔭 k (a - b) := Iff.rfl

theorem inI_int (h𝔭 : 𝔭.IsMaximal) {k : ℕ} {z : 𝓞 K} : InI 𝔭 k (κ z) ↔ z ∈ extP K 𝔭 ^ k := by
  simpa only [congrP_iff_inI, map_zero, sub_zero, Ideal.Quotient.eq_zero_iff_mem] using
    integralBasisSpans.congrP_int h𝔭 k z 0

theorem inI_ι (h𝔭 : 𝔭.IsMaximal) {k : ℕ} {n : 𝓞 F} : InI 𝔭 k (κ (ι n)) ↔ n ∈ 𝔭 ^ k :=
  (inI_int (z := ι n) h𝔭).trans (mem_pow_iff (K := K) 𝔭 k n)

theorem InI.of_mul (hp : 𝔭.IsPrime) {k : ℕ} {t : 𝓞 F} (ht : t ∉ 𝔭) {a : K}
    (h : InI 𝔭 k (κ (ι t) * a)) : InI 𝔭 k a := by
  obtain ⟨u, hu, z, hz, e⟩ := h
  exact ⟨u * t, fun h => (hp.mem_or_mem h).elim hu ht, z, hz, by rw [e, map_mul, map_mul, mul_assoc]⟩

theorem InI.zero (hp : 𝔭.IsPrime) (k : ℕ) : InI (K := K) 𝔭 k 0 :=
  ⟨1, fun h => hp.ne_top ((Ideal.eq_top_iff_one 𝔭).2 h), 0, zero_mem _, by simp⟩

theorem exists_frac (hF : IsFixF K F) {D : K} (hD : star D = D) (h0 : InI 𝔭 0 D) :
    ∃ t δ : 𝓞 F, t ∉ 𝔭 ∧ κ (ι δ) = κ (ι t) * D := by
  obtain ⟨t, ht, z, -, e⟩ := h0
  obtain ⟨δ, hδ⟩ := (conjO_eq_iff_mem_range hF z).1 (by
    apply RingOfIntegers.coe_injective
    show star (κ z) = κ z
    rw [e, star_mul', hD, star_ι hF])
  exact ⟨t, δ, ht, by rw [hδ, e]⟩

theorem InI.divK (h𝔭 : 𝔭.IsMaximal) (hF : IsFixF K F) {D : K} (hD : star D = D) (h0 : InI 𝔭 0 D)
    {v : ℕ} (hv : ¬ InI 𝔭 (v + 1) D) {k : ℕ} {a : K} (ha : InI 𝔭 (v + k) a) :
    InI 𝔭 k (D⁻¹ * a) := by
  obtain ⟨t, δ, ht, e⟩ := exists_frac hF hD h0
  have hδv : δ ∉ 𝔭 ^ (v + 1) := fun h =>
    hv (InI.of_mul h𝔭.isPrime ht (by rw [← e]; exact (inI_ι h𝔭).2 h))
  have hδ0 : δ ≠ 0 := fun h => hδv (h ▸ zero_mem _)
  have h1 := InI.div h𝔭 hδ0 hδv ha
  have h2 := InI.mul h𝔭.isPrime (InI.int h𝔭.isPrime (ι t)) h1
  rw [zero_add] at h2
  have ht0 := κι_ne_zero (K := K) (ne_zero_of_notMem ht)
  have hδ0' := κι_ne_zero (K := K) hδ0
  have hD0 : D ≠ 0 := by
    rintro rfl
    rw [mul_zero] at e
    exact hδ0' e
  have : D⁻¹ * a = κ (ι t) * ((κ (ι δ))⁻¹ * a) := by
    rw [e]
    field_simp
  rw [this]
  exact h2

end Formalism.HermitianLattices.Ext.L3.Cell
