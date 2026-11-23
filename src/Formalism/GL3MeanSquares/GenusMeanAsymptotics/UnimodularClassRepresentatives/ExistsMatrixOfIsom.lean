module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.EquivFunEquivOfMatrixSymm
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0006
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0013

@[expose] public section

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.HU

open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
local notation "jK" => algebraMap (𝓞 K) K

def IsE (h : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (e : ℕ) : Prop :=
  ∀ x : V, (∀ y ∈ A, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)) →
    ∀ t ∈ 𝔭 ^ e, algebraMap (𝓞 F) (𝓞 K) t • x ∈ A

theorem gramK_det_ne_zero {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V) :
    (gramK h b).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  apply hv
  have h1 := form_repr h b (b.equivFun.symm v) (b.equivFun.symm v)
  rw [LinearEquiv.apply_symm_apply, hv0, dotProduct_zero] at h1
  have h2 := hd _ h1
  rw [← b.equivFun.apply_symm_apply v, h2, map_zero]

theorem exists_E (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V)
    {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {e : ℕ} (he : IsE h (locF 𝔭 (spanO b)) 𝔭 e) {π₀ : 𝓞 F} (hπ : π₀ ∈ 𝔭) :
    ∃ E : Matrix κ κ K, Ent (SP K 𝔭) E ∧ gramK h b * E = jK (ι π₀) ^ e • (1 : Matrix κ κ K) := by
  have hdet : IsUnit (gramK h b).det := isUnit_iff_ne_zero.2 (gramK_det_ne_zero hd b)
  refine ⟨jK (ι π₀) ^ e • (gramK h b)⁻¹, ?_, by rw [Matrix.mul_smul, Matrix.mul_nonsing_inv _ hdet]⟩
  intro i j
  have h1 : ∀ y ∈ locF 𝔭 (spanO b), h y (b.equivFun.symm fun i => (gramK h b)⁻¹ i j) ∈
      locF 𝔭 (1 : Submodule (𝓞 K) K) := by
    intro y hy
    rw [form_repr h b, LinearEquiv.apply_symm_apply]
    have h2 : (gramK h b *ᵥ fun i => (gramK h b)⁻¹ i j) = Pi.single j 1 := by
      funext l
      have : (gramK h b *ᵥ fun i => (gramK h b)⁻¹ i j) l = (gramK h b * (gramK h b)⁻¹) l j := rfl
      rw [this, Matrix.mul_nonsing_inv _ hdet, Matrix.one_apply, Pi.single_apply]
    rw [h2, dotProduct_single_one, ← mem_SP_iff_locF]
    exact InP.conj hF ((mem_locF_iff_repr b y).1 hy j)
  have h3 := (mem_locF_iff_repr b _).1 (he _ h1 (π₀ ^ e) (Ideal.pow_mem_pow hπ e)) i
  rw [← algebraMap_smul K, map_smul, LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul, map_pow,
    map_pow] at h3
  exact h3

theorem gramK_eq_map {h : V →ₗ⋆[K] V →ₗ[K] K} {b : Basis κ K V} {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, jK (H i j) = h (b i) (b j)) : gramK h b = H.map jK := by
  ext i j
  exact (hH i j).symm

theorem map_form (H Y : Matrix κ κ (𝓞 K)) :
    (Y.map jK)ᴴ * H.map jK * Y.map jK = (Yᴴ * H * Y).map jK := by
  rw [Matrix.map_mul, Matrix.map_mul, conjTranspose_map jK (fun _ => rfl)]

theorem exists_Z {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {π₀ s₀ : 𝓞 F} (hu : IsUnif0 𝔭 π₀ s₀)
    {H Y : Matrix κ κ (𝓞 K)} {k : ℕ} (hY : ∀ i j, (Yᴴ * H * Y - H) i j ∈ extP K 𝔭 ^ k) :
    ∃ Z : Matrix κ κ K, Ent (SP K 𝔭) Z ∧
      (Y.map jK)ᴴ * H.map jK * Y.map jK = H.map jK + jK (ι π₀) ^ k • Z := by
  choose Z hZ hZ' using fun i j => (mem_noncompactPart_iff hu k _).1 (inP_jK (hY i j))
  refine ⟨Matrix.of Z, hZ, ?_⟩
  rw [map_form]
  ext i j
  have := hZ' i j
  rw [Matrix.sub_apply, map_sub] at this
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul,
    ← this]
  ring

theorem ent_map {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (Y : Matrix κ κ (𝓞 K)) : Ent (SP K 𝔭) (Y.map jK) :=
  fun _ _ => jK_mem_SP _

theorem equivFun_sum_smul (b : Basis κ K V) (c : κ → 𝓞 K) :
    b.equivFun (∑ l, c l • b l) = fun l => jK (c l) := by
  have : ∑ l, c l • b l = ∑ l, jK (c l) • b l :=
    Finset.sum_congr rfl fun l _ => (algebraMap_smul K _ _).symm
  rw [this, ← Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]

theorem exists_isom_matrix (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V) {H : Matrix κ κ (𝓞 K)}
    (hH : ∀ i j, jK (H i j) = h (b i) (b j)) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {e k : ℕ}
    (he : IsE h (locF 𝔭 (spanO b)) 𝔭 e) (hk : e + 1 ≤ k) (Y : Matrix κ κ (𝓞 K))
    (hY : ∀ i j, (Yᴴ * H * Y - H) i j ∈ extP K 𝔭 ^ k) :
    ∃ g ∈ autSub h (locF 𝔭 (spanO b)), ∀ i, g (b i) - ∑ l, Y l i • b l ∈
      (extP K 𝔭 ^ (k - e) • locF 𝔭 (spanO b) : Submodule (𝓞 K) V) := by
  have := h𝔭.isPrime
  obtain ⟨π₀, s₀, hu⟩ := exists_isUnif0 h𝔭
  obtain ⟨E, hE, hHE⟩ := exists_E hF hd b he hu.mem
  obtain ⟨Z, hZ, hXZ⟩ := exists_Z hu hY
  have hg := gramK_eq_map hH
  rw [hg] at hHE
  have hHh : (H.map jK)ᴴ = H.map jK := by rw [← hg]; exact gramK_conjTranspose hs b
  obtain ⟨G, G', D, hG, hG', hD, hGG, hU, hGX⟩ := exists_unitary_near (isLocUnif hK hF h𝔭 hu) hHh
    (ent_map H) hE hHE hk (ent_map Y) hZ hXZ
  refine ⟨equivOfMatrix b G G' hGG, ⟨equivOfMatrix_mem_isom h b G G' hGG (by rw [hg]; exact hU),
    gmap_equivOfMatrix b G G' hGG hG hG'⟩, fun i => ?_⟩
  rw [mem_smul_locF_iff_repr]
  intro l
  have hb1 : b.equivFun (b i) = Pi.single i 1 := by
    funext j
    rw [Basis.equivFun_self, Pi.single_apply]
    simp only [eq_comm]
  rw [map_sub, equivFun_equivOfMatrix, equivFun_sum_smul, hb1, mulVec_single_one, Pi.sub_apply]
  show InP 𝔭 (k - e) (G l i - jK (Y l i))
  rw [hGX, mem_noncompactPart_iff hu]
  refine ⟨D l i, hD l i, ?_⟩
  simp

theorem form_col (H Y : Matrix κ κ (𝓞 K)) (i j : κ) :
    (Yᴴ * H * Y) i j = star (fun l => Y l i) ⬝ᵥ (H *ᵥ fun l => Y l j) := by
  have := form_mulVec Y H (Pi.single i 1) (Pi.single j 1)
  rw [form_single, mulVec_single_one, mulVec_single_one] at this
  exact this.symm

end Formalism.HermitianLattices.Ext.L3.HU
