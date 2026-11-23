module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsMatrixOfIsom
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0023
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FirstFamilyOperatorEnd

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CoeCmbSingle
section
open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.HU

open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

def cmb (b : Basis κ K V) (c : κ → 𝓞 K) : spanO b := (bO b).equivFun.symm c

theorem coe_cmb (b : Basis κ K V) (c : κ → 𝓞 K) : (cmb b c : V) = ∑ l, c l • b l := by
  rw [cmb, Basis.equivFun_symm_apply, Submodule.coe_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [Submodule.coe_smul, bO_apply]

theorem crd_cmb (b : Basis κ K V) (c : κ → 𝓞 K) : crd b (cmb b c) = c :=
  (bO b).equivFun.apply_symm_apply c

theorem cmb_crd (b : Basis κ K V) (y : spanO b) : cmb b (crd b y) = y :=
  (bO b).equivFun.symm_apply_apply y

def inA (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] (b : Basis κ K V) : spanO b →ₗ[𝓞 K] ↥(locF 𝔭 (spanO b)) :=
  Submodule.inclusion (le_locF 𝔭 (spanO b))

theorem coe_inA (𝔭 : Ideal (𝓞 F)) [𝔭.IsPrime] (b : Basis κ K V) (y : spanO b) : (inA 𝔭 b y : V) = y := rfl

abbrev QA (𝔭 : Ideal (𝓞 F)) (b : Basis κ K V) (k : ℕ) : Type :=
  ↥(locF 𝔭 (spanO b)) ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥(locF 𝔭 (spanO b)))

theorem mk_eq_iff {𝔭 : Ideal (𝓞 F)} (b : Basis κ K V) (k : ℕ) (x y : ↥(locF 𝔭 (spanO b))) :
    (Submodule.Quotient.mk x : QA 𝔭 b k) = Submodule.Quotient.mk y ↔
      (x : V) - y ∈ (extP K 𝔭 ^ k • locF 𝔭 (spanO b) : Submodule (𝓞 K) V) := by
  rw [Submodule.Quotient.eq, Submodule.mem_smul_top_iff]
  rfl

theorem quotLocF_mk' {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) [𝔭.IsPrime] (b : Basis κ K V) (k : ℕ)
    (y : spanO b) : quotLocF h𝔭 (spanO b) k (Submodule.Quotient.mk y) = Submodule.Quotient.mk (inA 𝔭 b y) :=
  rfl

theorem exists_cmb {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) [𝔭.IsPrime] (b : Basis κ K V) (k : ℕ)
    (q : QA 𝔭 b k) : ∃ c : κ → 𝓞 K, q = Submodule.Quotient.mk (inA 𝔭 b (cmb b c)) := by
  obtain ⟨q₀, rfl⟩ := (quotLocF h𝔭 (spanO b) k).surjective q
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q₀
  exact ⟨crd b y, by rw [cmb_crd, quotLocF_mk']⟩

theorem cmb_eq_sum (b : Basis κ K V) (c : κ → 𝓞 K) : cmb b c = ∑ i, c i • cmb b (Pi.single i 1) := by
  apply (bO b).equivFun.injective
  show crd b _ = crd b _
  rw [crd_cmb]
  have : crd b (∑ i, c i • cmb b (Pi.single i 1)) = ∑ i, c i • crd b (cmb b (Pi.single i 1)) := by
    unfold crd
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
  rw [this]
  funext l
  simp [crd_cmb, Pi.single_apply]

theorem end_apply_cmb {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] (b : Basis κ K V) (k : ℕ)
    (X : Module.End (𝓞 K) (QA 𝔭 b k)) (Y : Matrix κ κ (𝓞 K))
    (hXY : ∀ i, X (Submodule.Quotient.mk (inA 𝔭 b (cmb b (Pi.single i 1)))) =
      Submodule.Quotient.mk (inA 𝔭 b (cmb b fun l => Y l i))) (c : κ → 𝓞 K) :
    X (Submodule.Quotient.mk (inA 𝔭 b (cmb b c))) = Submodule.Quotient.mk (inA 𝔭 b (cmb b (Y *ᵥ c))) := by
  have h1 : cmb b (Y *ᵥ c) = ∑ i, c i • cmb b fun l => Y l i := by
    apply (bO b).equivFun.injective
    show crd b _ = crd b _
    have : crd b (∑ i, c i • cmb b fun l => Y l i) = ∑ i, c i • crd b (cmb b fun l => Y l i) := by
      unfold crd
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => map_smul _ _ _
    rw [this, crd_cmb]
    funext l
    simp [crd_cmb, mulVec, dotProduct, mul_comm]
  rw [h1, cmb_eq_sum b c]
  simp only [← Submodule.mkQ_apply] at hXY ⊢
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, hXY]

end Formalism.HermitianLattices.Ext.L3.HU
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NkCountLocF
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem nkCount_locF (hF : IsFixF K F) (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F))
    (h𝔭 : 𝔭.IsMaximal) (k : ℕ) (n : 𝓞 F) : nkCount h (locF 𝔭 L) 𝔭 k n = nkCount h L 𝔭 k n :=
  localizedQuotients.nkCount_locF hF h L 𝔭 h𝔭 k n

theorem akCount_locF (hF : IsFixF K F) (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F))
    (h𝔭 : 𝔭.IsMaximal) (k : ℕ) : akCount h (locF 𝔭 L) 𝔭 k = akCount h L 𝔭 k :=
  localizedQuotients.akCount_locF hF h L 𝔭 h𝔭 k

theorem vd_locF (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : vd h (locF 𝔭 L) 𝔭 = vd h L 𝔭 :=
  localizedQuotients.vd_locF hF h L h𝔭

theorem nkCount_succ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) {k : ℕ}
    (hk : 2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2 ≤ k) :
    nkCount h L 𝔭 (k + 1) n = Ideal.absNorm 𝔭 ^ (2 * finrank K V - 1) * nkCount h L 𝔭 k n :=
  firstFamilyOperatorEnd.nkCount_succ_fine hK hF hs hd hL hLi h𝔭 (localValuationFiltration.notMem_pow_vF h𝔭 hn) (by omega)

theorem alphaN_congr (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n n' : 𝓞 F} (hn : n ≠ 0)
    {k : ℕ} (hk : vF 𝔭 n + 2 * vd h L 𝔭 + 2 ≤ k) (hc : n - n' ∈ 𝔭 ^ k) :
    alphaN h L 𝔭 n = alphaN h L 𝔭 n' := by
  have hn1 := localValuationFiltration.notMem_pow_vF h𝔭 hn
  have hn1' : n' ∉ 𝔭 ^ (vF 𝔭 n + 1) := by
    intro h'
    apply hn1
    have hk' : 𝔭 ^ k ≤ 𝔭 ^ (vF 𝔭 n + 1) := Ideal.pow_le_pow_right (by omega)
    have := Ideal.add_mem _ (hk' hc) h'
    simpa using this
  rw [firstFamilyOperatorEnd.alphaN_eq hK hF hs hd hL hLi h𝔭 hn1 (k := k) (by omega),
    firstFamilyOperatorEnd.alphaN_eq hK hF hs hd hL hLi h𝔭 hn1' (k := k) (by omega),
    firstFamilyOperatorEnd.nkCount_congr hF hs hd hL hLi h𝔭 hc]

theorem nkCount_le (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    (hm : 2 ≤ finrank K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ C : ℝ, ∀ (k : ℕ) (n : 𝓞 F),
      (nkCount h L 𝔭 k n : ℝ) ≤ C * (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1)) := by
  refine ⟨2 * (Ideal.absNorm 𝔭 : ℝ) ^ (2 * vd h L 𝔭 + 1), fun k n => ?_⟩
  have := firstFamilyOperatorEnd.nkCount_le_nat hK hF hs hd hL hLi hm h𝔭 k n
  exact_mod_cast this

theorem alphaL_pos (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : 0 < alphaL h L 𝔭 := by
  rw [firstFamilyOperatorEnd.alphaL_eq hK hF hs hd hL hLi h𝔭 (k := 2 * vd h L 𝔭 + 1) le_rfl]
  have hN : 0 < Ideal.absNorm 𝔭 := by
    haveI := h𝔭
    exact Nat.pos_of_ne_zero fun h0 =>
      Ideal.IsMaximal.ne_bot_of_isIntegral_int 𝔭 (Ideal.absNorm_eq_zero_iff.mp h0)
  apply div_pos
  · exact_mod_cast firstFamilyOperatorEnd.akCount_pos hF hs hd hL hLi h𝔭 _
  · apply pow_pos
    exact_mod_cast hN

end Formalism.HermitianLattices.Ext.L3
end
end

