module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0043
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0042
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0044
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.RelIndexSSubInfEq
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.RelIndexEqMapMulKer
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0039
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0030
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0017
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0018
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FactorIdentity

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatioHolds
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem relIndex_sSub_inf (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {A₀ : Submodule (𝓞 K) V}
    (hA₀ : Submodule.IsFullLattice K A₀) (hA₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h A₀) {B₀ : Submodule (𝓞 K) V}
    (hB₀ : Submodule.IsFullLattice K B₀) (hB₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h B₀) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ c₀ : ℕ, ∀ c ≥ c₀, ∃ k₀ : ℕ, ∀ k ≥ k₀,
      sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀) ≤ sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀) ∧
      (sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀)).relIndex
          (sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀)) *
          Ideal.absNorm 𝔭 ^ (finrank K V * vd h (locF 𝔭 B₀) 𝔭) =
        Ideal.absNorm 𝔭 ^ (finrank K V ^ 2 * c + finrank K V * vd h (locF 𝔭 A₀) 𝔭) := by
  obtain ⟨c₀, hc₀⟩ := relIndex_sSub_inf_eq hK hF hs hd hA₀ hA₀i hB₀ hB₀i h𝔭
  refine ⟨c₀, fun c hc => ?_⟩
  obtain ⟨k₀, hk₀⟩ := hc₀ c hc
  refine ⟨k₀, fun k hk => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hk₀ k hk
  refine ⟨h1, ?_⟩
  rw [h3]
  exact relIndex_hermL hK hF hs hd (by first | exact hA₀ | exact hA₀.toIsLattice) hA₀i
    (by first | exact hB₀ | exact hB₀.toIsLattice) hB₀i h𝔭 h2

end Formalism.HermitianLattices.Ext.L3.D2

namespace Formalism.HermitianLattices.Ext.L3

open D2

theorem local_density_ratio_holds :
    ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K],
      Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F →
      ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
        [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (A₀ B₀ : Submodule (𝓞 K) V)
        (𝔭 : Ideal (𝓞 F)),
        h.IsSymm → IsTotPosDef h → 𝔭.IsMaximal → Submodule.IsFullLattice K A₀ →
        Submodule.IsFullLattice K B₀ → Formalism.HermitianLatticesTheory.IsIntegralLat h A₀ →
        Formalism.HermitianLatticesTheory.IsIntegralLat h B₀ →
        alphaL h (locF 𝔭 A₀) 𝔭 * (Ideal.absNorm 𝔭 : ℝ) ^ (finrank K V * vd h (locF 𝔭 B₀) 𝔭) *
            orbCount h (locF 𝔭 B₀) (locF 𝔭 A₀) =
          alphaL h (locF 𝔭 B₀) 𝔭 * (Ideal.absNorm 𝔭 : ℝ) ^ (finrank K V * vd h (locF 𝔭 A₀) 𝔭) *
            orbCount h (locF 𝔭 A₀) (locF 𝔭 B₀) := by
  intro K F _ _ _ _ _ _ hK hF V _ _ _ _ _ h A₀ B₀ 𝔭 hs hd h𝔭 hA₀ hB₀ hA₀i hB₀i
  obtain ⟨c₁, hc₁⟩ := D2.relIndex_sSub_inf hK hF hs hd hA₀ hA₀i hB₀ hB₀i h𝔭
  obtain ⟨c₂, hc₂⟩ := D2.relIndex_nSub hK hF hA₀ hB₀ h𝔭
  set c := c₁ + c₂ with hc
  obtain ⟨k₁, hk₁⟩ := hc₁ c (by omega)
  obtain ⟨k₂, hk₂⟩ := hc₂ c (by omega)
  obtain ⟨k₃, hk₃⟩ := D2.akCount_eq_relIndex hK hF hs hd (by first | exact hA₀ | exact hA₀.toIsLattice) hA₀i h𝔭
  obtain ⟨k₄, hk₄⟩ := D2.akCount_eq_relIndex hK hF hs hd (by first | exact hB₀ | exact hB₀.toIsLattice) hB₀i h𝔭
  obtain ⟨k₅, hk₅⟩ := D2.relIndex_inf_glSub hK hF hs hd hA₀ hA₀i hB₀ h𝔭
  obtain ⟨k₆, hk₆⟩ := D2.relIndex_inf_glSub hK hF hs hd hB₀ hB₀i hA₀ h𝔭
  obtain ⟨k₇, hk₇⟩ := D2.nSub_le_glSub hB₀ hA₀ h𝔭
  obtain ⟨k₈, hk₈⟩ := D2.alphaL_eq hK hF hs hd
    (by first | exact hA₀ | exact hA₀.toIsLattice) hA₀i h𝔭
  obtain ⟨k₉, hk₉⟩ := D2.alphaL_eq hK hF hs hd
    (by first | exact hB₀ | exact hB₀.toIsLattice) hB₀i h𝔭
  set k := k₁ + k₂ + k₃ + k₄ + k₅ + k₆ + k₇ + k₈ + k₉ with hk
  obtain ⟨hJI, hIJ⟩ := hk₁ k (by omega)
  obtain ⟨hNN, hNNi⟩ := hk₂ k (by omega)
  have hakA := hk₃ k (by omega)
  have hakB := hk₄ (k + c) (by omega)
  have horbAB := hk₅ k (by omega)
  have horbBA := hk₆ (k + c) (by omega)
  have hNBA := hk₇ (k + c) (by omega)
  have hαA := hk₈ k (by omega)
  have hαB := hk₉ (k + c) (by omega)
  have f1 := D2.nSub_le_sSub hF hA₀i h𝔭 k
  have f2 := D2.nSub_le_sSub hF hB₀i h𝔭 (k + c)
  have hNJ : nSub (locF 𝔭 B₀) 𝔭 (k + c) ≤ sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀) :=
    le_inf f2 hNBA
  have hIS : sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀) ≤ sSub h (locF 𝔭 A₀) 𝔭 k := inf_le_left
  have hJS : sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀) ≤ sSub h (locF 𝔭 B₀) 𝔭 (k + c) :=
    inf_le_left
  have e1 := Subgroup.relIndex_mul_relIndex (hHK := hNN) (hKL := f1)
  have e2 := Subgroup.relIndex_mul_relIndex (hHK := hNJ) (hKL := hJI)
  have e3 := Subgroup.relIndex_mul_relIndex (hHK := hNJ.trans hJI) (hKL := hIS)
  have e4 := Subgroup.relIndex_mul_relIndex (hHK := hNJ) (hKL := hJS)
  have e5 : (nSub (locF 𝔭 A₀) 𝔭 k).relIndex (sSub h (locF 𝔭 A₀) 𝔭 k) *
      (nSub (locF 𝔭 B₀) 𝔭 (k + c)).relIndex (nSub (locF 𝔭 A₀) 𝔭 k) =
      (nSub (locF 𝔭 B₀) 𝔭 (k + c)).relIndex (sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀)) *
        ((sSub h (locF 𝔭 B₀) 𝔭 (k + c) ⊓ glSub (locF 𝔭 A₀)).relIndex
            (sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀)) *
          (sSub h (locF 𝔭 A₀) 𝔭 k ⊓ glSub (locF 𝔭 B₀)).relIndex (sSub h (locF 𝔭 A₀) 𝔭 k)) := by
    rw [mul_comm, e1, ← e3, ← e2, mul_assoc]
  have E : akCount h (locF 𝔭 A₀) 𝔭 k * Ideal.absNorm 𝔭 ^ (2 * finrank K V ^ 2 * c) *
      Ideal.absNorm 𝔭 ^ (finrank K V * vd h (locF 𝔭 B₀) 𝔭) * orbCount h (locF 𝔭 B₀) (locF 𝔭 A₀) =
      akCount h (locF 𝔭 B₀) 𝔭 (k + c) * orbCount h (locF 𝔭 A₀) (locF 𝔭 B₀) *
        Ideal.absNorm 𝔭 ^ (finrank K V ^ 2 * c + finrank K V * vd h (locF 𝔭 A₀) 𝔭) := by
    rw [hakA, hakB, ← horbAB, ← horbBA, ← hNNi, ← hIJ, ← e4, e5]
    ring
  have hQ : (Ideal.absNorm 𝔭 : ℝ) ≠ 0 := by
    have hb : 𝔭 ≠ ⊥ :=
      Ring.ne_bot_of_isMaximal_of_not_isField h𝔭 (NumberField.RingOfIntegers.not_isField F)
    exact_mod_cast fun h0 => hb (Ideal.absNorm_eq_zero_iff.mp h0)
  have Er : (akCount h (locF 𝔭 A₀) 𝔭 k : ℝ) * (Ideal.absNorm 𝔭 : ℝ) ^ (2 * finrank K V ^ 2 * c) *
      (Ideal.absNorm 𝔭 : ℝ) ^ (finrank K V * vd h (locF 𝔭 B₀) 𝔭) *
        (orbCount h (locF 𝔭 B₀) (locF 𝔭 A₀) : ℝ) =
      (akCount h (locF 𝔭 B₀) 𝔭 (k + c) : ℝ) * (orbCount h (locF 𝔭 A₀) (locF 𝔭 B₀) : ℝ) *
        (Ideal.absNorm 𝔭 : ℝ) ^ (finrank K V ^ 2 * c + finrank K V * vd h (locF 𝔭 A₀) 𝔭) := by
    exact_mod_cast E
  rw [hαA, hαB, div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
    div_eq_div_iff (pow_ne_zero _ hQ) (pow_ne_zero _ hQ)]
  apply mul_right_cancel₀ (pow_ne_zero (finrank K V ^ 2 * c) hQ)
  linear_combination ((Ideal.absNorm 𝔭 : ℝ) ^ (k * finrank K V ^ 2)) * Er

end Formalism.HermitianLattices.Ext.L3
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassConstSucc
section
open NumberField Module Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

namespace Step

theorem final_algebra (μ c lam D P a mm vv sq lV : ℝ) (f : ℕ) (hD : 0 < D) (hP : 0 < P)
    (ha : 0 < a) (hmm : 0 < mm) (hvv : 0 < vv) (hsq : 0 < sq)
    (h : μ * ((P / (mm * a)) ^ f / (vv * D)) = 0 + c * lam * D⁻¹ * ((mm ^ f)⁻¹ / sq * lV)) :
    μ = c * ((a / P) ^ f * vv / sq * lV) * lam := by
  have hD' := hD.ne'
  have hP' := hP.ne'
  have ha' := ha.ne'
  have hmm' := hmm.ne'
  have hvv' := hvv.ne'
  have hsq' := hsq.ne'
  have hX : (P / (mm * a)) ^ f / (vv * D) ≠ 0 := by positivity
  rw [zero_add] at h
  rw [eq_div_of_mul_eq hX h, div_pow, mul_pow, div_pow]
  field_simp

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem normD_pos {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) : 0 < normD h L := by
  have hd' : ∀ x, h x x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨φ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := hd x hne φ
    simp [hx] at this
  have hne := LocF.discrIdeal_ne_bot hd' hL hLi
  unfold normD
  apply Real.sqrt_pos.mpr
  have : Ideal.absNorm (discrIdeal h L) ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hne
  exact_mod_cast Nat.pos_of_ne_zero this

theorem tendsto_left (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {s : Finset (Submodule (𝓞 K) V)} (hsr : Formalism.ThetaLiftIndependence.IsClassReps h L s) :
    Tendsto (fun j : ℕ => (∑ M ∈ s, (ballCount h M ((j : ℝ) ^ 2) : ℝ) /
        (Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℝ)) / (j : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V))
      atTop (𝓝 (Formalism.HermitianLatticesTheory.mass h L *
        ((Real.pi ^ finrank K V / ((finrank K V).factorial : ℝ)) ^ Formalism.HermitianLatticesTheory.fDeg K /
          (Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V) * normD h L)))) := by
  rw [RankOne.mass_eq_sum h L s hsr, Finset.sum_mul]
  simp_rw [Finset.sum_div]
  refine tendsto_finsetSum _ fun M hM => ?_
  have hg := hsr.1 M hM
  obtain ⟨hMi, -, hMD⟩ := integral_of_mem_genus hK hF hs hd hL hLi hg
  have ht := (tendsto_ballCount hK hF hs hd hg.1 hMi).const_mul
    ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℝ)⁻¹)
  rw [hMD] at ht
  refine ht.congr fun j => ?_
  rw [div_eq_mul_inv (ballCount h M ((j : ℝ) ^ 2) : ℝ), div_eq_mul_inv, div_eq_mul_inv]
  ring

theorem tendsto_right (hH : HermRepUnram) (hLI : LIStat) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    (hm : 2 ≤ finrank K V) {c : ℝ} (hc : MassConst K F (finrank K V - 1) c) :
    Tendsto (fun j : ℕ => (Formalism.HermitianLatticesTheory.mass h L + ∑ᶠ n ∈ boxSet K F ((j : ℝ) ^ 2),
        repMass h L (algebraMap F K (n : F))) / (j : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V))
      atTop (𝓝 (0 + c * lamG F h L * (normD h L)⁻¹ *
        ((finrank K V : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
          Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) * lValEtaF K F (finrank K V)))) := by
  have hf : 0 < Formalism.HermitianLatticesTheory.fDeg K := Fintype.card_pos
  have hexp : 2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V ≠ 0 := by positivity
  have h1 : Tendsto (fun j : ℕ => Formalism.HermitianLatticesTheory.mass h L /
      (j : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((tendsto_pow_atTop hexp).comp tendsto_natCast_atTop_atTop)
  have h2 := (tendsto_singS_sum hK hF hs hd hL hLi hm).const_mul
    (c * lamG F h L * (normD h L)⁻¹)
  refine (h1.add h2).congr fun j => ?_
  rw [add_div]
  congr 1
  rw [finsum_mem_congr rfl fun n hn => repMass_eq hH hLI hK hF hs hd hL hLi hm hc hn,
    finsum_mem_eq_finite_toFinset_sum _ (A5.boxSet_finite hK hF ((j : ℝ) ^ 2)),
    finsum_mem_eq_finite_toFinset_sum _ (A5.boxSet_finite hK hF ((j : ℝ) ^ 2)),
    ← Finset.mul_sum, zpow_neg, zpow_natCast, ← pow_mul, ← mul_assoc 2, div_eq_mul_inv]
  ring

end Step

theorem massConst_succ (hH : HermRepUnram) (hLI : LIStat) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K)
    (hF : IsFixF K F) {m : ℕ} (hm : 2 ≤ m) {c : ℝ} (hc0 : 0 < c) (hc : MassConst K F (m - 1) c) :
    MassConst K F m (c * Formalism.HermitianLatticesTheory.massRatioRightSide K m) := by
  unfold MassConst
  intro V _ _ _ _ _ h L hs hd hfin hL hLi
  subst hfin
  obtain ⟨s, hsr⟩ := StabilizerLattices.exists_classReps hs hd hL.toIsLattice
  have hlim := Step.tendsto_left hK hF hs hd hL hLi hsr
  have hlim2 := Step.tendsto_right hH hLI hK hF hs hd hL hLi hm hc
  have hfun : (fun j : ℕ => (∑ M ∈ s, (ballCount h M ((j : ℝ) ^ 2) : ℝ) /
        (Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℝ)) / (j : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V)) =
      fun j : ℕ => (Formalism.HermitianLatticesTheory.mass h L + ∑ᶠ n ∈ boxSet K F ((j : ℝ) ^ 2),
        repMass h L (algebraMap F K (n : F))) / (j : ℝ) ^ (2 * Formalism.HermitianLatticesTheory.fDeg K * finrank K V) := by
    funext j
    rw [sum_ballCount_eq hK hF hs hd hL.toIsLattice hLi hsr (by positivity)]
  rw [hfun] at hlim
  have hAB := tendsto_nhds_unique hlim hlim2
  have hn0 : 0 < finrank K V := by omega
  have hfact : ((finrank K V).factorial : ℝ) =
      (finrank K V : ℝ) * ((finrank K V - 1).factorial : ℝ) := by
    rw [← Nat.mul_factorial_pred hn0.ne']
    push_cast
    ring
  rw [hfact, zpow_neg, zpow_natCast] at hAB
  have hv := vInv_pos K
  have key := Step.final_algebra (Formalism.HermitianLatticesTheory.mass h L) c (lamG F h L) (normD h L)
    (Real.pi ^ finrank K V) ((finrank K V - 1).factorial : ℝ) (finrank K V : ℝ)
    (Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * finrank K V))
    (Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K)) (lValEtaF K F (finrank K V))
    (Formalism.HermitianLatticesTheory.fDeg K) (Step.normD_pos hd hL hLi) (by positivity) (by positivity)
    (by exact_mod_cast hn0) (by positivity) (by positivity) hAB
  rw [massRatio_eq_lvalue hK hF (finrank K V) hm]
  exact key

end Formalism.HermitianLattices.Ext.L3
end
end

