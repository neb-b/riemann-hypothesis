module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0031
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0027
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.NormRepCountEqEulerFacInert
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0012
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.UnitaryDensityFieldFurther
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0015
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0037
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0020
public import Formalism.ThetaLiftIndependence.ThetaOrbitSums.ClassRepsDefinite
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardFibGEqProd
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.Bundle0038

@[expose] public section

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlphaNOfVdZeroUnit
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

namespace unitaryAbsoluteValueBounds

theorem abs_eta_pow (𝔭 : Ideal (𝓞 F)) (M : ℕ) : |etaF K F 𝔭 ^ M| = 1 := by
  have hη : etaF K F 𝔭 = 1 ∨ etaF K F 𝔭 = -1 := by
    unfold etaF
    split_ifs <;> simp
  rcases hη with h | h <;> rw [h] <;> simp

theorem abs_x_eq (𝔭 : Ideal (𝓞 F)) (m : ℕ) :
    |etaF K F 𝔭 ^ m * ((Ideal.absNorm 𝔭 : ℝ) ^ (m - 1))⁻¹| = ((Ideal.absNorm 𝔭 : ℝ) ^ (m - 1))⁻¹ := by
  rw [abs_mul, abs_eta_pow, one_mul, abs_of_nonneg (by positivity)]

theorem alphaN_rank_zero (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hm : finrank K V = 0) {n : 𝓞 F} (hn : n ≠ 0) : alphaN h L 𝔭 n = 0 := by
  have hsub : Subsingleton V := finrank_zero_iff.1 hm
  have hLfull : Submodule.IsFullLattice K L :=
    { toIsLattice := hL, span_eq_top := Subsingleton.elim _ _ }
  rw [firstFamilyOperatorEnd.alphaN_eq hK hF hs hd hLfull hLi h𝔭
    (localValuationFiltration.notMem_pow_vF h𝔭 hn)
    (k := 2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2) (by omega)]
  have h0 : nkCount h L 𝔭 (2 * vd h L 𝔭 + 2 * vF 𝔭 n + 2) n = 0 := by
    unfold nkCount
    rw [Nat.card_eq_zero]
    left
    constructor
    rintro ⟨x, y, -, hc⟩
    have hy : h (y : V) (y : V) = algebraMap F K ((0 : 𝓞 F) : F) := by
      rw [Subsingleton.elim (y : V) 0]
      simp
    rw [hy, MeanB.congrP_algebraMap_iff_sub_mem h𝔭, zero_sub, neg_mem_iff, mem_pow_iff_le_vF h𝔭 hn] at hc
    omega
  rw [h0]
  simp

end unitaryAbsoluteValueBounds

theorem alphaN_of_vd_zero_unit (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0)
    (hm : 1 ≤ finrank K V) {n : 𝓞 F} (hn : n ∉ 𝔭) :
    alphaN h L 𝔭 n = (1 - etaF K F 𝔭 ^ finrank K V * (Ideal.absNorm 𝔭 : ℝ) ^ (-(finrank K V : ℤ))) :=
  unitaryAbsoluteValueBounds.alphaN_unit hK hF hs hd (by first | exact hL | exact hL.toIsLattice) hLi h𝔭 hv hm hn

theorem alphaN_eq_of_vF_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0)
    {n n' : 𝓞 F} (hn : n ≠ 0) (hn' : n' ≠ 0) (hvv : vF 𝔭 n = vF 𝔭 n') :
    alphaN h L 𝔭 n = alphaN h L 𝔭 n' := by
  rcases Nat.eq_zero_or_pos (finrank K V) with hm | hm
  · rw [unitaryAbsoluteValueBounds.alphaN_rank_zero hK hF hs hd hL.toIsLattice hLi h𝔭 hm hn,
      unitaryAbsoluteValueBounds.alphaN_rank_zero hK hF hs hd hL.toIsLattice hLi h𝔭 hm hn']
  · rw [unitaryAbsoluteValueBounds.alphaN_closed hK hF hs hd (by first | exact hL | exact hL.toIsLattice) hLi h𝔭 hv hm _ n hn rfl, unitaryAbsoluteValueBounds.alphaN_closed hK hF hs hd (by first | exact hL | exact hL.toIsLattice) hLi h𝔭 hv hm _ n' hn' rfl, hvv]

theorem alphaN_rho_diff_bound (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0) {n n' : 𝓞 F} (hn : n ≠ 0) (hn' : n' ≠ 0)
    (hvv : vF 𝔭 n = vF 𝔭 n' + 1) :
    |alphaN h L 𝔭 n / (1 - etaF K F 𝔭 ^ finrank K V * (Ideal.absNorm 𝔭 : ℝ) ^ (-(finrank K V : ℤ))) - alphaN h L 𝔭 n' / (1 - etaF K F 𝔭 ^ finrank K V * (Ideal.absNorm 𝔭 : ℝ) ^ (-(finrank K V : ℤ)))| ≤
      8 * ((vF 𝔭 n : ℝ) + 1) ^ 2 *
        (Ideal.absNorm 𝔭 : ℝ) ^ (-(((finrank K V - 1) * ((vF 𝔭 n + 1) / 2) : ℕ) : ℤ)) := by
  have hq : (1 : ℝ) < (Ideal.absNorm 𝔭 : ℝ) := unitaryAbsoluteValueBounds.one_lt_q h𝔭
  rw [unitaryAbsoluteValueBounds.alphaN_closed hK hF hs hd (by first | exact hL | exact hL.toIsLattice) hLi h𝔭 hv (by omega) _ n hn rfl,
    unitaryAbsoluteValueBounds.alphaN_closed hK hF hs hd (by first | exact hL | exact hL.toIsLattice) hLi h𝔭 hv (by omega) _ n' hn' rfl,
    mul_div_cancel_left₀ _ (unitaryAbsoluteValueBounds.beta_pos h𝔭 (by omega)).ne',
    mul_div_cancel_left₀ _ (unitaryAbsoluteValueBounds.beta_pos h𝔭 (by omega)).ne', hvv,
    Finset.sum_range_succ _ (vF 𝔭 n' + 1), add_sub_cancel_left, abs_pow, unitaryAbsoluteValueBounds.abs_x_eq, zpow_neg,
    zpow_natCast, inv_pow, ← pow_mul]
  have h1 : ((Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * (vF 𝔭 n' + 1)))⁻¹ ≤
      ((Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * ((vF 𝔭 n' + 1 + 1) / 2)))⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hq.le (Nat.mul_le_mul_left _ (by omega)))
  have h2 : (0 : ℝ) ≤ ((Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * ((vF 𝔭 n' + 1 + 1) / 2)))⁻¹ := by
    positivity
  have h3 : (1 : ℝ) ≤ 8 * (((vF 𝔭 n' + 1 : ℕ) : ℝ) + 1) ^ 2 := by
    have : (0 : ℝ) ≤ ((vF 𝔭 n' + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  calc _ ≤ _ := h1
    _ = 1 * _ := (one_mul _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right h3 h2

end Formalism.HermitianLattices.Ext.L3
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsMassConstOne
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace RankOne

open Formalism.HermitianLatticesTheory Formalism.ThetaLiftIndependence

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem trace_pos {h : V →ₗ⋆[K] V →ₗ[K] K} (hd : IsTotPosDef h) :
    ∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x) := by
  intro x hx
  have hsum := trace_eq_sum_embeddings ℂ (K := ℚ) (x := h x x)
  have hre : ((Algebra.trace ℚ K (h x x) : ℚ) : ℝ) = ∑ σ : K →ₐ[ℚ] ℂ, (σ (h x x)).re := by
    have := congrArg Complex.re hsum
    simpa [Complex.re_sum] using this
  have hne : Nonempty (K →ₐ[ℚ] ℂ) := ⟨IsAlgClosed.lift⟩
  have hpos : 0 < ∑ σ : K →ₐ[ℚ] ℂ, (σ (h x x)).re :=
    Finset.sum_pos (fun σ _ => hd x hx σ.toRingHom) Finset.univ_nonempty
  exact_mod_cast hre ▸ hpos

theorem exists_model [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (hd : IsTotPosDef h) (h1 : finrank K V = 1) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) :
    ∃ (h' : K →ₗ⋆[K] K →ₗ[K] K) (A : Submodule (𝓞 K) K), h' 1 1 ≠ 0 ∧ Submodule.IsFullLattice K A ∧
      (∃ s, IsClassReps h' A s) ∧ mass h' A = mass h L := by
  let b := Module.finBasisOfFinrankEq K V h1
  let φ : V ≃ₗ[K] K := b.equivFun.trans (LinearEquiv.funUnique (Fin 1) K K)
  let h' : K →ₗ⋆[K] K →ₗ[K] K := (h.comp φ.symm.toLinearMap).compl₂ φ.symm.toLinearMap
  have hh' : ∀ x y, h' (φ x) (φ y) = h x y := by
    intro x y
    simp [h']
  have htr := trace_pos hd
  obtain ⟨hex, -, -⟩ := Formalism.HermitianLatticesTheory.massBasic K V h hs htr L hL
  obtain ⟨hex', hm⟩ := mass_mapE φ hh' hex
  refine ⟨h', mapE φ L, ?_, isFullLattice_mapE φ hL, hex', hm⟩
  have h0 : φ.symm 1 ≠ 0 := by simp
  intro hz
  have := htr _ h0
  have hz' : h (φ.symm 1) (φ.symm 1) = 0 := by simpa [h'] using hz
  rw [hz', map_zero] at this
  exact lt_irrefl _ this

end RankOne

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem exists_massConst_one (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) :
    ∃ c : ℝ, 0 < c ∧ MassConst K F 1 c := by
  obtain ⟨h₀, hh⟩ : ∃ h₀ : K →ₗ⋆[K] K →ₗ[K] K, ∀ x y, h₀ x y = star x * y :=
    ⟨LinearMap.mk₂'ₛₗ (starRingEnd K) (RingHom.id K) (fun x y => star x * y)
      (fun x y z => by simp [add_mul]) (fun a x y => by simp [smul_eq_mul, mul_assoc, starRingEnd_apply])
      (fun x y z => by simp [mul_add]) (fun a x y => by simp [smul_eq_mul, mul_left_comm]),
      fun _ _ => rfl⟩
  have hs₀ : h₀.IsSymm := by
    first
      | (intro x y; simp [hh, starRingEnd_apply, mul_comm])
      | (constructor; intro x y; simp [hh, starRingEnd_apply, mul_comm])
  have hd₀ : IsTotPosDef h₀ := by
    intro x hx φ
    have hx' : φ x ≠ 0 := (map_ne_zero φ).mpr hx
    have : φ (h₀ x x) = ((Complex.normSq (φ x) : ℝ) : ℂ) := by
      rw [hh, map_mul, hK.2.1 φ x, Complex.normSq_eq_conj_mul_self]
    rw [this, Complex.ofReal_re]
    exact Complex.normSq_pos.mpr hx'
  have hn₀ : h₀ 1 1 ≠ 0 := by simp [hh]
  set L₀ : Submodule (𝓞 K) K := Submodule.span (𝓞 K) {(1 : K)}
  have hL₀ : Submodule.IsFullLattice K L₀ :=
    { toIsLattice := Submodule.IsLattice.of_fg K (Submodule.fg_span_singleton _)
      span_eq_top := RankOne.span_eq_top_of_ne_zero (Submodule.subset_span rfl) one_ne_zero }
  obtain ⟨hex₀, -, hpos₀⟩ := Formalism.HermitianLatticesTheory.massBasic K K h₀ hs₀
    (RankOne.trace_pos hd₀) L₀ hL₀
  refine ⟨Formalism.HermitianLatticesTheory.mass h₀ L₀, hpos₀, ?_⟩
  intro V _ _ _ _ _ h L hs hd h1 hL hLi
  obtain ⟨h', A, hn', hA, -, hm⟩ := RankOne.exists_model hs hd h1 hL
  have hlam : lamG F h L = 1 := by
    unfold lamG
    exact (tprod_congr fun p => localFactor_rank_one hK hF hs hd hL hLi h1 p.2).trans tprod_one
  rw [hlam, mul_one, ← hm]
  exact RankOne.mass_eq_of_lattices hn₀ hn' hL₀ hA hex₀

end Formalism.HermitianLattices.Ext.L3
end
end

-- bundled from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.RepMassEqProdPsi
section
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem repMass_eq_prod_psi (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {c : ℝ}
    (hc : MassConst K F (finrank K V - 1) c) :
    repMass h L (h S.x₀ S.x₀) = c * ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, psiP S L 𝔭.1 :=
  MassProductFormula.repMass_eq_prod_psi' hK hF hs hd S (by first | exact hL | exact hL.toIsLattice) hLi hc

end Formalism.HermitianLattices.Ext.L3
end
end

