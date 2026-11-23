module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0001
public import GroundTheory.GlobalFields.TateThesis.Bundle0009
public import GroundTheory.AutomorphicForms.Bundle0019
public import GroundTheory.AutomorphicForms.GL2.GJGlobalLattice
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import GroundTheory.GlobalFields.TateThesis.IdeleMeasure

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.UnipotentInvariants.AbLeMulOneAddNormOfFinPartMemCompact
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical


open scoped nonZeroDivisors in
private theorem one_le_of_mem {d : 𝓞 ℚ} (hd0 : d ≠ 0) {e : ℚ} (he : e ≠ 0)
    (h : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (algebraMap (𝓞 ℚ) ℚ d * e) ∈
      integralFiniteAdeles (𝓞 ℚ) ℚ) :
    1 ≤ |((algebraMap (𝓞 ℚ) ℚ d : ℚ) : ℝ)| * |(e : ℝ)| := by
  have h2 : algebraMap (𝓞 ℚ) ℚ d * e ∈ ((1 : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ) : FractionalIdeal (𝓞 ℚ)⁰ ℚ) := by
    rw [← algebraMap_mem_idealFiniteAdeles_iff, ← SetLike.mem_coe, idealFiniteAdeles_one]
    exact h
  rw [Units.val_one] at h2
  obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp h2
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp (RingOfIntegers.isIntegral_coe r)
  have hdK : algebraMap (𝓞 ℚ) ℚ d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 ℚ) ℚ)).mpr hd0
  have hnq : (n : ℚ) = algebraMap (𝓞 ℚ) ℚ d * e := by
    rw [← hr]
    exact hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : algebraMap (𝓞 ℚ) ℚ d * e ≠ 0 := mul_ne_zero hdK he
    exact this (by simpa using hnq.symm)
  have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn0
  rw [← abs_mul]
  have : (n : ℝ) = ((algebraMap (𝓞 ℚ) ℚ d : ℚ) : ℝ) * (e : ℝ) := by
    have := congrArg (fun q : ℚ => (q : ℝ)) hnq
    simpa using this
  rwa [this] at h1

private theorem norm_rt (w : InfinitePlace ℚ) (c : ℚ) : ‖(rt c : A ℚ).1 w‖ = |(c : ℝ)| := by
  have h : InfinitePlace.Completion.extensionEmbedding w ((rt c : A ℚ).1 w) = w.embedding c := by
    rw [AdeleRing.algebraMap_fst_apply, InfinitePlace.Completion.extensionEmbedding_coe]
    rfl
  have h2 := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) ((rt c : A ℚ).1 w)
  rw [← h2, h, InfinitePlace.norm_embedding_eq, Rat.infinitePlace_apply, Rat.cast_abs]


open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction in
private theorem idele_le {K1 : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)} (hK : IsCompact K1) (w : InfinitePlace ℚ) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : IdeleGroup ℚ, ((x : A ℚ)).2 ∈ K1 → ab x ≤ M * ‖(x : A ℚ).1 w‖ := by
  obtain ⟨S, hS, hSm⟩ := exists_isCompact_mul_mem_of_ideleModule_mem_Icc (K := ℚ) one_pos 1
  set Q : Set (FiniteAdeleRing (𝓞 ℚ) ℚ) :=
    (fun p : IdeleGroup ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ => (((p.1⁻¹ : IdeleGroup ℚ) : A ℚ)).2 * p.2) '' (S ×ˢ K1)
  have hi : Continuous fun u : IdeleGroup ℚ => (((u⁻¹ : IdeleGroup ℚ) : A ℚ)).2 :=
    continuous_snd.comp Units.continuous_coe_inv
  have hQ : IsCompact Q := (hS.prod hK).image ((hi.comp continuous_fst).mul continuous_snd)
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact hQ
  have hc : Continuous fun u : IdeleGroup ℚ => ‖(((u⁻¹ : IdeleGroup ℚ) : A ℚ)).1 w‖ :=
    continuous_norm.comp ((continuous_apply w).comp (continuous_fst.comp Units.continuous_coe_inv))
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hc.continuousOn
  set b := max B 1
  have hb1 : 1 ≤ b := le_max_right _ _
  set D : ℝ := |((algebraMap (𝓞 ℚ) ℚ d : ℚ) : ℝ)|
  have hdK : algebraMap (𝓞 ℚ) ℚ d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 ℚ) ℚ)).mpr hd0
  have hD : 0 < D := abs_pos.2 (by exact_mod_cast hdK)
  refine ⟨D * b, by positivity, fun x hx => ?_⟩
  have hρ : 0 < ab x := (IdeleGroup.ideleModule ℚ x).2
  set p : IdeleGroup ℚ := posIdele (ab x) hρ with hp
  have hm : (IdeleGroup.ideleModule ℚ (p⁻¹ * x) : ℝ) = 1 := by
    have h1 : (IdeleGroup.ideleModule ℚ (p⁻¹ * x) : ℝ) =
        ((IdeleGroup.ideleModule ℚ p : ℝ))⁻¹ * (IdeleGroup.ideleModule ℚ x : ℝ) := by
      simp [map_mul, map_inv]
    rw [h1, hp, ideleModule_posIdele]
    change (ab x ^ Module.finrank ℚ ℚ)⁻¹ * ab x = 1
    rw [Module.finrank_self, pow_one, inv_mul_cancel₀ hρ.ne']
  obtain ⟨t, ht⟩ := hSm _ hm.ge hm.le
  set u := IdeleGroup.diagonal ℚ t * (p⁻¹ * x) with hu
  have hux : ((u⁻¹ * x : IdeleGroup ℚ) : A ℚ) = rt ((t : ℚ)⁻¹) * (p : A ℚ) := by
    have e1 : u⁻¹ * x = IdeleGroup.diagonal ℚ t⁻¹ * p := by
      rw [hu, map_inv, mul_inv, mul_inv, inv_inv, mul_assoc, mul_assoc, inv_mul_cancel, mul_one]
    rw [e1, Units.val_mul, IdeleGroup.coe_diagonal, Units.val_inv_eq_inv_val]
  have hp2 : (((p : IdeleGroup ℚ) : A ℚ)).2 = 1 := by
    apply RestrictedProduct.ext
    intro v
    exact posIdele_finite _ hρ v
  have hmem : algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((t : ℚ)⁻¹) ∈ Q := by
    refine ⟨(u, (x : A ℚ).2), ⟨ht, hx⟩, ?_⟩
    have := congrArg Prod.snd hux
    rw [Units.val_mul] at this
    change (((u⁻¹ : IdeleGroup ℚ) : A ℚ)).2 * (x : A ℚ).2 = (rt ((t : ℚ)⁻¹) : A ℚ).2 * (((p : IdeleGroup ℚ) : A ℚ)).2 at this
    rw [hp2, mul_one] at this
    exact this
  have hint : 1 ≤ D * |(((t : ℚ)⁻¹ : ℚ) : ℝ)| := by
    refine one_le_of_mem hd0 (inv_ne_zero t.ne_zero) ?_
    rw [map_mul]
    exact hd _ hmem
  have hub : ‖(((u⁻¹ : IdeleGroup ℚ) : A ℚ)).1 w‖ ≤ b :=
    ((le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hB u ht))).trans (le_max_left _ _)
  have hu1 : 1 ≤ b * ‖(((u : IdeleGroup ℚ) : A ℚ)).1 w‖ := by
    have e : (((u⁻¹ : IdeleGroup ℚ) : A ℚ)).1 w * (((u : IdeleGroup ℚ) : A ℚ)).1 w = 1 :=
      congrFun (congrArg Prod.fst (Units.inv_mul u)) w
    have e2 := congrArg norm e
    rw [norm_mul, norm_one] at e2
    rw [← e2]
    exact mul_le_mul_of_nonneg_right hub (norm_nonneg _)
  have hxu : (x : A ℚ) = rt ((t : ℚ)⁻¹) * (p : A ℚ) * (u : A ℚ) := by
    rw [← hux, Units.val_mul, mul_comm, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  have hxw : ‖(x : A ℚ).1 w‖ = |(((t : ℚ)⁻¹ : ℚ) : ℝ)| * ab x * ‖(((u : IdeleGroup ℚ) : A ℚ)).1 w‖ := by
    have e : (x : A ℚ).1 w = (rt ((t : ℚ)⁻¹) : A ℚ).1 w * (((p : IdeleGroup ℚ) : A ℚ)).1 w * (((u : IdeleGroup ℚ) : A ℚ)).1 w :=
      congrFun (congrArg Prod.fst hxu) w
    rw [e, norm_mul, norm_mul, norm_rt, hp, norm_posIdele_infinite]
  rw [hxw]
  set T := |(((t : ℚ)⁻¹ : ℚ) : ℝ)|
  set U := ‖(((u : IdeleGroup ℚ) : A ℚ)).1 w‖
  have h3 : 1 ≤ (D * T) * (b * U) := by
    have hU : 0 ≤ b * U := by positivity
    nlinarith
  calc ab x = ab x * 1 := (mul_one _).symm
    _ ≤ ab x * ((D * T) * (b * U)) := by gcongr
    _ = D * b * (T * ab x * U) := by ring

theorem UpperTheory.ab_le_mul_one_add_norm_of_finPart_mem_compact :
    ∀ (K : Set (Fin 4 → FiniteAdeleRing (𝓞 ℚ) ℚ)) (δ : ℚ), IsCompact K → ∃ L : ℝ, 0 < L ∧ ∀ (a : (A ℚ)ˣ) (ξ : Fin 4 → ℚ), qr δ ξ ≠ 0 → finPartPi (sc a ξ) ∈ K → ab a ≤ L * (1 + ‖infPartPi (sc a ξ)‖) := by
  intro K δ hK
  obtain ⟨w⟩ : Nonempty (InfinitePlace ℚ) := inferInstance
  set g : (Fin 4 → FiniteAdeleRing (𝓞 ℚ) ℚ) → FiniteAdeleRing (𝓞 ℚ) ℚ :=
    fun v => v 2 ^ 2 - (rt δ : A ℚ).2 * v 3 ^ 2 - v 1 * v 0 with hgdef
  have hg : Continuous g := by
    have h0 := continuous_apply (A := fun _ : Fin 4 => FiniteAdeleRing (𝓞 ℚ) ℚ) (0 : Fin 4)
    have h1 := continuous_apply (A := fun _ : Fin 4 => FiniteAdeleRing (𝓞 ℚ) ℚ) (1 : Fin 4)
    have h2 := continuous_apply (A := fun _ : Fin 4 => FiniteAdeleRing (𝓞 ℚ) ℚ) (2 : Fin 4)
    have h3 := continuous_apply (A := fun _ : Fin 4 => FiniteAdeleRing (𝓞 ℚ) ℚ) (3 : Fin 4)
    exact ((h2.pow 2).sub (continuous_const.mul (h3.pow 2))).sub (h1.mul h0)
  obtain ⟨M, hM0, hM⟩ := idele_le (hK.image hg) w
  have hδ : 0 ≤ |(δ : ℝ)| := abs_nonneg _
  refine ⟨M * (2 + |(δ : ℝ)|) + 1, by positivity, fun a ξ hT hfin => ?_⟩
  set x : IdeleGroup ℚ := a ^ 2 * IdeleGroup.diagonal ℚ (Units.mk0 (qr δ ξ) hT) with hxdef
  have hx : (x : A ℚ) = q4 δ (sc a ξ) := by
    rw [hxdef, Units.val_mul, Units.val_pow_eq_pow_val, IdeleGroup.coe_diagonal]
    simp only [Units.val_mk0, qr, q4, sc, map_sub, map_mul, map_pow]
    ring
  have hxf : ((x : A ℚ)).2 ∈ g '' K := ⟨finPartPi (sc a ξ), hfin, by rw [hx]; rfl⟩
  have hab : ab x = ab a ^ 2 := by
    rw [hxdef, ab_mul, ab_pow, ab_diagonal, mul_one]
  set N := ‖infPartPi (sc a ξ)‖ with hN
  have hN0 : 0 ≤ N := norm_nonneg _
  have hc : ∀ i, ‖(sc a ξ i).1 w‖ ≤ N := fun i =>
    (GroundTheory.Automorphic.GJGlobal.norm_apply_le_norm_homeomorphMixedSpace _ w).trans
      (norm_le_pi_norm (infPartPi (sc a ξ)) i)
  have hxw : ‖(x : A ℚ).1 w‖ ≤ (2 + |(δ : ℝ)|) * N ^ 2 := by
    have e : (x : A ℚ).1 w = (sc a ξ 2).1 w ^ 2 - (rt δ : A ℚ).1 w * (sc a ξ 3).1 w ^ 2 -
        (sc a ξ 1).1 w * (sc a ξ 0).1 w := by
      rw [hx]
      rfl
    rw [e]
    have h1 := norm_sub_le ((sc a ξ 2).1 w ^ 2 - (rt δ : A ℚ).1 w * (sc a ξ 3).1 w ^ 2)
      ((sc a ξ 1).1 w * (sc a ξ 0).1 w)
    have h2 := norm_sub_le ((sc a ξ 2).1 w ^ 2) ((rt δ : A ℚ).1 w * (sc a ξ 3).1 w ^ 2)
    rw [norm_mul] at h1
    rw [norm_mul, norm_pow, norm_pow, norm_rt] at h2
    have p2 : ‖(sc a ξ 2).1 w‖ ^ 2 ≤ N ^ 2 := by gcongr; exact hc 2
    have p3 : ‖(sc a ξ 3).1 w‖ ^ 2 ≤ N ^ 2 := by gcongr; exact hc 3
    have p10 : ‖(sc a ξ 1).1 w‖ * ‖(sc a ξ 0).1 w‖ ≤ N * N := by
      gcongr
      · exact hc 1
      · exact hc 0
    have p3' : |(δ : ℝ)| * ‖(sc a ξ 3).1 w‖ ^ 2 ≤ |(δ : ℝ)| * N ^ 2 := by gcongr
    nlinarith
  have hsq : ab a ^ 2 ≤ ((M * (2 + |(δ : ℝ)|) + 1) * (1 + N)) ^ 2 := by
    have h1 := hM x hxf
    rw [hab] at h1
    have h2 : M * ‖(x : A ℚ).1 w‖ ≤ M * ((2 + |(δ : ℝ)|) * N ^ 2) := by gcongr
    set P := M * (2 + |(δ : ℝ)|) with hP
    have hP0 : 0 ≤ P := by positivity
    have h3 : P * N ^ 2 ≤ ((P + 1) * (1 + N)) ^ 2 := by
      have : N ^ 2 ≤ (1 + N) ^ 2 := by nlinarith
      have h4 : P ≤ (P + 1) ^ 2 := by nlinarith
      calc P * N ^ 2 ≤ (P + 1) ^ 2 * (1 + N) ^ 2 := by gcongr
        _ = _ := by ring
    calc ab a ^ 2 ≤ M * ((2 + |(δ : ℝ)|) * N ^ 2) := h1.trans h2
      _ = P * N ^ 2 := by rw [hP]; ring
      _ ≤ _ := h3
  exact abs_le_of_sq_le_sq' hsq (by positivity) |>.2
end

-- bundled from Development.AutomorphicArithmetic.UnipotentInvariants.ExistsCompactSiegelDecompositionHeightLe
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E]

private theorem pos_snd (s : ℝ) (hs : 0 < s) :
    (((GroundTheory.Automorphic.Reduction.posIdele s hs : IdeleGroup E) : A E)).2 = 1 := by
  apply RestrictedProduct.ext
  intro v
  exact GroundTheory.Automorphic.Reduction.posIdele_finite s hs v

private theorem pos_inv_snd (s : ℝ) (hs : 0 < s) :
    ((((GroundTheory.Automorphic.Reduction.posIdele s hs : IdeleGroup E)⁻¹ : IdeleGroup E) : A E)).2 = 1 := by
  have e : ((((GroundTheory.Automorphic.Reduction.posIdele s hs : IdeleGroup E)⁻¹ : IdeleGroup E) : A E)).2 *
      (((GroundTheory.Automorphic.Reduction.posIdele s hs : IdeleGroup E) : A E)).2 = 1 :=
    congrArg Prod.snd (Units.inv_mul (GroundTheory.Automorphic.Reduction.posIdele s hs : IdeleGroup E))
  rwa [pos_snd, mul_one] at e

private theorem norm_pos_inv (s : ℝ) (hs : 0 < s) (w : InfinitePlace E) :
    ‖((((GroundTheory.Automorphic.Reduction.posIdele s hs : IdeleGroup E)⁻¹ : IdeleGroup E) : A E)).1 w‖ = s⁻¹ := by
  have e : ((((GroundTheory.Automorphic.Reduction.posIdele s hs : IdeleGroup E)⁻¹ : IdeleGroup E) : A E)).1 w *
      (((GroundTheory.Automorphic.Reduction.posIdele s hs : IdeleGroup E) : A E)).1 w = 1 :=
    congrArg (fun z : A E => z.1 w) (Units.inv_mul (GroundTheory.Automorphic.Reduction.posIdele s hs : IdeleGroup E))
  have h := congrArg norm e
  rw [norm_mul, GroundTheory.Automorphic.Reduction.norm_posIdele_infinite, norm_one] at h
  exact eq_inv_of_mul_eq_one_left h

variable [_root_.NumberField.IsTotallyComplex E]

private theorem norm_pInf (x : A E) (w : InfinitePlace E) : ‖pInf E x w‖ = ‖x.1 w‖ := by
  have e : pInf E x w = InfinitePlace.Completion.extensionEmbedding w (x.1 w) := by
    have h := UpperTheory.V.Cm.infEq_apply (pInf E x) w
    rw [show infEq E (pInf E x) = x.1 from (infEq E).apply_symm_apply x.1] at h
    rw [← InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply (IsTotallyComplex.isComplex w), h,
      RingEquiv.apply_symm_apply]
  rw [e]
  exact (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _

private theorem norm_toL_mD_le (q : (A E)ˣ) {r : ℝ} (hr : 0 ≤ r) (h1 : ∀ w, ‖(q : A E).1 w‖ ≤ r)
    (h2 : ∀ w, ‖((q⁻¹ : (A E)ˣ) : A E).1 w‖ ≤ r) :
    ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (gl (mD q))).val‖ ≤ r := by
  refine (pi_norm_le_iff_of_nonneg hr).2 fun i => (pi_norm_le_iff_of_nonneg hr).2 fun j =>
    (pi_norm_le_iff_of_nonneg hr).2 fun w => ?_
  change ‖pInf E ((mD q).1 i j) w‖ ≤ r
  rw [norm_pInf]
  fin_cases i <;> fin_cases j
  · simpa using h1 w
  · refine le_trans (le_of_eq ?_) hr
    simp
    first | exact norm_zero | rfl
  · refine le_trans (le_of_eq ?_) hr
    simp
    first | exact norm_zero | rfl
  · simpa using h2 w

end SlopeTestRemainingChoices

open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction in
theorem UpperTheory.exists_compact_siegel_decomposition_height_le :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (c : ℝ), 0 < c → ∃ (Y : Set (G1 E)) (C₂ : ℝ), IsCompact Y ∧ ∀ (u : A E) (b : (A E)ˣ), c ≤ ab b → ∃ (γ : Matrix.SpecialLinearGroup (Fin 2) E) (z : GL (Fin 2) (Cinf E)), ∃ w ∈ Y, gl (nU u * mD b) = gl (ratS E γ) * infGL E 2 z * gl w ∧ Ht z ≤ C₂ * ab b := by
  intro E _ _ _ c hc
  obtain ⟨S, hS, hSm⟩ := exists_isCompact_mul_mem_of_ideleModule_mem_Icc (K := E) hc c
  have hcont : Continuous fun x : InfiniteAdeleRing E => ∑ w : InfinitePlace E, ‖x w‖ :=
    continuous_finsetSum _ fun w _ => continuous_norm.comp (continuous_apply w)
  obtain ⟨M, hM⟩ := (isCompact_closure_fundamentalSetInfinite E).exists_bound_of_continuousOn hcont.continuousOn
  let L : Set (A E) := ((homeomorphMixedSpace E) ⁻¹' Metric.closedBall 0 M) ×ˢ
    (integralFiniteAdeles (𝓞 E) E : Set (FiniteAdeleRing (𝓞 E) E))
  have hL : IsCompact L :=
    ((homeomorphMixedSpace E).isCompact_preimage.2 (isCompact_closedBall _ _)).prod
      (isCompact_integralFiniteAdeles E)
  refine ⟨(fun x : A E × IdeleGroup E => nU x.1 * mD x.2) '' (L ×ˢ S), 3 / c, (hL.prod hS).image
    ((continuous_nU.comp continuous_fst).mul (continuous_mD.comp continuous_snd)), fun u b hb => ?_⟩
  set d := Module.finrank ℚ E
  have hd : d ≠ 0 := Module.finrank_pos.ne'
  have hx : 1 ≤ ab b / c := (one_le_div hc).2 hb
  set s := (ab b / c) ^ (d : ℝ)⁻¹
  have hs1 : 1 ≤ s := Real.one_le_rpow hx (by positivity)
  have hs0 : 0 < s := one_pos.trans_le hs1
  have hsd : s ^ d = ab b / c := Real.rpow_inv_natCast_pow (zero_le_one.trans hx) hd
  set p : IdeleGroup E := posIdele s hs0 with hp
  have hm : (IdeleGroup.ideleModule E (p⁻¹ * b) : ℝ) = c := by
    have h1 : (IdeleGroup.ideleModule E (p⁻¹ * b) : ℝ) =
        ((IdeleGroup.ideleModule E p : ℝ))⁻¹ * (IdeleGroup.ideleModule E b : ℝ) := by
      simp [map_mul, map_inv]
    have h2 : (0 : ℝ) < ab b := hc.trans_le hb
    rw [h1, hp, ideleModule_posIdele, hsd]
    change (ab b / c)⁻¹ * ab b = c
    field_simp
  obtain ⟨t, ht⟩ := hSm _ hm.ge hm.le
  set a : (A E)ˣ := IdeleGroup.diagonal E t with ha
  set w0 : IdeleGroup E := a * (p⁻¹ * b) with hw0
  have hb' : b = a⁻¹ * p * w0 := by
    rw [hw0, mul_assoc, mul_left_comm p, mul_inv_cancel_left, inv_mul_cancel_left]
  set v : A E := (a : A E) ^ 2 * u with hv
  obtain ⟨f, hf, -⟩ := existsUnique_sub_mem_fundamentalSet E v
  set u2 : A E := v - rt f with hu2
  set u3 : A E := (((p⁻¹ : IdeleGroup E) : (A E)ˣ) : A E) ^ 2 * u2 with hu3
  have h1 : nU u * mD a⁻¹ = mD a⁻¹ * nU v := by
    rw [mD_mul_nU a⁻¹ v]
    congr 2
    rw [hv, ← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]
  have h2 : nU v = nU (rt f) * nU u2 := by
    rw [← nU_add, hu2, add_sub_cancel]
  have h3 : nU u2 * mD p = mD p * nU u3 := by
    rw [mD_mul_nU p u3]
    congr 2
    rw [hu3, ← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]
  have hdec : nU u * mD b = (mD a⁻¹ * nU (rt f)) * mD p * (nU u3 * mD w0) := by
    calc nU u * mD b = (nU u * mD a⁻¹) * mD p * mD w0 := by rw [hb', mD_mul, mD_mul]; simp only [mul_assoc]
      _ = mD a⁻¹ * nU (rt f) * (nU u2 * mD p) * mD w0 := by rw [h1, h2]; simp only [mul_assoc]
      _ = _ := by rw [h3]; simp only [mul_assoc]
  have hG : mD a⁻¹ * nU (rt f) ∈ Gam E := by
    refine (Gam E).mul_mem ?_ (nU_rt_mem f)
    rw [mD_inv]
    exact (Gam E).inv_mem (mD_diagonal_mem t)
  obtain ⟨γ, hγ⟩ := hG
  have hu3L : u3 ∈ L := by
    have hpw : ∀ w, ‖u3.1 w‖ ≤ ‖u2.1 w‖ := fun w => by
      have e : u3.1 w = ((((p⁻¹ : IdeleGroup E) : A E)).1 w) ^ 2 * u2.1 w := rfl
      rw [e, norm_mul, norm_pow, hp, norm_pos_inv]
      have : (s⁻¹) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hs1)
      nlinarith [norm_nonneg (u2.1 w)]
    refine ⟨?_, ?_⟩
    · refine mem_closedBall_zero_iff.2 ?_
      refine (GJGlobal.norm_homeomorphMixedSpace_le_sum u3.1).trans ?_
      refine (Finset.sum_le_sum fun w _ => hpw w).trans ?_
      exact (le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hM u2.1 (subset_closure hf.1)))
    · have e : u3.2 = ((((p⁻¹ : IdeleGroup E) : A E)).2) ^ 2 * u2.2 := rfl
      rw [e, hp, pos_inv_snd, one_pow, one_mul]
      exact hf.2
  let z : GL (Fin 2) (Cinf E) := Matrix.GeneralLinearGroup.map (pInf E) (gl (mD p))
  have hz : infGL E 2 z = gl (mD p) := by
    refine ga_ext (pInf_infGL z) ?_
    rw [pFin_infGL]
    have hpf : pFin E (p : A E) = 1 := pos_snd s hs0
    have hpfi : pFin E (((p⁻¹ : IdeleGroup E) : (A E)ˣ) : A E) = 1 := pos_inv_snd s hs0
    refine Units.ext (Matrix.ext fun i j => ?_)
    change (1 : Matrix (Fin 2) (Fin 2) (Af E)) i j = pFin E ((mD p).1 i j)
    fin_cases i <;> fin_cases j <;> simp [hpf, hpfi]
  refine ⟨γ, z, nU u3 * mD w0, ⟨(u3, w0), ⟨hu3L, ht⟩, rfl⟩, ?_, ?_⟩
  · rw [hdec, ← hγ, hz]
    exact Units.ext rfl
  · have hsi : s⁻¹ ≤ s := (inv_le_one_of_one_le₀ hs1).trans hs1
    have hle1 : ‖toL z.val‖ ≤ s := norm_toL_mD_le p hs0.le
      (fun w => (norm_posIdele_infinite s hs0 w).le) (fun w => (norm_pos_inv s hs0 w).le.trans hsi)
    have hzi : z⁻¹ = Matrix.GeneralLinearGroup.map (pInf E) (gl (mD p⁻¹)) := by
      refine inv_eq_of_mul_eq_one_right ?_
      have e : gl (mD p) * gl (mD p⁻¹) = 1 := by
        have e1 : mD p * mD p⁻¹ = 1 := by rw [← mD_mul, mul_inv_cancel, mD_one]
        have e2 : gl (mD p) * gl (mD p⁻¹) = gl (mD p * mD p⁻¹) := Units.ext rfl
        rw [e2, e1]
        exact Units.ext rfl
      change Matrix.GeneralLinearGroup.map (pInf E) (gl (mD p)) * _ = 1
      rw [← map_mul, e, map_one]
    have hle2 : ‖toL (z⁻¹).val‖ ≤ s := by
      rw [hzi]
      refine norm_toL_mD_le p⁻¹ hs0.le (fun w => (norm_pos_inv s hs0 w).le.trans hsi) fun w => ?_
      rw [inv_inv]
      exact (norm_posIdele_infinite s hs0 w).le
    have hss : s ≤ ab b / c := hsd ▸ le_self_pow₀ hs1 hd
    have e3 : 3 / c * ab b = 3 * (ab b / c) := by ring
    have e4 : Ht z = 1 + ‖toL z.val‖ + ‖toL (z⁻¹).val‖ := rfl
    rw [e3, e4]
    linarith
end

-- bundled from Development.AutomorphicArithmetic.UnipotentInvariants.ExistsUnipotentInvariantSetUniqueRowScaling
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal

private theorem tri {E : Type} [Field E] [NumberField E] (g h : Matrix.SpecialLinearGroup (Fin 2) E) (t : Eˣ)
    (hrow : g.1 1 = (t : E) • h.1 1) :
    ∃ β : A E, ratS E g = nU β * mD (IdeleGroup.diagonal E t⁻¹) * ratS E h := by
  obtain ⟨k, hk⟩ : ∃ k, k = g * h⁻¹ := ⟨_, rfl⟩
  have hdet : h.1 0 0 * h.1 1 1 - h.1 0 1 * h.1 1 0 = 1 := by
    have hd := h.det_coe
    rwa [Matrix.det_fin_two] at hd
  have hg0 : g.1 1 0 = t * h.1 1 0 := by simpa using congrFun hrow 0
  have hg1 : g.1 1 1 = t * h.1 1 1 := by simpa using congrFun hrow 1
  have e0 : k.1 1 0 = 0 := by
    rw [hk]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    simp [hg0, hg1]
    ring
  have e1 : k.1 1 1 = t := by
    rw [hk]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    simp [hg0, hg1]
    linear_combination (t : E) * hdet
  have e2 : k.1 0 0 = ((t⁻¹ : Eˣ) : E) := by
    have hd := k.det_coe
    rw [Matrix.det_fin_two, e0, e1] at hd
    have ht : (t : E) ≠ 0 := t.ne_zero
    simp only [Units.val_inv_eq_inv_val]
    field_simp
    linear_combination hd
  have d2 : (((IdeleGroup.diagonal E t⁻¹)⁻¹ : (A E)ˣ) : A E) = UpperTheory.ConvolutionTheory.R2.rt (t : E) := by
    rw [← map_inv, inv_inv]
    rfl
  have d3 : (((IdeleGroup.diagonal E t)⁻¹ : (A E)ˣ) : A E) = algebraMap E (A E) (t : E)⁻¹ := by
    rw [← map_inv]
    exact congrArg (algebraMap E (A E)) (Units.val_inv_eq_inv_val t)
  refine ⟨UpperTheory.ConvolutionTheory.R2.rt (k.1 0 1 * ((t⁻¹ : Eˣ) : E)), ?_⟩
  have hkm : ratS E k = nU (UpperTheory.ConvolutionTheory.R2.rt (k.1 0 1 * ((t⁻¹ : Eˣ) : E))) * mD (IdeleGroup.diagonal E t⁻¹) := by
    refine Subtype.ext ?_
    rw [M.val_mul, M.val_ratS]
    ext i j
    fin_cases i <;> fin_cases j
    · simp [nU, mD, Matrix.mul_apply, Fin.sum_univ_two, d3, e2]
    · simp only [nU, mD, Matrix.mul_apply, Fin.sum_univ_two, d2]
      simp [← map_mul]
    · simp [nU, mD, Matrix.mul_apply, Fin.sum_univ_two, e0]
    · simp [nU, mD, Matrix.mul_apply, Fin.sum_univ_two, d2, e1]
  have hgk : g = k * h := by rw [hk, inv_mul_cancel_right]
  calc ratS E g = ratS E (k * h) := by rw [← hgk]
    _ = _ := by rw [map_mul, hkm]

theorem UpperTheory.exists_unipotentInvariant_set_unique_row_scaling :
    TorCo → ∀ (E : Type) [Field E] [NumberField E], ∃ T : Set (G1 E), MeasurableSet T ∧ (∀ b x, nU b * x ∈ T ↔ x ∈ T) ∧ ∀ σ : {r : Fin 2 → E // r ≠ 0} → Matrix.SpecialLinearGroup (Fin 2) E, M.RowSec σ → ∀ (x : G1 E) (r : {r : Fin 2 → E // r ≠ 0}), ∃! t : Eˣ, ∃ r' ∈ {r' : {r : Fin 2 → E // r ≠ 0} | ratS E (σ r') * x ∈ T}, r'.1 = (t : E) • r.1 := by
  intro hT E _ _
  obtain ⟨α, hm, hu, hd⟩ := hT E
  obtain ⟨Tq, hTq⟩ : ∃ Tq : Subgroup (IdeleGroup E), Tq = (IdeleGroup.diagonal E).range := ⟨_, rfl⟩
  have hmem : ∀ g : Tq, mD g.1 ∈ Gam E := by
    rintro ⟨g, hg⟩
    rw [hTq] at hg
    obtain ⟨t, rfl⟩ := hg
    exact M.mD_diag_mem t
  haveI : DiscreteTopology Tq := by
    refine DiscreteTopology.of_continuous_injective (f := fun g : Tq => (⟨mD g.1, hmem g⟩ : Gam E)) ?_ ?_
    · exact (M.continuous_mD.comp continuous_subtype_val).subtype_mk _
    · intro a b hab
      have h1 : mD a.1 = mD b.1 := congrArg (·.1) hab
      have h2 := congrArg (fun g : G1 E => g.1 0 0) h1
      exact Subtype.ext (Units.ext (by simpa [mD] using h2))
  obtain ⟨F, hF, huniq, -⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup Tq
  have hdiag : Function.Injective (IdeleGroup.diagonal E) := by
    intro a b hab
    have h1 : ((IdeleGroup.diagonal E a : (A E)ˣ) : A E) = ((IdeleGroup.diagonal E b : (A E)ˣ) : A E) := by rw [hab]
    exact Units.ext (AdeleRing.algebraMap_injective (𝓞 E) E h1)
  refine ⟨α ⁻¹' F, hm hF, fun b x => by simp [hu], ?_⟩
  intro σ hσ x r
  have key : ∀ (t : Eˣ) (r' : {r : Fin 2 → E // r ≠ 0}), r'.1 = (t : E) • r.1 →
      α (ratS E (σ r') * x) = IdeleGroup.diagonal E t⁻¹ * α (ratS E (σ r) * x) := by
    intro t r' hr
    obtain ⟨β, hβ⟩ := tri (σ r') (σ r) t (by rw [hσ r', hσ r, hr])
    rw [hβ, mul_assoc, mul_assoc, hu, hd]
  obtain ⟨⟨g, hg⟩, hgF, hgU⟩ := huniq (α (ratS E (σ r) * x))
  have hg' := hg
  rw [hTq] at hg'
  obtain ⟨s, rfl⟩ := hg'
  have hne : ((s⁻¹ : Eˣ) : E) • r.1 ≠ 0 := by
    intro h0
    exact r.2 ((smul_eq_zero.mp h0).resolve_left (Units.ne_zero _))
  refine ⟨s⁻¹, ⟨⟨_, hne⟩, ?_, rfl⟩, ?_⟩
  · show α (ratS E (σ _) * x) ∈ F
    rw [key s⁻¹ _ rfl, inv_inv]
    exact hgF
  · rintro t ⟨r', hr'T, hr'⟩
    have hin : IdeleGroup.diagonal E t⁻¹ * α (ratS E (σ r) * x) ∈ F := by
      rw [← key t r' hr']
      exact hr'T
    have hmemt : IdeleGroup.diagonal E t⁻¹ ∈ Tq := by
      rw [hTq]
      exact ⟨_, rfl⟩
    have := hgU ⟨_, hmemt⟩ hin
    have h2 : IdeleGroup.diagonal E t⁻¹ = IdeleGroup.diagonal E s := congrArg Subtype.val this
    rw [← inv_inv t, hdiag h2]
end

