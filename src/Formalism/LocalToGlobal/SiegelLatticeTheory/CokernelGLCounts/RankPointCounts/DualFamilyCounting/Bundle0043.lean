module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0040
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0030
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FrameZZEqNegT
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SpanAtMono
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NormUnits
section
open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU Formalism.HermitianLattices.Ext.L3.integralBasisSpans Formalism.L2.SG.Pf.GluingBases Formalism.L2.SG.Pf.UnitPairSolutions
  Formalism.L2.SG.Pf.GluedFormOrthogonality Formalism.L2.SG.Pf.NormUnitsOrthogonality

theorem last_unit_holds : LastUnit := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hCM hFix h hS hN U hUc _ hΛ M _ _ 𝔭 h𝔭 b a hJ _ π w c τ hG j hj
  classical
  haveI : 𝔭.IsPrime := h𝔭.isPrime
  obtain ⟨hwU, hwo, hwn, hτinj, ⟨s₀, hU0⟩, hpair, hτlt, hfree⟩ := hG
  obtain ⟨hbU, hbloc, hbo, hbn, ha0⟩ := hJ
  obtain ⟨Λ₀, hΛlat, hΛu⟩ := hΛ
  have hA0 : ∀ i, algebraMap F K (a i : F) ≠ 0 := fun i => by
    rw [map_ne_zero]
    exact_mod_cast ha0 i
  have hC0 : ∀ k, algebraMap F K (c k) ≠ 0 := fun k => by
    rw [map_ne_zero]
    exact (hwn k).2
  have hπ0 : π ≠ 0 := fun e => hU0.notMem (e ▸ Submodule.zero_mem _)
  have hP0 : algebraMap F K (π : F) ≠ 0 := by
    rw [map_ne_zero]
    exact_mod_cast hπ0
  have hSPπ : algebraMap F K (π : F) ∈ SP K 𝔭 := by
    have := mem_SP_of_inP (K := K) hU0 (inP_of_mem_pow (K := K) (k := 0) (t := π) (by simp))
    simpa using this
  have hcard : Fintype.card (Fin (finrank K U) ⊕ Fin (finrank K (orthK h U))) = finrank K V := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Submodule.finrank_add_eq_of_isCompl hUc]
  haveI : Nonempty (Fin (finrank K U) ⊕ Fin (finrank K (orthK h U))) := ⟨Sum.inr j⟩
  let g : Fin (finrank K U) ⊕ Fin (finrank K (orthK h U)) → V := Sum.elim b w
  have horth : ∀ s t, s ≠ t → h (g s) (g t) = 0 := by
    rintro (i|i) (k|k) hst
    · exact hbo i k (fun e => hst (congrArg Sum.inl e))
    · exact form_U_orth (hbU i) (hwU k)
    · exact form_orth_U hS (hbU k) (hwU i)
    · exact hwo i k (fun e => hst (congrArg Sum.inr e))
  have hnorm : ∀ s, h (g s) (g s) ≠ 0 := by
    rintro (i|i)
    · show h (b i) (b i) ≠ 0
      rw [hbn i]
      exact hA0 i
    · show h (w i) (w i) ≠ 0
      rw [(hwn i).1]
      exact hC0 i
  have hli : LinearIndependent K g := linInd_orth g horth hnorm
  let γ := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hγ : ∀ s, γ s = g s := fun s =>
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank hli hcard) s
  have hdetγ : (gramK h γ).det =
      (∏ i, algebraMap F K (a i : F)) * ∏ k, algebraMap F K (c k) := by
    rw [gram_det_orth h γ (fun s t hst => by rw [hγ, hγ]; exact horth s t hst), Fintype.prod_sum_type]
    congr 1
    · exact Finset.prod_congr rfl (fun i _ => by rw [hγ]; exact hbn i)
    · exact Finset.prod_congr rfl (fun k _ => by rw [hγ]; exact (hwn k).1)
  have hfull : Submodule.IsFullLattice K Λ₀ := by
    refine { toIsLattice := hΛlat, span_eq_top := ?_ }
    obtain ⟨S, hS⟩ := hΛlat.fg
    obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finset
      (nonZeroDivisors (𝓞 K)) (Finset.image (fun p : V × _ => h p.1 (γ p.2)) (S ×ˢ Finset.univ))
    have hdK : algebraMap (𝓞 K) K d ≠ 0 := by
      exact fun e => (nonZeroDivisors.ne_zero hd) (IsFractionRing.injective (𝓞 K) K (by simpa using e))
    have hmem : ∀ i, d • γ i ∈ Λ₀ := by
      intro i
      rw [← hΛu]
      simp only [HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf,
        Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]
      intro y hy
      have key : ∀ y ∈ Submodule.span (𝓞 K) (S : Set V),
          ∃ r : 𝓞 K, algebraMap (𝓞 K) K r = h y (d • γ i) := by
        intro y hy
        induction hy using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨r, hr⟩ := hint (h y (γ i)) (Finset.mem_image.mpr ⟨(y, i), Finset.mem_product.mpr ⟨hy, Finset.mem_univ _⟩, rfl⟩)
          refine ⟨r, ?_⟩
          rw [← algebraMap_smul K d, LinearMap.map_smul, smul_eq_mul]
          exact hr
        | zero => exact ⟨0, by simp⟩
        | add x y _ _ hx hy =>
          obtain ⟨a, ha⟩ := hx
          obtain ⟨b, hb⟩ := hy
          exact ⟨a + b, by simp only [map_add, LinearMap.add_apply, ha, hb]⟩
        | smul a x _ hx =>
          obtain ⟨b, hb⟩ := hx
          obtain ⟨a', ha'⟩ := Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range a
          refine ⟨a' * b, ?_⟩
          rw [map_mul, ha', hb, ← algebraMap_smul K a x, LinearMap.map_smulₛₗ₂]
          simp only [LinearMap.smul_apply, starRingEnd_apply, smul_eq_mul]
      exact key y (by rw [hS]; exact hy)
    rw [eq_top_iff]
    intro x _
    rw [← γ.sum_repr x]
    refine Submodule.sum_mem _ fun i _ => ?_
    have hi : γ i ∈ Submodule.span K (Λ₀ : Set V) := by
      have : γ i = (algebraMap (𝓞 K) K d)⁻¹ • (d • γ i) := by
        rw [← algebraMap_smul K d, smul_smul, inv_mul_cancel₀ hdK, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (hmem i))
    exact Submodule.smul_mem _ _ hi
  obtain ⟨β, -, hβ⟩ := LocalSpans.exists_basis_locF hfull h𝔭
  let e : Fin (finrank K V) ≃ Fin (finrank K U) ⊕ Fin (finrank K (orthK h U)) :=
    Fintype.equivOfCardEq (by rw [Fintype.card_fin, hcard])
  let β' := β.reindex e
  have hsp : spanO β' = Submodule.span (𝓞 K) (Set.range β) := by
    show Submodule.span (𝓞 K) (Set.range ⇑(β.reindex e)) = _
    rw [Basis.range_reindex]
  have hsd : dualF h 𝔭 (locF 𝔭 (spanO β')) = locF 𝔭 (spanO β') := by
    rw [hsp, hβ, ← G7.locF_dual hFix h hΛlat.fg h𝔭.isPrime, (hΛu : HermitianLatticesTheory.dual h Λ₀ = Λ₀)]
  obtain ⟨hu1, hu2⟩ := det_unit_of_selfdual hFix hS hN β' hsd
  have hd : (β'.toMatrix γ).det ≠ 0 :=
    Matrix.det_ne_zero_of_right_inverse (Basis.toMatrix_mul_toMatrix_flip β' γ)
  have hNUγ : NU 𝔭 (gramK h γ).det := by
    rw [gram_det_change h β' γ]
    exact NU.norm_mul hu1 hu2 hd
  have hunitA : ∀ i, vF 𝔭 (a i) = 0 → NU 𝔭 (algebraMap F K (a i : F)) := by
    intro i hv
    apply NU.of_unit
    · have := mem_SP_of_inP (K := K) hU0 (inP_vF (K := K) h𝔭 (ha0 i))
      rw [hv] at this
      simpa using this
    · have := unit_part hCM hFix h𝔭 hU0 (ha0 i)
      rw [hv] at this
      simpa using this
  have hunitC : ∀ k : Fin (finrank K (orthK h U)), (k : ℕ) + 1 < finrank K (orthK h U) →
      (∀ i, vF 𝔭 (a i) ≠ 0 → τ i ≠ k) → NU 𝔭 (algebraMap F K (c k)) := by
    intro k hk hk'
    obtain ⟨h1, h2⟩ := hfree k hk hk'
    apply NU.of_unit
    · simpa using mem_SP_of_inP (K := K) hU0 h1
    · simpa using mem_SP_of_inP (K := K) hU0 h2
  have hpairNU : ∀ i, vF 𝔭 (a i) ≠ 0 →
      NU 𝔭 (algebraMap F K (a i : F) * algebraMap F K (c (τ i))) := by
    intro i hv
    obtain ⟨-, hCu⟩ := unit_part_c hCM hFix h𝔭 hU0 (ha0 i) hv (hpair i hv)
    have hAu := unit_part hCM hFix h𝔭 hU0 (ha0 i)
    have hAd := mem_SP_of_inP (K := K) hU0 (inP_vF (K := K) h𝔭 (ha0 i))
    have hs := mem_SP_of_inP (K := K) hU0 (hpair i hv)
    rw [map_add (f := _)] at hs
    set A := algebraMap F K (a i : F)
    set C := algebraMap F K (c (τ i))
    set P := algebraMap F K (π : F)
    set v := vF 𝔭 (a i)
    have e1 : P ^ v * P⁻¹ ^ v = 1 := by rw [← mul_pow, mul_inv_cancel₀ hP0, one_pow]
    have hCd : P⁻¹ ^ v * C ∈ SP K 𝔭 := by
      have e2 : P⁻¹ ^ v * C = P ^ v * (P⁻¹ ^ (2 * v) * (A + C)) - P⁻¹ ^ v * A := by
        rw [two_mul, pow_add]
        linear_combination (-(P⁻¹ ^ v * (A + C))) * e1
      rw [e2]
      exact sub_mem (mul_mem (pow_mem hSPπ _) hs) hAd
    apply NU.pair (hA0 i) (star_fix hFix _)
    · have e3 : C * A⁻¹ = (P⁻¹ ^ v * C) * (A⁻¹ * P ^ v) := by
        linear_combination (-(C * A⁻¹)) * e1
      rw [e3]
      exact mul_mem hCd hAu
    · have e3 : A * C⁻¹ = (P⁻¹ ^ v * A) * (C⁻¹ * P ^ v) := by
        linear_combination (-(A * C⁻¹)) * e1
      rw [e3]
      exact mul_mem hAd hCu
  let T := Finset.univ.filter (fun i => vF 𝔭 (a i) ≠ 0)
  let S := T.image τ
  have hSj : S ⊆ Finset.univ.erase j := by
    intro k hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hk
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro e
    have := hτlt i (Finset.mem_filter.mp hi).2
    rw [e] at this
    omega
  have hinjT : Set.InjOn τ T := fun i hi k hk e =>
    hτinj i k (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hk).2 e
  have hCprod : ∏ k, algebraMap F K (c k) = algebraMap F K (c j) *
      ((∏ i ∈ T, algebraMap F K (c (τ i))) * ∏ k ∈ (Finset.univ.erase j) \ S, algebraMap F K (c k)) := by
    rw [← Finset.mul_prod_erase Finset.univ (fun k => algebraMap F K (c k)) (Finset.mem_univ j),
      ← Finset.prod_sdiff hSj, Finset.prod_image hinjT]
    ring
  have hAprod : ∏ i, algebraMap F K (a i : F) = (∏ i ∈ T, algebraMap F K (a i : F)) *
      ∏ i ∈ Finset.univ.filter (fun i => ¬ vF 𝔭 (a i) ≠ 0), algebraMap F K (a i : F) :=
    (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
  have htot : (gramK h γ).det = algebraMap F K (c j) *
      ((∏ i ∈ T, algebraMap F K (a i : F) * algebraMap F K (c (τ i))) *
        (∏ i ∈ Finset.univ.filter (fun i => ¬ vF 𝔭 (a i) ≠ 0), algebraMap F K (a i : F)) *
        ∏ k ∈ (Finset.univ.erase j) \ S, algebraMap F K (c k)) := by
    rw [hdetγ, hAprod, hCprod, Finset.prod_mul_distrib]
    ring
  have hX : NU 𝔭 ((∏ i ∈ T, algebraMap F K (a i : F) * algebraMap F K (c (τ i))) *
        (∏ i ∈ Finset.univ.filter (fun i => ¬ vF 𝔭 (a i) ≠ 0), algebraMap F K (a i : F)) *
        ∏ k ∈ (Finset.univ.erase j) \ S, algebraMap F K (c k)) := by
    refine NU.mul (NU.mul ?_ ?_) ?_
    · exact NU.prod _ _ fun i hi => hpairNU i (Finset.mem_filter.mp hi).2
    · exact NU.prod _ _ fun i hi => hunitA i (by simpa using (Finset.mem_filter.mp hi).2)
    · refine NU.prod _ _ fun k hk => ?_
      obtain ⟨hk1, hk2⟩ := Finset.mem_sdiff.mp hk
      have hkj : k ≠ j := (Finset.mem_erase.mp hk1).1
      apply hunitC k
      · have h1 := k.isLt
        have h2 := Fin.val_ne_of_ne hkj
        omega
      · intro i hi e
        exact hk2 (Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, e⟩)
  have hX0 : (∏ i ∈ T, algebraMap F K (a i : F) * algebraMap F K (c (τ i))) *
        (∏ i ∈ Finset.univ.filter (fun i => ¬ vF 𝔭 (a i) ≠ 0), algebraMap F K (a i : F)) *
        ∏ k ∈ (Finset.univ.erase j) \ S, algebraMap F K (c k) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_ <;> refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    · exact mul_ne_zero (hA0 i) (hC0 _)
    · exact hA0 i
    · exact hC0 i
  rw [htot] at hNUγ
  exact NU.of_mul_left hNUγ hX hX0

end Formalism.L2.SG.Pf.Cnt
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RowVZero
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.NOf

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.S Formalism.L2.SG.Pf.NcReal.JX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hJ_add_l {n : ℕ} (ε : Fin n → Bool) (x y z : Fin n → ℂ) : hJ ε (x + y) z = hJ ε x z + hJ ε y z := by
  first
    | simp only [hJ, star_add, Matrix.add_dotProduct]
    | simp only [hJ, star_add, add_dotProduct]
    | simp [hJ, Matrix.add_dotProduct]
    | simp [hJ, add_dotProduct]

theorem hJ_conj' {n : ℕ} (ε : Fin n → Bool) (x y : Fin n → ℂ) : hJ ε y x = star (hJ ε x y) := by
  simp only [hJ, Formalism.REAL.Jm, dotProduct, Matrix.mulVec_diagonal, star_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : ε i <;> simp [h, mul_comm]

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem emb_star (v : InfinitePlace X.B.I.F) (t : D.host.E) :
    embS D (X.pl v) (star t) = star (embS D (X.pl v) t) := by
  first
    | exact NumberField.IsCMField.complexEmbedding_complexConj _ t
    | (simp only [Formalism.MainNotions.S.embS]; exact NumberField.IsCMField.complexEmbedding_complexConj _ t)
    | (haveI := D.host.isCMField_hostE
       rw [show (star t : D.host.E) = NumberField.IsCMField.complexConj D.host.E t from rfl]
       exact NumberField.IsCMField.complexEmbedding_complexConj _ _ t)
    | (haveI := D.host.isCMField_hostE
       exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E (embS D (X.pl v)) t)

theorem rowV_add (x y : (VS D).V) : rowV X u (x + y) = rowV X u x + rowV X u y := by
  funext v j
  have hc : X.crd (x + y) = X.crd x + X.crd y := by
    first
      | exact Formalism.L2.SG.Pf.Vanish2.crd_add X x y
      | exact Formalism.L2.SG.HidaSetting.crd_add X x y
      | (funext i; simp [Formalism.L2.SG.HidaSetting.HidaSetting.crd, Formalism.L2.SG.HidaSetting.crdOf])
  have hr : rv X.B.I v (X.crd x + X.crd y) = rv X.B.I v (X.crd x) + rv X.B.I v (X.crd y) := by
    unfold rv
    rw [← Matrix.mulVec_add]
    congr 1
    funext i
    simp only [Pi.add_apply, map_add]
  simp only [rowV, Pi.add_apply, hc, hr]
  split_ifs <;> exact hJ_add_l _ _ _ _

theorem rowV_zero : rowV X u 0 = 0 := by
  have h := rowV_add X u 0 0
  rw [add_zero] at h
  simpa using h

theorem rowV_neg (x : (VS D).V) : rowV X u (-x) = -rowV X u x := by
  rw [eq_neg_iff_add_eq_zero, add_comm (rowV X u (-x)), ← rowV_add, add_neg_cancel, rowV_zero]

theorem rowV_sub (x y : (VS D).V) : rowV X u (x - y) = rowV X u x - rowV X u y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, rowV_add, rowV_neg]

def rowHom : (VS D).V →+ (InfinitePlace X.B.I.F → Fin (D.R.k + 1) → ℂ) :=
  AddMonoidHom.mk' (rowV X u) (rowV_add X u)

end Formalism.L2.SG.Pf.NcReal.JX.NOf
end
end

