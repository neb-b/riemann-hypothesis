module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0025
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinGradedFrameIff

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XFlagframeBasis
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_flagframe_basis

variable {Ω : Type*} [Field Ω] {V : Type*} [AddCommGroup V] [Module Ω V] {N : ℕ}

theorem repr_expand (w u : Module.Basis (Fin N) Ω V) (v : V) (j : Fin N) :
    w.repr v j = ∑ q, u.repr v q * w.repr (u q) j := by
  conv_lhs => rw [← u.sum_repr v]
  exact GradedFrameCharacterisation.repr_sum_smul w _ _ j

theorem top_coord (w u : Module.Basis (Fin N) Ω V) (hup : ∀ i j, i < j → w.repr (u i) j = 0)
    (v : V) (i : Fin N) (hv : ∀ j, i < j → u.repr v j = 0) :
    (∀ j, i < j → w.repr v j = 0) ∧ w.repr v i = u.repr v i * w.repr (u i) i := by
  refine ⟨fun j hj => ?_, ?_⟩
  · rw [repr_expand w u]
    refine Finset.sum_eq_zero fun q _ => ?_
    by_cases hq : i < q
    · rw [hv q hq, zero_mul]
    · rw [hup q j (lt_of_le_of_lt (not_lt.mp hq) hj), mul_zero]
  · rw [repr_expand w u]
    refine Finset.sum_eq_single i (fun q _ hq => ?_) (fun h => absurd (Finset.mem_univ i) h)
    rcases lt_or_gt_of_ne hq with h | h
    · rw [hup q i h, mul_zero]
    · rw [hv q h, zero_mul]

theorem vanish_above (w u : Module.Basis (Fin N) Ω V) (hup : ∀ i j, i < j → w.repr (u i) j = 0)
    (hd : ∀ i, w.repr (u i) i ≠ 0) (v : V) (i : Fin N) (hv : ∀ j, i < j → w.repr v j = 0) :
    ∀ j, i < j → u.repr v j = 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  have hne : (Finset.univ.filter (fun j => i < j ∧ u.repr v j ≠ 0)).Nonempty := by
    obtain ⟨j, hj, hj'⟩ := hcon
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj, hj'⟩⟩
  obtain ⟨m, hmS, hmax⟩ := Finset.exists_max_image _ id hne
  have hm := (Finset.mem_filter.mp hmS).2
  have habove : ∀ j, m < j → u.repr v j = 0 := by
    intro j hj
    by_contra h0
    have hjS := hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_trans hm.1 hj, h0⟩)
    exact absurd hjS (not_le.mpr hj)
  have ht := top_coord w u hup v m habove
  have h0 := hv m hm.1
  rw [ht.2] at h0
  exact mul_ne_zero hm.2 (hd m) h0

theorem exists_basis (w : Module.Basis (Fin N) Ω V) (f : Fin N → V)
    (hup : ∀ i j, i < j → w.repr (f i) j = 0) (hd : ∀ i, w.repr (f i) i ≠ 0) :
    ∃ u : Module.Basis (Fin N) Ω V, ∀ i, u i = f i := by
  classical
  rcases isEmpty_or_nonempty (Fin N) with hN | hN
  · exact ⟨w, fun i => isEmptyElim i⟩
  · have hli : LinearIndependent Ω f := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      by_contra hcon
      push_neg at hcon
      have hne : (Finset.univ.filter (fun j => g j ≠ 0)).Nonempty := by
        obtain ⟨j, hj⟩ := hcon
        exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
      obtain ⟨m, hmS, hmax⟩ := Finset.exists_max_image _ id hne
      have hm := (Finset.mem_filter.mp hmS).2
      have h0 := congrArg (fun v => w.repr v m) hg
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, map_zero,
        Finsupp.coe_zero, Pi.zero_apply] at h0
      rw [Finset.sum_eq_single m] at h0
      · exact mul_ne_zero hm (hd m) h0
      · intro q _ hqm
        rcases lt_or_gt_of_ne hqm with h | h
        · rw [hup q m h, mul_zero]
        · have hgq : g q = 0 := by
            by_contra hq
            exact absurd (hmax q (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩)) (not_le.mpr h)
          rw [hgq, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ m) h
    refine ⟨basisOfLinearIndependentOfCardEqFinrank hli ?_, fun i => ?_⟩
    · rw [Module.finrank_eq_card_basis w]
    · rw [coe_basisOfLinearIndependentOfCardEqFinrank]

theorem coords_mem {O : Type*} [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω) (L : AddSubgroup V)
    (u : Module.Basis (Fin N) Ω V) (hst : ∀ a ∈ R, ∀ i, a • u i ∈ L)
    (htop : ∀ v ∈ L, ∀ i, (∀ j, i < j → u.repr v j = 0) → u.repr v i ∈ R) :
    ∀ v ∈ L, ∀ i, u.repr v i ∈ R := by
  classical
  have main : ∀ k : ℕ, ∀ v ∈ L, (∀ j : Fin N, k ≤ j.val → u.repr v j = 0) → ∀ i, u.repr v i ∈ R := by
    intro k
    induction k with
    | zero =>
      intro v _ hv i
      rw [hv i (Nat.zero_le _)]
      exact R.zero_mem
    | succ k ih =>
      intro v hvL hv
      by_cases hk : k < N
      · have ha : u.repr v ⟨k, hk⟩ ∈ R :=
          htop v hvL ⟨k, hk⟩ (fun j hj => hv j (Nat.succ_le_of_lt (Fin.lt_def.mp hj)))
        have hv'L : v - u.repr v ⟨k, hk⟩ • u ⟨k, hk⟩ ∈ L := L.sub_mem hvL (hst _ ha _)
        have hrep : ∀ j, u.repr (v - u.repr v ⟨k, hk⟩ • u ⟨k, hk⟩) j =
            u.repr v j - u.repr v ⟨k, hk⟩ * (if (⟨k, hk⟩ : Fin N) = j then 1 else 0) := by
          intro j
          rw [map_sub, map_smul, Module.Basis.repr_self, Finsupp.coe_sub, Pi.sub_apply, Finsupp.smul_apply,
            Finsupp.single_apply, smul_eq_mul]
        have hv' : ∀ j : Fin N, k ≤ j.val → u.repr (v - u.repr v ⟨k, hk⟩ • u ⟨k, hk⟩) j = 0 := by
          intro j hj
          rw [hrep j]
          rcases Nat.lt_or_eq_of_le hj with h | h
          · have hne : (⟨k, hk⟩ : Fin N) ≠ j := fun e => by
              rw [← e] at h
              exact lt_irrefl _ h
            rw [hv j h, if_neg hne, mul_zero, sub_zero]
          · have he : (⟨k, hk⟩ : Fin N) = j := Fin.ext h
            subst he
            rw [if_pos rfl, mul_one, sub_self]
        intro i
        have hi := ih _ hv'L hv' i
        rw [hrep i] at hi
        have h2 : u.repr v ⟨k, hk⟩ * (if (⟨k, hk⟩ : Fin N) = i then (1 : Ω) else 0) ∈ R := by
          split_ifs
          · rw [mul_one]
            exact ha
          · rw [mul_zero]
            exact R.zero_mem
        have h3 := R.add_mem hi h2
        rwa [sub_add_cancel] at h3
      · intro i
        exact ih v hvL (fun j hj => hv j (by have := j.isLt; omega)) i
  intro v hv i
  exact main N v hv (fun j hj => absurd j.isLt (not_lt.mpr hj)) i

end PositivityTheory.Xgn.A_flagframe_basis

open PositivityTheory.Xgn.A_flagframe_basis in
theorem PositivityTheory.Xgn.t_flagframe_basis : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E : ChartBundle O (mseg x) N V) (w : Module.Basis (Fin N) Ω V) (b : Fin N → K → ℤ), IsFlagFrame x E w b ↔ ∀ s, mseg x s ≠ 0 → ∃ u : Module.Basis (Fin N) Ω V, (∀ i j, i < j → w.repr (u i) j = 0) ∧ (∀ i, w.repr (u i) i = chartMon x s (b i)) ∧ ∀ v, v ∈ E.lat s ↔ ∀ i, u.repr v i ∈ chartRing O (mseg x) s := by
  intro O _ Ω _ _ K _ _ ι _ x N V _ _ E w b
  have hmon : ∀ s, mseg x s ≠ 0 → ∀ d : K → ℤ, chartMon x s d ≠ 0 := by
    intro s hs d
    have hs' : ∏ k : K, x ⟨k, s k⟩ ≠ 0 := hs
    show ∏ k : K, x ⟨k, s k⟩ ^ d k ≠ 0
    exact Finset.prod_ne_zero_iff.mpr fun k _ =>
      zpow_ne_zero _ (Finset.prod_ne_zero_iff.mp hs' k (Finset.mem_univ _))
  constructor
  · intro hF s hs
    have hdeg : ∀ i, ∃ f ∈ E.lat s, (∀ j, i < j → w.repr f j = 0) ∧ w.repr f i = chartMon x s (b i) := by
      intro i
      have hmem : chartMon x s (b i) ∈ degLat O x (b i) s := ⟨1, Subalgebra.one_mem _, (one_mul _).symm⟩
      rw [← hF.graded s hs i] at hmem
      exact hmem
    choose f hfL hfup hfd using hdeg
    obtain ⟨u, hu⟩ := exists_basis w f hfup (fun i => by rw [hfd i]; exact hmon s hs (b i))
    have hup_u : ∀ i j, i < j → w.repr (u i) j = 0 := fun i j hij => by
      rw [hu i]
      exact hfup i j hij
    refine ⟨u, hup_u, fun i => by rw [hu i]; exact hfd i, fun v => ⟨fun hv => ?_, fun hv => ?_⟩⟩
    · refine coords_mem (chartRing O (mseg x) s) (E.lat s) u
        (fun a ha i => by rw [hu i]; exact E.stable s a ha _ (hfL i)) ?_ v hv
      intro v' hv' i hup'
      have ht := top_coord w u hup_u v' i hup'
      have hin : w.repr v' i ∈ degLat O x (b i) s := by
        rw [← hF.graded s hs i]
        exact ⟨v', hv', ht.1, rfl⟩
      obtain ⟨a, ha, hae⟩ := hin
      rw [ht.2, hu i, hfd i] at hae
      have hc := mul_right_cancel₀ (hmon s hs (b i)) hae
      rw [hc]
      exact ha
    · rw [← u.sum_repr v]
      exact AddSubgroup.sum_mem _ fun q _ => by
        rw [hu q]
        exact E.stable s _ (hv q) _ (hfL q)
  · intro hR
    refine ⟨fun s hs i => ?_⟩
    obtain ⟨u, hup, hdiag, hmem⟩ := hR s hs
    ext t
    constructor
    · rintro ⟨v, hv, habove, rfl⟩
      have hd : ∀ i, w.repr (u i) i ≠ 0 := fun i => by
        rw [hdiag i]
        exact hmon s hs (b i)
      have hu_above := vanish_above w u hup hd v i habove
      have ht := top_coord w u hup v i hu_above
      exact ⟨u.repr v i, (hmem v).mp hv i, by rw [ht.2, hdiag i]; rfl⟩
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a • u i, (hmem _).mpr fun j => ?_, fun j hj => ?_, ?_⟩
      · rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
        split_ifs
        · rw [mul_one]
          exact ha
        · rw [mul_zero]
          exact Subalgebra.zero_mem _
      · rw [map_smul, Finsupp.smul_apply, hup i j hj, smul_zero]
      · rw [map_smul, Finsupp.smul_apply, hdiag i, smul_eq_mul]
        rfl
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XFlagframeDual
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_flagframe_dual

theorem tri_inv {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V] {N : ℕ}
    (w u : Module.Basis (Fin N) Ω V) (h : ∀ i j, i < j → w.repr (u i) j = 0) :
    (∀ i j, i < j → u.repr (w i) j = 0) ∧ ∀ i, u.repr (w i) i = (w.repr (u i) i)⁻¹ := by
  have hM : (w.toMatrix u).BlockTriangular id := fun i j hij => h j i hij
  have hMN : w.toMatrix u * u.toMatrix w = 1 := Module.Basis.toMatrix_mul_toMatrix_flip w u
  haveI : Invertible (w.toMatrix u) := ⟨u.toMatrix w, Module.Basis.toMatrix_mul_toMatrix_flip u w, hMN⟩
  have hinv : (w.toMatrix u)⁻¹ = u.toMatrix w := Matrix.inv_eq_right_inv hMN
  have hN : (u.toMatrix w).BlockTriangular id := hinv ▸ Matrix.blockTriangular_inv_of_blockTriangular hM
  refine ⟨fun i j hij => hN hij, fun i => ?_⟩
  have hii := congrFun (congrFun hMN i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq, Finset.sum_eq_single i] at hii
  · simp only [Module.Basis.toMatrix_apply] at hii
    exact eq_inv_of_mul_eq_one_right hii
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with hk | hk
    · rw [hM hk, zero_mul]
    · rw [hN hk, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem repr_of_pair {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V]
    {V₁ : Type} [AddCommGroup V₁] [Module Ω V₁] {N : ℕ} (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω)
    (w : Fin N → V) (w₁ : Module.Basis (Fin N) Ω V₁)
    (h : ∀ i j, β (w i) (w₁ j) = if i = j.rev then 1 else 0) (y : V₁) (j : Fin N) :
    w₁.repr y j = β (w j.rev) y := by
  have hy := congrArg (β (w j.rev)) (w₁.sum_repr y)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum] at hy
  simp only [map_smul, h, smul_eq_mul, mul_ite, mul_one, mul_zero, Fin.rev_inj] at hy
  rw [← hy]
  simp

theorem exists_dual {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V]
    {V₁ : Type} [AddCommGroup V₁] [Module Ω V₁] {N : ℕ} (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω)
    (hβ : Function.Bijective β.flip) (u : Module.Basis (Fin N) Ω V) :
    ∃ u₁ : Module.Basis (Fin N) Ω V₁, ∀ v j, β v (u₁ j) = u.repr v j.rev := by
  let e := LinearEquiv.ofBijective β.flip hβ
  refine ⟨(u.dualBasis.reindex Fin.revPerm).map e.symm, fun v j => ?_⟩
  simp only [Module.Basis.map_apply, Module.Basis.reindex_apply, Fin.revPerm_symm, Fin.revPerm_apply]
  change e (e.symm (u.dualBasis j.rev)) v = _
  simp

end PositivityTheory.Xgn.A_flagframe_dual

theorem PositivityTheory.Xgn.t_flagframe_dual : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (E : ChartBundle O (mseg x) N V) (F : ChartBundle O (mseg x) N V₁) (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω), IsDualLat O x β E.lat F.lat → ∀ (w : Module.Basis (Fin N) Ω V) (b : Fin N → K → ℤ), IsFlagFrame x E w b → ∀ w₁ : Module.Basis (Fin N) Ω V₁, (∀ i j, β (w i) (w₁ j) = if i = j.rev then 1 else 0) → IsFlagFrame x F w₁ (fun j => -b j.rev) := by
  intro O _ Ω _ _ K _ _ ι _ x N V _ _ V₁ _ _ E F β hD w b hE w₁ hw₁
  refine ⟨fun c hc j => ?_⟩
  have hne : ∀ k, x ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.mp hc k (Finset.mem_univ k)
  let m : Fin N → Ω := fun i => ∏ k, x ⟨k, c k⟩ ^ b i k
  have hm : ∀ i, m i ≠ 0 := fun i => Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hne k)
  have hinvm : ∀ i, ∏ k, x ⟨k, c k⟩ ^ (-b i) k = (m i)⁻¹ := by
    intro i
    simp only [m, Pi.neg_apply, zpow_neg, Finset.prod_inv_distrib]
  have hgr := hE.graded c hc
  have hex : ∀ i, ∃ v ∈ E.lat c, (∀ j, i < j → w.repr v j = 0) ∧ w.repr v i = m i := by
    intro i
    have hmem : m i ∈ degLat O x (b i) c := ⟨1, one_mem _, (one_mul _).symm⟩
    rw [← hgr i] at hmem
    exact hmem
  choose e he1 he2 he3 using hex
  have hP : (w.toMatrix e).BlockTriangular id := fun i j hij => he2 j i hij
  have hdet : IsUnit (w.det e) := by
    rw [Module.Basis.det_apply, Matrix.det_of_upperTriangular hP]
    refine (Finset.prod_ne_zero_iff.mpr fun i _ => ?_).isUnit
    rw [Module.Basis.toMatrix_apply, he3]
    exact hm i
  have hbasis := (Module.Basis.is_basis_iff_det w).mpr hdet
  let eb : Module.Basis (Fin N) Ω V := Module.Basis.mk hbasis.1 hbasis.2.ge
  have heb : ∀ i, eb i = e i := fun i => Module.Basis.mk_apply _ _ _
  have htri := A_flagframe_dual.tri_inv w eb (by
    intro i k hik
    rw [heb]
    exact he2 i k hik)
  have hrep : ∀ y k, w₁.repr y k = β (w k.rev) y :=
    fun y k => A_flagframe_dual.repr_of_pair β w w₁ hw₁ y k
  have hstep : ∀ n : ℕ, ∀ v ∈ E.lat c, (∀ k : Fin N, n ≤ k.val → w.repr v k = 0) →
      ∀ k, eb.repr v k ∈ chartRing O (mseg x) c := by
    intro n
    induction n with
    | zero =>
      intro v _ hz k
      have hv0 : v = 0 := w.ext_elem fun i => by rw [hz i (Nat.zero_le _), map_zero]; rfl
      rw [hv0, map_zero]
      exact zero_mem _
    | succ n ih =>
      intro v hv hz k
      by_cases hn : n < N
      · let i : Fin N := ⟨n, hn⟩
        have hmem : w.repr v i ∈ degLat O x (b i) c := by
          rw [← hgr i]
          exact ⟨v, hv, fun j hij => hz j hij, rfl⟩
        obtain ⟨α, hα, hs⟩ := hmem
        have hv' : v - α • e i ∈ E.lat c := sub_mem hv (E.stable c α hα (e i) (he1 i))
        have hz' : ∀ k : Fin N, n ≤ k.val → w.repr (v - α • e i) k = 0 := by
          intro k hk
          rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
          rcases Nat.lt_or_eq_of_le hk with hk | hk
          · have hik : i < k := hk
            rw [hz k hk, he2 i k hik, mul_zero, sub_zero]
          · have hik : k = i := Fin.ext hk.symm
            rw [hik, hs, he3]
            exact sub_self _
        have h1 := ih _ hv' hz' k
        have h2 : eb.repr v k = eb.repr (v - α • e i) k + α * eb.repr (e i) k := by
          rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
          ring
        rw [h2]
        refine add_mem h1 (mul_mem hα ?_)
        rw [← heb, Module.Basis.repr_self, Finsupp.single_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
      · exact ih v hv (fun k hk => absurd k.isLt (by omega)) k
  have hcoef : ∀ v ∈ E.lat c, ∀ k, eb.repr v k ∈ chartRing O (mseg x) c :=
    fun v hv => hstep N v hv (fun k hk => absurd k.isLt (by omega))
  ext s
  constructor
  · rintro ⟨w', hw', hz, rfl⟩
    have key : β (e j.rev) w' = m j.rev * w₁.repr w' j := by
      conv_lhs => rw [← w.sum_repr (e j.rev)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, LinearMap.sum_apply, Finset.sum_eq_single j.rev]
      · rw [map_smul, LinearMap.smul_apply, smul_eq_mul, he3, hrep w' j]
      · intro k _ hk
        rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
        rcases lt_or_gt_of_ne hk with hk | hk
        · have hjk : j < k.rev := Fin.lt_rev_iff.mp hk
          have hb : β (w k) w' = w₁.repr w' k.rev := by rw [hrep, Fin.rev_rev]
          rw [hb, hz _ hjk, mul_zero]
        · rw [he2 _ _ hk, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
    refine ⟨β (e j.rev) w', (hD.2 c hc w').1 hw' (e j.rev) (he1 _), ?_⟩
    show w₁.repr w' j = β (e j.rev) w' * ∏ k, x ⟨k, c k⟩ ^ (-b j.rev) k
    rw [key, hinvm, mul_comm (m j.rev), mul_assoc, mul_inv_cancel₀ (hm _), mul_one]
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨f, hf⟩ := hD.1.2 (a • eb.coord j.rev)
    have hfv : ∀ v, β v f = a * eb.repr v j.rev := by
      intro v
      have := LinearMap.congr_fun hf v
      simpa using this
    refine ⟨f, (hD.2 c hc f).2 fun v hv => ?_, fun k hk => ?_, ?_⟩
    · rw [hfv]
      exact mul_mem ha (hcoef v hv _)
    · rw [hrep, hfv, htri.1 _ _ (Fin.rev_lt_rev.mpr hk), mul_zero]
    · show w₁.repr f j = a * ∏ k, x ⟨k, c k⟩ ^ (-b j.rev) k
      rw [hrep, hfv, htri.2, heb, he3, hinvm]
end

-- bundled from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XPullLine
section
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_pull_line
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (restrictChart)
open ReciprocityTheory.ChartRestriction.G.Geo (div_mem_chartRing)

variable {O : Type} [CommRing O] {Ω Ω₁ : Type} [Field Ω] [Field Ω₁] [Algebra O Ω] [Algebra O Ω₁]
  {K K' : Type} [Fintype K] [Fintype K'] {ι : K → Type} {ι' : K' → Type}

def comb (t : ∀ k, ι k) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) : ∀ k : K ⊕ K', Sum.elim ι ι' k
  | .inl k => t k
  | .inr k => s (.inr k)

theorem mseg_join (φ : Ω →ₐ[O] Ω₁) (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) :
    mseg (joinCoord (fun p => φ (x p)) z) s =
      φ (mseg x (restrictChart s)) * mseg z (fun k => s (.inr k)) := by
  simp only [mseg, Fintype.prod_sum_type, map_prod]
  rfl

theorem chartMon_join (φ : Ω →ₐ[O] Ω₁) (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) (a : K → ℤ) :
    chartMon (joinCoord (fun p => φ (x p)) z) s (pullDeg (K' := K') a) =
      φ (chartMon x (restrictChart s) a) := by
  simp only [chartMon, Fintype.prod_sum_type, pullDeg, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply,
    zpow_zero, Finset.prod_const_one, mul_one, map_prod, map_zpow₀]
  rfl

theorem map_mem (φ : Ω →ₐ[O] Ω₁) (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁)
    (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) (hs : mseg (joinCoord (fun p => φ (x p)) z) s ≠ 0)
    (r : Ω) (hr : r ∈ chartRing O (mseg x) (restrictChart s)) :
    φ r ∈ chartRing O (mseg (joinCoord (fun p => φ (x p)) z)) s := by
  have hw : mseg z (fun k => s (.inr k)) ≠ 0 := by
    rw [mseg_join] at hs
    exact right_ne_zero_of_mul hs
  have hle : chartRing O (mseg x) (restrictChart s) ≤
      (chartRing O (mseg (joinCoord (fun p => φ (x p)) z)) s).comap φ := by
    unfold chartRing
    apply Algebra.adjoin_le
    rintro _ ⟨t, rfl⟩
    have h : φ (mseg x t / mseg x (restrictChart s)) =
        mseg (joinCoord (fun p => φ (x p)) z) (comb t s) / mseg (joinCoord (fun p => φ (x p)) z) s := by
      rw [mseg_join φ x z (comb t s), mseg_join φ x z s, map_div₀]
      exact (mul_div_mul_right _ _ hw).symm
    have h2 := div_mem_chartRing (o := O) (mseg (joinCoord (fun p => φ (x p)) z)) s (comb t s)
    rw [← h] at h2
    exact h2
  exact hle hr

theorem main [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
    (φ : Ω →ₐ[O] Ω₁) (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁) (u : Ω) (a : K → ℤ)
    (A : (∀ k, ι k) → AddSubgroup Ω) (hA : IsLine O x u a A)
    (B : (∀ k : K ⊕ K', Sum.elim ι ι' k) → AddSubgroup Ω₁)
    (hB : ∀ s, mseg (joinCoord (fun p => φ (x p)) z) s ≠ 0 → B s = AddSubgroup.closure
      {v | ∃ c ∈ chartRing O (mseg (joinCoord (fun p => φ (x p)) z)) s, ∃ e ∈ A (restrictChart s),
        v = c • φ e}) (s : ∀ k : K ⊕ K', Sum.elim ι ι' k)
    (hs : mseg (joinCoord (fun p => φ (x p)) z) s ≠ 0) (v : Ω₁) :
    v ∈ B s ↔ ∃ r ∈ chartRing O (mseg (joinCoord (fun p => φ (x p)) z)) s,
      v = r * (φ u * chartMon (joinCoord (fun p => φ (x p)) z) s (pullDeg (K' := K') a)) := by
  have hx : mseg x (restrictChart s) ≠ 0 := by
    rw [mseg_join] at hs
    intro h
    exact left_ne_zero_of_mul hs (by rw [h, map_zero])
  rw [hB s hs, chartMon_join, ← map_mul]
  constructor
  · intro hv
    induction hv using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨c, hc, e, he, rfl⟩ := hw
      obtain ⟨r, hr, rfl⟩ := (hA _ hx e).1 he
      refine ⟨c * φ r, mul_mem hc (map_mem φ x z s hs r hr), ?_⟩
      rw [smul_eq_mul, map_mul, mul_assoc]
    | zero => exact ⟨0, zero_mem _, by rw [zero_mul]⟩
    | add w₁ w₂ _ _ h₁ h₂ =>
      obtain ⟨r₁, hr₁, rfl⟩ := h₁
      obtain ⟨r₂, hr₂, rfl⟩ := h₂
      exact ⟨r₁ + r₂, add_mem hr₁ hr₂, by rw [add_mul]⟩
    | neg w _ h =>
      obtain ⟨r, hr, rfl⟩ := h
      exact ⟨-r, neg_mem hr, by rw [neg_mul]⟩
  · rintro ⟨r, hr, rfl⟩
    exact AddSubgroup.subset_closure ⟨r, hr, _, (hA _ hx _).2 ⟨1, one_mem _, (one_mul _).symm⟩, rfl⟩

end PositivityTheory.Xgn.A_pull_line
end

