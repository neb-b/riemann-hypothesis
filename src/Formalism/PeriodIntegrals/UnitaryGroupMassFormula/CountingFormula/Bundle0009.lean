module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0008

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGFL
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S Polynomial
open ValuativeRel

theorem fl_cj_mem {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  rw [L.9] at hx ⊢
  exact hx.map ((L.1 : E →ₐ[F] E).restrictScalars 𝒪[F])

theorem fl_mem_int {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hinj : Function.Injective (algebraMap F E))
    {a : F} (ha : algebraMap F E a ∈ L.O) : a ∈ 𝒪[F] := by
  have h1 : IsIntegral 𝒪[F] (algebraMap F E a) := (L.9 _).1 ha
  letI : FaithfulSMul F E := (faithfulSMul_iff_algebraMap_injective F E).2 hinj
  have h2 : IsIntegral 𝒪[F] a := isIntegral_algebraMap_iff.1 h1
  exact (Valuation.integer.integers _).mem_of_integral h2

theorem fl_int_mem {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (a : 𝒪[F]) : algebraMap F E a ∈ L.O := by
  rw [L.9]
  have h : IsIntegral 𝒪[F] (algebraMap 𝒪[F] E a) := isIntegral_algebraMap
  rwa [IsScalarTower.algebraMap_apply 𝒪[F] F E] at h

theorem fl_fix_int {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hinj : Function.Injective (algebraMap F E))
    {y : E} (hy : y ∈ L.O) (hc : L.cj y = y) : ∃ a : 𝒪[F], algebraMap F E a = y := by
  obtain ⟨a, ha⟩ := (L.3 y).1 hc
  have haO : a ∈ 𝒪[F] := fl_mem_int L hinj (ha ▸ hy)
  exact ⟨⟨a, haO⟩, ha⟩

theorem fl_norm {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hinj : Function.Injective (algebraMap F E))
    {x : E} (hx : x ∈ L.O) : ∃ n : 𝒪[F], algebraMap F E n = x * L.cj x := by
  refine fl_fix_int L hinj (L.O.mul_mem hx (fl_cj_mem L hx)) ?_
  rw [map_mul, L.2, mul_comm]

theorem fl_trace {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (hinj : Function.Injective (algebraMap F E))
    {x : E} (hx : x ∈ L.O) : ∃ t : 𝒪[F], algebraMap F E t = x + L.cj x := by
  refine fl_fix_int L hinj (L.O.add_mem hx (fl_cj_mem L hx)) ?_
  rw [map_add (f := _), L.2, add_comm]

theorem fl_den_F {F : Type} [Field F] [ValuativeRel F] (a : F) :
    ∃ c : 𝒪[F], c ≠ 0 ∧ (c : F) * a ∈ 𝒪[F] := by
  by_cases ha : a ∈ 𝒪[F]
  · exact ⟨1, one_ne_zero, by simpa using ha⟩
  · have ha0 : a ≠ 0 := by
      rintro rfl
      exact ha (zero_mem _)
    have hv : 1 < ValuativeRel.valuation F a := by
      rw [Valuation.mem_integer_iff, not_le] at ha
      exact ha
    have hmem : a⁻¹ ∈ 𝒪[F] := by
      rw [Valuation.mem_integer_iff, map_inv₀]
      exact inv_le_one_of_one_le₀ hv.le
    refine ⟨⟨a⁻¹, hmem⟩, ?_, ?_⟩
    · intro h
      have h' := congrArg Subtype.val h
      simp [ha0] at h'
    · simp [ha0]

theorem fl_den {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (x : E) :
    ∃ c : 𝒪[F], c ≠ 0 ∧ algebraMap F E c * x ∈ L.O := by
  obtain ⟨t, ht⟩ := (L.3 (x + L.cj x)).1 (by rw [map_add (f := _), L.2, add_comm])
  obtain ⟨m, hm⟩ := (L.3 (x * L.cj x)).1 (by rw [map_mul, L.2, mul_comm])
  obtain ⟨c1, hc1, ht1⟩ := fl_den_F t
  obtain ⟨c2, hc2, hm2⟩ := fl_den_F m
  refine ⟨c1 * c2, mul_ne_zero hc1 hc2, ?_⟩
  rw [L.9]
  have key : ∀ z : 𝒪[F], algebraMap 𝒪[F] E z = algebraMap F E (z : F) :=
    fun z => IsScalarTower.algebraMap_apply 𝒪[F] F E z
  have hx2 : x * x = algebraMap F E t * x - algebraMap F E m := by rw [ht, hm]; ring
  refine ⟨X ^ 2 - C (c2 * ⟨(c1 : F) * t, ht1⟩) * X + C (c1 ^ 2 * c2 * ⟨(c2 : F) * m, hm2⟩), by monicity!, ?_⟩
  simp only [eval₂_add, eval₂_sub, eval₂_mul, eval₂_X_pow, eval₂_C, eval₂_X, key]
  push_cast
  try simp only [map_mul, map_pow]
  linear_combination (algebraMap F E c1 * algebraMap F E c2) ^ 2 * hx2

end PI.UnitaryGroupMassFormula.CntFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGSO
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S
open Classical ValuativeRel

theorem isIntegral_iff_mem_integer (F : Type) [Field F] [ValuativeRel F] (a : F) :
    IsIntegral 𝒪[F] a ↔ a ∈ 𝒪[F] := by
  constructor
  · intro h
    exact (Valuation.integer.integers _).mem_of_integral h
  · intro h
    have e : a = algebraMap 𝒪[F] F ⟨a, h⟩ := rfl
    rw [e]
    exact isIntegral_algebraMap

theorem integral_split_count : OSplit := by
  intro F E _ _ _ _ _ _ L _ e x
  rw [L.O_def]
  have key : IsIntegral 𝒪[F] x ↔ IsIntegral 𝒪[F] (e x) := by
    constructor
    · intro h
      exact h.map ((e : E →ₐ[F] F × F).restrictScalars 𝒪[F])
    · intro h
      have h' := h.map ((e.symm : F × F →ₐ[F] E).restrictScalars 𝒪[F])
      simpa using h'
  rw [key]
  constructor
  · intro h
    exact ⟨(isIntegral_iff_mem_integer F _).1 (h.map (AlgHom.fst 𝒪[F] F F)),
      (isIntegral_iff_mem_integer F _).1 (h.map (AlgHom.snd 𝒪[F] F F))⟩
  · rintro ⟨h1, h2⟩
    exact IsIntegral.pair ((isIntegral_iff_mem_integer F _).2 h1) ((isIntegral_iff_mem_integer F _).2 h2)

end PI.UnitaryGroupMassFormula.CntFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DsumCancel
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def skL (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) :
    (VS D).V →ₗ[D.host.E] (VS D).V :=
  LinearMap.id + ∑ a, ∑ a', S a a' • ((VS D).hT (D.sp.hypE a')).smulRight (D.sp.hypE a)

theorem skL_apply (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (v : (VS D).V) :
    skL D S v = v + ∑ a, (∑ a', S a a' * (VS D).hT (D.sp.hypE a') v) • D.sp.hypE a := by
  simp only [skL, LinearMap.add_apply, LinearMap.id_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.smulRight_apply, smul_smul, Finset.sum_smul]

theorem hE_skL (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (b : Fin D.R.rS)
    (v : (VS D).V) : (VS D).hT (D.sp.hypE b) (skL D S v) = (VS D).hT (D.sp.hypE b) v := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [skL_apply, map_add (f := _), map_sum]
  simp [D.sp.hyp_ee]

theorem skL_inv (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (v : (VS D).V) :
    skL D (-S) (skL D S v) = v := by
  rw [skL_apply D (-S) (skL D S v)]
  simp only [hE_skL]
  rw [skL_apply]
  have e : ∀ a, (∑ a', (-S) a a' * (VS D).hT (D.sp.hypE a') v) =
      -(∑ a', S a a' * (VS D).hT (D.sp.hypE a') v) := fun a => by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [Matrix.neg_apply, neg_mul]
  simp_rw [e, neg_smul, Finset.sum_neg_distrib]
  exact add_neg_cancel_right _ _

def skE (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) : (VS D).V ≃ₗ[D.host.E] (VS D).V :=
  LinearEquiv.ofLinear (skL D S) (skL D (-S))
    (LinearMap.ext fun v => by
      have h := skL_inv D (-S) v
      rw [neg_neg] at h
      exact h)
    (LinearMap.ext fun v => skL_inv D S v)

theorem skE_apply (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (v : (VS D).V) :
    skE D S v = skL D S v := rfl

theorem dsum_cancel {K : Type} [CommRing K] {r : ℕ} (S : Matrix (Fin r) (Fin r) K) (X Y : Fin r → K) :
    ∑ a, (∑ a', S a a' * X a') * Y a + ∑ a, (∑ a', -S a' a * Y a') * X a = 0 := by
  have e : ∑ a, (∑ a', -S a' a * Y a') * X a = -∑ a, (∑ a', S a a' * X a') * Y a := by
    simp only [Finset.sum_mul, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
    ring
  rw [e, add_neg_cancel]

theorem skL_isom (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (hS : ∀ i j, star (S j i) = -S i j) (u v : (VS D).V) :
    (VS D).hT (skL D S u) (skL D S v) = (VS D).hT u v := by
  have hue : ∀ b, (VS D).hT u (D.sp.hypE b) = star ((VS D).hT (D.sp.hypE b) u) := fun b =>
    ((VS D).herm.eq (D.sp.hypE b) u).symm
  have key := dsum_cancel S (fun b => (VS D).hT (D.sp.hypE b) v) (fun b => star ((VS D).hT (D.sp.hypE b) u))
  beta_reduce at key
  rw [skL_apply, skL_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_add (f := _), map_sum, LinearMap.add_apply, LinearMap.sum_apply, LinearMap.map_smulₛₗ₂, map_smul,
    D.sp.hyp_ee, hue, smul_eq_mul, mul_zero, Finset.sum_const_zero, add_zero, starRingEnd_apply, star_sum,
    star_mul', hS]
  linear_combination key

theorem hE_int (D : Formalism.BasicNotions.D7) {T : D.host.E} {F0 : FlagG (VS D) D.R.rS T}
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hF : FixedOK D F0 Λ) (a : Fin D.R.rS) {v : (VS D).V}
    (hv : v ∈ Λ) : ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (VS D).hT (D.sp.hypE a) v := by
  have he : D.sp.hypE a ∈ Λ := by
    have h1 := hF.2.2.2.1 a
    rwa [hF.2.2.1] at h1
  have hU' : Formalism.HermitianLatticesTheory.dual (VS D).hT Λ = Λ := hF.2.1
  have hv' : v ∈ Formalism.HermitianLatticesTheory.dual (VS D).hT Λ := by rw [hU']; exact hv
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply] at hv'
  obtain ⟨o, ho⟩ := Submodule.mem_one.mp (hv' _ he)
  exact ⟨o, ho⟩

theorem skL_lat (D : Formalism.BasicNotions.D7) {T : D.host.E} {F0 : FlagG (VS D) D.R.rS T}
    {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hF : FixedOK D F0 Λ) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (hO : ∀ i j, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = S i j) {v : (VS D).V} (hv : v ∈ Λ) :
    skL D S v ∈ Λ := by
  rw [skL_apply]
  refine Λ.add_mem hv (Λ.sum_mem fun a _ => ?_)
  have he : D.sp.hypE a ∈ Λ := by
    have h1 := hF.2.2.2.1 a
    rwa [hF.2.2.1] at h1
  have hc : (∑ a', S a a' * (VS D).hT (D.sp.hypE a') v) ∈ (algebraMap (𝓞 D.host.E) D.host.E).range :=
    sum_mem fun a' _ => mul_mem (hO a a') (hE_int D hF a' hv)
  obtain ⟨o, ho⟩ := hc
  rw [← ho, algebraMap_smul]
  exact Λ.smul_mem o he

theorem skL_X (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) {x : (VS D).V}
    (hx : x ∈ Submodule.span D.host.E (Set.range D.sp.hypE)) : skL D S x = x := by
  have h0 : ∀ a', (VS D).hT (D.sp.hypE a') x = 0 := by
    intro a'
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨b, rfl⟩ := hy
      exact D.sp.hyp_ee a' b
    | zero => simp
    | add y z _ _ hy hz => rw [map_add (f := _), hy, hz, add_zero]
    | smul c y _ hy => rw [map_smul, hy, smul_zero]
  rw [skL_apply]
  simp [h0]

theorem skL_sub_mem (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) (x : (VS D).V) :
    skL D S x - x ∈ Submodule.span D.host.E (Set.range D.sp.hypE) := by
  rw [skL_apply, add_sub_cancel_left]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem skE_mem (D : Formalism.BasicNotions.D7) {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hF : FixedOK D F0 Λ) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (hS : ∀ i j, star (S j i) = -S i j)
    (hO : ∀ i j, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = S i j) :
    skE D S ∈ N0 F0 Λ := by
  have hFe : F0.e = D.sp.hypE := hF.2.2.1
  have hspan : ∀ x ∈ Submodule.span D.host.E (Set.range F0.e), skE D S x = x := by
    intro x hx
    rw [hFe] at hx
    exact skL_X D S hx
  have hO' : ∀ i j, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o = (-S) i j := fun i j => by
    obtain ⟨o, ho⟩ := hO i j
    exact ⟨-o, by rw [map_neg, ho, Matrix.neg_apply]⟩
  have hzm : ∀ a', (VS D).hT (D.sp.hypE a') D.sp.zm = 0 := fun a' => by
    rw [← (VS D).herm.eq D.sp.zm (D.sp.hypE a'), (D.sp.hyp_orthz a').1, map_zero]
  simp only [N0, NLam, IsAutLam, Set.mem_setOf_eq]
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
  · intro x y
    exact skL_isom D S hS x y
  · apply le_antisymm
    · exact Submodule.map_le_iff_le_comap.mpr fun v hv => skL_lat D hF S hO hv
    · intro v hv
      refine Submodule.mem_map.mpr ⟨skL D (-S) v, skL_lat D hF (-S) hO' hv, ?_⟩
      have h1 := skL_inv D (-S) v
      rw [neg_neg] at h1
      exact h1
  · intro j x hx
    have hx' : x ∈ Submodule.span D.host.E (Set.range F0.e) :=
      Submodule.span_mono (Set.image_subset_range _ _) hx
    rw [hspan x hx', sub_self]
    exact Submodule.zero_mem _
  · intro x _
    have h1 := skL_sub_mem D S x
    rw [← hFe] at h1
    exact h1
  · intro a
    exact hspan _ (Submodule.subset_span ⟨a, rfl⟩)
  · obtain ⟨c, _, hcz⟩ := hF.2.2.2.2
    rw [hcz, map_smul]
    congr 1
    rw [skE_apply, skL_apply]
    simp [hzm]

private theorem pW_skL (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (w : (VS D).V) : pW D (skL D S w) = pW D w := by
  have hf : ∀ a b, (VS D).hT (D.sp.hypF b) (D.sp.hypE a) = if a = b then 1 else 0 := fun a b => by
    rw [← (VS D).herm.eq (D.sp.hypE a) (D.sp.hypF b), D.sp.hyp_ef]
    split_ifs <;> simp
  have hz : ∀ a, (VS D).hT D.sp.zm (D.sp.hypE a) = 0 := fun a => (D.sp.hyp_orthz a).1
  rw [skL_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [pW, map_add (f := _), map_sum, map_smul, hf, hz, D.sp.hyp_ee, smul_eq_mul, mul_zero, add_zero,
    mul_ite, mul_one, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true, add_smul,
    Finset.sum_add_distrib, Finset.sum_const_zero, zero_smul]
  module

theorem pWf_skE (D : Formalism.BasicNotions.D7) (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E)
    (x : (Fin D.R.rS → (VS D).V) × (VS D).V) : pWf D (act D (skE D S) x) = pWf D x := by
  funext b
  have hfr : fr D (act D (skE D S) x) b = skL D S (fr D x b) := by
    simp only [fr, act]
    exact (congrFun (Fin.comp_snoc (fun w => (skE D S) w) x.1 x.2) b).symm
  simp only [pWf]
  rw [hfr, pW_skL]

theorem alM_skE (D : Formalism.BasicNotions.D7) {T : D.host.E} (T' : D.host.E) (F0 : FlagG (VS D) D.R.rS T)
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (hF : FixedOK D F0 Λ) (Z : MatZ D)
    (S : Matrix (Fin D.R.rS) (Fin D.R.rS) D.host.E) {x : (Fin D.R.rS → (VS D).V) × (VS D).V}
    (hx : Good D T' F0 Λ Z x) : alM D (act D (skE D S) x) = alM D x + S * betaZ D Z := by
  ext a b
  have hf : ∀ c, (VS D).hT (D.sp.hypF a) (D.sp.hypE c) = if c = a then 1 else 0 := fun c => by
    rw [← (VS D).herm.eq (D.sp.hypE c) (D.sp.hypF a), D.sp.hyp_ef]
    split_ifs <;> simp
  have hZ : ∀ c', (VS D).hT (D.sp.hypE c') (fr D x b) = Z (Fin.castSucc c') b := fun c' => by
    have h1 := hx.2.1 (Fin.castSucc c') b
    simp only [Formalism.MainNotions.S.brS, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc, hF.2.2.1] at h1
    exact h1
  have hfr : fr D (act D (skE D S) x) b = skL D S (fr D x b) := by
    simp only [fr, act]
    exact (congrFun (Fin.comp_snoc (fun w => (skE D S) w) x.1 x.2) b).symm
  simp only [alM, Matrix.add_apply, Matrix.mul_apply, betaZ, Matrix.submatrix_apply, id]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hfr, skL_apply, map_add (f := _), map_sum]
  simp only [map_smul, smul_eq_mul, hf, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, hZ]

end PI.UnitaryGroupMassFormula.CntFormula
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.FlbHZeroRight
section
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S Module
open ValuativeRel

theorem flb_int_mem {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) (a : 𝒪[F]) : algebraMap F E a ∈ L.O := by
  exact (L.O_def _).2 isIntegral_algebraMap

theorem flb_cj_mem {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] (L : Loc.LocE F E) {x : E} (hx : x ∈ L.O) : L.cj x ∈ L.O := by
  exact (L.O_def _).2 (((L.O_def x).1 hx).map ((L.cj : E →ₐ[F] E).restrictScalars 𝒪[F]))

theorem flb_pid {E : Type} [CommRing E] (S : Subring E) (p : E) (hp : p ∈ S)
    (hfac : ∀ x ∈ S, x ≠ 0 → ∃ k : ℕ, ∃ u ∈ S, (∃ w ∈ S, u * w = 1) ∧ x = p ^ k * u) :
    IsPrincipalIdealRing S := by
  classical
  refine ⟨fun I => ?_⟩
  have hget : ∀ x : S, x ∈ I → ∀ (j : ℕ) (u : E), u ∈ S → (∃ w ∈ S, u * w = 1) →
      (x : E) = p ^ j * u → (⟨p, hp⟩ : S) ^ j ∈ I := by
    rintro x hxI j u hu ⟨w, hw, huw⟩ hxe
    have h : (⟨p, hp⟩ : S) ^ j = x * ⟨w, hw⟩ := by
      apply Subtype.ext
      simp only [SubmonoidClass.coe_pow, Subring.coe_mul, hxe]
      rw [mul_assoc, huw, mul_one]
    rw [h]
    exact I.mul_mem_right _ hxI
  by_cases hI : ∃ x ∈ I, x ≠ 0
  · have hex : ∃ k : ℕ, (⟨p, hp⟩ : S) ^ k ∈ I := by
      obtain ⟨x, hxI, hx0⟩ := hI
      obtain ⟨k, u, hu, huw, hxe⟩ := hfac x x.2 (fun h => hx0 (Subtype.ext h))
      exact ⟨k, hget x hxI k u hu huw hxe⟩
    refine ⟨⟨(⟨p, hp⟩ : S) ^ Nat.find hex, ?_⟩⟩
    apply le_antisymm
    · intro x hxI
      by_cases hx0 : x = 0
      · rw [hx0]
        exact Submodule.zero_mem _
      obtain ⟨j, u, hu, huw, hxe⟩ := hfac x x.2 (fun h => hx0 (Subtype.ext h))
      have hkj : Nat.find hex ≤ j := Nat.find_min' hex (hget x hxI j u hu huw hxe)
      rw [Ideal.submodule_span_eq, Ideal.mem_span_singleton']
      refine ⟨(⟨p, hp⟩ : S) ^ (j - Nat.find hex) * ⟨u, hu⟩, ?_⟩
      apply Subtype.ext
      simp only [SubmonoidClass.coe_pow, Subring.coe_mul, hxe]
      rw [mul_comm, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hkj]
    · rw [Ideal.submodule_span_eq, Ideal.span_le, Set.singleton_subset_iff]
      exact Nat.find_spec hex
  · push Not at hI
    refine ⟨⟨0, ?_⟩⟩
    rw [Submodule.span_singleton_eq_bot.mpr rfl]
    exact (Submodule.eq_bot_iff I).mpr hI

section Herm

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem flb_h_add_right {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [H.h_herm (y + y') x, H.h_add_left, map_add (f := _), ← H.h_herm, ← H.h_herm]

theorem flb_h_smul_right {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) (x : V) (a : E) (y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [H.h_herm (a • y) x, H.h_smul_left, map_mul, ← H.h_herm]

theorem flb_h_sum_right {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) {ι : Type} [Fintype ι] (x : V) (c : ι → E) (v : ι → V) :
    H.h x (∑ i, c i • v i) = ∑ i, M.L.cj (c i) * H.h x (v i) := by
  have hs := map_sum (AddMonoidHom.mk' (H.h x) (flb_h_add_right H x)) (fun i => c i • v i) Finset.univ
  simp only [AddMonoidHom.mk'_apply] at hs
  rw [hs]
  exact Finset.sum_congr rfl fun i _ => flb_h_smul_right H x (c i) (v i)

theorem flb_h_sum_left {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) {ι : Type} [Fintype ι] (y : V) (c : ι → E) (v : ι → V) :
    H.h (∑ i, c i • v i) y = ∑ i, c i * H.h (v i) y := by
  have hs := map_sum (AddMonoidHom.mk' (fun z => H.h z y) (fun a b => H.h_add_left a b y))
    (fun i => c i • v i) Finset.univ
  simp only [AddMonoidHom.mk'_apply] at hs
  rw [hs]
  exact Finset.sum_congr rfl fun i _ => H.h_smul_left (c i) (v i) y

end Herm

end PI.UnitaryGroupMassFormula.CntFormula
end
end

