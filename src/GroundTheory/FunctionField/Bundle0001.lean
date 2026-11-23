module

public import Mathlib
public import GroundTheory.FunctionField.PlaceDefs
public import GroundTheory.FunctionField.PlaceBasic

@[expose] public section

-- bundled from GroundTheory.FunctionField.Approximation
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.FunctionField

namespace Place

variable {k K : Type*} [Field k] [Field K] [Algebra k K] [IsFunctionField k K]

theorem valuation_le_exp_iff (v : Place k K) {x : K} (hx : x ≠ 0) (n : ℤ) :
    v.valuation x ≤ WithZero.exp n ↔ -n ≤ v.ord x := by
  rw [v.valuation_eq_exp_neg_ord hx, WithZero.exp_le_exp]
  omega

theorem ord_neg (v : Place k K) (x : K) : v.ord (-x) = v.ord x := by
  simp only [ord, Valuation.map_neg]

theorem ord_add_of_lt (v : Place k K) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : v.ord a < v.ord b) : a + b ≠ 0 ∧ v.ord (a + b) = v.ord a := by
  have hlt : v.valuation b < v.valuation a := by
    rw [v.valuation_eq_exp_neg_ord ha, v.valuation_eq_exp_neg_ord hb, WithZero.exp_lt_exp]
    omega
  have heq : v.valuation (a + b) = v.valuation a := Valuation.map_add_eq_of_lt_left _ hlt
  refine ⟨fun h0 => ?_, by simp only [ord, heq]⟩
  rw [h0, map_zero] at heq
  exact ha ((Valuation.zero_iff _).1 heq.symm)

theorem ne_zero_of_ord_ne_zero (v : Place k K) {x : K} (h : v.ord x ≠ 0) : x ≠ 0 := by
  rintro rfl
  exact h v.ord_zero

theorem exists_ord_pos_forall_ord_neg (v : Place k K) (S : Finset (Place k K)) (hv : v ∉ S) :
    ∃ u : K, u ≠ 0 ∧ 0 < v.ord u ∧ ∀ w ∈ S, w.ord u < 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    obtain ⟨π, hπ⟩ := v.exists_ord_eq_one
    exact ⟨π, v.ne_zero_of_ord_ne_zero (by omega), by omega, by simp⟩
  | insert w S hwS ih =>
    rw [Finset.mem_insert, not_or] at hv
    obtain ⟨y, hy0, hyv, hyS⟩ := ih hv.2

    obtain ⟨y₁, hy₁v, hy₁w⟩ := SetLike.not_le_iff_exists.1 fun h => hv.1 (eq_of_le h)
    obtain ⟨y₂, hy₂w, hy₂v⟩ := SetLike.not_le_iff_exists.1 fun h => hv.1 (eq_of_le h).symm
    have hy₁0 : y₁ ≠ 0 := fun h => hy₁w (h ▸ w.ring.zero_mem)
    have hy₂0 : y₂ ≠ 0 := fun h => hy₂v (h ▸ v.ring.zero_mem)
    have h1 := (v.ord_nonneg_iff hy₁0).2 hy₁v
    have h2 : v.ord y₂ < 0 := not_le.1 fun h => hy₂v ((v.ord_nonneg_iff hy₂0).1 h)
    have h3 : w.ord y₁ < 0 := not_le.1 fun h => hy₁w ((w.ord_nonneg_iff hy₁0).1 h)
    have h4 := (w.ord_nonneg_iff hy₂0).2 hy₂w
    set z := y₁ / y₂ with hz
    have hz0 : z ≠ 0 := div_ne_zero hy₁0 hy₂0
    have hzv : 0 < v.ord z := by rw [hz, v.ord_div hy₁0 hy₂0]; omega
    have hzw : w.ord z < 0 := by rw [hz, w.ord_div hy₁0 hy₂0]; omega
    by_cases hyw : w.ord y < 0
    · refine ⟨y, hy0, hyv, ?_⟩
      intro w' hw'
      rw [Finset.mem_insert] at hw'
      rcases hw' with rfl | hw'
      · exact hyw
      · exact hyS w' hw'
    push Not at hyw
    set r : ℕ := 1 + ∑ w' ∈ S, (w'.ord y).natAbs with hr
    have hzr0 : z ^ r ≠ 0 := pow_ne_zero _ hz0
    have hordr : ∀ w' : Place k K, w'.ord (z ^ r) = r * w'.ord z := fun w' => w'.ord_pow z r
    have hr1 : (1 : ℤ) ≤ r := by exact_mod_cast Nat.le_add_right 1 _
    have hw := w.ord_add_of_lt hzr0 hy0 (by
      rw [hordr]
      have := mul_neg_of_pos_of_neg (show (0 : ℤ) < r by omega) hzw
      omega)
    refine ⟨z ^ r + y, hw.1, ?_, ?_⟩
    · refine lt_of_lt_of_le (lt_min ?_ hyv) (v.min_le_ord_add hzr0 hy0 hw.1)
      rw [hordr]; exact mul_pos (by omega) hzv
    · intro w' hw'
      rw [Finset.mem_insert] at hw'
      rcases hw' with rfl | hw'
      · rw [hw.2, hordr]; exact mul_neg_of_pos_of_neg (by omega) hzw
      · have hyw' := hyS w' hw'
        have habs : ((w'.ord y).natAbs : ℤ) < r := by
          have h' := Finset.single_le_sum (f := fun w'' : Place k K => (w''.ord y).natAbs)
            (fun _ _ => Nat.zero_le _) hw'
          have h'' : (w'.ord y).natAbs < r := by rw [hr]; omega
          exact_mod_cast h''
        rcases le_or_gt 0 (w'.ord z) with hzw' | hzw'
        · have h := w'.ord_add_of_lt hy0 hzr0 (by
            rw [hordr]
            have := mul_nonneg (show (0 : ℤ) ≤ r by omega) hzw'
            omega)
          rw [add_comm, h.2]; exact hyw'
        · have h := w'.ord_add_of_lt hzr0 hy0 (by
            rw [hordr]
            have := mul_le_mul_of_nonneg_left (show w'.ord z ≤ -1 by omega)
              (show (0 : ℤ) ≤ r by omega)
            omega)
          rw [h.2, hordr]; exact mul_neg_of_pos_of_neg (by omega) hzw'

theorem exists_near_one (v : Place k K) (S : Finset (Place k K)) (hv : v ∉ S) (n : ℤ) :
    ∃ e : K, v.valuation (e - 1) ≤ WithZero.exp (-n) ∧
      ∀ w ∈ S, w.valuation e ≤ WithZero.exp (-n) := by
  obtain ⟨u, hu0, huv, huS⟩ := v.exists_ord_pos_forall_ord_neg S hv
  set s : ℕ := n.toNat + 1 with hs
  have hsn : n ≤ (s : ℤ) := by rw [hs]; push_cast; omega
  have hs1 : (1 : ℤ) ≤ s := by rw [hs]; push_cast; omega
  have ha0 : u ^ s ≠ 0 := pow_ne_zero _ hu0
  have hord : ∀ w : Place k K, w.ord (u ^ s) = s * w.ord u := fun w => w.ord_pow u s
  have hv1 := v.ord_add_of_lt one_ne_zero ha0 (by rw [hord, ord_one]; exact mul_pos (by omega) huv)
  refine ⟨(1 + u ^ s)⁻¹, ?_, ?_⟩
  · have heq : (1 + u ^ s)⁻¹ - 1 = -(u ^ s) / (1 + u ^ s) := by
      field_simp [hv1.1]
      ring
    have hne : -(u ^ s) / (1 + u ^ s) ≠ 0 := div_ne_zero (neg_ne_zero.2 ha0) hv1.1
    rw [heq, v.valuation_le_exp_iff hne, v.ord_div (neg_ne_zero.2 ha0) hv1.1, ord_neg, hv1.2,
      ord_one, hord]
    have := mul_le_mul_of_nonneg_left (show 1 ≤ v.ord u by omega) (show (0 : ℤ) ≤ s by omega)
    omega
  · intro w hw
    have hw1 := w.ord_add_of_lt ha0 one_ne_zero (by
      rw [hord, ord_one]; exact mul_neg_of_pos_of_neg (by omega) (huS w hw))
    rw [add_comm] at hw1
    rw [w.valuation_le_exp_iff (inv_ne_zero hw1.1), ord_inv, hw1.2, hord]
    have := mul_le_mul_of_nonneg_left (show w.ord u ≤ -1 by have := huS w hw; omega)
      (show (0 : ℤ) ≤ s by omega)
    omega

theorem exists_approx_const (S : Finset (Place k K)) (y : Place k K → K) (n : ℤ) :
    ∃ z : K, ∀ v ∈ S, v.valuation (z - y v) ≤ WithZero.exp (-n) := by
  classical
  set B : ℤ := ∑ w ∈ S, ∑ v ∈ S, ((w.ord (y v)).natAbs : ℤ) with hB
  have hyB : ∀ v ∈ S, ∀ w ∈ S, w.valuation (y v) ≤ WithZero.exp B := by
    intro v hv w hw
    by_cases h0 : y v = 0
    · rw [h0, map_zero]; exact zero_le
    rw [w.valuation_le_exp_iff h0]
    have h1 : ((w.ord (y v)).natAbs : ℤ) ≤ ∑ v' ∈ S, ((w.ord (y v')).natAbs : ℤ) :=
      Finset.single_le_sum (f := fun v' => ((w.ord (y v')).natAbs : ℤ))
        (fun _ _ => Int.natCast_nonneg _) hv
    have h2 : ∑ v' ∈ S, ((w.ord (y v')).natAbs : ℤ) ≤ B :=
      Finset.single_le_sum (f := fun w' : Place k K => ∑ v' ∈ S, ((w'.ord (y v')).natAbs : ℤ))
        (fun _ _ => Finset.sum_nonneg fun _ _ => Int.natCast_nonneg _) hw
    omega
  choose e he using fun v : Place k K => v.exists_near_one (S.erase v) (S.notMem_erase v) (n + B)
  refine ⟨∑ v ∈ S, y v * e v, fun w hw => ?_⟩
  have hsplit : ∑ v ∈ S, y v * e v - y w =
      y w * (e w - 1) + ∑ v ∈ S.erase w, y v * e v := by
    rw [← Finset.add_sum_erase S _ hw]
    ring
  have hbound : WithZero.exp B * WithZero.exp (-(n + B)) = WithZero.exp (-n) := by
    rw [← WithZero.exp_add]
    congr 1
    ring
  rw [hsplit]
  refine Valuation.map_add_le _ ?_ (Valuation.map_sum_le _ fun v hv => ?_)
  · rw [map_mul, ← hbound]
    exact mul_le_mul' (hyB w hw w hw) (he w).1
  · rw [map_mul, ← hbound]
    exact mul_le_mul' (hyB v (Finset.mem_of_mem_erase hv) w hw)
      ((he v).2 w (Finset.mem_erase.2 ⟨fun h => (Finset.ne_of_mem_erase hv) h.symm, hw⟩))

theorem exists_approx (S : Finset (Place k K)) (y : Place k K → K) (n : Place k K → ℤ) :
    ∃ z : K, ∀ v ∈ S, v.valuation (z - y v) ≤ WithZero.exp (-n v) := by
  set N : ℤ := ∑ v ∈ S, ((n v).natAbs : ℤ) with hN
  obtain ⟨z, hz⟩ := exists_approx_const S y N
  refine ⟨z, fun v hv => (hz v hv).trans ?_⟩
  rw [WithZero.exp_le_exp, neg_le_neg_iff]
  have := Finset.single_le_sum (f := fun v : Place k K => ((n v).natAbs : ℤ))
    (fun _ _ => Int.natCast_nonneg _) hv
  omega

end Place

end GroundTheory.FunctionField
end

-- bundled from GroundTheory.FunctionField.PlaceAbove
section
namespace GroundTheory.FunctionField

namespace Place

variable {k K K' : Type*} [Field k] [Field K] [Field K'] [Algebra k K] [Algebra k K']
  [Algebra K K'] [IsScalarTower k K K']

def LiesOver (w : Place k K') (v : Place k K) : Prop :=
  w.ring.comap (algebraMap K K') = v.ring

omit [IsScalarTower k K K'] in
theorem LiesOver.mem_iff {w : Place k K'} {v : Place k K} (h : w.LiesOver v) {x : K} :
    algebraMap K K' x ∈ w.ring ↔ x ∈ v.ring := by
  rw [← ValuationSubring.mem_comap, h]

omit [IsScalarTower k K K'] in
theorem LiesOver.algebraMap_mem {w : Place k K'} {v : Place k K} (h : w.LiesOver v) {x : K}
    (hx : x ∈ v.ring) : algebraMap K K' x ∈ w.ring :=
  h.mem_iff.2 hx

def comap [Algebra.IsAlgebraic K K'] (w : Place k K') : Place k K where
  ring := w.ring.comap (algebraMap K K')
  ne_top := by
    intro htop
    apply w.ne_top
    have hK : ∀ a : K, algebraMap K K' a ∈ w.ring := fun a =>
      ValuationSubring.mem_comap.1 (htop ▸ ValuationSubring.mem_top a)
    let : Algebra K w.ring := (RingHom.codRestrict (algebraMap K K') w.ring hK).toAlgebra
    have : IsScalarTower K w.ring K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
    refine eq_top_iff.2 fun z _ => ?_
    have hz : IsIntegral w.ring z := (Algebra.IsIntegral.isIntegral (R := K) z).tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hz
    rw [← hy]
    exact y.2
  algebraMap_mem c := by
    rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact w.algebraMap_mem c

theorem liesOver_comap [Algebra.IsAlgebraic K K'] (w : Place k K') : w.LiesOver (w.comap (K := K)) :=
  rfl

theorem liesOver_iff_comap_eq [Algebra.IsAlgebraic K K'] {w : Place k K'} {v : Place k K} :
    w.LiesOver v ↔ w.comap = v :=
  ⟨fun h => Place.ext h, fun h => congrArg Place.ring h⟩

theorem liesOver_of_le [IsFunctionField k K] [Algebra.IsAlgebraic K K'] {w : Place k K'}
    {v : Place k K} (h : ∀ x ∈ v.ring, algebraMap K K' x ∈ w.ring) : w.LiesOver v := by
  have := Place.eq_of_le (v := v) (w := w.comap) fun x hx => ValuationSubring.mem_comap.2 (h x hx)
  exact liesOver_iff_comap_eq.2 this.symm

abbrev LiesOver.algebra {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    Algebra v.ring w.ring :=
  (RingHom.codRestrict ((algebraMap K K').comp v.ring.subtype) w.ring
    fun a => h.algebraMap_mem a.2).toAlgebra

omit [IsScalarTower k K K'] in
theorem LiesOver.isLocalHom {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    let := h.algebra
    IsLocalHom (algebraMap v.ring w.ring) := by
  let := h.algebra
  refine ⟨fun a ha => ?_⟩
  rw [ValuationSubring.valuation_eq_one_iff] at ha ⊢
  have hw : w.ring.valuation (algebraMap K K' (a : K)) = 1 := ha
  have ha0 : (a : K) ≠ 0 := by
    intro h0
    rw [h0, map_zero, map_zero] at hw
    exact zero_ne_one hw
  have hinv : (a : K)⁻¹ ∈ v.ring := by
    rw [← h.mem_iff, ← w.ring.valuation_le_one_iff, map_inv₀, map_inv₀, hw, inv_one]
  have h1 := (v.ring.valuation_le_one_iff _).2 hinv
  rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ha0))] at h1
  exact le_antisymm (v.ring.valuation_le_one a) h1

theorem LiesOver.isScalarTower {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    let := h.algebra
    IsScalarTower k v.ring w.ring := by
  let := h.algebra
  exact IsScalarTower.of_algebraMap_eq fun c =>
    Subtype.ext (IsScalarTower.algebraMap_apply k K K' c)

theorem _root_.GroundTheory.FunctionField.IsFunctionField.of_finiteDimensional [IsFunctionField k K]
    [FiniteDimensional K K'] : IsFunctionField k K' := by
  obtain ⟨y, hy, hfin⟩ := IsFunctionField.exists_transcendental_finiteDimensional (k := k) (K := K)
  have hb := (isTranscendenceBasis_singleton hy hfin).algebraMap_comp (A := K')
  have hr : Set.range (⇑(algebraMap K K') ∘ ((↑) : ({y} : Set K) → K)) = {algebraMap K K' y} := by
    rw [Set.range_comp, Subtype.range_coe, Set.image_singleton]
  have halg := hb.isAlgebraic_field
  rw [hr] at halg
  have := essFiniteType (k := k) (K := K)
  have : Algebra.EssFiniteType k K' := Algebra.EssFiniteType.comp k K K'
  have : Algebra.EssFiniteType (IntermediateField.adjoin k {algebraMap K K' y}) K' :=
    Algebra.EssFiniteType.of_comp k _ K'
  exact ⟨⟨algebraMap K K' y,
    (algebraicIndependent_singleton_iff (⟨y, rfl⟩ : ({y} : Set K))).1 hb.1,
    Algebra.finite_of_essFiniteType_of_isAlgebraic⟩⟩

section Degree

variable [IsFunctionField k K]

noncomputable def uniformizer (v : Place k K) : K :=
  Classical.choose v.exists_ord_eq_one

theorem ord_uniformizer (v : Place k K) : v.ord v.uniformizer = 1 :=
  Classical.choose_spec v.exists_ord_eq_one

theorem uniformizer_ne_zero (v : Place k K) : v.uniformizer ≠ 0 := fun h => by
  have h1 := v.ord_uniformizer
  rw [h, ord_zero] at h1
  exact zero_ne_one h1

variable [IsFunctionField k K']

noncomputable def ramificationIdx (w : Place k K') (v : Place k K) : ℕ :=
  (w.ord (algebraMap K K' v.uniformizer)).toNat

noncomputable def inertiaDeg (w : Place k K') (v : Place k K) : ℕ :=
  w.deg / v.deg

omit [IsFunctionField k K] [IsFunctionField k K'] [IsScalarTower k K K'] in
theorem LiesOver.isTorsionFree {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    letI := h.algebra
    Module.IsTorsionFree v.ring w.ring := by
  let := h.algebra
  exact Module.isTorsionFree_iff_algebraMap_injective.2 fun a b hab =>
    Subtype.ext ((algebraMap K K').injective (congrArg Subtype.val hab))


omit [IsScalarTower k K K'] in
theorem LiesOver.valuation_algebraMap {w : Place k K'} {v : Place k K} (h : w.LiesOver v) (x : K) :
    letI := h.algebra
    v.valuation x ^ (IsLocalRing.maximalIdeal v.ring).ramificationIdx'
        (IsLocalRing.maximalIdeal w.ring) =
      w.valuation (algebraMap K K' x) := by
  let := h.algebra
  have := h.isLocalHom
  have := h.isTorsionFree
  let : Algebra v.ring K' := ((algebraMap K K').comp (algebraMap v.ring K)).toAlgebra
  have : IsScalarTower v.ring K K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower v.ring w.ring K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : w.heightOneSpectrum.asIdeal.LiesOver v.heightOneSpectrum.asIdeal :=
    inferInstanceAs ((IsLocalRing.maximalIdeal w.ring).LiesOver (IsLocalRing.maximalIdeal v.ring))
  have hv := IsDedekindDomain.HeightOneSpectrum.valuation_liesOver K' v.heightOneSpectrum
    w.heightOneSpectrum x
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx v.heightOneSpectrum.asIdeal
    w.heightOneSpectrum.asIdeal v.heightOneSpectrum.ne_bot] at hv
  simpa only [Place.valuation, Place.heightOneSpectrum] using hv

theorem LiesOver.ramificationIdx'_eq {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    letI := h.algebra
    (IsLocalRing.maximalIdeal v.ring).ramificationIdx' (IsLocalRing.maximalIdeal w.ring) =
      w.ramificationIdx v := by
  let := h.algebra
  have h1 := h.valuation_algebraMap v.uniformizer
  have hπ : algebraMap K K' v.uniformizer ≠ 0 := (map_ne_zero _).2 v.uniformizer_ne_zero
  rw [v.valuation_eq_exp_neg_ord v.uniformizer_ne_zero, v.ord_uniformizer,
    w.valuation_eq_exp_neg_ord hπ, ← WithZero.exp_nsmul, WithZero.exp_inj, nsmul_eq_mul] at h1
  rw [ramificationIdx]
  omega

theorem LiesOver.ord_algebraMap {w : Place k K'} {v : Place k K} (h : w.LiesOver v) (x : K) :
    w.ord (algebraMap K K' x) = w.ramificationIdx v * v.ord x := by
  by_cases hx : x = 0
  · simp [hx]
  let := h.algebra
  have h1 := h.valuation_algebraMap x
  have hx' : algebraMap K K' x ≠ 0 := (map_ne_zero _).2 hx
  rw [v.valuation_eq_exp_neg_ord hx, w.valuation_eq_exp_neg_ord hx', ← WithZero.exp_nsmul,
    WithZero.exp_inj, nsmul_eq_mul, h.ramificationIdx'_eq] at h1
  linarith


omit [IsFunctionField k K'] in
theorem LiesOver.deg_mul_finrank {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    letI := h.algebra
    letI := h.isLocalHom
    v.deg * Module.finrank v.ResidueField w.ResidueField = w.deg := by
  let := h.algebra
  have := h.isLocalHom
  have := h.isScalarTower
  exact (letI : Module.Free v.ResidueField w.ResidueField := Module.Free.of_divisionRing _ _; Module.finrank_mul_finrank k v.ResidueField w.ResidueField)


omit [IsFunctionField k K'] in
theorem LiesOver.finrank_residueField {w : Place k K'} {v : Place k K} (h : w.LiesOver v) :
    letI := h.algebra
    letI := h.isLocalHom
    Module.finrank v.ResidueField w.ResidueField = w.inertiaDeg v := by
  let := h.algebra
  have := h.isLocalHom
  rw [inertiaDeg, ← h.deg_mul_finrank, Nat.mul_div_cancel_left _ v.deg_pos]

end Degree

end Place

end GroundTheory.FunctionField
end

