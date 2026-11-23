module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Formalism.SatakeDualWeyl.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0212
public import Formalism.GradedWeylDivisibility.StatementA
public import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharactersMulComapConjIndLinear
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0259
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0260
public import Formalism.SatakeDualWeyl.Statement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0082
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0262
public import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousUniMat
section
open MeasureTheory GlobalTheory.PRep GlobalTheory.LGrp Matrix
open scoped NNReal

noncomputable section
namespace GlobalTheory.BorelModulus

abbrev Pos (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2}

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem mem_U_iff (g : GL (Fin n) k) :
    g ∈ (borelGL k (Fin n)).U ↔ (∀ i j, j < i → g.val i j = 0) ∧ ∀ i, g.val i i = 1 := by
  rw [LeviDatum.mem_U]
  constructor
  · rintro ⟨h, e⟩
    exact ⟨fun _ _ hij => h hij, fun i => congrArg (fun t : Fin n → kˣ => (t i : k)) e⟩
  · rintro ⟨h, e⟩
    exact ⟨fun _ _ hij => h _ _ hij, funext fun i => Units.ext (e i)⟩

def uniMat (x : Pos n → k) : Matrix (Fin n) (Fin n) k :=
  fun i j => if h : i < j then x ⟨(i, j), h⟩ else if i = j then 1 else 0

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem uniMat_low (x : Pos n → k) (i j : Fin n) (h : j < i) : uniMat x i j = 0 := by
  simp [uniMat, h.not_gt, h.ne']

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem uniMat_diag (x : Pos n → k) (i : Fin n) : uniMat x i i = 1 := by
  simp [uniMat]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem uniMat_det (x : Pos n → k) : (uniMat x).det = 1 := by
  rw [det_of_upperTriangular (fun i j h => uniMat_low x i j h)]
  simp [uniMat_diag]

theorem continuous_uniMat : Continuous (uniMat : (Pos n → k) → _) := by
  refine continuous_matrix fun i j => ?_
  unfold uniMat
  split_ifs
  · exact continuous_apply _
  · exact continuous_const
  · exact continuous_const

def uniGL (x : Pos n → k) : GL (Fin n) k :=
  ⟨uniMat x, (uniMat x).adjugate, by rw [mul_adjugate, uniMat_det, one_smul],
    by rw [adjugate_mul, uniMat_det, one_smul]⟩

theorem continuous_uniGL : Continuous (uniGL : (Pos n → k) → _) :=
  Units.continuous_iff.2 ⟨continuous_uniMat, continuous_uniMat.matrix_adjugate⟩

def coord (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) :
    (borelGL k (Fin n)).U ≃ₜ (Pos n → k) where
  toFun u p := u.1.val p.1.1 p.1.2
  invFun x := ⟨uniGL x, (mem_U_iff _).2 ⟨uniMat_low x, uniMat_diag x⟩⟩
  left_inv u := by
    obtain ⟨h1, h2⟩ := (mem_U_iff _).1 u.2
    refine Subtype.ext (Units.ext (Matrix.ext fun i j => ?_))
    show uniMat (fun p : Pos n => u.1.val p.1.1 p.1.2) i j = u.1.val i j
    rcases lt_trichotomy i j with h | rfl | h
    · simp [uniMat, h]
    · rw [uniMat_diag, h2]
    · rw [uniMat_low _ _ _ h, h1 _ _ h]
  right_inv x := by
    funext p
    show uniMat x _ _ = _
    simp [uniMat, p.2]
  continuous_toFun := continuous_pi fun p => (continuous_entry _ _).comp continuous_subtype_val
  continuous_invFun := continuous_uniGL.subtype_mk _

theorem coord_apply (u : (borelGL k (Fin n)).U) (p : Pos n) : coord k n u p = u.1.val p.1.1 p.1.2 := rfl

def leftMat (A : Matrix (Fin n) (Fin n) k) : Matrix (Pos n) (Pos n) k :=
  fun p q => if q.1.2 = p.1.2 then A p.1.1 q.1.1 else 0

theorem leftMat_det (u : (borelGL k (Fin n)).U) : (leftMat u.1.val).det = 1 := by
  obtain ⟨h1, h2⟩ := (mem_U_iff _).1 u.2
  have hb : (leftMat u.1.val).BlockTriangular (fun p => p.1.1) := fun p q h => by
    simp [leftMat, h1 _ _ h]
  rw [hb.det_fintype]
  refine Finset.prod_eq_one fun a _ => ?_
  have : (leftMat u.1.val).toSquareBlock (fun p => p.1.1) a = 1 := by
    ext ⟨⟨⟨i, j⟩, hp⟩, rfl⟩ ⟨⟨⟨i', j'⟩, hq⟩, e⟩
    obtain rfl : i' = i := e
    simp [toSquareBlock_def, leftMat, h2, Matrix.one_apply, eq_comm]
  rw [this, det_one]

theorem coord_mul (u x : (borelGL k (Fin n)).U) :
    coord k n (u * x) = (leftMat u.1.val).mulVec (coord k n x) + coord k n u := by
  obtain ⟨h1, h2⟩ := (mem_U_iff _).1 x.2
  funext ⟨⟨i, j⟩, hp⟩
  show (u.1.val * x.1.val) i j = ∑ q : Pos n, (if q.1.2 = j then u.1.val i q.1.1 else 0) * x.1.val q.1.1 q.1.2 +
    u.1.val i j
  rw [← Finset.sum_subtype (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2) (by simp)
    (fun q : Fin n × Fin n => (if q.2 = j then u.1.val i q.1 else 0) * x.1.val q.1 q.2),
    Finset.sum_filter, Fintype.sum_prod_type, Matrix.mul_apply]
  have : u.1.val i j = ∑ l, if l = j then u.1.val i l else 0 := by simp
  rw [this, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)]
  rcases lt_trichotomy l j with h | rfl | h
  · simp [h, h.ne]
  · simp [h2]
  · simp [h.not_gt, h.ne', h1 _ _ h]

theorem coord_conj (t : Fin n → kˣ) (ht) (x : (borelGL k (Fin n)).U) :
    coord k n (conjAut _ ⟨(borelGL k (Fin n)).s t, ht⟩ x) =
      (diagonal fun p : Pos n => ((t p.1.1 * (t p.1.2)⁻¹ : kˣ) : k)).mulVec (coord k n x) := by
  funext p
  rw [mulVec_diagonal, coord_apply, conjAut_coe, coord_apply]
  show ((diagHom k (Fin n) t) * x.1 * (diagHom k (Fin n) t)⁻¹).val _ _ = _
  rw [← map_inv, Units.val_mul, Units.val_mul, diagHom_val, diagHom_val, mul_diagonal, diagonal_mul]
  simp only [Pi.inv_apply, Units.val_mul]
  ring

theorem prod_pos_eq {G : Type} [CommGroup G] (t : Fin n → G) :
    ∏ p : Pos n, (t p.1.1 * (t p.1.2)⁻¹) = ∏ i : Fin n, t i ^ ((n : ℤ) - 1 - 2 * (i.val : ℤ)) := by
  rw [← Finset.prod_subtype (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2) (by simp)
    (fun q : Fin n × Fin n => t q.1 * (t q.2)⁻¹), Finset.prod_mul_distrib, Finset.prod_filter, Finset.prod_filter,
    Fintype.prod_prod_type, Fintype.prod_prod_type_right, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [← Finset.prod_filter, Finset.prod_const]
  rw [Finset.filter_lt_eq_Ioi, Finset.filter_gt_eq_Iio, Fin.card_Ioi, Fin.card_Iio, inv_pow, ← zpow_natCast,
    ← zpow_natCast, ← _root_.zpow_sub]
  congr 1
  have := i.2
  omega

theorem delta_eq (q : (borelGL k (Fin n)).Q) :
    (borelGL k (Fin n)).delta q =
      distribHaarChar k (∏ p : Pos n, ((borelGL k (Fin n)).p q p.1.1 * ((borelGL k (Fin n)).p q p.1.2)⁻¹)) := by
  haveI := SplitWeil.secondCountable k
  borelize k
  borelize ↥(borelGL k (Fin n)).U
  let ν : Measure k := Measure.addHaar
  let π : Measure (Pos n → k) := Measure.pi fun _ => ν
  let e := coord k n
  let μ : Measure (borelGL k (Fin n)).U := Measure.map e.symm π
  have hm : ∀ A : Matrix (Pos n) (Pos n) k, Measurable A.mulVec := fun A =>
    (continuous_const.matrix_mulVec continuous_id).measurable
  have hes : Measurable e.symm := e.symm.continuous.measurable
  haveI : π.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure π
  haveI : μ.Regular := Measure.Regular.map e.symm
  haveI : μ.IsOpenPosMeasure := e.symm.continuous.isOpenPosMeasure_map e.symm.surjective
  haveI : μ.IsMulLeftInvariant := ⟨fun u => by
    have h1 : (fun x => u * x) ∘ e.symm = e.symm ∘ (fun y => y + e u) ∘ (leftMat u.1.val).mulVec := by
      funext y
      apply e.injective
      simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
      rw [coord_mul, Homeomorph.apply_symm_apply]
    have h2 := WeilM.smul_map_mulVec_pi ν (leftMat u.1.val) 1 (by rw [leftMat_det]; rfl)
    rw [map_one, ENNReal.coe_one, one_smul] at h2
    rw [Measure.map_map (measurable_const_mul u) hes, h1,
      ← Measure.map_map hes ((measurable_add_const _).comp (hm _)),
      ← Measure.map_map (measurable_add_const _) (hm _), h2, map_add_right_eq_self]⟩
  haveI : μ.IsHaarMeasure := {}
  set t := (borelGL k (Fin n)).p q
  rw [LeviDatum.delta_apply]
  set g : Subgroup.normalizer ((borelGL k (Fin n)).U : Set (GL (Fin n) k)) := ⟨(borelGL k (Fin n)).s t, _⟩
  set c := distribHaarChar k (∏ p : Pos n, (t p.1.1 * (t p.1.2)⁻¹))
  have hc : Continuous (conjAut (borelGL k (Fin n)).U g) := (conjAut _ g).continuous
  have h3 : (c : ENNReal) • Measure.map (conjAut _ g) μ = μ := by
    have h1 : (conjAut _ g) ∘ e.symm =
        e.symm ∘ (diagonal fun p : Pos n => ((t p.1.1 * (t p.1.2)⁻¹ : kˣ) : k)).mulVec := by
      funext y
      apply e.injective
      simp only [Function.comp_apply, Homeomorph.apply_symm_apply]
      rw [coord_conj, Homeomorph.apply_symm_apply]
    have h2 := WeilM.smul_map_mulVec_pi ν (diagonal fun p : Pos n => ((t p.1.1 * (t p.1.2)⁻¹ : kˣ) : k))
      (∏ p : Pos n, (t p.1.1 * (t p.1.2)⁻¹)) (by rw [det_diagonal, Units.coe_prod])
    rw [Measure.map_map hc.measurable hes, h1, ← Measure.map_map hes (hm _),
      ← Measure.map_smul, h2]
    exact hes.aemeasurable
  haveI : LocallyCompactSpace (borelGL k (Fin n)).U := (borelGL k (Fin n)).closed_U.locallyCompactSpace
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : (borelGL k (Fin n)).U)
  have h4 := modulus_measure _ (borelGL k (Fin n)).closed_U μ g K
  have h5 := congrArg (fun m : Measure _ => m (conjAut _ g '' K)) h3
  simp only [Measure.smul_apply, smul_eq_mul] at h5
  rw [Measure.map_apply hc.measurable
    (hK.image hc).isClosed.measurableSet,
    Set.preimage_image_eq _ (conjAut _ g).injective, h4] at h5
  exact (ENNReal.coe_injective ((ENNReal.mul_left_inj (Measure.measure_pos_of_mem_nhds μ hK1).ne'
    hK.measure_lt_top.ne).1 h5)).symm

theorem delta_borelGL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n : ℕ) (q : (borelGL k (Fin n)).Q), (((borelGL k (Fin n)).delta q : ℝ≥0) : ℝ) =
      ∏ i : Fin n, GlobalTheory.SplitWeil.nabs k ((borelGL k (Fin n)).p q i) ^ ((n : ℤ) - 1 - 2 * (i.val : ℤ)) := by
  intro k _ _ _ _ n q
  rw [delta_eq, prod_pos_eq, map_prod, NNReal.coe_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h : ∀ (x : kˣ) (m : ℤ), distribHaarChar k (x ^ m) = distribHaarChar k x ^ m := fun x m =>
    (congrArg Units.val (map_zpow (distribHaarChar k (G := kˣ)).toHomUnits x m)).trans
      (Units.val_zpow_eq_zpow_val _ _)
  rw [h, NNReal.coe_zpow]
  rfl

end GlobalTheory.BorelModulus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylEqBotOfNotAntitone
section
namespace GlobalTheory.NonDomZero

theorem exists_lt_lt_of_not_antitone {N : ℕ} {ν : Fin N → ℕ} (hν : ¬ Antitone ν) :
    ∃ a b : Fin N, a < b ∧ ν a < ν b := by
  simp only [Antitone, not_forall] at hν
  obtain ⟨a, b, hab, hlt⟩ := hν
  refine ⟨a, b, lt_of_le_of_ne hab ?_, lt_of_not_ge hlt⟩
  rintro rfl
  exact hlt le_rfl

theorem dualWeyl_eq_bot_of_not_antitone :
    ∀ (O : Type) [CommRing O] [IsDomain O] [CharZero O] (N : ℕ) (ν : Fin N → ℕ),
      ¬ Antitone ν → Formalism.GradedWeylDivisibility.dualWeyl O N N ν = ⊥ := by
  intro O _ _ _ N ν hν
  exact Formalism.GradedWeylDivisibility.dualWeylModuleNonDominant O N N ν (exists_lt_lt_of_not_antitone hν)

end GlobalTheory.NonDomZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmMemVirtualCharactersOfPowerSumEigenvalues
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.EsymmVirt

theorem esymm_zero' (s : Multiset ℂ) : s.esymm 0 = 1 := by
  simp [Multiset.esymm]

theorem esymm_cons_succ (a : ℂ) (s : Multiset ℂ) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.map_map, Multiset.sum_map_mul_left]

theorem coeff_prod_one_add (s : Multiset ℂ) (n : ℕ) :
    ((s.map fun a => (1 + C a * X : ℂ[X])).prod).coeff n = s.esymm n := by
  induction s using Multiset.induction_on generalizing n with
  | empty =>
    cases n with
    | zero => simp [Multiset.esymm]
    | succ n => simp [Multiset.esymm, Polynomial.coeff_one, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, add_mul, one_mul, mul_assoc, coeff_add, coeff_C_mul]
    cases n with
    | zero => simp [ih, esymm_zero']
    | succ n => rw [coeff_X_mul, ih, ih, esymm_cons_succ]

theorem esymm_add (s t : Multiset ℂ) (n : ℕ) :
    (s + t).esymm n = ∑ i ∈ Finset.range (n + 1), s.esymm i * t.esymm (n - i) := by
  rw [← coeff_prod_one_add, Multiset.map_add (f := _), Multiset.prod_add, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_prod_one_add]

theorem esymm_eq_of_psum_eq (s t : Multiset ℂ)
    (h : ∀ j : ℕ, 0 < j → (s.map (· ^ j)).sum = (t.map (· ^ j)).sum) (n : ℕ) :
    s.esymm n = t.esymm n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [esymm_zero', esymm_zero']
    have h1 := GlobalTheory.multiset_newton_psum s n hn
    have h2 := GlobalTheory.multiset_newton_psum t n hn
    have h3 : ∑ i ∈ Finset.Ioo 0 n, (-1) ^ i * s.esymm i * (s.map (· ^ (n - i))).sum
        = ∑ i ∈ Finset.Ioo 0 n, (-1) ^ i * t.esymm i * (t.map (· ^ (n - i))).sum := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [Finset.mem_Ioo] at hi
      rw [ih i hi.2, h (n - i) (by omega)]
    have h4 : ((-1) ^ (n + 1) * (n : ℂ)) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num)) (by exact_mod_cast hn.ne')
    apply mul_left_cancel₀ h4
    linear_combination h2 - h1 + h n hn + h3

variable {G : Type} [Group G] [Finite G]

theorem one_mem_virt : (fun _ : G => (1 : ℂ)) ∈ Virt ℂ ℂ G := by
  simpa using (virt_mul_comap_conj_ind_linear G).2.2.2.2 1

theorem esymm_add_mem_virt {A B : G → Multiset ℂ}
    (hA : ∀ s, (fun g => (A g).esymm s) ∈ Virt ℂ ℂ G)
    (hB : ∀ s, (fun g => (B g).esymm s) ∈ Virt ℂ ℂ G) (s : ℕ) :
    (fun g => (A g + B g).esymm s) ∈ Virt ℂ ℂ G := by
  have : (fun g => (A g + B g).esymm s) = ∑ i ∈ Finset.range (s + 1),
      (fun g => (A g).esymm i) * (fun g => (B g).esymm (s - i)) := by
    funext g
    simp [esymm_add, Finset.sum_apply]
  rw [this]
  exact sum_mem fun i _ => (virt_mul_comap_conj_ind_linear G).1 _ (hA _) _ (hB _)

theorem exists_multisets {φ : G → ℂ} (hφ : φ ∈ Virt ℂ ℂ G) :
    ∃ A B : G → Multiset ℂ, (∀ s, (fun g => (A g).esymm s) ∈ Virt ℂ ℂ G) ∧
      (∀ s, (fun g => (B g).esymm s) ∈ Virt ℂ ℂ G) ∧
      ∀ g j, 0 < j → φ (g ^ j) + ((B g).map (· ^ j)).sum = ((A g).map (· ^ j)).sum := by
  have h0 : ∀ s, (fun _ : G => (0 : Multiset ℂ).esymm s) ∈ Virt ℂ ℂ G := by
    intro s
    cases s with
    | zero => simpa only [esymm_zero'] using one_mem_virt
    | succ s =>
      have : (fun _ : G => (0 : Multiset ℂ).esymm (s + 1)) = 0 := by
        funext g
        simp [Multiset.esymm, Multiset.powersetCard_zero_right]
      rw [this]
      exact zero_mem _
  induction hφ using AddSubgroup.closure_induction with
  | mem a ha =>
    obtain ⟨n, ρ, hρ⟩ := (matrixChar_iff_isChar G a).2 ha
    refine ⟨fun g => (Matrix.charpoly (ρ g : Matrix (Fin n) (Fin n) ℂ)).roots, fun _ => 0,
      fun s => isChar_mem_virt_complex (isChar_esymm_roots_charpoly G n s ρ), h0, fun g j _ => ?_⟩
    rw [hρ, map_pow, Units.val_pow_eq_pow_val, Matrix.trace_eq_sum_roots_charpoly,
      GlobalTheory.CharpolyPow.roots_charpoly_pow]
    simp
  | zero => exact ⟨fun _ => 0, fun _ => 0, h0, h0, fun g j _ => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨A, B, hA, hB, h⟩ := hx
    obtain ⟨A', B', hA', hB', h'⟩ := hy
    refine ⟨fun g => A g + A' g, fun g => B g + B' g, esymm_add_mem_virt hA hA',
      esymm_add_mem_virt hB hB', fun g j hj => ?_⟩
    simp only [Pi.add_apply, Multiset.map_add (f := _), Multiset.sum_add]
    linear_combination h g j hj + h' g j hj
  | neg x _ hx =>
    obtain ⟨A, B, hA, hB, h⟩ := hx
    refine ⟨B, A, hB, hA, fun g j hj => ?_⟩
    simp only [Pi.neg_apply]
    linear_combination - h g j hj

theorem esymm_mem_virt : ∀ (G : Type) [Group G] [Finite G] (φ : G → ℂ) (x : G → Multiset ℂ),
    φ ∈ Virt ℂ ℂ G → (∀ (g : G) (j : ℕ), 0 < j → φ (g ^ j) = ((x g).map (· ^ j)).sum) →
    ∀ s : ℕ, (fun g => (x g).esymm s) ∈ Virt ℂ ℂ G := by
  intro G _ _ φ x hφ hx s
  obtain ⟨A, B, hA, hB, h⟩ := exists_multisets hφ
  have he : ∀ g n, (x g + B g).esymm n = (A g).esymm n := fun g n =>
    esymm_eq_of_psum_eq _ _ (fun j hj => by
      rw [Multiset.map_add (f := _), Multiset.sum_add, ← hx g j hj, h g j hj]) n
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    have : (fun g => (x g).esymm s) = (fun g => (A g).esymm s) - ∑ i ∈ Finset.range s,
        (fun g => (x g).esymm i) * (fun g => (B g).esymm (s - i)) := by
      funext g
      have := he g s
      rw [esymm_add, Finset.sum_range_succ, Nat.sub_self, esymm_zero', mul_one] at this
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.mul_apply]
      linear_combination this
    rw [this]
    exact sub_mem (hA s) (sum_mem fun i hi =>
      (virt_mul_comap_conj_ind_linear G).1 _ (ih i (Finset.mem_range.1 hi)) _ (hB _))

end GlobalTheory.EsymmVirt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatRingHomBasicPropertiesStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleFaithfullyFlatRingHom_basic_properties : (EtFF.IsMultiplicative ∧ EtFF.IsStableUnderCobaseChange ∧ EtFF.RespectsIso) ∧ (∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ↔ Etale (Spec.map g) ∧ Surjective (Spec.map g)) ∧ ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → Algebra.FiniteType ℤ A → Algebra.FiniteType ℤ B := by
  first | (exact @GlobalTheory.EtC.etFF_basic) | (exact GlobalTheory.EtC.etFF_basic) | (intros; apply GlobalTheory.EtC.etFF_basic  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCocycleOfMapToDegreeOneTerm
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem exists_cocycle_of_map_to_X_one :
    ∀ (C : Shv ℤ) (I : Cx ℤ) (ψ : C ⟶ I.X 1), ψ ≫ I.d 1 2 = 0 →
      ∃ w : Cocycle (sgl C) I 1, sglι C ≫ w.1.v 0 1 (zero_add 1) = ψ := by
  intro C I ψ hψ
  refine ⟨Cocycle.fromSingleMk ψ (zero_add 1) 2 (by norm_num) hψ, ?_⟩
  rw [Cocycle.fromSingleMk_coe, Cochain.fromSingleMk_v]
  exact (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 C).inv_hom_id_assoc ψ

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCyclicVectorOfSeparableCharpolyStatement
section
open Polynomial Matrix GlobalTheory.LatOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cyclicVector_of_separable_charpoly' : ∀ {K : Type} [Field K] (n : ℕ) (γ : Matrix (Fin n) (Fin n) K), γ.charpoly.Separable →
    ∃ v₀ : Fin n → K, ∀ u : Fin n → K, ∃ p : K[X], u = aeval γ p *ᵥ v₀ := by
  first | exact @GlobalTheory.LatOrb.exists_cyclicVector_of_separable_charpoly | exact GlobalTheory.LatOrb.exists_cyclicVector_of_separable_charpoly | (intros; apply GlobalTheory.LatOrb.exists_cyclicVector_of_separable_charpoly <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFilteredColimitFiniteTypeIntRingsStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_filteredColimit_finiteType_int_rings : ∀ A : CommRingCat.{0}, ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0}) (ι : D ⟶ (Functor.const J).obj A), Nonempty (IsColimit (Cocone.mk A ι)) ∧ ∀ j, Algebra.FiniteType ℤ (D.obj j) := by
  first | (exact @GlobalTheory.FiniteTypeColimit.exists_filtered_colimit_finiteType) | (exact GlobalTheory.FiniteTypeColimit.exists_filtered_colimit_finiteType) | (intros; apply GlobalTheory.FiniteTypeColimit.exists_filtered_colimit_finiteType  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePresentationModelOfIsColimit
section
open CategoryTheory Limits TensorProduct

namespace GlobalTheory.FpDescent

theorem exists_finitePresentation_model_of_isColimit :
    ∀ (J : Type) [SmallCategory J] [IsFiltered J] (F : J ⥤ CommRingCat.{0}) (c : Cocone F),
    IsColimit c → ∀ (D : Type) [CommRing D] [Algebra c.pt D], Algebra.FinitePresentation c.pt D →
    ∃ (j : J) (A : Type) (_ : CommRing A) (_ : Algebra (F.obj j) A)
      (_ : Algebra.FinitePresentation (F.obj j) A),
      letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
      Nonempty (c.pt ⊗[F.obj j] A ≃ₐ[c.pt] D) := by
  intro J _ _ F c hc D _ _ hD
  classical
  have hc' := isColimitOfPreserves (forget _) hc
  let P := Algebra.Presentation.ofFinitePresentation c.pt D
  obtain ⟨j, hj⟩ : ∃ j, P.coeffs ⊆ Set.range (c.ι.app j).hom := by
    have hfin := P.finite_coeffs
    choose jx x hx using fun y : c.pt ↦ Types.jointly_surjective_of_isColimit hc' y
    obtain ⟨j, hj⟩ := IsFiltered.sup_objs_exists (hfin.toFinset.image jx)
    refine ⟨j, fun y hy ↦ ?_⟩
    obtain ⟨f⟩ := hj (Finset.mem_image_of_mem jx (hfin.mem_toFinset.mpr hy))
    refine ⟨F.map f (x y), ?_⟩
    have h1 := hx y
    have h2 := congr(($(c.w f)).hom (x y))
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h2
    rw [h2]
    exact h1
  letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
  letI : Algebra (F.obj j) D := ((algebraMap c.pt D).comp (c.ι.app j).hom).toAlgebra
  haveI : IsScalarTower (F.obj j) c.pt D := IsScalarTower.of_algebraMap_eq (fun _ ↦ rfl)
  haveI : P.HasCoeffs (F.obj j) := ⟨hj⟩
  exact ⟨j, P.ModelOfHasCoeffs (F.obj j), inferInstance, inferInstance, inferInstance,
    ⟨P.tensorModelOfHasCoeffsEquiv (F.obj j)⟩⟩

end GlobalTheory.FpDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicParamOfDegZeroCompatibleStatement
section
open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_param_of_degZero_compatible : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → ∀ G : C0 K.Oc, (∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → G T' = φ.φ (G T)) → ∃ p : Hol F.V, ∀ T : K.Obj, G T = algebraMap (Hol F.V) T.C p := by
  first | exact @GlobalTheory.AnPer.Charts.exists_param_of_deg_zero | exact GlobalTheory.AnPer.Charts.exists_param_of_deg_zero | (intros; apply GlobalTheory.AnPer.Charts.exists_param_of_deg_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsSideMore
section
theorem GlobalTheory.FourClauses.adm : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.IrreducibleAdmissibleGL :=
  fun h k _ _ _ _ n V _ _ π hs hi => (h k).1 (Fin n) V π hs hi
end

