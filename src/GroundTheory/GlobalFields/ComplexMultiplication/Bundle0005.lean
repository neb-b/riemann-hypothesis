module

public import Mathlib
public import GroundTheory.GlobalFields.ComplexMultiplication.AnalyticAlgebraicPoints
public import GroundTheory.GlobalFields.ComplexMultiplication.ReductionPoints
public import GroundTheory.GlobalFields.ComplexMultiplication.ReductionGauss
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.Bundle0002

@[expose] public section

-- bundled from GroundTheory.GlobalFields.ComplexMultiplication.AnalyticAlgebraicIndependent
section
open Filter Topology Set Polynomial
open scoped PeriodPair

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

theorem meromorphicAt_fun_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ} {x : ℂ}
    (hf : ∀ i, MeromorphicAt (f i) x) : MeromorphicAt (fun z ↦ ∑ i ∈ s, f i z) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a).add ih

theorem germ_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ} (hf : ∀ i, Meromorphic (f i)) :
    germ (fun z ↦ ∑ i ∈ s, f i z) = ∑ i ∈ s, germ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [germ_const, map_zero]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have hs : Meromorphic fun z ↦ ∑ i ∈ s, f i z := fun x ↦
      meromorphicAt_fun_sum s fun i ↦ hf i x
    rw [← ih]
    exact germ_add (hf a) hs

theorem lt_meromorphicOrderAt_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ} {x : ℂ}
    (hf : ∀ i, MeromorphicAt (f i) x) {c : ℤ}
    (hc : ∀ i ∈ s, (c : WithTop ℤ) < meromorphicOrderAt (f i) x) :
    (c : WithTop ℤ) < meromorphicOrderAt (fun z ↦ ∑ i ∈ s, f i z) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    rw [meromorphicOrderAt_eq_top_iff.2 (Eventually.of_forall fun _ ↦ rfl)]
    exact WithTop.coe_lt_top c
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have hs : MeromorphicAt (fun z ↦ ∑ i ∈ s, f i z) x := meromorphicAt_fun_sum s hf
    have h1 := hc a (Finset.mem_insert_self a s)
    have h2 := ih fun i hi ↦ hc i (Finset.mem_insert_of_mem hi)
    exact lt_of_lt_of_le (lt_min h1 h2) (meromorphicOrderAt_add (hf a) hs)

theorem exists_int_of_real_mul_mem (L : PeriodPair) {r : ℝ} (h : (r : ℂ) * L.ω₁ ∈ L.lattice) :
    ∃ a : ℤ, r = a := by
  obtain ⟨m, n, e⟩ := PeriodPair.mem_lattice.1 h
  have := LinearIndependent.pair_iff.mp L.indep ((m : ℝ) - r) (n : ℝ) (by
    simp only [Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_intCast]
    linear_combination e)
  exact ⟨m, (sub_eq_zero.1 this.1).symm⟩

theorem sqrt_two_ne_zero : (Real.sqrt 2 : ℂ) ≠ 0 := by
  rw [ne_eq, Complex.ofReal_eq_zero]
  exact (Real.sqrt_pos.2 two_pos).ne'

theorem injective_mk_div_sqrt_two (L : PeriodPair) :
    Function.Injective fun m : ℕ ↦ Torus.mk L ((m : ℂ) * L.ω₁ / (Real.sqrt 2 : ℂ)) := by
  intro m m' hm
  simp only at hm
  rw [Torus.mk_eq_mk_iff] at hm
  have e : (m : ℂ) * L.ω₁ / (Real.sqrt 2 : ℂ) - (m' : ℂ) * L.ω₁ / (Real.sqrt 2 : ℂ) =
      ((((m : ℝ) - m') / Real.sqrt 2 : ℝ) : ℂ) * L.ω₁ := by
    push_cast
    ring
  rw [e] at hm
  obtain ⟨a, ha⟩ := exists_int_of_real_mul_mem L hm
  by_contra hne
  have hd : ((m : ℝ) - m') ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hne)
  have ha0 : (a : ℝ) ≠ 0 := by
    intro h0
    rw [h0] at ha
    exact hd ((div_eq_zero_iff.1 ha).resolve_right (Real.sqrt_pos.2 two_pos).ne')
  have hs2 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 two_pos).ne'
  have hs : Real.sqrt 2 = ((m : ℝ) - m') / a := by
    rw [eq_div_iff ha0]
    rw [div_eq_iff hs2] at ha
    linear_combination (-1 : ℝ) * ha
  exact irrational_sqrt_two ⟨((m : ℚ) - m') / a, by push_cast; exact hs.symm⟩

theorem meromorphicOrderAt_weierstrassP_sqrt_two (L : PeriodPair) {z₀ : ℂ}
    (hz : (Real.sqrt 2 : ℂ) * z₀ + 0 ∈ L.lattice) :
    meromorphicOrderAt (fun z ↦ ℘[L] ((Real.sqrt 2 : ℂ) * z + 0)) z₀ = -2 := by
  have hg : AnalyticAt ℂ (fun z : ℂ ↦ (Real.sqrt 2 : ℂ) * z + 0) z₀ := by fun_prop
  have hd : deriv (fun z : ℂ ↦ (Real.sqrt 2 : ℂ) * z + 0) z₀ ≠ 0 := by
    have h1 := ((hasDerivAt_id' z₀).const_mul (Real.sqrt 2 : ℂ)).add_const 0
    rw [h1.deriv, mul_one]
    exact sqrt_two_ne_zero
  have := meromorphicOrderAt_comp_of_deriv_ne_zero (f := ℘[L]) hg hd
  rw [Function.comp_def] at this
  rw [this, L.order_weierstrassP _ hz]

theorem ellEval_indep (L : PeriodPair) (p : (weierstrassCurve L).toAffine.FunctionField[X])
    (hp : p ≠ 0) :
    (p.map (ellEval L).toRingHom).eval (germ fun z ↦ ℘[L] ((Real.sqrt 2 : ℂ) * z + 0)) ≠ 0 := by
  set t : ℂ := (Real.sqrt 2 : ℂ)
  set h : ℂ → ℂ := fun z ↦ ℘[L] (t * z + 0)
  have mh : Meromorphic h := meromorphic_weierstrassP_affine L t 0
  choose f hf hfe using fun i ↦ exists_isEllipticFunction_ellEval_eq L (p.coeff i)
  set n := p.natDegree
  have mt : ∀ i, Meromorphic fun z ↦ f i z * h z ^ i := fun i x ↦
    ((hf i).1 x).mul ((mh x).pow i)
  have heval : (p.map (ellEval L).toRingHom).eval (germ h) =
      germ fun z ↦ ∑ i ∈ Finset.range (n + 1), f i z * h z ^ i := by
    rw [eval_eq_sum_range, natDegree_map_eq_of_injective (ellEval_injective L),
      germ_sum _ mt]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [coeff_map, show (fun z ↦ f i z * h z ^ i) = f i * h ^ i from rfl,
      germ_mul (hf i).1 (mh.pow (n := i)), germ_pow mh]
    congr 1
    exact hfe i
  intro h0
  rw [heval, germ_eq_zero_iff (fun x ↦ meromorphicAt_fun_sum _ fun i ↦ mt i x)] at h0

  have hfn : ¬ f n =ᶠ[codiscrete ℂ] 0 := by
    intro hz
    have h1 : ellEval L (p.coeff n) = 0 := by
      rw [hfe n, ← germ_zero]
      exact germ_congr (hf n).1 hz
    rw [map_eq_zero_iff _ (ellEval_injective L)] at h1
    exact hp (leadingCoeff_eq_zero.1 h1)

  set bad : Set ℂ := (⋃ i ∈ Finset.range (n + 1), singularSet (f i)) ∪ singularSet (f n)⁻¹
  have hbad : (Torus.mk L '' bad).Finite := by
    rw [image_union, image_iUnion₂]
    refine Finite.union (Finite.biUnion (Finset.finite_toSet _) fun i _ ↦
      finite_image_singularSet L (hf i).1 (hf i).2) ?_
    exact finite_image_singularSet L (hf n).1.inv fun z l hl ↦ by
      simp only [Pi.inv_apply, (hf n).2 z l hl]
  obtain ⟨m, hm⟩ := (hbad.preimage (injective_mk_div_sqrt_two L).injOn).infinite_compl.nonempty
  set z₀ : ℂ := (m : ℂ) * L.ω₁ / t
  have hz₀ : z₀ ∉ bad := fun hb ↦ hm ⟨z₀, hb, rfl⟩
  have hpole : t * z₀ + 0 ∈ L.lattice := by
    have : t * z₀ + 0 = (m : ℤ) • L.ω₁ := by
      simp only [z₀, t, add_zero, zsmul_eq_mul, Int.cast_natCast]
      field_simp [sqrt_two_ne_zero]
    rw [this]
    exact L.lattice.smul_mem (m : ℤ) L.ω₁_mem_lattice
  have han : ∀ i ∈ Finset.range (n + 1), AnalyticAt ℂ (f i) z₀ := fun i hi ↦ by
    by_contra hna
    exact hz₀ (Or.inl (mem_iUnion₂.2 ⟨i, hi, hna⟩))
  have haninv : AnalyticAt ℂ (f n)⁻¹ z₀ := by
    by_contra hna
    exact hz₀ (Or.inr hna)
  have hoh : meromorphicOrderAt h z₀ = -2 := meromorphicOrderAt_weierstrassP_sqrt_two L hpole
  have hon : meromorphicOrderAt (f n) z₀ = 0 := by
    have h1 := (han n (Finset.self_mem_range_succ n)).meromorphicOrderAt_nonneg
    have h2 := haninv.meromorphicOrderAt_nonneg
    rw [meromorphicOrderAt_inv] at h2
    have hne : meromorphicOrderAt (f n) z₀ ≠ ⊤ := fun ht ↦
      hfn (eventuallyEq_zero_codiscrete_of_nhdsNE (hf n).1 (meromorphicOrderAt_eq_top_iff.1 ht))
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 hne
    rw [← hk] at h1 h2 ⊢
    have : (0 : ℤ) ≤ k := by exact_mod_cast h1
    have : (0 : ℤ) ≤ -k := by exact_mod_cast h2
    have : k = 0 := by omega
    rw [this]
    rfl
  have hterm : ∀ i, meromorphicOrderAt (fun z ↦ f i z * h z ^ i) z₀ =
      meromorphicOrderAt (f i) z₀ + ((i * (-2) : ℤ) : WithTop ℤ) := fun i ↦ by
    rw [show (fun z ↦ f i z * h z ^ i) = f i * h ^ i from rfl,
      meromorphicOrderAt_mul ((hf i).1 z₀) ((mh z₀).pow i), meromorphicOrderAt_pow (mh z₀), hoh]
    congr 1
  have htop : meromorphicOrderAt (fun z ↦ f n z * h z ^ n) z₀ = ((-2 * n : ℤ) : WithTop ℤ) := by
    rw [hterm, hon, zero_add]
    congr 1
    ring
  have hrest : ((-2 * n : ℤ) : WithTop ℤ) <
      meromorphicOrderAt (fun z ↦ ∑ i ∈ Finset.range n, f i z * h z ^ i) z₀ := by
    apply lt_meromorphicOrderAt_sum _ (fun i ↦ mt i z₀)
    intro i hi
    rw [hterm]
    have hi' : i < n := Finset.mem_range.1 hi
    have h0 := (han i (Finset.mem_range.2 (by omega))).meromorphicOrderAt_nonneg
    cases hc : meromorphicOrderAt (f i) z₀ with
    | top =>
      rw [top_add]
      exact WithTop.coe_lt_top _
    | coe k =>
      rw [hc] at h0
      have : (0 : ℤ) ≤ k := by exact_mod_cast h0
      rw [← WithTop.coe_add, WithTop.coe_lt_coe]
      omega
  have hsum : meromorphicOrderAt (fun z ↦ ∑ i ∈ Finset.range (n + 1), f i z * h z ^ i) z₀ =
      ((-2 * n : ℤ) : WithTop ℤ) := by
    have e : (fun z ↦ ∑ i ∈ Finset.range (n + 1), f i z * h z ^ i) =
        (fun z ↦ f n z * h z ^ n) + fun z ↦ ∑ i ∈ Finset.range n, f i z * h z ^ i := by
      funext z
      simp only [Finset.sum_range_succ, Pi.add_apply]
      ring
    rw [e, meromorphicOrderAt_add_eq_left_of_lt (meromorphicAt_fun_sum _ fun i ↦ mt i z₀)
      (htop ▸ hrest), htop]
  have hzero : meromorphicOrderAt (fun z ↦ ∑ i ∈ Finset.range (n + 1), f i z * h z ^ i) z₀ = ⊤ :=
    meromorphicOrderAt_eq_top_iff.2 (eventuallyEq_zero_codiscrete_iff.1 h0 z₀)
  rw [hsum] at hzero
  exact WithTop.coe_ne_top hzero

end Elliptic
end GroundTheory.Global
end
end

-- bundled from GroundTheory.GlobalFields.ComplexMultiplication.ReductionMap
section
namespace GroundTheory.Global

noncomputable section

open IsLocalRing GroundTheory.Arith.Abelian WeierstrassCurve.Affine

section PointMap

variable {F L : Type*} [Field F] [Field L] [DecidableEq F] [DecidableEq L] (f : F →+* L)
  (V : WeierstrassCurve F)

def pointMapRing : V.toAffine.Point →+ (V.map f).toAffine.Point :=
  letI := f.toAlgebra
  Point.map (W' := V) (Algebra.ofId F L)

theorem pointMapRing_some {x y : F} (h : V.toAffine.Nonsingular x y) :
    ∃ h' : (V.map f).toAffine.Nonsingular (f x) (f y),
      pointMapRing f V (.some x y h) = .some _ _ h' :=
  ⟨_, rfl⟩

end PointMap

section Functorial

variable {𝒪₁ 𝒪₂ : Type*} [CommRing 𝒪₁] [IsDomain 𝒪₁] [IsDiscreteValuationRing 𝒪₁]
  [CommRing 𝒪₂] [IsDomain 𝒪₂] [IsDiscreteValuationRing 𝒪₂]
  (K₁ K₂ : Type*) [Field K₁] [Field K₂] [Algebra 𝒪₁ K₁] [IsFractionRing 𝒪₁ K₁] [Algebra 𝒪₂ K₂]
  [IsFractionRing 𝒪₂ K₂] {f : 𝒪₁ →+* 𝒪₂} [IsLocalHom f] {σ : K₁ →+* K₂}
  (hσ : σ.comp (algebraMap 𝒪₁ K₁) = (algebraMap 𝒪₂ K₂).comp f) (W : WeierstrassCurve 𝒪₁)

include hσ in
theorem map_curveK_eq :
    (W.map (algebraMap 𝒪₁ K₁)).map σ = (W.map f).map (algebraMap 𝒪₂ K₂) := by
  rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map, hσ]

theorem map_curveRed_eq :
    (W.map (residue 𝒪₁)).map (ResidueField.map f) = (W.map f).map (residue 𝒪₂) := by
  rw [WeierstrassCurve.map_map, WeierstrassCurve.map_map, ResidueField.map_comp_residue]


include hσ in
theorem map_notMem_range {X : K₁} (hX : X ∉ Set.range (algebraMap 𝒪₁ K₁)) :
    σ X ∉ Set.range (algebraMap 𝒪₂ K₂) := by
  rintro ⟨s, hs⟩
  obtain ⟨t, htm, ht⟩ := exists_inv_mem_of_notMem_range K₁ hX
  have hX0 : X ≠ 0 := fun h => hX ⟨0, by rw [h, map_zero]⟩
  have h1 : algebraMap 𝒪₂ K₂ (s * f t) = 1 := by
    rw [map_mul, hs, ← RingHom.comp_apply, ← hσ, RingHom.comp_apply, ht, ← map_mul,
      mul_inv_cancel₀ hX0, map_one]
  have hu : IsUnit (f t) := isUnit_iff_exists_inv.mpr ⟨s,
    IsFractionRing.injective 𝒪₂ K₂ (by rw [mul_comm, h1, map_one])⟩
  exact (mem_maximalIdeal _).1 htm (isUnit_of_map_unit f t hu)

variable [W.IsElliptic] [DecidableEq K₁] [DecidableEq K₂] [DecidableEq (ResidueField 𝒪₁)]
  [DecidableEq (ResidueField 𝒪₂)]

theorem reducePoint_pointMapRing (P : (curveK K₁ W).Point) :
    reducePoint K₂ (W.map f) (pointCongr (map_curveK_eq K₁ K₂ hσ W)
        (pointMapRing σ (W.map (algebraMap 𝒪₁ K₁)) P)) =
      pointCongr (map_curveRed_eq W)
        (pointMapRing (ResidueField.map f) (W.map (residue 𝒪₁)) (reducePoint K₁ W P)) := by
  rcases point_cases K₁ W P with rfl | ⟨X, Y, h, rfl, hX⟩ | ⟨x, y, h, rfl⟩
  · rw [reducePoint_zero, map_zero, map_zero, map_zero, map_zero, reducePoint_zero]
  · obtain ⟨h', e⟩ := pointMapRing_some σ (W.map (algebraMap 𝒪₁ K₁)) h
    rw [e, pointCongr_some, reducePoint_some_notMem K₂ (W.map f) _ (map_notMem_range K₁ K₂ hσ hX),
      reducePoint_some_notMem K₁ W h hX, map_zero, map_zero]
  · obtain ⟨h', e⟩ := pointMapRing_some σ (W.map (algebraMap 𝒪₁ K₁)) h
    have hx : σ (algebraMap 𝒪₁ K₁ x) = algebraMap 𝒪₂ K₂ (f x) := by
      rw [← RingHom.comp_apply, hσ, RingHom.comp_apply]
    have hy : σ (algebraMap 𝒪₁ K₁ y) = algebraMap 𝒪₂ K₂ (f y) := by
      rw [← RingHom.comp_apply, hσ, RingHom.comp_apply]
    have h₂ : (curveK K₂ (W.map f)).Nonsingular (algebraMap 𝒪₂ K₂ (f x))
        (algebraMap 𝒪₂ K₂ (f y)) := by
      have := (map_curveK_eq K₁ K₂ hσ W) ▸ h'
      rwa [hx, hy] at this
    have n₁ := nonsingular_residue_of_isElliptic K₁ W h.1
    have n₂ := nonsingular_residue_of_isElliptic K₂ (W.map f) h₂.1
    obtain ⟨n₁', e₁⟩ := pointMapRing_some (ResidueField.map f) (W.map (residue 𝒪₁)) n₁
    have e₂ : pointCongr (map_curveK_eq K₁ K₂ hσ W) (.some _ _ h') = .some _ _ h₂ := by
      rw [pointCongr_some, Point.some.injEq]
      exact ⟨hx, hy⟩
    rw [e, e₂, reducePoint_some_integral K₂ (W.map f) h₂ n₂, reducePoint_some_integral K₁ W h n₁,
      e₁, pointCongr_some, Point.some.injEq, ResidueField.map_residue, ResidueField.map_residue]
    exact ⟨rfl, rfl⟩

end Functorial

section FF

variable {𝒪 : Type*} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
  (K : Type*) [Field K] [Algebra 𝒪 K] [IsFractionRing 𝒪 K] (W W' : WeierstrassCurve 𝒪)

abbrev gaussCurve : WeierstrassCurve (gaussRing W) := W'.map (algebraMap 𝒪 (gaussRing W))

theorem gaussCurve_map_functionField :
    (gaussCurve W W').map (algebraMap (gaussRing W) (W.baseChange K).toAffine.FunctionField) =
      (W'.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField := by
  show W'.map ((algebraMap (gaussRing W) _).comp (algebraMap 𝒪 (gaussRing W))) =
    W'.map ((algebraMap K _).comp (algebraMap 𝒪 K))
  rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]

theorem gaussCurve_map_residue :
    ((gaussCurve W W').map (residue (gaussRing W))).map (gaussResidue W) =
      (W'.map (residue 𝒪)).baseChange (W.map (residue 𝒪)).toAffine.FunctionField := by
  simp only [gaussCurve, WeierstrassCurve.baseChange, WeierstrassCurve.map_map]
  congr 1
  ext c
  simp [gaussResidue_residue_algebraMap]

variable [W'.IsElliptic]

def reduceFF : ((W'.baseChange K).baseChange (W.baseChange K).toAffine.FunctionField).toAffine.Point →+
    ((W'.map (residue 𝒪)).baseChange (W.map (residue 𝒪)).toAffine.FunctionField).toAffine.Point :=
  haveI : DecidableEq (ResidueField (gaussRing W)) := Classical.decEq _
  (pointCongr (gaussCurve_map_residue W W')).toAddMonoidHom.comp
    ((pointMapRing (gaussResidue W) _).comp
      ((reductionHom (W.baseChange K).toAffine.FunctionField (gaussCurve W W')).comp
        (pointCongr (gaussCurve_map_functionField K W W').symm).toAddMonoidHom))

end FF

end

end GroundTheory.Global
end

