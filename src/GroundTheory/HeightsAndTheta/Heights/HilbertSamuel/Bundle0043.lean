module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0034
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0013
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0035
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0038

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PAnResNullForm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory Filter Topology Set

noncomputable section

namespace AnResNullForm

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem sameOrbit_trans_nf {a b c : (Σ k, ι k) → ℂ} (h1 : SameOrbit a b) (h2 : SameOrbit b c) :
    SameOrbit a c := by
  obtain ⟨c1, hc1, rfl⟩ := h1
  obtain ⟨c2, hc2, rfl⟩ := h2
  exact ⟨fun k => c1 k * c2 k, fun k => mul_ne_zero (hc1 k) (hc2 k), by funext q; simp [mul_assoc]⟩

theorem sameOrbit_symm_nf {a b : (Σ k, ι k) → ℂ} (h : SameOrbit a b) : SameOrbit b a := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext q
  simp [← mul_assoc, inv_mul_cancel₀ (hc q.1)]

theorem isClosed_blockProportional :
    IsClosed {q : ((Σ k, ι k) → ℂ) × ((Σ k, ι k) → ℂ) |
      ∀ k (i i' : ι k), q.1 ⟨k, i⟩ * q.2 ⟨k, i'⟩ = q.1 ⟨k, i'⟩ * q.2 ⟨k, i⟩} := by
  simp only [ofPred_forall]
  refine isClosed_iInter fun k => isClosed_iInter fun i => isClosed_iInter fun i' => isClosed_eq ?_ ?_ <;>
    fun_prop

theorem blockProportional_of_sameOrbit {a b : (Σ k, ι k) → ℂ} (h : SameOrbit a b) :
    ∀ k (i i' : ι k), a ⟨k, i⟩ * b ⟨k, i'⟩ = a ⟨k, i'⟩ * b ⟨k, i⟩ := by
  obtain ⟨c, -, rfl⟩ := h
  intro k i i'
  ring

theorem sameOrbit_of_blockProportional {a b : (Σ k, ι k) → ℂ} (ha : ∀ k, ∃ i, a ⟨k, i⟩ ≠ 0)
    (hb : ∀ k, ∃ i, b ⟨k, i⟩ ≠ 0) (h : ∀ k (i i' : ι k), a ⟨k, i⟩ * b ⟨k, i'⟩ = a ⟨k, i'⟩ * b ⟨k, i⟩) :
    SameOrbit a b := by
  choose p hp using hb
  refine ⟨fun k => a ⟨k, p k⟩ / b ⟨k, p k⟩, fun k => ?_, ?_⟩
  · intro h0
    obtain ⟨i, hi⟩ := ha k
    have h1 := h k i (p k)
    rcases div_eq_zero_iff.1 h0 with h0 | h0
    · rw [h0, zero_mul] at h1
      exact hi ((mul_eq_zero_iff_right (hp k)).1 h1)
    · exact hp k h0
  · funext ⟨k, i⟩
    show a ⟨k, i⟩ = a ⟨k, p k⟩ / b ⟨k, p k⟩ * b ⟨k, i⟩
    rw [div_mul_eq_mul_div, eq_div_iff (hp k)]
    exact h k i (p k)

theorem eval_eq_zero_iff_of_sameOrbit {G : MRing ι} {dG : K → ℕ} (hG : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog G dG)
    {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    eval z (map (Int.castRingHom ℂ) G) = 0 ↔ eval z' (map (Int.castRingHom ℂ) G) = 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [eval_smul_of_isMultiHomog hG,
    mul_eq_zero_iff_left (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k))]

variable {P J : Ideal (MRing ι)} {e : ℕ}

theorem continuousAt_lift (R : AnRes P J e) (x y : R.X) (hy : y ∈ R.U x) : ContinuousAt (R.lift x) y := by
  obtain ⟨j, hj⟩ := R.A.cover y
  rw [continuousAt_pi]
  intro p
  have hya : R.A.chart j y ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
    ⟨(R.A.chart j).map_source hj, by simpa [(R.A.chart j).left_inv hj] using hy⟩
  have h1 : ContinuousAt ((fun y' => R.lift x y' p) ∘ (R.A.chart j).symm) (R.A.chart j y) :=
    (R.holo x p j _ hya).continuousAt
  have h2 := h1.comp ((R.A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(R.A.chart j).open_source.mem_nhds hj] with y' hy'
  simp [(R.A.chart j).left_inv hy']

theorem isAnalyticSubset (R : AnRes P J e) {G : MRing ι} {dG : K → ℕ} (hG : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog G dG) :
    R.A.IsAnalyticSubset {x | eval (R.lift x x) (map (Int.castRingHom ℂ) G) = 0} := by
  intro x
  refine ⟨R.U x, R.isOpen_U x, R.mem_U x, 1, fun _ y => eval (R.lift x y) (map (Int.castRingHom ℂ) G),
    fun _ j y hy => ?_, ?_⟩
  · exact analyticAt_eval_comp (F := fun y' => R.lift x ((R.A.chart j).symm y')) (fun p => R.holo x p j y hy) G
  · ext y
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨h0, hy⟩
      exact ⟨hy, fun _ => (eval_eq_zero_iff_of_sameOrbit hG (R.compat x y y ⟨hy, R.mem_U y⟩)).2 h0⟩
    · rintro ⟨hy, h0⟩
      exact ⟨(eval_eq_zero_iff_of_sameOrbit hG (R.compat x y y ⟨hy, R.mem_U y⟩)).1 (h0 0), hy⟩

theorem interior_eq_empty (hND : NonvanishingDense.Statement) (R : AnRes P J e) (hP : IsArithVar P (e + 1))
    {G : MRing ι} {dG : K → ℕ} (hG : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog G dG) (hGP : G ∉ P) :
    interior {x | eval (R.lift x x) (map (Int.castRingHom ℂ) G) = 0} = ∅ := by
  set S := {x | eval (R.lift x x) (map (Int.castRingHom ℂ) G) = 0} with hS
  by_contra hne
  obtain ⟨x0, hx0⟩ := nonempty_iff_ne_empty.2 hne

  obtain ⟨x, hxW, hxJ⟩ : ∃ x ∈ interior S, R.lift x x ∉ mcPts J := by
    by_contra! hall
    obtain ⟨j, hj⟩ := R.A.cover x0
    have hopen : IsOpen (R.A.chart j '' (interior S ∩ (R.A.chart j).source)) :=
      ((R.A.chart j).isOpen_image_iff_of_subset_source inter_subset_right).2
        (isOpen_interior.inter (R.A.chart j).open_source)
    have hpos : 0 < volume (R.A.chart j '' (interior S ∩ (R.A.chart j).source)) :=
      hopen.measure_pos volume ⟨R.A.chart j x0, x0, ⟨hx0, hj⟩, rfl⟩
    have hsub : R.A.chart j '' (interior S ∩ (R.A.chart j).source) ⊆
        (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | R.lift x x ∈ mcPts J} := by
      rintro _ ⟨y, ⟨hyW, hys⟩, rfl⟩
      exact ⟨(R.A.chart j).map_source hys, by simpa [(R.A.chart j).left_inv hys] using hall y hyW⟩
    exact hpos.ne' (measure_mono_null hsub (R.null j))
  set z := R.lift x x with hzdef
  have hzP : z ∈ mcPts P := R.mem x x (R.mem_U x)

  set C := {z' : (Σ k, ι k) → ℂ | ∀ f ∈ J, eval z' (map (Int.castRingHom ℂ) f) = 0} with hC
  have hCc : IsClosed C := by
    simp only [hC, ofPred_forall]
    exact isClosed_iInter fun f => isClosed_iInter fun _ => isClosed_eq (MvPolynomial.continuous_eval _)
      continuous_const
  have hzC : z ∉ C := fun h => hxJ ⟨hzP.1, h⟩
  set T := {z' | z' ∈ mcPts P ∧ eval z' (map (Int.castRingHom ℂ) G) ≠ 0} ∩ Cᶜ with hT
  have hzT : z ∈ closure T := by
    rw [mem_closure_iff_nhds]
    intro t ht
    obtain ⟨w, ⟨hwt, hwC⟩, hw⟩ :=
      mem_closure_iff_nhds.1 (hND K ι P (e + 1) G hP hGP hzP) (t ∩ Cᶜ)
        (inter_mem ht (hCc.isOpen_compl.mem_nhds hzC))
    exact ⟨w, hwt, hw, hwC⟩

  have hex : ∀ z', ∃ x', z' ∈ T → SameOrbit (R.lift x' x') z' := fun z' => by
    by_cases h : z' ∈ T
    · obtain ⟨x', hx'⟩ := R.surj z' h.1.1 (fun hJ => h.2 hJ.2)
      exact ⟨x', fun _ => hx'⟩
    · exact ⟨x, fun h' => absurd h' h⟩
  choose xc hxc using hex
  have hxcW : ∀ z' ∈ T, xc z' ∉ interior S := fun z' hz' hW =>
    hz'.1.2 ((eval_eq_zero_iff_of_sameOrbit hG (hxc z' hz')).1 (show xc z' ∈ S from interior_subset hW))
  have : NeBot (𝓝[T] z) := mem_closure_iff_nhdsWithin_neBot.1 hzT
  obtain ⟨x', hx'⟩ := exists_clusterPt_of_compactSpace (map xc (𝓝[T] z))

  have hprop : (R.lift x' x', z) ∈ {q : ((Σ k, ι k) → ℂ) × ((Σ k, ι k) → ℂ) |
      ∀ k (i i' : ι k), q.1 ⟨k, i⟩ * q.2 ⟨k, i'⟩ = q.1 ⟨k, i'⟩ * q.2 ⟨k, i⟩} := by
    refine isClosed_blockProportional.closure_subset (mem_closure_iff_nhds.2 fun t ht => ?_)
    obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 ht
    have hU : R.U x' ∩ R.lift x' ⁻¹' u ∈ 𝓝 x' :=
      inter_mem ((R.isOpen_U x').mem_nhds (R.mem_U x')) (continuousAt_lift R x' x' (R.mem_U x') hu)
    have hV : xc '' (v ∩ T) ∈ map xc (𝓝[T] z) :=
      mem_map.2 (mem_of_superset (inter_mem_nhdsWithin T hv) fun z' hz' => ⟨z', ⟨hz'.2, hz'.1⟩, rfl⟩)
    obtain ⟨_, ⟨hyU, hyu⟩, z', ⟨hz'v, hz'T⟩, rfl⟩ := clusterPt_iff_nonempty.1 hx' hU hV
    refine ⟨(R.lift x' (xc z'), z'), huv ⟨hyu, hz'v⟩, ?_⟩
    exact blockProportional_of_sameOrbit
      (sameOrbit_trans_nf (R.compat x' (xc z') (xc z') ⟨hyU, R.mem_U _⟩) (hxc z' hz'T))
  have horb : SameOrbit (R.lift x' x') z :=
    sameOrbit_of_blockProportional (R.mem x' x' (R.mem_U x')).1 hzP.1 hprop
  have hxx' : x = x' := R.inj x x' hxJ (sameOrbit_symm_nf horb)
  subst hxx'
  obtain ⟨_, hyW, z', hz'T, rfl⟩ :=
    clusterPt_iff_nonempty.1 hx' (isOpen_interior.mem_nhds hxW)
      (mem_map.2 (mem_of_superset self_mem_nhdsWithin fun z' hz' => ⟨z', hz', rfl⟩) :
        xc '' T ∈ map xc (𝓝[T] z))
  exact hxcW z' hz'T hyW

end AnResNullForm

theorem AnResNullForm.proof (hND : NonvanishingDense.Statement) : AnResNullForm.Statement := by
  intro e K _ ι _ P J R G dG hP hG hGP j
  have h := analyticNull R.A _ (AnResNullForm.isAnalyticSubset R hG)
    (AnResNullForm.interior_eq_empty hND R hP hG hGP) j
  refine measure_mono_null ?_ h
  rintro a ⟨ha, haS⟩
  exact ⟨(R.A.chart j).symm a, ⟨haS, (R.A.chart j).map_target ha⟩, (R.A.chart j).right_inv ha⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockGraphImage
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

theorem BlockGraphImage.proof : BlockGraphImage.Statement := by
  intro K _ ι _ Ω _ _ κ _ y k₀ M N x hB

  let φ : MRing ι ⧸ mCoordIdeal y →+* MvPolynomial K Ω :=
    Ideal.Quotient.lift (mCoordIdeal y) (mConeMap y).toRingHom fun a ha => RingHom.mem_ker.1 ha
  have hφ : Function.Injective φ := by
    refine (injective_iff_map_eq_zero φ).2 fun a ha => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact Ideal.Quotient.eq_zero_iff_mem.2 (RingHom.mem_ker.2 ha)

  let ψ : Polynomial Ω →+* MvPolynomial Unit (MvPolynomial K Ω) :=
    Polynomial.eval₂RingHom ((C : MvPolynomial K Ω →+* _).comp C) (C (X k₀) * X ())
  let ev : MvPolynomial Unit (MvPolynomial K Ω) →+* Polynomial Ω :=
    eval₂Hom (Polynomial.C.comp (MvPolynomial.eval fun _ => (1 : Ω))) fun _ => Polynomial.X
  have hev : ∀ p, ev (ψ p) = p := by
    have h : ev.comp ψ = RingHom.id _ := by
      apply Polynomial.ringHom_ext
      · intro c
        simp [ψ, ev]
      · simp [ψ, ev]
    exact fun p => RingHom.congr_fun h p

  have hcone : ∀ q, mConeMap y (blockForms k₀ M q) = C (x q) * X k₀ := by
    intro q
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [blockForms, map_sum, map_mul, mConeMap, aeval_X, aeval_C, hB.1 q, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_assoc]
  let G : MRing (GlobalTheory κ) →+* MvPolynomial Unit (MvPolynomial K Ω) :=
    (MvPolynomial.map φ).comp ((graphMap (mCoordIdeal y) (blockForms k₀ M)).comp
      (rename (inrV (ι := ι) (ι₂ := GlobalTheory κ)) : MRing (GlobalTheory κ) →ₐ[ℤ] _).toRingHom)
  have hG : ∀ f, G f = ψ (coneMap ℤ x f) := by
    have h : G = ψ.comp (coneMap ℤ x).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro n
        exact RingHom.congr_fun (RingHom.ext_int (G.comp C) ((ψ.comp (coneMap ℤ x).toRingHom).comp C)) n
      · rintro ⟨u, j⟩
        cases u
        simp only [G, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, rename_X]
        rw [show (inrV (ι := ι) (ι₂ := GlobalTheory κ) ⟨(), j⟩) = ⟨Sum.inr (), j⟩ from rfl]
        rw [graphMap, eval₂Hom_X']
        simp only [map_mul, map_C, map_X, coneMap, aeval_X]
        rw [show φ (Ideal.Quotient.mk (mCoordIdeal y) (blockForms k₀ M ⟨(), j⟩)) = C (x ⟨(), j⟩) * X k₀ from
          (Ideal.Quotient.lift_mk _ _ _).trans (hcone _)]
        simp [ψ, mul_assoc]
    exact fun f => RingHom.congr_fun h f
  ext f
  show rename inrV f ∈ RingHom.ker (graphMap (mCoordIdeal y) (blockForms k₀ M)) ↔ f ∈ RingHom.ker (coneMap ℤ x)
  rw [RingHom.mem_ker, RingHom.mem_ker]
  constructor
  · intro h
    have h0 : G f = 0 := by
      show MvPolynomial.map φ (graphMap (mCoordIdeal y) (blockForms k₀ M) (rename inrV f)) = 0
      rw [h, map_zero]
    rw [hG] at h0
    rw [← hev (coneMap ℤ x f), h0, map_zero]
  · intro h
    apply MvPolynomial.map_injective φ hφ
    rw [map_zero]
    show G f = 0
    rw [hG, h, map_zero]

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageArith
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace BlockImageArithmetic

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

theorem ringKrullDim_eq (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ringKrullDim (MRing ι ⧸ mCoordIdeal y) =
      (((Algebra.trdeg ℤ (CoordinateConeArithVar.ratioField y c)).toENat + Fintype.card K + 1 : ℕ∞) :
        WithBot ℕ∞) := by
  have hhor := CoordinateConeArithVar.horizontal y
  have : (mCoordIdeal y).IsPrime := RingHom.ker_isPrime _
  have htr := ConeTrdeg.proof K ι (CoordinateConeArithVar.ratioField y c)
    (CoordinateConeArithVar.ratioPtL y c) (CoordinateConeArithVar.birational y c hc)
    (fun k ↦ ⟨c k, fun h0 ↦ by
      have h1 := congrArg Subtype.val h0
      simp [CoordinateConeArithVar.ratioPtL, CoordinateConeArithVar.ratioPt, hc] at h1⟩)
    (by rw [CoordinateConeArithVar.mCoordIdeal_ratioPtL y c hc]; exact hhor)
  rw [CoordinateConeArithVar.mCoordIdeal_ratioPtL y c hc] at htr
  rw [IntDomainDim.proof (MRing ι ⧸ mCoordIdeal y)
    (CoordinateConeArithVar.algebraMap_injective _ hhor), htr]
  simp only [map_add (f := _), map_natCast]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem div_mem_of_sum (F : IntermediateField ℚ Ω) {A B : Type} [Fintype B] (u : A → Ω) (v : B → Ω)
    (L : Matrix A B ℤ) (hu : ∀ a, u a = ∑ b, (L a b : Ω) * v b) (b₀ : B)
    (hF : ∀ b, v b / v b₀ ∈ F) (a : A) : u a / v b₀ ∈ F := by
  rw [hu, Finset.sum_div]
  refine sum_mem fun b _ ↦ ?_
  rw [mul_div_assoc]
  exact mul_mem (intCast_mem F _) (hF b)


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem ratio_mem_of_sum (F : IntermediateField ℚ Ω) {A B : Type} [Fintype B] (u : A → Ω) (v : B → Ω)
    (L : Matrix A B ℤ) (hu : ∀ a, u a = ∑ b, (L a b : Ω) * v b) (b₀ : B) (hv : v b₀ ≠ 0)
    (hF : ∀ b, v b / v b₀ ∈ F) (a a' : A) : u a / u a' ∈ F := by
  rw [← div_div_div_cancel_right₀ hv (u a) (u a')]
  exact div_mem (div_mem_of_sum F u v L hu b₀ hF a) (div_mem_of_sum F u v L hu b₀ hF a')


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem aeval_mem (F : IntermediateField ℚ Ω) (w : (Σ k, ι k) → Ω) (hw : ∀ p, w p ∈ F) (f : MRing ι) :
    aeval w f ∈ F := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [aeval_C, algebraMap_int_eq, eq_intCast]; exact intCast_mem F a
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | mul_X p q hp => rw [map_mul, aeval_X]; exact mul_mem hp (hw q)


omit [Fintype K] [CharZero Ω] in
theorem isMultiHomog_X_single [DecidableEq K] (p : Σ k, ι k) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (X p : MRing ι) (fun k ↦ if k = p.1 then 1 else 0) := by
  intro m hm k
  rw [support_X, Finset.mem_singleton] at hm
  subst hm
  obtain ⟨k', i'⟩ := p
  by_cases h : k = k'
  · subst h
    rw [Finset.sum_eq_single i']
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · simp [h]


omit [CharZero Ω] in
theorem aeval_mul_pow_of_block (y w : (Σ k, ι k) → Ω) (k₀ : K) (z : Ω)
    (hw : ∀ i, w ⟨k₀, i⟩ * z = y ⟨k₀, i⟩) {f : MRing ι} {d : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f d)
    (hd : ∀ k, k ≠ k₀ → d k = 0) : aeval w f * z ^ d k₀ = aeval y f := by
  classical
  conv_rhs => rw [f.as_sum]
  conv_lhs => rw [f.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  rw [aeval_monomial, aeval_monomial, mul_assoc]
  congr 1
  have hsum : ∑ p, m p = d k₀ := by
    rw [Fintype.sum_sigma, Finset.sum_eq_single k₀]
    · exact hf m hm k₀
    · intro k _ hk
      rw [hf m hm k, hd k hk]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hzero : ∀ p : Σ k, ι k, p.1 ≠ k₀ → m p = 0 := by
    intro p hp
    have h1 := hf m hm p.1
    rw [hd _ hp] at h1
    exact (Finset.sum_eq_zero_iff.mp h1) p.2 (Finset.mem_univ _)
  rw [Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _), Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _),
    ← hsum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ ↦ ?_
  rw [← mul_pow]
  by_cases hp : p.1 = k₀
  · obtain ⟨k, i⟩ := p
    simp only at hp
    subst hp
    rw [hw i]
  · rw [hzero p hp, pow_zero, pow_zero]

end BlockImageArithmetic


open BlockImageArithmetic in
theorem BlockImageArith.proof : BlockImageArith.Statement := by
  intro D K _ _ ι _ Ω _ _ y k₀ r M N x hY hbir hB _
  classical
  obtain ⟨hK, ⟨_, _, hrel⟩, _, hdim⟩ := hY
  have hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨i, hi⟩ := hrel k
    refine ⟨i, fun h0 ↦ hi ?_⟩
    show mConeMap y (X ⟨k, i⟩) = 0
    simp [mConeMap, h0]
  choose c hc using hnz
  obtain ⟨j₀, hj₀⟩ : ∃ j, x j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    apply hc k₀
    rw [hB.2 (c k₀)]
    simp [h]
  let c' : ∀ k, GlobalTheory (Fin r) k := fun _ ↦ j₀.2
  have hc' : ∀ k, x ⟨k, c' k⟩ ≠ 0 := fun _ ↦ hj₀
  set Fy := CoordinateConeArithVar.ratioField y c with hFy
  set Fx := CoordinateConeArithVar.ratioField (ι := GlobalTheory (Fin r)) x c' with hFx
  have hxF : ∀ j, x j / x j₀ ∈ Fx := fun j ↦ IntermediateField.subset_adjoin _ _ ⟨j, rfl⟩
  have hLx : Fx ≤ Fy := by
    rw [hFx, IntermediateField.adjoin_le_iff]
    rintro _ ⟨p, rfl⟩
    exact ratio_mem_of_sum Fy x (fun i ↦ y ⟨k₀, i⟩) M hB.1 (c k₀) (hc k₀)
      (fun i ↦ IntermediateField.subset_adjoin _ _ ⟨⟨k₀, i⟩, rfl⟩) p ⟨p.1, c' p.1⟩
  have hLy : Fy ≤ Fx := by
    rw [hFy, IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨k, i⟩, rfl⟩
    show y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ Fx
    have hyF : ∀ i, y ⟨k₀, i⟩ / x j₀ ∈ Fx := fun i ↦
      div_mem_of_sum Fx (fun i ↦ y ⟨k₀, i⟩) x N hB.2 j₀ hxF i
    let w : (Σ k, ι k) → Ω := fun p ↦ if p.1 = k₀ then y p / x j₀ else 0
    have hwF : ∀ p, w p ∈ Fx := by
      rintro ⟨k', i'⟩
      by_cases h : k' = k₀
      · subst h
        simp only [w, ite_true]
        exact hyF i'
      · simp only [w, h, ite_false]
        exact zero_mem _
    have hw : ∀ i, w ⟨k₀, i⟩ * x j₀ = y ⟨k₀, i⟩ := fun i ↦ by
      simp only [w, ite_true]
      exact div_mul_cancel₀ _ hj₀
    obtain ⟨n, g', h', hg', hh', hh0, heq⟩ := hbir _ (X ⟨k, i⟩) (X ⟨k, c k⟩)
      (isMultiHomog_X_single ⟨k, i⟩) (isMultiHomog_X_single ⟨k, c k⟩)
      (by rw [aeval_X]; exact hc k)
    rw [aeval_X, aeval_X] at heq
    have hd : ∀ k', k' ≠ k₀ → blockDeg k₀ n k' = 0 := fun k' hk' ↦ by simp [blockDeg, hk']
    have e1 := aeval_mul_pow_of_block y w k₀ (x j₀) hw hg' hd
    have e2 := aeval_mul_pow_of_block y w k₀ (x j₀) hw hh' hd
    have hwh : aeval w h' ≠ 0 := fun h0 ↦ hh0 (by rw [← e2, h0, zero_mul])
    have hrat : y ⟨k, i⟩ / y ⟨k, c k⟩ = aeval w g' / aeval w h' := by
      rw [div_eq_div_iff (hc k) hwh]
      apply mul_right_cancel₀ (pow_ne_zero (blockDeg k₀ n k₀) hj₀)
      linear_combination heq + y ⟨k, i⟩ * e2 - y ⟨k, c k⟩ * e1
    rw [hrat]
    exact div_mem (aeval_mem Fx w hwF g') (aeval_mem Fx w hwF h')
  have hLeq : Fy = Fx := le_antisymm hLy hLx
  have hdy := ringKrullDim_eq y c hc
  rw [hdim] at hdy
  rw [coordIdeal_eq_mCoordIdeal]
  refine ⟨⟨()⟩, ⟨RingHom.ker_isPrime _, CoordinateConeArithVar.isMultiHomogIdeal x,
    CoordinateConeArithVar.relevant x c' hc'⟩, CoordinateConeArithVar.horizontal x, ?_⟩
  rw [ringKrullDim_eq x c' hc']
  rw [← hFy, hLeq] at hdy
  generalize (Algebra.trdeg ℤ Fx).toENat = t at hdy ⊢
  have h1 : ((D + 1 + Fintype.card K : ℕ) : ℕ∞) = t + Fintype.card K + 1 := by exact_mod_cast hdy
  induction t using ENat.recTopCoe with
  | top => simp at h1
  | coe t =>
    have h2 : D + 1 + Fintype.card K = t + Fintype.card K + 1 := by exact_mod_cast h1
    have h3 : t = D := by omega
    subst h3
    rw [Fintype.card_unit]
    norm_cast

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartLatRank
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ChartLatRank.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (a : K → ℤ) (n : ℕ),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
      Module.finrank ℤ (AddSubgroup.toIntSubmodule (chartLat y a n)) = Module.finrank ℚ (chartLatQ y a n)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

