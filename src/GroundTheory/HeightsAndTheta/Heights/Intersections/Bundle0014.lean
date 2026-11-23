module

public import Mathlib
public import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemDivSuppOfDivCycleNeZero
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0012

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.JacMinorC
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial

theorem pderiv_facts_charZero {F : Type*} [Field F] [CharZero F] {σ : Type*} (p : MvPolynomial σ F) (j : σ) (hj : 0 < degreeOf j p) :
    pderiv j p ≠ 0 ∧ degreeOf j (pderiv j p) < degreeOf j p ∧
      (pderiv j p).vars ⊆ p.vars := by
  classical
  have hsupp : ∀ m ∈ (pderiv j p).support, m + Finsupp.single j 1 ∈ p.support := by
    intro m hm
    rw [mem_support_iff, coeff_pderiv] at hm
    rw [mem_support_iff]
    exact left_ne_zero_of_mul hm
  refine ⟨?_, ?_, ?_⟩
  · have : ¬ degreeOf j p < 1 := by omega
    rw [degreeOf_lt_iff one_pos] at this
    push_neg at this
    obtain ⟨m, hm, hmj⟩ := this
    have hle : Finsupp.single j 1 ≤ m := Finsupp.single_le_iff.mpr hmj
    intro h0
    have hc := congr_arg (AddMonoidAlgebra.coeff · (m - Finsupp.single j 1)) h0
    rw [coeff_pderiv, tsub_add_cancel_of_le hle, AddMonoidAlgebra.coeff_zero] at hc
    rw [mem_support_iff] at hm
    exact mul_ne_zero hm (Nat.cast_add_one_ne_zero _) hc
  · rw [degreeOf_lt_iff hj]
    intro m hm
    have := monomial_le_degreeOf j (hsupp m hm)
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at this
    omega
  · intro i hi
    rw [MvPolynomial.mem_vars_iff_mem_support] at hi ⊢
    obtain ⟨m, hm, him⟩ := hi
    refine ⟨m + Finsupp.single j 1, hsupp m hm, ?_⟩
    rw [Finsupp.mem_support_iff] at him ⊢
    simp only [Finsupp.add_apply]
    omega

theorem exists_jacobian_minor_not_mem_charZero {F : Type} [Field F] [CharZero F] {σ : Type} [Fintype σ]
    (𝔭 : Ideal (MvPolynomial σ F)) [𝔭.IsPrime] {t : ℕ}
    (G : Fin t → MvPolynomial σ F) (hG : Ideal.span (Set.range G) = 𝔭) (d : ℕ)
    (hd : ringKrullDim (MvPolynomial σ F ⧸ 𝔭) = d) :
    ∃ (a : Fin (Fintype.card σ - d) → Fin t) (b : Fin (Fintype.card σ - d) → σ),
      Matrix.det (Matrix.of fun i j => pderiv (b j) (G (a i))) ∉ 𝔭 := by
  classical
  let A := MvPolynomial σ F ⧸ 𝔭
  haveI : IsDomain A := Ideal.Quotient.isDomain 𝔭
  let K := FractionRing A
  let π : MvPolynomial σ F →+* K := (algebraMap A K).comp (Ideal.Quotient.mk 𝔭)
  have hπ : ∀ f, π f = 0 ↔ f ∈ 𝔭 := by
    intro f
    simp only [π, RingHom.comp_apply]
    rw [IsFractionRing.to_map_eq_zero_iff (R := A) (K := K), Ideal.Quotient.eq_zero_iff_mem]
  let xb : σ → A := fun s => Ideal.Quotient.mk 𝔭 (X s)
  have hmk : Ideal.Quotient.mkₐ F 𝔭 = aeval xb := MvPolynomial.algHom_ext fun s => by
    rw [aeval_X, Ideal.Quotient.mkₐ_eq_mk]
  have hmk' : ∀ f, Ideal.Quotient.mk 𝔭 f = aeval xb f := fun f => by
    rw [← hmk, Ideal.Quotient.mkₐ_eq_mk]

  haveI : Algebra.FiniteType F A := inferInstance
  obtain ⟨s0, hs1, hs2⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := F) (A := A)
  have hs0 : s0 = d := by
    have : (s0 : WithBot ℕ∞) = (d : WithBot ℕ∞) := hs1.symm.trans hd
    exact_mod_cast this
  subst hs0

  haveI : FaithfulSMul F A :=
    (faithfulSMul_iff_algebraMap_injective F A).mpr (algebraMap F A).injective
  have hadj : Algebra.adjoin F (Set.range xb) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval, ← hmk]
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mkₐ_surjective F 𝔭 x
    exact ⟨y, rfl⟩
  haveI : Algebra.IsAlgebraic (Algebra.adjoin F (Set.range xb)) A := by
    constructor
    intro a
    have ha : a ∈ Algebra.adjoin F (Set.range xb) := by rw [hadj]; trivial
    exact isAlgebraic_algebraMap (R := Algebra.adjoin F (Set.range xb)) (A := A)
      (⟨a, ha⟩ : Algebra.adjoin F (Set.range xb))
  obtain ⟨u, hu, hub⟩ := exists_isTranscendenceBasis_subset (R := F) (Set.range xb)
  haveI : Finite u := ((Set.finite_range xb).subset hu).to_subtype
  haveI : Fintype u := Fintype.ofFinite u
  have hcardu : Fintype.card u = s0 := by
    have h1 := hub.cardinalMk_eq_trdeg
    rw [hs2, Cardinal.mk_fintype] at h1
    exact_mod_cast h1
  let g : u → σ := fun y => (hu y.2).choose
  have hg : ∀ y, xb (g y) = y := fun y => (hu y.2).choose_spec
  have hginj : Function.Injective g := by
    intro y y' h
    apply Subtype.ext
    rw [← hg y, ← hg y', h]

  have hind : ∀ Q : MvPolynomial σ F, (↑Q.vars : Set σ) ⊆ Set.range g → Q ∈ 𝔭 → Q = 0 := by
    intro Q hQ hQp
    obtain ⟨q, rfl⟩ := exists_rename_eq_of_vars_subset_range Q g hginj hQ
    have h0 : aeval ((↑) : u → A) q = 0 := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, hmk', aeval_rename] at hQp
      have hfun : ((↑) : u → A) = xb ∘ g := funext fun y => (hg y).symm
      rw [hfun]
      exact hQp
    rw [hub.1.eq_zero_of_aeval_eq_zero q h0, map_zero]

  have hrel : ∀ j, j ∉ Set.range g → ∃ Q : MvPolynomial σ F,
      Q ∈ 𝔭 ∧ Q ≠ 0 ∧ (↑Q.vars : Set σ) ⊆ insert j (Set.range g) := by
    intro j hj
    let w : Option u → A := fun o => o.elim (xb j) ((↑) : u → A)
    have hw : ¬ AlgebraicIndependent F w := by
      intro h
      rw [AlgebraicIndependent.option_iff] at h
      exact h.2 (hub.isAlgebraic.isAlgebraic (xb j))
    rw [algebraicIndependent_iff] at hw
    push_neg at hw
    obtain ⟨p, hp0, hp⟩ := hw
    let h : Option u → σ := fun o => o.elim j g
    have hinj : Function.Injective h := by
      rintro (_ | y) (_ | y') hyy
      · rfl
      · exact absurd ⟨y', hyy.symm⟩ hj
      · exact absurd ⟨y, hyy⟩ hj
      · exact congr_arg some (hginj hyy)
    refine ⟨rename h p, ?_, ?_, ?_⟩
    · rw [← Ideal.Quotient.eq_zero_iff_mem, hmk', aeval_rename]
      have hfun : xb ∘ h = w := by
        funext o
        cases o with
        | none => rfl
        | some y => exact hg y
      rw [hfun]
      exact hp0
    · exact fun h0 => hp ((rename_injective h hinj) (h0.trans (map_zero _).symm))
    · intro i hi
      have := vars_rename h p (Finset.mem_coe.mp hi)
      obtain ⟨o, -, rfl⟩ := Finset.mem_image.mp this
      cases o with
      | none => exact Set.mem_insert _ _
      | some y => exact Set.mem_insert_of_mem _ ⟨y, rfl⟩

  have hT : Fintype.card {j // j ∉ Set.range g} = Fintype.card σ - s0 := by
    rw [Fintype.card_subtype_compl, ← hcardu]
    congr 1
    rw [← Set.card_range_of_injective hginj]
  let e : {j // j ∉ Set.range g} ≃ Fin (Fintype.card σ - s0) := Fintype.equivFinOfCardEq hT
  let b : Fin (Fintype.card σ - s0) → σ := fun k => (e.symm k).1
  have hb : ∀ k, b k ∉ Set.range g := fun k => (e.symm k).2
  have hbinj : Function.Injective b := fun k k' h => e.symm.injective (Subtype.ext h)
  let M : Matrix (Fin t) (Fin (Fintype.card σ - s0)) K := Matrix.of fun i k => π (pderiv (b k) (G i))
  have hM : ∀ c, M.mulVec c = 0 → c = 0 := by
    intro c hc
    let D : MvPolynomial σ F → K := fun f => ∑ k, π (pderiv (b k) f) * c k
    have hDG : ∀ i, D (G i) = 0 := fun i => by
      have := congr_fun hc i
      simpa [Matrix.mulVec, dotProduct, M, D] using this
    have hDp : ∀ f ∈ 𝔭, D f = 0 := by
      intro f hf
      rw [← hG] at hf
      induction hf using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact hDG i
      | zero => simp [D]
      | add x y _ _ hx hy =>
        have : D (x + y) = D x + D y := by
          simp only [D, map_add (f := _), add_mul, Finset.sum_add_distrib]
        rw [this, hx, hy, add_zero]
      | smul a x hx' hx =>
        have hx0 : π x = 0 := (hπ x).2 (hG ▸ hx')
        have : D (a • x) = π a * D x := by
          simp only [D, smul_eq_mul, Derivation.leibniz, map_add (f := _), map_mul, hx0, zero_mul,
            add_zero, Finset.mul_sum, mul_assoc]
        rw [this, hx, mul_zero]
    funext k0
    let j := b k0
    have hj : j ∉ Set.range g := hb k0
    have hex : ∃ n, ∃ Q : MvPolynomial σ F, Q ∈ 𝔭 ∧ Q ≠ 0 ∧
        (↑Q.vars : Set σ) ⊆ insert j (Set.range g) ∧ degreeOf j Q = n := by
      obtain ⟨Q, h1, h2, h3⟩ := hrel j hj
      exact ⟨_, Q, h1, h2, h3, rfl⟩
    obtain ⟨Q, hQp, hQ0, hQv, hQd⟩ := Nat.find_spec hex
    have hmin : ∀ Q' : MvPolynomial σ F, Q' ∈ 𝔭 → Q' ≠ 0 →
        (↑Q'.vars : Set σ) ⊆ insert j (Set.range g) → degreeOf j Q ≤ degreeOf j Q' := by
      intro Q' h1 h2 h3
      rw [hQd]
      exact Nat.find_min' hex ⟨Q', h1, h2, h3, rfl⟩
    have hpos : 0 < degreeOf j Q := by
      by_contra h0
      push_neg at h0
      apply hQ0
      apply hind Q _ hQp
      intro i hi
      rcases hQv hi with rfl | hi'
      · exfalso
        rw [Finset.mem_coe, MvPolynomial.mem_vars_iff_mem_support] at hi
        obtain ⟨m, hm, him⟩ := hi
        have := monomial_le_degreeOf j hm
        rw [Finsupp.mem_support_iff] at him
        omega
      · exact hi'
    obtain ⟨hd0, hdlt, hdv⟩ := pderiv_facts_charZero Q j hpos
    have hnot : π (pderiv j Q) ≠ 0 := by
      rw [Ne, hπ]
      intro hmem
      have := hmin _ hmem hd0 (fun i hi => hQv (Finset.mem_coe.mpr (hdv (Finset.mem_coe.mp hi))))
      omega
    have hDQ : D Q = π (pderiv j Q) * c k0 := by
      simp only [D]
      rw [Finset.sum_eq_single k0]
      · intro k _ hk
        have : pderiv (b k) Q = 0 := by
          apply pderiv_eq_zero_of_notMem_vars
          intro hv
          rcases hQv (Finset.mem_coe.mpr hv) with h | h
          · exact hk (hbinj h)
          · exact hb k h
        rw [this, map_zero, zero_mul]
      · intro h; exact absurd (Finset.mem_univ k0) h
    have := hDp Q hQp
    rw [hDQ] at this
    simpa using (mul_eq_zero.mp this).resolve_left hnot
  obtain ⟨a, ha⟩ := ReciprocityTheory.AnForm.R.gs_exists_rows_det_ne_zero M hM
  refine ⟨a, b, fun hmem => ha ?_⟩
  have h1 := (hπ _).2 hmem
  rw [RingHom.map_det] at h1
  have hM' : M.submatrix a id = π.mapMatrix (Matrix.of fun i j => pderiv (b j) (G (a i))) := by
    ext i k
    rfl
  rw [hM']
  exact h1

section Minors

open ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {R : Type} [CommRing R]

end Minors

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.NotIsHorizontalOfDimOne
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

section Cycles

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem mem_of_mem_divSupp' {P W : Ideal (MRing ι)} {f : MRing ι} (hW : W ∈ divSupp P f) : f ∈ W :=
  hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))

theorem mem_divSupp_mul_left' {P W : Ideal (MRing ι)} (hP : P.IsPrime) {f g : MRing ι}
    (hgP : g ∉ P) (hW : W ∈ divSupp P f) : W ∈ divSupp P (f * g) := by
  refine ⟨⟨⟨hW.1.1.1, (sup_span_mul_le P f g).trans hW.1.1.2⟩, fun Q hQ hQW => ?_⟩, hW.2⟩
  have hfg : f * g ∈ Q := hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  rcases hQ.1.mem_or_mem hfg with hf | hg
  · exact hW.1.2 ⟨hQ.1, sup_le (le_sup_left.trans hQ.2) (Ideal.span_singleton_le_iff_mem _ |>.mpr hf)⟩
      hQW
  · exact (eq_of_le_of_mem_minimalPrimes hP hW.1 hQ.1 (le_sup_left.trans hQ.2) hg hgP hQW).ge

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem mem_divSupp_of_mul' {P W : Ideal (MRing ι)} {f g : MRing ι}
    (hW : W ∈ divSupp P (f * g)) (hf : f ∈ W) : W ∈ divSupp P f :=
  ⟨⟨⟨hW.1.1.1, sup_le (le_sup_left.trans hW.1.1.2) (Ideal.span_singleton_le_iff_mem _ |>.mpr hf)⟩,
    fun _ hQ hQW => hW.1.2 ⟨hQ.1, (sup_span_mul_le P f g).trans hQ.2⟩ hQW⟩, hW.2⟩

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem multAt_eq' (J W : Ideal (MRing ι)) (hW : W.IsPrime) :
    multAt J W = (locLen (MRing ι ⧸ J) ⟨W, hW⟩).toNat := by
  simp [multAt, hW, locLen]

theorem divCycle_mul' {P : Ideal (MRing ι)} (hP : P.IsPrime) {f g : MRing ι}
    (hf : f ∉ P) (hg : g ∉ P) : divCycle P (f * g) = divCycle P f + divCycle P g := by
  classical
  ext W
  simp only [Finsupp.add_apply, divCycle, Finsupp.ofSupportFinite_coe]
  by_cases h : W ∈ divSupp P (f * g)
  · have hWp := h.1.1.1
    have h' : W ∈ divSupp P (g * f) := by rwa [mul_comm]
    have key := locLen_mul hP hf g ⟨W, hWp⟩
    have hfin := locLen_ne_top h.1
    rw [key] at hfin
    rw [if_pos h, multAt_eq' _ _ hWp, key]
    by_cases hfW : f ∈ W <;> by_cases hgW : g ∈ W
    · rw [if_pos (mem_divSupp_of_mul' h hfW), if_pos (mem_divSupp_of_mul' h' hgW),
        multAt_eq' _ _ hWp, multAt_eq' _ _ hWp, ENat.toNat_add (WithTop.add_ne_top.mp hfin).1
          (WithTop.add_ne_top.mp hfin).2, add_comm]
    · rw [if_pos (mem_divSupp_of_mul' h hfW), if_neg fun h2 => hgW (mem_of_mem_divSupp' h2),
        multAt_eq' _ _ hWp, locLen_quot_eq_zero _ hgW, zero_add, add_zero]
    · rw [if_neg fun h2 => hfW (mem_of_mem_divSupp' h2), if_pos (mem_divSupp_of_mul' h' hgW),
        multAt_eq' _ _ hWp, locLen_quot_eq_zero (V := P) (g := f) _ hfW, add_zero, zero_add]
    · exact absurd (hWp.mem_or_mem (mem_of_mem_divSupp' h)) (by tauto)
  · rw [if_neg h, if_neg fun h2 => h (mem_divSupp_mul_left' hP hg h2),
      if_neg fun h2 => h (by rw [mul_comm]; exact mem_divSupp_mul_left' hP hf h2)]


open Classical in
def cycWeight (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) {n : ℕ}
    (L : Fin n → HermLine ι) (W : Ideal (MRing ι)) : ℝ :=
  if IsHorizontal W then I W n L else (geoNum n W (fun j => (L j).a) : ℝ) * Real.log (charOf W)

theorem cycR_eq_sum (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι))
    {n : ℕ} (L : Fin n → HermLine ι) (s : MRing ι) :
    cycR I P L s = (divCycle P s).sum fun W m => (m : ℝ) * cycWeight I L W := by
  classical
  unfold cycR
  rw [finsum_mem_def, finsum_eq_sum_of_support_subset _ (s := (divCycle P s).support)]
  · refine Finset.sum_congr rfl fun W _ => ?_
    by_cases h : W ∈ divSupp P s
    · simp [Set.indicator, h, divCycle, Finsupp.ofSupportFinite_coe, cycWeight]
    · simp [Set.indicator, h, divCycle, Finsupp.ofSupportFinite_coe]
  · intro W hW
    rw [Function.mem_support] at hW
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    intro h0
    apply hW
    by_cases h : W ∈ divSupp P s
    · have : multAt (P ⊔ Ideal.span {s}) W = 0 := by
        simpa [divCycle, Finsupp.ofSupportFinite_coe, h] using h0
      simp [Set.indicator, h, this]
    · simp [Set.indicator, h]

theorem cycR_mul (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) {P : Ideal (MRing ι)}
    (hP : P.IsPrime) {n : ℕ} (L : Fin n → HermLine ι) {s t : MRing ι} (hs : s ∉ P) (ht : t ∉ P) :
    cycR I P L (s * t) = cycR I P L s + cycR I P L t := by
  rw [cycR_eq_sum, cycR_eq_sum, cycR_eq_sum, divCycle_mul' hP hs ht]
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by push_cast; ring)

end Cycles

section NoHorizontal

theorem not_isHorizontal_of_dimOne (h0 : ArithVarZeroStatement) {P : Ideal (MRing ι)} {A : HermLine ι}
    {s : MRing ι} {W : Ideal (MRing ι)} (hP : IsArithVar P 1) (hs : IsSectionOn P A s)
    (hW : W ∈ divSupp P s) : ¬ IsHorizontal W := fun hh =>
  h0 K ι W ((divSuppArith K ι P 0 A s W hP hs hW).1 hh)

theorem eval_ne_zero_of_dimOne (h0 : ArithVarZeroStatement) {P : Ideal (MRing ι)} {A : HermLine ι}
    {s : MRing ι} (hP : IsArithVar P 1) (hs : IsSectionOn P A s) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts P) : eval z (map (Int.castRingHom ℂ) s) ≠ 0 := by
  intro hzero
  let φ : MRing ι →+* ℂ := (eval z).comp (map (Int.castRingHom ℂ))
  have hQ : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hle : P ⊔ Ideal.span {s} ≤ RingHom.ker φ := by
    refine sup_le (fun f hf => ?_) ?_
    · rw [RingHom.mem_ker]
      exact hz.2 f hf
    · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
      exact hzero
  obtain ⟨W, hW, hWQ⟩ := Ideal.exists_minimalPrimes_le hle
  have hrel : IsRelevant W := fun k => by
    obtain ⟨i, hi⟩ := hz.1 k
    refine ⟨i, fun hX => hi ?_⟩
    have h1 := hWQ hX
    rw [RingHom.mem_ker] at h1
    simpa [φ] using h1
  have hhor : IsHorizontal W := by
    unfold IsHorizontal
    refine eq_bot_iff.mpr fun n hn => ?_
    rw [Ideal.mem_comap] at hn
    have h1 := hWQ hn
    rw [RingHom.mem_ker] at h1
    simp [φ] at h1
    simp [h1]
  exact not_isHorizontal_of_dimOne h0 hP hs ⟨hW, hrel⟩ hhor

end NoHorizontal

section Integral

theorem ptsIntegral_add_of_dimOne (hFF : FibreFiniteStatement) {P : Ideal (MRing ι)}
    (hP : IsArithVar P 1) (φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) {g g₁ g₂ : ((Σ k, ι k) → ℂ) → ℝ}
    (h : ∀ z ∈ mcPts P, g z = g₁ z + g₂ z) :
    ptsIntegral P φ g = ptsIntegral P φ g₁ + ptsIntegral P φ g₂ := by
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    rw [MeasureTheory.integral_unique, MeasureTheory.integral_unique, MeasureTheory.integral_unique,
      ← smul_add]
    congr 1
    have hfin : ∀ y, (fibre P hΨ.choose y).Finite := hFF K ι P 0 hΨ.choose hP hΨ.choose_spec
    refine Eq.trans ?_ (finsum_mem_add_distrib' ((hfin _).subset Set.inter_subset_left)
      ((hfin _).subset Set.inter_subset_left))
    refine finsum_mem_congr rfl fun w _ => ?_
    unfold sheetDensity
    split_ifs with hγ
    · have hz : ∀ y : Fin 0 → ℂ, hγ.choose y ∈ mcPts P := fun y =>
        (Subsingleton.elim _ y) ▸ hγ.choose_spec.2.self_of_nhds.2.1
      rw [h _ (hz _), add_mul]
    · simp
  · simp

end Integral

theorem SpecIntHeightFormula.proof (h0 : ArithVarZeroStatement) : SpecIntHeightFormula.Statement := by
  intro K _ ι _ I P A s hP _ hs
  rw [recR_eq]
  congr 1
  unfold cycR vertR
  refine finsum_mem_congr rfl fun W hW => ?_
  simp [not_isHorizontal_of_dimOne h0 hP hs hW]

theorem cycR_eq_vertR_of_dimOne (h0 : ArithVarZeroStatement) (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
    {P : Ideal (MRing ι)} {A : HermLine ι} {s : MRing ι} (hP : IsArithVar P 1) (hs : IsSectionOn P A s) :
    cycR I P (Fin.elim0 : Fin 0 → HermLine ι) s = vertR P (Fin.elim0 : Fin 0 → HermLine ι) s := by
  unfold cycR vertR
  refine finsum_mem_congr rfl fun W hW => ?_
  simp [not_isHorizontal_of_dimOne h0 hP hs hW]

theorem RegularityIndependence.proof (h0 : ArithVarZeroStatement) (hFF : FibreFiniteStatement)
    (hPF : RegularityProductFormula.Statement) : RegularityIndependence.Statement := by
  intro K _ ι _ I P A s t hP hs ht
  obtain ⟨a, ha, hsa, hsP⟩ := id hs
  obtain ⟨b, hb, htb, htP⟩ := id ht
  have hab : b = a := funext fun k => by exact_mod_cast (hb k).symm.trans (ha k)
  subst hab
  have hφ : (fun (j : Fin 0) (z : (Σ k, ι k) → ℂ) => Real.log (((Fin.elim0 : Fin 0 → HermLine ι) j).h z)) =
      (Fin.elim0 : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) := funext fun j => j.elim0
  have hsplit : arInt P s A (Fin.elim0 : Fin 0 → HermLine ι) =
      ptsIntegral P (Fin.elim0 : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ)
        (fun z => Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ / ‖eval z (map (Int.castRingHom ℂ) t)‖)) +
      arInt P t A (Fin.elim0 : Fin 0 → HermLine ι) := by
    unfold arInt
    rw [hφ]
    refine ptsIntegral_add_of_dimOne hFF hP _ fun z hz => ?_
    have hs0 := norm_ne_zero_iff.mpr (eval_ne_zero_of_dimOne h0 hP hs hz)
    have ht0 := norm_ne_zero_iff.mpr (eval_ne_zero_of_dimOne h0 hP ht hz)
    have hA := (A.pos z hz.1).ne'
    unfold logNorm
    rw [← Real.log_mul (div_ne_zero hs0 ht0) (div_ne_zero ht0 hA)]
    congr 1
    field_simp
  have hpf := hPF K ι P s t b hP hsa htb hsP htP
  rw [recR_eq, recR_eq, cycR_eq_vertR_of_dimOne h0 I hP hs, cycR_eq_vertR_of_dimOne h0 I hP ht, hsplit]
  linarith

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StHorizNotMem
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def HorizNotMem.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ)
    (s s' : MRing ι) (W : Ideal (MRing ι)),
    IsArithVar P d → s ∉ P → s' ∉ P →
    (∀ W, W ∈ divSupp P s → W ∈ divSupp P s' → ¬ IsHorizontal W) →
    W ∈ divSupp P s → IsHorizontal W → s' ∉ W

end GroundTheory.Heights₂.Heights.Inter
end
end

