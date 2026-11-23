module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

def IsMultilinFam (II : AllFam) : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι)) (n : ℕ) (L : Fin n → HermLine ι) (j : Fin n) (A B : HermLine ι),
    IsArithVar P n → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B →
    II K ι P n (Function.update L j (A.tensor B)) =
      II K ι P n (Function.update L j A) + II K ι P n (Function.update L j B)

def HasPFCoord (II : AllFam) : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k', ι' k') → Ω) (d : ℕ) (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι'),
    IsBlockMap κ v → IsArithVar (mCoordIdeal y) d → IsArithVar (imageZ v (mCoordIdeal y)) d →
    (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) →
    II K' ι' (mCoordIdeal y) d L' =
      (IntermediateField.relfinrank (blockFnField (y ∘ v)) (blockFnField y) : ℝ) *
        II K ι (imageZ v (mCoordIdeal y)) d L

def HasContractMixed (II : AllFam) : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d₀ d r : ℕ)
    (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι') (N : Fin r → HermLine ι'),
    IsBlockMap κ v → IsArithVar P' (d + r) → IsArithVar (imageZ v P') d₀ → d₀ < d →
    (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → (∀ j, IsSmoothHerm (N j)) →
    II K' ι' P' (d + r) (Fin.append L' N) = 0

def IsFullIntersectionSystem (II : IntersectionSystem) : Prop :=
  IsIntersectionSystem II ∧ IsMultilinFam II ∧ HasPFCoord II ∧ HasContractMixed II

def ArithIntersectionSystemStatement : Prop :=
  ∃ II : IntersectionSystem, IsFullIntersectionSystem II

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedB
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial ReciprocityTheory.AnForm.M Filter Topology

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)}
  {e : ℕ}

theorem continuousOn_lift (R : AnLogRes P J e) (x : R.X) (p : Σ k, ι k) :
    ContinuousOn (fun z => R.lift x z p) (R.U x) := by
  intro z hz
  obtain ⟨j, hj⟩ := R.A.cover z
  have ha : AnalyticAt ℂ ((fun w => R.lift x w p) ∘ (R.A.chart j).symm) (R.A.chart j z) :=
    R.holo x p j _ ⟨(R.A.chart j).map_source hj, by
      simp only [Set.mem_preimage, (R.A.chart j).left_inv hj]; exact hz⟩
  have hc : ContinuousAt (((fun w => R.lift x w p) ∘ (R.A.chart j).symm) ∘ (R.A.chart j)) z :=
    ha.continuousAt.comp ((R.A.chart j).continuousAt hj)
  refine (hc.congr ?_).continuousWithinAt
  filter_upwards [(R.A.chart j).open_source.mem_nhds hj] with w hw
  simp only [Function.comp_apply, (R.A.chart j).left_inv hw]

private theorem smoothOn_potOf_of_isSmoothHerm (R : AnLogRes P J e) {L : HermLine ι} (hL : IsSmoothHerm L)
    (x : R.X) : R.A.SmoothOn ((potOf R L).U x) ((potOf R L).φ x) := by
  intro j
  have hlift : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w => R.lift x ((R.A.chart j).symm w))
      ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) := by
    refine contDiffOn_pi.mpr fun p => ?_
    exact ((R.holo x p j).contDiffOn ((R.A.chart j).isOpen_inter_preimage_symm
      (R.isOpen_U x)).uniqueDiffOn).restrict_scalars ℝ
  have hcomp := (hL : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) L.h _).comp hlift (fun w hw => (R.mem x _ hw.2).1)
  exact hcomp.log fun w hw => (L.pos _ (R.mem x _ hw.2).1).ne'

private theorem exists_holo_re_eq_potOf_sub_on_overlap (R : AnLogRes P J e) (L : HermLine ι) (x x' y : R.X)
    (hy : y ∈ R.U x ∩ R.U x') : ∃ W : Set R.X, IsOpen W ∧ y ∈ W ∧ ∃ G : R.X → ℂ,
      R.A.HoloOn W G ∧ ∀ z ∈ W ∩ R.U x ∩ R.U x',
        (potOf R L).φ x z - (potOf R L).φ x' z = (G z).re := by
  classical
  obtain ⟨c, hc, hxy⟩ := R.compat x x' y hy
  choose i hi using (R.mem x' y hy.2).1
  have hVo : IsOpen (R.U x ∩ R.U x') := (R.isOpen_U x).inter (R.isOpen_U x')
  have hcx : ∀ p, ContinuousOn (fun z => R.lift x z p) (R.U x ∩ R.U x') := fun p =>
    (continuousOn_lift R x p).mono Set.inter_subset_left
  have hcx' : ∀ p, ContinuousOn (fun z => R.lift x' z p) (R.U x ∩ R.U x') := fun p =>
    (continuousOn_lift R x' p).mono Set.inter_subset_right
  let r : K → R.X → ℂ := fun k z => R.lift x z ⟨k, i k⟩ / R.lift x' z ⟨k, i k⟩ / c k
  let D : K → Set R.X := fun k => (R.U x ∩ R.U x') ∩ (fun z => R.lift x' z ⟨k, i k⟩) ⁻¹' {0}ᶜ
  have hD : ∀ k, IsOpen (D k) := fun k => (hcx' _).isOpen_inter_preimage hVo isOpen_compl_singleton
  have hr : ∀ k, ContinuousOn (r k) (D k) := fun k =>
    (((hcx _).mono Set.inter_subset_left).div ((hcx' _).mono Set.inter_subset_left)
      (fun z hz => hz.2)).div_const _
  let W : Set R.X := (R.U x ∩ R.U x') ∩ ⋂ k, (D k ∩ r k ⁻¹' Complex.slitPlane)
  have hW : IsOpen W :=
    hVo.inter (isOpen_iInter_of_finite fun k =>
      (hr k).isOpen_inter_preimage (hD k) Complex.isOpen_slitPlane)
  have hlk : ∀ k, R.lift x y ⟨k, i k⟩ = c k * R.lift x' y ⟨k, i k⟩ := fun k => congrFun hxy _
  have hyW : y ∈ W := by
    refine ⟨hy, Set.mem_iInter.mpr fun k => ⟨⟨hy, hi k⟩, ?_⟩⟩
    have : r k y = 1 := by
      simp only [r, hlk k]
      field_simp [hi k, hc k]
    simp only [Set.mem_preimage, this]
    exact Complex.one_mem_slitPlane
  refine ⟨W, hW, hyW, fun z => ∑ k, (L.a k : ℂ) * (Complex.log (r k z) + (Real.log ‖c k‖ : ℂ)),
    ?_, ?_⟩
  · intro j w hw
    have hzV : (R.A.chart j).symm w ∈ R.U x ∩ R.U x' := hw.2.1
    have hzk := fun k => Set.mem_iInter.mp hw.2.2 k
    have ha : ∀ p, AnalyticAt ℂ (fun w => R.lift x ((R.A.chart j).symm w) p) w := fun p =>
      R.holo x p j w ⟨hw.1, hzV.1⟩
    have ha' : ∀ p, AnalyticAt ℂ (fun w => R.lift x' ((R.A.chart j).symm w) p) w := fun p =>
      R.holo x' p j w ⟨hw.1, hzV.2⟩
    have hrk : ∀ k, AnalyticAt ℂ (fun w => r k ((R.A.chart j).symm w)) w := fun k =>
      ((ha _).div (ha' _) (hzk k).1.2).div analyticAt_const (hc k)
    show AnalyticAt ℂ (fun w => ∑ k, (L.a k : ℂ) *
      (Complex.log (r k ((R.A.chart j).symm w)) + (Real.log ‖c k‖ : ℂ))) w
    refine Finset.analyticAt_fun_sum (𝕜 := ℂ) Finset.univ fun k _ => ?_
    exact analyticAt_const.mul (((hrk k).clog (hzk k).2).add analyticAt_const)
  · rintro z ⟨⟨hzW, hzx⟩, hzx'⟩
    obtain ⟨c', hc', hz⟩ := R.compat x x' z ⟨hzx, hzx'⟩
    have hzk := fun k => Set.mem_iInter.mp hzW.2 k
    have h2 := L.pos _ (R.mem x' z hzx').1
    have hsm := L.smul c' (R.lift x' z) hc'
    rw [← hz] at hsm
    have hrz : ∀ k, r k z = c' k / c k := by
      intro k
      have hne : R.lift x' z ⟨k, i k⟩ ≠ 0 := (hzk k).1.2
      simp only [r, congrFun hz ⟨k, i k⟩]
      field_simp [hne, hc k]
    have hP : ∀ k ∈ Finset.univ, ‖c' k‖ ^ L.a k ≠ 0 := fun k _ =>
      zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc' k))
    simp only [potOf]
    rw [hsm, Real.log_mul (Finset.prod_ne_zero_iff.mpr hP) h2.ne', add_sub_cancel_right,
      Real.log_prod hP, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hrz k, Real.log_zpow]
    simp only [Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.add_re,
      Complex.log_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, zero_mul, sub_zero,
      norm_div, Real.log_div (norm_ne_zero_iff.mpr (hc' k)) (norm_ne_zero_iff.mpr (hc k))]
    ring

theorem isPotential_potOf (R : AnLogRes P J e) {L : HermLine ι} (hL : IsSmoothHerm L) :
    IsPotential R.A (potOf R L) :=
  ⟨smoothOn_potOf_of_isSmoothHerm R hL, fun x x' y hy => exists_holo_re_eq_potOf_sub_on_overlap R L x x' y hy⟩

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheet
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MeasureTheory Metric Filter Topology

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}

theorem isOpen_blockNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have h : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
    ext z
    simp
  rw [h]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem analyticAt_coord {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ}
    (h : AnalyticAt ℂ γ y) (p : Σ k, ι k) : AnalyticAt ℂ (fun y' => γ y' p) y :=
  analyticAt_pi_iff.mp h p

theorem pot_contDiffAt {L : HermLine ι} (hL : IsSmoothHerm L) {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ}
    {y : Fin e → ℂ} (hγ : AnalyticAt ℂ γ y) (hy : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0) :
    ContDiffAt ℝ 2 (fun y' => Real.log (L.h (γ y'))) y := by
  have hh : ContDiffAt ℝ 2 L.h (γ y) :=
    (hL.contDiffAt (isOpen_blockNonzero.mem_nhds hy)).of_le (WithTop.coe_le_coe.mpr le_top)
  have hγr : ContDiffAt ℝ 2 γ y := (hγ.contDiffAt (n := 2)).restrict_scalars ℝ
  exact (hh.comp y hγr).log (L.pos _ hy).ne'

theorem density_eq {L : Fin e → HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) {A : HermLine ι}
    {s : MRing ι} {P : Ideal (MRing ι)} (hs : IsSectionOn P A s)
    {γ γ' : (Fin e → ℂ) → (Σ k, ι k) → ℂ} {y : Fin e → ℂ}
    (hγ : AnalyticAt ℂ γ y) (hγ' : AnalyticAt ℂ γ' y) (hy : ∀ k, ∃ i, γ y ⟨k, i⟩ ≠ 0)
    (hseg : (fun y' => segre (γ y')) =ᶠ[𝓝 y] fun y' => segre (γ' y')) :
    logNorm A s (γ y) * maDensity (fun j y' => pot L j (γ y')) y =
      logNorm A s (γ' y) * maDensity (fun j y' => pot L j (γ' y')) y := by
  obtain ⟨a, ha, hsm, -⟩ := hs
  have hy0 := hy
  choose i0 hi0 using hy0
  obtain ⟨c, hc⟩ : ∃ c : (Fin e → ℂ) → K → ℂ,
      ∀ y' k, c y' k = γ' y' ⟨k, i0 k⟩ / γ y' ⟨k, i0 k⟩ := ⟨_, fun _ _ => rfl⟩
  have hnz : ∀ᶠ y' in 𝓝 y, ∀ k, γ y' ⟨k, i0 k⟩ ≠ 0 :=
    Filter.eventually_all.mpr fun k => (analyticAt_coord hγ ⟨k, i0 k⟩).continuousAt.eventually_ne (hi0 k)
  have hrel : ∀ᶠ y' in 𝓝 y, (∀ k, γ y' ⟨k, i0 k⟩ ≠ 0) ∧ (∀ k, c y' k ≠ 0) ∧
      γ' y' = bsmul (c y') (γ y') := by
    filter_upwards [hnz, hseg] with y' h0 hs'
    obtain ⟨h1, h2⟩ := eq_bsmul_of_segre_eq i0 h0 hs'
    have hcy : c y' = fun k => γ' y' ⟨k, i0 k⟩ / γ y' ⟨k, i0 k⟩ := funext (hc y')
    refine ⟨h0, fun k => ?_, by rw [hcy]; exact h2⟩
    rw [hc]
    exact div_ne_zero (h1 k) (h0 k)
  obtain ⟨-, hc0, hyrel⟩ := hrel.self_of_nhds
  have hlog : logNorm A s (γ' y) = logNorm A s (γ y) := by
    rw [hyrel]
    exact logNorm_bsmul A ha hsm hc0 _
  rw [hlog]
  congr 1
  have hj : ∀ j, cxHessian (fun y' => pot L j (γ' y')) y = cxHessian (fun y' => pot L j (γ y')) y := by
    intro j
    have hcan : ∀ k, AnalyticAt ℂ (fun y' => c y' k) y := by
      intro k
      have hfun : (fun y' => c y' k) = fun y' => γ' y' ⟨k, i0 k⟩ / γ y' ⟨k, i0 k⟩ :=
        funext fun y' => hc y' k
      rw [hfun]
      exact (analyticAt_coord hγ' _).div (analyticAt_coord hγ _) (hi0 k)
    have hG : AnalyticAt ℂ
        (fun y' => ∑ k, (((L j).a k : ℝ) : ℂ) * Complex.log (c y' k / c y k)) y := by
      have hk : ∀ k, AnalyticAt ℂ
          (fun y' => (((L j).a k : ℝ) : ℂ) * Complex.log (c y' k / c y k)) y := by
        intro k
        refine analyticAt_const.mul (((hcan k).div analyticAt_const (hc0 k)).clog ?_)
        show c y k / c y k ∈ Complex.slitPlane
        rw [div_self (hc0 k)]
        exact Complex.one_mem_slitPlane
      have h := Finset.analyticAt_sum (𝕜 := ℂ)
        (f := fun (k : K) (y' : Fin e → ℂ) => (((L j).a k : ℝ) : ℂ) * Complex.log (c y' k / c y k))
        (c := y) Finset.univ (fun k _ => hk k)
      convert h using 1
      funext y'
      rw [Finset.sum_apply]
    have hev : (fun y' => pot L j (γ' y')) =ᶠ[𝓝 y] fun y' => pot L j (γ y') +
        (∑ k, (((L j).a k : ℝ) : ℂ) * Complex.log (c y' k / c y k)).re +
        ∑ k, ((L j).a k : ℝ) * Real.log ‖c y k‖ := by
      filter_upwards [hrel] with y' hy'
      obtain ⟨h0, hck, h2⟩ := hy'
      have hpos : 0 < (L j).h (γ y') := (L j).pos _ fun k => ⟨i0 k, h0 k⟩
      have hne : ∀ k ∈ Finset.univ, ‖c y' k‖ ^ (L j).a k ≠ 0 :=
        fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hck k))
      have key : ∀ k, Real.log (‖c y' k‖ / ‖c y k‖) = Real.log ‖c y' k‖ - Real.log ‖c y k‖ :=
        fun k => Real.log_div (norm_ne_zero_iff.mpr (hck k)) (norm_ne_zero_iff.mpr (hc0 k))
      have hb : (L j).h (bsmul (c y') (γ y')) = (∏ k, ‖c y' k‖ ^ (L j).a k) * (L j).h (γ y') :=
        (L j).smul _ _ hck
      simp only [pot]
      rw [h2, hb, Real.log_mul (Finset.prod_ne_zero_iff.mpr hne) hpos.ne',
        Real.log_prod hne]
      simp only [Complex.re_sum, Complex.re_ofReal_mul, Complex.log_re, norm_div, key,
        Real.log_zpow, mul_sub, Finset.sum_sub_distrib]
      ring
    rw [cxHessian_congr hev]
    exact cxHessian_add_re _ (pot_contDiffAt (hL j) hγ hy) hG
  simp only [maDensity, hj]

theorem sheet_analyticAt (hA : OsgoodStatement) {P : Ideal (MRing ι)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {y : Fin e → ℂ}
    {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} (h : IsSheet P Ψ y w γ) :
    AnalyticAt ℂ γ y := by
  obtain ⟨U, hU, hUo, hyU⟩ := _root_.mem_nhds_iff.mp (h.2.mono fun _ h' => h'.1)
  rw [analyticAt_pi_iff]
  intro p
  exact hA e U _ hUo (fun y' hy' => (differentiableAt_pi.mp (hU hy') p).differentiableWithinAt) y hyU

theorem sheetIndep_of (hA : OsgoodStatement) (hfib : FibreFiniteStatement) : SheetIndepStatement := by
  intro K _ ι _ P e Ψ L A s hvar hgood hL _ hs
  have hbad := badSet_null hA (hfib K ι P e Ψ hvar hgood)
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hbad] with y hy w γ γ' h h'
  have hseg : (fun y' => segre (γ y')) =ᶠ[𝓝 y] fun y' => segre (γ' y') := by
    by_contra hne
    exact hy ⟨w, γ, γ', h, h', hne⟩
  exact density_eq hL hs (sheet_analyticAt hA h) (sheet_analyticAt hA h') h.2.self_of_nhds.2.1.1 hseg

theorem sheetIndep : SheetIndepStatement := sheetIndep_of osgood fibreFinite

end ReciprocityTheory.ChartRestriction.G.Geo
end
end

