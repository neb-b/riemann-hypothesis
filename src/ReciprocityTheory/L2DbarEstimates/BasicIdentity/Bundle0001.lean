module

public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.Imports
public import ReciprocityTheory.L2DbarEstimates.BasicIdentity.BasicIdentityStatement
public import ReciprocityTheory.L2DbarEstimates.BasicIdentity.HasCompactSupportDTw

@[expose] public section

-- bundled from ReciprocityTheory.L2DbarEstimates.BasicIdentity.ImportsBis
section
namespace ReciprocityTheory.L2DbarEstimates.E

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

private lemma chart_symm_eventuallyEq_of_isChart {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n)
    (e e' : OpenPartialHomeomorph M (V n)) (he : IsChart n z e) (he' : IsChart n z e')
    (p : M) (hp : p ∈ e.source) (hp' : p ∈ e'.source) :
    e.symm =ᶠ[nhds (z p)] e'.symm := by
  have he0 : Set.EqOn z e e.source := he
  have he0' : Set.EqOn z e' e'.source := he'
  have hzp : z p = e' p := he0' hp'
  have h2 : e'.target ∩ e'.symm ⁻¹' e.source ∈ nhds (z p) := by
    rw [hzp]
    refine (e'.isOpen_inter_preimage_symm e.open_source).mem_nhds ⟨e'.map_source hp', ?_⟩
    rw [Set.mem_preimage, e'.left_inv hp']
    exact hp
  filter_upwards [h2] with y hy
  have hs : e'.symm y ∈ e'.source := e'.map_target hy.1
  have h3 : e (e'.symm y) = y := by
    rw [← he0 hy.2, he0' hs, e'.right_inv hy.1]
  calc e.symm y = e.symm (e (e'.symm y)) := by rw [h3]
    _ = e'.symm y := e.left_inv hy.2

private lemma db_eq_wdb_comp_chart_symm {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n)
    (e0 : OpenPartialHomeomorph M (V n)) (he0 : IsChart n z e0) (k : Fin n) (g : M → ℂ)
    (p : M) (hp : p ∈ e0.source) : db n z k g p = wdb n k (g ∘ e0.symm) (z p) := by
  have hex : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ p ∈ e.source := ⟨e0, he0, hp⟩
  have hspec := Classical.choose_spec hex
  have hE : (g ∘ (Classical.choose hex).symm) =ᶠ[nhds (z p)] (g ∘ e0.symm) :=
    (chart_symm_eventuallyEq_of_isChart z _ e0 hspec.1 he0 p hspec.2 hp).fun_comp g
  rw [db, dite_eq_left hex]
  unfold wdb
  rw [hE.fderiv_eq]

private lemma d_apply_eq_wd_of_mem_source {n : ℕ} {M : Type*} [TopologicalSpace M] (z : M → V n)
    (e0 : OpenPartialHomeomorph M (V n)) (he0 : IsChart n z e0) (k : Fin n) (g : M → ℂ)
    (p : M) (hp : p ∈ e0.source) : d n z k g p = wd n k (g ∘ e0.symm) (z p) := by
  have hex : ∃ e : OpenPartialHomeomorph M (V n), IsChart n z e ∧ p ∈ e.source := ⟨e0, he0, hp⟩
  have hspec := Classical.choose_spec hex
  have hE : (g ∘ (Classical.choose hex).symm) =ᶠ[nhds (z p)] (g ∘ e0.symm) :=
    (chart_symm_eventuallyEq_of_isChart z _ e0 hspec.1 he0 p hspec.2 hp).fun_comp g
  rw [d, dite_eq_left hex]
  unfold wd
  rw [hE.fderiv_eq]

private lemma differentiableAt_wdb_and_fderiv_wdb_eq {n : ℕ} (k : Fin n) (h : V n → ℂ) (y0 : V n)
    (hd : DifferentiableAt ℝ (fderiv ℝ h) y0) :
    DifferentiableAt ℝ (wdb n k h) y0 ∧ ∀ v : V n, fderiv ℝ (wdb n k h) y0 v =
      (fderiv ℝ (fderiv ℝ h) y0 v (bas n k) +
        Complex.I * fderiv ℝ (fderiv ℝ h) y0 v (Complex.I • bas n k)) / 2 := by
  have hA := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (bas n k) y0)
  have hB := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (Complex.I • bas n k) y0)
  have hW := HasFDerivAt.const_mul (HasFDerivAt.add hA (HasFDerivAt.const_mul hB Complex.I))
    ((2 : ℂ)⁻¹)
  have heq : wdb n k h = fun y =>
      (2 : ℂ)⁻¹ * (fderiv ℝ h y (bas n k) + Complex.I * fderiv ℝ h y (Complex.I • bas n k)) := by
    funext y
    rw [wdb, div_eq_inv_mul]
  have hW' : HasFDerivAt (wdb n k h) ((2 : ℂ)⁻¹ •
      ((fderiv ℝ h y0).comp (0 : V n →L[ℝ] V n) + (fderiv ℝ (fderiv ℝ h) y0).flip (bas n k) +
        Complex.I • ((fderiv ℝ h y0).comp (0 : V n →L[ℝ] V n) +
          (fderiv ℝ (fderiv ℝ h) y0).flip (Complex.I • bas n k)))) y0 := by
    rw [heq]
    exact hW
  refine ⟨HasFDerivAt.differentiableAt hW', fun v => ?_⟩
  rw [HasFDerivAt.fderiv hW']
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, map_zero, zero_add,
    ContinuousLinearMap.flip_apply, smul_eq_mul]
  ring

private lemma differentiableAt_wd_and_fderiv_wd_eq {n : ℕ} (k : Fin n) (h : V n → ℂ) (y0 : V n)
    (hd : DifferentiableAt ℝ (fderiv ℝ h) y0) :
    DifferentiableAt ℝ (wd n k h) y0 ∧ ∀ v : V n, fderiv ℝ (wd n k h) y0 v =
      (fderiv ℝ (fderiv ℝ h) y0 v (bas n k) -
        Complex.I * fderiv ℝ (fderiv ℝ h) y0 v (Complex.I • bas n k)) / 2 := by
  have hA := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (bas n k) y0)
  have hB := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (Complex.I • bas n k) y0)
  have hW := HasFDerivAt.const_mul (HasFDerivAt.sub hA (HasFDerivAt.const_mul hB Complex.I))
    ((2 : ℂ)⁻¹)
  have heq : wd n k h = fun y =>
      (2 : ℂ)⁻¹ * (fderiv ℝ h y (bas n k) - Complex.I * fderiv ℝ h y (Complex.I • bas n k)) := by
    funext y
    rw [wd, div_eq_inv_mul]
  have hW' : HasFDerivAt (wd n k h) ((2 : ℂ)⁻¹ •
      ((fderiv ℝ h y0).comp (0 : V n →L[ℝ] V n) + (fderiv ℝ (fderiv ℝ h) y0).flip (bas n k) -
        Complex.I • ((fderiv ℝ h y0).comp (0 : V n →L[ℝ] V n) +
          (fderiv ℝ (fderiv ℝ h) y0).flip (Complex.I • bas n k)))) y0 := by
    rw [heq]
    exact hW
  refine ⟨HasFDerivAt.differentiableAt hW', fun v => ?_⟩
  rw [HasFDerivAt.fderiv hW']
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply, map_zero, zero_add, ContinuousLinearMap.flip_apply,
    smul_eq_mul]
  ring

theorem comm (n : ℕ) (M : Type*) [TopologicalSpace M] : CommStatement n M := by
  intro z hz ph j k u x hph hu
  obtain ⟨e0, hx0, hze⟩ := hz x
  have he0 : IsChart n z e0 := by
    intro y _
    rw [hze]
  have he0' : Set.EqOn z e0 e0.source := he0
  have hy0 : z x ∈ e0.target := by
    rw [he0' hx0]
    exact e0.map_source hx0
  have hnb : e0.target ∈ nhds (z x) := e0.open_target.mem_nhds hy0
  have hcH : ContDiffAt ℝ 2 (u ∘ e0.symm) (z x) := by
    have := (hu e0 he0).contDiffAt hnb
    simpa using this
  have hcP : ContDiffAt ℝ 2 ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm) (z x) := by
    have := (hph e0 he0).contDiffAt hnb
    simpa using this
  have hdH : DifferentiableAt ℝ (fderiv ℝ (u ∘ e0.symm)) (z x) :=
    (hcH.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdP : DifferentiableAt ℝ (fderiv ℝ ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm)) (z x) :=
    (hcP.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hH : DifferentiableAt ℝ (u ∘ e0.symm) (z x) := hcH.differentiableAt (by norm_num)
  have hsymH : ∀ v w : V n, fderiv ℝ (fderiv ℝ (u ∘ e0.symm)) (z x) v w =
      fderiv ℝ (fderiv ℝ (u ∘ e0.symm)) (z x) w v := by
    intro v w
    first
      | exact hcH.isSymmSndFDerivAt (by simp) v w
      | exact hcH.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField]) v w
  have hsymP : ∀ v w : V n, fderiv ℝ (fderiv ℝ ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm)) (z x) v w =
      fderiv ℝ (fderiv ℝ ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm)) (z x) w v := by
    intro v w
    first
      | exact hcP.isSymmSndFDerivAt (by simp) v w
      | exact hcP.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField]) v w
  have hloc1 : ((db n z j u) ∘ e0.symm) =ᶠ[nhds (z x)] wdb n j (u ∘ e0.symm) := by
    filter_upwards [hnb] with y hy
    rw [Function.comp_apply, db_eq_wdb_comp_chart_symm z e0 he0 j u _ (e0.map_target hy),
      he0' (e0.map_target hy), e0.right_inv hy]
  have hloc2 : ((db n z j (fun y => ((ph y : ℝ) : ℂ))) ∘ e0.symm) =ᶠ[nhds (z x)] wdb n j ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm) := by
    filter_upwards [hnb] with y hy
    rw [Function.comp_apply, db_eq_wdb_comp_chart_symm z e0 he0 j _ _ (e0.map_target hy),
      he0' (e0.map_target hy), e0.right_inv hy]
  have hloc3 : ((fun y => d n z k u y - u y * d n z k (fun y => ((ph y : ℝ) : ℂ)) y) ∘ e0.symm) =ᶠ[nhds (z x)]
      (fun y => wd n k (u ∘ e0.symm) y - (u ∘ e0.symm) y * wd n k ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm) y) := by
    filter_upwards [hnb] with y hy
    have hp := e0.map_target hy
    rw [Function.comp_apply, d_apply_eq_wd_of_mem_source z e0 he0 k u _ hp, d_apply_eq_wd_of_mem_source z e0 he0 k _ _ hp,
      he0' hp, e0.right_inv hy]
    rfl
  have hux : u x = (u ∘ e0.symm) (z x) := by
    rw [Function.comp_apply, he0' hx0, e0.left_inv hx0]
  have hW1 := (differentiableAt_wdb_and_fderiv_wdb_eq j _ _ hdH).2
  have hW2 := differentiableAt_wd_and_fderiv_wd_eq k _ _ hdH
  have hW3 := differentiableAt_wd_and_fderiv_wd_eq k _ _ hdP
  have hW4 := (differentiableAt_wdb_and_fderiv_wdb_eq j _ _ hdP).2
  have hFG : fderiv ℝ (fun y => wd n k (u ∘ e0.symm) y - (u ∘ e0.symm) y * wd n k ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm) y) (z x) =
      fderiv ℝ (wd n k (u ∘ e0.symm)) (z x) - ((u ∘ e0.symm) (z x) • fderiv ℝ (wd n k ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm)) (z x) +
        wd n k ((fun y => ((ph y : ℝ) : ℂ)) ∘ e0.symm) (z x) • fderiv ℝ (u ∘ e0.symm) (z x)) := by
    have h1 := HasFDerivAt.sub (DifferentiableAt.hasFDerivAt hW2.1)
      (HasFDerivAt.mul (DifferentiableAt.hasFDerivAt hH) (DifferentiableAt.hasFDerivAt hW3.1))
    exact HasFDerivAt.fderiv h1
  show (d n z k (db n z j u) x - db n z j u x * d n z k (fun y => ((ph y : ℝ) : ℂ)) x) -
      db n z j (fun y => d n z k u y - u y * d n z k (fun y => ((ph y : ℝ) : ℂ)) y) x =
    d n z k (db n z j (fun y => ((ph y : ℝ) : ℂ))) x * u x
  rw [d_apply_eq_wd_of_mem_source z e0 he0 k (db n z j u) x hx0, db_eq_wdb_comp_chart_symm z e0 he0 j u x hx0,
    d_apply_eq_wd_of_mem_source z e0 he0 k (fun y => ((ph y : ℝ) : ℂ)) x hx0, db_eq_wdb_comp_chart_symm z e0 he0 j _ x hx0,
    d_apply_eq_wd_of_mem_source z e0 he0 k (db n z j (fun y => ((ph y : ℝ) : ℂ))) x hx0, hux]
  unfold wd wdb
  rw [hloc1.fderiv_eq, hloc2.fderiv_eq, hloc3.fderiv_eq, hFG]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hW1 (bas n k), hW1 (Complex.I • bas n k), hW2.2 (bas n j), hW2.2 (Complex.I • bas n j),
    hW3.2 (bas n j), hW3.2 (Complex.I • bas n j), hW4 (bas n k), hW4 (Complex.I • bas n k)]
  unfold wd
  rw [hsymH (bas n k) (bas n j), hsymH (bas n k) (Complex.I • bas n j),
    hsymH (Complex.I • bas n k) (bas n j), hsymH (Complex.I • bas n k) (Complex.I • bas n j),
    hsymP (bas n k) (bas n j), hsymP (bas n k) (Complex.I • bas n j),
    hsymP (Complex.I • bas n k) (bas n j), hsymP (Complex.I • bas n k) (Complex.I • bas n j)]
  ring

end

end ReciprocityTheory.L2DbarEstimates.E
end

-- bundled from ReciprocityTheory.L2DbarEstimates.BasicIdentity.TstarNormSq
section
namespace ReciprocityTheory.L2DbarEstimates.E

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

theorem tStarIbp (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : TStarIbpStatement n M := by
  intro z hz ph₁ ph₂ g f _hph₁ hph₂ hg hf
  have hE := ck_expNeg n z 1 ph₂ hph₂
  have hF : ∀ j, Ck n z 1 (fun y => (Real.exp (-ph₂ y) : ℂ) * f y j) :=
    fun j => Ck.mul n z 1 _ _ hE (hf j).1
  have hFc : ∀ j, HasCompactSupport (fun y => (Real.exp (-ph₂ y) : ℂ) * f y j) :=
    fun j => (hf j).2.mul_left
  have hG : ∀ j, Ck n z 1 (fun y => conj ((Real.exp (-ph₂ y) : ℂ) * f y j)) :=
    fun j => Ck.conj n z 1 _ (hF j)
  have hGc : ∀ j, HasCompactSupport (fun y => conj ((Real.exp (-ph₂ y) : ℂ) * f y j)) :=
    fun j => (hFc j).comp_left (map_zero (starRingEnd ℂ))
  have hj : ∀ j, ∫ x, db n z j g x * conj ((Real.exp (-ph₂ x) : ℂ) * f x j) ∂vol n z =
      -∫ x, g x * conj (d n z j (fun y => (Real.exp (-ph₂ y) : ℂ) * f y j) x) ∂vol n z := by
    intro j
    rw [integral_db_mul n z hz j g _ hg (hG j) (hGc j)]
    congr 2
    funext x
    rw [db_conj]
  have hint1 : ∀ j ∈ (Finset.univ : Finset (Fin n)), Integrable
      (fun x => db n z j g x * conj ((Real.exp (-ph₂ x) : ℂ) * f x j)) (vol n z) := by
    intro j _
    apply integrable_of_continuous n z hz
    · exact (Ck.continuous n z hz 0 _ (Ck.db n z 0 j g hg)).mul
        (Ck.continuous n z hz 1 _ (hG j))
    · exact (hGc j).mul_left
  have hint2 : ∀ j ∈ (Finset.univ : Finset (Fin n)), Integrable
      (fun x => g x * conj (d n z j (fun y => (Real.exp (-ph₂ y) : ℂ) * f y j) x)) (vol n z) := by
    intro j _
    apply integrable_of_continuous n z hz
    · exact (Ck.continuous n z hz 1 _ hg).mul
        (Ck.continuous n z hz 0 _ (Ck.conj n z 0 _ (Ck.d n z 0 j _ (hF j))))
    · exact ((hasCompactSupport_d n z j _ (hFc j)).comp_left (map_zero (starRingEnd ℂ))).mul_left
  have lhs : ∫ x, (∑ j, db n z j g x * conj (f x j)) * (Real.exp (-ph₂ x) : ℂ) ∂vol n z =
      ∑ j, ∫ x, db n z j g x * conj ((Real.exp (-ph₂ x) : ℂ) * f x j) ∂vol n z := by
    rw [← integral_finsetSum _ hint1]
    congr 1
    funext x
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [map_mul, Complex.conj_ofReal]
    ring
  have rhs : ∫ x, g x * conj (tstar n z ph₁ ph₂ f x) * (Real.exp (-ph₁ x) : ℂ) ∂vol n z =
      ∑ j, -∫ x, g x * conj (d n z j (fun y => (Real.exp (-ph₂ y) : ℂ) * f y j) x) ∂vol n z := by
    rw [Finset.sum_neg_distrib, ← integral_finsetSum _ hint2, ← integral_neg]
    congr 1
    funext x
    have he : (Real.exp (ph₁ x) : ℂ) * (Real.exp (-ph₁ x) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, Complex.ofReal_one]
    unfold tstar
    rw [← Finset.mul_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_neg, map_mul, map_sum, Complex.conj_ofReal]
    generalize (∑ j : Fin n, conj (d n z j (fun y => (Real.exp (-ph₂ y) : ℂ) * f y j) x)) = S
    linear_combination (-(g x * S)) * he
  rw [lhs, rhs]
  exact Finset.sum_congr rfl (fun j _ => hj j)

private theorem d_sub_of_ck_one (n : ℕ) {M : Type*} [TopologicalSpace M] (z : M → V n) (f g : M → ℂ)
    (hf : Ck n z 1 f) (hg : Ck n z 1 g) (j : Fin n) (x : M) :
    d n z j (fun y => f y - g y) x = d n z j f x - d n z j g x := by
  have h := d_add n z (fun y => f y - g y) g (Ck.sub n z 1 f g hf hg) hg j x
  simp only [sub_add_cancel] at h
  rw [h]
  ring

theorem tStarPoint (n : ℕ) (M : Type*) [TopologicalSpace M] : TStarPointStatement n M := by
  intro z hz ph ψ f hph hψ hf x
  have hg : Ck n z 1 (fun y => (ψ y : ℂ) - (ph y : ℂ)) := Ck.sub n z 1 _ _ hψ hph
  have hE : Ck n z 1 (fun y => Complex.exp ((ψ y : ℂ) - (ph y : ℂ))) := Ck.cexp n z 1 _ hg
  have hEfun : (fun y => (Real.exp (-(ph y - ψ y)) : ℂ)) =
      fun y => Complex.exp ((ψ y : ℂ) - (ph y : ℂ)) := by
    funext y
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hdE : ∀ j, d n z j (fun y => Complex.exp ((ψ y : ℂ) - (ph y : ℂ))) x =
      Complex.exp ((ψ x : ℂ) - (ph x : ℂ)) *
        (d n z j (fun y => (ψ y : ℂ)) x - d n z j (fun y => (ph y : ℂ)) x) := by
    intro j
    rw [d_cexp n z _ hg j x, d_sub_of_ck_one n z _ _ hψ hph j x]
  have key : ∀ j, d n z j (fun y => (Real.exp (-(ph y - ψ y)) : ℂ) * f y j) x =
      Complex.exp ((ψ x : ℂ) - (ph x : ℂ)) *
        (dTw n z ph j (fun y => f y j) x + f x j * d n z j (fun y => (ψ y : ℂ)) x) := by
    intro j
    have hfun : (fun y => (Real.exp (-(ph y - ψ y)) : ℂ) * f y j) =
        fun y => Complex.exp ((ψ y : ℂ) - (ph y : ℂ)) * f y j := by
      funext y
      rw [congrFun hEfun y]
    rw [hfun, d_mul n z _ _ hE (hf j) j x, hdE j]
    simp only [dTw]
    ring
  show (Real.exp (ψ x) : ℂ) * -((Real.exp (ph x - 2 * ψ x) : ℂ) *
      ∑ j, d n z j (fun y => (Real.exp (-(ph y - ψ y)) : ℂ) * f y j) x) = _
  rw [Finset.sum_congr rfl (fun j _ => key j), ← Finset.mul_sum]
  have hexp : (Real.exp (ψ x) : ℂ) * (Real.exp (ph x - 2 * ψ x) : ℂ) *
      Complex.exp ((ψ x : ℂ) - (ph x : ℂ)) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add, Complex.ofReal_exp, ← Complex.exp_add,
      ← Complex.exp_zero]
    congr 1
    push_cast
    ring
  linear_combination (-(∑ j, (dTw n z ph j (fun y => f y j) x +
    f x j * d n z j (fun y => (ψ y : ℂ)) x))) * hexp

theorem tstar_norm_sq (n : ℕ) {M : Type*} [TopologicalSpace M] (z : M → V n)
    (hz : IsLocalHomeomorph z) (ph ψ : M → ℝ) (f : M → V n) (hph : CkR n z 1 ph)
    (hψ : CkR n z 1 ψ) (hf : ∀ j, Ck n z 1 (fun x => f x j)) (x : M) :
    ‖tstar n z (fun y => ph y - 2 * ψ y) (fun y => ph y - ψ y) f x‖ ^ 2 *
        Real.exp (-(ph x - 2 * ψ x)) =
      ‖∑ j, (dTw n z ph j (fun y => f y j) x + f x j * d n z j (fun y => (ψ y : ℂ)) x)‖ ^ 2 *
        Real.exp (-ph x) := by
  have hp := tStarPoint n M z hz ph ψ f hph hψ hf x
  set S := ∑ j, (dTw n z ph j (fun y => f y j) x + f x j * d n z j (fun y => (ψ y : ℂ)) x) with hS
  set T := tstar n z (fun y => ph y - 2 * ψ y) (fun y => ph y - ψ y) f x with hT
  have he := Real.exp_pos (ψ x)
  have hn : Real.exp (ψ x) * ‖T‖ = ‖S‖ := by
    have h1 := congrArg (fun w : ℂ => ‖w‖) hp
    simp only [norm_mul, norm_neg] at h1
    rw [← h1]
    congr 1
    first
      | rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos he]
      | simp [abs_of_pos he]
  have hT' : ‖T‖ = ‖S‖ * Real.exp (-ψ x) := by
    rw [Real.exp_neg, ← hn]
    first
      | rw [mul_comm (Real.exp (ψ x)), mul_assoc, mul_inv_cancel₀ he.ne', mul_one]
      | field_simp
  have hx : Real.exp (-ψ x) ^ 2 * Real.exp (-(ph x - 2 * ψ x)) = Real.exp (-ph x) := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [hT', mul_pow, mul_assoc, hx]

end

end ReciprocityTheory.L2DbarEstimates.E
end

-- bundled from ReciprocityTheory.L2DbarEstimates.BasicIdentity.WIbpLeft
section
namespace ReciprocityTheory.L2DbarEstimates.E

open MeasureTheory
open scoped ComplexConjugate

noncomputable section

theorem wIbp_left (n : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] (z : M → V n) (hz : IsLocalHomeomorph z) (ph : M → ℝ)
    (k : Fin n) (a b : M → ℂ) (hph : CkR n z 1 ph) (ha : Ck n z 1 a) (hb : Ck n z 1 b)
    (hc : HasCompactSupport a ∨ HasCompactSupport b) :
    (∫ x, db n z k a x * conj (b x) * (Real.exp (-ph x) : ℂ) ∂vol n z) =
      -∫ x, a x * conj (dTw n z ph k b x) * (Real.exp (-ph x) : ℂ) ∂vol n z := by
  have hw : Ck n z 1 (fun x => (Real.exp (-ph x) : ℂ)) := ck_expNeg n z 1 ph hph
  have hbc : Ck n z 1 (fun x => conj (b x)) := Ck.conj n z 1 b hb
  set g : M → ℂ := fun x => conj (b x) * (Real.exp (-ph x) : ℂ) with hgdef
  have hg : Ck n z 1 g := Ck.mul n z 1 _ _ hbc hw

  have hdg : ∀ x, a x * db n z k g x =
      a x * conj (dTw n z ph k b x) * (Real.exp (-ph x) : ℂ) := by
    intro x
    have h1 := db_mul n z _ _ hbc hw k x
    beta_reduce at h1
    rw [hgdef, h1, db_conj n z b k x, db_expNeg n z ph hph k x, dTw, db_ofReal n z ph k x]
    simp only [map_sub, map_mul]
    ring
  have hL : (fun x => db n z k a x * conj (b x) * (Real.exp (-ph x) : ℂ)) =
      fun x => db n z k a x * g x := by
    funext x
    simp only [hgdef]
    ring
  have hR : (fun x => a x * conj (dTw n z ph k b x) * (Real.exp (-ph x) : ℂ)) =
      fun x => a x * db n z k g x := by
    funext x
    exact (hdg x).symm
  rw [hL, hR]
  rcases hc with hca | hcb
  · have h := integral_db_mul n z hz k g a hg ha hca
    have e1 : (fun x => db n z k a x * g x) = fun x => g x * db n z k a x := by
      funext x
      ring
    have e2 : (fun x => a x * db n z k g x) = fun x => db n z k g x * a x := by
      funext x
      ring
    rw [e1, e2, h, neg_neg]
  · have hgc : HasCompactSupport g :=
      (hcb.comp_left (map_zero (starRingEnd ℂ))).mul_right
    exact integral_db_mul n z hz k a g ha hg hgc

theorem wIbp (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] : WIbpStatement n M := by
  intro z hz ph k a b hph ha hb hc
  refine ⟨wIbp_left n z hz ph k a b hph ha hb hc, ?_⟩

  have h := wIbp_left n z hz ph k b a hph hb ha hc.symm
  have h' := congrArg (starRingEnd ℂ) h
  rw [← integral_conj, map_neg, ← integral_conj] at h'
  have e1 : (fun x => dTw n z ph k a x * conj (b x) * (Real.exp (-ph x) : ℂ)) =
      fun x => conj (b x * conj (dTw n z ph k a x) * (Real.exp (-ph x) : ℂ)) := by
    funext x
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
    ring
  have e2 : (fun x => a x * conj (db n z k b x) * (Real.exp (-ph x) : ℂ)) =
      fun x => conj (db n z k b x * conj (a x) * (Real.exp (-ph x) : ℂ)) := by
    funext x
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
    ring
  rw [e1, e2, h', neg_neg]

end

end ReciprocityTheory.L2DbarEstimates.E
end

