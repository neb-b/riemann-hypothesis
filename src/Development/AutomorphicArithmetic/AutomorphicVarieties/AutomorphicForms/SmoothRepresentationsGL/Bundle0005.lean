module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.LevelS
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

theorem UpperTheory.V.Af.Smo.levelS :
    UpperTheory.V.Af.Smo.LevelS := by
  intro E _ _ n V
  let e := AdelicGLn.finiteRestrictedEquiv E n
  let f : (∀ v : HeightOneSpectrum (𝓞 E), (GLnLocal.integralGL (v.adicCompletion E) n : Set (GL (Fin n) (v.adicCompletion E)))) →
      GL (Fin n) (Af E) := fun x => e.symm (RestrictedProduct.structureMap _ _ Filter.cofinite x)
  have hf : Continuous f := e.symm.continuous.comp RestrictedProduct.isEmbedding_structureMap.continuous
  let o : ∀ v : HeightOneSpectrum (𝓞 E), (GLnLocal.integralGL (v.adicCompletion E) n : Set (GL (Fin n) (v.adicCompletion E))) :=
    fun v => ⟨1, one_mem _⟩
  have ho : f o = 1 := by
    refine e.symm_apply_eq.2 ?_
    rw [map_one]
    rfl
  have hV : f ⁻¹' (V : Set (GL (Fin n) (Af E))) ∈ 𝓝 o := hf.continuousAt.preimage_mem_nhds (ho ▸ V.mem_nhds_one)
  rw [nhds_pi, Filter.mem_pi'] at hV
  obtain ⟨S, t, ht, hS⟩ := hV
  refine ⟨S, fun k hk => ?_⟩
  have hek : ∀ v, e k v = cmp v k := fun v => Units.ext (Matrix.ext fun _ _ => rfl)
  have hi : ∀ v : HeightOneSpectrum (𝓞 E), cmp v k ∈ GLnLocal.integralGL (v.adicCompletion E) n := fun v => by
    have h := GlobalTheory.AdelicU.mem_GLint_iff.1 (hk.2 v)
    rw [GLnLocal.mem_integralGL_iff]
    simp only [GroundTheory.Global.mem_valuationInteger_iff]
    exact h
  have hx : f (fun v => ⟨cmp v k, hi v⟩) = k := by
    refine e.symm_apply_eq.2 (DFunLike.ext _ _ fun v => ?_)
    exact (hek v).symm
  rw [← hx]
  refine hS fun v hv => ?_
  have : (⟨cmp v k, hi v⟩ : (GLnLocal.integralGL (v.adicCompletion E) n : Set (GL (Fin n) (v.adicCompletion E)))) = o v :=
    Subtype.ext (hk.1 v hv)
  exact this ▸ mem_of_mem_nhds (ht v)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.LinChange
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem linearMap_comp_eq_on_smul_of_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (A B : V →L[ℝ] V)
    (h1 : ∀ x, B (A x) = x) (h2 : ∀ x, A (B x) = x) (f : V → ℂ) :
    ∫ x, f (A x) ∂μ = ((|(LinearMap.det (A : V →ₗ[ℝ] V))⁻¹| : ℝ) : ℂ) * ∫ x, f x ∂μ := by
  let e : V ≃L[ℝ] V := ContinuousLinearEquiv.equivOfInverse A B h1 h2
  have hd : LinearMap.det (A : V →ₗ[ℝ] V) ≠ 0 := (LinearEquiv.isUnit_det' e.toLinearEquiv).ne_zero
  have hm : MeasurableEmbedding (A : V →ₗ[ℝ] V) := e.toHomeomorph.measurableEmbedding
  have := hm.integral_map (μ := μ) f
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar μ hd, integral_smul_measure,
    ENNReal.toReal_ofReal (abs_nonneg _)] at this
  rw [← Complex.real_smul, this]
  rfl

theorem UpperTheory.V.Af.Smo.linChange :
    UpperTheory.V.Af.Smo.LinChange := by
  intro E _ _ n
  refine ⟨fun s => ((|(LinearMap.det (lmul (toL s.val) : Lie E n →ₗ[ℝ] Lie E n))⁻¹| : ℝ) : ℂ), ?_, fun s f => ?_⟩
  · have : (lmul (toL (1 : GL (Fin n) (Rinf E)).val) : Lie E n →ₗ[ℝ] Lie E n) = LinearMap.id :=
      LinearMap.ext fun x => one_mul (Matrix.of x)
    simp only [this]
    simp
  · haveI : (volume : Measure (Rinf E)).IsAddHaarMeasure := inferInstance
    haveI : (volume : Measure (Fin n → Rinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
    haveI : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
    exact linearMap_comp_eq_on_smul_of_eq volume (lmul (toL s.val)) (lmul (toL (s⁻¹).val))
      (fun x => s.inv_mul_cancel_left (Matrix.of x)) (fun x => s.mul_inv_cancel_left (Matrix.of x)) f
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.LocDual
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem mul_inv_lt_mul_inv_mul_inv_of_le_of_lt_one {G : Type} [LinearOrderedCommGroupWithZero G] (ua g ux p : G) (hua : ua ≠ 0)
    (hg : 0 < g) (hgx : g ≤ ux) (hp : p < 1) (hp0 : p ≠ 0) :
    ua * ux⁻¹ < ua * g⁻¹ * p⁻¹ := by
  have h1 : ux⁻¹ ≤ g⁻¹ := inv_anti₀ hg hgx
  have h2 : ua * ux⁻¹ ≤ ua * g⁻¹ := by gcongr
  have h3 : 1 < p⁻¹ := one_lt_inv₀ (zero_lt_iff.mpr hp0) |>.mpr hp
  have h4 : 0 < ua * g⁻¹ := by
    apply zero_lt_iff.mpr
    exact mul_ne_zero hua (inv_ne_zero hg.ne')
  calc ua * ux⁻¹ ≤ ua * g⁻¹ := h2
    _ = ua * g⁻¹ * 1 := (mul_one _).symm
    _ < ua * g⁻¹ * p⁻¹ := mul_lt_mul_of_pos_left h3 h4

private theorem mul_lt_of_lt_mul_inv_of_lt {G : Type} [LinearOrderedCommGroupWithZero G] (q y r g1 : G) (hr : 0 < r)
    (hy : y < r) (hq : q < g1 * r⁻¹) : q * y < g1 := by
  calc q * y ≤ q * r := by gcongr
    _ < g1 * r⁻¹ * r := mul_lt_mul_of_pos_right hq hr
    _ = g1 := by rw [mul_assoc, inv_mul_cancel₀ hr.ne', mul_one]

theorem UpperTheory.V.Af.Smo.locDual :
    UpperTheory.V.Af.Smo.LocDual := by
  intro E _ _ w ψ hψ V hV
  obtain ⟨a, ha⟩ : ∃ a, ψ a ≠ 1 := by
    by_contra h
    push_neg at h
    exact hψ (AddChar.ext _ _ fun x => by simpa using h x)
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hV
  obtain ⟨C, hC, hC0⟩ := exists_compact_mem_nhds (0 : HeightOneSpectrum.adicCompletion E w)
  obtain ⟨γ₁, hγ₁⟩ := Valued.mem_nhds_zero.mp hC0
  obtain ⟨π₀, hπ₀⟩ := HeightOneSpectrum.valuation_exists_uniformizer E w
  have hvπ : Valued.v (π₀ : HeightOneSpectrum.adicCompletion E w) = WithZero.exp (-1 : ℤ) := by
    simp [hπ₀]
  have hπ0 : (π₀ : HeightOneSpectrum.adicCompletion E w) ≠ 0 := by
    intro h
    rw [h, map_zero] at hvπ
    exact WithZero.zero_ne_coe hvπ
  have hπ1 : Valued.v.restrict (π₀ : HeightOneSpectrum.adicCompletion E w) < 1 := by
    rw [Valuation.restrict_lt_one_iff, hvπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hπn : Valued.v.restrict (π₀ : HeightOneSpectrum.adicCompletion E w) ≠ 0 := by
    rw [Ne, Valuation.restrict_eq_zero_iff, hvπ]
    exact WithZero.exp_ne_zero
  have hua : Valued.v.restrict a ≠ 0 := by simp [ha0]
  set R := Units.mk0 (Valued.v.restrict a * (γ : _)⁻¹ *
    (Valued.v.restrict (π₀ : HeightOneSpectrum.adicCompletion E w))⁻¹)
    (mul_ne_zero (mul_ne_zero hua γ⁻¹.ne_zero) (inv_ne_zero hπn)) with hR
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hπ1 (γ₁ * R⁻¹)
  refine ⟨Valued.v.restrict.ltAddSubgroup R, ?_, ?_, ?_⟩
  · rw [Valuation.coe_ltAddSubgroup]
    exact Valued.isOpen_ball _ _
  · rw [Valuation.coe_ltAddSubgroup]
    refine IsCompact.of_isClosed_subset
      (hC.image (continuous_const.mul continuous_id :
        Continuous fun z : HeightOneSpectrum.adicCompletion E w =>
          ((π₀ : HeightOneSpectrum.adicCompletion E w) ^ n)⁻¹ * z))
      (Valued.isClosed_ball _ _) ?_
    intro y hy
    refine ⟨(π₀ : HeightOneSpectrum.adicCompletion E w) ^ n * y, hγ₁ ?_, ?_⟩
    · show Valued.v.restrict ((π₀ : HeightOneSpectrum.adicCompletion E w) ^ n * y) < γ₁
      rw [map_mul, map_pow]
      refine mul_lt_of_lt_mul_inv_of_lt _ _ _ _ (zero_lt_iff.mpr R.ne_zero) hy ?_
      simpa using hn
    · exact inv_mul_cancel_left₀ (pow_ne_zero n hπ0) y
  · intro x hx
    by_contra hxV
    have hxg : (γ : _) ≤ Valued.v.restrict x := by
      by_contra h
      push_neg at h
      exact hxV (hγ h)
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hxg
      exact γ.ne_zero (le_antisymm hxg zero_le')
    have hy : a * x⁻¹ ∈ Valued.v.restrict.ltAddSubgroup R := by
      rw [← SetLike.mem_coe, Valuation.coe_ltAddSubgroup]
      show Valued.v.restrict (a * x⁻¹) < R
      rw [map_mul, map_inv₀, hR, Units.val_mk0, Units.val_inv_eq_inv_val]
      exact mul_inv_lt_mul_inv_mul_inv_of_le_of_lt_one _ _ _ _ hua (zero_lt_iff.mpr γ.ne_zero) hxg hπ1 hπn
    have h1 := hx _ hy
    rw [mul_comm a, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul] at h1
    exact ha h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.LocKir
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem exists_conj_le {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : OpenSubgroup G) (s : Finset G) : ∃ U₁ : OpenSubgroup G, ∀ u ∈ U₁, ∀ x ∈ s, x⁻¹ * u * x ∈ U := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨⊤, by simp⟩
  | insert a s _ ih =>
    obtain ⟨V, hV⟩ := ih
    have hc : Continuous (MulAut.conj a⁻¹).toMonoidHom := by
      change Continuous fun u : G => a⁻¹ * u * a⁻¹⁻¹
      fun_prop
    refine ⟨V ⊓ U.comap (MulAut.conj a⁻¹).toMonoidHom hc, fun u hu x hx => ?_⟩
    obtain ⟨h1, h2⟩ := OpenSubgroup.mem_inf.1 hu
    rcases Finset.mem_insert.1 hx with rfl | hx
    · have h3 : x⁻¹ * u * x⁻¹⁻¹ ∈ U := OpenSubgroup.mem_comap.1 h2
      rwa [inv_inv] at h3
    · exact hV u h1 x hx

private theorem supN_one {R : Type} [CommRing R] {n : ℕ} : supN (1 : Matrix (Fin n) (Fin n) R) = 0 := by
  unfold supN
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h
  · exact Matrix.one_apply_ne (by rintro rfl; omega)
  · rfl

private theorem rowM_one {R : Type} [CommRing R] {n : ℕ} (m : Fin n) :
    rowM m ((1 : Matrix (Fin n) (Fin n) R) m) = 1 := by
  ext i j
  simp only [rowM, Matrix.of_apply]
  split_ifs with h
  · rw [h.1]
  · rfl

private theorem isWh_comb {R : Type} [CommRing R] {n : ℕ} {ψ : R → ℂ} {W : GL (Fin n) R → ℂ} (hW : IsWh ψ W)
    (c : GL (Fin n) R →₀ ℂ) : IsWh ψ (comb c W) := by
  intro ν hν g
  unfold comb
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr fun x _ => ?_
  rw [mul_assoc, hW ν hν]
  ring

theorem UpperTheory.V.Af.Smo.locKir :
    UpperTheory.V.Af.Smo.ColConj → UpperTheory.V.Af.Smo.RowStep → UpperTheory.V.Af.Smo.LocStep → UpperTheory.V.Af.Smo.LocKir := by
  classical
  intro hcol hrow hstep E _ _ w ψ h0 h1 n m hm U
  induction m with
  | zero =>
    refine ⟨Finsupp.single 1 1, fun p => ψ (supN p.val), ?_, fun W hW _ p hp => ?_⟩
    · simp only [Units.val_one, supN_one, AddChar.map_zero_eq_one]
    · unfold comb
      rw [Finsupp.sum_single_index (by simp), one_mul, hW p hp]
  | succ m ih =>
    obtain ⟨c₀, H₀, hH₀, hc₀⟩ := ih (by omega)
    obtain ⟨U₁, hU₁⟩ := exists_conj_le U c₀.support
    let m' : Fin n := ⟨m, by omega⟩
    obtain ⟨c₁, h, hh1, hh, hc₁⟩ := hstep E w ψ h0 h1 n m' hm U₁
    obtain ⟨c, -, hc⟩ := exists_comb_comb c₁ c₀
    have hσ : ∃ σ : (Fin n → w.adicCompletion E) → GL (Fin n) (w.adicCompletion E),
        ∀ ξ (s : GL (Fin n) (w.adicCompletion E)), s.val = rowM m' ξ → σ ξ = s := by
      refine ⟨fun ξ => if e : ∃ s : GL (Fin n) (w.adicCompletion E), s.val = rowM m' ξ then e.choose else 1,
        fun ξ s hs => ?_⟩
      have e : ∃ s : GL (Fin n) (w.adicCompletion E), s.val = rowM m' ξ := ⟨s, hs⟩
      simp only [dif_pos e]
      exact Units.ext (e.choose_spec.trans hs.symm)
    obtain ⟨σ, hσ⟩ := hσ
    refine ⟨c, fun p => h (p.val m') * H₀ (p * (σ (p.val m'))⁻¹), ?_, fun W hW hWU p hp => ?_⟩
    · have : σ ((1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) m') = 1 := hσ _ 1 (rowM_one m').symm
      simp only [Units.val_one, hh1, this, inv_one, mul_one, one_mul, hH₀]
    · have hinv : ∀ g, ∀ u ∈ U₁, comb c₀ W (g * u) = comb c₀ W g := by
        intro g u hu
        unfold comb
        refine Finsupp.sum_congr fun x hx => ?_
        rw [← hWU (g * x) _ (hU₁ u hu x hx)]
        congr 2
        group
      rw [hc, hc₁ (comb c₀ W) hinv p (p.val m') ?_]
      · by_cases hz : h (p.val m') = 0
        · simp only [hz, zero_mul]
        · obtain ⟨s, hsU, hs⟩ := hh _ hz
          simp only [hσ _ s hs]
          rw [← hinv p s⁻¹ (U₁.inv_mem hsU), hc₀ W hW hWU _ (hrow _ n m' p s hp hs), mul_assoc]
      · intro u t ht
        obtain ⟨ν, hν, e1, e2⟩ := hcol _ n m' hm p hp u
        have e : p * t = ν * p := Units.ext (by rw [Units.val_mul, Units.val_mul, ht, e2])
        rw [e, isWh_comb hW c₀ ν hν, e1]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.OrthConv
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem conv_left {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {n : ℕ} (f : GA E n → ℂ)
    (α : Lie E n → ℂ) (z : GA E n) (h : ∀ g, f (z * g) = f g) (g : GA E n) : Af.Smo.conv f α (z * g) = Af.Smo.conv f α g := by
  have e : chart f (z * g) = chart f g := by
    funext x
    unfold chart
    split_ifs with hx
    · rw [mul_assoc, h]
    · rfl
  unfold Af.Smo.conv
  rw [e]

set_option synthInstance.maxHeartbeats 200000 in
private theorem zero_of_sq {E : Type} [Field E] [NumberField E] {n : ℕ} (μ : Measure (Reduction.normOneGL (K := E) (n := n)))
    [μ.IsHaarMeasure] (F : AdelicGLn.AdelicGL E n → ℂ) (hc : Continuous F) (C : ℝ) (hC : ∀ g, ‖F g‖ ≤ C)
    (h : IsLeftInvariant F)
    (h0 : ∫ q, starRingEnd ℂ (CuspidalSpectrum.cuspQuot h q) * CuspidalSpectrum.cuspQuot h q
      ∂(RightCosetSpace.quotientMeasure (Reduction.rationalGLOne (K := E) (n := n)) μ) = 0) :
    ∀ y ∈ Reduction.normOneGL (K := E) (n := n), F y = 0 := by
  have := Reduction.isFiniteMeasure_quotientMeasure (K := E) (n := n) μ
  have hq := CuspidalSpectrum.continuous_cuspQuot h hc
  have hb : ∀ q, ‖CuspidalSpectrum.cuspQuot h q‖ ≤ C := fun q => by
    obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
    exact hC _
  have h1 : ∫ q, ‖CuspidalSpectrum.cuspQuot h q‖ ^ 2
      ∂(RightCosetSpace.quotientMeasure (Reduction.rationalGLOne (K := E) (n := n)) μ) = 0 := by
    rw [← Complex.ofReal_eq_zero, ← integral_complex_ofReal, ← h0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only [Complex.conj_mul', Complex.ofReal_pow]
  have hi : Integrable (fun q => ‖CuspidalSpectrum.cuspQuot h q‖ ^ 2)
      (RightCosetSpace.quotientMeasure (Reduction.rationalGLOne (K := E) (n := n)) μ) :=
    Integrable.of_bound (hq.norm.pow 2).aestronglyMeasurable (C ^ 2) (Filter.Eventually.of_forall fun q => by
      rw [norm_pow, norm_norm]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb q) 2)
  have h2 := (integral_eq_zero_iff_of_nonneg (fun q => sq_nonneg _) hi).1 h1
  have h3 := QuasiMeasurePreserving.ae_eq_comp (RightCosetSpace.quasiMeasurePreserving_mk (Reduction.rationalGLOne (K := E) (n := n)) μ) h2
  have h4 := (Continuous.ae_eq_iff_eq μ (f := fun y : Reduction.normOneGL (K := E) (n := n) => ‖F y‖ ^ 2)
    ((hc.comp continuous_subtype_val).norm.pow 2) continuous_const).1 h3
  intro y hy
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 (congrFun h4 ⟨y, hy⟩))

theorem UpperTheory.V.Af.Smo.orthConv :
    UpperTheory.V.Af.Smo.OrthStep → UpperTheory.V.Af.Smo.ConvCont → UpperTheory.V.Af.Smo.OrthConv := by
  intro hS hC E _ _ _ n μ _ φ φ' hφ hφ' ho β β' e
  obtain ⟨C, hb⟩ := exists_norm_le_of_mem_centralCuspForms hφ
  obtain ⟨C', hb'⟩ := exists_norm_le_of_mem_centralCuspForms hφ'
  have l : IsLeftInvariant (Af.Smo.conv φ.1 β) := fun γ g => conv_left _ _ _ (φ.2.1.isLeftInvariant γ) g
  have l' : IsLeftInvariant (Af.Smo.conv φ'.1 β') := fun γ g => conv_left _ _ _ (φ'.2.1.isLeftInvariant γ) g
  obtain ⟨hc, D, hD⟩ := hC E n φ'.1 φ'.2.1.continuous ⟨C', hb'⟩ β'
  have s1 : ∀ g, ∫ q, starRingEnd ℂ (quotTr φ g q) * CuspidalSpectrum.cuspQuot l' q
      ∂(RightCosetSpace.quotientMeasure (Reduction.rationalGLOne (K := E) (n := n)) μ) = 0 := fun g =>
    hS E n μ φ'.1 φ'.2.1.continuous ⟨C', hb'⟩ φ'.2.1.isLeftInvariant (fun q => starRingEnd ℂ (quotTr φ g q))
      (Complex.continuous_conj.comp (continuous_quotTr φ g))
      ⟨C, fun q => by
        obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
        rw [Complex.norm_conj]
        exact hb _⟩
      (fun g' _ => ho g g') β' l'
  have s2 := hS E n μ φ.1 φ.2.1.continuous ⟨C, hb⟩ φ.2.1.isLeftInvariant
    (fun q => starRingEnd ℂ (CuspidalSpectrum.cuspQuot l' q))
    (Complex.continuous_conj.comp (CuspidalSpectrum.continuous_cuspQuot l' hc))
    ⟨D, fun q => by
      obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
      rw [Complex.norm_conj]
      exact hD _⟩
    (fun g _ => by
      have h := congrArg (starRingEnd ℂ) (s1 g)
      rw [← integral_conj, map_zero] at h
      refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)) h
      simp only [map_mul, Complex.conj_conj]
      exact mul_comm _ _) β l
  have e' : CuspidalSpectrum.cuspQuot l = CuspidalSpectrum.cuspQuot l' :=
    CuspidalSpectrum.cuspQuot_surj_eq l l' fun y => congrFun e _
  rw [e'] at s2
  have z := zero_of_sq μ _ hc D hD l' s2
  rw [e]
  funext x
  obtain ⟨s, y, hy, rfl⟩ := CuspidalSpectrum.exists_centralSection_mul_mem_normOneGL x
  exact (conv_left _ _ _ (hφ' s) y).trans (z y hy)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.OrthStep
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem sfinite_of_finite {X : Type} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] :
    SFinite ν := inferInstance

theorem UpperTheory.V.Af.Smo.orthStep :
    UpperTheory.V.Af.Smo.ChartCont → UpperTheory.V.Af.Smo.OrthStep := by
  set_option synthInstance.maxHeartbeats 200000 in
    classical
    intro hcc E _ _ _ n μ _ f hf ⟨C, hC⟩ hl a ha ⟨D, hD⟩ h0 β h
    have := Reduction.isFiniteMeasure_quotientMeasure (K := E) (n := n) μ
    generalize RightCosetSpace.quotientMeasure (Reduction.rationalGLOne (K := E) (n := n)) μ = ν at *
    have : SFinite ν := sfinite_of_finite ν
    have : (volume : Measure (Rinf E)).IsAddHaarMeasure := isAddHaarMeasure_volume_pi _
    have : (volume : Measure (Fin n → Rinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
    have : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
    have hr : ∀ g : GA E n, IsLeftInvariant fun x => f (x * g) := fun g γ x => by
      show f (AdelicGLn.diagonal E n γ * x * g) = f (x * g)
      rw [mul_assoc]
      exact hl γ _
    have hF : ∀ x : Lie E n, IsLeftInvariant fun g : GA E n => chart f g x := fun x γ g => by
      show chart f (AdelicGLn.diagonal E n γ * g) x = chart f g x
      unfold chart
      split_ifs with hx
      · exact hr _ γ g
      · rfl
    let F : RightCosetSpace (Reduction.rationalGLOne (K := E) (n := n)) × Lie E n → ℂ := fun z =>
      CuspidalSpectrum.cuspQuot (hF z.2) z.1
    have hFmk : ∀ (y : Reduction.normOneGL (K := E) (n := n)) x,
        F (RightCosetSpace.mk (Reduction.rationalGLOne (K := E) (n := n)) y, x) = chart f y.1 x := fun _ _ => rfl
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
    have hFb : ∀ z, ‖F z‖ ≤ C := by
      rintro ⟨q, x⟩
      obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
      rw [hFmk]
      unfold chart
      split_ifs
      · exact hC _
      · simpa using hC0
    have hF0 : ∀ q x, x ∉ invSet E n → F (q, x) = 0 := by
      intro q x hx
      obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
      rw [hFmk]
      exact dif_neg hx
    have hopen : IsOpen ((Set.univ : Set (RightCosetSpace (Reduction.rationalGLOne (K := E) (n := n)))) ×ˢ invSet E n) :=
      isOpen_univ.prod TR.isOpen_invSet
    have hFc : ContinuousOn F (Set.univ ×ˢ invSet E n) := by
      rintro ⟨q, x⟩ ⟨-, hx⟩
      obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
      have hq := (RightCosetSpace.isOpenQuotientMap_mk (Reduction.rationalGLOne (K := E) (n := n))).prodMap
        (IsOpenQuotientMap.id (X := Lie E n))
      refine ContinuousAt.continuousWithinAt ?_
      refine (hq.continuousAt_comp_iff (g := F) (x := (y, x))).1 ?_
      have h1 : ContinuousAt (fun z : GA E n × Lie E n => chart f z.1 z.2) (y.1, x) :=
        (hcc E n f hf).1.continuousAt ((isOpen_univ.prod TR.isOpen_invSet).mem_nhds ⟨trivial, hx⟩)
      have h2 : Continuous fun z : Reduction.normOneGL (K := E) (n := n) × Lie E n => ((z.1.1, z.2) : GA E n × Lie E n) :=
        (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
      exact ContinuousAt.comp (f := fun z : Reduction.normOneGL (K := E) (n := n) × Lie E n => ((z.1.1, z.2) : GA E n × Lie E n))
        (x := (y, x)) h1 h2.continuousAt
    have hFm : Measurable F := by
      have hc : ContinuousOn F (Set.univ ×ˢ invSet E n)ᶜ :=
        (continuousOn_const (c := (0 : ℂ))).congr fun z hz => hF0 z.1 z.2 fun hx => hz ⟨trivial, hx⟩
      have := hFc.measurable_piecewise hc hopen.measurableSet
      rwa [Set.piecewise_same] at this
    have hint : Integrable (fun z : RightCosetSpace (Reduction.rationalGLOne (K := E) (n := n)) × Lie E n =>
        (a z.1 * F z) * β z.2)
        (ν.prod volume) := by
      have hβ : Integrable (fun z : RightCosetSpace (Reduction.rationalGLOne (K := E) (n := n)) × Lie E n => β z.2)
          (ν.prod volume) :=
        (β.integrable (μ := volume)).comp_snd _
      refine hβ.bdd_mul (c := D * C) (((ha.measurable.comp measurable_fst).mul hFm).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun z => ?_)
      rw [norm_mul]
      exact mul_le_mul (hD _) (hFb _) (norm_nonneg _) ((norm_nonneg _).trans (hD z.1))
    have e1 : ∀ q, a q * CuspidalSpectrum.cuspQuot h q = ∫ x, (a q * F (q, x)) * β x := by
      intro q
      obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
      rw [CuspidalSpectrum.cuspQuot_mk, conv, ← integral_const_mul]
      simp only [hFmk, mul_assoc]
    have e2 : ∀ x, ∫ q, (a q * F (q, x)) * β x ∂ν = 0 := by
      intro x
      rw [integral_mul_const]
      by_cases hx : x ∈ invSet E n
      · have hx' : IsUnit (Matrix.of x) := hx
        have e : ∀ q, F (q, x) = CuspidalSpectrum.cuspQuot (hr (infGL E n hx'.unit)) q := by
          intro q
          obtain ⟨y, rfl⟩ := RightCosetSpace.mk_surjective _ q
          rw [hFmk, CuspidalSpectrum.cuspQuot_mk]
          exact dif_pos hx'
        simp only [e]
        rw [h0, zero_mul]
      · simp [hF0 _ x hx]
    simp only [e1]
    rw [integral_integral_swap (f := fun q x => (a q * F (q, x)) * β x) hint]
    simp only [e2, integral_zero]
end

