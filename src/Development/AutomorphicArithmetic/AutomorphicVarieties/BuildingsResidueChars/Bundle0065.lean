module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.Bundle0002
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.QuadraticSplitting.QuadSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinContinuousLeftAction
section
open UpperTheory.V.Sd.Eis

noncomputable section

open NumberField MeasureTheory Topology Matrix Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private theorem map_aff1 {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (x : R) :
    GeneralLinearGroup.map f (aff 1 x) = aff 1 (f x) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aff]

private theorem aff_one_zero {R : Type} [CommRing R] : aff (1 : Rˣ) (0 : R) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [aff]

private theorem infGL_aff (x : TR.Rinf F) : TR.infGL F 2 (aff 1 x) = aff 1 (TR.sInf F x) := by
  refine TR.ga_ext ?_ ?_
  · rw [TR.pInf_infGL, map_aff1]
    exact congrArg _ ((TR.infEq F).symm_apply_apply x).symm
  · rw [TR.pFin_infGL, map_aff1]
    exact aff_one_zero.symm

private theorem infGL_left (a : GL (Fin 2) (TR.Rinf F)) (g : GA F 2) :
    TR.infGL F 2 a * g = g * TR.infGL F 2 ((GeneralLinearGroup.map (TR.pInf F) g)⁻¹ * a * GeneralLinearGroup.map (TR.pInf F) g) :=
  TR.ga_ext (by simp only [map_mul, map_inv, TR.pInf_infGL]; group) (by simp only [map_mul, map_inv, TR.pFin_infGL]; group)

omit [IsTotallyReal F] in
private theorem conj_deriv (h : GL (Fin 2) (TR.Rinf F)) (a : ℝ → GL (Fin 2) (TR.Rinf F)) (X : Matrix (Fin 2) (Fin 2) (TR.Rinf F))
    (ha : HasDerivAt (fun t => TR.toL (a t).val) (TR.toL X) 0) :
    HasDerivAt (fun t => TR.toL (h⁻¹ * a t * h).val) (TR.toL ((h⁻¹).val * X * h.val)) 0 :=
  ((TR.rmul (TR.toL h.val)).comp (TR.lmul (TR.toL (h⁻¹).val))).hasFDerivAt.comp_hasDerivAt (0 : ℝ) ha

open Classical in
omit [IsTotallyReal F] in
private theorem conj_dec (h : GL (Fin 2) (TR.Rinf F)) (i j : Fin 2) (u : TR.Rinf F) :
    TR.toL ((h⁻¹).val * Matrix.single i j u * h.val) = ∑ v, u v • ∑ a, ∑ b,
      ((((GeneralLinearGroup.map (Pi.evalRingHom (fun _ => ℝ) v) h)⁻¹).val * Matrix.single i j (1 : ℝ) *
        (GeneralLinearGroup.map (Pi.evalRingHom (fun _ => ℝ) v) h).val) a b : ℝ) •
          TR.toL (Matrix.single a b (Pi.single v 1 : TR.Rinf F)) := by
  funext a b w
  simp only [← map_inv]
  generalize h⁻¹ = h'
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.single_apply, Fin.sum_univ_two, Pi.single_apply, Finset.sum_apply] <;> ring

omit [IsTotallyReal F] in
private theorem nil_curve (u : TR.Rinf F) :
    Continuous (fun t : ℝ => aff (1 : (TR.Rinf F)ˣ) (t • u)) ∧
    (∀ s t : ℝ, aff (1 : (TR.Rinf F)ˣ) ((s + t) • u) = aff 1 (s • u) * aff 1 (t • u)) ∧
    HasDerivAt (fun t : ℝ => TR.toL (aff (1 : (TR.Rinf F)ˣ) (t • u)).val) (TR.toL (Matrix.single 0 1 u)) 0 := by
  refine ⟨Units.continuous_iff.2 ⟨?_, ?_⟩, fun s t => ?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff, -Matrix.coe_units_inv] <;> fun_prop
  · ext i j : 2
    fin_cases i <;> fin_cases j <;> simp [aff, add_smul, add_comm]
  · refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff, hasDerivAt_const]
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const u

omit [IsTotallyReal F] in
private theorem tor_curve (u : TR.Rinf F) (y : ℝ → (TR.Rinf F)ˣ) (hy : ∀ t v, (y t).val v = Real.exp (t * u v)) :
    Continuous (fun t : ℝ => aff (y t) 0) ∧
    (∀ s t : ℝ, aff (y (s + t)) 0 = aff (y s) 0 * aff (y t) 0) ∧
    HasDerivAt (fun t : ℝ => TR.toL (aff (y t) 0).val) (TR.toL (Matrix.single 0 0 u)) 0 := by
  have e : ∀ t, (y t).val = fun v => Real.exp (t * u v) := fun t => funext (hy t)
  have e' : ∀ t, ((y t)⁻¹).val = fun v => Real.exp (-(t * u v)) := fun t =>
    Units.inv_eq_of_mul_eq_one_right (by funext v; simp [hy, ← Real.exp_add])
  refine ⟨Units.continuous_iff.2 ⟨?_, ?_⟩, fun s t => ?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff, e] <;> fun_prop
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff, -Matrix.coe_units_inv, e'] <;> fun_prop
  · ext i j v
    fin_cases i <;> fin_cases j <;> simp [aff, hy, add_mul, Real.exp_add]
  · refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [aff, hasDerivAt_const]
    refine hasDerivAt_pi.2 fun v => ?_
    simpa [hy] using ((hasDerivAt_id (0 : ℝ)).mul_const (u v)).exp

theorem UpperTheory.eisenstein_continuous_left_action :
    UpperTheory.V.Sd.Eis.SmCont → UpperTheory.V.Sd.Eis.CtBasic → UpperTheory.V.Sd.Eis.CtLie → UpperTheory.V.Sd.Eis.LieAlg → UpperTheory.V.Sd.Eis.CentLie → UpperTheory.V.Sd.Eis.CtLeft := by
  intro hS hB hL hA hC F _ _ _ _ _ μ _ D hD k c ω hω φ hφ u y hy g
  classical
  have hl := hL F μ D hD φ hφ.aut.left hφ.aut.level
  have hb := hB F μ D hD φ.1 (hS F 2 φ hφ.aut.level) hφ.aut.left
  have hi : ∀ X, IntegrableOn (fun x : NA F => (TR.lie F 2 X φ).1 (unip x * g)) D μ := fun X =>
    (hB F μ D hD _ (hl X).1.2 (hl X).1.1).1 g
  let L : TR.Lie F 2 →ₗ[ℝ] ℂ :=
    { toFun := fun X => cterm μ D (TR.lie F 2 X φ).1 g
      map_add' := fun X Y => by
        rw [map_add (f := _)]
        exact integral_add (hi X) (hi Y)
      map_smul' := fun r X => by
        rw [map_smul]
        exact integral_smul r (fun x : NA F => (TR.lie F 2 X φ).1 (unip x * g)) }
  have hsm : ∀ (X) (z : ℂ) (ψ : TR.Sm F 2), TR.lie F 2 X φ = z • ψ → L X = z * cterm μ D ψ.1 g := fun X z ψ e => by
    change cterm μ D (TR.lie F 2 X φ).1 g = _
    rw [e]
    exact integral_const_mul z (fun x : NA F => ψ.1 (unip x * g))
  set h := GeneralLinearGroup.map (TR.pInf F) g with hh
  have key : ∀ (a : ℝ → GL (Fin 2) (TR.Rinf F)) (X : Matrix (Fin 2) (Fin 2) (TR.Rinf F)), Continuous a →
      (∀ s t, a (s + t) = a s * a t) → HasDerivAt (fun t => TR.toL (a t).val) (TR.toL X) 0 →
      HasDerivAt (fun t => cterm μ D φ.1 (TR.infGL F 2 (a t) * g)) (L (TR.toL ((h⁻¹).val * X * h.val))) 0 := by
    intro a X h1 h2 h3
    simp only [infGL_left _ g]
    exact (hl _).2 (fun t => h⁻¹ * a t * h) (by fun_prop) (fun s t => by rw [h2]; group) (conj_deriv h a X h3) g
  have hnil : ∀ x : TR.Rinf F, L (TR.toL ((h⁻¹).val * Matrix.single 0 1 x * h.val)) = 0 := fun x => by
    obtain ⟨h1, h2, h3⟩ := nil_curve x
    have := key _ _ h1 h2 h3
    simp only [infGL_aff, hb.2.1] at this
    exact this.unique (hasDerivAt_const _ _)
  let E : InfinitePlace F → Fin 2 → Fin 2 → TR.Lie F 2 := fun v a b => TR.toL (Matrix.single a b (Pi.single v 1 : TR.Rinf F))
  have hE : ∀ v a b, TR.lie F 2 (E v a b) = TR.Eop v a b := fun _ _ _ => by
    simp only [E, TR.Eop]
  have hdec : ∀ (i j : Fin 2) (x : TR.Rinf F), L (TR.toL ((h⁻¹).val * Matrix.single i j x * h.val)) =
      ∑ v, (x v : ℂ) * ∑ a, ∑ b,
      ((((GeneralLinearGroup.map (Pi.evalRingHom (fun _ => ℝ) v) h)⁻¹).val * Matrix.single i j (1 : ℝ) *
        (GeneralLinearGroup.map (Pi.evalRingHom (fun _ => ℝ) v) h).val) a b : ℝ) * L (E v a b) := fun i j x => by
    rw [conj_dec]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Complex.real_smul, E]
  have hv := fun v : InfinitePlace F => hA (GeneralLinearGroup.map (Pi.evalRingHom (fun _ => ℝ) v) h) (fun a b => L (E v a b))
    (k * cterm μ D φ.1 g)
    (by
      rw [← map_add (f := _), hsm _ 0 φ, zero_mul]
      rw [map_add (f := _), hE, hE, zero_smul]
      exact hC F k c ω hω φ hφ v)
    (by
      rw [← map_sub, hsm _ (Complex.I * k) φ, mul_assoc]
      rw [map_sub, hE, hE]
      exact hφ.wt v)
    (by
      rw [← map_sub, ← map_add (f := _), hsm _ Complex.I (TR.lie F 2 (E v 0 1 + E v 1 0) φ)]
      · rfl
      rw [map_sub, map_add (f := _), hE, hE, hE, hE]
      exact hφ.low v)
    (by
      have := hnil (Pi.single v 1)
      rw [hdec, Finset.sum_eq_single v (fun w _ hw => by simp [Pi.single_eq_of_ne hw]) (by simp)] at this
      simpa only [Pi.single_eq_same, Complex.ofReal_one, one_mul] using this)
  obtain ⟨h1, h2, h3⟩ := tor_curve u y hy
  have := key _ _ h1 h2 h3
  rw [hdec] at this
  simp only [hv] at this
  convert this using 1
  rw [← Finset.sum_mul]
  push_cast
  ring
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinPeriodDerivative
section
open UpperTheory.V.Sd.Eis

private theorem UpperTheory.exists_bound_of_continuous_periodic_cocompact (A : Type) [AddCommGroup A] [TopologicalSpace A] (Γ : AddSubgroup A)
    (hC : Cocpt Γ) (g : A → ℝ → ℂ) (hg : Continuous (Function.uncurry g))
    (hgp : ∀ γ ∈ Γ, ∀ (x : A), g (γ + x) = g x) :
    ∃ M : ℝ, ∀ x : A, ∀ t ∈ Set.Icc (-1 : ℝ) 1, ‖g x t‖ ≤ M := by
  obtain ⟨C, hCc, hCx⟩ := hC
  have hK : IsCompact (C ×ˢ Set.Icc (-1 : ℝ) 1) := hCc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨M, fun x t ht => ?_⟩
  obtain ⟨γ, hγ, hxγ⟩ := hCx x
  have h1 : g x = g (x - γ) := by
    have := hgp γ hγ (x - γ)
    rw [add_sub_cancel] at this
    exact this
  rw [h1]
  exact hM (x - γ, t) ⟨hxγ, ht⟩

theorem UpperTheory.eisenstein_period_derivative :
    UpperTheory.V.Sd.Eis.PerDeriv := by
  intro A _ _ _ _ _ _ Γ hC μ D hDt f f' hf hf' hfp hf'p hd
  obtain ⟨M, hM⟩ := UpperTheory.exists_bound_of_continuous_periodic_cocompact A Γ hC f' hf' hf'p
  obtain ⟨N, hN⟩ := UpperTheory.exists_bound_of_continuous_periodic_cocompact A Γ hC f hf hfp
  have hslice : ∀ (g : A → ℝ → ℂ), Continuous (Function.uncurry g) → ∀ t : ℝ, Continuous (fun x => g x t) :=
    fun g hg t => hg.comp (continuous_id.prodMk continuous_const)
  haveI hfin : MeasureTheory.IsFiniteMeasure (μ.restrict D) := MeasureTheory.isFiniteMeasure_restrict.2 hDt
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict D)
    (F := fun t x => f x t) (F' := fun t x => f' x t) (x₀ := (0 : ℝ)) (bound := fun _ => M)
    (Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1))
    (Filter.Eventually.of_forall fun t => (hslice f hf t).aestronglyMeasurable)
    (MeasureTheory.Measure.integrableOn_of_bounded (M := N) hDt (hslice f hf 0).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => hN x 0 ⟨by norm_num, by norm_num⟩))
    (hslice f' hf' 0).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x t ht => hM x t ht)
    (MeasureTheory.integrable_const M)
    (Filter.Eventually.of_forall fun x t _ => hd x t)
  exact key.2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.EisensteinSmoothContinuous
section
open UpperTheory.V.Sd.Eis
open NumberField Topology Matrix Neutral.B1 GlobalTheory.CuspRep Formalism.L2.Host UpperTheory.V

private theorem cont_map {R S : Type} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    (a : ℕ) (f : R →+* S) (hf : Continuous f) :
    Continuous (fun g : GL (Fin a) R => GeneralLinearGroup.map f g) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · exact Units.continuous_val.matrix_map hf
  · exact Units.continuous_coe_inv.matrix_map hf

private theorem cont_pInf (F : Type) [Field F] [NumberField F] [IsTotallyReal F] : Continuous (TR.pInf F) := by
  have h : Continuous (TR.infEq F).symm :=
    continuous_pi fun w =>
      (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
        (continuous_apply w)
  exact h.comp continuous_fst

theorem UpperTheory.eisenstein_smooth_continuous :
    UpperTheory.V.Sd.Eis.SmCont := by
  intro F _ _ _ a φ hU
  have hy := cont_map a (TR.pInf F) (cont_pInf F)
  have hk := cont_map a (pFin F) continuous_snd
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  set k₀ := GeneralLinearGroup.map (pFin F) g₀ with hk₀
  have hy' : Continuous fun g : GA F a => TR.toL (GeneralLinearGroup.map (TR.pInf F) g).val :=
    (Units.continuous_val (M := Matrix (Fin a) (Fin a) (TR.Rinf F))).comp hy
  have hc : ContinuousAt (fun g : GA F a =>
      TR.chart φ.1 (finGL F a k₀) (TR.toL (GeneralLinearGroup.map (TR.pInf F) g).val)) g₀ :=
    ContinuousAt.comp (f := fun g : GA F a => TR.toL (GeneralLinearGroup.map (TR.pInf F) g).val)
      (TR.contDiffAt_chart φ.2 _ (TR.val_mem_invSet _)).continuousAt hy'.continuousAt
  refine hc.congr ?_
  have hk' : Continuous fun g : GA F a => k₀⁻¹ * GeneralLinearGroup.map (pFin F) g :=
    continuous_const.mul hk
  have hn : ∀ᶠ g : GA F a in 𝓝 g₀, TR.finRep F a (k₀⁻¹ * GeneralLinearGroup.map (pFin F) g) φ = φ := by
    refine (hU.preimage hk').mem_nhds ?_
    change TR.finRep F a (k₀⁻¹ * k₀) φ = φ
    rw [inv_mul_cancel, map_one]; rfl
  filter_upwards [hn] with g hg
  rw [TR.chart_val]
  have e := congrFun (congrArg Subtype.val hg) (finGL F a k₀ * TR.infGL F a (GeneralLinearGroup.map (TR.pInf F) g))
  rw [← e]
  change φ.1 (_ * finGL F a _) = _
  rw [← TR.infGL_comm, mul_assoc, ← map_mul, mul_inv_cancel_left, TR.infGL_mul_finGL]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsCharacterSeparation
section
open UpperTheory.V.Sd.Eis

private theorem exists_addChar_fourier_coeff_ne_zero_of_ne_zero {α : Type} [AddCommGroup α] [Fintype α] (F : α → ℂ) (hF : F ≠ 0) :
    ∃ ψ : AddChar α ℂ, ∑ a, F a * ψ (-a) ≠ 0 := by
  classical
  by_contra h
  push_neg at h
  apply hF
  funext x
  have key : ∑ ψ : AddChar α ℂ, ∑ a, F a * ψ (x - a) = (Fintype.card α : ℂ) * F x := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, AddChar.sum_apply_eq_ite, sub_eq_zero]
    rw [Finset.sum_eq_single x]
    · simp [mul_comm]
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  have key2 : ∑ ψ : AddChar α ℂ, ∑ a, F a * ψ (x - a) = 0 := by
    apply Finset.sum_eq_zero
    intro ψ _
    simp_rw [sub_eq_add_neg, AddChar.map_add_eq_mul, mul_left_comm (F _), ← Finset.mul_sum, h ψ,
      mul_zero]
  have hc : (Fintype.card α : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have := key.symm.trans key2
  simpa [hc] using this

theorem UpperTheory.exists_character_separation :
    UpperTheory.V.Sd.Eis.CharPick := by
  intro T _ U₀ hU₀ f₀ hf₀ hinv
  classical
  have inv_out : ∀ (V : Subgroup T) (w : T → ℂ), (∀ t u, u ∈ V → w (t * u) = w t) →
      ∀ t : T, w ((QuotientGroup.mk t : T ⧸ V).out) = w t := by
    intro V w hw t
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul V t
    rw [hh, hw _ _ h.2]
  haveI : Fintype (T ⧸ U₀) := Fintype.ofFinite _
  let F : Additive (T ⧸ U₀) → ℂ := fun a => f₀ (Additive.toMul a).out
  have hF : F ≠ 0 := by
    obtain ⟨t, ht⟩ := Function.ne_iff.mp hf₀
    intro h0
    apply ht
    have := congrFun h0 (Additive.ofMul (QuotientGroup.mk t))
    simp only [F, toMul_ofMul, Pi.zero_apply] at this
    rw [inv_out U₀ f₀ hinv t] at this
    exact this
  obtain ⟨ψ, hψ⟩ := exists_addChar_fourier_coeff_ne_zero_of_ne_zero F hF
  let χ : T →* ℂˣ :=
    { toFun := fun t => ⟨ψ (Additive.ofMul (QuotientGroup.mk t : T ⧸ U₀)),
        ψ (-(Additive.ofMul (QuotientGroup.mk t : T ⧸ U₀))),
        by rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one],
        by rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]⟩
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp [AddChar.map_add_eq_mul] }
  have hχval : ∀ t, (((χ t)⁻¹ : ℂˣ) : ℂ) = ψ (-(Additive.ofMul (QuotientGroup.mk t : T ⧸ U₀))) :=
    fun t => rfl
  have hχU₀ : ∀ u ∈ U₀, χ u = 1 := by
    intro u hu
    ext
    simp [χ, (QuotientGroup.eq_one_iff u).mpr hu]
  let aV : Subgroup T → (T → ℂ) → ℂ := fun V h =>
    ∑ᶠ q : T ⧸ V, h q.out * (((χ q.out)⁻¹ : ℂˣ) : ℂ)
  have aV_lin : ∀ V : Subgroup T, V.FiniteIndex → ∀ (c : ℂ) (p p' : T → ℂ),
      aV V (c • p + p') = c * aV V p + aV V p' := by
    intro V hV c p p'
    haveI := hV
    haveI : Fintype (T ⧸ V) := Fintype.ofFinite _
    simp only [aV, finsum_eq_sum_of_fintype, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
      Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  have aV_zero : ∀ V : Subgroup T, aV V 0 = 0 := by
    intro V; simp [aV]
  have kill : ∀ V : Subgroup T, V.FiniteIndex → V ≤ U₀ → ∀ g : T → ℂ,
      (∀ t u, u ∈ V → g (t * u) = g t) → ∀ s, aV V (fun t => g (t * s)) = (χ s : ℂ) * aV V g := by
    intro V hV hVU g hg s
    haveI := hV
    haveI : Fintype (T ⧸ V) := Fintype.ofFinite _
    let φ : T → ℂ := fun t => g t * (((χ t)⁻¹ : ℂˣ) : ℂ)
    have hφ : ∀ t u, u ∈ V → φ (t * u) = φ t := by
      intro t u hu
      simp only [φ, map_mul, hχU₀ u (hVU hu), mul_one, hg t u hu]
    simp only [aV, finsum_eq_sum_of_fintype]
    have hre : ∑ q : T ⧸ V, g q.out * (((χ q.out)⁻¹ : ℂˣ) : ℂ)
        = ∑ q : T ⧸ V, g (q * (QuotientGroup.mk s : T ⧸ V)).out
            * (((χ (q * (QuotientGroup.mk s : T ⧸ V)).out)⁻¹ : ℂˣ) : ℂ) :=
      (Equiv.sum_comp (Equiv.mulRight (QuotientGroup.mk s : T ⧸ V))
        (fun q => g q.out * (((χ q.out)⁻¹ : ℂˣ) : ℂ))).symm
    rw [hre, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    have hq : q * (QuotientGroup.mk s : T ⧸ V) = QuotientGroup.mk (q.out * s) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
    have h2 := inv_out V φ hφ (q.out * s)
    rw [hq]
    change _ = _ * φ _
    rw [h2]
    simp only [φ, map_mul, mul_inv, Units.val_mul]
    have hs1 : (χ s : ℂ) * (((χ s)⁻¹ : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    linear_combination (-(g (q.out * s) * (((χ q.out)⁻¹ : ℂˣ) : ℂ))) * hs1
  have fiber : ∀ V : Subgroup T, V ≤ U₀ → V.FiniteIndex → aV V f₀ ≠ 0 := by
    intro V hVU hV
    haveI := hV
    haveI : Fintype (T ⧸ V) := Fintype.ofFinite _
    let π : T ⧸ V →* T ⧸ U₀ := QuotientGroup.map V U₀ (MonoidHom.id T) (fun x hx => hVU hx)
    let φ0 : T → ℂ := fun t => f₀ t * (((χ t)⁻¹ : ℂˣ) : ℂ)
    have hφ0 : ∀ t u, u ∈ U₀ → φ0 (t * u) = φ0 t := by
      intro t u hu
      simp only [φ0, map_mul, hχU₀ u hu, mul_one, hinv t u hu]
    let Kf : T ⧸ U₀ → ℂ := fun r => φ0 r.out
    have hH : ∀ q : T ⧸ V, f₀ q.out * (((χ q.out)⁻¹ : ℂˣ) : ℂ) = Kf (π q) := by
      intro q
      have : π q = QuotientGroup.mk q.out := by
        conv_lhs => rw [← QuotientGroup.out_eq' q]
        rfl
      rw [this]
      exact (inv_out U₀ φ0 hφ0 q.out).symm
    have hsurj : ∀ r : T ⧸ U₀, r ∈ Set.range π := by
      intro r
      refine ⟨QuotientGroup.mk r.out, ?_⟩
      change (QuotientGroup.mk r.out : T ⧸ U₀) = r
      exact QuotientGroup.out_eq' r
    have hcard : ∀ r : T ⧸ U₀, (Finset.univ.filter fun q => π q = r).card
        = (Finset.univ.filter fun q => π q = 1).card :=
      fun r => MonoidHom.card_fiber_eq_of_mem_range π (hsurj r) (hsurj 1)
    have hpos : (Finset.univ.filter fun q => π q = 1).card ≠ 0 := by
      rw [Finset.card_ne_zero]
      exact ⟨1, by simp⟩
    have hsumK : ∑ r, Kf r ≠ 0 := by
      have e : ∑ r, Kf r = ∑ a, F a * ψ (-a) := by
        refine Fintype.sum_equiv Additive.ofMul _ _ (fun r => ?_)
        simp only [Kf, φ0, F, hχval, QuotientGroup.out_eq', toMul_ofMul]
      rw [e]; exact hψ
    simp only [aV, finsum_eq_sum_of_fintype, hH]
    rw [← Finset.sum_fiberwise' Finset.univ π Kf]
    simp only [Finset.sum_const, hcard, nsmul_eq_mul, ← Finset.mul_sum]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hpos) hsumK
  let Kset : Set (T → ℂ) := {p | ∃ (U : Subgroup T) (g : T → ℂ) (s : T), U.FiniteIndex ∧
      (∀ t u, u ∈ U → g (t * u) = g t) ∧ p = (fun t => g (t * s)) - (χ s : ℂ) • g}
  have key : ∀ p : T → ℂ, p ∈ Submodule.span ℂ Kset → ∃ V : Subgroup T, V ≤ U₀ ∧ V.FiniteIndex ∧
      ∀ V' : Subgroup T, V' ≤ V → V'.FiniteIndex → aV V' p = 0 := by
    intro p hmem
    induction hmem using Submodule.span_induction with
    | mem p hp =>
      obtain ⟨U, g, s, hU, hg, rfl⟩ := hp
      haveI := hU
      haveI := hU₀
      refine ⟨U ⊓ U₀, inf_le_right, inferInstance, fun V' hV' hV'f => ?_⟩
      have hg' : ∀ t u, u ∈ V' → g (t * u) = g t :=
        fun t u hu => hg t u (Subgroup.mem_inf.mp (hV' hu)).1
      have e : (fun t => g (t * s)) - (χ s : ℂ) • g = (-(χ s : ℂ)) • g + (fun t => g (t * s)) := by
        funext t; simp; ring
      rw [e, aV_lin V' hV'f, kill V' hV'f (hV'.trans inf_le_right) g hg' s]
      ring
    | zero => exact ⟨U₀, le_rfl, hU₀, fun V' _ _ => aV_zero V'⟩
    | add x y _ _ hx hy =>
      obtain ⟨V1, hV1U, hV1f, hV1⟩ := hx
      obtain ⟨V2, hV2U, hV2f, hV2⟩ := hy
      haveI := hV1f
      haveI := hV2f
      refine ⟨V1 ⊓ V2, inf_le_left.trans hV1U, inferInstance, fun V' hV' hV'f => ?_⟩
      have := aV_lin V' hV'f 1 x y
      rw [one_smul, one_mul] at this
      rw [this, hV1 V' (hV'.trans inf_le_left) hV'f, hV2 V' (hV'.trans inf_le_right) hV'f, add_zero]
    | smul c x _ hx =>
      obtain ⟨V1, hV1U, hV1f, hV1⟩ := hx
      refine ⟨V1, hV1U, hV1f, fun V' hV' hV'f => ?_⟩
      have := aV_lin V' hV'f c x 0
      rw [add_zero, aV_zero, add_zero] at this
      rw [this, hV1 V' hV' hV'f, mul_zero]
  have hnot : f₀ ∉ Submodule.span ℂ Kset := by
    intro hmem
    obtain ⟨V, hVU, hVf, hV⟩ := key f₀ hmem
    exact fiber V hVU hVf (hV V le_rfl hVf)
  obtain ⟨L, hL, hLK⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  refine ⟨χ, L, hχU₀, hL, ?_⟩
  intro U hU f hf s
  have hmemK : (fun t => f (t * s)) - (χ s : ℂ) • f ∈ Submodule.span ℂ Kset :=
    Submodule.subset_span ⟨U, f, s, hU, hf, rfl⟩
  have h0 : L ((fun t => f (t * s)) - (χ s : ℂ) • f) = 0 := by
    have := Submodule.mem_map_of_mem (f := L) hmemK
    rw [hLK, Submodule.mem_bot] at this
    exact this
  rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h0
  exact h0
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsRibetLattice
section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S2

theorem UpperTheory.exists_ribet_lattice :
    UpperTheory.V.Sd.S2.RibOf := by
  intro Ω _ _ _ l _ c D T k₀ _ _ φ ι k t r hyp hch hd u hu
  haveI : IsAlgClosure k₀ Ω := ⟨IsAlgClosure.isAlgClosed ℚ, inferInstance⟩
  haveI : IsGalois k₀ Ω := {}
  have hc : Continuous (resQ k₀ : G k₀ Ω →* G ℚ Ω) := by
    have h := (galEmbTop ℚ k₀ Ω).1.continuous
    have e : (resQ k₀ : G k₀ Ω →* G ℚ Ω) = galEmb ℚ k₀ Ω := by
      ext σ x
      rw [galEmb_apply]; rfl
    rw [e]; exact h
  let H : Subgroup (G k₀ Ω) := T.F.fixingSubgroup.comap (resQ k₀)
  have hHo : IsOpen (H : Set (G k₀ Ω)) := T.F.fixingSubgroup_isOpen.preimage hc
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 (H.isClosed_of_isOpen hHo).isCompact
  have hg : resQ T.F T.g0 ∈ T.F.fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact T.g0.commutes ⟨x, hx⟩
  have huH : u ∈ H := by
    show resQ k₀ u ∈ T.F.fixingSubgroup
    rw [hu]; exact mul_mem hg hg
  obtain ⟨ρ', ⟨g, hρ⟩, q1, q2, q3, s, q4⟩ := ribetLat l H (r.comp H.subtype) 1 (((up D.ξ).comp (resQ k₀)).comp H.subtype)
    (hd.cont.comp continuous_subtype_val) (hd.irr H hHo) (fun s => ⟨by simp, hch.unit _ _⟩)
    (fun s i => by
      have := hd.res s i
      simpa only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, MonoidHom.comp_apply, MonoidHom.one_apply,
        Subgroup.coe_subtype] using this) ⟨u, huH⟩ (by
      have := hch.sq
      rw [← hu] at this
      exact this)
  have e : ∀ s : H, ((MulAut.conj g).toMonoidHom.comp r) s = ρ' s := fun s => (hρ s).symm
  refine ⟨(MulAut.conj g).toMonoidHom.comp r, ⟨g, fun _ => rfl⟩, ?_, ?_, fun h hh => ?_, s, s.2, ?_⟩
  · rw [e ⟨u, huH⟩]; exact q1
  · rw [e ⟨u, huH⟩]; exact q2
  · rw [e ⟨h, hh⟩]; exact q3 ⟨h, hh⟩
  · rw [e s]; exact q4
end

