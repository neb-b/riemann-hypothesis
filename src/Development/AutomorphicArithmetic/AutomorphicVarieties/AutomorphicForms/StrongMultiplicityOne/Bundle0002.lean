module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.StrongMultOneC

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.ConvCont
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

theorem UpperTheory.V.Af.StrongMultiplicityOne.convCont :
    UpperTheory.V.Af.StrongMultiplicityOne.ChartCont → UpperTheory.V.Af.StrongMultiplicityOne.ConvCont := by
  intro hc E _ _ _ n f hf hb α
  obtain ⟨C, hC⟩ := hb
  obtain ⟨h1, h2⟩ := hc E n f hf
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
  have hch : ∀ g x, ‖chart f g x‖ ≤ C := by
    intro g x
    unfold GlobalTheory.CuspRep.chart
    split_ifs
    · exact hC _
    · simpa using hC0
  have hbd : ∀ g x, ‖chart f g x * α x‖ ≤ C * ‖α x‖ := by
    intro g x
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hch g x) (norm_nonneg _)
  haveI i1 : (volume : Measure (Cinf E)).IsAddHaarMeasure := inferInstance
  haveI i2 : (volume : Measure (Fin n → Cinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI i3 : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hint : Integrable (fun x => C * ‖α x‖) := (α.integrable.norm).const_mul C
  haveI : FirstCountableTopology (GA E n) :=
    GroundTheory.Automorphic.FourierWhittaker.firstCountableTopology_adelicGL ..
  refine ⟨?_, ∫ x, C * ‖α x‖, fun g => ?_⟩
  · unfold conv
    refine continuous_of_dominated (bound := fun x => C * ‖α x‖) (fun g => ?_) (fun g => ?_) hint ?_
    · exact ((h2 g).mul α.continuous.measurable).aestronglyMeasurable
    · exact Filter.Eventually.of_forall (hbd g)
    · refine Filter.Eventually.of_forall fun x => ?_
      refine Continuous.mul ?_ continuous_const
      by_cases hx : x ∈ invSet E n
      · exact h1.comp_continuous (f := fun g : GA E n => (g, x)) (by fun_prop) fun g => ⟨Set.mem_univ _, hx⟩
      · have : (fun g => chart f g x) = fun _ => 0 := by
          funext g
          unfold GlobalTheory.CuspRep.chart
          exact dif_neg hx
        rw [this]
        exact continuous_const
  · exact norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall (hbd g))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.ConvFub
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

theorem UpperTheory.V.Af.StrongMultiplicityOne.convFub :
    UpperTheory.V.Af.StrongMultiplicityOne.ChartCont → UpperTheory.V.Af.StrongMultiplicityOne.ConvFub := by
  classical
  intro hc E _ _ _ n f hf ⟨C, hC⟩ α X _ _ _ _ ν _ u a hu ha ⟨D, hD⟩ g
  have hS : MeasurableSet ((Set.univ : Set X) ×ˢ invSet E n) :=
    (isOpen_univ.prod GlobalTheory.CuspRep.isOpen_invSet).measurableSet
  have h1 : ContinuousOn (fun z : X × Lie E n => chart f (u z.1 * g) z.2) (Set.univ ×ˢ invSet E n) :=
    (hc E n f hf).1.comp (f := fun z : X × Lie E n => (u z.1 * g, z.2))
      (((hu.comp continuous_fst).mul continuous_const).prodMk continuous_snd).continuousOn
      fun z hz => ⟨trivial, hz.2⟩
  have h2 : Measurable fun z : X × Lie E n => chart f (u z.1 * g) z.2 := by
    have := h1.measurable_piecewise (g := fun _ => 0) continuousOn_const hS
    convert this using 1
    funext z
    by_cases hz : z ∈ (Set.univ : Set X) ×ˢ invSet E n
    · rw [Set.piecewise_eq_of_mem _ _ _ hz]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hz, chart]
      exact dif_neg fun h => hz ⟨trivial, h⟩
  have hb : ∀ g y, ‖chart f g y‖ ≤ C := fun g y => by
    unfold chart
    split_ifs
    · exact hC _
    · simpa using (norm_nonneg _).trans (hC 1)
  haveI : (volume : Measure (Fin n → Cinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hα : Integrable (fun y => α y) (volume : Measure (Lie E n)) := α.integrable
  have ha' : Integrable a ν := Integrable.of_bound ha.measurable.aestronglyMeasurable D (.of_forall hD)
  have hi : Integrable (fun z : X × Lie E n => chart f (u z.1 * g) z.2 * (a z.1 * α z.2)) (ν.prod volume) :=
    (ha'.mul_prod hα).bdd_mul h2.aestronglyMeasurable (.of_forall fun z => hb _ _)
  calc ∫ x, conv f α (u x * g) * a x ∂ν
      = ∫ x, (∫ y, chart f (u x * g) y * (a x * α y)) ∂ν := by
        refine integral_congr_ae (.of_forall fun x => ?_)
        simp only [conv]
        rw [← integral_mul_const]
        exact integral_congr_ae (.of_forall fun y => by ring)
    _ = ∫ y, ∫ x, chart f (u x * g) y * (a x * α y) ∂ν := integral_integral_swap hi
    _ = _ := by
        unfold conv
        refine integral_congr_ae (.of_forall fun y => ?_)
        simp only [chart]
        split_ifs with h
        · rw [← integral_mul_const]
          exact integral_congr_ae (.of_forall fun x => by simp only [mul_assoc])
        · simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.ConvNice
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

theorem UpperTheory.V.Af.StrongMultiplicityOne.convNice :
    UpperTheory.V.Af.StrongMultiplicityOne.ConvCont → UpperTheory.V.Af.StrongMultiplicityOne.ConvFub → UpperTheory.V.Af.StrongMultiplicityOne.ConvNice := by
  intro hc hf E _ _ _ n f hN α
  obtain ⟨h1, h2⟩ := hc E n f hN.cont hN.bdd α
  refine ⟨⟨h1, h2, ?_, ?_, ?_⟩, ?_⟩
  · intro γ g
    have e : chart f (AdelicGLn.diagonal E n γ * g) = chart f g := by
      funext x
      simp only [chart, mul_assoc, hN.left γ]
    simp only [conv, e]
  · intro r hr hrn g
    haveI : IsFiniteMeasure ((unipMeasure E n r).restrict (unipFundamentalDomain E n r)) := by
      obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_unipFundamentalDomain (K := E) (n := n) (r := r)
      exact ⟨by
        rw [Measure.restrict_apply_univ]
        exact (measure_mono hDC).trans_lt hC.measure_lt_top⟩
    have h := hf E n f hN.cont hN.bdd α _ ((unipMeasure E n r).restrict (unipFundamentalDomain E n r))
      unipGL (fun _ => 1) continuous_unipGL continuous_const ⟨1, fun _ => by simp⟩ g
    simp only [mul_one] at h
    have e : (fun g' => ∫ x in unipFundamentalDomain E n r, f (unipGL x * g') ∂unipMeasure E n r) = fun _ => 0 :=
      funext fun g' => hN.cusp r hr hrn g'
    rw [constantTerm, h, e]
    simp [conv, chart]
  · obtain ⟨V, hV⟩ := hN.level
    refine ⟨V, fun g v hv => ?_⟩
    have e : (fun x => f (x * finGL E n v)) = f := funext fun x => hV x v hv
    rw [conv, ← GlobalTheory.CuspRep.chart_rt_fin, e, conv]
  · funext g
    haveI : IsFiniteMeasure ((FourierWhittaker.vecMeasure E (FourierWhittaker.Pos n)).restrict
        (FourierWhittaker.vecDomain E (FourierWhittaker.Pos n))) :=
      ⟨by rw [Measure.restrict_apply_univ, FourierWhittaker.vecMeasure_vecDomain]; exact ENNReal.one_lt_top⟩
    exact hf E n f hN.cont hN.bdd α _ ((FourierWhittaker.vecMeasure E (FourierWhittaker.Pos n)).restrict
        (FourierWhittaker.vecDomain E (FourierWhittaker.Pos n))) FourierWhittaker.uGL
      (fun X => (GroundTheory.Global.adelicChar E (-FourierWhittaker.supSum 0 X) : ℂ)) FourierWhittaker.continuous_uGL
      (continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp
        (FourierWhittaker.continuous_supSum 0).neg)) ⟨1, fun _ => (Circle.norm_coe _).le⟩ g
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.CornerIsY
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

private theorem corner_isY {R S : Type} [CommRing R] [CommRing S] {n : ℕ} (m : ℕ) (s : R →ₙ+* S) (y : GL (Fin n) R)
    (h : IsY m y.val) :
    IsY m (GlobalTheory.CuspRep.cornerGL n s y).val ∧ supN (GlobalTheory.CuspRep.cornerGL n s y).val = s (supN y.val) := by
  have e : ∀ i j, (GlobalTheory.CuspRep.cornerGL n s y).val i j =
      (1 : Matrix (Fin n) (Fin n) S) i j - s ((1 : Matrix (Fin n) (Fin n) R) i j) + s (y.val i j) := fun _ _ => rfl
  refine ⟨fun i hi => ⟨?_, fun j hj => ?_⟩, ?_⟩
  · rw [e, (h i hi).1]; simp
  · rw [e, (h i hi).2 j hj, Matrix.one_apply_ne hj.ne', Matrix.one_apply_ne hj.ne']; simp
  · unfold supN
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hij
    · have hne : i ≠ j := fun h' => by subst h'; omega
      rw [e, Matrix.one_apply_ne hne, Matrix.one_apply_ne hne]; simp
    · simp

theorem UpperTheory.V.Af.StrongMultiplicityOne.embY :
    UpperTheory.V.Af.StrongMultiplicityOne.EmbY := by
  intro E _ _ _ n m
  exact ⟨fun w y h => corner_isY m (sLoc E w) y h, fun y h => corner_isY m (sFin E) y h,
    fun y h => corner_isY m (sInf E) y h, fun w => GlobalTheory.CuspRep.CuspSub.continuous_locGL w⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.EigMap
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

section

variable {E : Type} [Field E] [NumberField E] {n : ℕ} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}

private theorem sum_Tj {ϖ : w.adicCompletion E} (hϖ : Formalism.UG.IsUnifV E w ϖ) (j : ℕ) :
    ∃ s : Finset (GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := n)),
      ∀ F : GL (Fin n) (w.adicCompletion E) ⧸ GlobalTheory.LFun.KGL w (n := n) → ℂ,
        ∑ᶠ c, Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j c.out * F c =
          ∑ c ∈ s, Formalism.UG.Tj ℂ n (Formalism.UG.Ov E w) ϖ j c.out * F c := by
  have hf := Formalism.UG.P.finite_support_cosets (Formalism.UG.Final.GLintComm E w n) (GlobalTheory.LFun.Tj_mem_hecke (n := n) hϖ j).2
  refine ⟨hf.toFinset, fun F => finsum_eq_sum_of_support_subset _ fun c hc => ?_⟩
  rw [Set.Finite.coe_toFinset]
  exact left_ne_zero_of_mul hc

private theorem eig_zero (h : B.card = n) : Eig w B (fun _ : GL (Fin n) (w.adicCompletion E) => (0 : ℂ)) :=
  ⟨h, fun _ _ _ => rfl, fun _ _ _ _ _ => by simp⟩

private theorem eig_sub {W W' : GL (Fin n) (w.adicCompletion E) → ℂ} (h : Eig w B W) (h' : Eig w B W') :
    Eig w B (fun y => W y - W' y) := by
  refine ⟨h.card, fun g k hk => by simp only [h.inv g k hk, h'.inv g k hk], fun ϖ hϖ j hj g => ?_⟩
  obtain ⟨s, hs⟩ := sum_Tj (n := n) hϖ j
  have e := h.eig ϖ hϖ j hj g
  have e' := h'.eig ϖ hϖ j hj g
  rw [hs] at e e' ⊢
  simp only [mul_sub, Finset.sum_sub_distrib, e, e']

private theorem eig_int {X : Type} [MeasurableSpace X] (μ : Measure X) (hB : B.card = n)
    (F : X → GL (Fin n) (w.adicCompletion E) → ℂ) (a : X → ℂ) (h : ∀ x, Eig w B (F x))
    (hi : ∀ y, Integrable (fun x => F x y * a x) μ) : Eig w B (fun y => ∫ x, F x y * a x ∂μ) := by
  refine ⟨hB, fun g k hk => by simp only [fun x => (h x).inv g k hk], fun ϖ hϖ j hj g => ?_⟩
  obtain ⟨s, hs⟩ := sum_Tj (n := n) hϖ j
  rw [hs]
  simp only [← integral_const_mul]
  rw [← integral_finsetSum _ fun c _ => (hi _).const_mul _]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have e := (h x).eig ϖ hϖ j hj g
  rw [hs] at e
  simp only [← mul_assoc, ← e, Finset.sum_mul]

end

open GroundTheory.Automorphic.FourierWhittaker in
theorem UpperTheory.V.Af.StrongMultiplicityOne.eigMap :
    UpperTheory.V.Af.StrongMultiplicityOne.ChartCont → UpperTheory.V.Af.StrongMultiplicityOne.EigMap := by
  intro hC E _ _ _ n w B f hf
  refine ⟨fun hN g => ?_, fun hN α g => ?_, fun f' hf' g => eig_sub (hf g) (hf' g)⟩
  · refine eig_int ((vecMeasure E (Pos n)).restrict (vecDomain E (Pos n))) (hf 1).card
      (fun X y => f (uGL X * (g * finGL E n (locGL E n w y))))
      (fun X => (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ)) (fun X => ?_) fun y => ?_
    · simpa only [mul_assoc] using hf (uGL X * g)
    · have hc : Continuous fun X : Pos n → Ad E => f (uGL X * (g * finGL E n (locGL E n w y))) *
          (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) :=
        (hN.cont.comp (continuous_uGL.mul continuous_const)).mul
          (continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp (continuous_supSum 0).neg))
      exact (hc.continuousOn.integrableOn_compact isCompact_closure_vecDomain).mono_set subset_closure
  · refine eig_int volume (hf 1).card (fun x y => chart f (g * finGL E n (locGL E n w y)) x) α (fun x => ?_) fun y => ?_
    · by_cases hx : IsUnit (Matrix.of x)
      · have := hf (g * infGL E n hx.unit)
        simpa only [chart, dif_pos hx, mul_assoc, GlobalTheory.CuspRep.infGL_comm] using this
      · simpa only [chart, dif_neg hx] using eig_zero (w := w) (hf 1).card
    · obtain ⟨C, hC'⟩ := hN.bdd
      haveI : BorelSpace (Lie E n) := inferInstance
      haveI : (volume : Measure (Cinf E)).IsAddHaarMeasure := inferInstance
      haveI : (volume : Measure (Fin n → Cinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
      haveI : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
      refine α.integrable.bdd_mul (c := C) ((hC E n f hN.cont).2 _).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      unfold chart
      split_ifs
      · exact hC' _
      · simpa using (norm_nonneg _).trans (hC' 1)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.EigOfSat
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

theorem UpperTheory.V.Af.StrongMultiplicityOne.eigOfSat :
    UpperTheory.V.Af.StrongMultiplicityOne.EigOfSat := by
  intro E _ _ _ n π w B hB φ hφ hK g
  refine ⟨hB.card, fun y k hk => ?_, fun ϖ hϖ j hj y => ?_⟩
  · rw [map_mul, map_mul, ← mul_assoc, hK _ k hk]
  · by_cases h0 : φ = 0
    · subst h0
      simp
    have he := (hB.2 (⟨φ, hφ⟩ : π.V)
      (GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (Subtype.ext (funext fun x => hK x k hk))) fun h => h0 (congrArg Subtype.val h)).2.2.2 ϖ hϖ j hj
    let ev : π.V →+ ℂ :=
      { toFun := fun ψ => ψ.1.1 (g * finGL E n (locGL E n w y))
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hs := ev.map_finsum (GlobalTheory.LFun.finite_heckeVec (Formalism.UG.Final.GLintComm E w n)
      (GlobalTheory.LFun.Tj_mem_hecke hϖ j) (π.locRep w) ⟨φ, hφ⟩)
    refine Eq.trans (finsum_congr fun c => ?_) (hs.symm.trans (congrArg ev he))
    rw [map_mul, map_mul, ← mul_assoc]
    rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.FinKir
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

private theorem isY_map {R S : Type} [CommRing R] [CommRing S] {n m : ℕ} (f : R →+* S) {k : GL (Fin n) R}
    (h : IsY m k.val) : IsY m (GeneralLinearGroup.map f k).val := by
  intro i hi
  refine ⟨?_, fun j hj => ?_⟩
  · change f (k.val i i) = 1
    rw [(h i hi).1, map_one]
  · change f (k.val i j) = 0
    rw [(h i hi).2 j hj, map_zero]

private theorem isY_one {R : Type} [CommRing R] {n m : ℕ} : IsY m (1 : GL (Fin n) R).val := by
  intro i _
  exact ⟨by simp, fun j hj => by simp [Matrix.one_apply_ne hj.ne']⟩

private theorem isY_of_cmp {E : Type} [Field E] [NumberField E] {n m : ℕ} {k : GL (Fin n) (Af E)}
    (h : ∀ w, IsY m (cmp w k).val) : IsY m k.val := by
  intro i hi
  refine ⟨DFunLike.ext _ _ fun w => ?_, fun j hj => DFunLike.ext _ _ fun w => ?_⟩
  · exact (h w i hi).1
  · exact (h w i hi).2 j hj

private theorem loc_comm {E : Type} [Field E] [NumberField E] {n : ℕ} {w : HeightOneSpectrum (𝓞 E)}
    {k : GL (Fin n) (Af E)} (hk : cmp w k = 1) (y : GL (Fin n) (w.adicCompletion E)) :
    k * locGL E n w y = locGL E n w y * k := by
  refine cmp_ext fun v => ?_
  rw [map_mul, map_mul]
  by_cases hv : v = w
  · subst hv
    rw [hk, one_mul, mul_one]
  · rw [show cmp v (locGL E n w y) = 1 from GlobalTheory.CuspRep.pLoc_locGL_of_ne hv y, one_mul, mul_one]

private theorem supp_mul {E : Type} [Field E] [NumberField E] {n : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))}
    {a b : GL (Fin n) (Af E)} (ha : SuppIn S a) (hb : SuppIn S b) : SuppIn S (a * b) := fun w hw => by
  rw [map_mul, ha w hw, hb w hw, mul_one]

private theorem supp_loc {E : Type} [Field E] [NumberField E] {n : ℕ} {S : Finset (HeightOneSpectrum (𝓞 E))}
    {w : HeightOneSpectrum (𝓞 E)} (hw : w ∈ S) (y : GL (Fin n) (w.adicCompletion E)) :
    SuppIn S (locGL E n w y) := fun v hv =>
  GlobalTheory.CuspRep.pLoc_locGL_of_ne (fun e : v = w => hv (e ▸ hw)) y

private theorem comb_mapDomain {G G' : Type} [Group G] [Group G'] (f : G →* G') (c : G →₀ ℂ) (W : G' → ℂ)
    (g : G') (p : G) : comb (c.mapDomain f) W (g * f p) = comb c (fun y => W (g * f y)) p := by
  unfold comb
  rw [Finsupp.sum_mapDomain_index (by simp) (by intros; ring)]
  simp only [map_mul, mul_assoc]

theorem UpperTheory.V.Af.StrongMultiplicityOne.finKir :
    UpperTheory.V.Af.Smo.LocKir → UpperTheory.V.Af.Smo.PsiLoc → UpperTheory.V.Af.StrongMultiplicityOne.EmbY → UpperTheory.V.Af.StrongMultiplicityOne.FinKir := by
  classical
  intro hK hP hE E _ _ _ n hn S U
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨Finsupp.single 1 1, fun _ => 1, rfl, fun x hx => ?_, fun W _ _ p hp _ => ?_⟩
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hx)]
      exact fun w _ => map_one _
    · obtain rfl : p = 1 := cmp_ext fun w => (hp w (Finset.notMem_empty w)).trans (map_one _).symm
      unfold comb
      rw [Finsupp.sum_single_index (by simp), mul_one]
  | insert w S hw ih =>
    obtain ⟨c₁, H₁, h1, hs₁, hc₁⟩ := ih
    obtain ⟨hE1, -, -, hEc⟩ := hE E n 0
    obtain ⟨c₀, H₀, h0, hc₀⟩ := hK E w (psiL w) ((hP E).1 w).1 ((hP E).1 w).2 n (n - 1) (by omega)
      (U.comap (locGL E n w) (hEc w))
    obtain ⟨c, hs, hc⟩ := exists_comb_comb c₁ (c₀.mapDomain (locGL E n w))
    have mono : ∀ {k : GL (Fin n) (Af E)}, SuppIn S k → SuppIn (insert w S) k :=
      fun hk v hv => hk v fun h => hv (Finset.mem_insert_of_mem h)
    have hl : ∀ y, SuppIn (insert w S) (locGL E n w y) := supp_loc (Finset.mem_insert_self w S)
    refine ⟨c, fun p => H₀ (cmp w p) * H₁ (p * (locGL E n w (cmp w p))⁻¹), ?_, fun x hx => ?_,
      fun W hW hU p hp hY => ?_⟩
    · simp only [map_one, inv_one, mul_one, h0, h1]
    · obtain ⟨a, ha, b, hb, rfl⟩ := hs x hx
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hb)
      exact supp_mul (mono (hs₁ a ha)) (hl y)
    · have key : ∀ g, SuppIn S g → comb (c₀.mapDomain (locGL E n w)) W (g * locGL E n w (cmp w p))
          = H₀ (cmp w p) * W g := by
        intro g hg
        rw [comb_mapDomain, hc₀ (fun y => W (g * locGL E n w y)) ?_ ?_ _ (isY_map _ hY), map_one, mul_one]
        · intro ν hν y
          beta_reduce
          rw [map_mul, ← mul_assoc, loc_comm (hg w hw), mul_assoc,
            hW _ (hl ν) (hE1 w ν hν).1 _ (supp_mul (mono hg) (hl y)), (hE1 w ν hν).2]
          rfl
        · intro y u hu
          beta_reduce
          rw [map_mul, ← mul_assoc]
          exact hU _ (supp_mul (mono hg) (hl y)) _ hu (hl u)
      set p' := p * (locGL E n w (cmp w p))⁻¹ with hp'
      have e0 : cmp w p' = 1 := by
        rw [hp', map_mul, map_inv, show cmp w (locGL E n w (cmp w p)) = cmp w p from GlobalTheory.CuspRep.pLoc_locGL w _,
          mul_inv_cancel]
      have e1 : ∀ v, v ≠ w → cmp v p' = cmp v p := fun v hv => by
        rw [hp', map_mul, map_inv, show cmp v (locGL E n w (cmp w p)) = 1 from GlobalTheory.CuspRep.pLoc_locGL_of_ne hv _,
          inv_one, mul_one]
      have hS : SuppIn S p' := fun v hv => by
        by_cases h : v = w
        · subst h; exact e0
        · rw [e1 v h]
          exact hp v fun h' => (Finset.mem_insert.1 h').elim h hv
      have hY' : IsY (n - 1) p'.val := isY_of_cmp fun v => by
        by_cases h : v = w
        · subst h; rw [e0]; exact isY_one
        · rw [e1 v h]; exact isY_map _ hY
      have ep : p = p' * locGL E n w (cmp w p) := by rw [hp', inv_mul_cancel_right]
      have hI := hc₁ W (fun ν hν hy g hg => hW ν (mono hν) hy g (mono hg))
        (fun g hg u hu hu' => hU g (mono hg) u hu (mono hu')) p' hS hY'
      rw [hc, mul_assoc, ← hI]
      unfold comb at key ⊢
      rw [Finsupp.mul_sum]
      refine Finsupp.sum_congr fun x hx => ?_
      have e2 : p * x = p' * x * locGL E n w (cmp w p) := by
        rw [mul_assoc, loc_comm (hs₁ x hx w hw), ← mul_assoc, ← ep]
      rw [e2, key _ (supp_mul hS (hs₁ x hx))]
      ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.StrongMultiplicityOne.LinChange
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V.Af.Smo hiding psiR conv Cen SameSat ArchStep LinChange ArchKir PsiInf EmbY FinKir ChartCont ConvCont ConvFub ConvNice SeedConv EigMap KillP SphAll Vanish OrthStep OrthConv EigOfSat Seed SetUp Pair CenSame
open GlobalTheory.CuspRep (Cinf Lie chart infGL pInf sInf toL lmul invSet)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology
open UpperTheory.V UpperTheory.V.Af.StrongMultiplicityOne

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

theorem UpperTheory.V.Af.StrongMultiplicityOne.linChange :
    UpperTheory.V.Af.StrongMultiplicityOne.LinChange := by
  intro E _ _ n
  refine ⟨fun s => ((|(LinearMap.det (lmul (toL s.val) : Lie E n →ₗ[ℝ] Lie E n))⁻¹| : ℝ) : ℂ), ?_, fun s f => ?_⟩
  · have : (lmul (toL (1 : GL (Fin n) (Cinf E)).val) : Lie E n →ₗ[ℝ] Lie E n) = LinearMap.id :=
      LinearMap.ext fun x => one_mul (Matrix.of x)
    simp only [this]
    simp
  · haveI : (volume : Measure (Cinf E)).IsAddHaarMeasure := inferInstance
    haveI : (volume : Measure (Fin n → Cinf E)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
    haveI : (volume : Measure (Lie E n)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
    exact linearMap_comp_eq_on_smul_of_eq volume (lmul (toL s.val)) (lmul (toL (s⁻¹).val))
      (fun x => s.inv_mul_cancel_left (Matrix.of x)) (fun x => s.mul_inv_cancel_left (Matrix.of x)) f
end

