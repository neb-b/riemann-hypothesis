module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0003
public import GroundTheory.AutomorphicForms.QuotientMeasure
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.SplitDescentOfImagQuadDescent

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.MeasurableAl
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

noncomputable section

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.TorCoPf

variable {E : Type} [Field E] [NumberField E]

private theorem isClosed_vle {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] [Valued K Γ] :
    IsClosed {p : K × K | (Valued.v p.2 : Γ) ≤ Valued.v p.1} := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro p hp
  have hp' : (Valued.v p.1 : Γ) < Valued.v p.2 := not_le.1 hp
  have hne : (Valued.v p.2 : Γ) ≠ 0 := (lt_of_le_of_lt zero_le' hp').ne'
  have hB : IsOpen {x : K | (Valued.v x : Γ) < Valued.v p.2} := by
    have := Valued.isOpen_ball K (Valued.v.restrict p.2)
    simpa only [Valuation.restrict_lt_iff] using this
  have hN : ({x : K | (Valued.v x : Γ) < Valued.v p.2} ×ˢ {y : K | (Valued.v y : Γ) = Valued.v p.2}) ∈ 𝓝 p :=
    prod_mem_nhds (hB.mem_nhds hp') (Valued.locally_const hne)
  filter_upwards [hN] with q hq
  have h1 : (Valued.v q.1 : Γ) < Valued.v p.2 := hq.1
  have h2 : (Valued.v q.2 : Γ) = Valued.v p.2 := hq.2
  show ¬ (Valued.v q.2 : Γ) ≤ Valued.v q.1
  rw [h2]
  exact not_le.2 h1

private def pI (h : G1 E) (v : InfinitePlace E) : v.Completion :=
  if ‖(h 1 1).1 v‖ ≤ ‖(h 1 0).1 v‖ then (h 1 0).1 v else (h 1 1).1 v

private def pF (h : G1 E) (w : HeightOneSpectrum (𝓞 E)) : w.adicCompletion E :=
  if Valued.v ((h 1 1).2 w) ≤ Valued.v ((h 1 0).2 w) then (h 1 0).2 w else (h 1 1).2 w

private theorem det_eq (h : G1 E) : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
  have := h.2
  rwa [Matrix.det_fin_two] at this

private theorem det_I (h : G1 E) (v : InfinitePlace E) :
    (h 0 0).1 v * (h 1 1).1 v - (h 0 1).1 v * (h 1 0).1 v = 1 :=
  congrArg (fun x : A E => x.1 v) (det_eq h)

private theorem det_F (h : G1 E) (w : HeightOneSpectrum (𝓞 E)) :
    (h 0 0).2 w * (h 1 1).2 w - (h 0 1).2 w * (h 1 0).2 w = 1 :=
  congrArg (fun x : A E => x.2 w) (det_eq h)

private theorem pI_ne (h : G1 E) (v : InfinitePlace E) : pI h v ≠ 0 := by
  unfold pI
  split_ifs with hc
  · intro h0
    rw [h0, norm_zero] at hc
    have hd : (h 1 1).1 v = 0 := norm_le_zero_iff.1 hc
    have := det_I h v
    rw [h0, hd] at this
    simp at this
  · intro h0
    rw [h0, norm_zero] at hc
    exact hc (norm_nonneg _)

private theorem pF_ne (h : G1 E) (w : HeightOneSpectrum (𝓞 E)) : pF h w ≠ 0 := by
  unfold pF
  split_ifs with hc
  · intro h0
    rw [h0, map_zero] at hc
    have hd : (h 1 1).2 w = 0 := (map_eq_zero _).1 (le_zero_iff.1 hc)
    have := det_F h w
    rw [h0, hd] at this
    simp at this
  · intro h0
    rw [h0, map_zero] at hc
    exact hc zero_le'

private theorem pF_one (h : G1 E) : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, Valued.v (pF h w) = 1 := by
  filter_upwards [(h 0 0).2.2, (h 0 1).2.2, (h 1 0).2.2, (h 1 1).2.2] with w ha hb hc hd
  have ha' : Valued.v ((h 0 0).2 w) ≤ 1 := ha
  have hb' : Valued.v ((h 0 1).2 w) ≤ 1 := hb
  have hc' : Valued.v ((h 1 0).2 w) ≤ 1 := hc
  have hd' : Valued.v ((h 1 1).2 w) ≤ 1 := hd
  have hmax : ¬ (Valued.v ((h 1 0).2 w) < 1 ∧ Valued.v ((h 1 1).2 w) < 1) := by
    rintro ⟨h1, h2⟩
    have e1 : Valued.v ((h 0 0).2 w * (h 1 1).2 w) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' ha') h2
    have e2 : Valued.v ((h 0 1).2 w * (h 1 0).2 w) < 1 := by
      rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' hb') h1
    have := Valuation.map_sub_lt _ e1 e2
    rw [det_F h w, map_one] at this
    exact lt_irrefl _ this
  unfold pF
  split_ifs with hle
  · by_contra hne
    exact hmax ⟨lt_of_le_of_ne hc' hne, lt_of_le_of_lt hle (lt_of_le_of_ne hc' hne)⟩
  · by_contra hne
    exact hmax ⟨lt_of_lt_of_le (not_le.1 hle) hd', lt_of_le_of_ne hd' hne⟩

private def bF (h : G1 E) : FiniteAdeleRing (𝓞 E) E :=
  ⟨pF h, (pF_one h).mono fun w hw => (le_of_eq hw : Valued.v (pF h w) ≤ 1)⟩

private def cF (h : G1 E) : FiniteAdeleRing (𝓞 E) E :=
  ⟨fun w => (pF h w)⁻¹, (pF_one h).mono fun w hw =>
    (le_of_eq (by rw [map_inv₀, hw, inv_one]) : Valued.v (pF h w)⁻¹ ≤ 1)⟩

private def al (h : G1 E) : IdeleGroup E where
  val := (fun v => (pI h v)⁻¹, cF h)
  inv := (fun v => pI h v, bF h)
  val_inv := Prod.ext (funext fun v => inv_mul_cancel₀ (pI_ne h v))
    (Subtype.ext <| funext fun w => inv_mul_cancel₀ (pF_ne h w))
  inv_val := Prod.ext (funext fun v => mul_inv_cancel₀ (pI_ne h v))
    (Subtype.ext <| funext fun w => mul_inv_cancel₀ (pF_ne h w))

private def co (x : IdeleGroup E) :
    (∀ v : InfinitePlace E, v.Completion) × (∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletion E) :=
  (((x⁻¹ : IdeleGroup E) : A E).1, fun w => ((x⁻¹ : IdeleGroup E) : A E).2 w)

private theorem continuous_co : Continuous (co : IdeleGroup E → _) := by
  have h0 : Continuous fun x : IdeleGroup E => ((x⁻¹ : IdeleGroup E) : A E) :=
    Units.continuous_val.comp continuous_inv
  refine Continuous.prodMk (continuous_fst.comp h0) (continuous_pi fun w => ?_)
  exact (RestrictedProduct.continuous_eval w).comp (continuous_snd.comp h0)

private theorem injective_co : Function.Injective (co : IdeleGroup E → _) := by
  intro x y hxy
  have h1 := congrArg Prod.fst hxy
  have h2 := congrArg Prod.snd hxy
  apply inv_injective
  apply Units.ext
  exact Prod.ext h1 (Subtype.ext <| funext fun w => congrFun h2 w)

private theorem cont_e (i j : Fin 2) : Continuous fun h : G1 E => (h i j : A E) :=
  Continuous.matrix_elem continuous_subtype_val i j

private theorem cont_I (i j : Fin 2) (v : InfinitePlace E) : Continuous fun h : G1 E => (h i j).1 v :=
  (continuous_apply v).comp (continuous_fst.comp (cont_e i j))

private theorem cont_F (i j : Fin 2) (w : HeightOneSpectrum (𝓞 E)) : Continuous fun h : G1 E => (h i j).2 w :=
  (RestrictedProduct.continuous_eval w).comp (continuous_snd.comp (cont_e i j))

private theorem measurable_al : Measurable (al : G1 E → IdeleGroup E) := by
  letI : ∀ v : InfinitePlace E, MeasurableSpace v.Completion := fun _ => borel _
  haveI : ∀ v : InfinitePlace E, BorelSpace v.Completion := fun _ => ⟨rfl⟩
  letI : ∀ w : HeightOneSpectrum (𝓞 E), MeasurableSpace (w.adicCompletion E) := fun _ => borel _
  haveI : ∀ w : HeightOneSpectrum (𝓞 E), BorelSpace (w.adicCompletion E) := fun _ => ⟨rfl⟩
  have hc := comap_eq_borel_of_continuous_injective (continuous_co (E := E)) (injective_co (E := E))
  have hm : Measurable ((co : IdeleGroup E → _) ∘ (al : G1 E → IdeleGroup E)) := by
    refine Measurable.prodMk (measurable_pi_iff.2 fun v => ?_) (measurable_pi_iff.2 fun w => ?_)
    · have hS : MeasurableSet {h : G1 E | ‖(h 1 1).1 v‖ ≤ ‖(h 1 0).1 v‖} :=
        (isClosed_le (cont_I 1 1 v).norm (cont_I 1 0 v).norm).measurableSet
      exact Measurable.ite hS (cont_I 1 0 v).measurable (cont_I 1 1 v).measurable
    · have hS : MeasurableSet {h : G1 E | Valued.v ((h 1 1).2 w) ≤ Valued.v ((h 1 0).2 w)} :=
        (isClosed_vle.preimage ((cont_F 1 0 w).prodMk (cont_F 1 1 w))).measurableSet
      exact Measurable.ite hS (cont_F 1 0 w).measurable (cont_F 1 1 w).measurable
  have h2 := measurable_comap_iff.2 hm
  rw [hc, ← BorelSpace.measurable_eq] at h2
  exact h2

private theorem e_nU (u : A E) (h : G1 E) (j : Fin 2) : (nU u * h) 1 j = h 1 j := by
  show ((nU u).1 * h.1) 1 j = h.1 1 j
  simp [nU, Matrix.mul_apply, Fin.sum_univ_two]

private theorem e_mD (t : (A E)ˣ) (h : G1 E) (j : Fin 2) :
    (mD t * h) 1 j = ((t⁻¹ : (A E)ˣ) : A E) * h 1 j := by
  show ((mD t).1 * h.1) 1 j = ((t⁻¹ : (A E)ˣ) : A E) * h.1 1 j
  simp [mD, Matrix.mul_apply, Fin.sum_univ_two]

private theorem al_nU (u : A E) (h : G1 E) : al (nU u * h) = al h := by
  have hI : pI (nU u * h) = pI h := by
    funext v
    simp only [pI, e_nU]
  have hF : pF (nU u * h) = pF h := by
    funext w
    simp only [pF, e_nU]
  apply Units.ext
  refine Prod.ext (funext fun v => ?_) (Subtype.ext <| funext fun w => ?_)
  · show (pI (nU u * h) v)⁻¹ = (pI h v)⁻¹
    rw [hI]
  · show (pF (nU u * h) w)⁻¹ = (pF h w)⁻¹
    rw [hF]

private theorem tI (t : (A E)ˣ) (v : InfinitePlace E) :
    ((t⁻¹ : (A E)ˣ) : A E).1 v * (t : A E).1 v = 1 :=
  congrArg (fun x : A E => x.1 v) (Units.inv_mul t)

private theorem tF (t : (A E)ˣ) (w : HeightOneSpectrum (𝓞 E)) :
    ((t⁻¹ : (A E)ˣ) : A E).2 w * (t : A E).2 w = 1 :=
  congrArg (fun x : A E => x.2 w) (Units.inv_mul t)

private theorem pI_mD (t : (A E)ˣ) (h : G1 E) (v : InfinitePlace E) :
    pI (mD t * h) v = ((t⁻¹ : (A E)ˣ) : A E).1 v * pI h v := by
  have hs : ((t⁻¹ : (A E)ˣ) : A E).1 v ≠ 0 := left_ne_zero_of_mul_eq_one (tI t v)
  have e : ∀ j, (mD t * h) 1 j = ((t⁻¹ : (A E)ˣ) : A E) * h 1 j := e_mD t h
  have e' : ∀ j, ((mD t * h) 1 j).1 v = ((t⁻¹ : (A E)ˣ) : A E).1 v * (h 1 j).1 v := fun j => by rw [e j]; rfl
  have key : ‖((mD t * h) 1 1).1 v‖ ≤ ‖((mD t * h) 1 0).1 v‖ ↔ ‖(h 1 1).1 v‖ ≤ ‖(h 1 0).1 v‖ := by
    rw [e', e', norm_mul, norm_mul]
    exact mul_le_mul_iff_of_pos_left (norm_pos_iff.2 hs)
  unfold pI
  by_cases hc : ‖(h 1 1).1 v‖ ≤ ‖(h 1 0).1 v‖
  · rw [if_pos hc, if_pos (key.2 hc), e']
  · rw [if_neg hc, if_neg (fun x => hc (key.1 x)), e']

private theorem pF_mD (t : (A E)ˣ) (h : G1 E) (w : HeightOneSpectrum (𝓞 E)) :
    pF (mD t * h) w = ((t⁻¹ : (A E)ˣ) : A E).2 w * pF h w := by
  have hs : ((t⁻¹ : (A E)ˣ) : A E).2 w ≠ 0 := left_ne_zero_of_mul_eq_one (tF t w)
  have hs' : Valued.v (((t⁻¹ : (A E)ˣ) : A E).2 w) ≠ 0 := (Valuation.ne_zero_iff _).2 hs
  have e : ∀ j, (mD t * h) 1 j = ((t⁻¹ : (A E)ˣ) : A E) * h 1 j := e_mD t h
  have e' : ∀ j, ((mD t * h) 1 j).2 w = ((t⁻¹ : (A E)ˣ) : A E).2 w * (h 1 j).2 w := fun j => by rw [e j]; rfl
  have key : Valued.v (((mD t * h) 1 1).2 w) ≤ Valued.v (((mD t * h) 1 0).2 w) ↔
      Valued.v ((h 1 1).2 w) ≤ Valued.v ((h 1 0).2 w) := by
    rw [e', e', map_mul, map_mul]
    constructor
    · intro x
      have := mul_le_mul_right x (Valued.v (((t⁻¹ : (A E)ˣ) : A E).2 w))⁻¹
      simpa [inv_mul_cancel_left₀ hs'] using this
    · intro x
      exact mul_le_mul_right x _
  unfold pF
  by_cases hc : Valued.v ((h 1 1).2 w) ≤ Valued.v ((h 1 0).2 w)
  · rw [if_pos hc, if_pos (key.2 hc), e']
  · rw [if_neg hc, if_neg (fun x => hc (key.1 x)), e']

private theorem al_mD (t : (A E)ˣ) (h : G1 E) : al (mD t * h) = t * al h := by
  apply Units.ext
  refine Prod.ext (funext fun v => ?_) (Subtype.ext <| funext fun w => ?_)
  · show (pI (mD t * h) v)⁻¹ = (t : A E).1 v * (pI h v)⁻¹
    rw [pI_mD, mul_inv, inv_eq_of_mul_eq_one_right (tI t v)]
  · show (pF (mD t * h) w)⁻¹ = (t : A E).2 w * (pF h w)⁻¹
    rw [pF_mD, mul_inv, inv_eq_of_mul_eq_one_right (tF t w)]

end UpperTheory.ConvolutionTheory.RankTwoDescent.TorCoPf

open UpperTheory.ConvolutionTheory.RankTwoDescent.TorCoPf in
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.torCo :
    TorCo := by
  intro E _ _
  exact ⟨al, measurable_al, al_nU, al_mD⟩
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbFn
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.orbFn :
    OrbS → OrbFn := by
  intro hS E _ _ _ D M j hj c hc hcs
  have hstab := (hS E D).2.1
  haveI : PolishSpace (G1 E) := GroundTheory.Automorphic.polishSpace_of_locallyCompact
  haveI := M.haar
  haveI := M.right
  have hval : ∀ g : G1 ℚ, (j g).1 = g.1.map (AdeleBaseChange.adeleMap ℚ E) := fun g => by
    have := congrArg Units.val (hj g)
    simpa [em] using this
  have hjc : Continuous j := by
    refine continuous_induced_rng.2 ?_
    exact (continuous_subtype_val.matrix_map AdeleBaseChange.continuous_adeleMap).congr fun g => (hval g).symm
  set O : G1 E → V4 ℚ := fun h => D.act (gl h)⁻¹ (rp X0) with hO
  set cc : G1 E → ℂ := fun h => ∫ g, c (j g * h) ∂M.μ with hcc
  have hgl : Continuous fun h : G1 E => gl h := by
    refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
    have e : ∀ h : G1 E, ((gl h)⁻¹ : GL (Fin 2) (A E)).val = (h⁻¹ : G1 E).1 := fun h => by
      have : (gl h)⁻¹ = gl h⁻¹ := by simp only [gl, map_inv]
      rw [this]; rfl
    have hi : Continuous fun h : G1 E => (h⁻¹ : G1 E).1 :=
      (continuous_subtype_val : Continuous fun g : G1 E => g.1).comp continuous_inv
    exact hi.congr fun h => (e h).symm
  have hglc : Continuous fun h : G1 E => (gl h)⁻¹ := hgl.inv
  have hOc : Continuous O := D.continuous_act' hglc continuous_const
  have hccm : Measurable cc := by
    have hF : StronglyMeasurable (Function.uncurry fun (h : G1 E) (g : G1 ℚ) => c (j g * h)) :=
      (hc.comp ((hjc.comp continuous_snd).mul continuous_fst)).stronglyMeasurable
    exact (hF.integral_prod_right (ν := M.μ)).measurable
  have hfac : Function.FactorsThrough cc O := by
    intro a b hab
    have h1 : D.act (gl (b * a⁻¹)) (rp X0) = rp X0 := by
      have hab' : D.act (gl a)⁻¹ (rp X0) = D.act (gl b)⁻¹ (rp X0) := hab
      have e : gl (b * a⁻¹) = gl b * (gl a)⁻¹ := by simp only [gl, map_mul, map_inv]
      rw [e, Dat.act_mul, hab', Dat.act_act_inv]
    obtain ⟨g0, hg0⟩ := (hstab (b * a⁻¹)).1 h1
    have h2 : b * a⁻¹ = j g0 := Matrix.SpecialLinearGroup.toGL_injective (hg0.trans (hj g0).symm)
    have h3 : b = j g0 * a := by rw [← h2]; group
    simp only [hcc]
    rw [h3]
    have := integral_mul_right_eq_self (μ := M.μ) (fun g => c (j g * a)) g0
    simp only [map_mul, mul_assoc] at this
    exact this.symm
  refine ⟨Function.extend O cc 0, ?_, fun h => hfac.extend_apply 0 h⟩
  have hR : MeasurableSet (Set.range O) := by
    obtain ⟨K, hK, hU⟩ := isSigmaCompact_range hOc
    rw [← hU]
    exact MeasurableSet.iUnion fun n => (hK n).measurableSet
  refine measurable_of_restrict_of_restrict_compl hR ?_ ?_
  · have hr : Measurable (Set.rangeFactorization O) := hOc.measurable.subtype_mk
    refine (Measurable.measurable_comp_iff_of_surjective hr Set.rangeFactorization_surjective).1 ?_
    have e : (Set.range O).domRestrict (Function.extend O cc 0) ∘ Set.rangeFactorization O = cc := by
      funext h
      exact hfac.extend_apply 0 h
    rw [e]
    exact hccm
  · have e : (Set.range O)ᶜ.domRestrict (Function.extend O cc 0) = fun _ => 0 := by
      funext x
      exact Function.extend_apply' cc (0 : V4 ℚ → ℂ) x.1 fun ⟨a, ha⟩ => x.2 ⟨a, ha⟩
    rw [e]
    exact measurable_const
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Rev
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.rev :
    ThetaLiftEqAnisotropicPart → Coef → ThetaLiftIsBoundedCuspidal → Dens → Fub → CoefPer → Rev := by
  rintro hE hC hF hD hB hP E _ _ _ D W M N P ⟨φ, hφ, h, hne⟩
  obtain ⟨ph, hph, h0⟩ : ∃ ph ∈ Fock D.δ, f0 W N ph φ.1 ≠ 0 := by
    by_contra hn
    push Not at hn
    refine hne (hP E D W M N P φ hφ (fun ph hph => ?_) h)
    have h1 := hC E D W M N P ph hph φ hφ (qr D.δ X0) 1
    rw [← hE E D W M N P ph hph φ hφ, hn ph hph] at h1
    have hδ : qr D.δ X0 ≠ 0 := by
      have := D.neg (Rat.castHom ℝ)
      simp only [qr, X0, eq_ratCast, Rat.cast_lt_zero] at this ⊢
      simpa using this.ne
    have e : {ξ | qr D.δ ξ ≠ 0 ∧ qr D.δ ξ = qr D.δ X0} = {ξ | qr D.δ ξ = qr D.δ X0} :=
      Set.ext fun ξ => ⟨fun h => h.2, fun h => ⟨(show qr D.δ ξ = _ from h) ▸ hδ, h⟩⟩
    rw [e] at h1
    simp only [Pi.zero_apply, zero_mul, integral_zero] at h1
    refine (mul_eq_zero.1 h1.symm).resolve_left ?_
    simp [Measure.real, adeleMeasure_fundamentalSet]
  obtain ⟨π, hπ, f, hf, h2⟩ := hD M _ (hF E D W M N P ph hph φ hφ) h0
  exact ⟨π, hπ, f, hf, ph, hph, φ, hφ, hB E D W M N P ph hph φ hφ π f hf ▸ h2⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SplitEig
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

section Objects

variable {E : Type} [Field E] [NumberField E]

structure Bd (Ψ : GL (Fin 2) (A E) → ℂ) : Prop where
  cont : Continuous Ψ
  left : ∀ γ g, Ψ (ratGL E 2 γ * g) = Ψ g
  bdd : ∀ C : Set (GL (Fin 2) (A E)), IsCompact C → ∃ B : ℝ, ∀ h : G1 E, ∀ k ∈ C, ‖Ψ (gl h * k)‖ ≤ B

def PosC (Ψ : GL (Fin 2) (A E) → ℂ) : Prop := ∀ s g, Ψ (GroundTheory.Automorphic.Reduction.centralSection E 2 s * g) = Ψ g

variable [_root_.NumberField.IsTotallyComplex E]

structure InvPair (V V' : Submodule ℂ (Sm E 2)) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) : Prop where
  st : _root_.GlobalTheory.CuspRep.IsStable V
  st' : _root_.GlobalTheory.CuspRep.IsStable V'
  fin : ∀ k (x : V) (y : V'), B ⟨act (.fin k) x.1, st _ _ x.2⟩ ⟨act (.fin k) y.1, st' _ _ y.2⟩ = B x y
  cpt : ∀ k (x : V) (y : V'), B ⟨act (.cpt k) x.1, st _ _ x.2⟩ ⟨act (.cpt k) y.1, st' _ _ y.2⟩ = B x y
  lie : ∀ X (x : V) (y : V'), B ⟨act (.lie X) x.1, st _ _ x.2⟩ y + B x ⟨act (.lie X) y.1, st' _ _ y.2⟩ = 0

end Objects

def MeanLaws : Prop := ∀ (E : Type) [Field E] [NumberField E] (N : MeasE E) (Ψ : GL (Fin 2) (A E) → ℂ), Bd Ψ →
  (∀ y, IntegrableOn (fun h => Ψ (gl h * y)) N.D N.μ) ∧ (Continuous fun y => mean N fun x => Ψ (x * y)) ∧
  (∀ (h : G1 E) y, (mean N fun x => Ψ (x * (gl h * y))) = mean N fun x => Ψ (x * y)) ∧
  ∀ γ y, (mean N fun x => Ψ (x * (ratGL E 2 γ * y))) = mean N fun x => Ψ (x * y)

def UILaws : Prop := ∀ (E : Type) [Field E] [NumberField E] (β : (A E)ˣ → ℂ), Continuous β →
  (∀ (e : Eˣ) t, β (IdeleGroup.diagonal E e * t) = β t) →
  IntegrableOn (fun z : IdeleGroup.normOneSubgroup E => β (z : IdeleGroup E)) (normOneFundamentalDomain E) (normOneMeasure E) ∧
  (∃ B : ℝ, ∀ t : (A E)ˣ, ab t = 1 → ‖β t‖ ≤ B) ∧ ∀ d : (A E)ˣ, ab d = 1 → (UI fun t => β (t * d)) = UI β

def IILaws : Prop := ∀ (E : Type) [Field E] [NumberField E] (N : MeasE E) (Ψ : GL (Fin 2) (A E) → ℂ), Bd Ψ →
  (∀ Ψ', Bd Ψ' → ∀ c : ℂ, (II N fun x => Ψ x + c * Ψ' x) = II N Ψ + c * II N Ψ') ∧
  (PosC Ψ → ∀ g, (II N fun x => Ψ (x * g)) = II N Ψ)

def IILie : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (N : MeasE E) (Φ φ : Sm E 2) (X),
  (Bd fun x => Φ.1 x * φ.1 x) → (PosC fun x => Φ.1 x * φ.1 x) → (Bd fun x => (act (.lie X) Φ).1 x * φ.1 x) →
  (Bd fun x => Φ.1 x * (act (.lie X) φ).1 x) →
  (II N fun x => (act (.lie X) Φ).1 x * φ.1 x) + (II N fun x => Φ.1 x * (act (.lie X) φ).1 x) = 0

def SpanGrow : Prop := All fun E _ _ _ _ W M _ _ => ∀ π : TR.CuspSub ℚ 2, ∀ Φ ∈ span W M π,
  ∀ C : Set (GL (Fin 2) (A E)), IsCompact C → ∀ c : ℝ, 0 < c → ∃ (r : ℕ) (B : ℝ), ∀ b a, ∀ k ∈ C, c ≤ ab a →
    ‖Φ.1 (gl (nU b * mD a) * k)‖ ≤ B * ab a ^ r

def ProdBd : Prop := All fun _ _ _ _ _ W M _ P => ∀ π : TR.CuspSub ℚ 2, ∀ Φ ∈ span W M π, ∀ φ ∈ P.V,
  (Bd fun x => Φ.1 x * φ.1 x) ∧ (PosInv π → GlobalTheory.DiscSpec.IsNormalised P → PosC fun x => Φ.1 x * φ.1 x)

def KillW : Prop := ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (Φ : GL (Fin 2) (A E) → ℂ), Continuous Φ →
  (∀ γ g, Φ (ratGL E 2 γ * g) = Φ g) → (∀ h, WE D Φ h = 0) → ∀ (h : G1 E) g, Φ (gl h * g) = Φ g

def PairEx : Prop := All fun _ _ _ _ D W M N P => GlobalTheory.DiscSpec.IsNormalised P → ∀ π : TR.CuspSub ℚ 2, PosInv π →
  ∃ B : span W M π →ₗ[ℂ] P.V →ₗ[ℂ] ℂ, InvPair _ _ B ∧ (∀ x y, B x y = II N fun g => x.1.1 g * y.1.1 g) ∧
    ∀ x : span W M π, (∀ h, WE D x.1.1 h = 0) → B x = 0

def SplitEig : Prop := All fun E _ _ _ D W M _ _ => ∀ π : TR.CuspSub ℚ 2, ∀ Φ ∈ span W M π, ∀ (v : P ℚ) (w : P E), SplitAt v w →
  ∀ B, π.HasSat v B → Fix w Φ.1 → EigAt w B (WE D Φ.1)

def SatPair : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (V : Submodule ℂ (Sm E 2)) (Q : CuspSub E 2)
  (B : V →ₗ[ℂ] Q.V →ₗ[ℂ] ℂ), InvPair V Q.V B → B ≠ 0 → ∀ (w : P E) (T : V →ₗ[ℂ] (GL (Fin 2) (A E) → ℂ)),
  (∀ x : V, ∀ᶠ y in 𝓝 (1 : GL (Fin 2) (Kv w)), ∀ g, x.1.1 (g * lc w y) = x.1.1 g) →
  (∀ (x x' : V) y, (∀ g, x'.1.1 g = x.1.1 (g * lc w y)) → ∀ g, T x' g = T x (g * lc w y)) → (∀ x, T x = 0 → B x = 0) →
  ∀ C C' : Multiset ℂˣ, (∀ x : V, Fix w x.1.1 → EigAt w C (T x)) → (CG.mk Q).HasSat w C' → C' = C.map (·⁻¹)

def InfPair : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (V : Submodule ℂ (Sm E 2)) (Q : CuspSub E 2)
  (B : V →ₗ[ℂ] Q.V →ₗ[ℂ] ℂ), InvPair V Q.V B → B ≠ 0 → ∀ (τ : E →+* ℂ) (m m' : Multiset ℂ), m.card = 2 →
  (∀ u, ∀ Φ ∈ V, cap τ u Φ = (m.map (u + ·)).prod • Φ) → Q.HasInfChar τ m' → m' = m.map Neg.neg

def CharSel : Prop := ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (β : (A E)ˣ → ℂ), Continuous β →
  (∀ (e : Eˣ) t, β (IdeleGroup.diagonal E e * t) = β t) →
  (UI fun z => β (z * (Units.map (D.bar : A E →* A E) z)⁻¹)) ≠ 0 →
  ∃ χ : HChar E, (∀ z : (A E)ˣ, χ.1 (z * (Units.map (D.bar : A E →* A E) z)⁻¹) = 1) ∧
    (∀ z : (A E)ˣ, (∃ s, Matrix.GeneralLinearGroup.scalar (Fin 2) z = GroundTheory.Automorphic.Reduction.centralSection E 2 s) → χ.1 z = 1) ∧
    (UI fun t => ((χ.1 t : ℂˣ) : ℂ) * β t) ≠ 0

def CharDown : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (χ : HChar E),
  (∀ z : (A E)ˣ, χ.1 (z * (Units.map (D.bar : A E →* A E) z)⁻¹) = 1) → ∃ χ₀ : HChar ℚ, ∀ z : (A E)ˣ, χ.1 z = χ₀.1 (ideleNorm ℚ E z)

def FinS : Prop := All fun E _ _ _ D W M N P => GlobalTheory.DiscSpec.IsNormalised P → ∀ π : TR.CuspSub ℚ 2, PosInv π →
  (∃ f ∈ π.V, ∃ ph ∈ Fock D.δ, ∃ φ ∈ P.V, (II N fun x => lift W M f.1 ph x * φ.1 x) ≠ 0) →
  ∃ π' : TR.CuspSub ℚ 2, SplitBC π'.HasSat (CG.mk P).HasSat ∧
    ∀ τ m, P.HasInfChar τ m → π'.HasInfChar (InfinitePlace.mk (τ.comp (algebraMap ℚ E))) m

def DownN : Prop := ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], Module.finrank ℚ E = 2 → ∀ P : CuspSub E 2,
  GlobalTheory.DiscSpec.IsNormalised P → ConjInv P → ∃ π' : TR.CuspSub ℚ 2, SplitBC π'.HasSat (CG.mk P).HasSat ∧
    ∀ τ m, P.HasInfChar τ m → π'.HasInfChar (InfinitePlace.mk (τ.comp (algebraMap ℚ E))) m

end UpperTheory.ConvolutionTheory.RankTwoDescent

end
end

