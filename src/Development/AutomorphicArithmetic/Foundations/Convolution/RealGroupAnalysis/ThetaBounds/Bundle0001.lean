module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.ActMat
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.InfinitesimalCharacterPullback.HasInfCharPullSub
public import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.Bundle0003
public import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms.CompletionsOverBasisRepr

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ActCont
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem cont_inf (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) :
    Continuous (infGL E a) := by
  have hs : Continuous (sInf E : Cinf E → Ad E) := (GlobalTheory.CuspRep.continuous_infEq E).prodMk continuous_const
  exact Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map hs))

private theorem cont_fin (E : Type) [Field E] [NumberField E] (a : ℕ) :
    Continuous (finGL E a) := by
  have hs : Continuous (sFin E : Af E → Ad E) := continuous_const.prodMk continuous_id
  exact Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map hs))

private theorem cont_unherm {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (D : Dat F E) : Continuous D.unherm := by
  have hco : ∀ i, Continuous fun z => D.co z i := fun i => (continuous_apply i).comp D.continuous_co
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact (hco 0).comp (continuous_id.matrix_elem 1 1)
  · exact (hco 0).comp (continuous_id.matrix_elem 0 0)
  · exact (hco 0).comp (continuous_id.matrix_elem 0 1)
  · exact (hco 1).comp (continuous_id.matrix_elem 0 1)

private theorem cont_act {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (D : Dat F E) (v : V4 F) : Continuous fun h : GL (Fin 2) (A E) => D.act h v := by
  have hv : Continuous fun h : GL (Fin 2) (A E) => h.val := Units.continuous_val
  exact (cont_unherm D).comp ((hv.matrix_mul continuous_const).matrix_mul
    (hv.matrix_map D.continuous_bar).matrix_transpose)

theorem UpperTheory.ConvolutionTheory.R2.Ff.actCont :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E), ActCont D := by
  intro F E _ _ _ _ _ _ _ D
  obtain ⟨ρ, hρ, -, -⟩ := UpperTheory.ConvolutionTheory.R2.D.actMat F E D
  have hval : Continuous fun h => (ρ h).val := continuous_matrix fun i j => by
    have e : ∀ h, (ρ h).val i j = D.act h (Pi.single j 1) i := fun h => by rw [hρ]; simp
    simp only [e]
    exact (continuous_apply i).comp (cont_act D _)
  refine ⟨ρ, Units.continuous_iff.2 ⟨hval, ?_⟩, hρ, continuous_nu, cont_inf E 2, cont_fin E 2⟩
  have e : (fun h => (((ρ h)⁻¹ : GL (Fin 4) (A F)) : Matrix (Fin 4) (Fin 4) (A F))) = fun h => (ρ h⁻¹).val := by
    funext h; rw [map_inv]
  exact e ▸ hval.comp continuous_inv
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ActInf
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E]

private theorem cont_coord (τ : E →+* ℂ) : Continuous (coord (E := E) τ) :=
  AddMonoidHomClass.continuous_of_bound (coord τ) 1 fun x => by
    simpa using UpperTheory.V.FieldIso.norm_coord_le τ x

private theorem cont_pInfE : Continuous (pInf E) := continuous_pi fun w =>
  (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
    ((continuous_apply w).comp continuous_fst)

private theorem cont_pInfF : Continuous (TR.pInf F) := continuous_pi fun w =>
  (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
    ((continuous_apply w).comp continuous_fst)

private theorem tau_real (τ : E →+* ℂ) (k : F) :
    τ (algebraMap F E k) =
      ((InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ)) k : ℝ) : ℂ) := by
  have hv := IsTotallyReal.isReal (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ)
  rw [InfinitePlace.embedding_of_isReal_apply hv]
  have hr : ComplexEmbedding.conjugate (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ).embedding = (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ).embedding :=
    InfinitePlace.isReal_iff.1 hv
  rcases InfinitePlace.embedding_mk_eq (τ.comp (algebraMap F E)) with h | h
  · exact (congrArg (fun f : F →+* ℂ => f k) h).symm
  · have h' : (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ).embedding = ComplexEmbedding.conjugate (τ.comp (algebraMap F E)) := h
    have h2 : τ.comp (algebraMap F E) = (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ).embedding := by
      rw [← hr, h']
      exact (star_star _).symm
    exact congrArg (fun f : F →+* ℂ => f k) h2

private theorem pInfF_rat (k : F) (w : InfinitePlace F) :
    TR.pInf F (rt k) w = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) k := by
  have hw := IsTotallyReal.isReal w
  change (InfinitePlace.Completion.ringEquivRealOfIsReal hw) (algebraMap F (InfiniteAdeleRing F) k w) = _
  rw [InfinitePlace.Completion.ringEquivRealOfIsReal_apply, InfiniteAdeleRing.algebraMap_apply,
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw]
  rfl

private theorem r_am (τ : E →+* ℂ) (a : A F) :
    coord τ (pInf E (am E a)) = ((TR.pInf F a (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ) : ℝ) : ℂ) := by
  have key : (fun x : InfiniteAdeleRing F => coord τ (pInf E (am E ((x, 0) : A F)))) =
      fun x => ((TR.pInf F ((x, 0) : A F) (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ) : ℝ) : ℂ) := by
    have hc : Continuous fun x : InfiniteAdeleRing F => ((x, 0) : A F) := Continuous.prodMk_left 0
    refine (InfiniteAdeleRing.denseRange_algebraMap (K := F)).equalizer
      ((cont_coord τ).comp (cont_pInfE.comp (continuous_am.comp hc)))
      (Complex.continuous_ofReal.comp ((continuous_apply _).comp (cont_pInfF.comp hc))) (funext fun k => ?_)
    have e1 : pInf E (am E ((algebraMap F (InfiniteAdeleRing F) k, 0) : A F)) = pInf E (am E (rt k)) := rfl
    have e2 : TR.pInf F ((algebraMap F (InfiniteAdeleRing F) k, 0) : A F) = TR.pInf F (rt k) := rfl
    simp only [Function.comp_apply]
    rw [e1, e2, am_rt, pInfF_rat, ← tau_real]
    exact coord_algebraMap τ _
  exact congrFun key a.1

variable (D : Dat F E)

private theorem r_mk (τ : E →+* ℂ) (u t : A F) :
    coord τ (pInf E (D.mkE u t)) = ((TR.pInf F u (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ) : ℝ) : ℂ) +
      τ D.θ * ((TR.pInf F t (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ) : ℝ) : ℂ) := by
  have e : coord τ (pInf E (rt D.θ)) = τ D.θ := coord_algebraMap τ _
  rw [D.mkE_def, map_add (f := _), map_add (f := _), map_mul, map_mul, r_am, r_am, e, mul_comm]

private theorem conj_θ (τ : E →+* ℂ) : starRingEnd ℂ (τ D.θ) = -τ D.θ := by
  have hv := IsTotallyReal.isReal (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ)
  have hc := D.neg (InfinitePlace.embedding_of_isReal hv)
  have hz : τ D.θ ^ 2 = ((InfinitePlace.embedding_of_isReal hv D.δ : ℝ) : ℂ) := by
    rw [← map_pow, D.sq, tau_real]
  generalize τ D.θ = z at hz
  generalize InfinitePlace.embedding_of_isReal hv D.δ = c at hz hc
  have h1 := congrArg Complex.re hz
  have h2 := congrArg Complex.im hz
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at h1 h2
  have hre : z.re = 0 := by
    by_contra h
    have h3 : z.im = 0 := by
      have : z.re * z.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left h
    rw [h3] at h1
    nlinarith [mul_self_nonneg z.re]
  apply Complex.ext
  · simp [hre]
  · simp

private theorem r_bar (τ : E →+* ℂ) (z : A E) :
    coord τ (pInf E (D.bar z)) = starRingEnd ℂ (coord τ (pInf E z)) := by
  obtain ⟨u, t, rfl⟩ := D.exists_mkE z
  rw [D.bar_mkE, r_mk, r_mk, map_add (f := _), map_mul, conj_θ, Complex.conj_ofReal, Complex.conj_ofReal, map_neg, Pi.neg_apply]
  push_cast
  ring

private theorem map_herm (τ : E →+* ℂ) (v : V4 F) :
    (D.herm v).map ((coord τ).comp (pInf E)) =
      Hm (τ D.θ) (UpperTheory.ConvolutionTheory.R2.Fo.pl F τ) fun i => TR.pInf F (v i) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Dat.herm, Hm, r_mk, r_am, sub_eq_add_neg]

private theorem fin_part (y : GL (Fin 2) (Cinf E)) (v : V4 F) :
    finPartPi (D.act (infGL E 2 y) v) = finPartPi v := by
  let eF : A F := ((0, 1) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  have heF : eF * eF = eF := Prod.ext (mul_zero _) (mul_one _)
  set e : A E := am E eF with he
  have he2 : e * e = e := by rw [he, ← map_mul, heF]
  have hbar : D.bar e = e := D.bar_am eF
  have hfst : e.1 = 0 := map_zero (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E))
  have hsnd : e.2 = 1 := map_one (AdeleBaseChange.finiteAdeleMap F E)
  have hM : e • (infGL E 2 y).val = e • (1 : Matrix (Fin 2) (Fin 2) (A E)) := by
    ext1 i j
    have h := congrArg (fun g : GL (Fin 2) (Af E) => g.val i j) (pFin_infGL y)
    refine Prod.ext ?_ ?_
    · change e.1 * _ = e.1 * _
      rw [hfst, zero_mul, zero_mul]
    · change e.2 * _ = e.2 * _
      rw [hsnd, one_mul, one_mul]
      exact h.trans (by
        change (1 : Matrix (Fin 2) (Fin 2) (Af E)) i j = _
        by_cases hij : i = j
        · subst hij; simp <;> rfl
        · simp [Matrix.one_apply_ne hij] <;> rfl)
  have hS : e • D.star2 (infGL E 2 y).val = e • (1 : Matrix (Fin 2) (Fin 2) (A E)) := by
    have hs : ∀ X : Matrix (Fin 2) (Fin 2) (A E), D.star2 (e • X) = e • D.star2 X := fun X => by
      ext1 i j
      simp [Dat.conjTransposeGal_apply, hbar]
    rw [← hs, hM, hs, Dat.conjTransposeGal_one]
  have L : ∀ X Y : Matrix (Fin 2) (Fin 2) (A E), (e • X) * D.herm v * (e • Y) = e • (X * D.herm v * Y) := fun X Y => by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, he2]
  have main : D.act (infGL E 2 y) (eF • v) = eF • v := D.herm_injective (by
    rw [D.herm_act, D.herm_smul]
    calc (infGL E 2 y).val * (am E eF • D.herm v) * D.star2 (infGL E 2 y).val
        = e • ((infGL E 2 y).val * D.herm v * D.star2 (infGL E 2 y).val) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, he]
      _ = (e • (infGL E 2 y).val) * D.herm v * (e • D.star2 (infGL E 2 y).val) := (L _ _).symm
      _ = (e • 1) * D.herm v * (e • 1) := by rw [hM, hS]
      _ = am E eF • D.herm v := by rw [L]; simp [he])
  rw [D.act_smul] at main
  funext i
  have h := congrArg (fun x : V4 F => (x i).2) main
  exact (one_mul _).symm.trans (h.trans (one_mul _))

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.R2.Ff.actInf :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E), ActInf D := by
  intro F E _ _ _ _ _ _ _ D y v
  refine ⟨fin_part D y v, fun τ => ?_⟩
  have hy : ((infGL E 2 y).val).map ((coord τ).comp (pInf E)) = y.val.map (coord τ) := by
    ext1 i j
    exact congrArg (coord τ) (congrArg (fun g : GL (Fin 2) (Cinf E) => g.val i j) (pInf_infGL y))
  have hs : (D.star2 (infGL E 2 y).val).map ((coord τ).comp (pInf E)) = (y.val.map (coord τ))ᴴ := by
    rw [← hy]
    ext1 i j
    exact r_bar D τ _
  have h := congrArg (fun X => X.map ((coord τ).comp (pInf E))) (D.herm_act (infGL E 2 y) v)
  simp only [Matrix.map_mul, map_herm, hy, hs] at h
  exact h
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ContinuousAdeleInfHom
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Ff

open GroundTheory.Heights₂.Theta NumberField.mixedEmbedding

section

variable {K : Type} [Field K] [NumberField K]

private theorem inv_map_mulVec {R : Type} [CommRing R] (h : A K →+* R) (g : GL (Fin 4) (A K))
    (v : Fin 4 → A K) :
    (g⁻¹).val.map h *ᵥ (fun i => h ((g.val *ᵥ v) i)) = fun i => h (v i) := by
  rw [map_mulVec_eq, Matrix.mulVec_mulVec, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Matrix.map_one h (map_zero h) (map_one h), Matrix.one_mulVec]

private theorem continuous_adeleInfHom : Continuous (adeleInfHom : A K → mixedSpace K) :=
  (homeomorphMixedSpace K).continuous.comp continuous_fst

private theorem continuous_adeleFinHom : Continuous (adeleFinHom : A K → FiniteAdeleRing (𝓞 K) K) :=
  continuous_snd

private theorem continuous_invEntry (i j : Fin 4) :
    Continuous fun x : GL (Fin 4) (A K) => (x⁻¹).val i j :=
  (Units.continuous_val.comp continuous_inv).matrix_elem i j

private theorem wt_nonneg (S : Set (Fin 4 → FiniteAdeleRing (𝓞 K) K)) (N : ℕ) (v : V4 K) :
    0 ≤ wt S N v := by
  unfold wt
  split_ifs
  · positivity
  · exact le_rfl

private theorem wt_le_of {S S' : Set (Fin 4 → FiniteAdeleRing (𝓞 K) K)} {N : ℕ} {v w : V4 K} {m : ℝ}
    (hm1 : 1 ≤ m) (h : finPartPi w ∈ S → finPartPi v ∈ S' ∧ ‖infPartPi v‖ ≤ m * ‖infPartPi w‖) :
    wt S N w ≤ m ^ N * wt S' N v := by
  have hm0 : 0 ≤ m ^ N := by positivity
  by_cases hv : finPartPi w ∈ S
  · obtain ⟨hfin, hs⟩ := h hv
    generalize hsd : ‖infPartPi v‖ = s at hs
    generalize htd : ‖infPartPi w‖ = t at hs
    have ht0 : 0 ≤ t := htd ▸ norm_nonneg _
    have hs0 : 0 ≤ s := hsd ▸ norm_nonneg _
    have h1 : 1 + s ≤ m * (1 + t) := by nlinarith
    have hp : (1 + s) ^ N ≤ m ^ N * (1 + t) ^ N := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) h1 N
    have e1 : wt S N w = ((1 + t) ^ N)⁻¹ := by rw [← htd]; exact if_pos hv
    have e2 : wt S' N v = ((1 + s) ^ N)⁻¹ := by rw [← hsd]; exact if_pos hfin
    rw [e1, e2, ← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  · have : wt S N w = 0 := if_neg hv
    rw [this]
    exact mul_nonneg hm0 (wt_nonneg _ _ _)

private theorem norm_mulVec_le (M : Matrix (Fin 4) (Fin 4) (mixedSpace K))
    (u : Fin 4 → mixedSpace K) : ‖M *ᵥ u‖ ≤ (∑ i, ∑ j, ‖M i j‖) * ‖u‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  calc ‖(M *ᵥ u) i‖ = ‖∑ j, M i j * u j‖ := rfl
    _ ≤ ∑ j, ‖M i j * u j‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖M i j‖ * ‖u‖ := Finset.sum_le_sum fun j _ =>
        (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_le_pi_norm u j) (norm_nonneg _))
    _ = (∑ j, ‖M i j‖) * ‖u‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ i, ∑ j, ‖M i j‖) * ‖u‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact Finset.single_le_sum (f := fun i => ∑ j, ‖M i j‖)
          (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) (Finset.mem_univ i)

end

end UpperTheory.ConvolutionTheory.R2.Ff

open GroundTheory.Heights₂.Theta NumberField.mixedEmbedding in
theorem UpperTheory.ConvolutionTheory.R2.Ff.wtLin :
    ∀ (F : Type) [Field F] [NumberField F], WtLin F := by
  intro F _ _ C hC K hK

  let ψ : GL (Fin 4) (A F) × (Fin 4 → FiniteAdeleRing (𝓞 F) F) → (Fin 4 → FiniteAdeleRing (𝓞 F) F) :=
    fun p => (p.1⁻¹).val.map adeleFinHom *ᵥ p.2
  have hψ : Continuous ψ := by
    exact (Continuous.matrix_map (Units.continuous_val.comp (continuous_inv.comp continuous_fst))
      continuous_adeleFinHom).matrix_mulVec continuous_snd
  refine ⟨ψ '' (C ×ˢ K), (hC.prod hK).image hψ, fun N => ?_⟩

  let β : GL (Fin 4) (A F) → ℝ := fun x => ∑ i, ∑ j, ‖(x⁻¹).val.map (adeleInfHom (K := F)) i j‖
  have hβ : Continuous β := by
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact (continuous_adeleInfHom.comp (continuous_invEntry i j)).norm
  obtain ⟨B₀, hB₀⟩ := (hC.image hβ).bddAbove
  have hβle : ∀ x ∈ C, β x ≤ B₀ := fun x hx => hB₀ ⟨x, hx, rfl⟩
  set m : ℝ := max 1 B₀ with hm
  have hm1 : 1 ≤ m := le_max_left _ _
  refine ⟨m ^ N, fun x hx v => ?_⟩
  refine wt_le_of hm1 fun hv => ?_
  have hfin : finPartPi v ∈ ψ '' (C ×ˢ K) := by
    refine ⟨(x, finPartPi (x.val *ᵥ v)), ⟨hx, hv⟩, ?_⟩
    have := inv_map_mulVec (adeleFinHom (K := F)) x v
    simpa only [ψ, finPartPi_eq_adeleFinHom] using this
  have hinf : infPartPi v = (x⁻¹).val.map adeleInfHom *ᵥ infPartPi (x.val *ᵥ v) := by
    have := inv_map_mulVec (adeleInfHom (K := F)) x v
    simpa only [infPartPi_eq_adeleInfHom] using this.symm
  refine ⟨hfin, ?_⟩
  rw [hinf]
  exact (norm_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right
    ((hβle x hx).trans (le_max_right _ _)) (norm_nonneg _))
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.CurveE
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private theorem pInf_sInf (x : TR.Rinf F) : TR.pInf F (TR.sInf F x) = x :=
  (TR.infEq F).symm_apply_apply x

private theorem pFin_sInf (x : TR.Rinf F) : pFin F (TR.sInf F x) = 0 := rfl

private noncomputable def cU (w : InfinitePlace F) (t : ℝ) : GL (Fin 2) (TR.Rinf F) :=
  ⟨!![1, Pi.single w t; 0, 1], !![1, Pi.single w (-t); 0, 1],
    by
      ext i j v
      fin_cases i <;> fin_cases j <;> by_cases h : v = w <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Pi.single_apply, h],
    by
      ext i j v
      fin_cases i <;> fin_cases j <;> by_cases h : v = w <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Pi.single_apply, h]⟩

private theorem cU_val (w : InfinitePlace F) (t : ℝ) : (cU w t).val = !![1, Pi.single w t; 0, 1] := rfl

private theorem cU_add (w : InfinitePlace F) (s t : ℝ) : cU w (s + t) = cU w s * cU w t := by
  refine Units.ext ?_
  rw [Units.val_mul, cU_val, cU_val, cU_val]
  ext i j v
  fin_cases i <;> fin_cases j <;> by_cases h : v = w <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Pi.single_apply, h, add_comm]

private theorem cU_der (w : InfinitePlace F) :
    HasDerivAt (fun t => TR.toL (cU w t).val) (TR.toL (Matrix.single 0 1 (Pi.single w 1))) 0 := by
  have e : (fun t => TR.toL (cU w t).val) =
      fun t : ℝ => TR.toL (1 : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) + t • TR.toL (Matrix.single 0 1 (Pi.single w 1)) := by
    funext t
    ext i j v
    fin_cases i <;> fin_cases j <;> by_cases h : v = w <;> simp [cU_val, Matrix.single_apply, Pi.single_apply, h]
  rw [e]
  have h := ((hasDerivAt_id (0 : ℝ)).smul_const (TR.toL (Matrix.single 0 1 (Pi.single w 1)) : TR.Lie F 2)).const_add
    (TR.toL (1 : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) : TR.Lie F 2)
  simpa only [id, one_smul] using h

private theorem unipotent_placeEmbed_gl (w : InfinitePlace F) (t : ℝ) : gl (nU (Fo.at1 w t)) = TR.infGL F 2 (cU w t) := by
  refine TR.ga_ext ?_ ?_
  · rw [TR.pInf_infGL]
    refine Units.ext ?_
    ext i j v
    fin_cases i <;> fin_cases j <;> simp [cU_val, Fo.at1, nU, gl, Matrix.SpecialLinearGroup.toGL, pInf_sInf]
  · rw [TR.pFin_infGL]
    refine Units.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Fo.at1, nU, gl, Matrix.SpecialLinearGroup.toGL, pFin_sInf]

private theorem character_placeEmbed_exp (w : InfinitePlace F) (t : ℝ) (q : A F) :
    ψ (Fo.at1 w t * q) = Complex.exp (Fo.cc * ((t : ℂ) * Fo.cw w q)) := by
  rw [(UpperTheory.ConvolutionTheory.R2.C.splitA F).2]
  have h2 : (Fo.at1 w t * q).2 = 0 := by
    change (0 : FiniteAdeleRing (𝓞 F) F) * q.2 = 0
    exact zero_mul _
  rw [h2, AddChar.map_zero_eq_one, Circle.coe_one, mul_one, Finset.prod_eq_single w]
  · simp [Fo.at1, Fo.cc, Fo.cw, pInf_sInf]
  · intro v _ hv
    simp [Fo.at1, pInf_sInf, hv]
  · simp

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.R2.Ff.curveE :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (O : Fo.Ops F) (W : Weil D), CurveE O W := by
  intro F E _ _ _ _ _ _ _ D O W w
  refine ⟨fun t => nU (Fo.at1 w t), cU w, ⟨cU_add w, cU_der w⟩, unipotent_placeEmbed_gl w, fun φ t v => ?_⟩
  have he : (O.e D.δ w φ).1 v = Fo.cc * Fo.cw w (q4 D.δ v) * φ.1 v := by
    have a : ∀ i j (χ : S4 F), (O.x w i (O.x w j χ)).1 v = Fo.cw w (v i) * (Fo.cw w (v j) * χ.1 v) := fun i j χ => by
      rw [O.x_apply, O.x_apply]
    simp only [Fo.Ops.e, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply]
    change Fo.cc * (((O.x w 2 (O.x w 2 φ)).1 v - Fo.cw w (rt D.δ) * (O.x w 3 (O.x w 3 φ)).1 v) - (O.x w 1 (O.x w 0 φ)).1 v) = _
    rw [a, a, a]
    simp only [Fo.cw, q4, map_sub, map_mul, map_pow, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
    push_cast
    ring
  have e1 : (fun s => (W.Om (nU (Fo.at1 w s)) φ).1 v) =
      fun s : ℝ => Complex.exp (Fo.cc * ((s : ℂ) * Fo.cw w (q4 D.δ v))) * φ.1 v := by
    funext s
    rw [W.Om_n, character_placeEmbed_exp]
  simp only []
  rw [e1, W.Om_n, character_placeEmbed_exp, he]
  have h0 : HasDerivAt (fun s : ℝ => Fo.cc * ((s : ℂ) * Fo.cw w (q4 D.δ v))) (Fo.cc * Fo.cw w (q4 D.δ v)) t := by
    simpa using (((hasDerivAt_id t).ofReal_comp).mul_const (Fo.cw w (q4 D.δ v))).const_mul Fo.cc
  rw [← mul_assoc (Complex.exp _)]
  exact h0.cexp.mul_const (φ.1 v)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.FstFinGL
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem fst_finGL' {E : Type} [Field E] [NumberField E] (k : GL (Fin 2) (Af E)) :
    Matrix.GeneralLinearGroup.map (RingHom.fst (InfiniteAdeleRing E) (Af E)) (finGL E 2 k) = 1 :=
  map_cornerGL_of_zero _ _ (fun _ => rfl) k

private theorem det_fst {E : Type} [Field E] [NumberField E] (k : GL (Fin 2) (Af E)) :
    ((Matrix.GeneralLinearGroup.det (finGL E 2 k) : (A E)ˣ) : A E).1 = 1 := by
  have h := GlobalTheory.CuspRep.det_map (RingHom.fst (InfiniteAdeleRing E) (Af E)) (finGL E 2 k)
  rw [fst_finGL'] at h
  exact h.symm.trans (by simp)

private theorem norm_fst {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (x : (A E)ˣ) (hx : (x : A E).1 = 1) : ((ideleNorm F E x : (A F)ˣ) : A F).1 = 1 := by
  funext v
  rw [ideleNorm_fst, hx]
  exact Finset.prod_eq_one fun w _ => map_one _

private theorem dM_of_fst {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (t : (A F)ˣ) (ht : (t : A F).1 = 1) :
    finGL F 2 (Matrix.GeneralLinearGroup.map (pFin F) (dM t)) = dM t := by
  have h := TR.infGL_mul_finGL (dM t)
  have h1 : Matrix.GeneralLinearGroup.map (TR.pInf F) (dM t) = 1 := by
    have ht' : TR.pInf F (t : A F) = 1 := by
      change (TR.infEq F).symm (t : A F).1 = 1
      rw [ht]; exact map_one _
    refine Units.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ht']
  rw [h1, map_one, one_mul] at h
  exact h

theorem UpperTheory.ConvolutionTheory.R2.Ff.finTr :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (_D : Dat F E), FinTr F E := by
  intro F E _ _ _ _ _ _ _ _
  let κ : GL (Fin 2) (Af E) →* GL (Fin 2) (Af F) :=
    { toFun := fun k => Matrix.GeneralLinearGroup.map (pFin F) (dM (nu F (finGL E 2 k)))
      map_one' := by simp [nu]
      map_mul' := fun a b => by simp [nu, dM_mul] }
  refine ⟨κ, ?_, fun k => (dM_of_fst _ (norm_fst _ (det_fst k))).symm⟩
  have hp : Continuous (pFin F) := continuous_snd
  have hm : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) (pFin F)) :=
    Continuous.units_map _ (Continuous.matrix_map continuous_id hp)
  have hf : Continuous (finGL E 2) := Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map (continuous_const.prodMk continuous_id :
    Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))))
  exact hm.comp (continuous_dM.comp (continuous_ideleNorm.comp (Matrix.GeneralLinearGroup.continuous_det.comp hf)))
end

