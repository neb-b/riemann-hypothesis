module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
public import GroundTheory.GlobalFields.TateThesis.Bundle0009
public import GroundTheory.AutomorphicForms.Bundle0019
public import GroundTheory.AutomorphicForms.GL2.GJGlobalLattice
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.DifferentiableSchwartzTranslate
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F]

private theorem infPart_add (a b : V4 F) : infPartPi (a + b) = infPartPi a + infPartPi b := by
  funext i
  simp only [infPartPi, Pi.add_apply, homeomorphMixedSpace_apply]
  exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) _ _

variable [IsTotallyReal F]

private noncomputable def ell : (Fin 4 → TR.Rinf F) →L[ℝ] (Fin 4 → mixedEmbedding.mixedSpace F) :=
  AddMonoidHom.toRealLinearMap
    { toFun := fun x => infPartPi fun i => TR.sInf F (x i)
      map_zero' := by
        funext i
        simp only [infPartPi, map_zero, Pi.zero_apply, homeomorphMixedSpace_apply]
        exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
      map_add' := fun x y => by
        have : (fun i => TR.sInf F ((x + y) i)) = (fun i => TR.sInf F (x i)) + fun i => TR.sInf F (y i) := by
          funext i
          simp only [Pi.add_apply, map_add (f := _)]
        rw [this, infPart_add] }
    (continuous_pi fun i => (homeomorphMixedSpace F).continuous.comp
      ((TR.continuous_infEq F).comp (continuous_apply i)))

private theorem differentiable_schwartz_translate (v : V4 F) {Φ : V4 F → ℂ} (h : Φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) :
    Differentiable ℝ fun x : Fin 4 → TR.Rinf F => Φ fun i => v i + TR.sInf F (x i) := by
  induction h using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨f, g, hg, rfl⟩ := hG
    have e : ∀ x : Fin 4 → TR.Rinf F, schwartzBruhatTensorPi f g (fun i => v i + TR.sInf F (x i)) =
        f (infPartPi v + ell x) * g (finPartPi v) := by
      intro x
      have h1 : infPartPi (fun i => v i + TR.sInf F (x i)) = infPartPi v + ell x :=
        infPart_add v fun i => TR.sInf F (x i)
      have h2 : finPartPi (fun i => v i + TR.sInf F (x i)) = finPartPi v := by
        funext i
        exact add_zero (v i).2
      simp only [schwartzBruhatTensorPi, h1, h2]
    simp_rw [e]
    exact (f.differentiable.comp ((differentiable_const _).add ell.differentiable)).mul_const _
  | zero => exact differentiable_const _
  | add G H _ _ hG hH => exact hG.add hH
  | smul c G _ hG => exact hG.const_smul c

end SlopeTestRemainingChoices

theorem UpperTheory.ConvolutionTheory.R2.Ff.sDiff :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (O : Fo.Ops F), SDiff O := by
  intro F _ _ _ O φ v x x' h0 hx
  set G : (Fin 4 → TR.Rinf F) → ℂ := fun y => φ.1 fun i => v i + TR.sInf F (y i) with hG
  have hd : DifferentiableAt ℝ G 0 := differentiable_schwartz_translate v φ.2 0
  have hF : HasFDerivAt G (fderiv ℝ G 0) (x 0) := by
    rw [h0]
    exact hd.hasFDerivAt
  have hc : HasDerivAt (fun t => G (x t)) (fderiv ℝ G 0 x') 0 := hF.comp_hasDerivAt 0 hx
  have hb : ∀ i w, fderiv ℝ G 0 (Pi.single i (Pi.single w 1)) = (O.d w i φ).1 v := by
    intro i w
    set e : Fin 4 → TR.Rinf F := Pi.single i (Pi.single w 1) with he
    have hl : HasDerivAt (fun t : ℝ => t • e) e 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const e
    have hF0 : HasFDerivAt G (fderiv ℝ G 0) ((0 : ℝ) • e) := by
      rw [zero_smul]
      exact hd.hasFDerivAt
    have h1 := hF0.comp_hasDerivAt (0 : ℝ) hl
    have h2 := O.d_spec w i φ v
    have hfun : (fun t : ℝ => G (t • e)) = fun t : ℝ => φ.1 (v + Pi.single i (Fo.at1 w t)) := by
      funext t
      refine congrArg φ.1 ?_
      funext j
      by_cases hj : j = i
      · subst hj
        have : (t • e) j = Pi.single w t := by
          funext u
          by_cases hu : u = w
          · subst hu
            simp [he]
          · simp [he, hu]
        simp [this, Fo.at1]
      · have : (t • e) j = 0 := by simp [he, hj]
        simp [this, hj]
    exact (HasDerivAt.unique (by simpa [Function.comp_def, hfun] using h1) h2)
  have hs : x' = ∑ i, ∑ w, x' i w • (Pi.single i (Pi.single w 1) : Fin 4 → TR.Rinf F) := by
    funext i w
    have h1 : ∀ c, c ≠ i → (∑ u, x' c u • (Pi.single c (Pi.single u 1) : Fin 4 → TR.Rinf F)) i = 0 := by
      intro c hc
      simp [Finset.sum_apply, Pi.single_eq_of_ne hc.symm]
    have h2 : (∑ u, x' i u • (Pi.single i (Pi.single u 1) : Fin 4 → TR.Rinf F)) i w = x' i w := by
      simp [Finset.sum_apply, Pi.single_apply]
    rw [Finset.sum_apply, Finset.sum_eq_single i (fun c _ hc => h1 c hc) (by simp), h2]
  have key : fderiv ℝ G 0 x' = ∑ i, ∑ w, ((x' i w : ℝ) : ℂ) * (O.d w i φ).1 v := by
    conv_lhs => rw [hs]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, hb, Complex.real_smul]
  rw [← key]
  exact hc
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.EmbPiInjective
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Ff

open scoped nonZeroDivisors
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F]

private noncomputable def lw (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (N : ℕ) (ξ : Fin 4 → F) : ℝ :=
  if ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 F)⁰ F) then ((1 + ‖embPi F ξ‖) ^ N)⁻¹ else 0

private theorem lw_nonneg (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (N : ℕ) (ξ : Fin 4 → F) : 0 ≤ lw J N ξ := by
  unfold lw
  split_ifs
  · positivity
  · exact le_rfl

private theorem wt_nonneg (K : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)) (N : ℕ) (v : V4 F) : 0 ≤ wt K N v := by
  unfold wt
  split_ifs
  · positivity
  · exact le_rfl

private theorem summable_lat (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) {N : ℕ}
    (hN : Module.finrank ℝ (Fin 4 → mixedEmbedding.mixedSpace F) < N) :
    Summable fun z : idealLatticePi (K := F) (fun _ : Fin 4 => J) =>
      ((1 + ‖(z : Fin 4 → mixedEmbedding.mixedSpace F)‖) ^ N)⁻¹ := by
  have hrank : Module.finrank ℤ (idealLatticePi (K := F) (fun _ : Fin 4 => J)) < N := by
    rw [ZLattice.rank ℝ (idealLatticePi (K := F) (fun _ : Fin 4 => J))]; exact hN
  have hs := ZLattice.summable_norm_pow_inv (idealLatticePi (K := F) (fun _ : Fin 4 => J)) N hrank
  refine Summable.of_norm_bounded_eventually hs ?_
  filter_upwards [(Set.finite_singleton (0 : idealLatticePi (K := F) (fun _ : Fin 4 => J))).compl_mem_cofinite] with z hz
  have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hz' : ‖z‖ = ‖(z : Fin 4 → mixedEmbedding.mixedSpace F)‖ := rfl
  rw [Real.norm_of_nonneg (inv_nonneg.2 (by positivity)), inv_pow, ← hz']
  gcongr
  linarith

private theorem mem_lat (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) (ξ : Fin 4 → F)
    (h : ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 F)⁰ F)) :
    embPi F ξ ∈ idealLatticePi (K := F) (fun _ : Fin 4 => J) := by
  rw [mem_idealLatticePi]
  intro i
  exact (mixedEmbedding.mem_idealLattice F J).2 ⟨_, h i, rfl⟩

private theorem embPi_injective : Function.Injective (embPi F : (Fin 4 → F) → _) := fun _ _ h =>
  funext fun i => (mixedEmbedding F).injective (congrFun h i)

private theorem summable_lw (J : (FractionalIdeal (𝓞 F)⁰ F)ˣ) {N : ℕ}
    (hN : Module.finrank ℝ (Fin 4 → mixedEmbedding.mixedSpace F) < N) : Summable (lw J N) := by
  have hsT : Summable fun ξ : {ξ : Fin 4 → F | ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 F)⁰ F)} =>
      ((1 + ‖embPi F (ξ : Fin 4 → F)‖) ^ N)⁻¹ := by
    have hinj : Function.Injective fun ξ : {ξ : Fin 4 → F | ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 F)⁰ F)} =>
        (⟨embPi F ξ.1, mem_lat J ξ.1 ξ.2⟩ : idealLatticePi (K := F) (fun _ : Fin 4 => J)) := fun x y h =>
      Subtype.ext (embPi_injective (congrArg Subtype.val h))
    have h := (summable_lat J hN).comp_injective hinj
    refine h.congr fun ξ => ?_
    simp only [Function.comp_apply]
  have heq : lw (F := F) J N = Set.indicator {ξ : Fin 4 → F | ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 F)⁰ F)}
      (fun ξ => ((1 + ‖embPi F ξ‖) ^ N)⁻¹) := by
    funext ξ
    unfold lw
    by_cases h : ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 F)⁰ F)
    · rw [if_pos h, Set.indicator_of_mem (show ξ ∈ {ξ : Fin 4 → F | ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 F)⁰ F)} from h)]
    · rw [if_neg h, Set.indicator_of_notMem (show ξ ∉ {ξ : Fin 4 → F | ∀ i, ξ i ∈ (J : FractionalIdeal (𝓞 F)⁰ F)} from h)]
  rw [heq, ← summable_subtype_iff_indicator]
  exact hsT

private theorem mixed_le {S : Set (IdeleGroup F)} (hS : IsCompact S) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (s : ℝ) (hs : 0 < s), 1 ≤ s → ∀ u ∈ S, ∀ η : F,
      ‖mixedEmbedding F η‖ ≤ B * ‖homeomorphMixedSpace F
        ((((posIdele s hs * u : IdeleGroup F) : A F) * rt η).1)‖ := by
  have hc : Continuous fun u : IdeleGroup F => ∑ w : InfinitePlace F, ‖(((u⁻¹ : IdeleGroup F) : A F)).1 w‖ :=
    continuous_finsetSum _ fun w _ => continuous_norm.comp
      ((continuous_apply w).comp (continuous_fst.comp Units.continuous_coe_inv))
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hc.continuousOn
  set b := max M 1
  have hb1 : 1 ≤ b := le_max_right _ _
  set n : ℝ := (Fintype.card (InfinitePlace F) : ℝ)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  refine ⟨n * b + 1, by nlinarith, fun s hs hs1 u hu η => ?_⟩
  set y := (((posIdele s hs * u : IdeleGroup F) : A F) * rt η).1
  have hub : ∀ w, ‖(((u⁻¹ : IdeleGroup F) : A F)).1 w‖ ≤ b := fun w => by
    refine le_trans ?_ ((le_abs_self _).trans ((Real.norm_eq_abs _ ▸ hM u hu).trans (le_max_left _ _)))
    exact Finset.single_le_sum (f := fun w : InfinitePlace F => ‖(((u⁻¹ : IdeleGroup F) : A F)).1 w‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ w)
  have hw : ∀ w, ‖(rt η : A F).1 w‖ ≤ b * ‖homeomorphMixedSpace F y‖ := fun w => by
    have e1 : y w = ((posIdele s hs : IdeleGroup F) : A F).1 w * (((u : IdeleGroup F) : A F) * rt η).1 w := by
      simp only [y, Units.val_mul, mul_assoc]
      rfl
    have e2 : (rt η : A F).1 w = (((u⁻¹ : IdeleGroup F) : A F)).1 w * (((u : IdeleGroup F) : A F) * rt η).1 w := by
      have : (rt η : A F) = ((u⁻¹ : IdeleGroup F) : A F) * (((u : IdeleGroup F) : A F) * rt η) := by
        rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
      exact congrArg (fun z : A F => z.1 w) this
    have e3 : ‖(((u : IdeleGroup F) : A F) * rt η).1 w‖ ≤ ‖y w‖ := by
      rw [e1, norm_mul, norm_posIdele_infinite]
      nlinarith [norm_nonneg ((((u : IdeleGroup F) : A F) * rt η).1 w)]
    rw [e2, norm_mul]
    exact mul_le_mul (hub w) (e3.trans (GJGlobal.norm_apply_le_norm_homeomorphMixedSpace y w)) (norm_nonneg _)
      (by linarith)
  have h1 : ‖mixedEmbedding F η‖ ≤ ∑ w : InfinitePlace F, ‖(rt η : A F).1 w‖ := by
    have := GJGlobal.norm_homeomorphMixedSpace_le_sum (algebraMap F (InfiniteAdeleRing F) η)
    rw [homeomorphMixedSpace_algebraMap] at this
    exact this
  have h2 : ∑ w : InfinitePlace F, ‖(rt η : A F).1 w‖ ≤ n * (b * ‖homeomorphMixedSpace F y‖) := by
    refine (Finset.sum_le_sum fun w _ => hw w).trans_eq ?_
    simp [n, Finset.card_univ]
  nlinarith [norm_nonneg (homeomorphMixedSpace F y)]

private theorem fin_mem {K : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)} (hK : IsCompact K)
    {S : Set (IdeleGroup F)} (hS : IsCompact S) :
    ∃ J : (FractionalIdeal (𝓞 F)⁰ F)ˣ, ∀ (s : ℝ) (hs : 0 < s), ∀ u ∈ S, ∀ η : Fin 4 → F,
      finPartPi (sc (posIdele s hs * u) η) ∈ K → ∀ i, η i ∈ (J : FractionalIdeal (𝓞 F)⁰ F) := by
  set Kf : Set (FiniteAdeleRing (𝓞 F) F) := ⋃ i : Fin 4, (fun k : Fin 4 → FiniteAdeleRing (𝓞 F) F => k i) '' K
  have hKf : IsCompact Kf := isCompact_iUnion fun i => hK.image (continuous_apply i)
  set Q : Set (FiniteAdeleRing (𝓞 F) F) :=
    (fun p : IdeleGroup F × FiniteAdeleRing (𝓞 F) F => (((p.1⁻¹ : IdeleGroup F) : A F)).2 * p.2) '' (S ×ˢ Kf)
  have hi : Continuous fun u : IdeleGroup F => (((u⁻¹ : IdeleGroup F) : A F)).2 :=
    continuous_snd.comp Units.continuous_coe_inv
  have hQ : IsCompact Q := (hS.prod hKf).image ((hi.comp continuous_fst).mul continuous_snd)
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem_integralFiniteAdeles_of_isCompact hQ
  set dK := algebraMap (𝓞 F) F d
  have hdK : dK ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hd0
  refine ⟨Units.mk0 (FractionalIdeal.spanSingleton (𝓞 F)⁰ dK⁻¹)
    ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr (inv_ne_zero hdK)), fun s hs u hu η hη i => ?_⟩
  have hp : (((posIdele s hs : IdeleGroup F) : A F)).2 = 1 := by
    apply RestrictedProduct.ext
    intro v
    exact posIdele_finite s hs v
  have hmem : algebraMap F (FiniteAdeleRing (𝓞 F) F) (η i) ∈ Q := by
    refine ⟨(u, finPartPi (sc (posIdele s hs * u) η) i),
      ⟨hu, Set.mem_iUnion.2 ⟨i, _, hη, rfl⟩⟩, ?_⟩
    have e1 : finPartPi (sc (posIdele s hs * u) η) i =
        (((u : IdeleGroup F) : A F)).2 * algebraMap F (FiniteAdeleRing (𝓞 F) F) (η i) := by
      change ((((posIdele s hs * u : IdeleGroup F) : A F)) * rt (η i)).2 = _
      rw [Units.val_mul, mul_assoc]
      change (((posIdele s hs : IdeleGroup F) : A F)).2 * _ = _
      rw [hp, one_mul]
      rfl
    have e2 : (((u⁻¹ : IdeleGroup F) : A F)).2 * (((u : IdeleGroup F) : A F)).2 = 1 :=
      congrArg Prod.snd (Units.inv_mul u)
    change (((u⁻¹ : IdeleGroup F) : A F)).2 * finPartPi (sc (posIdele s hs * u) η) i = _
    rw [e1, ← mul_assoc, e2, one_mul]
  have h1 := hd _ hmem
  rw [← map_mul] at h1
  have h2 : dK * η i ∈ ((1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [← algebraMap_mem_idealFiniteAdeles_iff, ← SetLike.mem_coe, idealFiniteAdeles_one]
    exact h1
  rw [Units.val_one] at h2
  obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).mp h2
  refine (FractionalIdeal.mem_spanSingleton _).mpr ⟨r, ?_⟩
  rw [Algebra.smul_def, hr, mul_comm dK, mul_assoc, mul_inv_cancel₀ hdK, mul_one]

private theorem wt_le {K : Set (Fin 4 → FiniteAdeleRing (𝓞 F) F)} {J : (FractionalIdeal (𝓞 F)⁰ F)ˣ}
    {B : ℝ} (hB : 1 ≤ B) {a : (A F)ˣ}
    (hfin : ∀ η : Fin 4 → F, finPartPi (sc a η) ∈ K → ∀ i, η i ∈ (J : FractionalIdeal (𝓞 F)⁰ F))
    (hinf : ∀ η : F, ‖mixedEmbedding F η‖ ≤ B * ‖homeomorphMixedSpace F (((a : A F) * rt η).1)‖)
    (N : ℕ) (η : Fin 4 → F) : wt K N (sc a η) ≤ B ^ N * lw J N η := by
  have hB0 : 0 < B := one_pos.trans_le hB
  by_cases h : finPartPi (sc a η) ∈ K
  · unfold wt lw
    rw [if_pos h, if_pos (hfin η h)]
    have h1 : ‖embPi F η‖ ≤ B * ‖infPartPi (sc a η)‖ :=
      (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (hinf (η i)).trans
        (mul_le_mul_of_nonneg_left (norm_le_pi_norm (infPartPi (sc a η)) i) hB0.le)
    have h2 : 1 + ‖embPi F η‖ ≤ B * (1 + ‖infPartPi (sc a η)‖) := by linarith
    calc ((1 + ‖infPartPi (sc a η)‖) ^ N)⁻¹ = B ^ N * ((B * (1 + ‖infPartPi (sc a η)‖)) ^ N)⁻¹ := by
          rw [mul_pow, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
      _ ≤ B ^ N * ((1 + ‖embPi F η‖) ^ N)⁻¹ := by gcongr
  · unfold wt
    rw [if_neg h]
    exact mul_nonneg (by positivity) (lw_nonneg _ _ _)

end SlopeTestRemainingChoices

end UpperTheory.ConvolutionTheory.R2.Ff

open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction in
theorem UpperTheory.ConvolutionTheory.R2.Ff.wtSum :
    ∀ (F : Type) [Field F] [NumberField F], WtSum F := by
  intro F _ _
  refine ⟨Module.finrank ℝ (Fin 4 → mixedEmbedding.mixedSpace F) + 1, fun K hK c hc => ?_⟩
  set N := Module.finrank ℝ (Fin 4 → mixedEmbedding.mixedSpace F) + 1 with hNdef
  obtain ⟨S, hS, hSm⟩ := exists_isCompact_mul_mem_of_ideleModule_mem_Icc (K := F) hc c
  obtain ⟨J, hJ⟩ := fin_mem hK hS
  obtain ⟨B, hB1, hB⟩ := mixed_le hS
  have hsum : Summable (lw J N) := summable_lw J (Nat.lt_succ_self _)
  have hB0 : 0 ≤ B ^ N := pow_nonneg (zero_le_one.trans hB1) _
  refine ⟨B ^ N * ∑' ξ, lw J N ξ, fun a ha => ?_⟩
  set d := Module.finrank ℚ F
  have hd : d ≠ 0 := Module.finrank_pos.ne'
  have hx : 1 ≤ ab a / c := (one_le_div hc).2 ha
  set s := (ab a / c) ^ (d : ℝ)⁻¹
  have hs1 : 1 ≤ s := Real.one_le_rpow hx (by positivity)
  have hs0 : 0 < s := one_pos.trans_le hs1
  have hsd : s ^ d = ab a / c := Real.rpow_inv_natCast_pow (zero_le_one.trans hx) hd
  set p : IdeleGroup F := posIdele s hs0 with hp
  have hm : (IdeleGroup.ideleModule F (p⁻¹ * a) : ℝ) = c := by
    have h1 : (IdeleGroup.ideleModule F (p⁻¹ * a) : ℝ) =
        ((IdeleGroup.ideleModule F p : ℝ))⁻¹ * (IdeleGroup.ideleModule F a : ℝ) := by
      simp [map_mul, map_inv]
    have h2 : (0 : ℝ) < ab a := hc.trans_le ha
    rw [h1, hp, ideleModule_posIdele, hsd]
    change (ab a / c)⁻¹ * ab a = c
    field_simp
  obtain ⟨t, ht⟩ := hSm _ hm.ge hm.le
  set u := IdeleGroup.diagonal F t * (p⁻¹ * a) with hu
  have hau : IdeleGroup.diagonal F t * a = p * u := by
    rw [hu, mul_left_comm, mul_inv_cancel_left]
  let e : (Fin 4 → F) ≃ (Fin 4 → F) := Equiv.piCongrRight fun _ => Units.mulLeft t
  have hsc : ∀ ξ, sc a (e ξ) = sc (p * u) ξ := fun ξ => by
    funext i
    have h1 : ((IdeleGroup.diagonal F t : IdeleGroup F) : A F) = rt (t : F) := IdeleGroup.coe_diagonal _ _
    have h2 : ((p * u : IdeleGroup F) : A F) = (a : A F) * rt (t : F) := by
      rw [← hau, Units.val_mul, h1, mul_comm]
    change (a : A F) * rt ((t : F) * ξ i) = ((p * u : IdeleGroup F) : A F) * rt (ξ i)
    rw [h2, show rt ((t : F) * ξ i) = rt (t : F) * rt (ξ i) from map_mul _ _ _, mul_assoc]
  have hle : ∀ ξ, wt K N (sc a (e ξ)) ≤ B ^ N * lw J N ξ := fun ξ => by
    rw [hsc]
    exact wt_le hB1 (hJ s hs0 u ht) (hB s hs0 hs1 u ht) N ξ
  have hs' : Summable fun ξ => wt K N (sc a (e ξ)) :=
    Summable.of_nonneg_of_le (fun _ => wt_nonneg _ _ _) hle (hsum.mul_left _)
  refine ⟨e.summable_iff.1 hs', ?_⟩
  rw [← e.tsum_eq, ← tsum_mul_left]
  exact hs'.tsum_le_tsum hle (hsum.mul_left _)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.ExValCont
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Ff

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

open scoped Matrix.Norms.Operator

private theorem ex_val (X : Lie E 2) (t : ℝ) : (ex X t).val = NormedSpace.exp (t • Matrix.of X) := rfl

private theorem ex_add (X : Lie E 2) (s t : ℝ) : ex X (s + t) = ex X s * ex X t := by
  refine Units.ext ?_
  rw [Units.val_mul, ex_val, ex_val, ex_val, add_smul]
  exact NormedSpace.exp_add_of_commute (((Commute.refl (Matrix.of X)).smul_left s).smul_right t)

private theorem ex_zero (X : Lie E 2) : ex X 0 = 1 := by
  refine Units.ext ?_
  rw [ex_val, zero_smul, NormedSpace.exp_zero]
  rfl

private theorem ex_inv (X : Lie E 2) (t : ℝ) : (ex X t)⁻¹ = ex X (-t) :=
  inv_eq_of_mul_eq_one_right (by rw [← ex_add, add_neg_cancel, ex_zero])

private theorem ex_val_cont (X : Lie E 2) : Continuous fun t : ℝ => (ex X t).val :=
  continuous_iff_continuousAt.2 fun t =>
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) (Matrix.of X) t).continuousAt

private theorem ex_cont (X : Lie E 2) : Continuous (ex X) := by
  refine Units.continuous_iff.2 ⟨ex_val_cont X, ?_⟩
  simp only [ex_inv]
  exact (ex_val_cont X).comp continuous_neg

private theorem ex_der (X : Lie E 2) : HasDerivAt (fun t => toL (ex X t).val) X 0 := by
  let L : Matrix (Fin 2) (Fin 2) (Cinf E) →L[ℝ] Lie E 2 :=
    { toLinearMap := (Matrix.ofLinearEquiv ℝ).symm.toLinearMap, cont := continuous_id }
  have h : HasDerivAt (fun t : ℝ => L (NormedSpace.exp (t • Matrix.of X)))
      (L (NormedSpace.exp ((0 : ℝ) • Matrix.of X) * Matrix.of X)) 0 :=
    L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_exp_smul_const (𝕂 := ℝ) (Matrix.of X) (0 : ℝ))
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h
  exact h

private theorem ex_ent (X : Lie E 2) (i j : Fin 2) :
    HasDerivAt (fun t => (ex X t).val i j) (X i j) 0 :=
  hasDerivAt_pi.1 (hasDerivAt_pi.1 (ex_der X) i) j

private theorem ex_det_der (X : Lie E 2) :
    HasDerivAt (fun t => (ex X t).val.det) ((Matrix.of X).trace) 0 := by
  have h := ((ex_ent X 0 0).mul (ex_ent X 1 1)).sub ((ex_ent X 0 1).mul (ex_ent X 1 0))
  have e0 : (ex X 0).val = 1 := by rw [ex_zero]; rfl
  simp only [e0, Matrix.one_apply_eq, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true,
    Matrix.one_apply_ne, mul_one, one_mul, zero_mul, mul_zero, add_zero, sub_zero] at h
  rw [Matrix.trace_fin_two]
  simp only [Matrix.det_fin_two]
  exact h

private theorem ex_det (X : Lie E 2) (hX : (Matrix.of X).trace = 0) (t : ℝ) : (ex X t).val.det = 1 := by
  have hm : ∀ s t, (ex X (s + t)).val.det = (ex X s).val.det * (ex X t).val.det := fun s t => by
    rw [ex_add, Units.val_mul, Matrix.det_mul]
  have hd : ∀ t, HasDerivAt (fun s => (ex X s).val.det) (0 : Cinf E) t := fun t => by
    have h0 := ex_det_der X
    rw [hX] at h0
    have h1 : HasDerivAt (fun s => (ex X (s - t)).val.det) (0 : Cinf E) t :=
      HasDerivAt.comp_sub_const t t (by simpa using h0)
    have h2 := h1.const_mul (ex X t).val.det
    rw [mul_zero] at h2
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
    show (ex X s).val.det = (ex X t).val.det * (ex X (s - t)).val.det
    rw [← hm, add_sub_cancel]
  have hc := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv) t 0
  have e0 : (ex X 0).val = 1 := by rw [ex_zero]; rfl
  simpa [e0] using hc

private theorem ex_cen (X : Lie E 2) (s : Cinf E) (t : ℝ) : ex (X + zE s) t = ex (zE s) t * ex X t := by
  refine Units.ext ?_
  rw [Units.val_mul, ex_val, ex_val, ex_val]
  have e : Matrix.of (X + zE s) = Matrix.of (zE s) + Matrix.of X := by
    rw [add_comm]; rfl
  have c : Commute (Matrix.of (zE s)) (Matrix.of X) :=
    Matrix.scalar_commute s (fun r => Commute.all _ _) (Matrix.of X)
  rw [e, smul_add]
  exact NormedSpace.exp_add_of_commute ((c.smul_left t).smul_right t)

end

end UpperTheory.ConvolutionTheory.R2.Ff

theorem UpperTheory.ConvolutionTheory.R2.Ff.exPar :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E], ExPar E := by
  intro E _ _ _ X
  exact ⟨ex_add X, ex_cont X, ex_der X, ex_det X, fun s t => ex_cen X s t⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.LCen
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.lCen :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), LCen W := by
  intro F E _ _ _ _ _ _ _ D W z
  refine ⟨LinearMap.ext fun φ => Subtype.ext (funext fun v => ?_), nu_scalar z⟩
  have hη : W.η.1 (ideleNorm F E z)⁻¹ = 1 := by rw [map_inv, W.η_norm, inv_one]
  have hs : (Matrix.GeneralLinearGroup.scalar (Fin 2) z)⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 2) z⁻¹ :=
    (map_inv _ _).symm
  have hv : D.act (Matrix.GeneralLinearGroup.scalar (Fin 2) z)⁻¹ v =
      fun i => (((ideleNorm F E z)⁻¹ : (A F)ˣ) : A F) * v i := by
    rw [hs, D.act_scalar, map_inv]; rfl
  rw [W.L_apply, W.Om_m, nu_scalar, hv, hη, ab_inv, ab_pow]
  simp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.LieSplit
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.lieSplit {E : Type} [Field E] [NumberField E] (X : Lie E 2) :
    ∃ (Y : Lie E 2) (s : Cinf E), (Matrix.of Y).trace = 0 ∧ X = Y + zE s ∧ X 0 0 + X 1 1 = s + s := by
  have h : X 0 0 + X 1 1 = (2⁻¹ : ℝ) • (X 0 0 + X 1 1) + (2⁻¹ : ℝ) • (X 0 0 + X 1 1) := by
    rw [← add_smul]; norm_num
  refine ⟨X - zE ((2⁻¹ : ℝ) • (X 0 0 + X 1 1)), _, ?_, (sub_add_cancel _ _).symm, h⟩
  rw [Matrix.trace_fin_two]
  change (X 0 0 - (2⁻¹ : ℝ) • (X 0 0 + X 1 1)) + (X 1 1 - (2⁻¹ : ℝ) • (X 0 0 + X 1 1)) = 0
  linear_combination h
end

