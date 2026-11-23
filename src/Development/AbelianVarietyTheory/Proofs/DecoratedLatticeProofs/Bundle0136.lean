module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0237
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0127
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0522
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0130

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmIntegralComm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.CommInt

theorem om_integral_comm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (U : Type) [TopologicalSpace U] [SecondCountableTopology U] [MeasurableSpace U] [BorelSpace U] (m : Measure U) [SFinite m] (F : U → WO S T → ℂ) (p : GA D S × GA D T) (β : U → ℝ), (∀ u, IsThetaFunO ψ S T (F u)) → Continuous (Function.uncurry F) → Continuous (fun q : U × WO S T => om p (F q.1) q.2) → Integrable β m → (∀ u w, ‖F u w‖ ≤ β u ∧ ‖om p (F u) w‖ ≤ β u) → IsThetaFunO ψ S T (fun w => ∫ u, F u w ∂m) → ∀ w, om p (fun w' => ∫ u, F u w' ∂m) w = ∫ u, om p (F u) w ∂m := by
  intro D ψ S T χS χT om hom U _ _ _ _ m _ F p β hF hFc hOc hβ hdom hG w
  have hψ := hom.std
  obtain ⟨-, -, i3, -, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  haveI : FirstCountableTopology (WO S T) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := GlobalTheory.Size.exists_isCovolOne S T
  haveI hfin : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  haveI : SFinite (μ.restrict 𝓕) := @instSFiniteOfSigmaFinite _ _ _ (@IsFiniteMeasure.toSigmaFinite _ _ _ hfin)
  set G : WO S T → ℂ := fun w => ∫ u, F u w ∂m with hGdef
  set H : WO S T → ℂ := fun w => ∫ u, om p (F u) w ∂m with hHdef
  have hHc : Continuous H := by
    refine continuous_of_dominated (bound := β) (fun x => ?_) (fun x => ?_) hβ ?_
    · exact (hOc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun u => (hdom u x).2
    · exact Filter.Eventually.of_forall fun u => hOc.comp (continuous_const.prodMk continuous_id)
  have hHb : ∀ x, ‖H x‖ ≤ ∫ u, β u ∂m := fun x =>
    norm_integral_le_of_norm_le hβ (Filter.Eventually.of_forall fun u => (hdom u x).2)
  have hOG := hom.om_pres p _ hG
  set q : WO S T → ℂ := fun x => om p G x - H x with hqdef
  have hq : q = 0 := by
    refine _root_.GlobalTheory.ThetaOrthTotal.eq_zero_of_orthogonal_theta D ψ hψ S T μ 𝓕 hμ h𝓕 q (hOG.cont.sub hHc) ?_ ?_
    · intro γ x
      have e1 := hOG.quasi γ x
      have e2 : H (ratW T S γ + x) = ψ (-(symplOH S T (ratW T S γ) x)) * H x := by
        simp only [hHdef]
        rw [← integral_const_mul]
        congr 1
        funext u
        exact (hom.om_pres p _ (hF u)).quasi γ x
      simp only [hqdef]
      rw [e1, e2]
      ring
    · intro f hf

      haveI : SecondCountableTopology (WO S T) := i3
      obtain ⟨CG, hCG⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ _ hOG
      have hf0 := hom.om_pres p⁻¹ f hf
      have hff0 : om p (om p⁻¹ f) = f := by
        change (om p * om p⁻¹) f = f
        rw [← map_mul, mul_inv_cancel, map_one]; rfl
      set f0 := om p⁻¹ f with hf0def
      obtain ⟨C0, hC0⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ _ hf0
      obtain ⟨Cf, hCf⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ _ hf
      have hint : ∀ (g h : WO S T → ℂ) (a b : ℝ), Continuous g → Continuous h → (∀ x, ‖g x‖ ≤ a) →
          (∀ x, ‖h x‖ ≤ b) → Integrable (fun x => g x * star (h x)) (μ.restrict 𝓕) := by
        intro g h a b hg hh ha hb
        refine Integrable.mono' (integrable_const (a * b)) (hg.mul hh.star).aestronglyMeasurable
          (ae_of_all _ fun x => ?_)
        rw [norm_mul, norm_star]
        exact mul_le_mul (ha x) (hb x) (norm_nonneg _) ((norm_nonneg _).trans (ha x))
      have hprod : ∀ (K : U → WO S T → ℂ) (h : WO S T → ℂ) (b : ℝ), Continuous (fun z : U × WO S T => K z.1 z.2) →
          (∀ u x, ‖K u x‖ ≤ β u) → Continuous h → (∀ x, ‖h x‖ ≤ b) →
          Integrable (Function.uncurry fun x u => K u x * star (h x)) ((μ.restrict 𝓕).prod m) := by
        intro K h b hK hKb hh hb
        refine Integrable.mono' (((integrable_const b).mul_prod hβ)) ?_ (ae_of_all _ fun z => ?_)
        · exact ((hK.comp (continuous_snd.prodMk continuous_fst)).mul (hh.comp continuous_fst).star).aestronglyMeasurable
        · show ‖K z.2 z.1 * star (h z.1)‖ ≤ b * β z.2
          rw [norm_mul, norm_star, mul_comm b]
          exact mul_le_mul (hKb z.2 z.1) (hb z.1) (norm_nonneg _) ((norm_nonneg _).trans (hKb z.2 z.1))
      have hsc := fun g g' (hg : IsThetaFunO ψ S T g) (hg' : IsThetaFunO ψ S T g') =>
        GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hψ S T μ 𝓕 hμ h𝓕 (om p) (hom.om_pres p) (hom.om_unit μ 𝓕 hμ h𝓕 p) g g' hg hg'
      have A : ∫ x in 𝓕, om p G x * star (f x) ∂μ = ∫ x in 𝓕, G x * star (f0 x) ∂μ := by
        rw [← hff0]; exact hsc G f0 hG hf0
      have B : ∫ x in 𝓕, G x * star (f0 x) ∂μ = ∫ x in 𝓕, H x * star (f x) ∂μ := by
        calc ∫ x in 𝓕, G x * star (f0 x) ∂μ = ∫ x in 𝓕, ∫ u, F u x * star (f0 x) ∂m ∂μ := by
              refine integral_congr_ae (ae_of_all _ fun x => ?_)
              show (∫ u, F u x ∂m) * star (f0 x) = ∫ u, F u x * star (f0 x) ∂m
              rw [integral_mul_const]
          _ = ∫ u, ∫ x in 𝓕, F u x * star (f0 x) ∂μ ∂m :=
              integral_integral_swap (hprod F f0 C0 hFc (fun u x => (hdom u x).1) hf0.cont hC0)
          _ = ∫ u, ∫ x in 𝓕, om p (F u) x * star (f x) ∂μ ∂m := by
              refine integral_congr_ae (ae_of_all _ fun u => ?_)
              rw [← hff0]; exact (hsc (F u) f0 (hF u) hf0).symm
          _ = ∫ x in 𝓕, ∫ u, om p (F u) x * star (f x) ∂m ∂μ :=
              (integral_integral_swap (hprod (fun u => om p (F u)) f Cf hOc (fun u x => (hdom u x).2) hf.cont hCf)).symm
          _ = ∫ x in 𝓕, H x * star (f x) ∂μ := by
              refine integral_congr_ae (ae_of_all _ fun x => ?_)
              show ∫ u, om p (F u) x * star (f x) ∂m = (∫ u, om p (F u) x ∂m) * star (f x)
              rw [integral_mul_const]
      have i1 := hint (om p G) f CG Cf hOG.cont hf.cont hCG hCf
      have i2 := hint H f (∫ u, β u ∂m) Cf hHc hf.cont hHb hCf
      simp only [hqdef, sub_mul]
      rw [integral_sub i1 i2, A, B, sub_self]
  have := congrFun hq w
  simp only [hqdef, Pi.zero_apply, sub_eq_zero] at this
  exact this

end GlobalTheory.CommInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PiTensorSubmoduleEqTopOfAbsolutelyIrreducibleSta
section
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.TensorIrr

open GlobalTheory.Chain.IoLift

variable {ι : Type} [Fintype ι] {K : ι → Type} [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)]

theorem position_add (i : ι) (f g : Module.End ℂ (K i)) : intersection_update_fsHerm_neg_one i (f + g) = intersection_update_fsHerm_neg_one i f + intersection_update_fsHerm_neg_one i g := by
  ext v
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.add_apply, position_tprod, LinearMap.add_apply]
  rw [← MultilinearMap.map_update_add]

theorem position_mul (i : ι) (f g : Module.End ℂ (K i)) : intersection_update_fsHerm_neg_one i (f * g) = intersection_update_fsHerm_neg_one i f ∘ₗ intersection_update_fsHerm_neg_one i g := by
  ext v
  simp [position_tprod]

theorem position_algebraMap (i : ι) (c : ℂ) :
    intersection_update_fsHerm_neg_one i (algebraMap ℂ (Module.End ℂ (K i)) c) = c • LinearMap.id := by
  ext v
  simp only [LinearMap.compMultilinearMap_apply, position_tprod, LinearMap.smul_apply, LinearMap.id_apply]
  rw [Module.algebraMap_end_apply, MultilinearMap.map_update_smul, Function.update_eq_self]
  rfl

theorem stable_adjoin_position (i : ι) {G : Type} (a : G → Module.End ℂ (K i))
    (N : Submodule ℂ (⨂[ℂ] j, K j)) (hN : ∀ g, ∀ x ∈ N, intersection_update_fsHerm_neg_one i (a g) x ∈ N)
    {r : Module.End ℂ (K i)} (hr : r ∈ Algebra.adjoin ℂ (Set.range a)) :
    ∀ y ∈ N, intersection_update_fsHerm_neg_one i r y ∈ N := by
  induction hr using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨g, rfl⟩ := hx; exact hN g
  | algebraMap c =>
    intro y hy
    rw [position_algebraMap]
    exact N.smul_mem c hy
  | add x y _ _ hx hy =>
    intro z hz
    rw [position_add]
    exact N.add_mem (hx z hz) (hy z hz)
  | mul x y _ _ hx hy =>
    intro z hz
    rw [position_mul]
    exact hx _ (hy z hz)

theorem exists_finset_position (i : ι) (t : ⨂[ℂ] j, K j) :
    ∃ s : Finset (K i), ∀ f g : Module.End ℂ (K i), (∀ m ∈ s, f m = g m) → intersection_update_fsHerm_neg_one i f t = intersection_update_fsHerm_neg_one i g t := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r u =>
    refine ⟨{u i}, fun f g h => ?_⟩
    rw [map_smul, map_smul, position_tprod, position_tprod, h (u i) (Finset.mem_singleton_self _)]
  | add x y hx hy =>
    obtain ⟨s, hs⟩ := hx
    obtain ⟨s', hs'⟩ := hy
    refine ⟨s ∪ s', fun f g h => ?_⟩
    rw [map_add (f := _), map_add (f := _), hs f g fun m hm => h m (Finset.mem_union_left _ hm),
      hs' f g fun m hm => h m (Finset.mem_union_right _ hm)]

theorem eq_zero_of_subsingleton (i : ι) [Subsingleton (K i)] (t : ⨂[ℂ] j, K j) : t = 0 := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r u =>
    rw [MultilinearMap.map_coord_zero _ i (Subsingleton.elim _ _), smul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

end GlobalTheory.TensorIrr

namespace GlobalTheory.TensorIrr

open GlobalTheory.Chain.IoLift

variable {ι : Type} [Fintype ι] {K : ι → Type} [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)]

theorem stable_all_position (i : ι) {G : Type} (a : G → Module.End ℂ (K i)) (ha : AbsIrr a) [Nontrivial (K i)]
    (N : Submodule ℂ (⨂[ℂ] j, K j)) (hN : ∀ g, ∀ x ∈ N, intersection_update_fsHerm_neg_one i (a g) x ∈ N)
    (f : Module.End ℂ (K i)) : ∀ y ∈ N, intersection_update_fsHerm_neg_one i f y ∈ N := by
  intro y hy
  obtain ⟨s, hs⟩ := exists_finset_position i y
  obtain ⟨r, hr, hfr⟩ := GlobalTheory.IrrTensor.density a ha.1 ha.2 f s
  rw [hs f r hfr]
  exact stable_adjoin_position i a N hN hr y hy

theorem stable_map (N : Submodule ℂ (⨂[ℂ] j, K j))
    (hN : ∀ i (f : Module.End ℂ (K i)), ∀ y ∈ N, intersection_update_fsHerm_neg_one i f y ∈ N) (f : ∀ i, Module.End ℂ (K i)) :
    ∀ y ∈ N, PiTensorProduct.map f y ∈ N := by
  have key : ∀ s : Finset ι, ∀ y ∈ N,
      PiTensorProduct.map (fun i => if i ∈ s then f i else LinearMap.id) y ∈ N := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro y hy; simpa using hy
    | insert i s hi ih =>
      have : PiTensorProduct.map (fun j => if j ∈ insert i s then f j else LinearMap.id) =
          intersection_update_fsHerm_neg_one i (f i) ∘ₗ PiTensorProduct.map (fun i => if i ∈ s then f i else LinearMap.id) := by
        ext v
        simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, PiTensorProduct.map_tprod,
          position_tprod]
        congr 1
        funext j
        by_cases hj : j = i
        · subst hj; simp [hi]
        · simp [hj]
      intro y hy
      rw [this, LinearMap.comp_apply]
      exact hN i (f i) _ (ih y hy)
  intro y hy
  simpa using key Finset.univ y hy

theorem eq_top_of_stable : ∀ (ι : Type) [Fintype ι] (K : ι → Type) [∀ i, AddCommGroup (K i)] [∀ i, Module ℂ (K i)] (G : ι → Type) (a : ∀ i, G i → Module.End ℂ (K i)), (∀ i, GlobalTheory.Chain.IoLift.AbsIrr (a i)) → ∀ N : Submodule ℂ (PiTensorProduct ℂ K), (∀ i g, ∀ x ∈ N, GlobalTheory.Chain.IoLift.intersection_update_fsHerm_neg_one i (a i g) x ∈ N) → N ≠ ⊥ → N = ⊤ := by
  intro ι _ K _ _ G a ha N hN hne
  obtain ⟨x, hxN, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hnt : ∀ i, Nontrivial (K i) := by
    intro i
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact hx0 (eq_zero_of_subsingleton i x)
  have hall : ∀ i (f : Module.End ℂ (K i)), ∀ y ∈ N, intersection_update_fsHerm_neg_one i f y ∈ N := fun i f =>
    stable_all_position i (a i) (ha i) N (hN i) f
  obtain ⟨w, hw⟩ : ∃ w, Scal.tform w x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hx0 (Scal.eq_of_tform fun w => by rw [h w, map_zero])
  have htp : ∀ v : ∀ i, K i, PiTensorProduct.tprod ℂ v ∈ N := by
    intro v
    have hm : PiTensorProduct.map (fun i => (w i).smulRight (v i)) =
        (Scal.tform w).smulRight (PiTensorProduct.tprod ℂ v) := by
      ext u
      simp [Scal.tform_tprod, MultilinearMap.map_smul_univ]
    have h1 := stable_map N hall (fun i => (w i).smulRight (v i)) x hxN
    rw [hm, LinearMap.smulRight_apply] at h1
    have h2 := N.smul_mem (Scal.tform w x)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hw, one_smul] at h2
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  exact htp v

end GlobalTheory.TensorIrr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFunctionsSumUniformLimitProductSpan
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.DenseSum

theorem unifLimit_prodSpan : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S A B T : HSp D) (o : OrthDec S A B), ∀ f, IsThetaFunO ψ S T f → GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.UnifLimit (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.prodSpan (o.resS T) (IsThetaFunO ψ A T) (IsThetaFunO ψ B T)) f := by
  intro D ψ hψ S A B T o f hf ε hε
  obtain ⟨n, P, g, hPc, hPl, hg, hfg⟩ := _root_.GlobalTheory.ThetaSplitApprox.exists_approx D ψ hψ S A B T o f hf (ε / 2) (by positivity)
  have hb : ∀ i, ∃ C : ℝ, ∀ v, ‖g i v‖ ≤ C := fun i =>
    GlobalTheory.IsoMean.isThetaFunO_bounded B T ψ hψ (g i) (hg i)
  choose C hC using hb
  set M : ℝ := 1 + ∑ i, |C i| with hMdef
  have hM : 0 < M := by
    have : 0 ≤ ∑ i, |C i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    linarith
  have hδ : 0 < ε / (2 * M) := by positivity
  have hφ : ∀ i, ∃ φ : WO A T → ℂ, IsThetaFunO ψ A T φ ∧ ∀ u, ‖P i u - φ u‖ ≤ ε / (2 * M) := fun i =>
    _root_.GlobalTheory.HeisSmoothing.exists_theta_near D ψ hψ A T (P i) (hPc i) (hPl i) _ hδ
  choose φ hφt hφa using hφ
  refine ⟨∑ i, fun w => φ i ((o.resS T) w).1 * g i ((o.resS T) w).2, ?_, ?_⟩
  · exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨φ i, g i, hφt i, hg i, rfl⟩
  · intro w
    have key : ‖∑ i, P i ((o.resS T) w).1 * g i ((o.resS T) w).2 -
        ∑ i, φ i ((o.resS T) w).1 * g i ((o.resS T) w).2‖ ≤ ε / 2 := by
      rw [← Finset.sum_sub_distrib]
      calc _ ≤ ∑ i, ‖P i ((o.resS T) w).1 * g i ((o.resS T) w).2 - φ i ((o.resS T) w).1 * g i ((o.resS T) w).2‖ :=
            norm_sum_le _ _
        _ ≤ ∑ i, ε / (2 * M) * |C i| := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [← sub_mul, norm_mul]
            exact mul_le_mul (hφa i _) ((hC i _).trans (le_abs_self _)) (norm_nonneg _) hδ.le
        _ = ε / (2 * M) * ∑ i, |C i| := by rw [Finset.mul_sum]
        _ ≤ ε / (2 * M) * M := by
            refine mul_le_mul_of_nonneg_left ?_ hδ.le
            rw [hMdef]; linarith
        _ = ε / 2 := by field_simp
    have hsum : (∑ i, fun w => φ i ((o.resS T) w).1 * g i ((o.resS T) w).2) w =
        ∑ i, φ i ((o.resS T) w).1 * g i ((o.resS T) w).2 := by
      simp [Finset.sum_apply]
    rw [hsum]
    calc ‖f w - ∑ i, φ i ((o.resS T) w).1 * g i ((o.resS T) w).2‖
        = ‖(f w - ∑ i, P i ((o.resS T) w).1 * g i ((o.resS T) w).2) +
          (∑ i, P i ((o.resS T) w).1 * g i ((o.resS T) w).2 - ∑ i, φ i ((o.resS T) w).1 * g i ((o.resS T) w).2)‖ := by
          congr 1; ring
      _ ≤ ε / 2 + ε / 2 := (norm_add_le _ _).trans (add_le_add (hfg w) key)
      _ = ε := by ring

end GlobalTheory.DenseSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorIntegralCommOfBoundedFiniteMeasure
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.CommIntBdd

theorem om_integral_comm_dom : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (U : Type) [TopologicalSpace U] [SecondCountableTopology U] [MeasurableSpace U] [BorelSpace U] (m : Measure U) [SFinite m] (F : U → WO S T → ℂ) (p : GA D S × GA D T) (β : U → ℝ), (∀ u, IsThetaFunO ψ S T (F u)) → Continuous (Function.uncurry F) → Continuous (fun q : U × WO S T => om p (F q.1) q.2) → Integrable β m → (∀ u w, ‖F u w‖ ≤ β u ∧ ‖om p (F u) w‖ ≤ β u) → IsThetaFunO ψ S T (fun w => ∫ u, F u w ∂m) → ∀ w, om p (fun w' => ∫ u, F u w' ∂m) w = ∫ u, om p (F u) w ∂m := by
  intro D ψ S T χS χT om hom U _ _ _ _ m _ F p β hF hFc hOc hβ hdom hG w
  have hψ := hom.std
  obtain ⟨-, -, i3, -, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  haveI : FirstCountableTopology (WO S T) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := GlobalTheory.Size.exists_isCovolOne S T
  haveI hfin : IsFiniteMeasure (μ.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  haveI : SFinite (μ.restrict 𝓕) := @instSFiniteOfSigmaFinite _ _ _ (@IsFiniteMeasure.toSigmaFinite _ _ _ hfin)
  set G : WO S T → ℂ := fun w => ∫ u, F u w ∂m with hGdef
  set H : WO S T → ℂ := fun w => ∫ u, om p (F u) w ∂m with hHdef
  have hHc : Continuous H := by
    refine continuous_of_dominated (bound := β) (fun x => ?_) (fun x => ?_) hβ ?_
    · exact (hOc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun u => (hdom u x).2
    · exact Filter.Eventually.of_forall fun u => hOc.comp (continuous_const.prodMk continuous_id)
  have hHb : ∀ x, ‖H x‖ ≤ ∫ u, β u ∂m := fun x =>
    norm_integral_le_of_norm_le hβ (Filter.Eventually.of_forall fun u => (hdom u x).2)
  have hOG := hom.om_pres p _ hG
  set q : WO S T → ℂ := fun x => om p G x - H x with hqdef
  have hq : q = 0 := by
    refine _root_.GlobalTheory.ThetaOrthTotal.eq_zero_of_orthogonal_theta D ψ hψ S T μ 𝓕 hμ h𝓕 q (hOG.cont.sub hHc) ?_ ?_
    · intro γ x
      have e1 := hOG.quasi γ x
      have e2 : H (ratW T S γ + x) = ψ (-(symplOH S T (ratW T S γ) x)) * H x := by
        simp only [hHdef]
        rw [← integral_const_mul]
        congr 1
        funext u
        exact (hom.om_pres p _ (hF u)).quasi γ x
      simp only [hqdef]
      rw [e1, e2]
      ring
    · intro f hf

      haveI : SecondCountableTopology (WO S T) := i3
      obtain ⟨CG, hCG⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ _ hOG
      have hf0 := hom.om_pres p⁻¹ f hf
      have hff0 : om p (om p⁻¹ f) = f := by
        change (om p * om p⁻¹) f = f
        rw [← map_mul, mul_inv_cancel, map_one]; rfl
      set f0 := om p⁻¹ f with hf0def
      obtain ⟨C0, hC0⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ _ hf0
      obtain ⟨Cf, hCf⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ _ hf
      have hint : ∀ (g h : WO S T → ℂ) (a b : ℝ), Continuous g → Continuous h → (∀ x, ‖g x‖ ≤ a) →
          (∀ x, ‖h x‖ ≤ b) → Integrable (fun x => g x * star (h x)) (μ.restrict 𝓕) := by
        intro g h a b hg hh ha hb
        refine Integrable.mono' (integrable_const (a * b)) (hg.mul hh.star).aestronglyMeasurable
          (ae_of_all _ fun x => ?_)
        rw [norm_mul, norm_star]
        exact mul_le_mul (ha x) (hb x) (norm_nonneg _) ((norm_nonneg _).trans (ha x))
      have hprod : ∀ (K : U → WO S T → ℂ) (h : WO S T → ℂ) (b : ℝ), Continuous (fun z : U × WO S T => K z.1 z.2) →
          (∀ u x, ‖K u x‖ ≤ β u) → Continuous h → (∀ x, ‖h x‖ ≤ b) →
          Integrable (Function.uncurry fun x u => K u x * star (h x)) ((μ.restrict 𝓕).prod m) := by
        intro K h b hK hKb hh hb
        refine Integrable.mono' (((integrable_const b).mul_prod hβ)) ?_ (ae_of_all _ fun z => ?_)
        · exact ((hK.comp (continuous_snd.prodMk continuous_fst)).mul (hh.comp continuous_fst).star).aestronglyMeasurable
        · show ‖K z.2 z.1 * star (h z.1)‖ ≤ b * β z.2
          rw [norm_mul, norm_star, mul_comm b]
          exact mul_le_mul (hKb z.2 z.1) (hb z.1) (norm_nonneg _) ((norm_nonneg _).trans (hKb z.2 z.1))
      have hsc := fun g g' (hg : IsThetaFunO ψ S T g) (hg' : IsThetaFunO ψ S T g') =>
        GlobalTheory.Mem.LiftPolar.scalar_eq D ψ hψ S T μ 𝓕 hμ h𝓕 (om p) (hom.om_pres p) (hom.om_unit μ 𝓕 hμ h𝓕 p) g g' hg hg'
      have A : ∫ x in 𝓕, om p G x * star (f x) ∂μ = ∫ x in 𝓕, G x * star (f0 x) ∂μ := by
        rw [← hff0]; exact hsc G f0 hG hf0
      have B : ∫ x in 𝓕, G x * star (f0 x) ∂μ = ∫ x in 𝓕, H x * star (f x) ∂μ := by
        calc ∫ x in 𝓕, G x * star (f0 x) ∂μ = ∫ x in 𝓕, ∫ u, F u x * star (f0 x) ∂m ∂μ := by
              refine integral_congr_ae (ae_of_all _ fun x => ?_)
              show (∫ u, F u x ∂m) * star (f0 x) = ∫ u, F u x * star (f0 x) ∂m
              rw [integral_mul_const]
          _ = ∫ u, ∫ x in 𝓕, F u x * star (f0 x) ∂μ ∂m :=
              integral_integral_swap (hprod F f0 C0 hFc (fun u x => (hdom u x).1) hf0.cont hC0)
          _ = ∫ u, ∫ x in 𝓕, om p (F u) x * star (f x) ∂μ ∂m := by
              refine integral_congr_ae (ae_of_all _ fun u => ?_)
              rw [← hff0]; exact (hsc (F u) f0 (hF u) hf0).symm
          _ = ∫ x in 𝓕, ∫ u, om p (F u) x * star (f x) ∂m ∂μ :=
              (integral_integral_swap (hprod (fun u => om p (F u)) f Cf hOc (fun u x => (hdom u x).2) hf.cont hCf)).symm
          _ = ∫ x in 𝓕, H x * star (f x) ∂μ := by
              refine integral_congr_ae (ae_of_all _ fun x => ?_)
              show ∫ u, om p (F u) x * star (f x) ∂m = (∫ u, om p (F u) x ∂m) * star (f x)
              rw [integral_mul_const]
      have i1 := hint (om p G) f CG Cf hOG.cont hf.cont hCG hCf
      have i2 := hint H f (∫ u, β u ∂m) Cf hHc hf.cont hHb hCf
      simp only [hqdef, sub_mul]
      rw [integral_sub i1 i2, A, B, sub_self]
  have := congrFun hq w
  simp only [hqdef, Pi.zero_apply, sub_eq_zero] at this
  exact this

theorem om_integral_comm_bdd : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (Ω : Type) [TopologicalSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω] [SecondCountableTopology Ω] (m : Measure Ω) [IsFiniteMeasure m] (F : Ω → WO S T → ℂ) (p : GA D S × GA D T), (∀ a, IsThetaFunO ψ S T (F a)) → (Continuous fun q : Ω × WO S T => F q.1 q.2) → (∃ C : ℝ, ∀ a x, ‖F a x‖ ≤ C) → (Continuous fun q : Ω × WO S T => om p (F q.1) q.2) → (∃ C : ℝ, ∀ a x, ‖om p (F a) x‖ ≤ C) → IsThetaFunO ψ S T (fun x => ∫ a, F a x ∂m) → ∀ x, om p (fun y => ∫ a, F a y ∂m) x = ∫ a, om p (F a) x ∂m := by
  intro D ψ S T χS χT om hom Ω _ _ _ _ m _ F p hF hFc hFb hOc hOb hG x
  obtain ⟨C1, hC1⟩ := hFb
  obtain ⟨C2, hC2⟩ := hOb
  exact om_integral_comm_dom D ψ S T χS χT om hom Ω m F p (fun _ => max C1 C2) hF hFc hOc
    (integrable_const _) (fun a w => ⟨(hC1 a w).trans (le_max_left _ _), (hC2 a w).trans (le_max_right _ _)⟩) hG x

end GlobalTheory.CommIntBdd
end
end

