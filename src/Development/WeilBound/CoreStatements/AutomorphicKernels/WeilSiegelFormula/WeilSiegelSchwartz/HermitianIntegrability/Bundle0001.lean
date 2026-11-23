module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.WeilSiegelFormula.WeilSiegelSchwartz.HermitianIntegrability.UntupTupOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0657
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0717
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0645
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0547

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.WeilSiegelFormula.WeilSiegelSchwartz.HermitianIntegrability.ExistsIntegralEqMul
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace PositivityTheory.PfWsf.Hand.TupleUntupling

variable {D : D7}

theorem exists_integral_eq_mul {V V' : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] [AddCommGroup V'] [TopologicalSpace V'] [IsTopologicalAddGroup V']
    [MeasurableSpace V'] [BorelSpace V'] [LocallyCompactSpace V'] [SecondCountableTopology V']
    (f : V → V') (g : V' → V) (h1 : Function.LeftInverse g f) (h2 : Function.RightInverse g f)
    (hadd : ∀ x y, f (x + y) = f x + f y) (hc : Continuous f) (hc' : Continuous g)
    (ν : Measure V) (hν : ν.IsAddHaarMeasure) (μ : Measure V') (hμ : μ.IsAddHaarMeasure) :
    ∃ c : ℂ, ∀ u : V' → ℂ, ∫ x, u (f x) ∂ν = c * ∫ y, u y ∂μ := by
  let e : V ≃+ V' := { toFun := f, invFun := g, left_inv := h1, right_inv := h2, map_add' := hadd }
  haveI : (ν.map f).IsAddHaarMeasure := e.isAddHaarMeasure_map ν hc hc'
  refine ⟨((Measure.addHaarScalarFactor (ν.map f) μ : ℝ) : ℂ), fun u => ?_⟩
  have h : ∫ y, u y ∂(ν.map f) = ∫ x, u (f x) ∂ν :=
    integral_map_equiv
      ({ toEquiv := e.toEquiv, continuous_toFun := hc, continuous_invFun := hc' } : V ≃ₜ V').toMeasurableEquiv u
  rw [← h]
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul (ν.map f) μ]
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

theorem gramR_untup (V : HSp D) {r : ℕ} (y : Mx D V.rank r) :
    gramR (AF D.host.F) D.sp.cm.sig V.gram (untup y) = GlobalTheory.StdUnn.inner V y y := by
  ext a b
  simp only [gramR, untup, hR, Formalism.UG.hform, JR, GlobalTheory.StdUnn.inner, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  change _ = (cA D (y i a)) * (incA D (V.gram i j) * y j b)
  rw [mul_assoc]
  rfl


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem starN_hermE (V : HSp D) {r : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D V.rank r))
    (hμ : μ.IsAddHaarMeasure) (dx : Measure (Fin r → Fin V.rank → AE D)) (hdx : dx.IsAddHaarMeasure) :
    ∃ c : ℂ, ∀ (Φ : (Fin r → Fin V.rank → AE D) → ℂ) (b : hermA D r),
      starN D.sp.cm.sig V.gram ψ dx Φ (hermE D r b) = c * Jt ψ V μ (fun y => Φ (untup y)) b := by
  obtain ⟨k1, k2, k3, -, -, -⟩ := lattice_Mx D V.rank r
  haveI : IsTopologicalAddGroup (Mx D V.rank r) := k1
  haveI : LocallyCompactSpace (Mx D V.rank r) := k2
  haveI : SecondCountableTopology (Mx D V.rank r) := k3
  haveI : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  obtain ⟨j1, -, -, i4, i5⟩ := Formalism.IndefR.Eqv.ae_facts D
  haveI : BorelSpace (Fin V.rank → AE D) := Pi.borelSpace
  haveI : BorelSpace (Fin r → Fin V.rank → AE D) := Pi.borelSpace
  obtain ⟨c, hc⟩ := exists_integral_eq_mul (tupOf (D := D) (m := V.rank) (r := r)) untup untup_tupOf tupOf_untup
    (fun _ _ => rfl) (continuous_matrix fun i a => (continuous_apply i).comp (continuous_apply a))
    (continuous_pi fun a => continuous_pi fun i => continuous_id.matrix_elem i a) dx hdx μ hμ
  refine ⟨c, fun Φ b => ?_⟩
  unfold starN Jt
  rw [← hc]
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  have hg := gramR_untup V (tupOf X)
  change Φ X * ψ (_ * Algebra.trace _ _
    (Matrix.trace (b.1 * gramR (AF D.host.F) D.sp.cm.sig V.gram (untup (tupOf X))))) = _
  rw [hg]
  rfl

end PositivityTheory.PfWsf.Hand.TupleUntupling
end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.WeilSiegelFormula.WeilSiegelSchwartz.HermitianIntegrability.ExistsSchwartzOfIsSchwartzArch
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace PositivityTheory.PfWsf.Hand.TupleUntupling

variable {D : D7}

theorem exists_schwartz_of_isSchwartzArch {θ : InfFam D} (hθ : IsInfFam θ) {m r : ℕ}
    {a : (Fin r → Fin m → Ainf D.host.F ⊗[D.host.F] D.host.E) → ℂ}
    (ha : GlobalTheory.Published.SiegelOneVector.IsSchwartzArch (F := D.host.F) (E := D.host.E) a) :
    ∃ f : SchwartzMap (D.what₂.Tau → Fin m → Fin r → ℂ) ℂ, ∀ Y, a Y = f fun τ i j => θ τ (Y j i) := by
  obtain ⟨N, e, he, he', f, hf⟩ := ha
  obtain ⟨P, hP⟩ := GlobalTheory.CompanionTheory.SiegelND.SchGlue.exists_infHomeo hθ
  let Q : (Fin r → Fin m → Ainf D.host.F ⊗[D.host.F] D.host.E) ≃ₜ (D.what₂.Tau → Fin m → Fin r → ℂ) :=
    { toFun := fun Y τ i j => P (Y j i) τ
      invFun := fun c j i => P.symm fun τ => c τ i j
      left_inv := fun Y => by simp
      right_inv := fun c => by simp
      continuous_toFun := continuous_pi fun τ => continuous_pi fun i => continuous_pi fun j =>
        (continuous_apply τ).comp (P.continuous.comp ((continuous_apply i).comp (continuous_apply j)))
      continuous_invFun := continuous_pi fun j => continuous_pi fun i => P.symm.continuous.comp
        (continuous_pi fun τ => (continuous_apply j).comp ((continuous_apply i).comp (continuous_apply τ))) }
  have hQ : ∀ Y τ i j, Q Y τ i j = θ τ (Y j i) := fun Y τ i j => hP _ _
  have hadd : ∀ X Y, Q (X + Y) = Q X + Q Y := fun X Y => by
    funext τ i j
    simp only [hQ, Pi.add_apply, map_add (f := _)]
  let A : (D.what₂.Tau → Fin m → Fin r → ℂ) ≃+ (Fin N → ℝ) := (AddEquiv.mk' Q.toEquiv hadd).symm.trans e
  have hA : Continuous A := he.comp Q.symm.continuous
  have hA' : Continuous A.symm := Q.continuous.comp he'
  let L : (D.what₂.Tau → Fin m → Fin r → ℂ) ≃L[ℝ] (Fin N → ℝ) := A.toRealLinearEquiv hA hA'
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L f, fun Y => ?_⟩
  have hY : (fun τ i j => θ τ (Y j i)) = Q Y := funext fun τ => funext fun i => funext fun j => (hQ Y τ i j).symm
  rw [hf, hY]
  show f (e Y) = f (e (Q.symm (Q Y)))
  rw [Homeomorph.symm_apply_apply]

theorem mem_schwartzA_of_sb (θ : InfFam D) (hθ : IsInfFam θ) {m r : ℕ} (Φ : (Fin r → Fin m → AE D) → ℂ)
    (hΦ : GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (F := D.host.F) (E := D.host.E) Φ) :
    (fun y : Mx D m r => Φ (untup y)) ∈ schwartzA θ m r := by
  obtain ⟨k, a, b, ha, hb, hs⟩ := hΦ
  choose f hf using fun i => exists_schwartz_of_isSchwartzArch hθ (ha i)
  have hg : ∀ i, (fun Z : Fin m → Fin r → Af D.host.F ⊗[D.host.F] D.host.E => b i fun j l => Z l j) ∈
      GlobalTheory.WeilM.SB (Fin m → Fin r → Af D.host.F ⊗[D.host.F] D.host.E) := fun i => by
    have h := GlobalTheory.CompanionTheory.SiegelND.SchGlue.isSB_swap (D := D) (m := r) (r := m) (g := b i) ⟨(hb i).1, (hb i).2⟩
    exact ⟨h.1, h.2⟩
  have hsum : (fun y : Mx D m r => Φ (untup y)) = ∑ i : Fin k, fun x : Mx D m r =>
      f i (fun τ l j => compAt θ τ x l j) *
        (fun Z : Fin m → Fin r → Af D.host.F ⊗[D.host.F] D.host.E => b i fun j l => Z l j)
          (fun l j => finPart D (x l j)) := by
    funext y
    rw [hs, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hf]
    rfl
  rw [hsum]
  exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨f i, _, hg i, rfl⟩

end PositivityTheory.PfWsf.Hand.TupleUntupling
end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.WeilSiegelFormula.WeilSiegelSchwartz.HermitianIntegrability.IntegrableOfAddEquiv
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace PositivityTheory.PfWsf.Jab.WsInteg

variable {D : D7}

def hermE (D : D7) (r : ℕ) (b : hermA D r) : HermR (AF D.host.F) D.sp.cm.sig r :=
  ⟨b.1, fun i j => by
    have h := congrFun (congrFun b.2 i) j
    simp only [GlobalTheory.MixModel.adj, Matrix.transpose_apply, Matrix.map_apply] at h
    exact h⟩

theorem integrable_of_addEquiv {V V' : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [MeasurableSpace V] [BorelSpace V] [AddCommGroup V'] [TopologicalSpace V'] [IsTopologicalAddGroup V']
    [MeasurableSpace V'] [BorelSpace V'] [LocallyCompactSpace V'] [SecondCountableTopology V']
    (g : V → V') (k : V' → V) (h1 : Function.LeftInverse k g) (h2 : Function.RightInverse k g)
    (hadd : ∀ x y, g (x + y) = g x + g y) (hc : Continuous g) (hc' : Continuous k)
    (μ : Measure V) (hμ : μ.IsAddHaarMeasure) (ν : Measure V') (hν : ν.IsAddHaarMeasure)
    (f : V' → ℂ) (hf : Integrable (fun b => f (g b)) μ) : Integrable f ν := by
  let e : V ≃+ V' := { toFun := g, invFun := k, left_inv := h1, right_inv := h2, map_add' := hadd }
  let h : V ≃ₜ V' := { toEquiv := e.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
  haveI : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ hc hc'
  have hi : Integrable f (μ.map e) := (integrable_map_equiv h.toMeasurableEquiv f).2 hf
  rw [Measure.isAddLeftInvariant_eq_smul ν (μ.map e)]
  exact hi.smul_measure_nnreal


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem integrable_of_hermE {r : ℕ} (lam : Measure (hermA D r)) (hlam : lam.IsAddHaarMeasure)
    (db : Measure (HermR (AF D.host.F) D.sp.cm.sig r)) (hdb : db.IsAddHaarMeasure)
    (f : HermR (AF D.host.F) D.sp.cm.sig r → ℂ) (hf : Integrable (fun b => f (hermE D r b)) lam) :
    Integrable f db := by
  haveI : IsTopologicalAddGroup (Mx D r r) := inferInstanceAs (IsTopologicalAddGroup (Fin r → Fin r → AE D))
  haveI i3 : SecondCountableTopology (Mx D r r) := inferInstanceAs (SecondCountableTopology (Fin r → Fin r → AE D))
  haveI : BorelSpace (Mx D r r) := ⟨rfl⟩
  haveI : BorelSpace (hermA D r) := Subtype.borelSpace _
  haveI : SecondCountableTopology (HermR (AF D.host.F) D.sp.cm.sig r) :=
    @Topology.IsInducing.secondCountableTopology _ _ _ _ _ i3 Topology.IsInducing.subtypeVal
  exact integrable_of_addEquiv (hermE D r) (fun S => ⟨S.1, Matrix.ext fun a c => S.2 a c⟩) (fun _ => rfl)
    (fun _ => rfl) (fun _ _ => rfl) (continuous_subtype_val.subtype_mk _) (continuous_subtype_val.subtype_mk _)
    lam hlam db hdb f hf

end PositivityTheory.PfWsf.Jab.WsInteg
end
end

