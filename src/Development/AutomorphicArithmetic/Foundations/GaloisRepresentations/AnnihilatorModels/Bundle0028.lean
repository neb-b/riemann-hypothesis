module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0004
public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0009
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0347
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0234
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0618
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0012
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericScale

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.AdmissibleSequenceExact
section
namespace UpperTheory.Gal.crystallineComparison

theorem admissible_sequence_exact : AdmExact := admissibleExact_of_dualInvariantExact dinvExact_of
theorem joinAbs_holds : JoinAbs :=
  joinAbs_of nilEmb_of (nilSubq_of admissible_sequence_exact nilEmb_of) nilAnn_of annSub_of (annExt_of dinvExt_of) admissible_sequence_exact
theorem boundSt_holds : BoundSt := boundSt_of
theorem stOfCr_holds : StOfCr := stOfCr_of annPer_of boundSt_of

end UpperTheory.Gal.crystallineComparison
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetCommon
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.detCommon_of :
    CommonModel := by
  intro l _ P AI hT E Ω _ _ _ Gw O _ _ _ Bw a r c hr hc
  obtain ⟨T⟩ := hT
  obtain ⟨L₁, r₁, hm₁, hc₁⟩ := hr
  obtain ⟨L₂, c₂, hm₂, hp₂⟩ := hc
  have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  haveI := L₁.2
  haveI := (supExt L₁ L₂).2
  have hs₁ : IsSst P (Bw.repE L₁ r₁) := GlobalTheory.CrysSst.isSst_of_isCrys P AI T (Bw.repE L₁ r₁) hc₁
  have hs := GlobalTheory.AboveL.RepConj.isSst_enlarge P Bw l₁ r₁ hs₁
  refine ⟨supExt L₁ L₂, mapRep (IntermediateField.inclusion l₁).toRingHom r₁,
    mapRep (IntermediateField.inclusion l₂).toRingHom c₂, hm₁.enlarge l₁, hm₂.enlarge l₂, hs, ?_,
    GlobalTheory.PstExt.isPst_enlarge P Bw l₂ c₂ hp₂⟩
  haveI : FiniteDimensional ℚ_[l] (Fin a → ↥(supExt L₁ L₂).1) := Module.Finite.trans ↥(supExt L₁ L₂).1 _
  exact GlobalTheory.GalCut.IwaTwist.isPst_of_isSst P AI T _ hs
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDetSpan
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.detSpan_of :
    CoFacts → SpanS := by
  intro hco l _ P AI hT K LL a ρ hρ S _ π
  obtain ⟨T⟩ := hT
  haveI := LL.2
  haveI : FiniteDimensional ℚ_[l] (Fin a → ↥LL.1) := Module.Finite.trans ↥LL.1 (Fin a → ↥LL.1)
  have honB : ∀ (f : End ℚ_[l] (Bst P)) (y : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P),
      onB P ℚ_[l] (Fin a → ↥LL.1) f y =
        AlgebraTensorModule.map (LinearMap.id : (Fin a → ↥LL.1) →ₗ[↥LL.1] (Fin a → ↥LL.1)) f y := by
    intro f y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => rw [onB_tmul]; rfl
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  have hsumco : ∀ {k : ℕ} (Y : Fin k → (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P) (m : Fin a),
      co (∑ j, Y j) m = ∑ j, co (Y j) m := by
    intro k Y m
    unfold co
    exact map_sum _ _ _
  have hone : ∀ i m : Fin a, π (co ((Pi.single i 1 : Fin a → ↥LL.1) ⊗ₜ[ℚ_[l]] (1 : Bst P)) m) =
      (Pi.single i 1 : Fin a → S) m := by
    intro i m
    rw [co_tmul, Pi.single_apply, Pi.single_apply]
    split_ifs
    · rw [← Algebra.TensorProduct.one_def, map_one]
    · rw [zero_tmul, map_zero]
  have key : ∀ i : Fin a, (Pi.single i 1 : Fin a → S) ∈ Submodule.span S (Set.range fun (x : ↥(Dpst P ρ)) i =>
      π (co (x : (Fin a → ↥LL.1) ⊗[ℚ_[l]] Bst P) i)) := by
    intro i
    obtain ⟨k, b, x, hx, hsum⟩ := _root_.GlobalTheory.Pst.Dst_spans_tensor_Bst l P AI T K (Fin a → ↥LL.1) (GlobalTheory.PstCoeff.resQ ρ)
      (GlobalTheory.GalCut.IwaTwist.isSst_resQ P ρ hρ) (Pi.single i 1)
    have hxD : ∀ j, x j ∈ Dpst P ρ := fun j => (mem_Dpst P ρ).mpr ⟨K, fun g _ => by
      have h := (mem_Dst P _).mp (hx j) g
      rwa [GlobalTheory.PstCoeff.stRep_resQ] at h⟩
    have hfin : (Pi.single i 1 : Fin a → S) =
        ∑ j, π ((1 : ↥LL.1) ⊗ₜ[ℚ_[l]] b j) • (fun m => π (co (x j) m)) := by
      funext m
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hone i m, hsum, hsumco, map_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [honB, (hco ℚ_[l] ↥LL.1 (Bst P) a).2.2.1 (b j) (x j)]
      simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    rw [hfin]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨x j, hxD j⟩, rfl⟩)
  rw [eq_top_iff, ← (Pi.basisFun S (Fin a)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  rw [Pi.basisFun_apply]
  exact key i
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PPhiKNil
section
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem nil_of_eq {W : Type} [AddCommGroup W] [Module ℂ W] (M : End ℂ W) {p p' : Polynomial ℂ} (e : p = p')
    (h : IsNilpotent (Polynomial.aeval M p)) : IsNilpotent (Polynomial.aeval M p') := e ▸ h

theorem UpperTheory.Gal.crystallineComparison.phiKNil_of :
    DvdOfNil → NilWeil → NilRho → WdModel → PhiKOfNil := by
  intro hD hW hR hM
  unfold PhiKOfNil
  intro l _ P AI hT ι E Ω _ _ _ _ _ A w h O _ _ _ Bw hj a r LL r' hm hcr Q hN s u hu hQ
  obtain ⟨T⟩ := hT
  haveI := LL.2
  have hSst : IsSst P (Bw.repE LL r') := GlobalTheory.CrysSst.isSst_of_isCrys P AI T _ hcr
  have hV : IsPst P (Bw.repE LL r') := GlobalTheory.GalCut.IwaTwist.isPst_of_isSst P AI T _ hSst
  haveI := hV.finite
  have hd : deg (frob h)⁻¹ = -1 := by rw [deg_inv, deg_frob]
  have h1 := hW l P E Ω A w h O Bw hj LL _ (Bw.repE LL r') hV hSst Q hN _ hd
  have h2 := nil_of_eq _ hQ (hR l P ι E Ω A w h O Bw hj LL _ (Bw.repE LL r') hV Q _ h1)
  obtain ⟨h3, _⟩ := hM l P ι E Ω A w h O Bw hj a r LL r' hm hV (frob h)⁻¹
  obtain ⟨m, hm'⟩ := hD ℂ _ _ s u hu h2
  exact ⟨(frob h)⁻¹, hd, m, h3 ▸ hm'⟩
end

