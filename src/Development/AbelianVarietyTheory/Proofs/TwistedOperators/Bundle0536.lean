module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0817
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqrtDivMulEqSqrtMul
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentApproximation.AddDense
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0525
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0528
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1738
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0148
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0161
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0474

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMultilinearColumnRowKernelPairing
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.ArrowMultilinear

section General

variable {V : ℕ → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module ℂ (V j)]

theorem chainTo_congr {k k' : ∀ j, V j →ₗ[ℂ] V (j + 1)} : ∀ n, (∀ j < n, k j = k' j) → chainTo k n = chainTo k' n
  | 0, _ => rfl
  | n + 1, h => by
    show k n ∘ₗ chainTo k n = k' n ∘ₗ chainTo k' n
    rw [h n (Nat.lt_succ_self n), chainTo_congr n fun j hj => h j (Nat.lt_succ_of_lt hj)]

theorem chain_multilinear : ∀ (m : ℕ) (A : Fin m → Type) [∀ j, AddCommGroup (A j)] [∀ j, Module ℂ (A j)]
    (k : ∀ j : Fin m, A j →ₗ[ℂ] (V j →ₗ[ℂ] V (j + 1))),
    ∃ M : (∀ j, A j) →ₘₗ[ℂ] (V 0 →ₗ[ℂ] V m), ∀ fs,
      M fs = chainTo (fun j => if h : j < m then k ⟨j, h⟩ (fs ⟨j, h⟩) else 0) m := by
  intro m
  induction m with
  | zero =>
    intro A _ _ k
    exact ⟨MultilinearMap.constOfIsEmpty (RingHom.id ℂ) A LinearMap.id, fun _ => rfl⟩
  | succ m ih =>
    intro A _ _ k
    obtain ⟨M, hM⟩ := ih (fun j => A j.castSucc) (fun j => k j.castSucc)
    let kl : A (Fin.last m) →ₗ[ℂ] (V m →ₗ[ℂ] V (m + 1)) := k (Fin.last m)
    refine ⟨MultilinearMap.uncurryRight
      (((LinearMap.llcomp ℂ (V 0) (V m) (V (m + 1)) ∘ₗ kl).flip).compMultilinearMap M), fun fs => ?_⟩
    show kl (fs (Fin.last m)) ∘ₗ M (Fin.init fs) = _ ∘ₗ chainTo _ m
    rw [hM]
    beta_reduce
    rw [dite_eq_left (Nat.lt_succ_self m)]
    congr 1
    refine chainTo_congr m fun j hj => ?_
    rw [dite_eq_left hj, dite_eq_left (Nat.lt_succ_of_lt hj)]
    rfl

theorem pair_multilinear {ι κ X Y : Type} {A : ι → Type} {B : κ → Type} [∀ j, AddCommGroup (A j)] [∀ j, Module ℂ (A j)]
    [∀ j, AddCommGroup (B j)] [∀ j, Module ℂ (B j)] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (β : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) (Ma : (∀ j, A j) →ₘₗ[ℂ] X) (Mb : (∀ j, B j) →ₘₗ[ℂ] Y) :
    ∃ M : (∀ j, A j) →ₘₗ[ℂ] ((∀ j, B j) →ₘₗ[ℂ] ℂ), ∀ a b, M a b = β (Ma a) (Mb b) := by
  let L : X →ₗ[ℂ] ((∀ j, B j) →ₘₗ[ℂ] ℂ) :=
    { toFun := fun x => (β x).compMultilinearMap Mb
      map_add' := fun x x' => by ext b; simp
      map_smul' := fun c x => by ext b; simp }
  exact ⟨L.compMultilinearMap Ma, fun _ _ => rfl⟩

theorem compl_multilinear {ι κ X Y P Q : Type} {A : ι → Type} {B : κ → Type} [∀ j, AddCommGroup (A j)] [∀ j, Module ℂ (A j)]
    [∀ j, AddCommGroup (B j)] [∀ j, Module ℂ (B j)] [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup P] [Module ℂ P] [AddCommGroup Q] [Module ℂ Q]
    (β : X →ₗ[ℂ] Y →ₗ[ℂ] ℂ) (c : (∀ j, A j) → P →ₗ[ℂ] X) (r : (∀ j, B j) → Q →ₗ[ℂ] Y) (u : P) (v : Q)
    (hc : ∃ M : (∀ j, A j) →ₘₗ[ℂ] X, ∀ a, M a = c a u)
    (hr : ∃ M : (∀ j, B j) →ₘₗ[ℂ] Y, ∀ b, M b = r b v) :
    ∃ M : (∀ j, A j) →ₘₗ[ℂ] ((∀ j, B j) →ₘₗ[ℂ] ℂ), ∀ a b, M a b = β.compl₁₂ (c a) (r b) u v := by
  obtain ⟨Ma, ha⟩ := hc
  obtain ⟨Mb, hb⟩ := hr
  obtain ⟨M, hM⟩ := pair_multilinear β Ma Mb
  exact ⟨M, fun a b => by rw [hM, ha, hb, LinearMap.compl₁₂_apply]⟩

end General

section Jet

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem jetLin_add (J J' : (Formalism.L2.Ker.DVar ι a b →₀ ℕ) → ℂ) :
    Formalism.L2.Ker.jetLin (J + J') = Formalism.L2.Ker.jetLin J + Formalism.L2.Ker.jetLin J' := by
  refine (MvPolynomial.basisMonomials _ ℂ).ext fun m => ?_
  simp only [Formalism.L2.Ker.jetLin, LinearMap.add_apply, Module.Basis.constr_basis, Pi.add_apply, map_add (f := _)]

theorem jetLin_smul (c : ℂ) (J : (Formalism.L2.Ker.DVar ι a b →₀ ℕ) → ℂ) :
    Formalism.L2.Ker.jetLin (c • J) = c • Formalism.L2.Ker.jetLin J := by
  refine (MvPolynomial.basisMonomials _ ℂ).ext fun m => ?_
  simp only [Formalism.L2.Ker.jetLin, LinearMap.smul_apply, Module.Basis.constr_basis, Pi.smul_apply, map_smul]

end Jet

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem jetTab_add (W : G.Weil) (B : VertexFrames G) (p : Pair T) {f f' : WO (G.pS p) (G.pT p) → ℂ}
    (hf : IsThetaFunO W.ψ _ _ f) (hf' : IsThetaFunO W.ψ _ _ f') (x : FinPt G p.small) (y : FinPt G p.big) :
    jetTab W B p (f + f') x y = jetTab W B p f x y + jetTab W B p f' x y := by
  funext k
  simp only [jetTab, kerFin, fockIn, GridData.Weil.ker, thetaKO, Pi.add_apply]
  rw [GlobalTheory.SpecFac.pureTensorO_add W.ψ_std W.θ_is _ _ _ _ hf hf', map_add (f := _), Pi.add_apply]

theorem jetTab_smul (W : G.Weil) (B : VertexFrames G) (p : Pair T) (c : ℂ) (f : WO (G.pS p) (G.pT p) → ℂ)
    (x : FinPt G p.small) (y : FinPt G p.big) :
    jetTab W B p (c • f) x y = c • jetTab W B p f x y := by
  funext k
  simp only [jetTab, kerFin, fockIn, GridData.Weil.ker, thetaKO, Pi.smul_apply]
  rw [GlobalTheory.FiniteFock.pureTensorO_smul, map_smul, Pi.smul_apply]

def fockLin (W : G.Weil) (B : VertexFrames G) (p : Pair T) (x : FinPt G p.small) (y : FinPt G p.big) :
    thSub W p →ₗ[ℂ] (VV ℂ (wt G p.small) →ₗ[ℂ] VV ℂ (wt G p.big)) where
  toFun f := fockComp W B p f x y
  map_add' f f' := by
    ext1 v
    simp only [fockComp, Submodule.coe_add]
    rw [jetTab_add W B p f.2 f'.2]
    simp only [Formalism.L2.Ker.jetOp, Formalism.L2.Ker.jetMap, jetLin_add, LinearMap.comp_apply, LinearMap.add_apply, map_add (f := _)]
  map_smul' c f := by
    ext1 v
    simp only [fockComp, Submodule.coe_smul]
    rw [jetTab_smul]
    simp only [Formalism.L2.Ker.jetOp, Formalism.L2.Ker.jetMap, jetLin_smul, LinearMap.comp_apply, LinearMap.smul_apply, map_smul,
      RingHom.id_apply]

variable {W : G.Weil} {U : Set T}

theorem col_multilinear (S : GridChoice W U) (t : T) (x : ∀ j, FinPt G (.top j)) (Ψ₀ : VV ℂ (wt G (.top 0))) :
    ∃ M : (∀ j : Fin D.R.m, thSub W (.top t j)) →ₘₗ[ℂ] VV ℂ (wt G (.top D.R.m)),
      ∀ fs, M fs = colMapV S (fun j => (fs j : WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ)) x Ψ₀ := by
  obtain ⟨Mc, hc⟩ := chain_multilinear (V := fun j => VV ℂ (wt G (.top j))) D.R.m
    (fun j : Fin D.R.m => thSub W (.top t j))
    (fun j => S.Z.scal 1 (.top t j) • fockLin W S.N.frC (.top t j) (x j * S.N.u _) (x (j + 1) * S.N.u _))
  refine ⟨(LinearMap.applyₗ (R := ℂ) (rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹ Ψ₀)).compMultilinearMap Mc, fun fs => ?_⟩
  show Mc fs _ = _
  rw [hc]
  refine LinearMap.congr_fun (chainTo_congr (V := fun j => VV ℂ (wt G (.top j))) D.R.m fun j hj => ?_) _
  exact dite_congr rfl (fun _ => rfl) (fun _ => rfl)

theorem row_multilinear (S : GridChoice W U) (y : ∀ i, FinPt G (.grid i D.R.m))
    (F₀ : VV ℂ (listedWt G (.grid 0 D.R.m))) :
    ∃ M : (∀ i : Fin D.R.m, thSub W (.chi i D.R.m : Pair T)) →ₘₗ[ℂ] VV ℂ (wt G (.grid D.R.m D.R.m)),
      ∀ gs, M gs =
        rowMapV S (fun i => (gs i : WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)) y F₀ := by
  obtain ⟨Mr, hr⟩ := chain_multilinear (V := fun i => VV ℂ (wt G (.grid i D.R.m))) D.R.m
    (fun i : Fin D.R.m => thSub W (.chi i D.R.m : Pair T))
    (fun i => S.Z.scal 1 (.chi i D.R.m : Pair T) •
      fockLin W S.N.frC (.chi i D.R.m : Pair T) (y i * S.N.u _) (y (i + 1) * S.N.u _))
  refine ⟨(LinearMap.applyₗ (R := ℂ)
    (rhoVr (tauE D) _ (S.N.fr (.grid 0 D.R.m))⁻¹ (funOf (listedWt G (.grid 0 D.R.m)) F₀))).compMultilinearMap Mr,
    fun gs => ?_⟩
  show Mr gs _ = _
  rw [hr]
  refine LinearMap.congr_fun (chainTo_congr (V := fun i => VV ℂ (wt G (.grid i D.R.m))) D.R.m fun j hj => ?_) _
  exact dite_congr rfl (fun _ => rfl) (fun _ => rfl)

theorem pairing_multilinear {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (t : T) (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m))
    (Ψ₀ : VV ℂ (wt G (.top 0))) (F₀ : VV ℂ (listedWt G (.grid 0 D.R.m))) :
    ∃ M : (∀ j : Fin D.R.m, thSub W (.top t j)) →ₘₗ[ℂ]
        ((∀ i : Fin D.R.m, thSub W (.chi i D.R.m : Pair T)) →ₘₗ[ℂ] ℂ),
      ∀ fs gs, M fs gs = (brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))).compl₁₂
        (colMapV S (fun j => (fs j : WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ)) x)
        (rowMapV S (fun i => (gs i : WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)) y) Ψ₀ F₀ := by
  exact compl_multilinear (brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m)))
    (fun fs : ∀ j : Fin D.R.m, thSub W (.top t j) =>
      colMapV S (fun j => (fs j : WO (G.pS (.top t j)) (G.pT (.top t j)) → ℂ)) x)
    (fun gs : ∀ i : Fin D.R.m, thSub W (.chi i D.R.m : Pair T) =>
      rowMapV S (fun i => (gs i : WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)) y) Ψ₀ F₀
    (col_multilinear S t x Ψ₀) (row_multilinear S y F₀)

end GlobalTheory.ArrowMultilinear
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalApproxFinitePointVacuumLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.NTheta (IsIdemAt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.FinApprox

variable {D : D7}

def finRat (D : D7) : D.host.E →+ AE D := TensorProduct.mk D.host.F (AF D.host.F) D.host.E (pairA D.host.F 0 1)

theorem finRat_apply (a : D.host.E) : finRat D a = pairA D.host.F 0 1 ⊗ₜ[D.host.F] a := rfl

theorem finRat_eq (a : D.host.E) : incA D a - pairA D.host.F 1 0 ⊗ₜ[D.host.F] a = finRat D a := by
  have h1 : (1 : AF D.host.F) = pairA D.host.F 1 0 + pairA D.host.F 0 1 :=
    Prod.ext (add_zero (1 : Ainf D.host.F)).symm (zero_add (1 : Af D.host.F)).symm
  rw [finRat_apply]
  show (1 : AF D.host.F) ⊗ₜ[D.host.F] a - _ = _
  rw [h1, TensorProduct.add_tmul, add_sub_cancel_left]

private theorem infPart_tmul' (a : AF D.host.F) (e : D.host.E) :
    infPart D (a ⊗ₜ[D.host.F] e) = fstA D.host.F a ⊗ₜ[D.host.F] e := by
  show Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (a ⊗ₜ[D.host.F] e) = _
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

theorem infPart_finRat (a : D.host.E) : infPart D (finRat D a) = 0 := by
  rw [finRat_apply, infPart_tmul']
  have h0 : fstA D.host.F (pairA D.host.F 0 1) = 0 := rfl
  rw [h0, TensorProduct.zero_tmul]

private theorem exists_witt_eq_teich_add_p_teich_frob_symm_add_p_sq_mul (w : AE D) :
    w = ∑ i, (Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr w i ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E i := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).sum_repr w]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

private theorem fstA_basis_repr_eq_zero_of_infPart_eq_zero {z : AE D} (hz : infPart D z = 0) (i : Fin (Module.finrank D.host.F D.host.E)) :
    fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr z i) = 0 := by
  have h1 : infPart D z = ∑ j, fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr z j) •
      Algebra.TensorProduct.basis (Ainf D.host.F) (Module.finBasis D.host.F D.host.E) j := by
    conv_lhs => rw [exists_witt_eq_teich_add_p_teich_frob_symm_add_p_sq_mul z]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [infPart_tmul', Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have h2 := congrArg
    (fun v => (Algebra.TensorProduct.basis (Ainf D.host.F) (Module.finBasis D.host.F D.host.E)).repr v i) h1
  simp only [hz, map_zero, Finsupp.coe_zero, Pi.zero_apply, Module.Basis.repr_sum_self] at h2
  exact h2.symm

private theorem eq_sum_pairA_zero_tmul_finBasis_of_infPart_eq_zero {z : AE D} (hz : infPart D z = 0) :
    z = ∑ i, pairA D.host.F 0 (sndA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr z i)) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E i := by
  conv_lhs => rw [exists_witt_eq_teich_add_p_teich_frob_symm_add_p_sq_mul z]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  exact Prod.ext (fstA_basis_repr_eq_zero_of_infPart_eq_zero hz i) rfl

theorem mem_closure_finRat {z : AE D} (hz : infPart D z = 0) : z ∈ closure (Set.range (finRat D)) := by
  have hd : DenseRange (Pi.map fun _ : Fin (Module.finrank D.host.F D.host.E) =>
      ⇑(algebraMap D.host.F (Af D.host.F))) :=
    DenseRange.piMap fun _ => AdeleCharTwist.denseRange_fin
  have hc : Continuous fun y : Fin (Module.finrank D.host.F D.host.E) → Af D.host.F =>
      ∑ i, pairA D.host.F 0 (y i) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E i := by
    refine continuous_finsetSum _ fun i _ => ?_
    have h1 : Continuous fun a : AF D.host.F => a ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E i := by
      have he : (fun a : AF D.host.F => a ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E i) =
          fun a => a • ((1 : AF D.host.F) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E i) := by
        funext a
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [he]
      exact Continuous.smul (M := AF D.host.F) (X := AE D) continuous_id continuous_const
    have h2 : Continuous fun y : Fin (Module.finrank D.host.F D.host.E) → Af D.host.F => pairA D.host.F 0 (y i) := by
      show Continuous fun y : Fin (Module.finrank D.host.F D.host.E) → Af D.host.F => ((0 : Ainf D.host.F), y i)
      exact continuous_const.prodMk (continuous_apply i)
    exact h1.comp h2
  have hm : Set.MapsTo (fun y : Fin (Module.finrank D.host.F D.host.E) → Af D.host.F =>
      ∑ i, pairA D.host.F 0 (y i) ⊗ₜ[D.host.F] Module.finBasis D.host.F D.host.E i)
      (Set.range (Pi.map fun _ : Fin (Module.finrank D.host.F D.host.E) => ⇑(algebraMap D.host.F (Af D.host.F))))
      (Set.range (finRat D)) := by
    rintro _ ⟨q, rfl⟩
    refine ⟨∑ i, q i • Module.finBasis D.host.F D.host.E i, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [finRat_apply, ← TensorProduct.smul_tmul]
    congr 1
    exact Prod.ext (smul_zero (q i)) ((Algebra.smul_def (q i) (1 : Af D.host.F)).trans (mul_one _))
  have hz' := map_mem_closure hc (hd fun i => sndA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).repr z i)) hm
  rw [eq_sum_pairA_zero_tmul_finBasis_of_infPart_eq_zero hz]
  exact hz'

theorem mem_closure_mat {m n : ℕ} {y : Mx D m n} (hy : y.map (infPart D) = 0) :
    y ∈ closure (Set.range fun ℓ : Matrix (Fin m) (Fin n) D.host.E => (ℓ.map (finRat D) : Mx D m n)) := by
  have h1 : ∀ i j, y i j ∈ closure (Set.range (finRat D)) := fun i j =>
    mem_closure_finRat (by simpa using congrFun (congrFun hy i) j)
  have h2 : (y : Fin m → Fin n → AE D) ∈
      closure (Set.univ.pi fun _ : Fin m => Set.univ.pi fun _ : Fin n => Set.range (finRat D)) := by
    refine mem_closure_pi.mpr fun i _ => ?_
    refine mem_closure_pi.mpr fun j _ => ?_
    exact h1 i j
  refine closure_mono ?_ h2
  intro x hx
  have hx' : ∀ i j, ∃ a, finRat D a = x i j := fun i j => hx i (Set.mem_univ i) j (Set.mem_univ j)
  choose ℓ hℓ using hx'
  exact ⟨Matrix.of ℓ, by ext i j; exact hℓ i j⟩

theorem actO_fin {S T : HSp D} (g : GA D S) (h : GA D T) {x : WO S T} (hx : x.map (infPart D) = 0) :
    (actO S T g h x).map (infPart D) = 0 := by
  unfold actO
  rw [Matrix.map_mul, Matrix.map_mul, hx, Matrix.mul_zero, Matrix.zero_mul]

private theorem continuous_actO_one {S T : HSp D} (h : GA D T) : Continuous (actO S T 1 h) := by
  haveI := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  unfold actO
  fun_prop

theorem exists_approx {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (g : GA D T) {x : WO S T} (hx : x.map (infPart D) = 0) :
    ∃ (ℓ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (w : WO S T), w.map (infPart D) = 0 ∧ heisO ψ S T w f = f ∧
      x = actO S T 1 g⁻¹ (ratW T S ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T ℓ) + w := by
  haveI := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  obtain ⟨U, hUo, hU⟩ := hf.level
  have hy : (actO S T 1 g x).map (infPart D) = 0 := actO_fin 1 g hx
  have hVo : IsOpen {v : WO S T | actO S T 1 g⁻¹ (actO S T 1 g x - v) ∈ U} :=
    hUo.preimage ((continuous_actO_one (S := S) g⁻¹).comp (continuous_const.sub continuous_id))
  have h0 : actO S T 1 g⁻¹ 0 = 0 := by
    have h00 := GlobalTheory.HeckeVacuum.act_sub g⁻¹ (0 : WO S T) 0
    rwa [sub_self, sub_self] at h00
  have hyV : actO S T 1 g x ∈ {v : WO S T | actO S T 1 g⁻¹ (actO S T 1 g x - v) ∈ U} := by
    show actO S T 1 g⁻¹ (actO S T 1 g x - actO S T 1 g x) ∈ U
    rw [sub_self, h0]
    exact U.zero_mem
  obtain ⟨_, hvV, ℓ, rfl⟩ := mem_closure_iff.mp (mem_closure_mat (m := T.rank) (n := S.rank) hy) _ hVo hyV
  have hrat : ratW T S ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T ℓ = (ℓ.map (finRat D) : WO S T) := by
    ext i j
    exact finRat_eq (ℓ i j)
  have key : actO S T 1 g⁻¹ (ratW T S ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt S T ℓ) =
      actO S T 1 g⁻¹ (ℓ.map (finRat D)) := congrArg _ hrat
  have hw : (actO S T 1 g⁻¹ (actO S T 1 g x - ℓ.map (finRat D))).map (infPart D) = 0 := by
    refine actO_fin 1 g⁻¹ ?_
    ext i j
    have hij : infPart D (actO S T 1 g x i j) = 0 := by simpa using congrFun (congrFun hy i) j
    simp [hij, infPart_finRat]
  refine ⟨ℓ, actO S T 1 g⁻¹ (actO S T 1 g x - ℓ.map (finRat D)), hw,
    hU (actO S T 1 g⁻¹ (actO S T 1 g x - ℓ.map (finRat D))) hvV hw, ?_⟩
  rw [key, GlobalTheory.HeckeVacuum.act_sub, add_sub_cancel, ← GlobalTheory.HeckeVacuum.act_mul, inv_mul_cancel,
    GlobalTheory.HeckeVacuum.act_one]

theorem exists_rat_approx : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F),
    R.toLevCh.Is A.μ0 → R.IsFam → R.IsThP → ∀ (i : Fin D.R.m) (g : GA D (Wc D i)) (x : WO (Vc D i) (Wc D i)),
    x.map (infPart D) = 0 → ∃ (ℓ : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (w : WO (Vc D i) (Wc D i)),
      w.map (infPart D) = 0 ∧ heisO R.ψ (Vc D i) (Wc D i) w (R.vacP i) = R.vacP i ∧
      x = actO (Vc D i) (Wc D i) 1 g⁻¹ (ratW (Wc D i) (Vc D i) ℓ - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) ℓ) + w := by
  intro D G _ _ Pl0 T0 A T _ R _ _ hP i g x hx
  exact exists_approx (hP.vP i A.μ0).1.2.theta g hx

end GlobalTheory.FinApprox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteZetaIntegralThetaLiftEqPartialLValueStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteZetaIntegral_thetaLift_eq_partialLValue : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.UnramifiedDoublingGL → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), FiniteZetaL R F := by
  first | exact @GlobalTheory.FinZeta.finiteZetaL | exact GlobalTheory.FinZeta.finiteZetaL | (intros; apply GlobalTheory.FinZeta.finiteZetaL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HTensMixHalfS
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section

namespace GlobalTheory.SmallDat.VacFix

theorem hTens_mixHalfS {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {i j : ℕ} (e : Num G i j)
    (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (hWW : Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e) (ε : AE D)
    (hε : ε * cA D ε = 0) (γ : GlobalTheory.SmallDat.PtS G i j) (hγ : γ ∈ mixHalfS e ε) :
    hTens (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ = 0 := by
  refine GlobalTheory.BigDat.VacFix.hTens_eq_zero (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) GlobalTheory.DualPairCheck.cA_cA e _ _
    (fun a b => ?_) (fun a b => ?_) ε hε γ (fun a b => ?_) (fun a b => ?_)
  · exact (congrArg (incA D) ((congrFun (congrFun hWW _) _).trans (GlobalTheory.BigDat.VacFix.skewGram_inl_inr _ _ e a b))).trans (map_zero _)
  · exact (congrArg (incA D) ((congrFun (congrFun hWW _) _).trans (GlobalTheory.BigDat.VacFix.skewGram_inr_inl _ _ e a b))).trans (map_zero _)
  · exact GlobalTheory.BigDat.VacFix.isHalf_of_mulG (spW₁ G i j) ε (colV e γ)ᵀ hγ.1 b a
  · refine GlobalTheory.BigDat.VacFix.isHalf_of_mulG (spV₁ G i j) ε ((γ.submatrix id fun k => e (.inr k)).map (cA D)) (fun a b => ?_) a b
    exact neg_injective ((mul_neg _ _).symm.trans (hγ.2 a b))

theorem vac_fixed : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (t : T) (i j : ℕ) (e : Num G i j) (Bs : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X → IsTriple Bs Γ X om om' →
    ∀ v : Pl D.host.F, (∀ u ∈ GlobalTheory.SmallDat.latPtS t e v, u ∈ latAtV Γ.V' Γ.W v) →
      ∀ γ ∈ GlobalTheory.SmallDat.genPtS t e v, Acts (evFin D.host.F v) (Γ.M'.co.rho W.ψ γ) (Γ.M'.vac v) (Γ.M'.vac v) := by
  intro D T L sc G W M t i j e Bs Γ X om om' h hT v hL γ hγ
  obtain ⟨-, -, θ, -, hθ⟩ := hT.geo.hM'.vac v
  have h1 := hθ γ (hL γ (GlobalTheory.SmallDat.genPtS_subset t e v hγ))
  have h2 : Bs.ψ (⅟(2 : AF D.host.F) * symp (R := AF D.host.F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig)
      (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E)) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J)
      (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) = 1 := by
    rcases hγ with ⟨γ', hγ', rfl⟩ | ⟨-, ε, hε, hγ⟩
    · exact GlobalTheory.BigDat.VacFix.psi_double _ Bs Γ.V' Γ.W _ _ _ _ hT.base hT.geo.hV' hT.geo.hW v θ γ' (hL γ' hγ')
    · unfold symp
      rw [hTens_mixHalfS e Γ h.JWW ε hε.2.1 γ hγ, mul_zero, map_zero, mul_zero, AddChar.map_zero_eq_one]
  rw [h2, one_smul, h.ψ] at h1
  exact h1

end GlobalTheory.SmallDat.VacFix

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergDerivativeZeroOrEmptyEqZeroStatement
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergDerivative_zero_or_empty_eq_zero : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (g h : SInf F (Fin n × Fin d)) (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))),
    ActsD (evI F) (M.heisLine ψ u) g h → (g = 0 ∨ IsEmpty (Fin n × Fin d)) → h = 0 := by
  first | exact @GlobalTheory.HeisDerivZero.actsD_eq_zero | exact GlobalTheory.HeisDerivZero.actsD_eq_zero | (intros; apply GlobalTheory.HeisDerivZero.actsD_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumAddConjComponentIndicatorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotentSum_add_conj_component_indicator : ∀ {D : D7} {e : AE D} {P : Finset (Pl D.host.E)}, IsIdemSum e P → ∀ w : Pl D.host.E,
    ((w ∈ P ∨ GlobalTheory.IdemSupport.cP w ∈ P) → GlobalTheory.StdFrames.cpt (D := D) w (toEAf D (e + cA D e)) = 1) ∧
    (w ∉ P → GlobalTheory.IdemSupport.cP w ∉ P → GlobalTheory.StdFrames.cpt (D := D) w (toEAf D (e + cA D e)) = 0) := by
  first | exact @GlobalTheory.IdemPairCpt.cpt_add_cA_idemSum | exact GlobalTheory.IdemPairCpt.cpt_add_cA_idemSum | (intros; apply GlobalTheory.IdemPairCpt.cpt_add_cA_idemSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeOfStabiliserMulInvEqStandardLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeOf_stabiliser_mul_inv_eq_standardLattice : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (X : Node), DefNode D.R.m X → ∀ k : FinPt G X,
    (∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr X)) ↔
        Matrix.mulVec (Formalism.IndefR.Lev.finE (G.V X) k.1).1 v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat (S.N.fr X))) →
    GlobalTheory.SumSize.latAt S X (k * (S.N.u X)⁻¹) = stdL D _ := by
  first | exact @GlobalTheory.LatStdStab.latAt_mul_inv_eq_stdL | exact GlobalTheory.LatStdStab.latAt_mul_inv_eq_stdL | (intros; apply GlobalTheory.LatStdStab.latAt_mul_inv_eq_stdL <;> assumption)
end

