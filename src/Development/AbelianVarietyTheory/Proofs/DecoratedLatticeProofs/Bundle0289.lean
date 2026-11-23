module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0124
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0284
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepComb
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRangeEmb4EqTop
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0274
public import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.IntegralSquareRoots.OneEntryMem
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0750
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0071
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRationalMatrixOfMemPeriodLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.LamPre

theorem exists_mat_of_mem_lamC : ∀ (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), ∀ x ∈ LamC (tauE D) δ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N', ∃ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, toHom S T hS hT γ ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' ∧ embH (tauE D) δ (toHom S T hS hT γ) = x ∧ ∃ v, GlobalTheory.AdTh.IsFinOf S T γ v := by
  intro D S T a b hS hT δ N N' x hx
  obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.1 hx
  refine ⟨(LinearMap.toMatrix' y).reindex (finCongr hT).symm (finCongr hS).symm, ?_, ?_, ?_⟩
  · have e : toHom S T hS hT ((LinearMap.toMatrix' y).reindex (finCongr hT).symm (finCongr hS).symm) = y := by
      unfold toHom
      rw [show ((LinearMap.toMatrix' y).reindex (finCongr hT).symm (finCongr hS).symm).reindex (finCongr hT) (finCongr hS)
          = LinearMap.toMatrix' y from by ext i j; simp, Matrix.toLin'_toMatrix']
    rw [e]; exact hy
  · have e : toHom S T hS hT ((LinearMap.toMatrix' y).reindex (finCongr hT).symm (finCongr hS).symm) = y := by
      unfold toHom
      rw [show ((LinearMap.toMatrix' y).reindex (finCongr hT).symm (finCongr hS).symm).reindex (finCongr hT) (finCongr hS)
          = LinearMap.toMatrix' y from by ext i j; simp, Matrix.toLin'_toMatrix']
    rw [e]
  · exact ⟨GlobalTheory.VacUnique.finRat S T _, GlobalTheory.VacUnique.finRat_inf S T _, GlobalTheory.VacUnique.finRat_fin S T _⟩

end GlobalTheory.AdForm.LamPre
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteAnnihilatorOpenSubgroupInBox
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
noncomputable section

namespace GlobalTheory.AnnihBox

variable {D : D7}

theorem cA_smul (r : AF D.host.F) (z : AE D) : cA D (r • z) = r • cA D z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [cA, sigR, TensorProduct.smul_tmul']
  | add a b ha hb => rw [smul_add, map_add (f := _), map_add (f := _), ha, hb, smul_add]

def cALin (D : D7) : AE D →ₗ[AF D.host.F] AE D where
  toFun := cA D
  map_add' := map_add _
  map_smul' := cA_smul

theorem continuous_cA' : Continuous (cA D) :=
  IsModuleTopology.continuous_of_linearMap (cALin D)

theorem infPart_cA_eq (a : AE D) : infPart D (cA D a) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D a) := by
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul r e => simp [cA, sigR, infPart]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb, map_add (f := _)]

theorem infPart_cA' (a : AE D) (h : infPart D a = 0) : infPart D (cA D a) = 0 := by
  rw [infPart_cA_eq, h, map_zero]

theorem symplO_extX_extY_single (S S₀ T : HSp D) {ρ : ℕ} (d : HypDec S S₀ ρ) (x : Mx D T.rank ρ)
    (i : Fin T.rank) (j : Fin ρ) (c : AE D) :
    symplO S T (d.extX T x) (d.extY T (Matrix.single i j (cA D c))) =
      Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (gA T ⬝ x) i j * c) := by
  have h := d.hO_ext T x 0 0 (Matrix.single i j (cA D c)) 0 0
  simp only [map_zero, add_zero, zero_add] at h
  have h0 : hO S₀ T (0 : WO S₀ T) 0 = 0 := by simp [hO]
  have hp : pairS T (0 : Mx D T.rank ρ) 0 = 0 := by simp [pairS, adj]
  rw [h0, hp, add_zero, add_zero] at h
  have ha : adj (Matrix.single i j (cA D c)) = Matrix.single j i c := by
    ext a b
    simp only [adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.single_apply]
    by_cases h1 : i = b <;> by_cases h2 : j = a <;> simp [h1, h2, GlobalTheory.DualPairCheck.cA_cA]
  unfold symplO
  rw [h, pairS, ha, Matrix.trace_single_mul, smul_eq_mul]
  ring_nf

set_option synthInstance.maxHeartbeats 400000 in
theorem map_finPart_mul_map {n m : ℕ} (M : Mx D n n) (c : AE D) (z : Mx D n m)
    (hz : ∀ i j, finPart D (z i j) = 0) : (M ⬝ z.map (fun w => c * w)).map (finPart D) = 0 := by
  ext i j
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.map_apply, Matrix.mul_apply, map_sum (finPart D), Matrix.zero_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [Matrix.map_apply, RingHom.map_mul, RingHom.map_mul, hz l j, mul_zero, mul_zero]

end GlobalTheory.AnnihBox


open GlobalTheory.AnnihBox in
theorem GlobalTheory.AnnihBox.annihilator_inBox : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (U : AddSubgroup (WO S T)), IsOpen (U : Set (WO S T)) → ∃ K : Set (Mx D T.rank ρ), IsCompact K ∧ ∀ x : Mx D T.rank ρ, (∀ a : Mx D T.rank ρ, a.map (infPart D) = 0 → d.extY T a ∈ U → ψ (symplO S T (d.extX T x) (d.extY T a)) = 1) → InBox K x := by
  intro D ψ hψ S S₀ T ρ d U hU
  let g : Fin T.rank → Fin ρ → (AE D →+ Mx D T.rank ρ) := fun i j =>
    { toFun := fun c => Matrix.single i j (cA D c)
      map_zero' := by simp
      map_add' := fun a b => by simp [Matrix.single_add] }
  have hg : ∀ i j, Continuous (g i j) := fun i j => by
    show Continuous fun c => Matrix.single i j (cA D c)
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [Matrix.single_apply]
    split_ifs
    · exact continuous_cA'
    · exact continuous_const
  let f : Fin T.rank → Fin ρ → (AE D →+ WO S T) := fun i j => (d.extY T).comp (g i j)
  have hf : ∀ i j, Continuous (f i j) := fun i j => by
    show Continuous fun c => d.extY T (g i j c)
    simp only [HypDec.extY_apply]
    exact (hg i j).matrix_mul continuous_const
  have hK := fun i j => GlobalTheory.T.stdChar_annihilator_openSubgroup_finPart_compact D ψ hψ (U.comap (f i j)) (hU.preimage (hf i j))
  choose K hKc hK using hK
  let R : Mx D T.rank ρ → Mx D T.rank ρ := fun k => giA T ⬝ k.map (fun z => incA D D.host.xi0⁻¹ * z)
  have hR : Continuous R :=
    continuous_const.matrix_mul (continuous_id.matrix_map (continuous_const.mul continuous_id))
  refine ⟨R '' (Set.univ.pi fun i => Set.univ.pi fun j => K i j : Set (Mx D T.rank ρ)),
    (isCompact_univ_pi fun i => isCompact_univ_pi fun j => hKc i j).image hR, ?_⟩
  intro x hx
  have hy : ∀ i j, ∃ k ∈ K i j, finPart D (incA D D.host.xi0 * (gA T ⬝ x) i j - k) = 0 := fun i j =>
    hK i j _ fun c hc hc0 => by
      have h1 : (Matrix.single i j (cA D c)).map (infPart D) = 0 := by
        ext a b
        simp only [Matrix.map_apply, Matrix.single_apply, Matrix.zero_apply]
        split_ifs
        · exact infPart_cA' c hc0
        · exact map_zero _
      have h2 := hx (Matrix.single i j (cA D c)) h1 hc
      rwa [symplO_extX_extY_single] at h2
  choose k hk hk0 using hy
  refine ⟨R (Matrix.of k), ⟨Matrix.of k, fun i _ j _ => hk i j, rfl⟩, ?_⟩
  have hsub : ∀ a b : Mx D T.rank ρ, R (a - b) = R a - R b := fun a b => by
    simp only [R]
    rw [← Matrix.mul_sub]
    congr 1
    ext i j
    simp [mul_sub]
  have hx' : R (Matrix.of fun i j => incA D D.host.xi0 * (gA T ⬝ x) i j) = x := by
    simp only [R]
    have e : (Matrix.of fun i j => incA D D.host.xi0 * (gA T ⬝ x) i j).map (fun z => incA D D.host.xi0⁻¹ * z) =
        gA T ⬝ x := by
      ext i j
      simp only [Matrix.map_apply, Matrix.of_apply]
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, one_mul]
    rw [e, giA_gA_cancel]
  have e : x - R (Matrix.of k) = R (Matrix.of fun i j => incA D D.host.xi0 * (gA T ⬝ x) i j - k i j) := by
    have hm : (Matrix.of fun i j => incA D D.host.xi0 * (gA T ⬝ x) i j - k i j) =
        (Matrix.of fun i j => incA D D.host.xi0 * (gA T ⬝ x) i j) - Matrix.of k := Matrix.ext fun _ _ => rfl
    rw [hm, hsub, hx']
  exact (congrArg (fun y => y.map (finPart D)) e).trans (map_finPart_mul_map _ _ _ fun i j => hk0 i j)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FiniteCommCreation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.FinComm

theorem finite_comm_creation : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (μ : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T μ μ om → ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ f, IsHol θ S T ψ f → IsHol θ S T ψ (om (g, h) f) ∧ ∀ P, IsThetaFunO ψ S T (pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P) ∧ om (g, h) (pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P) = pureTensorO ψ θ S T (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (om (g, h) f) P := by
  intro D ψ θ S T a b hS hT δ sc hP μ om hom g hg h hh f hf
  have hθ : IsInfFam θ := hP.inf
  have hg' : g⁻¹ ∈ GfC S := inv_mem hg
  have e : ∀ τ z, Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (om (g, h) f) =
      om (g, h) (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) := by
    intro τ z
    rw [GlobalTheory.OrientedHeis.om_dRho hom hθ g h τ z hf.1, GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ T hh,
      GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ S hg', Matrix.one_mul, Matrix.mul_one]
  refine ⟨⟨hom.om_pres _ f hf.1, fun τ z => ?_⟩, fun P => ⟨?_, ?_⟩⟩
  · have h0 := hf.2 τ z
    unfold annih at h0 ⊢
    rw [e, e, ← map_smul, ← map_add (f := _), h0, map_zero]
  · refine (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ S T μ μ om hom hθ (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1)
      (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) g h ?_ ?_ ?_ ?_ f hf.1 P).1 <;> intro τ
    · rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ S hg]
    · rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ T hh]
    · rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ S hg, Matrix.one_mul]
    · rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ T hh, Matrix.one_mul]
  · exact GlobalTheory.OrientedHeis.om_fin_pureTensorO ψ S T μ μ om hom θ hθ g hg h hh _ _ _ _ f P hf.1

end GlobalTheory.AdForm.FinComm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockPolynomialJetValueEqJetLinearFormRescaled
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker

namespace GlobalTheory.KJInf

theorem mvZ_scal_monomial {ι : Type} {a b : ℕ} (r : ι → ℂ) (k : ι × Fin b × Fin a →₀ ℕ) (c : ℂ) :
    mvZ (fun _ => (1 : Matrix (Fin a) (Fin a) ℂ)) (fun τ => r τ • (1 : Matrix (Fin b) (Fin b) ℂ)) (MvPolynomial.monomial k c) =
      MvPolynomial.monomial k (c * k.prod fun v n => r v.1 ^ n) := by
  set M := mvZ (fun _ => (1 : Matrix (Fin a) (Fin a) ℂ)) (fun τ => r τ • (1 : Matrix (Fin b) (Fin b) ℂ)) with hM
  have hX : ∀ v : ι × Fin b × Fin a, M (MvPolynomial.X v) = MvPolynomial.C (r v.1) * MvPolynomial.X v := by
    intro v
    simp only [hM, mvZ, MvPolynomial.aeval_X]
    rw [Finset.sum_eq_single v.2.1]
    · rw [Finset.sum_eq_single v.2.2]
      · simp
      · intro j _ hj; simp [Matrix.one_apply_ne (Ne.symm hj)]
      · simp
    · intro i _ hi; simp [Matrix.one_apply_ne hi]
    · simp
  have hC : M (MvPolynomial.C c) = MvPolynomial.C c := by
    simp only [hM, mvZ, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  rw [MvPolynomial.monomial_eq, map_mul, MvPolynomial.monomial_eq, hC]
  simp only [Finsupp.prod, map_prod, map_pow, hX, mul_pow, Finset.prod_mul_distrib, MvPolynomial.C_mul, mul_assoc]

end GlobalTheory.KJInf

namespace GlobalTheory.KJInf

theorem jetP_eq_jetL : ∀ (D : D7) (S T : HSp D) (s : ℂ) (cD : D.what₂.Tau → ℂ), (∀ τ, cD τ ≠ 0) → ∀ (G : VCx D.what₂.Tau S.rank T.rank → ℂ) (P : FP D.what₂.Tau S.rank T.rank), jetP S T rfl rfl s G P = jetL cD G (mvZ (fun _ => 1) (fun τ => (s / cD τ) • 1) P) := by
  intro D S T s cD hcD G P
  have hid : (fun v : FVar D T.rank S.rank => (v.1, Fin.cast rfl v.2.1, Fin.cast rfl v.2.2)) = id := by
    funext v; rfl
  unfold GlobalTheory.AdForm.jetP
  rw [hid]
  simp only [Finsupp.mapDomain_id]
  conv_rhs => rw [P.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mvZ_scal_monomial]
  have hm : ∀ x : ℂ, (MvPolynomial.monomial k x : FP D.what₂.Tau S.rank T.rank) = x • MvPolynomial.monomial k 1 := by
    intro x; rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hm, map_smul, jetL_monomial, smul_eq_mul]
  unfold jetC
  rw [mul_assoc, ← mul_assoc (k.prod _), ← Finsupp.prod_mul]
  congr 2
  refine Finsupp.prod_congr fun v _ => ?_
  rw [← mul_pow, div_mul_cancel₀ _ (hcD v.1)]

end GlobalTheory.KJInf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GaussianReadingFiniteRationalHeisenbergTranslate
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.HeisRead

variable {D : D7}


open GlobalTheory.FockCompare in
theorem realPt_eq_iota {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} (hσ : GlobalTheory.FockCompare.Chart θ σ) (S T : HSp D) (Z : RW T S) :
    realPt θ (m := T.rank) (n := S.rank) (fun τ => Matrix.of fun i j => Z τ i j) = iotaW σ T S Z := by
  have hex : ∃ w : Mx D T.rank S.rank, w.map (finPart D) = 0 ∧ ∀ τ, compAt θ τ w = Matrix.of fun i j => Z τ i j :=
    ⟨iotaW σ T S Z, hσ.real_iota T S Z, fun τ => congrFun (hσ.pi_iota T S Z) τ⟩
  have hs := Classical.epsilon_spec hex
  exact hσ.real_ext hs.1 (hσ.real_iota T S Z) (funext fun τ => (hs.2 τ).trans (congrFun (hσ.pi_iota T S Z) τ).symm)

theorem embH_toHom_apply (S T : HSp D) (δ : ℂ) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (τ : D.what₂.Tau)
    (i : Fin T.rank) (j : Fin S.rank) :
    embH (tauE D) δ (toHom S T rfl rfl γ) τ i j = δ * tauE D τ (γ i j) := by
  simp [embH, toHom, Matrix.toLin'_apply]

end GlobalTheory.AdForm.HeisRead

namespace GlobalTheory.AdForm.HeisRead

theorem term_eq (k sc : ℝ) (δ w g : ℂ) (hδ : δ ≠ 0) (hsc : sc * ‖δ‖ ^ 2 = 2 * k) :
    2 * (Complex.I * (k : ℂ) * ((starRingEnd ℂ) g * -(δ⁻¹ * w))).re = ((sc : ℂ) * (w * (starRingEnd ℂ) (δ * g))).im := by
  have hn : Complex.normSq δ ≠ 0 := Complex.normSq_pos.2 hδ |>.ne'
  have hsc' : sc = 2 * k / Complex.normSq δ := by
    rw [Complex.normSq_eq_norm_sq, eq_div_iff (by rwa [← Complex.normSq_eq_norm_sq]), hsc]
  subst hsc'
  simp only [Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im, Complex.conj_re, Complex.conj_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im]
  rw [Complex.normSq_apply] at hn ⊢
  field_simp
  ring
end GlobalTheory.AdForm.HeisRead

namespace GlobalTheory.AdForm.HeisRead
variable {D : D7}

theorem HV_conj {ι : Type} [Fintype ι] {a b : ℕ} (sc : ℝ) (z w : VV ι a b) :
    HV sc w z = starRingEnd ℂ (HV sc z w) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [HV, LinearMap.mk₂'ₛₗ_apply, map_mul, map_sum, Complex.conj_ofReal, Complex.conj_conj]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => mul_comm _ _


open GlobalTheory.OrientedHeis in
theorem omO_eq_im (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (δ : ℂ) (sc : ℝ) (hP : StdPair θ S T δ sc ψ)
    (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (z : VCx D.what₂.Tau S.rank T.rank) :
    omO S T (fun τ i j => -(δ⁻¹ * z τ i j)) (fun τ i j => tauE D τ (γ i j)) =
      (HV sc z (embH (tauE D) δ (toHom S T rfl rfl γ))).im := by
  simp only [omO, LinearMap.mk₂_apply, HV, LinearMap.mk₂'ₛₗ_apply, embH_toHom_apply, formAt, hP.gS, hP.gT, inv_one,
    Matrix.one_apply, apply_ite (tauE D _), map_one, map_zero, hP.xi]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hin : ∀ τ (x1 : Fin S.rank), (∑ x2 : Fin S.rank, ∑ x3 : Fin T.rank, if x1 = x2 then (starRingEnd ℂ) ((tauE D τ) (γ x3 x2)) * -(δ⁻¹ * z τ x3 x1) else 0) =
      ∑ x3 : Fin T.rank, (starRingEnd ℂ) ((tauE D τ) (γ x3 x1)) * -(δ⁻¹ * z τ x3 x1) := fun τ x1 => by
    rw [Finset.sum_comm]; simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [hin]
  rw [Finset.mul_sum, Complex.im_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Finset.sum_comm, Finset.mul_sum, Complex.re_sum, Finset.mul_sum, Finset.mul_sum, Complex.im_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Complex.re_sum, Finset.mul_sum, Finset.mul_sum, Complex.im_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact term_eq _ sc δ _ _ hP.ne hP.scale
end GlobalTheory.AdForm.HeisRead
namespace GlobalTheory.AdForm.HeisRead


open GlobalTheory.FockCompare GlobalTheory.OrientedHeis in
theorem xiN_heisO_finOf : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ f, IsThetaFunO ψ S T f → ∀ γ v, GlobalTheory.AdTh.IsFinOf S T γ v → xiN θ S T hS hT δ sc (heisO ψ S T v f) = Formalism.L2.Th1.H.opU (HV sc) (embH (tauE D) δ (toHom S T hS hT γ)) (xiN θ S T hS hT δ sc f) := by
  intro D ψ θ S T a b hS hT δ sc hP f hf γ v hv
  subst hS hT
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hP.inf
  funext z
  let G : RW T S := fun τ i j => tauE D τ (γ i j)
  let Z : RW T S := fun τ i j => -(δ⁻¹ * z τ i j)
  have hrat : ratW T S γ = v + iotaW σ T S G := by
    have h1 : ratW T S γ - v = iotaW σ T S G := by
      refine hσ.real_ext (x := ratW T S γ - v) ?_ (hσ.real_iota _ _ _) ?_
      · show (ratW T S γ - v).map (finPart D) = 0
        rw [Matrix.map_sub _ (finPart D).map_sub, hv.2, sub_self]
      · rw [hσ.pi_iota, map_sub]
        funext τ i j
        have h0 : piW θ T S v τ i j = 0 := by
          show θ τ (infPart D (v i j)) = 0
          rw [show infPart D (v i j) = 0 from congrFun (congrFun hv.1 i) j, map_zero]
        show θ τ (infPart D (incA D (γ i j))) - piW θ T S v τ i j = _
        rw [h0, sub_zero, comp_incA hP.inf]
    rw [← h1]; abel
  have hX : ∀ τ i j, embH (tauE D) δ (toHom S T rfl rfl γ) τ i j = δ * tauE D τ (γ i j) :=
    GlobalTheory.AdForm.HeisRead.embH_toHom_apply S T δ γ
  have hp : realPt θ (m := T.rank) (n := S.rank) (fun τ => Matrix.of fun i j => -(δ⁻¹ * z τ (Fin.cast rfl i) (Fin.cast rfl j))) = iotaW σ T S Z := by
    simpa using GlobalTheory.AdForm.HeisRead.realPt_eq_iota hσ S T Z
  have hp' : realPt θ (m := T.rank) (n := S.rank) (fun τ => Matrix.of fun i j => -(δ⁻¹ * (z + embH (tauE D) δ (toHom S T rfl rfl γ)) τ (Fin.cast rfl i) (Fin.cast rfl j))) = iotaW σ T S (Z - G) := by
    rw [← GlobalTheory.AdForm.HeisRead.realPt_eq_iota hσ S T (Z - G)]
    congr 1
    funext τ i j
    simp only [Fin.cast_eq_self, Pi.add_apply, hX, Matrix.of_apply, Pi.sub_apply, Z, G]
    field_simp [hP.ne]
    ring
  unfold xiN Formalism.L2.Th1.H.opU heisO
  beta_reduce
  rw [hp, hp']
  have e0 : symplOH S T (iotaW σ T S Z) v = 0 := GlobalTheory.FinTranslate.symplOH_real_fin hv.1 (hσ.real_iota _ _ _)
  have e1 : iotaW σ T S Z + v = ratW T S γ + iotaW σ T S (Z - G) := by rw [hrat, map_sub]; abel
  have e2 : f (ratW T S γ + iotaW σ T S (Z - G)) = ψ (symplOH S T (iotaW σ T S (Z - G)) (iotaW σ T S G)) * f (iotaW σ T S (Z - G)) := by
    rw [hf.quasi, ← GlobalTheory.FinTranslate.symplOH_skew, hrat, symplOH_add_right,
      GlobalTheory.FinTranslate.symplOH_real_fin hv.1 (hσ.real_iota _ _ _), zero_add]
  have e3 : ψ (symplOH S T (iotaW σ T S (Z - G)) (iotaW σ T S G)) =
      Complex.exp (-(Real.pi * Complex.I) * ((HV sc z (embH (tauE D) δ (toHom S T rfl rfl γ))).im : ℂ)) := by
    rw [psi_symplOH hσ hP.std, hσ.pi_iota, LinearMap.map_sub₂, omO_self hσ, sub_zero]
    exact congrArg (fun t : ℝ => Complex.exp (-(Real.pi * Complex.I) * (t : ℂ)))
      (GlobalTheory.AdForm.HeisRead.omO_eq_im θ ψ S T δ sc hP γ z)
  rw [e0, AddChar.map_zero_eq_one, one_mul, e1, e2, e3]
  set X := embH (tauE D) δ (toHom S T rfl rfl γ)
  have hadd : HV sc (z + X) (z + X) = HV sc z z + HV sc z X + HV sc X z + HV sc X X := by
    simp only [map_add (f := _), LinearMap.add_apply]; ring
  have hc : HV sc X z = starRingEnd ℂ (HV sc z X) := GlobalTheory.AdForm.HeisRead.HV_conj sc z X
  have hcj : starRingEnd ℂ (HV sc z X) = HV sc z X - 2 * Complex.I * ((HV sc z X).im : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  rw [← mul_assoc, ← Complex.exp_add, mul_right_comm, ← Complex.exp_add]
  congr 2
  rw [hadd, hc, hcj]
  ring

end GlobalTheory.AdForm.HeisRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GenusTypePlaceSetNotConjugatePlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeConjPg

theorem pg_places_not_isConjPl : ∀ {D : D7} (Pg : Finset (Pl D.host.E)), GlobalTheory.Core.Mi.IsTypePlaces Pg → (∃ e, IsIdemSum e Pg) → ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ IsConjPl (D := D) PP PP' := by
  intro D Pg _ he PP hP PP' hP'
  obtain ⟨e, he⟩ := he
  exact GlobalTheory.ChainOnto.FlagAct.not_isConjPl_of_idemSum he PP hP PP' hP'

end GlobalTheory.SeeConjPg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeChainStandardPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaLineStd

theorem aaOf_top (D : D7) : (Formalism.L2.PairingIndexBounds.F.aaOf D ⊤) = (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) :=
  GlobalTheory.Mem.Col2.Th.perAA_top D.host

end GlobalTheory.ThetaLineStd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDetRootCharMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitRootProd

theorem mu_root_mul : ∀ (D : D7) (V : HSp D) (μ : (AE D)ˣ →* Circle) (n : ℕ), Even n → ResEta D μ n → ∀ e, IsSplitIdem D e → ∀ (s g : GA D V), SuppAt e V s → ∀ x₀ x x₁, IsDetAt e V s x₀ → IsDetRoot V g x → IsDetRoot V (s * g) x₁ → μ x₁ = μ x₀ * μ x := by
  intro D V μ n hn hres e he s g hs x₀ x x₁ h0 hx hx1
  have r0 : IsDetRoot V s x₀ := Formalism.L2.Theta.isDetAt_root he V s hs x₀ h0
  have r : IsDetRoot V (s * g) (x₀ * x) := GlobalTheory.Member.isDetRoot_mul V s g x₀ x r0 hx
  obtain ⟨a, ha⟩ := (GlobalTheory.Member.isDetRoot_laws D V).2.1 (s * g) (x₀ * x) x₁ r hx1
  obtain ⟨⟨η, hη⟩, hall⟩ := hres
  have hμ := hall η hη a
  obtain ⟨k, hk⟩ := hn
  rw [ha, map_mul, hμ, hk, ← two_mul, pow_mul, Formalism.L2.Theta.eta_sq hη a, one_pow, mul_one, map_mul]

end GlobalTheory.SplitRootProd
end

