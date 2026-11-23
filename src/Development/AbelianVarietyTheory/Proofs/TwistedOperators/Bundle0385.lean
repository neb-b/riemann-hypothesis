module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsAtOneRealPlaceOverVacuum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockPolynomialOperatorHeisenbergDerivative
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0314
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0194
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0016
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicStabilizerInertPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0342
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0376
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaTraceBaseChangeIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieAlgebrasAtPlaceActFockVectorsByFockOperators
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
open GlobalTheory.ChainFr (Fr ptF IsVacF)

noncomputable section

namespace GlobalTheory.ArchRec.LieAtPlace

variable {D : D7}


open scoped ComplexOrder in
theorem cart_isCartanInv {V : HSp D} (A : Fr V) (τ : D.what₂.Tau) : IsCartanInv (gramAt D V τ) (A.cart τ) := by
  have h1 : A.fr τ * (A.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ))
  have h2 : (A.fr τ)⁻¹ * A.fr τ = 1 := mul_eq_one_comm.1 h1
  have hJ := Formalism.REAL.Jm_mul_self (A.ε τ)
  have hJ' := Formalism.REAL.Jm_conjTranspose (A.ε τ)
  have hG : gramAt D V τ * A.cart τ = (A.fr τ)ᴴ * A.fr τ := by
    rw [← A.fr_gram τ]; unfold Fr.cart
    calc _ = (A.fr τ)ᴴ * (Formalism.REAL.Jm (A.ε τ) * (A.fr τ * (A.fr τ)⁻¹) * Formalism.REAL.Jm (A.ε τ)) * A.fr τ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one, hJ, Matrix.mul_one]
  have hs : A.cart τ * A.cart τ = 1 := by
    unfold Fr.cart
    calc _ = (A.fr τ)⁻¹ * (Formalism.REAL.Jm (A.ε τ) * (A.fr τ * (A.fr τ)⁻¹) * Formalism.REAL.Jm (A.ε τ)) * A.fr τ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one, hJ, Matrix.mul_one, h2]
  refine ⟨hs, ?_, ?_⟩
  · have hGh : (gramAt D V τ)ᴴ = gramAt D V τ := by
      rw [← A.fr_gram τ]; simp [Matrix.conjTranspose_mul, hJ', Matrix.mul_assoc]
    have h3 : (A.cart τ)ᴴ * gramAt D V τ = gramAt D V τ * A.cart τ := by
      have := congrArg Matrix.conjTranspose hG
      rw [Matrix.conjTranspose_mul, hGh, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at this
      rw [this, hG]
    rw [h3, Matrix.mul_assoc, hs, Matrix.mul_one]
  · rw [hG]
    exact Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit (A.fr_unit τ))

theorem exists_fr {V : HSp D} {τ : D.what₂.Tau} {s fr : Mn V.rank} {ε : Fin V.rank → Bool}
    (h : IsFrameOf (gramAt D V τ) s ε fr) : ∃ A : Fr V, A.ε τ = ε ∧ A.fr τ = fr ∧ A.cart τ = s := by
  classical
  obtain ⟨A⟩ := (GlobalTheory.FrameExists.frame_exists_signCompat D V).1
  refine ⟨⟨Function.update A.ε τ ε, Function.update A.fr τ fr, fun ρ => ?_, fun ρ => ?_⟩, by simp, by simp, ?_⟩
  · by_cases e : ρ = τ
    · subst e; rw [Function.update_self]; exact h.1
    · rw [Function.update_of_ne e]; exact A.fr_unit ρ
  · by_cases e : ρ = τ
    · subst e; rw [Function.update_self, Function.update_self]; exact h.2.1
    · rw [Function.update_of_ne e, Function.update_of_ne e]; exact A.fr_gram ρ
  · simp [Fr.cart, h.2.2]

theorem pure_rename {ι κ X : Type} {A : ι → (X → ℂ) → (X → ℂ)} {A' : κ → (X → ℂ) → (X → ℂ)} {g : X → ℂ}
    (hX : ∀ v Q, pureTensorL A g (MvPolynomial.X v * Q) = A v (pureTensorL A g Q))
    (hX' : ∀ v Q, pureTensorL A' g (MvPolynomial.X v * Q) = A' v (pureTensorL A' g Q))
    (e : κ → ι) (h : ∀ k, A (e k) = A' k) (Q : MvPolynomial κ ℂ) :
    pureTensorL A g (MvPolynomial.rename e Q) = pureTensorL A' g Q := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.rename_C, ← mul_one (MvPolynomial.C a : MvPolynomial ι ℂ),
      ← mul_one (MvPolynomial.C a : MvPolynomial κ ℂ), MvPolynomial.C_mul', MvPolynomial.C_mul', map_smul, map_smul,
      GlobalTheory.FockIndep.pure_one, GlobalTheory.FockIndep.pure_one]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    rw [mul_comm, map_mul (MvPolynomial.rename e), MvPolynomial.rename_X, hX, hX', hp, h]

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem ptF_rename (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A : Fr S) (B : Fr T) (τ : D.what₂.Tau)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (P : LPol T.rank S.rank) :
    ptF ψ θ A B f (MvPolynomial.rename (fun s => (τ, s)) P) =
      ptAt ψ θ S T τ (A.cart τ) (B.cart τ) (A.fr τ)⁻¹ (B.fr τ)⁻¹ f P := by
  have hS := cart_isCartanInv A
  have hT := cart_isCartanInv B
  refine pure_rename (fun v Q => ?_) (fun v Q => ?_) _ (fun k => rfl) P
  · refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add)
      (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) (fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h) ?_ ?_ ?_ hf Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' hψ hθ i.1 _ hS hT j.1 _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h
  · refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add)
      (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) (fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h) ?_ ?_ ?_ hf Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' hψ hθ τ _ hS hT τ _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h

theorem ins_one {a b : ℕ} (τ : D.what₂.Tau) (p : LPol b a) :
    GlobalTheory.Chain.RealIt.GlueProof.ins τ (fun _ => 1) p = (MvPolynomial.rename (fun s => (τ, s)) p : PolF D b a) := by
  rw [GlobalTheory.Chain.RealIt.GlueProof.ins_apply]
  simp [GlobalTheory.Chain.RealIt.GlueProof.rest]

theorem derAll_of_one (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {τ : D.what₂.Tau}
    {sS frS : Mn S.rank} {εS : Fin S.rank → Bool} {sT frT : Mn T.rank} {εT : Fin T.rank → Bool}
    (hS : IsFrameOf (gramAt D S τ) sS εS frS) (hT : IsFrameOf (gramAt D T τ) sT εT frT)
    {ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {γ : ℝ → GA D S × GA D T} (hγ : QuadGen ψ θ τ ω γ)
    {f₀ : WO S T → ℂ} (h0 : IsThetaFunO ψ S T f₀) (v0 : IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f₀) (n0 : f₀ ≠ 0)
    {P P' : LPol T.rank S.rank}
    (hd : ∀ z, HasDerivAt (fun t : ℝ => ω (γ t) (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f₀ P) z)
      (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f₀ P' z) 0)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hv : IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f) :
    DerAll ψ ω γ (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f P) (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f P') := by
  obtain ⟨k, c, z, z', lam, hq⟩ := hγ
  choose L hL using _root_.GlobalTheory.ArchRec.DerFock.exists_dRho_ptAt D ψ θ S T τ hψ hθ sS frS εS sT frT εT hS hT
  have hc := _root_.GlobalTheory.OnePlaceFock.fock_at_one_place D ψ θ S T τ hψ hθ sS frS εS sT frT εT hS hT
  have key : ∀ g, IsThetaFunO ψ S T g → IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) g →
      DerAll ψ ω γ (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ g P)
        (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ g ((∑ i, c i • L (z i) (L (z' i) P)) + lam • P)) := fun g hg vg => by
    have h := hq _ ((hc g hg vg).1 P)
    simp only [hL _ g hg vg] at h
    have e : ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ g ((∑ i, c i • L (z i) (L (z' i) P)) + lam • P) =
        (∑ i, c i • ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ g (L (z i) (L (z' i) P))) +
          lam • ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ g P := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [ptAt, map_add (f := _), map_sum, map_smul]
    rw [e]
    exact h
  have e : P' = (∑ i, c i • L (z i) (L (z' i) P)) + lam • P := by
    refine ((hc f₀ h0 v0).2 n0).1 (funext fun w => (hd w).unique ?_)
    simpa using (key f₀ h0 v0).1 1 w
  rw [e]
  exact key f hf hv

theorem lieAt_of_vacAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (τ : D.what₂.Tau), IsInfFam θ → IsWeilDatumO ψ S T χS χT ω → ∀ aS aT : ℚ, HasInfExp D χS τ aS → HasInfExp D χT τ aT → ∀ (sS frS : Mn S.rank) (εS : Fin S.rank → Bool) (sT frT : Mn T.rank) (εT : Fin T.rank → Bool), IsFrameOf (gramAt D S τ) sS εS frS → IsFrameOf (gramAt D T τ) sT εT frT → ∀ f, IsThetaFunO ψ S T f → IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f → LieAt ψ θ τ ω εS frS εT frT aS aT (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f) := by
  intro D ψ θ S T χS χT ω τ hθ hW aS aT haS haT sS frS εS sT frT εT hS hT f hf hv
  have hψ := hW.std
  obtain ⟨A, rfl, rfl, rfl⟩ := exists_fr hS
  obtain ⟨B, rfl, rfl, rfl⟩ := exists_fr hT
  obtain ⟨f₀, h0, n0⟩ := GlobalTheory.IndefiniteRowSideFullHecke.BoundedCommutantVacua.exists_isVac_ne_zero hψ hθ (cart_isCartanInv A) (cart_isCartanInv B)
  have hl := _root_.GlobalTheory.LieScalar.lieFockAll D S T A B θ ψ χS χT ω f₀ τ aS aT hθ hW haS haT h0
  have hg := _root_.GlobalTheory.ArchRec.Gen.quadGen_oneP D ψ θ S T χS χT ω τ hθ hW
  refine ⟨fun X hX P => ?_, fun Y hY P => ?_⟩
  · refine derAll_of_one hψ hθ hS hT (hg.1 X hX) h0.1 (h0.2 τ) n0 (fun z => ?_) hf hv
    have h := hl.1 X hX (MvPolynomial.rename (fun s => (τ, s)) P) z
    rw [← ins_one, GlobalTheory.Chain.RealIt.GlueProof.fockS_ins, ← map_smul, ← map_add (f := _), ins_one, ins_one,
      ptF_rename hψ hθ A B τ h0.1, ptF_rename hψ hθ A B τ h0.1, neg_smul, ← sub_eq_add_neg] at h
    exact h
  · refine derAll_of_one hψ hθ hS hT (hg.2 Y hY) h0.1 (h0.2 τ) n0 (fun z => ?_) hf hv
    have h := hl.2 Y hY (MvPolynomial.rename (fun s => (τ, s)) P) z
    rw [← ins_one, GlobalTheory.Chain.RealIt.GlueProof.fockT_ins, ← map_smul, ← map_add (f := _), ins_one, ins_one,
      ptF_rename hψ hθ A B τ h0.1, ptF_rename hψ hθ A B τ h0.1] at h
    exact h

end GlobalTheory.ArchRec.LieAtPlace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalDecompositionNonsplitPlace
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

namespace GlobalTheory.InertIwasawaLoc

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.LFun GlobalTheory.InertIwasawaIso

theorem exists_loc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {c : 𝓞 E} (hc : (c : E) + σ c = 1) {n r : ℕ}
    {J : Matrix (Fin n) (Fin n) E} (hJ : IsHermND σ J) {L : Submodule (𝓞 E) (Fin n → E)} [Submodule.IsFullLattice E L]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (hw : Formalism.UG.IsInertAt F E v w)
    (hv : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.UnramAt F E v) (hL : IsSelfDualAt σ J L v) {e : Matrix (Fin n) (Fin r) E}
    {p : Matrix (Fin r) (Fin n) E} (hp : p * e = 1) (he : Formalism.UG.cT (σ : E →+* E) e * J * e = 0) (y : GLoc σ J v) :
    ∃ q k : GLoc σ J v, k ∈ stabLoc σ J L v ∧ y = q * k ∧ ∃ β : GL (Fin r) (Fv F v ⊗[F] E),
      (HA.mat (Fv F v) σ J q).1 * e.map (inclR (Fv F v)) = e.map (inclR (Fv F v)) * β.1 := by
  have h := (InertChart.under_eq_iff hw w).2 rfl
  obtain ⟨a, ha⟩ := Frames.exists_isLatticeFrame (F := F) L
  have hN := GlobalTheory.UnramSelfDual.exists_norm v hσ (GlobalTheory.UnramConjUnit.exists_sub_conj_unit _ _ _ hσ v hv)
  have hO : ∀ z, z ∈ GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.OEv F E v ↔ z ∈ intLoc F E v := GlobalTheory.StabOrbit.mem_OEv_iff v
  simp only [hO] at hN
  let ι : E →+* Fv F v ⊗[F] E := inclR (Fv F v)
  obtain ⟨k, h1, h2, h3⟩ := exists_stab (intLoc F E v) (w.adicCompletionIntegers E)
    (InertChart.complEquiv hw h) (InertChart.mem_intLoc_iff hw h)
    (σ := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Fv F v) σ) (fun _ => sigR_mem_intLoc σ) (sigR_invol (InertChart.conj_conj hσ))
    (τ := ι c) (tmul_mem_intLoc (one_mem _) c)
    (by change ι c + ι (σ c) = 1
        rw [← map_add (f := _), hc, map_one]) hN
    (J := JR (Fv F v) J) (by ext i j; exact congrArg ι (hJ.1 i j))
    ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_det_JR hJ.2)) (Λ := latLoc F L v)
    (fun y => Submodule.ext_iff.1 hL y) (ha v) (X := e.map ι) (P := p.map ι)
    (by rw [← Matrix.map_mul, hp, Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.cT_map (σ : E →+* E) _ ι (fun _ => rfl), show JR (Fv F v) J = J.map ι from rfl,
          ← Matrix.map_mul, ← Matrix.map_mul, he, Matrix.map_zero _ (map_zero _)])
    (g := matHom _ σ J y) y.2
  let κ : GLoc σ J v := ⟨k, h1⟩
  exact ⟨y * κ⁻¹, κ, h2, (inv_mul_cancel_right y κ).symm, h3⟩

end GlobalTheory.InertIwasawaLoc

namespace GlobalTheory.InertIwasawaLoc

open scoped Matrix TensorProduct

end GlobalTheory.InertIwasawaLoc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemKernelOfGeometricFibresReducedBaseStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_kernel_of_geometric_fibres_reduced_base : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : Type) [CommRing T] [IsReduced T] (x x' : Sp T ⟶ Xo.X) (Ψ : Gx x ⟶ Gx x') (a : Over.mk x ⟶ Xo.univ.t.G), Ψ ≫ (fst (Over.mk x') Xo.univ.t.G).left = (fst (Over.mk x) Xo.univ.t.G).left → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (χ : T →+* Ω) (x₁ x₁' : Sp Ω ⟶ Xo.X) (Ψ₁ : Gx x₁ ⟶ Gx x₁'), IsFib χ Ψ Ψ₁ → ∃ b ∈ transKer Xo.univ.t.G Ψ₁, b.left = spMap χ ≫ a.left) → a ∈ transKer Xo.univ.t.G Ψ := by
  first | exact @GlobalTheory.HeckeEx.mem_transKer_of_geometric | exact GlobalTheory.HeckeEx.mem_transKer_of_geometric | (intros; apply GlobalTheory.HeckeEx.mem_transKer_of_geometric <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermsRationalUnipotentInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.UnipMixed

variable {D : D7}

theorem mt_mul_frame (V : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (g : GA D V) (hg : g ∈ NI V C) :
    mt V g * C.map (incA D) = C.map (incA D) := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨h, -, -⟩ := hg
    have h' : (mt V g - 1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) * (C.map (incA D) : Matrix (Fin V.rank) (Fin r) (AE D)) = 0 := h
    rwa [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h'
  | one => rw [GlobalTheory.AdelicLatMove.mt_one, Matrix.one_mul]
  | mul g h _ _ hg hh => rw [GlobalTheory.AdelicLatMove.mt_mul, Matrix.mul_assoc, hh, hg]
  | inv g _ hg =>
    conv_lhs => rw [← hg]
    rw [← Matrix.mul_assoc, ← GlobalTheory.AdelicLatMove.mt_mul, inv_mul_cancel, GlobalTheory.AdelicLatMove.mt_one, Matrix.one_mul]

theorem hO_eq_trace (S T : HSp D) (x y : WO S T) :
    hO S T x y = Matrix.trace (S.gram⁻¹.map (incA D) * (y.map (cA D))ᵀ * T.gram.map (incA D) * x) := by
  simp only [hO, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans ?_
  exact Finset.sum_comm

theorem symplOH_isoPart_eq_zero (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (t : Mx D W.rank r)
    (δ : WO V W) (hδ : δ * C.map (incA D) = 0) : symplOH V W (isoPart V W C t) δ = 0 := by
  have hh : hO V W (isoPart V W C t) δ = 0 := by
    rw [hO_eq_trace]
    have hP : (adj D C * V.gram).map (incA D) = ((C.map (incA D)).map (cA D))ᵀ * V.gram.map (incA D) := by
      rw [Matrix.map_mul]; rfl
    have hC : ((C.map (incA D)).map (cA D))ᵀ * (δ.map (cA D))ᵀ = 0 := by
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, hδ, Matrix.map_zero _ (map_zero _), Matrix.transpose_zero]
    simp only [isoPart]
    rw [hP, ← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, Matrix.mul_assoc _ (V.gram.map (incA D)), GlobalTheory.SplitOnto.gram_mul_inv, Matrix.mul_one, hC,
      Matrix.zero_mul, Matrix.zero_mul, Matrix.trace_zero]
  simp only [symplOH, symplO, hh, mul_zero, map_zero]

theorem heisO_add_rat (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) {ψ : AddChar (AF D.host.F) ℂ}
    (hψ : IsStdChar D ψ (-1)) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
    (x δ : Matrix (Fin W.rank) (Fin V.rank) D.host.E) (hδ : δ.map (incA D) * C.map (incA D) = 0) (t : Mx D W.rank r) :
    heisO ψ V W (x.map (incA D) + δ.map (incA D)) f (isoPart V W C t) =
      heisO ψ V W (x.map (incA D)) f (isoPart V W C t) := by
  have o := symplOH_isoPart_eq_zero V W C t _ hδ
  have ha := GlobalTheory.OrientedFormLaws.symplOH_rat (S := V) (T := W) δ x
  generalize (1 / 2 * Algebra.trace D.host.F D.host.E (D.host.xi0 * GlobalTheory.LatVac.hRat V W δ x)) = a at ha
  have q := hf.quasi δ (isoPart V W C t + x.map (incA D))
  have e : isoPart V W C t + (x.map (incA D) + δ.map (incA D)) = ratW W V δ + (isoPart V W C t + x.map (incA D)) := by
    simp only [ratW]; abel
  have s1 : symplOH V W (ratW W V δ) (isoPart V W C t + x.map (incA D)) = algebraMap D.host.F (AF D.host.F) a := by
    rw [GlobalTheory.FinTranslate.symplOH_add_right, GlobalTheory.FinTranslate.symplOH_skew, ratW, o, neg_zero, zero_add, ha]
  have s2 : ψ (-(algebraMap D.host.F (AF D.host.F) a)) = 1 := by
    rw [← map_neg]; exact hψ.1.2.2.1 (-a)
  simp only [heisO]
  rw [e, q, s1, s2, GlobalTheory.FinTranslate.symplOH_add_right, o, add_zero, one_mul]

theorem res_heisO_unip : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ n ∈ NI V C, n ∈ GQ V → ∀ (y : Matrix (Fin W.rank) (Fin r) D.host.E) f, IsThetaFunO ψ V W f → res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) (ω (n, 1) f)) 0 = res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) f) 0 := by
  intro D V V' W r C C' B hs _ _ _ ψ χS χT ω hω μ 𝓨 hcov n hnN hnQ y f hf
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : Matrix (Fin V.rank) (Fin V.rank) D.host.E, mt V n = n₀.map (incA D) := by
    obtain ⟨γ', -, e⟩ := hnQ
    exact ⟨γ'.1, (congrArg Units.val e).symm⟩
  set X₀ : Matrix (Fin W.rank) (Fin V.rank) D.host.E := y * (adj D C' * V.gram) with hX₀
  have hx : isoPart V W C' (y.map (incA D)) = X₀.map (incA D) := by
    simp only [isoPart, hX₀, Matrix.map_mul]
  set δ : Matrix (Fin W.rank) (Fin V.rank) D.host.E := X₀ * (n₀ - 1) with hδdef
  have hδ : δ.map (incA D) * C.map (incA D) = 0 := by
    rw [hδdef, Matrix.map_mul, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _), ← hn₀, Matrix.mul_assoc,
      Matrix.sub_mul, Matrix.one_mul, mt_mul_frame V C n hnN, sub_self, Matrix.mul_zero]
  have hx' : actO V W n⁻¹ 1 (X₀.map (incA D)) = X₀.map (incA D) + δ.map (incA D) := by
    simp only [actO, inv_inv, GlobalTheory.AdelicLatMove.mt_one, Matrix.one_mul, hn₀, hδdef]
    rw [← Matrix.map_mul, Matrix.mul_sub, Matrix.mul_one, ← Matrix.map_add _ (map_add _), add_sub_cancel]
  have hA : heisO ψ V W (X₀.map (incA D)) (ω (n, 1) f) =
      ω (n, 1) (heisO ψ V W (actO V W n⁻¹ 1 (X₀.map (incA D))) f) := by
    rw [hω.om_heis n 1 _ f hf]
    congr 1
    have := GlobalTheory.AdelicLatMove.actO_actO_inv V W n 1 (X₀.map (incA D))
    rw [inv_one] at this
    exact this.symm
  have hK := _root_.GlobalTheory.UnipRes.res_unip D V V' W r C B hs ψ χS χT ω hω μ 𝓨 hcov ⟨n, hnN⟩ _
    (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hω.std hf (actO V W n⁻¹ 1 (X₀.map (incA D))))
  rw [hx, hA, show res V V' W C B μ 𝓨 (ω (n, 1) (heisO ψ V W (actO V W n⁻¹ 1 (X₀.map (incA D))) f)) =
    res V V' W C B μ 𝓨 (heisO ψ V W (actO V W n⁻¹ 1 (X₀.map (incA D))) f) from hK, hx']
  have hm : midPart V V' W B 0 = 0 := by simp [midPart]
  simp only [res, hm, add_zero]
  congr 1
  funext t
  exact heisO_add_rat V W C hω.std hf X₀ δ hδ t

end GlobalTheory.UnipMixed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedMulPullbackCommutesBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeExBC

theorem isMulPull_baseChange : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x : Sp T ⟶ Xo.X} {x₁ : Sp Ω ⟶ Xo.X} {pm : Gx x₁ ⟶ Gx x} {p : ℕ} {s : LB.Sec (PPx x)} {s' : LB.Sec (PPx x₁)} {s₁ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk x))}, IsCan χ pm → (∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP s' r z J = sv Xo.univ.t.G Xo.univ.t.PP s (r ≫ pm) z J) → IsMulPull Xo.univ.t.G Xo.univ.t.PP p s s₁ → ∃ s₁' : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk x₁)), IsMulPull Xo.univ.t.G Xo.univ.t.PP p s' s₁' ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → sv Xo.univ.t.G Xo.univ.t.PP s₁' r z J = sv Xo.univ.t.G Xo.univ.t.PP s₁ (r ≫ pm) z J := by
  intro E _ _ _ H Dw l Xo T Ω _ _ χ x x₁ pm p s s' s₁ hc hv h
  obtain ⟨hx, h₁, h₂⟩ := hc
  let σ : (Over.mk x₁ : Over Xo.X) ⟶ Over.mk x := Over.homMk (spMap χ) hx.symm
  have hpm : pm = (σ ▷ Xo.univ.t.G).left := GlobalTheory.HeckeFrCompare.gx_ext
    (by rw [h₂, ← Over.comp_left, whiskerRight_fst]; rfl) (by rw [h₁, ← Over.comp_left, whiskerRight_snd])
  obtain ⟨s'', hs''⟩ := exists_pullRel Xo.univ.t.PP.L 1 (σ ▷ Xo.univ.t.G) (whiskerRight_snd σ Xo.univ.t.G) s
  have e : s'' = s' := GlobalTheory.ThetaTrace.sec_ext (sec_ext_val (L := Xo.univ.t.PP.L)
    (φ := fun _ : Fin 1 => (snd (Over.mk x₁) Xo.univ.t.G).left) Xo.univ.t.PP.isLB fun z J hJ =>
      (GlobalTheory.ThetaTraceBC.sv_of_pullRel hs'' _ z hJ).trans (by rw [← hpm]; exact (hv _ _ z J hJ).symm))
  subst e
  obtain ⟨s₁', hm, hr⟩ := GlobalTheory.ThetaTraceBC.isMulPull_pull σ hs'' h
  exact ⟨s₁', hm, fun Z r z J hJ => (GlobalTheory.ThetaTraceBC.sv_of_pullRel hr r z hJ).trans (by rw [hpm])⟩

end GlobalTheory.HeckeExBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictionTransfer
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.Twist.RestrictionTransfer

theorem rest_transfer : ∀ (F : Type) [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (r : (κ → AF F) → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r → (∃ x, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r x ≠ 0) →
    ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f₁ r := by
  intro F _ _ κ _ f r ⟨hinv, hsch⟩ ⟨x₀, hx₀⟩ f₁
  refine ⟨hinv, ?_⟩
  set a₀ : κ → mixedEmbedding.mixedSpace F := fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x₀ i) with ha₀
  have hc : f a₀ ≠ 0 := by
    intro h; apply hx₀; simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]; rw [← ha₀, h, zero_mul]
  let zz : (κ → AF F) → (κ → AF F) := fun x i =>
    (((x₀ i).1 - (x i).1, 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
  have hz1 : ∀ x i, (x i + zz x i).1 = (x₀ i).1 := by
    intro x i; show (x i).1 + ((x₀ i).1 - (x i).1) = _; ring
  have hz2 : ∀ x i, (x i + zz x i).2 = (x i).2 := by
    intro x i; show (x i).2 + 0 = _; simp
  have hev : ∀ x, (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((x + zz x) i)) = a₀ := by
    intro x; funext i; simp only [Pi.add_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI, ha₀]; rw [hz1]
  have hAt : ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (zz x) := by
    intro x u hu
    have hu1 : u.1 = 0 := by
      exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.mp hu
    funext i
    show ((u.1 * ((x₀ i).1 - (x i).1), u.2 * 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) = (0, 0)
    rw [hu1]; simp
  let L : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) :=
    { toFun := fun Φ x => f₁ (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x i)) * Φ (x + zz x)
      map_add' := by intro Φ Ψ; funext x; simp [mul_add]
      map_smul' := by intro c Φ; funext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
  have key : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, L Φ ∈ GlobalTheory.WeilM.schA F κ := by
    intro Φ hΦ
    induction hΦ using Submodule.span_induction with
    | mem Φ hΦ =>
      obtain ⟨g, h, hh, rfl⟩ := hΦ
      have : L (GlobalTheory.WeilM.pureA F g h) = g a₀ • GlobalTheory.WeilM.pureA F f₁ h := by
        funext x
        have e := hev x
        simp only [L, LinearMap.coe_mk, AddHom.coe_mk, GlobalTheory.WeilM.pureA, Pi.smul_apply, smul_eq_mul]
        simp only [Pi.add_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI] at e ⊢
        rw [e]
        have : (fun i => (x i + zz x i).2) = fun i => (x i).2 := funext fun i => hz2 x i
        rw [this]; ring
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨f₁, h, hh, rfl⟩)
    | zero => simp
    | add Φ Ψ _ _ h1 h2 => rw [map_add (f := _)]; exact Submodule.add_mem _ h1 h2
    | smul c Φ _ h1 => rw [map_smul]; exact Submodule.smul_mem _ c h1
  have hLt : L (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r) =
      f a₀ • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f₁ r := by
    funext x
    simp only [L, LinearMap.coe_mk, AddHom.coe_mk, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, Pi.smul_apply, smul_eq_mul]
    rw [hev x, hinv x (zz x) (hAt x)]; ring
  have hm := key _ hsch
  rw [hLt] at hm
  have := Submodule.smul_mem _ (f a₀)⁻¹ hm
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

end GlobalTheory.Twist.RestrictionTransfer
end

