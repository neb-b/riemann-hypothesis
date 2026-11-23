module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0763
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1182
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1192
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0826
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1181
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1177
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1180
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1175
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1186

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthonormalFrameFinitePartMemCompletedLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameLat

theorem frame_finRat_mem_latO : ∀ {D : D7} (S T : HSp D) (B : GL (Fin S.rank) D.host.E) (B' : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * S.gram * B.1 = 1 → ∀ M : Matrix (Fin T.rank) (Fin S.rank) D.host.E, (∀ i j, M i j ∈ D.host.AA) → GlobalTheory.VacUnique.finRat S T (-(B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1)) ∈ latO S T (colLat B : Set (Fin S.rank → D.host.E)) (colLat B' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  intro D S T B B' hB M hM
  have hinv : ((B⁻¹ : GL (Fin S.rank) D.host.E).1) = Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * S.gram := by
    have h1 : ((B⁻¹ : GL (Fin S.rank) D.host.E).1) * B.1 = 1 := by
      have := congrArg Units.val (inv_mul_cancel B); simpa using this
    have h2 : B.1 * ((B⁻¹ : GL (Fin S.rank) D.host.E).1) = 1 := by
      have := congrArg Units.val (mul_inv_cancel B); simpa using this
    calc ((B⁻¹ : GL (Fin S.rank) D.host.E).1)
        = (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * S.gram * B.1) * ((B⁻¹ : GL (Fin S.rank) D.host.E).1) := by rw [hB, one_mul]
      _ = _ := by rw [Matrix.mul_assoc _ B.1, h2, Matrix.mul_one]
  have key : -(B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1) = ∑ l, ∑ k,
      GlobalTheory.LatVac.genMap S T (-M l k) (fun m => B.1 m k) (fun i => B'.1 i l) := by
    rw [hinv]
    ext i j
    simp only [GlobalTheory.LatVac.genMap, Matrix.neg_apply, Matrix.sum_apply, Matrix.of_apply, Matrix.mul_apply]
    have hc : ∀ k m, Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 k m = star (B.1 m k) := fun _ _ => rfl
    simp only [hc, Finset.sum_mul, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    rw [neg_mul, neg_mul, mul_assoc, mul_assoc, mul_left_comm]
  have hmem : -(B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1) ∈ GlobalTheory.LatVac.latRat S T (colLat B : Set (Fin S.rank → D.host.E)) (colLat B' : Set (Fin T.rank → D.host.E)) := by
    rw [key]
    refine AddSubgroup.sum_mem _ fun l _ => AddSubgroup.sum_mem _ fun k _ => AddSubgroup.subset_closure ?_
    refine ⟨-M l k, Submodule.neg_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) (hM l k), _, ?_, _, ?_, rfl⟩
    · exact Submodule.subset_span ⟨k, rfl⟩
    · exact Submodule.subset_span ⟨l, rfl⟩
  exact GlobalTheory.LatVac.finTens_mem_latO (GlobalTheory.LatVac.one_mem_intAf _) hmem

end GlobalTheory.FrameLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyFunMemSmoothVectors
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct ContDiff

namespace GlobalTheory.CentralOps

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

variable {D : D7}

def algEntry (V : HSp D) (τ : D.what₂.Tau) (m j : Fin V.rank) : AlgInf V →ₗ[ℝ] ℂ where
  toFun u := (u : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) τ m j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem contDiff_expEntry (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D}
    (R : RealPoints θ V) (τ : D.what₂.Tau) (m j : Fin V.rank) :
    ContDiff ℝ ∞ fun X : LieN V => algEntry V τ m j (NormedSpace.exp (jInf V X)) := by
  haveI : CompleteSpace (AlgInf V) := FiniteDimensional.complete ℝ (AlgInf V)
  haveI : FiniteDimensional ℝ (LieN V) := FiniteDimensional.of_injective (jInf V) (isLieData R).inj
  have h1 : ContDiff ℝ ∞ (NormedSpace.exp : AlgInf V → AlgInf V) :=
    contDiff_iff_contDiffAt.2 fun x => (NormedSpace.exp_analytic (𝕂 := ℝ) x).contDiffAt
  exact (LinearMap.toContinuousLinearMap (algEntry V τ m j)).contDiff.comp
    (h1.comp (LinearMap.toContinuousLinearMap (jInf V)).contDiff)

theorem realEntries_mul_exp (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D}
    (R : RealPoints θ V) (g : GA D V) (X : LieN V) (p : D.what₂.Tau × Fin V.rank × Fin V.rank) :
    realEntries θ V (g * expMap (jInf V) (secInf θ V) X) p =
      ∑ m, infMat D.sp.cm.sig V.gram (θ p.1) g p.2.1 m * algEntry V p.1 m p.2.2 (NormedSpace.exp (jInf V X)) := by
  have h2 := (isExpFam_expInf R X).2 p.1
  change infMat D.sp.cm.sig V.gram (θ p.1) (g * expInf θ V X) p.2.1 p.2.2 = _
  rw [R.2.2.2.1, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  change infMat D.sp.cm.sig V.gram (θ p.1) (expInf θ V X) m p.2.2 = (NormedSpace.exp (jInf V X) : AlgInf V) p.1 m p.2.2
  rw [exp_algInf, h2]
  rfl

theorem polyFun_mem_smF : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D),
    RealPoints θ V → ∀ P : PolyE V, polyFun θ V P ∈ SmF θ V := by
  intro D θ V R P g
  have hc : ∀ p : D.what₂.Tau × Fin V.rank × Fin V.rank,
      ContDiff ℝ ∞ fun X : LieN V => realEntries θ V (g * expMap (jInf V) (secInf θ V) X) p := by
    intro p
    simp only [realEntries_mul_exp θ R]
    exact ContDiff.sum fun m _ => contDiff_const.mul (contDiff_expEntry θ R p.1 m p.2.2)
  change ContDiff ℝ ∞ fun X : LieN V => MvPolynomial.eval (realEntries θ V (g * expMap (jInf V) (secInf θ V) X)) P
  induction P using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa only [map_add (f := _)] using hp.add hq
  | mul_X p n hp => simpa only [map_mul, MvPolynomial.eval_X] using hp.mul (hc n)

end GlobalTheory.CentralOps

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalPointFinitePartIsotropicPairing
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RatFinIso

variable {D : D7}

theorem symplOH_ratW_finRat_neg (S T : HSp D) (v : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    symplOH S T (ratW T S v) (GlobalTheory.VacUnique.finRat S T (-v)) = 0 := by
  set u : WO S T := ratW T S v - GlobalTheory.VacUnique.finRat S T v with hu
  have hfin : u.map (finPart D) = 0 := by
    funext i j
    have e1 := congrFun (congrFun (GlobalTheory.VacUnique.finRat_fin S T v) i) j
    show finPart D (ratW T S v i j - GlobalTheory.VacUnique.finRat S T v i j) = 0
    rw [RingHom.map_sub]
    simp only [Matrix.map_apply] at e1
    rw [e1, sub_self]
  have hr : ratW T S v = u + GlobalTheory.VacUnique.finRat S T v := by rw [hu, sub_add_cancel]
  rw [hr, GlobalTheory.FinTranslate.symplOH_add_left, map_neg, GlobalTheory.FinTranslate.symplOH_neg_right,
    GlobalTheory.FinTranslate.symplOH_neg_right, GlobalTheory.FinTranslate.symplOH_self,
    GlobalTheory.FinTranslate.symplOH_real_fin (GlobalTheory.VacUnique.finRat_inf S T v) hfin]
  simp

theorem isotropic : ∀ {D : D7} (S T : HSp D) (v : Matrix (Fin T.rank) (Fin S.rank) D.host.E),
    symplOH S T (ratW T S v) (GlobalTheory.VacUnique.finRat S T (-v)) = 0 :=
  fun S T v => symplOH_ratW_finRat_neg S T v

end GlobalTheory.RatFinIso

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPointsRestrictionSmoothRightDerivEq
section
noncomputable section

open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.HCA GroundTheory.Automorphic NormedSpace
open scoped ContDiff

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

namespace GlobalTheory.HCA

theorem glRes_smooth_rightDeriv : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ),
    ∀ φ : Sm E a, ∀ x, (glH E a).IsSmoothFun (glRes φ.1 x) ∧
      ∀ X : glL E a, (glH E a).rightDeriv X (glRes φ.1 x) = glRes (lie E a (toL X.1) φ).1 x := by
  intro E _ _ _ a φ x
  let T : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap
  have hT : ∀ M, T M = toL M := fun _ => rfl
  have key : ∀ (g : glG E a) (Y : glL E a), glRes φ.1 x (g * (glH E a).expG Y) =
      chart φ.1 x (T ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * exp (Y : Matrix (Fin a) (Fin a) (Cinf E)))) := by
    intro g Y
    rw [hT]
    exact (chart_val φ.1 x ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) * ((glH E a).expG Y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ))).symm
  have hs : (glH E a).IsSmoothFun (glRes φ.1 x) := by
    rw [IsExpLieAlgebra.isSmoothFun_iff]
    intro g
    have e : (fun Y : glL E a => glRes φ.1 x (g * (glH E a).expG Y)) =
        chart φ.1 x ∘ fun Y : glL E a => T ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * exp (Y : Matrix (Fin a) (Fin a) (Cinf E))) :=
      funext (key g)
    rw [e]
    have h1 : ContDiff ℝ ∞ (fun Y : glL E a => T ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ).val * exp (Y : Matrix (Fin a) (Fin a) (Cinf E)))) :=
      T.contDiff.comp (contDiff_const.mul ((contDiff_exp ℝ _).comp (glL E a).subtypeL.contDiff))
    exact (φ.2 x).comp_contDiff h1 fun Y =>
      ((g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) * ((glH E a).expG Y : (Matrix (Fin a) (Fin a) (Cinf E))ˣ)).isUnit
  refine ⟨hs, fun X => funext fun g => ?_⟩
  have h2 := hasDerivAt_exp_smul_const (𝕂 := ℝ) (X : Matrix (Fin a) (Fin a) (Cinf E)) (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  have hc : HasDerivAt (fun t : ℝ => toL (((glH E a).expG (t • X) : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) : Matrix (Fin a) (Fin a) (Cinf E)))
      (toL X.1) 0 := T.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
  have h0 : (((glH E a).expG ((0 : ℝ) • X) : glG E a) : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) = 1 := by
    ext : 1
    simp
  have h3 := hasDerivAt_curve φ (x * infGL E a (g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ))
    (fun t => ((glH E a).expG (t • X) : (Matrix (Fin a) (Fin a) (Cinf E))ˣ)) (toL X.1) h0 hc
  have ef : (fun t : ℝ => glRes φ.1 x (g * (glH E a).expG (t • X))) = fun t : ℝ =>
      φ.1 (x * infGL E a (g : (Matrix (Fin a) (Fin a) (Cinf E))ˣ) *
        infGL E a ((glH E a).expG (t • X) : (Matrix (Fin a) (Fin a) (Cinf E))ˣ)) := by
    funext t
    simp only [glRes, Subgroup.coe_mul, map_mul, mul_assoc]
  have h4 := (glH E a).hasDerivAt_rightDeriv hs X g
  rw [ef] at h4
  exact h4.unique h3

end GlobalTheory.HCA

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightLieDerivativeRealEntryPolynomialFunction
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct

namespace GlobalTheory.PolyRightDeriv

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

theorem hasDerivAt_eval {σ : Type} (δ : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) (c : ℝ → σ → ℂ)
    (h : ∀ p, HasDerivAt (fun t => c t p) (MvPolynomial.eval (c 0) (δ (MvPolynomial.X p))) 0) (P : MvPolynomial σ ℂ) :
    HasDerivAt (fun t => MvPolynomial.eval (c t) P) (MvPolynomial.eval (c 0) (δ P)) 0 := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa [MvPolynomial.derivation_C] using hasDerivAt_const (0 : ℝ) a
  | add P Q hP hQ => simp only [map_add (f := _)]; exact hP.add hQ
  | mul_X P p hP =>
    have := hP.mul (h p)
    simp only [map_mul, MvPolynomial.eval_X, Derivation.leibniz, smul_eq_mul, map_add (f := _)]
    exact this.congr_deriv (by ring)

theorem hasDerivAt_entry {n : ℕ} (A X : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (A * NormedSpace.exp (t • X)) i j) ((A * X) i j) 0 := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X (0 : ℝ)
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun B => (A * B) i j
      map_add' := fun B C => by simp [mul_add]
      map_smul' := fun c B => by simp }
  have h2 := (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h2
  exact h2

theorem lieDer_polyFun (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (R : RealPoints θ V) (τ : D.what₂.Tau) (X : LieAt V τ) (P : PolyE V) :
    lieDer V (expInf θ V) (atPlace V τ X) (polyFun θ V P) = polyFun θ V (matDer τ X.1 P) := by
  classical
  funext g
  let c : ℝ → D.what₂.Tau × Fin V.rank × Fin V.rank → ℂ :=
    fun t => realEntries θ V (g * expInf θ V (t • atPlace V τ X))
  have hc : ∀ t p, c t p = (infMat D.sp.cm.sig V.gram (θ p.1) g *
      NormedSpace.exp (t • (atPlace V τ X p.1 : Matrix (Fin V.rank) (Fin V.rank) ℂ))) p.2.1 p.2.2 := fun t p => by
    simp only [c, realEntries]
    rw [R.2.2.2.1, (isExpFam_expInf R (t • atPlace V τ X)).2]
    rfl
  have h0 : c 0 = realEntries θ V g := funext fun p => by
    rw [hc, zero_smul, NormedSpace.exp_zero, mul_one]; rfl
  have h := hasDerivAt_eval (matDer τ X.1) c (fun p => by
    simp only [hc]
    convert hasDerivAt_entry (infMat D.sp.cm.sig V.gram (θ p.1) g)
      (atPlace V τ X p.1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) p.2.1 p.2.2 using 1
    rw [h0, matDer_X]
    obtain ⟨τ', i, j⟩ := p
    by_cases e : τ' = τ
    · subst e
      simp [atPlace, Matrix.mul_apply, realEntries]
    · simp [atPlace, e, Pi.single_eq_of_ne e]) P
  rw [h0] at h
  exact h.deriv

end GlobalTheory.PolyRightDeriv

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsDimLeAddMulSectionsDimCut
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory.SiuChain

theorem hdim_le_of_cls_eq_add_nsmul (k : Type) [Field k] [Infinite k] (X : Scheme.{0})
    [Algebra k Γ(X, ⊤)]
    (hX : IsProjOver (strHom k (X := X))) (G : X.Modules) [IsFiniteQC G] (B M : LB X) (hB : B.IsLB)
    (hM : M.IsLB) (t : B.Sec) (ht : Mono (cutHom G hB t)) (j : ℕ) :
    ∀ (M' : LB X) (hM' : M'.IsLB), cls M hM = cls M' hM' + j • cls B hB →
      hdim k (twist G M') 0 ≤ hdim k (twist G M) 0 := by
  induction j with
  | zero =>
    intro M' hM' h
    rw [zero_nsmul, add_zero] at h
    obtain ⟨e⟩ := nonempty_twist_iso_of_cls_eq G hM hM' h
    exact (hdim_congr k 0 e).ge
  | succ j ih =>
    intro M' hM' h
    have h1 := cls_tens hM' hB (isLB_tens hM' hB)
    have h2 := ih _ (isLB_tens hM' hB) (by rw [h1, h, succ_nsmul']; abel)
    exact ((GlobalTheory.T.sheafCohomologyDim_twist_cut_inequalities k X hX G B _ M' hB _ hM' t ht h1).2.2).trans h2

theorem hdim_le_add_mul_hdim_cut : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (F : X.Modules) [IsFiniteQC F], ∀ (B M : LB X) (hB : B.IsLB) (hM : M.IsLB) (s t : B.Sec), Mono (cutHom F hB s) → Mono (cutHom (cut F hB s) hB t) → ∀ (j : ℕ) (M' : LB X) (hM' : M'.IsLB), cls M hM = cls M' hM' + j • cls B hB → hdim k (twist F M) 0 ≤ hdim k (twist F M') 0 + j * hdim k (twist (cut F hB s) M) 0 := by
  intro k _ _ X _ hX F _ B M hB hM s t hs ht j
  induction j with
  | zero =>
    intro M' hM' h
    rw [zero_nsmul, add_zero] at h
    obtain ⟨e⟩ := nonempty_twist_iso_of_cls_eq F hM hM' h
    rw [hdim_congr k 0 e]
    omega
  | succ j ih =>
    intro M' hM' h
    have h1 := cls_tens hM' hB (isLB_tens hM' hB)
    have h0 : cls M hM = cls (tens M' B) (isLB_tens hM' hB) + j • cls B hB := by
      rw [h1, h, succ_nsmul']; abel
    have h2 := ih _ (isLB_tens hM' hB) h0
    have h3 := (GlobalTheory.T.sheafCohomologyDim_twist_cut_inequalities k X hX F B _ M' hB _ hM' s hs h1).1 0
    have h4 := hdim_le_of_cls_eq_add_nsmul k X hX (cut F hB s) B M hB hM t ht j _
      (isLB_tens hM' hB) h0
    rw [Nat.succ_mul]
    omega

end GlobalTheory.SiuChain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeedOrbKVanish
section
open MeasureTheory Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKDef
open scoped TensorProduct Classical

namespace GlobalTheory.TorusElementPower

theorem torusElt_pow_eq {k : Type} [Field k] {N : ℕ} (ϖ : kˣ) (ν : Fin N → ℤ) (m : ℕ) :
    GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ ν ^ m = GlobalTheory.GLDoubling.torusElt k (Fin N) ϖ (fun a => (m : ℤ) * ν a) := by
  unfold GlobalTheory.GLDoubling.torusElt
  rw [← map_pow]
  congr 1
  funext i
  simp [← zpow_natCast, ← _root_.zpow_mul, mul_comm]

end GlobalTheory.TorusElementPower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SerreHolomorphicSectionsHolds
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts

theorem GlobalTheory.Published.serreHolomorphicSections_holds : GlobalTheory.Published.SerreHolomorphicSections := by
  intro Y p D hs hp R B hB
  refine ⟨fun s t h => ?_, fun s => ?_⟩
  · have e : s.f = t.f := funext fun i => GlobalTheory.eq_of_ev_eq_of_smoothOfRelativeDimension Y p D hs _ _ _ fun y _ =>
      congrFun₂ (congrArg Subtype.val h) i y
    cases s; cases t; congr
  have loc (i : B.ι) (x : B.U i) : ∃ V : Y.Opens, x.1 ∈ V ∧ V ≤ B.U i ∧ ∃ c : Γ(Y, V),
      ∀ y ∈ ptsIn p (RingHom.id ℂ) V, ev p (RingHom.id ℂ) V c y = s.1 i y := by
    obtain ⟨U, hxU, hU⟩ := GlobalTheory.exists_open_isDomain_of_smooth_complex Y p D hs x
    obtain ⟨V, n, u, hx, hV, ha, h⟩ := GlobalTheory.exists_affine_boundary_functions_of_isProjOver Y p hp (U ⊓ B.U i) x ⟨hxU, x.2⟩
    have hi := hV.trans inf_le_right
    have hd := hU V (hV.trans inf_le_left) hx
    have hh := (s.2.2 i).mono (ptsIn_mono hi)
    obtain ⟨C, m, hC⟩ := GlobalTheory.continuous_section_polynomial_growth Y p hp B hB s.1 s.2.1
      (fun j => (s.2.2 j).continuousOn (isOpen_ptsIn _)) i V n u hi h
    obtain ⟨a, b, hb, e⟩ := SerreSections.exists_mul_eq_of_polynomial_growth Y p D hs R V ha hd _ hh n u C m hC
    exact ⟨V, hx, hi, GlobalTheory.exists_ev_eq_of_continuousOn_quotient Y p D hs V ha hd _ (hh.continuousOn (isOpen_ptsIn _)) a b hb e⟩
  choose V hx hV c hc using loc
  have glue (i : B.ι) : ∃ f : Γ(Y, B.U i), ∀ y ∈ ptsIn p (RingHom.id ℂ) (B.U i),
      ev p (RingHom.id ℂ) _ f y = s.1 i y := by
    obtain ⟨f, hf, -⟩ := TopCat.Sheaf.existsUnique_gluing' Y.sheaf (V i) (B.U i)
      (fun x => homOfLE (hV i x)) (fun x h => Opens.mem_iSup.2 ⟨⟨x, h⟩, hx i _⟩) (c i) fun x x' =>
        GlobalTheory.eq_of_ev_eq_of_smoothOfRelativeDimension Y p D hs (V i x ⊓ V i x') _ _ fun y hy =>
          ((ev_res inf_le_left hy _).trans (hc i x y (mem_ptsIn_inf.1 hy).1)).trans
            ((ev_res inf_le_right hy _).trans (hc i x' y (mem_ptsIn_inf.1 hy).2)).symm
    refine ⟨f, fun y hy => ?_⟩
    have hy' : y ∈ ptsIn p (RingHom.id ℂ) (V i ⟨_, mem_ptsIn.1 hy⟩) := mem_ptsIn.2 (hx i _)
    rw [← hc i _ y hy', ← hf]
    exact (ev_res _ hy' _).symm
  choose f hf using glue
  refine ⟨⟨f, fun i j => GlobalTheory.eq_of_ev_eq_of_smoothOfRelativeDimension Y p D hs _ _ _ fun y hy => ?_⟩, Subtype.ext (funext₂ fun i y => ?_)⟩
  · have h := mem_ptsIn_inf.1 hy
    refine (ev_res inf_le_left hy _).trans (Eq.trans ?_ (ev_mul _ _ _).symm)
    rw [hf i y h.1, s.2.1.1 i j y h.1 h.2, ← hf j y h.2]
    exact congrArg _ (ev_res inf_le_right hy _).symm
  · by_cases h : y ∈ ptsIn p (RingHom.id ℂ) (B.U i)
    · exact hf i y h
    · exact (ev_of_notMem h _).trans (s.2.1.2 i y h).symm

theorem GlobalTheory.AnRead.bijective_valC {F : Type} [Field F] {Y : Scheme.{0}} {p : Y ⟶ Sp F} {σ : F →+* ℂ} {D : ℕ}
    [SmoothOfRelativeDimension D p] (hp : IsProjOver p) (R : AnRead p σ D) {B : LB Y} (hB : B.IsLB) :
    Function.Bijective (R.valC B) :=
  GlobalTheory.Published.serreHolomorphicSections_holds.bijective_valC hp R hB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusElementMul
section
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.StdPar GlobalTheory.IdTorus
open GlobalTheory.Doubling (absE conjUnit)
open scoped TensorProduct

namespace GlobalTheory.IdTorus
theorem isIdTorusElt_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E} {l l' : Fin r → (AF F ⊗[F] E)ˣ} {a b : GAd σ J}
    (ha : IsIdTorusElt σ J X Y l a) (hb : IsIdTorusElt σ J X Y l' b) : IsIdTorusElt σ J X Y (l * l') (a * b) := by
  obtain ⟨ha1, ha2, ha3⟩ := ha
  obtain ⟨hb1, hb2, hb3⟩ := hb
  refine ⟨?_, ?_, fun z hz => ?_⟩
  · rw [map_mul, Units.val_mul, Matrix.mul_assoc, hb1, ← Matrix.mul_assoc, ha1, Matrix.mul_assoc, diagonal_mul_diagonal]
    exact congrArg _ (congrArg _ (funext fun k => by simp))
  · rw [map_mul, Units.val_mul, Matrix.mul_assoc, hb2, ← Matrix.mul_assoc, ha2, Matrix.mul_assoc, diagonal_mul_diagonal]
    exact congrArg _ (congrArg _ (funext fun k => by simp [map_mul, mul_inv, Units.val_mul, mul_comm]))
  · rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hb3 z hz, ha3 z hz]
end GlobalTheory.IdTorus
end

