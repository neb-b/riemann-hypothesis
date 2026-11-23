module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1197
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1209
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0986
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0968
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0955
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0873
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0546
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0690
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0919
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0916
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0704
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowDerivationChainRule.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0967
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1164
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1208
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1205
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixedOpenSubgroupGLw
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.BCT

theorem finiteDimensional_fixed_openSubgroup_GLw : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    ∀ (n : ℕ) (w : Pl E) (σ : SmIrr (GLw n w)) (U : Subgroup (GLw n w)), IsOpen (U : Set (GLw n w)) →
      FiniteDimensional ℂ (fixed σ.ρ U) := by
  intro E _ _ _ n w σ U hU
  letI := GlobalTheory.LocalData.complRel w
  haveI := GlobalTheory.LocalData.isLocalField w
  have hadm : IsAdmissible σ.ρ :=
    GlobalTheory.FourClauses.irreducibleAdmissibleGL (w.adicCompletion E) n σ.V σ.ρ σ.smooth σ.irred
  obtain ⟨ho, hc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  have hK : FiniteDimensional ℂ (fixed σ.ρ (U ⊓ GlobalTheory.LFun.KGL w (n := n))) :=
    hadm.2 _ (hU.inter ho) (hc.inter_left (U.isClosed_of_isOpen hU))
  have hle : fixed σ.ρ U ≤ fixed σ.ρ (U ⊓ GlobalTheory.LFun.KGL w (n := n)) := fun v hv h => hv ⟨h.1, h.2.1⟩
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.BCT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveCotangentGlobalSectionsGroupSche
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FramesFGP

theorem finite_projective_top {O : Type} [CommRing O] (F : (Sp O).Modules)
    (h : ∀ x : Sp O, ∃ (U : (Sp O).Opens) (n : ℕ) (s : Fin n → Γ(F, U)),
      x ∈ U ∧ GlobalTheory.VB.IsFrame s) :
    Module.Finite Γ(Sp O, ⊤) Γ(F, ⊤) ∧ Module.Projective Γ(Sp O, ⊤) Γ(F, ⊤) := by
  haveI : F.IsQuasicoherent := GlobalTheory.OmegaGlobal.isQuasicoherent_of_frames h
  choose U n e hx he using h
  have hU := isAffineOpen_top (Sp O)
  let s : Set Γ(Sp O, ⊤) := {f | ∃ x, (Sp O).basicOpen f ≤ U x}
  have hs : Ideal.span s = ⊤ := by
    rw [← hU.self_le_iSup_basicOpen_iff]
    intro y _
    obtain ⟨f, hf, hyf⟩ := hU.exists_basicOpen_le (V := U y) ⟨y, hx y⟩ (by simp)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, y, hf⟩, hyf⟩
  haveI (g : s) := hU.isLocalization_basicOpen g.1
  haveI (g : s) := GlobalTheory.QCoh.isLocalizedModule_resBasicOpen F hU g.1
  let b (g : s) : Module.Basis (Fin (n g.2.choose)) Γ(Sp O, (Sp O).basicOpen g.1)
      Γ(F, (Sp O).basicOpen g.1) := (he g.2.choose).basis g.2.choose_spec
  haveI (g : s) : Module.Free Γ(Sp O, (Sp O).basicOpen g.1) Γ(F, (Sp O).basicOpen g.1) :=
    .of_basis (b g)
  haveI (g : s) : Module.Finite Γ(Sp O, (Sp O).basicOpen g.1) Γ(F, (Sp O).basicOpen g.1) :=
    .of_basis (b g)
  haveI (g : s) : Module.Flat Γ(Sp O, ⊤) Γ(F, (Sp O).basicOpen g.1) := by
    haveI : Module.Flat Γ(Sp O, ⊤) Γ(Sp O, (Sp O).basicOpen g.1) :=
      IsLocalization.flat _ (Submonoid.powers g.1)
    exact Module.Flat.trans Γ(Sp O, ⊤) Γ(Sp O, (Sp O).basicOpen g.1) _
  haveI hfp : Module.FinitePresentation Γ(Sp O, ⊤) Γ(F, ⊤) :=
    Module.FinitePresentation.of_localizationSpan' s hs
      (Mₚ := fun g : s => Γ(F, (Sp O).basicOpen g.1))
      (Rₚ := fun g : s => Γ(Sp O, (Sp O).basicOpen g.1))
      (fun g => GlobalTheory.QCoh.resBasicOpen F g.1) fun _ => Module.finitePresentation_of_projective _ _
  haveI : Module.Flat Γ(Sp O, ⊤) Γ(F, ⊤) :=
    Module.flat_of_isLocalized_span Γ(Sp O, ⊤) Γ(F, ⊤) s hs
      (fun g : s => Γ(F, (Sp O).basicOpen g.1)) (fun g => GlobalTheory.QCoh.resBasicOpen F g.1)
      fun _ => inferInstance
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

end GlobalTheory.FramesFGP

theorem GlobalTheory.FramesFGP.finite_projective_wmod : ∀ (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A],
    (∀ x : Sp O, ∃ (U : (Sp O).Opens) (n : ℕ) (s : Fin n → Γ(GlobalTheory.LieVB.omega A, U)),
      x ∈ U ∧ GlobalTheory.VB.IsFrame s) → Module.Finite O (Wmod A) ∧ Module.Projective O (Wmod A) := by
  intro O _ A _ h
  obtain ⟨h1, h2⟩ := GlobalTheory.FramesFGP.finite_projective_top (GlobalTheory.LieVB.omega A) h
  letI : Module Γ(Sp O, ⊤) (Wmod A) := inferInstanceAs (Module Γ(Sp O, ⊤) Γ(GlobalTheory.LieVB.omega A, ⊤))
  haveI : Module.Finite Γ(Sp O, ⊤) (Wmod A) := h1
  haveI : Module.Projective Γ(Sp O, ⊤) (Wmod A) := h2
  have hb : Function.Bijective (GlobalTheory.LieVB.cst O) :=
    ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of O)).inv
  let E : O ≃+* Γ(Sp O, ⊤) := RingEquiv.ofBijective (GlobalTheory.LieVB.cst O) hb
  letI : Algebra O Γ(Sp O, ⊤) := (GlobalTheory.LieVB.cst O).toAlgebra
  haveI : IsScalarTower O Γ(Sp O, ⊤) (Wmod A) := .of_algebraMap_smul fun _ _ => rfl
  haveI : Module.Finite O Γ(Sp O, ⊤) :=
    Module.Finite.of_surjective (Algebra.linearMap O Γ(Sp O, ⊤)) hb.2
  refine ⟨Module.Finite.trans Γ(Sp O, ⊤) (Wmod A), ?_⟩
  haveI : RingHomInvPair (E.symm : Γ(Sp O, ⊤) →+* O) (E : O →+* Γ(Sp O, ⊤)) :=
    ⟨RingHom.ext E.apply_symm_apply, RingHom.ext E.symm_apply_apply⟩
  haveI : RingHomInvPair (E : O →+* Γ(Sp O, ⊤)) (E.symm : Γ(Sp O, ⊤) →+* O) := .symm _ _
  let e : Wmod A ≃ₛₗ[(E.symm : Γ(Sp O, ⊤) →+* O)] Wmod A :=
    { toFun := id
      invFun := id
      map_add' := fun _ _ => rfl
      map_smul' := fun r m => by
        change r • m = GlobalTheory.LieVB.cst O (E.symm r) • m
        congr 1
        exact (E.apply_symm_apply r).symm
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Module.Projective.of_equiv e

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialSpaceEqFockImageOfArchLaws
section
noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.RealLift.PolRangePf

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

theorem atPl_eq' (w : ι) (L : Module.End ℂ (V w)) :
    atPl w L = PiTensorProduct.mapMultilinear ℂ V V (Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w L) := rfl

theorem atPl_add' (w : ι) (L L' : Module.End ℂ (V w)) : atPl w (L + L') = atPl w L + atPl w L' := by
  simp only [atPl_eq', MultilinearMap.map_update_add]

theorem atPl_smul' (w : ι) (c : ℂ) (L : Module.End ℂ (V w)) : atPl w (c • L) = c • atPl w L := by
  simp only [atPl_eq', MultilinearMap.map_update_smul, RingHom.id_apply]

theorem atPl_zero' (w : ι) : atPl w (0 : Module.End ℂ (V w)) = 0 := by
  simp only [atPl_eq', MultilinearMap.map_update_zero]

theorem atPl_tprod (w : ι) (L : Module.End ℂ (V w)) (f : ∀ i, V i) :
    atPl w L (PiTensorProduct.tprod ℂ f) = PiTensorProduct.tprod ℂ (Function.update f w (L (f w))) := by
  rw [atPl, PiTensorProduct.map_tprod]
  congr 1
  funext i
  by_cases h : i = w
  · subst h; simp
  · simp [Function.update_of_ne h]

end Tensor

theorem heisOp_zero {P Q R S : ℕ} : heisOp (P := P) (Q := Q) (R := R) (S := S) 0 = 0 := by
  simp [heisOp]

theorem Jm_transpose' (p q : ℕ) : (Jm p q)ᵀ = Jm p q := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_transpose]

theorem exists_at_piInf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (z : InfinitePlace F → ℂ) : ∃ a : AE F E, At (evI F) a ∧ ∀ w, piInf (τ w) a = z w := GlobalTheory.T.exists_archimedean_adele_CM_prescribed_embedding_values hcm τ z

theorem exists_mat_at {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    {m k : Type} (z : InfinitePlace F → Matrix m k ℂ) :
    ∃ u : Matrix m k (AE F E), At (evI F) u ∧ ∀ w, u.map (piInf (τ w)) = z w := by
  choose a ha using fun i j => exists_at_piInf hcm τ (fun w => z w i j)
  refine ⟨Matrix.of a, fun x hx => ?_, fun w => ?_⟩
  · ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.zero_apply]
    exact (ha i j).1 x hx
  · ext i j
    simp [(ha i j).2 w]

theorem mulX_mem_span {P Q R S : ℕ} (l : Ln P Q R S) :
    LinearMap.mulLeft ℂ (MvPolynomial.X l : Formalism.BasicNotions.TH.Pol P Q R S) ∈
      Submodule.span ℂ (Set.range (heisOp (P := P) (Q := Q) (R := R) (S := S))) := GlobalTheory.T.fockVariableMultiplication_mem_span_heisenbergOperators l

theorem tens_top {ι σ : Type} [Fintype ι] [DecidableEq ι] (N : Submodule ℂ (⨂[ℂ] _ : ι, MvPolynomial σ ℂ))
    (h1 : PiTensorProduct.tprod ℂ (fun _ => (1 : MvPolynomial σ ℂ)) ∈ N)
    (hN : ∀ w l, ∀ T ∈ N, atPl w (LinearMap.mulLeft ℂ (MvPolynomial.X l : MvPolynomial σ ℂ)) T ∈ N) : N = ⊤ := _root_.GlobalTheory.RealLift.tensor_submodule_eq_top N h1 hN

theorem tens_top_heis {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ}
    (N : Submodule ℂ (⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S))
    (h1 : PiTensorProduct.tprod ℂ (fun _ => (1 : Formalism.BasicNotions.TH.Pol P Q R S)) ∈ N)
    (hN : ∀ w c, ∀ T ∈ N, atPl w (heisOp (P := P) (Q := Q) (R := R) (S := S) c) T ∈ N) : N = ⊤ := by
  refine tens_top N h1 fun w l T hT => ?_
  let K : Submodule ℂ (Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S)) :=
    { carrier := {L | ∀ T ∈ N, atPl w L T ∈ N}
      add_mem' := fun {a b} ha hb T hT => by
        rw [atPl_add', LinearMap.add_apply]; exact N.add_mem (ha T hT) (hb T hT)
      zero_mem' := fun T _ => by rw [atPl_zero']; exact N.zero_mem
      smul_mem' := fun c a ha T hT => by rw [atPl_smul', LinearMap.smul_apply]; exact N.smul_mem c (ha T hT) }
  have hK : Submodule.span ℂ (Set.range (heisOp (P := P) (Q := Q) (R := R) (S := S))) ≤ K :=
    Submodule.span_le.2 (by rintro _ ⟨c, rfl⟩; exact hN w c)
  exact hK (mulX_mem_span l) T hT

theorem heisOp_twist_one {P Q R S : ℕ} (c : Matrix (Ix P Q) (Ix R S) ℂ) :
    heisOp (Complex.I • (Jm P Q * c * Jm R S)) 1 = Complex.I • heisOp c 1 := _root_.GlobalTheory.RealLift.heisOp_twist_one c

theorem sumPl_twist_one {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ℕ} (c : ι → Matrix (Ix P Q) (Ix R S) ℂ) :
    sumPl (fun w => heisOp (Complex.I • (Jm P Q * c w * Jm R S))) (PiTensorProduct.tprod ℂ (fun _ => (1 : Formalism.BasicNotions.TH.Pol P Q R S)))
      = Complex.I • sumPl (fun w => heisOp (c w)) (PiTensorProduct.tprod ℂ (fun _ => (1 : Formalism.BasicNotions.TH.Pol P Q R S))) := by
  simp only [sumPl, LinearMap.sum_apply, Finset.smul_sum, atPl_tprod, heisOp_twist_one]
  refine Finset.sum_congr rfl fun w _ => ?_
  exact (PiTensorProduct.tprod ℂ).map_update_smul _ w Complex.I _

theorem polRange_of (hL : ActsLaws) (_hD : DerEx) (hV : VacLine) : PolRange := by
  intro F E _ _ _ _ _ σ n d P Q R S X W M ψ τ A C Φ hcm hψ hfr hθX hθW hΦ
  have hz : ∀ (u : Matrix (Fin n) (Fin d) (AE F E)) (t : ℝ), M.co.rho ψ (realAd F t • u) 0 = 0 := by
    intro u t; funext x; simp [Darboux.rho, schr]
  have toD : ∀ u (f f₁ : SInf F (Fin n × Fin d)), SD (fun t => M.co.rho ψ (realAd F t • u)) f f₁ →
      ActsD (evI F) (M.heisLine ψ u) f f₁ := fun u f f₁ h => (hL F (Fin n × Fin d) f f₁ f₁).1 _ (hz u) h
  have uniq : ∀ u (f f₁ f₂ : SInf F (Fin n × Fin d)), ActsD (evI F) (M.heisLine ψ u) f f₁ →
      ActsD (evI F) (M.heisLine ψ u) f f₂ → f₁ = f₂ := fun u f f₁ f₂ h1 h2 => (hL F _ f f₁ f₂).2.2.1 _ h1 h2
  choose A' hA' using fun w => (hfr.2.1 w).2
  choose C' hC' using fun w => (hfr.2.2 w).2
  have decomp : ∀ (u : Matrix (Fin n) (Fin d) (AE F E)) w,
      u.map (piInf (τ w)) = A w * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * (C w)ᵀ := by
    intro u w
    rw [show A w * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * (C w)ᵀ =
        (A w * A' w) * u.map (piInf (τ w)) * ((C w) * (C' w))ᵀ by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc], hA', hC']
    simp
  have der : ∀ u, At (evI F) u → ∀ c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ,
      (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) → ∀ T,
      ActsD (evI F) (M.heisLine ψ u) (Φ T) (Φ (sumPl (fun w => heisOp (c w)) T)) :=
    fun u hu c hc T => toD _ _ _ (hΦ.2 u hu c hc T)
  have tw : ∀ w (c : Matrix (Ix P Q) (Ix R S) ℂ) (e : ℂ),
      A w * (e • (Jm P Q * c * Jm R S)) * (C w)ᵀ = e • (X.θ w * (A w * c * (C w)ᵀ) * (W.θ w)ᵀ) := by
    intro w c e
    have h2 : (C w)ᵀ * (W.θ w)ᵀ = Jm R S * (C w)ᵀ := by
      rw [← Matrix.transpose_mul, hθW w, Matrix.transpose_mul, Jm_transpose']
    calc A w * (e • (Jm P Q * c * Jm R S)) * (C w)ᵀ = e • ((A w * Jm P Q) * c * (Jm R S * (C w)ᵀ)) := by
          simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = _ := by rw [← hθX w, ← h2]; simp only [Matrix.mul_assoc]
  have gauss1 : M.IsGauss ψ τ (Φ (PiTensorProduct.tprod ℂ (fun _ => (1 : Formalism.BasicNotions.TH.Pol P Q R S)))) := by
    refine ⟨fun _ => 1, fun u u' hu hu' hrel f f' hf hf' => ?_⟩
    have hc : ∀ w, u.map (piInf (τ w)) = A w * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * (C w)ᵀ := decomp u
    have hc' : ∀ w, u'.map (piInf (τ w)) =
        A w * (Complex.I • (Jm P Q * (A' w * u.map (piInf (τ w)) * (C' w)ᵀ) * Jm R S)) * (C w)ᵀ := by
      intro w; rw [hrel w, tw, ← hc w]; simp
    rw [uniq u _ _ _ hf (der u hu _ hc _), uniq u' _ _ _ hf' (der u' hu' _ hc' _), sumPl_twist_one, map_smul]
  have gauss_mem : ∀ f₀, M.IsGauss ψ τ f₀ → f₀ ∈ M.Pol ψ τ := fun f₀ h => by
    unfold Model.Pol
    exact Submodule.mem_sInf.2 fun N hN => hN.1 f₀ h
  have pol_der : ∀ u, At (evI F) u → ∀ f ∈ M.Pol ψ τ, ∀ f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ → f₁ ∈ M.Pol ψ τ := by
    intro u hu f hf f₁ h1
    unfold Model.Pol at hf ⊢
    exact Submodule.mem_sInf.2 fun N hN => hN.2 u hu f (Submodule.mem_sInf.1 hf N hN) f₁ h1
  apply le_antisymm
  · rintro _ ⟨T, rfl⟩
    have htop : (M.Pol ψ τ).comap Φ = ⊤ := by
      refine tens_top_heis _ (gauss_mem _ gauss1) fun w c T hT => ?_
      obtain ⟨u, hu, hu'⟩ := exists_mat_at hcm τ
        (fun w' => A w' * Function.update (0 : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) w c w' * (C w')ᵀ)
      have hs : sumPl (fun w' => heisOp (Function.update (0 : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) w c w')) T =
          atPl w (heisOp c) T := by
        rw [sumPl, LinearMap.sum_apply, Finset.sum_eq_single w]
        · simp
        · intro b _ hb; simp [Function.update_of_ne hb, heisOp_zero, atPl_zero']
        · simp
      have := pol_der u hu _ hT _ (der u hu _ hu' T)
      rwa [hs] at this
    have : T ∈ (M.Pol ψ τ).comap Φ := htop ▸ Submodule.mem_top
    exact this
  · unfold Model.Pol
    refine sInf_le ⟨fun f₀ hf₀ => ?_, fun u hu f hf f₁ h1 => ?_⟩
    · obtain ⟨ε, hε⟩ := hf₀
      obtain ⟨z, hz⟩ := hV F E σ (Fin n) (Fin d) (Fin n × Fin d) P Q R S ψ τ (incM F X.J) (incM F W.J) M.co 1
        Complex.I A C Φ hcm hψ hfr hΦ f₀ ε (fun u u' hu hu' c hc hc' f f' hf hf' =>
          hε u u' hu hu' (fun w => by rw [hc' w, tw, ← hc w]) f f' (toD _ _ _ hf) (toD _ _ _ hf'))
      exact ⟨z • PiTensorProduct.tprod ℂ (fun _ => (1 : Formalism.BasicNotions.TH.Pol P Q R S)), by rw [map_smul, hz]⟩
    · obtain ⟨T, rfl⟩ := hf
      exact ⟨_, (uniq u _ _ _ (der u hu _ (decomp u) T) h1)⟩

end GlobalTheory.RealLift.PolRangePf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormExists
section
noncomputable section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair

namespace GlobalTheory.CharPair

theorem L_actR (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (i j : Ix P Q) (G : Mdl P Q) :
    fockAct1 P Q R 0 (Eab i j) (embR P Q R h k G) = embR P Q R h k (opR P Q R k i j G) := by
  rcases i with a | b <;> rcases j with a' | b'
  · exact _root_.GlobalTheory.CharPair.FirstBlock.act_first_block P Q R h k a a' G
  · exact _root_.GlobalTheory.CharPair.fockAct1_Eab_inl_inr_embR P Q R h k a b' G
  · exact _root_.GlobalTheory.CharPair.fockAct1_embR_inr_inl P Q R h k a' b G
  · exact _root_.GlobalTheory.CharPair.fockAct1_inr_inr_embR P Q R h k b b' G

theorem mat_eq_sum {P Q : ℕ} (Z : Mat P Q) : Z = ∑ i, ∑ j, Z i j • Eab i j := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
  simp [Eab, Matrix.smul_single]

theorem actR_full (P Q R : ℕ) (h : P ≤ R) (k : ℕ) (Z : Mat P Q) (G : Mdl P Q) :
    fockAct1 P Q R 0 Z (embR P Q R h k G) = embR P Q R h k (actR P Q R k Z G) := by
  conv_lhs => rw [mat_eq_sum Z]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, L_actR, actR_apply]

end GlobalTheory.CharPair

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyBundleIsNefOfNonnegWeights
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory.HSNef.FSNef

section Sec

variable {X : Scheme.{0}} [IsIntegral X]


open Classical in
def fnOnOpen (U : X.Opens) (g : X.functionField) (hg : ∀ x ∈ U, RegAt x g) : Γ(X, U) :=
  if h : genericPoint X ∈ U then (exists_fnOf_eq h hg).choose else 0

theorem fnOf_fnOnOpen {U : X.Opens} {g : X.functionField} (hg : ∀ x ∈ U, RegAt x g) (h : genericPoint X ∈ U) :
    fnOf U h (fnOnOpen U g hg) = g := by
  classical
  rw [fnOnOpen, dite_eq_left h]
  exact (exists_fnOf_eq h hg).choose_spec

def secOfRat (B : LB X) (ρ : B.ι → X.functionFieldˣ) (hρ : IsRatSec B ρ) (g : X.functionField)
    (hg : ∀ c, ∀ x ∈ B.U c, RegAt x (g * ρ c)) : B.Sec where
  f c := fnOnOpen (B.U c) _ (hg c)
  compat i j := fn_ext fun h => by
    change fnOf _ h (resG X inf_le_left _) =
      fnOf _ h ((B.g i j : Γ(X, B.U i ⊓ B.U j)) * resG X inf_le_right _)
    rw [map_mul, fnOf_resG, fnOf_resG, fnOf_fnOnOpen, fnOf_fnOnOpen, hρ i j h]
    ring

theorem fnOf_secOfRat {B : LB X} {ρ : B.ι → X.functionFieldˣ} (hρ : IsRatSec B ρ) {g : X.functionField}
    (hg : ∀ c, ∀ x ∈ B.U c, RegAt x (g * ρ c)) (c : B.ι) (h : genericPoint X ∈ B.U c) :
    fnOf _ h ((secOfRat B ρ hρ g hg).f c) = g * ρ c :=
  fnOf_fnOnOpen (hg c) h

end Sec

theorem isNef_of_isFS : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k)
    (D : ℕ), IsArithVar p D → ∀ (M : HermLB p) (J : Type) [Fintype J] (f : J → X.functionField) (w : J → ℝ),
    IsFS M f w → (∀ j, 0 ≤ w j) → M.IsNef D := by
  intro hA k _ X _ p D hX M J _ f w hFS hw
  have hsemi := _root_.GlobalTheory.HSNef.semiPos_of_isFS k X p D M J f w hFS
  obtain ⟨ρ, hρ, hreg, hφ⟩ := hFS
  let s : J → M.B.Sec := fun j => secOfRat M.B ρ hρ (f j) fun c x hx => (hreg x c hx).1 j
  have hs : ∀ j c (h : genericPoint X ∈ M.B.U c), fnOf _ h ((s j).f c) = f j * ρ c :=
    fun j c h => fnOf_secOfRat hρ _ c h
  let e := Fintype.equivFin J
  refine _root_.GlobalTheory.GenNef.isNef_of_gen_small hA k X p D hX M (Fintype.card J) (fun i => s (e.symm i)) hsemi (fun i => ?_) (fun x => ?_)
  · intro σ y
    have hy : y ∈ ptsIn p σ (M.B.U (pick (M.φ σ).isLB y)) := mem_pick _ y
    have hg : genericPoint X ∈ M.B.U (pick (M.φ σ).isLB y) := gen_mem (mem_ptsIn.1 hy)
    have hval : ∀ l, secVal p σ (s l) (pick (M.φ σ).isLB y) y =
        ratVal (f l * (ρ (pick (M.φ σ).isLB y) : X.functionField)) y := fun l => by
      rw [secVal_apply, ← ratVal_fnOf hy hg, hs]
    rw [Weight.nsq, hval, hφ σ y _ hy]
    obtain ⟨l, hl⟩ := (hreg _ _ (mem_ptsIn.1 hy)).2
    have hnn : ∀ m ∈ Finset.univ, 0 ≤ ‖ratVal (f m * (ρ (pick (M.φ σ).isLB y) : X.functionField)) y‖ ^ 2 * Real.exp (2 * w m) :=
      fun m _ => by positivity
    have hpos : 0 < ∑ m, ‖ratVal (f m * (ρ (pick (M.φ σ).isLB y) : X.functionField)) y‖ ^ 2 * Real.exp (2 * w m) :=
      lt_of_lt_of_le (mul_pos (pow_pos (norm_pos_iff.2 (ratVal_ne_zero hl)) 2) (Real.exp_pos _))
        (Finset.single_le_sum hnn (Finset.mem_univ l))
    rw [Real.exp_neg, Real.exp_log hpos, ← div_eq_mul_inv, div_le_one hpos]
    refine le_trans ?_ (Finset.single_le_sum hnn (Finset.mem_univ (e.symm i)))
    exact le_mul_of_one_le_right (by positivity) (Real.one_le_exp (by linarith [hw (e.symm i)]))
  · obtain ⟨c, hc⟩ := exists_chart M.isLB x
    obtain ⟨j, hj⟩ := (hreg x c hc).2
    refine ⟨e j, ?_⟩
    rw [e.symm_apply_apply, mem_nonzeroLocus_iff _ c hc, ← unitAt_fnOf_iff hc (gen_mem hc), hs]
    exact hj

end GlobalTheory.HSNef.FSNef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.H1GrowthNoSectionsNefStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.h1_dim_bound_of_no_sections_nonneg_interNum : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (L : LB X), L.IsLB → ∀ (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d + 1 : ℕ) → (∀ m : ℕ, 1 ≤ m → hdim k (twist F (lbPow L m)) 0 = 0) → 0 ≤ interNum k F (fun _ : Fin (d + 1) => L) → (∀ i, 2 ≤ i → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) i ≤ C * ((d + 1) * (m + 1) ^ d))) → (∃ C : ℕ, ∀ m : ℕ, hdim k (twist F (lbPow L m)) 1 ≤ C * ((d + 1) * (m + 1) ^ d)) := by
  first | exact @GlobalTheory.noSection_H1_bound_riemann_roch | exact GlobalTheory.noSection_H1_bound_riemann_roch | (intros; apply GlobalTheory.noSection_H1_bound_riemann_roch <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharactersRestrictionEta
section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.WeilExGen

theorem exists_isWeil : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → W.IsSkew σ B r' s' → ∀ M : Model σ X W, M.IsGood B.ψ →
    ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → ∃ om, M.IsWeil B.ψ χX χW om :=
  fun h => h.weilRepresentationExists

end GlobalTheory.WeilExGen
end

