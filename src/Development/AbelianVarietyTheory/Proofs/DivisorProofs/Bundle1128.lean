module

public import Mathlib
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1091
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelCOfInnerProductFormula
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1123
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1121
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsFactorialMulEulerCharTwistPowSubLe
section
set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist

namespace GlobalTheory

theorem abs_factorial_mul_chi_twist_lbPow_sub_le : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k (X := X)) → ∀ (d : ℕ) (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) → ∀ L : LB X, L.IsLB → ∃ C : ℕ, ∀ m : ℕ, |(d.factorial : ℤ) * chi k (twist F (lbPow L m)) - interNum k F (fun _ : Fin d => L) * (m : ℤ) ^ d| ≤ C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) := by
  intro k _ _ X _ hproj d F _ hsupp L hL
  have hv : DiffVanish (d + 1) (chiPic k F) :=
    diffVanish_chiPic_of_isProjOver (algebraMap_eq_strHom k X) F hproj hsupp
  obtain ⟨p, hpdeg, hpeval, hpcoeff⟩ := hv.exists_polynomial_int ℚ (cls L hL) 0
  obtain ⟨C, hC⟩ := abs_factorial_mul_eval_sub_top_le d p hpdeg
  refine ⟨C, fun m => ?_⟩
  have hmd : multiDiff (fun _ : Fin d => cls L hL) (chiPic k F) 0 =
      interNum k F (fun _ : Fin d => L) :=
    hv.multiDiff_chiPic (L := fun _ : Fin d => L) (by simp) (fun _ => hL) 0
  have hchi : chi k (twist F (lbPow L m)) = chiPic k F ((m : ℤ) • cls L hL) := by
    rw [← twistZ_natCast]
    exact chi_twistZ k F hL (m : ℤ)
  have heval : p.eval (m : ℚ) = (chi k (twist F (lbPow L m)) : ℚ) := by
    have e := hpeval (m : ℤ)
    rw [zero_add, ← hchi, Int.cast_natCast] at e
    exact e
  have hfac : (d.factorial : ℚ) * p.coeff d = (interNum k F (fun _ : Fin d => L) : ℚ) := by
    rw [hpcoeff, hmd, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast d.factorial_ne_zero), one_mul]
  have h := hC m
  rw [heval, hfac] at h
  have h' : ((|(d.factorial : ℤ) * chi k (twist F (lbPow L m)) -
      interNum k F (fun _ : Fin d => L) * (m : ℤ) ^ d| : ℤ) : ℚ) ≤
      ((C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) : ℤ) : ℚ) := by
    push_cast
    exact h
  exact_mod_cast h'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfBlockDetIntegralGLInvariantStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absHalf_blockDet_integralGL_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (m k : GLw a w × GLw b w),
    k.1 ∈ GlobalTheory.LFun.KGL w (n := a) → k.2 ∈ GlobalTheory.LFun.KGL w (n := b) →
    absHalf w ((k * m).1.val.det ^ b / (k * m).2.val.det ^ a) = absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) ∧
      absHalf w ((m * k).1.val.det ^ b / (m * k).2.val.det ^ a) = absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) := by
  first | exact @GlobalTheory.BCT.absHalf_blockDet_KGL_invariant | exact GlobalTheory.BCT.absHalf_blockDet_KGL_invariant | (intros; apply GlobalTheory.BCT.absHalf_blockDet_KGL_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedFrameEventuallyNearComplexPointStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adaptedFrame_eventually_near_complexPoint : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) {y : CxPts X.str σ} {A : Mat (fun _ : Unit => m) X.Fn}, A ∈ E.S (under y) → ∀ᶠ z in 𝓝 y, A ∈ E.S (under z) := by
  first | exact @GlobalTheory.GoodTop.frame_eventually | exact GlobalTheory.GoodTop.frame_eventually | (intros; apply GlobalTheory.GoodTop.frame_eventually <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddGroupFGLineBundleSectionsArithmeticVariety
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

namespace GlobalTheory

theorem addGroupFG_sec_of_isArithVar : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ B : LB X, B.IsLB → AddGroup.FG B.Sec := by
  intro k _ X _ p D h B hB
  letI : Algebra k Γ(X, ⊤) :=
    ((Scheme.Hom.appTop p).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).toAlgebra
  have hf : ∀ r : k, algebraMap k Γ(X, ⊤) r =
      (Scheme.Hom.appTop p) ((Scheme.ΓSpecIso (CommRingCat.of k)).inv r) := fun _ => rfl
  haveI := h.finite
  haveI : IsNoetherianRing k := isNoetherian_of_tower ℤ inferInstance
  have hfin : Module.Finite k (coh (twist (QCoh.structureModule X) B) 0) :=
    finite_coh_twist_of_isProjOver hf (QCoh.structureModule X) h.isProjOver hB 0
  haveI : Module.Finite ℤ (coh (twist (QCoh.structureModule X) B) 0) := Module.Finite.trans k _
  have hfg : AddGroup.FG (coh (twist (QCoh.structureModule X) B) 0) :=
    Module.Finite.iff_addGroup_fg.mp inferInstance
  exact AddGroup.fg_of_surjective (f := (cohZeroTwistEquiv B).toAddEquiv.toAddMonoidHom)
    (cohZeroTwistEquiv B).toAddEquiv.surjective

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLiftScalarOfInnerProductFormulaBis
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicLift_scalar_of_innerProductFormula : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), LiftIsCuspC R F → SourceLevelLawC R F → InnerProductFormulaC R F → FockCoefficientC R F → DeltaNorm D → FiniteZetaC R F → LevelIndexNormC R F → MassLower D → FormalDegreeUpperC R F → AdelC R F := by
  first | exact @GlobalTheory.LowRow.adelC_of_innerProductFormula | exact GlobalTheory.LowRow.adelC_of_innerProductFormula | (intros; apply GlobalTheory.LowRow.adelC_of_innerProductFormula <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AemeasurableChartOfLocallyContinuousDensityStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aemeasurable_chart_of_locally_continuous_density : ∀ {n : ℕ} {Y : Type} [TopologicalSpace Y] (e : OpenPartialHomeomorph Y (V n)) {S : Set Y} {d : Y → ℝ}, IsOpen S → (∀ y ∈ S, y ∈ e.source → ∃ g : V n → ℝ, ContinuousAt g (e y) ∧ ∀ᶠ z in 𝓝 y, d z = g (e z)) → AEMeasurable (fun v => d (e.symm v)) (volume.restrict (e.target ∩ e.symm ⁻¹' S)) := by
  first | exact @GlobalTheory.GoodTop.aemeasurable_chart_of_locally_continuous | exact GlobalTheory.GoodTop.aemeasurable_chart_of_locally_continuous | (intros; apply GlobalTheory.GoodTop.aemeasurable_chart_of_locally_continuous <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicIndependentEtaleTowerCoordinates
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.FieldPair

theorem etTower_coords_algebraicIndependent {K L : Type} [Field K] [Field L] (cK : ℂ →+* K)
    (cL : ℂ →+* L) (n r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R) :
    IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) →
    Function.Injective (MvPolynomial.eval₂Hom ι τ) →
    (letI := cL.toAlgebra; AlgebraicIndependent ℂ
      (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))) := by
  intro h hx hinj
  letI := cL.toAlgebra
  let c0 : ℂ →+* R := cK.codRestrict R h.base.const_mem
  let φ : MvPolynomial (Fin n) ℂ →+* R := MvPolynomial.eval₂Hom c0 x
  have hφinj : Function.Injective φ := by
    have hxK : Function.Injective (MvPolynomial.eval₂Hom cK (fun i => (x i : K))) := by
      letI := cK.toAlgebra
      have h1 := hx.1
      rw [algebraicIndependent_iff_injective_aeval] at h1
      exact h1
    have hcomp : R.subtype.comp φ = MvPolynomial.eval₂Hom cK (fun i => (x i : K)) := by
      ext <;> simp [φ, c0]
    intro a b e
    apply hxK
    rw [← hcomp, RingHom.comp_apply, RingHom.comp_apply, e]
  have key : (T.subtype.comp ((MvPolynomial.eval₂Hom ι τ).comp ((MvPolynomial.map φ).comp
        (MvPolynomial.sumAlgEquiv ℂ (Fin r) (Fin n)).toRingEquiv.toRingHom)))
        = (MvPolynomial.aeval (Sum.elim (fun i => (τ i : L)) (fun i => (ι (x i) : L)))).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      have := h.const a
      simp [φ, c0, MvPolynomial.sumAlgEquiv_C_inl]
      exact this
    · rintro (i | j) <;> simp [φ, MvPolynomial.sumAlgEquiv_X_inl, MvPolynomial.sumAlgEquiv_X_inr]
  have hy : Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)) ∘ finSumFinEquiv
      = Sum.elim (fun i => (τ i : L)) (fun i => (ι (x i) : L)) := by
    ext (i | j) <;> simp
  rw [← algebraicIndependent_equiv finSumFinEquiv, hy, algebraicIndependent_iff_injective_aeval,
    injective_iff_map_eq_zero]
  intro P hP
  have hP' : T.subtype.comp ((MvPolynomial.eval₂Hom ι τ).comp ((MvPolynomial.map φ).comp
        (MvPolynomial.sumAlgEquiv ℂ (Fin r) (Fin n)).toRingEquiv.toRingHom)) P = 0 := by
    rw [key]; exact hP
  have h1 : MvPolynomial.eval₂Hom ι τ (MvPolynomial.map φ (MvPolynomial.sumAlgEquiv ℂ (Fin r) (Fin n) P)) = 0 :=
    Subtype.ext hP'
  have h2 := (injective_iff_map_eq_zero _).1 hinj _ h1
  have h3 := (injective_iff_map_eq_zero _).1 (MvPolynomial.map_injective φ hφinj) _ h2
  exact (MvPolynomial.sumAlgEquiv ℂ (Fin r) (Fin n)).map_eq_zero_iff.1 h3

end GlobalTheory.FieldPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiDiagonalEpsilonGramMulVec
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiGrid.SumDual

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem sum_eq_dot {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    ∑ i, ∑ j, star (x i) * G i j * y j = star x ⬝ᵥ G *ᵥ y := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]

omit [NumberField E] [StarRing E] in
theorem antiDiagonalEpsilonGram_mulVec {c : ℕ} (ε : E) (u : Fin c → E) (p : Fin c) :
    (antiDiagonalSignGramMatrix c ε *ᵥ u) p = (if p = p.rev then ε else 1) * u p.rev := by
  simp only [mulVec, dotProduct]
  rw [Finset.sum_eq_single p.rev]
  · have := p.2
    simp only [antiDiagonalSignGramMatrix, Fin.val_rev]
    rw [if_pos (by omega)]
  · intro q _ hq
    have := p.2
    simp only [antiDiagonalSignGramMatrix]
    rw [if_neg, zero_mul]
    intro h
    exact hq (Fin.ext (by rw [Fin.val_rev]; omega))
  · intro h; exact absurd (Finset.mem_univ _) h

theorem gram_herm (S : HSpace E) : S.gramᴴ = S.gram := by
  ext i j
  exact S.herm.eq _ _

theorem hT_eq (S : HSpace E) (x y : S.V) :
    S.hT x y = star (S.frame.equivFun x) ⬝ᵥ S.gram *ᵥ S.frame.equivFun y := by
  rw [← sum_eq_dot]
  conv_lhs => rw [← S.frame.sum_repr x, ← S.frame.sum_repr y]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.sum_apply, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp only [RingHom.id_apply, Module.Basis.equivFun_apply, HSpace.gram]
  ring

theorem gram_inj (S : HSpace E) (y : Fin S.rank → E) (h : S.gram *ᵥ y = 0) : y = 0 := by
  obtain ⟨y, rfl⟩ := S.frame.equivFun.surjective y
  rw [S.nondeg.2 y fun x => by rw [hT_eq, h, dotProduct_zero], map_zero]

theorem gram_isom (A B : HSpace E) (ι : A.V →ₗ[E] B.V) (h : HSpace.IsIsomEmb A B ι) :
    (LinearMap.toMatrix A.frame B.frame ι)ᴴ * B.gram * LinearMap.toMatrix A.frame B.frame ι = A.gram := by
  ext i j
  rw [HSpace.gram, ← h, hT_eq, Matrix.mul_assoc]
  simp only [Matrix.mul_apply, dotProduct, mulVec, conjTranspose_apply, LinearMap.toMatrix_apply, Pi.star_apply,
    Module.Basis.equivFun_apply]

theorem selfDual_sum {n k c : ℕ} (hs : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (star x))
    (G : Matrix (Fin n) (Fin n) E) (J : Matrix (Fin k) (Fin k) E) (M : Matrix (Fin n) (Fin k) E)
    (a : Matrix (Fin n) (Fin c) E) (ε : E) (hε : ε = 1 ∨ ε = -1) (hG : Gᴴ = G) (hJ : ∀ y, J *ᵥ y = 0 → y = 0)
    (h1 : Mᴴ * G * M = J) (h2 : Mᴴ * G * a = 0) (h3 : aᴴ * G * a = antiDiagonalSignGramMatrix c ε) (hr : k + c = n)
    (Λ : Submodule (𝓞 E) (Fin k → E)) (𝔟 : Fin c → FractionalIdeal (𝓞 E)⁰ E)
    (hΛ : Submodule.IsLattice E Λ)
    (hΛd : ∀ y, y ∈ Λ ↔ ∀ x ∈ Λ, ∃ b : 𝓞 E, (b : E) = ∑ i, ∑ j, star (x i) * J i j * y j)
    (hb : ∀ p, 𝔟 p ≠ 0) (hd : ∀ p x, x ∈ 𝔟 p.rev ↔ star x ∈ (𝔟 p)⁻¹)
    (L : Submodule (𝓞 E) (Fin n → E))
    (hL : ∀ x, x ∈ L ↔ ∃ y ∈ Λ, ∃ u : Fin c → E, (∀ p, u p ∈ 𝔟 p) ∧ x = M *ᵥ y + a *ᵥ u) :
    Submodule.IsLattice E L ∧
      ∀ y, y ∈ L ↔ ∀ x ∈ L, ∃ b : 𝓞 E, (b : E) = ∑ i, ∑ j, star (x i) * G i j * y j := by
  classical
  have h2' : aᴴ * G * M = 0 := by
    have := congrArg conjTranspose h2
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hG, conjTranspose_zero,
      ← Matrix.mul_assoc] at this
  have eM : ∀ y u, Mᴴ *ᵥ G *ᵥ (M *ᵥ y + a *ᵥ u) = J *ᵥ y := fun y u => by
    simp only [mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc, h1, h2, zero_mulVec, add_zero]
  have ea : ∀ y u, aᴴ *ᵥ G *ᵥ (M *ᵥ y + a *ᵥ u) = antiDiagonalSignGramMatrix c ε *ᵥ u := fun y u => by
    simp only [mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc, h2', h3, zero_mulVec, zero_add]
  have key : ∀ x v y u, ∑ i, ∑ j, star ((M *ᵥ x + a *ᵥ v) i) * G i j * (M *ᵥ y + a *ᵥ u) j =
      (∑ i, ∑ j, star (x i) * J i j * y j) + ∑ p, (if p = p.rev then ε else 1) * (star (v p) * u p.rev) := by
    intro x v y u
    rw [sum_eq_dot, sum_eq_dot, star_add, add_dotProduct, star_mulVec, star_mulVec, ← dotProduct_mulVec,
      ← dotProduct_mulVec, eM, ea]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [antiDiagonalEpsilonGram_mulVec, Pi.star_apply]; ring
  have hsg : ∀ p : Fin c, ∃ e : 𝓞 E, (e : E) = (if p = p.rev then ε else 1) ∧ e * e = 1 := fun p => by
    split_ifs
    · rcases hε with rfl | rfl
      · exact ⟨1, rfl, by simp⟩
      · exact ⟨-1, by simp, by simp⟩
    · exact ⟨1, rfl, by simp⟩
  have hst : ∀ z : E, (∃ b : 𝓞 E, (b : E) = z) → ∃ b : 𝓞 E, (b : E) = star z := by
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨star (b : E), hs _ b.isIntegral_coe⟩, rfl⟩
  let f : ((Fin k → E) × (Fin c → E)) →ₗ[E] (Fin n → E) := M.mulVecLin.coprod a.mulVecLin
  have hf : ∀ y u, f (y, u) = M *ᵥ y + a *ᵥ u := fun _ _ => rfl
  have finj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 ?_
    rintro ⟨y, u⟩ h
    rw [hf] at h
    have e1 := eM y u
    have e2 := ea y u
    rw [h, mulVec_zero, mulVec_zero] at e1 e2
    refine Prod.ext (hJ y e1.symm) (funext fun p => ?_)
    have e3 := congrFun e2 p.rev
    obtain ⟨e, he, hee⟩ := hsg p.rev
    rw [antiDiagonalEpsilonGram_mulVec, ← he, Fin.rev_rev] at e3
    have he0 : (e : E) ≠ 0 := by
      intro h0
      have : e = 0 := by exact_mod_cast h0
      rw [this] at hee; simp at hee
    exact (mul_eq_zero.1 e3.symm).resolve_left he0
  have fsur : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hr])).1 finj
  refine ⟨⟨?_, ?_⟩, fun y' => ⟨?_, fun h => ?_⟩⟩
  · have : L = (Λ.prod (Submodule.pi Set.univ fun p => (𝔟 p : Submodule (𝓞 E) E))).map (f.restrictScalars (𝓞 E)) := by
      ext x
      rw [hL, Submodule.mem_map]
      constructor
      · rintro ⟨y, hy, u, hu, rfl⟩
        exact ⟨(y, u), ⟨hy, fun p _ => hu p⟩, rfl⟩
      · rintro ⟨⟨y, u⟩, ⟨hy, hu⟩, rfl⟩
        exact ⟨y, hy, u, fun p => hu p trivial, rfl⟩
    rw [this]
    exact (hΛ.fg.prod (Submodule.fg_pi fun p => FractionalIdeal.fg_of_isNoetherianRing le_rfl _)).map _
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli
  · intro hy' x' hx'
    obtain ⟨y, hy, u, hu, rfl⟩ := (hL _).1 hy'
    obtain ⟨x, hx, v, hv, rfl⟩ := (hL _).1 hx'
    obtain ⟨b, hb1⟩ := (hΛd y).1 hy x hx
    have : ∀ p : Fin c, ∃ t : 𝓞 E, (t : E) = (if p = p.rev then ε else 1) * (star (v p) * u p.rev) := fun p => by
      obtain ⟨e, he, -⟩ := hsg p
      have := (FractionalIdeal.mem_inv_iff (hb p)).1 ((hd p _).1 (hu p.rev)) _ (hv p)
      obtain ⟨t, ht⟩ := hst _ ((FractionalIdeal.mem_one_iff _).1 this)
      refine ⟨e * t, ?_⟩
      rw [← he, RingOfIntegers.coe_eq_algebraMap, map_mul]
      congr 1
      refine ht.trans ?_
      rw [star_mul, star_star]
    choose t ht using this
    refine ⟨b + ∑ p, t p, ?_⟩
    rw [key, ← hb1, ← Finset.sum_congr rfl fun p _ => ht p]
    simp
  · obtain ⟨⟨y, u⟩, rfl⟩ := fsur y'
    rw [hf] at h ⊢
    refine (hL _).2 ⟨y, (hΛd y).2 fun x hx => ?_, u, fun q => ?_, rfl⟩
    · have := h _ ((hL _).2 ⟨x, hx, 0, fun p => (𝔟 p).zero_mem, rfl⟩)
      rw [key] at this
      simpa using this
    · obtain ⟨p, rfl⟩ := Fin.rev_surjective q
      refine (hd p _).2 ((FractionalIdeal.mem_inv_iff (hb p)).2 fun s hs => ?_)
      have := h _ ((hL _).2 ⟨0, Λ.zero_mem, Pi.single p s, fun q => by
        by_cases hq : q = p
        · subst hq; simpa using hs
        · rw [Pi.single_eq_of_ne hq]; exact (𝔟 q).zero_mem, rfl⟩)
      rw [key, Finset.sum_eq_single p (fun q _ hq => by rw [Pi.single_eq_of_ne hq]; simp)
        (fun h => absurd (Finset.mem_univ _) h)] at this
      obtain ⟨b, hb1⟩ := this
      obtain ⟨e, he, hee⟩ := hsg p
      rw [← he] at hb1
      have hee' : (e : E) * e = 1 := by exact_mod_cast congrArg (fun z : 𝓞 E => (z : E)) hee
      obtain ⟨t, ht⟩ := hst (star s * u p.rev) ⟨e * b, by
        rw [RingOfIntegers.coe_eq_algebraMap, map_mul]
        change (e : E) * (b : E) = _
        rw [hb1]
        simp only [Pi.zero_apply, star_zero, zero_mul, Finset.sum_const_zero, zero_add, Pi.single_eq_same]
        rw [← mul_assoc, hee', one_mul]⟩
      refine (FractionalIdeal.mem_one_iff _).2 ⟨t, ht.trans ?_⟩
      rw [star_mul, star_star]

end General

theorem isSelfDualC_lat : ∀ (D : D7) (A B : HSp D) (c : ℕ) (ε : D.host.E) (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E), (ε = 1 ∨ ε = -1) → IsSelfDualC A Λ → (∀ p, 𝔟 p ≠ 0) → (∀ p x, x ∈ 𝔟 p.rev ↔ star x ∈ (𝔟 p)⁻¹) → IsSelfDualC B (d.lat Λ 𝔟) := by
  intro D A B c ε d Λ 𝔟 hε hΛ hb hd
  exact selfDual_sum Formalism.BasicNotions.Examples₂.star_isIntegral B.gram A.gram (frameMat B A d.ι) d.a ε hε (gram_herm B) (gram_inj A)
    (gram_isom A B d.ι d.isom) d.perp d.gram d.rank Λ 𝔟 hΛ.1 hΛ.2 hb hd _ fun _ => Iff.rfl

end GlobalTheory.ChiGrid.SumDual
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiholomorphicDerivCutoffConnectionDifferenceEqStatement
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.antiholomorphicDeriv_cutoff_connection_difference_eq : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ρ : V n → ℝ} {G₀ G₁ : V n → Matrix r r ℂ} {v : V n}, DifferentiableAt ℝ ρ v → MContDiffAt 2 G₀ v → IsUnit (G₀ v).det → MContDiffAt 2 G₁ v → IsUnit (G₁ v).det → (fun a b => mdbar (fun x => -((ρ x : ℂ) • (conn G₁ x (coordVec a) - conn G₀ x (coordVec a)))) v (coordVec b)) = (ρ v : ℂ) • (curvAt G₁ v - curvAt G₀ v) - cutForm ρ G₀ G₁ v := by
  first | exact @GlobalTheory.GoodTop.mdbar_neg_cut_conn_sub | exact GlobalTheory.GoodTop.mdbar_neg_cut_conn_sub | (intros; apply GlobalTheory.GoodTop.mdbar_neg_cut_conn_sub <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithInterProjectionFormulaOfHeightProjectionFor
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.Published

theorem arProj_of_heightProjection (H : HeightProjection) : ArProj := by
  intro k _ X Y _ _ p q D hX hY π hπ hg hm
  have key (L : HermLB p) (a : ℝ) (ha : L.IsSelfInter a) :
      (L.pull π hπ).IsSelfInter ((π.residueDegree (genericPoint Y) : ℝ) * a) := by
    obtain ⟨h, hh, rfl⟩ := ha
    have := H k X Y p q D D hX hY π hπ (by
      rw [hg, (genericPoint_spec X).def]
      exact (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph).trans hX.dim_eq) hm L h hh
    exact (congrArg (fun x => (π.residueDegree (genericPoint Y) : ℝ) * h x) hg) ▸ this
  refine ⟨key, fun ι _ L Φ hΦ => ⟨fun n => ?_, fun P d hd hP => ?_⟩⟩
  · exact (ArInt.isometric_comb_pull L n π hπ).symm.isSelfInter hY (key _ _ (hΦ.1 n))
  · rw [LinearMap.smul_apply, hΦ.2 P d hd hP, smul_zero]

end GlobalTheory.Published
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelGoodFormsDimsAgreePartwise
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.DimPartsFull

theorem dimParts : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → GoodStable A3.A.X → GlobalTheory.CuspMult.CuspDecomp D → GlobalTheory.CuspMult.MultEq R.toRealDat → R.toRealDat.LUnif → (R.toCx3 F).DimParts false :=
  fun hP _ _ _ _ _ _ _ _ _ _ _ _ R F _ hOk hW hEx hX hD hM hU =>
    dimParts_of_schur R F hOk hW hEx hX hD hM hU (_root_.GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hP R.toRealDat)

end GlobalTheory.DimPartsFull

end
end

