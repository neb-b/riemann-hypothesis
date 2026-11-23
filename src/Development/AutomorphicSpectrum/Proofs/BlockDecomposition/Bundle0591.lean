module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0080
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BranchProperAtPointHolds
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0051
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0082
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0073
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0068
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0072
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0058
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0550
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0554
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0563
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0528
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
public import GroundTheory.GlobalFields.ComplexMultiplication.MainTheorem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
public import Development.WeilBound.CoreStatements.ThetaDilations.ThetaLint
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleCompactSets
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0061
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupProjections
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0021
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0011
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0576
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0519
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0551
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0529
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0537
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionCardLeAbsNormPow
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0543
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0530
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0546
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1363

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SliceBranchesHolds
section
set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.SliceBranch

theorem sliceBranches : GroundTheory.Heights₂.Heights.SliceBranches.Statement :=
  GroundTheory.Heights₂.Heights.SliceBranches.proof
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.SliceImmersiveGeneral.full
    _root_.GlobalTheory.CompanionTheory.Ar.Branch.branchProperAtPoint
    GroundTheory.Heights₂.Heights.SliceMatricesOpen.full
    GroundTheory.Heights₂.Heights.ImplicitCurve.full

end GlobalTheory.CompanionTheory.Ar.SliceBranch
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulInvSub
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em
open IsDedekindDomain NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.OrbExist

variable {D : D7} {a b c n r t : ℕ}

theorem mm_jn (hn : r + t = n) (M : Mx D c a) (x : Mx D a r) (v : Mx D a t) :
    mm M (jn hn x v) = jn hn (mm M x) (mm M v) := by
  unfold jn mm
  rw [← Matrix.mul_fromCols]
  ext i j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, id]

theorem jn_bl (hn : r + t = n) (w : Mx D a r) (v : Mx D a t) (p : Mx D r r) (q : Mx D r t) (s : Mx D t r) (u : Mx D t t) :
    mm (jn hn w v) (bl hn p q s u) = jn hn (mm w p + mm v s) (mm w q + mm v u) := by
  unfold jn PositivityTheory.Rg.Rsw.L.mm
  rw [show bl hn p q s u =
      (Matrix.fromBlocks p q s u).submatrix
        (finSumFinEquiv.trans (finCongr hn)).symm (finSumFinEquiv.trans (finCongr hn)).symm from rfl]
  rw [Matrix.submatrix_mul_equiv, Matrix.fromCols_mul_fromBlocks]

theorem block_mul₂ (hn : r + t = n) (p p' : Mx D r r) (q q' : Mx D r t) (s s' : Mx D t r) (u u' : Mx D t t) :
    (bl hn p q s u * bl hn p' q' s' u' : Matrix (Fin n) (Fin n) (AE D)) =
      bl hn (mm p p' + mm q s') (mm p q' + mm q u') (mm s p' + mm u s') (mm s q' + mm u u') := by
  unfold bl
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem blockRowSubstitution_one (hn : r + t = n) :
    bl hn (1 : Mx D r r) (0 : Mx D r t) (0 : Mx D t r) (1 : Mx D t t) = (1 : Matrix (Fin n) (Fin n) (AE D)) := by
  unfold bl
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem smul_blockMatrix_sub_one (hn : r + t = n) (e : AE D) (p : Mx D r r) (q : Mx D r t) (s : Mx D t r) (u : Mx D t t)
    (h₁ : e • (p - 1) = p - 1) (h₂ : e • q = q) (h₃ : e • s = s) (h₄ : e • (u - 1) = u - 1) :
    e • (bl hn p q s u - 1) = bl hn p q s u - 1 := by
  have h : bl hn p q s u - 1 = bl hn (p - 1) q s (u - 1) := by
    rw [← blockRowSubstitution_one hn]
    unfold bl
    ext i j
    simp only [Matrix.sub_apply, Matrix.submatrix_apply]
    rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i | i <;>
      rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j <;> simp
  rw [h]
  unfold bl
  ext i j
  simp only [Matrix.smul_apply, Matrix.submatrix_apply]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm i with i | i <;>
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j <;> simp only [Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  · exact congrFun (congrFun h₁ i) j
  · exact congrFun (congrFun h₂ i) j
  · exact congrFun (congrFun h₃ i) j
  · exact congrFun (congrFun h₄ i) j

def shU (hn : r + t = n) (y : Mx D r t) : GL (Fin n) (AE D) where
  val := bl hn 1 y 0 1
  inv := bl hn 1 (-y) 0 1
  val_inv := by
    rw [block_mul₂]
    simpa [mm] using blockRowSubstitution_one hn
  inv_val := by
    rw [block_mul₂]
    simpa [mm] using blockRowSubstitution_one hn

def colU (hn : r + t = n) (g : GL (Fin t) (AE D)) : GL (Fin n) (AE D) where
  val := bl hn 1 0 0 g.1
  inv := bl hn 1 0 0 (g⁻¹).1
  val_inv := by
    rw [block_mul₂]
    have : g.1 * (g⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    simpa [mm, this] using blockRowSubstitution_one hn
  inv_val := by
    rw [block_mul₂]
    have : (g⁻¹).1 * g.1 = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    simpa [mm, this] using blockRowSubstitution_one hn

theorem smul_inv_sub (e : AE D) (g : GL (Fin t) (AE D)) (h : e • (g.1 - 1) = g.1 - 1) :
    e • ((g⁻¹).1 - 1) = (g⁻¹).1 - 1 := by
  have h1 : (g⁻¹).1 * g.1 = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h2 : (g⁻¹).1 - 1 = - ((g⁻¹).1 * (g.1 - 1)) := by
    rw [Matrix.mul_sub, h1, Matrix.mul_one, neg_sub]
  rw [h2, smul_neg, ← Matrix.mul_smul, h]

theorem trans_int {X N : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace N] [MeasurableSpace N]
    [BorelSpace N] (σ : Measure X) (lam : Measure N) (k : N → X → ℂ) (f : X → ℂ) (Θ : X ≃ₜ X) (c : N ≃ₜ N) (κ₁ κ₂ : ℝ≥0)
    (h₁ : σ.map Θ = κ₁ • σ) (h₂ : lam.map c = κ₂ • lam) (hk : ∀ x, ∀ᵐ z ∂σ, k x z = k (c x) (Θ z)) :
    ∫ x, ∫ z, f (Θ z) * k x z ∂σ ∂lam = ((κ₁ * κ₂ : ℝ≥0) : ℂ) * ∫ x, ∫ z, f z * k x z ∂σ ∂lam := by
  have hin : ∀ x, ∫ z, f (Θ z) * k x z ∂σ = (κ₁ : ℂ) * ∫ z, f z * k (c x) z ∂σ := by
    intro x
    have e₁ : ∫ z, f (Θ z) * k x z ∂σ = ∫ z, (fun w => f w * k (c x) w) (Θ z) ∂σ :=
      integral_congr_ae ((hk x).mono fun z hz => by simp only [hz])
    have e₃ := Θ.measurableEmbedding.integral_map (μ := σ) (fun w => f w * k (c x) w)
    rw [e₁, ← e₃, h₁, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  simp only [hin]
  rw [integral_const_mul]
  have e₂ : ∫ x, ∫ z, f z * k (c x) z ∂σ ∂lam = ∫ x, (fun u => ∫ z, f z * k u z ∂σ) (c x) ∂lam := rfl
  have e₄ := c.measurableEmbedding.integral_map (μ := lam) (fun u => ∫ z, f z * k u z ∂σ)
  rw [e₂, ← e₄, h₂, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  push_cast
  ring

theorem map_val_rel {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] (ν : Measure X) (i : X → Y) (Θ : X → X) (T : Y → Y)
    (κ : ℝ≥0) (hi : Measurable i) (hΘ : Measurable Θ) (hT : Measurable T) (hc : ∀ z, i (Θ z) = T (i z)) (h : ν.map Θ = κ • ν) :
    (ν.map i).map T = κ • ν.map i := by
  rw [Measure.map_map hT hi]
  have : T ∘ i = i ∘ Θ := funext fun z => (hc z).symm
  rw [this, ← Measure.map_map hi hΘ, h, Measure.map_smul]
  exact hi.aemeasurable

end GlobalTheory.CompanionTheory.OrbExist

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmulQuotientInvMkEqMkIffMulEquiv
section
open NumberField
open scoped nonZeroDivisors
open scoped GlobalTheory.Idele

namespace GlobalTheory.CompanionTheory.IdeleQuot

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {K : Type} [Field K] [NumberField K]

theorem finitePart_apply (s : GroundTheory.Global.IdeleGroup K) (v : HeightOneSpectrum (𝓞 K)) :
    ((GlobalTheory.EllipticCM.finitePart (K := K) s : (FiniteAdeleRing (𝓞 K) K)ˣ) :
      FiniteAdeleRing (𝓞 K) K) v =
      (GroundTheory.Global.IdeleGroup.finiteProj v s : v.adicCompletion K) := by
  rw [GroundTheory.Global.IdeleGroup.coe_finiteProj]
  rfl

theorem finitePart_inv (s : GroundTheory.Global.IdeleGroup K) :
    GlobalTheory.EllipticCM.finitePart (K := K) s⁻¹ = (GlobalTheory.EllipticCM.finitePart (K := K) s)⁻¹ :=
  map_inv (Units.map (MonoidHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))) s

theorem ord_vw_finitePart (s : GroundTheory.Global.IdeleGroup K) (v : HeightOneSpectrum (𝓞 K)) :
    GlobalTheory.Idele.ord_vw (GlobalTheory.EllipticCM.finitePart (K := K) s) v =
      GroundTheory.Global.IdeleGroup.ord v s :=
  rfl

theorem coe_smul_eq_finitePart_smul (s : GroundTheory.Global.IdeleGroup K)
    (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ((s • 𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      GlobalTheory.EllipticCM.finitePart (K := K) s • (𝔞 : FractionalIdeal (𝓞 K)⁰ K) :=
  GlobalTheory.Idele.eq_of_count_eq (Units.ne_zero _) (GlobalTheory.Idele.smul_ne_zero _ 𝔞.ne_zero) fun v => by
    rw [GroundTheory.Global.IdeleGroup.count_smul, GlobalTheory.Idele.count_smul _ 𝔞.ne_zero, ord_vw_finitePart]

theorem smulQuotient_inv_mk_eq_mk_iff_mulEquiv :
    ∀ {K : Type} [Field K] [NumberField K] (s : GroundTheory.Global.IdeleGroup K)
      (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (x y : K),
      GroundTheory.Global.IdeleGroup.smulQuotient s⁻¹ 𝔞 (Submodule.Quotient.mk x) =
          Submodule.Quotient.mk y ↔
        GlobalTheory.Idele.mulEquiv (GlobalTheory.EllipticCM.finitePart (K := K) s)⁻¹ 𝔞.ne_zero rfl
          (Submodule.Quotient.mk x) = Submodule.Quotient.mk y := by
  intro K _ _ s 𝔞 x y
  rw [GroundTheory.Global.IdeleGroup.smulQuotient_mk_eq_mk_iff, GlobalTheory.Idele.mulEquiv_mk_eq_mk_iff]
  refine forall_congr' fun v => ?_
  rw [← finitePart_inv, finitePart_apply s⁻¹ v, coe_smul_eq_finitePart_smul]
  rfl

end GlobalTheory.CompanionTheory.IdeleQuot
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaMeasureLocallyFiniteInvariant
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.ThetaFrame

theorem free_act {S : Type} [CommRing S] {M n : ℕ} (g : GL (Fin M) S) {Y : Fin n → Fin M → S}
    (hY : LinearIndependent S Y) :
    LinearIndependent S fun a => (g : Matrix (Fin M) (Fin M) S) *ᵥ Y a := by
  have hk : LinearMap.ker (Matrix.mulVecLin (g : Matrix (Fin M) (Fin M) S)) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro x y h
    have h2 := congrArg (Matrix.mulVec ((g⁻¹ : GL (Fin M) S) : Matrix (Fin M) (Fin M) S)) h
    simpa [Matrix.mulVec_mulVec] using h2
  exact hY.map' _ hk

theorem free_of_unit {S : Type} [CommRing S] {M : ℕ} {Y : Fin 1 → Fin M → S} {i : Fin M}
    (hu : IsUnit (Y 0 i)) : LinearIndependent S Y := by
  rw [Fintype.linearIndependent_iff]
  intro g hg a
  have h1 := congrFun hg i
  simp only [Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
  rw [Subsingleton.elim a 0]
  exact hu.mul_left_eq_zero.1 h1

section Rat

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem free_ratTup (R : Type) [CommRing R] [Algebra F R] {M : ℕ} {X : Fin 1 → Fin M → E}
    (hX : LinearIndependent E X) : LinearIndependent (R ⊗[F] E) (ratTup (F := F) R X) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.1 (hX.ne_zero 0)
  exact free_of_unit (i := i) ((isUnit_iff_ne_zero.2 hi).map (inclR (F := F) R))

variable [NumberField F]

theorem projInf_ratTup {M n : ℕ} (X : Fin n → Fin M → E) :
    projInf (ratTup (F := F) (AF F) X) = ratTup (Ainf F) X := by
  funext a i
  simp [projInf, ratTup, inclR]

theorem projV_ratTup (v : HeightOneSpectrum (𝓞 F)) {M n : ℕ} (X : Fin n → Fin M → E) :
    projV v (projFin (ratTup (F := F) (AF F) X)) = ratTup (Fv F v) X := by
  funext a i
  simp [projV, projFin, ratTup, inclR]

theorem act_rat_free {σ : E →ₐ[F] E} {M n : ℕ} {J : Matrix (Fin M) (Fin M) E} (γ : HFinIn (AF F) σ J)
    {X : Fin n → Fin M → E} (hX : LinearIndependent E X) :
    ∃ X' : Fin n → Fin M → E, LinearIndependent E X' ∧
      actW (AF F) σ J γ.1 (ratTup (AF F) X) = ratTup (AF F) X' := by
  obtain ⟨γ, g, -, e⟩ := γ
  refine ⟨fun a => g.val *ᵥ X a, free_act g hX, funext fun a => funext fun i => ?_⟩
  have e' : (HA.mat (AF F) σ J γ).val = g.val.map (inclR (AF F)) := (congrArg Units.val e).symm
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [actW, actTup, e', ratTup, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]

end Rat

theorem theta_inv_of_stable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)) (hμ : IsHaarH F E σ M J μ)
    (h𝓕 : IsFDH F E σ M J μ 𝓕) (n : ℕ) (S : Set (Fin n → Fin M → E))
    (hS : ∀ (γ : HFinIn (AF F) σ J) (X : Fin n → Fin M → E), X ∈ S →
      ∃ X' ∈ S, actW (AF F) σ J γ.1 (ratTup (AF F) X) = ratTup (AF F) X')
    (h : HA (AF F) σ J) :
    (thetaMeas σ J μ 𝓕 S).map (actW (AF F) σ J h) = thetaMeas σ J μ 𝓕 S := by
  obtain ⟨⟨_, _, _⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨_, _, _, _, -, -, -, hB, -, hg⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm (AF F)
  have := hB n M
  obtain ⟨_, _, _, _, _, hact⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hcm M J hJ (AF F)
  obtain ⟨ac, a1, a2, ag⟩ := hact n
  have hl := PositivityTheory.PlacePermOperatorBicommutantSpan.theta_lint F E σ hcm M J hJ μ 𝓕 hμ h𝓕 n S
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective _ _)
  have hri : Function.Injective (ratTup (F := F) (AF F) : (Fin n → Fin M → E) → _) := fun X Y h =>
    funext fun a => funext fun i => hinj (congrFun (congrFun h a) i)
  have hm : Measurable (actW (AF F) σ J h : (Fin n → Fin M → _) → _) :=
    (ac.comp (continuous_const.prodMk continuous_id)).measurable
  have hfin := ((_root_.GlobalTheory.CompanionTheory.SW.finVol_unitaryGroup F E σ hcm M J hJ).2 μ hμ).2 𝓕 h𝓕
  have : μ.IsHaarMeasure := hμ
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  have : Countable Γ := (_root_.GlobalTheory.CompanionTheory.SW.rational_countable_discrete F E σ hcm M J hJ).1
  have h𝓕' : IsFundamentalDomain Γ 𝓕 μ := h𝓕
  obtain ⟨-, _, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.LatticeUnimod.unimodular_of_isFundamentalDomain (HA (AF F) σ J) Γ μ 𝓕 h𝓕' hfin
  refine Measure.ext_of_lintegral _ fun Φ hΦ => ?_
  rw [lintegral_map hΦ hm, hl (fun X => Φ (actW (AF F) σ J h X)) (hΦ.comp hm), hl _ hΦ]
  congr 1
  set f : HA (AF F) σ J → ℝ≥0∞ := fun g => ∑' X : S,
    Φ (actW (AF F) σ J g⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) with hf
  have hle : ∀ (γ : Γ) g, f (γ • g) ≤ f g := fun γ g => by
    choose t hts ht using fun X : S => hS γ⁻¹ X.1 X.2
    have ht' : ∀ X, actW (AF F) σ J (γ : HA (AF F) σ J)⁻¹ (ratTup (AF F) X.1) = ratTup (AF F) (t X) := ht
    have hti : Function.Injective fun X => (⟨t X, hts X⟩ : S) := fun X Y e => by
      have h1 := congrArg (actW (AF F) σ J γ) ((ht' X).trans ((congrArg (fun Z => ratTup (AF F) Z.1) e).trans (ht' Y).symm))
      simp only [← a2, mul_inv_cancel, a1] at h1
      exact Subtype.ext (hri h1)
    refine le_trans (le_of_eq (tsum_congr fun X => ?_)) (ENNReal.tsum_comp_le_tsum_of_injective hti _)
    rw [Subgroup.smul_def, smul_eq_mul, mul_inv_rev, a2, ht']
  have hinv : ∀ (γ : Γ) g, f (γ • g) = f g := fun γ g =>
    (hle γ g).antisymm (by simpa using hle γ⁻¹ (γ • g))
  have hD := h𝓕'.preimage_of_equiv (measurePreserving_mul_right μ h).quasiMeasurePreserving (e := id)
    Function.bijective_id fun γ g => (mul_assoc _ _ _)
  rw [h𝓕'.setLIntegral_eq hD f hinv, ← (measurePreserving_mul_right μ h).setLIntegral_comp_preimage_emb
    (measurableEmbedding_mulRight _)]
  simp only [hf, mul_inv_rev, ← a2, mul_inv_cancel_left]

theorem measurableSet_free (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) :
    MeasurableSet {X : Fin 1 → Fin M → AF F ⊗[F] E | gramR (AF F) σ J X = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (AF F)) ∧
      LinearIndependent (Ainf F ⊗[F] E) (projInf X) ∧ ∀ v, LinearIndependent (Fv F v ⊗[F] E) (projV v (projFin X))} := by
  obtain ⟨⟨_, _, _⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨_, _, _, _, -, -, -, hB, -, hg⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm (AF F)
  have := hB 1 M
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hcm.2.2.1]; norm_num)
  obtain ⟨c1, c2, c3, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hcm _ (Module.finBasis F E) 1 M
  have o1 : IsOpen {X : Fin 1 → Fin M → Ainf F ⊗[F] E | LinearIndependent (Ainf F ⊗[F] E) X} :=
    PI.VolStabSW.TensAllW.isOpen_linIndep (Module.finBasis F E) (Ainf F) (PI.VolStabSW.isOpen_units_Ainf F)
      (PI.VolStabSW.lip_ainf F)
  have o2 : ∀ v, IsOpen {X : Fin 1 → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X} := fun v =>
    PI.VolStabSW.TensAllW.isOpen_linIndep (Module.finBasis F E) (Fv F v) (PI.VolStabSW.isOpen_units_Fv F v)
      (PI.VolStabSW.TensAllW.lip_field _)
  have m1 : MeasurableSet {X : Fin 1 → Fin M → AF F ⊗[F] E | gramR (AF F) σ J X = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (AF F))} :=
    (isClosed_eq (hg 1 M J) continuous_const).measurableSet
  have m2 : MeasurableSet {X : Fin 1 → Fin M → AF F ⊗[F] E | LinearIndependent (Ainf F ⊗[F] E) (projInf X)} :=
    (o1.preimage c1).measurableSet
  have m3 : MeasurableSet {X : Fin 1 → Fin M → AF F ⊗[F] E | ∀ v, LinearIndependent (Fv F v ⊗[F] E) (projV v (projFin X))} := by
    rw [Set.setOf_forall]
    exact MeasurableSet.iInter fun v => (((o2 v).preimage (c3 v)).preimage c2).measurableSet
  exact m1.inter (m2.inter m3)

theorem theta_frames_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → IsLocallyFiniteMeasure (thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E))) ∧ (∀ h : HA (AF F) σ J, (thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E))).map (actW (AF F) σ J h) = thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E))) ∧ thetaMeas σ J μ 𝓕 (framesE σ J (0 : Matrix (Fin 1) (Fin 1) E)) {X : Fin 1 → Fin M → AF F ⊗[F] E | gramR (AF F) σ J X = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (AF F)) ∧ LinearIndependent (Ainf F ⊗[F] E) (projInf X) ∧ ∀ v, LinearIndependent (Fv F v ⊗[F] E) (projV v (projFin X))}ᶜ = 0 := by
  intro F E _ _ _ _ _ σ hcm M J hJ hM μ 𝓕 hμ h𝓕
  obtain ⟨⟨_, _, _⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨_, _, _, _, -, -, -, hB, -, hg⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm (AF F)
  have := hB 1 M
  obtain ⟨_, _, _, _, _, hact⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hcm M J hJ (AF F)
  obtain ⟨ac, a1, a2, ag⟩ := hact 1
  have hrat := (_root_.GlobalTheory.CompanionTheory.SW.GramLocal.gram_local F E σ hcm M J hJ 1 0 0).2
  obtain ⟨pinf, p, hp, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.HProj.components F E σ hcm M J hJ
  have hl := PositivityTheory.PlacePermOperatorBicommutantSpan.theta_lint F E σ hcm M J hJ μ 𝓕 hμ h𝓕 1
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective _ _)
  refine ⟨⟨fun X => ?_⟩, fun h => ?_, ?_⟩
  · obtain ⟨K, hK, hX⟩ := exists_compact_mem_nhds X
    obtain ⟨N, r, hN, hr, hsub⟩ := (_root_.GlobalTheory.CompanionTheory.SW.Cpt.compact_tuples F E σ hcm _ (Module.finBasis F E) 1 M).2 K hK
    obtain ⟨C, hC⟩ := _root_.GlobalTheory.CompanionTheory.SW.MeanCount.mean_count_box F E σ hcm M J hJ hM _ (Module.finBasis F E) μ 𝓕 hμ h𝓕 N hN
    refine ⟨K, hX, lt_of_le_of_lt (le_trans ?_ ((measure_mono (fun X hX => hsub X hX)).trans (hC r hr))) ENNReal.ofReal_lt_top⟩
    have hm : Measurable (K.indicator (1 : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞)) := measurable_one.indicator hK.measurableSet
    rw [← lintegral_indicator_one hK.measurableSet, ← lintegral_indicator_one hK.measurableSet,
      hl _ _ hm, hl _ _ hm]
    have hs : framesE σ J (0 : Matrix (Fin 1) (Fin 1) E) ⊆ {X | X ≠ 0} :=
      fun X hX h0 => hX.1.ne_zero 0 (congrFun h0 0)
    exact mul_le_mul_right (lintegral_mono fun h => ENNReal.tsum_mono_subtype (fun X => K.indicator
      (1 : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞) (actW (AF F) σ J h⁻¹ (ratTup (AF F) X))) hs) _
  · refine theta_inv_of_stable F E σ hcm M J hJ μ 𝓕 hμ h𝓕 1 _ (fun γ X hX => ?_) h
    obtain ⟨X', hX', e⟩ := act_rat_free γ hX.1
    refine ⟨X', ⟨hX', ?_⟩, e⟩
    refine Matrix.map_injective hinj ?_
    show (gramE σ J X').map (inclR (AF F)) = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (AF F))
    rw [← hrat, ← e]
    refine (ag _ _).trans ?_
    rw [hrat, hX.2]
  · have hc := (measurableSet_free F E σ hcm M J).compl
    rw [← lintegral_indicator_one hc, hl _ _ (measurable_one.indicator hc)]
    have e : ∀ (h : HA (AF F) σ J) (X : framesE σ J (0 : Matrix (Fin 1) (Fin 1) E)), Set.indicator
        {X : Fin 1 → Fin M → AF F ⊗[F] E | gramR (AF F) σ J X = (0 : Matrix (Fin 1) (Fin 1) E).map (inclR (AF F)) ∧
          LinearIndependent (Ainf F ⊗[F] E) (projInf X) ∧ ∀ v, LinearIndependent (Fv F v ⊗[F] E) (projV v (projFin X))}ᶜ
        (1 : (Fin 1 → Fin M → AF F ⊗[F] E) → ℝ≥0∞)
        (actW (AF F) σ J h⁻¹ (ratTup (AF F) X.1)) = 0 := fun h X => by
      apply Set.indicator_of_notMem
      rw [Set.notMem_compl_iff]
      refine ⟨?_, ?_, fun v => ?_⟩
      · rw [ag, hrat, X.2.2]
      · rw [(hp 1 h⁻¹ _).1, projInf_ratTup]
        exact free_act (HA.mat (Ainf F) σ J (pinf h⁻¹)) (free_ratTup _ X.2.1)
      · rw [(hp 1 h⁻¹ _).2 v, projV_ratTup]
        exact free_act (HA.mat (Fv F v) σ J (p v h⁻¹)) (free_ratTup _ X.2.1)
    simp only [e, tsum_zero, lintegral_zero, mul_zero]

end GlobalTheory.CompanionTheory.WeilSiegel.Free.ThetaFrame
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorsionNormZetaBoundStatement
section
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_norm_zeta_bound : ∀ (K : Type) [Field K] [NumberField K] (m : ℕ) (L : Submodule (𝓞 K) (Fin m → K)), IsLat L → ∀ r : ℝ, 1 < r → Summable (fun x : (Fin m → K) ⧸ L => (Ideal.absNorm (Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x) : ℝ) ^ (-((m : ℝ) + r))) ∧ ∑' x : (Fin m → K) ⧸ L, (Ideal.absNorm (Ideal.torsionOf (𝓞 K) ((Fin m → K) ⧸ L) x) : ℝ) ^ (-((m : ℝ) + r)) ≤ zetaR K r := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.sum_torsion | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.sum_torsion | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS.sum_torsion <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwCentRatFComm
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.RatCentComm

theorem commute_norm {G : Type} [Group G] (θ : G →* G) (hθ : ∀ g, θ (θ g) = g) (D g : G)
    (hg : g ∈ twCent θ D) : g * (D * θ D) = (D * θ D) * g := by
  have h1 : g * D = D * θ g := hg
  have h2 : θ g = D⁻¹ * g * D := by rw [mul_assoc, h1]; group
  have h3 := congrArg θ h2
  rw [hθ, map_mul, map_mul, map_inv, h2] at h3
  calc g * (D * θ D)
      = (D * θ D) * ((θ D)⁻¹ * (D⁻¹ * g * D) * θ D) := by group
    _ = _ := by rw [← h3]

theorem twCent_ratF_comm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (δ : GL (Fin n) E),
    (δ * thE E n δ).val.charpoly.Separable →
    ∀ a ∈ twCent (thF E n) (ratF E n δ), ∀ b ∈ twCent (thF E n) (ratF E n δ), a * b = b * a := by
  intro E _ _ _ n δ hs a ha b hb
  have hθ : ∀ g, thF E n (thF E n g) = g :=
    GlobalTheory.LocTwist.thetaGL_thetaGL n _ (fun y => GlobalTheory.ThetaPull.cFin_cFin y)
  obtain ⟨v, hv⟩ := GlobalTheory.ClassParam.exists_cyclic_field _ hs
  have hv' : IsUnit (GlobalTheory.ClassParam.krylov (ratF E n δ * thF E n (ratF E n δ)).val
      (algebraMap E (Af E) ∘ v)).det := by
    have h1 := (IsUnit.mk0 _ hv).map (algebraMap E (Af E))
    rw [RingHom.map_det, RingHom.mapMatrix_apply, GlobalTheory.ClassParam.krylov_map] at h1
    rw [GlobalTheory.MassNorm.thF_ratF, ← map_mul]
    exact h1
  have hc : ∀ g ∈ twCent (thF E n) (ratF E n δ),
      Commute g.val (ratF E n δ * thF E n (ratF E n δ)).val := fun g hg => by
    change g.val * _ = _ * g.val
    rw [← Units.val_mul, ← Units.val_mul, commute_norm _ hθ _ _ hg]
  obtain ⟨p, hp⟩ := GlobalTheory.MassNorm.aeval_of_commute_cyclic _ hv' (hc a ha)
  obtain ⟨q, hq⟩ := GlobalTheory.MassNorm.aeval_of_commute_cyclic _ hv' (hc b hb)
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, hp, hq, ← map_mul, ← map_mul, mul_comm]

end GlobalTheory.CompanionTheory.RatCentComm
end
end

