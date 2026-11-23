module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0178
public import ReciprocityTheory.DualLattices.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumEqConstMulPetersson
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0180
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HyperspecialFixesAllChainVacuaAtInertPrime
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0181
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0121
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Formalism.SharpRestriction.ParConsts

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteBasisAlgebraicForms
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU GlobalTheory.CuspRep GlobalTheory.PRep

noncomputable section

namespace GlobalTheory.IntStruct


open MvPolynomial in
theorem exists_coord_eq_sum_coeff {σ : Type} {d : ℕ} (V : Submodule ℂ (MvPolynomial σ ℂ)) (B : Module.Basis (Fin d) ℂ V)
    (i : Fin d) : ∃ (s : Finset (σ →₀ ℕ)) (a : s → ℂ), ∀ v : V,
      B.repr v i = ∑ m : s, a m * (v : MvPolynomial σ ℂ).coeff m.1 := by
  classical
  let s : Finset (σ →₀ ℕ) := Finset.univ.biUnion fun j => ((B j : V) : MvPolynomial σ ℂ).support
  let R : V →ₗ[ℂ] (s → ℂ) := LinearMap.pi fun m => (lcoeff ℂ m.1).comp V.subtype
  have hR : LinearMap.ker R = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun v hv => ?_
    have h0 : ∀ m : s, (v : MvPolynomial σ ℂ).coeff m.1 = 0 := fun m => congrFun hv m
    refine Subtype.ext (MvPolynomial.ext _ _ fun m => ?_)
    change (v : MvPolynomial σ ℂ).coeff m = 0
    by_cases hm : m ∈ s
    · exact h0 ⟨m, hm⟩
    · have hv' : (v : MvPolynomial σ ℂ) = ∑ j, B.repr v j • ((B j : V) : MvPolynomial σ ℂ) := by
        calc (v : MvPolynomial σ ℂ) = ((∑ j, B.repr v j • B j : V) : MvPolynomial σ ℂ) := by rw [B.sum_repr v]
          _ = _ := by rw [Submodule.coe_sum]; rfl
      rw [hv', coeff_sum]
      simp only [coeff_smul]
      refine Finset.sum_eq_zero fun j _ => ?_
      have : m ∉ ((B j : V) : MvPolynomial σ ℂ).support := fun h =>
        hm (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, h⟩)
      rw [notMem_support_iff.1 this, smul_zero]
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective R hR
  refine ⟨s, fun m => B.repr (L (Pi.single m 1)) i, fun v => ?_⟩
  have e1 : B.repr v i = ((B.coord i).comp L) (R v) := by
    rw [LinearMap.comp_apply, ← LinearMap.comp_apply L R, hL, LinearMap.id_apply, Module.Basis.coord_apply]
  rw [e1, LinearMap.pi_apply_eq_sum_univ ((B.coord i).comp L) (R v)]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hs : (fun j => if m = j then (1 : ℂ) else 0) = Pi.single m 1 := by
    funext j
    simp [Pi.single_apply, eq_comm]
  rw [hs, smul_eq_mul, mul_comm]
  rfl

end GlobalTheory.IntStruct

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ISupIndepOfPairwiseOrthogonalDefinite
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem petersson_form_classSum_comparison :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n)
      (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ), GlobalTheory.CoefDuty.IsInvForm a β → ∃ B, GlobalTheory.CoefDuty.IsPetersson a B ∧
      ∀ (J : Subgroup (GAf L n)) (χ : J →* ℂˣ) (T : Finset (GAf L n)), GlobalTheory.CoefDuty.IsBounded J →
        (∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → ∃ h : κ ∈ J, χ ⟨κ, h⟩ = 1) →
        GlobalTheory.CoefDuty.IsClassReps J T → ∃ c : ℝ, 0 < c ∧ ∀ f ∈ NG.TypeSp a.ρ J χ,
          ∀ f' ∈ NG.TypeSp a.ρ J χ, GlobalTheory.CoefDuty.classSum a β J T f f' = (c : ℂ) * B f f' :=
  _root_.GlobalTheory.ClassPet.classSum_eq_pet

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntegralOffPrimesMatrixStepEntryDataStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegralOffPrimes_matrixStepEntryData : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → ∀ u μ, (∀ k, D.host.g k ∉ Y.Qp μ) → ∀ (i : ℕ), i < t.m2 → ∀ al be p p' x, IntOff (t.O u μ).S (t.seam.σ₀ (XiEntry (u := t.word u) t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) i al be p p' x)) := by
  first | exact @GlobalTheory.KerTie.intOff_xiEntry | exact GlobalTheory.KerTie.intOff_xiEntry | (intros; apply GlobalTheory.KerTie.intOff_xiEntry <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelThetaRelationOfIndicatorRelationSplit
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

namespace GlobalTheory.KerRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem eqOffSplit_of_eqOff : ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) (n : ℕ) (L L₀ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), GL3Theta.SplitP D P → GL3Theta.EqOff D P L L₀ → GL3Theta.EqOffSplit D L L₀ := _root_.GlobalTheory.EqOffSplitOfSplit.eqOffSplit_of_eqOff

theorem kerTh_common : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 → B.LatAll → B.VecP χ → ∀ (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ), 0 < cl → (∀ Q ∈ SS, Formalism.L2.Col.conjPrime₂ Q ∉ SS) → ∀ (a b : ℕ) (P : HeightOneSpectrum (𝓞 D.host.E)), GL3Theta.SplitP D P → P ∉ SS → Formalism.L2.Col.conjPrime₂ P ∉ SS → ((cl : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ((cl : ℕ) : 𝓞 D.host.E) ∉ (Formalism.L2.Col.conjPrime₂ P).asIdeal → ∀ (N₀ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N₀' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ), TaylorLogMetric.admitted D a b N₀ N₀' → DatLoc D cc SS cl N₀ N₀' Ξ → ∀ (ι : Type) [Fintype ι] (N : ι → Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : ι → Submodule (𝓞 D.host.E) (Fin b → D.host.E)), (∀ i, TaylorLogMetric.admitted D a b (N i) (N' i) ∧ GL3Theta.EqOff D P (N i) N₀ ∧ GL3Theta.EqOff D P (N' i) N₀') → ∃ T : (TaylorLogMetric.VC D a b → ℂ) →ₗ[ℂ] (TaylorLogMetric.VC D a b → ℂ), ∀ i, kerTh B χ SS cl (N i) (N' i) Ξ = T (B.eNat χ a b (N i) (N' i)) := GlobalTheory.T.kernelFunctions_common_linearOperator_off_splitPrime

theorem eqOffSplit_refl (D : D7) {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : GL3Theta.EqOffSplit D L L :=
  ⟨1, one_ne_zero, fun Q hQ => (Q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hQ isUnit_one)).elim,
    fun x hx => by simpa using hx, fun x hx => by simpa using hx⟩

theorem eqOffSplit_symm {D : D7} {n : ℕ} {L₁ L₂ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (h : GL3Theta.EqOffSplit D L₁ L₂) : GL3Theta.EqOffSplit D L₂ L₁ := by
  obtain ⟨a, ha0, hsa, ha1, ha2⟩ := h
  exact ⟨a, ha0, hsa, ha2, ha1⟩

theorem mem_Th_const_mul (D : D7) (T : TaylorLogMetric.Tor D) {a b : ℕ} {L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)} {F : TaylorLogMetric.VC D a b → ℂ} (hF : F ∈ TaylorLogMetric.Th D T L L') (k : ℂ) :
    (fun z => k * F z) ∈ TaylorLogMetric.Th D T L L' := by
  refine ⟨hF.1.const_mul k, fun x hx z => ?_⟩
  have := hF.2 x hx z
  simp only [TaylorLogMetric.U] at this ⊢
  rw [← this]; ring

theorem chiFac_ne_zero (D : D7) {χ : TaylorLogMetric.IdE D → ℂ} (hχ : TaylorLogMetric.IsChi D χ) {a b : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin a → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)}
    (h : StandardLatticesGL3.SD D L) (h' : StandardLatticesGL3.SD D L') : Base.chiFac χ a b L L' ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ (GlobalTheory.ThetaMove.Moved.chi_detId_ne_zero hχ (GlobalTheory.ThetaMove.Moved.sd_stdL D a) h))
    (zpow_ne_zero _ (GlobalTheory.ThetaMove.Moved.chi_detId_ne_zero hχ (GlobalTheory.ThetaMove.Moved.sd_stdL D b) h'))

theorem thMoved_move_right (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) {a b : ℕ}
    (hχ : TaylorLogMetric.IsChi D χ) (hE : B.EqP χ) (ha : Even a) (hb : Even b) (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E))
    (L' L'' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (h : StandardLatticesGL3.SD D L) (h' : StandardLatticesGL3.SD D L') (h'' : StandardLatticesGL3.SD D L'') :
    B.thMoved a b L L'' = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L L'') (B.thMoved a b L L') := by
  funext z
  have e : Base.chiFac χ a b L L'' * B.thMoved a b L L'' z = χ (TaylorLogMetric.detId D L' L'') ^ (-((a / 2 : ℕ) : ℤ)) *
      TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L L'')
        (fun w => Base.chiFac χ a b L L' * B.thMoved a b L L' w) z :=
    congrFun (hE.2.1 a b ⟨L, h⟩ ⟨L', h'⟩ ⟨L'', h''⟩ ha hb) z
  have f : Base.chiFac χ a b L L'' = χ (TaylorLogMetric.detId D L' L'') ^ (-((a / 2 : ℕ) : ℤ)) * Base.chiFac χ a b L L' := by
    unfold Base.chiFac
    rw [GlobalTheory.ThetaMove.Moved.chi_detId_mul hχ (GlobalTheory.ThetaMove.Moved.sd_stdL D b) h' h'', mul_zpow]
    ring
  rw [GlobalTheory.ThetaMove.Moved.iop_mul, ← mul_assoc, ← f] at e
  exact mul_left_cancel₀ (chiFac_ne_zero D hχ h h'') e

theorem thMoved_move_left (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) {a b : ℕ}
    (hχ : TaylorLogMetric.IsChi D χ) (hE : B.EqP χ) (ha : Even a) (hb : Even b) (L L₁ : Submodule (𝓞 D.host.E) (Fin a → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (h : StandardLatticesGL3.SD D L) (h₁ : StandardLatticesGL3.SD D L₁) (h' : StandardLatticesGL3.SD D L') :
    B.thMoved a b L₁ L' = TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L₁ L') (B.thMoved a b L L') := by
  funext z
  have e : Base.chiFac χ a b L₁ L' * B.thMoved a b L₁ L' z = χ (TaylorLogMetric.detId D L L₁) ^ (((b / 2 : ℕ) : ℤ)) *
      TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L L') (TaylorLogMetric.La D B.tor L₁ L')
        (fun w => Base.chiFac χ a b L L' * B.thMoved a b L L' w) z :=
    congrFun (hE.2.2 a b ⟨L, h⟩ ⟨L₁, h₁⟩ ⟨L', h'⟩ ha hb) z
  have f : Base.chiFac χ a b L₁ L' = χ (TaylorLogMetric.detId D L L₁) ^ (((b / 2 : ℕ) : ℤ)) * Base.chiFac χ a b L L' := by
    unfold Base.chiFac
    rw [GlobalTheory.ThetaMove.Moved.chi_detId_mul hχ (GlobalTheory.ThetaMove.Moved.sd_stdL D a) h h₁, mul_zpow]
    ring
  rw [GlobalTheory.ThetaMove.Moved.iop_mul, ← mul_assoc, ← f] at e
  exact mul_left_cancel₀ (chiFac_ne_zero D hχ h₁ h') e

theorem kerTh_relation_of_indicator : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → δ ≠ 0 → TaylorLogMetric.IsChi D χ → B.LatAll → B.VecP χ → B.EqP χ → GL3Theta.modelXi D → GL3Theta.movesCompose D → ∀ (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ), 0 < cl → (∀ Q ∈ SS, Formalism.L2.Col.conjPrime₂ Q ∉ SS) → ∀ (a b : ℕ) (P : HeightOneSpectrum (𝓞 D.host.E)), GL3Theta.SplitP D P → P ∉ SS → Formalism.L2.Col.conjPrime₂ P ∉ SS → ((cl : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ((cl : ℕ) : 𝓞 D.host.E) ∉ (Formalism.L2.Col.conjPrime₂ P).asIdeal → ∀ (N₀ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N₀' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (Ξ : Formalism.L2.Col.HomE D.host.E a b → ℂ), TaylorLogMetric.admitted D a b N₀ N₀' → DatLoc D cc SS cl N₀ N₀' Ξ → ∀ (ι : Type) [Fintype ι] (N : ι → Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : ι → Submodule (𝓞 D.host.E) (Fin b → D.host.E)), (∀ i, TaylorLogMetric.admitted D a b (N i) (N' i) ∧ GL3Theta.EqOff D P (N i) N₀ ∧ GL3Theta.EqOff D P (N' i) N₀') → ∀ c : ι → ℂ, (∑ i, c i • Set.indicator (GL3Theta.YP D P (N i) (N' i) : Set (Matrix (Fin b) (Fin a) (GL3Theta.EP D P))) (1 : Matrix (Fin b) (Fin a) (GL3Theta.EP D P) → ℂ)) = 0 → ∀ z, ∑ i, c i * (((Real.sqrt (GL3Theta.volP (GL3Theta.YP D P N₀ N₀') (GL3Theta.YP D P (N i) (N' i))) : ℝ) : ℂ) * (Base.chiFac χ a b (N i) (N' i))⁻¹ * kerTh B χ SS cl (N i) (N' i) Ξ z) = 0 := by
  intro D cc δ B χ hcc hδ hδ0 hχ hL hV hE hModel hMoves SS cl hcl hSS a b P hP hPS hPS' hcP hcP' N₀ N₀' Ξ hA0 hD ι _ N N' hN c hrel z
  obtain ⟨T, hT⟩ := kerTh_common D cc δ B χ hcc hδ hδ0 hL hV SS cl hcl hSS a b P hP hPS hPS' hcP hcP' N₀ N₀' Ξ hA0 hD ι N N' hN
  obtain ⟨ha, hb, h0, h0'⟩ := hA0
  have hth0 : B.thMoved a b N₀ N₀' ∈ TaylorLogMetric.Th D (TaylorLogMetric.tor0 D cc δ) N₀ N₀' := by
    have hm := mem_Th_const_mul D (TaylorLogMetric.tor0 D cc δ) (hV a b N₀ N₀' ⟨ha, hb, h0, h0'⟩).1 (Base.chiFac χ a b N₀ N₀')⁻¹
    convert hm using 1
    funext w
    show _ = _ * (Base.chiFac χ a b N₀ N₀' * _)
    rw [← mul_assoc, inv_mul_cancel₀ (chiFac_ne_zero D hχ h0 h0'), one_mul]
  obtain ⟨Xi, -, hXi⟩ := hModel cc δ hcc hδ a b N₀ N₀' ⟨ha, hb, h0, h0'⟩ P hP _ hth0
  have hmove : ∀ i, B.thMoved a b (N i) (N' i) =
      TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor N₀ N₀') (TaylorLogMetric.La D B.tor (N i) (N' i)) (B.thMoved a b N₀ N₀') := by
    intro i
    obtain ⟨⟨-, -, hi, hi'⟩, ho, ho'⟩ := hN i
    rw [thMoved_move_right D cc δ B χ hχ hE ha hb (N i) N₀' (N' i) hi h0' hi',
      thMoved_move_left D cc δ B χ hχ hE ha hb N₀ (N i) N₀' h0 hi h0']
    exact hMoves cc δ hcc hδ a b N₀ (N i) (N i) N₀' N₀' (N' i) ⟨ha, hb, h0, h0'⟩ ⟨ha, hb, hi, h0'⟩ ⟨ha, hb, hi, hi'⟩
      (eqOffSplit_symm (eqOffSplit_of_eqOff D P _ _ _ hP ho)) (eqOffSplit_refl D _) (eqOffSplit_refl D _)
      (eqOffSplit_symm (eqOffSplit_of_eqOff D P _ _ _ hP ho')) _ hth0
  have key : ∀ i, ((Real.sqrt (GL3Theta.volP (GL3Theta.YP D P N₀ N₀') (GL3Theta.YP D P (N i) (N' i))) : ℝ) : ℂ) *
      (Base.chiFac χ a b (N i) (N' i))⁻¹ * kerTh B χ SS cl (N i) (N' i) Ξ z =
      T (Xi (Set.indicator (GL3Theta.YP D P (N i) (N' i) : Set (Matrix (Fin b) (Fin a) (GL3Theta.EP D P))) 1)) z := by
    intro i
    obtain ⟨⟨-, -, hi, hi'⟩, -, -⟩ := hN i
    set s : ℂ := ((Real.sqrt (GL3Theta.volP (GL3Theta.YP D P N₀ N₀') (GL3Theta.YP D P (N i) (N' i))) : ℝ) : ℂ) with hs
    set X := Xi (Set.indicator (GL3Theta.YP D P (N i) (N' i) : Set (Matrix (Fin b) (Fin a) (GL3Theta.EP D P))) 1) with hX
    have hm : B.thMoved a b (N i) (N' i) = fun w => s⁻¹ * X w := by
      rw [hmove i, hXi (N i) (N' i) ⟨ha, hb, hi, hi'⟩ (hN i).2.1 (hN i).2.2]
      funext w
      push_cast
      rfl
    have he : B.eNat χ a b (N i) (N' i) = (Base.chiFac χ a b (N i) (N' i) * s⁻¹) • X := by
      funext w
      show Base.chiFac χ a b (N i) (N' i) * B.thMoved a b (N i) (N' i) w = _
      rw [hm, Pi.smul_apply, smul_eq_mul, mul_assoc]
    have hs0 : s ≠ 0 := by
      intro h0s
      apply (hV a b (N i) (N' i) ⟨ha, hb, hi, hi'⟩).2.1
      rw [he, h0s, inv_zero, mul_zero, zero_smul]
    rw [hT i, he, map_smul, Pi.smul_apply, smul_eq_mul]
    field_simp [chiFac_ne_zero D hχ hi hi']
  simp_rw [key]
  have hsum := congrArg (fun f => T (Xi f) z) hrel
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, map_zero, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hsum
  exact hsum

end GlobalTheory.KerRel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LiftInertEigenvaluesIffThetaImageEigensystem
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Hk3.InertLift

variable {D : D7}

theorem hkF_comb (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) (c : List ℤ →₀ ℂ)
    (F : Bridge.Gf V → W) : hkF V P c F = ∑ d ∈ c.support, c d • hkF V P (Finsupp.single d 1) F := by
  funext h
  simp only [hkF, Finset.sum_apply, Pi.smul_apply]
  rw [Finsupp.sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finsupp.sum_single_index (by simp), one_smul]

theorem hkF_nonlab (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) {d : List ℤ}
    (hd : ¬ IsLab V P d) (F : Bridge.Gf V → W) : hkF V P (Finsupp.single d 1) F = 0 := by
  funext h
  simp [hkF, rep, hd]


open Classical in
def tyOf (n : ℕ) (e : List ℤ) : List ℕ :=
  if h : ∃ y, Formalism.L2.Col.InertTypeOk n y ∧ e = GlobalTheory.Hk3.labIn n y then h.choose else []

theorem labIn_tyOf {n : ℕ} {e : List ℤ} (h : ∃ y, Formalism.L2.Col.InertTypeOk n y ∧ e = GlobalTheory.Hk3.labIn n y) :
    Formalism.L2.Col.InertTypeOk n (tyOf n e) ∧ e = GlobalTheory.Hk3.labIn n (tyOf n e) := by
  have hs : tyOf n e = h.choose := by
    simp only [tyOf]
    rw [dite_eq_left h]
  rw [hs]
  exact h.choose_spec


open Classical in
def valC (Lb : List ℤ → Prop) (n : ℕ) (a : List ℕ → ℂ) (c : List ℤ →₀ ℂ) : ℂ :=
  ∑ e ∈ c.support, c e * (if Lb e then a (tyOf n e) else 0)


open Classical in
theorem comb_apply {M X : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup X] [Module ℂ X] (e : M →ₗ[ℂ] X)
    (he : Function.Injective e) (h : (List ℤ →₀ ℂ) → Module.End ℂ M) (Tt : (List ℤ →₀ ℂ) → X → X)
    (hh : ∀ c x, e (h c x) = Tt c (e x))
    (hT : ∀ c F, Tt c F = ∑ d ∈ c.support, c d • Tt (Finsupp.single d 1) F)
    (Lb : List ℤ → Prop) (hT0 : ∀ d, ¬ Lb d → ∀ F, Tt (Finsupp.single d 1) F = 0) (n : ℕ) (a : List ℕ → ℂ) (u : M)
    (hlab : ∀ d, Lb d → ∃ y, Formalism.L2.Col.InertTypeOk n y ∧ d = GlobalTheory.Hk3.labIn n y)
    (heig : ∀ y, Formalism.L2.Col.InertTypeOk n y → h (Finsupp.single (GlobalTheory.Hk3.labIn n y) 1) u = a y • u) (c : List ℤ →₀ ℂ) :
    h c u = valC Lb n a c • u := by
  have hone : ∀ d, h (Finsupp.single d 1) u = (if Lb d then a (tyOf n d) else 0) • u := by
    intro d
    by_cases hd : Lb d
    · obtain ⟨h1, h2⟩ := labIn_tyOf (hlab d hd)
      have := heig _ h1
      rw [← h2] at this
      rw [if_pos hd, this]
    · rw [if_neg hd, zero_smul]
      apply he
      rw [hh, hT0 d hd, map_zero]
  apply he
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hh, hT, valC, Finset.sum_smul, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [mul_smul, ← hone d, map_smul, hh]

theorem evC_congr (V : HSp D) (P : Pl D.host.E) {a b : List ℤ → ℂ} (hab : ∀ d, IsLab V P d → a d = b d) (c : List ℤ →₀ ℂ) :
    evC V P a c = evC V P b c := by
  classical
  simp only [evC, Finsupp.sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hd : IsLab V P d
  · rw [if_pos hd, if_pos hd, hab d hd]
  · rw [if_neg hd, if_neg hd]

section Main

variable {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem tied_label (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt) (j : Fin D.R.m)
    (Q : A3.okI A3.A.μ0) (y : List ℕ) (hy : Formalism.L2.Col.InertTypeOk (Vc D j).rank y) :
    ∀ h, IsOpsV R.toRealDat j A3.A.μ0 h → ∀ f : (A3.A.fam.L j A3.A.μ0).S.Forms,
      R.jV j A3.A.μ0 ((A3.liftI j A3.A.μ0).opAll (Sum.inr (Q, y)) f) =
      h (R.plI Q.1) (Finsupp.single (GlobalTheory.Hk3.labIn (Vc D j).rank y) 1) (R.jV j A3.A.μ0 f) := by
  have h3 := _root_.GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hC
  have core := h3.1 hEx
  have hOk := h3.2.2.1
  have hin : ∀ k : A3.okI A3.A.μ0 × List ℕ, Formalism.L2.Col.InertTypeOk (Vc D j).rank k.2 →
      Good R.toRealDat A3.A.μ0 (R.plI k.1.1) ∧ conjPl (R.plI k.1.1) = R.plI k.1.1 ∧
        (GlobalTheory.Hk3.labIn (Vc D j).rank k.2).Pairwise (fun a b => b ≤ a) := fun k hk =>
    ⟨(hOk A3.A.μ0 k.1.1 k.1.2).1, (hOk A3.A.μ0 k.1.1 k.1.2).2,
      ((GlobalTheory.Hk3.labIn_selfDual_iff _ _).2 ⟨k.2, hk.2.2, hk.1, hk.2.1, rfl⟩).2.1⟩
  exact (hC.inert.hL j A3.A.μ0).elim fun Comparison₂ =>
    (_root_.GlobalTheory.InertHeckeLift.inert_lifts R.toRealDat F.lv2 core.lev core.fam core.models j A3.A.μ0 (A3.okI A3.A.μ0 × List ℕ)
      (fun k => R.plI k.1.1) (fun k => GlobalTheory.Hk3.labIn (Vc D j).rank k.2) (A3.heckeLI j A3.A.μ0)
      (fun k => Formalism.L2.Col.InertTypeOk (Vc D j).rank k.2) hin Comparison₂ (Q, y) hy).2.2.2

theorem one_side (R : RealDat3 D A3 Ks) (F : Face3 D A3) (hC : R.WeakCharacterisation F)
    (hEx : R.toRealDat.ExAt) (hSch : SchurAll R.toRealDat) (hIrr : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ) (j : Fin D.R.m)
    (c : Pl D.host.E → List ℤ → ℂ) (s : (A3.liftI j A3.A.μ0).OpIx → D.what₂.LL) (x : (A3.A.fam.L j A3.A.μ0).S.Forms)
    (hx : ∀ i, (A3.liftI j A3.A.μ0).opAll i x = s i • x)
    (hm : R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ∈ R.Wc' j c) (h0 : R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ≠ 0)
    (Q : A3.okI A3.A.μ0) :
    (∀ y, Formalism.L2.Col.InertTypeOk (Vc D j).rank y → ∀ cW,
      MatchW R.toRealDat j A3.A.μ0 (R.plI Q.1) (Finsupp.single (GlobalTheory.Hk3.labIn (Vc D j).rank y) 1) cW →
      D.what₂.embLL (s (Sum.inr (Q, y))) = evC (Wc D j) (R.plI Q.1) (c (R.plI Q.1)) cW) ∧
    (∀ d, IsLab (Wc D j) (R.plI Q.1) d → ∀ cV, MatchW R.toRealDat j A3.A.μ0 (R.plI Q.1) cV (Finsupp.single d 1) →
      c (R.plI Q.1) d =
        valC (IsLab (Vc D j) (R.plI Q.1)) (Vc D j).rank (fun y => D.what₂.embLL (s (Sum.inr (Q, y)))) cV) := by
  classical
  have h3 := _root_.GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hC
  have core := h3.1 hEx
  have hSF := h3.2.1
  have hg := (h3.2.2.1 A3.A.μ0 Q.1 Q.2).1
  have hcj := (h3.2.2.1 A3.A.μ0 Q.1 Q.2).2
  have hVall := (GlobalTheory.T.realization_family_normal_operators R.toRealDat F.lv2 core.lev core.fam core.models).2 j A3.A.μ0
  have hWall := _root_.GlobalTheory.SphOpsModel.sphericalOperators_forms_on_rank_space_normal_alt R.toRealDat F.lv2 core hSch hIrr R.SF hSF j
  obtain ⟨hV, hVo, -⟩ := hVall
  obtain ⟨hW, hWo, -, -, -, -, hWev, -⟩ := hWall
  have hwW : R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ∈ Wcc R.toRealDat R.SF j c := hm
  have heig : ∀ y, Formalism.L2.Col.InertTypeOk (Vc D j).rank y →
      hV (R.plI Q.1) (Finsupp.single (GlobalTheory.Hk3.labIn (Vc D j).rank y) 1) (R.jV j A3.A.μ0 x) =
        D.what₂.embLL (s (Sum.inr (Q, y))) • R.jV j A3.A.μ0 x := fun y hy =>
    (tied_label R F hC hEx j Q y hy hV hVo x).symm.trans
      ((congrArg (R.jV j A3.A.μ0) (hx (Sum.inr (Q, y)))).trans (LinearMap.map_smulₛₗ (R.jV j A3.A.μ0) _ x))
  have hlab : ∀ d, IsLab (Vc D j) (R.plI Q.1) d →
      ∃ y, Formalism.L2.Col.InertTypeOk (Vc D j).rank y ∧ d = GlobalTheory.Hk3.labIn (Vc D j).rank y := by
    intro d hd
    obtain ⟨h1, h2, h3⟩ := (_root_.GlobalTheory.LabChar.labels_char (Vc D j) (R.plI Q.1) d).1 hd
    obtain ⟨y, ya, yb, yc, yd⟩ := (GlobalTheory.Hk3.labIn_selfDual_iff _ d).1 ⟨h1, h2, h3 hcj⟩
    exact ⟨y, ⟨yb, yc, ya⟩, yd⟩
  have hthe : ∀ cV cW, MatchW R.toRealDat j A3.A.μ0 (R.plI Q.1) cV cW →
      R.thG j A3.A.μ0 (hV (R.plI Q.1) cV (R.jV j A3.A.μ0 x)) =
        hW (R.plI Q.1) cW (R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x)) := fun cV cW hM =>
    (_root_.GlobalTheory.SysW.matched_operators_theta_intertwine R.toRealDat F.lv2 core hSch hIrr R.SF hSF j A3.A.μ0 (R.plI Q.1) hg cV cW hM hV hVo).1 hW hWo
      (R.jV j A3.A.μ0 x)
  have hchain : ∀ (v : ℂ) cV cW, MatchW R.toRealDat j A3.A.μ0 (R.plI Q.1) cV cW →
      hV (R.plI Q.1) cV (R.jV j A3.A.μ0 x) = v • R.jV j A3.A.μ0 x →
      v = evC (Wc D j) (R.plI Q.1) (c (R.plI Q.1)) cW := fun v cV cW hM hv =>
    smul_left_injective ℂ h0 (((R.thG j A3.A.μ0).map_smul v _).symm.trans
      ((congrArg (R.thG j A3.A.μ0) hv.symm).trans ((hthe cV cW hM).trans (hWev c _ hg cW _ hwW))))
  refine ⟨fun y hy cW hM => hchain _ _ cW hM (heig y hy), fun d hd cV hM => ?_⟩
  have h2 : evC (Wc D j) (R.plI Q.1) (c (R.plI Q.1)) (Finsupp.single d 1) = c (R.plI Q.1) d := by
    simp [evC, hd]
  refine h2.symm.trans (hchain _ cV _ hM ?_).symm
  exact comb_apply (R.HV j A3.A.μ0).e (core.models.HV j A3.A.μ0).1 (hV (R.plI Q.1)) (hkF (Vc D j) (R.plI Q.1))
    (fun c y => hVo _ hg c y) (hkF_comb (Vc D j) (R.plI Q.1)) (IsLab (Vc D j) (R.plI Q.1))
    (fun d hd F => hkF_nonlab (Vc D j) (R.plI Q.1) hd F) (Vc D j).rank _ _ hlab heig cV

end Main

end GlobalTheory.Hk3.InertLift


open GlobalTheory.Hk3.InertLift in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Hk3.lift_inert_iff : HoweUnram → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), GlobalTheory.Chain.LiftInteg D → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → InertJunk A3 → (∀ χ ∈ A3.A.X, IsAbsIrrChar χ) → ∀ (j : Fin D.R.m) (c c' : Pl D.host.E → List ℤ → ℂ) (s s' : (A3.liftI j A3.A.μ0).OpIx → D.what₂.LL) (x x' : (A3.A.fam.L j A3.A.μ0).S.Forms), (∀ i, (A3.liftI j A3.A.μ0).opAll i x = s i • x) → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ∈ R.Wc' j c → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ≠ 0 → (∀ i, (A3.liftI j A3.A.μ0).opAll i x' = s' i • x') → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x') ∈ R.Wc' j c' → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x') ≠ 0 → ∀ Q : A3.okI A3.A.μ0, ((∀ y : List ℕ, s (Sum.inr (Q, y)) = s' (Sum.inr (Q, y))) ↔ ∀ d, IsLab (Wc D j) (R.plI Q.1) d → c (R.plI Q.1) d = c' (R.plI Q.1) d) := by
  intro hH D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hInt hC hEx hSch hJ hIrr j c c' s s' x x' hx hm h0 hx' hm' h0' Q
  have h3 := _root_.GlobalTheory.CoreThree.heckeCharacterisation_places_parts_of_weak R F hC
  have core := h3.1 hEx
  have hg := (h3.2.2.1 A3.A.μ0 Q.1 Q.2).1
  have hcj := (h3.2.2.1 A3.A.μ0 Q.1 Q.2).2
  have hTwo := _root_.GlobalTheory.Hk3.TwoSidedInert.twoSided_of_inert hH R.toRealDat F.lv2 hInt core hSch A3.A.μ0 _ hg hcj (_root_.GlobalTheory.VacFixInert.fixAll_inert R F hC A3.A.μ0 _ hg hcj)
  obtain ⟨a1, a2⟩ := one_side R F hC hEx hSch hIrr j c s x hx hm h0 Q
  obtain ⟨b1, b2⟩ := one_side R F hC hEx hSch hIrr j c' s' x' hx' hm' h0' Q
  constructor
  · intro hs d hd
    obtain ⟨cV, hM⟩ := (hTwo.2 j).2 (Finsupp.single d 1)
    rw [a2 d hd cV hM, b2 d hd cV hM]
    simp only [hs]
  · intro hcc y
    have hval : ∀ y, Formalism.L2.Col.InertTypeOk (Vc D j).rank y → s (Sum.inr (Q, y)) = s' (Sum.inr (Q, y)) := by
      intro y hy
      obtain ⟨cW, hM⟩ := (hTwo.2 j).1 (Finsupp.single (GlobalTheory.Hk3.labIn (Vc D j).rank y) 1)
      apply D.what₂.embLL.injective
      rw [a1 y hy cW hM, b1 y hy cW hM]
      exact evC_congr _ _ hcc cW
    have hx0 : x ≠ 0 := fun e => h0 ((congrArg (R.thG j A3.A.μ0) ((congrArg (R.jV j A3.A.μ0) e).trans (map_zero _))).trans (map_zero _))
    have hx0' : x' ≠ 0 := fun e => h0' ((congrArg (R.thG j A3.A.μ0) ((congrArg (R.jV j A3.A.μ0) e).trans (map_zero _))).trans (map_zero _))
    have hrk : (Vc D j).rank = A3.A.r + A3.A.t := R.B.rankL j
    have e1 : A3.heckeLI j A3.A.μ0 (Q, y) x = s (Sum.inr (Q, y)) • x := hx (Sum.inr (Q, y))
    have e2 : A3.heckeLI j A3.A.μ0 (Q, y) x' = s' (Sum.inr (Q, y)) • x' := hx' (Sum.inr (Q, y))
    rcases hJ.L j A3.A.μ0 Q y with hz | ⟨y', hy', he⟩
    · have z1 : s (Sum.inr (Q, y)) = 0 := smul_left_injective D.what₂.LL hx0
        (e1.symm.trans ((LinearMap.congr_fun hz x).trans (zero_smul _ x).symm))
      have z2 : s' (Sum.inr (Q, y)) = 0 := smul_left_injective D.what₂.LL hx0'
        (e2.symm.trans ((LinearMap.congr_fun hz x').trans (zero_smul _ x').symm))
      rw [z1, z2]
    · have f1 : A3.heckeLI j A3.A.μ0 (Q, y') x = s (Sum.inr (Q, y')) • x := hx (Sum.inr (Q, y'))
      have f2 : A3.heckeLI j A3.A.μ0 (Q, y') x' = s' (Sum.inr (Q, y')) • x' := hx' (Sum.inr (Q, y'))
      have g1 : s (Sum.inr (Q, y)) = s (Sum.inr (Q, y')) := smul_left_injective D.what₂.LL hx0
        (e1.symm.trans ((LinearMap.congr_fun he x).trans f1))
      have g2 : s' (Sum.inr (Q, y)) = s' (Sum.inr (Q, y')) := smul_left_injective D.what₂.LL hx0'
        (e2.symm.trans ((LinearMap.congr_fun he x').trans f2))
      rw [g1, g2]
      exact hval y' (hrk ▸ hy')

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PrecedingStepDatumIntegralAwayFromLevelsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.precedingStepDatum_integral_away_from_levels : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → ∀ u μ, (∀ k, D.host.g k ∉ Y.Qp μ) → ∀ al p₀ p Yb x, IntOff (t.O u μ).S (t.seam.σ₀ (XiCpl1 (u := t.word u) t.Ch t.sel (t.tup μ) (t.cst μ) (t.idx μ) t.m2 al p₀ p Yb x)) := by
  first | exact @GlobalTheory.xiCpl1_intOff | exact GlobalTheory.xiCpl1_intOff | (intros; apply GlobalTheory.xiCpl1_intOff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WordConditionsAtPlaceOfFrobeniusOrbitStatement
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wordConditions_at_place_of_frobeniusOrbit : ∀ {D : D7} (L : SizeData₂ D) (C₀ : ℝ) (HW : HWOf D.loc) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Enl D i w hw) (hG : Good (D.nbr i w hw).Kw 1 C.LL) r ρ π (ε : ℤˣ) (κ : D.host.E →+* ↥C.LL.1), Roomy L C₀ → Formalism.MainNotions.LocalSituation.adm7 D → D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → JumpIn (D.loc (D.nd.l i)) (K := (D.nbr i w hw).Kw) D (liftIdx D i) ε (Br.cEw D.nbr i w hw) κ (fun x => C.loc (rDuO D.nd i r x)) (C.loc (T2O D.nd i ρ π)) → ∃ g, IsOrbit g (DV.frobG D (D.nd.l i))⁻¹ ∧ C.WordBase r ρ π L HW hG (recWord L (liftIdx D i) ε g) := by
  first | exact @GlobalTheory.HTW.Rec.wordBase_of_jumpIn | exact GlobalTheory.HTW.Rec.wordBase_of_jumpIn | (intros; apply GlobalTheory.HTW.Rec.wordBase_of_jumpIn <;> assumption)
end

