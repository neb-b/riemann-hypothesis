module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevel
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUnique
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLaws
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompAtOfFin
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsOrthonormalisation
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0144
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0360
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0376
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0375
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0210
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaTraceBaseChangeIff

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DomainFrameEqRealTranslateMulBorel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameDecomp

theorem hermC_mulVec {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (x : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r → ℂ) :
    hermC τ G (x *ᵥ a) (x *ᵥ b) = ∑ i, ∑ j, a i * FD.gram τ G x i j * conj (b j) := by
  unfold hermC
  calc ∑ p, ∑ q, (x *ᵥ a) p * τ (G p q) * conj ((x *ᵥ b) q)
      = ∑ p, ∑ q, ∑ i, ∑ j, a i * (x p i * τ (G p q) * conj (x q j)) * conj (b j) := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
        rw [Finset.sum_mul, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = ∑ p, ∑ i, ∑ q, ∑ j, a i * (x p i * τ (G p q) * conj (x q j)) * conj (b j) :=
        Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ p, ∑ i, ∑ j, ∑ q, a i * (x p i * τ (G p q) * conj (x q j)) * conj (b j) :=
        Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ p, ∑ j, ∑ q, a i * (x p i * τ (G p q) * conj (x q j)) * conj (b j) := Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ p, ∑ q, a i * (x p i * τ (G p q) * conj (x q j)) * conj (b j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ j, a i * FD.gram τ G x i j * conj (b j) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [FD.gram, Matrix.of_apply, FD.col, hermC, Finset.mul_sum, Finset.sum_mul]

theorem isometry_of_gram_eq {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (x y : Matrix (Fin r) (Fin r) ℂ) (hy : y.det ≠ 0) (h : FD.gram τ G x = FD.gram τ G y) (v w : Fin r → ℂ) :
    hermC τ G ((x * y⁻¹) *ᵥ v) ((x * y⁻¹) *ᵥ w) = hermC τ G v w := by
  have hyu : IsUnit y.det := isUnit_iff_ne_zero.mpr hy
  have hback : ∀ c : Fin r → ℂ, y *ᵥ (y⁻¹ *ᵥ c) = c := fun c => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hyu, Matrix.one_mulVec]
  calc hermC τ G ((x * y⁻¹) *ᵥ v) ((x * y⁻¹) *ᵥ w)
      = hermC τ G (x *ᵥ (y⁻¹ *ᵥ v)) (x *ᵥ (y⁻¹ *ᵥ w)) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    _ = hermC τ G (y *ᵥ (y⁻¹ *ᵥ v)) (y *ᵥ (y⁻¹ *ᵥ w)) := by
        rw [hermC_mulVec, hermC_mulVec, h]
    _ = hermC τ G v w := by rw [hback, hback]

theorem exists_real_point {D : D7} {S T : HSp D} (C : Ctx S T)
    (u : C.X.Ψ → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hu : ∀ (σ : C.X.Ψ) v w, hermC σ.1 C.X.Gm (u σ *ᵥ v) (u σ *ᵥ w) = hermC σ.1 C.X.Gm v w) :
    ∃ a ∈ GinfC T, (fun σ => (compAt C.θ (C.m.e.symm σ) (Formalism.L2.Theta.mt T a)).map conj) = u := by
  obtain ⟨σ₀, hσ₀⟩ := GlobalTheory.RealLineAt.exists_inverse_chart C.inf
  obtain ⟨k, hk, hkτ⟩ := GlobalTheory.FockCompare.LiftUnitary.lift_unitary D C.θ σ₀ hσ₀ T
    (fun τ => (u (C.m.e τ)).map conj) (fun τ => by
      have hcc : ((u (C.m.e τ)).map conj).map conj = u (C.m.e τ) := by
        ext i j
        simp
      simp only [Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq]
      rw [GlobalTheory.StabProper.unitary_iff_form, hcc]
      intro v w
      have hform := hu (C.m.e τ) v w
      rw [GlobalTheory.StabProper.hermC_eq, GlobalTheory.StabProper.hermC_eq, Equiv.symm_apply_apply] at hform
      exact hform)
  refine ⟨k, hk, ?_⟩
  funext σ
  have hcomp : compAt C.θ (C.m.e.symm σ) (Formalism.L2.Theta.mt T k) = (u σ).map conj := by
    rw [GlobalTheory.StabProper.compAt_eq, ← GlobalTheory.FockCompare.RealAction.infMat_eq, hkτ, Equiv.apply_symm_apply]
  rw [hcomp]
  ext i j
  simp

theorem frame_decomp : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ x ∈ C.X.dom, ∃ a ∈ GinfC T, ∃ b ∈ Bor C.X.Ψ T.rank, x = rmul (C.xB (C.mvB a B)) b := by
  intro D S T C B hB x hx
  obtain ⟨o, b, -, -, hob, -⟩ := GlobalTheory.Ker.exists_orthonormalisation D.host.E T.rank C.X
  obtain ⟨hon, hbB, hxeq, -, -⟩ := hob x hx
  have hz : IsONFr C.X (C.xB B) := GlobalTheory.Ker.ONBasis.isONFr_xB C hB
  have hzdom : C.xB B ∈ C.X.dom := GlobalTheory.Ker.ONBasis.mem_dom C.X hz
  have hdet : ∀ σ, (FD.mat (C.xB B) σ).det ≠ 0 := fun σ => (hzdom σ).1
  obtain ⟨a, ha, hau⟩ := exists_real_point C
    (fun σ => FD.mat (o x) σ * (FD.mat (C.xB B) σ)⁻¹)
    (fun σ v w => isometry_of_gram_eq σ.1 C.X.Gm (FD.mat (o x) σ) (FD.mat (C.xB B) σ) (hdet σ)
      (by rw [hon σ, hz σ]) v w)
  refine ⟨a, ha, b x, hbB, ?_⟩
  have hmove : C.xB (C.mvB a B) = o x := by
    funext σ
    have hσ := congrFun hau σ
    have hstep : FD.mat (C.xB (C.mvB a B)) σ
        = (compAt C.θ (C.m.e.symm σ) (Formalism.L2.Theta.mt T a)).map conj * FD.mat (C.xB B) σ := by
      ext i j
      set_option synthInstance.maxHeartbeats 100000 in
        simp [GlobalTheory.Ker.Ctx.xB, GlobalTheory.Ker.Ctx.mvB, FD.mat, Matrix.mul_apply, map_sum]
    rw [hσ, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet σ)),
      Matrix.mul_one] at hstep
    exact hstep
  rw [hmove]
  exact hxeq

end GlobalTheory.FrameDecomp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaStepSemilocalZetaNeZeroOfReal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvenOnto.ZetaNeProof

variable {D : D7}

theorem coefW_mul_lev {c : Com D} {s s' : PiLocalization₂ D} (p : Step c s s') (m : Measure (WO s.V s'.V))
    (X : Set (WO s.V s'.V)) (φ : PolF D s'.V.rank s.V.rank)
    (hlaw : ∀ κ ∈ s.J, (p.ω (κ, 1)) (p.pt φ) = p.pt φ)
    (b : GA D s.V) (κ : GA D s.V) (hκ : κ ∈ s.J) :
    coefW p.ω m X (p.pt φ) (b * κ) = coefW p.ω m X (p.pt φ) b := by
  have hmul : p.ω (b * κ, 1) = p.ω (b, 1) * p.ω (κ, 1) := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one]
  have hv : p.ω (b * κ, 1) (p.pt φ) = p.ω (b, 1) (p.pt φ) := by
    rw [hmul, Module.End.mul_apply, hlaw κ hκ]
  unfold coefW
  rw [hv]

theorem hgtS_mul_lev {c : Com D} {s : PiLocalization₂ D} (hs : IsSelfDualC s.V s.Λ) (hfin : s.J ≤ GfC s.V)
    (hstab : ∀ k ∈ s.J, ∀ v,
      GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v)
    (a : GL (Fin s.V.rank) (AE D)) (b : GinfC s.V) (κ : GA D s.V) (hκ : κ ∈ s.J) :
    hgtS c s a ((b : GA D s.V) * κ) =
      ∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW s.V a w (GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (b : GA D s.V)) := by
  obtain ⟨h1, h2, h3⟩ := _root_.GlobalTheory.ChainOnto.hgt_one_components D s.V s.Λ hs
  have hκf : κ ∈ GfC s.V := hfin hκ
  unfold hgtS
  have hA : ∀ w, GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w ((b : GA D s.V) * κ) =
      GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (b : GA D s.V) := by
    intro w
    rw [map_mul, h2 κ hκf w, mul_one]
  have hF : ∀ v ∈ c.S, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ v
      (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v ((b : GA D s.V) * κ)) = 1 := by
    intro v _
    rw [map_mul, h3 b b.2 v, one_mul]
    exact h1 v _ (hstab κ hκ v)
  simp only [hA]
  rw [Finset.prod_eq_one hF, mul_one]

theorem zetaNe_of_real : ∀ D : D7, MetEx D → RealZeta D → ZetaNe D := by
  intro D hMet hRZ
  intro c hc k hk s s' hs hs' p hp m X hcov
  obtain ⟨φ, v, hvK, hR⟩ := hRZ c hc k hk s s' hs hs' p hp m X hcov
  have hkm : k ≤ c.m := hk.le
  obtain ⟨ipD, ip, hip⟩ := hMet c hc k hkm s hs
  obtain ⟨⟨hmOff, _, hAsub, mR, hmR, hint⟩, hpet⟩ := GlobalTheory.T.evenThetaChainStage_levelMeasure_peterssonCoefficient D c hc k hkm s hs
  have hlaw : ∀ κ ∈ s.J, (p.ω (κ, 1)) (p.pt φ) = p.pt φ :=
    fun κ hκ => hp.pre.law φ κ hκ 1 s'.J.one_mem
  have hsupp := hp.pre.supp m X hcov φ
  obtain ⟨hz, hzI⟩ := hR mR hmR
  refine ⟨φ, PiTensorProduct.tprod ℂ v, Submodule.subset_span ⟨v, hvK, rfl⟩, ?_⟩
  intro u hu
  have hipu : ip u u ≠ 0 := by
    intro h0
    have := hip.pos u hu
    rw [h0, Complex.zero_re] at this
    exact lt_irrefl _ this
  have hcipu : conj (ip u u) ≠ 0 := (map_ne_zero _).mpr hipu

  have hlawZ : ∀ (b : GinfC s.V), ∀ κ ∈ s.J,
      p.zint m X φ (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) ((b : GA D s.V) * κ) =
        conj (ip u u) * (coefW p.ω m X (p.pt φ) (b : GA D s.V) *
          conj (∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ)) := by
    intro b κ hκ
    unfold Step.zint
    rw [coefW_mul_lev p m X φ hlaw _ κ hκ, hpet ipD ip hip u v b κ hκ]
    simp only [map_mul]
    ring

  have hoff : ∀ g ∈ intOff c s \ s.big,
      p.zint m X φ (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) g = 0 := by
    rintro g ⟨hg, hgA⟩
    unfold Step.zint
    have h0 : coefW p.ω m X (p.pt φ) g = 0 := hsupp g hg hgA
    rw [h0, zero_mul]
  have hzInt : Integrable (fun g : GinfC s.V => coefW p.ω m X (p.pt φ) (g : GA D s.V) *
      conj (∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (g : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ)) mR := by
    by_contra hni
    exact hz (integral_undef hni)
  refine ⟨?_, ?_⟩
  · rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero hmOff hAsub hoff]
    rw [(hint _ _ (hzInt.const_mul (conj (ip u u))) hlawZ).2, integral_const_mul]
    exact mul_ne_zero hcipu hz
  · intro a hmaj hcomp
    obtain ⟨s₁, hs₁, hI⟩ := hzI a hmaj hcomp
    refine ⟨s₁, hs₁, ?_⟩
    refine IntegrableOn.of_forall_diff_eq_zero (s := s.big) ?_ hmOff ?_
    · refine (hint _ _ (hI.const_mul (conj (ip u u))) ?_).1
      intro b κ hκ
      rw [hlawZ b κ hκ, hgtS_mul_lev hs.selfDual hs.fin hs.stab a b κ hκ, mul_assoc]
    · intro g hg
      rw [hoff g hg, zero_mul]

end GlobalTheory.EvenOnto.ZetaNeProof
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAlgebraicDatumNotMatchedZeroByLocalMaps
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

namespace GlobalTheory.SquareAgree


open GlobalTheory.SmallThetaModules in
theorem exists_algD_not_polMatch_zero : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf →
    ∃ Φ ∈ GlobalTheory.SquareAgree.algD G.M' B.ψ B.emb, ¬ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch B G X R Rf 0 Φ := by
  intro F E _ _ _ _ _ σ a a' B G X om om' R Rf h
  classical
  let s : ∀ v, Rf.Pi v := fun v => Rf.p' v (G.M'.vac v)
  have hsph : ∀ v ∉ X.T, Rf.p v (G.M.vac v) = s v := fun v hv => (h.fin.sph v hv).1
  have hs0 : ∀ v ∉ X.T, s v ≠ 0 := fun v hv => by
    rw [← hsph v hv]; exact (h.fin.sph v hv).2
  have hXT : (X.T : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))).Finite := X.T.finite_toSet
  obtain ⟨q, hq⟩ := GlobalTheory.T.weil_model_projection_factorisation σ G.V G.W G.M B.ψ h.triple.geo.hM R.Pi R.p Rf.Pi Rf.p s
    (Filter.eventually_cofinite.2 (hXT.subset fun v hv => by by_contra hn; exact hv (hsph v hn)))
  obtain ⟨q', hq'⟩ := GlobalTheory.T.weil_model_projection_factorisation σ G.V' G.W G.M' B.ψ h.triple.geo.hM' R.Pi R.p' Rf.Pi Rf.p' s
    (Filter.Eventually.of_forall fun v => rfl)
  haveI := h.real.nontriv
  obtain ⟨x, hx⟩ := exists_ne (0 : R.Pi)
  have hx' : x ∈ (G.M'.Pol B.ψ B.emb).map R.p' := by rw [h.real.quot'.onto]; trivial
  obtain ⟨f, hf, hfx⟩ := hx'
  have hloc : ∀ v, ∃ φv, φv ∈ GlobalTheory.WeilM.SB _ ∧ Rf.p' v φv ≠ 0 ∧ (v ∉ X.T → φv = G.M'.vac v) := by
    intro v
    by_cases hv : v ∈ X.T
    · haveI := h.fin.nontriv v
      obtain ⟨y, hy⟩ := exists_ne (0 : Rf.Pi v)
      have hy' : y ∈ (GlobalTheory.WeilM.SB _).map (Rf.p' v) := by rw [h.fin.onto' v]; trivial
      obtain ⟨φv, h1, h2⟩ := hy'
      exact ⟨φv, h1, h2 ▸ hy, fun hn => absurd hv hn⟩
    · exact ⟨G.M'.vac v, (h.triple.geo.hM'.vac v).1, hs0 v hv, fun _ => rfl⟩
  choose φ hφSB hφ0 hφvac using hloc
  have hφev : ∀ᶠ v in Filter.cofinite, φ v = G.M'.vac v :=
    Filter.eventually_cofinite.2 (hXT.subset fun v hv => by by_contra hn; exact hv (hφvac v hn))
  have hΦ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ algD G.M' B.ψ B.emb :=
    Submodule.subset_span ⟨f, φ, hf, hφSB, hφev, rfl⟩
  obtain ⟨l₀, hl₀⟩ := Module.Projective.exists_dual_eq_one ℂ hx
  choose l hl using fun v => Module.Projective.exists_dual_eq_one ℂ (hφ0 v)
  have hls : ∀ v ∉ X.T, l v (s v) = 1 := fun v hv => by
    have := hl v
    rwa [hφvac v hv] at this
  have hadm : {v | l v (s v) ≠ 1}.Finite := hXT.subset fun v hv => by by_contra hn; exact hv (hls v hn)
  obtain ⟨Λ, hΛ⟩ := pureT_sep s (fun v => l v) hadm
  let LL : R.Pi ⊗[ℂ] RTens s →ₗ[ℂ] ℂ := TensorProduct.lift ((LinearMap.mul ℂ ℂ).compl₁₂ l₀ Λ)
  have hLL : ∀ x y, LL (x ⊗ₜ y) = l₀ x * Λ y := fun x y => by simp [LL]
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ, hΦ, ?_⟩
  rintro ⟨T, hT, m, m', fs, φs, fs', φs', hfam, hfam', h0, hΦe, htens⟩
  let LT : (⨂[ℂ] v : T, Rf.Pi v) →ₗ[ℂ] ℂ := PiTensorProduct.dualDistrib (⨂ₜ[ℂ] v : T, l v)
  let Ltot : R.Pi ⊗[ℂ] (⨂[ℂ] v : T, Rf.Pi v) →ₗ[ℂ] ℂ := TensorProduct.lift ((LinearMap.mul ℂ ℂ).compl₁₂ l₀ LT)
  have hLtot : ∀ x y, Ltot (x ⊗ₜ y) = l₀ x * LT y := fun x y => by simp [Ltot]
  have key : ∀ g : ∀ v, Rf.Pi v, (∀ v ∉ T, g v = s v) →
      Λ (pureT s g) = LT (PiTensorProduct.tprod ℂ fun v : T => g v) := by
    intro g hg
    have hr : Formalism.MainNotions.KudlaSiegelWeil.Restr s g := T.finite_toSet.subset fun v hv => by by_contra hn; exact hv (hg v hn)
    rw [hΛ g hr]
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := T) (fun v hv => by
      by_contra hn
      exact hv (by show l v (g v) = 1; rw [hg v hn]; exact hls v fun h' => hn (hT h')))]
    simp only [LT, PiTensorProduct.dualDistrib_apply]
    exact (Finset.prod_coe_sort T fun v => l v (g v)).symm
  have hP : ∀ i, LL (q (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (fs i) (φs i))) =
      Ltot (R.p (fs i) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => Rf.p v (φs i v)) := by
    intro i
    have ev : ∀ᶠ v in Filter.cofinite, φs i v = G.M.vac v :=
      Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by by_contra hn; exact hv ((hfam i).2.2 v hn))
    rw [hq _ _ (hfam i).2.1 ev, hLL, hLtot]
    congr 1
    exact key _ fun v hv => by rw [(hfam i).2.2 v hv]; exact hsph v fun h' => hv (hT h')
  have hP' : ∀ j, LL (q' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (fs' j) (φs' j))) =
      Ltot (R.p' (fs' j) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φs' j v)) := by
    intro j
    have ev : ∀ᶠ v in Filter.cofinite, φs' j v = G.M'.vac v :=
      Filter.eventually_cofinite.2 (T.finite_toSet.subset fun v hv => by by_contra hn; exact hv ((hfam' j).2.2 v hn))
    rw [hq' _ _ (hfam' j).2.1 ev, hLL, hLtot]
    congr 1
    exact key _ fun v hv => by rw [(hfam' j).2.2 v hv]
  have h1 : LL (q' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)) = 1 := by
    rw [hq' _ _ hφSB hφev, hLL, hfx, hl₀, one_mul]
    have hr : Formalism.MainNotions.KudlaSiegelWeil.Restr s (fun v => Rf.p' v (φ v)) :=
      hXT.subset fun v hv => by by_contra hn; exact hv (congrArg (Rf.p' v) (hφvac v hn))
    rw [hΛ _ hr]
    exact finprod_eq_one_of_forall_eq_one fun v => hl v
  have h2 : LL (q' (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ)) =
      Ltot (∑ j, R.p' (fs' j) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => Rf.p' v (φs' j v)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hΦe, map_sum, map_sum, map_sum]
    exact Finset.sum_congr rfl fun j _ => hP' j
  have h3 : Ltot (∑ i, R.p (fs i) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => Rf.p v (φs i v)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← Finset.sum_congr rfl fun i _ => hP i, ← map_sum, ← map_sum, ← h0, map_zero, map_zero]
  rw [htens, ← h2, h1] at h3
  exact one_ne_zero h3

end GlobalTheory.SquareAgree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetRepHeckeElementPrincipalLevel
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

open Formalism.IndefR.Lev GlobalTheory.HeckeParts Formalism.L2.NTheta

theorem GlobalTheory.HeckeDC.exists_rep : ∀ (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → R.IsFam → ∀ (i : Fin D.R.m) (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) (α : GA D (Wc D i))
    (Rc : Finset (GA D (Wc D i))) (e : AE D) (ϖ : 𝓞 D.host.E) (a₀ : GA D (Wc D i)),
    Bridge.SplitOff P (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) → IsHeckeAt (Wc D i) P k α →
    Bridge.IsDC (Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc →
    Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    Formalism.L2.NTheta.IsHeckeElt (Wc D i) e (ϖ : D.host.E) k a₀ →
    ∃ a ∈ Rc, a⁻¹ * a₀ ∈ Lev.levG (Wc D i) (R.βW i) (R.datWp i R.triv) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hL hF i P k α Rc e ϖ a₀ hso hα hRc he hϖ hϖ2 ha₀
  obtain ⟨c, hβ⟩ := hL.βW i
  have hN : ((1 ^ c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [one_pow, Nat.cast_one]
    exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have hoff : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Lev.IsConjPl PP P := by
    intro PP hPP
    have hPP' : PP ∈ R.Pg := hPP.elim id fun h => absurd h (Finset.notMem_empty _)
    have hS : PP ∈ (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) := hF.Sb hPP'
    refine ⟨fun h => hso.2.1 (h ▸ hS), fun h => hso.2.2 PP hS ?_⟩
    rw [Formalism.L2.Col.conjIdeal_asIdeal]
    refine PP.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P).isPrime.ne_top fun a ha => ?_
    obtain ⟨a', ha', e⟩ := h a ha
    rw [Formalism.L2.Col.mem_conjP]
    have : Formalism.L2.Col.cO D.host.E a = a' := RingOfIntegers.ext e.symm
    rwa [this]
  obtain ⟨Lp, -, -, -, hK⟩ := loc_package hβ (L := R.datWp i R.triv) ⟨hso.1, hN, hoff⟩ he
  obtain ⟨e', ϖ', he', h1', h2', hαe'⟩ := hα
  have hee : e' = e := idem_unique (Wc D i) he he'
  rw [hee] at hαe'
  obtain ⟨-, -, hloc⟩ := GlobalTheory.SplitPlace.split_local (Wc D i) P e he
  obtain ⟨x, hx, y, hy, hxy⟩ := ((hloc ϖ' h1' h2').2 k α hαe').2 ϖ a₀ hϖ hϖ2 ha₀
  obtain ⟨a, ⟨haR, haK⟩, -⟩ := hRc.2 a₀ ⟨⟨x, ((hK x).1 hx).1⟩, ⟨y, ((hK y).1 hy).1⟩, hxy⟩
  exact ⟨a, haR, haK⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivHeckeKernelSchemePointsHeckeKernels
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

namespace GlobalTheory.HeckeEx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {P : Ideal (𝓞 E)} {p i : ℕ}

theorem exists_carried (Z : KerScheme Xo P p i) {k : Type} [Field k] [IsAlgClosed k] (w : Sp k ⟶ Z.Hk)
    (y : Sp k ⟶ Xo.X) (hw : w ≫ Z.π₁ = y) :
    ∃ C : Subgroup (Over.mk y ⟶ Xo.univ.t.G), Xo.univ.t.HeckeKer (Over.mk y) Dw P p i C ∧
      ∀ C', Z.Carries w y C' ↔ C' = C := by
  subst hw
  obtain ⟨C₀, hC₀, hk⟩ := Z.hecke k w
  obtain ⟨ρ, e₀⟩ := GlobalTheory.HkSetPull.exists_equiv Z.m₁.cart (Over.mk w)
  have hh : ∀ (u : Over.mk w ⟶ Z.o₁.t.G) (v : Over.mk (w ≫ Z.π₁) ⟶ Xo.univ.t.G),
      v.left = u.left ≫ Z.m₁.toSABMap.φ → (u ∈ C₀ ↔ v ∈ Subgroup.comap ρ.symm.toMonoidHom C₀) := fun u v e => by
    rw [show v = ρ u from Over.OverMorphism.ext (e.trans (e₀ u).symm)]
    show _ ↔ ρ.symm (ρ u) ∈ C₀
    rw [ρ.symm_apply_apply]
  refine ⟨Subgroup.comap ρ.symm.toMonoidHom C₀,
    (GlobalTheory.HkSetPull.heckeKer_iff Dw P p i Z.m₁.toSABMap (Over.mk w) C₀ _ hh).1 hk, fun C' => ⟨fun h => ?_, ?_⟩⟩
  · ext v
    obtain ⟨u, rfl⟩ := ρ.surjective v
    exact (h.2 u _ (e₀ u)).symm.trans ((hC₀ u).symm.trans (hh u _ (e₀ u)))
  · rintro rfl
    exact ⟨rfl, fun u v e => (hC₀ u).symm.trans (hh u v e)⟩

theorem exists_equiv_carries : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : KerScheme Xo P p i), admitted l P p → ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Xo.X), ∃ e : {w : Sp k ⟶ Z.Hk // w ≫ Z.π₁ = y} ≃ {C : Subgroup (Over.mk y ⟶ Xo.univ.t.G) // Xo.univ.t.HeckeKer (Over.mk y) Dw P p i C}, ∀ w C, Z.Carries w.1 y C ↔ C = (e w).1 := by
  intro E _ _ _ H Dw l Xo P p i Z hA k _ _ y
  choose c hc hcc using fun w : {w : Sp k ⟶ Z.Hk // w ≫ Z.π₁ = y} => exists_carried Z w.1 y w.2
  refine ⟨Equiv.ofBijective (fun w => ⟨c w, hc w⟩) ⟨fun w w' e => ?_, fun C => ?_⟩, hcc⟩
  · exact Subtype.ext (((GlobalTheory.kerScheme_points E H Dw l Xo P p i Z hA).1 k y (c w) (hc w)).unique
      ((hcc w _).2 rfl) ((hcc w' _).2 (congrArg Subtype.val e)))
  · obtain ⟨z, hz, -⟩ := (GlobalTheory.kerScheme_points E H Dw l Xo P p i Z hA).1 k y C.1 C.2
    exact ⟨⟨z, hz.1⟩, Subtype.ext ((hcc ⟨z, hz.1⟩ _).1 hz).symm⟩

end GlobalTheory.HeckeEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRigidifiedThetaIsoBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaTraceBC

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeEx

theorem exists_isRigIso_baseChange : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {T Ω : Type} [CommRing T] [CommRing Ω] (χ : T →+* Ω) {x x' : Sp T ⟶ Xo.X} {x₁ x₁' : Sp Ω ⟶ Xo.X} {Ψ : Gx x ⟶ Gx x'} {Ψ₁ : Gx x₁ ⟶ Gx x₁'} {pm : Gx x₁ ⟶ Gx x} {pm' : Gx x₁' ⟶ Gx x'} {k : ℤ} {β : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP Ψ k)}, IsCan χ pm → IsCan χ pm' → Ψ₁ ≫ pm' = pm ≫ Ψ → Ψ₁ ≫ (fst (Over.mk x₁') Xo.univ.t.G).left = (fst (Over.mk x₁) Xo.univ.t.G).left → IsRigIso Xo.univ.t.G Xo.univ.t.PP Ψ k β → ∃ β₁ : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP Ψ₁ k), IsRigIso Xo.univ.t.G Xo.univ.t.PP Ψ₁ k β₁ ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x₁) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → val β₁ r z J = val β (r ≫ pm) z J := by
  intro E _ _ _ H Dw l Xo T Ω _ _ χ x x' x₁ x₁' Ψ Ψ₁ pm pm' k β hc hc' hΨ h0 hβ
  let σ : (Over.mk x₁ : Over Xo.X) ⟶ Over.mk x := Over.homMk (spMap χ) hc.1.symm
  let σ' : (Over.mk x₁' : Over Xo.X) ⟶ Over.mk x' := Over.homMk (spMap χ) hc'.1.symm
  have epm : pm = (σ ▷ Xo.univ.t.G).left := GlobalTheory.HeckeFrCompare.gx_ext
    (by rw [hc.2.2, ← Over.comp_left, whiskerRight_fst]; rfl) (by rw [hc.2.1, ← Over.comp_left, whiskerRight_snd])
  have epm' : pm' = (σ' ▷ Xo.univ.t.G).left := GlobalTheory.HeckeFrCompare.gx_ext
    (by rw [hc'.2.2, ← Over.comp_left, whiskerRight_fst]; rfl) (by rw [hc'.2.1, ← Over.comp_left, whiskerRight_snd])
  obtain ⟨β₁, h₁, hv⟩ := isRigIso_pull (σ := σ) (σ' := σ') rfl (by rw [← epm, ← epm']; exact hΨ) h0 hβ
  exact ⟨β₁, h₁, fun Z r z J hJ => by rw [hv r z hJ, ← epm]⟩

end GlobalTheory.HeckeEx
end
end

