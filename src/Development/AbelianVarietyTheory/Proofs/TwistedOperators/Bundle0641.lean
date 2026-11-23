module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0003
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0197
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0443
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutomorphicCuspFormsHermitianSpaceSignTwist
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0631
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnArrowKernelRealEqDetCharMulFockKernel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0442
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemSplit
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0595
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0565
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0624
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0458

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeightedAverageHaar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section
open scoped ComplexOrder
open GlobalTheory.ClassRegroup GlobalTheory.DefiniteClassAvg GlobalTheory.DefiniteClassReal
open GlobalTheory.Grid (neg sgn ofSgn)

namespace GlobalTheory.RowTest.BottomClassSumNeg

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}

theorem theta (hX : IsBottomTri W i j X) (t : T) (P : PolF D WW.rank A.rank) :
    IsThetaFunO W.ψ (neg A) WW (pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) :=
  GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := neg A) (T := WW) hX.is.isVac.1 hX.is.isVac.2.inf (fun τ => -X.rA.s τ) X.rA.B X.rW.s X.rW.B
    (GlobalTheory.ConstRatio.theta_f hX.is t).1 P

theorem ker_eq (t : T) (P : PolF D WW.rank A.rank) (h : GA D WW) (g : GA D A) :
    X.ker W.ψ W.θ t P h g = thetaKO ((X.ω t).toSgn true) ((ofSgn true A).symm g) h
      (pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) := by
  show thetaKO (X.ω t) g h _ = (X.ω t) ((ofSgn true A) ((ofSgn true A).symm g), h) _ 0
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem ker_left (hX : IsBottomTri W i j X) (t : T) (P : PolF D WW.rank A.rank) (h : GA D WW) :
    ∀ γ ∈ GQ A, ∀ g, X.ker W.ψ W.θ t P h (γ * g) = X.ker W.ψ W.θ t P h g := by
  intro γ hγ g
  have hK := GlobalTheory.thetaKO_rat_left_and_eigen_right W.ψ (neg A) WW _ _ _ (hX.is.weil t) _ (theta hX t P)
  rw [ker_eq, ker_eq, map_mul]
  have := hK.1 _ ((GlobalTheory.SgnIdent.mem_GQ_sgn true A _).2 (by rwa [MulEquiv.apply_symm_apply])) 1 (one_mem _)
    ((ofSgn true A).symm g) h
  rwa [one_mul] at this

theorem ker_cont (hX : IsBottomTri W i j X) (t : T) (P : PolF D WW.rank A.rank) (h : GA D WW) (x : GA D A) :
    Continuous fun k : GinfC A => X.ker W.ψ W.θ t P h (x * k) := by
  have hW := hX.is.weil t
  have hF := theta hX t P
  simp_rw [ker_eq]
  exact (hW.om_cont _ hF 0).comp (((GlobalTheory.Grid.continuous_ofSgn_symm true A).comp
    (continuous_const.mul continuous_subtype_val)).prodMk continuous_const)

end GlobalTheory.RowTest.BottomClassSumNeg

namespace GlobalTheory.RowTest.BottomClassSumNeg

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}

theorem level_all [Finite T] (t₀ : T) (hX : IsBottomTri W i j X) :
    ∃ K : Subgroup (GL (Fin A.rank) (Lev.EAf D)), GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel A K ∧
      ∀ (t : T) (P : PolF D WW.rank A.rank) (h : GA D WW), ∀ k ∈ Lev.levA A K, ∀ g,
        X.ker W.ψ W.θ t P h (g * k) = X.ker W.ψ W.θ t P h g := by
  choose K hK hinv using _root_.GlobalTheory.SrcLevel.exists_level_ker hX
  refine ⟨⨅ t, K t, ⟨?_, ?_⟩, fun t P h k hk g => hinv t P h k ?_ g⟩
  · have e : (((⨅ t, K t).comap (Lev.finE A) : Subgroup (GA D A)) : Set (GA D A)) =
        ⋂ t, (((K t).comap (Lev.finE A) : Subgroup (GA D A)) : Set (GA D A)) := by
      ext x; simp [Subgroup.mem_iInf]
    rw [e]
    exact isOpen_iInter_of_finite fun t => (hK t).1
  · have hcl : IsClosed ((((⨅ t, K t).comap (Lev.finE A) : Subgroup (GA D A)) : Set (GA D A))) := by
      have e : (((⨅ t, K t).comap (Lev.finE A) : Subgroup (GA D A)) : Set (GA D A)) =
          ⋂ t, (((K t).comap (Lev.finE A) : Subgroup (GA D A)) : Set (GA D A)) := by
        ext x; simp [Subgroup.mem_iInf]
      rw [e]
      exact isClosed_iInter fun t => Subgroup.isClosed_of_isOpen _ (hK t).1
    have e2 : ((Lev.levA A (⨅ t, K t) : Subgroup (GA D A)) : Set (GA D A)) =
        (Lev.levA A (K t₀) : Set (GA D A)) ∩ (((⨅ t, K t).comap (Lev.finE A) : Subgroup (GA D A)) : Set (GA D A)) := by
      ext x
      simp only [SetLike.mem_coe, Set.mem_inter_iff, Lev.mem_levA, Subgroup.mem_comap]
      exact ⟨fun ⟨h1, h2⟩ => ⟨⟨h1, (Subgroup.mem_iInf.1 h2) t₀⟩, h2⟩, fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩⟩
    rw [e2]
    exact (hK t₀).2.inter_right hcl
  · obtain ⟨hk1, hk2⟩ := Lev.mem_levA.1 hk
    exact Lev.mem_levA.2 ⟨hk1, (Subgroup.mem_iInf.1 hk2) t⟩

end GlobalTheory.RowTest.BottomClassSumNeg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpAttChrMu
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowRealEq

variable {D : D7} {T : Type} {L : LevCh D T}

theorem hasInfExp_attChr_mu {μ0 : T} (hL : L.Is μ0) (t : T) {j : ℕ} (hj : j < D.R.m) (n : ℕ) (τ : D.what₂.Tau) :
    HasInfExp D (Formalism.IndefR.Lift.attChr (L.mu t (j + 1)) L.eta n) τ
      (-(D.hc τ).e ⟨j, hj⟩ - if Odd n then 1 / 2 else 0) := by
  have h0 := GlobalTheory.ColKer.mu_exp hL t j hj τ
  have heta : HasInfExp D L.eta τ (1 / 2) :=
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta
      (GlobalTheory.Chain.StepVac.hasInfQ_tau (a := fun _ => 1 / 2) ⟨_, fun _ => by norm_num, L.C.isEta.inf⟩) τ
  unfold Formalism.IndefR.Lift.attChr
  split_ifs
  · rw [sub_eq_add_neg]
    exact GlobalTheory.Chain.StepVac.hasInfExp_mul h0 (GlobalTheory.Chain.StepVac.hasInfExp_inv heta)
  · simpa using h0

theorem realEqAt : Big fun ch => RealEqAt ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ => ?_⟩⟩
  have hL := hS.core.lev
  intro t t' j hj
  refine ⟨fun a ha b hb f hf => ?_, fun a ha b hb f hf => ?_⟩
  · exact GlobalTheory.RealEqWeil.weilDatum_realEq D _ _ _ _ _ _ _ _ _
      (ch.W.om_is (.top t j) (show j + 1 ≤ D.R.m by omega)) (ch.W.om_is (.top t' j) (show j + 1 ≤ D.R.m by omega))
      (fun τ => ⟨_, hasInfExp_attChr_mu hL t hj _ τ, hasInfExp_attChr_mu hL t' hj _ τ⟩)
      (fun τ => ⟨_, hasInfExp_attChr_mu hL t hj _ τ, hasInfExp_attChr_mu hL t' hj _ τ⟩) a ha b hb f hf
  · exact GlobalTheory.RealEqWeil.weilDatum_realEq D _ _ _ _ _ _ _ _ _
      (ch.W.om_is (.mu t D.R.m j) (show D.R.m ≤ D.R.m ∧ j + 1 ≤ D.R.m by omega))
      (ch.W.om_is (.mu t' D.R.m j) (show D.R.m ≤ D.R.m ∧ j + 1 ≤ D.R.m by omega))
      (fun τ => ⟨_, hasInfExp_attChr_mu hL t hj _ τ, hasInfExp_attChr_mu hL t' hj _ τ⟩)
      (fun τ => ⟨_, hasInfExp_attChr_mu hL t hj _ τ, hasInfExp_attChr_mu hL t' hj _ τ⟩) a ha b hb f hf

end GlobalTheory.RowRealEq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLocalLatticeMatricesInv
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.RowVal

theorem hasLoc_inv : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T) (B : Frames G) {j : ℕ}
    (hj : j ≤ D.R.m) (x : GA D (G.V (.grid D.R.m j)))
    (g : ∀ w : locPl G t, GL (Fin ((locGrid G t w.1).rank (D.R.m, j))) (Kw w.1)), HasLoc t B hj x g → HasLoc t B hj x⁻¹ (fun w => (g w)⁻¹) := by
  intro D T L sc G t B j hj x g ⟨e, he, hs, hg⟩
  refine ⟨e, he, ?_, fun w => by rw [map_inv, map_inv, hg w]⟩
  intro i k
  set c := e + Formalism.L2.Theta.cA D e
  have hinv : Formalism.L2.Theta.mt _ x⁻¹ * Formalism.L2.Theta.mt _ x = 1 := by
    simp [Formalism.L2.Theta.mt, map_inv]
  have key : Formalism.L2.Theta.mt _ x⁻¹ - 1 = -(Formalism.L2.Theta.mt _ x⁻¹ * (Formalism.L2.Theta.mt _ x - 1)) := by
    rw [Matrix.mul_sub, hinv, Matrix.mul_one]; abel
  rw [key, Matrix.neg_apply, Matrix.mul_apply, mul_neg, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_left_comm, hs l k]

end GlobalTheory.RowVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLocalLatticeMatricesMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RowVal

theorem isIdemSum_unique {D : D7} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {e e' : AE D}
    (he : Formalism.IndefR.Datum.IsIdemSum e P) (he' : Formalism.IndefR.Datum.IsIdemSum e' P) : e = e' := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  obtain ⟨⟨es', hes', rfl⟩, -⟩ := he'
  exact Finset.sum_congr rfl fun PP hPP =>
    Formalism.IndefR.Fin.idemAt_eq_split (Formalism.IndefR.Fin.idemAt_split (hes PP hPP)) (hes PP hPP) (hes' PP hPP)

theorem suppAt_mul_of {D : D7} {V : HSp D} {e : AE D} {a b : GA D V} (ha : SuppAt e V a) (hb : SuppAt e V b) :
    SuppAt e V (a * b) := by
  intro i j
  have hab : mt V (a * b) = mt V a * mt V b := rfl
  have hm : mt V (a * b) - 1 = (mt V a - 1) * mt V b + (mt V b - 1) := by
    rw [hab]; noncomm_ring
  rw [hm, Matrix.add_apply, Matrix.mul_apply, mul_add, Finset.mul_sum, hb i j]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_assoc, ha i k]

theorem hasLoc_mul : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (t : T) (B : Frames G) {j : ℕ}
    (hj : j ≤ D.R.m) (x y : GA D (G.V (.grid D.R.m j)))
    (g g' : ∀ w : locPl G t, GL (Fin ((locGrid G t w.1).rank (D.R.m, j))) (Kw w.1)), HasLoc t B hj x g → HasLoc t B hj y g' → HasLoc t B hj (x * y) (fun w => g w * g' w) := by
  intro D T L sc G t B j hj x y g g' ⟨e, he, hs, hg⟩ ⟨e', he', hs', hg'⟩
  rw [isIdemSum_unique he' he] at hs'
  refine ⟨e, he, suppAt_mul_of hs hs', fun w => ?_⟩
  rw [map_mul, map_mul, hg w, hg' w]

end GlobalTheory.RowVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InvAAMultipleDepthLatticeMapsCompletion
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.RowAAUnit

variable {D : D7}

theorem idem_smul_latA {S : HSp D} {L : Lat S} {P : GlobalTheory.FinPl.Pl D → Prop} (v : GlobalTheory.FinPl.Pl D)
    {z : Fin S.rank → AE D} (hz : z ∈ latA S L P) : GlobalTheory.FinPlLoc.idem D (· = v) • z ∈ latA S L (· = v) := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hαi, hα, a, ha, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨GlobalTheory.FinPlLoc.ePl D (· = v) * α, fun w => ?_, fun w hw => ?_, a, ha, x, hx, ?_⟩
    · rw [map_mul]; exact mul_mem (GlobalTheory.FinPlLoc.ePl_int _ w) (hαi w)
    · rw [map_mul, GlobalTheory.FinPlLoc.evalV_ePl, if_neg hw, zero_mul]
    · funext i
      rw [Pi.smul_apply, smul_eq_mul]
      unfold GlobalTheory.FinPlLoc.idem
      rw [Algebra.TensorProduct.tmul_mul_tmul, ← GlobalTheory.FinPlLoc.pairA_mul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg y _ h => rw [smul_neg]; exact neg_mem h

theorem smul_mulVec_mem_latV : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (M : WO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))), M ∈ latRow G (2 * ρ + 1) → ∀ v : GlobalTheory.FinPl.Pl D, ∀ y ∈ latV _ (G.Λ (.grid (2 * ρ + 2) 0)) (· = v), ∀ s ∈ GlobalTheory.SeeSaw.idV (D.host.AA⁻¹) v, s • (M *ᵥ y) ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) := by
  intro D hOff T L μ0 hL sc G W Mv hM F hF ρ h M hMr v y hy s hs
  have hV : IsSelfDualC (G.V (.grid (2 * ρ + 2) 0)) (G.Λ (.grid (2 * ρ + 2) 0)) :=
    (G.isV (X := .grid (2 * ρ + 2) 0) ⟨h, Nat.zero_le _⟩ (fun j hj => by injection hj with h1 h2; omega)).sd
  have hO : M ∈ latO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0)) (G.Λ (.grid (2 * ρ + 2) 0) : Set _)
      (G.Λ (.grid (2 * ρ + 1) 0) : Set _) (fun _ => True) :=
    GlobalTheory.RowLoc.mem_latO_negSp.1 hMr.1
  have hyT : y ∈ latV _ (G.Λ (.grid (2 * ρ + 2) 0)) (fun _ => True) := GlobalTheory.FinPl.PsiUnit.latV_mono trivial hy
  have hA : M *ᵥ y ∈ latA _ (G.Λ (.grid (2 * ρ + 1) 0)) (fun _ => True) := GlobalTheory.FinPl.LatMem.latO_maps hV hO hyT
  have hy' : GlobalTheory.FinPlLoc.idem D (· = v) • y = y := by
    funext i
    rw [Pi.smul_apply, smul_eq_mul]
    exact (GlobalTheory.FinPlLoc.mem_idAt_iff _ _).1 (GlobalTheory.FinPlLoc.latV_idAt hy i)
  have hAv : M *ᵥ y ∈ latA _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) := by
    rw [← hy', Matrix.mulVec_smul]
    exact idem_smul_latA v hA
  exact (((GlobalTheory.SeeSaw.idV_props D W.ψ W.ψ_std v).2.2.2.2.2.2 _ _ _).1 hAv).2 s hs

end GlobalTheory.AscFin.RowAAUnit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIteratedInvariantIntegralLinearAndCongr
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowVal.NIterLin

section
variable {G : Type} [Group G] [MeasurableSpace G] {R : Subgroup G} {μR : Measure R} {μG : Measure G}

theorem quot_sum {I : Type} (S : Finset I) (x : I → ℂ) (F : I → G → ℂ) (z : I → ℂ)
    (hF : ∀ n ∈ S, IsQuotIntL1 μR μG (F n) (z n)) :
    IsQuotIntL1 μR μG (fun g => ∑ n ∈ S, x n * F n g) (∑ n ∈ S, x n * z n) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have e : (fun g : G => ∑ n ∈ (∅ : Finset I), x n * F n g) = 0 := by funext g; simp
    rw [e, Finset.sum_empty]
    exact IsQuotIntL1.zero
  | insert a s ha ih =>
    have h1 := (hF a (Finset.mem_insert_self _ _)).smul (x a)
    have h2 := ih (fun n hn => hF n (Finset.mem_insert_of_mem hn))
    have h3 := h1.add h2
    rw [Finset.sum_insert ha]
    convert h3 using 1
    funext g
    simp [Finset.sum_insert ha]
end

variable {ι : Type} [DecidableEq ι] {H : ι → Type} [∀ i, Group (H i)] [∀ i, MeasurableSpace (H i)]
  {R : ∀ i, Subgroup (H i)} (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i))

theorem lin (l : List ι) : ∀ (h : ∀ i, H i) (I : Type) (S : Finset I) (x z : I → ℂ) (q : I → (∀ i, H i) → ℂ),
    (∀ n ∈ S, NIter ρ μ (q n) l h (z n)) → NIter ρ μ (fun g => ∑ n ∈ S, x n * q n g) l h (∑ n ∈ S, x n * z n) := by
  induction l with
  | nil =>
    intro h I S x z q hq
    simp only [NIter] at hq ⊢
    exact Finset.sum_congr rfl fun n hn => by rw [hq n hn]
  | cons i l ih =>
    intro h I S x z q hq
    classical
    simp only [NIter] at hq ⊢
    let F : I → H i → ℂ := fun n => if hn : n ∈ S then Classical.choose (hq n hn) else 0
    have hF : ∀ n ∈ S, IsQuotIntL1 (ρ i) (μ i) (F n) (z n) ∧ ∀ g, NIter ρ μ (q n) l (Function.update h i g) (F n g) := by
      intro n hn
      simp only [F, dif_pos hn]
      exact Classical.choose_spec (hq n hn)
    refine ⟨fun g => ∑ n ∈ S, x n * F n g, quot_sum S x F z fun n hn => (hF n hn).1, fun g => ?_⟩
    exact ih (Function.update h i g) I S x (fun n => F n g) q fun n hn => (hF n hn).2 g

theorem congr (l : List ι) : ∀ (h : ∀ i, H i) (q q' : (∀ i, H i) → ℂ) (z : ℂ),
    (∀ g : ∀ i, H i, (∀ i, i ∉ l → g i = h i) → q g = q' g) → NIter ρ μ q l h z → NIter ρ μ q' l h z := by
  induction l with
  | nil =>
    intro h q q' z hq hz
    simp only [NIter] at hz ⊢
    rw [hz]
    exact hq h fun _ _ => rfl
  | cons i l ih =>
    intro h q q' z hq hz
    simp only [NIter] at hz ⊢
    obtain ⟨f, hf, hf'⟩ := hz
    refine ⟨f, hf, fun g => ih (Function.update h i g) q q' (f g) (fun g' hg' => hq g' fun j hj => ?_) (hf' g)⟩
    have hji : j ≠ i := fun e => hj (e ▸ List.mem_cons_self ..)
    have hjl : j ∉ l := fun e => hj (List.mem_cons_of_mem _ e)
    rw [hg' j hjl, Function.update_of_ne hji]

end GlobalTheory.RowVal.NIterLin

theorem GlobalTheory.RowVal.niter_lin_congr : ∀ (ι : Type) [DecidableEq ι] (H : ι → Type) [∀ i, Group (H i)] [∀ i, MeasurableSpace (H i)] (R : ∀ i, Subgroup (H i)) (ρ : ∀ i, Measure (R i)) (μ : ∀ i, Measure (H i)) (l : List ι) (h : ∀ i, H i), (∀ (I : Type) (S : Finset I) (x z : I → ℂ) (q : I → (∀ i, H i) → ℂ), (∀ n ∈ S, NIter ρ μ (q n) l h (z n)) → NIter ρ μ (fun g => ∑ n ∈ S, x n * q n g) l h (∑ n ∈ S, x n * z n)) ∧ ∀ q q' z, (∀ g : ∀ i, H i, (∀ i, i ∉ l → g i = h i) → q g = q' g) → NIter ρ μ q l h z → NIter ρ μ q' l h z := by
  intro ι _ H _ _ R ρ μ l h
  exact ⟨fun I S x z q hq => GlobalTheory.RowVal.NIterLin.lin ρ μ l h I S x z q hq,
    fun q q' z hq hz => GlobalTheory.RowVal.NIterLin.congr ρ μ l h q q' z hq hz⟩

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRowFlagTiltUnique
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.TiltUnique

theorem tilt_unique : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {j : ℕ} (hj : j < D.R.m)
    (δ δ' : GA D (G.V (.grid D.R.m j))), IsTilt G j δ → IsTilt G j δ' → δ = δ' := by
  intro D T L sc G j hj δ δ' h h'
  rcases Nat.even_or_odd j with he | ho
  · rw [h.2.1 he, h'.2.1 he]
  · obtain ⟨a, ha⟩ := D.R.m_even
    obtain ⟨b, hb⟩ := ho
    have h₂ : D.R.m - 1 - j = 2 * ((D.R.m - 1 - j) / 2) := by omega
    obtain ⟨x1, x2, x3⟩ := h.2.2 _ hj h₂
    obtain ⟨y1, y2, y3⟩ := h'.2.2 _ hj h₂
    have k := (rowJac G j hj _ h₂).sum_eq_one
    have e0 : HMul.hMul (mt _ δ) (rowJac G j hj _ h₂).j0 = HMul.hMul (mt _ δ') (rowJac G j hj _ h₂).j0 := x1.trans y1.symm
    have eX : HMul.hMul (mt _ δ) (rowJac G j hj _ h₂).jX = HMul.hMul (mt _ δ') (rowJac G j hj _ h₂).jX := x2.trans y2.symm
    have eY : HMul.hMul (mt _ δ) (rowJac G j hj _ h₂).jY = HMul.hMul (mt _ δ') (rowJac G j hj _ h₂).jY := x3.trans y3.symm
    have hm : mt _ δ = mt _ δ' := by
      rw [← Matrix.mul_one (mt _ δ), ← Matrix.mul_one (mt _ δ')]
      rw [← k]
      simp only [Matrix.mul_add, ← Matrix.mul_assoc, e0, eX, eY]
    exact Subtype.ext (Units.ext hm)

end GlobalTheory.TiltUnique
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevJGridSuccIndep
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowVal

theorem levJ_grid_succ_indep {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t t' : T) (i j : ℕ) :
    levJ G t (.grid (i + 1) (j + 1)) = levJ G t' (.grid (i + 1) (j + 1)) := rfl

theorem levJ_top_indep {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t t' : T) (j : ℕ) :
    levJ G t (.top j) = levJ G t' (.top j) := by
  cases j <;> rfl

theorem vol_row_top_indep : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t t' : T) (M M' : Vol G), M.Is t → M'.Is t' → (∀ j, 1 ≤ j → j ≤ D.R.m → M.ν (.grid D.R.m j) = M'.ν (.grid D.R.m j)) ∧ ∀ j, j ≤ D.R.m → M.ν (.top j) = M'.ν (.top j) := by
  intro D T L sc G t t' M M' hM hM'
  refine ⟨fun j hj1 hjm => ?_, fun j hj => ?_⟩
  · obtain ⟨i, hi⟩ : ∃ i, D.R.m = i + 1 := ⟨D.R.m - 1, by omega⟩
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hX : levJ G t (.grid D.R.m (j' + 1)) = levJ G t' (.grid D.R.m (j' + 1)) := by
      rw [hi]; exact levJ_grid_succ_indep G t t' i j'
    have h1 := hM.vtx (.grid D.R.m (j' + 1)) ⟨le_rfl, hjm⟩
    have h2 := hM'.vtx (.grid D.R.m (j' + 1)) ⟨le_rfl, hjm⟩
    rw [← hX] at h2
    exact GlobalTheory.HaarNorm.vol_nu_eq_of_isAt M M' _ _ h1 h2
  · have h1 := hM.vtx (.top j) hj
    have h2 := hM'.vtx (.top j) hj
    rw [← levJ_top_indep G t t' j] at h2
    exact GlobalTheory.HaarNorm.vol_nu_eq_of_isAt M M' _ _ h1 h2

end GlobalTheory.RowVal
end

