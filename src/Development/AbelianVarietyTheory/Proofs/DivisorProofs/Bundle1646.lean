module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1575
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1550
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1637
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1454
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1604
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdelicUnitaryTranslateStandardLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1619
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1624
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApprox
section
noncomputable section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdRead

variable {D : D7}

def toE (D : D7) : Formalism.MainNotions.StandardLatticesGL3.AE D →+* EAf D :=
  ((Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toAlgHom.toRingHom).comp
    (GlobalTheory.BotFormula.toAfE D).toRingHom

def matE {a : ℕ} (k : Formalism.MainNotions.StandardLatticesGL3.GA D a) : Matrix (Fin a) (Fin a) (EAf D) :=
  ((k : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)).map (toE D)

def IsIntE {a d : ℕ} (z : Matrix (Fin d) (Fin a) D.host.E) : Prop := ∀ i j, ∃ b : 𝓞 D.host.E, z i j = (b : D.host.E)

def Approx (𝔪 : Ideal (𝓞 D.host.E)) (o : ℕ) {a d : ℕ} (k : Formalism.MainNotions.StandardLatticesGL3.GA D a) (z : Matrix (Fin d) (Fin a) D.host.E) : Prop :=
  ∀ i j, (z.map (inc D) - (unitBlock D o a d).map (inc D) *
    (((k : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
      Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) i j ∈ hatId D 𝔪

def GoodMod (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)) : Prop :=
  ∃ (SS : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ), IsIdemSum e SS ∧ (∀ w ∈ SS, 0 < c w) ∧
    𝔪 = ∏ w ∈ SS, w.asIdeal ^ c w ∧ IsCoprime 𝔪 D.host.𝔟

def KillsCong (ν : (AE D)ˣ →* Circle) (𝔪 : Ideal (𝓞 D.host.E)) : Prop :=
  ∀ x y, IsFinIdl x y → IntU D y → (y : Formalism.MainNotions.StandardLatticesGL3.AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → ν x = 1

def cosInd (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)) {S T : HSp D} {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
    (z : Matrix (Fin d) (Fin a) D.host.E) (t : WO S T) : ℂ :=
  if IsHalf e t ∧ ∀ i j, InId 𝔪 (toEAf D (t i j) - toEAf D e * eToEAf D (z (Fin.cast hT i) (Fin.cast hS j))) then 1 else 0

def cosV (δ : ℂ) (𝔪 : Ideal (𝓞 D.host.E)) {a d : ℕ} (z : Matrix (Fin d) (Fin a) D.host.E) (G : VC D a d → ℂ) : VC D a d → ℂ :=
  ((Real.sqrt ((Ideal.absNorm 𝔪 : ℝ) ^ (a * d)) : ℂ))⁻¹ •
    Wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ z)
      (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) G)

theorem cosV_smul (δ : ℂ) (𝔪 : Ideal (𝓞 D.host.E)) {a d : ℕ} (z : Matrix (Fin d) (Fin a) D.host.E) (c : ℂ)
    (G : VC D a d → ℂ) : cosV δ 𝔪 z (c • G) = c • cosV δ 𝔪 z G := by
  have hU : ∀ (x : VC D a d) (F : VC D a d → ℂ),
      Formalism.MainNotions.TaylorLogMetric.U D (tor0 D ⊤ δ) x (c • F) = c • Formalism.MainNotions.TaylorLogMetric.U D (tor0 D ⊤ δ) x F := fun x F => by
    funext y
    simp only [Formalism.MainNotions.TaylorLogMetric.U, Pi.smul_apply, smul_eq_mul, mul_assoc]
  have hI : ∀ A B : AddSubgroup (VC D a d), Iop D (tor0 D ⊤ δ) A B (c • G) = c • Iop D (tor0 D ⊤ δ) A B G := fun A B => by
    funext y
    simp only [Iop, hU, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
    rw [← mul_finsum, mul_left_comm]
  funext y
  simp only [cosV, Wd, hI, hU, Pi.smul_apply, smul_eq_mul]
  ring

theorem GoodMod.ne_bot {e : AE D} {𝔪 : Ideal (𝓞 D.host.E)} (h : GoodMod e 𝔪) : 𝔪 ≠ ⊥ := by
  obtain ⟨SS, c, -, -, rfl, -⟩ := h
  exact Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ w.ne_bot

theorem exists_approx {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) (o : ℕ) {a : ℕ} (d : ℕ) {k : Formalism.MainNotions.StandardLatticesGL3.GA D a}
    (hk : k ∈ intG D a) : ∃ z : Matrix (Fin d) (Fin a) D.host.E, IsIntE z ∧ Approx 𝔪 o k z := by
  have hn : 0 < Ideal.absNorm 𝔪 := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 h𝔪)
  have hI : ∀ i j, ((unitBlock D o a d).map (inc D) *
      (((k : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
        Matrix (Fin a) (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D))) i j ∈ OhE D := by
    intro i j
    rw [Matrix.mul_apply]
    refine sum_mem fun l _ => mul_mem ?_ (((GlobalTheory.NormSum.mem_intG k).1 hk) l j).2
    by_cases h : i.1 = o + l.1
    · simp [unitBlock, h]
    · simp [unitBlock, h]
  choose b w hw hb using fun i j => GlobalTheory.CongApprox.exists_int_approx D _ hn _ (hI i j)
  refine ⟨Matrix.of fun i j => (b i j : D.host.E), fun i j => ⟨b i j, rfl⟩, fun i j => ?_⟩
  rw [Matrix.sub_apply, hb i j]
  have e : (Matrix.of fun i j => (b i j : D.host.E)).map (inc D) i j -
      (inc D (b i j : D.host.E) + (Ideal.absNorm 𝔪 : Formalism.MainNotions.StandardLatticesGL3.AE D) * w i j) =
      inc D (((Ideal.absNorm 𝔪 : 𝓞 D.host.E)) : D.host.E) * (-w i j) := by
    simp
  rw [e]
  exact AddSubgroup.subset_closure ⟨_, Ideal.absNorm_mem 𝔪, _, neg_mem (hw i j), rfl⟩

end GlobalTheory.StdRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFdPosFin
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

noncomputable section

namespace GlobalTheory.ThetaSchurUnitF


open scoped TensorProduct Matrix in
open NumberField IsDedekindDomain in
open MeasureTheory in
theorem _root_.GlobalTheory.ThetaSchurUnitF.exists_fd_pos_fin {F E : Type} [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
    {ψ : AddChar (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ℂ} (hψ : ∀ a, ‖ψ a‖ = 1) {f : _root_.Formalism.IndefR.DatumF.WOF F E nS nT → ℂ}
    (hf : _root_.Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ ψ f)
    {y : _root_.Formalism.IndefR.DatumF.WOF F E nS nT} (hy : f y ≠ 0) :
    ∃ (μ : Measure (_root_.Formalism.IndefR.DatumF.WOF F E nS nT)) (𝓕 : Set (_root_.Formalism.IndefR.DatumF.WOF F E nS nT)), μ.IsAddHaarMeasure ∧
      IsAddFundamentalDomain (_root_.Formalism.IndefR.DatumF.ratLF F E nS nT) 𝓕 μ ∧
      (∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) ≠ 0 ∧ (∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ) ≠ ⊤ := by
  obtain ⟨h1, h2, h3, h4, h5, K, hK, hcov⟩ := _root_.GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  haveI : BorelSpace (_root_.Formalism.IndefR.DatumF.WOF F E nS nT) := ⟨rfl⟩
  obtain ⟨⟨μ, 𝓕, hμ, h𝓕, -⟩, hN⟩ :=
    _root_.GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact _ (_root_.Formalism.IndefR.DatumF.ratLF F E nS nT) K hK hcov
  have hper : ∀ γ ∈ _root_.Formalism.IndefR.DatumF.ratLF F E nS nT, ∀ w, ‖f (γ + w)‖ = ‖f w‖ := by
    intro γ hγ w
    have h := _root_.GlobalTheory.ThetaSchurF.prod_periodic hψ hf hf hγ w
    simp only [← starRingEnd_apply, RCLike.mul_conj] at h
    have h' : ‖f (γ + w)‖ ^ 2 = ‖f w‖ ^ 2 := by exact_mod_cast h
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h'
  obtain ⟨N, hN⟩ := hN f hf.cont hper
  obtain ⟨-, htop, hl, -⟩ := hN μ 𝓕 hμ h𝓕
  haveI : Countable (_root_.Formalism.IndefR.DatumF.ratLF F E nS nT) :=
    (TopologicalSpace.separableSpace_iff_countable).1 inferInstance
  refine ⟨μ, 𝓕, hμ, h𝓕, ?_, ?_⟩
  · intro hz
    have hall : ∫⁻ w, ‖f w‖ₑ ^ 2 ∂μ = 0 := by
      rw [h𝓕.lintegral_eq_tsum']
      refine ENNReal.tsum_eq_zero.2 fun γ => ?_
      rw [← hz]
      refine lintegral_congr fun w => ?_
      rw [AddSubgroup.vadd_def, vadd_eq_add, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
        hper _ (-γ).2 w]
    have hcont : Continuous fun w => ‖f w‖ₑ ^ 2 :=
      (ENNReal.continuous_pow 2).comp (continuous_enorm.comp hf.cont)
    have hae := (lintegral_eq_zero_iff hcont.measurable).1 hall
    have heq := (Continuous.ae_eq_iff_eq μ hcont continuous_const).1 hae
    have hfy := congrFun heq y
    simp [hy] at hfy
  · rw [hl]
    exact ENNReal.mul_ne_top htop (by simp)

end GlobalTheory.ThetaSchurUnitF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicEmbeddingStandardUnitaryGroup
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FinEmbStd

variable {D : D7}

theorem eq_of_finHom (V : HSp D) {g g' : GA D V} (hg : g ∈ GfC V) (hg' : g' ∈ GfC V)
    (h : ∀ i j, GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (((finHom V g : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) i j) =
      GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (((finHom V g' : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) i j)) :
    g = g' := by
  refine GlobalTheory.UnitarySplit.ga_ext V ?_ ?_
  · rw [MonoidHom.mem_ker.1 hg, MonoidHom.mem_ker.1 hg']
  · exact Units.ext (Matrix.ext fun i j => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective (h i j))

theorem toFinE_inc (e : D.host.E) :
    GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.inc D e) = algebraMap D.host.E _ e := by
  change GlobalTheory.LFun.toFinAd ℚ D.host.E (1 ⊗ₜ[ℚ] e) = _
  rw [GlobalTheory.LFun.toFinAd_tmul, map_one, one_mul]

theorem finAdEquiv_inclR (e : D.host.E) :
    GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (inclR (F := D.host.F) (Af D.host.F) e) = algebraMap D.host.E _ e := by
  change GlobalTheory.LFun.toFinAd D.host.F D.host.E (1 ⊗ₜ[D.host.F] e) = _
  rw [GlobalTheory.LFun.toFinAd_tmul, map_one, one_mul]

theorem toFinE_toAfE_symm (y : TensorProduct D.host.F (Af D.host.F) D.host.E) :
    GlobalTheory.BotFormula.toFinE D ((GlobalTheory.BotFormula.toAfE D).symm y) = GlobalTheory.LFun.finAdEquiv D.host.F D.host.E y := by
  simp [GlobalTheory.BotFormula.toAfE]

theorem finAdEquiv_finHom_rat (V : HSp D) (γ : GA D V) (u : GL (Fin V.rank) D.host.E)
    (hγ : Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) u = matHom V γ) (i j : Fin V.rank) :
    GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (((finHom V γ : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) i j) =
      algebraMap D.host.E _ ((u : Matrix (Fin V.rank) (Fin V.rank) D.host.E) i j) := by
  have : ((finHom V γ : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) i j =
      inclR (F := D.host.F) (Af D.host.F) ((u : Matrix (Fin V.rank) (Fin V.rank) D.host.E) i j) := by
    change (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E))
      (((matHom V γ : GL _ _) : Matrix (Fin V.rank) (Fin V.rank) _) i j) = _
    rw [← hγ]
    change (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E))
      (inclR (F := D.host.F) (AF D.host.F) ((u : Matrix (Fin V.rank) (Fin V.rank) D.host.E) i j)) = _
    simp [inclR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  rw [this, finAdEquiv_inclR]

theorem exists_std_of_GfC (V : HSp D) (hG : V.gram = 1) (g : GA D V) (hg : g ∈ GfC V) :
    ∃ x : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank, IsFinPt V g x := by
  let M : Matrix (Fin V.rank) (Fin V.rank) (TensorProduct D.host.F (Af D.host.F) D.host.E) := (finHom V g).val
  have hM : Formalism.UG.cT (sigR (Af D.host.F) D.sp.cm.sig) M * M = 1 := by
    have h2 := GlobalTheory.UnitarySplit.finHom_mem V g
    change Formalism.UG.cT _ M * JR (Af D.host.F) V.gram * M = JR (Af D.host.F) V.gram at h2
    rw [hG, JR, Matrix.map_one _ (map_zero _) (map_one _), mul_one] at h2
    exact h2
  have hu : Formalism.UG.cT (Formalism.MainNotions.StandardLatticesGL3.sgA D) (M.map (GlobalTheory.BotFormula.toAfE D).symm.toRingHom) *
      M.map (GlobalTheory.BotFormula.toAfE D).symm.toRingHom = 1 := by
    refine GlobalTheory.DefU.ClassFin.unitary_map _ (sigR (Af D.host.F) D.sp.cm.sig) _ ?_ _ hM
    intro y
    apply (GlobalTheory.BotFormula.toAfE D).injective
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, RingEquiv.apply_symm_apply, GlobalTheory.BotFormula.toAfE_sgA]
  let x0 : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D) := Formalism.UG.bc (GlobalTheory.BotFormula.toAfE D).symm.toRingHom (finHom V g)
  have hx0 : x0 ∈ Formalism.MainNotions.StandardLatticesGL3.GA D V.rank := by
    change Formalism.UG.cT _ (M.map (GlobalTheory.BotFormula.toAfE D).symm.toRingHom) *
      (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map _ * (M.map (GlobalTheory.BotFormula.toAfE D).symm.toRingHom) = _
    rw [Matrix.map_one _ (map_zero _) (map_one _), mul_one]
    exact hu
  refine ⟨⟨x0, hx0⟩, hg, rfl, fun i j => ?_⟩
  exact (toFinE_toAfE_symm _).symm

theorem exists_GQ_of_rat (V : HSp D) (hG : V.gram = 1) (x : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank) (hxr : x ∈ ratG D V.rank)
    (g : GA D V) (hg : ∀ i j,
      GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (((finHom V g : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) i j) =
        GlobalTheory.BotFormula.toFinE D (((x : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin V.rank) (Fin V.rank) _) i j)) :
    ∃ γ ∈ GQ V, finHom V γ = finHom V g := by
  rw [GlobalTheory.NormSum.ratG_eq_ratPts] at hxr
  obtain ⟨u, hu, hu'⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hxr)
  let U : Matrix (Fin V.rank) (Fin V.rank) D.host.E := u.val
  have huV : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) U * V.gram * U = V.gram := by
    have h : Formalism.UG.cT (D.host.conj : D.host.E →+* D.host.E) U * 1 * U = 1 := hu
    have hc : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) U = Formalism.UG.cT (D.host.conj : D.host.E →+* D.host.E) U := by
      exact Matrix.ext fun i j => Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D _
    rw [hG, hc]; exact h
  have hcT : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (U.map (inclR (F := D.host.F) (AF D.host.F))) =
      (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) U).map (inclR (F := D.host.F) (AF D.host.F)) := by
    ext i j
    simp [Formalism.UG.cT, sigR, inclR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  have hmem : Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) u ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    change Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (U.map (inclR (F := D.host.F) (AF D.host.F))) *
      JR (AF D.host.F) V.gram * U.map (inclR (F := D.host.F) (AF D.host.F)) = JR (AF D.host.F) V.gram
    rw [hcT, JR, ← Matrix.map_mul, ← Matrix.map_mul, huV]
  let γ : GA D V := ⟨Formalism.UG.bc (inclR (F := D.host.F) (AF D.host.F)) u, hmem⟩
  refine ⟨γ, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨u, huV, rfl⟩), ?_⟩
  apply Units.ext
  refine Matrix.ext fun i j => ?_
  apply (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).injective
  rw [finAdEquiv_finHom_rat V γ u rfl i j, hg i j, ← toFinE_inc]
  congr 1
  rw [← hu']
  rfl

theorem exists_finEmb : ∀ {D : D7} (V : HSp D) (n : ℕ), V.gram = 1 → V.rank = n → ∃ ι : Formalism.MainNotions.StandardLatticesGL3.GA D n →* GA D V,
    (∀ x, IsFinPt V (ι x) x) ∧ Function.Injective ι ∧ ι.range = GfC V ∧
      ∀ x, (∃ γ ∈ GQ V, finHom V γ = finHom V (ι x)) ↔ x ∈ ratG D n := by
  intro D V n hG hr
  subst hr
  have key : ∀ (g : GA D V) (x : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank), IsFinPt V g x ↔ g ∈ GfC V ∧ ∀ i j,
      GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (((finHom V g : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) i j) =
        GlobalTheory.BotFormula.toFinE D (((x : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin V.rank) (Fin V.rank) _) i j) := by
    intro g x
    constructor
    · rintro ⟨h1, e, h2⟩
      exact ⟨h1, fun i j => by simpa using h2 i j⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, rfl, fun i j => by simpa using h2 i j⟩
  choose f hf using fun x : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank => GlobalTheory.BotFormula.exists_isFinPt_of_gram_one V hG x rfl
  have uniq : ∀ g x, IsFinPt V g x → g = f x := by
    intro g x hg
    obtain ⟨g1, g2⟩ := (key g x).1 hg
    obtain ⟨f1, f2⟩ := (key _ x).1 (hf x)
    exact eq_of_finHom V g1 f1 fun i j => (g2 i j).trans (f2 i j).symm
  have hfx : ∀ x, ∀ i j, GlobalTheory.LFun.finAdEquiv D.host.F D.host.E
      (((finHom V (f x) : GL (Fin V.rank) _) : Matrix (Fin V.rank) (Fin V.rank) _) i j) =
        GlobalTheory.BotFormula.toFinE D (((x : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin V.rank) (Fin V.rank) _) i j) :=
    fun x => ((key _ x).1 (hf x)).2
  let ι : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank →* GA D V :=
    { toFun := f
      map_one' := (uniq 1 1 ((key 1 1).2 ⟨one_mem _, fun i j => by
          simp [Matrix.one_apply, apply_ite]; split_ifs <;> simp_all⟩)).symm
      map_mul' := fun x y => (uniq _ _ ((key _ _).2 ⟨mul_mem ((key _ x).1 (hf x)).1 ((key _ y).1 (hf y)).1, fun i j => by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_mul, Units.val_mul, Subgroup.coe_mul, Matrix.mul_apply, map_sum, hfx]⟩)).symm }
  refine ⟨ι, hf, ?_, ?_, ?_⟩
  · intro x y hxy
    change f x = f y at hxy
    apply Subtype.ext; apply Units.ext; ext i j
    apply (GlobalTheory.BotFormula.toFinE D).injective
    rw [← hfx x, ← hfx y, hxy]
  · apply le_antisymm
    · rintro _ ⟨x, rfl⟩; exact ((key _ x).1 (hf x)).1
    · intro g hg
      obtain ⟨x, hx⟩ := exists_std_of_GfC V hG g hg
      exact ⟨x, (uniq g x hx).symm⟩
  · intro x
    constructor
    · rintro ⟨γ, hγ, he⟩
      change finHom V γ = finHom V (f x) at he
      obtain ⟨u, -, hu'⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
      rw [GlobalTheory.NormSum.mem_ratG]
      refine ⟨(u : Matrix (Fin V.rank) (Fin V.rank) D.host.E), ?_⟩
      refine Matrix.ext fun i j => ?_
      apply (GlobalTheory.BotFormula.toFinE D).injective
      rw [Matrix.map_apply, toFinE_inc, ← hfx x, ← he, finAdEquiv_finHom_rat V γ u hu' i j]
    · intro hxr
      exact exists_GQ_of_rat V hG x hxr (f x) (hfx x)

end GlobalTheory.FinEmbStd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryMovesSelfDualLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GenusTranslate

open GlobalTheory.AdLat GlobalTheory.UnRep

theorem hatL_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (z : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    z ∈ Formalism.L2.Herm.hatL L ↔
      (fun i => (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).symm (z i)) ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) := by
  refine ⟨GlobalTheory.PrincInLevel.swap_symm_mem_hat L z, fun h => ?_⟩
  have := GlobalTheory.PrincInLevel.swap_mem_hatL L _ h
  simpa using this


set_option maxHeartbeats 2000000 in
theorem exists_move_colLat : ∀ (D : D7) (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * V.gram * fr.1 = 1 → IsSelfDualC V Λ →
    ∃ x : GA D V, x ∈ GfC V ∧ ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) (colLat fr) ↔
      (Formalism.IndefR.Lev.finE V x).1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  intro D V fr Λ hfr hΛ
  have hU := _root_.GlobalTheory.FramePull.unimod_comap_frame D V fr Λ hfr hΛ
  have hT : (Formalism.L2.Pj.GenLat.mk (Λ.comap ((Matrix.mulVecLin fr.1).restrictScalars (𝓞 D.host.E)))).TrivAt 1 :=
    ⟨0, Nat.coprime_zero_left 1 |>.2 rfl, by simp, by simp⟩
  have hgen : ∃ g : GL (Fin V.rank) (GlobalTheory.AdLat.RA D.host.F D.host.E), GlobalTheory.UnRep.IsUnA (GlobalTheory.Member.cF D) 1 g.1 ∧
      ∀ z, z ∈ GlobalTheory.AdLat.hat D.host.F ((Λ.comap ((Matrix.mulVecLin fr.1).restrictScalars (𝓞 D.host.E)) :
        Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E)) ↔
      (g⁻¹).1 *ᵥ z ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.Pj.stdLat D.host.E V.rank : Set (Fin V.rank → D.host.E)) := by
    obtain ⟨g, hgU, hgL, -⟩ := GlobalTheory.AdelTranslate.exists_adelic_translate D.host.E (Formalism.L2.Pj.hostOfRecord D) V.rank 1 _
      one_pos hU hT
    have hstd := GlobalTheory.UnRep.StdInhab.main D.host.E (Formalism.L2.Pj.hostOfRecord D) V.rank
    have hfg := hstd.2.2.1
    have hsp := hstd.2.2.2.1
    have hL := GlobalTheory.AdLat.exists_lattice_latOf (maximalRealSubfield D.host.E) D.host.E V.rank
      (Formalism.L2.Pj.stdLat D.host.E V.rank) g hfg hsp
    obtain ⟨Λ'', hL''⟩ := hL
    have h1 := hL''.1
    have h4 := hL''.2.2.2
    have e : Λ'' = Λ.comap ((Matrix.mulVecLin fr.1).restrictScalars (𝓞 D.host.E)) :=
      SetLike.coe_injective (h1.trans hgL.symm)
    refine ⟨g, by
      have hc : GlobalTheory.Member.cF D = IsCMField.complexConj D.host.E := AlgEquiv.ext fun _ => rfl
      rw [hc]; exact hgU, fun z => ?_⟩
    rw [← e, ← SetLike.mem_coe, h4]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rwa [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    · intro hz
      exact ⟨_, hz, by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]⟩
  obtain ⟨g, hgU, hg'⟩ := hgen
  have hfm1 : GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1 * GlobalTheory.UnRep.fm D.host.F fr.1 = 1 := by
    rw [← GlobalTheory.UnRep.FullReps.fm_mul, Units.inv_mul, GlobalTheory.UnRep.FullReps.fm_one]
  have hfm2 : GlobalTheory.UnRep.fm D.host.F fr.1 * GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1 = 1 := by
    rw [← GlobalTheory.UnRep.FullReps.fm_mul, Units.mul_inv, GlobalTheory.UnRep.FullReps.fm_one]
  obtain ⟨U, hU1, hU2⟩ : ∃ U : GL (Fin V.rank) (GlobalTheory.AdLat.RA D.host.F D.host.E),
      U.1 = GlobalTheory.UnRep.fm D.host.F fr.1 ∧ (U⁻¹).1 = GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1 :=
    ⟨⟨GlobalTheory.UnRep.fm D.host.F fr.1, GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1, hfm2, hfm1⟩, rfl, rfl⟩
  have hX := _root_.GlobalTheory.UnitConjFrame.isUnA_frame_conj D V fr g.1 hfr hgU
  rw [← hU1, ← hU2, ← Units.val_mul, ← Units.val_mul] at hX
  obtain ⟨X, hXe⟩ : ∃ X : GL (Fin V.rank) (GlobalTheory.AdLat.RA D.host.F D.host.E), X = U * g * U⁻¹ := ⟨_, rfl⟩
  rw [← hXe] at hX
  have hlift := (GlobalTheory.UnitarySplit.real_finite_split D V).2.2.2.1 X hX
  obtain ⟨x, hx, hxX⟩ := hlift
  have key : ∀ w : Fin V.rank → GlobalTheory.AdLat.RA D.host.F D.host.E,
      w ∈ GlobalTheory.AdLat.hat D.host.F (colLat fr : Set (Fin V.rank → D.host.E)) ↔
        X.1 *ᵥ w ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin V.rank → D.host.E)) := by
    intro w
    have ew : GlobalTheory.UnRep.fm D.host.F fr.1 *ᵥ (GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1 *ᵥ w) = w := by
      rw [Matrix.mulVec_mulVec, ← GlobalTheory.UnRep.FullReps.fm_mul, Units.mul_inv, GlobalTheory.UnRep.FullReps.fm_one, Matrix.one_mulVec]
    have h1 := _root_.GlobalTheory.HatPullback.main D.host.F D.host.E V.rank fr (colLat fr) (GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1 *ᵥ w)
    rw [ew, _root_.GlobalTheory.ColStd.colLat_comap_eq_stdLat] at h1
    have h2 := _root_.GlobalTheory.HatPullback.main D.host.F D.host.E V.rank fr Λ (g.1 *ᵥ (GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1 *ᵥ w))
    have hgg : (g⁻¹).1 *ᵥ (g.1 *ᵥ (GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1 *ᵥ w)) = GlobalTheory.UnRep.fm D.host.F (fr⁻¹).1 *ᵥ w := by
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    rw [hg', hgg] at h2
    rw [h1, hXe, Units.val_mul, Units.val_mul, hU1, hU2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h2]
  refine ⟨x, hx, fun v => ?_⟩
  have hfin : (fun i => (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E).symm
      (((Formalism.IndefR.Lev.finE V x).1 *ᵥ v) i)) =
      X.1 *ᵥ fun i => (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E).symm (v i) := by
    have hfe : Formalism.IndefR.Lev.finE V x = Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) X := by rw [← hxX]; rfl
    rw [hfe]
    funext i
    rw [AlgEquiv.symm_apply_eq]
    have hv : ⇑(Formalism.IndefR.Lev.swapAE D) ∘ (fun j =>
        (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E).symm (v j)) = v :=
      funext fun j => (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E).apply_symm_apply (v j)
    have hm := RingHom.map_mulVec (Formalism.IndefR.Lev.swapAE D) X.1
      (fun j => (Algebra.TensorProduct.comm D.host.F (FiniteAdeleRing (𝓞 D.host.F) D.host.F) D.host.E).symm (v j)) i
    rw [hv] at hm
    exact hm.symm
  rw [hatL_iff, hatL_iff, hfin]
  exact key _

end GlobalTheory.GenusTranslate
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarAdelicIntegralFormulaStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_haar_adelic_integral_formula : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ᶠ v in cofinite, PsiUnr ψ v) →
    (∀ v : Pl (F := F), ∃ x, psiLoc ψ v x ≠ 1) → ∀ (κ : Type) [Fintype κ],
    ∃ μ : Measure (κ → AF F), μ.IsAddRightInvariant ∧
      ∀ (g : (κ → mixedEmbedding.mixedSpace F) → ℂ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), Continuous g →
        Integrable g (measI F κ) → (∀ v, φ v ∈ SB (κ → Fv F v)) → (∀ᶠ v in cofinite, φ v = GlobalTheory.SympChange.indO v) →
        Integrable (fun x => g (fun i => evI F (x i)) * ∏ᶠ v, φ v (fun i => evFin F v (x i))) μ ∧
        ∫ x, g (fun i => evI F (x i)) * ∏ᶠ v, φ v (fun i => evFin F v (x i)) ∂μ =
          (∫ z, g z ∂(measI F κ)) * ∏ᶠ v, ∫ z, φ v z ∂(Measure.pi fun _ : κ => measV ψ v) := by
  first | exact @GlobalTheory.WeylMeas.exists_meas | exact GlobalTheory.WeylMeas.exists_meas | (intros; apply GlobalTheory.WeylMeas.exists_meas <;> assumption)
end

