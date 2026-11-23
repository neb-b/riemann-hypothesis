module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0221
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0190
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.FundamentalContinuity.AdelicIsomorphismStatement
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompProjAnisotropicAnisotropicEmbedding

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledBasisSkewColumnMatrixGramInverse
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

section General

variable {E : Type} [Field E] [StarRing E] {n : ℕ}

theorem gram_fromCols_smul (G : Matrix (Fin (n + n)) (Fin (n + n)) E) (e e' : Matrix (Fin (n + n)) (Fin n) E) (μ : E)
    (hμ : star μ = -μ) (h₁ : eᴴ * G * e = 0) (h₂ : e'ᴴ * G * e' = 0) (h₃ : e'ᴴ * G * e = 1) (h₄ : eᴴ * G * e' = 1) :
    ((Matrix.fromCols e (μ • e')).submatrix id finSumFinEquiv.symm)ᴴ * G *
        (Matrix.fromCols e (μ • e')).submatrix id finSumFinEquiv.symm = μ • blk4 0 1 (-1) 0 := by
  have h : (Matrix.fromCols e (μ • e'))ᴴ * G * Matrix.fromCols e (μ • e') = μ • Matrix.fromBlocks 0 1 (-1) 0 := by
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols,
      Matrix.conjTranspose_smul, hμ, Matrix.fromBlocks_smul]
    simp only [Matrix.smul_mul, Matrix.mul_smul, h₁, h₂, h₃, h₄, smul_zero, smul_neg, neg_smul, Matrix.neg_mul, neg_zero]
  ext i j
  exact congrFun (congrFun h (finSumFinEquiv.symm i)) (finSumFinEquiv.symm j)

theorem fromRows_mul_fromCols_smul (G : Matrix (Fin (n + n)) (Fin (n + n)) E) (e e' : Matrix (Fin (n + n)) (Fin n) E)
    (μ : E) (hμ : μ ≠ 0) (h₁ : eᴴ * G * e = 0) (h₂ : e'ᴴ * G * e' = 0) (h₃ : e'ᴴ * G * e = 1) (h₄ : eᴴ * G * e' = 1) :
    (Matrix.fromRows (e'ᴴ * G) (μ⁻¹ • (eᴴ * G))).submatrix finSumFinEquiv.symm id *
        (Matrix.fromCols e (μ • e')).submatrix id finSumFinEquiv.symm = (1 : Matrix (Fin (n + n)) (Fin (n + n)) E) := by
  have h : Matrix.fromRows (e'ᴴ * G) (μ⁻¹ • (eᴴ * G)) * Matrix.fromCols e (μ • e') = 1 := by
    rw [Matrix.fromRows_mul_fromCols]
    simp only [Matrix.smul_mul, Matrix.mul_smul, h₁, h₂, h₃, h₄, smul_zero, smul_smul, mul_inv_cancel₀ hμ,
      one_smul, Matrix.fromBlocks_one]
  rw [← Matrix.submatrix_one_equiv (finSumFinEquiv (m := n) (n := n)).symm, ← h]
  rfl

end General

theorem Tm_gram_inv : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → (Tm A μ)ᴴ * (dblSp A).gram * Tm A μ = μ • Jst D A.rank ∧ IsUnit (Tm A μ).det ∧ (Tm A μ)⁻¹ = (Matrix.fromRows (dblDec A).qX (μ⁻¹ • (dblDec A).qY)).submatrix finSumFinEquiv.symm id := by
  intro D A μ hμ
  have h₄ : (dblDec A).eᴴ * (dblSp A).gram * (dblDec A).e' = 1 := by
    have := congrArg Matrix.conjTranspose (dblDec A).e'e
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, gram_conjTranspose,
      Matrix.conjTranspose_one, ← Matrix.mul_assoc] at this
  have hi := fromRows_mul_fromCols_smul (n := A.rank) (dblSp A).gram (dblDec A).e (dblDec A).e' μ hμ.1
    (dblDec A).ee (dblDec A).e'e' (dblDec A).e'e h₄
  exact ⟨gram_fromCols_smul (n := A.rank) (dblSp A).gram (dblDec A).e (dblDec A).e' μ hμ.2
    (dblDec A).ee (dblDec A).e'e' (dblDec A).e'e h₄, Matrix.isUnit_det_of_left_inverse hi, Matrix.inv_eq_left_inv hi⟩

end GlobalTheory.StdUnn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledPairThetaFunctionEqZeroOfSchrodingerEqZer
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

namespace GlobalTheory.Core.Rk.SchwInj

theorem sch_heisO_extY {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (A B : HSp D)
    {ν : Measure (WO A B)} {𝓨 : Set (WO A B)} (hν : IsCovolOne (ratL B A) ν 𝓨) {f : WO (dblSp A) B → ℂ}
    (hf : IsThetaFunO ψ (dblSp A) B f) (x y : Mx D B.rank A.rank) :
    sch ψ A B ν 𝓨 (heisO ψ (dblSp A) B ((dblDec A).extY B y) f) x =
      ψ (symplO (dblSp A) B ((dblDec A).extX B x) ((dblDec A).extY B y)) * sch ψ A B ν 𝓨 f x :=
  congrFun ((GlobalTheory.HeisMixSource.heis_mixS D ψ hψ (dblSp A) (zeroSp D) B A.rank (dblDec A) ⟨ν, 𝓨, hν⟩ f hf).2.1 x y) 0

theorem exists_extX_add_extY {D : D7} (A B : HSp D) (w : WO (dblSp A) B) :
    ∃ x y : Mx D B.rank A.rank, w = (dblDec A).extX B x + (dblDec A).extY B y := by
  obtain ⟨⟨x, w₀, y⟩, rfl⟩ := ((dblDec A).coordS B).symm.surjective w
  have hw : w₀ = 0 := Matrix.ext fun _ j => Fin.elim0 j
  subst hw
  refine ⟨x, y, ?_⟩
  show (dblDec A).extX B x + (dblDec A).ext0 B 0 + (dblDec A).extY B y = _
  rw [map_zero, add_zero]

theorem eq_zero_of_sch_eq_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D) (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f → sch ψ A B ν 𝓨 f = 0 → f = 0 := by
  intro D ψ hψ A B ν 𝓨 hν f hf hs
  funext w
  obtain ⟨x, y, rfl⟩ := exists_extX_add_extY A B w
  have hg := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf ((dblDec A).extY B y)
  have hsum := (_root_.GlobalTheory.Core.Rk.SchPeriod.theta_eq_sum_sch D ψ hψ A B ν 𝓨 hν _ hg x).2
  simp only [sch_heisO_extY hψ A B hν hf, hs, Pi.zero_apply, mul_zero] at hsum
  have h0 : ψ (symplOH (dblSp A) B ((dblDec A).extX B x) ((dblDec A).extY B y)) *
      f ((dblDec A).extX B x + (dblDec A).extY B y) = 0 := hsum.unique hasSum_zero
  refine (mul_eq_zero.1 h0).resolve_left fun h => ?_
  have h1 := ψ.map_add_eq_mul (symplOH (dblSp A) B ((dblDec A).extX B x) ((dblDec A).extY B y))
    (-symplOH (dblSp A) B ((dblDec A).extX B x) ((dblDec A).extY B y))
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at h1
  exact one_ne_zero h1

end GlobalTheory.Core.Rk.SchwInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingNegligibleOrbitUnfoldedIntegralEqZero
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.DblOrbit

theorem integral_eq_zero_of_not_open : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)) (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ s : ℂ, ∀ φ ∈ degPS V a μ s, ∀ γ ∈ GQ (dblSp V), (¬ ∃ δ ∈ GQ V, γ * (io V (δ, 1))⁻¹ ∈ siegel V) → ∀ f₁ f₂ : GA D V → ℂ, Continuous f₁ → Continuous f₂ → GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) f₁ → IsCuspFun V f₁ → ∀ (g₂ : GA D V) (Γ' : Subgroup (GA D V)), (∀ x, x ∈ Γ' ↔ x ∈ GQ V ∧ γ * io V (x, 1) * γ⁻¹ ∈ siegel V) → ∀ m : Measure (GA D V), m.IsHaarMeasure → ∀ 𝓖 : Set (GA D V), IsFundamentalDomain Γ' 𝓖 m → IntegrableOn (fun h => GlobalTheory.Eis.dblIntegrand V μ (fun x => φ (γ * x)) f₁ f₂ (h, g₂)) 𝓖 m → ∫ h in 𝓖, GlobalTheory.Eis.dblIntegrand V μ (fun x => φ (γ * x)) f₁ f₂ (h, g₂) ∂m = 0 := by
  intro D V a μ hμ s φ hφ γ hγ hnot f₁ f₂ hf₁ hf₂ hleft hcusp g₂ Γ' hΓ' m hm 𝓖 h𝓖 hint
  haveI := hm
  obtain ⟨r, C, hC, hN, hnorm⟩ := _root_.GlobalTheory.Core.Rk.Dich.offOpen D V γ hγ hnot
  set N := NA (frameFlag hC) with hNdef
  have hNI : ∀ n, n ∈ N ↔ n ∈ NI V C := fun n => by rw [hNdef, NA_frameFlag hC]
  have hφ' := (mem_degPS V a).1 hφ
  set K : GA D V → ℂ := fun h => φ (γ * io V (h, g₂)) * f₂ g₂ * ((μ (detA V g₂) : ℂ))⁻¹ with hK
  set F : GA D V → ℂ := fun h => conj (f₁ h) with hF
  have hEq : (fun h => GlobalTheory.Eis.dblIntegrand V μ (fun x => φ (γ * x)) f₁ f₂ (h, g₂)) = fun h => K h * F h := by
    funext h; simp only [GlobalTheory.Eis.dblIntegrand, hK, hF]; ring
  rw [hEq] at hint ⊢
  have hΓ'le : ∀ x ∈ Γ', x ∈ GQ V := fun x hx => ((hΓ' x).1 hx).1
  have hΓc : Countable Γ' := by
    refine Function.Injective.countable (f := fun x : Γ' => (⟨x, hΓ'le x x.2⟩ : GQ V)) ?_
    intro x y hxy; exact Subtype.ext (by simpa using congrArg Subtype.val hxy)
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
  have hNc : IsClosed (N : Set (GA D V)) := IsoFlag.isClosed_unip _ D.sp.cm _
  have hnormN : ∀ δ ∈ Γ', ∀ n ∈ N, δ * n * δ⁻¹ ∈ N := by
    intro δ hδ n hn
    obtain ⟨h1, h2⟩ := (hΓ' δ).1 hδ
    exact (hNI _).2 (hnorm δ h1 h2 n ((hNI n).1 hn))
  have hsub : Γ'.subgroupOf N = (GQ V).subgroupOf N := by
    ext n
    simp only [Subgroup.mem_subgroupOf]
    refine ⟨fun h => hΓ'le _ h, fun h => (hΓ' _).2 ⟨h, ?_⟩⟩
    obtain ⟨p, hp, -⟩ := hN n ((hNI n).1 n.2)
    rw [hp, mul_inv_cancel_right]; exact p.2
  let κ : Measure N := Measure.haar
  let 𝓝 : Set N := stdDom ((GQ V).subgroupOf N)
  have hcc : Cocompact (GQ V) N := cocompact_single _
  have h𝓝 : IsFundamentalDomain ((GQ V).subgroupOf N) 𝓝 κ := isFundamentalDomain_stdDom _ _
  have h𝓝' : IsFundamentalDomain (Γ'.subgroupOf N) 𝓝 κ := by rw [hsub]; exact h𝓝
  have h𝓝t : κ 𝓝 ≠ ⊤ := hcc.measure_ne_top h𝓝
  have hKc : Continuous K :=
    ((hφ'.2.1.comp (continuous_const.mul ((continuous_io V).comp (continuous_id.prodMk continuous_const)))).mul
      continuous_const).mul continuous_const
  have hFc : Continuous F := Complex.continuous_conj.comp hf₁
  have hKN : ∀ n ∈ N, ∀ h, K (n * h) = K h := by
    intro n hn h
    obtain ⟨p, hp, hp1⟩ := hN n ((hNI n).1 hn)
    have e : io V (n * h, g₂) = io V (n, 1) * io V (h, g₂) := by rw [← map_mul]; simp
    simp only [hK]
    rw [e, ← mul_assoc, hp, mul_assoc (p : GA D (dblSp V)) γ, hφ'.1, hp1]
    simp
  have hKΓ : ∀ δ ∈ Γ', ∀ h, K (δ * h) = K h := by
    intro δ hδ h
    obtain ⟨h1, h2⟩ := (hΓ' δ).1 hδ
    have hq : γ * io V (δ, 1) * γ⁻¹ ∈ siegelQ V :=
      Subgroup.mem_inf.2 ⟨h2, (GQ (dblSp V)).mul_mem ((GQ _).mul_mem hγ (io_mem_GQ V h1 (one_mem _)))
        ((GQ _).inv_mem hγ)⟩
    have e : γ * io V (δ * h, g₂) = (γ * io V (δ, 1) * γ⁻¹) * (γ * io V (h, g₂)) := by
      rw [show ((δ * h, g₂) : GA D V × GA D V) = (δ, 1) * (h, g₂) by simp, map_mul]; group
    simp only [hK]
    rw [e, apply_siegelQ_mul V a hμ hφ hq]
  have hFΓ : ∀ δ ∈ Γ', ∀ h, F (δ * h) = F h := by
    intro δ hδ h; simp only [hF]; rw [hleft δ (hΓ'le δ hδ) h]
  have h0 : ∀ h, ∫ n in 𝓝, F ((n : GA D V) * h) ∂κ = 0 := by
    intro h
    have hc : constTerm (frameFlag hC) f₁ = 0 := (isCuspFun_iff hleft).1 hcusp _ _
    have h1 : constTermOn (GQ V) N f₁ h = 0 := congrFun hc h
    have h2 := (hcc.constTermOn_eq_zero_iff h𝓝 hleft h).1 h1
    simp only [hF]; rw [integral_conj, h2, map_zero]
  exact GlobalTheory.UnfoldNormal.unfold_zero_mean (GA D V) m Γ' N hΓc hNc hnormN κ 𝓝 inferInstance h𝓝' h𝓝t K F
    hKc.measurable hFc.measurable hKN hKΓ hFΓ h0 𝓖 h𝓖 hint

end GlobalTheory.DblOrbit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EulerProductConjugationStableParametersPosStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.euler_product_conjugation_stable_parameters_pos : ∀ (D : D7) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (B : GlobalTheory.LFun.Fam D.host.E) (μ : (AE D)ˣ →* Circle) (r : ℕ) (κ s : ℝ), IsHeckeChar D μ → ResEta D μ 0 → GlobalTheory.LFun.UnrOff (F := D.host.F) μ (S : Set (HeightOneSpectrum (𝓞 D.host.F))) → GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (S : Set (HeightOneSpectrum (𝓞 D.host.F)))) B r κ → κ + 1 < s → (∀ w ∉ GlobalTheory.LFun.above D.host.E (S : Set (HeightOneSpectrum (𝓞 D.host.F))), (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) → w ≠ w' → B w' = (B w).map star) ∧ (¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → (B w).map star = B w)) → ∃ l : ℝ, 0 < l ∧ GlobalTheory.LFun.LSD D S B μ (s : ℂ) = l := by
  first | exact @GlobalTheory.EulerConjPos.lsd_pos | exact GlobalTheory.EulerConjPos.lsd_pos | (intros; apply GlobalTheory.EulerConjPos.lsd_pos <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralRealPointUnitScalarSinglePlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.CentralUnit

variable {D : D7}

theorem exists_unit {θ : InfFam D} (hθ : IsInfFam θ) (τ : D.what₂.Tau) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ∃ a : AE D, finPart D a = 1 ∧ (∀ ρ, θ ρ (infPart D a) = if ρ = τ then ζ else 1) ∧ cA D a * a = 1 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.exists_chart hθ
  let v : D.what₂.Tau → ℂ := fun ρ => if ρ = τ then ζ - 1 else 0
  let a : AE D := 1 + σ v
  have a1 : finPart D a = 1 := by
    simp only [a]; rw [RingHom.map_add (f := _), hσ.fin, RingHom.map_one, add_zero]
  have a2 : ∀ ρ, θ ρ (infPart D a) = if ρ = τ then ζ else 1 := by
    intro ρ
    simp only [a]; rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hσ.comp, RingHom.map_one, RingHom.map_one]
    simp only [v]
    split_ifs <;> ring
  refine ⟨a, a1, a2, sub_eq_zero.1 (hσ.ext _ ?_ fun ρ => ?_)⟩
  · have e : finPart D (cA D a) = sigR (Af D.host.F) D.sp.cm.sig (finPart D a) :=
      GlobalTheory.FockCompare.LiftUnitary.snd_sigR D.sp.cm.sig a
    rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_one, e, a1, RingHom.map_one, one_mul, sub_self]
  · rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_mul, RingHom.map_mul, RingHom.map_one, RingHom.map_one,
      GlobalTheory.FockCompare.comp_cA hθ, a2]
    split_ifs
    · rw [Complex.conj_mul', hζ, Complex.ofReal_one, one_pow, sub_self]
    · rw [RingHom.map_one, one_mul, sub_self]

theorem scalar_mem (S : HSp D) {a : AE D} (ha : cA D a * a = 1) :
    Formalism.UG.cT (cA D) (Matrix.diagonal fun _ : Fin S.rank => a) * JR (AF D.host.F) S.gram *
      (Matrix.diagonal fun _ : Fin S.rank => a) = JR (AF D.host.F) S.gram := by
  rw [Formalism.UG.cT, Matrix.diagonal_map (RingHom.map_zero _), Matrix.diagonal_transpose]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  linear_combination (JR (AF D.host.F) S.gram i j) * ha

noncomputable def scalarElt (S : HSp D) {a : AE D} (ha : cA D a * a = 1) : GA D S :=
  ⟨⟨Matrix.diagonal fun _ => a, Matrix.diagonal fun _ => cA D a,
    by rw [Matrix.diagonal_mul_diagonal, mul_comm, ha, Matrix.diagonal_one],
    by rw [Matrix.diagonal_mul_diagonal, ha, Matrix.diagonal_one]⟩, scalar_mem S ha⟩

theorem mt_scalarElt (S : HSp D) {a : AE D} (ha : cA D a * a = 1) :
    Formalism.L2.Theta.mt S (scalarElt S ha) = Matrix.diagonal fun _ => a := rfl

theorem scalarElt_mem_GinfC (S : HSp D) {a : AE D} (ha : cA D a * a = 1) (h1 : finPart D a = 1) :
    scalarElt S ha ∈ GinfC S := by
  rw [GinfC, MonoidHom.mem_ker]
  refine Units.ext ?_
  ext i j
  change ((Matrix.diagonal fun _ : Fin S.rank => a).map (finPart D)) i j =
    (1 : Matrix (Fin S.rank) (Fin S.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) i j
  rw [Matrix.map_apply, Matrix.diagonal_apply, Matrix.one_apply]
  split_ifs
  · exact h1
  · exact RingHom.map_zero _

theorem scalarElt_mem_center (S : HSp D) {a : AE D} (ha : cA D a * a = 1) :
    scalarElt S ha ∈ Subgroup.center (GA D S) := by
  refine Subgroup.mem_center_iff.2 fun k => Subtype.ext (Units.ext ?_)
  ext i j
  change (k.1.val * Matrix.diagonal fun _ : Fin S.rank => a) i j = ((Matrix.diagonal fun _ : Fin S.rank => a) * k.1.val) i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

theorem compAt_scalarElt (θ : InfFam D) (τ : D.what₂.Tau) (S : HSp D) {a : AE D} (ha : cA D a * a = 1) :
    compAt θ τ (Formalism.L2.Theta.mt S (scalarElt S ha)) = θ τ (infPart D a) • (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) := by
  rw [mt_scalarElt]
  ext i j
  rw [compAt, Matrix.map_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

theorem exists_central_of_norm_one : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (S : HSp D) (τ : D.what₂.Tau) (ζ : ℂ), ‖ζ‖ = 1 → ∃ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) ∧ compAt θ τ (Formalism.L2.Theta.mt S z) = ζ • (1 : Matrix (Fin S.rank) (Fin S.rank) ℂ) ∧ ∀ ρ : D.what₂.Tau, ρ ≠ τ → compAt θ ρ (Formalism.L2.Theta.mt S z) = 1 := by
  intro D θ hθ S τ ζ hζ
  obtain ⟨a, a1, a2, ac⟩ := exists_unit hθ τ hζ
  refine ⟨scalarElt S ac, scalarElt_mem_GinfC S ac a1, scalarElt_mem_center S ac, ?_, fun ρ hρ => ?_⟩
  · rw [compAt_scalarElt, a2, if_pos rfl]
  · rw [compAt_scalarElt, a2, if_neg hρ, one_smul]

end GlobalTheory.CentralUnit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsClopenCompactNbhdZero
section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AfTensNbhd

variable (F : Type) [Field F] [NumberField F]

def intAf : Set (FiniteAdeleRing (𝓞 F) F) :=
  {a | ∀ v, a v ∈ HeightOneSpectrum.adicCompletionIntegers F v}

theorem isOpen_intAf : IsOpen (intAf F) := by
  unfold intAf
  exact RestrictedProduct.isOpen_forall_mem (fun v => by
    exact Valued.isOpen_integer _)

theorem isCompact_intAf : IsCompact (intAf F) :=
  (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).1

theorem isClosed_intAf : IsClosed (intAf F) := by
  haveI := GlobalTheory.IntegralFinAdele.t2Space_finiteAdeleRing' F
  exact (isCompact_intAf F).isClosed

theorem zero_mem_intAf : (0 : FiniteAdeleRing (𝓞 F) F) ∈ intAf F := fun v => by
  exact zero_mem _

end GlobalTheory.AfTensNbhd

namespace GlobalTheory.AfTensNbhd

section Tens

variable (F : Type) [Field F] [NumberField F] (E : Type) [Field E] [Algebra F E] [FiniteDimensional F E]

noncomputable def coordEquiv : ((Af F) ⊗[F] E) ≃ₗ[(Af F)] (Module.Free.ChooseBasisIndex F E → (Af F)) :=
  (Algebra.TensorProduct.basis (Af F) (Module.Free.chooseBasis F E)).equivFun

local instance : IsModuleTopology (Af F) ((Af F) ⊗[F] E) := ⟨rfl⟩

theorem continuous_coordEquiv : Continuous (coordEquiv F E) :=
  IsModuleTopology.continuous_of_linearMap (coordEquiv F E).toLinearMap

theorem continuous_coordEquiv_symm : Continuous (coordEquiv F E).symm := by
  haveI : ContinuousAdd ((Af F) ⊗[F] E) := IsModuleTopology.toContinuousAdd (Af F) _
  haveI : ContinuousSMul (Af F) ((Af F) ⊗[F] E) := IsModuleTopology.toContinuousSMul (Af F) _
  exact IsModuleTopology.continuous_of_linearMap (coordEquiv F E).symm.toLinearMap

noncomputable def intTens : Set ((Af F) ⊗[F] E) := coordEquiv F E ⁻¹' Set.univ.pi (fun _ => intAf F)

theorem isClopen_intTens : IsClopen (intTens F E) :=
  ⟨(isClosed_set_pi fun _ _ => isClosed_intAf F).preimage (continuous_coordEquiv F E),
   (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_intAf F).preimage (continuous_coordEquiv F E)⟩

theorem isCompact_intTens : IsCompact (intTens F E) := by
  have h := (isCompact_univ_pi fun _ => isCompact_intAf F).image (continuous_coordEquiv_symm F E)
  convert h using 1
  ext x
  constructor
  · intro hx
    exact ⟨coordEquiv F E x, hx, (coordEquiv F E).symm_apply_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    change coordEquiv F E ((coordEquiv F E).symm y) ∈ Set.univ.pi (fun _ => intAf F)
    rw [LinearEquiv.apply_symm_apply]
    exact hy

theorem zero_mem_intTens : (0 : (Af F) ⊗[F] E) ∈ intTens F E := by
  intro i _
  rw [map_zero]
  exact zero_mem_intAf F

end Tens

end GlobalTheory.AfTensNbhd

namespace GlobalTheory.AfTensNbhd

theorem exists_clopen_compact_nbhd_zero : ∀ (D : D7) (m n : ℕ), ∃ U : Set (Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E), IsClopen U ∧ IsCompact U ∧ (0 : Fin m → Fin n → Af D.host.F ⊗[D.host.F] D.host.E) ∈ U := by
  intro D m n
  refine ⟨Set.univ.pi (fun _ => Set.univ.pi (fun _ => intTens D.host.F D.host.E)), ⟨?_, ?_⟩, ?_, ?_⟩
  · exact isClosed_set_pi fun _ _ => isClosed_set_pi fun _ _ => (isClopen_intTens D.host.F D.host.E).1
  · exact isOpen_set_pi Set.finite_univ fun _ _ =>
      isOpen_set_pi Set.finite_univ fun _ _ => (isClopen_intTens D.host.F D.host.E).2
  · exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_intTens D.host.F D.host.E
  · intro i _ j _
    exact zero_mem_intTens D.host.F D.host.E

end GlobalTheory.AfTensNbhd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLeviPreimageOfFixIsotropicFrames
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.SG.AdBridge GlobalTheory.BesselChar

noncomputable section

namespace GlobalTheory.MixModel.HypDec

variable {D : D7}

theorem gram_mt {S : HSp D} (g : GA D S) {k l : ℕ} (x : Mx D S.rank k) (y : Mx D S.rank l) :
    adj (mt S g ⬝ x) ⬝ (gA S ⬝ (mt S g ⬝ y)) = adj x ⬝ (gA S ⬝ y) := by
  rw [adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc (adj (mt S g)),
    mt_unitary]

theorem exists_emb0_eq_of_fix_jX_jY {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (g : GA D S)
    (hX : mt S g ⬝ d.jX = d.jX) (hY : mt S g ⬝ d.jY = d.jY) : ∃ b : GA D S₀, d.emb0 b = g := by
  set M := mt S g with hM
  set B := d.p0 ⬝ M ⬝ d.j0 with hB
  have h1 : d.pX ⬝ M ⬝ d.j0 = 0 := by
    rw [pX_eq, Matrix.mul_assoc, Matrix.mul_assoc, ← hY, adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S) M,
      ← Matrix.mul_assoc (adj M), mt_unitary, gramR_Y0_eq_TI]
  have h2 : d.pY ⬝ M ⬝ d.j0 = 0 := by
    rw [pY_eq, Matrix.mul_assoc, Matrix.mul_assoc, ← hX, adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S) M,
      ← Matrix.mul_assoc (adj M), mt_unitary, wittDecomp_gram_X_anisotropic]
  have h3 : M ⬝ d.j0 = d.j0 ⬝ B := by
    rw [Matrix.mul_assoc] at h1 h2
    rw [← Matrix.one_mul (M ⬝ d.j0), ← d.sum_eq_one]
    simp only [Matrix.add_mul, Matrix.mul_assoc, h1, h2, Matrix.mul_zero, add_zero, zero_add, hB]
  have h4 : adj B * (gA S₀ * B) = gA S₀ := by
    have e1 := gram_mt g d.j0 d.j0
    rw [← hM, h3, d.gram_00, adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (gA S), ← Matrix.mul_assoc (adj d.j0),
      ← Matrix.mul_assoc (adj d.j0), Matrix.mul_assoc (adj d.j0), d.gram_00] at e1
    exact e1
  refine ⟨ofMat S₀ B h4, d.ga_ext ?_ ?_ ?_⟩
  · rw [wittDecomp_anisotropicEmbedding_inclX, ← hM, hX]
  · rw [wittDecomp_anisotropicEmbedding_inclAnisotropic, mt_ofMat, ← hM, h3]
  · rw [wittDecomp_anisotropicEmbedding_inclY, ← hM, hY]

end GlobalTheory.MixModel.HypDec

end
end

