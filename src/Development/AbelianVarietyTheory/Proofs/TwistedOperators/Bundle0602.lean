module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0417
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0378
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0520
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0594
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
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1498
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0208
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1256
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0792
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0877
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0592
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0588
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0597
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0600
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCuspTypedTestGridIffSenderGridConj
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0333
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0430
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BasePointCharacterTrivialOnDepthLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.XCharBF

noncomputable section

namespace GlobalTheory.XCharBF

variable {D : D7}

theorem sympl_xZero {V V₀ W W₀ : HSp D} {ρ : ℕ} (dB : HypDec V V₀ ρ) (dJ : HypDec W W₀ ρ) (u : Mx D W.rank V.rank) :
    symplO V W (dB.extX W dJ.jX) (dB.extY W (u ⬝ dB.jY)) =
      Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * cA D ((dJ.pY ⬝ u ⬝ dB.jY).trace)) := by
  have h := dB.hO_ext W dJ.jX 0 0 (u ⬝ dB.jY) 0 0
  simp only [map_zero, add_zero, zero_add] at h
  rw [symplO, h]
  congr 2
  have e1 : gA W ⬝ dJ.jX = adj dJ.pY := by rw [dJ.pY_eq, adj_mul, adj_gA, adj_adj]
  simp only [pairS, hO_eq_trace, adj_zero, Matrix.zero_mul, Matrix.mul_zero, trace_zero, add_zero, e1]
  rw [← adj_mul, Matrix.mul_assoc]
  exact trace_adj _

end GlobalTheory.XCharBF

theorem GlobalTheory.AscFin.pcBF_xZero_char : OnStd fun {D} _ _ {sc} {G} W F =>
    ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * ρ + 1),
      W.ψ (symplO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0))
        ((F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) (xZero (F.dJ ρ h)))
        ((F.dB ρ h).extY (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jY))) = 1 := by
  intro D hq T L μ0 hL sc G W M hM F hF ρ h u hu
  rw [show xZero (F.dJ ρ h) = (F.dJ ρ h).jX from rfl, GlobalTheory.XCharBF.sympl_xZero]
  refine _root_.GlobalTheory.XCharBF.adelicTraceChar_differentGen_conj_idealCompletion W.ψ_std _ ?_
  rw [Matrix.trace]
  refine sum_mem fun p _ => ?_
  refine _root_.GlobalTheory.XCharComb.mem_complId_AA_AAbar hq μ0 hL G _ (GlobalTheory.T.besselStep_diagonalCoordinates_mem_complementIdeal hF ρ h u hu.1 p) fun e he => ?_
  change e * ((F.dJ ρ h).pY ⬝ u ⬝ (F.dB ρ h).jY) p p ∈ complId D.host.AAbar
  have := GlobalTheory.T.completed_diagonal_coordinate_mem_completion_conj_AA hF ρ h (e • u) (hu.2 e he) p
  rwa [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul] at this

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTriangleFiniteDoubleCosets
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

open scoped ComplexOrder Classical

namespace GlobalTheory.BotClassFin

variable {D : D7}

def finPart (V : HSp D) (g : GA D V) : GA D V := ((GlobalTheory.AdelicSplit.splitEquiv V).symm g).2.1

theorem continuous_finPart (V : HSp D) : Continuous (finPart V) :=
  continuous_subtype_val.comp (continuous_snd.comp (GlobalTheory.AdelicSplit.splitEquiv V).symm.continuous)

theorem finPart_mem (V : HSp D) (g : GA D V) : finPart V g ∈ GfC V := ((GlobalTheory.AdelicSplit.splitEquiv V).symm g).2.2

theorem finPart_one (V : HSp D) : finPart V 1 = 1 := by
  simp [finPart, map_one]

theorem finHom_finPart (V : HSp D) (g : GA D V) : finHom V (finPart V g) = finHom V g := by
  set p := (GlobalTheory.AdelicSplit.splitEquiv V).symm g with hp
  have e : g = p.1.1 * p.2.1 := ((GlobalTheory.AdelicSplit.splitEquiv V).apply_symm_apply g).symm
  have h1 : finHom V p.1.1 = 1 := p.1.2
  conv_rhs => rw [e]
  rw [map_mul, h1, one_mul]
  rfl

theorem exists_reps_of_open (V : HSp D) (hV : ∀ τ, (gramAt D V τ).PosDef) (J : Subgroup (GA D V))
    (hJ : IsOpen (J : Set (GA D V))) :
    ∃ H : Finset (GA D V), (∀ h ∈ H, h ∈ GfC V) ∧
      ∀ h ∈ GfC V, ∃ γ ∈ GQ V, ∃ r ∈ GinfC V, ∃ h₀ ∈ H, ∃ κ ∈ J, κ ∈ GfC V ∧ h = γ * r * h₀ * κ := by
  haveI := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.2.2.2.1
  set L : Subgroup (Bridge.Gf V) := (J ⊓ GfC V).map (finHom V).rangeRestrict with hL
  have hO : GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting.IsOpenLev V L := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.SublevelSplitting.IsOpenLev
    refine Subgroup.isOpen_of_mem_nhds (g := (1 : GA D V)) _ ?_
    have h1 : (finPart V) ⁻¹' (J : Set (GA D V)) ∈ nhds (1 : GA D V) := by
      refine (hJ.preimage (continuous_finPart V)).mem_nhds ?_
      show finPart V 1 ∈ J
      rw [finPart_one]
      exact J.one_mem
    refine Filter.mem_of_superset h1 fun g hg => ?_
    refine Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨finPart V g, ⟨hg, finPart_mem V g⟩, ?_⟩)
    exact Subtype.ext (finHom_finPart V g)
  obtain ⟨m, c, hc⟩ := GlobalTheory.RepsObj.exists_cover V hV L hO
  choose x hx using fun a => GlobalTheory.FunObj.ClassFin.gfcToGf_surjective V (c a)
  refine ⟨Finset.univ.image fun a => (x a).1, ?_, ?_⟩
  · intro h hh
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hh
    exact (x a).2
  · intro h hh
    obtain ⟨a, γ, k, e⟩ := hc ((finHom V).rangeRestrict h)
    obtain ⟨κ, ⟨hκJ, hκf⟩, hκ⟩ := Subgroup.mem_map.1 k.2
    have ex : finHom V (x a).1 = (c a).1 := congrArg Subtype.val (hx a)
    have ek : finHom V κ = k.1.1 := congrArg Subtype.val hκ
    have eγ : ((Bridge.ratF V γ : Bridge.Gf V) : _) = finHom V γ.1 := rfl
    have e' : finHom V h = finHom V γ.1 * finHom V (x a).1 * finHom V κ := by
      have := congrArg Subtype.val e
      rw [ex, ek, ← eγ]
      exact this
    refine ⟨γ.1, γ.2, γ.1⁻¹ * h * κ⁻¹ * (x a).1⁻¹, ?_, (x a).1, Finset.mem_image.2 ⟨a, Finset.mem_univ _, rfl⟩, κ, hκJ, hκf,
      by group⟩
    show finHom V _ = 1
    simp only [map_mul, map_inv, e']
    group

end GlobalTheory.BotClassFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTriangleMonomialSupportFinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.BottomDeg

open GlobalTheory.Grid (neg sgn ofSgn)

variable {D : D7}


open Classical in
theorem pureTensorO_scal_pm {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {S T : HSp D} (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hs : ∀ τ, sS τ = 1 ∨ sS τ = -1) (ht : ∀ τ, sT τ = 1 ∨ sT τ = -1)
    (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f) (ζ : D.what₂.Tau → ℂ) (hζ : ∀ τ, ‖ζ τ‖ = 1)
    (α : FVar D T.rank S.rank →₀ ℕ) :
    pureTensorO ψ θ S T sS sT (fun τ => ζ τ • BS τ) BT f (MvPolynomial.monomial α 1) =
      (∏ τ, (if (sS τ = 1 ↔ sT τ = 1) then (ζ τ)⁻¹ else ζ τ) ^ (∑ v ∈ α.support with v.1 = τ, α v)) •
        pureTensorO ψ θ S T sS sT BS BT f (MvPolynomial.monomial α 1) := by
  have hz : ∀ τ, ζ τ ≠ 0 := fun τ h => by simpa [h] using hζ τ
  let μ : D.what₂.Tau → ℂ := fun τ => if (sS τ = 1 ↔ sT τ = 1) then (ζ τ)⁻¹ else ζ τ
  have key : ∀ (i : FVar D T.rank S.rank) g, IsThetaFunO ψ S T g →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) (fun τ => ζ τ • BS τ) BT i g =
      μ i.1 • aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i g := by
    rintro ⟨ρ, a, j⟩ g hg
    simp only [aPlusAll, μ]
    rw [GlobalTheory.FockScal.unitMap_smul _ _ (hz ρ),
      GlobalTheory.FockSubst.aPlus_dir_smul hψ hθ ρ _ _ hg _ _ (GlobalTheory.FockScal.cplxO_pm (hs ρ) (ht ρ) a j _)]
    congr 1
    rw [map_inv₀, ← Complex.inv_eq_conj (hζ ρ), inv_inv]
    simp only [decide_eq_true_eq]
  have hA : ∀ i f, IsThetaFunO ψ S T f →
      IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i f) :=
    fun _ _ h => GlobalTheory.FockSubst.aPlus_th hψ hθ _ _ _ h
  have Asm : ∀ i (a : ℂ) f, IsThetaFunO ψ S T f →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i (a • f) =
      a • aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i f :=
    fun _ a _ h => GlobalTheory.FockSubst.aPlus_smul hψ hθ _ _ _ a h
  unfold pureTensorO
  exact GlobalTheory.FockScal.pure_scal (P := IsThetaFunO ψ S T) (fun v : FVar D T.rank S.rank => v.1) μ
    (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) hA Asm key hf α


open Classical in
theorem scalar_exists {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) (t : T) (τ₀ : D.what₂.Tau) :
    ∃ C w : ℂ, (w = Complex.exp Complex.I ∨ w = (Complex.exp Complex.I)⁻¹) ∧
      ∀ (k : FVar D WW.rank A.rank →₀ ℕ) (h : GA D WW),
        X.I W.ψ W.θ t (MvPolynomial.monomial k 1) h =
          (C * w ^ (∑ v ∈ k.support with v.1 = τ₀, k v)) * X.I W.ψ W.θ t (MvPolynomial.monomial k 1) h := by
  classical
  have hI := hX.is
  have hθ : IsInfFam W.θ := hI.isVac.2.inf
  have hψ : IsStdChar D W.ψ (-1) := hI.isVac.1
  set om' := (X.ω t).toSgn true with hom'
  have hom := hI.weil t
  have hsA : ∀ τ, X.rA.s τ = 1 := fun τ => (hX.std.2.2 τ).1
  have hsW : ∀ τ, X.rW.s τ = 1 := fun τ => (hX.stdW.2.2 τ).1
  have he : ‖Complex.exp Complex.I‖ = 1 := by simpa using Complex.norm_exp_ofReal_mul_I 1
  obtain ⟨z', hz', -, h1, h2⟩ := GlobalTheory.CentralUnit.exists_central_of_norm_one D W.θ hθ (neg A) τ₀ (Complex.exp Complex.I) he
  set ζ : D.what₂.Tau → ℂ := fun τ => if τ = τ₀ then Complex.exp Complex.I else 1 with hζdef
  have hζ : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt (neg A) z') = ζ τ • (1 : Matrix (Fin (neg A).rank) (Fin (neg A).rank) ℂ) := by
    intro τ
    by_cases hτ : τ = τ₀
    · subst hτ
      simp only [hζdef, if_pos rfl, h1]
    · simp only [hζdef, if_neg hτ, h2 τ hτ, one_smul]
  have hζn : ∀ τ, ‖ζ τ‖ = 1 := fun τ => by
    by_cases hτ : τ = τ₀
    · simp only [hζdef, if_pos hτ, he]
    · simp only [hζdef, if_neg hτ, norm_one]
  have hf : IsThetaFunO W.ψ (neg A) WW (X.f t) := (GlobalTheory.ConstRatio.theta_f hI t).1
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hI.idem t)
  have hfock : ∀ τ, IsFockVacAt (heisO W.ψ (neg A) WW) W.θ τ (cplxO (-X.rA.s τ) (X.rW.s τ)) (X.f t) := fun τ =>
    GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hθ ho.infPart_eq ho.conj.infPart_eq (hI.fst t)
      hI.isVac.2.theta hf (hI.isVac.2.fock τ)
  have cS : ∀ τ, IsCartanInv (gramAt D (neg A) τ) (-X.rA.s τ) := fun τ => GlobalTheory.Grid.isCartanInv_sgn true A τ (hI.rigA.2.2 τ).1
  have cT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hI.rigW.2.2 τ).1
  have hdet : ∀ τ, (gramAt D (neg A) τ).det ≠ 0 := fun τ h0 => by
    have := (cS τ).2.2.det_pos.ne'
    rw [Matrix.det_mul, h0, zero_mul] at this
    exact this rfl
  obtain ⟨r, hr, -⟩ := GlobalTheory.VacuumCharacter.exists_root hθ (neg A) hdet z' hz'
  have hy1 : IsDetRoot WW 1 1 := by
    show _ = _
    rw [Units.val_one, RingHom.map_one, mul_one]
    exact (Matrix.det_one).symm
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have one : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt WW 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one WW _
  obtain ⟨C, hC⟩ : ∃ C : ℂ, om' (z', 1) (X.f t) = C • X.f t :=
    ⟨_, GlobalTheory.WeilVacChar.vacuum_character D W.ψ hψ (neg A) WW W.θ hθ _ _ om' η hη hom (fun τ => -X.rA.s τ) X.rW.s cS cT
      z' hz' 1 (one_mem _) (fun τ => by rw [hζ τ, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [one, one_mul, mul_one]) r 1 hr hy1 (X.f t) hf hfock⟩

  have hop : ∀ k : FVar D WW.rank A.rank →₀ ℕ, _ := fun k =>
    GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ (neg A) WW _ _ om' hom hθ (fun τ => -X.rA.s τ) (fun τ => -X.rA.s τ)
      X.rA.B (fun τ => ζ τ • X.rA.B τ) X.rW.s X.rW.s X.rW.B X.rW.B z' 1
      (fun τ => by rw [hζ τ, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [one, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [hζ τ, Matrix.smul_mul, Matrix.one_mul])
      (fun τ => by rw [one, Matrix.one_mul]) (X.f t) hf (MvPolynomial.monomial k 1)
  set w : ℂ := if (-X.rA.s τ₀ = 1 ↔ X.rW.s τ₀ = 1) then (Complex.exp Complex.I)⁻¹ else Complex.exp Complex.I with hw
  have hscal : ∀ k : FVar D WW.rank A.rank →₀ ℕ,
      om' (z', 1) (pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t)
        (MvPolynomial.monomial k 1)) =
        (C * w ^ (∑ v ∈ k.support with v.1 = τ₀, k v)) •
          pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) (MvPolynomial.monomial k 1) := by
    intro k
    rw [(hop k).2, hC, GlobalTheory.FiniteFock.pureTensorO_smul,
      pureTensorO_scal_pm (S := neg A) (T := WW) hψ hθ (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (fun τ => Or.inr (by rw [hsA])) (fun τ => Or.inl (hsW τ)) (X.f t) hf ζ hζn k,
      smul_smul]
    congr 2
    rw [Finset.prod_eq_single τ₀]
    · simp only [hζdef, if_pos rfl, hw]
    · intro ρ _ hρ
      simp only [hζdef, if_neg hρ, inv_one, ite_self, one_pow]
    · simp
  refine ⟨C, w, by rw [hw]; split_ifs; exacts [Or.inr rfl, Or.inl rfl], fun k h => ?_⟩
  set φ := pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) (MvPolynomial.monomial k 1)
    with hφ
  have hK := GlobalTheory.thetaKO_rat_left_and_eigen_right W.ψ (neg A) WW _ _ om' hom φ (hop k).1
  have hker : ∀ g : GA D A, X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h g = thetaKO om' ((ofSgn true A).symm g) h φ :=
    fun g => by
      show thetaKO (X.ω t) g h φ = (X.ω t) ((ofSgn true A) ((ofSgn true A).symm g), h) φ 0
      rw [MulEquiv.apply_symm_apply]
      rfl
  have hleft : ∀ γ ∈ GQ A, ∀ g, X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h (γ * g) =
      X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h g := by
    intro γ hγ g
    rw [hker, hker, map_mul]
    have := hK.1 _ ((GlobalTheory.SgnIdent.mem_GQ_sgn true A _).2 (by rwa [MulEquiv.apply_symm_apply])) 1 (one_mem _)
      ((ofSgn true A).symm g) h
    rwa [one_mul] at this
  have hright : ∀ g, X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h (g * ofSgn true A z') =
      (C * w ^ (∑ v ∈ k.support with v.1 = τ₀, k v)) * X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h g := by
    intro g
    rw [hker, hker, map_mul, MulEquiv.symm_apply_apply]
    have := hK.2 z' 1 _ (hscal k) ((ofSgn true A).symm g) h
    rwa [mul_one] at this
  show ∫ g in X.fd, X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h g ∂X.m =
    _ * ∫ g in X.fd, X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h g ∂X.m
  calc _ = ∫ g in X.fd, X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h (g * ofSgn true A z') ∂X.m :=
        (GlobalTheory.ChainOnto.setIntegral_fd_mul_right D A X.m X.fd hI.meas.1 hI.meas.2 _ hleft (ofSgn true A z')).symm
    _ = _ := by
        simp_rw [hright]
        exact integral_const_mul _ _

end GlobalTheory.BottomDeg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalAlongDownGridArrows
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FlipRun

theorem ga_eq_of_match {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts}
    {G' : GridData R.toLevCh sc} {W : G'.Weil} {G : GlobalTheory.Grid.GridPre R} (hM : GlobalTheory.GridJoin.Match G W) {i j : ℕ}
    (hi : i ≤ D.R.m) (hj : j ≤ D.R.m) : GA D (G.V i j).V = GA D (G'.V (.grid i j)) := by
  obtain ⟨L, h1, h2, e⟩ := (hM.1.vert i j hi hj).sp
  rw [e]; rfl

end GlobalTheory.FlipRun
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteBottomWeilActionFockPureTensorSubstituti
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.BottomAct

open GlobalTheory.Grid (neg sgn ofSgn)

theorem conj_invT_of_unitary {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : Matrix.conjTranspose M * M = 1) :
    ((M⁻¹).transpose).map (starRingEnd ℂ) = M := by
  rw [Matrix.inv_eq_left_inv h]
  ext a b
  simp only [Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply, RCLike.star_def, Complex.conj_conj]

theorem conj_invT_compAt {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} (hV : V.gram = 1) (g : GA D V)
    (τ : D.what₂.Tau) :
    (((compAt θ τ (Formalism.L2.Theta.mt V g))⁻¹).transpose).map (starRingEnd ℂ) = compAt θ τ (Formalism.L2.Theta.mt V g) := by
  have h1 := GlobalTheory.StdUnn.CartanMove.compAt_isom hθ V g τ
  have hg : gramAt D V τ = 1 := by
    unfold gramAt
    rw [hV]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  rw [hg, Matrix.mul_one] at h1
  exact conj_invT_of_unitary h1

theorem om_pureTensorO_bottom : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ (t : T) (g : GA D A) (P : MvPolynomial (FVar D WW.rank A.rank) ℂ), (X.ω t).toSgn true ((GlobalTheory.Grid.ofSgn true A).symm g, 1) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) = pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B ((X.ω t).toSgn true ((GlobalTheory.Grid.ofSgn true A).symm g, 1) (X.f t)) (GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ)) (fun τ => compAt W.θ τ (Formalism.L2.Theta.mt A g)) P) := by
  intro D T L sc G W i j A A' WW X hX t g P
  have hI := hX.is
  have hθ : IsInfFam W.θ := hI.isVac.2.inf
  have hψ : IsStdChar D W.ψ (-1) := hI.isVac.1
  have hom := hI.weil t
  have hsA : ∀ τ, X.rA.s τ = 1 := fun τ => (hX.std.2.2 τ).1
  have hsW : ∀ τ, X.rW.s τ = 1 := fun τ => (hX.stdW.2.2 τ).1
  have hBA : ∀ τ, X.rA.B τ = 1 := fun τ => (hX.std.2.2 τ).2
  have hf : IsThetaFunO W.ψ (neg A) WW (X.f t) := (GlobalTheory.ConstRatio.theta_f hI t).1
  have hmt : Formalism.L2.Theta.mt (neg A) ((ofSgn true A).symm g) = Formalism.L2.Theta.mt A g := by
    rw [← GlobalTheory.Grid.mt_ofSgn, MulEquiv.apply_symm_apply]
  set u : D.what₂.Tau → Matrix (Fin A.rank) (Fin A.rank) ℂ := fun τ => compAt W.θ τ (Formalism.L2.Theta.mt A g) with hu
  have one : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt WW 1) = 1 := fun τ => GlobalTheory.StdUnn.CartanMove.compAt_mt_one W.θ τ WW
  have hop := GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ (neg A) WW _ _ ((X.ω t).toSgn true) hom hθ
    (fun τ => -X.rA.s τ) (fun τ => -X.rA.s τ) X.rA.B (fun τ => X.rA.B τ * u τ) X.rW.s X.rW.s X.rW.B
    (fun τ => X.rW.B τ * 1) ((ofSgn true A).symm g) 1
    (fun τ => by rw [hmt, hsA, Matrix.neg_mul, Matrix.mul_neg, Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [one, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [hmt, hBA, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [one, Matrix.one_mul, Matrix.mul_one]) (X.f t) hf P
  rw [hop.2]
  have hf' : IsThetaFunO W.ψ (neg A) WW ((X.ω t).toSgn true ((ofSgn true A).symm g, 1) (X.f t)) :=
    hom.om_pres _ _ hf
  have e1 : (fun τ => -X.rA.s τ) = fun _ => (-1 : Matrix (Fin A.rank) (Fin A.rank) ℂ) := funext fun τ => by rw [hsA]
  have e2 : X.rW.s = fun _ => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ) := funext hsW
  have key := GlobalTheory.FockNegSubst.pureTensorO_negSp_subst D W.ψ W.θ A WW hψ hθ X.rA.B u X.rW.B (fun _ => 1) _ hf' P
  have hunit : ∀ τ, (((u τ)⁻¹).transpose).map (starRingEnd ℂ) = u τ := fun τ => conj_invT_compAt hθ hX.std.1 g τ
  have hv : (fun _ : D.what₂.Tau => (1 : Matrix (Fin WW.rank) (Fin WW.rank) ℂ).map (starRingEnd ℂ)) = fun _ => 1 :=
    funext fun _ => Matrix.map_one _ (map_zero _) (map_one _)
  rw [funext hunit, hv] at key
  rw [e1, e2]
  exact key

end GlobalTheory.BottomAct

end
end

