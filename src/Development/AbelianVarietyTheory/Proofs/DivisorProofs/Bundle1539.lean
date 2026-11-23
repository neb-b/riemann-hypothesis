module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0252
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Formalism.LocalToGlobal.IndefiniteReal.DatumF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1378
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1374
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1377
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1439
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1054
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1503
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1505
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0892
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorRationalTranslateMemThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1498
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0258
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunOPosSigIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.Grid (neg)
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.RallisBottom

variable {D : D7}

def posSig (A : HSp D) : HSp D := { A with sig := fun _ => (A.rank, 0) }

theorem posSig_sigOK {A : HSp D} (h : A.gram = 1) : (posSig A).SigOK := fun τ => by
  have e : (posSig A).gram.map τ = 1 := by
    show A.gram.map τ = 1
    rw [h]; exact Matrix.map_one _ (map_zero τ) (map_one τ)
  show Formalism.UG.HasSignature ((posSig A).gram.map τ) A.rank 0
  rw [e]
  exact GlobalTheory.Proof.GenusMassSignature.hasSignature_of_posDef Matrix.PosDef.one

theorem thetaFunO_posSig_iff {ψ : AddChar (AF D.host.F) ℂ} {A WW : HSp D} (f : WO (neg A) WW → ℂ) :
    IsThetaFunO ψ (neg (posSig A)) WW f ↔ IsThetaFunO ψ (neg A) WW f :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4⟩, fun h => ⟨h.1, h.2, h.3, h.4⟩⟩

theorem isWeil_posSig {ψ : AddChar (AF D.host.F) ℂ} {A WW : HSp D} {χA χW : (AE D)ˣ →* Circle} {ω : GlobalTheory.Grid.WRep A WW}
    (h : GlobalTheory.Grid.IsWeil ψ true A WW χA χW ω) : GlobalTheory.Grid.IsWeil ψ true (posSig A) WW χA χW ω := by
  unfold GlobalTheory.Grid.IsWeil at h ⊢
  exact
    { std := h.std
      hecS := h.hecS
      hecT := h.hecT
      resS := h.resS
      resT := h.resT
      om_pres := fun p f hf => (thetaFunO_posSig_iff (A := A) (WW := WW) _).2 (h.om_pres p f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf))
      om_heis := fun g k w f hf => h.om_heis g k w f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf)
      om_aut := fun γ hγ γ' hγ' f hf => h.om_aut γ hγ γ' hγ' f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf)
      om_cont := fun f hf => h.om_cont f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf)
      om_unit := fun μ 𝓕 h1 h2 p f hf => h.om_unit μ 𝓕 h1 h2 p f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf)
      om_split := fun e he g k h1 h2 x y h3 h4 =>
        (h.om_split e he g k h1 h2 x y h3 h4).imp fun _ hr => ⟨hr.1, fun ℓ hℓ f hf =>
          hr.2 ℓ (fun u hu f hf => hℓ u hu f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).2 hf)) f ((thetaFunO_posSig_iff (A := A) (WW := WW) f).1 hf)⟩ }

theorem isVacO_posSig {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {A WW : HSp D} {sA sW LA LW} {f : WO (neg A) WW → ℂ}
    (h : IsVacO ψ θ (neg A) WW sA sW LA LW f) : IsVacO ψ θ (neg (posSig A)) WW sA sW LA LW f :=
  ⟨h.1, ⟨h.2.inf, (thetaFunO_posSig_iff (A := A) (WW := WW) f).2 h.2.theta, h.2.lat, h.2.fock, h.2.norm⟩⟩

variable {T : Type}

def Tri.posSig {A A' WW : HSp D} (X : Tri T A A' WW) : Tri T (posSig A) A' WW :=
  ⟨⟨X.rA.Λ, X.rA.β, X.rA.s, X.rA.B⟩, X.rA', X.rW, X.ω, X.ω', X.vac, X.vac', X.e, X.c, X.f, X.f', X.m, X.fd, X.m', X.fd'⟩

variable {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}

theorem isBottomTri_posSig {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) :
    IsBottomTri W i j (Tri.posSig X) := by
  refine ⟨hX.rank, hX.rank', hX.std, hX.std', hX.stdW, ?_⟩
  exact
    { rank := hX.is.rank
      rigA := hX.is.rigA
      rigA' := hX.is.rigA'
      rigW := hX.is.rigW
      weil := fun t => isWeil_posSig (hX.is.weil t)
      weil' := hX.is.weil'
      isVac := isVacO_posSig hX.is.isVac
      isVac' := hX.is.isVac'
      idem := hX.is.idem
      expo := hX.is.expo
      fst := hX.is.fst
      snd := hX.is.snd
      meas := hX.is.meas
      meas' := hX.is.meas' }

theorem sigOK_posSig {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) :
    (posSig A).SigOK := posSig_sigOK hX.std.1

end GlobalTheory.RallisBottom

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionSmoothVectorRealHeisenberg
section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

noncomputable section

namespace GlobalTheory.ThetaSmoothF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def iotaHom {nS nT : ℕ} (ι : (InfinitePlace F → ℂ) →+ AEF F E) : (IxF F nS nT → ℂ) →+ WOF F E nS nT where
  toFun := iotaVF ι
  map_zero' := iotaVF_zero ι
  map_add' := iotaVF_add ι

theorem contDiff_heis_iota (σ : E →ₐ[F] E) (B : Base F E) (hB : B.IsGood σ) {nS nT : ℕ}
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E)
    {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E} (hι : IsChartF θ ι)
    {f : WOF F E nS nT → ℂ} (hf : IsThetaFunOF σ JS JT ξ₀ B.ψ f) (x : WOF F E nS nT) :
    ContDiff ℝ ∞ fun v : IxF F nS nT → ℂ => heisOF σ JS JT ξ₀ B.ψ (iotaVF ι v) f x := by
  obtain ⟨lam, hl, hlam⟩ := GlobalTheory.HeisLineDiffF.exists_log (_root_.GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB)
  let φ : (IxF F nS nT → ℂ) →+ ℂ :=
    { toFun := fun v => lam (symplOHF σ JS JT ξ₀ x (iotaVF ι v))
      map_zero' := by rw [iotaVF_zero, GlobalTheory.HeisLineDiffF.symplOHF_zero_right, map_zero]
      map_add' := fun u v => by rw [iotaVF_add, GlobalTheory.HeisLineDiffF.symplOHF_add_right, map_add (f := _)] }
  have hφ : Continuous φ := hl.comp (GlobalTheory.HeisLineDiffF.continuous_symplOHF σ JS JT ξ₀ x (continuous_iotaVF hι))
  let eqv := (Module.finBasis ℝ (IxF F nS nT → ℂ)).equivFunL
  let L' : (Fin (Module.finrank ℝ (IxF F nS nT → ℂ)) → ℝ) →+ WOF F E nS nT :=
    (iotaHom ι).comp eqv.symm.toLinearEquiv.toAddMonoidHom
  have hL' : Continuous L' := (continuous_iotaVF hι).comp eqv.symm.continuous
  have hsm := hf.smooth _ L' hL' (fun t => real_iotaVF hι _) x
  have hg : ContDiff ℝ ∞ fun v : IxF F nS nT → ℂ => f (x + iotaVF ι v) := by
    have h1 := hsm.comp eqv.contDiff
    convert h1 using 1
    funext v
    simp [L', iotaHom]
  have e : (fun v : IxF F nS nT → ℂ => heisOF σ JS JT ξ₀ B.ψ (iotaVF ι v) f x) =
      fun v => Complex.exp (φ.toRealLinearMap hφ v) * f (x + iotaVF ι v) := by
    funext v
    rw [heisOF, hlam _ (GlobalTheory.HeisLineDiffF.sndA_symplOHF σ JS JT ξ₀ x _ (real_iotaVF hι v))]
    rfl
  rw [e]
  exact ((φ.toRealLinearMap hφ).contDiff.cexp).mul hg

end GlobalTheory.ThetaSmoothF


open GlobalTheory.ThetaSmoothF in
theorem GlobalTheory.ThetaSmoothF.sm_of_thetaF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ (hψ : IsCharAF F B.ψ) (f : BBF σ JS JT ξ₀ B.ψ), IsThetaFunOF σ JS JT ξ₀ B.ψ f.1 →
        Sm (rhoVF σ JS JT ξ₀ B.ψ hψ ι) f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hξ' θ hθ ι hι hψ f hf
  have hstd := _root_.GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB
  let H := HMF (nS := nS) (nT := nT) JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1)
  let B₀ : (IxF F nS nT → ℂ) →ₗ[ℝ] (IxF F nS nT → ℂ) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun x y => (star y ⬝ᵥ H *ᵥ x).im)
      (fun x x' y => by simp [Matrix.mulVec_add, dotProduct_add])
      (fun c x y => by simp [Matrix.mulVec_smul, dotProduct_smul])
      (fun x y y' => by simp [add_dotProduct])
      (fun c x y => by simp [star_smul, smul_dotProduct])
  let om : (IxF F nS nT → ℂ) →L[ℝ] (IxF F nS nT → ℂ) →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap ((LinearMap.toContinuousLinearMap (𝕜 := ℝ)).toLinearMap ∘ₗ B₀)
  have e : (fun x y => om x y) = fun x y => (star y ⬝ᵥ H *ᵥ x).im := rfl
  have hH : IsHeis (fun x y : IxF F nS nT → ℂ => (star y ⬝ᵥ H *ᵥ x).im) (rhoVF σ JS JT ξ₀ B.ψ hψ ι) := by
    refine ⟨fun g => ?_, fun u v g => ?_, fun u g => norm_rhoBF hψ _ g, fun g => ?_⟩
    · show rhoBF σ JS JT ξ₀ B.ψ hψ (iotaVF ι 0) g = g
      rw [iotaVF_zero]
      exact rhoBF_zero hψ g
    · show rhoBF σ JS JT ξ₀ B.ψ hψ (iotaVF ι u) (rhoBF σ JS JT ξ₀ B.ψ hψ (iotaVF ι v) g) =
        _ • rhoBF σ JS JT ξ₀ B.ψ hψ (iotaVF ι (u + v)) g
      rw [rhoBF_rhoBF, iotaVF_add, _root_.GlobalTheory.RealCharF.psi_symplOHF_iotaVF F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξ' θ hθ ι hι u v]
    · exact (_root_.GlobalTheory.RealWeilF.continuous_rhoBF F E σ nS nT JS JT ξ₀ B.ψ hψ g).comp (continuous_iotaVF hι)
  refine _root_.GlobalTheory.RealWeil.sm_of_weak_deriv_closed (IxF F nS nT → ℂ) (BBF σ JS JT ξ₀ B.ψ) om (rhoVF σ JS JT ξ₀ B.ψ hψ ι) (e ▸ hH)
    (WOF F E nS nT) (ev _ _) norm_ev_le (fun b C => norm_QB_le b)
    (fun x v => ⟨B.ψ (symplOHF σ JS JT ξ₀ x (iotaVF ι v)), x + iotaVF ι v, fun b => rfl⟩)
    {g | IsThetaFunOF σ JS JT ξ₀ B.ψ g.1} ?_ ?_ f hf
  · intro g hg x
    exact (contDiff_heis_iota σ B hB JS JT ξ₀ hι hg x).differentiable (by simp)
  · intro g hg z
    let L : ℝ →+ WOF F E nS nT :=
      { toFun := fun t => iotaVF ι (t • z)
        map_zero' := by rw [zero_smul, iotaVF_zero]
        map_add' := fun s t => by rw [add_smul, iotaVF_add] }
    have hL : Continuous L := (continuous_iotaVF hι).comp (continuous_id.smul continuous_const)
    have hL0 : ∀ t, (L t).map (finPartF F E) = 0 := fun t => real_iotaVF hι _
    let d : WOF F E nS nT → ℂ := fun w => deriv (fun t : ℝ => heisOF σ JS JT ξ₀ B.ψ (L t) g.1 w) 0
    have hlev : ∃ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) ∧
        ∀ u ∈ U, u.map (infPartF F E) = 0 → heisOF σ JS JT ξ₀ B.ψ u d = d := by
      obtain ⟨U, hU, hUf⟩ := hg.level
      exact ⟨U, hU, fun u hu hu0 =>
        _root_.GlobalTheory.HeisDerivCM.heisOF_deriv_fix F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξ' hstd g.1 L hL hL0 u hu0 (hUf u hu hu0)⟩
    have hsm : ∀ (k : ℕ) (L' : (Fin k → ℝ) →+ WOF F E nS nT), Continuous L' →
        (∀ t, (L' t).map (finPartF F E) = 0) → ∀ w, ContDiff ℝ ∞ fun t => d (w + L' t) :=
      fun k L' hL' hL'0 w => _root_.GlobalTheory.ThetaLineSmoothF.contDiff_deriv_heisOF_line F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξ' hstd g.1 hg L hL hL0 k L' hL' hL'0 w
    have hd : IsThetaFunOF σ JS JT ξ₀ B.ψ d :=
      ⟨fun γ w => _root_.GlobalTheory.ThetaDerivQuasi.deriv_heis_quasi F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξ' hstd g.1 hg L hL hL0 γ w, hlev,
        GlobalTheory.T.theta_lift_standard_character_indefinite F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξ' hstd d hlev hsm, hsm⟩
    have hb := _root_.GlobalTheory.TowerFD.thetaFunOF_bounded F E σ nS nT JS JT ξ₀ B.ψ hψ d hd
    refine ⟨toBF d hd.cont hb hd.quasi, hd, fun x => ?_⟩
    exact (_root_.GlobalTheory.HeisLineDiffF.differentiableAt_heisOF_line F E σ B hB nS nT JS JT hS hT ξ₀ hξ hξ' hstd g.1 hg L hL hL0 x).hasDerivAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridBlockCongruenceOffTypePrimeDescription
section
namespace IwahoriGroupOffset
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.CompanionTheory.StepGroupOff

theorem symm_mem_KO_iff {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b) (g : GL b k) :
    (reGL e).symm g ∈ KO k a ↔ g ∈ KO k b := by
  rw [mem_KO, mem_KO, ← map_inv, reGL_symm_val, reGL_symm_val]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => by simpa using h1 (e.symm i) (e.symm j), fun i j => by simpa using h2 (e.symm i) (e.symm j)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => h1 _ _, fun i j => h2 _ _⟩

theorem twoBlock_gridIndex {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E)
    (j : ℕ) (x : Ix (Fin D.R.r) (Fin D.R.t) j) :
    Formalism.L2.DIV.blk2 D.R.r (ixFin G t w j x) = Sum.elim (fun _ => 0) (fun _ => 1) x := by
  rcases x with a | ⟨c, b⟩
  · simp [Formalism.L2.DIV.blk2, (ixFin_val G t w j).1 a]
  · simp [Formalism.L2.DIV.blk2, (ixFin_val G t w j).2 c b]

theorem mem_map_stepGroup_iff : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E), w ∉ L.Pg → ∀ (j : ℕ) (g : GL (Fin ((locGrid G t w).rank (0, j))) (Kw w)), g ∈ (stepGroup L t w j).map (reGL (ixFin G t w j)).toMonoidHom ↔ g ∈ KO (Kw w) (Fin ((locGrid G t w).rank (0, j))) ∧ (w ∈ L.Q t → ∀ a b, Formalism.L2.DIV.blk2 D.R.r b < Formalism.L2.DIV.blk2 D.R.r a → valuation (Kw w) (g.1 a b) < 1) := by
  intro D T L sc G t w hP j g
  rw [Subgroup.mem_map_equiv, stepGroup, if_neg hP]
  by_cases hQ : w ∈ L.Q t
  · rw [if_pos hQ]
    refine (mem_parahoric (k := Kw w) (r := Fin D.R.r) (s := Fin j × Fin D.R.t) (δ := 1) (hδ := fun _ _ => rfl)).trans ?_
    rw [symm_mem_KO_iff]
    refine and_congr_right fun _ => ?_
    constructor
    · intro h _ a b hab
      obtain ⟨x, rfl⟩ := (ixFin G t w j).surjective a
      obtain ⟨y, rfl⟩ := (ixFin G t w j).surjective b
      rw [twoBlock_gridIndex, twoBlock_gridIndex] at hab
      rcases x with x | x <;> rcases y with y | y
      · simp at hab
      · simp at hab
      · simpa [reGL_symm_val, Matrix.toBlocks₂₁] using h x y
      · simp at hab
    · intro h i l
      have := h hQ (ixFin G t w j (.inr i)) (ixFin G t w j (.inl l)) (by simp [twoBlock_gridIndex])
      simpa [reGL_symm_val, Matrix.toBlocks₂₁] using this
  · rw [if_neg hQ, symm_mem_KO_iff]
    exact ⟨fun h => ⟨h, fun h' => absurd h' hQ⟩, fun h => h.1⟩

end GlobalTheory.CompanionTheory.StepGroupOff

end
end

end IwahoriGroupOffset
section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory
open scoped TensorProduct nonZeroDivisors ComplexOrder
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

theorem _root_.GlobalTheory.Adopt.thetaGridBlockCongruence_offTypePrime_description : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (w : Pl D.host.E), w ∉ L.Pg → ∀ (j : ℕ) (g : GL (Fin ((locGrid G t w).rank (0, j))) (Kw w)), g ∈ (stepGroup L t w j).map (reGL (ixFin G t w j)).toMonoidHom ↔ g ∈ KO (Kw w) (Fin ((locGrid G t w).rank (0, j))) ∧ (w ∈ L.Q t → ∀ a b, Formalism.L2.DIV.blk2 D.R.r b < Formalism.L2.DIV.blk2 D.R.r a → valuation (Kw w) (g.1 a b) < 1) := by
  first | exact @IwahoriGroupOffset.GlobalTheory.CompanionTheory.StepGroupOff.mem_map_stepGroup_iff | exact IwahoriGroupOffset.GlobalTheory.CompanionTheory.StepGroupOff.mem_map_stepGroup_iff | (intros; apply IwahoriGroupOffset.GlobalTheory.CompanionTheory.StepGroupOff.mem_map_stepGroup_iff <;> assumption)

end
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPointMemStandardAndSkewLatticeOfEntriesMem
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
open scoped nonZeroDivisors

namespace GlobalTheory.FunObj.SqNum

theorem pt_mem_of_entries_mem (D : D7) (δ : ℂ) (𝔪 : Ideal (𝓞 D.host.E)) {a d : ℕ}
    (w : Matrix (Fin d) (Fin a) D.host.E) (hw : ∀ i j, ∃ b ∈ 𝔪, w i j = (b : D.host.E)) :
    pt D (tor0 D ⊤ δ) δ w ∈ La0 D (tor0 D ⊤ δ) a d ∧
      pt D (tor0 D ⊤ δ) δ w ∈ La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) := by
  have key : ∀ L' : Submodule (𝓞 D.host.E) (Fin d → D.host.E), (∀ x ∈ stdL D a, w.mulVec x ∈ L') →
      pt D (tor0 D ⊤ δ) δ w ∈ La D (tor0 D ⊤ δ) (stdL D a) L' := by
    intro L' hL'
    refine AddSubgroup.subset_closure ⟨δ, AddSubgroup.subset_closure ⟨1, trivial, by simp⟩, w, ?_, rfl⟩
    refine Submodule.subset_span ⟨1, ?_, w, Submodule.subset_span hL', (one_smul _ _).symm⟩
    refine FractionalIdeal.one_mem_inv_coe_ideal fun h => ?_
    have h2 := D.host.𝔟_spec.2
    rw [h, Ideal.smul_bot, sup_bot_eq] at h2
    exact bot_ne_top h2
  have hent : ∀ x ∈ stdL D a, ∀ i, w.mulVec x i ∈
      ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E) := by
    intro x hx i
    show ∑ j, w i j * x j ∈ _
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨b, hb, hbw⟩ := hw i j
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 (hx j trivial)
    refine (FractionalIdeal.mem_coeIdeal _).2 ⟨b * y, 𝔪.mul_mem_right y hb, ?_⟩
    rw [hbw, ← hy, map_mul]
  refine ⟨key _ fun x hx i _ => ?_, key _ fun x hx i _ => ?_⟩
  · have := (FractionalIdeal.coe_le_coe.2 FractionalIdeal.coeIdeal_le_one) (hent x hx i)
    rw [FractionalIdeal.coe_one] at this
    exact this
  · by_cases h𝔪 : 𝔪 = ⊥
    · have := hent x hx i
      rw [h𝔪, FractionalIdeal.coeIdeal_bot] at this
      have h0 : w.mulVec x i = 0 := by simpa using this
      rw [h0]
      exact zero_mem _
    · have hne : ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
        rw [Ne, FractionalIdeal.coeIdeal_eq_zero]
        intro h
        apply h𝔪
        have := congrArg (fun J : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • J) h
        simpa using this
      have hle : (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≤
          (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
            ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
        rw [FractionalIdeal.le_div_iff_mul_le hne]
        first
        | exact mul_le_of_le_one_right' FractionalIdeal.coeIdeal_le_one
        | exact mul_le_of_le_one_right (zero_le _) FractionalIdeal.coeIdeal_le_one
        | exact (mul_le_mul_left FractionalIdeal.coeIdeal_le_one _).trans_eq (mul_one _)
        | exact (FractionalIdeal.mul_le_mul_left FractionalIdeal.coeIdeal_le_one _).trans_eq (mul_one _)
        | exact (mul_le_mul_of_nonneg_left FractionalIdeal.coeIdeal_le_one (zero_le _)).trans_eq (mul_one _)
      exact (FractionalIdeal.coe_le_coe.2 hle) (hent x hx i)

end GlobalTheory.FunObj.SqNum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumAdjointNegSourceKernelsAgree
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV GlobalTheory.RouteSeesaw

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.AdjSwap

theorem dagger_eq_adjM {D : D7} (S B : HSp D) (y : Mx D B.rank S.rank) :
    GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S B y = adjM S B y := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger, adjM]
  rw [← Matrix.mul_assoc]
  rfl

theorem weil_adjoint_negSource : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S B : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (ω₂ : GA D B × GA D S →* Module.End ℂ (WO B S → ℂ)), IsWeilDatumO ψ B S χS χT ω₂ →
    ∃ (ω : GA D (negSp S) × GA D B →* Module.End ℂ (WO (negSp S) B → ℂ)) (χ χ' : (AE D)ˣ →* Circle),
      IsWeilDatumO ψ (negSp S) B χ χ' ω ∧ ∀ f : WO B S → ℂ, IsThetaFunO ψ B S f →
        IsThetaFunO ψ (negSp S) B (fun y => f (adjM S B y)) ∧
        ∀ g₁ u, thetaKO ω (negGA S u) g₁ (fun y => f (adjM S B y)) = thetaKO ω₂ g₁ u f := by
  intro D ψ hψ S B χS χT ω₂ H
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjSource (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint ω₂), χT⁻¹, χS⁻¹,
    GlobalTheory.ConjWeil.weil_conjSource D ψ S B _ _ _ (GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint D ψ B S _ _ ω₂ H),
    fun f hf => ?_⟩
  have e : (fun y : WO (negSp S) B => f (adjM S B y)) =
      GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S B) f) := by
    funext y; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_eq_adjM]
  rw [e]
  have h1 : IsThetaFunO ψ S B (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S B) f) :=
    ((GlobalTheory.AdjointPair.adjoint_clauses D ψ hψ B S).2.2.1 f).2 hf
  refine ⟨((GlobalTheory.CjNeg.theta_heis_neg D ψ hψ S B).1 _).2.2 h1, fun g₁ u => ?_⟩
  show GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjSource (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint ω₂) (negGA S u, g₁) _ 0 = ω₂ (g₁, u) f 0
  rw [GlobalTheory.ConjWeil.conjSource_apply]
  simp only [MulEquiv.symm_apply_apply, GlobalTheory.ConjWeil.cj_id_cj_id]
  rw [GlobalTheory.TensorTargetRule.conjAdjoint_cj]
  simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_eq_adjM, adjM_zero]

end GlobalTheory.AdjSwap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorIntegralPointVacuumRootOfUnitySmul
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.FunObj.StdDatum

theorem vacuum_int_root_of_unity : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ),
    e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) → ∀ (W : WeilO D ⊤ δ a d e0) (r : GA D a), r ∈ intG D a →
    ∃ c : ℂ, (∃ m : ℕ, 0 < m ∧ c ^ m = 1) ∧ W.Om r 1 e0 = c • e0 := by
  intro D δ crv a d e0 he W r hr
  obtain ⟨x, x', hx, hx', h⟩ := (GlobalTheory.NormSum.VacInt.vacuum_eigen D (GlobalTheory.InducedType.induced_type D).1 ⊤ δ crv a d e0 he W).2.1
    r hr 1 (one_mem _)
  obtain ⟨m, hm, hxm⟩ := (_root_.GlobalTheory.HeckeVal.hecke_values D d W.chV' x).2.1 hx
  obtain ⟨m', hm', hxm'⟩ := (_root_.GlobalTheory.HeckeVal.hecke_values D a W.chV x').2.1 hx'
  refine ⟨_, ⟨m * m', Nat.mul_pos hm hm', ?_⟩, h⟩
  rw [← Units.val_pow_eq_pow_val, mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul,
    mul_comm W.ep, mul_comm W.ep', zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, mul_comm m m', pow_mul, hxm', one_pow, one_zpow,
    mul_comm m' m, pow_mul, hxm, one_pow, one_zpow, one_mul, Units.val_one]

end GlobalTheory.FunObj.StdDatum
end

