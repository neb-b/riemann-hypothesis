module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationOfMemNotMemSq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricTestFunctionsAgreeRationalPoints
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
public import Formalism.LocalToGlobal.Columns.ChainTw

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockFiniteHeis

variable {D : D7}

theorem foldr_lin {ι X : Type} (p : (X → ℂ) → Prop) (A : ι → (X → ℂ) → (X → ℂ))
    (hp : ∀ i f, p f → p (A i f)) (hadd : ∀ i f g, p f → p g → A i (f + g) = A i f + A i g)
    (hsmul : ∀ i (c : ℂ) f, p f → A i (c • f) = c • A i f) (padd : ∀ f g, p f → p g → p (f + g))
    (psmul : ∀ (c : ℂ) f, p f → p (c • f)) (c : ℂ) {f g : X → ℂ} (hf : p f) (hg : p g) (l : List ι) :
    l.foldr (fun i h => A i h) (c • f + g) = c • l.foldr (fun i h => A i h) f + l.foldr (fun i h => A i h) g := by
  have hm : ∀ l : List ι, p (l.foldr (fun i h => A i h) f) ∧ p (l.foldr (fun i h => A i h) g) := by
    intro l
    induction l with
    | nil => exact ⟨hf, hg⟩
    | cons i l ih => exact ⟨hp i _ ih.1, hp i _ ih.2⟩
  induction l with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldr_cons, List.foldr_cons, List.foldr_cons, ih, hadd i _ _ (psmul c _ (hm l).1) (hm l).2,
      hsmul i c _ (hm l).1]

theorem pureTensorO_lin (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (c : ℂ) {f g : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ S T sS sT BS BT (c • f + g) φ =
      c • pureTensorO ψ θ S T sS sT BS BT f φ + pureTensorO ψ θ S T sS sT BS BT g φ := by
  have theta_add {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
      IsThetaFunO ψ S T (f + g) := by
    refine {
        quasi γ w := by simp only [Pi.add_apply, hf.quasi, hg.quasi, mul_add]
        level := by
          obtain ⟨U, hU, h1⟩ := hf.level
          obtain ⟨U', hU', h2⟩ := hg.level
          refine ⟨U ⊓ U', hU.inter hU', fun u hu h0 => ?_⟩
          funext w
          have e1 := congrFun (h1 u hu.1 h0) w
          have e2 := congrFun (h2 u hu.2 h0) w
          unfold heisO at e1 e2 ⊢
          rw [Pi.add_apply, Pi.add_apply, mul_add, e1, e2]
        cont := hf.cont.add hg.cont
        smooth k L h1 h2 w := (hf.smooth k L h1 h2 w).add (hg.smooth k L h1 h2 w)

    }
  have theta_smul (c : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) := by
    refine {
        quasi γ w := by
          rw [Pi.smul_apply, Pi.smul_apply, hf.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm]
        level := by
          obtain ⟨U, hU, h1⟩ := hf.level
          refine ⟨U, hU, fun u hu h0 => ?_⟩
          funext w
          have e1 := congrFun (h1 u hu h0) w
          unfold heisO at e1 ⊢
          rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, e1]
        cont := hf.cont.const_smul c
        smooth k L h1 h2 w := contDiff_const.mul (hf.smooth k L h1 h2 w)
    }
  have h : pureTensorO ψ θ S T sS sT BS BT (c • f + g) =
      c • pureTensorO ψ θ S T sS sT BS BT f + pureTensorO ψ θ S T sS sT BS BT g := by
    refine (MvPolynomial.basisMonomials _ ℂ).ext fun k => ?_
    rw [LinearMap.add_apply, LinearMap.smul_apply]
    unfold pureTensorO pureTensorL
    rw [Module.Basis.constr_basis, Module.Basis.constr_basis, Module.Basis.constr_basis]
    unfold opPow
    have A1 : ∀ k f, IsThetaFunO ψ S T f →
        IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT k f) :=
      fun k f hf => GlobalTheory.FockIndep.aPlus_theta hψ hθ k.1 (cplxO (sS k.1) (sT k.1)) _ hf
    have A2 : ∀ k f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g →
        aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT k (f + g) =
          aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT k f +
            aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT k g :=
      fun k f g hf hg => GlobalTheory.FockIndep.aPlus_add hψ hθ k.1 (cplxO (sS k.1) (sT k.1)) _ hf hg
    have A3 : ∀ k (c : ℂ) f, IsThetaFunO ψ S T f →
        aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT k (c • f) =
          c • aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT k f :=
      fun k c f hf => GlobalTheory.FockIndep.aPlus_smul hψ hθ k.1 (cplxO (sS k.1) (sT k.1)) _ c hf
    exact foldr_lin (IsThetaFunO ψ S T) (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) A1 A2 A3
      (fun _ _ hf hg => theta_add hf hg) (fun c _ hf => theta_smul c hf) c hf hg _
  rw [h, LinearMap.add_apply, LinearMap.smul_apply]

end GlobalTheory.FockFiniteHeis

namespace GlobalTheory.FockFiniteHeis

theorem pureTensorO_zero {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    pureTensorO ψ θ S T sS sT BS BT (0 : WO S T → ℂ) φ = 0 := by
  have theta_zero : IsThetaFunO ψ S T 0 := by
    refine {
        quasi γ w := by simp only [Pi.zero_apply, mul_zero]
        level := ⟨⊤, isOpen_univ, fun u _ _ => by funext w; simp only [heisO, Pi.zero_apply, mul_zero]⟩
        cont := continuous_const
        smooth k L _ _ w := contDiff_const

    }
  have h := pureTensorO_lin ψ θ S T hψ hθ sS BS sT BT (-1) theta_zero theta_zero φ
  rwa [smul_zero, add_zero, neg_one_smul, neg_add_cancel] at h

theorem heis_comb_pureTensorO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ sS sT BS BT (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ (n : ℕ) (a : Fin n → ℂ) (y : Fin n → WO S T), (∀ i, (y i).map (infPart D) = 0) → ∀ φ, ∑ i, a i • heisO ψ S T (y i) (pureTensorO ψ θ S T sS sT BS BT f φ) = pureTensorO ψ θ S T sS sT BS BT (∑ i, a i • heisO ψ S T (y i) f) φ ∧ pureTensorO ψ θ S T sS sT BS BT (0 : WO S T → ℂ) φ = 0 := by
  intro D ψ θ S T hψ hθ sS sT BS BT f hf n a y hy φ
  have theta_zero : IsThetaFunO ψ S T 0 := by
    refine {
        quasi γ w := by simp only [Pi.zero_apply, mul_zero]
        level := ⟨⊤, isOpen_univ, fun u _ _ => by funext w; simp only [heisO, Pi.zero_apply, mul_zero]⟩
        cont := continuous_const
        smooth k L _ _ w := contDiff_const

    }
  have theta_add {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) :
      IsThetaFunO ψ S T (f + g) := by
    refine {
        quasi γ w := by simp only [Pi.add_apply, hf.quasi, hg.quasi, mul_add]
        level := by
          obtain ⟨U, hU, h1⟩ := hf.level
          obtain ⟨U', hU', h2⟩ := hg.level
          refine ⟨U ⊓ U', hU.inter hU', fun u hu h0 => ?_⟩
          funext w
          have e1 := congrFun (h1 u hu.1 h0) w
          have e2 := congrFun (h2 u hu.2 h0) w
          unfold heisO at e1 e2 ⊢
          rw [Pi.add_apply, Pi.add_apply, mul_add, e1, e2]
        cont := hf.cont.add hg.cont
        smooth k L h1 h2 w := (hf.smooth k L h1 h2 w).add (hg.smooth k L h1 h2 w)

    }
  have theta_smul (c : ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (c • f) := by
    refine {
        quasi γ w := by
          rw [Pi.smul_apply, Pi.smul_apply, hf.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm]
        level := by
          obtain ⟨U, hU, h1⟩ := hf.level
          refine ⟨U, hU, fun u hu h0 => ?_⟩
          funext w
          have e1 := congrFun (h1 u hu h0) w
          unfold heisO at e1 ⊢
          rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, e1]
        cont := hf.cont.const_smul c
        smooth k L h1 h2 w := contDiff_const.mul (hf.smooth k L h1 h2 w)
    }
  have ft := GlobalTheory.FinTranslate.finite_translate D ψ θ S T hψ hθ f hf
  have hth : ∀ i, IsThetaFunO ψ S T (heisO ψ S T (y i) f) := fun i => (ft.2 (y i) (hy i)).1
  have key : ∀ s : Finset (Fin n), IsThetaFunO ψ S T (∑ i ∈ s, a i • heisO ψ S T (y i) f) ∧
      pureTensorO ψ θ S T sS sT BS BT (∑ i ∈ s, a i • heisO ψ S T (y i) f) φ =
        ∑ i ∈ s, a i • pureTensorO ψ θ S T sS sT BS BT (heisO ψ S T (y i) f) φ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      exact ⟨theta_zero, pureTensorO_zero ψ θ S T hψ hθ sS BS sT BT φ⟩
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      refine ⟨theta_add (theta_smul _ (hth i)) ih.1, ?_⟩
      rw [pureTensorO_lin ψ θ S T hψ hθ sS BS sT BT (a i) (hth i) ih.1 φ, ih.2]
  refine ⟨?_, pureTensorO_zero ψ θ S T hψ hθ sS BS sT BT φ⟩
  rw [(key Finset.univ).2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(ft.2 (y i) (hy i)).2 sS BS sT BT φ]

end GlobalTheory.FockFiniteHeis

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergThetaMixedModelTargetOfMixedModel
section
namespace I195MixedCoordinates_1f38ee5ffec15f714787e016

open Formalism.BasicNotions Formalism.BasicNotions.TH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.MixModel MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

public noncomputable abbrev source
    {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D T.rank ρ))
    (𝓕 : Set (Mx D T.rank ρ)) (f : WO S T → ℂ) (x : Mx D T.rank ρ) : WO S₀ T → ℂ :=
  fun w₀ => ∫ a in 𝓕, heisO ψ S T (a * d.pY)
    (heisO ψ S T (x * d.pX) (heisO ψ S T (w₀ * d.p0) f)) 0 ∂μ

public noncomputable abbrev target
    {D : D7} {T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (S : HSp D)
    (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D ρ S.rank))
    (𝓕 : Set (Mx D ρ S.rank)) (f : WO S T → ℂ) (y : Mx D S.rank ρ) : WO S T₀ → ℂ :=
  fun w₀ => ∫ ξ in 𝓕, heisO ψ S T (d.jX * ξ)
    (heisO ψ S T (d.jY * (incA D (-D.host.xi0⁻¹) • (adj y * gA S)))
      (heisO ψ S T (d.j0 * w₀) f)) 0 ∂μ

end I195MixedCoordinates_1f38ee5ffec15f714787e016

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.HeisTarget

variable {D : D7}

theorem symplOH_skew' (S T : HSp D) (x y : WO S T) : symplOH S T y x = -symplOH S T x y := by
  unfold symplOH; rw [GlobalTheory.OrientedHeis.symplO_skew, mul_neg]

theorem symplO_eq_two (S T : HSp D) (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  unfold symplOH
  rw [← add_mul, ← map_add (f := _), add_halves, map_one, one_mul]

variable {ψ : AddChar (AF D.host.F) ℂ} {S T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ)

theorem mixT_heis_incX {μ : Measure (Mx D ρ S.rank)} {𝓕 : Set (Mx D ρ S.rank)}
    (hμ : IsCovolOne (ratMx D ρ S.rank) μ 𝓕) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (ξ : Mx D ρ S.rank) (y : Mx D S.rank ρ) :
    (_root_.I195MixedCoordinates_1f38ee5ffec15f714787e016.target d) S ψ μ 𝓕 (heisO ψ S T (d.incX S ξ) f) y =
      ψ (symplO S T (d.incAdj S y) (d.incX S ξ)) • (_root_.I195MixedCoordinates_1f38ee5ffec15f714787e016.target d) S ψ μ 𝓕 f y := by
  funext w₀
  have key : ∀ ξ' : Mx D ρ S.rank,
      heisO ψ S T (d.incX S ξ') (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀)
        (heisO ψ S T (d.incX S ξ) f))) 0 =
      ψ (symplO S T (d.incAdj S y) (d.incX S ξ)) *
        heisO ψ S T (d.incX S (ξ' + ξ)) (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀) f)) 0 := by
    intro ξ'
    rw [HypDec.integrandT_eq, HypDec.integrandT_eq]
    simp only [heisO]
    rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, map_add (d.incX S)]
    congr 1
    · congr 1
      have h1 := d.symplOH_incX_incX S ξ' ξ
      have h2 : symplOH S T (d.inc0 S w₀) (d.incX S ξ) = 0 := by
        rw [symplOH_skew', d.wittDecomp_sympl_inclIsotropic_inclAnisotropic S ξ w₀, neg_zero]
      have h3 := symplOH_skew' S T (d.incAdj S y) (d.incX S ξ)
      simp only [GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right, h1, h2, h3,
        symplO_eq_two]
      ring
    · congr 1
      abel
  change ∫ ξ' in 𝓕, heisO ψ S T (d.incX S ξ') (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀) (heisO ψ S T (d.incX S ξ) f))) 0 ∂μ = ψ _ * ∫ ξ' in 𝓕, heisO ψ S T (d.incX S ξ') (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀) f)) 0 ∂μ
  simp_rw [key]
  rw [integral_const_mul]
  congr 1
  exact covolOne_integral_add hμ (fun ξ' => heisO ψ S T (d.incX S ξ') (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀) f)) 0)
    (d.integrandT_periodic hf y w₀) ξ

theorem mixedModelTarget_heisenberg_anisotropic_part {μ : Measure (Mx D ρ S.rank)} {𝓕 : Set (Mx D ρ S.rank)}
    (f : WO S T → ℂ) (v : WO S T₀) (y : Mx D S.rank ρ) :
    (_root_.I195MixedCoordinates_1f38ee5ffec15f714787e016.target d) S ψ μ 𝓕 (heisO ψ S T (d.inc0 S v) f) y = heisO ψ S T₀ v ((_root_.I195MixedCoordinates_1f38ee5ffec15f714787e016.target d) S ψ μ 𝓕 f y) := by
  funext w₀
  have key : ∀ ξ' : Mx D ρ S.rank,
      heisO ψ S T (d.incX S ξ') (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀)
        (heisO ψ S T (d.inc0 S v) f))) 0 =
      ψ (symplOH S T₀ w₀ v) *
        heisO ψ S T (d.incX S ξ') (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S (w₀ + v)) f)) 0 := by
    intro ξ'
    rw [HypDec.integrandT_eq, HypDec.integrandT_eq]
    simp only [heisO]
    rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, map_add (d.inc0 S)]
    congr 1
    · congr 1
      have h1 := d.wittDecomp_sympl_inclIsotropic_inclAnisotropic S ξ' v
      have h2 : symplOH S T (d.incAdj S y) (d.inc0 S v) = 0 := by
        rw [HypDec.incAdj_apply]; exact d.wittDecomp_sympl_inclDual_inclAnisotropic S _ v
      have h3 := d.wittDecomp_sympl_inclAnisotropic_inclAnisotropic S w₀ v
      simp only [GlobalTheory.OrientedHeis.symplOH_add_left, h1, h2, h3]
      ring
    · congr 1
      abel
  change ∫ ξ' in 𝓕, heisO ψ S T (d.incX S ξ') (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S w₀) (heisO ψ S T (d.inc0 S v) f))) 0 ∂μ = ψ _ * ∫ ξ' in 𝓕, heisO ψ S T (d.incX S ξ') (heisO ψ S T (d.incAdj S y) (heisO ψ S T (d.inc0 S (w₀ + v)) f)) 0 ∂μ
  simp_rw [key]
  rw [integral_const_mul]

end GlobalTheory.HeisTarget

namespace GlobalTheory.HeisTarget

variable {D : D7}

theorem hasSum_mixT {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T T₀ : HSp D} {ρ : ℕ}
    (d : HypDec T T₀ ρ) {μ : Measure (Mx D ρ S.rank)} {𝓕 : Set (Mx D ρ S.rank)}
    (hμ : IsCovolOne (ratMx D ρ S.rank) μ 𝓕) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    HasSum (fun y : Matrix (Fin S.rank) (Fin ρ) D.host.E => (_root_.I195MixedCoordinates_1f38ee5ffec15f714787e016.target d) S ψ μ 𝓕 f (rat y) 0) (f 0) := by
  obtain ⟨μ', 𝓕', hμ', -, -, -, hsw⟩ := _root_.GlobalTheory.MixSwap.mixS_cj_dagger D ψ hψ S T T₀ ρ d μ 𝓕 hμ
  have hg : IsThetaFunO ψ T S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S) f) :=
    ((_root_.GlobalTheory.AdjointPair.adjoint_clauses D ψ hψ S T).2.2.1 f).2 hf
  have h5 := (_root_.GlobalTheory.HeisMixSource.heis_mixS D ψ hψ T T₀ S ρ d ⟨μ', 𝓕', hμ'⟩ _ hg).2.2.2.2 0
  have hx : (D.host.xi0 : D.host.E) ≠ 0 := GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D
  let σ : Matrix (Fin S.rank) (Fin ρ) D.host.E ≃ Matrix (Fin S.rank) (Fin ρ) D.host.E :=
    { toFun := fun y => D.host.xi0⁻¹ • y
      invFun := fun y => D.host.xi0 • y
      left_inv := fun y => by simp only [smul_smul, mul_inv_cancel₀ hx, one_smul]
      right_inv := fun y => by simp only [smul_smul, inv_mul_cancel₀ hx, one_smul] }
  rw [← σ.hasSum_iff] at h5
  have e : ∀ y : Matrix (Fin S.rank) (Fin ρ) D.host.E,
      (_root_.I195MixedCoordinates_1f38ee5ffec15f714787e016.source d) S ψ μ' 𝓕' (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S) f) (rat (σ y)) 0 =
        starRingEnd ℂ ((_root_.I195MixedCoordinates_1f38ee5ffec15f714787e016.target d) S ψ μ 𝓕 f (rat y) 0) := by
    intro y
    show (_root_.I195MixedCoordinates_1f38ee5ffec15f714787e016.source d) S ψ μ' 𝓕' _ (rat (D.host.xi0⁻¹ • y)) 0 = _
    rw [rat_smul]
    have hh := congrFun (hsw f (rat y)) 0
    simpa only [I195MixedCoordinates_79cab7195843a34bfe21655d.source,
      I195MixedCoordinates_79cab7195843a34bfe21655d.target,
      I195MixedCoordinates_1f38ee5ffec15f714787e016.source,
      I195MixedCoordinates_1f38ee5ffec15f714787e016.target,
      GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj,
      GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger,
      adj_zero, Matrix.zero_mul, Matrix.mul_zero] using hh
  have h0 : GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S) f (d.ext0 S 0) = starRingEnd ℂ (f 0) := by
    simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger]
  simp only [Function.comp_def, e, h0] at h5
  exact Complex.hasSum_conj'.1 h5

theorem heisenbergTarget (D : D7) : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.HeisenbergTarget D := by
  intro ψ hψ S T T₀ ρ d μ 𝓕 hμ f hf
  exact ⟨fun ξ y => mixT_heis_incX d hμ hf ξ y, fun w₀ y => mixedModelTarget_heisenberg_anisotropic_part d f w₀ y, hasSum_mixT hψ d hμ hf⟩

theorem main : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.HeisenbergTarget D := heisenbergTarget

end GlobalTheory.HeisTarget

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.I0M
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.SBesEx

variable {D : D7}

def cY (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (y : (VS D).V) :
    Fin (D.sp.Y 0).rank → D.host.E :=
  fun k => X.ιE (X.crd y (Fin.cast (rank_eq X h) k))

def scl (t lam : D.host.E) (a : Fin D.R.rS) : D.host.E := t * lam ^ (D.R.rS - (a : ℕ))

def eM (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t lam : D.host.E) :
    Matrix (Fin (D.sp.Y 0).rank) (Fin D.R.rS) D.host.E :=
  fun k a => scl t lam a * cY X h (X.eX a) k

def e'M (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t lam : D.host.E) :
    Matrix (Fin (D.sp.Y 0).rank) (Fin D.R.rS) D.host.E :=
  fun k a => (star (scl t lam a))⁻¹ * cY X h (X.fY a) k

def qM (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    Matrix (Fin (D.sp.Y 0).rank) (Fin (D.sp.X 0).rank) D.host.E :=
  fun k j => X.ιE (X.crd (Formalism.L2.SG.ColDict.qFr wt (Fin.cast (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) j))
    (Fin.cast (rank_eq X h) k))

def zM (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (t : D.host.E) (L : HSp D) :
    Matrix (Fin (D.sp.Y 0).rank) (Fin L.rank) D.host.E :=
  fun k _ => t * cY X h (X.zu u) k

def i0M (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word)
    (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V) (t : D.host.E) {V₀ L : HSp D} (o : OrthDec V₀ (D.sp.X 0) L) :
    Matrix (Fin (D.sp.Y 0).rank) (Fin V₀.rank) D.host.E :=
  qM X h wt * o.qA + zM X h u t L * o.qB

def zeta (L : HSp D) : Fin L.rank → D.host.E := fun _ => 1

end GlobalTheory.Core.SBesEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdeleCharacterEqOneIntegralUnitsUnramifiedAdelic
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LFun

open GlobalTheory.Doubling GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem ideleAt_eq_prod_locIdele {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (x : (Fv F v ⊗[F] E)ˣ) :
    ideleAt F E v x = ∏ w ∈ (Formalism.L2.Host.finite_aboveF (L := E) F v).toFinset.attach,
      locIdele F w.1 (Units.map (toCompl ((Formalism.L2.Host.finite_aboveF (L := E) F v).mem_toFinset.1 w.2)).toMonoidHom x) := by
  classical
  have hc : ∀ u' : HeightOneSpectrum (𝓞 F), Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F u') (AlgHom.id F E)
      (finTens F E (ideleAt F E v x)) = (unitFin F E u' (ideleAt F E v x) : Fv F u' ⊗[F] E) := fun u' => by
    change ((Algebra.TensorProduct.map _ _).comp (Algebra.TensorProduct.map _ _)) _ = _
    rw [← Algebra.TensorProduct.map_comp]
    rfl
  refine Units.ext (tens_ext ?_ ((finAdEquiv F E).injective (FiniteAdeleRing.ext _ fun u => ?_)))
  · rw [Units.coe_prod, map_prod]
    simp only [infTens_locIdele, Finset.prod_const_one]
    exact map_extUnit_zero (fstA F) _ _ (fun a => rfl) x
  · rw [Units.coe_prod, map_prod (finTens F E), map_prod (finAdEquiv F E)]
    simp only [finTens_locIdele]
    change _ = evalV E u (∏ w ∈ (Formalism.L2.Host.finite_aboveF (L := E) F v).toFinset.attach, _)
    rw [map_prod]
    by_cases hu : u.under (𝓞 F) = v
    · rw [finAdEquiv_apply hu, hc, unitFin_ideleAt_self]
      have hm : u ∈ (Formalism.L2.Host.finite_aboveF (L := E) F v).toFinset :=
        (Formalism.L2.Host.finite_aboveF (L := E) F v).mem_toFinset.2 hu
      rw [Finset.prod_eq_single_of_mem ⟨u, hm⟩ (Finset.mem_attach _ _)]
      · exact (finSingle_self u _).symm
      · rintro b - hb
        exact finSingle_ne (fun e => hb (Subtype.ext e.symm)) _
    · rw [finAdEquiv_apply rfl, hc, unitFin_ideleAt_ne hu, Units.val_one, map_one]
      refine (Finset.prod_eq_one fun b _ => ?_).symm
      have hb : b.1.under (𝓞 F) = v := (Formalism.L2.Host.finite_aboveF (L := E) F v).mem_toFinset.1 b.2
      exact finSingle_ne (fun e : u = b.1 => hu (by rw [e]; exact hb)) _

theorem charAt_eq_one_of_unrAt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (μ : (AF F ⊗[F] E)ˣ →* Circle) (v : HeightOneSpectrum (𝓞 F)) (y : (Fv F v ⊗[F] E)ˣ)
    (hy : (y : Fv F v ⊗[F] E) ∈ intLoc F E v) (hy' : ((y⁻¹ : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) ∈ intLoc F E v)
    (hμ : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt μ w) : charAt μ v y = 1 := by
  show μ (ideleAt F E v y) = 1
  rw [ideleAt_eq_prod_locIdele, map_prod]
  refine Finset.prod_eq_one fun w _ => ?_
  have h : w.1.under (𝓞 F) = v := (Formalism.L2.Host.finite_aboveF (L := E) F v).mem_toFinset.1 w.2
  have hu : Formalism.L2.Host.IsUnitAt w.1 (Units.map (toCompl h).toMonoidHom y) := by
    refine (EulerTie.isUnitAt_iff w.1 _).2 ⟨?_, ?_⟩
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (InertChart.toCompl_mem h hy)
    · rw [← map_inv]
      exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (InertChart.toCompl_mem h hy')
  have := hμ w.1 h _ hu
  exact Circle.ext (congrArg Units.val this)

end GlobalTheory.LFun

theorem GlobalTheory.LFun.charAt_eq_one_of_unrAt_datum : ∀ (D : D7) (μ : (AE D)ˣ →* Circle) (v : FinPl D) (y : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ), (y : Fv D.host.F v ⊗[D.host.F] D.host.E) ∈ intLoc D.host.F D.host.E v → ((y⁻¹ : (Fv D.host.F v ⊗[D.host.F] D.host.E)ˣ) : Fv D.host.F v ⊗[D.host.F] D.host.E) ∈ intLoc D.host.F D.host.E v → (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt μ w) → charAt μ v y = 1 := by
  intro D μ v y hy hy' hμ
  exact GlobalTheory.LFun.charAt_eq_one_of_unrAt μ v y hy hy' hμ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricTestFunctionsAgreeRationalPointsStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parahoric_test_functions_agree_rational_points : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → PhiAgree Ch sel mu cst σ₀ P ι s W := by
  first | exact @GlobalTheory.TwBridge.PhiProof.phiAgree_of_atTwist | exact GlobalTheory.TwBridge.PhiProof.phiAgree_of_atTwist | (intros; apply GlobalTheory.TwBridge.PhiProof.phiAgree_of_atTwist <;> assumption)
end

