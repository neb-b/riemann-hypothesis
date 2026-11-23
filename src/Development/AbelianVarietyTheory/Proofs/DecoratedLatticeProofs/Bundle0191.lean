module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0168
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairOperatorStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0090
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateDecayRealEntries
section
namespace I195MixedCoordinates_0369f17677cfefcc2f91e8fc

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

end I195MixedCoordinates_0369f17677cfefcc2f91e8fc

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.Unf

theorem mixS_decay : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (N : ℕ), ∃ C : ℝ≥0, ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ x w, ‖d.mixS T ψ v.μ v.𝓕 f x w‖ₑ * ENNReal.ofReal ((1 + realSize θ x) ^ N) ≤ C * supSob ψ θ N f := by
  intro D ψ hψ θ hθ S S₀ T ρ d v N
  obtain ⟨k, τs, zs, K, hK⟩ := _root_.GlobalTheory.RealPairBound.realSize_le_pairing D θ T ρ
  choose Z hZ using fun i => _root_.GlobalTheory.Unf.norm_mixS_dRho_ge D ψ hψ θ hθ S S₀ T ρ d v (τs i) (zs i)
  have hsf := _root_.GlobalTheory.Unf.SupFin.supSob_laws D ψ hψ θ hθ S T
  choose Cd hCd using fun i => (hsf.2.1 (τs i) (Z i)).2
  induction N with
  | zero =>
    refine ⟨1, fun f hf x w => ?_⟩
    rw [pow_zero, ENNReal.ofReal_one, mul_one, ENNReal.coe_one, one_mul]
    have hs : supSob ψ θ 0 f = ⨆ w, ‖f w‖ₑ := GlobalTheory.Size.wordSum_zero _ _ _
    rw [hs]
    calc _ ≤ ∫⁻ a in v.𝓕, ‖heisO ψ S T (d.extY T a) (heisO ψ S T (d.extX T x) (heisO ψ S T (d.ext0 T w) f)) 0‖ₑ ∂v.μ :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ _ in v.𝓕, (⨆ w, ‖f w‖ₑ) ∂v.μ := lintegral_mono fun a => by
          rw [d.integrandS_eq, enorm_mul]
          have h1 : ‖ψ (symplOH S T (d.extY T a) (d.extX T x))‖ₑ = 1 := by
            rw [← ofReal_norm_eq_enorm, hψ.1.2.1, ENNReal.ofReal_one]
          rw [h1, one_mul]
          exact le_iSup (fun w => ‖f w‖ₑ) _
      _ = _ := by rw [setLIntegral_const, v.covol.2.2, mul_one]
  | succ N ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨C + K.toNNReal * ∑ i, C * Cd i, fun f hf x w => ?_⟩
    set R := realSize θ x with hRdef
    have hR0 : 0 ≤ R := realSize_nonneg θ x
    set M := (_root_.I195MixedCoordinates_0369f17677cfefcc2f91e8fc.source d) T ψ v.μ v.𝓕 f x w
    set s := supSob ψ θ (N + 1) f
    have hNs : supSob ψ θ N f ≤ s := GlobalTheory.Size.wordSum_mono (Nat.le_succ N) f
    have hpow : ENNReal.ofReal ((1 + R) ^ (N + 1)) =
        ENNReal.ofReal ((1 + R) ^ N) + ENNReal.ofReal R * ENNReal.ofReal ((1 + R) ^ N) := by
      rw [← ENNReal.ofReal_mul hR0, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    have hA : ‖M‖ₑ * ENNReal.ofReal ((1 + R) ^ N) ≤ C * s := (hC f hf x w).trans (by gcongr)
    have hRle : ENNReal.ofReal R ≤ K.toNNReal * ∑ i, ENNReal.ofReal |2 * (tauE D (τs i) D.host.xi0 *
        ((compAt θ (τs i) x)ᴴ * gramAt D T (τs i) * zs i).trace).re| := by
      refine (ENNReal.ofReal_le_ofReal (hK x)).trans (le_of_eq ?_)
      rw [ENNReal.ofReal_mul' (Finset.sum_nonneg fun i _ => abs_nonneg _),
        ENNReal.ofReal_sum_of_nonneg fun i _ => abs_nonneg _]
      rfl
    have hi : ∀ i, ENNReal.ofReal |2 * (tauE D (τs i) D.host.xi0 *
        ((compAt θ (τs i) x)ᴴ * gramAt D T (τs i) * zs i).trace).re| * (‖M‖ₑ * ENNReal.ofReal ((1 + R) ^ N)) ≤
        C * Cd i * s := fun i => by
      have hDf := GlobalTheory.OrientedHeis.theta_dRho hθ hψ (τs i) (Z i) hf
      rw [← mul_assoc, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (abs_nonneg _)]
      calc _ ≤ ‖d.mixS T ψ v.μ v.𝓕 (dRho (heisO ψ S T) θ (τs i) (Z i) f) x w‖ₑ * ENNReal.ofReal ((1 + R) ^ N) := by
            gcongr
            rw [← ofReal_norm_eq_enorm]
            exact ENNReal.ofReal_le_ofReal (hZ i f hf x w)
        _ ≤ C * supSob ψ θ N (dRho (heisO ψ S T) θ (τs i) (Z i) f) := hC _ hDf x w
        _ ≤ C * (Cd i * s) := by gcongr; exact hCd i N f hf
        _ = C * Cd i * s := (mul_assoc _ _ _).symm
    calc ‖M‖ₑ * ENNReal.ofReal ((1 + R) ^ (N + 1))
        = ‖M‖ₑ * ENNReal.ofReal ((1 + R) ^ N) + ENNReal.ofReal R * (‖M‖ₑ * ENNReal.ofReal ((1 + R) ^ N)) := by
          rw [hpow, mul_add, mul_left_comm]
      _ ≤ C * s + (K.toNNReal * ∑ i, ENNReal.ofReal |2 * (tauE D (τs i) D.host.xi0 *
            ((compAt θ (τs i) x)ᴴ * gramAt D T (τs i) * zs i).trace).re|) * (‖M‖ₑ * ENNReal.ofReal ((1 + R) ^ N)) :=
          add_le_add hA (by gcongr)
      _ ≤ C * s + K.toNNReal * ∑ i, (C * Cd i * s : ℝ≥0∞) := by
          rw [mul_assoc, Finset.sum_mul]
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hi i) zero_le)
      _ = _ := by
          push_cast
          rw [add_mul, mul_assoc, Finset.sum_mul]

end GlobalTheory.Unf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrthDecSumLatticeSelfDual
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.Core.Rk.SumBox

noncomputable section

namespace GlobalTheory.Core.Rk.SumBox

variable {D : D7}

theorem pair_eq_dot (n : ℕ) (G : Matrix (Fin n) (Fin n) D.host.E) (x y : Fin n → D.host.E) :
    ∑ i, ∑ j, star (x i) * G i j * y j = star x ⬝ᵥ (G *ᵥ y) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]

theorem pair_iA {B W H : HSp D} (o : OrthDec B W H) (x : Fin W.rank → D.host.E) (y : Fin B.rank → D.host.E) :
    ∑ i, ∑ j, star ((o.iA *ᵥ x) i) * B.gram i j * y j = ∑ i, ∑ j, star (x i) * W.gram i j * (o.qA *ᵥ y) j := by
  have hq : W.gram * o.qA = o.iAᴴ * B.gram := by
    rw [OrthDec.qA, Matrix.mul_nonsing_inv_cancel_left _ _ (gram_isUnit_det W)]
  rw [pair_eq_dot, pair_eq_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hq]

theorem pair_iB {B W H : HSp D} (o : OrthDec B W H) (x : Fin H.rank → D.host.E) (y : Fin B.rank → D.host.E) :
    ∑ i, ∑ j, star ((o.iB *ᵥ x) i) * B.gram i j * y j = ∑ i, ∑ j, star (x i) * H.gram i j * (o.qB *ᵥ y) j :=
  pair_iA o.symm x y

theorem split_vec {B W H : HSp D} (o : OrthDec B W H) (y : Fin B.rank → D.host.E) :
    o.iA *ᵥ (o.qA *ᵥ y) + o.iB *ᵥ (o.qB *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, o.iA_qA_add, Matrix.one_mulVec]

theorem qA_split {B W H : HSp D} (o : OrthDec B W H) (x : Fin W.rank → D.host.E) (x' : Fin H.rank → D.host.E) :
    o.qA *ᵥ (o.iA *ᵥ x + o.iB *ᵥ x') = x := by
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, o.qA_iA, o.qA_iB, Matrix.one_mulVec,
    Matrix.zero_mulVec, add_zero]

theorem qB_split {B W H : HSp D} (o : OrthDec B W H) (x : Fin W.rank → D.host.E) (x' : Fin H.rank → D.host.E) :
    o.qB *ᵥ (o.iA *ᵥ x + o.iB *ᵥ x') = x' := by
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, o.qB_iA, o.qB_iB, Matrix.one_mulVec,
    Matrix.zero_mulVec, zero_add]

theorem iA_mem_sumLatO {B W H : HSp D} (o : OrthDec B W H) {LW : Lat W} (LH : Lat H) {x : Fin W.rank → D.host.E}
    (hx : x ∈ LW) : o.iA *ᵥ x ∈ sumLatO o LW LH :=
  (mem_sumLatO o LW LH _).2 ⟨x, hx, 0, zero_mem _, by rw [Matrix.mulVec_zero, add_zero]⟩

theorem iB_mem_sumLatO {B W H : HSp D} (o : OrthDec B W H) (LW : Lat W) {LH : Lat H} {x : Fin H.rank → D.host.E}
    (hx : x ∈ LH) : o.iB *ᵥ x ∈ sumLatO o LW LH :=
  (mem_sumLatO o LW LH _).2 ⟨0, zero_mem _, x, hx, by rw [Matrix.mulVec_zero, zero_add]⟩

theorem isLattice_sumLatO {B W H : HSp D} (o : OrthDec B W H) (LW : Lat W) (LH : Lat H)
    (hW : Submodule.IsLattice D.host.E LW) (hH : Submodule.IsLattice D.host.E LH) :
    Submodule.IsLattice D.host.E (sumLatO o LW LH) := by
  exact Submodule.IsLattice.of_fg D.host.E ((hW.fg.map _).sup (hH.fg.map _))

theorem selfDual_sumLatO : ∀ (D : D7) (B W H : HSp D) (o : OrthDec B W H) (LW : Lat W) (LH : Lat H),
    IsSelfDualC W LW → IsSelfDualC H LH → IsSelfDualC B (sumLatO o LW LH) := by
  intro D B W H o LW LH hW hH
  refine ⟨isLattice_sumLatO o LW LH hW.1 hH.1, fun y => ⟨fun hy x hx => ?_, fun hy => ?_⟩⟩
  · obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := (mem_sumLatO o LW LH y).1 hy
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := (mem_sumLatO o LW LH x).1 hx
    obtain ⟨b₁, hb₁⟩ := (hW.2 y₁).1 hy₁ x₁ hx₁
    obtain ⟨b₂, hb₂⟩ := (hH.2 y₂).1 hy₂ x₂ hx₂
    refine ⟨b₁ + b₂, ?_⟩
    have e : ∑ i, ∑ j, star ((o.iA *ᵥ x₁ + o.iB *ᵥ x₂) i) * B.gram i j * (o.iA *ᵥ y₁ + o.iB *ᵥ y₂) j =
        ∑ i, ∑ j, star ((o.iA *ᵥ x₁) i) * B.gram i j * (o.iA *ᵥ y₁ + o.iB *ᵥ y₂) j +
          ∑ i, ∑ j, star ((o.iB *ᵥ x₂) i) * B.gram i j * (o.iA *ᵥ y₁ + o.iB *ᵥ y₂) j := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.add_apply, star_add]
      ring
    rw [e, pair_iA, pair_iB, qA_split, qB_split, ← hb₁, ← hb₂]
    push_cast
    ring
  · have hA : o.qA *ᵥ y ∈ LW := (hW.2 _).2 fun x hx => by
      obtain ⟨b, hb⟩ := hy _ (iA_mem_sumLatO o LH hx)
      exact ⟨b, hb.trans (pair_iA o x y)⟩
    have hB : o.qB *ᵥ y ∈ LH := (hH.2 _).2 fun x hx => by
      obtain ⟨b, hb⟩ := hy _ (iB_mem_sumLatO o LW hx)
      exact ⟨b, hb.trans (pair_iB o x y)⟩
    rw [← split_vec o y]
    exact (mem_sumLatO o LW LH _).2 ⟨_, hA, _, hB, rfl⟩

end GlobalTheory.Core.Rk.SumBox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PushforwardHaarRealPointsTimesLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

namespace GlobalTheory.ChainOnto.HaarInf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem finE_of_mem_ginfC (V : HSp D) {x : GA D V} (hx : x ∈ GinfC V) : Lev.finE V x = 1 := by
  simp only [Lev.finE, MonoidHom.comp_apply]
  rw [show finHom V x = 1 from hx, map_one]

theorem finE_toFin (V : HSp D) (g : GA D V) : Lev.finE V (GlobalTheory.AutMult.toFin V g : GA D V) = Lev.finE V g := by
  conv_rhs => rw [← GlobalTheory.AutMult.toInf_mul_toFin g]
  rw [map_mul, finE_of_mem_ginfC V (GlobalTheory.AutMult.toInf V g).2, one_mul]

theorem proj_of_mem_ginfC (V : HSp D) (x : GinfC V) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v (x : GA D V) = 1 := by
  rw [← GlobalTheory.AutMult.toInf_coe x]
  exact GlobalTheory.AdelicU.proj_ofInf _ _ v _

theorem toInf_eq_one_iff (V : HSp D) (g : GA D V) : GlobalTheory.AutMult.toInf V g = 1 ↔ g ∈ GfC V := by
  refine ⟨fun h => ?_, fun h => by simpa using GlobalTheory.AutMult.toInf_coe_fin (⟨g, h⟩ : GfC V)⟩
  have e := GlobalTheory.AutMult.toInf_mul_toFin g
  rw [h, OneMemClass.coe_one, one_mul] at e
  exact e ▸ (GlobalTheory.AutMult.toFin V g).2

theorem pushforward_haar_real : ∀ D : D7, LevFacts D → ForStage D fun c _ s => MeasurableSet (intOff c s) ∧ MeasurableSet {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L} ∧ {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L} ⊆ intOff c s ∧ (∀ g : GA D s.V, Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L → ∃ b : GinfC s.V, ∃ κ ∈ Lev.levG s.V s.β s.L, g = (b : GA D s.V) * κ) ∧ ∃ mR : Measure (GinfC s.V), mR.IsHaarMeasure ∧ ∀ (f : GinfC s.V → ℂ) (F : GA D s.V → ℂ), Integrable f mR → (∀ (b : GinfC s.V), ∀ κ ∈ Lev.levG s.V s.β s.L, F ((b : GA D s.V) * κ) = f b) → IntegrableOn F {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L} s.ν ∧ ∫ g in {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L}, F g ∂s.ν = ∫ b, f b ∂mR := by
  intro D hL c hc j hj s hs
  obtain ⟨h1, -, h3, -, -, -⟩ := hL c hc j hj s hs
  haveI := hs.haar
  set V := s.V
  set K := Lev.levG s.V s.β s.L
  let A : Subgroup (GA D V) := (Formalism.L2.DIV.lev D.sp.cm V.gram s.β s.L).comap (Lev.finE V)
  have hAset : (A : Set (GA D V)) = {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L} := rfl

  have hfinK : ∀ g ∈ A, (GlobalTheory.AutMult.toFin V g : GA D V) ∈ K := fun g hg =>
    ⟨(GlobalTheory.AutMult.toFin V g).2, Subgroup.mem_comap.2 (by rw [finE_toFin]; exact Subgroup.mem_comap.1 hg)⟩

  have hAopen : IsOpen (A : Set (GA D V)) := by
    obtain ⟨U, hU, hUK⟩ := h1
    let Lf : Subgroup (GfC V) := K.subgroupOf (GfC V)
    have hLf : IsOpen (Lf : Set (GfC V)) := by
      refine Subgroup.isOpen_mono (H₁ := U.subgroupOf (GfC V)) (fun k hk => ?_) (hU.preimage continuous_subtype_val)
      exact (hUK k hk k.2).1
    have e : (A : Set (GA D V)) = GlobalTheory.AutMult.toFin V ⁻¹' (Lf : Set (GfC V)) := by
      ext g
      refine ⟨fun hg => hfinK g hg, fun hg => ?_⟩
      have := Subgroup.mem_comap.1 hg.2
      refine Subgroup.mem_comap.2 ?_
      rw [← finE_toFin]; exact this
    rw [e]; exact hLf.preimage (GlobalTheory.AutMult.continuous_toFin V)

  have hAint : (A : Set (GA D V)) ⊆ intOff c s := by
    intro g hg v _
    rw [← GlobalTheory.AutMult.toInf_mul_toFin g, map_mul, proj_of_mem_ginfC, one_mul]
    exact h3 _ (hfinK g hg) v

  let I : Subgroup (GA D V) :=
    { carrier := intOff c s
      mul_mem' := fun {a b} ha hb v hv => by rw [map_mul]; exact mul_mem (ha v hv) (hb v hv)
      one_mem' := fun v _ => by rw [map_one]; exact one_mem _
      inv_mem' := fun {a} ha v hv => by rw [map_inv]; exact inv_mem (ha v hv) }
  have hIopen : IsOpen (I : Set (GA D V)) := Subgroup.isOpen_mono (H₁ := A) hAint hAopen

  have hker : {g : GA D V | g ∈ A ∧ GlobalTheory.AutMult.toInf V g = 1} = (K : Set (GA D V)) := by
    ext g
    simp only [Set.mem_setOf_eq, toInf_eq_one_iff]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have hKc : IsCompact (K : Set (GA D V)) :=
    GlobalTheory.T.isCompact_finite_adelic_subgroup_integral_open D V s.Λ hs.selfDual K inf_le_left h3 (by
      obtain ⟨U, hU, hUK⟩ := h1
      exact ⟨U, hU, fun k hk hk' => (hUK k hk hk').1⟩)
  have hpi : ∀ b : GinfC V, GlobalTheory.AutMult.toInf V ((GinfC V).subtype b) = b := fun b => GlobalTheory.AutMult.toInf_coe b
  have hiA : ∀ b : GinfC V, (GinfC V).subtype b ∈ A := fun b => by
    refine Subgroup.mem_comap.2 ?_
    rw [Subgroup.subtype_apply, finE_of_mem_ginfC V b.2]; exact one_mem _
  have hHaar : (Measure.map (GlobalTheory.AutMult.toInf V) (s.ν.restrict (A : Set (GA D V)))).IsHaarMeasure :=
    _root_.GlobalTheory.ChainOnto.map_restrict_isHaar (GA D V) (GinfC V) s.ν A (GinfC V).subtype (GlobalTheory.AutMult.toInf V) hAopen
      continuous_subtype_val (GlobalTheory.AutMult.continuous_toInf V) hpi hiA (hker ▸ hKc)
  refine ⟨hIopen.measurableSet, hAopen.measurableSet, hAint, fun g hg => ?_, ?_⟩
  · exact ⟨GlobalTheory.AutMult.toInf V g, GlobalTheory.AutMult.toFin V g, hfinK g hg, (GlobalTheory.AutMult.toInf_mul_toFin g).symm⟩
  refine ⟨_, hHaar, fun f F hf hF => ?_⟩
  have hmeas : AEMeasurable (GlobalTheory.AutMult.toInf V) (s.ν.restrict (A : Set (GA D V))) :=
    (GlobalTheory.AutMult.continuous_toInf V).measurable.aemeasurable
  have hFA : ∀ g ∈ (A : Set (GA D V)), F g = f (GlobalTheory.AutMult.toInf V g) := fun g hg => by
    conv_lhs => rw [← GlobalTheory.AutMult.toInf_mul_toFin g]
    exact hF _ _ (hfinK g hg)
  have hint : IntegrableOn (fun g => f (GlobalTheory.AutMult.toInf V g)) (A : Set (GA D V)) s.ν :=
    (integrable_map_measure hf.aestronglyMeasurable hmeas).1 hf
  refine ⟨hint.congr_fun (fun g hg => (hFA g hg).symm) hAopen.measurableSet, ?_⟩
  rw [← hAset, setIntegral_congr_fun hAopen.measurableSet hFA, integral_map hmeas hf.aestronglyMeasurable]

end GlobalTheory.ChainOnto.HaarInf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamUnitaryHolds
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.RamUnit

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n]

def pet (vS : Vol S) (ψ ψ' : Form k n (GA D S → ℂ)) (P : Pair k n) : ℂ :=
  ∫ g in vS.𝓕, ψ P g * star (ψ' P g) ∂vS.μ

theorem rep_apply (β : Frame p S n) (g : GL n k) (f : GA D S → ℂ) (x : GA D S) :
    β.rep g f x = f (x * β.gl g) := rfl

theorem pet_const (vS : Vol S) (β : Frame p S n) {ψ ψ' : Form k n (GA D S → ℂ)} (hψ : ψ ∈ EqForm β.rep)
    (hψ' : ψ' ∈ EqForm β.rep) (hl : ∀ P, ∀ γ ∈ GQ S, ∀ g, ψ P (γ * g) = ψ P g)
    (hl' : ∀ P, ∀ γ ∈ GQ S, ∀ g, ψ' P (γ * g) = ψ' P g) (P Q : Pair k n) : pet vS ψ ψ' P = pet vS ψ ψ' Q := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (GL n k) P Q
  unfold pet
  rw [hψ g P, hψ' g P]
  simp only [rep_apply]
  exact (GlobalTheory.ChainOnto.setIntegral_fd_mul_right D S vS.μ vS.𝓕 vS.haar vS.fund (fun x => ψ P x * star (ψ' P x))
    (fun γ hγ x => by simp only [hl P γ hγ, hl' P γ hγ]) (β.gl g)).symm

theorem sum_pet_FFStar (vS : Vol S) (hS : CoCpt S) (q : Unif k) (χ : AddChar 𝓀[k] ℂ)
    (hχ : ∀ a, (starRingEnd ℂ) (χ a) = χ (-a))
    {φ ψ : Form k n (GA D S → ℂ)} (hφ : ∀ P, IsContAut S (φ P)) (hψ : ∀ P, IsContAut S (ψ P))
    (L : Submodule 𝒪[k] (n → k)) :
    ∑ P ∈ withLat L, pet vS (FFStar q χ φ) ψ P = ∑ P₁ ∈ withKer L, pet vS φ (FF q χ ψ) P₁ := by
  have hint : ∀ P₁ P, IntegrableOn (fun g => φ P₁ g * star (ψ P g)) vS.𝓕 vS.μ := fun P₁ P =>
    (GlobalTheory.CocompactParam.continuous_integral_param D S hS vS Unit (fun g _ => φ P₁ g * star (ψ P g))
      (((hφ P₁).2.mul (hψ P).2.star).comp continuous_fst)
      (fun γ hγ g _ => by simp only [(hφ P₁).1 γ hγ, (hψ P).1 γ hγ])).1 ()
  have e1 : ∀ P ∈ withLat L, pet vS (FFStar q χ φ) ψ P =
      ∑ P₁ ∈ withKer L, χ (-cross q P₁ P) * ∫ g in vS.𝓕, φ P₁ g * star (ψ P g) ∂vS.μ := by
    intro P hP
    rw [mem_withLat] at hP
    unfold pet
    rw [FFStar_apply, hP]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]
    rw [integral_finsetSum _ (fun P₁ _ => (hint P₁ P).const_mul _)]
    exact Finset.sum_congr rfl fun P₁ _ => integral_const_mul _ _
  have e2 : ∀ P₁ ∈ withKer L, pet vS φ (FF q χ ψ) P₁ =
      ∑ P ∈ withLat L, χ (-cross q P₁ P) * ∫ g in vS.𝓕, φ P₁ g * star (ψ P g) ∂vS.μ := by
    intro P₁ hP₁
    rw [mem_withKer] at hP₁
    unfold pet
    rw [FF_apply, hP₁]
    have : ∀ g, φ P₁ g * star ((∑ P ∈ withLat L, χ (cross q P₁ P) • ψ P) g) =
        ∑ P ∈ withLat L, χ (-cross q P₁ P) * (φ P₁ g * star (ψ P g)) := fun g => by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_sum, Finset.mul_sum, star_mul']
      refine Finset.sum_congr rfl fun P _ => ?_
      rw [← hχ]
      change φ P₁ g * ((starRingEnd ℂ) (χ (cross q P₁ P)) * star (ψ P g)) = _
      ring
    simp only [this]
    rw [integral_finsetSum _ (fun P _ => (hint P₁ P).const_mul _)]
    exact Finset.sum_congr rfl fun P _ => integral_const_mul _ _
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_comm]

end GlobalTheory.FinPl.RamUnit

namespace GlobalTheory.FinPl.RamUnit

theorem ramUnitary_holds : ∀ D : D7, GlobalTheory.FinPl.RamUnitary D := by
  intro D k _ _ _ _ p n _ _ q χ hχ ε S hS vS β P φ₀ φ₀' hφ₀ hφ₀'
  obtain ⟨φ, hφ, rfl⟩ := hφ₀
  obtain ⟨φ', hφ', rfl⟩ := hφ₀'
  have hB := GlobalTheory.FinPl.ramBijective_holds D k p n q χ hχ (resChar χ hχ q) rfl ε S β P
  obtain ⟨hA, eA⟩ := hB.2.1 φ hφ
  obtain ⟨hA', eA'⟩ := hB.2.1 φ' hφ'
  rw [eA, eA']
  have hO : OperatorIdentities k n (GA D S → ℂ) q (resChar χ hχ q) :=
    ((GlobalTheory.PairOp.pairOperatorStatement k q χ hχ n).1 (GA D S → ℂ)).2
  set X := FFStar q (resChar χ hχ q) φ with hX
  set X' := FFStar q (resChar χ hχ q) φ' with hX'
  have cX : ∀ Q, IsContAut S (X Q) := fun Q => by
    have := hA.2.2 (ε⁻¹ • Q)
    rwa [dia_apply, smul_inv_smul] at this
  have cX' : ∀ Q, IsContAut S (X' Q) := fun Q => by
    have := hA'.2.2 (ε⁻¹ • Q)
    rwa [dia_apply, smul_inv_smul] at this
  have eFF : FF q (resChar χ hχ q) X' = ((resCard k : ℂ) ^ Fintype.card n) • φ' := hO.FF_FFStar_ram φ' hφ'.2.1
  have c2 : ∀ Q, IsContAut S ((FF q (resChar χ hχ q) X') Q) := fun Q => by
    rw [eFF]
    exact ⟨fun γ hγ g => by simp only [Pi.smul_apply, smul_eq_mul, (hφ'.2.2 Q).1 γ hγ],
      continuous_const.mul (hφ'.2.2 Q).2⟩
  have hsum := sum_pet_FFStar vS hS q (resChar χ hχ q) (conj_resChar hχ q) hφ.2.2 cX' P.lat
  have k1 : ∀ Q ∈ withLat P.lat, pet vS X X' Q = pet vS X X' (ε • P) := fun Q _ =>
    pet_const vS β (FFStar_mem_EqForm q _ hφ.1) (FFStar_mem_EqForm q _ hφ'.1) (fun Q => (cX Q).1)
      (fun Q => (cX' Q).1) Q (ε • P)
  have k2 : ∀ Q ∈ withKer P.lat, pet vS φ (FF q (resChar χ hχ q) X') Q = pet vS φ (FF q (resChar χ hχ q) X') P :=
    fun Q _ => pet_const vS β hφ.1 (FF_mem_EqForm q _ (FFStar_mem_EqForm q _ hφ'.1)) (fun Q => (hφ.2.2 Q).1)
      (fun Q => (c2 Q).1) Q P
  have hcard : (withLat P.lat).card = (withKer P.lat).card := by
    classical
    have e : Red P.lat ≃ₗ[𝓀[k]] Module.Dual 𝓀[k] (Red P.lat) :=
      (Module.Free.chooseBasis 𝓀[k] (Red P.lat)).toDualEquiv
    have e' : {x : Red P.lat // x ≠ 0} ≃ {f : Module.Dual 𝓀[k] (Red P.lat) // f ≠ 0} :=
      e.toEquiv.subtypeEquiv (fun x => by simp)
    refine Finset.card_eq_of_equiv ?_
    exact (Equiv.subtypeEquivRight (fun P => mem_withLat)).trans
      ((latEquiv P.lat).symm.trans (e'.symm.trans ((kerEquiv P.lat q).trans
        (Equiv.subtypeEquivRight (fun P => mem_withKer.symm)))))
  rw [Finset.sum_congr rfl k1, Finset.sum_congr rfl k2, Finset.sum_const, Finset.sum_const,
    ← hcard] at hsum
  have hN : (withLat P.lat).card ≠ 0 := (Finset.card_pos.2 ⟨P, mem_withLat.2 rfl⟩).ne'
  have hpe : pet vS X X' (ε • P) = pet vS φ (FF q (resChar χ hχ q) X') P := by
    rw [← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ] at hsum
    exact smul_right_injective ℂ (Nat.cast_ne_zero.2 hN) hsum
  change pet vS X X' (ε • P) = _
  rw [hpe, eFF]
  unfold pet
  simp only [Pi.smul_apply, smul_eq_mul, star_mul', star_pow, Complex.star_def, Complex.conj_natCast]
  rw [← integral_const_mul]
  congr 1
  funext g
  ring

end GlobalTheory.FinPl.RamUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalParameterBoundNonsplitPlacesStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalParameterBound_nonsplit_places : GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.UnramDoublingInert → ∀ D : D7, ParamBoundOn D fun v => ¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  first | exact @GlobalTheory.Core.Rk.ParamInert.paramBoundOn_nonsplit | exact GlobalTheory.Core.Rk.ParamInert.paramBoundOn_nonsplit | (intros; apply GlobalTheory.Core.Rk.ParamInert.paramBoundOn_nonsplit <;> assumption)
end

