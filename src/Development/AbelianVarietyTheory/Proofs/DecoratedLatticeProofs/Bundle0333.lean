module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValDetSubOneLt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TildeQDetPtEqChiId
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0777
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0291
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0255
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0091
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0050
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0221
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MoveRationalInvariant
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0321
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableMajorantCoordinateCosetMeasure
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0134
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0438
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralDefiniteQuotientEqClassSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0310
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainMoveCharactersEqRhoUpToBase
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.AdForm.TwDat


set_option maxHeartbeats 800000 in
theorem chr_root_mul_base {B : Base} {X : PreX B.toPre} {I : TC B X} (hI : I.Ok) {l : I.Laws} {Z : TC.Later B (I.cols l)}
    {u : B.Word} {a : I.ι} {Ch : ℕ → Type} {A : TwDat I l Z u a Ch} (hA : A.Is) (j : Fin B.R.m) (k : ℕ) (hk : k ≤ B.R.m)
    (β : Ch k) (c : {c // A.chOf k c = β}) (x : (AE (I.rec7 l Z))ˣ) (hx : IsDetRoot _ (A.h k β c) x) :
    (A.chr ((j : ℕ) + 1) x : ℂ) * (A.chr ((j : ℕ) + 1) (A.xr k β) : ℂ) =
      ((tildeQ B.host I.SQ (I.C.mu0 j * I.xi a) (detPt B.host I.SQ ((I.stp u a k).rep c.1).1.1) : ℂˣ) : ℂ) := by
  obtain ⟨c, rfl⟩ := c
  have hlev := GlobalTheory.Mem.LevTwist.levOk_twists B X I hI
  have hpt := (hA.reads k hk).pt c
  obtain ⟨a', ha'⟩ := GlobalTheory.Mem.DetLift.exists_isDetLift B.R B.host (B.R.N k) _ hpt.uni
  obtain ⟨hkA, hkAm, hxr⟩ := hA.kA k hk (A.chOf k c)
  obtain ⟨hh, hhm⟩ := hA.h k hk (A.chOf k c) ⟨c, rfl⟩
  have hg : A.h k (A.chOf k c) ⟨c, rfl⟩ * A.kA k (A.chOf k c) ∈ GfC _ := mul_mem hh hkA
  have hfin : finM _ (rankN (I.rec7 l Z) k hk) (A.h k (A.chOf k c) ⟨c, rfl⟩ * A.kA k (A.chOf k c)) =
      ((((show TC.GA B (B.R.N k) from ((A.K k hk (A.chOf k c)).y ⟨c, rfl⟩).1) * A.kb k (A.chOf k c) : TC.GA B (B.R.N k))) :
        Matrix (Fin (B.R.N k)) (Fin (B.R.N k)) (Formalism.L2.DIV.AfE B.host.F B.host.E)) := by
    rw [GlobalTheory.RepLattice.finM_mul', hhm, hkAm, Units.val_mul]
    rfl
  have hroot := GlobalTheory.TwistFinPart.isDetRoot_mul' _ _ _ _ _ hx hxr
  have htw := (GlobalTheory.Mem.ReadTwist.isTwist_of_reads B.R B.host _ B.embLL I.S (I.tup a) (I.xi a) (hI.xi_reads a)).1
  have key := GlobalTheory.DetRootRead.chr_at_detRoot (I.rec7 l Z) (A.chr ((j : ℕ) + 1)) (I.C.mu0 j * I.xi a) (hA.chr j)
    (Formalism.L2.Host.HChar.TrivOn.mul (I.C.isMu0 j).triv htw.2.1) _ _ _ _ hg hfin _ hroot a' ha'
  have hm := reference_characters_factor_tame I.SQ I.C j
  have hxi : KDq B.host I.SQ ≤ ((I.xi a).1.comp (Chr.finPartI B.host.E)).ker :=
    (KDq_anti B.host (I.Q_subset_SQ a)).trans (hlev.2.2 a).1
  have hfac : KDq B.host I.SQ ≤ ((I.C.mu0 j * I.xi a).1.comp (Chr.finPartI B.host.E)).ker := fun b hb => by
    have e : (I.C.mu0 j).1 (Chr.finPartI B.host.E b) = 1 := hm hb
    have e' : (I.xi a).1 (Chr.finPartI B.host.E b) = 1 := hxi hb
    show (I.C.mu0 j).1 (Chr.finPartI B.host.E b) * (I.xi a).1 (Chr.finPartI B.host.E b) = 1
    rw [e, e', one_mul]
  rw [← GlobalTheory.Mem.Col2.DetSpec.mk_eq_detPt B.R B.host _ _ _ _ _ _ _ a' hlev.1 hpt ha', tildeQ_mk _ _ hfac, ← Circle.coe_mul, ← map_mul]
  exact key

theorem rho_eq {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i + 1 ≤ B.R.m)
    (c : (I.stp u a i).Cl) : (I.chIn u a).rho i c =
      ((tildeQ B.host I.SQ (I.C.mu0 ⟨i, hi⟩ * I.xi a) (detPt B.host I.SQ ((I.stp u a i).rep c).1.1) : ℂˣ) : ℂ)⁻¹ *
        chiId I.C.chiPsi (Th.detId B.host (Th.stdL B.host (B.R.N i)) ((I.stp u a i).rep c).1.1.deco.1.N) ^
          (-((B.R.N (i + 1) / 2 : ℕ) : ℤ)) := by
  have hlev := GlobalTheory.Mem.LevTwist.levOk_twists B X I hI
  have hxi : KDq B.host I.SQ ≤ ((I.xi a).1.comp (Chr.finPartI B.host.E)).ker :=
    (KDq_anti B.host (I.Q_subset_SQ a)).trans (hlev.2.2 a).1
  show ((rhoAt I.SQ I.C (I.xi a) i ((I.stp u a i).rep c).1.1 : ℂˣ) : ℂ) = _
  rw [rhoAt, muTilQ_succ B.host I.SQ I.C.mu0 ⟨i, hi⟩, xiDet, tildeQ_mul B.host I.SQ (reference_characters_factor_tame I.SQ I.C ⟨i, hi⟩) hxi,
    MonoidHom.mul_apply]
  rw [← GlobalTheory.Mem.ChiDet.tildeQ_detPt_eq_chiId B.R B.host _ I.C _ _ _ _ I.SQ _ hlev.1]
  simp only [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, mul_inv]

theorem rho'_eq {B : Base} {X : PreX B.toPre} (I : TC B X) (hI : I.Ok) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i + 1 ≤ B.R.m)
    (c' : (I.stp u a (i + 1)).Cl) : (I.chIn u a).rho' i c' =
      ((tildeQ B.host I.SQ (I.C.mu0 ⟨i, hi⟩ * I.xi a) (detPt B.host I.SQ ((I.stp u a (i + 1)).rep c').1.1) : ℂˣ) : ℂ) *
        chiId I.C.chiPsi (Th.detId B.host (Th.stdL B.host (B.R.N (i + 1))) ((I.stp u a (i + 1)).rep c').1.1.deco.1.N) ^
          ((B.R.N i / 2 : ℕ) : ℤ) := by
  have hlev := GlobalTheory.Mem.LevTwist.levOk_twists B X I hI
  have hxi : KDq B.host I.SQ ≤ ((I.xi a).1.comp (Chr.finPartI B.host.E)).ker :=
    (KDq_anti B.host (I.Q_subset_SQ a)).trans (hlev.2.2 a).1
  show ((rhoAt' I.SQ I.C (I.xi a) i ((I.stp u a (i + 1)).rep c').1.1 : ℂˣ) : ℂ) = _
  rw [rhoAt', muTilQ_succ B.host I.SQ I.C.mu0 ⟨i, hi⟩, xiDet, tildeQ_mul B.host I.SQ (reference_characters_factor_tame I.SQ I.C ⟨i, hi⟩) hxi,
    MonoidHom.mul_apply]
  rw [← GlobalTheory.Mem.ChiDet.tildeQ_detPt_eq_chiId B.R B.host _ I.C _ _ _ _ I.SQ _ hlev.1]
  simp only [Units.val_mul, Units.val_zpow_eq_zpow_val]

theorem moves_alg (X Y r₀ r₁ a b : ℂ) (p q : ℤ) (hX : X ≠ 0) (hY : Y ≠ 0) (h₀ : r₀ ≠ 0) (h₁ : r₁ ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    X⁻¹ * Y = r₀ * r₁⁻¹ * ((X * r₀)⁻¹ * a ^ (-p) * (Y * r₁ * b ^ q)) * (a ^ p * b ^ (-q)) := by
  have h1 : a ^ p ≠ 0 := zpow_ne_zero p ha
  have h2 : b ^ q ≠ 0 := zpow_ne_zero q hb
  rw [_root_.zpow_neg, _root_.zpow_neg]
  field_simp

theorem chr_moves_eq_rho_base : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ (c : {c // A.chOf i c = α}) (c' : {c // A.chOf (i + 1) c = γ}) x y, IsDetRoot _ (A.h i α c) x → IsDetRoot _ (A.h (i + 1) γ c') y → (A.chr (i + 1) x : ℂ)⁻¹ * (A.chr (i + 1) y : ℂ) = (A.chr (i + 1) (A.xr i α) : ℂ) * (A.chr (i + 1) (A.xr (i + 1) γ) : ℂ)⁻¹ * ((I.chIn u a).rho i c.1 * (I.chIn u a).rho' i c'.1) * I.A.chiF (B.R.N i) (B.R.N (i + 1)) ((I.stp u a i).rep c.1).1.1.deco.1.N ((I.stp u a (i + 1)).rep c'.1).1.1.deco.1.N := by
  intro B X I hI _ l Z u a Ch A hA i hi α γ c c' x y hx hy
  have h0 := chr_root_mul_base hI hA ⟨i, hi⟩ i (Nat.le_of_succ_le hi) α c x hx
  have h1 := chr_root_mul_base hI hA ⟨i, hi⟩ (i + 1) hi γ c' y hy
  rw [rho_eq I hI u a i hi, rho'_eq I hI u a i hi]
  simp only [ColIn.A, AmbIn.amb, Th.chiFac, ColIn.chi]
  rw [← h0, ← h1]
  exact moves_alg _ _ _ _ _ _ _ _ (Circle.coe_ne_zero _) (Circle.coe_ne_zero _) (Circle.coe_ne_zero _)
    (Circle.coe_ne_zero _) (chiId_ne_zero _ _) (chiId_ne_zero _ _)

end GlobalTheory.AdForm.TwDat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompIncAAlgebraMap
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
open NumberField IsDedekindDomain
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocMod.SplitCompl

open GlobalTheory.FinPl GlobalTheory.FinPl.SplitPoint GlobalTheory.IdemModTwo GlobalTheory.SplitIdem GlobalTheory.SplitChart GlobalTheory.SplitHecke

variable {D : D7}

theorem incA_algebraMap (t : D.host.F) :
    incA D (algebraMap D.host.F D.host.E t) = algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) t) := by
  rw [← IsScalarTower.algebraMap_apply]
  exact (Algebra.TensorProduct.includeRight (R := D.host.F) (A := AF D.host.F) (B := D.host.E)).commutes t

theorem comp_incA_algebraMap {v : Pl D} {e : AE D} (he : SplitAt D v e) (t : D.host.F) :
    comp he (incA D (algebraMap D.host.F D.host.E t)) = algebraMap D.host.F (Fv D.host.F v) t := by
  rw [incA_algebraMap, comp_algebraMap]
  rfl

def emb {v : Pl D} {e : AE D} (he : SplitAt D v e) : D.host.E →ₐ[D.host.F] Fv D.host.F v :=
  { (comp he).comp (incA D) with commutes' := comp_incA_algebraMap he }

theorem comp_sec {v : Pl D} {e : AE D} (he : SplitAt D v e) (a : Fv D.host.F v) : comp he (sec D v e a) = a := by
  rw [sec_apply, map_mul, comp_fj, comp_self, mul_one, evalV_singleV_same]

theorem sec_comp {v : Pl D} {e : AE D} (he : SplitAt D v e) (x : AE D) : sec D v e (comp he x) = e * x :=
  (sc_spec he x).symm

theorem int_iff_sec {v : Pl D} {e : AE D} (he : SplitAt D v e) (a : Fv D.host.F v) :
    a ∈ 𝒪[Fv D.host.F v] ↔ finPart D (sec D v e a) ∈ intAE D := by
  have h1 := (chart_comp he).2.2.2 (sec D v e a)
  rw [← sec_comp he, comp_sec he] at h1
  rw [h1, isInt_Ov, mem_integer_iff]

def splitPt {v : Pl D} {e : AE D} (h : IsSplitIdem D e) (he : SplitAt D v e)
    (hab : ∃ ε, IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε) : SplitPt D (Fv D.host.F v) where
  v := v
  e := e
  split := h
  above := hab
  pr := comp he
  sec := sec D v e
  pr_sec := comp_sec he
  sec_pr := sec_comp he
  cont_pr := continuous_comp he
  cont_sec := continuous_sec
  int_iff := int_iff_sec he

theorem emb_apply {v : Pl D} {e : AE D} (he : SplitAt D v e) (a : D.host.E) : emb he a = comp he (incA D a) := rfl

theorem splitPrime_emb {v : Pl D} {e : AE D} (he : SplitAt D v e) (PP : HeightOneSpectrum (𝓞 D.host.E))
    (h : Formalism.L2.NTheta.IsIdemAt e PP) : GlobalTheory.AdelicU.splitPrime (emb he) = PP := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  by_cases hx : x = 0
  · subst hx; simp only [Submodule.zero_mem]
  rw [GlobalTheory.AdelicU.mem_splitPrime, h.2 x hx, ← sec_comp he, ← emb_apply]
  have h0 : emb he (x : D.host.E) ≠ 0 :=
    (map_ne_zero _).2 (RingOfIntegers.coe_ne_zero_iff.2 hx)
  rw [← int_iff_sec he, mem_integer_iff, HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_inv₀, not_le,
    one_lt_inv₀ (zero_lt_iff.2 ((map_ne_zero _).2 h0))]

theorem exists_place : ∀ (D : D7) (PP : Formalism.L2.DIV.Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e PP → ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (q : GlobalTheory.FinPl.SplitPt D k), q.e = e ∧ q.v = PP.under (NumberField.RingOfIntegers D.host.F) ∧ (∀ a, (ofSplit q).pr a ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt PP a) ∧ DenseRange (ofSplit q).pr := by
  intro D PP e h
  obtain ⟨-, -, v, ε, hε, hs⟩ := h.1
  have he : SplitAt D v e := splitAt_of h.1 hε hs
  have hP := splitPrime_emb he PP h
  refine ⟨Fv D.host.F v, inferInstance, inferInstance, inferInstance, inferInstance, splitPt h.1 he ⟨ε, hε, hs⟩, rfl, ?_, ?_, ?_⟩
  · show v = _
    rw [← hP, GlobalTheory.AdelicU.splitPrime_under]
  · intro a
    change emb he a ∈ _ ↔ _
    rw [mem_integer_iff, HeightOneSpectrum.mem_adicCompletionIntegers, GlobalTheory.AdelicU.valued_apply_eq_valuation, hP,
      GlobalTheory.Proof.IntegralPowerExpansion.intAt_iff_val]
  · change DenseRange (emb he)
    refine Dense.mono ?_ (HeightOneSpectrum.denseRange_algebraMap D.host.F v)
    rintro _ ⟨t, rfl⟩
    exact ⟨algebraMap D.host.F D.host.E t, (emb he).commutes t⟩
end GlobalTheory.LocMod.SplitCompl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactCommutingCartanInvolutionMovedStandard
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.StdUnn.CartanMove

variable {D : D7}

theorem mt_mul' (V : HSp D) (g h : GA D V) :
    Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  simp [Formalism.L2.Theta.mt, map_mul, Units.val_mul]

theorem compAt_mt_one (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) :
    compAt θ τ (Formalism.L2.Theta.mt V 1) = 1 := by
  have : Formalism.L2.Theta.mt V 1 = 1 := by simp [Formalism.L2.Theta.mt]
  rw [this]
  exact Matrix.map_one (f := (θ τ).comp (infPart D)) (map_zero _) (map_one _)

theorem compAt_mt_mul (θ : InfFam D) (τ : D.what₂.Tau) (V : HSp D) (g h : GA D V) :
    compAt θ τ (Formalism.L2.Theta.mt V (g * h)) = compAt θ τ (Formalism.L2.Theta.mt V g) * compAt θ τ (Formalism.L2.Theta.mt V h) := by
  rw [mt_mul']
  exact GlobalTheory.AdForm.RatMove.compAt_mul θ τ _ _

theorem compAt_isom {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (g : GA D V) (τ : D.what₂.Tau) :
    (compAt θ τ (Formalism.L2.Theta.mt V g))ᴴ * gramAt D V τ * compAt θ τ (Formalism.L2.Theta.mt V g) = gramAt D V τ :=
  GlobalTheory.FockCompare.RealAction.infMat_mem_UH hθ V g τ

theorem isCartanInv_conj {k : ℕ} {G s P Pi : Matrix (Fin k) (Fin k) ℂ} (hs : IsCartanInv G s)
    (hPi : Pi * P = 1) (hPPi : P * Pi = 1) (hiso : Piᴴ * G * Pi = G) : IsCartanInv G (Pi * s * P) := by
  obtain ⟨h1, h2, h3⟩ := hs
  have hP : Pᴴ * G * P = G := by
    calc Pᴴ * G * P = Pᴴ * (Piᴴ * G * Pi) * P := by rw [hiso]
      _ = (Pi * P)ᴴ * G * (Pi * P) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = G := by rw [hPi, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hGPi : G * Pi = Pᴴ * G := by
    calc G * Pi = (Pi * P)ᴴ * G * Pi := by rw [hPi, Matrix.conjTranspose_one, Matrix.one_mul]
      _ = Pᴴ * (Piᴴ * G * Pi) := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Pᴴ * G := by rw [hiso]
  refine ⟨?_, ?_, ?_⟩
  · calc Pi * s * P * (Pi * s * P) = Pi * s * (P * Pi) * s * P := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hPPi, Matrix.mul_one, Matrix.mul_assoc Pi s s, h1, Matrix.mul_one, hPi]
  · calc (Pi * s * P)ᴴ * G * (Pi * s * P) = Pᴴ * (sᴴ * (Piᴴ * G * Pi) * s) * P := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = G := by rw [hiso, h2, hP]
  · have e : G * (Pi * s * P) = Pᴴ * (G * s) * P := by
      calc G * (Pi * s * P) = G * Pi * s * P := by simp only [Matrix.mul_assoc]
        _ = Pᴴ * (G * s) * P := by rw [hGPi]; simp only [Matrix.mul_assoc]
    rw [e]
    refine h3.conjTranspose_mul_mul_same ?_
    intro v w hvw
    have := congrArg (fun x => Pi.mulVec x) hvw
    simpa [Matrix.mulVec_mulVec, hPi] using this

end GlobalTheory.StdUnn.CartanMove
end

namespace GlobalTheory.StdUnn.CartanMove

open scoped ComplexOrder

theorem cartan_move_std : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ (a : GL (Fin A.rank) (AE D)) (p : siegel A), IsConj A a κ p → ∀ θ : InfFam D, IsInfFam θ → ∀ sS : RealMat (dblSp A), (∀ τ, IsCartanInv (gramAt D (dblSp A) τ) (sS τ)) → (∀ k ∈ Khat A a, ∀ τ, compAt θ τ (mt (dblSp A) k) * sS τ = sS τ * compAt θ τ (mt (dblSp A) k)) → ∃ s' : RealMat (dblSp A), IsStdInv A μ s' ∧ ∀ τ, s' τ * compAt θ τ (mt (dblSp A) (p : GA D (dblSp A))⁻¹) = compAt θ τ (mt (dblSp A) (p : GA D (dblSp A))⁻¹) * sS τ := by
  intro D A μ hμ κ hκ a p hp θ hθ sS hsS hcomm
  obtain ⟨k₀, hk₀K, hk₀⟩ := _root_.GlobalTheory.CartanPt.exists_mem_K_compAt_eq_stdInv D θ hθ A.rank μ hμ
  have hstd : IsStdInv A μ (fun τ => compAt θ τ (Formalism.L2.Theta.mt (dblSp A) (κ.symm k₀))) := by
    intro τ
    have h := hκ (κ.symm k₀)
    rw [κ.apply_symm_apply k₀] at h
    have h2 := congrArg (compAt θ τ) h
    rw [GlobalTheory.AdForm.RatMove.compAt_mul, GlobalTheory.AdForm.RatMove.compAt_mul] at h2
    have hr : compAt θ τ (rat (Tm A μ)) = (Tm A μ).map (tauE D τ) := GlobalTheory.AdForm.RatMove.compAt_rat hθ τ _
    rw [hr, hk₀] at h2
    exact h2.symm
  refine ⟨_, hstd, fun τ => ?_⟩
  dsimp only
  set k₁ := κ.symm k₀ with hk₁
  set P := compAt θ τ (Formalism.L2.Theta.mt (dblSp A) (p : GA D (dblSp A))) with hPdef
  set Pi := compAt θ τ (Formalism.L2.Theta.mt (dblSp A) (p : GA D (dblSp A))⁻¹) with hPidef
  set S1 := compAt θ τ (Formalism.L2.Theta.mt (dblSp A) k₁) with hS1
  have hPi : Pi * P = 1 := by rw [hPidef, hPdef, ← compAt_mt_mul, inv_mul_cancel, compAt_mt_one]
  have hPPi : P * Pi = 1 := by rw [hPidef, hPdef, ← compAt_mt_mul, mul_inv_cancel, compAt_mt_one]
  have hmem : (p : GA D (dblSp A)) * k₁ * (p : GA D (dblSp A))⁻¹ ∈ Khat A a := by
    rw [hp]
    have e : (p : GA D (dblSp A))⁻¹ * ((p : GA D (dblSp A)) * k₁ * (p : GA D (dblSp A))⁻¹) * (p : GA D (dblSp A)) = k₁ := by
      group
    rw [e, hk₁, κ.apply_symm_apply]
    exact hk₀K
  have hc := hcomm _ hmem τ
  rw [compAt_mt_mul, compAt_mt_mul] at hc
  have hcar' : IsCartanInv (gramAt D (dblSp A) τ) (Pi * sS τ * P) :=
    isCartanInv_conj (hsS τ) hPi hPPi (compAt_isom hθ _ _ τ)
  have hcar : IsCartanInv (gramAt D (dblSp A) τ) S1 := _root_.GlobalTheory.CartStd.isCartanInv_stdInv D A μ hμ _ hstd τ
  have hcm : S1 * (Pi * sS τ * P) = Pi * sS τ * P * S1 := by
    calc S1 * (Pi * sS τ * P) = (Pi * P) * S1 * Pi * sS τ * P := by rw [hPi, Matrix.one_mul]; simp only [Matrix.mul_assoc]
      _ = Pi * (P * S1 * Pi * sS τ) * P := by simp only [Matrix.mul_assoc]
      _ = Pi * (sS τ * (P * S1 * Pi)) * P := by rw [hc]
      _ = Pi * sS τ * P * S1 * (Pi * P) := by simp only [Matrix.mul_assoc]
      _ = Pi * sS τ * P * S1 := by rw [hPi, Matrix.mul_one]
  have heq : S1 = Pi * sS τ * P := _root_.GlobalTheory.StdUnn.isCartanInv_eq_of_commute _ _ _ _ hcar hcar' hcm
  rw [heq, Matrix.mul_assoc (Pi * sS τ) P Pi, hPPi, Matrix.mul_one]

end GlobalTheory.StdUnn.CartanMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledPairSchrodingerFunctionContinuousIntegrab
section
namespace I195MixedCoordinates_5e656a824e7915d837d372f3

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

end I195MixedCoordinates_5e656a824e7915d837d372f3

@[expose] public section

open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW

namespace GlobalTheory.Core.Rk.SchInt

theorem mixS_continuous_integrable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S S₀ T : HSp D} {ρ : ℕ}
    (d : HypDec S S₀ ρ) (v : GlobalTheory.Unf.VolM D T.rank ρ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (w : WO S₀ T) :
    Continuous (fun x => (_root_.I195MixedCoordinates_5e656a824e7915d837d372f3.source d) T ψ v.μ v.𝓕 f x w) ∧ Integrable (fun x => (_root_.I195MixedCoordinates_5e656a824e7915d837d372f3.source d) T ψ v.μ v.𝓕 f x w) v.μ := by
  have hc : Continuous (fun x => (_root_.I195MixedCoordinates_5e656a824e7915d837d372f3.source d) T ψ v.μ v.𝓕 f x w) :=
    (GlobalTheory.HeisMixSource.heis_mixS D ψ hψ S S₀ T ρ d v f hf).2.2.2.1.comp
      (f := fun x : Mx D T.rank ρ => (x, w)) (continuous_id.prodMk continuous_const)
  refine ⟨hc, ?_⟩
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D T.rank ρ
  haveI : BorelSpace (Mx D T.rank ρ) := ⟨rfl⟩
  haveI := v.covol.1
  obtain ⟨N, hN⟩ := GlobalTheory.Unf.MajInt.maj_integrable D θ hθ T.rank ρ (fun _ _ => True) 0 v.μ inferInstance
    (Filter.Eventually.of_forall fun x i j h => (h trivial).elim)
    (fun t _ => by
      have e : (fun x : Mx D T.rank ρ => x + t) = fun x => t + x := funext fun x => add_comm x t
      rw [e]; exact map_add_left_eq_self v.μ t)
  obtain ⟨U, hU, hfU⟩ := hf.level
  have hfL : f ∈ GlobalTheory.Size.thetaLevel ψ S T U := ⟨hf, hfU⟩
  obtain ⟨K, hK, hKN⟩ := GlobalTheory.Unf.mixS_le_maj D ψ hψ θ hθ S S₀ T ρ d v U hU
  obtain ⟨C, hC⟩ := hKN N
  have hfin := (_root_.GlobalTheory.Unf.SupFin.supSob_laws D ψ hψ θ hθ S T).1 N f hf
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  have hI := (hN K hK).2
  refine lt_of_le_of_lt (lintegral_mono fun x => (hC f hfL x w).trans
    (mul_le_mul_right (Real.ofReal_le_enorm _) _)) ?_
  rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin)]
  exact ENNReal.mul_lt_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin).lt_top hI

theorem sch_continuous_integrable : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (A B : HSp D)
    (ν : Measure (WO A B)) (𝓨 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓨 → ∀ f, IsThetaFunO ψ (dblSp A) B f →
    Continuous (sch ψ A B ν 𝓨 f) ∧ Integrable (sch ψ A B ν 𝓨 f) ν :=
  fun _ _ hψ A _ ν 𝓨 hν _ hf => mixS_continuous_integrable hψ (dblDec A) ⟨ν, 𝓨, hν⟩ hf 0

end GlobalTheory.Core.Rk.SchInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBadPrimeOverChartBadPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
open GlobalTheory.Mem.Col2.AdT
open Filter Topology

namespace GlobalTheory.Mem.Col2.AdT

theorem exists_SBof_over_sub : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), v ∈ Formalism.L2.Forms.badG (I.rec7 l Z) ∨ I.UnderQ a v → ∃ P : SBof I a, Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) := by
  intro B X I hOk _ l Z a v hv
  obtain ⟨P, hP, hPv⟩ := exists_SBof_over I hOk l Z a v hv
  exact ⟨⟨P, hP⟩, hPv⟩

end GlobalTheory.Mem.Col2.AdT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCharExponentInfinityKernelShiftStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_charExponent_infinity_kernel_shift : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m), ∃ e : (I.rec7 l Z).what₂.Tau → ℤ, (∀ τ, HasInfExp (I.rec7 l Z) (A.chr (i + 1)) τ (e τ)) ∧ ∀ τ, (I.chain l u a).sSharp i τ = -e τ - ((I.rec7 l Z).sp.X (i + 1)).rank / 2 ∧ -(I.chain l u a).sDiv i τ = e τ + ((I.rec7 l Z).sp.X i).rank / 2 ∧ 0 ≤ shiftOf (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u i) τ + (I.chain l u a).sSharp i τ := by
  first | exact @GlobalTheory.AdForm.TwDat.chr_exp_shifts | exact GlobalTheory.AdForm.TwDat.chr_exp_shifts | (intros; apply GlobalTheory.AdForm.TwDat.chr_exp_shifts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsContinuousLocalGLEmbeddingSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocEmb

theorem exists_gl : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) (Y : Type) [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y),
    ∃ gl : GL Y k →* GA D V, Continuous gl ∧ (∀ x, SuppAt q.e V (gl x) ∧ (mt V (gl x)).map q.pr = F.β * x.val * F.γ) ∧
      ∀ g x, SuppAt q.e V g → (mt V g).map q.pr = F.β * x.val * F.γ → g = gl x := by
  intro D k _ _ _ _ q V Y _ _ F
  obtain ⟨h1, -, h3⟩ := (_root_.GlobalTheory.LocGrp.local_groups D k (GlobalTheory.LocMod.ofSplit q)).1 V Y F
  choose f hf hu using h1
  have hmul : ∀ x y, f (x * y) = f x * f y := fun x y => (hu (x * y) _ (h3 _ _ _ _ (hf x) (hf y))).symm
  have hone : f 1 = 1 := by
    have h := hmul 1 1
    rw [mul_one] at h
    exact (mul_eq_left.1 h.symm)
  let gl : GL Y k →* GA D V := { toFun := f, map_one' := hone, map_mul' := hmul }
  let fr : GlobalTheory.FinPl.Frame q V Y := ⟨F.β, F.γ, F.βγ, F.γβ, gl, fun x => (hf x).1, fun x => (hf x).2⟩
  refine ⟨gl, GlobalTheory.FrameCont.continuous_gl D k q V Y fr, fun x => hf x, fun g x hs hm => hu x g ⟨hs, hm⟩⟩

end GlobalTheory.LocEmb
end
end

