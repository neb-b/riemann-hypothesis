module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0349
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspRapidDecayOfSobolev
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RootExchangeUnipotentHaarAndModulus
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsUnimodularBlockUpperTriangularSymmetricLevels
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqSemiMeasOfCovolOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilFormulaRootExchangeParabolicIntersection
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0345
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0346
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0348
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemTranslate
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TriStep

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ}

theorem rTrans_rTrans {G : Type} [Semigroup G] (a b : G) (F : G → ℂ) : rTrans a (rTrans b F) = rTrans (a * b) F := by
  funext g; simp [rTrans, mul_assoc]

theorem rTrans_one {G : Type} [Monoid G] (F : G → ℂ) : rTrans 1 F = F := by
  funext g; simp [rTrans]

def space (Q : QStep S) : Submodule ℂ (GA D S.B'.V → ℂ) where
  carrier := {f | (∀ y, IsContAut S.B'.V (rTrans (Q.gl₂ y) f)) ∧
    ∃ U : Subgroup (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k), IsOpen (U : Set (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k)) ∧
      ∀ u ∈ U, rTrans (Q.gl₂ u) f = f}
  zero_mem' := ⟨fun y => ⟨fun _ _ _ => rfl, continuous_const⟩, ⊤, isOpen_univ, fun _ _ => rfl⟩
  add_mem' := by
    rintro f g ⟨hf, U, hU, hfU⟩ ⟨hg, V, hV, hgV⟩
    refine ⟨fun y => ⟨fun γ hγ x => ?_, ?_⟩, U ⊓ V, hU.inter hV, fun u hu => ?_⟩
    · change f (γ * x * _) + g (γ * x * _) = f (x * _) + g (x * _)
      have h1 := (hf y).1 γ hγ x
      have h2 := (hg y).1 γ hγ x
      simp only [rTrans] at h1 h2
      rw [h1, h2]
    · exact (hf y).2.add (hg y).2
    · have h1 := hfU u hu.1
      have h2 := hgV u hu.2
      funext x
      have e1 := congrFun h1 x
      have e2 := congrFun h2 x
      simp only [rTrans, Pi.add_apply] at e1 e2 ⊢
      rw [e1, e2]
  smul_mem' := by
    rintro a f ⟨hf, U, hU, hfU⟩
    refine ⟨fun y => ⟨fun γ hγ x => ?_, ?_⟩, U, hU, fun u hu => ?_⟩
    · have h1 := (hf y).1 γ hγ x
      simp only [rTrans, Pi.smul_apply, smul_eq_mul] at h1 ⊢
      rw [h1]
    · exact continuous_const.mul (hf y).2
    · have h1 := hfU u hu
      funext x
      have e1 := congrFun h1 x
      simp only [rTrans, Pi.smul_apply, smul_eq_mul] at e1 ⊢
      rw [e1]

theorem mem_translate (Q : QStep S) (y : GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k) {f : GA D S.B'.V → ℂ} (hf : f ∈ space Q) :
    rTrans (Q.gl₂ y) f ∈ space Q := by
  obtain ⟨hc, U, hU, hfU⟩ := hf
  refine ⟨fun y' => ?_, U.comap (MulAut.conj y⁻¹).toMonoidHom, ?_, fun u hu => ?_⟩
  · rw [rTrans_rTrans, ← map_mul]; exact hc _
  · have hc : Continuous fun x : GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k => y⁻¹ * x * y⁻¹⁻¹ :=
      (continuous_const.mul continuous_id).mul continuous_const
    exact hU.preimage hc
  · have hu' : y⁻¹ * u * y ∈ U := by simpa using hu
    rw [rTrans_rTrans, ← map_mul, show u * y = y * (y⁻¹ * u * y) by group, map_mul, ← rTrans_rTrans, hfU _ hu']

def rep (Q : QStep S) : Representation ℂ (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k) (space Q) where
  toFun y :=
    { toFun := fun f => ⟨rTrans (Q.gl₂ y) f.1, mem_translate Q y f.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    ext f x
    simp [rTrans]
  map_mul' x y := by
    ext f g
    rw [Module.End.mul_apply]
    change f.1 (g * Q.gl₂ (x * y)) = f.1 (g * Q.gl₂ x * Q.gl₂ y)
    rw [map_mul, mul_assoc]

def valK (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ) (φ : GA D S.B.A → ℂ)
    (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ))
    (Ξ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k)) (f : GA D S.B'.V → ℂ) : ℂ :=
  S.B'.per ψ (biLift S.oma S.omb S.B.vA S.J.v0 φ (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ Ξ))) f

theorem smooth (Q : QStep S) : IsSmoothRep (rep Q) := by
  intro v
  obtain ⟨-, U, hU, hfU⟩ := v.2
  let H : Subgroup (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k) :=
    { carrier := {g | rep Q g v = v}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hb, ha]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hle : U ≤ H := fun u hu => Subtype.ext (hfU u hu)
  exact Subgroup.isOpen_mono hle hU

end GlobalTheory.TriStep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrbitSumModerateGrowth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ENNReal NNReal

set_option maxHeartbeats 1000000

namespace GlobalTheory.Unf

theorem orbit_sum_moderate_growth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (vN : VolN d) (vW : Vol W) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (G : GA D W → ℂ) (Φ : WO V W → ℂ), RapidDec W G → IsThetaFunO ψ V W Φ → ∃ (C : ℝ) (A : ℕ), ∀ g : GA D V, ∫⁻ p in vN.𝓝 ×ˢ vW.𝓕, ∑' y : Orb W x₀, ‖G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) y.1‖ₑ ∂(vN.ν.prod vW.μ) ≤ ENNReal.ofReal (C * height V g ^ A) := by
  intro D ψ V V₀ W ρ d χV χW om om' hw hw' vS vN vW x₀ G Φ hG hΦ
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag V (isIsoSub_e d)
  haveI := vN.unit.1
  haveI := vW.haar
  obtain ⟨C, A, hC⟩ := _root_.GlobalTheory.Unf.sum_term_bound D ψ V V₀ W ρ d χV χW om om' hw hw' vS Φ hΦ
  obtain ⟨B, hBd⟩ := hG.2.2 A
  have hB0 : 0 ≤ B := (mul_nonneg (norm_nonneg _) (pow_nonneg (quotHeight_pos W 1).le _)).trans (hBd 1)
  have hfin : (vN.ν.prod vW.μ) (vN.𝓝 ×ˢ vW.𝓕) ≠ ⊤ := by
    rw [Measure.prod_prod, vN.unit.2.2, one_mul]
    exact GlobalTheory.Chain.LiftReg.vol_ne_top vW.haar vW.fund
  have hK0 : 0 ≤ max C 0 * B := mul_nonneg (le_max_right _ _) hB0
  have hm0 : 0 ≤ ((vN.ν.prod vW.μ) (vN.𝓝 ×ˢ vW.𝓕)).toReal := ENNReal.toReal_nonneg
  refine ⟨max C 0 * B * ((vN.ν.prod vW.μ) (vN.𝓝 ×ˢ vW.𝓕)).toReal, A, fun g => ?_⟩
  have hg0 : 0 ≤ height V g ^ A := pow_nonneg (height_pos V g).le _
  have hpt : ∀ (n : flagN d) (h : GA D W),
      ∑' y : Orb W x₀, ‖G h * term ψ d W vS (om (n.1 * g, h) Φ) y.1‖ₑ ≤
        ENNReal.ofReal (max C 0 * B * height V g ^ A) := by
    intro n h
    have h1 : ∑' y : Orb W x₀, ‖G h * term ψ d W vS (om (n.1 * g, h) Φ) y.1‖ₑ =
        ‖G h‖ₑ * ∑' y : Orb W x₀, ‖term ψ d W vS (om (n.1 * g, h) Φ) y.1‖ₑ := by
      simp_rw [enorm_mul]
      exact ENNReal.tsum_mul_left
    have h2 : ∑' y : Orb W x₀, ‖term ψ d W vS (om (n.1 * g, h) Φ) y.1‖ₑ ≤
        ∑' x : Matrix (Fin W.rank) (Fin ρ) D.host.E, ‖term ψ d W vS (om (n.1 * g, h) Φ) x‖ₑ :=
      ENNReal.tsum_comp_le_tsum_of_injective (f := fun y : Orb W x₀ => y.1)
        Subtype.val_injective (fun x => ‖term ψ d W vS (om (n.1 * g, h) Φ) x‖ₑ)
    have hq0 : 0 ≤ quotHeight W h ^ A := pow_nonneg (quotHeight_pos W h).le _
    have h3 : ∑' x : Matrix (Fin W.rank) (Fin ρ) D.host.E, ‖term ψ d W vS (om (n.1 * g, h) Φ) x‖ₑ ≤
        ENNReal.ofReal (max C 0 * height V g ^ A * quotHeight W h ^ A) := by
      refine (hC g h n.1 n.2).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [mul_pow, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hg0) hq0
    have h4 : ‖G h‖ * (max C 0 * height V g ^ A * quotHeight W h ^ A) ≤ max C 0 * B * height V g ^ A := by
      have e : ‖G h‖ * (max C 0 * height V g ^ A * quotHeight W h ^ A) =
          max C 0 * height V g ^ A * (‖G h‖ * quotHeight W h ^ A) := by ring
      rw [e, mul_right_comm (max C 0) B]
      exact mul_le_mul_of_nonneg_left (hBd h) (mul_nonneg (le_max_right _ _) hg0)
    rw [h1]
    refine (mul_le_mul' le_rfl (h2.trans h3)).trans ?_
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal h4
  calc ∫⁻ p in vN.𝓝 ×ˢ vW.𝓕, ∑' y : Orb W x₀, ‖G p.2 * term ψ d W vS (om (p.1.1 * g, p.2) Φ) y.1‖ₑ ∂(vN.ν.prod vW.μ)
      ≤ ∫⁻ p in vN.𝓝 ×ˢ vW.𝓕, ENNReal.ofReal (max C 0 * B * height V g ^ A) ∂(vN.ν.prod vW.μ) :=
        lintegral_mono fun p => hpt p.1 p.2
    _ = ENNReal.ofReal (max C 0 * B * height V g ^ A) * (vN.ν.prod vW.μ) (vN.𝓝 ×ˢ vW.𝓕) := setLIntegral_const _ _
    _ = ENNReal.ofReal (max C 0 * B * ((vN.ν.prod vW.μ) (vN.𝓝 ×ˢ vW.𝓕)).toReal * height V g ^ A) := by
        rw [← ENNReal.ofReal_toReal hfin, ENNReal.toReal_ofReal hm0, ← ENNReal.ofReal_mul (mul_nonneg hK0 hg0)]
        congr 1; ring

end GlobalTheory.Unf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairFiniteAdeleZeroMulPairFiniteAdeleZero
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.AdForm GlobalTheory.LocMod
open NumberField
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdHomOrth

variable {D : D7}

def finInt (D : D7) : AddSubgroup (AE D) :=
  AddSubgroup.closure {z | ∃ α ∈ intAf D.host.F, ∃ x : D.host.E, IsIntegral ℤ x ∧ z = (pairA D.host.F 0 α) ⊗ₜ[D.host.F] x}

theorem gen_mem {α : Af D.host.F} (hα : α ∈ intAf D.host.F) {x : D.host.E} (hx : IsIntegral ℤ x) :
    ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] x : AE D) ∈ finInt D :=
  AddSubgroup.subset_closure ⟨α, hα, x, hx, rfl⟩

theorem star_int {x : D.host.E} (hx : IsIntegral ℤ x) : IsIntegral ℤ (star x) :=
  hx.map (starRingEnd D.host.E).toIntAlgHom

theorem incA_eq (e : D.host.E) : incA D e = ((1 : AF D.host.F) ⊗ₜ[D.host.F] e : AE D) := rfl

theorem cA_tmul (a : AF D.host.F) (e : D.host.E) : cA D (a ⊗ₜ[D.host.F] e) = a ⊗ₜ[D.host.F] star e := rfl

theorem trace_tmul {R : Type} [CommRing R] [Algebra D.host.F R] (a : R) (e : D.host.E) :
    Algebra.trace R (R ⊗[D.host.F] D.host.E) (a ⊗ₜ[D.host.F] e) =
      a * algebraMap D.host.F R (Algebra.trace D.host.F D.host.E e) := by
  have h1 : a ⊗ₜ[D.host.F] e = a • ((1 : R) ⊗ₜ[D.host.F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have h2 : Algebra.lmul R (R ⊗[D.host.F] D.host.E) ((1 : R) ⊗ₜ[D.host.F] e) =
      (Algebra.lmul D.host.F D.host.E e).baseChange R := by
    ext x
    simp
  rw [h1, map_smul, smul_eq_mul, Algebra.trace_apply, h2, LinearMap.trace_baseChange, ← Algebra.trace_apply]

theorem intAf_mul' {a b : Af D.host.F} (ha : a ∈ intAf D.host.F) (hb : b ∈ intAf D.host.F) : a * b ∈ intAf D.host.F :=
  fun w => by rw [map_mul]; exact mul_mem (ha w) (hb w)

theorem coe_mem_intAf (r : 𝓞 D.host.F) : algebraMap D.host.F (Af D.host.F) (r : D.host.F) ∈ intAf D.host.F := by
  intro v
  rw [AlgHom.commutes]
  exact IsDedekindDomain.HeightOneSpectrum.coe_algebraMap_mem (𝓞 D.host.F) D.host.F v r

theorem char_int {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {β : Af D.host.F} (hβ : β ∈ intAf D.host.F) :
    ψ (pairA D.host.F 0 β) = 1 := by
  have := GlobalTheory.IntDense.addChar_eq_one_of_integral D.host.F ψ hψ.1.1 1 (fun a => by
    have htr : Algebra.trace ℚ D.host.F (a : D.host.F) = ((Algebra.intTrace ℤ (𝓞 D.host.F) a : ℤ) : ℚ) :=
      (Algebra.algebraMap_intTrace (A := ℤ) (K := ℚ) (L := D.host.F) a).symm
    rw [mul_one, GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ, htr, mul_comm]
    push_cast
    exact Complex.exp_int_mul_two_pi_mul_I _) β hβ
  rwa [map_one, mul_one] at this

theorem pairFiniteAdele_zero_mul_pairFiniteAdele_zero (α β : Af D.host.F) :
    pairA D.host.F 0 α * pairA D.host.F 0 β = pairA D.host.F 0 (α * β) :=
  Prod.ext (mul_zero (0 : Ainf D.host.F)) rfl

theorem pairFiniteAdele_zero_mul_algebraMap_base (α : Af D.host.F) (q : D.host.F) :
    pairA D.host.F 0 α * algebraMap D.host.F (AF D.host.F) q =
      pairA D.host.F 0 (α * algebraMap D.host.F (Af D.host.F) q) :=
  Prod.ext (zero_mul (algebraMap D.host.F (Ainf D.host.F) q)) rfl

theorem incA_mul_mem {e : D.host.E} (he : IsIntegral ℤ e) {z : AE D} (hz : z ∈ finInt D) : incA D e * z ∈ finInt D := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hy
    rw [incA_eq, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact gen_mem hα (he.mul hx)
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem cA_mem {z : AE D} (hz : z ∈ finInt D) : cA D z ∈ finInt D := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hy
    rw [cA_tmul]
    exact gen_mem hα (star_int hx)
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem mul_mem' {z w : AE D} (hz : z ∈ finInt D) (hw : w ∈ finInt D) : z * w ∈ finInt D := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hy
    induction hw using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨β, hβ, x', hx', rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul, pairFiniteAdele_zero_mul_pairFiniteAdele_zero]
      exact gen_mem (intAf_mul' hα hβ) (hx.mul hx')
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | neg x _ hx => rw [mul_neg]; exact neg_mem hx
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

theorem psi_trace {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {z : AE D} (hz : z ∈ finInt D) :
    ψ (Algebra.trace (AF D.host.F) (AE D) z) = 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, hα, x, hx, rfl⟩ := hy
    have hint : IsIntegral ℤ (Algebra.trace D.host.F D.host.E x) := Algebra.isIntegral_trace hx
    rw [trace_tmul, pairFiniteAdele_zero_mul_algebraMap_base]
    exact char_int hψ (intAf_mul' hα (coe_mem_intAf ⟨_, hint⟩))
  | zero => rw [map_zero]; exact AddChar.map_zero_eq_one ψ
  | add x y _ _ hx hy => rw [map_add (f := _), AddChar.map_add_eq_mul, hx, hy, one_mul]
  | neg x _ hx => rw [map_neg, AddChar.map_neg_eq_inv, hx, inv_one]

theorem exists_den {ι : Type} [Fintype ι] (f : ι → D.host.E) :
    ∃ d : ℕ, 0 < d ∧ ∀ i, IsIntegral ℤ ((d : D.host.E) * f i) := by
  have : Algebra.IsAlgebraic ℤ D.host.E :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := D.host.E)).2 inferInstance
  obtain ⟨y, hy, h⟩ := Algebra.IsAlgebraic.exists_integral_multiples ℤ (Finset.univ.image f)
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, fun i => ?_⟩
  have h1 := h (f i) (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
  rw [zsmul_eq_mul] at h1
  rcases Int.natAbs_eq y with e | e
  · rw [e] at h1; simpa using h1
  · rw [e] at h1
    have := h1.neg
    simpa using this

theorem exists_den_entries (S T : HSp D) : ∃ d : ℕ, 0 < d ∧ ∀ v ∈ stdHom S T, ∀ r s, (d : AE D) * v r s ∈ finInt D := by
  obtain ⟨a0, ha0, hfrac⟩ := D.host.AA.isFractional
  have ha0' : ((a0 : 𝓞 D.host.E) : D.host.E) ≠ 0 := by
    intro h
    exact nonZeroDivisors.coe_ne_zero ⟨a0, ha0⟩ (RingOfIntegers.coe_eq_zero_iff.1 h)
  obtain ⟨d, hd, hx0⟩ := exists_den (D := D) fun _ : Unit => ((a0 : D.host.E))⁻¹
  obtain ⟨e, he, hG⟩ := exists_den (D := D) fun p : Fin S.rank × Fin S.rank => S.gram p.1 p.2
  refine ⟨d * e, Nat.mul_pos hd he, fun v hv => ?_⟩
  induction hv using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    intro r c
    have hint' : IsIntegral ℤ (((d * e : ℕ) : D.host.E) * (a * t r * ∑ k, star (s k) * S.gram k c)) := by
      have hA : IsIntegral ℤ ((a0 : D.host.E) * a) := by
        obtain ⟨y, hy⟩ := hfrac a ha
        have h2 : IsIntegral ℤ (algebraMap (𝓞 D.host.E) D.host.E y) := y.2
        rw [hy, Algebra.smul_def] at h2
        exact h2
      have hsum : IsIntegral ℤ (∑ k, star (s k) * ((e : D.host.E) * S.gram k c)) :=
        IsIntegral.sum _ fun k _ => IsIntegral.mul (star_int (hs k)) (hG (k, c))
      have e1 : ((d * e : ℕ) : D.host.E) * (a * t r * ∑ k, star (s k) * S.gram k c) =
          ((d : D.host.E) * ((a0 : D.host.E))⁻¹) * ((a0 : D.host.E) * a) * t r *
            ∑ k, star (s k) * ((e : D.host.E) * S.gram k c) := by
        have hx : ((a0 : D.host.E))⁻¹ * (a0 : D.host.E) = 1 := inv_mul_cancel₀ ha0'
        have e2 : ∑ k, star (s k) * ((e : D.host.E) * S.gram k c) = (e : D.host.E) * ∑ k, star (s k) * S.gram k c := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
        rw [e2]; push_cast
        linear_combination (-((d : D.host.E) * e * a * t r * ∑ k, star (s k) * S.gram k c)) * hx
      rw [e1]
      exact (((hx0 ()).mul hA).mul (ht r)).mul hsum
    rw [Matrix.of_apply, ← map_natCast (incA D) (d * e), incA_eq, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact gen_mem hα hint'
  | zero => intro r s; rw [Matrix.zero_apply, mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => intro r s; rw [Matrix.add_apply, mul_add]; exact add_mem (hx r s) (hy r s)
  | neg x _ hx => intro r s; rw [Matrix.neg_apply, mul_neg]; exact neg_mem (hx r s)

theorem exists_nsmul_orth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D), ∃ M : ℕ, 0 < M ∧ ∀ x ∈ stdHom S T, ∀ w ∈ stdHom S T, ψ (symplO S T x (M • w)) = 1 := by
  intro D ψ hψ S T
  obtain ⟨d, hd, hden⟩ := exists_den_entries S T
  obtain ⟨p, hp, hξ⟩ := exists_den (D := D) fun _ : Unit => D.host.xi0
  obtain ⟨q, hq, hS⟩ := exists_den (D := D) fun i : Fin S.rank × Fin S.rank => S.gram⁻¹ i.1 i.2
  obtain ⟨r, hr, hT⟩ := exists_den (D := D) fun i : Fin T.rank × Fin T.rank => T.gram i.1 i.2
  refine ⟨p * q * r * d * d, by positivity, fun x hx w hw => ?_⟩
  refine psi_trace hψ ?_
  unfold hO
  simp only [Finset.mul_sum]
  refine sum_mem fun a _ => sum_mem fun b _ => sum_mem fun c _ => sum_mem fun e _ => ?_
  have key : incA D D.host.xi0 * (incA D (S.gram⁻¹ a b) * cA D (((p * q * r * d * d) • w) c b) * incA D (T.gram c e) * x e a) =
      incA D ((p : D.host.E) * D.host.xi0) * (incA D ((q : D.host.E) * S.gram⁻¹ a b) * (incA D ((r : D.host.E) * T.gram c e) *
        (cA D ((d : AE D) * w c b) * ((d : AE D) * x e a)))) := by
    rw [Matrix.smul_apply, nsmul_eq_mul]
    simp only [map_mul, map_natCast, Nat.cast_mul]
    ring
  rw [key]
  exact incA_mul_mem (hξ ()) (incA_mul_mem (hS (a, b)) (incA_mul_mem (hT (c, e))
    (mul_mem' (cA_mem (hden w hw c b)) (hden x hx e a))))

end GlobalTheory.StdHomOrth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdRFJCoe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace

noncomputable section
namespace GlobalTheory.HaarR

variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

def prodR (p : ℕ) (q : GL n k × N k n c p) : R k n c p :=
  ⟨embX c q.1 * (q.2 : GL (n ⊕ Fin c) k), mul_mem (Subgroup.mem_sup_left ⟨q.1, rfl⟩) (Subgroup.mem_sup_right q.2.2)⟩

def prodRFJ (ρ : ℕ) (q : (GL n k × N k n c (ρ + 1)) × (n → k)) : RFJ k n c ρ :=
  ⟨embX c q.1.1 * (q.1.2 : GL (n ⊕ Fin c) k) * colE c (ρ + 1) q.2,
    mul_mem (Subgroup.mem_sup_right (mul_mem (Subgroup.mem_sup_left ⟨q.1.1, rfl⟩) (Subgroup.mem_sup_right q.1.2.2)))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right
        ((GlobalTheory.RootEx.Radical.unipotent_radical_basic k n c ρ).2.2.2.2.2.2.2 (ρ + 1) q.2 (Nat.lt_succ_self ρ)).1))⟩

@[simp] theorem prodR_coe (p : ℕ) (q : GL n k × N k n c p) :
    (prodR p q : GL (n ⊕ Fin c) k) = embX c q.1 * (q.2 : GL (n ⊕ Fin c) k) := rfl

@[simp] theorem prodRFJ_coe (ρ : ℕ) (q : (GL n k × N k n c (ρ + 1)) × (n → k)) :
    (prodRFJ ρ q : GL (n ⊕ Fin c) k) = embX c q.1.1 * (q.1.2 : GL (n ⊕ Fin c) k) * colE c (ρ + 1) q.2 := rfl

def cjE (ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) (β : n → k) (u : N k n c (ρ + 1)) : N k n c (ρ + 1) :=
  ⟨colE c (ρ + 1) β * (u : GL (n ⊕ Fin c) k) * (colE c (ρ + 1) β)⁻¹,
    (GlobalTheory.RootEx.FourierJacobiGroup.mem_RFJ_iff k n c ρ h1 h2).2 β u u.2⟩

@[simp] theorem cjE_coe (ρ : ℕ) (h1 : 1 ≤ ρ) (h2 : ρ < c) (β : n → k) (u : N k n c (ρ + 1)) :
    (cjE ρ h1 h2 β u : GL (n ⊕ Fin c) k) = colE c (ρ + 1) β * (u : GL (n ⊕ Fin c) k) * (colE c (ρ + 1) β)⁻¹ := rfl

end GlobalTheory.HaarR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarFormsOnChartsOfTrueColumnTupleStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalarForms_on_charts_of_trueColumnTuple : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (i : ℕ) (hi : i ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi i, (∀ c, (fun z : FrN (I.rec7 l Z) (B.R.N i) => φ c ⟨z.1, z.2⟩) ∈ ValC _ (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u i)) ∧ ∀ β y, ∀ γ ∈ GQ ((I.rec7 l Z).sp.X i), ∀ c, ∀ k ∈ GinfC ((I.rec7 l Z).sp.X i), ∀ (κ : A.U i β) (y' : (I.chain l u a).Y i), IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) i hi) k) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ → A.rd θ i hi β φ y (γ * (A.h i β c * k) * κ.1) = (A.chi i β κ : ℂ) * φ c.1 y' := by
  first | exact @GlobalTheory.AdForm.rd_charts | exact GlobalTheory.AdForm.rd_charts | (intros; apply GlobalTheory.AdForm.rd_charts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticesConjugateAtFinitePlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl

namespace GlobalTheory.FinPl.SelfDualConj

theorem conj_at_place : ∀ (D : D7) (V : HSp D) (L M : Lat V), IsSelfDualC V L → IsSelfDualC V M →
    ∀ x : Pl D, ∃ g ∈ grpAt V (· = x), Moves V g L M (· = x) := by
  intro D V L M hL hM x
  obtain ⟨γ, hγ, h⟩ := _root_.GlobalTheory.IwaOrbit.selfDual_orbit D V x (latV V L (· = x)) (latV V M (· = x)) (GlobalTheory.FinPl.TamePlaces.tame D x)
    (GlobalTheory.IwaPlace.LocSD.isSDAt_latV D V L x hL) (GlobalTheory.IwaPlace.LocSD.isSDAt_latV D V M x hM)
  exact ⟨γ, hγ, fun y hy => h y hy⟩

end GlobalTheory.FinPl.SelfDualConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitarySupportedSplitPlacesEqProdLocalPartsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitarySupported_splitPlaces_eq_prod_local_parts : ∀ (D : D7) (V : HSp D) (n : ℕ) (k : Fin n → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i)), Function.Injective (fun i => (q i).v) → ∀ g ∈ GlobalTheory.FinPl.grpAt V (fun p => ∃ i, p = (q i).v), ∃ h : Fin n → GA D V, (∀ i, SuppAt (q i).e V (h i)) ∧ g = ((List.finRange n).map h).prod := by
  first | exact @GlobalTheory.SplitDecomp.prod_of_grpAt | exact GlobalTheory.SplitDecomp.prod_of_grpAt | (intros; apply GlobalTheory.SplitDecomp.prod_of_grpAt <;> assumption)
end

