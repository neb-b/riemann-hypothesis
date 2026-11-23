module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0562
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActLevMemCuspA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1816
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0114
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0348
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0746
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0005
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetFrBorOfLift
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepIntegrandBesselPeriodInvariantProof
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0464
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0372
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlacewiseToAdelicDecompositionForall
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JacobiToBesselFlatMapSupportProof
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0478
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0401
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0564
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0295
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridCoreIffFirstRowExtByZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthLatticeGridCore_iff_firstRow_extByZero : OnStd fun {D} _ _ _ {G} _ F => ∀ (h : 2 * 0 + 2 ≤ D.R.m) (a : WO (G.V (.core 1)) (Yc D 0)), F.oz.jA ⬝ a ∈ latCore G 0 ↔ (F.dJ 0 h).ext0 (Yc D 0) a ∈ latRow G 0 := by
  first | exact @GlobalTheory.CoreRowLat.jA_mem_latCore_iff | exact GlobalTheory.CoreRowLat.jA_mem_latCore_iff | (intros; apply GlobalTheory.CoreRowLat.jA_mem_latCore_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeoAct
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeometricAction


set_option maxHeartbeats 1000000 in
theorem geoAct : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), R.toLevCh.Is A.μ0 → R.IsModels → FWTie T R κ v₀ → (∀ i, OMPins T R κ v₀ O i) → EquivAll T R κ O → GeoAct T R κ v₀ := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ O hL hM fw hpins hall
  have ht : TieIn T R κ v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  refine GlobalTheory.GeoLevel.geoAct_of_eqAt ht hM.HW hM.gW O hpins ?_
  intro i σ hσ hV

  have hpb : T.pb = R.C.P.pb :=
    GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore R fw.laws.toLawsM hL ((hpins i).2.tuple ()).half
  exact hall i σ hσ hV (_root_.GlobalTheory.EquivConst.exists_equivariant_constants T R κ v₀ O hL ht hpb hpins i σ hσ hV)

end GlobalTheory.GeometricAction
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodPlaceOneCosetOfBesselLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.OneCosetGood

variable {D : D7}

theorem ell_mul {ρ : ℕ} (u : GL (Fin ρ) (AE D)) (hu : u ∈ UX D ρ) (j : Fin ρ) :
    ∑ l, ell D ρ l * u.1 l j = ell D ρ j := by
  have hu' := mem_UX.1 hu
  have hρ : 0 < ρ := Fin.pos j
  set m : Fin ρ := ⟨ρ - 1, by omega⟩ with hmdef
  have hm : m.1 + 1 = ρ := by rw [hmdef]; simp only; omega
  have hne : ∀ b : Fin ρ, b ≠ m → ¬ (b.1 + 1 = ρ) := fun b hb h => hb (Fin.ext (by rw [hmdef]; simp only; omega))
  rw [Finset.sum_eq_single m]
  · rw [show ell D ρ m = 1 from if_pos hm, one_mul]
    by_cases hj : j = m
    · rw [hj, (hu' m m).2, show ell D ρ m = 1 from if_pos hm]
    · have hlt : j < m := by
        rw [Fin.lt_iff_val_lt_val]
        have h1 := j.2
        have h2 : j.1 ≠ m.1 := fun h => hj (Fin.ext h)
        rw [hmdef] at h2 ⊢
        simp only at h2 ⊢
        omega
      rw [(hu' m j).1 hlt, show ell D ρ j = 0 from if_neg (hne j hj)]
  · intro b _ hb
    rw [show ell D ρ b = 0 from if_neg (hne b hb), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem yZero_mul {V₀ : HSp D} {ρ : ℕ} (z : Fin V₀.rank → D.host.E) (u : GL (Fin ρ) (AE D)) (hu : u ∈ UX D ρ) :
    yZero V₀ ρ z ⬝ u.1 = yZero V₀ ρ z := by
  ext k j
  simp only [yZero, zEll, Matrix.neg_mul, Matrix.neg_apply, Matrix.mul_apply, vecMulVec_apply, neg_mul,
    Finset.sum_neg_distrib, neg_inj]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, ell_mul u hu j]


set_option maxHeartbeats 1000000 in
theorem cond_red : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V₀ W W₀ : HSp D) (ρ : ℕ) (dW : HypDec W W₀ ρ) (p : Pieces V₀ W W₀ ρ ρ) (z : Fin V₀.rank → D.host.E) (P : GlobalTheory.FinPl.Pl D → Prop) (r g : GA D W), r ∈ Rgrp W (xZero dW) → Cond dW p (xZero dW) (yZero V₀ ρ z) ψ P (r * g) → Cond dW p (xZero dW) (yZero V₀ ρ z) ψ P g := by
  intro D ψ V₀ W W₀ ρ dW p z P r g hr H
  have hr' : r⁻¹ ∈ Rgrp W (xZero dW) := inv_mem hr
  obtain ⟨u, hu, hru⟩ := hr
  obtain ⟨u', hu', hru'⟩ := hr'
  have hinv : mt W (r * g)⁻¹ = mt W g⁻¹ ⬝ mt W r⁻¹ := by rw [_root_.mul_inv_rev, mt_mul]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨w, a, ha, hw⟩ := H.pt
    refine ⟨⟨u' * w.1, mul_mem hu' w.2⟩, a, ha, ?_⟩
    have e : mt W (r * g)⁻¹ ⬝ (xZero dW ⬝ w.1.1) = mt W g⁻¹ ⬝ (xZero dW ⬝ (u' * w.1).1) := by
      rw [hinv, Matrix.mul_assoc, ← Matrix.mul_assoc (mt W r⁻¹), hru', Units.val_mul, Matrix.mul_assoc]
    rw [← e]; exact hw
  · intro N hN hup hmem
    have hU := mem_UX.1 (inv_mem hu')
    have h1 : MxAt P ((u'⁻¹).1 ⬝ N) := fun i j => by
      simp only [Matrix.mul_apply]
      exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hN k j)
    have h2 : ∀ i j, j ≤ i → ((u'⁻¹).1 ⬝ N) i j = 0 := by
      intro i j hij
      simp only [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k < i
      · rw [(hU i k).1 hk, zero_mul]
      · rw [hup k j (le_trans hij (not_lt.1 hk)), mul_zero]
    have h3 : mt W (r * g)⁻¹ ⬝ (xZero dW ⬝ ((u'⁻¹).1 ⬝ N)) = mt W g⁻¹ ⬝ (xZero dW ⬝ N) := by
      rw [hinv, Matrix.mul_assoc, ← Matrix.mul_assoc (mt W r⁻¹), hru']
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (u'.1) ((u'⁻¹).1) N, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
    have h4 : upSum ((u'⁻¹).1 ⬝ N) = upSum N := by
      unfold upSum
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      split_ifs with hj
      · simp only [Matrix.mul_apply]
        rw [Finset.sum_eq_single i]
        · rw [(hU i i).2, one_mul]
        · intro k _ hk
          rcases lt_or_gt_of_ne hk with hk | hk
          · rw [(hU i k).1 hk, zero_mul]
          · rw [hup k j (by rw [Fin.le_iff_val_le_val]; have := Fin.lt_iff_val_lt_val.1 hk; omega), mul_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      · rfl
    rw [← h4]
    exact H.shift _ h1 h2 (h3 ▸ hmem)
  · intro ξ hξ ξ' hP he
    have e : mt W (r * g) ⬝ dW.incX V₀ ξ = dW.incX V₀ (u.1 ⬝ ξ') := by
      rw [mt_mul, Matrix.mul_assoc, he, HypDec.incX_apply, HypDec.incX_apply, ← Matrix.mul_assoc,
        show mt W r ⬝ dW.jX = dW.jX ⬝ u.1 from hru, Matrix.mul_assoc]
    rw [← H.iso ξ hξ (u.1 ⬝ ξ') hP e]
    congr 1
    rw [GlobalTheory.OrientedHeis.symplO_skew (dW.incX V₀ ξ') (dW.incAdj V₀ _),
      GlobalTheory.OrientedHeis.symplO_skew (dW.incX V₀ (u.1 ⬝ ξ')) (dW.incAdj V₀ _), HypDec.symplO_incX_incAdj,
      HypDec.symplO_incX_incAdj, ← Matrix.mul_assoc, yZero_mul z u hu]

end GlobalTheory.OneCosetGood

namespace GlobalTheory.OneCosetGood

open GlobalTheory.FinPl (Lat idAt intAt grpAt InK)


set_option maxHeartbeats 1000000 in
theorem oneCoset_good : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (p : Pieces V₀ W W₀ ρ ρ) (z : Fin V₀.rank → D.host.E) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (v : GlobalTheory.FinPl.Pl D), GoodAt dV dW (xZero dW) ψ LV LV₀ LW LW₀ v → StdAt dV dW p LV LW v → (0 < ρ → ∀ a ∈ idAt D (· = v), dW.incAdj V₀ (a • yZero V₀ ρ z) ∈ latO V₀ W (LV₀ : Set _) (LW : Set _) (· = v) ↔ a ∈ intAt D (· = v)) → ∀ h ∈ grpAt W (· = v), (∀ κ, GlobalTheory.FinPl.InK W LW (· = v) κ → Cond dW p (xZero dW) (yZero V₀ ρ z) ψ (· = v) (h * κ)) → CosetAt W (Rgrp W (xZero dW)) LW v h := by
  intro D ψ hψ V V₀ W W₀ ρ dV dW p z LV LV₀ LW LW₀ v hG hS hlast h hh hC
  obtain ⟨n, hnN, hnG, t, ht, htG, γ, hγ, κ, hκ, rfl⟩ :=
    GlobalTheory.IwaPlace.iwasawa_at_place D W W₀ ρ dW LW LW₀ v (GlobalTheory.FinPl.TamePlaces.tame D v) hG.sdW hG.sdW₀ hG.monoW h hh
  have hR : Rgrp W (xZero dW) = jacGrp dW := (GlobalTheory.Unf.base_point D W W₀ ρ dW).2.2.2.1
  have hr : n * dW.emb0 γ ∈ Rgrp W (xZero dW) := by
    rw [hR]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hnN) (Subgroup.mem_sup_right ⟨γ, rfl⟩)
  have heq : n * dW.levi t * dW.emb0 γ * κ * κ⁻¹ = n * dW.emb0 γ * dW.levi t := by
    rw [mul_inv_cancel_right, mul_assoc n, ← dW.wittHyperbolic_anisotropic_commute_levi, mul_assoc]
  have hc := cond_red D ψ V₀ W W₀ ρ dW p z (· = v) _ _ hr (heq ▸ hC κ⁻¹ (inK_inv hκ))
  have hinv := GlobalTheory.T.goodPlace_pointCondition_torus_inverseDiag_integral D ψ hψ V V₀ W W₀ ρ dV dW p LV LV₀ LW LW₀ v hG hS t ht htG hc.pt
  have hint : ∀ i : Fin ρ, t.1 i i - 1 ∈ intAt D (· = v) := by
    intro i
    by_cases hi : i.1 + 1 < ρ
    · exact GlobalTheory.T.goodPlace_shiftCondition_torus_diag_integral D ψ hψ V V₀ W W₀ ρ dV dW p LV LV₀ LW LW₀ v hG hS t ht htG hc.shift i ⟨i.1 + 1, hi⟩ rfl
    · exact _root_.GlobalTheory.AscFin.IsoDiag.last_diag_int_iso D ψ hψ V V₀ W W₀ ρ dV dW p z LV LV₀ LW LW₀ v hG hS hlast t ht htG hc.iso i (by omega)
  have hK := GlobalTheory.FinPl.LeviUnitK.inK_levi D W W₀ ρ dW LW LW₀ v hG.sdW hG.monoW t ht htG (fun i => ⟨hint i, hinv i⟩)
  refine ⟨n * dW.emb0 γ, hr, ?_, dW.levi t * κ, inK_mul hK hκ, ?_⟩
  · exact Subgroup.mul_mem _ hnG (GlobalTheory.OneCosetEmb.wittCoreEmbedding_mem_unitaryAdelicSupportedSubgroup D W W₀ ρ dW (· = v) γ hγ)
  · rw [mul_assoc n (dW.levi t), ← dW.wittHyperbolic_anisotropic_commute_levi γ t]
    simp only [mul_assoc]

end GlobalTheory.OneCosetGood

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointEqUnipotentFrameChangeCosetRep
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

namespace GlobalTheory.HeckePointCoset

theorem exists_coset_frBor :
    ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV →
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ (h : GA D (Wc D i)) (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∀ C : hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩),
        ∀ z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z →
        ∀ (k' : (T.U ((i : ℕ) + 1) σ).Comp) (x' : ((T.U ((i : ℕ) + 1) σ).X k').dom) (t' : Ix (T.Q.Dw ((i : ℕ) + 1)) → (CAt σ)ˣ),
          FrBor t' ((T.U ((i : ℕ) + 1) σ).un k' x') z →
        ∀ (gam : ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).Λ →ₗ[𝓞 D.host.E] ((T.U ((i : ℕ) + 1) σ).X k').Λ) (A : (D.host.E →+* ℂ) → ℕ → ℕ → ℂ),
          (∀ u v : ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).Λ, Algebra.trace ℚ D.host.E (-((T.U ((i : ℕ) + 1) σ).X k').ξ0 * ReciprocityTheory.ChartRestriction.G.FD.herm ((T.U ((i : ℕ) + 1) σ).X k').Gm (gam u : Fin D.R.r → D.host.E) (gam v : Fin D.R.r → D.host.E)) =
            (p : ℚ) ^ 2 * Algebra.trace ℚ D.host.E (-((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).ξ0 * ReciprocityTheory.ChartRestriction.G.FD.herm ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).Gm (u : Fin D.R.r → D.host.E) (v : Fin D.R.r → D.host.E))) →
          (∀ w : ((T.U ((i : ℕ) + 1) σ).X k').Λ, ∃ v, gam v = (p ^ 2) • w) →
          (∀ τ a b, b < a → A τ a b = 0) →
          (∀ τ, ∀ n < (T.Q.Dw ((i : ℕ) + 1)).mult τ, ∀ v : ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).Λ,
            perFr ((T.U ((i : ℕ) + 1) σ).X k') x'.1 (gam v : Fin D.R.r → D.host.E) (relab T.Q.c σ τ) n =
              p * ∑ b ∈ Finset.range ((T.Q.Dw ((i : ℕ) + 1)).mult τ), A τ n b * perFr ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 (v : Fin D.R.r → D.host.E) (relab T.Q.c σ τ) b) →
          (∀ τ (n : Fin ((T.Q.Dw ((i : ℕ) + 1)).mult τ)), A τ n n = toC (t' (some ⟨τ, n⟩) : CAt σ)) →
          ∃ a ∈ Rc, ∃ (hx' : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1).dom) (t : Ix (T.Q.Dw ((i : ℕ) + 1)) → (CAt σ)ˣ),
            (∀ j, j ≠ none → t j = 1) ∧ FrBor t ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2, hx'⟩) z :=
  GlobalTheory.HeckePointIdent.exists_coset_frBor_of_lift

end GlobalTheory.HeckePointCoset
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InBigFb
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.Unf.FB GlobalTheory.FinPl GlobalTheory.FinPl.HandInvPf
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowOneCos

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}


set_option maxHeartbeats 1000000 in
theorem flatBF_source {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) {Ψ : WO B.V J.W → ℂ}
    (hΨ : IsThetaFunO ψ B.V J.W Ψ) {n : GA D B.V} (hn : n ∈ flagN B.d) :
    ∃ c : ℂ, c ≠ 0 ∧ flatBF s (s.om (n, 1) Ψ) = c • flatBF s Ψ := by
  have hψ := s.weil.std
  obtain ⟨u, hu, b, c, rfl⟩ := GlobalTheory.MixPer.Decomp.flag_decomp B.d hn
  obtain ⟨om', hom'⟩ := (GlobalTheory.Desc.weil_data_descend D ψ B.V J.W s.χV s.χW s.om s.weil).1 B.V₀ ρ B.d
  have FS := fun f hf => _root_.GlobalTheory.MixSourceFormulas.mixed_source D ψ B.V B.V₀ J.W ρ B.d s.χV s.χW s.om om' s.weil hom' s.vS.μ s.vS.𝓕 s.vS.covol f hf
  have MV := fun x => (_root_.GlobalTheory.MixValues.mixed_values D ψ hψ).1 B.V B.V₀ J.W ρ B.d s.vS.μ s.vS.𝓕 s.vS.covol Ψ hΨ x
  have hdet : Matrix.GeneralLinearGroup.det u = 1 := by
    have bt : Matrix.BlockTriangular u.1 id := fun a b h => (hu a b).1 h
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_isUpperTriangular bt, Units.val_one]
    exact Finset.prod_eq_one fun i _ => (hu i i).2
  have hmod : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod J.W.rank u = 1 := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod, hdet, map_one, NNReal.coe_one, Real.one_rpow]
  have h1 := s.weil.om_pres (B.d.nC c, 1) Ψ hΨ
  have h2 := s.weil.om_pres (B.d.nB b, 1) _ h1
  have e : s.om (B.d.levi u * (B.d.nB b * B.d.nC c), 1) Ψ =
      s.om (B.d.levi u, 1) (s.om (B.d.nB b, 1) (s.om (B.d.nC c, 1) Ψ)) := by
    rw [← om_mul, ← om_mul, mul_assoc, mul_one, mul_one]
  let u' : UX D ρ := ⟨u, hu⟩
  have hq : ∀ X : Mx D ρ ρ, B.d.qS J.W c (xZero J.d ⬝ X) = 0 := fun X => by
    have h0 : adj J.d.jX ⬝ (gA J.W ⬝ (J.d.jX ⬝ X)) = 0 := by
      rw [← Matrix.mul_assoc, ← J.d.pY_eq, ← Matrix.mul_assoc, J.d.pY_jX, Matrix.zero_mul]
    rw [HypDec.qS, HypDec.symplOH_extX_extY, pairS, xZero, adj_mul, adj_mul, Matrix.mul_assoc, Matrix.mul_assoc, h0,
      Matrix.mul_zero, Matrix.mul_zero, trace_zero, map_zero]
  set y := yZero B.V₀ ρ (vecB B.o B.ζ) with hy
  set k : ℂ := ψ (Algebra.trace (AF D.host.F) (AE D) (ell D ρ ⬝ᵥ b *ᵥ ratV (vecB B.o B.ζ))) with hk
  have key : ∀ v : UX D ρ,
      evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (B.d.levi u * (B.d.nB b * B.d.nC c), 1) Ψ) (xZero J.d ⬝ v.1.1) y =
        k • evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ (v * u').1.1) y := by
    intro v
    have ex : xZero J.d ⬝ v.1.1 ⬝ u.1 = xZero J.d ⬝ (v * u').1.1 := by
      rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]
    have t1 := (FS _ h2).levi u (xZero J.d ⬝ v.1.1)
    rw [hdet, hmod, map_one, inv_one, Circle.coe_one, Complex.ofReal_one, mul_one, one_smul, ex] at t1
    have t2 := (FS _ h1).unip b (xZero J.d ⬝ (v * u').1.1)
    rw [Matrix.mul_assoc (xZero J.d)] at t2
    have t3 : B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 (s.om (B.d.nC c, 1) Ψ) (xZero J.d ⬝ (v * u').1.1) =
        ψ (B.d.qS J.W c (xZero J.d ⬝ (v * u').1.1)) • B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 Ψ (xZero J.d ⬝ (v * u').1.1) :=
      (FS _ hΨ).centre c _
    rw [hq, AddChar.map_zero_eq_one, one_smul] at t3
    rw [e]
    change (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target J.d) B.V₀ ψ s.vT.μ s.vT.𝓕
      (B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 _ _) y =
      k • (_root_.I195MixedCoordinates_a63f0715cbf334f1e52c5d7b.target J.d) B.V₀ ψ s.vT.μ s.vT.𝓕
        (B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 Ψ _) y
    change B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 _ _ = B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 _ _ at t1
    change B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 _ _ = heisO ψ B.V₀ J.W _ (B.d.mixS J.W ψ s.vS.μ s.vS.𝓕 _ _) at t2
    rw [t1, t2, t3]
    have t4 := (_root_.GlobalTheory.HeisTarget.main D ψ hψ B.V₀ J.W J.W₀ ρ J.d s.vT.μ s.vT.𝓕 s.vT.covol _ (MV (xZero J.d ⬝ (v * u').1.1))).1
      ((v * u').1.1 ⬝ b) y
    have t5 : symplO B.V₀ J.W (J.d.incAdj B.V₀ y) (J.d.incX B.V₀ ((v * u').1.1 ⬝ b)) =
        Algebra.trace (AF D.host.F) (AE D) (ell D ρ ⬝ᵥ b *ᵥ ratV (vecB B.o B.ζ)) := by
      refine (symplO_yZero J.d _ _).trans ?_
      rw [← Matrix.mulVec_mulVec, dotProduct_mulVec, ell_vecMul (v * u').2]
    rw [t5] at t4
    exact t4
  have : BorelSpace (UX D ρ) := ⟨rfl⟩
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.UnitU.topology D ρ
  have := (GlobalTheory.UnitU.isUnitU_exists_unique_rightInvariant D ρ).2.2 _ s.vU.unit
  have hmul : ∀ v : UX D ρ, psiUni ψ (v * u').1 = psiUni ψ v.1 * psiUni ψ u := fun v => by
    rw [← ThLaws.psiFlag_levi ψ J.d, ← ThLaws.psiFlag_levi ψ J.d, ← ThLaws.psiFlag_levi ψ J.d, Subgroup.coe_mul, map_mul,
      psiFlag_mul J.d ψ (J.d.levi_mem_NFlag v.2) (J.d.levi_mem_NFlag hu)]
  have hu1 : psiUni ψ u * star (psiUni ψ u) = 1 := mul_star_psi hψ _
  refine ⟨psiUni ψ u * k, mul_ne_zero (left_ne_zero_of_mul_eq_one hu1) (GlobalTheory.FlatRInv.addChar_ne_zero ψ _), ?_⟩
  funext w
  simp only [Pi.smul_apply, smul_eq_mul]
  change ∫ v, star (psiUni ψ v.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕
      (s.om (B.d.levi u * (B.d.nB b * B.d.nC c), 1) Ψ) (xZero J.d ⬝ v.1.1) y w ∂s.vU.ν = _ *
    ∫ v, star (psiUni ψ v.1) * evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ v.1.1) y w ∂s.vU.ν
  conv_rhs => rw [← integral_mul_right_eq_self _ u', ← integral_const_mul]
  congr 1
  funext v
  rw [key, hmul, star_mul']
  simp only [Pi.smul_apply, smul_eq_mul]
  generalize evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ (v * u').1.1) y w = z
  linear_combination (-(star (psiUni ψ v.1) * k * z)) * hu1

theorem flatBF_src_ne {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) {Ψ : WO B.V J.W → ℂ}
    (hΨ : IsThetaFunO ψ B.V J.W Ψ) {r : GA D B.V} (hr : r ∈ besGrp B.d B.o) (h : flatBF s (s.om (r, 1) Ψ) ≠ 0) :
    flatBF s Ψ ≠ 0 := by
  intro h0
  apply h
  obtain ⟨n, hn, a, rfl⟩ := (GlobalTheory.CharLaws.mem_besGrp B.d B.o r).1 hr
  obtain ⟨om', hom'⟩ := (GlobalTheory.Desc.weil_data_descend D ψ B.V J.W s.χV s.χW s.om s.weil).1 B.V₀ ρ B.d
  have e := _root_.GlobalTheory.FlatEqui.flatBF_equivariant D ψ ρ B J s om' hom' Ψ hΨ a 1 (one_mem _) 1
  rw [map_one, mul_one, h0, (GlobalTheory.FlatRInv.opA_eq_zero_iff ψ J.d B.o B.ζ s.om₀ 1 1 0).2 rfl, map_zero, smul_zero] at e
  obtain ⟨c, -, hc⟩ := flatBF_source s (s.weil.om_pres (embA B.d B.o a, 1) Ψ hΨ) hn
  rw [← om_mul, one_mul, e, smul_zero] at hc
  exact hc

theorem flatFB_src_ne {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ} (s : StepFB ψ J B) {Ψ : WO J.W B.V → ℂ}
    (hΨ : IsThetaFunO ψ J.W B.V Ψ) {r : GA D J.W} (hr : r ∈ jacGrp J.d) (h : flatFB s (s.om (r, 1) Ψ) ≠ 0) :
    flatFB s Ψ ≠ 0 := by
  intro h0
  apply h
  obtain ⟨n, hn, a, rfl⟩ := (GlobalTheory.MixPer.Decomp.mem_jacGrp_iff J.d).1 hr
  have e := GlobalTheory.T.jacobiToBesselFlat_intertwines_weilAction D (GlobalTheory.Desc.weil_data_descend D) ψ σ J B s Ψ hΨ a 1
  rw [map_one, h0, map_zero] at e
  have hc := flatFB_source s (s.weil.om_pres (J.d.emb0 a, 1) Ψ hΨ) hn
  rw [← om_mul, one_mul, e, (GlobalTheory.FlatRInv.heisO_eq_zero_iff ψ _ _ _ 0).2 rfl, smul_zero] at hc
  exact hc

theorem inBig_bf {ρ : ℕ} {B : BesLev D ρ} {J : JacLev D ρ} (s : StepBF ψ B J) {LV : Lat B.V} {LV₀ : Lat B.V₀} {LW : Lat J.W}
    {LW₀ : Lat J.W₀} {P : Pl D → Prop} (good : ∀ v, P v → GoodBF ψ B J LV LV₀ LW LW₀ v) (unr : ∀ v, P v → UnrAt s v)
    (sd : IsSelfDualC J.W LW) {Φ : WO B.V J.W → ℂ} (hΦ : Vac ψ B.V J.W LV LW P Φ) {g : GA D B.V} {h : GA D J.W}
    (hg : InBig B.V (besGrp B.d B.o) LV P g) (hne : flatBF s (s.om (g, h) Φ) ≠ 0) : InBig J.W (jacGrp J.d) LW P h := by
  obtain ⟨r, hr, -, g', hg', κ, hκ, rfl⟩ := hg
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.FinPl.suppFirst_all D ψ ρ B J s LV LV₀ LW LW₀ P good unr sd Φ hΦ
  refine (h2 g' hg').1 h (flatBF_src_ne s (s.weil.om_pres _ _ hΦ.1) hr ?_)
  have e : s.om (r * g' * κ, h) Φ = s.om (r, 1) (s.om (g', h) (s.om (κ, 1) Φ)) := by
    rw [← om_mul, ← om_mul, one_mul, mul_one]
  rwa [e, h1 κ 1 hκ ⟨one_mem _, fun y _ => by rw [mt_one, Matrix.one_mulVec]⟩] at hne

theorem inBig_fb {σ : ℕ} {J : JacLev D (σ + 1)} {B : BesLev D σ} (s : StepFB ψ J B) {LV : Lat J.W} {LV₀ : Lat J.W₀} {LW : Lat B.V}
    {LW₀ : Lat B.V₀} {P : Pl D → Prop} (ad : ∀ v, P v → AdaptFB ψ J B LV LV₀ LW LW₀ v) (unr : ∀ v, P v → UnrAt s v)
    (spl : ∀ v, P v → SplitCore B LW₀ v) (sdV : IsSelfDualC J.W LV) (sd : IsSelfDualC B.V LW) {Φ : WO J.W B.V → ℂ}
    (hΦ : Vac ψ J.W B.V LV LW P Φ) {g : GA D J.W} {h : GA D B.V}
    (hg : InBig J.W (jacGrp J.d) LV P g) (hne : flatFB s (s.om (g, h) Φ) ≠ 0) : InBig B.V (besGrp B.d B.o) LW P h := by
  obtain ⟨r, hr, -, g', hg', κ, hκ, rfl⟩ := hg
  have tameP : ∀ v, P v → Tame D v := fun v hv => (ad v hv).tame
  have h1 := _root_.GlobalTheory.StabSetFix.stab_fix_vac D ψ J.W B.V s.χV s.χW s.om s.weil LV LW sdV sd P
    (fun v hv => ⟨tameP v hv, (unr v hv).1, (unr v hv).2⟩) Φ hΦ κ 1 hκ ⟨one_mem _, fun y _ => by rw [mt_one, Matrix.one_mulVec]⟩
  have e : s.om (r * g' * κ, h) Φ = s.om (r, 1) (s.om (g', h) (s.om (κ, 1) Φ)) := by
    rw [← om_mul, ← om_mul, one_mul, mul_one]
  rw [e, h1] at hne
  replace hne := flatFB_src_ne s (s.weil.om_pres _ _ hΦ.1) hr hne
  refine _root_.GlobalTheory.FinPl.placesToAdeles_all D B.V LW P sd (besGrp B.d B.o) h fun v hv => ?_
  obtain ⟨x, hx, h', hh', rfl⟩ := _root_.GlobalTheory.FinPl.decompAt D B.V h v
  refine ⟨x, hx, h', hh', rfl, ?_⟩
  have hΦv : Vac ψ J.W B.V LV LW (· = v) Φ :=
    ((_root_.GlobalTheory.VacLoc.vac_loc D ψ J.W B.V s.χV s.χW s.om s.weil LV LW sdV sd P tameP Φ).1.mp hΦ).2 v hv
  have hf : Vac ψ J.W B.V LV LW (· = v) (s.om (g', h') Φ) :=
    (_root_.GlobalTheory.VacLoc.vac_loc D ψ J.W B.V s.χV s.χW s.om s.weil LV LW sdV sd (· = v)
      (fun w hw => hw ▸ tameP v hv) Φ).2.1 hΦv g' (_root_.GlobalTheory.FinPl.grpOff_anti D J.W P (· = v) (fun w hw => hw ▸ hv) hg') h' hh'
  have hom : s.om (g', x * h') Φ = s.om (1, x) (s.om (g', h') Φ) := by rw [← om_mul, one_mul]
  rw [hom] at hne
  obtain ⟨n, hnF, hnv, γ, hγ, k, hk, hdec, hγp⟩ :=
    (_root_.GlobalTheory.FinPl.supportShift D ψ σ J B s LV LV₀ LW LW₀ v (ad v hv) (unr v hv) (flatFB s)
      ((GlobalTheory.FlatLawsDuality.flatLaws_all D ψ (· = v)).2 σ J B s) ((_root_.GlobalTheory.FlatShiftPf.flatShift D ψ (· = v)).2 σ J B s) _ hf).2 x hx hne
  obtain ⟨a₀, ha₀, κ₀, hκ₀, rfl⟩ := _root_.GlobalTheory.FinPl.SplitOrbit.orbitSplit D σ B LW₀ v (tameP v hv) (ad v hv).sdW₀ (spl v hv) γ hγ hγp
  obtain ⟨r', hr', hrv, κ', hκ', heq⟩ := _root_.GlobalTheory.FinPl.OrbitCoset.orbit_coset D σ B LW LW₀ v (ad v hv).monoW n hnF hnv a₀ ha₀ κ₀ hκ₀ k hk
  exact ⟨r', hr', hrv, κ', hκ', hdec.trans heq⟩

end GlobalTheory.RowOneCos

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemAdelicLatticeAtPlaceOfTensorWithLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.FinDecomp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_adelicLatticeAtPlace_of_tensor_with_lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n d : ℕ)
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (q : Fin d → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), 0 < n → X.L.IsFullLattice E →
    (∀ x ∈ X.L, Matrix.vecMulVec (fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F) (x i)) q ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X W v) →
    q ∈ GlobalTheory.InertSph.latAt W v := by
  intro F E _ _ _ _ _ n d X W v q hn hL h
  letI := hL
  exact GlobalTheory.LatExtract.main F E n d X W v q hn inferInstance h
end

