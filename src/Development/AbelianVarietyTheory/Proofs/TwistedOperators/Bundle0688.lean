module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0336
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0603
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockConjugatesSpanDepthData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0343
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0543
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0575
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0588
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0687
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0679
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0669
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0678
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0685
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0641
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0643
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0672

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodNonvanishingAscentOfDepthData
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.Asc

theorem ascent_of_depFixed : DepFixed → Ascent := fun hD =>
  have hTot : FockTot := _root_.GlobalTheory.ConjDataTotal.fockTot
  have hPart : PartFixed := _root_.GlobalTheory.Asc.partFixed_of_depFixed hD _root_.GlobalTheory.FirstRowDepth.datumDep
  _root_.GlobalTheory.Asc.ascent_of_rungs (_root_.GlobalTheory.AscFin.towerEx_of_depFixed hD) (GlobalTheory.T.nonvanishing_thetaTower_bottom_rung hTot) (_root_.GlobalTheory.AscRungB.rungB hTot hPart)
    (_root_.GlobalTheory.Asc.RungJac.rungJ hTot hPart)

end GlobalTheory.Asc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryBaseVacuaLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowVal

theorem exists_locAt_big : Big fun ch => ∃ s, LocAt ch s :=
  GlobalTheory.RowReal.big_mono (fun ch h => by
               obtain ⟨⟨⟨s, hP⟩, hC⟩, hL⟩ := h
               exact ⟨s, hL s hP hC⟩)
    (Big.and (Big.and _root_.GlobalTheory.FlatPlace.big_placeAt _root_.GlobalTheory.RowVal.conLin_big) _root_.GlobalTheory.LocAsm.locAt_of_placeAt)

end GlobalTheory.RowVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalisedKernelExpansionSumLevelInvariant
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.ExpansionInvariance

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem levels_invariant (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T}
    (hL : L.Is μ₀) (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) (ht : t ∈ U)
    (hβ : β ∈ S.supp t Φ) (hτ : S.IsExpansion t Φ β τ)
    (hv : ∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i))
    (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))) :
    (∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (j : ℕ) (hj : 0 < j) (hjm : j < D.R.m) (k : FinPt G (.top j)),
      finG (G.V (.top j)) k ∈ S.levTop t Φ β j hjm →
      pairPts S τ (Function.update x j (x j * k)) y (Ψ (Function.update x j (x j * k) 0)) (F (y 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0))) ∧
    ((∀ (x : FinPt G (.top 0)) (k : FinPt G (.top 0)), finG (G.V (.top 0)) k ∈ G.Kplus → Ψ (x * k) = Ψ x) →
    ∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.top 0)),
      finG (G.V (.top 0)) k ∈ S.levTop t Φ β 0 (by have := D.R.two_le_m; omega) →
      pairPts S τ (Function.update x 0 (x 0 * k)) y (Ψ (x 0 * k)) (F (y 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0))) ∧
    (∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (i : ℕ) (hi : 0 < i) (him : i < D.R.m) (k : FinPt G (.grid i D.R.m)),
      finG (G.V (.grid i D.R.m)) k ∈ S.levRow t i him.le →
      pairPts S τ x (Function.update y i (y i * k)) (Ψ (x 0)) (F (Function.update y i (y i * k) 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0))) ∧
    (∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (k : FinPt G (.grid D.R.m D.R.m)),
      x D.R.m = finEmb G.sp.topDec (y D.R.m) → finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl →
      pairPts S τ (Function.update x D.R.m (finEmb G.sp.topDec (y D.R.m * k))) (Function.update y D.R.m (y D.R.m * k))
        (Ψ (Function.update x D.R.m (finEmb G.sp.topDec (y D.R.m * k)) 0)) (F (Function.update y D.R.m (y D.R.m * k) 0)) =
      pairPts S τ x y (Ψ (x 0)) (F (y 0))) :=
  ⟨_root_.GlobalTheory.ExpansionInvariance.pairPts_update_top S hL hde hc ht hβ hτ hv Ψ F, GlobalTheory.T.expansionPairing_invariant_parabolic_basePoint S hL hde hc ht hβ hτ hv Ψ F,
    _root_.GlobalTheory.RowVertexInv.pairPts_update_row S hL hde hc ht hβ hτ hv Ψ F, GlobalTheory.T.expansion_pairing_invariant_last_vertex_level S hL hde hc ht hβ hτ hv Ψ F⟩

end GlobalTheory.ExpansionInvariance

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TiltedPointsCoveredByRepresentativeCells
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RowVal

theorem eltAt {k : Type} [Field k] {Gr : GlobalTheory.SplitFlip.Grid k} {hs : 1 ≤ Gr.s} {J : Gr.Level} (ρ : Reps hs J)
    (β : Cosets hs J) (i : ℕ) (hi : i < Gr.m - 2) : ρ.elt β (Gr.m, i + 1) = ρ.rep ⟨i, hi⟩ (β ⟨i, hi⟩) := by
  rw [Reps.elt, onColumn_apply]
  simp only [dif_pos hi]


set_option maxHeartbeats 1600000 in
theorem cover_at : Big fun ch => ∀ s, CoverAt ch s := by
  refine big_mono (fun {D} _ _ _ _ _ _ _ _ _ _ _ ch h => ?_) (Big.and _root_.GlobalTheory.LatOfHasLoc.mem_latGrp_of_hasLoc GlobalTheory.T.exists_periodGroup_point_lifting_rowGroup_localElements)
  obtain ⟨h5, h7⟩ := h
  classical
  intro s t b hb p hp
  have hidx : ∀ i : ℕ, i < D.R.m - 2 → i + 1 ∈ idx D := fun i hi => by
    simp only [idx, List.mem_range'_1]; omega
  choose r hr a ha δ x g hδ hx k hk hpe using hp
  let β : CosFam ch.G t := fun w i => DoubleCoset.mk _ _
    ((sgnAt ch.G t s w.1 (i + 1))⁻¹ * g (i + 1) (hidx i i.2) (by have h : (i : ℕ) < D.R.m - 2 := i.2; omega) w)
  refine ⟨β, fun j hj => ?_⟩
  have hj1 : 1 ≤ j ∧ j < 1 + (D.R.m - 2) := by simpa [idx, List.mem_range'_1] using hj
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hi : i < D.R.m - 2 := by omega
  have hjm : i + 1 ≤ D.R.m := by omega
  have hj' : i + 1 < D.R.m := by omega
  obtain ⟨-, hb2⟩ := hb β
  obtain ⟨δ', r', hδ', hr', hfin, a₀, ha₀, hab⟩ := hb2 (i + 1) hj hjm
  have key : ∀ w : locPl ch.G t, ∃ l : GL (Fin ((locGrid ch.G t w.1).rank (D.R.m, i + 1))) (Kw w.1), l ∈ rowR (G := locGrid ch.G t w.1) one_le_sLen (j := i + 1) hj' ∧
      ∃ κ ∈ givenLevel ch.G t w.1 (D.R.m, i + 1),
        (repsAt ch.G t w.1).elt (β w) (D.R.m, i + 1) =
          l * ((sgnAt ch.G t s w.1 (i + 1))⁻¹ * g (i + 1) hj hjm w) * κ := by
    intro w
    have e1 : (repsAt ch.G t w.1).elt (β w) (D.R.m, i + 1) = (repsAt ch.G t w.1).rep ⟨i, hi⟩ (β w ⟨i, hi⟩) :=
      eltAt (repsAt ch.G t w.1) (β w) i hi
    have e2 := (repsAt ch.G t w.1).mk_rep ⟨i, hi⟩ (β w ⟨i, hi⟩)
    rw [e1]
    obtain ⟨l, hl, κ, hκ, e⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 e2.symm
    exact ⟨l, hl, κ, hκ, e⟩
  choose l hl κ hκ hrep using key
  obtain ⟨y, hy, hyR⟩ := h7 s t (i + 1) hj hjm hj' (δ (i + 1) hj hjm) (hδ _ _ _) (fun w => (l w)⁻¹)
    fun w => inv_mem (hl w)
  have h1 := _root_.GlobalTheory.RowVal.hasLoc_mul t ch.S.B hjm y r' _ _ hy hr'
  have h2 := _root_.GlobalTheory.RowVal.hasLoc_inv t ch.S.B hjm (y * r') _ h1
  have hz := _root_.GlobalTheory.RowVal.hasLoc_mul t ch.S.B hjm ((y * r')⁻¹) (x (i + 1) hj hjm) _ _ h2 (hx (i + 1) hj hjm)
  have hfun : (fun w => ((sgnAt ch.G t s w.1 (i + 1) * (l w)⁻¹ * (sgnAt ch.G t s w.1 (i + 1))⁻¹) *
      (sgnAt ch.G t s w.1 (i + 1) * (repsAt ch.G t w.1).elt (β w) (D.R.m, i + 1)))⁻¹ * g (i + 1) hj hjm w) =
      fun w => (κ w)⁻¹ := by
    funext w
    rw [hrep w]
    group
  rw [hfun] at hz
  set z := (y * r')⁻¹ * x (i + 1) hj hjm with hzdef
  have hzl : z ∈ latGrp ch.G (i + 1) := h5 t (i + 1) (by omega) hjm _ _ hz fun w => inv_mem (hκ w)
  have htilt : δ (i + 1) hj hjm = δ' := _root_.GlobalTheory.TiltUnique.tilt_unique ch.G hj' _ _ (hδ _ _ _) hδ'
  have hyf : y ∈ GfC _ := _root_.GlobalTheory.RowCover.mem_GfC_of_hasLoc t ch.S.B hjm _ _ hy
  set Y := δ (i + 1) hj hjm * y * (δ (i + 1) hj hjm)⁻¹ with hY
  have hYf : Y ∈ GfC _ := by
    rw [GfC, MonoidHom.mem_ker] at hyf ⊢
    rw [hY, map_mul, map_mul, hyf, mul_one, map_inv, mul_inv_cancel]
  have hcomm : a (i + 1) hj hjm * Y = Y * a (i + 1) hj hjm :=
    (GlobalTheory.AdelicSplit.adelic_split D _).2.2.1 _ (ha _ _ _) _ hYf
  refine ⟨r (i + 1) hj hjm * Y, mul_mem (hr _ _ _) hyR, a (i + 1) hj hjm * a₀, mul_mem (ha _ _ _) ha₀,
    z * k (i + 1) hj hjm, mul_mem hzl (hk _ _ _), ?_⟩
  have hxz : x (i + 1) hj hjm = y * r' * z := by rw [hzdef, mul_inv_cancel_left]
  rw [hpe (i + 1) hj hjm, hxz, show r (i + 1) hj hjm * Y * (a (i + 1) hj hjm * a₀) * b β (i + 1) * (z * k (i + 1) hj hjm) =
    r (i + 1) hj hjm * (a (i + 1) hj hjm * Y) * (a₀ * b β (i + 1)) * z * k (i + 1) hj hjm by
      rw [hcomm]; simp only [mul_assoc], hab, ← htilt, hY]
  simp only [mul_assoc, inv_mul_cancel_left]

end GlobalTheory.RowVal
end
end

