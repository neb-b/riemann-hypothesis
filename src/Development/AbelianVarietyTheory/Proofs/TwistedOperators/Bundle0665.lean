module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0629
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0639
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0650
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0506
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0483
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0093
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0647
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0458
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0648
public import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0649
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0632
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0480
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0391
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0465
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGivenStageEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0637
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0345
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0407
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0601
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0419
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0295
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0447
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.QEqColPer
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR Formalism.IndefR.Links GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.ChiGrid GlobalTheory.Unf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowChain

open GlobalTheory.FunObj GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (Wl : G.Weil) {t : T} {M : Vol G}

theorem Q_eq_colPer (hM : M.Is t) : ∀ (σ j : ℕ) (hj : j + 2 * σ + 2 = D.R.m) (vN : VolN (besDecAt G j σ hj))
    (Φ : (chainFrom G Wl t hM σ j hj vN).Data), (chainFrom G Wl t hM σ j hj vN).IsTheta Φ →
    ∀ (F : Fn G (.grid D.R.m D.R.m)), IsContAut _ F → ∀ (φ : GA D (G.V (.top j)) → ℂ), IsContAut _ φ →
    ∀ (g : GA D (G.V (.grid D.R.m j))) (h : (chainFrom G Wl t hM σ j hj vN).Var),
      (chainFrom G Wl t hM σ j hj vN).Q Φ F φ g h = colPer Wl hM σ j hj vN Φ F φ g h
  | 0, j, hj, vN, Φ, hΦ, F, hF, φ, hφ, g, _ => LastSeeSawStep.main G Wl t hM j hj vN Φ.1 Φ.2 F φ hΦ.1 hΦ.2 hF hφ g
  | σ + 1, j, hj, vN, Φ, hΦ, F, hF, φ, hφ, g, h => by
    have ih := Q_eq_colPer hM σ (j + 1 + 1) (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some Φ.2.2 hΦ.2.2 F hF
    let B := besAt G hM j (σ + 1) hj vN
    let J := jacAt G hM (j + 1) (σ + 1) (by omega)
    let B' := besAt G hM (j + 1 + 1) σ (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN (besDecAt G (j + 1 + 1) σ (by omega))).some
    let s₁ : StepBF Wl.ψ B J :=
      stepAt G Wl t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
    let s₂ : StepFB Wl.ψ J B' :=
      stepAt G Wl t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)) (besDecAt G (j + 1 + 1) σ (by omega))
    have t₁ : IsThetaFunO Wl.ψ B.V₀ J.W₀ (flatBF s₁ (s₁.om (g, h.1) Φ.1)) :=
      (GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (_root_.GlobalTheory.Unf.Flat.flatLaw D) Wl.ψ).1 _ B J s₁ _ (s₁.weil.om_pres (g, h.1) _ hΦ.1)
    have t₂ : IsThetaFunO Wl.ψ J.W₀ B'.V₀ (flatFB s₂ (s₂.om (h.1, h.2.1) Φ.2.1)) :=
      (GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (_root_.GlobalTheory.Unf.Flat.flatLaw D) Wl.ψ).2 _ J B' s₂ _ (s₂.weil.om_pres (h.1, h.2.1) _ hΦ.2.1)
    have hc := GlobalTheory.FinPl.ValDbl.contAut_hand0 s₁ s₂ (linkAt hM j σ hj vN (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
      ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some) hφ t₁ t₂
    have e := ih _ hc h.2.1 h.2.2
    refine e.trans ?_
    show colPer Wl hM σ (j + 1 + 1) _ _ Φ.2.2 F _ h.2.1 h.2.2 = colPer Wl hM σ (j + 1 + 1) _ _ Φ.2.2 F _ h.2.1 h.2.2
    congr 1
    exact dbl_hand_eq_biLift G Wl t hM σ j hj vN Φ.1 Φ.2.1 φ hΦ.1 hΦ.2.1 hφ g h.1 h.2.1

end GlobalTheory.RowChain

namespace GlobalTheory.RowChain

open GlobalTheory.FunObj GlobalTheory.RowUnf

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (Wl : G.Weil) {t : T} {M : Vol G}

theorem iter_chain (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) (hd : AllTheta G Wl t d) (F : Fn G (.grid D.R.m D.R.m))
    (hF : IsContAut _ F) (φ : GA D (G.V (.top 0)) → ℂ) (hφ : IsContAut _ φ)
    (hR : (chain G Wl t hM).Rapid (chainData G Wl t hM d) F) :
    (chain G Wl t hM).Iter ((chain G Wl t hM).Q (chainData G Wl t hM d) F φ 1)
      ((topLev G hM).per Wl.ψ φ ((chain G Wl t hM).down (chainData G Wl t hM d) F)) := by
  have h := (GlobalTheory.Unf.unfoldings_of_chain D).2.2.2.2.2.1 Wl.ψ _ _ _ (chain G Wl t hM) (chainData G Wl t hM d) F φ 1
    (chainData_isTheta G Wl t hM d hd) hF hφ hR
  have e : rTrans 1 ((chain G Wl t hM).down (chainData G Wl t hM d) F) = (chain G Wl t hM).down (chainData G Wl t hM d) F := by
    funext z; simp [rTrans]
  rwa [e] at h

theorem chain_Q_eq (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) (hd : AllTheta G Wl t d) (F : Fn G (.grid D.R.m D.R.m))
    (hF : IsContAut _ F) (φ : GA D (G.V (.top 0)) → ℂ) (hφ : IsContAut _ φ) (h' : (chain G Wl t hM).Var) :
    (chain G Wl t hM).Q (chainData G Wl t hM d) F φ 1 h' =
      colPer Wl hM _ 0 top_idx (topVN hM) (chainData G Wl t hM d) F φ 1 h' :=
  Q_eq_colPer Wl hM _ 0 top_idx (topVN hM) _ (chainData_isTheta G Wl t hM d hd) F hF φ hφ 1 h'

theorem iter_colPer (hM : M.Is t) (d : PureT G (downPath t D.R.m D.R.m)) (hd : AllTheta G Wl t d) (F : Fn G (.grid D.R.m D.R.m))
    (hF : IsContAut _ F) (φ : GA D (G.V (.top 0)) → ℂ) (hφ : IsContAut _ φ)
    (hR : (chain G Wl t hM).Rapid (chainData G Wl t hM d) F) :
    (chain G Wl t hM).Iter (colPer Wl hM _ 0 top_idx (topVN hM) (chainData G Wl t hM d) F φ 1)
      ((topLev G hM).per Wl.ψ φ ((chain G Wl t hM).down (chainData G Wl t hM d) F)) := by
  have h := iter_chain Wl hM d hd F hF φ hφ hR
  have e : (chain G Wl t hM).Q (chainData G Wl t hM d) F φ 1 = colPer Wl hM _ 0 top_idx (topVN hM) (chainData G Wl t hM d) F φ 1 :=
    funext (chain_Q_eq Wl hM d hd F hF φ hφ)
  rwa [e] at h

end GlobalTheory.RowChain
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowDataLocalPureTensorsLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowSingle

theorem locPl_under {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) (t : T) :
    ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ∈ G.pl.S0 ∨ ∃ w' ∈ L.Q t, w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F) := by
  intro w hw
  unfold locPl at hw
  rcases Finset.mem_union.1 hw with h | h
  · left
    unfold Places.W0 at h
    obtain ⟨v, hv, rfl⟩ := by simpa only [Finset.mem_image] using h
    rw [G.pl.under_w hv]
    exact hv
  · exact Or.inr ⟨w, h, rfl⟩

theorem exists_rowData {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} (W : G.Weil)
    {μ₀ : T} (hL : L.Is μ₀) (ρ : RealMatch W) (t : T) (e : AE D) (he : IsIdemSum e (locPl G t))
    (F : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ) (fr : SchRow G)
    (hfr : ∀ i : Fin D.R.m, IsLocVec W (.chi i D.R.m) e (ρ.vX i D.R.m) (F i) (fr i)) :
    ∃ (dr : ∀ i : Fin D.R.m, FinDatum G t (.chi i D.R.m))
      (cr : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) →₀ ℂ),
      (∀ i, (dr i).e = e ∧ IsCombOf W (dr i) (cr i)) ∧ (∀ i, comb W.ψ _ _ (cr i) (ρ.vX i D.R.m) = fr i) ∧
        ∀ i, (dr i).fn = F i := by
  let dr : ∀ i : Fin D.R.m, FinDatum G t (.chi i D.R.m) := fun i =>
    { FinDatum.ind G t (.chi i D.R.m) (locPl G t) (locPl_under G t) e he with fn := F i, sb := (hfr i).1 }
  let d : PureDat G t := (fun j => FinDatum.vacuum G t (.top t j), dr)
  obtain ⟨c, hc⟩ := GlobalTheory.CombsExist.exists_isCombs W hL (Finsupp.single d 1)
  have hc' := (hc d (by simp)).2
  refine ⟨dr, fun i => (c d).2 i, fun i => ⟨rfl, hc' i⟩, fun i => ?_, fun i => rfl⟩
  have hv := ρ.vX_is i D.R.m i.2 le_rfl
  obtain ⟨⟨Tm, hTm⟩, h1⟩ := (hc' i).2.2 (ρ.vX i D.R.m) hv.2.theta hv.2.lat
  exact (h1 Tm hTm).trans ((hfr i).2.2 Tm hTm).symm

theorem rowData : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (e : AE D), IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)) (fr : SchRow ch.G), (∀ i : Fin D.R.m, IsLocVec ch.W (.chi i D.R.m) e (ch.rm.vX i D.R.m) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fr i)) → ∃ (dr : ∀ i : Fin D.R.m, FinDatum ch.G t (.chi i D.R.m)) (cr : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T)) →₀ ℂ), (∀ i, (dr i).e = e ∧ IsCombOf ch.W (dr i) (cr i)) ∧ (∀ i, comb ch.W.ψ _ _ (cr i) (ch.rm.vX i D.R.m) = fr i) ∧ ∀ i y, IsHalf e y → (dr i).fn y = ∏ w : locPl ch.G t, φ w (.ex i D.R.m) (ch.S.B.coord t w.1 (X := (i, D.R.m)) (Y := (i + 1, D.R.m)) ⟨i.2.le, le_rfl⟩ ⟨i.2, le_rfl⟩ (y.map fun a => cpt w.1 (toEAf D a))) := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ => ?_⟩⟩
  intro t e he φ fr hfr
  obtain ⟨dr, cr, h1, h2, h3⟩ := exists_rowData ch.W s.core.lev ch.rm t e he _ fr hfr
  exact ⟨dr, cr, h1, h2, fun i y hy => by simp only [h3 i, hy, ↓reduceIte]⟩

end GlobalTheory.RowSingle
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestTupleTermMeasuresDifferByScalars
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped NNReal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section
namespace GlobalTheory.TermScales

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem finE_toFin' (V : HSp D) (g : GA D V) : Lev.finE V (GlobalTheory.AutMult.toFin V g : GA D V) = Lev.finE V g := by
  conv_rhs => rw [← GlobalTheory.AutMult.toInf_mul_toFin g]
  have hx : Lev.finE V (GlobalTheory.AutMult.toInf V g : GA D V) = 1 := by
    simp only [Lev.finE, MonoidHom.comp_apply]
    rw [show finHom V (GlobalTheory.AutMult.toInf V g : GA D V) = 1 from (GlobalTheory.AutMult.toInf V g).2, map_one]
  rw [map_mul, hx, one_mul]

theorem isAt_congr (M : Vol G) (X : Node) {K K' : Subgroup (GL (Fin (G.V X).rank) (Lev.EAf D))}
    (hK : ∀ k : FinPt G X, finG (G.V X) k ∈ K ↔ finG (G.V X) k ∈ K') (h : M.IsAt X K) : M.IsAt X K' := by
  have hK' : ∀ g : GA D (G.V X), Lev.finE (G.V X) g ∈ K ↔ Lev.finE (G.V X) g ∈ K' := by
    intro g
    rw [← finE_toFin' (G.V X) g]
    exact hK (GlobalTheory.AutMult.toFin (G.V X) g)
  unfold Vol.IsAt at h ⊢
  split_ifs at h ⊢
  · simpa only [IsMeasDef, Lev.IsMeasLevDef, Lev.IsMeasLevW, hK'] using h
  · simpa only [Lev.IsMeasFD, Lev.IsMeasLev, Lev.IsMeasLevW, hK'] using h

theorem isHaar_of_isAt (M : Vol G) (X : Node) {K : Subgroup (GL (Fin (G.V X).rank) (Lev.EAf D))} (h : M.IsAt X K) :
    (M.ν X).IsHaarMeasure := by
  unfold Vol.IsAt at h
  split_ifs at h
  · exact h.1.1
  · exact h.1.1

end GlobalTheory.TermScales


open GlobalTheory.TermScales in
theorem GlobalTheory.TermScales.exists_scales : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t Φ β (M M' : Vol ch.G), M.Is t → IsTermVol t ch.S.toGridChoice Φ β M' →
    ∃ x : Node → ℝ≥0, Scales M M' x ∧
      ∀ X : Node, DefNode D.R.m X → X ≠ .top D.R.m → (∀ j ∈ idx D, X ≠ .top j) → x X = 1 := by
  refine big_mono ?_ (Big.and _root_.GlobalTheory.RowLevelUnit.levRow_iff_levJ _root_.GlobalTheory.LastLevUnit.levTop_iff_levJ)
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch hch
  obtain ⟨hrow, htop⟩ := hch
  intro t Φ β M M' hM hM'
  have hdef : ∀ X : Node, DefNode D.R.m X → X ≠ .top D.R.m → Node.InRange D.R.m X := by
    intro X hX _
    rcases X with ⟨i, j⟩ | i | j
    · exact ⟨hX.1, hX.2.le⟩
    · exact hX.elim
    · exact hX
  have hM'at : ∀ X : Node, DefNode D.R.m X → X ≠ .top D.R.m → ∃ K, M'.IsAt X K := by
    intro X hX hne
    rcases X with ⟨i, j⟩ | i | j
    · obtain ⟨hi, rfl⟩ := hX
      exact ⟨_, hM'.2 i hi⟩
    · exact hX.elim
    · have hj : j < D.R.m := lt_of_le_of_ne hX (fun e => hne (by rw [e]))
      exact ⟨_, hM'.1 j hj⟩
  have key : ∀ X : Node, ∃ c : ℝ≥0, (DefNode D.R.m X → X ≠ .top D.R.m → M.ν X = c • M'.ν X) ∧
      (DefNode D.R.m X → X ≠ .top D.R.m → (∀ j ∈ idx D, X ≠ .top j) → c = 1) := by
    intro X
    by_cases hX : DefNode D.R.m X ∧ X ≠ .top D.R.m ∧ ∀ j ∈ idx D, X ≠ .top j
    · obtain ⟨hd, hne, hidx⟩ := hX
      refine ⟨1, fun _ _ => ?_, fun _ _ _ => rfl⟩
      rw [one_smul]
      have hMX := hM.vtx X (hdef X hd hne)
      rcases X with ⟨i, j⟩ | i | j
      · obtain ⟨hi, rfl⟩ := hd
        exact GlobalTheory.HaarNorm.vol_nu_eq_of_isAt M M' _ _ hMX (isAt_congr M' _ (hrow t i hi) (hM'.2 i hi))
      · exact hd.elim
      · have hj : j < D.R.m := lt_of_le_of_ne hd (fun e => hne (by rw [e]))
        have hj' : j ∉ idx D := fun hm => hidx j hm rfl
        simp only [idx, List.mem_range'_1] at hj'
        rcases Nat.eq_zero_or_pos j with rfl | hpos
        · exact GlobalTheory.HaarNorm.vol_nu_eq_of_isAt M M' _ _ hMX (hM'.1 0 hj)
        · have e : j = D.R.m - 1 := by omega
          have h2 : 2 ≤ D.R.m := by omega
          subst e
          exact GlobalTheory.HaarNorm.vol_nu_eq_of_isAt M M' _ _ hMX (isAt_congr M' _ (htop t Φ β hj h2) (hM'.1 _ hj))
    · by_cases hX' : DefNode D.R.m X ∧ X ≠ .top D.R.m
      · obtain ⟨hd, hne⟩ := hX'
        obtain ⟨i1, i2, i3, i4, i5, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (ch.G.V X)
        obtain ⟨K', hK'⟩ := hM'at X hd hne
        haveI := isHaar_of_isAt M X (hM.vtx X (hdef X hd hne))
        haveI := isHaar_of_isAt M' X hK'
        exact ⟨Measure.haarScalarFactor (M.ν X) (M'.ν X), fun _ _ => Measure.isMulLeftInvariant_eq_smul _ _,
          fun h1 h2 h3 => (hX ⟨h1, h2, h3⟩).elim⟩
      · exact ⟨1, fun h1 h2 => (hX' ⟨h1, h2⟩).elim, fun h1 h2 _ => (hX' ⟨h1, h2⟩).elim⟩
  choose x hx using key
  exact ⟨x, fun X h1 h2 => (hx X).1 h1 h2, fun X h1 h2 h3 => (hx X).2 h1 h2 h3⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StaircaseLatticeIsotropicLineIdealIffStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.staircase_lattice_isotropic_line_ideal_iff : OnStd fun {D} _ _ {sc} {G} _ F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m) (v : GlobalTheory.FinPl.Pl D) (i : Fin ρ), ∀ a ∈ idAt D (· = v), GlobalTheory.FinPl.colMul (F.dJ ρ h).jX i a ∈ latV _ (G.Λ (.grid (2 * ρ + 1) 0)) (· = v) ↔ a ∈ GlobalTheory.SeeSaw.idV (FractionalIdeal.spanSingleton _ ((-D.host.xi0) ^ (i.1 + 1))⁻¹ * (G.pl.stA sc ^ (2 * ρ - i.1) * (G.pl.stAbar sc ^ (i.1 + 1))⁻¹)) v := by
  first | exact @GlobalTheory.StairLine.colMul_dJ_mem_iff | exact GlobalTheory.StairLine.colMul_dJ_mem_iff | (intros; apply GlobalTheory.StairLine.colMul_dJ_mem_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StarAdjointMemHatLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.LineDepthZero

set_option maxHeartbeats 1000000

theorem smul_mem_hatMx_of_mem_latO {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {S B : HSp D}
    (LS : Lat S) (Λ₀ : Lat B) (hS : IsSelfDualC S LS)
    (hv : ∀ w ∈ G.pl.W0, ∀ b ∈ D.host.AA * shiftId G,
      Valued.v (algebraMap D.host.E (Kw w) b) ≤ WithZero.exp (-(cosExp G w : ℤ)))
    (e : AE D) (he : IsIdemSum e G.pl.W0) :
    ∀ z ∈ latO S B (LS : Set _) (idLat (shiftId G) Λ₀ : Set _) (fun _ => True),
      e • z ∈ hatMx (G.modul • homLat LS Λ₀) := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    have key : ∀ t ∈ idLat (shiftId G) Λ₀, ∀ a ∈ D.host.AA,
        e • (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S B) ∈
          hatMx (G.modul • homLat LS Λ₀) := by
      intro t ht
      induction ht using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨j, hj, y, hy, rfl⟩ := hx
        intro a ha
        have h1 := _root_.GlobalTheory.HalfScalarHat.idemSum_smul_mem_hatMx G (homLat LS Λ₀) e he α hα (a * j)
          (fun w hw => hv w hw _ (FractionalIdeal.mul_mem_mul ha hj)) _
          (GlobalTheory.RowLatChi.genMap_one_mem_homLat hS hs hy)
        convert h1 using 3
        ext i k
        simp only [Matrix.of_apply, GlobalTheory.LatVac.genMap, Pi.smul_apply, smul_eq_mul]
        ring_nf
      | zero =>
        intro a ha
        have e0 : (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F]
            (a * (0 : Fin B.rank → D.host.E) i * ∑ k, star (s k) * S.gram k j) : WO S B) = 0 := by
          ext i j; simp
        rw [e0, smul_zero]; exact zero_mem _
      | add x y _ _ hx hy =>
        intro a ha
        have e0 : (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F]
            (a * (x + y) i * ∑ k, star (s k) * S.gram k j) : WO S B) =
            (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * x i * ∑ k, star (s k) * S.gram k j)) +
            (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * y i * ∑ k, star (s k) * S.gram k j)) := by
          ext i j
          simp only [Matrix.of_apply, Matrix.add_apply, Pi.add_apply, mul_add, add_mul, TensorProduct.tmul_add]
        rw [e0, smul_add]; exact add_mem (hx a ha) (hy a ha)
      | smul o x _ hx =>
        intro a ha
        have ha' : a * algebraMap (𝓞 D.host.E) D.host.E o ∈ D.host.AA := by
          rw [mul_comm, ← Algebra.smul_def]; exact Submodule.smul_mem _ o ha
        convert hx _ ha' using 4
        ext i j
        simp only [Matrix.of_apply, Pi.smul_apply, Algebra.smul_def]
        ring_nf
    exact key t ht a ha
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

end GlobalTheory.LineDepthZero


open GlobalTheory.LineDepthZero in
theorem GlobalTheory.AscFin.BoxBF.lineAdj_zero_dep : OnStd fun {D} _ _ {sc} {G} W F => ∀ (h : 2 * 0 + 2 ≤ D.R.m), ∀ u ∈ (pcBF W F 0 h).Γ₀, ∀ e : AE D, IsIdemSum e G.pl.W0 → e • (incA D D.host.xi0⁻¹ • GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj _ _ (((F.oB 0 h).resS (G.V (.core (2 * 0 + 1))) u).2)) ∈ hatMx (G.modul • homLat (G.Λ (.core (2 * 0 + 1))) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) := by
  intro D hD T L μ0 hL sc G W Mv hM F hF h u hu e he
  have hx := _root_.GlobalTheory.AscFin.BoxBF.lineComp_mem_latO D hD T L μ0 hL sc G W Mv hM F hF 0 h u hu
  have hy := GlobalTheory.AdjLatO.incA_inv_xi0_smul_starAdj_mem_latO D (negSp F.Lz) (G.V (.core (2 * 0 + 1))) _
    (idLat (shiftId G) (Submodule.span (𝓞 D.host.E) {F.ζ 0})) (G.Λ (.core (2 * 0 + 1))) (fun _ => True)
    (_root_.GlobalTheory.AdjSrcZero.star_smul_mem_span G _) _ hx
  have sdC : IsSelfDualC (G.V (.core (2 * 0 + 1))) (G.Λ (.core (2 * 0 + 1))) := (G.sp.P_is (2 * 0 + 1) (by omega)).sd
  exact smul_mem_hatMx_of_mem_latO G _ _ sdC (_root_.GlobalTheory.AscFin.ShiftVal.val_le_cosExp hD μ0 hL G) e he _ hy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaContractionLinearLeftLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ConnectionLinear

section Helpers
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem contr_comb_left (hψ : IsStdChar D ψ (-1)) {ρ σ : ℕ} {B : Unf.BesLev D ρ} {B' : Unf.BesLev D σ}
    (l : Unf.Link B B'.L B'.ζ) (S : HSp D) (vL : Unf.VolM D B'.L.rank S.rank) (c : ℂ) {X Y : WO B.V₀ S → ℂ}
    {Z : WO S B'.V₀ → ℂ} (hX : IsThetaFunO ψ B.V₀ S X) (hY : IsThetaFunO ψ B.V₀ S Y) (hZ : IsThetaFunO ψ S B'.V₀ Z)
    (u : WO B.A S) (v : WO S B'.A) :
    Unf.contr l S vL (c • X + Y) Z u v = c * Unf.contr l S vL X Z u v + Unf.contr l S vL Y Z u v := by
  have i1 := GlobalTheory.ContractionLocal.integrable_contr hψ l S vL hX hZ u v
  have i2 := GlobalTheory.ContractionLocal.integrable_contr hψ l S vL hY hZ u v
  unfold GlobalTheory.Unf.contr
  rw [← integral_const_mul, ← integral_add (i1.const_mul c) i2]
  congr 1
  funext w
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem contr_flatBF_smul_add (hψ : IsStdChar D ψ (-1)) {ρ σ : ℕ} {B : Unf.BesLev D ρ} {J : Unf.JacLev D ρ}
    {B' : Unf.BesLev D σ} (s : Unf.StepBF ψ B J) (l : Unf.Link B B'.L B'.ζ) (vL : Unf.VolM D B'.L.rank J.W₀.rank)
    (c : ℂ) {X Y : WO B.V J.W → ℂ} {Z : WO J.W₀ B'.V₀ → ℂ} (hX : IsThetaFunO ψ B.V J.W X)
    (hY : IsThetaFunO ψ B.V J.W Y) (hZ : IsThetaFunO ψ J.W₀ B'.V₀ Z) (u : WO B.A J.W₀) (v : WO J.W₀ B'.A) :
    Unf.contr l J.W₀ vL (Unf.flatBF s (c • X + Y)) Z u v =
      c * Unf.contr l J.W₀ vL (Unf.flatBF s X) Z u v + Unf.contr l J.W₀ vL (Unf.flatBF s Y) Z u v := by
  have hF := GlobalTheory.Unf.Flat.flatLaw D
  have fX := (_root_.GlobalTheory.Unf.FlatTheta.flat_isThetaFun D hF ψ).1 ρ B J s X hX
  have fY := (_root_.GlobalTheory.Unf.FlatTheta.flat_isThetaFun D hF ψ).1 ρ B J s Y hY
  have hcX := GlobalTheory.OrientedHeis.theta_smul c hX
  rw [(GlobalTheory.FlatLin.flatBF_linear D hF ψ ρ B J s (c • X) Y c hcX hY).1,
    (GlobalTheory.FlatLin.flatBF_linear D hF ψ ρ B J s X Y c hX hY).2]
  exact contr_comb_left hψ l J.W₀ vL c fX fY hZ u v

end Helpers

section Grid
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem fock_comb (W : G.Weil) (p : Pair T) (c : ℂ) {f g : WO (G.pS p) (G.pT p) → ℂ} (hf : IsThetaFunO W.ψ _ _ f)
    (hg : IsThetaFunO W.ψ _ _ g) (Q : PolF D (G.pT p).rank (G.pS p).rank) :
    W.fock p (c • f + g) Q = c • W.fock p f Q + W.fock p g Q := by
  unfold GridData.Weil.fock
  exact GlobalTheory.FockFiniteHeis.pureTensorO_lin W.ψ W.θ _ _ W.ψ_std W.θ_is _ _ _ _ c hf hg Q

theorem fock_theta (W : G.Weil) (p : Pair T) {f : WO (G.pS p) (G.pT p) → ℂ} (hf : IsThetaFunO W.ψ _ _ f)
    (Q : PolF D (G.pT p).rank (G.pS p).rank) : IsThetaFunO W.ψ _ _ (W.fock p f Q) := by
  unfold GridData.Weil.fock
  exact GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ hf Q

end Grid

theorem contrLin_left : Big fun ch => ContrLin ch 0 := by

  refine ⟨0, fun ε CF _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _
  intro j hj hjm hm t M hM P h Φ a ha φ φ' c hΦ hφ hφ' u v
  obtain ⟨a, ha'⟩ := a
  simp only [add_zero] at ha
  subst ha

  have h1 : ¬ (a + 2 * 0 + 2 = D.R.m) := by omega
  have h2 : a + 2 * ((D.R.m - 4 - a) / 2 + 1) + 2 = D.R.m := by
    obtain ⟨k, hk⟩ := hj
    obtain ⟨n, hn⟩ := hm
    omega
  have hin : (Pair.mu t D.R.m a : Pair T).InRange D.R.m := show D.R.m ≤ D.R.m ∧ a + 1 ≤ D.R.m from ⟨le_rfl, by omega⟩
  have hin' : (Pair.mu t D.R.m (a + 1) : Pair T).InRange D.R.m :=
    show D.R.m ≤ D.R.m ∧ a + 1 + 1 ≤ D.R.m from ⟨le_rfl, by omega⟩
  simp only [conAt, dif_neg h1, fockD]
  simp (disch := simp) only [Function.update_self, Function.update_of_ne]
  simp only [h2, ↓reduceDIte]
  · rw [fock_comb ch.W (Pair.mu t D.R.m a) c hφ hφ' (P ⟨a, ha'⟩), map_add (f := _), map_smul]
    refine contr_flatBF_smul_add ch.W.ψ_std (B := besAt ch.G hM a ((D.R.m - 4 - a) / 2 + 1) h2 _)
      (J := jacAt ch.G hM (a + 1) ((D.R.m - 4 - a) / 2 + 1) (by omega)) _ _ _ c ?_ ?_ ?_ _ _
    · exact (ch.W.om_is _ hin).om_pres _ _ (fock_theta ch.W _ hφ _)
    · exact (ch.W.om_is _ hin).om_pres _ _ (fock_theta ch.W _ hφ' _)
    · exact (_root_.GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (GlobalTheory.Unf.Flat.flatLaw D) _).2 _ _ _ _ _
        ((ch.W.om_is _ hin').om_pres _ _ (fock_theta ch.W _ (hΦ ⟨a + 1, by omega⟩) _))

end GlobalTheory.ConnectionLinear
end
end

