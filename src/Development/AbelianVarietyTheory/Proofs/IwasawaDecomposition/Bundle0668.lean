module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0589
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0573
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0498
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
public import Formalism.DegreeFormula.Statement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0651
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0598
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0664
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0652
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0002
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0450
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftSchurMultiplierCompatibility
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1619
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnramifiedHeckeCharHalfExponentRestrictQua
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitHeckeRowsEqDoubleCosetOperators
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainCompositeLiftIntertwinesFiniteGroupActions
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorSmallestSpaceForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricPointClassFormMassEqCovolume
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open MeasureTheory Formalism.DegreeFormula GlobalTheory.TrueCx

namespace GlobalTheory.BaseVolume

theorem mass_openPart_eq_covol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → chernTopPart Eb (lieGram e U hj f₀ A₀) (pointPoly H Dw) 1 (ptsIn X.str (σ.comp e.toRingHom) (openPart j)) = ENNReal.ofReal (GlobalTheory.TrueCx.covol (U.X k)) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hg hU Φ k X j f f₀ Eb A₀ hj hL
  have hj' : Dw.p ≤ Dw.p + Dw.q := Nat.le_add_right _ _
  have hp : (U.X k).p0 = Dw.p + Dw.q - Dw.p := by have := (hU.2.1 k).1; omega
  obtain ⟨ψ, hψ⟩ := _root_.GlobalTheory.LieBase.UnifExists.exists_unif E H Dw l Xo c O β Y T F e σ U hg hU Φ k X j f f₀ Eb A₀ hj hL
  have himg := _root_.GlobalTheory.UnifImage.image_domFlat_eq_ptsIn_openPart E H Dw l Xo c O β Y T F e σ U hg hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  have hfib := _root_.GlobalTheory.UnifFibre.fibre_gamma E H Dw l Xo c O β Y T F e σ U hg hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  have hinv := _root_.GlobalTheory.UnfInv.psi_moebI_eq E H Dw l Xo c O β Y T F e σ U hg hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  have hdens := _root_.GlobalTheory.UnifDens.chernTopPart_image E H Dw l Xo c O β Y T F e σ U hg hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  have hnull := _root_.GlobalTheory.UnifNull.image_null E H Dw l Xo c O β Y T F e σ U hg hU Φ k X j f f₀ Eb A₀ hj hL ψ hψ
  obtain ⟨FD, hFD⟩ := GlobalTheory.BoundedFundDomain.exists_isFD E (Dw.p + Dw.q) Dw.p (U.X k) hj' (U.X k).Ψ (Equiv.refl _) hp
  obtain ⟨hlt, hcov⟩ := GlobalTheory.FlagFibre.covol_eq_muD E (Dw.p + Dw.q) Dw.p (U.X k) hj' (U.X k).Ψ (Equiv.refl _) hp FD hFD
  obtain ⟨hFm, hFsub, hFcov, hFbad⟩ := hFD
  set μD := muD (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) with hμD
  set Bad := {v | v ∈ FD ∧ ∃ γ ∈ gammaU (U.X k) hj' (Equiv.refl (U.X k).Ψ), flat (moebI γ (unflat v)) ∈ FD ∧
    moebI γ (unflat v) ≠ unflat v} with hBad
  set B' := toMeasurable μD Bad with hB'
  have hB'0 : μD B' = 0 := by rw [hB', measure_toMeasurable]; exact hFbad
  have hfu : ∀ v : (U.X k).Ψ × Fin Dw.p × Fin (Dw.p + Dw.q - Dw.p) → ℂ, flat (unflat v) = v := fun v => rfl
  have hinj : Set.InjOn ψ (FD \ B') := by
    intro v hv w hw hvw
    obtain ⟨γ, hγ, hγe⟩ := hfib v (hFsub hv.1) w (hFsub hw.1) hvw
    have hnb : v ∉ Bad := fun h => hv.2 (subset_toMeasurable _ _ h)
    have h1 : moebI γ (unflat v) = unflat v := by
      by_contra hne
      exact hnb ⟨hv.1, γ, hγ, by rw [hγe, hfu]; exact hw.1, hne⟩
    rw [← hfu v, ← hfu w, ← hγe, h1]
  have hD := hdens (FD \ B') (Set.diff_subset.trans hFsub) (hFm.diff (measurableSet_toMeasurable _ _)) hinj
  have hN := hnull (FD ∩ B') (Set.inter_subset_left.trans hFsub) (measure_mono_null Set.inter_subset_right hB'0)
  have hmF : μD (FD \ B') = μD FD := measure_diff_null hB'0
  have hsub : ψ '' DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) ⊆ ψ '' (FD \ B') ∪ ψ '' (FD ∩ B') := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨γ, hγ, hγF⟩ := hFcov (unflat v) hv
    rw [← Set.image_union, Set.diff_union_inter, ← hinv γ hγ v hv]
    exact Set.mem_image_of_mem _ hγF
  have hsup : ψ '' (FD \ B') ⊆ ψ '' DomFlat (U.X k).Ψ Dw.p (Dw.p + Dw.q - Dw.p) :=
    Set.image_mono (Set.diff_subset.trans hFsub)
  rw [← himg, hcov, ENNReal.ofReal_mul' ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hlt.ne, ← hmF, ← hD]
  refine le_antisymm ?_ (measure_mono hsup)
  calc _ ≤ _ := measure_mono hsub
    _ ≤ _ := measure_union_le _ _
    _ = _ := by rw [hN, add_zero]

end GlobalTheory.BaseVolume
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsAtAndSeedFacts
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeCharacterRestriction

variable {D : D7}

section Chars

variable {T : Type} {L : LevCh D T} {μ0 : T}

theorem isHecke_mu (hL : L.Is μ0) (t : T) (j : Fin D.R.m) : IsHeckeChar D (L.mu t ((j : ℕ) + 1)) :=
  ⟨(hL.mu0 j).1.1.mul (hL.xi t).1.1, fun x =>
    (congrArg₂ (· * ·) ((hL.mu0 j).1.2 x) ((hL.xi t).1.2 x)).trans (mul_one _)⟩

theorem resEta_mu (hL : L.Is μ0) (t : T) (j : Fin D.R.m) : ResEta D (L.mu t ((j : ℕ) + 1)) 0 := by
  have hres := GlobalTheory.Mem.EtaTilde.isEta_res D L.eta L.C.eta hL.eta L.C.isEta
  refine ⟨⟨_, hres⟩, fun η _ a => ?_⟩
  show L.mu0 ((j : ℕ) + 1) (idF D a) * L.xi t (idF D a) = _
  rw [pow_zero, GlobalTheory.GridWeil.triv_base (hL.mu0 j) (L.C.isMu0 j).triv a, GlobalTheory.GridWeil.triv_base (hL.xi t) (hL.xi_triv t) a, mul_one]

theorem resEta_eta (hL : L.Is μ0) : ResEta D L.eta 1 := by
  have hres := GlobalTheory.Mem.EtaTilde.isEta_res D L.eta L.C.eta hL.eta L.C.isEta
  refine ⟨⟨_, hres⟩, fun η h a => ?_⟩
  rw [(GlobalTheory.IdeleNormChar.existsUnique_isEta D).unique h hres, pow_one, MonoidHom.comp_apply]

theorem isHecke_quot (hL : L.Is μ0) (t : T) (j : Fin D.R.m) : IsHeckeChar D (L.mu t ((j : ℕ) + 1) * L.eta⁻¹) :=
  ⟨(isHecke_mu hL t j).1.mul (hL.eta.1.1.inv), fun x => by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, (isHecke_mu hL t j).2, hL.eta.1.2, inv_one, mul_one]⟩

theorem resEta_quot (hL : L.Is μ0) (t : T) (j : Fin D.R.m) {n : ℕ} (hn : Odd n) :
    ResEta D (L.mu t ((j : ℕ) + 1) * L.eta⁻¹) n :=
  resEta_parity (resEta_mul (resEta_mu hL t j) (resEta_inv (resEta_eta hL)))
    (by obtain ⟨c, rfl⟩ := hn; omega)

theorem resEta_even (hL : L.Is μ0) (t : T) (j : Fin D.R.m) {n : ℕ} (hn : Even n) :
    ResEta D (L.mu t ((j : ℕ) + 1)) n :=
  resEta_parity (resEta_mu hL t j) (by obtain ⟨c, rfl⟩ := hn; omega)

theorem odd_r : Odd D.R.r := by
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have := D.R.two_le_m
  refine ⟨a + b - 1, ?_⟩
  unfold Ranks.r
  omega

theorem even_rankY (j : ℕ) : Even (D.R.rankY j) ↔ ¬ Even j := by
  have h1 : ¬ Even D.R.r := Nat.not_even_iff_odd.2 odd_r
  have h2 : ¬ Even D.R.t := Nat.not_even_iff_odd.2 D.R.t_odd
  unfold Ranks.rankY
  rw [Nat.even_add, Nat.even_mul]
  tauto

theorem rank_Yc {k : ℕ} (h : k ≤ D.R.m) : (Yc D k).rank = D.R.rankY k := by
  show (D.sp.Y (min k D.R.m)).rank = _
  rw [min_eq_left h]
  exact D.sp.Y_rank k h

theorem step_facts (hL : L.Is μ0) (t : T) (j : Fin D.R.m) {a b : ℕ} (ha : Even a ↔ ¬ Even (j : ℕ)) (hb : Even b ↔ Even (j : ℕ)) :
    IsHeckeChar D (Lift.chrStep (L.mu t) L.eta ((j : ℕ) + 1)).1 ∧ IsHeckeChar D (Lift.chrStep (L.mu t) L.eta ((j : ℕ) + 1)).2 ∧
      ResEta D (Lift.chrStep (L.mu t) L.eta ((j : ℕ) + 1)).1 a ∧ ResEta D (Lift.chrStep (L.mu t) L.eta ((j : ℕ) + 1)).2 b := by
  unfold Lift.chrStep
  by_cases h : Even (j : ℕ)
  · rw [if_pos h.add_one]
    exact ⟨isHecke_quot hL t j, isHecke_mu hL t j,
      resEta_quot hL t j (Nat.not_even_iff_odd.1 fun e => ha.1 e h), resEta_even hL t j (hb.2 h)⟩
  · rw [if_neg (fun e => h (by simpa [Nat.odd_add_one] using e))]
    exact ⟨isHecke_mu hL t j, isHecke_quot hL t j, resEta_even hL t j (ha.2 h),
      resEta_quot hL t j (Nat.not_even_iff_odd.1 fun e => h (hb.1 e))⟩

theorem splitFacts (hL : L.Is μ0) (t : T) :
    (∀ k, k + 1 < D.R.m → IsHeckeChar D (Lift.chrStep (L.mu t) L.eta (k + 1)).1 ∧
      IsHeckeChar D (Lift.chrStep (L.mu t) L.eta (k + 1)).2 ∧
      ResEta D (Lift.chrStep (L.mu t) L.eta (k + 1)).1 (Yc D k).rank ∧
      ResEta D (Lift.chrStep (L.mu t) L.eta (k + 1)).2 (Yc D (k + 1)).rank) ∧
    (IsHeckeChar D (Lift.chrStep (L.mu t) L.eta D.R.m).1 ∧ IsHeckeChar D (Lift.chrStep (L.mu t) L.eta D.R.m).2 ∧
      ResEta D (Lift.chrStep (L.mu t) L.eta D.R.m).1 (Yc D (D.R.m - 1)).rank ∧
      ResEta D (Lift.chrStep (L.mu t) L.eta D.R.m).2 D.sp.X'.rank) ∧
    ∀ i : Fin D.R.m, IsHeckeChar D (Lift.chrTh (L.mu t) L.eta ((i : ℕ) + 1)).1 ∧
      IsHeckeChar D (Lift.chrTh (L.mu t) L.eta ((i : ℕ) + 1)).2 ∧
      ResEta D (Lift.chrTh (L.mu t) L.eta ((i : ℕ) + 1)).1 (Vc D i).rank ∧
      ResEta D (Lift.chrTh (L.mu t) L.eta ((i : ℕ) + 1)).2 (Wc D i).rank := by
  have hm2 := D.R.two_le_m
  refine ⟨fun k hk => ?_, ?_, fun i => ?_⟩
  · refine step_facts hL t ⟨k, by omega⟩ (a := (Yc D k).rank) (b := (Yc D (k + 1)).rank) ?_ ?_
    · rw [rank_Yc (by omega)]; exact even_rankY k
    · rw [rank_Yc (by omega), even_rankY]
      show _ ↔ Even k
      rw [Nat.even_add_one, not_not]
  · have hj : D.R.m - 1 < D.R.m := by omega
    have e : D.R.m - 1 + 1 = D.R.m := by omega
    have hne : ¬ Even (D.R.m - 1) := fun h => by
      have := h.add_one
      rw [e] at this
      exact (Nat.not_odd_iff_even.2 D.R.m_even) this
    have key := step_facts hL t ⟨D.R.m - 1, hj⟩ (a := (Yc D (D.R.m - 1)).rank) (b := D.sp.X'.rank)
      (by rw [rank_Yc (by omega)]; exact even_rankY _)
      (by
        rw [D.sp.X'_rank]
        show Even (D.R.rankY D.R.m) ↔ Even (D.R.m - 1)
        rw [even_rankY]
        exact iff_of_false (not_not.2 D.R.m_even) hne)
    simpa only [e] using key
  · have hV : (Vc D i).rank = D.R.nV := D.sp.V_rank _ (by omega) (by omega)
    have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (by omega) (by omega)
    refine ⟨isHecke_mu hL t i, isHecke_quot hL t i, resEta_even hL t i ?_, resEta_quot hL t i ?_⟩
    · rw [hV]
      exact odd_r.add_odd D.R.t_odd
    · rw [hW]
      exact odd_r

end Chars

section Places

variable {T : Type} {L : LevCh D T} {μ0 : T}

theorem not_isConjPl_union (hL : L.Is μ0) (t : T) {P P' : Pl D.host.E} (h : P ∈ L.Pg ∨ P ∈ L.Q t)
    (h' : P' ∈ L.Pg ∨ P' ∈ L.Q t) : ¬ Lev.IsConjPl P P' := by
  rcases h with h | h
  · exact (GlobalTheory.ChainEquiv.places_sep L μ0 hL t).1 P h P' h'
  · rcases h' with h' | h'
    · intro hc
      obtain ⟨⟨q, hq, hcard, -, hne⟩, -⟩ := hL.Q_pl t P h
      obtain ⟨k, hk⟩ := (hL.Pg P').1 h'
      have h1 : (q : 𝓞 D.host.E) ∈ P.asIdeal := by
        have hzero : Nat.card (kP P) • (1 : kP P) = 0 := card_nsmul_eq_zero'
        rw [hcard, nsmul_one] at hzero
        exact Ideal.Quotient.eq_zero_iff_mem.1 ((map_natCast _ q).trans hzero)
      exact hne k (GlobalTheory.ChainEquiv.eq_of_natCast_mem P' hq (D.host.g_prime k)
        (GlobalTheory.ChainEquiv.natCast_mem_of_isConjPl hc h1) (L.C.P.overP hk))
    · exact (hL.Q_pl t P h).2 P' h'

end Places

theorem liftsAt_and_seedFacts : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type)
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (F : Face D A), LiftsAt D A Ks F ∧ SeedFacts D A Ks F := by
  intro D G _ _ Pl0 T A Ks _ _ _ F
  refine ⟨fun R h => ⟨GlobalTheory.LevelRowsObj.liftsExist h.lev, fun i => GlobalTheory.GeoActRoad.levelLiftsExist_gridVertexSpaces h.lev i⟩, fun R h => ⟨?_, ?_⟩⟩
  · exact fun t => splitFacts h.lev t
  · classical
    intro t
    refine ⟨(GlobalTheory.ChainEquiv.places_sep R.toLevCh A.μ0 h.lev t).2, GlobalTheory.CentralShift.exists_idemSum _ fun P hP P' hP' => ?_⟩
    exact not_isConjPl_union h.lev t (Finset.mem_union.1 hP) (Finset.mem_union.1 hP')

end GlobalTheory.HeckeCharacterRestriction
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitHeckeRowsEqDoubleCosetOperatorsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitHecke_rows_eq_doubleCoset_operators : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E)
    (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W),
    cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) →
    Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) →
    ∀ t, ∀ P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ, GlobalTheory.Mem.R3.RowAd.ReadsDeco X I hX Xg tr cX t P →
      Nonempty (Bridge.HeckeTie (Bridge.ratF X.toD7.sp.X') P ((famR X I hX U Xg tr).A.heckeR t) (fun i => 1 ≤ i.2 ∧ i.2 ≤ X.toD7.sp.X'.rank)
        (isTEnv X.toD7.sp.X' (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) ((famR X I hX U Xg tr).A.ok t))
        (isLocEnv X.toD7.sp.X' (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) ((famR X I hX U Xg tr).A.ok t))) := by
  first | exact @GlobalTheory.Mem.R3.RowHk.hecke_tie | exact GlobalTheory.Mem.R3.RowHk.hecke_tie | (intros; apply GlobalTheory.Mem.R3.RowHk.hecke_tie <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevLift
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
noncomputable section

namespace GlobalTheory.Mem.R3.DTheta.StepLevLift

theorem stepLev_lift : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Pins R F cG → Holds R F → ∀ (b : Bool) (t : T) (k : ℕ), k + 1 < D.R.m → ∀ κ ∈ levS (Yc D k) (R.βY k) (R.datYt t k (R.toRealDat.levR F.lv2 b)), ∃ κ' ∈ levS (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)), R.ωY t k (κ, κ') (R.vY t k) = (levChi (Yc D k) (R.βY k) (R.datYt t k (R.toRealDat.levR F.lv2 b)) κ * (levChi (Yc D (k + 1)) (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)) κ')⁻¹) • R.vY t k := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hP hH b t k hk κ hκ
  have hL := hP.char.base.lev
  have hk' : k < D.R.m := Nat.lt_of_succ_lt hk
  obtain ⟨hκ1, hκ2⟩ := hκ
  set g0 : G0 R.Pg D.R.r := rTup (R.βY k) (R.datYt t k R.triv) (finE (Yc D k) κ) with hg0
  have hl : IsLevelLift (Yc D k) (R.βY k) (R.datYt t k R.triv) g0 κ := ⟨hκ1, hκ2.1, rfl⟩
  obtain ⟨κ', hl'⟩ := GlobalTheory.ChainLiftEquiv.liftsExist_chain R.toRealDat hL t (k + 1) hk g0
  have hlaw := GlobalTheory.StepVecLaw.stepVec_lifts R.toRealDat hL hP.char.base.models.inf hP.char.base.chain.ωY
    hP.char.base.chain.vY t k hk g0 κ κ' hl hl'
  have hmem : rTup (R.βY (k + 1)) (R.datYt t (k + 1) R.triv) (finE (Yc D (k + 1)) κ') ∈
      (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)).P.H := by
    rw [hl'.2.2]; exact hκ2.2
  refine ⟨κ', ⟨hl'.1, hl'.2.1, hmem⟩, ?_⟩
  have e1 := levFn_withP (V := Yc D k) (β := R.βY k) (L := R.datYt t k (R.toRealDat.levR F.lv2 b))
    (R.datYt t k (R.toRealDat.levR F.lv2 b)).P (finE (Yc D k) κ)
  have e2 := levFn_withP (V := Yc D (k + 1)) (β := R.βY (k + 1)) (L := R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b))
    (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)).P (finE (Yc D (k + 1)) κ')
  have x1 : ext1 (R.datYt t k (R.toRealDat.levR F.lv2 b)).P.H (R.datYt t k (R.toRealDat.levR F.lv2 b)).P.chi
      (rTup (R.βY k) (R.datYt t k (R.toRealDat.levR F.lv2 b)) (finE (Yc D k) κ)) =
      ext1 (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)).P.H (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)).P.chi
      (rTup (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)) (finE (Yc D (k + 1)) κ')) := by
    have : rTup (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)) (finE (Yc D (k + 1)) κ') = g0 := hl'.2.2
    rw [this]
    rfl
  unfold levChi
  change R.ωY t k (κ, κ') (R.vY t k) = (((Formalism.L2.DIV.levFn (R.βY k) (withP (R.datYt t k (R.toRealDat.levR F.lv2 b)) (R.datYt t k (R.toRealDat.levR F.lv2 b)).P) (finE (Yc D k) κ) : ℂˣ) : ℂ) * ((Formalism.L2.DIV.levFn (R.βY (k + 1)) (withP (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)).P) (finE (Yc D (k + 1)) κ') : ℂˣ) : ℂ)⁻¹) • R.vY t k
  rw [e1, e2, x1]
  unfold levChi at hlaw
  change ((Formalism.L2.DIV.levFn (R.βY k) (flagL (R.datYt t k (R.toRealDat.levR F.lv2 b))) (finE (Yc D k) κ) : ℂˣ) : ℂ)⁻¹ • R.ωY t k (κ, κ') (R.vY t k) = ((Formalism.L2.DIV.levFn (R.βY (k + 1)) (flagL (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b))) (finE (Yc D (k + 1)) κ') : ℂˣ) : ℂ)⁻¹ • R.vY t k at hlaw
  set c := ext1 (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)).P.H (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)).P.chi
      (rTup (R.βY (k + 1)) (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b)) (finE (Yc D (k + 1)) κ'))
  set a := Formalism.L2.DIV.levFn (R.βY k) (flagL (R.datYt t k (R.toRealDat.levR F.lv2 b))) (finE (Yc D k) κ)
  set a' := Formalism.L2.DIV.levFn (R.βY (k + 1)) (flagL (R.datYt t (k + 1) (R.toRealDat.levR F.lv2 b))) (finE (Yc D (k + 1)) κ')
  have ha : ((a : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hc : ((c : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have h3 : R.ωY t k (κ, κ') (R.vY t k) = (((a : ℂˣ) : ℂ) * ((a' : ℂˣ) : ℂ)⁻¹) • R.vY t k := by
    rw [mul_smul, ← hlaw, smul_inv_smul₀ ha]
  rw [h3, Units.val_mul, Units.val_mul]
  congr 1
  field_simp

end GlobalTheory.Mem.R3.DTheta.StepLevLift

end
end

