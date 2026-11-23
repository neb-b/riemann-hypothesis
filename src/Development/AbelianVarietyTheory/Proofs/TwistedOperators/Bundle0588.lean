module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0585
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOrthogonalSumLatticeSameLatticedSpace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0250
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0544
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0668
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOverBoth
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeCoprimeSmallConductor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPermOfCardFalse
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0365
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0407
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0575
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0446
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0460
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0451
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0587
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0586
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0584

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ActEqTranslateLiftV
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RationalFormsAction

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)

theorem isTranslate_act_V (hr : R.grp_red_L) (hj : R.models_jV) (i : Fin D.R.m) (t : T0) (g : G)
    (x : (A.fam.L i t).S.Forms) :
    GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations.IsTranslate (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) ((R.HV i t).e (R.jV i t x))
      ((R.HV i t).e (R.jV i t ((A.fam.L i t).r g x))) := by

  have hred := hr i t
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TranslateRepresentations.IsTranslate
  constructor
  ·
    obtain ⟨q, hq⟩ := (R.B.L i t).act_tie.red_surj g
    have hq' := hred q
    rw [hq] at hq'
    exact ⟨q, hq'.symm⟩
  · intro κ hκ h

    have hg : (R.B.L i t).act_tie.red κ = g := by
      apply R.eG.injective
      rw [hred κ]
      exact hκ

    have key := congrFun ((R.B.L i t).act_tie.act_eq g κ hg x) h
    have e1 := hj i t ((A.fam.L i t).r g x)
    have e2 := hj i t x

    refine (congrFun e1 h).trans (key.trans ?_)
    exact congrArg (fun w => ((((levEnv (Vc D i) (R.βV i) (R.datVt i t)).ch κ)⁻¹ : ℂˣ) : ℂ) • w)
      (congrFun e2 (h * (κ : Bridge.Gf (Vc D i)))).symm

end GlobalTheory.RationalFormsAction

theorem GlobalTheory.RationalFormsAction.act_eq_translate_lift_V : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.grp_red_L → R.models_jV → ∀ i t (g : G) (x : (A.fam.L i t).S.Forms), ∃ κ, IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) (R.eG g) κ ∧ ∀ h, (R.HV i t).e (R.jV i t ((A.fam.L i t).r g x)) h = (levChi _ (R.βV i) (flagL (R.datVt i t)) κ)⁻¹ • (R.HV i t).e (R.jV i t x) (h * (finHom _).rangeRestrict κ) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hr hj i t g x

  have htr := GlobalTheory.RationalFormsAction.isTranslate_act_V R hr hj i t g x
  have hex := GlobalTheory.LiftEquivariance.exists_adelic_lift htr
  exact hex

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AuxiliaryPrimeLtFirstTypePrimeOfSizes
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridJoin

open GlobalTheory.Grid GlobalTheory.ChiGrid

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}

theorem isSpaces_withArr {G : GridPre R} {X ωT vacT ItT ωC vacC ItC dn ItU vC} (h : G.IsSpaces) :
    (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC).IsSpaces := by
  obtain ⟨a, b, c, d, e, f, g⟩ := h
  exact ⟨a, b, c, d, e, f, g⟩

theorem isSpaces_withMeas {G : GridPre R} {m00 mV mP mX} (h : G.IsSpaces) : (withMeas G m00 mV mP mX).IsSpaces := by
  obtain ⟨a, b, c, d, e, f, g⟩ := h
  exact ⟨a, b, c, d, e, f, g⟩

theorem spAgree_withArr {G : GridPre R} {X ωT vacT ItT ωC vacC ItC dn ItU vC} {G' : GridData R.toLevCh sc} {W : G'.Weil}
    (h : SpAgree G W) : SpAgree (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC) W := by
  obtain ⟨a, b, c, d, e, f, g, i, j, k⟩ := h
  exact ⟨a, b, c, d, e, f, g, i, j, k⟩

theorem spAgree_withMeas {G : GridPre R} {m00 mV mP mX} {G' : GridData R.toLevCh sc} {W : G'.Weil} (h : SpAgree G W) :
    SpAgree (withMeas G m00 mV mP mX) W := by
  obtain ⟨a, b, c, d, e, f, g, i, j, k⟩ := h
  exact ⟨a, b, c, d, e, f, g, i, j, k⟩

theorem isChars_withArr {G : GridPre R} {X ωT vacT ItT ωC vacC ItC dn ItU vC} (h : G.IsChars) :
    (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC).IsChars := by
  obtain ⟨a, b, c⟩ := h
  exact ⟨a, b, c⟩

theorem isChars_withMeas {G : GridPre R} {m00 mV mP mX} (h : G.IsChars) : (withMeas G m00 mV mP mX).IsChars := by
  obtain ⟨a, b, c⟩ := h
  exact ⟨a, b, c⟩

theorem isArrows_withMeas {G : GridPre R} {m00 mV mP mX} (h : G.IsArrows) : (withMeas G m00 mV mP mX).IsArrows := by
  obtain ⟨a, b, c, d, e⟩ := h
  exact ⟨a, b, c, d, e⟩

theorem isData_withMeas {G : GridPre R} {m00 mV mP mX} (h : G.IsData) : (withMeas G m00 mV mP mX).IsData :=
  fun i hi c => h i hi c

theorem arrAgree_withMeas {G : GridPre R} {m00 mV mP mX} {G' : GridData R.toLevCh sc} {W : G'.Weil} (h : ArrAgree G W) :
    ArrAgree (withMeas G m00 mV mP mX) W := by
  obtain ⟨a, b, c, d, e, f⟩ := h
  exact ⟨a, b, c, d, e, f⟩

theorem pg_under_inj {F : Face D A} (hR : GlobalTheory.Hk3.Core R F) :
    ∀ PP ∈ R.Pg, ∀ PP' ∈ R.Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') → PP = PP' := by
  intro P hP P' hP' e
  rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq (D := D) e with h | h
  · exact h
  · exact absurd (GlobalTheory.GoodPrimes.isConjPl_iff.2 h) (GlobalTheory.HeckeCharacterRestriction.not_isConjPl_union hR.lev A.μ0 (Or.inl hP') (Or.inl hP))

theorem auxiliaryPrime_splitsCompletely {L : LevCh D T} (P : Places L) : Formalism.L2.Host.SplitsCompletely {P.w P.v0} := by
  intro v hv p hp hpv
  obtain rfl := Finset.mem_singleton.1 hv
  obtain ⟨h1, h2, -⟩ := leastSplitAuxiliaryPrimeThetaChain_spec D
  have hm : q0 D ≡ 1 [MOD D.host.QS * D.host.q * D.host.d] := by
    have : q0 D ≡ 1 [MOD Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D] := by
      rw [← h2]; exact (Nat.mod_modEq _ _).symm
    exact Nat.ModEq.of_mul_left _ this
  have hq : ((q0 D : ℕ) : 𝓞 D.host.E) ∈ (P.w P.v0).asIdeal := by
    have h := P.basePlace_over_qZero
    rw [← P.under_w (P.mem_S0_of_sum_eq.2 (Or.inl rfl))] at h
    rw [← map_natCast (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))]
    exact h
  obtain rfl : p = q0 D := GlobalTheory.GridPlaces.prime_eq_of_mem _ hp h1 hpv hq
  exact (GlobalTheory.SplitChoice.splitsCompletely_of_modEq_one D h1 hm).2

theorem auxiliaryPrime_ne_typePrime {L : LevCh D T} (G' : GridData L sc) (k : Fin 2) : q0 D ≠ D.host.g k := by
  intro e
  apply G'.ch.basePlace_not_mem_chiGridBadPlaces
  have h := G'.pl.basePlace_over_qZero
  rw [e] at h
  rw [S1_mem_OmF]
  fin_cases k
  exacts [Or.inl h, Or.inr (Or.inl h)]

theorem auxiliaryPrime_ne_levelPrimes_of_lt (h : q0 D < D.host.g 0) : q0 D ≠ D.sp.T ∧ ∀ u : D.what₂.Word, q0 D ≠ (D.mem u).A.T :=
  have key : ∀ u : D.what₂.Word, q0 D ≠ (D.mem u).A.T := fun u => (h.trans (GlobalTheory.EX.DC.firstTypePrime_lt_rowPrime D u)).ne
  ⟨D.sp_T ▸ key D.u₀, key⟩

theorem auxiliaryPrime_lt_firstTypePrime_of_sizeRows {large₂ : SizeData₂ D} (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) : q0 D < D.host.g 0 := by
  have h1 : Real.log (q0 D) ≤ large₂.sc.L := hs.2.2.2.2.2.2.2.2.1
  have h2 := (hs.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 0 0).1
  have hq : (0 : ℝ) < q0 D := by exact_mod_cast (leastSplitAuxiliaryPrimeThetaChain_spec D).1.pos
  have h3 : (q0 D : ℝ) ≤ large₂.sc.b := (Real.log_le_iff_le_exp hq).1 h1
  have hb : 1 ≤ large₂.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _)
  have hk : (2 : ℝ) ≤ D.R.k := by have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 2 ≤ D.R.k)
  have h4 : (D.R.k : ℝ) * large₂.sc.b ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := le_self_pow₀ (by nlinarith) (by norm_num)
  have : (q0 D : ℝ) < D.host.g 0 := by nlinarith
  exact_mod_cast this

theorem exists_gridPre_agree (hDS : GlobalTheory.Published.DiscreteSeriesUpqExists) (hDC : GlobalTheory.Published.DiscreteSeriesCover)
    (hHC : GlobalTheory.Published.HarishChandraModules) (hH : HostHyp D) (hS : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D) (hq : q0 D < D.host.g 0)
    {F : Face D A} (hR : GlobalTheory.Hk3.Core R F)
    (hsc : sc.cGap = 1) {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil) (hW : W.Over R)
    (hL : ∀ X : GlobalTheory.ChiGrid.Node, X.InRange D.R.m → (∀ j, X ≠ .grid 0 j) → (G'.Λ X : Set _) = L0c D (G'.V X))
    (oV : ∀ i j, 1 ≤ i → i ≤ D.R.m → j ≤ D.R.m → ∀ τ, ∃ (lam : Fin (G'.V (.grid i j)).rank → ℝ)
      (ε : Fin (G'.V (.grid i j)).rank → Bool), IsEnum (GlobalTheory.Grid.parV D i j τ) lam ε ∧
        (W.onb (.grid i j) τ)ᴴ * gramAt D (G'.V (.grid i j)) τ * W.onb (.grid i j) τ = Formalism.REAL.Jm ε)
    (oP : ∀ i, i ≤ D.R.m → ∀ τ, ∃ (lam : Fin (G'.V (.core i)).rank → ℝ) (ε : Fin (G'.V (.core i)).rank → Bool),
      IsEnum (GlobalTheory.Grid.parP D i τ) lam ε ∧
        (W.onb (.core i) τ)ᴴ * gramAt D (G'.V (.core i)) τ * W.onb (.core i) τ = Formalism.REAL.Jm ε)
    (oX : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, ∃ (lam : Fin (G'.V (.top j)).rank → ℝ) (ε : Fin (G'.V (.top j)).rank → Bool),
      IsEnum (GlobalTheory.Grid.parXp D j τ) lam ε ∧
        (W.onb (.top j) τ)ᴴ * gramAt D (G'.V (.top j)) τ * W.onb (.top j) τ = Formalism.REAL.Jm ε)
    (hc : W.cart (.top 0) = W.cart (.core D.R.m)) (hb : W.onb (.top 0) = W.onb (.core D.R.m)) :
    ∃ G : GlobalTheory.Grid.GridPre R, G.Is ∧ Agree G W := by
  obtain ⟨e, he, hcos⟩ := W.cosVec_is
  obtain ⟨G, rfl, hsp, hch, hag⟩ := _root_.GlobalTheory.GridJoin.exists_gridPre_spaces hDS hH hR hsc W hW hL (pg_under_inj hR) (auxiliaryPrime_splitsCompletely _)
    (auxiliaryPrime_ne_typePrime G') (auxiliaryPrime_ne_levelPrimes_of_lt hq) oV oP oX hc hb e he
  obtain ⟨X, ωT, vacT, ItT, ωC, vacC, ItC, dn, ItU, vC, harr, hdat, hag2⟩ : ∃ X ωT vacT ItT ωC vacC ItC dn ItU vC,
      (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC).IsArrows ∧ (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC).IsData ∧
        ArrAgree (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC) W := by
    first
      | exact _root_.GlobalTheory.GridJoin.exists_arrows hDC hHC hH hS hR hsc W hW G hsp hch hag hcos
      | exact _root_.GlobalTheory.GridJoin.exists_arrows hDC hHC hH hR hsc W hW G hsp hch hag hcos
  obtain ⟨m00, mV, mP, mX, hm⟩ := exists_isMeas (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC) (isSpaces_withArr hsp)
  exact ⟨withMeas (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC) m00 mV mP mX,
    ⟨isSpaces_withMeas (isSpaces_withArr hsp), isChars_withMeas (isChars_withArr hch), isArrows_withMeas harr, hm,
      isData_withMeas hdat⟩, spAgree_withMeas (spAgree_withArr hag), arrAgree_withMeas hag2⟩

theorem exists_gridPre_of_sizes (hDS : GlobalTheory.Published.DiscreteSeriesUpqExists) (hDC : GlobalTheory.Published.DiscreteSeriesCover)
    (hHC : GlobalTheory.Published.HarishChandraModules) (hH : HostHyp D) (hS : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D) (hq : q0 D < D.host.g 0)
    {F : Face D A} (hR : GlobalTheory.Hk3.Core R F)
    (hsc : sc.cGap = 1) {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil) (hW : W.Over R) :
    ∃ G : GlobalTheory.Grid.GridPre R, G.Is ∧ Match G W := by
  obtain ⟨G₁, W₁, h₁, hL⟩ := exists_sameWeil W
  obtain ⟨W₂, hW₂, -, -, ec, eo, ev, ek, e0, e1, -, oV, oP, oX, hc, hb⟩ := exists_weil_ordered hH hsc W₁ (h₁.over hW)
  have eb : ∀ X : GlobalTheory.ChiGrid.Node, X.InRange D.R.m → X ≠ .top 0 → ∀ τ, ∃ σ : Equiv.Perm (Fin (G₁.V X).rank),
      W₂.onb X τ = (W₁.onb X τ).submatrix id σ := fun X hX h0 τ => by
    by_cases h : ∀ j, X ≠ .grid 0 j
    · exact e1 X hX h h0 τ
    · obtain ⟨j, hj⟩ := not_forall.1 h
      obtain rfl := not_not.1 hj
      exact ⟨1, congrFun (e0 j) τ⟩
  obtain ⟨G, hG, a, b⟩ := exists_gridPre_agree hDS hDC hHC hH hS hq hR hsc W₂ hW₂ hL oV oP oX hc hb
  have ep := h₁.pl
  refine ⟨G, hG, ⟨fun j hj => nodeAgree_grid0_of_weil_over W hW j hj,
    fun i j hi hj => (a.vert i j hi hj).nodeMatch_of h₁ ec (eb (.grid i j) ⟨hi, hj⟩),
    fun i hi => (a.core i hi).nodeMatch_of h₁ ec (eb (.core i) hi),
    fun j hj => (a.top j hj).nodeMatch_of h₁ ec (eb (.top j) hj), a.q0, ep ▸ a.w0, ep ▸ a.e0, ep ▸ a.places,
    a.lvl.trans (congrArg (fun P => Places.modul P sc) ep), fun i x y => h₁.chiH ▸ a.chiH i x y,
    fun i x y => h₁.chi ▸ a.chi i x y⟩, b.of_sameWeil h₁ eo ev ek⟩

theorem exists_gridPre (hDS : GlobalTheory.Published.DiscreteSeriesUpqExists) (hDC : GlobalTheory.Published.DiscreteSeriesCover)
    (hHC : GlobalTheory.Published.HarishChandraModules) (hH : HostHyp D) {large₂ : SizeData₂ D} (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂)
    {F : Face D A} (hR : GlobalTheory.Hk3.Core R F)
    (hsc : sc.cGap = 1) {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil) (hW : W.Over R) :
    ∃ G : GlobalTheory.Grid.GridPre R, G.Is ∧ Match G W :=
  exists_gridPre_of_sizes hDS hDC hHC hH (GlobalTheory.RowSizes.sizes_of_sizeRows large₂ hs) (auxiliaryPrime_lt_firstTypePrime_of_sizeRows hs) hR hsc W hW

end GlobalTheory.GridJoin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselToFourierJacobiNonvanishingTower
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.Asc.RungJac

theorem exists_step {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {V V₀ W W₀ : HSp D} {ρ σ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ)
    {χV χW : (AE D)ˣ →* Circle} {om : Om V W} (h : IsWeilDatumO ψ V W χV χW om) (vW : GlobalTheory.Unf.Vol W) :
    ∃ s : Step ψ V V₀ W W₀ ρ σ, s.om = om ∧ s.χV = χV ∧ s.χW = χW ∧ s.vW = vW := by

  have hdesc := GlobalTheory.Unf.descent_of_weilDatumExists D (GlobalTheory.WeilDatumExistence.weilDatumExists D)
  obtain ⟨omA, hA⟩ := (hdesc ψ V W χV χW om h).1 V₀ ρ dV
  obtain ⟨om₀, h₀⟩ := (hdesc ψ V₀ W χV χW omA hA).2 W₀ σ dW

  obtain ⟨vS⟩ := GlobalTheory.Unf.VolExist.nonempty_volM D W.rank ρ
  obtain ⟨vT⟩ := GlobalTheory.Unf.VolExist.nonempty_volM D σ V₀.rank
  obtain ⟨vU⟩ := GlobalTheory.Unf.VolExist.nonempty_volU D ρ
  exact ⟨{ χV := χV, χW := χW, om := om, om₀ := om₀, weil := h, weil₀ := h₀, vW := vW, vS := vS, vT := vT, vU := vU },
    rfl, rfl, rfl, rfl⟩

private theorem rapidDec_star' {D : D7} {V : HSp D} {f : GA D V → ℂ} (hf : RapidDec V f) : RapidDec V (star f) := by
  refine ⟨fun γ hγ g => ?_, continuous_star.comp hf.2.1, fun N => ?_⟩
  · show star (f (γ * g)) = star (f g)
    rw [hf.1 γ hγ g]
  · obtain ⟨C, hC⟩ := hf.2.2 N
    exact ⟨C, fun g => by simpa only [Pi.star_apply, norm_star] using hC g⟩

private theorem isHeckeChar_of_isHeckeChar_mul {D : D7} {χ χ' : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ)
    (h' : IsHeckeChar D (χ * χ')) : IsHeckeChar D χ' := by
  have e : (χ' : (AE D)ˣ → Circle) = fun x => (χ x)⁻¹ * (χ * χ') x := by
    funext x
    simp
  refine ⟨?_, fun x => ?_⟩
  · rw [e]
    exact h.1.inv.mul h'.1
  · have hx := h'.2 x
    rw [MonoidHom.mul_apply, h.2 x, one_mul] at hx
    exact hx


set_option maxHeartbeats 1000000 in
theorem rungJ : FockTot → PartFixed → RungJ := by
  intro hFock hFix D hD T L μ0 hL sc G W M hM v F ΓL _hEnds hGood Ψ hΨ u hu k h h' hB
  obtain ⟨ρ, Φ, hne⟩ := hB
  have hi : 2 * k + 2 < D.R.m := by omega

  obtain ⟨c1, c2, -, c4, c5, c6, c7, c8, c9h, c9f⟩ :=
    _root_.GlobalTheory.Asc.conjRead_holds D hD T L μ0 hL sc G W M hM (2 * k + 2) hi
  obtain ⟨c4a, c4b⟩ := c4 ⟨k + 1, by omega⟩
  rw [c4a, c4b] at c1

  have hex := GlobalTheory.WeilDatumExistence.weilDatumExists D
  have hc2 := ((GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumExistenceCriterion.weilDatumExists_iff D).1 hex _ _ W.ψ _ _).1 ⟨_, c2⟩
  have hc1 := ((GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumExistenceCriterion.weilDatumExists_iff D).1 hex _ _ W.ψ _ _).1 ⟨_, c1⟩
  have hEta : IsHeckeChar D L.eta := isHeckeChar_of_isHeckeChar_mul hc2.2.1 hc1.2.2.1
  obtain ⟨omz, hz⟩ : ∃ omz : Om (G.V (.core (2 * k + 2 + 1))) (negSp F.Lz),
      IsWeilDatumO W.ψ _ _ (G.ch.chi (D.R.m - (2 * k + 2)))⁻¹ L.eta omz := by
    refine hex _ _ W.ψ _ _ W.ψ_std hc2.2.1 hEta hc2.2.2.2.1 ?_
    show ResEta D L.eta F.Lz.rank
    rw [F.rk]
    exact GlobalTheory.HeckeCharacterRestriction.resEta_eta hL

  obtain ⟨s, hs_om, hs_χV, hs_χW, hs_vW⟩ := exists_step (F.dJ (k + 1) h) (F.dB k h') c1
    ⟨M.ν (.grid (2 * k + 2) 0), M.fd (.grid (2 * k + 2) 0), c9h, c9f⟩
  obtain ⟨𝒮, Γ₀, hLoc, hRow, hBox⟩ := hGood.fb k h h' s hs_om

  obtain ⟨f, hf, hΨi⟩ := hΨ.2 (2 * k + 2) hi
  obtain ⟨Φ₀, hΦ₀, hΦ₀ne⟩ := hGood.lineNe (k + 1) h
  have hVf := (c5 f).1 hf
  have hRφ : RapidDec _ (star (Ψ (2 * k + 2 + 1))) := rapidDec_star' (hΨ.1 _ (by omega))
  have hRG : RapidDec _ (star (part W M ρ Φ u (2 * k + 2) h')) := rapidDec_star' (hu ρ Φ _ _)
  have hK : ∀ x ∈ lev G (.grid (2 * k + 2) 0), ∀ g,
      star (part W M ρ Φ u (2 * k + 2) h') (g * x) = star (part W M ρ Φ u (2 * k + 2) h') g :=
    fun x hx g => congrArg star (hFix D hD T L μ0 hL sc G W M hM ρ Φ u (2 * k + 1) h' x hx g)

  have hper : (F.bes v k h').per W.ψ
      (liftT (omCore W (2 * k + 2)) (v (2 * k + 2 + 1)).μ (v (2 * k + 2 + 1)).𝓕 (star (Ψ (2 * k + 2 + 1))) (star f))
      (star (part W M ρ Φ u (2 * k + 2) h')) ≠ 0 := by
    rw [← c6 v f (Ψ (2 * k + 2 + 1)), ← hΨi]
    exact hne

  obtain ⟨Φ', hΦ'𝒮, hΦ'ne⟩ := _root_.GlobalTheory.UpFromBessel.upFB D W.ψ k (F.jac v (k + 1) h) (F.bes v k h') s 𝒮 Γ₀ _ hLoc
    (G.ch.chi (D.R.m - (2 * k + 2)))⁻¹ L.eta (omCore W (2 * k + 2)) omz hs_χW (by rw [hs_χV]; exact c2)
    (by rw [hs_χV]; exact hz) _ _ hRφ hRG hK (star f) Φ₀ hVf.1 hΦ₀.1 hΦ₀ne (hBox _ _ hVf hΦ₀) hper

  have hTame := (_root_.GlobalTheory.LiftTame.lift_periods_tame D W.ψ _ s.vW (star (part W M ρ Φ u (2 * k + 2) h')) hRG).2 (k + 1)
    (F.jac v (k + 1) h) _ _ s.om s.weil (negSp F.Lz) (F.ζ (k + 1)) _ _ omz hz (star (Ψ (2 * k + 2 + 1))) Φ₀ hRφ hΦ₀.1
  have hFk := hFock D hD T L μ0 hL sc G W M hM ⟨2 * k + 2, hi⟩ _ hTame
  obtain ⟨κ, P, hκP⟩ : ∃ κ P, (F.jac v (k + 1) h).per W.ψ (F.ζ (k + 1)) omz (star (Ψ (2 * k + 2 + 1)))
      (s.lift (star (part W M ρ Φ u (2 * k + 2) h')) (star (W.fock (.chi (2 * k + 2) 0) (W.cosVec (2 * k + 2) κ) P))) Φ₀ ≠ 0 := by
    by_contra hall
    push_neg at hall
    exact hΦ'ne (hFk hall Φ' (hRow Φ' hΦ'𝒮))

  have hpart : part W M (Function.update ρ ⟨2 * k + 2, hi⟩ P) (Function.update Φ ⟨2 * k + 2, hi⟩ κ) u (2 * k + 2) hi.le =
      part W M ρ Φ u (2 * k + 2) hi.le := by
    refine (c8 ρ Φ _ _ u fun j hj => ?_).symm
    have hj' : j ≠ ⟨2 * k + 2, hi⟩ := fun e => by
      rw [e] at hj
      exact lt_irrefl _ hj
    exact ⟨(Function.update_of_ne hj' P ρ).symm, (Function.update_of_ne hj' κ Φ).symm⟩
  have hdat : W.datum (Function.update ρ ⟨2 * k + 2, hi⟩ P) (Function.update Φ ⟨2 * k + 2, hi⟩ κ) ⟨2 * k + 2, hi⟩ =
      W.fock (.chi (2 * k + 2) 0) (W.cosVec (2 * k + 2) κ) P := by
    simp only [GridData.Weil.datum, Function.update_self]
  have hlift := c7 (Function.update ρ ⟨2 * k + 2, hi⟩ P) (Function.update Φ ⟨2 * k + 2, hi⟩ κ) u
  rw [hpart, hdat] at hlift
  have e2 : ∀ G0 X, s.lift G0 X = liftS (omRow W (2 * k + 2)) (M.ν (.grid (2 * k + 2) 0)) (M.fd (.grid (2 * k + 2) 0)) G0 X := by
    intro G0 X
    show liftS s.om s.vW.μ s.vW.𝓕 G0 X = _
    rw [hs_om, hs_vW]
  rw [e2] at hκP
  refine ⟨_, omz, hz, Function.update ρ ⟨2 * k + 2, hi⟩ P, Function.update Φ ⟨2 * k + 2, hi⟩ κ, Φ₀, hΦ₀, ?_⟩
  have key : (F.jac v (k + 1) h).per W.ψ (F.ζ (k + 1)) omz (star (Ψ (2 * k + 2 + 1)))
      (star (part W M (Function.update ρ ⟨2 * k + 2, hi⟩ P) (Function.update Φ ⟨2 * k + 2, hi⟩ κ) u (2 * k + 2 + 1) hi)) Φ₀ ≠ 0 := by
    rw [hlift]
    exact hκP
  exact key

end GlobalTheory.Asc.RungJac

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChiArrowPairMovesStandardVacuumByScalar
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowChiVac

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem vac_chi_scalar : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {i : ℕ}, i + 1 ≤ D.R.m → ∀ (x : FinPt G (.grid i D.R.m)) (y : FinPt G (.grid (i + 1) D.R.m)), (∀ u, u ∈ latO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (S.N.latS (.chi i D.R.m) : Set _) (S.N.latT (.chi i D.R.m) : Set _) (fun _ => True) ↔ actO _ _ (G.toPair (.chi i D.R.m) x y).1 (G.toPair (.chi i D.R.m) x y).2 u ∈ latO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (S.N.latS (.chi i D.R.m) : Set _) (S.N.latT (.chi i D.R.m) : Set _) (fun _ => True)) → ∃ c : ℂ, W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) x y) (S.Z.vac (.chi i D.R.m)) = c • S.Z.vac (.chi i D.R.m) := by
  intro D T L sc G W U S i hi x y hlat
  have hp : DefPair D.R.m (Pair.chi i D.R.m : Pair T) := ⟨hi, rfl⟩
  have hom := W.om_is (.chi i D.R.m) (by simp only [Pair.InRange, Pair.big, Node.InRange]; omega)
  have m1 : (G.toPair (.chi i D.R.m) x y).1 ∈ GfC _ := GlobalTheory.LastRowVac.negGA_mem _ y.2
  have m2 : (G.toPair (.chi i D.R.m) x y).2 ∈ GfC _ := x.2
  have hΛ : ∀ u, u ∈ latO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (S.N.latS (.chi i D.R.m) : Set _)
        (S.N.latT (.chi i D.R.m) : Set _) (fun _ => True) ↔
      ∃ u₀ ∈ latO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) (S.N.latS (.chi i D.R.m) : Set _)
        (S.N.latT (.chi i D.R.m) : Set _) (fun _ => True),
        u = actO _ _ (G.toPair (.chi i D.R.m) x y).1 (G.toPair (.chi i D.R.m) x y).2 u₀ := by
    intro u
    have e := GlobalTheory.WeilVacMove.actO_inv_actO (G.toPair (.chi i D.R.m) x y).1⁻¹ (G.toPair (.chi i D.R.m) x y).2⁻¹ u
    rw [inv_inv, inv_inv] at e
    constructor
    · intro hu
      refine ⟨actO _ _ (G.toPair (.chi i D.R.m) x y).1⁻¹ (G.toPair (.chi i D.R.m) x y).2⁻¹ u, (hlat _).2 ?_, e.symm⟩
      rw [e]
      exact hu
    · rintro ⟨u₀, hu₀, rfl⟩
      exact (hlat u₀).1 hu₀
  have hv' := GlobalTheory.WeilVacMove.isVacO_om D W.ψ W.θ _ _ _ _ (W.om _) hom W.θ_is _ _ _ _ _ _ _ _
    (G.toPair (.chi i D.R.m) x y).1 (G.toPair (.chi i D.R.m) x y).2
    (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC W.θ _ m1, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC W.θ _ m2, Matrix.mul_one, Matrix.one_mul])
    hΛ _ (S.Z.vac_is _ hp)
  obtain ⟨c, -, hc⟩ := GlobalTheory.LastRowVac.eq_smul_vac S hp _ hv'
  exact ⟨c, hc⟩

end GlobalTheory.RowChiVac

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeTermGeneratorConstantViaFrameStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTerm_generator_constant_via_frame : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV →
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ (h : GA D (Wc D i))
      (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∀ a ∈ Rc, ∀ (C : hkKer (Xo := T.Q.Xo ((i : ℕ) + 1)) P.asIdeal p k (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩)) z, hkRelFr P.asIdeal p k (GlobalTheory.ThetaTrace.hkTr (T.Q.Xo ((i : ℕ) + 1)) T.Q.c p) (CAt σ) ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) C z →
        ∀ (hx' : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1).dom) (t : Ix (T.Q.Dw ((i : ℕ) + 1)) → (CAt σ)ˣ),
          (∀ j, j ≠ none → t j = 1) → FrBor t ((T.U ((i : ℕ) + 1) σ).un (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).2, hx'⟩) z →
          toC (t none : CAt σ) ^ (κ i).n *
              ((T.cE ((i : ℕ) + 1) σ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) *
                σ (hkScal T.Q.c 1 P.asIdeal k D.R.nV)) =
            (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.muAt T R i P)⁻¹ ^ k *
              (T.cE ((i : ℕ) + 1) σ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV (h * a)).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) (h * a)) := by
  first | exact @GlobalTheory.HeckeGenConst.generator_constant | exact GlobalTheory.HeckeGenConst.generator_constant | (intros; apply GlobalTheory.HeckeGenConst.generator_constant <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedGridArrowLatticeIffIntegralFrameMatrStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_completedGridArrowLattice_iff_integral_frameMatrix : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (B : Frames G) (t : T) {e₁ : AE D} {P₁ : Finset (Pl D.host.E)}, IsIdemSum e₁ P₁ → (∀ w ∈ P₁, ((∀ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) ≤ 1) ∧ ∃ a ∈ D.host.AA, Valued.v (algebraMap D.host.E (Kw w) a) = 1)) → ∀ (i : Fin D.R.m) (z : WO (G.pS (.chi (i : ℕ) 0)) (G.pT (.chi (i : ℕ) 0))), IsHalf e₁ z → (z ∈ (latO (G.pS (.chi (i : ℕ) 0)) (G.pT (.chi (i : ℕ) 0)) (G.latS (.chi (i : ℕ) 0) : Set _) (G.latT (.chi (i : ℕ) 0) : Set _) fun _ => True) ↔ ∀ w ∈ P₁, GlobalTheory.StepData.IntM (B.coord t w (X := ((i : ℕ), 0)) (Y := ((i : ℕ) + 1, 0)) ⟨i.2.le, Nat.zero_le _⟩ ⟨i.2, Nat.zero_le _⟩ (z.map (cpt (D := D) w ∘ toEAf D)))) := by
  first | exact @GlobalTheory.RowLatChi.mem_latO_iff_intM | exact GlobalTheory.RowLatChi.mem_latO_iff_intM | (intros; apply GlobalTheory.RowLatChi.mem_latO_iff_intM <;> assumption)
end

