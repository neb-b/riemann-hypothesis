module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapEq
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TupPrimeEmpty
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0468
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0986
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0907
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1227
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1592
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1586
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1589
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1649
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlace

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatHeckeCharacterTrivialCongruentUnits
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.Mem.HeckeLevel

open GlobalTheory.Mem.Chr

theorem exists_level_nat : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L), ∃ M : ℕ, 0 < M ∧ ∀ a : Neutral.B1.Ideles L, a ∈ GlobalTheory.Mem.Chr.unitIdl L → (∀ w, (a : AdeleRing (𝓞 L) L).1 w = 1) → (∀ P : HeightOneSpectrum (𝓞 L), Valued.v ((a : AdeleRing (𝓞 L) L).2 P - 1) ≤ Valued.v ((M : L) : P.adicCompletion L)) → χ.1 a = 1 := by
  intro L _ _ χ
  classical
  obtain ⟨hfin, hlev⟩ := GlobalTheory.Mem.UnrAe.unr_ae_and_level L χ
  choose n hn using hlev
  refine ⟨∏ P ∈ hfin.toFinset, (Ideal.absNorm P.asIdeal) ^ (n P), ?_, ?_⟩
  · refine Finset.prod_pos fun P _ => pow_pos (Nat.pos_of_ne_zero fun h => P.ne_bot ?_) _
    exact Ideal.absNorm_eq_zero_iff.1 h
  · intro a ha h1 hv
    refine GlobalTheory.Mem.LocTriv.eq_one_of_local L χ.1 χ.2.1 a ha h1 fun P x hx => ?_
    have hxu : IsUnitAt P x := by
      unfold IsUnitAt
      rw [hx]
      exact ha P
    by_cases hP : P ∈ hfin.toFinset
    · refine hn P x hxu ?_
      rw [hx]
      refine (hv P).trans ?_
      have e : (((∏ Q ∈ hfin.toFinset, (Ideal.absNorm Q.asIdeal) ^ (n Q) : ℕ) : L) : P.adicCompletion L) =
          (((∏ Q ∈ hfin.toFinset, (Ideal.absNorm Q.asIdeal) ^ (n Q) : ℕ) : 𝓞 L) : L) := by
        push_cast
        rfl
      rw [e, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap,
        HeightOneSpectrum.intValuation_le_pow_iff_dvd]
      have hd : (Ideal.absNorm P.asIdeal) ^ (n P) ∣ ∏ Q ∈ hfin.toFinset, (Ideal.absNorm Q.asIdeal) ^ (n Q) :=
        Finset.dvd_prod_of_mem _ hP
      have hd' := Ideal.span_singleton_le_span_singleton.2 (Nat.cast_dvd_cast (α := 𝓞 L) hd)
      refine Ideal.dvd_iff_le.2 (le_trans hd' ?_)
      rw [Nat.cast_pow, ← Ideal.span_singleton_pow]
      refine Ideal.pow_right_mono ?_ _
      rw [Ideal.span_singleton_le_iff_mem]
      exact Ideal.absNorm_mem P.asIdeal
    · have hu : χ.UnrAt P := by
        by_contra h
        exact hP (hfin.mem_toFinset.2 h)
      exact hu x hxu

end GlobalTheory.Mem.HeckeLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroComplementaryAdelicSchwartzFunction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

open scoped Classical

namespace GlobalTheory.RestComplement

theorem exists_rest_ne_zero : ∀ {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {κ : Type} [Fintype κ]
    (f : (κ → Fv F v) → ℂ), f ∈ GlobalTheory.WeilM.SB (κ → Fv F v) →
    ∃ r : (κ → AF F) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) f r ∧ ∃ x₀, r x₀ ≠ 0 := by
  intro F _ _ v κ _ φ hφ
  obtain ⟨f, hf⟩ := GlobalTheory.TensUniq.exists_sInf_ne_zero F κ
  let φs : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F w) → ℂ :=
    fun w => Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1
  have hstd : ∀ᶠ w in Filter.cofinite, φs w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers F} 1 :=
    Filter.Eventually.of_forall fun _ => rfl
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φs hstd
  have hRest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (evFin F v) φ r := by
    refine ⟨hr, ?_⟩
    rw [hrt φ]
    refine GlobalTheory.TensUniq.pure_mem_schA f _ (fun w => ?_) (GlobalTheory.PureFactor.update_eventually φs v φ hstd)
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]; exact hφ
    · rw [Function.update_of_ne hw]; exact GlobalTheory.StdVacuum.indicator_mem_SB w
  refine ⟨r, hRest, 0, ?_⟩
  have e := congrFun (hrt (fun _ => 1)) 0
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, one_mul] at e
  rw [e]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
  have hI : (fun i : κ => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F ((0 : κ → AF F) i)) = 0 := by
    funext i
    show (InfiniteAdeleRing.ringEquiv_mixedSpace F) (0 : AF F).1 = 0
    exact map_zero _
  have hP : (∏ᶠ w, Function.update φs v (fun _ => 1) w fun i => evFin F w ((0 : κ → AF F) i)) = 1 := by
    refine finprod_eq_one_of_forall_eq_one fun w => ?_
    by_cases hw : w = v
    · subst hw; rw [Function.update_self]
    · rw [Function.update_of_ne hw]
      simp only [φs, Pi.zero_apply, map_zero]
      rw [Set.indicator_of_mem (by intro i; exact zero_mem _)]
      rfl
  rw [hI, hP, mul_one]
  exact hf

end GlobalTheory.RestComplement
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalisedTupleDataOverRowFieldConditions
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PinsOverClauses

open GlobalTheory.CoverHalf GlobalTheory.TwistField GlobalTheory.PinnedData GlobalTheory.PinsOverField
open scoped nonZeroDivisors

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

variable (R : RealDat D A Ks) (i : Fin D.R.m)


set_option maxHeartbeats 1000000 in
theorem exists_phi_core {F : Face D A} (hR : GlobalTheory.Hk3.Core R F) (hV : VStd D i) (t : T0) {La : Type} [AddCommGroup La]
    [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)) (hι : LatEmb (Wc D i) ι)
    (M : IntermediateField ℚ ℂ) (hM : M = D.what₂.embLL.toRatAlgHom.fieldRange)
    (hP : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal)
    (J : Ideal (𝓞 D.host.E))
    (hJ : ∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q t → ∀ c ∈ J, ∃ c' ∈ PP.asIdeal, (c' : D.host.E) = D.sp.cm.sig (c : D.host.E)) :
    ∃ φ : (Fin (Vc D i).rank → La ⧸ (J • ⊤ : Submodule (𝓞 D.host.E) La)) → M, PhiIs R i M.val.toRingHom t ι (J • ⊤) φ := by
  have hv : ∀ y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP),
      omegaK R.Pg y * omegaQ (R.Q t) (Wc D i).rank (R.xiR t) (-1) y ∈ M := fun y => by
    refine mul_mem ?_ ?_
    · unfold omegaK
      split_ifs
      exacts [one_mem _, zero_mem _]
    · unfold omegaQ
      split_ifs
      · exact prod_mem fun PP _ => zpow_mem (hM ▸ xiR_mem R hR.lev hR.fam t PP.1 PP.2 _) _
      · exact zero_mem _
  obtain ⟨-, e, he, -⟩ := hR.thP.vP i t
  have hβ := _root_.GlobalTheory.StdFrameInv.isIntM_inv D i _ _ hV (hR.lev.βV i)
  have hi : ∀ x a, rowP (Wc D i) (R.βW i) e (ι x) a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun x a =>
    rowP_int _ _ _ (hR.lev.βW i) e _ he (fun PP h => hP PP (by simpa using h)) _
      (hι.2.le (LinearMap.mem_range_self ι x)) a
  refine ⟨fun q => ⟨_, hv fun PP => redM PP
    (FWT.uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => ι (q b).out)⟩, e, he, fun x =>
    ⟨(redM_uMat (Vc D i) (Wc D i) hV.1 _ hβ (R.βW i) e (fun b => ι (x b)) fun b a => hi (x b) a).1, ?_⟩⟩
  exact omega_congr _ _ _ _ _ _ _ fun PP hPP => exists_datum (Vc D i) (Wc D i) hV.1 _ hβ (R.βW i) e ι hi J PP (hJ PP hPP) x _
    fun b => (Submodule.Quotient.eq _).1 (Quotient.out_eq _)


set_option maxHeartbeats 2000000 in
theorem pinsOverL_of_clauses : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m), GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → OMPins T R κ v₀ O i → QGuard R → GlobalTheory.TwistField.CoverField T R → GlobalTheory.TwistField.PinsOverL T R κ v₀ i := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ O i hR _hoff _hused hfw hO hG hC
  obtain ⟨fw⟩ := id hfw
  have hT := fw.laws
  have hpb : T.pb = R.C.P.pb := GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore R hT.toLawsM hR.lev (hO.2.tuple ()).half
  obtain ⟨hc', hP⟩ := hO
  have hV : VStd D i := hP.lift.std
  have hB0 := (hP.tuple ()).B
  have hb0 := hP.bad ()
  have hjL := hP.lift.field
  have hlev := hP.lift.lev
  have hio := hP.io
  have hact := hP.act
  choose l₂ hl₁ hl₂ using exists_half_tupPrime T.toCore R hT.toLawsM hR.lev hpb hG
  obtain ⟨dδ, U₂, dict₂, xi, -, hcov, hhalf, hxi, hcxi, hmod, -⟩ :=
    GlobalTheory.CoverOverField.coversAt D G Pl0 T0 A T R hT hR.lev hR.fam.roots
      (GlobalTheory.TwistValues.xiVal D G Pl0 T0 A _ R hR.lev hR.fam) hC i (Vc D i).rank _ l₂ hl₁ hl₂ (O i).c' (O i).hle hc'
  obtain ⟨gramR, c0R, c0L, hTie⟩ := hR.fam.tie
  obtain ⟨c0', hcb, hplace⟩ := GlobalTheory.Div.CoefExtension.exists_ext_placeEx D G Pl0 T0 A _ R hR.lev hR.grp.chiW hR.fam hR.models
    gramR c0R c0L hTie i (O i).c'.F (O i).jL (inC (O i).c') hjL
  have hc0 : ∃ gramR c0R c0L, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
      (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L ∧ CoefficientBaseChange R i (O i).jL (inC (O i).c') (c0L i) c0' :=
    ⟨gramR, c0R, c0L, hTie, hcb⟩
  choose Cl fCl h J' bad Lh gam vol La Nc hrep hdv hvol hok hlat using fun t =>
    GlobalTheory.SplitReps.exists_repsR_repsOK R i (hR.lev.βV i) hV (O i).c'.F t (dδ t).l₂ hb0.1
  have hbad : ∀ t, 0 < bad t ∧ BadPin (bad t) (D.host.QS * D.host.q) D.host.d (D.host.g 0 * D.host.g 1) := fun t =>
    ⟨Nat.pos_of_ne_zero (hrep t).1, hb0.2.1.trans (hdv t), hb0.2.2.1.trans (hdv t), hb0.2.2.2.1.trans (hdv t),
      hb0.2.2.2.2.trans (hdv t)⟩
  choose B hBis using fun t => exists_BIs R i hR.lev hR.fam (O i).c'.F hc' hB0 t (hdv t)
  have hodd : Odd ((T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q) := by
    obtain ⟨e1, e2, -⟩ := hT.pins.2.2.2 _ (inR i)
    have h5 := Formalism.L2.NTheta.odd_r D.R
    have h6 := i.2
    have h7 := D.R.m_add_three_le_k
    rw [e1, e2]
    convert h5 using 1
    simp only [Ranks.sigW, Ranks.r]
    omega
  choose epF hepF using fun t => (GlobalTheory.ClassTieCompare.exists_epIs_iff (n := (Vc D i).rank) (Dw := T.Q.Dw ((i : ℕ) + 1))
    (bad t) (B t)).2 fun L cc g d => _root_.GlobalTheory.LawOfSquares.law_of_squares _ _ _ _ hodd L cc g.1 g.2.2 d.1 d.2
  choose φ hφis using fun t => exists_phi_core R i hR hV t (iotaW T i) (latEmb_iotaW T hT i) (O i).c'.F hc'
    (hhalf t).2.2 (Mfr (dδ t).l₂) fun PP hPP c hc => by
    have hM : (dδ t).l₂.Mb ≤ PP.asIdeal := by
      rw [(hcov t).1.2.2.2.1]
      rcases hPP with hPP | hPP
      · rw [(hhalf t).1]
        exact Ideal.mul_le_left.trans (Ideal.prod_le_inf.trans (Finset.inf_le hPP))
      · exact Ideal.mul_le_right.trans ((hhalf t).2.1 PP hPP)
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ T.Q.H.bar.surjective).1 hc
    refine ⟨b, hM hb, ?_⟩
    change _ = star ((T.Q.H.bar b : 𝓞 D.host.E) : D.host.E)
    rw [T.Q.H.bar_eq]
    exact (star_star _).symm
  choose thAd hth using fun t => GlobalTheory.AdelicSide.exists_thAd_of_models D G Pl0 T0 A _ R hR.models i t _ _ c0' _ (h t) _
    (hrep t).2.2.1 (hrep t).2.2.2.2.2.1 (v₀ i (sg0 D A))
  refine ⟨{ c' := (O i).c', hle := (O i).hle, jL := (O i).jL, hV := (O i).hV, c0' := c0', lev := (O i).lev, dδ := dδ, Cl' := Cl,
            bad := bad, Lh := Lh, La := La, Nc := Nc, gam := gam, vol := vol, ep := fun t k => epF t (Lh t k), B := B,
            epF := epF, io := (O i).io, hw := (O i).hw, φ := φ,
            w := fun t _ q => (dδ t).eF.symm (phiHat (dδ t).c₂ (fun x => (dδ t).eF (φ t x)) q),
            U₂ := U₂, dict₂ := dict₂, xi := xi, thAd := thAd,
            Plc := fun t x => ∃ x₀, Place R i t (h t) c0' (jVx R i t x₀) x }, hc',
    ⟨hjL, hV, fw.hv₀ i _, hc0, hlev⟩,
    fun t => ⟨⟨h t, J' t, hrep t, hplace t _ _, hth t, fun _ => Iff.rfl⟩, hBis t, hxi t, hφis t, hhalf t⟩,
    hact, hbad, fun t => ⟨hok t, hlat t⟩, fun t => ⟨fun _ => rfl, hepF t⟩, hio,
    fun t k q => AlgEquiv.apply_symm_apply _ _, hcov, hcxi, hmod⟩

end GlobalTheory.PinsOverClauses
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecondCoordinateOfOrthogonalSelfDual
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory

theorem selfDual_exists_snd_of_orth : ∀ {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {κ : Type} [Fintype κ]
    (ψ₀ : AddChar (Fv F v) ℂ) (Λ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))),
    (∀ z, z ∈ Λ ↔ ∀ l ∈ Λ, ψ₀ (z.1 ⬝ᵥ l.2 - l.1 ⬝ᵥ z.2) = 1) →
    (∀ a ∈ v.adicCompletionIntegers F, ∀ l ∈ Λ, a • l ∈ Λ) →
    (∃ c : Fv F v, c ≠ 0 ∧ ∀ l ∈ Λ, ∀ i, c * l.1 i ∈ v.adicCompletionIntegers F) →
    ∀ u : κ → Fv F v, (∀ y, ((0 : κ → Fv F v), y) ∈ Λ → ψ₀ (u ⬝ᵥ y) = 1) → ∃ y', (u, y') ∈ Λ := by
  intro F _ _ v κ _ ψ₀ Λ hdual hsmul hbd u hu
  classical
  obtain ⟨c, hc0, hc⟩ := hbd
  let O := v.adicCompletionIntegers F
  let Λ' : Submodule O ((κ → Fv F v) × (κ → Fv F v)) :=
    { carrier := Λ
      add_mem' := fun ha hb => Λ.add_mem ha hb
      zero_mem' := Λ.zero_mem
      smul_mem' := fun a l hl => hsmul (a : Fv F v) a.2 l hl }
  let Λ₁ : Submodule O (κ → Fv F v) := Λ'.map (LinearMap.fst O _ _)
  let φ : (κ → O) →ₗ[O] (κ → Fv F v) :=
    { toFun := fun x i => c⁻¹ * (x i : Fv F v)
      map_add' := by intro x y; funext i; simp [mul_add]
      map_smul' := by intro a x; funext i; simp [Algebra.smul_def]; ring }
  have hle : Λ₁ ≤ LinearMap.range φ := by
    rintro x ⟨l, hl, rfl⟩
    refine ⟨fun i => ⟨c * l.1 i, hc l hl i⟩, ?_⟩
    funext i
    simp [φ, hc0]
  haveI : IsNoetherian O (LinearMap.range φ) := isNoetherian_of_isNoetherianRing_of_finite _ _
  haveI : IsNoetherian O Λ₁ := isNoetherian_of_le hle
  haveI : Module.Finite O Λ₁ := Module.IsNoetherian.finite O Λ₁
  haveI : Module.IsTorsionFree O Λ₁ := inferInstance
  haveI : Module.Free O Λ₁ := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis O Λ₁
  have hlift : ∀ i, ∃ l ∈ Λ, l.1 = (b i : κ → Fv F v) := fun i => by
    obtain ⟨l, hl, he⟩ := Submodule.mem_map.1 (b i).2
    exact ⟨l, hl, he⟩
  choose L hL hL1 using hlift
  have hliO : LinearIndependent O (fun i => (b i : κ → Fv F v)) :=
    b.linearIndependent.map' Λ₁.subtype (Submodule.ker_subtype _)
  have hliK : LinearIndependent (Fv F v) (fun i => (b i : κ → Fv F v)) :=
    (LinearIndependent.iff_fractionRing O (Fv F v)).1 hliO
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Finsupp.linearCombination (Fv F v) (fun i => u ⬝ᵥ (L i).2)) ∘ₗ (Module.Basis.span hliK).repr.toLinearMap)
  have hgb : ∀ i, g (b i) = u ⬝ᵥ (L i).2 := by
    intro i
    have h1 := LinearMap.congr_fun hg (Module.Basis.span hliK i)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.repr_self,
      Finsupp.linearCombination_single, one_smul, Submodule.subtype_apply] at h1
    rw [Module.Basis.span_apply] at h1
    exact h1
  let y' : κ → Fv F v := fun j => g (fun k => if j = k then 1 else 0)
  have hy : ∀ x, x ⬝ᵥ y' = g x := by
    intro x
    rw [LinearMap.pi_apply_eq_sum_univ g x]
    simp [dotProduct, smul_eq_mul, y']
  refine ⟨y', (hdual _).2 ?_⟩
  intro l hl
  have hl1 : l.1 ∈ Λ₁ := Submodule.mem_map.2 ⟨l, hl, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a, a = b.repr ⟨l.1, hl1⟩ := ⟨_, rfl⟩
  have hsum : l.1 = ∑ i, (a i : Fv F v) • (b i : κ → Fv F v) := by
    have h := congrArg Subtype.val (b.sum_repr ⟨l.1, hl1⟩)
    rw [← ha] at h
    refine h.symm.trans ?_
    rw [Submodule.coe_sum]
    rfl
  let m := l - ∑ i, (a i : Fv F v) • L i
  have hm : m ∈ Λ := Λ.sub_mem hl (Λ.sum_mem fun i _ => hsmul _ (a i).2 _ (hL i))
  have hm1 : m.1 = 0 := by
    simp [m, Prod.fst_sum, hL1, ← hsum]
  have hm2 : m.2 = l.2 - ∑ i, (a i : Fv F v) • (L i).2 := by simp [m, Prod.snd_sum]
  have key : u ⬝ᵥ l.2 - l.1 ⬝ᵥ y' = u ⬝ᵥ m.2 := by
    rw [hy, hm2, dotProduct_sub, dotProduct_sum]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.map_smul, hgb, dotProduct_smul]
  rw [key]
  apply hu
  have : ((0 : κ → Fv F v), m.2) = m := Prod.ext hm1.symm rfl
  rw [this]; exact hm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponents
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section
namespace GlobalTheory.SplitComps

open GlobalTheory.EmbChart (atPlace tensAt compFin_tensAt tensAt_mul_right)

theorem exists_mat_comps : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)) (τ : E →ₐ[F] Fv F v) {m n : Type} (P₀ P₁ : Matrix m n (Fv F v)), ∃ u : Matrix m n (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) u ∧ u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW τ) = P₀ ∧ u.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.piW (τ.comp σ)) = P₁ := by
  intro F E _ _ _ _ _ σ h v τ m n P₀ P₁
  refine ⟨Matrix.of fun i j => tensAt E v ((splitAlgEquiv h τ).symm (P₀ i j, P₁ i j)), ?_, ?_, ?_⟩
  · intro a ha
    ext i j
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.zero_apply]
    rw [Algebra.smul_def, mul_comm, tensAt_mul_right]
    have : compFin F E v (algebraMap (AF F) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) a) = 0 := by
      change evFin F v a ⊗ₜ[F] (1 : E) = 0
      rw [ha, TensorProduct.zero_tmul]
    rw [this, mul_zero, map_zero]
  · refine Matrix.ext fun i j => ?_
    rw [Matrix.map_apply, Matrix.of_apply]
    change splitProj τ (compFin F E v (tensAt E v _)) = _
    rw [compFin_tensAt, splitProj_symm]
  · refine Matrix.ext fun i j => ?_
    rw [Matrix.map_apply, Matrix.of_apply]
    change splitProj (τ.comp σ) (compFin F E v (tensAt E v _)) = _
    rw [compFin_tensAt, splitProj_comp_symm]

end GlobalTheory.SplitComps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTrigPolynomialIndicatorAwayFromPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trigPolynomial_indicator_awayFromPlace : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F))
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → (∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), ∃ t, GlobalTheory.LatVac.psiAt ψ w t ≠ 1) →
    ∀ K : Set (κ → Af F), IsCompact K → ∀ (y : κ → AF F) (V : Set (κ → Af F)), IsOpen V → (fun i => (y i).2) ∈ V →
    ∃ (A : Set (κ → Af F)) (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ),
      IsOpen A ∧ (fun i => (y i).2) ∈ A ∧ (∀ b ∈ s, GlobalTheory.LatVac.liftV v 1 • b = 0) ∧
      (∀ x z : κ → AF F, GlobalTheory.LatVac.liftV v 1 • z = z →
        ((fun i => ((x + z) i).2) ∈ A ↔ (fun i => (x i).2) ∈ A)) ∧
      (∀ x : κ → AF F, (fun i => (x i).2) ∈ A →
        (fun i => ((x + (GlobalTheory.LatVac.liftV v 1 • y - GlobalTheory.LatVac.liftV v 1 • x)) i).2) ∈ V) ∧
      ∀ x : κ → AF F, (fun i => (x i).2) ∈ K →
        ∑ b ∈ s, c b * ψ (x ⬝ᵥ b) = A.indicator (fun _ => (1 : ℂ)) (fun i => (x i).2) := by
  first | exact @GlobalTheory.OffVTrig.exists_offV_indicator_poly | exact GlobalTheory.OffVTrig.exists_offV_indicator_poly | (intros; apply GlobalTheory.OffVTrig.exists_offV_indicator_poly <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceTensorLatticeSelfDualSymplectic
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

namespace GlobalTheory.InertLatSelfDual

theorem latAtV_selfDual_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E), B.IsGood σ →
    ∀ {n d : ℕ} (X : Spc F E n) (Y : Spc F E d) (r s r' s' : ℕ), X.IsHerm σ B r s → Y.IsSkew σ B r' s' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ z : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) z →
      (z ∈ latAtV X Y v ↔ ∀ γ ∈ latAtV X Y v,
        B.ψ (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) Y.J) z γ) = 1) := by
  intro F E _ _ _ _ _ σ B hB n d X Y r s r' s' hX hY v _w _hin z hz
  exact GlobalTheory.LatSelfDualAll.latAtV_selfDual F E σ B n d X Y r s r' s' hB hX hY v z hz

end GlobalTheory.InertLatSelfDual
end

