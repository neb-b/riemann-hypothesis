module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRepsOfFiniteIndex
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0156
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0203
public import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0205
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0986
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0990
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0907
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0775
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0764
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1625
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeExtensionAlongFieldEmbeddingDuals
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarmonicPolynomialEqZeroOfFunction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Formalism.LocalToGlobal.Columns.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0784
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0783
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNormalisedDataNormalCoefficientField
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.PinsNormal

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levJ_eq (R : RealDat D A Ks) (i : Fin D.R.m) {t t' : T0} (e : R.Q t' = R.Q t) : levJ R i t' = levJ R i t := by
  have key : ∀ (Q Q' : Finset (Pl D.host.E)) (ξ ξ' : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), Q = Q' →
      lev D.sp.cm (Vc D i).gram (R.βV i) (Lev.flag1L (Lev.datY _ D.R.r D.R.t 1 (r_le_V i) R.Pg Q (LevelP.triv _ _ _)
        (fun _ => R.chi ((i : ℕ) + 1)) ξ Lev.Frm.A)) =
      lev D.sp.cm (Vc D i).gram (R.βV i) (Lev.flag1L (Lev.datY _ D.R.r D.R.t 1 (r_le_V i) R.Pg Q' (LevelP.triv _ _ _)
        (fun _ => R.chi ((i : ℕ) + 1)) ξ' Lev.Frm.A)) := by
    rintro Q _ ξ ξ' rfl
    exact Subgroup.ext fun x => Iff.rfl
  have h := key _ _ (R.xiR t') (R.xiR t) e
  unfold levJ levEnv
  exact congrArg (fun K => (Lev.toAfE (Vc D i) K).comap (finHom (Vc D i)).range.subtype) h

theorem repsR_of_eq (R : RealDat D A Ks) (i : Fin D.R.m) {t t' : T0} (e : R.Q t' = R.Q t) {K' : Type} [Field K'] {Cl : Type} [Fintype Cl]
    {h : Cl → GA D (Vc D i)} {bad : ℕ} {J' : Subgroup (Bridge.Gf (Vc D i))}
    {Lh : Cl → Submodule (𝓞 D.host.E) (Fin (Vc D i).rank → D.host.E)} {gam : Cl → ℕ} {vol : K'}
    (H : RepsR R i t' h bad J' Lh gam vol) : RepsR R i t h bad J' Lh gam vol := by
  unfold RepsR at H ⊢
  rwa [levJ_eq R i e, e] at H

theorem extC_down (R : RealDat D A Ks) (i : Fin D.R.m) {K₁ K₂ : Type} [Field K₁] [Field K₂] (j₁ : D.what₂.LL →+* K₁) (j₂ : D.what₂.LL →+* K₂)
    (σ₁ : K₁ →+* ℂ) (σ₂ : K₂ →+* ℂ) (h₁ : σ₁.comp j₁ = D.what₂.embLL) (h₂ : σ₂.comp j₂ = D.what₂.embLL)
    (hs : Function.Surjective j₁) (c0 : VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W)
    (a₁ : VsV D i K₁ →ₛₗ[σ₁] (R.cV i).W) (a₂ : VsV D i K₂ →ₛₗ[σ₂] (R.cV i).W)
    (H₁ : CoefficientBaseChange R i j₁ σ₁ c0 a₁) (H₂ : CoefficientBaseChange R i j₂ σ₂ c0 a₂) (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W)
    (hc : ExtC R i σ₂ a₂ c) : ExtC R i σ₁ a₁ c := by
  intro v v' e
  let ε : K₁ ≃+* D.what₂.LL := (RingEquiv.ofBijective j₁ ⟨j₁.injective, hs⟩).symm
  have hε : j₁.comp (ε : K₁ →+* D.what₂.LL) = RingHom.id K₁ := RingHom.ext fun x => (RingEquiv.ofBijective j₁ ⟨j₁.injective, hs⟩).apply_symm_apply x
  let u : VsV D i D.what₂.LL := ⟨MvPolynomial.map (ε : K₁ →+* D.what₂.LL) (v : Pol K₁ D.what₂.Tau (Vc D i).rank),
    Formalism.L2.Ker.map_mem_VV _ _ _ v.2⟩
  obtain ⟨w₁, e₁, f₁⟩ := H₁ u
  obtain ⟨w₂, e₂, f₂⟩ := H₂ u
  have hw : w₁ = v := Subtype.ext (by
    rw [e₁]
    change MvPolynomial.map j₁ (MvPolynomial.map (ε : K₁ →+* D.what₂.LL) (v : Pol K₁ D.what₂.Tau (Vc D i).rank)) = _
    rw [MvPolynomial.map_map, hε, MvPolynomial.map_id])
  rw [← hw, f₁, ← f₂]
  refine hc w₂ v' ?_
  rw [e, e₂, MvPolynomial.map_map, h₂, ← hw, e₁, MvPolynomial.map_map, h₁]

theorem exists_normal_coeff {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) :
    ∃ c' : Coeff l, c.F ≤ c'.F ∧ Normal ℚ c'.F := by
  have := c.fin
  have hle : c.F ≤ IntermediateField.normalClosure ℚ c.F ℂ := IntermediateField.le_normalClosure c.F
  have : IsNormalClosure ℚ c.F (IntermediateField.normalClosure ℚ c.F ℂ) :=
    Algebra.IsAlgebraic.isNormalClosure_normalClosure fun x => IsAlgClosed.splits _
  exact ⟨⟨IntermediateField.normalClosure ℚ c.F ℂ, inferInstance, fun τ a => hle (c.conj τ a), hle c.zeta_mem,
    c.le.trans hle⟩, hle, IsNormalClosure.normal (F := ℚ) (K := c.F) (L := IntermediateField.normalClosure ℚ c.F ℂ)⟩


set_option maxHeartbeats 4000000 in
theorem exists_pins_normal : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)), GlobalTheory.Hk3.Core R F → Finite T0 → Nonempty (FWTie T R κ v₀) → QGuard R → ∀ i : Fin D.R.m, OMPins T R κ v₀ O i → ∃ M : OMDat T.toCore R i T0 id, M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) ∧ M.lev = (O i).lev ∧ (∀ c, ExtC R i (inC (O i).c') (O i).c0' c ↔ ExtC R i (inC M.c') M.c0' c) ∧ Normal ℚ M.c'.F ∧ GlobalTheory.CompRat.CurveOver T.Q.H M.c'.F 1 ∧ (∀ t x, ((R.xi t x : Circle) : ℂ) ∈ M.c'.F) ∧ ∀ t t' : T0, R.Q t' = R.Q t → ∃ e, SameCover M t t' e := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ O hC hfin hfw hG i hO
  obtain ⟨fw⟩ := id hfw
  have hT := fw.laws
  have hL : R.toLevCh.Is A.μ0 := hC.lev
  have hchi : R.grp_chiW := hC.grp.chiW
  have hfam := hC.fam
  have hmodels := hC.models
  have hvP : R.thP_vP := hC.thP.vP
  obtain ⟨hpb, hV, hlev⟩ := _root_.GlobalTheory.BasePins.orient_std_lev D G Pl0 T0 A T R κ v₀ O hL hT i hO
  obtain ⟨gramR, c0R, c0L, htie, hc0O⟩ := hO.2.lift.c0
  haveI : Nonempty T0 := ⟨A.μ0⟩
  let rep : T0 → T0 := fun t => Function.invFun R.Q (R.Q t)
  have hrepQ : ∀ t, R.Q (rep t) = R.Q t := fun t => Function.invFun_eq (f := R.Q) ⟨t, rfl⟩
  have hrepE : ∀ t t' : T0, R.Q t' = R.Q t → rep t' = rep t := fun t t' e => congrArg (Function.invFun R.Q) e
  choose pd l₂ h1 h2 using fun t => GlobalTheory.CoverHalf.exists_half_of_laws T.toCore R hT.toLawsM hL hpb hG t
  obtain ⟨c₁, hc1a, hc1b, hc1xi, hc⟩ := GlobalTheory.OneCover.exists_covers_rep T R hT hL i (Vc D i).rank pd
    (fun t => GlobalTheory.CoverHalf.coverHalf D (R.Q t)) l₂ h1 h2 rep hrepQ
  choose Mφ hMφ hφ using fun t => GlobalTheory.T.exists_level_place_datum_over_number_field D G Pl0 T0 A _ R hL hvP i hV t _ (iotaW T i)
    (GlobalTheory.PinnedDataGiven.latEmb_iotaW T hT i)
  choose MB hMB hB using fun t => _root_.GlobalTheory.Mem.BVal.exists_field_BIs D G Pl0 T0 A _ R hL i t
  have := c₁.fin
  obtain ⟨c₂, hc₂⟩ := GlobalTheory.TupleCover.exists_coeff_ge T.Q.l (c₁.F ⊔ ⨆ t, (Mφ t ⊔ MB t))
  obtain ⟨c₃, hc₃, hcurve⟩ := GlobalTheory.CurveField.exists_coeff_curveOver _ T.Q.H T.Q.l c₂ 1 one_pos
  obtain ⟨c', hc', hnorm⟩ := exists_normal_coeff c₃
  have h23 : c₂.F ≤ c'.F := hc₃.trans hc'
  have h3 : c₁.F ≤ c'.F := (le_sup_left.trans hc₂).trans h23
  have h4 : ∀ t, Mφ t ⊔ MB t ≤ c'.F := fun t =>
    (((le_iSup (fun t => Mφ t ⊔ MB t) t).trans le_sup_right).trans hc₂).trans h23
  have hle : T.Q.c.F ≤ c'.F := hc1a.trans h3
  have hLL := hc1b.trans h3
  obtain ⟨d, U, dict, f, xi, -, hcov, hhalf, hxi, hcxi, hmod⟩ := hc c' hle h3
  let dδ : T0 → DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' (Vc D i).rank := fun t => { d (rep t) with cδ := f t }
  let jL : D.what₂.LL →+* c'.F := D.what₂.embLL.codRestrict c'.F fun x => hLL ⟨x, rfl⟩
  have hjL : (inC c').comp jL = D.what₂.embLL := RingHom.ext fun _ => rfl
  obtain ⟨c0', hc0, hplace⟩ := _root_.GlobalTheory.Div.CoefExtension.exists_ext_placeEx D G Pl0 T0 A _ R hL hchi hfam hmodels gramR c0R c0L htie i c'.F jL (inC c') hjL
  obtain ⟨Cl, fCl, h, J', bad, Lh, gam, vol, La, Nc, hrep, hbad, hcl⟩ :=
    GlobalTheory.SplitReps.exists_repsR_repsCov R i (hL.βV i) hV c'.F (T.Q.Xo ((i : ℕ) + 1)) c' id d
  have hrepR : ∀ t, RepsR R i t (h (rep t)) (bad (rep t)) (J' (rep t)) (Lh (rep t)) (gam (rep t)) (vol (rep t)) :=
    fun t => repsR_of_eq R i (hrepQ t) (hrep (rep t)).1
  choose B hBis using fun t => hB t c'.F (le_sup_right.trans (h4 t)) (bad (rep t)) (hbad (rep t)).2.2.2.2
    fun PP hPP => (hrepR t).2.1 PP (Or.inr hPP)
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
    (bad (rep t)) (B t)).2 fun L cc g d => _root_.GlobalTheory.LawOfSquares.law_of_squares _ _ _ _ hodd L cc g.1 g.2.2 d.1 d.2
  obtain ⟨io, hw, hio⟩ := _root_.GlobalTheory.CoefMapRecord.exists_io_record D T.Q hT.pins κ fw.kap i c'
  choose φ hφis using fun t => hφ t c'.F (le_sup_left.trans (h4 t)) (hhalf t).2.2 (Mfr (dδ t).l₂) fun PP hPP c hc => by
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
  choose thAd hth using fun t => _root_.GlobalTheory.AdelicSide.exists_thAd_of_models D G Pl0 T0 A _ R hmodels i t _ _ c0' _ (h (rep t)) _ (hrepR t).2.2.1
    (hrepR t).2.2.2.2.2.1 (v₀ i (sg0 D A))
  have hact := fun c => GlobalTheory.T.levelAction_framedPoints_isAction D G Pl0 T0 A T R hL hT hpb i c (O i).lev hlev
  let M : OMDat T.toCore R i T0 id :=
    { c' := c', hle := hle, jL := jL, hV := hT.spaceW _ (inR i) _ rfl, c0' := c0', lev := (O i).lev, dδ := dδ,
      Cl' := fun t => Cl (rep t), fCl := fun t => fCl (rep t),
      bad := fun t => bad (rep t), Lh := fun t => Lh (rep t), La := fun t => La (rep t), Nc := fun t => Nc (rep t),
      gam := fun t => gam (rep t), vol := fun t => vol (rep t), ep := fun t k => epF t (Lh (rep t) k), B := B,
      epF := epF, io := io, hw := hw, φ := φ,
      w := fun t _ q => (dδ t).eF.symm (phiHat (dδ t).c₂ (fun x => (dδ t).eF (φ t x)) q),
      U₂ := fun t => U (rep t), dict₂ := fun t => dict (rep t), xi := xi, thAd := thAd,
      Plc := fun t x => ∃ x₀, Place R i t (h (rep t)) c0' (jVx R i t x₀) x }
  have hMP : M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) :=
    ⟨⟨hjL, hV, fw.hv₀ i _, ⟨gramR, c0R, c0L, htie, hc0⟩, hlev⟩,
      fun t => ⟨⟨h (rep t), J' (rep t), hrepR t, hplace t _ _, hth t, fun _ => Iff.rfl⟩, hBis t, hxi t, hφis t, hhalf t⟩,
      ⟨hact _, hact _⟩, fun t => hbad (rep t), fun t => hcl (rep t), fun t => ⟨fun _ => rfl, hepF t⟩, hio,
      fun t k q => AlgEquiv.apply_symm_apply _ _, hcov, hcxi, hmod⟩
  refine ⟨M, hMP, rfl, ?_, hnorm, hcurve c' hc', fun t x => h3 (hc1xi t x), fun t t' e => ?_⟩
  · obtain ⟨cM, hcM, -, huM⟩ := _root_.GlobalTheory.CoefExtC.exists_extC_bijective_unique D G Pl0 T0 A T R F κ v₀ hC ⟨fw⟩ i T0 id M hMP
    obtain ⟨cO, -, -, huO⟩ := _root_.GlobalTheory.CoefExtC.exists_extC_bijective_unique D G Pl0 T0 A T R F κ v₀ hC ⟨fw⟩ i Unit (fun _ => A.μ0) (O i) hO.2
    have hsurj : Function.Surjective (O i).jL := by
      intro x
      have hx : (x : ℂ) ∈ D.what₂.embLL.toRatAlgHom.fieldRange := hO.1 ▸ x.2
      obtain ⟨y, hy⟩ := hx
      refine ⟨y, Subtype.ext ?_⟩
      have := RingHom.congr_fun hO.2.lift.field y
      exact this.trans hy
    have hsame : ExtC R i (inC (O i).c') (O i).c0' cM :=
      extC_down R i (O i).jL jL (inC (O i).c') (inC c') hO.2.lift.field hjL hsurj (c0L i) (O i).c0' c0' hc0O hc0 cM hcM
    have e0 : cM = _ := huO cM hsame
    intro c
    constructor
    · intro hc'
      rw [huO c hc', ← e0]
      exact hcM
    · intro hc'
      rw [huM c hc']
      exact hsame
  · have er : rep t' = rep t := hrepE t t' e
    have key : ∀ a b : T0, a = b → ∀ (fa : Rul (d a).Xo₂ (d a).c₂) (fb : Rul (d b).Xo₂ (d b).c₂),
        ∃ cx : Rul (d b).Xo₂ (d b).c₂, ({ d a with cδ := fa } : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' (Vc D i).rank) =
          { ({ d b with cδ := fb } : DeltaDat (T.Q.Xo ((i : ℕ) + 1)) c' (Vc D i).rank) with cδ := cx } := by
      rintro a _ rfl fa fb
      exact ⟨fa, rfl⟩
    have keyK : ∀ {β : Type} (g : ∀ a, Cl a → β) (a b : T0) (hab : a = b) (k : Cl a), g b (cast (congrArg Cl hab) k) = g a k := by
      rintro β g a _ rfl k
      rfl
    refine ⟨Equiv.cast (congrArg Cl er.symm), key _ _ er (f t') (f t), congr_arg_heq U er, congr_arg_heq dict er,
      congrArg bad er, congrArg vol er, fun k => ⟨keyK Lh _ _ er.symm k, keyK La _ _ er.symm k, keyK Nc _ _ er.symm k,
      keyK gam _ _ er.symm k⟩⟩

end GlobalTheory.PinsNormal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockHarmonicLatticeFgAndSpansValueSpace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.IndefR.Links (PolF)
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExportSeries.HarmLattice

theorem fg_span_comap {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (O : Subring ℂ)
    (H : Submodule ℂ V) (f : V →ₗ[ℂ] W) (hinj : ∀ P ∈ H, f P = 0 → P = 0) (L : Submodule O W) (hfg : L.FG)
    (hsp : Submodule.span ℂ (L : Set W) = H.map f) :
    (H.restrictScalars O ⊓ L.comap (f.restrictScalars O)).FG ∧
      Submodule.span ℂ ((H.restrictScalars O ⊓ L.comap (f.restrictScalars O) : Submodule O V) : Set V) = H := by
  have him : f '' ((H.restrictScalars O ⊓ L.comap (f.restrictScalars O) : Submodule O V) : Set V) = L := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx.2
    · intro hy
      have : y ∈ H.map f := hsp ▸ Submodule.subset_span hy
      obtain ⟨x, hx, rfl⟩ := this
      exact ⟨x, ⟨hx, hy⟩, rfl⟩
  constructor
  · refine Submodule.fg_of_fg_map_of_fg_inf_ker (f.restrictScalars O) ?_ ?_
    · have : (H.restrictScalars O ⊓ L.comap (f.restrictScalars O)).map (f.restrictScalars O) = L :=
        SetLike.coe_injective him
      rw [this]
      exact hfg
    · have : (H.restrictScalars O ⊓ L.comap (f.restrictScalars O)) ⊓ LinearMap.ker (f.restrictScalars O) = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        exact hinj x hx.1.1 hx.2
      rw [this]
      exact Submodule.fg_bot
  · have hle : Submodule.span ℂ ((H.restrictScalars O ⊓ L.comap (f.restrictScalars O) : Submodule O V) : Set V) ≤ H :=
      Submodule.span_le.2 fun x hx => hx.1
    refine le_antisymm hle fun x hx => ?_
    have : f x ∈ (Submodule.span ℂ ((H.restrictScalars O ⊓ L.comap (f.restrictScalars O) : Submodule O V) : Set V)).map f := by
      rw [Submodule.map_span, him, hsp]
      exact Submodule.mem_map_of_mem hx
    obtain ⟨y, hy, e⟩ := this
    have h0 : x - y = 0 := hinj _ (sub_mem hx (hle hy)) (by rw [map_sub, e, sub_self])
    rw [sub_eq_zero.1 h0]
    exact hy

variable {D : D7} {n : ℕ}

def cf (lam : D.what₂.Tau → DomWeight n) : VV ℂ lam →ₗ[ℂ] (GLR D n → ℂ) where
  toFun F := coefFn (RingHom.id ℂ) lam (F : Pol ℂ D.what₂.Tau n)
  map_add' F G := by
    funext x
    simp only [coefFn, Submodule.coe_add, map_add (f := _), Pi.add_apply, mul_add]
  map_smul' c F := by
    funext x
    simp only [coefFn, Submodule.coe_smul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval₂Hom_C, RingHom.id_apply,
      Pi.smul_apply, smul_eq_mul]
    ring

theorem coefFn_eq {K : Type} [Field K] (σ : K →+* ℂ) (lam : D.what₂.Tau → DomWeight n) (F : VV K lam) :
    coefFn σ lam (F : Pol K D.what₂.Tau n) = cf lam (GlobalTheory.CoefModel.mapVV σ lam F) := by
  funext x
  change _ = coefFn (RingHom.id ℂ) lam (MvPolynomial.map σ F.1) x
  simp only [coefFn, MvPolynomial.eval₂Hom_map_hom, RingHom.id_comp]

variable {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ} {emb : D.what₂.Tau → (D.host.E →+* K)} {O : Subring ℂ}

private theorem nabAtr_full (lam : D.what₂.Tau → DomWeight n)
    {M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hM : Submodule.IsFullLattice D.host.E M) :
    Submodule.IsFullLattice K (nabAtr emb lam M) := by
  classical
  refine nb_lattice (nb_comm_nab lam) _ fun τ => ?_
  obtain ⟨m, x, ξ, hx, hξ, h⟩ := GlobalTheory.TauLat.exists_dual_family M hM
  let e (z : Fin n → D.host.E) (a : Fin n) : K := emb τ (z a)
  have hx' (i : Fin m) : e (x i) ∈ tauLat emb τ M :=
    Submodule.subset_span ⟨x i, hx i, rfl⟩
  have hξ' (i : Fin m) : e (ξ i) ∈ dualFr (tauLat emb τ M) := by
    intro y hy
    change y ∈ Submodule.span (𝓞 K) (e '' (M : Set (Fin n → D.host.E))) at hy
    induction hy using Submodule.span_induction with
    | mem _ hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      change (fun a => emb τ (ξ i a)) ⬝ᵥ (fun a => emb τ (z a)) ∈ _
      rw [← GlobalTheory.TauLat.map_dot]
      exact du_map_mem_one _ ((GlobalTheory.TauLat.mem_one_iff _).2 (hξ i z hz))
    | zero => rw [dotProduct_zero]; exact zero_mem _
    | add _ _ _ _ hy hz => rw [dotProduct_add]; exact add_mem hy hz
    | smul c _ _ hy => rw [dotProduct_smul]; exact Submodule.smul_mem _ c hy
  have hexpand (y : Fin n → K) :
      y = ∑ i, (y ⬝ᵥ e (x i)) • e (ξ i) := by
    simpa only [dotProduct_comm y, e] using GlobalTheory.TauLat.expand_left (emb τ) h y
  refine { toIsLattice := Submodule.IsLattice.of_fg K ?_, span_eq_top := ?_ }
  · refine ⟨Finset.univ.image (fun i => e (ξ i)), le_antisymm ?_ ?_⟩
    · rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, Submodule.span_le, Set.range_subset_iff]
      exact hξ'
    · intro y hy
      rw [hexpand y]
      exact Submodule.sum_mem _ fun i _ =>
        du_smul_of_mem_one _ (hy _ (hx' i)) (Submodule.subset_span (by simp))
  · rw [eq_top_iff]
    intro y _
    rw [hexpand y]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hξ' i))

theorem coefLatFn_fg (hc : IsCoefRing σ emb O) (lam : D.what₂.Tau → DomWeight n)
    {M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hM : Submodule.IsFullLattice D.host.E M) :
    (coefLatFn σ emb O lam M).FG := by
  obtain ⟨s, hs, e⟩ := Submodule.fg_def.1 (nabAtr_full (emb := emb) lam hM).fg
  refine Submodule.fg_def.2 ⟨(fun F => cf lam (GlobalTheory.CoefModel.mapVV σ lam F)) '' s, hs.image _, le_antisymm ?_ ?_⟩
  · refine Submodule.span_mono ?_
    rintro _ ⟨F, hF, rfl⟩
    exact ⟨F, e ▸ Submodule.subset_span hF, (coefFn_eq σ lam F).symm⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨F, hF, rfl⟩
    rw [coefFn_eq, SetLike.mem_coe]
    rw [← e] at hF
    induction hF using Submodule.span_induction with
    | mem F h => exact Submodule.subset_span ⟨F, h, rfl⟩
    | zero => rw [map_zero, map_zero]; exact zero_mem _
    | add _ _ _ _ h1 h2 => rw [map_add (f := _), map_add (f := _)]; exact add_mem h1 h2
    | smul a F _ h1 =>
      rw [← algebraMap_smul K a F, LinearMap.map_smulₛₗ, map_smul]
      exact Submodule.smul_mem _ (⟨σ a, hc.int a⟩ : O) h1

theorem span_coefLatFn (lam : D.what₂.Tau → DomWeight n)
    {M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hM : Submodule.IsFullLattice D.host.E M) :
    Submodule.span ℂ (coefLatFn σ emb O lam M : Set (GLR D n → ℂ)) =
      Submodule.span ℂ {φ | ∃ F : VV ℂ lam, φ = coefFn (RingHom.id ℂ) lam (F : Pol ℂ D.what₂.Tau n)} := by
  rw [coefLatFn, Submodule.span_span_of_tower]
  refine le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨F, -, rfl⟩
    exact ⟨_, coefFn_eq σ lam F⟩
  · rintro _ ⟨F, rfl⟩
    have key : ∀ G : VV K lam, cf lam (GlobalTheory.CoefModel.mapVV σ lam G) ∈
        Submodule.span ℂ {φ | ∃ F ∈ nabAtr emb lam M, φ = coefFn σ lam (F : VV K lam)} := by
      intro G
      have hG : G ∈ Submodule.span K (nabAtr emb lam M : Set (VV K lam)) := by
        rw [(nabAtr_full (emb := emb) lam hM).span_eq_top]
        exact Submodule.mem_top
      induction hG using Submodule.span_induction with
      | mem F h => exact Submodule.subset_span ⟨F, h, (coefFn_eq σ lam F).symm⟩
      | zero => rw [map_zero, map_zero]; exact zero_mem _
      | add _ _ _ _ h1 h2 => rw [map_add (f := _), map_add (f := _)]; exact add_mem h1 h2
      | smul a F _ h1 =>
        rw [LinearMap.map_smulₛₗ, map_smul]
        exact Submodule.smul_mem _ _ h1
    have hF : F ∈ Submodule.span ℂ (Set.range fun i => GlobalTheory.CoefModel.mapVV σ lam (bVV K lam i)) := by
      rw [GlobalTheory.CoefModel.span_mapVV]; trivial
    change cf lam F ∈ _
    have := Submodule.mem_map_of_mem (f := cf lam) hF
    rw [Submodule.map_span] at this
    refine Submodule.span_le.2 ?_ this
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact key _

theorem harmLat_fg_span : ∀ (D : D7) (m n : ℕ) (w : Weight D n) (B : GLR D n) (K : Type) [Field K] [NumberField K] (σ : K →+* ℂ) (emb : D.what₂.Tau → (D.host.E →+* K)) (O : Subring ℂ) (M : Submodule (𝓞 D.host.E) (Fin n → D.host.E)), w.Good → (∀ τ, w.p τ + w.q τ ≤ m) → IsCoefRing σ emb O → Submodule.IsFullLattice D.host.E M → (harmLat σ emb O m w B M).FG ∧ Submodule.span ℂ (harmLat σ emb O m w B M : Set (PolF D m n)) = harm m w B := by
  intro D m n w B K _ _ σ emb O M hw hm hc hM
  exact fg_span_comap O (harm m w B) (harmFn m w B) (_root_.GlobalTheory.ExportSeries.HarmInj.harm_inj D m n w B hw hm) _ (coefLatFn_fg hc w.lam hM)
    ((span_coefLatFn w.lam hM).trans (GlobalTheory.T.fockHarmonicValueSpace_map_eq_dualWeylModuleFunctions D m n w B hw hm).symm)

end GlobalTheory.ExportSeries.HarmLattice

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockSubstitutionHomogeneousCoeffMemAfterScaling
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.FockCoefInt

open MvPolynomial

def coeffSub (O : Subring ℂ) (σ : Type) : Subring (MvPolynomial σ ℂ) where
  carrier := {Q | ∀ mo, Q.coeff mo ∈ O}
  mul_mem' {a b} ha hb mo := by
    rw [coeff_mul]; exact O.sum_mem fun x _ => O.mul_mem (ha _) (hb _)
  one_mem' mo := by
    rw [coeff_one]; split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  add_mem' {a b} ha hb mo := by rw [MvPolynomial.coeff_add]; exact O.add_mem (ha mo) (hb mo)
  zero_mem' mo := by rw [AddMonoidAlgebra.coeff_zero]; exact O.zero_mem
  neg_mem' {a} ha mo := by rw [coeff_neg]; exact O.neg_mem (ha mo)

theorem C_mem_coeffSub {O : Subring ℂ} {σ : Type} {c : ℂ} (hc : c ∈ O) : (C c : MvPolynomial σ ℂ) ∈ coeffSub O σ := by
  intro mo
  rw [coeff_C]; split_ifs
  · exact hc
  · exact O.zero_mem

theorem C_pow_mul_aeval_mem {σ : Type} (O : Subring ℂ) (z : ℂ) (g : σ → MvPolynomial σ ℂ)
    (hg : ∀ v, C z * g v ∈ coeffSub O σ) (d : ℕ) (P : MvPolynomial σ ℂ) (hP : P.IsHomogeneous d)
    (hc : P ∈ coeffSub O σ) : C (z ^ d) * aeval g P ∈ coeffSub O σ := by
  rw [P.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.mul_sum]
  refine Subring.sum_mem _ fun mo hmo => ?_
  have hdeg : ∑ v ∈ mo.support, mo v = d := by
    have := hP (mem_support_iff.mp hmo)
    rw [← this, Finsupp.weight_apply, Finsupp.sum]
    simp
  rw [aeval_monomial, ← hdeg, Finsupp.prod, ← Finset.prod_pow_eq_pow_sum, map_prod, mul_left_comm,
    ← Finset.prod_mul_distrib]
  simp_rw [map_pow, ← mul_pow]
  refine Subring.mul_mem _ ?_ (Subring.prod_mem _ fun v _ => Subring.pow_mem _ ?_ _)
  · rw [algebraMap_eq]; exact C_mem_coeffSub (hc mo)
  · exact hg v

theorem fockSubst_coeff_mem : ∀ (D : D7) (m n : ℕ) (p : D.what₂.Tau → ℕ) (u : GlobalTheory.ExportSeries.GLR D n) (O : Subring ℂ) (z : ℂ),
    (∀ τ x y, z * (((u τ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) x y ∈ O ∧
      z * ((u τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) x y ∈ O) →
    ∀ (d : ℕ) (P : MvPolynomial (FVar D m n) ℂ), P.IsHomogeneous d → (∀ mo, P.coeff mo ∈ O) →
      ∀ mo, z ^ d * (GlobalTheory.ExportSeries.fockSubst p u P).coeff mo ∈ O := by
  intro D m n p u O z hu d P hP hc mo
  rw [GlobalTheory.ExportSeries.fockSubst, ← coeff_C_mul]
  refine C_pow_mul_aeval_mem O z _ ?_ d P hP hc mo
  · intro v
    split_ifs
    all_goals
      rw [Finset.mul_sum]
      refine Subring.sum_mem _ fun b _ => ?_
      rw [← mul_assoc, ← map_mul]
      intro mo'
      rw [coeff_C_mul, coeff_X']
      split_ifs
      · rw [mul_one]; first | exact (hu _ _ _).1 | exact (hu _ _ _).2
      · rw [mul_zero]; exact O.zero_mem

end GlobalTheory.FockCoefInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceInvariantFormsSeparateThetaFunctionsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_invariantForms_separate_thetaFunctions : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ a : AE D, IsSplitIdem D a → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ ℓ, InvForm ψ S T a ℓ → ∀ x, IsHalf a x → ℓ (heisO ψ S T x f) = 0) → f = 0 := by
  first | exact @GlobalTheory.DownLift.SplitSep.invForms_separate | exact GlobalTheory.DownLift.SplitSep.invForms_separate | (intros; apply GlobalTheory.DownLift.SplitSep.invForms_separate <;> assumption)
end

