module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0039
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2534
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2522
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2730
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2834
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1646
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresenta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0224
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1186
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBottomPairBigMemberTwistedTuple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2835
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1204
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1837
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1704
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1718
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetIndicatorReadsAsTranslateCurveTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1677
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1762
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1670
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1749
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1148
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1136
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1221
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2802
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1205
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2812
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithVarietyReciprocityAtComplexEmbedding
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.MixRec

theorem injective_of_finite_int {k : Type} [CommRing k] [IsDomain k] [Module.Finite ℤ k]
    (σ : k →+* ℂ) : Function.Injective σ := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  have hker : RingHom.ker σ = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
    rw [eq_bot_iff]
    intro n hn
    rw [Ideal.mem_comap, RingHom.mem_ker, eq_intCast, map_intCast, Int.cast_eq_zero] at hn
    simp [hn]
  intro a ha
  have : a ∈ RingHom.ker σ := ha
  rwa [hker, Ideal.mem_bot] at this

theorem exists_extension {k : Type} [CommRing k] [IsDomain k] [Module.Finite ℤ k]
    (K : Type) [Field K] [Algebra k K] [IsFractionRing k K] (σ : k →+* ℂ) :
    ∃ τ : K →+* ℂ, σ = τ.comp (algebraMap k K) :=
  ⟨IsFractionRing.lift (A := k) (K := K) (injective_of_finite_int σ),
    RingHom.ext fun x => (IsFractionRing.lift_algebraMap (K := K) (injective_of_finite_int σ) x).symm⟩

theorem side_symm : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (e : ℕ), IsArithVar p (e + 1) → ∀ (σ : k →+* ℂ) (L : Fin e → MLine p σ) (M N : MLine p σ) (s : M.B.Sec) (hs : genericPoint X ∈ nonzeroLocus s) (t : N.B.Sec) (ht : genericPoint X ∈ nonzeroLocus t), (∀ z : X, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → side N L (M.logSec s) (N.logSec t) (divOfSec M.φ.isLB s hs) = side M L (N.logSec t) (M.logSec s) (divOfSec N.φ.isLB t ht) := by
  intro hP k _ X _ _ p e h σ
  haveI := h.isDomain
  haveI := h.finite
  obtain ⟨K, _, _, _⟩ : ∃ (K : Type) (_ : Field K) (_ : Algebra k K), IsFractionRing k K :=
    ⟨FractionRing k, inferInstance, inferInstance, inferInstance⟩
  obtain ⟨τ, hτ⟩ := exists_extension K σ
  subst hτ
  intro L M N s hs t ht hcod
  obtain ⟨G, j, q, hp⟩ : ∃ (G : Scheme.{0}) (j : G ⟶ X) (q : G ⟶ Sp K),
      IsPullback j q p (spMap (algebraMap k K)) := ⟨_, _, _, IsPullback.of_hasPullback _ _⟩
  obtain ⟨hGi, hGn, hproj, hdim, hgen, -, hstalk, hcoh, -⟩ :=
    _root_.GlobalTheory.Mix.genericFibre_facts k K X G p q j hp (e + 1) h
  obtain ⟨s', hs', hsl, hsm, hslog⟩ := _root_.GlobalTheory.Mix.exists_sec_bc k K X G p q j hp τ hstalk M s hs hgen
  obtain ⟨t', ht', htl, htm, htlog⟩ := _root_.GlobalTheory.Mix.exists_sec_bc k K X G p q j hp τ hstalk N t ht hgen
  have hcod' : ∀ z : G, Order.coheight z = 1 → z ∈ nonzeroLocus s' ∨ z ∈ nonzeroLocus t' := by
    intro z hz
    rw [hsl, htl]
    exact hcod (j z) ((hcoh z).trans hz)
  have hrec := _root_.GlobalTheory.Mix.reciprocity_of_noCommonDivisor hP K G q τ e hproj hdim (fun i => (L i).bc hp.w τ) (M.bc hp.w τ)
    (N.bc hp.w τ) s' hs' t' ht' hcod'
  have e1 := _root_.GlobalTheory.Mix.side_bc_eq k K X G p q j hp τ e h _ _ hsm N L (M.logSec s) (N.logSec t)
  have e2 := _root_.GlobalTheory.Mix.side_bc_eq k K X G p q j hp τ e h _ _ htm M L (N.logSec t) (M.logSec s)
  have hsf : (M.bc hp.w τ).logSec s' = fun y => M.logSec s (bcPt hp.w τ y) := funext hslog
  have htf : (N.bc hp.w τ).logSec t' = fun y => N.logSec t (bcPt hp.w τ y) := funext htlog
  rw [hsf, htf] at hrec
  exact e1.symm.trans (hrec.trans e2)

end GlobalTheory.MixRec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleUnitConstant
section
noncomputable section

section

open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

namespace GlobalTheory.StdRead

variable {D : D7}

theorem xiN_eq {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {a d : ℕ}
    (hS : S.rank = a) (hT : T.rank = d) {δ : ℂ} (hs : δ ≠ 0) {G : VC D a d → ℂ} {f : WO S T → ℂ}
    (h : Reads ψ θ hS hT ⊤ δ 1 G f) :
    GlobalTheory.AdForm.xiN θ S T hS hT (-δ) (Formalism.MainNotions.TaylorLogMetric.area (lamOf D ⊤ δ))⁻¹ f = G := by
  funext z
  obtain ⟨σ, hσ⟩ := GlobalTheory.FockCompare.exists_chart hθ
  have hsp : ∀ Z : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ,
      (GlobalTheory.AdForm.realPt θ Z).map (finPart D) = 0 ∧ ∀ τ, compAt θ τ (GlobalTheory.AdForm.realPt θ Z) = Z τ := fun Z => by
    refine Classical.epsilon_spec (p := fun w : Mx D T.rank S.rank => w.map (finPart D) = 0 ∧ ∀ τ, compAt θ τ w = Z τ)
      ⟨Matrix.of fun i j => σ fun τ => Z τ i j, ?_, fun τ => ?_⟩
    · ext i j; exact hσ.fin _
    · ext i j; exact hσ.comp _ _
  unfold GlobalTheory.AdForm.xiN
  obtain ⟨h1, h2⟩ := hsp fun τ => Matrix.of fun i j => -((-δ)⁻¹ * z τ (Fin.cast hT i) (Fin.cast hS j))
  have hY : GlobalTheory.NormExact.coordY θ hS hT δ 1 (GlobalTheory.AdForm.realPt θ
      fun τ => Matrix.of fun i j => -((-δ)⁻¹ * z τ (Fin.cast hT i) (Fin.cast hS j))) = z := by
    funext τ i j
    unfold GlobalTheory.NormExact.coordY
    rw [h2, map_one, mul_one, Matrix.of_apply, inv_neg, neg_mul, neg_neg, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]
    rfl
  rw [h.2 _ h1, hY, ← mul_assoc, ← Complex.exp_add]
  have hH : Formalism.L2.Ker.HV (Formalism.MainNotions.TaylorLogMetric.area (lamOf D ⊤ δ))⁻¹ z z = Formalism.MainNotions.TaylorLogMetric.Hf D (tor0 D ⊤ δ) z z := by
    change (((Formalism.MainNotions.TaylorLogMetric.area (lamOf D ⊤ δ))⁻¹ : ℝ) : ℂ) * _ = _ / ((Formalism.MainNotions.TaylorLogMetric.area (lamOf D ⊤ δ) : ℝ) : ℂ)
    rw [div_eq_inv_mul, Complex.ofReal_inv]
  rw [hH, neg_mul, add_neg_cancel, Complex.exp_zero, one_mul]

theorem reads_sum {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {a d : ℕ} {hS : S.rank = a} {hT : T.rank = d}
    {δ : ℂ} {ι : Type} (R : Finset ι) (G : ι → VC D a d → ℂ) (f : ι → WO S T → ℂ)
    (h : ∀ r ∈ R, Reads ψ θ hS hT ⊤ δ 1 (G r) (f r)) : Reads ψ θ hS hT ⊤ δ 1 (∑ r ∈ R, G r) (∑ r ∈ R, f r) := by
  induction R using Finset.induction_on with
  | empty => exact ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).zero_mem, fun w _ => by simp⟩
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    exact (h x (Finset.mem_insert_self _ _)).add (ih fun r hr => h r (Finset.mem_insert_of_mem hr))

def IsPh (u : ℂ) : Prop := ‖u‖ = 1 ∧ u ∈ Qbar ∧ ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), ‖lamC lam u‖ = 1

theorem IsPh.mul {u v : ℂ} (hu : IsPh u) (hv : IsPh v) : IsPh (u * v) :=
  ⟨by rw [norm_mul, hu.1, hv.1, mul_one], mul_mem hu.2.1 hv.2.1, fun p _ lam => by
    rw [GlobalTheory.BotFormula.lamC_mul lam hu.2.1 hv.2.1, norm_mul, hu.2.2, hv.2.2, mul_one]⟩

theorem lamC_one {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) : lamC lam 1 = 1 := by
  unfold lamC
  rw [dite_eq_left (one_mem _)]
  exact map_one lam

theorem IsPh.conj {u : ℂ} (hu : IsPh u) : IsPh (starRingEnd ℂ u) := by
  have h0 : u ≠ 0 := fun h => by simpa [h] using hu.1
  have e : starRingEnd ℂ u = u⁻¹ := (Complex.inv_eq_conj hu.1).symm
  refine ⟨by rw [Complex.norm_conj, hu.1], e ▸ inv_mem hu.2.1, fun p _ lam => ?_⟩
  have h := GlobalTheory.BotFormula.lamC_mul lam hu.2.1 (inv_mem hu.2.1)
  rw [mul_inv_cancel₀ h0, lamC_one] at h
  have h2 := congrArg norm h
  rw [norm_mul, hu.2.2, norm_one, one_mul] at h2
  rw [e, ← h2]

theorem isPh_of_pow {u : ℂ} {m : ℕ} (hm : 0 < m) (h : u ^ m = 1) : IsPh u := by
  have hQ : u ∈ Qbar := by
    rw [mem_algebraicClosure_iff]
    exact (IsIntegral.of_pow hm (h ▸ isIntegral_one)).isAlgebraic
  refine ⟨(pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 (by rw [← norm_pow, h, norm_one]), hQ, fun p _ lam => ?_⟩
  refine (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 ?_
  unfold lamC
  rw [dite_eq_left hQ, ← norm_pow, ← map_pow, show (⟨u, hQ⟩ : Qbar) ^ m = 1 from Subtype.ext h, map_one, norm_one]

theorem exists_const (hI : GlobalTheory.NormSum.Inp D) (δ t0 : ℂ) {a d : ℕ} (G : VC D a d → ℂ)
    (hG : G ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d)) (h0 : G ≠ 0) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ e0, Crv D ⊤ δ → Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 → oddE0 D ⊤ δ t0 a d e0 → e0 ≠ 0 →
      ∃ u, IsPh u ∧ G = (κ * u) • e0 := by
  by_cases hex : ∃ e1, Crv D ⊤ δ ∧ oddE0 D ⊤ δ t0 a d e1 ∧ e1 ≠ 0
  · obtain ⟨e1, hC, h1, hne⟩ := hex
    have k0 := GlobalTheory.NormSum.VacMove.klat (D := D) (tor0 D ⊤ δ) (GlobalTheory.NormSum.VacMove.moves_one D a)
      (GlobalTheory.NormSum.VacMove.moves_one D d)
    obtain ⟨hline, -⟩ := GlobalTheory.ThetaLine.theta_line D hI.g1 ⊤ δ hC a d _ k0
    obtain ⟨κ, hκ⟩ := hline G hG e1 h1.1 hne
    refine ⟨κ, fun h => h0 (by rw [hκ, h, zero_smul]), fun e0 _ ht he hn => ?_⟩
    obtain ⟨u, hu, e⟩ := GlobalTheory.VacuumUnique.vacuum_unique hI hC he h1 hn
    obtain ⟨a1, a2⟩ := _root_.GlobalTheory.VacUnit.vac_unit hI hC ht he h1 hn u e
    exact ⟨u, ⟨hu, a1, a2⟩, by rw [hκ, e, smul_smul]⟩
  · exact ⟨1, one_ne_zero, fun e0 hC _ he hn => absurd ⟨e0, hC, he, hn⟩ hex⟩

theorem reads_std (hI : GlobalTheory.NormSum.Inp D) {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {S T : HSp D} (hS : S.rank = P.a) (hT : T.rank = P.d) (hcc : D.host.ccK = ⊤) (hs : Setup ψ θ S T ⊤ δ 1) {v f : WO S T → ℂ}
    (hv : IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (stdL D S.rank : Set (Fin S.rank → D.host.E))
      (stdL D T.rank : Set (Fin T.rank → D.host.E)) v)
    {c : ℂ} (hc : c • P.e0 ∈ Th D (tor0 D ⊤ δ) (stdL D P.a) (stdL D P.d)) (hr : Reads ψ θ hS hT ⊤ δ 1 (c • P.e0) v)
    {e : AE D} {𝔪 : Ideal (𝓞 D.host.E)} (hm : GoodMod e 𝔪) {ν : (AE D)ˣ →* Circle} (hν : HasFinPart ν⁻¹ P.W.chV' P.W.ep')
    (hk : KillsCong ν 𝔪) {β : GL (Fin S.rank) (EAf D)} (hβ : Formalism.L2.DIV.IsFrame β (stdL D S.rank))
    (hstd : GlobalTheory.FunObj.SqNum.IsStdDatum P 𝔪 0) {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)}
    (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e (latO S T (stdL D S.rank : Set (Fin S.rank → D.host.E))
      (stdL D T.rank : Set (Fin T.rank → D.host.E)) fun _ => True) 1 v Tm)
    (hf : f = Tm fun w => starRingEnd ℂ (stdFst ν e 𝔪 S T β 1 w)) :
    ∃ u, IsPh u ∧ Reads ψ θ hS hT ⊤ δ 1 ((c * u) • P.F) f := by
  obtain ⟨R, hR1, hR2, hF⟩ := hstd
  obtain ⟨b1, b2⟩ := _root_.GlobalTheory.StdRead.isIntM_of_isFrame_stdL β hβ
  obtain ⟨m, hm0, hpow⟩ := _root_.GlobalTheory.StdRead.unitChar_pow_eq_one e 𝔪 hm ν hk β b1 b2
  choose! z hz using fun (k : Formalism.MainNotions.StandardLatticesGL3.GA D P.a) (hk : k ∈ intG D P.a) => exists_approx hm.ne_bot 0 P.d hk
  have hz' : ∀ r ∈ R, IsIntE (z r) ∧ Approx 𝔪 0 r (z r) := fun r hr => hz r (hR1 r hr)
  have h0 := GlobalTheory.T.idealIndicator_reads_norm_pow_mul_intertwinedVacuum ψ θ S T hS hT δ hcc hs v hv _ hc hr e 𝔪 hm Tm hTm
  have h1 := GlobalTheory.T.cosetIndicator_reads_as_translate_curveTheta ψ θ S T hS hT δ hcc hs v hv _ hc hr e 𝔪 hm Tm hTm h0
  refine ⟨_, (isPh_of_pow hm0 hpow).conj, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hf, _root_.GlobalTheory.StdExpand.conj_stdFst_eq_sum S T hS hT P.a_le e 𝔪 hm ν hk β b1 b2 R hR1 hR2 z hz', map_smul, map_sum, mul_comm c, mul_smul, hF,
    Finset.smul_sum]
  refine Reads.smul (reads_sum R _ _ fun r hr => ?_) _
  rw [_root_.GlobalTheory.StdRead.Move.om_cosetVec hI P hm.ne_bot 0 r (hR1 r hr) _ (GlobalTheory.T.integral_action_unit_character_eigen hI P e 𝔪 hm ν hν hk r (hR1 r hr)) (z r) (hz' r hr).1 (hz' r hr).2,
    map_smul, smul_comm c, ← cosV_smul]
  exact (h1 (z r) (hz' r hr).1).smul _

variable {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}


open GlobalTheory.FunObj.SqNum GlobalTheory.FunObj.StdDatum GlobalTheory.Mem.Col2.SplitChar in
theorem killsCong {μ₀ : T} (hL : L.Is μ₀) (G : GlobalTheory.ChiGrid.GridData L sc) (t : T) (i j : Fin D.R.m) :
    KillsCong (G.nu t i (j + 1)) (GlobalTheory.SqTop.modT G t) := by
  intro x u hxu hu hm
  have hle := Ideal.mul_mono (TwBig.modT_le_condE G t) (TwBig.conj_smul_mono (TwBig.modT_le_condE G t))
  have h1 := TwBig.nuInv_base_eq_one hL G i j u hu (TwBig.hatId_mono hle hm)
  have h2 := GlobalTheory.BotPairSmall.CondXi.xiH_eq_one_of_cong hL G t u hu hm
  have e : nuH G t i j = nuH G μ₀ i j * L.xiH t := by
    show L.C.mu0 j * L.xiH t / G.ch.chiH (D.R.m - i) = L.C.mu0 j * L.xiH μ₀ / G.ch.chiH (D.R.m - i) * L.xiH t
    rw [hL.xi_base, mul_one, mul_div_right_comm]
  have h3 := _root_.GlobalTheory.FinIdlRead.chr_finIdl _ _ (chrEq_nu G t i j hL) x u hxu
  have e1 : (nuH G μ₀ i j * L.xiH t).1 (finIdl D u) = (nuH G μ₀ i j).1 (finIdl D u) * (L.xiH t).1 (finIdl D u) := rfl
  have e2 : (nuH G μ₀ i j).1 (finIdl D u) = 1 := inv_eq_one.1 h1
  rw [e, e1, e2, h2, mul_one] at h3
  exact Circle.coe_injective (by simpa using h3)

end GlobalTheory.StdRead

end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdRead

end GlobalTheory.StdRead

end
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFamilyMovingPartsChainBound
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSNef

theorem Total.comp {X : Scheme.{0}} [IsIntegral X] {J J' : Type} {f : J → X.functionField} (h : Total f)
    (ι : J' → J) : Total (f ∘ ι) :=
  ⟨fun j => h.1 (ι j), fun x j l => h.2 x (ι j) (ι l)⟩

theorem selfInter_nonneg_of_isFS (hC : GlobalTheory.Published.ArCalc) (hA : AmpleHS) (hS : SemiPull) {k : Type} [CommRing k]
    {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D) {M : HermLB p} {J : Type} [Fintype J]
    {f : J → X.functionField} {w : J → ℝ} (hM : IsFS M f w) (hw : ∀ j, 0 ≤ w j) {μ : ℝ} (hμ : M.IsSelfInter μ) :
    0 ≤ μ := by
  have hnef := _root_.GlobalTheory.HSNef.FSNef.isNef_of_isFS hC k X p D hX M J f w hM hw
  have hht := (_root_.GlobalTheory.KleimanNef.htNef_of_isNef hC hA hS k X p D hX M hnef).2
  obtain ⟨h, hh, rfl⟩ := hμ
  exact hht h hh _

theorem levels_le_selfInter (hC : GlobalTheory.Published.ArCalc) (hA : AmpleHS) (hS : SemiPull) (k : Type) [CommRing k]
    (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsArithVar p D) (x : Fin D → X.functionField) (Δ : ℝ)
    (hx : AlgebraicIndependent ℤ x) (hΔ : 0 < Δ) :
    ∀ (N : ℕ) (J : Type) [Fintype J] (e : J → X.functionField) (n : J → ℕ) (M : HermLB p) (μ : ℝ),
      LinearIndependent ℤ e → (∀ j, n j ≤ N) → Total (boxFam e x) → IsFS M (boxFam e x) (fun c => n c.1 * Δ) →
      M.IsSelfInter μ → ((D + 1).factorial : ℝ) * Δ * ∑ j, (n j : ℝ) ≤ μ := by
  intro N
  induction N with
  | zero =>
    intro J _ e n M μ _ hn _ hM hμ
    have h0 : ∀ j, n j = 0 := fun j => Nat.le_zero.1 (hn j)
    simp only [h0, Nat.cast_zero, Finset.sum_const_zero, mul_zero]
    exact selfInter_nonneg_of_isFS hC hA hS hX hM (fun c => by simp [h0]) hμ
  | succ N ih =>
    intro J _ e n M μ he hn ht hM hμ
    classical
    have hw0 : ∀ c : J × Finset (Fin D), 0 ≤ (n c.1 : ℝ) * Δ := fun c => by positivity
    by_cases hJ : ∀ j, n j = 0
    · simp only [hJ, Nat.cast_zero, Finset.sum_const_zero, mul_zero]
      exact selfInter_nonneg_of_isFS hC hA hS hX hM hw0 hμ
    push_neg at hJ
    obtain ⟨j₀, hj₀⟩ := hJ
    let J' := {j // 1 ≤ n j}
    let e' : J' → X.functionField := fun j => e j.1
    let n' : J' → ℕ := fun j => n j.1 - 1
    let ι : J' × Finset (Fin D) → J × Finset (Fin D) := fun c => (c.1.1, c.2)
    have hι : Function.Injective ι := by
      rintro ⟨⟨a, ha⟩, s⟩ ⟨⟨b, hb⟩, t⟩ h
      simp only [ι, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    have hbox : boxFam e' x = boxFam e x ∘ ι := rfl
    haveI : Nonempty (J' × Finset (Fin D)) := ⟨(⟨j₀, Nat.one_le_iff_ne_zero.2 hj₀⟩, ∅)⟩
    have ht' : Total (boxFam e' x) := hbox ▸ ht.comp ι
    obtain ⟨M', hM'⟩ := _root_.GlobalTheory.HSNef.exists_isFS k X p (J' × Finset (Fin D)) (boxFam e' x) (fun c => (n' c.1 : ℝ) * Δ) ht'
    obtain ⟨h', hh'⟩ := (hC.arExists k X p D hX).1 M'
    have hμ' : M'.IsSelfInter (h' (genericPoint X)) := ⟨h', hh', rfl⟩
    have he' : LinearIndependent ℤ e' := he.comp _ Subtype.val_injective
    have hn' : ∀ j, n' j ≤ N := fun j => by
      have := hn j.1
      simp only [n']
      omega
    have IH := ih J' e' n' M' _ he' hn' ht' hM' hμ'
    have hw0' : ∀ c : J' × Finset (Fin D), 0 ≤ (n' c.1 : ℝ) * Δ := fun c => by positivity
    have hstep : ∀ c : J' × Finset (Fin D), (n' c.1 : ℝ) * Δ + Δ ≤ (n (ι c).1 : ℝ) * Δ := fun c => by
      have h1 := c.1.2
      simp only [n', ι]
      rw [Nat.cast_sub h1]
      push_cast
      linarith
    have hle : Le (M'.shift (fun _ => Δ) fun _ => rfl) M :=
      _root_.GlobalTheory.HSNef.le_shift_of_isFS_sub k X p M M' (J × Finset (Fin D)) (J' × Finset (Fin D)) (boxFam e x) (fun c => (n c.1 : ℝ) * Δ)
        (fun c => (n' c.1 : ℝ) * Δ) ι Δ hι hM (hbox ▸ hM') hstep
    have hnefM := _root_.GlobalTheory.HSNef.FSNef.isNef_of_isFS hC k X p D hX M _ _ _ hM hw0
    have hnefM' := _root_.GlobalTheory.HSNef.FSNef.isNef_of_isFS hC k X p D hX M' _ _ _ hM' hw0'
    have hnefS := GlobalTheory.NefShift.isNef_shift_nonneg k X p D hX M' Δ hΔ.le hnefM'
    have hsh := hC.arShift k X p D hX M' _ Δ hμ'
    have hmono := _root_.GlobalTheory.HSNefMono.selfInter_mono_of_isNef hC hA hS k X p D hX M _ μ _ hnefM hnefS hle hμ hsh
    have hrk := _root_.GlobalTheory.HSNef.fs_box_rank_le hC hA k X p D hX M' J' e' x (fun c => (n' c.1 : ℝ) * Δ) he' hx hw0' hM'
    have hsum : ∑ j, (n j : ℝ) = ∑ j : J', (n' j : ℝ) + Fintype.card J' := by
      rw [← Fintype.sum_subtype_add_sum_subtype (fun j => 1 ≤ n j) (fun j => (n j : ℝ))]
      have h2 : ∑ j : {j // ¬ 1 ≤ n j}, (n j.1 : ℝ) = 0 :=
        Finset.sum_eq_zero fun j _ => by
          have := j.2
          have : n j.1 = 0 := by omega
          simp [this]
      rw [h2, add_zero]
      have h3 : ∀ j : J', (n j.1 : ℝ) = (n' j : ℝ) + 1 := fun j => by
        simp only [n']
        rw [Nat.cast_sub j.2]
        ring
      simp only [h3, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      rfl
    have hf : ((D + 1).factorial : ℝ) = ((D : ℝ) + 1) * D.factorial := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hcard : ((D + 1).factorial : ℝ) * Δ * Fintype.card J' ≤ ((D : ℝ) + 1) * Δ * gdeg M' D := by
      calc ((D + 1).factorial : ℝ) * Δ * Fintype.card J' = ((D : ℝ) + 1) * Δ * (D.factorial * Fintype.card J') := by
            rw [hf]; ring
        _ ≤ ((D : ℝ) + 1) * Δ * gdeg M' D := mul_le_mul_of_nonneg_left hrk (by positivity)
    rw [hsum, mul_add]
    linarith

theorem chain_moving_parts : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (x : Fin D → X.functionField) (Δ : ℝ), AlgebraicIndependent ℤ x → 0 < Δ → ∀ (N : ℕ) (J : Type) [Fintype J] (e : J → X.functionField) (n : J → ℕ) (M : HermLB p) (μ : ℝ), LinearIndependent ℤ e → (∀ j, n j ≤ N) → Total (boxFam e x) → IsFS M (boxFam e x) (fun c => n c.1 * Δ) → M.IsSelfInter μ → ((D + 1).factorial : ℝ) * Δ * ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ μ + ((D : ℝ) + 1) * Δ * gdeg M D := by
  intro hC hA hS k _ X _ p D hX x Δ hx hΔ N J _ e n M μ he hn ht hM hμ
  have key := levels_le_selfInter hC hA hS k X p D hX x Δ hx hΔ N J e n M μ he hn ht hM hμ
  have hw0 : ∀ c : J × Finset (Fin D), 0 ≤ (n c.1 : ℝ) * Δ := fun c => by positivity
  have hrk := _root_.GlobalTheory.HSNef.fs_box_rank_le hC hA k X p D hX M J e x (fun c => (n c.1 : ℝ) * Δ) he hx hw0 hM
  have hf : ((D + 1).factorial : ℝ) = ((D : ℝ) + 1) * D.factorial := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have hcard : ((D + 1).factorial : ℝ) * Δ * Fintype.card J ≤ ((D : ℝ) + 1) * Δ * gdeg M D := by
    calc ((D + 1).factorial : ℝ) * Δ * Fintype.card J = ((D : ℝ) + 1) * Δ * (D.factorial * Fintype.card J) := by
          rw [hf]; ring
      _ ≤ ((D : ℝ) + 1) * Δ * gdeg M D := mul_le_mul_of_nonneg_left hrk (by positivity)
  have hsum : ((∑ j, (n j + 1) : ℕ) : ℝ) = ∑ j, (n j : ℝ) + Fintype.card J := by
    push_cast
    rw [Finset.sum_add_distrib]
    simp
  rw [hsum, mul_add]
  linarith

end GlobalTheory.HSNef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BundleIsoOntoPullbackIntertwinesTransitions
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LogKSCoc

theorem res_res {X : Scheme.{0}} {U V W : X.Opens} (h : V ≤ U) (h' : W ≤ V) (a : Γ(X, U)ˣ) :
    res h' (res h a) = res (h'.trans h) a := by
  ext
  change (X.presheaf.map _).hom ((X.presheaf.map _).hom _) = (X.presheaf.map _).hom _
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem res_intertwines {Y : Scheme.{0}} {P Q A B V : Y.Opens} (a : Γ(Y, P)ˣ) (a' : Γ(Y, Q)ˣ) (m : Γ(Y, A)ˣ)
    (l : Γ(Y, B)ˣ) (hA : P ⊓ Q ≤ A) (hB : P ⊓ Q ≤ B)
    (e : res (inf_le_left : P ⊓ Q ≤ P) a = res hA m * (res hB l)⁻¹ * res (inf_le_right : P ⊓ Q ≤ Q) a')
    (h : V ≤ P) (h' : V ≤ Q) (hM : V ≤ A) (hL : V ≤ B) :
    res hM m * res h' a' = res h a * res hL l := by
  have e' := congrArg (res (le_inf h h')) e
  simp only [map_mul, map_inv, res_res] at e'
  rw [e', _root_.mul_right_comm, inv_mul_cancel_right]

theorem gen_intertwines {Y : Scheme.{0}} (M L : LB Y) (w : LB.Iso L M) (hw : w.IsGen) (i i' : M.ι) (k k' : L.ι)
    {V : Y.Opens} (h : V ≤ M.U i ⊓ L.U k) (h' : V ≤ M.U i' ⊓ L.U k') (hM : V ≤ M.U i ⊓ M.U i')
    (hL : V ≤ L.U k ⊓ L.U k') :
    res hM (M.g i i') * res h' (w.s (i', k')) = res h (w.s (i, k)) * res hL (L.g k k') := by
  exact res_intertwines (w.s (i, k)) (w.s (i', k')) (M.g i i') (L.g k k') _ _ (hw (i, k) (i', k')) h h' hM hL

theorem iso_pull_intertwines : ∀ (Y Z : Scheme.{0}) (φ : Y ⟶ Z) (L : LB Z) (L' : LB Y) (w : LB.Iso L' (L.pull φ)), w.IsGen → ∀ (i i' : L.ι) (k k' : L'.ι) (O O' : Y.Opens) (hO : O ≤ (L.pull φ).U (fun _ => i) ⊓ L'.U k) (hO' : O' ≤ (L.pull φ).U (fun _ => i') ⊓ L'.U k') (hk : O ≤ L'.U k) (hk' : O' ≤ L'.U k') (hu : O ⊓ O' ≤ φ ⁻¹ᵁ (L.U i ⊓ L.U i')), resG Y hu (pullU φ _ (L.g i i')).val * resG Y (inf_le_right : O ⊓ O' ≤ O') (resG Y hO' (w.s (fun _ => i', k')).val) = resG Y (inf_le_left : O ⊓ O' ≤ O) (resG Y hO (w.s (fun _ => i, k)).val) * resG Y (inf_le_inf hk hk') (L'.g k k').val := by
  intro Y Z φ L L' w hw i i' k k' O O' hO hO' hk hk' hu
  have e := gen_intertwines (L.pull φ) L' w hw (fun _ => i) (fun _ => i') k k' (V := O ⊓ O')
    (inf_le_left.trans hO) (inf_le_right.trans hO')
    (inf_le_inf (hO.trans inf_le_left) (hO'.trans inf_le_left)) (inf_le_inf hk hk')
  have g : res (inf_le_inf (hO.trans inf_le_left) (hO'.trans inf_le_left))
      ((L.pull φ).g (fun _ => i) (fun _ => i')) = res hu (pullU φ _ (L.g i i')) := by
    unfold LB.pull LB.LinComb
    dsimp only
    rw [Fintype.prod_unique, zpow_one]
    exact res_res _ _ _
  rw [g] at e
  have e₁ := congrArg Units.val (res_res hO (inf_le_left : O ⊓ O' ≤ O) (w.s (fun _ => i, k)))
  have e₂ := congrArg Units.val (res_res hO' (inf_le_right : O ⊓ O' ≤ O') (w.s (fun _ => i', k')))
  exact (congrArg (_ * ·) e₂).trans ((congrArg Units.val e).trans (congrArg (· * _) e₁.symm))

end GlobalTheory.LogKSCoc
end

