module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0389
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemCutQGrp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0412
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.Bundle0005
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
public import Formalism.GradedWeylDivisibility.FinalD
public import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
public import Formalism.LocalRingCardinality.FactDelDualNabla
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0321
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0031
public import Formalism.LocalToGlobal.Divisibility.Bundle0008

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChartsReadingStepZero
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.Chart0

open GlobalTheory.Mem.Col2.MemChart

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

abbrev lvG (a : I.ι) := levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0

abbrev lvQ (a : I.ι) := levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0

def yT (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) : GA B (B.R.N 0) :=
  Classical.epsilon fun g : GA B (B.R.N 0) => PtOf (g * kStd X u (B.R.N 0)) (extTo I.SQ ((I.stp u a 0).rep c).1.1)

theorem yT_spec (hI : I.Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) :
    PtOf (yT I u a c * kStd X u (B.R.N 0)) (extTo I.SQ ((I.stp u a 0).rep c).1.1) := by
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.Mem.Col2.PtTwist.exists_ptOf_twists I hI u _ (extTo I.SQ ((I.stp u a 0).rep c).1.1)
  exact Classical.epsilon_spec (p := fun g : GA B (B.R.N 0) => PtOf (g * kStd X u (B.R.N 0)) (extTo I.SQ ((I.stp u a 0).rep c).1.1))
    ⟨g * (kStd X u (B.R.N 0))⁻¹, by rwa [inv_mul_cancel_right]⟩

theorem cos0 {u : B.Word} {a : I.ι} (q q' : PtAt B.R I.sel (I.tup a) (I.cst a) u 0) : cosetIn q = cosetIn q' := by
  have key : ∀ q : PtAt B.R I.sel (I.tup a) (I.cst a) u 0, cosetIn q = fun _ => ∅ := fun q => by
    have h1 : q.1.2 = ∅ := by
      have := q.2
      rwa [ysAt_ys_of_ne _ _ _ (by have := B.R.two_le_m; omega)] at this
    funext P
    unfold cosetIn
    rw [h1]
    simp
  rw [key, key]

theorem stepZero_classes_bijective_decoratedLattice (hI : I.Ok) (u : B.Word) (a : I.ι) :
    Function.Bijective fun c : (I.stp u a 0).Cl =>
      decoCls (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (colLev I.Ch 0).grp ((I.stp u a 0).rep c).1.1.deco := by
  letI := StepZero.idxUnique (hI.idx_ok a)
  have h := StepZero.clMap_bijective (Λ₀ := colLev I.Ch 0) ((I.Tp a).pref u 0) (fun _ => ⟨fun _ => 0, fun _ _ _ => le_rfl⟩)
    (StepZero.ysAt_zero I.sel (I.tup a) (I.cst a) (R := B.R)) (StepZero.levGAt_zero (I.Tp a) (hI.idx_ok a)) (StepZero.levQAt_zero (I.Tp a) (hI.idx_ok a))
  convert h using 1
  funext c
  have e := StepZero.clMap_cl (y := ysAt B.R I.sel (I.tup a) (I.cst a) 0) (Θ := lvQ I a) (Λ₀ := colLev I.Ch 0) ((I.Tp a).pref u 0) (fun _ => ⟨fun _ => 0, fun _ _ _ => le_rfl⟩)
    (StepZero.levGAt_zero (I.Tp a) (hI.idx_ok a)) c.1 ((I.stp u a 0).rep c)
  have e2 : (I.stp u a 0).cl c.1 ((I.stp u a 0).rep c) = c := by
    obtain ⟨b, q⟩ := c
    exact congrArg (Sigma.mk b) ((I.stp u a 0).rp_spec b q)
  rw [e2] at e
  exact e.symm

theorem stab_range0 (hI : I.Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) (γ : GL (Fin (B.R.N 0)) B.host.E) :
    γ ∈ (stM (lvG I a) (lvQ I a) ((I.Tp a).pref u 0) (I.pref u a 0) c).range ↔
      ∃ g : UF B.fields.E (B.R.N 0) × (colLev I.Ch 0).grp, ufGL B.fields.E (B.R.N 0) g.1 = γ ∧
        g • ((I.stp u a 0).rep c).1.1.deco = ((I.stp u a 0).rep c).1.1.deco := by
  have hL := hI.idx_ok a
  have hy := StepZero.ysAt_zero I.sel (I.tup a) (I.cst a) (R := B.R)
  constructor
  · rintro ⟨⟨g, hg⟩, rfl⟩
    refine ⟨StepZero.down (y := ysAt B.R I.sel (I.tup a) (I.cst a) 0) (Θ := lvQ I a) ((I.Tp a).pref u 0) (StepZero.levGAt_zero (I.Tp a) hL) c.1 g, rfl, ?_⟩
    exact (StepZero.deco_smul (y := ysAt B.R I.sel (I.tup a) (I.cst a) 0) (Θ := lvQ I a) _ (StepZero.levGAt_zero (I.Tp a) hL) c.1 g _).symm.trans (congrArg (fun q => q.1.1.deco) hg)
  · rintro ⟨g₀, rfl, hg⟩
    obtain ⟨g, h1, h2⟩ := StepZero.exists_lift ((I.Tp a).pref u 0) hy (StepZero.levGAt_zero (I.Tp a) hL)
      (StepZero.levQAt_zero (I.Tp a) hL) c.1 _ _ g₀ hg
    exact ⟨⟨g, h2⟩, congrArg (fun g => ufGL B.fields.E (B.R.N 0) g.1) h1⟩

theorem red0 (hI : I.Ok) (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) (x : GA B (B.R.N 0))
    (κ : (I.stp u a 0).G c.1) (h1 : (I.stp u a 0).gam c.1 κ = 1)
    (h2 : PtOf (yT I u a c * x * kStd X u (B.R.N 0)) ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)).1.1) :
    ∃ hJ : x ∈ J0 B.sp.cm (B.R.N 0) ((B.primes X).vT u), redG B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs ⟨x, hJ⟩ = κ.2.1.1⁻¹ := by
  have hg := dia_of_pt hPr u (yT_spec I hI u a c)
  have hx := dia_of_pt hPr u h2
  have e1 : κ.1 = 1 := ufGL_inj B.sp.cm (B.R.N 0) (h1.trans (map_one _).symm)
  exact red_of_act B.sp.cm (B.R.N 0) (diaT (Pr := B.primes X) u) hg.1 hx.1 κ.2.1.1 (by
    rw [hg.2, hx.2]
    show ((κ.1, κ.2.1.1) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs)) • _ = _
    rw [e1]
    rfl)

theorem lev0 (hI : I.Ok) (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) (x : GA B (B.R.N 0))
    (q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0) (h : PtOf (yT I u a c * x * kStd X u (B.R.N 0)) q) :
    x ∈ levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (colLev I.Ch 0).grp ↔
      ∃ κ : (I.stp u a 0).G c.1, (I.stp u a 0).gam c.1 κ = 1 ∧ ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)).1.1 = q ∧
        cosetIn ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)) = cosetIn ((I.stp u a 0).rep c) := by
  have hL := hI.idx_ok a
  have hy := StepZero.ysAt_zero I.sel (I.tup a) (I.cst a) (R := B.R)
  have hΛ := StepZero.levGAt_zero (I.Tp a) hL
  have hΘ := StepZero.levQAt_zero (I.Tp a) hL
  have hg := dia_of_pt hPr u (yT_spec I hI u a c)
  have hx := dia_of_pt hPr u h
  constructor
  · intro hxU
    have h1 := act_of_mem B.sp.cm (B.R.N 0) _ (diaT (Pr := B.primes X) u) hg.1 ⟨x, hxU⟩
    rw [hg.2, hx.2] at h1
    obtain ⟨p, hp⟩ := exists_ptAt (R := B.R) I.sel (I.tup a) (I.cst a) q
    obtain ⟨g, h2, h3⟩ := StepZero.exists_lift ((I.Tp a).pref u 0) hy hΛ hΘ c.1 ((I.stp u a 0).rep c) p
      (1, (Formalism.L2.Col.levRed B.sp.cm (B.R.N 0) _ _ _ ⟨x, hxU⟩)⁻¹) (by rw [hp]; exact h1.symm)
    refine ⟨g, ?_, ?_, cos0 I _ _⟩
    · show ufGL B.fields.E (B.R.N 0) g.1 = 1
      rw [show g.1 = 1 from congrArg Prod.fst h2, map_one]
    · exact (congrArg (fun p : PtAt B.R I.sel (I.tup a) (I.cst a) u 0 => p.1.1) h3).trans hp
  · rintro ⟨κ, h1, h2, -⟩
    obtain ⟨hJ, hr⟩ := red0 I hI hPr u a c x κ h1 (h2 ▸ h)
    refine (mem_levU _ _ _ _ _).2 ⟨hJ, ?_⟩
    have key : ∀ (Λ' : LevFam B.fields.E B.fields.K (B.R.N 0) (B.primes X).vGs), Λ' = colLev I.Ch 0 → ∀ g : Λ'.grp,
        g.1 ∈ (colLev I.Ch 0).grp := by
      rintro _ rfl g
      exact g.2
    have hm : κ.2.1.1 ∈ (colLev I.Ch 0).grp := key _ (hΛ c.1) κ.2.1
    rw [hr]
    exact inv_mem hm

theorem chr0 (hI : I.Ok) (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) (x : GA B (B.R.N 0))
    (hxU : x ∈ levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (colLev I.Ch 0).grp)
    (κ : (I.stp u a 0).G c.1) (h1 : (I.stp u a 0).gam c.1 κ = 1)
    (h2 : PtOf (yT I u a c * x * kStd X u (B.R.N 0)) ((I.stp u a 0).act c.1 κ ((I.stp u a 0).rep c)).1.1) :
    ((levTyp (F := B.host.F) (hc := B.sp.cm) ((Units.map B.embLL.toMonoidHom).comp (colLev I.Ch 0).chr) ⟨x, hxU⟩ : ℂˣ) : ℂ) =
      B.embLL (((I.stp u a 0).chr c.1 κ : B.LLˣ) : B.LL) := by
  have hL := hI.idx_ok a
  have hΛ := StepZero.levGAt_zero (I.Tp a) hL
  have hΘ := StepZero.levQAt_zero (I.Tp a) hL
  have hg := dia_of_pt hPr u (yT_spec I hI u a c)
  have hx := dia_of_pt hPr u h2
  have e1 : κ.1 = 1 := ufGL_inj B.sp.cm (B.R.N 0) (h1.trans (map_one _).symm)
  obtain ⟨hJ, hr⟩ := red_of_act B.sp.cm (B.R.N 0) (diaT (Pr := B.primes X) u) hg.1 hx.1 κ.2.1.1 (by
    rw [hg.2, hx.2]
    show ((κ.1, κ.2.1.1) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs)) • _ = _
    rw [e1]
    rfl)
  have e2 : Formalism.L2.Col.levRed B.sp.cm (B.R.N 0) _ _ _ ⟨x, hxU⟩ = (⟨κ.2.1.1, hΛ c.1 ▸ κ.2.1.2⟩ : (colLev I.Ch 0).grp)⁻¹ :=
    Subtype.ext hr
  show ((Units.map B.embLL.toMonoidHom ((colLev I.Ch 0).chr (Formalism.L2.Col.levRed B.sp.cm (B.R.N 0) _ _ _ ⟨x, hxU⟩)))⁻¹ : ℂˣ).1 =
    B.embLL (((lvG I a c.1).chr κ.2.1 * (lvQ I a c.1).chr κ.2.2 : B.LLˣ) : B.LL)
  rw [e2, StepZero.chr_eq_one (hΘ c.1), mul_one, StepZero.chr_congr (hΛ c.1), map_inv, map_inv, inv_inv]
  rfl


set_option maxHeartbeats 1000000 in
theorem charts_zero : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι), ∃ (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a 0).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad 0 (Nat.zero_le _) (fun c : {c // chOf c = β} => (I.chain l u a).stab 0 c.1) (fun c => latCrd (I.rec7 l Z) 0 (Nat.zero_le _) (I.latAt u a 0 c.1))), I.ReadsK l Z u a 0 (Nat.zero_le _) chOf K := by
  intro B X I hI hP l Z u a
  have hPr := l.pr
  have hX := GlobalTheory.Mem.FieldsLaws.fields_ok B
  have hi : 0 ≤ B.R.m := Nat.zero_le _
  obtain ⟨hg, -, hl⟩ := (_root_.GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 0 hi
  have hf : B.fields.f = B.R.f := (hPr.vT_card u).symm.trans (l.lev u I.mu0).card_ST
  have hL := hI.idx_ok a
  let chOf : (I.stp u a 0).Cl → Unit := fun _ => ()
  obtain ⟨lev, Y, SI, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := chart_exists (F := B.host.F) (E := B.host.E) B.sp.cm (B.R.N 0)
    (fun w => (colLev I.Ch 0 w).H) (f := B.R.f)
    (basePi_of_ok hX hPr u) (hPr.piT_norm u) (rls_vT_iff hX hPr u)
    (fun P hP => by simpa only [Ideal.absNorm_eq_natCard] using hPr.vT_norm u P hP) (rls_T_notUnder hPr u)
    (hf ▸ colBase_index (X := B.fields) B.sp.cm (B.R.N 0) hPr u) ((Units.map B.embLL.toMonoidHom).comp (colLev I.Ch 0).chr)
    (gramN (I.rec7 l Z) 0 hi) hg (badG (I.rec7 l Z)) (Set.ext fun v => (plUnder_vGs (X := B.fields) B.sp.cm hPr v).symm)
    (fun c : {c // chOf c = ()} => (I.stp u a 0).Stab c.1) (fun c => latCrd (I.rec7 l Z) 0 hi (I.latAt u a 0 c.1))
    (diaT (Pr := B.primes X) u) (fun c => ((I.stp u a 0).rep c.1).1.1.deco) (fun c => yT I u a c.1)
    (fun c => (dia_of_pt hPr u (yT_spec I hI u a c.1)).1) (fun c => (dia_of_pt hPr u (yT_spec I hI u a c.1)).2)
    ((stepZero_classes_bijective_decoratedLattice I hI u a).comp (Equiv.subtypeUnivEquiv fun _ => rfl).bijective) (fun c => (hl u a).1 c.1)
    (fun c => stM (lvG I a) (lvQ I a) _ _ c.1) (fun c => stM_inj (lvG I a) (lvQ I a) _ _ ((l.ch u a).step 0) c.1)
    (fun c γ => stab_range0 I hI u a c.1 γ)
  obtain ⟨k1, k2, k3⟩ := kStd_spec hPr u (B.R.N 0)
  letI := StepZero.idxUnique hL
  obtain ⟨q₀, -⟩ := exists_ptAt (R := B.R) I.sel (I.tup a) (I.cst a) (u := u) (j := 0) (DecoF.base _ _ _ _ _)
  refine ⟨badG (I.rec7 l Z), Unit, chOf, fun _ => ⟨lev, Y, h1, h2, SI, h3, h4⟩, fun _ => kStd X u (B.R.N 0),
    ⟨fun c c' => ⟨fun _ => ⟨Subsingleton.elim _ _, cos0 I _ _⟩, fun _ => rfl⟩,
      fun _ => ⟨(I.stp u a 0).cl default q₀, rfl⟩, fun β x => ?_, fun _ => k1, fun _ v hv _ _ => k2 v hv, fun _ => k3,
      fun c => ?_, fun c x q h => ?_, fun c x κ hκ h => ?_, fun c s => h9 _ _⟩⟩
  · exact (h5 ▸ Iff.rfl : x ∈ lev.Lb ↔ x ∈ baseLb B.fields.E (B.R.N 0) ((B.primes X).vT u)).trans (mem_baseLb hPr u _ x)
  · have e := h8 ⟨c, rfl⟩
    show PtOf ((Y ⟨c, rfl⟩).1 * kStd X u (B.R.N 0)) _
    rw [e]
    exact yT_spec I hI u a c
  · have e := h8 ⟨c, rfl⟩
    replace h : PtOf (yT I u a c * x * kStd X u (B.R.N 0)) q := e ▸ h
    exact (h6 ▸ Iff.rfl : x ∈ lev.U ↔ x ∈ levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs
      (colLev I.Ch 0).grp).trans (lev0 I hI hPr u a c x q h)
  · have e := h8 ⟨c, rfl⟩
    have hx : (id x.1 : GA B (B.R.N 0)) ∈ levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs
      (colLev I.Ch 0).grp := h6 ▸ x.2
    refine (congrArg Units.val (h7 x hx)).trans ?_
    exact chr0 I hI hPr u a c x.1 hx κ hκ (e ▸ h)

end GlobalTheory.Mem.Col2.TC.Chart0
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugatedChartDataLocalLevelAtQ
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.ChEx

theorem dc_mul_inv_bij {G : Type} [Group G] (Γ K K' : Subgroup G) (b : G) (hK : ∀ x, x ∈ K' ↔ b⁻¹ * x * b ∈ K)
    {ι : Type} (z : ι → G) (hz : Function.Bijective fun i => (Quotient.mk'' (z i) : ClassSet Γ K)) :
    Function.Bijective fun i => (Quotient.mk'' (z i * b⁻¹) : ClassSet Γ K') := by
  constructor
  · intro i j hij
    obtain ⟨h, hh, k, hk, e⟩ := (@DoubleCoset.eq _ _ Γ K' _ _).1 hij
    refine hz.1 ((@DoubleCoset.eq _ _ Γ K _ _).2 ⟨h, hh, b⁻¹ * k * b, (hK k).1 hk, ?_⟩)
    calc z j = (z j * b⁻¹) * b := by group
      _ = h * z i * (b⁻¹ * k * b) := by rw [e]; group
  · intro w
    induction w using Quotient.inductionOn' with
    | h x =>
      obtain ⟨i, hi⟩ := hz.2 (Quotient.mk'' (x * b))
      obtain ⟨h, hh, k, hk, e⟩ := (@DoubleCoset.eq _ _ Γ K _ _).1 hi
      refine ⟨i, (@DoubleCoset.eq _ _ Γ K' _ _).2 ⟨h, hh, b * k * b⁻¹, (hK _).2 ?_, ?_⟩⟩
      · have : b⁻¹ * (b * k * b⁻¹) * b = k := by group
        rw [this]
        exact hk
      · calc x = (x * b) * b⁻¹ := by group
          _ = (h * z i * k) * b⁻¹ := by rw [e]
          _ = h * (z i * b⁻¹) * (b * k * b⁻¹) := by group

theorem mem_range_qdStab {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] {Θ : LevQFam E K n Q}
    (H : Subgroup (GLG (E := E) (n := n) (SG := SG))) (p : DecoF E n ST SG Q) (γ : URat hc n) :
    γ ∈ (qdStab (hc := hc) (Θ := Θ) H p).range ↔ ∃ g : UF E n × H × Θ.grp, ufGL E n g.1 = γ.1 ∧ g • p = p := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a.1, ?_, a.2⟩
    rw [← qdf_ratHom_stab (hc := hc) H p a, ha, ufGL_ratHom]
  · rintro ⟨g, hg1, hg2⟩
    refine ⟨⟨g, hg2⟩, (ratHom_bijective hc n).1 ?_⟩
    exact (qdf_ratHom_stab (hc := hc) H p ⟨g, hg2⟩).trans
      (ufGL_inj hc n (hg1.trans (ufGL_ratHom hc n γ).symm))

theorem chartQ_exists : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] {ST SG Q : Finset (Pl E)} {K : Type} [Field K] (Hw : ∀ w : SG, Subgroup (GL (Fin n) (𝓞 E ⧸ w.1.asIdeal))) {π : 𝓞 E} {T f : ℕ} (hB : BasePi ST π) (hTπ : π * cO E π = (T : 𝓞 E)) (hST : ∀ P : Pl E, P ∈ ST ↔ π ∈ P.asIdeal) (hcard : ∀ P ∈ ST, Nat.card (𝓞 E ⧸ P.asIdeal) = T) (hSG : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → v ∉ plUnder F SG) (hidx : (baseLb E n ST).toAddSubgroup.relIndex (Submodule.span (𝓞 E) (Formalism.BasicNotions.dualSet (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (baseLb E n ST))).toAddSubgroup = T ^ (2 * f)) (lam : (Subgroup.pi Set.univ Hw : Subgroup (GLG (E := E) (n := n) (SG := SG))) →* ℂˣ) {Θ : LevQFam E K n Q} (q : QLoc hc n Q Θ) (hO : QOpen q) (hQT : ∀ P : Q, (T : 𝓞 F) ∉ (qv F P.1).asIdeal) (σ₀ : K →+* ℂ) (b : GL (Fin n) (AfE F E)) (hbU : b ∈ UAd hc n) (hbV : ∀ v, bc (prV (E := E) v) b ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST)) (hbL : ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F, b.1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST) ↔ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)) (hbT : ∀ v, v ∈ plUnder F ST → (levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v)).map (MulAut.conj (bc (prV (E := E) v) b)).toMonoidHom = levelVL hc.sig (1 : Matrix (Fin n) (Fin n) E) v (baseLb E n ST) ⊓ stabFun (baseDualV hc n ST v) (fLoc hc n ST v)) (hbO : ∀ v, v ∉ badQ' (F := F) SG Q → (T : 𝓞 F) ∉ v.asIdeal → bc (prV (E := E) v) b = 1) (J : Matrix (Fin n) (Fin n) E) (hJ : J = 1) (bad : Set (HeightOneSpectrum (𝓞 F))) (hb : bad = badQ' (F := F) SG Q) {cl : Type} (stab : cl → Type) [∀ c, Group (stab c)] (lat : cl → Submodule (𝓞 E) (Fin n → E)) (s : cl → DecoF E n ST SG Q) (y : cl → GL (Fin n) (AfE F E)) (hy : ∀ c, y c ∈ UAd hc n) (hd : ∀ c, FrOver q (y c) (s c)) (hs : Function.Bijective fun c => (Quotient.mk'' (s c) : DecoFCl (K := K) n ST SG Q (Subgroup.pi Set.univ Hw) Θ)) (hlat : ∀ c, lat c = (s c).deco.1.L) (st : ∀ c, stab c →* GL (Fin n) E) (hinj : ∀ c, Function.Injective (st c)) (hr : ∀ c γ, γ ∈ (st c).range ↔ ∃ g : UF E n × ↥(Subgroup.pi Set.univ Hw : Subgroup (GLG (E := E) (n := n) (SG := SG))) × ↥Θ.grp, ufGL E n g.1 = γ ∧ g • s c = s c) (hchr : ∀ P : Q, ∃ m : ℕ, 0 < m ∧ ∀ k, q.chr P k ^ m = 1), ∃ (lev : StepLevel F E hc.sig J T f bad) (Y : cl → UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)) (SI : ∀ c, stab c →* UJ (hc.sig : E →+* E) J), Function.Bijective (fun c => (Quotient.mk'' (Y c) : Cls lev)) ∧ (∀ c (x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F), x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (lat c) ↔ ((Y c).1⁻¹).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) lev.Lb) ∧ (∀ c, Function.Injective (SI c)) ∧ (∀ c (γ : UJ (hc.sig : E →+* E) J), γ ∈ (SI c).range ↔ bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈ lev.U.map (MulAut.conj (Y c).1).toMonoidHom) ∧ lev.Lb = baseLb E n ST ∧ lev.U = (levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q).map (MulAut.conj b).toMonoidHom ∧ (∀ (x : lev.U) (z : levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q), x.1 = b * z.1 * b⁻¹ → lev.chi x = ((levTyp lam).comp (Subgroup.inclusion (levUQ_le q _)) * (chiQ q _ σ₀)⁻¹ : levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q →* ℂˣ) z) ∧ (∃ m : ℕ, 0 < m ∧ ∀ κ, lev.chi κ ^ m = 1) ∧ (∀ c, (Y c).1 = y c * b⁻¹) ∧ ∀ c a, (SI c a).1 = st c a := by
  intro F E _ _ _ _ _ _ hc n _ ST SG Q K _ Hw π T f hB hTπ hST hcard hSG hidx lam Θ q hO hQT σ₀ b hbU hbV hbL hbT hbO J hJ bad hb
    cl stab _ lat s y hy hd hs hlat st hinj hr hchr
  subst hJ hb
  classical
  let S := stepOfQ hc n Hw q hB hTπ hST hcard hSG hidx lam hO hQT σ₀
  have hbT' : ∀ v, (T : 𝓞 F) ∈ v.asIdeal →
      (S.Uloc v).map (MulAut.conj (bc (prV (E := E) v) b)).toMonoidHom = S.Uloc v := by
    intro v hv
    rw [S.UlocAlt v hv]
    exact hbT v ((mem_plUnder_iff_norm hc hST T hTπ v).2 hv)
  obtain ⟨S', hLb, hU, hchi⟩ := GlobalTheory.T.exists_stepLevel_conj_baseLatticeUnitary S b hbU hbV hbT' hbO
  have hlam : ∃ m : ℕ, 0 < m ∧ ∀ h, lam h ^ m = 1 := by
    haveI : Finite (GLG (E := E) (n := n) (SG := SG)) := inferInstance
    refine ⟨Nat.card (Subgroup.pi Set.univ Hw : Subgroup (GLG (E := E) (n := n) (SG := SG))), Nat.card_pos, fun h => ?_⟩
    rw [← map_pow, pow_card_eq_one', map_one]
  obtain ⟨m, hm, hM⟩ := stepOfQ_chi_fin hc n Hw q hB hTπ hST hcard hSG hidx lam hO hQT σ₀ hlam hchr
  let e := Equiv.ofBijective _ hs
  let s' : DecoFCl (K := K) n ST SG Q (Subgroup.pi Set.univ Hw) Θ → DecoF E n ST SG Q := fun c => s (e.symm c)
  have hs' : ∀ c, (Quotient.mk'' (s' c) : DecoFCl (K := K) n ST SG Q (Subgroup.pi Set.univ Hw) Θ) = c :=
    fun c => e.apply_symm_apply c
  let y' : DecoFCl (K := K) n ST SG Q (Subgroup.pi Set.univ Hw) Θ → UAd hc n := fun c => ⟨y (e.symm c), hy _⟩
  have hy' : ∀ c, FrOver q (y' c).1 (s' c) := fun c => hd _
  let C := recClsFy q (qdf_frLat q) qdf_frExists s' hs' y' hy'
  have hm' : ∀ c a, st c a ∈ URat hc n := fun c a => by
    obtain ⟨g, hg, -⟩ := (hr c _).1 ⟨a, rfl⟩
    rw [← hg]
    exact ufGL_mem hc n _
  have hYU : ∀ c, y c * b⁻¹ ∈ UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F) :=
    fun c => mul_mem (hy c) (inv_mem hbU)
  refine ⟨S', fun c => ⟨y c * b⁻¹, hYU c⟩, fun c => (st c).codRestrict _ (hm' c), ?_, fun c x => ?_,
    fun c a a' h => hinj c (congrArg Subtype.val h), fun c γ => ?_, hLb, hU, fun x z h => hchi x z h, ?_,
    fun _ => rfl, fun _ _ => rfl⟩
  ·
    have hC : ∀ c, C.y (e c) = ⟨y c, hy c⟩ := fun c => Subtype.ext (congrArg y (e.symm_apply_apply c))
    have hz := C.y_bij.comp e.bijective
    have hz' : Function.Bijective fun c => (Quotient.mk'' (⟨y c, hy c⟩ : UPts hc.sig (1 : Matrix (Fin n) (Fin n) E)
        (FiniteAdeleRing (𝓞 F) F)) : ClassSet ((ratPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)).subgroupOf
          (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)))
        ((levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q).subgroupOf (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)))) := by
      convert hz using 2 with c
      simp only [Function.comp_apply, hC]
    exact dc_mul_inv_bij ((ratPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)).subgroupOf
          (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)))
        ((levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q).subgroupOf (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F)))
        (S'.U.subgroupOf (UPts hc.sig (1 : Matrix (Fin n) (Fin n) E) (FiniteAdeleRing (𝓞 F) F))) ⟨b, hbU⟩ (fun x => by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hU, mem_map_conj]
      rfl) _ hz'
  ·
    have h := decoRaw_carries hc n ST SG (hy c) x
    rw [← rlc_decoOf_val hc n ST SG (hy c), (hd c).1, ← hlat] at h
    refine (h.trans ?_)
    rw [hLb]
    show _ ↔ ((y c * b⁻¹)⁻¹ : GL (Fin n) _).1 *ᵥ x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (baseLb E n ST)
    rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (hbL _).symm
  ·
    have h := C.stabI_range (e c) γ.1 γ.2
    change (⟨γ.1, γ.2⟩ : URat hc n) ∈ (qdStab (hc := hc) (Θ := Θ) (Subgroup.pi Set.univ Hw) (s (e.symm (e c)))).range ↔
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ.1 ∈
        (levUQ hc n ST SG Q (Subgroup.pi Set.univ Hw) q).map (MulAut.conj (y (e.symm (e c)))).toMonoidHom at h
    rw [e.symm_apply_apply, mem_range_qdStab, ← hr] at h
    refine Iff.trans ⟨fun ⟨a, ha⟩ => ⟨a, congrArg Subtype.val ha⟩, fun ⟨a, ha⟩ => ⟨a, Subtype.ext ha⟩⟩ (h.trans ?_)
    rw [hU, mem_map_conj, mem_map_conj, mem_map_conj]
    show _ ↔ b⁻¹ * ((y c * b⁻¹)⁻¹ * _ * (y c * b⁻¹)) * b ∈ _
    have e2 : ∀ g : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F), b⁻¹ * ((y c * b⁻¹)⁻¹ * g * (y c * b⁻¹)) * b = (y c)⁻¹ * g * y c :=
      fun g => by group
    rw [e2]
    exact Iff.rfl
  ·
    refine ⟨m, hm, fun κ => ?_⟩
    have h1 : ∀ x, x ∈ S'.U → b⁻¹ * x * b ∈ S.U := fun x hx => by
      rw [hU, mem_map_conj] at hx
      exact hx
    have hk : b⁻¹ * κ.1 * b ∈ S.U := h1 κ.1 κ.2
    rw [hchi κ ⟨_, hk⟩ (by show κ.1 = b * (b⁻¹ * κ.1 * b) * b⁻¹; group), hM]

end GlobalTheory.Mem.Col2.ChEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFunctionalFrameMinorPolynomialsEqMinorProd
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem.CanonicalSurjection

namespace GlobalTheory.Mem.RangeMinors

theorem exists_dual_sum_smul_eq {V ι : Type} [AddCommGroup V] [Module ℚ V] [Fintype ι] (n : ι → V) (J₀ : ι) :
    ∃ ψ : Module.Dual ℚ V, ∑ J, ψ (n J) • n J = n J₀ := by
  let T : Module.Dual ℚ V →ₗ[ℚ] V :=
    { toFun := fun ψ => ∑ J, ψ (n J) • n J
      map_add' := fun a b => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c a => by simp [Finset.smul_sum, mul_smul] }
  by_contra h
  have hn : n J₀ ∉ LinearMap.range T := fun ⟨ψ, hψ⟩ => h ⟨ψ, hψ⟩
  obtain ⟨φ, hφ, hbot⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hn inferInstance
  have h0 : φ (T φ) = 0 := by
    have : φ (T φ) ∈ (LinearMap.range T).map φ := Submodule.mem_map_of_mem ⟨φ, rfl⟩
    rw [hbot] at this
    simpa using this
  have h1 : ∑ J, φ (n J) * φ (n J) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [T, map_sum] using h0
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun J _ => mul_self_nonneg (φ (n J)))).1 h1 J₀ (Finset.mem_univ _)
  exact hφ (mul_self_eq_zero.1 h2)

theorem exists_dual_baseChange {σ : Type} (k : Type) [Field k] [CharZero k] (ψ : Module.Dual ℚ (MvPolynomial σ ℚ)) :
    ∃ ph : Module.Dual k (MvPolynomial σ k),
      ∀ F : MvPolynomial σ ℚ, ph (MvPolynomial.map (algebraMap ℚ k) F) = algebraMap ℚ k (ψ F) := by
  refine ⟨(MvPolynomial.basisMonomials σ k).constr k fun m => algebraMap ℚ k (ψ (MvPolynomial.monomial m 1)), fun F => ?_⟩
  induction F using MvPolynomial.induction_on' with
  | monomial m a =>
    have e1 : (MvPolynomial.monomial m a : MvPolynomial σ ℚ) = a • MvPolynomial.monomial m 1 := by
      rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    have e2 : MvPolynomial.map (algebraMap ℚ k) (MvPolynomial.monomial m a : MvPolynomial σ ℚ) =
        algebraMap ℚ k a • MvPolynomial.basisMonomials σ k m := by
      rw [MvPolynomial.map_monomial, MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [e2, map_smul, Module.Basis.constr_basis]
    conv_rhs => rw [e1, map_smul, smul_eq_mul, map_mul]
    rw [smul_eq_mul]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), hp, hq, map_add (f := _), map_add (f := _)]

theorem eval_nablaX_eq_minY {Lt k : Type} [Fintype Lt] [DecidableEq Lt] [CommRing k] (N : ℕ) (nu : Lt → YoungDiagram)
    (J : KM.ColChoice N nu) (y : Lt → Fin N → ℕ → k) :
    MvPolynomial.eval (fun v : Lt × ℕ × Fin N => y v.1 v.2.2 v.2.1)
      (MvPolynomial.map (Int.castRingHom k) (KM.nablaX N nu J)) = GL3Columns.minY N nu J y := by
  unfold KM.nablaX GL3Columns.minY
  simp only [map_prod]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  rw [RingHom.map_det, RingHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext i j
  simp

theorem exists_dual_DeX_eq_minY : ∀ (D : D7) (k : Type) [Field k] [CharZero k] (N : ℕ) (nu : Bool × Formalism.MainNotions.G.HH D → YoungDiagram)
    (J : KM.ColChoice N nu), ∃ ph : Module.Dual k (MvPolynomial ((Bool × Formalism.MainNotions.G.HH D) × ℕ × Fin N) k),
      ∀ y : Bool × Formalism.MainNotions.G.HH D → Fin N → ℕ → k, ph (GL3Columns.DeX N nu y) = GL3Columns.minY N nu J y := by
  intro D k _ _ N nu J₀
  classical
  haveI : Finite (KM.ColChoice N nu) := by
    unfold KM.ColChoice
    infer_instance
  letI : Fintype (KM.ColChoice N nu) := Fintype.ofFinite _
  obtain ⟨ψ, hψ⟩ := exists_dual_sum_smul_eq
    (fun J : KM.ColChoice N nu => MvPolynomial.map (Int.castRingHom ℚ) (KM.nablaX N nu J)) J₀
  obtain ⟨ph, hph⟩ := exists_dual_baseChange k ψ
  have hm : ∀ J : KM.ColChoice N nu, MvPolynomial.map (algebraMap ℚ k)
      (MvPolynomial.map (Int.castRingHom ℚ) (KM.nablaX N nu J)) =
      MvPolynomial.map (Int.castRingHom k) (KM.nablaX N nu J) := fun J => by
    rw [MvPolynomial.map_map]
    congr 2
    exact RingHom.ext_int _ _
  refine ⟨ph, fun y => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [GL3Columns.wwCB_holds D k N nu y, finsum_eq_sum_of_fintype, map_sum]
  have h := congrArg (fun F => MvPolynomial.eval (fun v : (Bool × Formalism.MainNotions.G.HH D) × ℕ × Fin N => y v.1 v.2.2 v.2.1)
    (MvPolynomial.map (algebraMap ℚ k) F)) hψ
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum] at h
  rw [hm, eval_nablaX_eq_minY] at h
  rw [← h]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [← MvPolynomial.smul_eq_C_mul, map_smul, ← hm, hph, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, map_mul,
    MvPolynomial.eval_C, hm, eval_nablaX_eq_minY, smul_eq_mul, mul_comm]

end GlobalTheory.Mem.RangeMinors
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReferenceClassMatchingCouplingCosetStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.TC.ChTw GlobalTheory.Mem.Col2.TC.ChTw.Match Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_reference_class_matching_coupling_coset : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ), 1 ≤ i → i < B.R.m →
    ∀ (c : (I.stp u a i).Cl) (b0 : Idx I.sel (I.tup I.mu0) (I.idx I.mu0) i), ∃ c0 : (I.stp u I.mu0 i).Cl, c0.1 = b0 ∧
      ∃ y : GLG (E := B.fields.E) (n := B.R.N i) (SG := (B.primes X).vGs), y ∈ (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) i b0).grp ∧
      ∀ (κ : (I.stp u a i).G c.1) (κ0 : (I.stp u I.mu0 i).G c0.1), (I.stp u a i).gam c.1 κ = 1 → (I.stp u I.mu0 i).gam c0.1 κ0 = 1 →
        κ.2.2 = 1 → (i + 1 = B.R.m → ∀ w, κ0.2.1.1 w = y w * κ.2.1.1 w * (y w)⁻¹) →
        (cosetIn ((I.stp u a i).act c.1 κ ((I.stp u a i).rep c)) = cosetIn ((I.stp u a i).rep c) ↔
          cosetIn ((I.stp u I.mu0 i).act c0.1 κ0 ((I.stp u I.mu0 i).rep c0)) = cosetIn ((I.stp u I.mu0 i).rep c0)) := by
  first | exact @GlobalTheory.Mem.Col2.TC.ChTw.Match.coset_match | exact GlobalTheory.Mem.Col2.TC.ChTw.Match.coset_match | (intros; apply GlobalTheory.Mem.Col2.TC.ChTw.Match.coset_match <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftGroupFormsEqExtendedRationalFormsCompanion
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3

namespace GlobalTheory.Mem.R3.Reads

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {K : Formalism.MainNotions.G.Consts} {Yd : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX}


set_option maxHeartbeats 2000000 in
theorem liftGroupForms_eq_extended_rationalForms_companion (x : TwIn ex) : Formalism.IndefR.RecTie.MtRead x.R.toRealDat x.F.lv2 x.Y.tupT x.Y.hm x.Y.hTop x.Y.hinj x.Y.IL
    (twPOf (divisionPairOfAdelicFormsFaceColumnsData x) x.Y.tupT x.Y.tupTie) := by
  intro μ hμ i v
  have key : ∀ (t : x.T) (μ : D.what₂.Tup) (e : x.Y.tup t = μ) (hμ : Formalism.IndefR.RecTie.Used0 D μ) (e' : x.Y.tupT μ = t)
      (v : D.what₂.MtL μ ((i : ℕ) + 1)),
      HEq (x.Y.IL.jMt μ hμ i (D.what₂.jMt μ ((i : ℕ) + 1) v)).1
        (x.R.toRealDat.extV i t (x.R.toRealDat.jV i t (liftForm x.A3.A x.F.P0 x.F.ψ0 i t ((x.Y.eMt i t).symm (e.symm ▸ v))))) := by
    intro t μ e hμ e' v
    subst e
    have := x.Y.mtRead i t hμ ((x.Y.eMt i t).symm v)
    rw [LinearEquiv.apply_symm_apply] at this
    exact heq_of_eq this
  have := eq_of_heq (key _ μ (x.Y.tupTie μ hμ) hμ rfl v)
  rw [this]
  unfold twPOf
  rw [dite_eq_left hμ]
  rfl



end GlobalTheory.Mem.R3.Reads

end
end

