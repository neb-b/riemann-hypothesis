module

public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0045
public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0009
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0011
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0033
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0044
public import Formalism.SharpRestriction.LevelLetterCocycles.RingHypothesesOfCrystalline
public import Formalism.SharpRestriction.LevelLetterCocycles.EvaluationAtUniformizerPower
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0021
public import Formalism.SharpRestriction.LevelLetterCocycles.JumpsInLetterOfEvenIndex
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0034
public import Formalism.SharpRestriction.LevelLetterCocycles.RingClausesAtUniformizer
public import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowerCongruenceOfAdmitted
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.IsAdicCompleteOfLe
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0019
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0042
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0026
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalClauseOfFrobeniusHyps
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Bundle0012
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.FilDimOf
public import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelClauseOfOpenTool
public import Formalism.SharpRestriction.LevelLetterCocycles.RingConditionOfDeltaInvariants

@[expose] public section

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.InFNcSmul
section
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

variable [IsDomain O] [NeZero n]

variable {W}

def SecCrit0 (A : ArcP n) (c' : ZMod n) (e : ℕ) (T : LocLat G Qp LL O) {d : ℕ} (b : Fin d → W.DD T)
    (sol : Fin d → ℕ → Fin d → LL) : Prop :=
  ∀ (x : W.DD T) (k : ℕ) (f : Fin d → W.EE),
    InFP W T c' (e + 1) 1 (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) • x) →
    RepVV W T c' (e + 1) (A.M PD.p) (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1)) b sol (lA W ^ k • x) f →
    (∀ m, InFr W (c' + ((e + 1 : ℕ) : ZMod n)) (W.π₀ * LamUp W A c' e)
      (ps W 0 ^ A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0) (f m)) →
    (InFNc W T (c' + ((e + 1 : ℕ) : ZMod n)) 1 x ↔
      ∃ κ : ℕ, SecIn W (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1)
        (condNN W T (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) b) fun m => lE W κ * f m)

theorem inFNc_smul (hπ : W.π₀ ∈ W.AΔ) (T : LocLat G Qp LL O) (a : ZMod n) {c : LetA O n} (hc : c ∈ W.AΔ)
    {x : W.DD T} (hx : InFNc W T a 1 x) : InFNc W T a 1 (c • x) := by
  obtain ⟨y, hy, hyl, rfl⟩ := hx
  exact ⟨c • y, Formalism.MainNotions.UnusedSlot80.SatW.smul_mem_NΔ W T hc hy, by rw [smul_comm, hyl], by simp⟩

theorem inFP_up (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (T : LocLat G Qp LL O) (A : ArcP n) (c' : ZMod n)
    (e N : ℕ) {vv : LetA O n} (hv : vv ∈ W.AΔ) (y : W.DD T)
    (hy : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • y)) :
    InFP W T c' (e + 1) 1 (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) • ((ps W 0 ^ N * vv) • W.φD T y)) := by
  obtain ⟨p, hp, hyp⟩ := hy
  rw [one_smul] at hyp
  have hp0Δ : ps W 0 ∈ W.AΔ := ps_mem_AΔ W hR.1 0
  refine ⟨(ps W 0 ^ N * vv * ps W 0 ^ A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0) • W.φD T p,
    Formalism.MainNotions.UnusedSlot80.Relay2.Pp_smul W T c' (e + 1) (W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.pow_mem hp0Δ N) hv)
      (W.AΔ.pow_mem hp0Δ _)) _ (φ_Pp W T c' e p hp), ?_⟩
  rw [one_smul, lam_succ, ← hyp, φD_smulA, smul_smul, smul_smul]
  unfold LamUp
  congr 1; ring

theorem good_zero (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts)
    (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hb : IsHor W T c' b sol) (e : ℕ) : Good A c' e T b sol 0 := by
  have hz : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • (0 : W.DD T)) := by
    rw [smul_zero]; exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_zero W T c' e _
  obtain ⟨κ, Hh, hHh⟩ := horTr_exists W C.hO2 C.hH C.hCA T hT.1 c' b sol hb (A.M PD.p)
  refine good_of_sec C A hA c' hc' T hT b sol hb e 0 hz 0 (fun _ => 0)
    ⟨κ, 0, Hh, fun _ => 0, hHh, fun k => ⟨W.AΔ.zero_mem, by simp⟩, by
      simp only [smul_zero, zero_smul, Finset.sum_const_zero, sub_zero]
      exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_zero W T c' e _⟩
    (fun m => inFr_zero W) 0 ?_
  simpa using secIn_zero W (condNN W T (c' + (e : ZMod n)) e b) (a := c' + (e : ZMod n)) (e := e)

theorem good_sum (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts)
    (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hb : IsHor W T c' b sol) (e : ℕ) {ι : Type} (s : Finset ι) (z : ι → W.DD T)
    (h : ∀ j ∈ s, Good A c' e T b sol (z j)) : Good A c' e T b sol (∑ j ∈ s, z j) := by
  induction s using Finset.induction_on with
  | empty => simpa using good_zero C A hA c' hc' T hT b sol hb e
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact good_add C A hA c' hc' T hT b sol hb e _ _ (h j (Finset.mem_insert_self j s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem φE_lE (t : ℕ) : W.φE (lE W t) = lE W t := by
  unfold lE; rw [map_pow, map_natCast]

theorem step_mp (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts)
    (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hb : IsHor W T c' b sol) (e : ℕ) (IH : Formalism.MainNotions.UnusedSlot80.ArcC.SecCrit W A c' e T d b sol)
    (h0 : SecCrit0 A c' e T b sol) (x : W.DD T)
    (hxP : InFP W T c' (e + 1) 1 (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) • x))
    (hxN : InFNc W T (c' + ((e + 1 : ℕ) : ZMod n)) 1 x) : Good A c' (e + 1) T b sol x := by
  set a : ZMod n := c' + (e : ZMod n) with hadef
  have ha' : c' + ((e + 1 : ℕ) : ZMod n) = a + 1 := by rw [hadef]; push_cast; ring
  set H : ℕ := A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0 with hHdef
  set hq : ℕ := Hw A.G₀ A.S A.η (A.ty (a + 1)) with hqdef
  set U : LetA O n := LamUp W A c' e with hUdef
  have hUΔ : U ∈ W.AΔ := Formalism.MainNotions.UnusedSlot80.ToolsR.φ_AΔ (Formalism.MainNotions.UnusedSlot80.ArcC.lam_mem_AΔ W C.hR.1 A _ e)
  have hp0Δ : ps W 0 ∈ W.AΔ := ps_mem_AΔ W C.hR.1 0
  obtain ⟨m₀, u₀, hu₀, u₁, hu₁, hl, ⟨r₀, hr₀, hu₀e⟩, ⟨s₁, hs₁, hu₁e⟩⟩ :=
    crt W (W.AΔ.mul_mem C.hR.1 (W.AΔ.pow_mem hUΔ 2)) (W.AΔ.pow_mem hp0Δ (H + hq))
      (cop_lamUp W C.hR C.hp0 A c' e (H + hq))

  have g0 : Good A c' (e + 1) T b sol (u₀ • x) := by
    have hz : InFP W T c' (e + 1) 1 (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) • (u₀ • x)) := by
      rw [smul_comm]; exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W T c' (e + 1) _ hu₀ hxP
    obtain ⟨κ, f, hrep, hfr⟩ := secOfP' W C.hinj C.hO2 C.hR C.hTr C.hH C.hCA C.h5p A hA c' (e + 1) T hT.1
      b sol hb x hxP
    have hrep0 := repVV_smul W T c' (e + 1) _ _ b sol _ f hu₀ hrep
    rw [smul_comm] at hrep0
    have hfr0 : ∀ m, InFr W (c' + ((e + 1 : ℕ) : ZMod n)) (W.π₀ * U) (ps W 0 ^ H)
        (algebraMap (LetA O n) W.EE u₀ * f m) := by
      intro m
      obtain ⟨t, ht, hft⟩ := hfr m
      refine ⟨r₀ * t, W.AΔ.mul_mem hr₀ ht, ?_⟩
      rw [lam_succ] at hft
      rw [hu₀e]
      simp only [map_mul, map_pow, map_one] at hft ⊢
      linear_combination (algebraMap (LetA O n) W.EE W.π₀ * algebraMap (LetA O n) W.EE U *
        algebraMap (LetA O n) W.EE r₀) * hft
    obtain ⟨κ₀, hS⟩ := (h0 (u₀ • x) κ _ hz hrep0 hfr0).1 (inFNc_smul C.hR.1 T _ hu₀ hxN)
    exact good_of_sec C A hA c' hc' T hT b sol hb (e + 1) _ hz κ _ hrep0 (fun m => inFr_mulA W (hfr m) hu₀) κ₀ hS

  obtain ⟨r, bb, β, hbb, hβ, hdec⟩ := exists_smul_pow_eq_sum_of_inFNc C T A hA hT a hq le_rfl x (by rwa [ha'] at hxN)
  have h5T := C.h5 T _ _ hT.1 (jumpsLet_of_win W A hA T hT)
  have gj : ∀ j, Good A c' (e + 1) T b sol ((ps W 0 ^ H * (s₁ * β j)) • W.φD T (bb j)) := by
    intro j
    have hbl : (letE a : LetA O n) • bb j = bb j := Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W T a (hbb j).2
    have hbN : InFNc W T a 1 (bb j) := ⟨bb j, (hbb j).1, hbl, (one_smul _ _).symm⟩
    have hbP : InFP W T c' e 1 (abelian₂ W A a e • bb j) :=
      Formalism.MainNotions.UnusedSlot80.ArcC.arc_down W C.hs C.hR T A hA h5T (C.hmod T hT.1) C.hΔ c' hc' e (bb j) hbN
    obtain ⟨κj, fj, hrepj, hfrj⟩ := secOfP' W C.hinj C.hO2 C.hR C.hTr C.hH C.hCA C.h5p A hA c' e T hT.1
      b sol hb (bb j) hbP
    obtain ⟨κ'j, hSj⟩ := (IH (bb j) κj fj hbP hrepj hfrj).1 hbN
    have hv : s₁ * β j ∈ W.AΔ := W.AΔ.mul_mem hs₁ (hβ j)
    have hPκ : InFP W T c' e 1 (abelian₂ W A (c' + (e : ZMod n)) e • (lA W ^ κj • bb j)) := by
      rw [smul_comm]; exact Formalism.MainNotions.UnusedSlot80.Relay2.inMultiple_smul W T c' e _ (lA_mem W κj) hbP
    obtain ⟨-, hrep', -⟩ := transport W C.hR C.hp0 T A c' e (A.M PD.p) b sol (lA W ^ κj • bb j) fj hPκ
      (by simpa using hrepj) hfrj H le_rfl hv
    have hel : (ps W 0 ^ H * (s₁ * β j)) • W.φD T (lA W ^ κj • bb j) =
        lA W ^ κj • ((ps W 0 ^ H * (s₁ * β j)) • W.φD T (bb j)) := by
      rw [φD_smulA, φA_lA, smul_comm]
    rw [hel] at hrep'
    have hlow0 : ∀ c₀ : Fin d → O, dvO W T (e + 1) b c₀ ∈ FilS W T (a + 1) 0 (-(H : ℤ)) := by
      intro c₀
      have := dvO_filLow W C.hbij A hA c' hc' T hT b hb.1 (e + 1) 0 (by omega) c₀
      rw [hHdef, ha']; rwa [ha'] at this
    have hS' := secIn_transport W T a e b H hv C.hR.1 hlow0 _ hSj
    rw [← ha'] at hS'
    refine good_of_sec C A hA c' hc' T hT b sol hb (e + 1) _ (inFP_up C.hR T A c' e H hv (bb j) hbP) κj _ hrep'
      (fun m => (transport W C.hR C.hp0 T A c' e (A.M PD.p) b sol (lA W ^ κj • bb j) fj hPκ
        (by simpa using hrepj) hfrj H le_rfl hv).2.2 m) κ'j ?_
    convert hS' using 1
    funext m
    rw [map_mul W.φE, φE_lE]
    ring
  have hu₁x : u₁ • x = ∑ j, (ps W 0 ^ H * (s₁ * β j)) • W.φD T (bb j) := by
    rw [hu₁e, show ps W 0 ^ (H + hq) * s₁ = (ps W 0 ^ H * s₁) * ps W 0 ^ hq by ring, mul_smul, hdec,
      Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul]; congr 1; ring
  have g1 : Good A c' (e + 1) T b sol (u₁ • x) := by
    rw [hu₁x]
    exact good_sum C A hA c' hc' T hT b sol hb (e + 1) _ _ fun j _ => gj j
  have g2 : Good A c' (e + 1) T b sol (lA W ^ m₀ • x) := by
    rw [hl, add_smul]
    exact good_add C A hA c' hc' T hT b sol hb (e + 1) _ _ g0 g1
  exact good_of_lpow C A hA c' hc' T hT b sol hb (e + 1) m₀ x hxP g2

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.UniformizerClauseOfAdmitted
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.bigCellDetWeightedEnergyIntegral

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9

variable (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
variable {CR CA CB CK : ℝ}

theorem caseA_loc' {l : ℕ} [Fact l.Prime] {K LL : Loc.FinExt l} (hg : Loc.Good K 1 LL)
    (hCA : Formalism.MainNotions.LiftingTheory.CaseA ((HW l).W K 1 LL hg)) : Loc.CaseA K LL := by
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  refine ⟨fun x hx => ?_, by rw [← hpl]; exact hCA.2.2, hg⟩
  obtain ⟨y, hy⟩ := hCA.1.2 ⟨x, hx⟩
  have h2 := y.2.2
  have : ((y : ↥(K0 K)) : Om l) = x := congrArg Subtype.val hy
  rw [this] at h2
  exact h2

theorem laurent_clause_of_admitted' (hA : admitted D HW F Cm CR CA CB CK) : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm :=
  fun l _ K s LL h => (hA.1 l K s LL h).2.2.2.1

theorem uniformizer_clause_of_admitted (hA : admitted D HW F Cm CR CA CB CK) : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F :=
  fun l _ K s LL h => (hA.1 l K s LL h).2.2.2.2.2.2.2.2.1

theorem level_tools_of_admitted' (hA : admitted D HW F Cm CR CA CB CK) : Formalism.MainNotions.WachCoordinates.adm7 D HW F Cm :=
  Formalism.MainNotions.UnusedSlot80.tools_unramified_statement D HW F Cm ⟨fun l _ K s LL h => (hA.1 l K s LL h).2.2.1, laurent_clause_of_admitted' D HW F Cm hA,
    uniformizer_clause_of_admitted D HW F Cm hA⟩


set_option maxHeartbeats 0 in
theorem dual_lemma_of_admitted (hA : admitted D HW F Cm CR CA CB CK) (l : ℕ) [Fact l.Prime] (K LL : Loc.FinExt l)
    (hg : Loc.Good K 1 LL) [NeZero (Module.finrank ℚ_[l] ↥(Loc.K0 K))] : LemmaDN ((HW l).W K 1 LL hg) := by
  intro d T₁ T₂ F' b S η m hset
  have hCA : Formalism.MainNotions.LiftingTheory.CaseA ((HW l).W K 1 LL hg) := hset.1
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hCAl : Loc.CaseA K LL := caseA_loc' D HW hg hCA
  have h5l : 5 ≤ l := by have := hset.2.1; rw [hpl] at this; omega
  set W := (HW l).W K 1 LL hg with hW
  have h1 := hA.1 l K 1 LL hg
  have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W := h1.2.2.2.2.2.2.2.2.1
  obtain ⟨hE, hC, hQ⟩ := hA.2.2.2.2.2.2.2.2.2.2.1 l K LL
  have hs : W.s = 1 := hCA.2.1
  haveI : IsFractionRing ↥(OL LL) ↥LL.1 := Formalism.MainNotions.UnusedSlot80.BCF.isFrac_OL LL
  haveI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) := Formalism.MainNotions.RamifiedCoefficientChains.S9.DLev.complete_max LL
  have hring : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W :=
    (((h9 _ (Formalism.MainNotions.LiftingTheory.gen_one_crys W)) hs hCA.2.2).2.2 (Formalism.MainNotions.UnusedSlot80.finrank_K0_eq_one_of_le_Kur hCAl.1)).1
  have C := ((Cm l).C K 1 LL hg).tie
  have hG := Formalism.MainNotions.N.Pv.LocalLengthBound.gam_of_tie W hs C
  have hLev : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W := (level_tools_of_admitted' D HW F Cm hA l K LL hCAl h5l).2
  have hRu : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules W := Formalism.MainNotions.N.Pv.LocalLengthBound.expRules_of W hLev hG.1 hG.2
  have hRing : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRing W := Formalism.MainNotions.N.Pv.LocalLengthBound.expRing_of W hring
  have hpt := Formalism.MainNotions.UnusedSlot80.points_exist_of_ring_condition D HW F (uniformizer_clause_of_admitted D HW F Cm hA)
  have hL := Formalism.MainNotions.UnusedSlot80.levCoeff_of_pt D HW F Cm (laurent_clause_of_admitted' D HW F Cm hA) hpt
  have hBall : ∀ (l' : ℕ) [Fact l'.Prime] (K' LL' : FinExt l') (hg' : Good K' 1 LL')
      [NeZero (Module.finrank ℚ_[l'] ↥(K0 K'))], Formalism.MainNotions.RamifiedCoefficientChains.Sh.BasTool ((HW l').W K' 1 LL' hg') := by
    intro l' _ K' LL' hg' _
    haveI : IsFractionRing ↥(OL LL') ↥LL'.1 := Formalism.MainNotions.UnusedSlot80.BCF.isFrac_OL LL'
    exact Formalism.MainNotions.RamifiedCoefficientChains.Sh.basTool_of _ (hA.1 l' K' 1 LL' hg').2.2.2.2.2.2.2.2.1
  have hEC : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpCrit W :=
    Formalism.MainNotions.N.Pv.LocalLengthBound.expCrit_D' D HW F Cm CR CA CB CK hA hL hBall l K LL hCAl h5l
  have hGM := Formalism.MainNotions.RamifiedCoefficientChains.S9.GM.gMem_of W hE hC hQ h1.2.2.2.2.1 h9 hRu hEC
  have hBas : Formalism.MainNotions.RamifiedCoefficientChains.Sh.BasTool W := Formalism.MainNotions.RamifiedCoefficientChains.Sh.basTool_of W h9
  have hΔ : IsUnit ((W.DelF.card : ℕ) : ↥(OL LL)) := by
    have hcard : W.DelF.card = l - 1 :=
      Formalism.MainNotions.UnusedSlot80.LevR.card_delF D HW F (uniformizer_clause_of_admitted D HW F Cm hA) l K LL hCAl
    by_contra hnu
    have hm : ((W.DelF.card : ℕ) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := hnu
    have hlm := Formalism.BasicNotions.Examples₂.LB.l_mem_max LL
    have e : ((l : ℕ) : ↥(OL LL)) - ((W.DelF.card : ℕ) : ↥(OL LL)) = 1 := by
      rw [hcard, Nat.cast_sub (by omega)]; simp
    have h3 := Submodule.sub_mem _ hlm hm
    rw [e] at h3
    exact (IsLocalRing.maximalIdeal.isMaximal ↥(OL LL)).ne_top ((Ideal.eq_top_iff_one _).2 h3)
  have hTH : Formalism.MainNotions.CrystallineLiftingInputs.THor W := Formalism.MainNotions.CrystallineLiftingInputs.Tools.frobenius_power_congruence_local D HW F Cm hA.1 l K LL hg
  have hZ := Formalism.MainNotions.RamifiedCoefficientChains.Sh.ZT.zTool_of W h9 (((Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData.truncation_clause_of_lattice_hypotheses D HW F Cm (uniformizer_clause_of_admitted D HW F Cm hA) hA.2.2.2.2.2.2.2.1 hA.2.2.2.2.2.2.2.2.1).2 l K LL hg).2) hTH hBas hRu
    hRing hΔ
  have hAd : Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB.AdaptBas W :=
    Formalism.MainNotions.RamifiedCoefficientChains.S9.AdM.adaptBas_of W hE hC hQ h1.2.2.1 h1.2.2.2.2.1 h9 (Formalism.MainNotions.WachCoordinates.Br.valRing_rec (D.loc l) LL)
  have hpm : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := by
    rw [hpl]; exact Formalism.BasicNotions.Examples₂.LB.l_mem_max LL
  have hPt : Formalism.MainNotions.LiftingTheory.CaseA W → ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1),
      IsPrimitiveRoot ζ ((D.loc l).PD K).p →
      ∃ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, Formalism.MainNotions.LiftingTheory.Over W τ i ∧ Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hg i ζ τ := by
    intro _ c ζ hζ
    obtain ⟨τ, hτ⟩ := hpt l K LL hCAl h5l c ζ (by rwa [hpl] at hζ)
    refine ⟨τ, ?_, hτ⟩
    obtain ⟨τs, ⟨hemb, -⟩, hres⟩ := hτ
    apply AlgHom.ext
    intro x
    have hy : (x : Om l) ∈ Ks K 1 := (le_sup_left : K0 K ≤ Ks K 1) x.2
    show τ (algebraMap ↥(K0 K) ↥K.1 x) = _
    rw [hres (algebraMap ↥(K0 K) ↥K.1 x) ⟨x, hy⟩ rfl]
    exact hemb x ⟨x, hy⟩ rfl
  have hDT : Formalism.MainNotions.RamifiedCoefficientChains.Sh.DetTool W :=
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.detTool_of W h9 _ h1.2.2.2.1 hPt hQ hpm hset.2.2.2.2.1
  have hDet := Formalism.MainNotions.RamifiedCoefficientChains.S9.DetA.detAlg_of W hE hC hQ h1.2.2.2.2.1 h9 hBas (fun _ => hDT)
    (Formalism.MainNotions.RamifiedCoefficientChains.S9.GCoord.gCoord_holds W)
  exact Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS.lemmaDN_of_S1E W hZ hAd hGM hDet d T₁ T₂ F' b S η m hset

end Formalism.MainNotions.RamifiedCoefficientChains.S9.bigCellDetWeightedEnergyIntegral
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.UniformizerClauseOfAdmittedAlt
section
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.LocalLemmasFromLiterature

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9

variable (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
variable {CR CA CB CK : ℝ}

theorem caseA_loc' {l : ℕ} [Fact l.Prime] {K LL : Loc.FinExt l} (hg : Loc.Good K 1 LL)
    (hCA : Formalism.MainNotions.LiftingTheory.CaseA ((HW l).W K 1 LL hg)) : Loc.CaseA K LL := by
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  refine ⟨fun x hx => ?_, by rw [← hpl]; exact hCA.2.2, hg⟩
  obtain ⟨y, hy⟩ := hCA.1.2 ⟨x, hx⟩
  have h2 := y.2.2
  have : ((y : ↥(K0 K)) : Om l) = x := congrArg Subtype.val hy
  rw [this] at h2
  exact h2

theorem laurent_clause_of_admitted' (hA : admitted D HW F Cm CR CA CB CK) : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm :=
  fun l _ K s LL h => (hA.1 l K s LL h).2.2.2.1

theorem uniformizer_clause_of_admitted (hA : admitted D HW F Cm CR CA CB CK) : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F :=
  fun l _ K s LL h => (hA.1 l K s LL h).2.2.2.2.2.2.2.2.1

theorem level_tools_of_admitted' (hA : admitted D HW F Cm CR CA CB CK) : Formalism.MainNotions.WachCoordinates.adm7 D HW F Cm :=
  Formalism.MainNotions.UnusedSlot80.tools_unramified_statement D HW F Cm ⟨fun l _ K s LL h => (hA.1 l K s LL h).2.2.1, laurent_clause_of_admitted' D HW F Cm hA,
    uniformizer_clause_of_admitted D HW F Cm hA⟩


set_option maxHeartbeats 0 in
theorem local_lemmas_of_literature (hA : admitted D HW F Cm CR CA CB CK) (h23 : Formalism.MainNotions.LiftingTheory.adm23 D HW F)
    (hHerr : Formalism.MainNotions.ElementDenominator.HerrClassNaturalExtension D.loc D.locA HW F) (a22 : Formalism.MainNotions.CrystallineLiftingBounds.adm22 D HW F)
    (hFont : Formalism.MainNotions.InvariantsGenerators.LitFont D HW F) : cocyclesToWachVectorsBoundAtGoodExtensions D HW F := by
  intro l _ K LL hg _
  intro d T₁ T₂ F' b S η m hset
  have hCA : Formalism.MainNotions.LiftingTheory.CaseA ((HW l).W K 1 LL hg) := hset.1
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hCAl : Loc.CaseA K LL := caseA_loc' D HW hg hCA
  have h5l : 5 ≤ l := by have := hset.2.1; rw [hpl] at this; omega
  set W := (HW l).W K 1 LL hg with hW
  have h1 := hA.1 l K 1 LL hg
  have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W := h1.2.2.2.2.2.2.2.2.1
  obtain ⟨hE, hC, hQ⟩ := hA.2.2.2.2.2.2.2.2.2.2.1 l K LL
  have hs : W.s = 1 := hCA.2.1
  haveI : IsFractionRing ↥(OL LL) ↥LL.1 := Formalism.MainNotions.UnusedSlot80.BCF.isFrac_OL LL
  haveI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  have hring : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W :=
    (((h9 _ (Formalism.MainNotions.LiftingTheory.gen_one_crys W)) hs hCA.2.2).2.2 (Formalism.MainNotions.UnusedSlot80.finrank_K0_eq_one_of_le_Kur hCAl.1)).1
  have C := ((Cm l).C K 1 LL hg).tie
  have hG := Formalism.MainNotions.N.Pv.LocalLengthBound.gam_of_tie W hs C
  have hLev : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W := (level_tools_of_admitted' D HW F Cm hA l K LL hCAl h5l).2
  have hRu : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules W := Formalism.MainNotions.N.Pv.LocalLengthBound.expRules_of W hLev hG.1 hG.2
  have hRing : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRing W := Formalism.MainNotions.N.Pv.LocalLengthBound.expRing_of W hring
  have hpt := Formalism.MainNotions.UnusedSlot80.points_exist_of_ring_condition D HW F (uniformizer_clause_of_admitted D HW F Cm hA)
  have hL := Formalism.MainNotions.UnusedSlot80.levCoeff_of_pt D HW F Cm (laurent_clause_of_admitted' D HW F Cm hA) hpt
  have hBas : Formalism.MainNotions.RamifiedCoefficientChains.Sh.BasTool W := Formalism.MainNotions.RamifiedCoefficientChains.Sh.basTool_of W h9
  have hK : Formalism.MainNotions.RamifiedCoefficientChains.Sh.LemK W := Formalism.MainNotions.N.Pv.LocalLengthBound.lemK_D D HW F Cm CR CA CB CK hA hL l K LL hCAl h5l
  have hFD : Formalism.MainNotions.RamifiedCoefficientChains.Sh.FilDim W := Formalism.MainNotions.N.Pv.LocalLengthBound.filDim_of W hQ
  have hΔ : IsUnit ((W.DelF.card : ℕ) : ↥(OL LL)) := by
    have hcard : W.DelF.card = l - 1 :=
      Formalism.MainNotions.UnusedSlot80.LevR.card_delF D HW F (uniformizer_clause_of_admitted D HW F Cm hA) l K LL hCAl
    by_contra hnu
    have hm : ((W.DelF.card : ℕ) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := hnu
    have hlm := Formalism.BasicNotions.Examples₂.LB.l_mem_max LL
    have e : ((l : ℕ) : ↥(OL LL)) - ((W.DelF.card : ℕ) : ↥(OL LL)) = 1 := by
      rw [hcard, Nat.cast_sub (by omega)]; simp
    have h3 := Submodule.sub_mem _ hlm hm
    rw [e] at h3
    exact (IsLocalRing.maximalIdeal.isMaximal ↥(OL LL)).ne_top ((Ideal.eq_top_iff_one _).2 h3)
  have hP9π : Formalism.MainNotions.LiftingTheory.P9π₀ W := (Formalism.MainNotions.LiftingTheory.uniformizer_ring_and_module_clauses W h9 hCA _ (Formalism.MainNotions.LiftingTheory.gen_one_crys W)).1
  have hRN : Formalism.MainNotions.LiftingTheory.CaseA W → Formalism.MainNotions.CrystallineLiftingInputs.RToolNum W := fun hCA' =>
    Formalism.MainNotions.CrystallineLiftingInputs.RToolNum_holds (D.loc l) (HW l) K LL hg hCA'
  have hDss : Formalism.MainNotions.RamifiedCoefficientChains.DssLet W := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 l K 1 LL hg
  have hS1 : Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step1 W :=
    Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.first_lift_of_uniformizer_clause W (Formalism.MainNotions.WachCoordinates.Br.valRing_rec (D.loc l) LL) hP9π hRN h9 hDss hRu hRing hK hFD
      hBas hE hC hQ
  have hTZ' : Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.TTool2Z W :=
    Formalism.MainNotions.CrystallineLiftingInputs.truncatedSeriesData.tTool2Z_DU D HW F (uniformizer_clause_of_admitted D HW F Cm hA) hA.2.2.2.2.2.2.2.1 hA.2.2.2.2.2.2.2.2.1 l K LL hg
  have hFT : Formalism.MainNotions.CrystallineLiftingInputs.FTool W := Formalism.MainNotions.CrystallineLiftingInputs.Tools.local_clause_of_admitted_statements D HW F Cm hA l K LL hg
  have h2a : ∀ T : LocLat _ ℚ_[l] ↥LL.1 ↥(OL LL), IsCrys _ T.ρ → Formalism.MainNotions.DeltaInvariantLattices.p2aK W T :=
    fun T hT => ((hA.2.2.1 l K 1 LL hg).1 T hT).2
  have hS2 : Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2 W :=
    Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.second_lift_of_hypotheses W hTZ' hFT hBas hK hFD hRing hRu h2a h1.2.2.2.2.1 h9 hE hC hQ
  have hQT : Formalism.MainNotions.CrystallineLiftingInputs.QTool W := Formalism.MainNotions.CrystallineLiftingInputs.Tools.level_clause_of_admitted_statements D HW F Cm hA h23 l K LL hg
  have hdex : W.DelF.card = ((D.loc l).PD K).p - 1 → ∃ dd : ↥(OL LL), dd * (W.DelF.card : ↥(OL LL)) = 1 :=
    fun _ => hΔ.exists_left_inv
  have hExt : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExtTool W :=
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.extData_extTool W (hHerr l K 1 LL hg).2.2.2 (Formalism.MainNotions.LiftingTheory.liftb_HExt_holds D HW F l K 1 LL hg)
      (Formalism.MainNotions.LiftingTheory.liftb_HOne_holds D HW F l K 1 LL hg) (Formalism.MainNotions.LiftingTheory.lker_HKer_D D HW F a22 l K 1 LL hg)
      (h23 l K LL) ((hFont l K LL hCAl).2.1) hdex h1.2.2.2.2.1 h1.2.2.2.2.2.1 h9 hQT
  exact Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.cocyclesToWachVectorsBound_of_extTool W hExt hS1 hS2 d T₁ T₂ F' b S η m hset

end Formalism.MainNotions.RamifiedCoefficientChains.S9.LocalLemmasFromLiterature
end
end

