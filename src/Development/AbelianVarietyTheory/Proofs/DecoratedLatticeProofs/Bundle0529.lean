module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0475
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0489
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.XiStdEqConstMulLocXi
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0461
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0379
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMemberStepCharts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0266
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0273
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0467
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainCompositeLiftIntertwinesFiniteGroupActions
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0144
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0144
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0526
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceBaseVacuumDatumExistsUnique
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaSliceLineSumEqIntertwinerImage
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0467
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsClopenIsCompactQLat
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CommuteOfOff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil
open ValuativeRel

noncomputable section
section Gen

open Formalism.L2.Col Formalism.L2.Ker Formalism.UG GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.MemChart

namespace GlobalTheory.PenLevTyp

theorem commute_of_off {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {v : HeightOneSpectrum (𝓞 F)} {x k : GL (Fin n) (AfE F E)} (hx : ∀ w, w ≠ v → bc (prV (E := E) w) x = 1)
    (hk : bc (prV (E := E) v) k = 1) : x * k = k * x := by
  have key : ∀ w, bc (prV (E := E) w) (x * k) = bc (prV (E := E) w) (k * x) := fun w => by
    rw [map_mul, map_mul]
    by_cases hw : w = v
    · subst hw
      rw [hk, mul_one, one_mul]
    · rw [hx w hw, mul_one, one_mul]
  apply Units.ext
  ext r s
  refine sub_eq_zero.1 (Formalism.UG.P.afsplit_inj _ fun w => ?_)
  rw [map_sub, sub_eq_zero]
  exact congrArg (fun g : GL (Fin n) _ => g.1 r s) (key w)

theorem fr_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} {g g' : GL (Fin n) (AfE F E)}
    {p p' : DecoF E n ST SG Q} (h : IsPtOf hc g p) (h' : IsPtOf hc g' p') (P : Q)
    (e0 : ∀ i j, adAt F P.1 (g.1 i j) = adAt F P.1 (g'.1 i j)) : p.fr P = p'.fr P := by
  have e : ∀ i j, p.fr P (Pi.single j 1) i = p'.fr P (Pi.single j 1) i := fun i j =>
    (algebraMap E (P.1.adicCompletion E)).injective ((h.fr P i j).symm.trans ((e0 i j).trans (h'.fr P i j)))
  apply LinearEquiv.toLinearMap_injective
  refine LinearMap.pi_ext fun j x => ?_
  have hs : (Pi.single j x : Sp E n) = x • Pi.single j 1 := by
    rw [← Pi.single_smul', smul_eq_mul, mul_one]
  simp only [LinearEquiv.coe_coe]
  rw [hs, map_smul, map_smul]
  funext i
  simp only [Pi.smul_apply, e]

theorem exists_pt {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} [NeZero n] {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} {g g' : GL (Fin n) (AfE F E)}
    {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) (hg' : g' ∈ UAd hc n)
    (e0 : ∀ P ∈ Q, ∀ i j, adAt F P (g'.1 i j) = adAt F P (g.1 i j)) : ∃ p' : DecoF E n ST SG Q, IsPtOf hc g' p' := by
  refine GlobalTheory.Mem.Col2.RatFrPt.exists_isPtOf_of_rat hc ST SG Q g' hg' fun P hP => ?_
  let f := p.fr ⟨P, hP⟩
  refine ⟨⟨LinearMap.toMatrix' f.toLinearMap, LinearMap.toMatrix' f.symm.toLinearMap, ?_, ?_⟩, fun r s => ?_⟩
  · rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_symm, LinearMap.toMatrix'_id]
  · rw [← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp, LinearMap.toMatrix'_id]
  · rw [e0 P hP, h.fr ⟨P, hP⟩ r s]
    simp only [LinearMap.toMatrix'_apply, LinearEquiv.coe_coe]
    rfl

section Pt

variable {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S S' : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {mu' : Tup X.F X.E X.K S'} {cst' : LocCst X (rowSG Pr sel mu')}
  {u : Pr.Word} {j : ℕ}

theorem coset_at (q : PtAt R sel mu cst u j) (h : j + 1 = R.m) {y : Sp X.E (R.N j)} (hy0 : y ∈ q.1.2) (w : Pr.vGs) :
    cosetIn q ⟨w.1, Finset.mem_union_left _ w.2⟩ = {z | z - (q.1.1.deco.1.liftFr w).symm y ∈ stdAt X.E (R.N j) w.1} ∧
      ((qOf w.1 : ℕ) : X.E) • (q.1.1.deco.1.liftFr w).symm y ∈ stdAt X.E (R.N j) w.1 ∧
      bar q w = {redV w.1 (((qOf w.1 : ℕ) : X.E) • (q.1.1.deco.1.liftFr w).symm y)} := by
  obtain ⟨y₀, hy₀, hY⟩ := q.mem_ybSet h
  have hd := q.1.1.deco.2
  have hf := GlobalTheory.TopStep.liftFr_spec hd w
  have h1 : ((qOf w.1 : ℕ) : X.E) • y₀ ∈ Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal q.1.1.deco.1.N := by
    have := (Formalism.L2.Col.mem_locLat _ _ _ _).1 hy₀ ⟨w.1, Finset.mem_union_left _ w.2⟩
    simpa [w.2] using this
  have h2 : ∀ z ∈ q.1.2, z - y₀ ∈ Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal q.1.1.deco.1.N := fun z hz => by
    rw [hY, Set.mem_setOf_eq, Formalism.L2.Col.mem_locLat] at hz
    simpa [w.2] using hz ⟨w.1, Finset.mem_union_left _ w.2⟩
  have h3 : ∀ z ∈ q.1.2, z - y ∈ Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal q.1.1.deco.1.N := fun z hz => by
    have := sub_mem (h2 z hz) (h2 y hy0)
    rwa [sub_sub_sub_cancel_right] at this
  have hq : ((qOf w.1 : ℕ) : X.E) • y ∈ Formalism.HermitianLatticesTheory.localization₂ w.1.asIdeal q.1.1.deco.1.N := by
    have := add_mem h1 (GlobalTheory.TopStep.smul_mem_locP (GlobalTheory.TopStep.intAt_nat (qOf w.1)) (h2 y hy0))
    rwa [← smul_add, add_sub_cancel] at this
  have hs : (q.1.1.deco.1.liftFr w).symm (((qOf w.1 : ℕ) : X.E) • y) ∈ stdAt X.E _ w.1 :=
    (hf.1 _).1 (by rw [LinearEquiv.apply_symm_apply]; exact hq)
  refine ⟨?_, by rw [← map_smul]; exact hs, ?_⟩
  · have hfr : frsF sel mu q.1.1 ⟨w.1, Finset.mem_union_left _ w.2⟩ = q.1.1.deco.1.liftFr w := dif_pos w.2
    ext z
    simp only [cosetIn, Set.mem_setOf_eq, if_pos w.2, pow_zero, inv_one, one_smul, hfr]
    constructor
    · rintro ⟨y', hy', hz⟩
      have h1 : (q.1.1.deco.1.liftFr w).symm y' - (q.1.1.deco.1.liftFr w).symm y ∈ stdAt X.E (R.N j) w.1 := by
        rw [← map_sub]
        exact (hf.1 _).1 (by rw [LinearEquiv.apply_symm_apply]; exact h3 y' hy')
      have := add_mem hz h1
      rwa [sub_add_sub_cancel] at this
    · exact fun hz => ⟨y, hy0, hz⟩
  · have key : q.1.1.deco.1.be w (((qOf w.1 : ℕ) : X.E) • y) =
        redV w.1 (((qOf w.1 : ℕ) : X.E) • (q.1.1.deco.1.liftFr w).symm y) := by
      rw [← map_smul, ← hf.2 _ hs, LinearEquiv.apply_symm_apply]
    ext v
    simp only [bar, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← key]
      have ht : z - y ∈ q.1.1.deco.1.at w.1 := h3 z hz
      have e : ((qOf w.1 : ℕ) : X.E) • z = ((qOf w.1 : ℕ) : X.E) • y + ((qOf w.1 : ℕ) : X.E) • (z - y) := by
        rw [← smul_add, add_sub_cancel]
      rw [e, hd.be_add w _ hq _ (GlobalTheory.TopStep.smul_mem_locP (GlobalTheory.TopStep.intAt_nat _) ht),
        GlobalTheory.TopStep.be_smul_int hd w (GlobalTheory.TopStep.intAt_nat _) ht, GlobalTheory.TopStep.reduction_absNorm_eq_zero, zero_smul, add_zero]
    · rintro rfl
      exact ⟨y, hy0, key.symm⟩

theorem cos_iff_bar (h : j + 1 = R.m) (w : Pr.vGs) (hq : ((qOf w.1 : ℕ) : 𝓞 X.E) ∉ w.1.asIdeal ^ 2) (q : PtAt R sel mu cst u j)
    (q' : PtAt R sel mu' cst' u j) :
    cosetIn q ⟨w.1, Finset.mem_union_left _ w.2⟩ = cosetIn q' ⟨w.1, Finset.mem_union_left _ w.2⟩ ↔ bar q w = bar q' w := by
  obtain ⟨h1, h2, h3⟩ := coset_at q h (q.repY_mem h) w
  obtain ⟨h1', h2', h3'⟩ := coset_at q' h (q'.repY_mem h) w
  rw [h1, h1', h3, h3', Set.singleton_eq_singleton_iff]
  exact coset_eq_iff_redV hq h2 h2'

end Pt

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X)

theorem levGAt_eq (hTw : TC.IsTw I) (a : I.ι) (j : ℕ) (hj : j < B.R.m) (b : Idx I.sel (I.tup a) (I.idx a) j) :
    levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) j b = colLevSym I.Ch j := by
  have h1 : levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) j b = (I.idx a).levG j (b.get hj) := by
    unfold levGAt
    rw [← Idx.some_get b hj]
    rfl
  have h2 : ∀ b', (I.idx a).levG j b' = colLevSym I.Ch j := by
    rw [(hTw a).2]
    exact fun _ => rfl
  rw [h1, h2]


set_option maxHeartbeats 2000000 in
theorem mem_lev_iff (hI : I.Ok) (hTw : TC.IsTw I) (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) (j : ℕ) (hj : j + 1 = B.R.m)
    [NeZero (B.R.N j)] {Ch : Type} {chOf : (I.stp u a j).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N j) → B.host.E)} {U : Ch → Subgroup (TC.GA B (B.R.N j))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u a j).Cl → TC.GA B (B.R.N j)} {st : ∀ c, (I.stp u a j).Stab c → GL (Fin (B.R.N j)) B.host.E}
    {k : Ch → TC.GA B (B.R.N j)} (hR : I.Reads u a j chOf Lb U chi y st k) (c : (I.stp u a j).Cl)
    (x : TC.GA B (B.R.N j)) (hx : x ∈ UAd B.sp.cm (B.R.N j)) (hc : x * k (chOf c) = k (chOf c) * x)
    (hc₀ : x * TC.kStd X u (B.R.N j) = TC.kStd X u (B.R.N j) * x)
    (h1 : ∀ P ∈ I.Q a, x.1.map (adAt B.host.F P) = 1) :
    x ∈ U (chOf c) ↔ x ∈ levU (F := B.host.F) B.sp.cm (B.R.N j) ((B.primes X).vT u) (B.primes X).vGs
      (chG (X := B.fields) (colLevSym I.Ch j) (bar (show PtAt B.R I.sel (I.tup a) (I.cst a) u j from (I.stp u a j).rep c))) := by
  have hy0 : IsPtOf B.sp.cm (y c * k (chOf c)) ((I.stp u a j).rep c).1.1 :=
    IsPtOf.of_extTo (I.Q_subset_SQ a)
      ((GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).2.1.mono_right (I.Q_subset_SQ a)) (hR.pt c)
  obtain ⟨g, hgd⟩ : ∃ g, g * TC.kStd X u (B.R.N j) = y c * k (chOf c) := ⟨_, inv_mul_cancel_right _ _⟩
  have hgx : g * x * TC.kStd X u (B.R.N j) = y c * x * k (chOf c) := by
    rw [mul_assoc, hc₀, ← mul_assoc, hgd, mul_assoc, ← hc, mul_assoc]
  rw [← hgd] at hy0
  have hg := dia_of_pt hPr u hy0
  have hk : TC.kStd X u (B.R.N j) ∈ UAd B.sp.cm (B.R.N j) := (kStd_spec hPr u (B.R.N j)).1.choose_spec.1.uni
  have e0 : ∀ P ∈ I.Q a, ∀ r s, adAt B.host.F P ((g * x * TC.kStd X u (B.R.N j)).1 r s) =
      adAt B.host.F P ((g * TC.kStd X u (B.R.N j)).1 r s) := fun P hP r s => by
    have e' : (g * x * TC.kStd X u (B.R.N j)).1.map (adAt B.host.F P) = (g * TC.kStd X u (B.R.N j)).1.map (adAt B.host.F P) := by
      rw [Units.val_mul, Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, h1 P hP, Matrix.mul_one]
    exact congrFun (congrFun e' r) s
  obtain ⟨q, hq⟩ := exists_pt hy0 (mul_mem (mul_mem hg.1 hx) hk) e0
  have hfr : ∀ P, q.fr P = ((I.stp u a j).rep c).1.1.fr P := fun P => fr_eq hq hy0 P (e0 P.1 P.2)
  have hxq := dia_of_pt hPr u hq
  have hΛ := levGAt_eq I hTw a j (by omega) c.1
  rw [hR.lev c x q (by rw [← hgx]; exact hq)]
  constructor
  · rintro ⟨κ, h1, h2, h3⟩
    have e1 : κ.1 = 1 := ufGL_inj B.sp.cm (B.R.N j) (h1.trans (map_one _).symm)
    obtain ⟨hJ, hr⟩ := red_of_act B.sp.cm (B.R.N j) (diaT (Pr := B.primes X) u) hg.1 hxq.1 κ.2.1.1 (by
      rw [hg.2, hxq.2, ← h2]
      show ((κ.1, κ.2.1.1) : UF B.fields.E (B.R.N j) × GLG (E := B.fields.E) (n := B.R.N j) (SG := (B.primes X).vGs)) • _ = _
      rw [e1]
      rfl)
    refine (mem_levU _ _ _ _ _).2 ⟨hJ, ?_⟩
    have key : ∀ (Λ' : LevFam B.fields.E B.fields.K (B.R.N j) (B.primes X).vGs), Λ' = colLevSym I.Ch j →
        ∀ g : Λ'.grp, g.1 ∈ (colLevSym I.Ch j).grp := by
      rintro _ rfl g
      exact g.2
    rw [hr]
    refine inv_mem (mem_chG.2 ⟨key _ hΛ κ.2.1, (bar_ya_eq_iff (X := B.fields) _ _ κ _).1 (funext fun w => ?_)⟩)
    exact (cos_iff_bar hj w (hqG hPr w.1 w.2) _ _).1 (congrFun h3 _)
  · intro hxU
    have h2 := act_of_mem B.sp.cm (B.R.N j) _ (diaT (Pr := B.primes X) u) hg.1 ⟨x, hxU⟩
    rw [hg.2, hxq.2] at h2
    have hm0 := mem_chG.1 ((levRed B.sp.cm (B.R.N j) _ _ _ ⟨x, hxU⟩)⁻¹).2
    have hm : ((levRed B.sp.cm (B.R.N j) _ _ _ ⟨x, hxU⟩)⁻¹).1 ∈ (levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) j c.1).grp := by
      rw [hΛ]
      exact hm0.1
    have h3 : ((I.stp u a j).act c.1 (1, ⟨_, hm⟩, 1) ((I.stp u a j).rep c)).1.1 = q := by
      refine Subtype.ext (Prod.ext h2.symm (funext fun P => ?_))
      show (1 : _ ≃ₗ[B.fields.E] _) * ((I.stp u a j).rep c).1.1.fr P * (1 : _ ≃ₗ[B.fields.E] _) = q.fr P
      rw [one_mul, mul_one, hfr]
    refine ⟨(1, ⟨_, hm⟩, 1), map_one (ufGL B.host.E (B.R.N j)), h3, funext fun P => ?_⟩
    by_cases hP : P.1 ∈ (B.primes X).vGs
    · exact (cos_iff_bar hj ⟨P.1, hP⟩ (hqG hPr P.1 hP) _ _).2 (congrFun
        ((bar_ya_eq_iff (X := B.fields) _ (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) j c.1) (1, ⟨_, hm⟩, 1) _).2 hm0.2) _)
    · have h4 : ((I.stp u a j).act c.1 (1, ⟨_, hm⟩, 1) ((I.stp u a j).rep c)).1.2 = ((I.stp u a j).rep c).1.2 := Set.image_id _
      unfold cosetIn
      rw [h3, h4]
      unfold frsF
      rw [dite_eq_right hP, dite_eq_right hP, hfr]

end GlobalTheory.PenLevTyp

end Gen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EZeroThetaDescentEval
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GoodFix

open Formalism.L2.DIV

theorem good_fix {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    (B : BlockDat K G Pl0) (ℓ : Lvl K G) (hX : ∀ χ ∈ ℓ.X, IsAbsIrrChar χ) (w : Fin (B.nV ℓ) → K) :
    ∑ g, (idemOf ℓ.X).coeff g • B.r g (B.S.basis.equivFun.symm (B.vE ℓ *ᵥ w)) =
      B.S.basis.equivFun.symm (B.vE ℓ *ᵥ w) := by
  set z := B.vE ℓ *ᵥ w with hz
  have hmem : z ∈ LinearMap.range (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ)).mulVecLin := by
    have e := (image_idempotent_spec K _ (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ))).2
    rw [← e]
    exact ⟨w, rfl⟩
  obtain ⟨y, hy⟩ := hmem
  have hid := (idempotent_central K G ℓ.X hX).1
  have hhom := group_action_matrix_hom K B.S G B.r
  have hfix : B.S.gaMat B.r (idemOf ℓ.X) *ᵥ z = z := by
    rw [← hy]
    change B.S.gaMat B.r (idemOf ℓ.X) *ᵥ (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ) *ᵥ y) = B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ) *ᵥ y
    rw [Matrix.mulVec_mulVec, ← hhom.2, goodAt, ← mul_assoc, hid]
  have hconv : ∀ (a : MonoidAlgebra K G) (x : Fin B.S.dim → K),
      B.S.basis.equivFun.symm (B.S.gaMat B.r a *ᵥ x) = ∑ g, a.coeff g • B.r g (B.S.basis.equivFun.symm x) := by
    intro a x
    apply B.S.basis.equivFun.injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearEquiv.apply_symm_apply, map_sum]
    simp only [CSD.gaMat, Matrix.sum_mulVec, Matrix.smul_mulVec, map_smul, CSD.actMat]
    refine Finset.sum_congr rfl fun g _ => ?_
    congr 1
    have := LinearMap.toMatrix_mulVec_repr B.S.basis B.S.basis (B.r g) (B.S.basis.equivFun.symm x)
    rw [Module.Basis.equivFun_apply]
    rw [← this]
    congr 1
    funext i
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  rw [← hconv, hfix]

end GlobalTheory.GoodFix

namespace GlobalTheory.GoodFix

open Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev


set_option maxHeartbeats 1000000 in
theorem thDn_act (hCR : GlobalTheory.Published.CuspRapidDecay) {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type}
    {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (h : R.toLevCh.Is A.μ0) (hM : R.IsModels) (hC : R.IsChain) (hred : R.grp_red_R) (t : T0) (g : G)
    (x : (A.fam.R t).S.Forms) (v : (R.MY 0).Vec) :
    R.thDn t (R.jX t ((A.fam.R t).r g x)) (PiTensorProduct.tprod ℂ v) =
      actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (R.thDn t (R.jX t x) (PiTensorProduct.tprod ℂ v)) := by
  have hS : ∀ j, j < D.R.m → SchurMult R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv))
      (levChi _ (R.βY j) (R.datYt t j R.triv)) (R.νY t j) (R.fdY t j) :=
    fun j _ => @GlobalTheory.MultFinite.schurMult D R.θ _ _ (R.MY j) (levS _ (R.βY j) (R.datYt t j R.triv))
      (levChi _ (R.βY j) (R.datYt t j R.triv)) hCR (R.νY t j) (R.fdY t j)
  refine (GlobalTheory.FormAction.act_eq_translate R hred hM.jX t g x).elim fun κ' hκ' => ?_
  refine (GlobalTheory.ChainLiftEquiv.liftsExist_chain R h t 0 (lt_of_lt_of_le two_pos D.R.two_le_m) (R.eG g)).elim fun κ hκ => ?_
  exact funext fun y =>
    (GlobalTheory.ChainLiftEquiv.thDn_shift R h hM hC t hS (R.eG g) κ' hκ'.1 (R.jX t x) (R.jX t ((A.fam.R t).r g x)) hκ'.2 κ hκ _ y).trans
      (GlobalTheory.ChainLiftEquiv.actL_zero R t (R.eG g) κ hκ _ (GlobalTheory.ChainLiftEquiv.thDn_type R t _ v) y).symm

end GlobalTheory.GoodFix

namespace GlobalTheory.GoodFix

open Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev


set_option maxHeartbeats 1000000 in
theorem goodProjector_fixes_compositeThetaLift_of_fixed (hCR : GlobalTheory.Published.CuspRapidDecay) {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type}
    {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (h : R.toLevCh.Is A.μ0) (hM : R.IsModels) (hC : R.IsChain) (hred : R.grp_red_R) (t : T0)
    (x : A.fam.amb.FR t) (hx : ∑ g, (idemOf A.X).coeff g • A.fam.amb.opR t (Sum.inr g) x = x) (v : (R.MY 0).Vec) :
    R.e0 (R.thDn t (R.jX t x) (PiTensorProduct.tprod ℂ v)) = R.thDn t (R.jX t x) (PiTensorProduct.tprod ℂ v) := by
  have key : R.thDn t (R.jX t x) (PiTensorProduct.tprod ℂ v) = R.e0 (R.thDn t (R.jX t x) (PiTensorProduct.tprod ℂ v)) := by
    conv_lhs => rw [← hx]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply]
    simp only [RealDat.e0, gaL, LinearMap.sum_apply, LinearMap.smul_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    exact congrArg (fun z => RealDat.eC (A := A) D.what₂.embLL g • z) (thDn_act hCR R h hM hC hred t g x v)
  exact key.symm

end GlobalTheory.GoodFix

end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeInnerProductFormulaOfDoublingEuler
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.IP

theorem heckeForm_of_global_euler : ∀ D : D7, GlobalForm D → EulerRight D → HeckeForm D := by
  intro D hG hE ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP hw LA LB Sf Φ₁ Φ₂ hF₁ hF₂ hU m mH hm hmH u₁ hu₁ u₂ hu₂ par hpar
    hsph hs
  obtain ⟨s₁, hs₁, hint⟩ := hs
  obtain ⟨hUp₁, hUp₂, hZint, z, hz, hpet⟩ :=
    hG A LA hU.sdA ψ θ B χA χB sA sB t cA a om ν 𝓕 hP hw m mH hm hmH Φ₁ Φ₂ hF₁ hF₂ u₁ hu₁ u₂ hu₂
  obtain ⟨hA1, ht1, hB, -⟩ := hP.setting
  have hs0 : sZero A B = (t : ℂ) / 2 := by
    simp only [sZero, hB]; push_cast; ring
  have hs0re : (sZero A B).re = (t : ℝ) / 2 := by rw [hs0]; simp
  obtain ⟨hcont, hbd, -⟩ := _root_.GlobalTheory.Core.Rk.IP.hgtL_props D A LA a hU.sdA hP.maj
  have hflat : ∀ s, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s =
      GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral.flatIntegrand (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g)
        (fun g => (hgtL A LA a g : ℝ)) (sZero A B) s := by
    intro s; funext g
    simp only [integrand, GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral.flatIntegrand, npow]; ring
  have hmeas : Measurable (fun g => (hgtL A LA a g : ℝ)) := (NNReal.continuous_coe.comp hcont).measurable
  have hfz := _root_.GlobalTheory.FlatFamily.flatZetaHolomorphic (GA D A) (m.restrict (openOff A LA Sf)) (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g)
    (fun g => (hgtL A LA a g : ℝ)) (sZero A B) (s₁ : ℂ) hmeas (fun g => by exact_mod_cast (hbd g).1)
    (fun g => by exact_mod_cast (hbd g).2) (by rw [← hflat]; exact hint)
  have hint0 : IntegrableOn (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g) (openOff A LA Sf) m := by
    have := hfz.1.1 (sZero A B) (by simp only [Set.mem_setOf_eq, Complex.ofReal_re, hs0re]; linarith)
    rwa [GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral.flatIntegrand_self] at this
  refine ⟨hUp₁, hUp₂, hint0, fun l hl => ?_⟩
  have hd := GlobalTheory.T.partialNormalizingFactorProduct_analytic_ne_zero D (Sf : Set (FinPl D)) A.rank B.rank
  have hER : EqRight (fun s => ∫ g, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m)
      (fun s => LFun.LSD D Sf par χB (s + 1 / 2) / LFun.dSfun D.host.E (Sf : Set (FinPl D)) A.rank B.rank s *
        ∫ g in openOff A LA Sf, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m) := by
    refine ⟨(A.rank : ℝ) + 1, fun s hs => ?_⟩
    have hs' : (A.rank : ℝ) + 1 < s.re := hs
    refine hE ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP LA LB Sf Φ₁ Φ₂ hF₁.1 hF₂.1 hU m hm u₁ hu₁ u₂ hu₂ par hpar hsph s hs'
      (hZint s ?_)
    have : (0 : ℝ) ≤ A.rank := Nat.cast_nonneg _
    linarith
  have hY : DifferentiableOn ℂ (fun s => ∫ g in openOff A LA Sf, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m)
      (rightOf s₁) := by
    have h2 := hfz.2.1
    simp only [Complex.ofReal_re] at h2
    refine h2.congr fun s _ => ?_
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral.flatZeta, hflat]
  have hL : HolValueAt (fun s => LFun.LSD D Sf par χB (s + 1 / 2)) (sZero A B) l := by rw [hs0]; exact hl
  have hmain := _root_.GlobalTheory.Core.Rk.IP.holValueAt_eq_div_mul _ _ _ _ (sZero A B) z l s₁ (by rw [hs0re]; positivity) (by rw [hs0re]; exact hs₁)
    hd.1 (fun s hs => (hd.2 s hs).1) hY hER hz hL
  rw [hpet, hmain, ← hs0]
  simp only [integrand_sZero]
  ring

end GlobalTheory.Core.Rk.IP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeesawDatumEqLatticePairOverVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)

namespace GlobalTheory.LastTarget

theorem tensRow_eq_phiOne {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n n'' : Type} [Fintype n] [DecidableEq n] [Fintype n''] [DecidableEq n''] (q : Unif k) (Q : Pair k n)
    (Λ : Submodule 𝒪[k] (n'' → k)) [Λ.IsFullLattice k] (c : 𝓀[k]ˣ) :
    tensRow (latInd Q.lat Λ) (cosetInd q Q.lat (c • Q).red) = phiOne (c • Q) (lastPair q Λ) := by
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  have h := ((GlobalTheory.LastSteps.lastTwoSteps k n n n'').2.2.2 q Q.lat Λ).1 ⟨(c • Q).red, (c • Q).red_ne⟩
  funext x
  have hx : withRow (x.submatrix Sum.inl id) (x (Sum.inr 0)) = x := by
    ext i j
    rcases i with i | i
    · rfl
    · fin_cases i; rfl
  have h2 := (h (x.submatrix Sum.inl id) (x (Sum.inr 0))).2
  rw [hx] at h2
  exact h2.symm

end GlobalTheory.LastTarget

namespace GlobalTheory.LastTarget

theorem charInd_ne_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] (χ : AddChar 𝓀[k] ℂ) (Q : Pair k n) : charInd χ Q ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have hne : ∀ a, χ a ≠ 0 := fun a ha => by
    have h1 := AddChar.map_add_eq_mul χ a (-a)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, ha, zero_mul] at h1
    exact one_ne_zero h1
  simp only [charInd, vecInd, Q.lat.zero_mem, if_true, mul_one, Pi.zero_apply] at h0
  exact hne _ h0

theorem lastTarget : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (q : Unif k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (χ : AddChar k Circle) (hχ : HasConductor χ 1), p.IsChar ψ χ → ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] (V₀ A L S X T L'' : HSp D) (o : OrthDec V₀ A L) (o'' : OrthDec X T L'') (ζ : Fin L.rank → D.host.E) (ζ₀ : Fin L''.rank → D.host.E), IsLineVec L ζ → IsLineVec L'' ζ₀ → ∀ (τ : Matrix (Fin L.rank) (Fin L''.rank) D.host.E) (lam : D.host.E), Matrix.mulVec τ ζ₀ = lam • ζ → valuation k (p.pr (incA D lam)) = 1 → τ.conjTranspose * (L.gram * τ) = (-(D.host.xi0 * star D.host.xi0)) • L''.gram → ∃ ε : 𝓀[k]ˣ, ∀ (α : Frame p A n') (α₀ : Frame p V₀ (n' ⊕ Fin 1)) (β : Frame p S n) (γ : Frame p T n'') (γ₀ : Frame p X (n'' ⊕ Fin 1)), IsSumFrame o ζ α α₀ → IsSumFrame o'' ζ₀ γ γ₀ → ∀ (Q : Pair k n) (Λ : Submodule 𝒪[k] (n'' → k)) [Λ.IsFullLattice k] (Ψ : Matrix n n' k → ℂ) (LS : Lat S) (LT : Lat T) (LX : Lat X), IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC X LX → β.IsLat LS Q.lat → γ.IsLat LT Λ → ∀ (L₁ : Lat V₀) (L₂ : Lat S) (f₁ Ξ : WO V₀ S → ℂ) (Φ₂ : WO S T → ℂ), Over ψ α₀ β L₁ L₂ f₁ (tensCol Ψ (charInd (resChar χ hχ q) Q)) Ξ → Vac ψ S T LS LT (· = p.v) Φ₂ → ∀ u : WO A S, ∃ g, Over ψ β γ₀ LS LX g (phiOne (ε • Q) (lastPair q Λ)) (lastBi o o'' τ Ξ Φ₂ u) := by
  intro D k _ _ _ _ p q ψ hψ hU χ hχ hc n n' n'' _ _ _ _ _ _ V₀ A L S X T L'' o o'' ζ ζ₀ hζ hζ₀ τ lam hτ hlam hG
  obtain ⟨ε, hε⟩ := _root_.GlobalTheory.KapStep.kapStep D k p q ψ hψ hU χ hχ hc n L S L'' ζ ζ₀ hζ hζ₀ τ lam hτ hlam hG
  refine ⟨ε, ?_⟩
  intro α α₀ β γ γ₀ hα hγ Q Λ _ Ψ LS LT LX hLS hLT hLX hβQ hγΛ L₁ L₂ f₁ Ξ Φ₂ hΞ hΦ₂ u
  obtain ⟨g₁, T₁, hg₁, hT₁, hT₁a⟩ := _root_.GlobalTheory.LastTgtSlice.main D k p n n' ψ hψ hU V₀ A L S o ζ hζ α α₀ β hα Ψ
    (charInd (resChar χ hχ q) Q) (charInd_ne_zero _ Q) LS hLS L₁ L₂ f₁ Ξ hΞ u
  obtain ⟨g₃, T₃, hg₃, hT₃, hT₃b⟩ := hε β LS hLS Q g₁ T₁ hg₁ hT₁
  have hO2 : Over ψ β γ LS LT Φ₂ (latInd Q.lat Λ) Φ₂ :=
    ((_root_.GlobalTheory.FinPl.overBasic D) k p n'' n ψ hψ S T β γ LS LT hLS hLT Φ₂ hΦ₂).2.2 hU Q.lat Λ hβQ hγΛ
  have hrow := tensRow_eq_phiOne q Q Λ ε
  have hSB : tensRow (latInd Q.lat Λ) (cosetInd q Q.lat (ε • Q).red) ∈ SB (Matrix (n'' ⊕ Fin 1) n k) :=
    hrow ▸ GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.phiOne_mem _ _
  obtain ⟨g, hg⟩ := GlobalTheory.T.splitPlace_datum_boxTensor_line_over_vacuum D k p n n'' ψ hψ hU S X T L'' o'' ζ₀ hζ₀ β γ γ₀ hγ LS LT LX hLS hLT hLX Φ₂ Φ₂
    (latInd Q.lat Λ) hO2 (cosetInd q Q.lat (ε • Q).red) g₃ T₃ hg₃ hT₃ hSB
  refine ⟨g, ?_⟩
  rw [← hrow]
  have hl : lastBi o o'' τ Ξ Φ₂ u = o''.boxT S Φ₂ (T₃ (rowFun β ζ₀ (cosetInd q Q.lat (ε • Q).red))) := by
    rw [hT₃b, hT₁a]
    rfl
  rw [hl]
  exact hg

end GlobalTheory.LastTarget
end

