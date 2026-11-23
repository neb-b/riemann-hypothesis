module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0422
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0389
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0381
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0343
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0079
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0304
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0292
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StrongApproximationDecomposition
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0417
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0341
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0414

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainIdealIndexProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.StepConst

variable {D : D7}

theorem local_part {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) (g : GA D V) :
    ∃ c : GA D V, SuppAt q.e V c ∧ (mt V c).map q.pr = (mt V g).map q.pr ∧
      GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram q.v (g * c⁻¹) = 1 := by
  obtain ⟨ε, hε, hE⟩ := q.above
  have hεε : ε * ε = ε := by rw [GlobalTheory.SplitCut.eFin_of_placeIdem hε, GlobalTheory.SplitCut.eFin_idem]
  have hEE : (q.e + cA D q.e) * (q.e + cA D q.e) = q.e + cA D q.e := by rw [hE, ← map_mul, hεε]
  have hEc : cA D (q.e + cA D q.e) = q.e + cA D q.e := by rw [hE, GlobalTheory.SplitCut.cA_algebraMap]
  have h1 : GlobalTheory.FinPl.compAt D q.v (q.e + cA D q.e) = 1 := by
    obtain ⟨α, rfl, a1, -⟩ := hε
    rw [hE]
    change evalV D.host.F q.v α ⊗ₜ[D.host.F] (1 : D.host.E) = 1
    rw [a1]
    rfl
  obtain ⟨c, hc⟩ := GlobalTheory.SplitCut.cut_exists V g _ hEE hEc
  refine ⟨c, fun i j => ?_, ?_, ?_⟩
  · rw [hc]
    exact GlobalTheory.SplitCut.idempotent_mul_cut_sub_one_entry _ hEE _ i j
  · rw [hc, GlobalTheory.GfCut.map_idem, GlobalTheory.LevelCut.pr_sum, one_smul, sub_self, zero_smul, add_zero]
  · rw [GlobalTheory.FinPl.KOpen.proj_eq_one_iff, ← GlobalTheory.FinPl.KOpen.map_eq_one_iff, GlobalTheory.SplitCut.mt_mul, Matrix.map_mul]
    have h2 : (mt V g).map (GlobalTheory.FinPl.compAt D q.v) = (mt V c).map (GlobalTheory.FinPl.compAt D q.v) := by
      rw [hc, GlobalTheory.GfCut.map_idem, h1, one_smul, sub_self, zero_smul, add_zero]
    rw [h2, ← Matrix.map_mul, ← GlobalTheory.SplitCut.mt_mul, mul_inv_cancel, GlobalTheory.SplitCut.mt_one,
      Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]

theorem moves_of_St {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : GlobalTheory.FinPl.Lat V} (hβ : IsFrame β Λ) (hΛ : Λ.FG)
    {h : GA D V} (hh : finE V h ∈ St β) (P : GlobalTheory.FinPl.Pl D → Prop) : GlobalTheory.FinPl.Moves V h Λ Λ P :=
  GlobalTheory.FinPl.KOpen.moves_of_levelOpen V Λ hΛ P (GlobalTheory.AdelicU.mem_levelOpen.2
    ((GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V β Λ hβ h).1 hh))

theorem mem_levG_of_inK {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : GlobalTheory.FinPl.Lat V} (hβ : IsFrame β Λ) (hΛ : Λ.FG)
    (L : LevDat D.host.E ℂ V.rank) {P : GlobalTheory.FinPl.Pl D → Prop}
    (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → ¬ P ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) {κ : GA D V} (hκ : GlobalTheory.FinPl.InK V Λ P κ) :
    κ ∈ levG V β L := by
  have hS : finE V κ ∈ St β := (GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V β Λ hβ κ).2
    (GlobalTheory.AdelicU.mem_levelOpen.1 (GlobalTheory.FinPl.KOpen.levelOpen_of_inK V Λ hΛ P hκ))
  obtain ⟨hf, h1⟩ := (GlobalTheory.FinPl.KOpen.mem_grpAt_iff V P κ).1 hκ.1
  exact ⟨hf, GlobalTheory.LevSplit.mem_lev_of_red _ _ β L _ (GlobalTheory.LevSplit.finE_mem_UA V κ) hS fun PP h =>
    GlobalTheory.ChainOnto.RedOne.redFn_eq_one D V β κ PP hS (h1 _ (hP PP h))⟩

theorem mem_levG_iff_base {V : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) {r t j : ℕ} (hr : r ≤ V.rank) (Pg Q Q₀ : Finset (Pl D.host.E))
    (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ ξ₀ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (h₀ : Q₀ = ∅)
    (h : GA D V) : h ∈ levG V β (datY _ r t j hr Pg Q P χ ξ Frm.B) ↔ h ∈ levG V β (datY _ r t j hr Pg Q₀ P χ ξ₀ Frm.B) ∧
      ∀ PP ∈ Q, redFn β PP (finE V h) ∈ blockTri (blk2 r) := by
  subst h₀
  constructor
  · rintro ⟨hf, h1, h2⟩
    obtain ⟨a1, a2, a3, a4⟩ := mem_parLev.1 h1
    exact ⟨⟨hf, mem_parLev.2 ⟨a1, a2, a3, fun PP hP => absurd hP (Finset.notMem_empty _)⟩, h2⟩, a4⟩
  · rintro ⟨⟨hf, h1, h2⟩, a4⟩
    obtain ⟨a1, a2, a3, -⟩ := mem_parLev.1 h1
    exact ⟨hf, mem_parLev.2 ⟨a1, a2, a3, a4⟩, h2⟩

theorem red_iff_local {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) {V : HSp D} {Y : Type} [Fintype Y] [DecidableEq Y] (Fr : GlobalTheory.LocMod.Frame k V.rank Y)
    (J : Subgroup (GL Y k)) {β : GL (Fin V.rank) (Lev.EAf D)} {Λ N : GlobalTheory.FinPl.Lat V} (hβ : IsFrame β Λ) (hΛ : Λ.FG)
    (L : LevDat D.host.E ℂ V.rank) {PP : Pl D.host.E} (hPP : PP ∈ L.Q) (hv : q.v = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))
    (hg : ∀ PP' ∈ L.Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ q.v) (hq : ∀ PP' ∈ L.Q, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') = q.v → PP' = PP)
    {b : GA D V} (hb : b ∈ GfC V) (hm : GlobalTheory.FinPl.Moves V b Λ N (· = q.v)) (hN : IntIn q V Fr N)
    (hJ : ∀ x ∈ KO k Y, ∀ c, (ofSplit q).IsLoc Fr c x → (b⁻¹ * c * b ∈ levG V β L ↔ x ∈ J))
    {g : GA D V} (hS : finE V (b⁻¹ * g * b) ∈ St β) {x : GL Y k} (hx : (mt V g).map q.pr = Fr.β * x.val * Fr.γ) :
    redFn β PP (finE V (b⁻¹ * g * b)) ∈ blockTri (blk2 L.r) ↔ x ∈ J := by
  have hxK : x ∈ KO k Y := _root_.GlobalTheory.SplitInt.mem_KO_of_moves q V Fr N (· = q.v) rfl hN g
    ((GlobalTheory.StMoves.moves_conj_iff g hm).1 (moves_of_St hβ hΛ hS _)) x hx
  obtain ⟨c, c1, c2, c3⟩ := local_part q V g
  rw [← hJ x hxK c ⟨c1, c2.trans hx⟩]
  obtain ⟨cf, c4⟩ := (GlobalTheory.FinPl.KOpen.mem_grpAt_iff V _ c).1
    (GlobalTheory.SuppGrp.mem_grpAt_of_suppAt D k q V c c1 (· = q.v) rfl)
  have p1 : ∀ u, u ≠ q.v → GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram u (b⁻¹ * c * b) = 1 := fun u hu => by
    rw [map_mul, map_mul, c4 u hu, mul_one, ← map_mul, inv_mul_cancel, map_one]
  have p2 : GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram q.v (b⁻¹ * (g * c⁻¹) * b) = 1 := by
    rw [map_mul, map_mul, c3, mul_one, ← map_mul, inv_mul_cancel, map_one]
  have e : b⁻¹ * g * b = (b⁻¹ * (g * c⁻¹) * b) * (b⁻¹ * c * b) := by group
  have hSc : finE V (b⁻¹ * c * b) ∈ St β := by
    refine (GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V β Λ hβ _).2 fun u => ?_
    by_cases hu : u = q.v
    · have := (GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V β Λ hβ _).1 hS u
      rw [e, map_mul, hu, p2, one_mul] at this
      rw [hu]
      exact this
    · rw [p1 u hu]
      exact one_mem _
  have hSd : finE V (b⁻¹ * (g * c⁻¹) * b) ∈ St β := by
    have := mul_mem hS (inv_mem hSc)
    rw [e, map_mul, mul_inv_cancel_right] at this
    exact this
  have r1 : redFn β PP (finE V (b⁻¹ * g * b)) = redFn β PP (finE V (b⁻¹ * c * b)) := by
    rw [e, map_mul, redFn_mul hSd hSc, GlobalTheory.ChainOnto.RedOne.redFn_eq_one D V β _ PP hSd (hv ▸ p2), one_mul]
  have r2 : ∀ PP' : Pl D.host.E, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ q.v → redFn β PP' (finE V (b⁻¹ * c * b)) = 1 := fun PP' h =>
    GlobalTheory.ChainOnto.RedOne.redFn_eq_one D V β _ PP' hSc (p1 _ h)
  rw [r1]
  refine ⟨fun h => ⟨(GfC V).mul_mem ((GfC V).mul_mem ((GfC V).inv_mem hb) cf) hb, mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA V _, hSc, fun PP' h' => ?_,
    fun PP' h' => ?_⟩, ?_⟩, fun h => parLev_q h.2.1 hPP⟩
  · rw [r2 PP' (hg PP' h')]
    exact one_mem _
  · by_cases h'' : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') = q.v
    · rw [hq PP' h' h'']
      exact h
    · rw [r2 PP' h'']
      exact one_mem _
  · have : rTup β L (finE V (b⁻¹ * c * b)) = 1 := by
      funext PP'
      show upperLeftBlock L.hr (redFn β PP'.1 _) = 1
      rw [r2 PP'.1 (hg _ PP'.2)]
      exact blockDiagonalExtendByOnePrimeField_one _ _
    rw [this]
    exact one_mem _

def moved {V : HSp D} (b : GA D V) (K : Subgroup (GA D V)) : Subgroup (GA D V) := K.comap (MulAut.conj b⁻¹).toMonoidHom

theorem mem_moved {V : HSp D} (b : GA D V) (K : Subgroup (GA D V)) (g : GA D V) : g ∈ moved b K ↔ b⁻¹ * g * b ∈ K := by
  simp [moved]

theorem moved_set {V : HSp D} (b : GA D V) (K : Subgroup (GA D V)) :
    {g : GfC V | b * g.1 * b⁻¹ ∈ moved b K} = {k : GfC V | k.1 ∈ (K : Set (GA D V))} := by
  ext g
  simp [mem_moved, mul_assoc]

theorem moved_level {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ N : GlobalTheory.FinPl.Lat V} (hβ : IsFrame β Λ) (hΛ : Λ.FG)
    (L : LevDat D.host.E ℂ V.rank) {P : GlobalTheory.FinPl.Pl D → Prop}
    (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → ¬ P ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) {b : GA D V} (hb : b ∈ GfC V)
    (hm : GlobalTheory.FinPl.Moves V b Λ N P) :
    moved b (levG V β L) ≤ GfC V ∧ IsCompact (moved b (levG V β L) : Set (GA D V)) ∧
      IsOpen (((moved b (levG V β L)).subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) ∧
      (∀ κ, GlobalTheory.FinPl.InK V N P κ → κ ∈ moved b (levG V β L)) ∧ ∀ g ∈ moved b (levG V β L), GlobalTheory.FinPl.Moves V g N N P := by
  refine ⟨fun g hg => ?_, ?_, ?_, fun κ hκ => ?_, fun g hg => ?_⟩
  · have h1 : b⁻¹ * g * b ∈ GfC V := ((mem_moved _ _ g).1 hg).1
    have e : g = b * (b⁻¹ * g * b) * b⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hb h1) (inv_mem hb)
  · have e : (moved b (levG V β L) : Set (GA D V)) = (fun x => b * x * b⁻¹) '' (levG V β L : Set (GA D V)) := by
      ext g
      constructor
      · intro hg
        exact ⟨b⁻¹ * g * b, (mem_moved _ _ g).1 hg, by group⟩
      · rintro ⟨k, hk, rfl⟩
        refine (mem_moved _ _ _).2 ?_
        have e2 : b⁻¹ * (b * k * b⁻¹) * b = k := by group
        rw [e2]
        exact hk
    rw [e]
    exact (GlobalTheory.ParahoricCompact.isCompact_levG V β L).image (by fun_prop)
  · have e : (((moved b (levG V β L)).subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) =
        (fun x : GfC V => (⟨b, hb⟩ : GfC V)⁻¹ * x * ⟨b, hb⟩) ⁻¹' {g : GfC V | (g : GA D V) ∈ levG V β L} := by
      ext x
      exact mem_moved b (levG V β L) x.1
    rw [e]
    exact (GlobalTheory.LevelOpen.isOpen_levG V β L).preimage (by fun_prop)
  · have hn : (GlobalTheory.FinPl.grpAt V P).Normal := MonoidHom.normal_ker _
    refine (mem_moved _ _ κ).2 (mem_levG_of_inK hβ hΛ L hP ⟨?_, (GlobalTheory.StMoves.moves_conj_iff κ hm).2 hκ.2⟩)
    have := hn.conj_mem κ hκ.1 b⁻¹
    rwa [inv_inv] at this
  · exact (GlobalTheory.StMoves.moves_conj_iff g hm).1
      (moves_of_St hβ hΛ (parLev_St (lev_le_parLev ((mem_moved _ _ g).1 hg).2)) P)

theorem exists_mat {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) {V : HSp D} {Y : Type} [Fintype Y] [DecidableEq Y] (Fr : GlobalTheory.LocMod.Frame k V.rank Y) (g : GA D V) :
    ∃ x : GL Y k, (mt V g).map q.pr = Fr.β * x.val * Fr.γ := by
  have hm : ∀ a a' : GA D V, a * a' = 1 → (mt V a).map q.pr * (mt V a').map q.pr = 1 := fun a a' ha => by
    rw [← Matrix.map_mul, ← GlobalTheory.SplitCut.mt_mul, ha, GlobalTheory.SplitCut.mt_one, Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]
  exact GlobalTheory.LevelCut.exists_coord Fr _ _ (hm g g⁻¹ (mul_inv_cancel g)) (hm g⁻¹ g (inv_mul_cancel g))

theorem under_ne {T : Type} {L : LevCh D T} {t₀ : T} (h : L.Is t₀) (t : T) {PP PP' : Pl D.host.E} (hQ : PP ∈ L.Q t) (hg : PP' ∈ L.Pg) :
    (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') ≠ (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) := by
  intro e
  obtain ⟨p, hp, hm, hne⟩ := GlobalTheory.LevelRamif.exists_prime_mem (h.Q_pl t) hQ
  obtain ⟨k, hk⟩ := (h.Pg PP').1 hg
  have key : ∀ (R : Pl D.host.E) (n : ℕ), (n : 𝓞 D.host.E) ∈ R.asIdeal ↔ (n : 𝓞 D.host.F) ∈ (R.under (𝓞 D.host.F)).asIdeal :=
    fun R n => by
      show _ ↔ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) n ∈ R.asIdeal
      rw [map_natCast]
  exact GlobalTheory.LevelRamif.not_two_primes PP' hp (D.host.g_prime k) (hne k) ((key _ _).2 (e ▸ (key _ _).1 hm))
    (GlobalTheory.LevelRamif.typePrime_mem hk)

theorem base_empty {T : Type} {L : LevCh D T} {t₀ : T} (h : L.Is t₀) : L.Q t₀ = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun PP hP => (h.Q_ram _ PP).2 (Or.inl hP) fun x _ => ?_
  rw [h.xi_base]
  rfl

end GlobalTheory.StepConst

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelsRepsRepresentUnitaryDoubleCosets
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

noncomputable section
namespace GlobalTheory.ChartReps

section Gen
variable {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (S : StepLevel D.host.F D.host.E (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) T f bad) {cl : Type}
  (y : cl → UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
  (U : Subgroup (GA D V)) (hU : ∀ g, g ∈ U ↔ g ∈ GfC V ∧ ∃ κ : S.U, κ.1.1 = finM V hn g)
  (h : cl → GA D V) (hh : ∀ c, h c ∈ GfC V ∧ finM V hn (h c) = (y c).1.1)

def finHomN : GA D V →* GL (Fin n) (EF D) where
  toFun g := GlobalTheory.AdForm.Model.finGL V hn g
  map_one' := Units.ext (GlobalTheory.AdForm.Model.finM_one V hn)
  map_mul' g g' := Units.ext (GlobalTheory.AdForm.Model.finM_mul V hn g g')

theorem finHomN_val (g : GA D V) : (finHomN V hn g).1 = finM V hn g := rfl

theorem finHomN_eq_one (g : GA D V) : finHomN V hn g = 1 ↔ g ∈ GinfC V := by
  rw [Units.ext_iff, finHomN_val, Units.val_one, GlobalTheory.AdForm.finM_eq_one_iff_mem_GinfC D V n hn g]


include hU in
theorem lift_mem (e : ↥(GfC V) ≃* ↥(UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)))
    (he : ∀ g, (e g).1.1 = finM V hn g.1) (κ : S.U) :
    (e.symm ⟨κ.1, ((S.U_eq κ.1).1 κ.2).1⟩).1 ∈ U ∧ finM V hn (e.symm ⟨κ.1, ((S.U_eq κ.1).1 κ.2).1⟩).1 = κ.1.1 := by
  have h1 : finM V hn (e.symm ⟨κ.1, ((S.U_eq κ.1).1 κ.2).1⟩).1 = κ.1.1 := by rw [← he, e.apply_symm_apply]
  exact ⟨(hU _).2 ⟨(e.symm _).2, κ, h1.symm⟩, h1⟩


include hU hh in
set_option maxHeartbeats 1000000 in
theorem reps_of_chart (hy : Function.Bijective (fun c => (Quotient.mk'' (y c) : Cls S))) : IsReps V U h := by
  letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  obtain ⟨e, he⟩ := GlobalTheory.FinPartIso.exists_finIso D V n hn
  obtain ⟨r, hr⟩ := GlobalTheory.RatPtsEquiv.rat_equiv D V n hn
  have hmemU : ∀ (g : GfC V), g.1 ∈ U ↔ (e g).1 ∈ S.U := by
    intro g
    rw [hU]
    constructor
    · rintro ⟨_, κ, hκ⟩
      have : (e g).1 = κ.1 := Units.ext ((he g).trans hκ.symm)
      rw [this]; exact κ.2
    · intro hx; exact ⟨g.2, ⟨(e g).1, hx⟩, he g⟩
  have hΦe : ∀ g : GfC V, finHomN V hn g.1 = (e g).1 := fun g => Units.ext (he g).symm
  refine ⟨fun g hg => ((hU g).1 hg).1, ?_, ?_, fun c => (hh c).1, ?_, ?_⟩
  · have hset : (U : Set (GA D V)) = (fun x => (e.symm x).1) '' {x | x.1 ∈ S.U} := by
      ext g
      constructor
      · intro hg
        have hgf := ((hU g).1 hg).1
        exact ⟨e ⟨g, hgf⟩, (hmemU ⟨g, hgf⟩).1 hg, by simp only [e.symm_apply_apply]⟩
      · rintro ⟨x, hx, rfl⟩
        exact (hmemU _).2 (by rw [e.apply_symm_apply]; exact hx)
    have hc : IsCompact {x : ↥(UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) | x.1 ∈ S.U} := by
      rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
      convert S.U_compact using 1
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩; exact hx
      · intro hz; exact ⟨⟨z, ((S.U_eq z).1 hz).1⟩, hz, rfl⟩
    rw [hset]
    exact hc.image (continuous_subtype_val.comp e.symm.continuous)
  · have : ((U.subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) = e ⁻¹' {x | x.1 ∈ S.U} := by
      ext g
      exact (Subgroup.mem_subgroupOf).trans (hmemU g)
    rw [this]
    exact S.U_open.preimage e.continuous
  · intro g
    obtain ⟨p, hpq⟩ : ∃ p : GinfC V × GfC V, g = p.1.1 * p.2.1 :=
      ⟨(GlobalTheory.AdelicSplit.splitEquiv V).symm g, ((GlobalTheory.AdelicSplit.splitEquiv V).apply_symm_apply g).symm⟩
    obtain ⟨⟨c, δ, κ0⟩, hδ, hdec⟩ := GlobalTheory.AdForm.Model.exists_dec V hn S y hy.2 p.2.1
    obtain ⟨κ, hκU, hκf⟩ : ∃ κ ∈ U, finM V hn κ = κ0.1.1 :=
      ⟨_, (lift_mem V hn S U hU e.toMulEquiv he κ0).1, (lift_mem V hn S U hU e.toMulEquiv he κ0).2⟩
    obtain ⟨γ, hγ, hΦγ⟩ : ∃ γ ∈ GQ V, finHomN V hn γ = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ := by
      refine ⟨(r.symm ⟨δ, hδ⟩).1, (r.symm ⟨δ, hδ⟩).2, ?_⟩
      apply Units.ext
      have h1 := hr (r.symm ⟨δ, hδ⟩)
      rw [MulEquiv.apply_symm_apply] at h1
      exact h1
    refine ⟨γ, hγ, c, (h c)⁻¹ * γ⁻¹ * g * κ⁻¹, ?_, κ, hκU, by group⟩
    rw [← finHomN_eq_one V hn]
    have e1 : finHomN V hn g = finHomN V hn p.2.1 := by
      rw [hpq, map_mul, (finHomN_eq_one V hn _).2 p.1.2, one_mul]
    have e2 : finHomN V hn p.2.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ * (y c).1 * κ0.1 :=
      Units.ext (by rw [finHomN_val, hdec])
    have e3 : finHomN V hn (h c) = (y c).1 := Units.ext (by rw [finHomN_val, (hh c).2])
    have e4 : finHomN V hn κ = κ0.1 := Units.ext (by rw [finHomN_val, hκf])
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, map_inv, e1, e2, e3, e4, hΦγ]
    group
  · intro c c' γ hγ k hk κ hκ heq
    obtain ⟨_, κ0, hκ0⟩ := (hU κ).1 hκ
    have hΦγ : finHomN V hn γ = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (r ⟨γ, hγ⟩).1 :=
      Units.ext (by rw [finHomN_val, hr ⟨γ, hγ⟩])
    have e3 : ∀ c, finHomN V hn (h c) = (y c).1 := fun c => Units.ext (by rw [finHomN_val, (hh c).2])
    have e4 : finHomN V hn κ = κ0.1 := Units.ext (by rw [finHomN_val, ← hκ0])
    have key : (y c').1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (r ⟨γ, hγ⟩).1 * (y c).1 * κ0.1 := by
      rw [← e3, ← e3, heq, ← e4, ← hΦγ]
      simp only [map_mul, (finHomN_eq_one V hn k).2 hk, mul_one]
    have hmemγ : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (r ⟨γ, hγ⟩).1 ∈
        UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := by
      rw [← hΦγ]; exact GlobalTheory.AdForm.Model.finGL_mem V hn γ
    apply hy.1
    show (Quotient.mk'' (y c) : Cls S) = Quotient.mk'' (y c')
    refine (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨⟨_, hmemγ⟩, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map_of_mem _ (r ⟨γ, hγ⟩).2),
      ⟨κ0.1, ((S.U_eq κ0.1).1 κ0.2).1⟩, Subgroup.mem_subgroupOf.2 κ0.2, Subtype.ext key⟩

end Gen

section Gen2
variable {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (S : StepLevel D.host.F D.host.E (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) T f bad) {cl : Type}
  (y : cl → UPts (sigD D) (V.gram.reindex (finCongr hn) (finCongr hn)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
  (U : Subgroup (GA D V)) (hU : ∀ g, g ∈ U ↔ g ∈ GfC V ∧ ∃ κ : S.U, κ.1.1 = finM V hn g)
  (h : cl → GA D V) (hh : ∀ c, h c ∈ GfC V ∧ finM V hn (h c) = (y c).1.1)


include hU hh in
set_option maxHeartbeats 1000000 in
theorem stabOrd_of_chart {stab : cl → Type} [∀ c, Group (stab c)]
    (stabI : ∀ c, stab c →* UJ (sigD D : D.host.E →+* D.host.E) (V.gram.reindex (finCongr hn) (finCongr hn)))
    (hinj : ∀ c, Function.Injective (stabI c))
    (hran : ∀ c (γ : UJ (sigD D : D.host.E →+* D.host.E) (V.gram.reindex (finCongr hn) (finCongr hn))),
      γ ∈ (stabI c).range ↔ bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 ∈
        S.U.map (MulAut.conj (y c).1).toMonoidHom)
    (c : cl) : stabOrd U (h c) = Nat.card (stab c) := by
  letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  obtain ⟨e, he⟩ := GlobalTheory.FinPartIso.exists_finIso D V n hn
  obtain ⟨r, hr⟩ := GlobalTheory.RatPtsEquiv.rat_equiv D V n hn
  have hΦγ : ∀ γ : GQ V, finHomN V hn γ.1 = bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (r γ).1 :=
    fun γ => Units.ext (hr γ)
  have e3 : finHomN V hn (h c) = (y c).1 := Units.ext (by rw [finHomN_val, (hh c).2])
  have hcond : ∀ γ : GQ V, (∃ k ∈ GinfC V, ∃ κ ∈ U, γ.1 * h c = h c * k * κ) ↔ r γ ∈ (stabI c).range := by
    intro γ
    rw [hran]
    constructor
    · rintro ⟨k, hk, κ, hκ, heq⟩
      obtain ⟨_, κ0, hκ0⟩ := (hU κ).1 hκ
      have e4 : finHomN V hn κ = κ0.1 := Units.ext (by rw [finHomN_val, ← hκ0])
      have key := congrArg (finHomN V hn) heq
      rw [map_mul, map_mul, map_mul, hΦγ, e3, e4, (finHomN_eq_one V hn k).2 hk, mul_one] at key
      refine Subgroup.mem_map.2 ⟨κ0.1, κ0.2, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, ← key]
      group
    · intro hmem
      obtain ⟨κ1, hκ1, hconj⟩ := Subgroup.mem_map.1 hmem
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hconj
      obtain ⟨κ, hκU, hκf⟩ : ∃ κ ∈ U, finM V hn κ = κ1.1 :=
        ⟨_, (lift_mem V hn S U hU e.toMulEquiv he ⟨κ1, hκ1⟩).1, (lift_mem V hn S U hU e.toMulEquiv he ⟨κ1, hκ1⟩).2⟩
      have e4 : finHomN V hn κ = κ1 := Units.ext (by rw [finHomN_val, hκf])
      refine ⟨(h c)⁻¹ * γ.1 * h c * κ⁻¹, ?_, κ, hκU, by group⟩
      rw [← finHomN_eq_one V hn, map_mul, map_mul, map_mul, map_inv, map_inv, hΦγ, e3, e4, ← hconj]
      group
  unfold stabOrd
  rw [Nat.card_congr (r.toEquiv.subtypeEquiv hcond)]
  exact (Nat.card_congr (MonoidHom.ofInjective (hinj c)).toEquiv).symm

end Gen2


set_option maxHeartbeats 1000000 in
theorem twDat_reps : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i ≤ B.R.m) β, IsReps ((I.rec7 l Z).sp.X i) (A.U i β) (A.h i β) ∧ (Continuous fun κ => ((A.chi i β κ : ℂˣ) : ℂ)) ∧ ∀ c, stabOrd (A.U i β) (A.h i β c) = Nat.card ((I.chain l u a).stab i c.1) := by
  intro B X I hOk hP l Z u a Ch A hA i hi β
  exact ⟨reps_of_chart _ (rankN (I.rec7 l Z) i hi) (A.K i hi β).lev (A.K i hi β).y (A.U i β) (hA.U i hi β) (A.h i β)
      (hA.h i hi β) (A.K i hi β).y_bij,
    _root_.GlobalTheory.AdForm.ChiCont.chi_continuous I hOk hP l Z u a Ch A hA i hi β,
    fun c => stabOrd_of_chart _ (rankN (I.rec7 l Z) i hi) (A.K i hi β).lev (A.K i hi β).y (A.U i β) (hA.U i hi β) (A.h i β)
      (hA.h i hi β) (A.K i hi β).stabI (A.K i hi β).stabI_inj (A.K i hi β).stabI_range c⟩

end GlobalTheory.ChartReps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsConstMovedVacuumAllTuples
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.VacAll

theorem vacT_twist {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {θ : InfFam (I.rec7 l Z)}
    {i : ℕ} {hi : i + 1 ≤ B.R.m} {c₀ : ℂ} {ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ} {μ₀ μ : (AE (I.rec7 l Z))ˣ →* Circle}
    {om₀ om : Om ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))}
    {vac : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ} (hv : IsThetaFunO ψ _ _ vac)
    (h0 : IsWeilDatumO ψ _ _ μ₀ μ₀ om₀) (h1 : IsWeilDatumO ψ _ _ μ μ om) (H : VacT I l Z θ i hi c₀ μ₀ om₀ vac) :
    VacT I l Z θ i hi c₀ μ om vac := by
  intro g hg h hh N N' hN hN' x y hx hy
  have e := GlobalTheory.WeilChange.weilData_differ_by_splitFac _ ψ _ _ μ₀ μ₀ μ μ om₀ om h0 h1 g h x y hx hy vac hv
  rw [e, xiS_smul, H g hg h hh N N' hN hN' x y hx hy]
  funext z
  have a1 : (μ₀ x : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have a2 : (μ₀ y : ℂ) ≠ 0 := Circle.coe_ne_zero _
  simp only [splitFacO, Circle.coe_mul, Circle.coe_inv]
  field_simp

end GlobalTheory.AdForm.VacAll

namespace GlobalTheory.AdForm.VacAll

theorem vacT_one : GlobalTheory.Published.StrongApproxSU → ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) vac, IsVacO ψ θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) vac → ∀ (a : I.ι) μ om, ChrEq μ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → IsWeilDatumO ψ _ _ μ μ om → ∃ c₀ : ℂ, c₀ ≠ 0 ∧ VacT I l Z θ i hi c₀ μ om vac := by
  intro hSA B X I hI hP l Z ψ θ hψ hθ i hi vac hvac a μ om hc hw
  obtain ⟨c₀, hc₀, h1⟩ := _root_.GlobalTheory.AdForm.VacAllBase.moveT_one I hI hP l Z ψ θ hψ hθ i hi vac hvac a μ om hc hw
  have hstd := (GlobalTheory.AdForm.StdStepsT.stdPair_steps_all I hI hP l Z ψ θ hψ hθ).1 i hi
  refine ⟨c₀, hc₀, vacT_iff.2 fun g hg h hh => ?_⟩
  obtain ⟨r, s, k, hr, hs, hk, hkL, rfl⟩ :=
    GlobalTheory.SplitDec.exists_rat_split_stab hSA _ _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) hstd.gS g hg
  obtain ⟨r', s', k', hr', hs', hk', hkL', rfl⟩ :=
    GlobalTheory.SplitDec.exists_rat_split_stab hSA _ _ _ (rankN (I.rec7 l Z) (i + 1) hi) hstd.gT h hh
  have h2 := _root_.GlobalTheory.AdForm.StabMoveTup.moveT_mul_stab I hI hP l Z ψ θ hψ hθ i hi vac hvac a μ om hc hw c₀ 1 1 (one_mem _) (one_mem _) h1 k hk k' hk' hkL hkL'
  rw [one_mul, one_mul] at h2
  have h3 := GlobalTheory.AdForm.VacConst.split_induction _ (fun g => MoveT I l Z θ i hi c₀ μ om vac g k') (fun g hg H e he t ht => by
    have := _root_.GlobalTheory.AdForm.VacSplit.moveT_split I hI hP l Z ψ θ hψ hθ i hi vac hvac a μ om hc hw c₀ g k' hg hk' H e he t 1 ht
      (GlobalTheory.AdForm.VacConst.suppAt_one e _)
    rwa [one_mul] at this) hs
  have hsk := mul_mem h3.1 hk
  have h4 := GlobalTheory.AdForm.VacConst.split_induction _ (fun h => MoveT I l Z θ i hi c₀ μ om vac (s * k) h) (fun h hh H e he t ht => by
    have := _root_.GlobalTheory.AdForm.VacSplit.moveT_split I hI hP l Z ψ θ hψ hθ i hi vac hvac a μ om hc hw c₀ (s * k) h hsk hh H e he 1 t
      (GlobalTheory.AdForm.VacConst.suppAt_one e _) ht
    rwa [one_mul] at this) hs'
  have h5 := _root_.GlobalTheory.AdForm.VacAllRat.moveT_rat I hI hP l Z ψ θ hψ hθ i hi vac hvac a μ om hc hw c₀ _ _ hsk (mul_mem h4.1 hk')
    (h4.2 k' hk' (h3.2 k hk h2)) r r' hr hr'
  rw [mul_assoc, mul_assoc]
  exact h5

theorem vacT_all : GlobalTheory.Published.StrongApproxSU → ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) vac, IsVacO ψ θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) vac → ∃ c₀ : ℂ, c₀ ≠ 0 ∧ ∀ (a : I.ι) μ om, ChrEq μ (I.C.mu0 ⟨i, hi⟩ * I.xi a) → IsWeilDatumO ψ _ _ μ μ om → VacT I l Z θ i hi c₀ μ om vac := by
  intro hSA B X I hI hP l Z ψ θ hψ hθ i hi vac hvac
  by_cases hex : ∃ (a : I.ι) (μ : (AE (I.rec7 l Z))ˣ →* Circle) (om : Om ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))),
      ChrEq μ (I.C.mu0 ⟨i, hi⟩ * I.xi a) ∧ IsWeilDatumO ψ _ _ μ μ om
  · obtain ⟨a₀, μ₀, om₀, hc0, hw0⟩ := hex
    obtain ⟨c₀, hc, H⟩ := vacT_one hSA I hI hP l Z ψ θ hψ hθ i hi vac hvac a₀ μ₀ om₀ hc0 hw0
    exact ⟨c₀, hc, fun a μ om _ hw => vacT_twist hvac.2.2 hw0 hw H⟩
  · exact ⟨1, one_ne_zero, fun a μ om hc hw => (hex ⟨a, μ, om, hc, hw⟩).elim⟩

end GlobalTheory.AdForm.VacAll
end

