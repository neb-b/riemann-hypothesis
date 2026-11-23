module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0351
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0356
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsComOfOf
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelTwistPrimesStepZeroCharacterEqOne
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilMatrixCoefficientVacuaUnramifiedPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0156
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0350
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.SetCut

section Alg

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem mul_eq_add_sub_one (c : R) (a b : Matrix n n R) (ha : c • (a - 1) = a - 1) (hb : c • (b - 1) = 0) :
    a * b = a + b - 1 ∧ b * a = a + b - 1 := by
  have h1 : (a - 1) * (b - 1) = 0 := by rw [← ha, Matrix.smul_mul, ← Matrix.mul_smul, hb, Matrix.mul_zero]
  have h2 : (b - 1) * (a - 1) = 0 := by rw [← ha, Matrix.mul_smul, ← Matrix.smul_mul, hb, Matrix.zero_mul]
  have e1 : a * b = (a - 1) * (b - 1) + (a + b - 1) := by noncomm_ring
  have e2 : b * a = (b - 1) * (a - 1) + (a + b - 1) := by noncomm_ring
  exact ⟨by rw [e1, h1, zero_add], by rw [e2, h2, zero_add]⟩

theorem cut_sub_one (c : R) (g : Matrix n n R) : c • g + (1 - c) • (1 : Matrix n n R) - 1 = c • (g - 1) := by
  rw [smul_sub, sub_smul, one_smul]; abel

theorem cut_left (c : R) (a b : Matrix n n R) (ha : c • (a - 1) = a - 1) (hb : c • (b - 1) = 0) :
    c • (a * b) + (1 - c) • (1 : Matrix n n R) = a := by
  rw [← sub_left_inj (a := 1), cut_sub_one, (mul_eq_add_sub_one c a b ha hb).1,
    show a + b - 1 - 1 = (a - 1) + (b - 1) by abel, smul_add, ha, hb, add_zero]

theorem cut_right (c : R) (a b : Matrix n n R) (ha : c • (a - 1) = a - 1) (hb : c • (b - 1) = 0) :
    (1 - c) • (a * b) + (1 - (1 - c)) • (1 : Matrix n n R) = b := by
  rw [← sub_left_inj (a := 1), cut_sub_one, (mul_eq_add_sub_one c a b ha hb).1,
    show a + b - 1 - 1 = (a - 1) + (b - 1) by abel, sub_smul, one_smul, smul_add, ha, hb]
  abel

theorem cut_mul_cut (c : R) (hc : c * c = c) (g : Matrix n n R) :
    (c • g + (1 - c) • (1 : Matrix n n R)) * ((1 - c) • g + (1 - (1 - c)) • (1 : Matrix n n R)) = g := by
  have h0 : c * (1 - c) = 0 := by rw [mul_sub, mul_one, hc, sub_self]
  rw [(mul_eq_add_sub_one c _ _ (by rw [cut_sub_one, smul_smul, hc]) (by rw [cut_sub_one, smul_smul, h0, zero_smul])).1,
    sub_sub_cancel, sub_smul, sub_smul, one_smul, one_smul]
  abel

end Alg

variable {D : D7}

theorem mem_idOff_iff (P : Pl D → Prop) (a : AE D) : a ∈ idOff D P ↔ ∀ w, P w → GlobalTheory.FinPl.compAt D w a = 0 := by
  simp only [idOff, Submodule.mem_iInf, RingHom.mem_ker, Subtype.forall]

theorem mem_GfC_iff_entries (V : HSp D) (g : GA D V) :
    g ∈ GfC V ↔ ∀ i j, infPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
  rw [GlobalTheory.UnitaryIdemCut.mem_GfC_iff, Units.ext_iff]
  change (Formalism.L2.Theta.mt V g).map (infPart D) = 1 ↔ _
  rw [← Matrix.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero, Matrix.map_apply]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
  · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, RingHom.map_zero]

theorem mem_grpAt_iff_parts (V : HSp D) (P : Pl D → Prop) (g : GA D V) :
    g ∈ grpAt V P ↔ ∀ i j, infPart D ((Formalism.L2.Theta.mt V g - 1) i j) = 0 ∧
      ∀ w, ¬ P w → GlobalTheory.FinPl.compAt D w ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
  rw [grpAt, mem_congGrp_iff]
  exact forall_congr' fun i => forall_congr' fun j => mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D P _

theorem mem_grpOff_iff_parts (V : HSp D) (P : Pl D → Prop) (g : GA D V) :
    g ∈ grpOff V P ↔ ∀ i j w, P w → GlobalTheory.FinPl.compAt D w ((Formalism.L2.Theta.mt V g - 1) i j) = 0 := by
  rw [grpOff, mem_congGrp_iff]
  exact forall_congr' fun i => forall_congr' fun j => mem_idOff_iff P _

theorem grpAt_le_GfC (V : HSp D) (P : Pl D → Prop) : grpAt V P ≤ GfC V := fun g hg =>
  (mem_GfC_iff_entries V g).2 fun i j => ((mem_grpAt_iff_parts V P g).1 hg i j).1

theorem grpAt_le_grpOff (V : HSp D) (P P' : Pl D → Prop) (h : ∀ p, P p → ¬ P' p) : grpAt V P ≤ grpOff V P' := fun g hg =>
  (mem_grpOff_iff_parts V P' g).2 fun i j w hw => ((mem_grpAt_iff_parts V P g).1 hg i j).2 w fun h' => h w h' hw

theorem GfC_inf_grpOff (V : HSp D) (P : Pl D → Prop) : GfC V ⊓ grpOff V P = grpAt V fun p => ¬ P p := by
  ext g
  rw [Subgroup.mem_inf, mem_GfC_iff_entries, mem_grpOff_iff_parts, mem_grpAt_iff_parts]
  exact ⟨fun h i j => ⟨h.1 i j, fun w hw => h.2 i j w (not_not.1 hw)⟩,
    fun h => ⟨fun i j => (h i j).1, fun i j w hw => (h i j).2 w (not_not.2 hw)⟩⟩

abbrev eQ (D : D7) (Q : Finset (Pl D)) : AE D := algebraMap (AF D.host.F) (AE D) (idemQ D Q)

theorem eQ_mul_self (Q : Finset (Pl D)) : eQ D Q * eQ D Q = eQ D Q := by
  rw [← RingHom.map_mul, idemQ_mul_self]

theorem algebraMap_one_sub (c : AF D.host.F) :
    algebraMap (AF D.host.F) (AE D) (1 - c) = 1 - algebraMap (AF D.host.F) (AE D) c := by
  rw [RingHom.map_sub, RingHom.map_one]

theorem smul_of_mem_Q (V : HSp D) (Q : Finset (Pl D)) {a : GA D V} (ha : a ∈ grpAt V (· ∈ Q)) :
    eQ D Q • (Formalism.L2.Theta.mt V a - 1) = Formalism.L2.Theta.mt V a - 1 := by
  rw [grpAt, mem_congGrp_iff] at ha
  exact Matrix.ext fun i j => (mem_idAt_Q_iff Q _).1 (ha i j)

open Classical in
theorem smul_of_mem_Qc (V : HSp D) (Q : Finset (Pl D)) {b : GA D V} (hb : b ∈ grpAt V (· ∉ Q)) :
    eQ D Q • (Formalism.L2.Theta.mt V b - 1) = 0 := by
  rw [mem_grpAt_iff_parts] at hb
  exact Matrix.ext fun i j => (mem_idOff_iff_mul (· ∈ Q) _ (parts_idemQ Q).1 (parts_idemQ Q).2 _).1
    ((mem_idOff_iff _ _).2 fun w hw => (hb i j).2 w (not_not.2 hw))

theorem comm_Q (V : HSp D) (Q : Finset (Pl D)) {a b : GA D V} (ha : a ∈ grpAt V (· ∈ Q)) (hb : b ∈ grpAt V (· ∉ Q)) :
    a * b = b * a := by
  have h := mul_eq_add_sub_one _ _ _ (smul_of_mem_Q V Q ha) (smul_of_mem_Qc V Q hb)
  apply mt_injective V
  rw [mt_mul, mt_mul]
  exact h.1.trans h.2.symm

theorem cutG_left (V : HSp D) (Q : Finset (Pl D)) {a b : GA D V} (ha : a ∈ grpAt V (· ∈ Q)) (hb : b ∈ grpAt V (· ∉ Q)) :
    cutG V _ (idemQ_mul_self Q) (a * b) = a := by
  apply mt_injective V
  rw [mt_cutG, mt_mul]
  exact cut_left _ _ _ (smul_of_mem_Q V Q ha) (smul_of_mem_Qc V Q hb)

theorem cutG_right (V : HSp D) (Q : Finset (Pl D)) {a b : GA D V} (ha : a ∈ grpAt V (· ∈ Q)) (hb : b ∈ grpAt V (· ∉ Q)) :
    cutG V _ (one_sub_idemQ_mul_self Q) (a * b) = b := by
  apply mt_injective V
  rw [mt_cutG, mt_mul, algebraMap_one_sub]
  exact cut_right _ _ _ (smul_of_mem_Q V Q ha) (smul_of_mem_Qc V Q hb)

theorem cutG_mul_cutG (V : HSp D) (Q : Finset (Pl D)) (g : GA D V) :
    cutG V _ (idemQ_mul_self Q) g * cutG V _ (one_sub_idemQ_mul_self Q) g = g := by
  apply mt_injective V
  rw [mt_mul, mt_cutG, mt_cutG, algebraMap_one_sub]
  exact cut_mul_cut _ (eQ_mul_self Q) _

theorem cutG_mem_Q (V : HSp D) (Q : Finset (Pl D)) (g : GA D V) :
    cutG V _ (idemQ_mul_self Q) g ∈ grpAt V (· ∈ Q) := by
  rw [grpAt, mem_congGrp_iff]
  intro i j
  rw [mt_cutG, cut_sub_one, mem_idAt_Q_iff, Matrix.smul_apply, smul_eq_mul, ← mul_assoc]
  exact congrArg (· * _) (eQ_mul_self Q)

open Classical in
theorem cutG_mem_Qc (V : HSp D) (Q : Finset (Pl D)) {g : GA D V} (hg : g ∈ GfC V) :
    cutG V _ (one_sub_idemQ_mul_self Q) g ∈ grpAt V (· ∉ Q) := by
  rw [mem_grpAt_iff_parts]
  intro i j
  rw [mt_cutG, cut_sub_one, Matrix.smul_apply, smul_eq_mul, algebraMap_one_sub]
  refine ⟨?_, fun w hw => ?_⟩
  · rw [RingHom.map_mul, (mem_GfC_iff_entries V g).1 hg i j, mul_zero]
  · rw [RingHom.map_mul, RingHom.map_sub, RingHom.map_one, (parts_idemQ Q).2 w, if_pos (not_not.1 hw), sub_self, zero_mul]

theorem isClosed_of_idem (V : HSp D) (P : Pl D → Prop) (c : AF D.host.F)
    (hc : ∀ a, a ∈ idAt D P ↔ algebraMap (AF D.host.F) (AE D) c * a = a) : IsClosed (grpAt V P : Set (GA D V)) := by
  have h := (_root_.GlobalTheory.FinPl.SetCut.continuous_cutG_and_isClosed D V).2 (1 - c)
  convert h using 1
  ext g
  rw [SetLike.mem_coe, grpAt, mem_congGrp_iff, Set.mem_setOf_eq]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [hc, algebraMap_one_sub, sub_mul, one_mul, sub_eq_zero, eq_comm]

def splitHomeo (V : HSp D) (Q : Finset (Pl D)) : (grpAt V (· ∈ Q) × grpAt V (· ∉ Q)) ≃ₜ GfC V where
  toFun p := ⟨p.1.1 * p.2.1, mul_mem (grpAt_le_GfC V _ p.1.2) (grpAt_le_GfC V _ p.2.2)⟩
  invFun g := (⟨cutG V _ (idemQ_mul_self Q) g.1, cutG_mem_Q V Q g.1⟩,
    ⟨cutG V _ (one_sub_idemQ_mul_self Q) g.1, cutG_mem_Qc V Q g.2⟩)
  left_inv p := Prod.ext (Subtype.ext (cutG_left V Q p.1.2 p.2.2)) (Subtype.ext (cutG_right V Q p.1.2 p.2.2))
  right_inv g := Subtype.ext (cutG_mul_cutG V Q g.1)
  continuous_toFun := by
    haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
    exact Continuous.subtype_mk
      ((continuous_subtype_val.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)) _
  continuous_invFun :=
    (Continuous.subtype_mk (((_root_.GlobalTheory.FinPl.SetCut.continuous_cutG_and_isClosed D V).1 _ _).comp continuous_subtype_val) _).prodMk
      (Continuous.subtype_mk (((_root_.GlobalTheory.FinPl.SetCut.continuous_cutG_and_isClosed D V).1 _ _).comp continuous_subtype_val) _)

theorem grp_split : ∀ (D : D7) (V : HSp D) (Q : Finset (Pl D)), IsClosed (grpAt V (· ∈ Q) : Set (GA D V)) ∧ IsClosed (grpAt V (· ∉ Q) : Set (GA D V)) ∧ grpAt V (· ∈ Q) ≤ GfC V ∧ grpAt V (· ∉ Q) ≤ GfC V ∧ (∀ a ∈ grpAt V (· ∈ Q), ∀ b ∈ grpAt V (· ∉ Q), a * b = b * a) ∧ (∃ e : (grpAt V (· ∈ Q) × grpAt V (· ∉ Q)) ≃ₜ GfC V, ∀ p, (e p : GA D V) = p.1 * p.2) ∧ (∀ P P' : Pl D → Prop, (∀ p, P p → ¬ P' p) → grpAt V P ≤ grpOff V P') ∧ (∀ P : Pl D → Prop, GfC V ⊓ grpOff V P = grpAt V fun p => ¬ P p) ∧ (∀ (L : Lat V), IsSelfDualC V L → ∀ P : Pl D → Prop, (∃ K : Subgroup (GA D V), (∀ g, g ∈ K ↔ InK V L P g) ∧ IsCompact (K : Set (GA D V)) ∧ IsOpen ((K.subgroupOf (grpAt V P) : Subgroup _) : Set (grpAt V P))) ∧ ∀ κ, InK V L P κ ↔ ∃ a b, InK V L (fun p => P p ∧ p ∈ Q) a ∧ InK V L (fun p => P p ∧ p ∉ Q) b ∧ κ = a * b) ∧ ∀ (V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ), (∀ a ∈ grpAt V (· ∈ Q), ∀ b ∈ grpAt V (· ∉ Q), a * b ∈ jacGrp d → a ∈ jacGrp d ∧ b ∈ jacGrp d) ∧ ∀ (A L : HSp D) (o : OrthDec V₀ A L), ∀ a ∈ grpAt V (· ∈ Q), ∀ b ∈ grpAt V (· ∉ Q), a * b ∈ besGrp d o → a ∈ besGrp d o ∧ b ∈ besGrp d o := by
  intro D V Q
  refine ⟨isClosed_of_idem V _ _ (mem_idAt_Q_iff Q), isClosed_of_idem V _ _ (mem_idAt_Qc_iff Q), grpAt_le_GfC V _,
    grpAt_le_GfC V _, fun a ha b hb => comm_Q V Q ha hb, ?_⟩
  refine ⟨⟨splitHomeo V Q, fun _ => rfl⟩, grpAt_le_grpOff V, GfC_inf_grpOff V, ?_, ?_⟩
  · intro L hL P
    exact ⟨_root_.GlobalTheory.FinPl.KOpen.exists_compact_open D V L hL P,
      _root_.GlobalTheory.FinPl.KSplit.inK_iff_prod D V L P Q⟩
  · intro V₀ ρ d
    constructor
    · intro a ha b hb h
      exact ⟨cutG_left V Q ha hb ▸ (_root_.GlobalTheory.FinPl.SetCut.cutG_mem_jacGrp_besGrp D V V₀ ρ d _ (idemQ_mul_self Q)).1 _ h,
        cutG_right V Q ha hb ▸ (_root_.GlobalTheory.FinPl.SetCut.cutG_mem_jacGrp_besGrp D V V₀ ρ d _ (one_sub_idemQ_mul_self Q)).1 _ h⟩
    · intro A L o a ha b hb h
      exact ⟨cutG_left V Q ha hb ▸ (_root_.GlobalTheory.FinPl.SetCut.cutG_mem_jacGrp_besGrp D V V₀ ρ d _ (idemQ_mul_self Q)).2 A L o _ h,
        cutG_right V Q ha hb ▸ (_root_.GlobalTheory.FinPl.SetCut.cutG_mem_jacGrp_besGrp D V V₀ ρ d _ (one_sub_idemQ_mul_self Q)).2 A L o _ h⟩

end GlobalTheory.FinPl.SetCut

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValConjSubLt
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LatPair

namespace GlobalTheory.SeeSaw.LevChi

open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (colGroup colChar colPos superSum)
open GlobalTheory.SymBridge

section Split

variable {D : D7} {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (q : GlobalTheory.FinPl.SplitPt D K) {PP : Formalism.L2.DIV.Pl D.host.E} (h : Formalism.L2.NTheta.IsIdemAt q.e PP)
include h

theorem val_rat_lt {y : D.host.E} (hy : PP.valuation D.host.E y < 1) : valuation K (q.pr (incA D y)) < 1 := by
  obtain ⟨r, d, e⟩ := PP.exists_primeCompl_mul_eq_of_integer y hy.le
  have hd : valuation K (q.pr (incA D ((d : 𝓞 D.host.E) : D.host.E))) = 1 :=
    le_antisymm (LevelTest.val_le_one q _) (not_lt.1 fun h' => d.2 ((LevelTest.val_lt_one_iff q h _).1 h'))
  have hr : r ∈ PP.asIdeal := by
    refine (HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.host.E) PP r).1 ?_
    show PP.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E r) < 1
    rw [← e, map_mul]
    exact (mul_le_of_le_one_right' (PP.valuation_le_one _)).trans_lt hy
  have := (LevelTest.val_lt_one_iff q h r).2 hr
  rwa [show (r : D.host.E) = y * ((d : 𝓞 D.host.E) : D.host.E) from e.symm, map_mul, map_mul, map_mul, hd, mul_one] at this


set_option maxHeartbeats 1000000 in
theorem val_pr_lt {z : AE D} (hz : Valued.v (adAt D.host.F PP (toEAf D z)) < 1) : valuation K (q.pr z) < 1 := by
  obtain ⟨y, N, r, hr, hN, e⟩ := exists_approx_small (F := D.host.F) (toEAf D z) {PP} (γ := 1) one_ne_zero
  have hN' := hN PP (Finset.mem_singleton_self PP)
  have h1 : PP.valuation D.host.E y < 1 := by
    rw [← valued_algebraMap, ← adAt_inclE D.host.F, ← sub_eq_iff_eq_add.2 e, map_sub]
    exact Valuation.map_sub_lt _ hz (valued_nat_mul_lt hr hN')
  have hnat : ∀ M : ℕ, (M : 𝓞 D.host.E) ∈ PP.asIdeal → valuation K (M : K) < 1 := fun M hM => by
    simpa using (LevelTest.val_lt_one_iff q h _).2 hM
  let sw := (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E)
  have hf : finPart D (z - incA D y) = (N : Af D.host.F ⊗[D.host.F] D.host.E) * sw.symm r := by
    apply sw.injective
    rw [map_mul, map_natCast, AlgEquiv.apply_symm_apply]
    show toEAf D (z - incA D y) = _
    rw [RingHom.map_sub, e]
    exact add_sub_cancel_left _ _
  have h2 : valuation K (q.pr (z - incA D y)) < 1 := by
    rcases Nat.eq_zero_or_pos N with rfl | hpos
    · refine (GlobalTheory.FinPl.SplitApprox.val_le q (Ideal.absNorm PP.asIdeal)
        (Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact PP.ne_bot)) _ 0 (zero_mem _) ?_).trans_lt
        (hnat _ (Ideal.absNorm_mem _))
      rw [hf, Nat.cast_zero, zero_mul, mul_zero]
    · refine (GlobalTheory.FinPl.SplitApprox.val_le q N hpos _ _ ((GlobalTheory.IdemSupport.mem_intAE_iff _).2 ?_) hf).trans_lt (hnat _ ?_)
      · exact (show Lev.swapAE D (sw.symm r) = r from sw.apply_symm_apply r).symm ▸ hr
      · rw [LevRead.valued_natCast] at hN'
        exact (HeightOneSpectrum.valuation_lt_one_iff_mem (K := D.host.E) PP _).1 hN'
  have h3 := (valuation K).map_add_lt h2 (val_rat_lt q h h1)
  rwa [← map_add, sub_add_cancel] at h3

end Split

section Local

variable {D : D7} {u : D.what₂.Word} {a : XPart D u} {ζ₀ : Fin a.Lz.rank → D.host.E} {PP : Formalism.L2.DIV.Pl D.host.E} (H : GX a ζ₀ PP)

end Local

end GlobalTheory.SeeSaw.LevChi

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDataLines
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.WeilLines

open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)

variable {D : D7}

theorem charUnram_mul {χ χ' : (AE D)ˣ →* Circle} {v} (h : CharUnramAt D χ v) (h' : CharUnramAt D χ' v) :
    CharUnramAt D (χ * χ') v := fun x h1 h2 h3 h4 => by
  rw [MonoidHom.mul_apply, h x h1 h2 h3 h4, h' x h1 h2 h3 h4, mul_one]

theorem charUnram_inv {χ : (AE D)ˣ →* Circle} {v} (h : CharUnramAt D χ v) : CharUnramAt D χ⁻¹ v := fun x h1 h2 h3 h4 => by
  rw [MonoidHom.inv_apply, h x h1 h2 h3 h4, inv_one]

end GlobalTheory.SeeSaw.WeilLines

namespace GlobalTheory.SeeSaw.WeilLines

open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (CharUnramAt)

end GlobalTheory.SeeSaw.WeilLines
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumInertPlaceStandardCayleyPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto

theorem eq_of_inert_under {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (hin : IsInertAt F E v w)
    (w' : HeightOneSpectrum (𝓞 E)) (h' : w'.under (𝓞 F) = v) : w' = w := by
  have hle : w.asIdeal ≤ w'.asIdeal := by
    rw [← hin, Ideal.map_le_iff_le_comap, ← h', HeightOneSpectrum.under_asIdeal]
  exact (HeightOneSpectrum.ext (w.isMaximal.eq_of_le w'.isPrime.ne_top hle)).symm


set_option maxHeartbeats 2000000 in
theorem std_cayley_of_inert : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → UnrAt χS w → UnrAt χT w → ∀ c ϖ eS eT, IsUnramInv ϖ c (qV D.host.F v) → IsInertChart D.sp.cm.sig S.gram (frameLat S) h c eS → IsInertChart D.sp.cm.sig T.gram (frameLat T) h c eT → ∀ f, VacFin ψ S T v f → f ≠ 0 → ∃ (δ : w.adicCompletion D.host.E) (ψ' : AddChar (w.adicCompletion D.host.E) ℂ) (M : Submodule ℂ (WO S T → ℂ)) (ρ : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E) → Module.End ℂ M) (ω : GU c S.rank × GU c T.rank →* Module.End ℂ M) (s : M), IsStd ϖ c (qV D.host.F v) δ ψ' ρ ω s ∧ (s : WO S T → ℂ) = f ∧ (∀ g g' (m : M), ((ω (g, g') m : M) : WO S T → ℂ) = om (embV S v (eS.symm g), embV T v (eT.symm g')) m) ∧ CayleyRule (qV D.host.F v) T.rank ρ (ω.comp (MonoidHom.inl _ _)) s ∧ CayleyRule (qV D.host.F v) S.rank ρ (ω.comp (MonoidHom.inr _ _)) s := by
  intro D ψ S T χS χT om hW v w h hin hS hT c ϖ eS eT hU heS heT f hf hf0
  obtain ⟨δ, ψ', M, ρ, ω, s, hstd, hsf, hω, hth, hρ⟩ :=
    _root_.GlobalTheory.InertFrameLoc.exists_isStd_inert D ψ S T χS χT om hW v w h hin hS hT c ϖ eS eT hU heS heT f hf hf0
  obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.Size.exists_isCovolOne S T
  have hψ := hW.std
  have hthf : IsThetaFunO ψ S T f := hf.1
  let l : M →ₗ[ℂ] ℂ :=
    { toFun := fun m => Lift.pet μ 𝓕 (m : WO S T → ℂ) f
      map_add' := fun m m' => by
        show GlobalTheory.Ker.ipO μ 𝓕 ((m + m' : M) : WO S T → ℂ) f = GlobalTheory.Ker.ipO μ 𝓕 _ f + GlobalTheory.Ker.ipO μ 𝓕 _ f
        rw [Submodule.coe_add]
        exact GlobalTheory.Size.ipO_add_left hψ hμ.1 hμ.2.1 (hth m) (hth m') hthf
      map_smul' := fun a m => by
        show GlobalTheory.Ker.ipO μ 𝓕 ((a • m : M) : WO S T → ℂ) f = a * GlobalTheory.Ker.ipO μ 𝓕 _ f
        rw [Submodule.coe_smul]
        exact GlobalTheory.Size.ipO_smul_left μ 𝓕 a _ _ }
  have hl : ∀ m : M, l m = Lift.pet μ 𝓕 (m : WO S T → ℂ) f := fun _ => rfl
  have hls : l s ≠ 0 := by
    rw [hl, hsf]
    exact fun h0 => hf0 ((GlobalTheory.Size.ipO_self_eq_zero_iff hψ hμ.1 hμ.2.1 hthf).1 h0)
  have hinv : ∀ u ∈ intMat (w.adicCompletion D.host.E) (Fin T.rank) (Fin S.rank), ∀ m : M, l (ρ u m) = l m := by
    intro u hu m
    obtain ⟨u0, hu0⟩ := hρ u
    have hfix : heisO ψ S T u0 f = f := by
      have e := hu0 s
      rw [hstd.fixes u hu, hsf] at e
      exact e.symm
    rw [hl, hl, hu0 m]
    conv_lhs => rw [← hfix]
    exact GlobalTheory.Size.ipO_heisO hψ hμ.1 hμ.2.1 (hth m) hthf u0
  have hcay := _root_.GlobalTheory.ChainOnto.cayleyRule_of_vacCoeff _ ϖ c (qV D.host.F v) δ ψ' S.rank T.rank M ρ ω s hstd l hls hinv
  obtain ⟨φ1, hk1, hc1⟩ := _root_.GlobalTheory.VacSource.vacuum_matrixCoefficient_source_inert_place D ψ S T χS χT om hW μ 𝓕 hμ v w h hin hS hT c ϖ eS hU heS
  have hunr : ∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v → UnrAt χS w' ∧ UnrAt χT w' :=
    fun w' h' => by
      rw [eq_of_inert_under hin w' h']
      exact ⟨hS, hT⟩
  obtain ⟨φ2, hk2, hc2⟩ := _root_.GlobalTheory.VacCoef.vac_coef D ψ S T χS χT om hW μ 𝓕 hμ v hunr
  have hval := (GlobalTheory.T.heckeChar_value_inert_place_and_segment D χS S.rank hW.hecS hW.resS v w h hin hS).1
  have hk2' := (hk2 w h).2 hin c ϖ eT hU heT
  rw [hval] at hk2'
  refine ⟨δ, ψ', M, ρ, ω, s, hstd, hsf, hω, hcay.1 φ1 hk1 fun g => ?_, hcay.2 (φ2 ∘ eT.symm) hk2' fun g => ?_⟩
  · exact (congrArg (fun x => Lift.pet μ 𝓕 x f) ((hω g 1 s).trans (by rw [map_one eT.symm, map_one (embV T v), hsf]))).trans
      ((hc1 g f f hf hf).trans (by rw [hl, hsf]))
  · exact (congrArg (fun x => Lift.pet μ 𝓕 x f) ((hω 1 g s).trans (by rw [map_one eS.symm, map_one (embV S v), hsf]))).trans
      ((hc2 (eT.symm g) f f hf hf).trans (by rw [hl, hsf]; rfl))

end GlobalTheory.ChainOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumOfRankOneGram
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.WeilTup

variable {D : D7}

theorem hecke_mul {χ χ' : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) (h' : IsHeckeChar D χ') : IsHeckeChar D (χ * χ') :=
  ⟨by show Continuous (fun x => χ x * χ' x); exact h.1.mul h'.1, fun x => by rw [MonoidHom.mul_apply, h.2 x, h'.2 x, mul_one]⟩

theorem hecke_inv {χ : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) : IsHeckeChar D χ⁻¹ :=
  ⟨by rw [show ⇑χ⁻¹ = fun x => (χ x)⁻¹ from funext fun x => MonoidHom.inv_apply χ x]; exact h.1.inv,
    fun x => by rw [MonoidHom.inv_apply, h.2 x, inv_one]⟩

theorem resEta_of_diff {μ χ : (AE D)ˣ →* Circle} {n : ℕ} (hA : ResEta D μ (n + 1)) (hB : ResEta D (μ * χ⁻¹) n) :
    ResEta D χ 1 := by
  refine ⟨hA.1, fun e he a => ?_⟩
  have h1 := hA.2 e he a
  have h2 := hB.2 e he a
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, h1, pow_succ] at h2
  rw [pow_one]
  exact (mul_left_cancel (mul_inv_eq_iff_eq_mul.1 h2)).symm

end GlobalTheory.Fam.WeilTup

end
end

