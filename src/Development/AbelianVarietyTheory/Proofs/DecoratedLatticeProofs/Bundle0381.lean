module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0359
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0267
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0362
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0351
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bundle0006
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlaceOfSupportedStabilizer
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0077

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSchwartzBruhatExtByZeroOfSplitPlaceHalf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)

namespace GlobalTheory.SBOfHalf

theorem exists_sb_ext_eq : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (Λ : AddSubgroup (WO S T)), IsOpen ((Λ.comap (GlobalTheory.LocMod.Witness.upH p FS FT) : AddSubgroup (Matrix Y Y' k)) : Set (Matrix Y Y' k)) → IsCompact ((Λ.comap (GlobalTheory.LocMod.Witness.upH p FS FT) : AddSubgroup (Matrix Y Y' k)) : Set (Matrix Y Y' k)) → ∀ Φ : WO S T → ℂ, IsSBHalf p.e Λ Φ → ∃ Φ' : SB (Matrix Y Y' k), GlobalTheory.LocMod.Witness.ext p FS FT Φ' = Φ := by
  intro D k _ _ _ _ p S T Y Y' _ _ _ _ FS FT Λ hAo hAc Φ hΦ
  classical
  set A : AddSubgroup (Matrix Y Y' k) := Λ.comap (GlobalTheory.LocMod.Witness.upH p FS FT) with hA
  obtain ⟨hsupp, k₀, hk₀, hinv, hsup⟩ := hΦ
  have hkF : ((k₀ : D.host.F)) ≠ 0 := Nat.cast_ne_zero.2 hk₀.ne'
  have hkk : ((k₀ : k)) ≠ 0 := by
    have h := (map_ne_zero (p.π.comp (algebraMap D.host.F (AE D)))).2 hkF
    simpa using h
  have hupA : ∀ a : Matrix Y Y' k, a ∈ A ↔ p.up FS FT a ∈ Λ := fun a => Iff.rfl
  have hnsmul : ∀ (x : Matrix Y Y' k), k₀ • x = (k₀ : k) • x := fun x => by
    rw [← Nat.cast_smul_eq_nsmul k]
  have hup_nsmul : ∀ (x : Matrix Y Y' k), p.up FS FT (k₀ • x) = k₀ • p.up FS FT x := fun x =>
    map_nsmul (GlobalTheory.LocMod.Witness.upH p FS FT) k₀ x
  let f : Matrix Y Y' k → ℂ := fun x => Φ (p.up FS FT x)
  have hloc : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hV : IsOpen {z : Matrix Y Y' k | (k₀ : k)⁻¹ • z ∈ A} :=
      hAo.preimage (continuous_const_smul _)
    have h0 : (x - x) ∈ {z : Matrix Y Y' k | (k₀ : k)⁻¹ • z ∈ A} := by
      simp only [sub_self, Set.mem_setOf_eq, smul_zero]; exact A.zero_mem
    have hn := (continuous_sub_right x).continuousAt.preimage_mem_nhds (hV.mem_nhds h0)
    filter_upwards [hn] with y hy
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hy
    have hy' : y = x + k₀ • ((k₀ : k)⁻¹ • (y - x)) := by
      rw [hnsmul, smul_smul, mul_inv_cancel₀ hkk, one_smul, add_sub_cancel]
    show Φ (p.up FS FT y) = Φ (p.up FS FT x)
    rw [hy', GlobalTheory.LocMod.Witness.up_add, hup_nsmul]
    exact hinv _ hy (GlobalTheory.LocMod.Witness.up_half p FS FT _) _
  have hcpt : HasCompactSupport f := by
    refine HasCompactSupport.intro (hAc.image (continuous_const_smul ((k₀ : k)⁻¹))) fun x hx => ?_
    by_contra hne
    apply hx
    refine ⟨k₀ • x, ?_, ?_⟩
    · show p.up FS FT (k₀ • x) ∈ Λ
      rw [hup_nsmul]; exact hsup _ hne
    · show (k₀ : k)⁻¹ • k₀ • x = x
      rw [hnsmul, smul_smul, inv_mul_cancel₀ hkk, one_smul]
  refine ⟨⟨f, hloc, hcpt⟩, ?_⟩
  funext t
  rw [GlobalTheory.LocMod.Witness.ext_apply]
  split_ifs with ht
  · show Φ (p.up FS FT (p.down FS FT t)) = Φ t
    rw [GlobalTheory.LocMod.Witness.up_down p FS FT ht]
  · by_contra h
    exact ht (hsupp t (Ne.symm h))

end GlobalTheory.SBOfHalf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticePatchedAtPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

namespace GlobalTheory.FinPl.Patch

open GlobalTheory.FinPlLoc

variable {D : D7}

theorem mul_eq_zero_of_ne {x w : Pl D} (h : w ≠ x) {a b : AE D} (ha : a ∈ idAt D (· = x)) (hb : b ∈ idAt D (· = w)) :
    a * b = 0 := by
  apply eq_zero_of_comp
  · rw [map_mul, infPart_of_idAt ha, zero_mul]
  · intro v
    rw [map_mul]
    by_cases hv : v = x
    · rw [compAt_of_idAt hb (w := v) (fun h' => h (h'.symm.trans hv)), mul_zero]
    · rw [compAt_of_idAt ha (w := v) hv, zero_mul]

theorem mulVec_eq_of_ne {S : HSp D} {x w : Pl D} (h : w ≠ x) {g : GA D S} (hg : g ∈ grpAt S (· = x))
    {y : Fin S.rank → AE D} (hy : ∀ i, y i ∈ idAt D (· = w)) : mt S g *ᵥ y = y := by
  have hg' := (mem_congGrp _ g).1 hg
  have h0 : (mt S g - 1) *ᵥ y = 0 := by
    funext i
    show ∑ j, (mt S g - 1) i j * y j = 0
    exact Finset.sum_eq_zero fun j _ => mul_eq_zero_of_ne h (hg' i j) (hy j)
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
  exact h0

theorem latV_eq_off {S : HSp D} {x w : Pl D} (h : w ≠ x) {g : GA D S} (hg : g ∈ grpAt S (· = x)) {L M : Lat S}
    (hm : Moves S g L M (· = w)) : latV S M (· = w) = latV S L (· = w) := by
  ext y
  constructor
  · intro hy
    have hid := latV_idAt hy
    rw [hm y hid, mulVec_eq_of_ne h hg hid]
    exact hy
  · intro hy
    have hid := latV_idAt hy
    have := (hm y hid).1 hy
    rwa [mulVec_eq_of_ne h hg hid] at this

theorem latV_le_of_moves {S : HSp D} {P : Pl D → Prop} {g : GA D S} {L M M' : Lat S} (hm : Moves S g L M P)
    (hm' : Moves S g L M' P) : latV S M P ≤ latV S M' P := by
  intro y hy
  have hid := latV_idAt hy
  have hz : ∀ i, (mt S g⁻¹ *ᵥ y) i ∈ idAt D P := fun i => by
    show ∑ j, mt S g⁻¹ i j * y j ∈ idAt D P
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hid j)
  have he : mt S g *ᵥ (mt S g⁻¹ *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, ← FinPlLoc.mt_mul, mul_inv_cancel, FinPlLoc.mt_one, Matrix.one_mulVec]
  have h1 := (hm _ hz).2 (by rw [he]; exact hy)
  have h2 := (hm' _ hz).1 h1
  rwa [he] at h2

theorem patch : ∀ (D : D7) (S : HSp D) (L L' : Lat S), IsSelfDualC S L → IsSelfDualC S L' → ∀ Z : Finset (Pl D),
    ∃ M : Lat S, IsSelfDualC S M ∧ (∀ x ∈ Z, latV S M (· = x) = latV S L' (· = x)) ∧
      ∀ x, x ∉ Z → latV S M (· = x) = latV S L (· = x) := by
  classical
  intro D S L L' hL hL' Z
  induction Z using Finset.induction_on with
  | empty => exact ⟨L, hL, fun x hx => absurd hx (Finset.notMem_empty x), fun _ _ => rfl⟩
  | insert x Z hx ih =>
    obtain ⟨M, hM, h1, h2⟩ := ih
    obtain ⟨g, hg, hgm⟩ := _root_.GlobalTheory.FinPl.SelfDualConj.conj_at_place D S M L' hM hL' x
    obtain ⟨M', hM', hmv⟩ := (_root_.GlobalTheory.FinPl.GlobImage.glob D S M hM).1 g
    refine ⟨M', hM', fun w hw => ?_, fun w hw => ?_⟩
    · by_cases hwx : w = x
      · subst hwx
        exact le_antisymm (latV_le_of_moves (hmv _) hgm) (latV_le_of_moves hgm (hmv _))
      · rw [latV_eq_off hwx hg (hmv _)]
        exact h1 w ((Finset.mem_insert.1 hw).resolve_left hwx)
    · rw [Finset.mem_insert, not_or] at hw
      rw [latV_eq_off hw.1 hg (hmv _)]
      exact h2 w hw.2

end GlobalTheory.FinPl.Patch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPlaceComponentRingHomIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm

noncomputable section
namespace GlobalTheory.FinPl.SplitPhi
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_e (p : SplitPt D k) : p.pr p.e = 1 := by
  have h := p.sec_pr 1
  rw [mul_one] at h
  rw [← h, p.pr_sec, map_one]

theorem prV_toEAf_e_ne (p : SplitPt D k) {w : HeightOneSpectrum (𝓞 D.host.F)} (hw : w ≠ p.v) :
    Formalism.UG.prV (E := D.host.E) w (toEAf D p.e) = 0 := by
  obtain ⟨ε, hε, he⟩ := p.above
  obtain ⟨h1, h2, -⟩ := p.split
  have : p.e = algebraMap (AF D.host.F) (AE D) ε * p.e := by
    rw [← he, add_mul, h1, mul_comm (cA D p.e), h2, add_zero]
  rw [this]
  exact GlobalTheory.AdForm.ChiStd.prV_toEAf_idem_mul hε hw _

theorem prV_toEAf_eps (p : SplitPt D k) {ε : AF D.host.F} (hε : IsPlaceIdem D p.v ε) :
    Formalism.UG.prV (E := D.host.E) p.v (toEAf D (algebraMap (AF D.host.F) (AE D) ε)) = 1 := by
  obtain ⟨α, rfl, h1, -⟩ := hε
  have h1' : (Formalism.UG.evalV D.host.F p.v) ((sndA D.host.F) (pairA D.host.F 0 α)) = 1 := h1
  rw [Algebra.TensorProduct.algebraMap_apply]
  simp [Formalism.IndefR.Datum.toEAf, finPart, Formalism.UG.prV]
  rw [h1']
  rfl

theorem prF_eq_zero (p : SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP)
    (y : EAf D) (hy : Formalism.UG.prV (E := D.host.E) p.v y = 0) : p.prF he y = 0 := by
  have h0 : toEAf D p.e * y = 0 := by
    refine Formalism.UG.P.afsplit_inj _ fun w => ?_
    rw [map_mul]
    by_cases hw : w = p.v
    · subst hw; rw [hy, mul_zero]
    · rw [prV_toEAf_e_ne p hw, zero_mul]
  have : p.prF he y = p.prF he (toEAf D p.e * y) := by
    rw [map_mul, p.prF_toEAf he, pr_e, one_mul]
  rw [this, h0, map_zero]

theorem prF_IE_prV (p : SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP)
    (y : EAf D) : p.prF he (Formalism.UG.P.afsplitIE p.v (Formalism.UG.prV (E := D.host.E) p.v y)) = p.prF he y := by
  rw [← sub_eq_zero, ← map_sub]
  apply prF_eq_zero p he
  rw [map_sub, Formalism.UG.P.afsplit_prV_IE, sub_self]

def phi (p : SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP) :
    D.host.E ⊗[D.host.F] p.v.adicCompletion D.host.F →+* k where
  toFun x := p.prF he (Formalism.UG.P.afsplitIE p.v x)
  map_one' := by
    have := prF_IE_prV p he 1
    rw [map_one (Formalism.UG.prV (E := D.host.E) p.v), map_one (p.prF he)] at this
    exact this
  map_mul' x y := by simp only [map_mul]
  map_zero' := by simp only [map_zero]
  map_add' x y := by simp only [map_add (f := _)]

theorem phi_apply (p : SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP)
    (x : D.host.E ⊗[D.host.F] p.v.adicCompletion D.host.F) :
    phi p he x = p.prF he (Formalism.UG.P.afsplitIE p.v x) := rfl

theorem phi_prV (p : SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP)
    (a : AE D) : phi p he (Formalism.UG.prV (E := D.host.E) p.v (toEAf D a)) = p.pr a := by
  rw [phi_apply, prF_IE_prV, p.prF_toEAf he]

theorem phi_inclE (p : SplitPt D k) {PP : HeightOneSpectrum (𝓞 D.host.E)} (he : Formalism.L2.NTheta.IsIdemAt p.e PP)
    (c : D.host.E) : phi p he (Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) c) = p.pr (incA D c) := by
  rw [← phi_prV p he]
  rfl

theorem tensInt_iff (v : HeightOneSpectrum (𝓞 D.host.F)) (z : D.host.E ⊗[D.host.F] v.adicCompletion D.host.F) :
    z ∈ Formalism.UG.tensInt (F := D.host.F) (v.adicCompletion D.host.F) (Formalism.UG.intOE D.host.E)
        (v.adicCompletionIntegers D.host.F).toSubring ↔
      Formalism.UG.P.afsplitIE v z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  refine ⟨Formalism.UG.P.afsplit_IE_int v z, fun h => ?_⟩
  have := Formalism.UG.P.afsplit_prV_int v _ h
  rwa [Formalism.UG.P.afsplit_prV_IE] at this

theorem sigR_sigR (z : EAf D) : Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)
    (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => exact congrArg (· ⊗ₜ[D.host.F] x) (star_star a)
  | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb]

theorem toEAf_cA (a : AE D) : toEAf D (cA D a) = Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (toEAf D a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add a b ha hb => simp only [RingHom.map_add (f := _), ha, hb]
  | tmul y e => rfl

theorem sigR_mem_iff (s : EAf D) : Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) s ∈
    Formalism.L2.Herm.intAf D.host.F D.host.E ↔ s ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  refine ⟨fun h => ?_, GlobalTheory.LevSplit.sigR_int⟩
  have := GlobalTheory.LevSplit.sigR_int h
  rwa [sigR_sigR] at this

theorem one_sub_e_mul (p : SplitPt D k) (y : EAf D)
    (hy : ∀ w, w ≠ p.v → Formalism.UG.prV (E := D.host.E) w y = 0) :
    (1 - toEAf D p.e) * y = toEAf D (cA D p.e) * y := by
  obtain ⟨ε, hε, he⟩ := p.above
  rw [← sub_eq_zero, ← sub_mul, sub_sub, ← RingHom.map_add (f := _), he]
  refine Formalism.UG.P.afsplit_inj _ fun w => ?_
  rw [map_mul]
  by_cases hw : w = p.v
  · subst hw; rw [map_sub, map_one, prV_toEAf_eps p hε, sub_self, zero_mul]
  · rw [hy w hw, mul_zero]

theorem sigR_inclE (v : HeightOneSpectrum (𝓞 D.host.F)) (c : D.host.E) :
    Formalism.UG.sigR (sigD D) (v.adicCompletion D.host.F) (Formalism.UG.inclE (F := D.host.F) (v.adicCompletion D.host.F) c) =
      Formalism.UG.inclE (F := D.host.F) (v.adicCompletion D.host.F) (sigD D c) := by
  simp only [Formalism.UG.sigR, Formalism.UG.inclE, Algebra.TensorProduct.includeLeftRingHom_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]

theorem exists_ringHom_int : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e PP →
    ∃ φ : D.host.E ⊗[D.host.F] p.v.adicCompletion D.host.F →+* k,
      (∀ a : AE D, φ (Formalism.UG.prV (E := D.host.E) p.v (toEAf D a)) = p.pr a) ∧
      (∀ c : D.host.E, φ (Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) c) = p.pr (incA D c)) ∧
      (∀ c : D.host.E, φ (Formalism.UG.sigR (sigD D) (p.v.adicCompletion D.host.F)
          (Formalism.UG.inclE (F := D.host.F) (p.v.adicCompletion D.host.F) c)) = p.pr (incA D (sigD D c))) ∧
      ∀ z, z ∈ Formalism.UG.tensInt (F := D.host.F) (p.v.adicCompletion D.host.F) (Formalism.UG.intOE D.host.E)
          (p.v.adicCompletionIntegers D.host.F).toSubring ↔
        φ z ∈ 𝒪[k] ∧ φ (Formalism.UG.sigR (sigD D) (p.v.adicCompletion D.host.F) z) ∈ 𝒪[k] := by
  intro D k _ _ _ _ p PP he
  refine ⟨phi p he, phi_prV p he, phi_inclE p he, fun c => by rw [sigR_inclE]; exact phi_inclE p he (sigD D c), fun z => ?_⟩
  set y := Formalism.UG.P.afsplitIE p.v z with hy
  have hsup : ∀ w, w ≠ p.v → Formalism.UG.prV (E := D.host.E) w y = 0 := fun w hw =>
    Formalism.UG.P.afsplit_prV_IE_ne p.v w hw z
  have hsig : Formalism.UG.P.afsplitIE p.v (Formalism.UG.sigR (sigD D) (p.v.adicCompletion D.host.F) z) =
      Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) y := by
    rw [hy]; exact (Formalism.UG.P.afsplit_sigR_IE (sigD D) p.v z).symm
  have h1 := tensInt_iff p.v z
  have h2 := p.mem_intAf_iff he y
  have h3 := one_sub_e_mul p y hsup
  have h4 := p.prF_mem_iff he (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) y)
  have h5 : toEAf D (cA D p.e) * y = Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)
      (toEAf D p.e * Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) y) := by
    rw [RingHom.map_mul, sigR_sigR, toEAf_cA]
  refine h1.trans (h2.trans ?_)
  rw [h3, h5, sigR_mem_iff, ← h4]
  have e1 : phi p he z = p.prF he y := phi_apply p he z
  have e2 : phi p he (Formalism.UG.sigR (sigD D) (p.v.adicCompletion D.host.F) z) =
      p.prF he (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) y) := (phi_apply p he _).trans (congrArg _ hsig)
  rw [e1, e2]
  exact and_comm

end GlobalTheory.FinPl.SplitPhi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSuppVecLocEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Pointwise

noncomputable section

namespace GlobalTheory.StMoves

variable {D : D7}


set_option maxHeartbeats 1600000 in
theorem mem_latV_iff_latLoc (V : HSp D) (L : Lat V) (hL : L.FG) (v : Pl D) (y : Fin V.rank → AE D)
    (hy : ∀ i, y i ∈ idAt D (· = v)) :
    y ∈ GlobalTheory.FinPl.latV V L (· = v) ↔
      GlobalTheory.AdelicU.vecLoc v (finPart D ∘ y) ∈ GlobalTheory.AdelicU.latLoc D.host.F L v := by
  rw [GlobalTheory.FinPl.KOpen.mem_latV_iff V L _ y hy, GlobalTheory.AdelicU.mem_latHat_iff hL]
  refine ⟨fun h => h v, fun h w => ?_⟩
  by_cases e : w = v
  · subst e; exact h
  · have h0 : GlobalTheory.AdelicU.vecLoc w (finPart D ∘ y) = 0 :=
      funext fun i => ((mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D _ _).1 (hy i)).2 w e
    rw [h0]; exact zero_mem _

theorem exists_supp_vecLoc_eq {n : ℕ} (v : Pl D) (z : Fin n → Fv D.host.F v ⊗[D.host.F] D.host.E) :
    ∃ y : Fin n → AE D, (∀ i, y i ∈ idAt D (· = v)) ∧ GlobalTheory.AdelicU.vecLoc v (finPart D ∘ y) = z := by
  choose lift hl1 hl2 using GlobalTheory.KStabBridge.exists_fin_lift (D := D)
  let y' : Fin n → Af D.host.F ⊗[D.host.F] D.host.E := fun i =>
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU (GlobalTheory.AdelicU.singleFin v) (GlobalTheory.AdelicU.singleFin_mul v) (z i)
  have h1 : GlobalTheory.AdelicU.vecLoc v y' = z :=
    funext fun i => GlobalTheory.AutFunCompare.map_tensNU_self _ _ _ (GlobalTheory.AdelicU.evalV_singleFin_self v) _
  have h2 : ∀ u, u ≠ v → GlobalTheory.AdelicU.vecLoc u y' = 0 := fun u hu =>
    funext fun i => GlobalTheory.AutFunCompare.map_tensNU_zero _ _ _ (GlobalTheory.AdelicU.evalV_singleFin_ne hu) _
  have h3 : finPart D ∘ (fun i => lift (y' i)) = y' := funext fun i => hl2 _
  refine ⟨fun i => lift (y' i), fun i => (mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere D _ _).2 ⟨hl1 _, fun w hw => ?_⟩, by rw [h3, h1]⟩
  change GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.compFin D w (finPart D (lift (y' i))) = 0
  rw [hl2]
  exact congrFun (h2 w hw) i


set_option maxHeartbeats 1600000 in
theorem moves_iff_stabLoc (V : HSp D) (L : Lat V) (hL : L.FG) (v : Pl D) (g : GA D V) :
    Moves V g L L (· = v) ↔
      GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram L v := by
  have key : ∀ y : Fin V.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) →
      (mt V g *ᵥ y ∈ GlobalTheory.FinPl.latV V L (· = v) ↔
        (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g)).1 *ᵥ
          GlobalTheory.AdelicU.vecLoc v (finPart D ∘ y) ∈ GlobalTheory.AdelicU.latLoc D.host.F L v) := fun y hy => by
    rw [mem_latV_iff_latLoc V L hL v _ (GlobalTheory.FinPl.KOpen.supp_mulVec V _ g hy), GlobalTheory.FinPl.KOpen.fin_mulVec]
    exact iff_of_eq (congrArg (· ∈ GlobalTheory.AdelicU.latLoc D.host.F L v)
      (GlobalTheory.AdelicU.vecLoc_mulVec D.sp.cm.sig V.gram v g _))
  refine Iff.trans ⟨fun h z => ?_, fun h y hy => ?_⟩ GlobalTheory.AdelicU.mem_stabLoc.symm
  · obtain ⟨y, hy, rfl⟩ := exists_supp_vecLoc_eq v z
    exact (mem_latV_iff_latLoc V L hL v y hy).symm.trans ((h y hy).trans (key y hy))
  · exact (mem_latV_iff_latLoc V L hL v y hy).trans ((h _).trans (key y hy).symm)

theorem moves_mul {V : HSp D} {g h : GA D V} {L M N : Lat V} {P : Pl D → Prop} (hg : Moves V g L M P)
    (hh : Moves V h M N P) : Moves V (h * g) L N P := by
  intro y hy
  rw [hg y hy, hh _ (GlobalTheory.FinPl.KOpen.supp_mulVec V P g hy)]
  show _ ↔ mt V (h * g) *ᵥ y ∈ _
  rw [show mt V (h * g) = mt V h * mt V g from rfl, Matrix.mulVec_mulVec]

theorem moves_inv {V : HSp D} {g : GA D V} {L M : Lat V} {P : Pl D → Prop} (hg : Moves V g L M P) :
    Moves V g⁻¹ M L P := by
  intro y hy
  have h1 := hg (mt V g⁻¹ *ᵥ y) (GlobalTheory.FinPl.KOpen.supp_mulVec V P g⁻¹ hy)
  rw [Matrix.mulVec_mulVec, show mt V g * mt V g⁻¹ = mt V (g * g⁻¹) from rfl, mul_inv_cancel,
    show mt V (1 : GA D V) = 1 from rfl, Matrix.one_mulVec] at h1
  exact h1.symm

theorem moves_conj_iff {V : HSp D} {t : GA D V} (h : GA D V) {L M : Lat V} {P : Pl D → Prop} (ht : Moves V t L M P) :
    Moves V (t⁻¹ * h * t) L L P ↔ Moves V h M M P := by
  refine ⟨fun H => ?_, fun H => ?_⟩
  · have := moves_mul (moves_mul (moves_inv ht) H) ht
    rwa [show t * (t⁻¹ * h * t * t⁻¹) = h by group] at this
  · have := moves_mul (moves_mul ht H) (moves_inv ht)
    rwa [← mul_assoc] at this

end GlobalTheory.StMoves

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FullOfSpanEqTop
section
namespace GlobalTheory.FullLatticeOfSpan

open NumberField

theorem exists_smul_mem {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V]
    [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (N : Submodule (𝓞 E) V) {x : V}
    (hx : x ∈ Submodule.span E (N : Set V)) : ∃ d : 𝓞 E, d ≠ 0 ∧ d • x ∈ N := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine N.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact N.smul_mem _ hay
    · rw [mul_smul]; exact N.smul_mem _ hbz
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) c
    have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
    have hsE : algebraMap (𝓞 E) E s ≠ 0 := by
      intro h
      exact hs0 (IsFractionRing.injective (𝓞 E) E (by rw [h, map_zero]))
    refine ⟨a * s, mul_ne_zero ha hs0, ?_⟩
    have : (a * s) • ((algebraMap (𝓞 E) E r / algebraMap (𝓞 E) E s) • y) = r • (a • y) := by
      rw [← algebraMap_smul E (a * s), ← algebraMap_smul E r, ← algebraMap_smul E a,
        smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [this]
    exact N.smul_mem _ hay

theorem exists_nat_dvd {E : Type} [Field E] [NumberField E] (d : 𝓞 E) (hd : d ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ d ∣ (m : 𝓞 E) := by
  refine ⟨Ideal.absNorm (Ideal.span {d}), ?_, ?_⟩
  · apply Nat.pos_of_ne_zero
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hd
  · exact Ideal.mem_span_singleton.mp (Ideal.absNorm_mem _)

theorem full_of_span_eq_top : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (N : Submodule (NumberField.RingOfIntegers E) (Formalism.L2.Col.Sp E n)),
    Submodule.span E (↑N : Set (Formalism.L2.Col.Sp E n)) = ⊤ → GlobalTheory.ThetaMove.Full N := by
  intro E _ _ n N hN x
  obtain ⟨d, hd, hdx⟩ := exists_smul_mem N (x := x) (by rw [hN]; trivial)
  obtain ⟨m, hm, c, hc⟩ := exists_nat_dvd d hd
  refine ⟨m, hm, ?_⟩
  rw [hc, mul_comm, mul_smul]
  exact N.smul_mem _ hdx

end GlobalTheory.FullLatticeOfSpan
end

