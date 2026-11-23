module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0288
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0089
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0371
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0217
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RedBasicsPf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagFrameVectorMemCommonSubspace
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EmbeddedDatumOfTermDefiniteSpace
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0293
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0311
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermDeterminedByFrameClassAndIsometry
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0373
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0312
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0308
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalLatticeStabilisersCommensurableAlmostEveryw
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Unfold.LocStab

theorem finrank_Vp_eq (D : D7) (p : PlF D) :
    Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  have := D.R.two_le_m; obtain ⟨t, ht⟩ := D.R.m_even
  unfold Ranks.rS Ranks.r; omega

theorem relIndex_comap_subtype {G : Type*} [Group G] (U X Y : Subgroup G) (hY : Y ≤ U) :
    (X.comap U.subtype).relIndex (Y.comap U.subtype) = X.relIndex Y := by
  rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq, Subgroup.range_subtype, inf_of_le_right hY]

theorem stabilizer_eq_comap {G α : Type*} [Group G] (U : Subgroup G) [MulAction U α] (S : Subgroup G) (d : α)
    (h : ∀ g : U, g.1 ∈ S ↔ g • d = d) : MulAction.stabilizer U d = S.comap U.subtype := by
  ext g
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_comap, Subgroup.coe_subtype, h g]

theorem comap_subtype_inf {G : Type*} [Group G] (U A : Subgroup G) :
    (U ⊓ A).comap U.subtype = A.comap U.subtype := by
  ext g; simp

end GlobalTheory.Unfold.LocStab

namespace GlobalTheory.Unfold.LocStab


set_option maxHeartbeats 1000000 in
theorem local_stabilisers : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ [∀ p, MulAction ↥(FP p).UW0 (LocNG.Datum (FP p))], (∀ p (g : ↥(FP p).UW0) (d d' : LocNG.Datum (FP p)), LocNG.Datum.Moves g.1 d d' ↔ g • d = d') → (∀ p (d : LocNG.Datum (FP p)) (g : ↥(FP p).UW0), g.1 ∈ LocNG.Datum.Stab d ↔ g • d = d) → ∀ (Λ₀ : LV D) (d0 : Dat Z FP), LocOver Λ₀ d0 → (∀ p, (MulAction.stabilizer ↥(FP p).UW0 (d0 p)).relIndex ((LocNG.Aut (lattice₂ D Z.M p Λ₀)).comap (FP p).UW0.subtype) ≠ 0 ∧ ((LocNG.Aut (lattice₂ D Z.M p Λ₀)).comap (FP p).UW0.subtype).relIndex (MulAction.stabilizer ↥(FP p).UW0 (d0 p)) ≠ 0) ∧ {p | (LocNG.Aut (lattice₂ D Z.M p Λ₀)).comap (FP p).UW0.subtype ≠ MulAction.stabilizer ↥(FP p).UW0 (d0 p)}.Finite ∧ ∀ d : Dat Z FP, (∀ p, ∃ τ, LocNG.IsTermOver (FP p) (d p) τ) → ∀ p, (MulAction.stabilizer ↥(FP p).UW0 (d0 p)).relIndex (MulAction.stabilizer ↥(FP p).UW0 (d p)) ≠ 0 ∧ (MulAction.stabilizer ↥(FP p).UW0 (d p)).relIndex (MulAction.stabilizer ↥(FP p).UW0 (d0 p)) ≠ 0 ∧ GlobalTheory.HL.invVol (MulAction.stabilizer ↥(FP p).UW0 (d0 p)) (MulAction.stabilizer ↥(FP p).UW0 (d p)) = LocNG.Datum.wt (d0 p) (d p) := by
  intro D X Y u u' F F' w hw hG Z FP hB hRel _ hMv hSt Λ₀ d0 hLO
  have hOK : ∀ p, (Z.M p).OK := fun p => (Z.agree p).1
  have hstab : ∀ p (d : LocNG.Datum (FP p)),
      MulAction.stabilizer ↥(FP p).UW0 d = (LocNG.Datum.Stab d).comap (FP p).UW0.subtype :=
    fun p d => stabilizer_eq_comap _ _ d (fun g => hSt p d g)
  have hle : ∀ p (d : LocNG.Datum (FP p)), LocNG.Datum.Stab d ≤ (FP p).UW0 :=
    fun p d => Subgroup.closure_le _ |>.2 fun g hg => hg.1
  choose τ0 hτ0 hτ0L using hLO.2
  have hc := fun p => _root_.GlobalTheory.HL.LocComm.stab_commensurable (Z.M p) (hOK p) (locH Z p) D.R.rS D.R.k (FP p) (finrank_Vp_eq D p)
    (hRel p) (d0 p) (τ0 p) (hτ0 p)
  have hA : ∀ p, (LocNG.Aut (lattice₂ D Z.M p Λ₀)).comap (FP p).UW0.subtype =
      ((FP p).UW0 ⊓ LocNG.Aut (τ0 p).abelian₂).comap (FP p).UW0.subtype := by
    intro p; rw [comap_subtype_inf, hτ0L p]
  refine ⟨fun p => ?_, ?_, fun d hd p => ?_⟩
  · rw [hA p, hstab p]
    refine ⟨?_, ?_⟩
    · rw [relIndex_comap_subtype _ _ _ inf_le_left, Subgroup.relIndex_eq_one.2 (hc p).1]
      exact one_ne_zero
    · rw [relIndex_comap_subtype _ _ _ (hle p (d0 p))]
      exact (hc p).2.1
  · have hAt : ∀ p, GlobalTheory.LocOver.AtBase Z p F F' (Tu D u) (Tu D u') (FP p) := fun p => by
      obtain ⟨h1, h2, h3, h4⟩ := hB p
      exact ⟨h1, h2, h3, h4⟩
    refine (_root_.GlobalTheory.PrimeAlmostAll.primeTo_finite D Z u u' F F' hG FP hAt).subset fun p hp hpr => hp ?_
    have h2 := _root_.GlobalTheory.HL.StabLat.stab_le_aut (Z.M p) (hOK p) (locH Z p) D.R.rS D.R.k (FP p) (finrank_Vp_eq D p)
      (hRel p) hpr (d0 p) (τ0 p) (hτ0 p)
    rw [hA p, hstab p]
    exact congrArg _ (le_antisymm (hc p).1 (le_inf (hle p (d0 p)) h2))
  · obtain ⟨τ, hτ⟩ := hd p
    have h3 := (hc p).2.2
    have hτc := _root_.GlobalTheory.HL.LocComm.stab_commensurable (Z.M p) (hOK p) (locH Z p) D.R.rS D.R.k (FP p) (finrank_Vp_eq D p)
      (hRel p) (d p) τ hτ
    rw [hstab p, hstab p, relIndex_comap_subtype _ _ _ (hle p (d p)),
      relIndex_comap_subtype _ _ _ (hle p (d0 p))]
    refine ⟨h3 (d p) τ hτ, hτc.2.2 (d0 p) (τ0 p) (hτ0 p), ?_⟩
    rw [GlobalTheory.HL.invVol, relIndex_comap_subtype _ _ _ (hle p (d p)),
      relIndex_comap_subtype _ _ _ (hle p (d0 p)), LocNG.Datum.wt, LocNG.volRel, one_div_div]

end GlobalTheory.Unfold.LocStab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ReducedMatrixOfActsAsDegreeOnePrimeFrame
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.ArithmeticCylinders Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.principalLevelFrame Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField ReciprocityTheory.Aut Formalism.AUTREP GlobalTheory.Mem.SRe GlobalTheory.LabPin
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LabPin.instCM
open scoped TensorProduct Matrix

namespace GlobalTheory.RowLev

open Formalism.L2.SG.Pf.RowDictPf Formalism.L2.SG.Pf.RedBasicsPf PIW.AdelClassFin IsDedekindDomain

theorem redMat0_of_actsAs : ∀ (I : AutInst) (N p : ℕ) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E)) (fr : GlobalTheory.RowLev.PlFrame I N p w) (x : I.Gf), x ∈ I.Kset → ∀ M : Matrix (Fin N) (Fin N) (ZMod p), fr.ActsAs x M → Formalism.L2.SG.Pf.RowDictPf.RedMat0 I w p x M := by
  intro I N p w fr x hx M hM
  have hp : p.Prime := fr.prime
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p :=
    (Nat.card_congr fr.residueEquiv.toEquiv).trans (Nat.card_zmod p)
  have h1 : ∀ u ∈ lamAf (F := I.F) (wLat0 I w), u ∈ extId I w.asIdeal • I.Lf := by
    refine fun u hu => lamAf_w_le I w _ (fun a ha y hy => ?_) hu
    rw [DictLat.iv_smulE]
    exact Submodule.smul_mem_smul (r := Inhab.psi I.F I.E a) (Ideal.subset_span ⟨a, ha, rfl⟩) (DictLat.iv_mem I hy)
  have h2 : ∀ u ∈ extId I w.asIdeal • I.Lf, u ∈ lamAf (F := I.F) (wLat0 I w) := by
    intro u hu
    refine Submodule.smul_induction_on hu (fun a ha v hv => ?_) (fun _ _ h h' => add_mem h h')
    refine Submodule.span_induction (p := fun a _ => a • v ∈ lamAf (F := I.F) (wLat0 I w)) ?_ ?_ ?_ ?_ ha
    · rintro z ⟨b, hb, e⟩
      show (z : I.E ⊗[I.F] Af I.F) • v ∈ _
      rw [e]
      exact smul_mem I w hb hv
    · simp
    · intro a b _ _ ha hb
      rw [add_smul]; exact add_mem ha hb
    · intro s a _ ha
      rw [smul_eq_mul, mul_smul]
      exact Submodule.smul_mem _ s ha
  have hz : ∀ u : I.Lf, fr.c u = 0 ↔ (u : Fin I.n → I.E ⊗[I.F] Af I.F) ∈ lamAf (F := I.F) (wLat0 I w) :=
    fun u => (fr.c_ker u).trans ⟨h2 _, h1 _⟩
  choose y hy using fun i : Fin N => fr.c_surj (Pi.single i 1)
  choose b hbL hb using fun i => dense I w hp hcard (y i).2
  let B : Fin N → I.Lf := fun i => ⟨iv I (b i), DictLat.iv_mem I (hbL i)⟩
  have hB : ∀ i, fr.c (B i) = Pi.single i 1 := by
    intro i
    have e : fr.c (y i - B i) = 0 := (hz _).2 (hb i)
    rw [map_sub, sub_eq_zero] at e
    rw [← e, hy]
  have hci : ∀ (n : ℤ) (u : I.Lf), fr.c ((n : IntAf I.F I.E) • u) = (n : ZMod p) • fr.c u := by
    intro n u; rw [map_smulₛₗ, map_intCast]
  have hcn : ∀ (n : ℕ) (u : I.Lf), fr.c ((n : IntAf I.F I.E) • u) = (n : ZMod p) • fr.c u := by
    intro n u; rw [map_smulₛₗ, map_natCast]
  refine ⟨b, ⟨hbL, fun z hz' => ?_⟩, fun i => ?_⟩
  · let Z : I.Lf := ⟨iv I z, DictLat.iv_mem I hz'⟩
    let c : Fin N → ℤ := fun j => ((fr.c Z j).val : ℤ)
    refine ⟨c, inter I w ?_⟩
    rw [iv_lin]
    have e0 : fr.c (Z - ∑ j, ((c j : ℤ) : IntAf I.F I.E) • B j) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, sub_eq_zero]
      simp only [hci, hB]
      funext k
      simp [c, Finset.sum_apply, Pi.single_apply]
    have e1 := (hz _).1 e0
    convert e1 using 1
    simp [Z, B, Submodule.coe_sum]
    rfl
  · let V : I.Lf := ⟨I.fmat x *ᵥ iv I (b i), Inhab.mulVec_mem hx (B i).2⟩
    have hV : fr.c V = M *ᵥ Pi.single i 1 := by rw [← hB i]; exact hM (B i) V.2
    have e0 : fr.c (V - ∑ j, (((M j i).val : ℕ) : IntAf I.F I.E) • B j) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, sub_eq_zero, hV]
      simp only [hcn, hB, ZMod.natCast_zmod_val]
      funext k
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_apply]
    have e1 := (hz _).1 e0
    convert e1 using 1
    rw [Submodule.coe_sub, Submodule.coe_sum]
    refine congrArg₂ (· - ·) rfl (Finset.sum_congr rfl fun j _ => ?_)
    show _ = ((((M j i).val : ℕ) : IntAf I.F I.E) : I.E ⊗[I.F] Af I.F) • iv I (b j)
    rw [SubringClass.coe_natCast]
    rfl

end GlobalTheory.RowLev
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumFrameClassWeightsLeDatumBound
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm GlobalTheory.TypeAsm.PerRow
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeAsm.PerRow

theorem sum_clsOm_le_datBd : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ → ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W), GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype → ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) (j x : ℕ) (δ : ℕ → D.host.E) (d : Submodule (𝓞 D.host.E) W × Submodule (𝓞 D.host.E) (W × W)) (N : GTu Y u → GlobalTheory.DegCnt.NF (HV D) D.R.rS) (A : Finset (GTu Y u)), A.Nonempty → (∀ t ∈ A, t ∈ relSet Y u ∧ t.lam = Λ ∧ jT t = j ∧ labT t = δ ∧ AdT t (N t) ∧ (N t).IsTerm (gS D) Λ ∧ (N t).gI (gS D) Λ = x ∧ GlobalTheory.DegAsm.datOf (F0 X u) (Ft t) W.subtype (gS D) Λ = d) → ∑ b ∈ A.image (frCls Λ), clsOm Y u Λ b ≤ GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j δ) (DbL D j δ) (NT D u) x := by
  intro D large₂ X Y u hStd W HW he Λ j x δ d N A hA hT
  obtain ⟨hK, -, -, -, hf, -, -, -, -, -, hV, hg2, -⟩ := _root_.GlobalTheory.TypeAsm.hostC D large₂ hStd
  have hgS : 1 ≤ gS D := by omega
  obtain ⟨t₀, ht₀⟩ := hA
  obtain ⟨-, -, hj0, hδ0, hAd0, hTm0, hg0, -⟩ := hT t₀ ht₀
  obtain ⟨-, -, hLDel, hLDb, -⟩ := _root_.GlobalTheory.TypeAsm.labC D large₂ X Y u hStd t₀ (N t₀) hAd0
  obtain ⟨-, hx1, -, -, hfW⟩ := _root_.GlobalTheory.DegAsm.isDat_datOf D.host.E (VS D).V W (HV D) HW W.subtype hK D.R.rS (F0 X u) (Ft t₀)
    (dI D) (N t₀) (gS D) Λ hgS he hAd0 hTm0
  obtain ⟨-, -, hDb1, hDel1, -⟩ := GlobalTheory.T.exists_star_stable_ideal_absorbing_minors D.host.E (VS D).V (HV D) hK D.R.rS (N t₀) (gS D) Λ hgS hTm0
  rw [hg0] at hx1
  rw [hLDel, hj0, hδ0] at hDel1
  rw [hLDb, hj0, hδ0] at hDb1
  let G : Set (Formalism.HermitianLatticeCounting.S6.FlagD (HV D) D.R.rS) → Formalism.HermitianLatticeCounting.S6.FlagD (HV D) D.R.rS := fun b =>
    if hb : ∃ t ∈ A, frCls Λ t = b then Ft hb.choose else F0 X u
  have hGb : ∀ b ∈ A.image (frCls Λ), ∃ t ∈ A, frCls Λ t = b ∧ G b = Ft t := by
    intro b hb
    have hb' : ∃ t ∈ A, frCls Λ t = b := Finset.mem_image.1 hb
    obtain ⟨h1, h2⟩ := hb'.choose_spec
    exact ⟨hb'.choose, h1, h2, by simp only [G, dif_pos hb']⟩
  have key := GlobalTheory.DegAsm.sum_weights_per_datum D.host.E (VS D).V W (HV D) HW W.subtype hK D.R.rS (F0 X u) (dI D)
    (gS D) j (Tu D u) x (fun l => star (δ l)) Λ d (k2Del D j δ) (DbL D j δ) (Set (Formalism.HermitianLatticeCounting.S6.FlagD (HV D) D.R.rS))
    (A.image (frCls Λ)) G hgS hx1 hDel1 hDb1 he ?_ ?_ ?_
  · have hsum : ∑ b ∈ A.image (frCls Λ), clsOm Y u Λ b =
        ∑ b ∈ A.image (frCls Λ), GlobalTheory.DegAsm.omI (F0 X u) (G b) (dI D) Λ := by
      refine Finset.sum_congr rfl fun b hb => ?_
      obtain ⟨t, ht, hbt, hG⟩ := hGb b hb
      obtain ⟨-, hlt, -⟩ := hT t ht
      rw [hG, ← hbt, clsOm_frCls hK Λ t hlt]
      unfold omT
      rw [hlt]
    rw [hsum]
    refine key.trans (le_of_eq ?_)
    rw [show Module.finrank D.host.E W = D.R.k by omega, hf]
    rfl
  · intro b hb
    obtain ⟨t, ht, -, hG⟩ := hGb b hb
    obtain ⟨-, -, hjt, hδt, hAdt, hTmt, hgt, -⟩ := hT t ht
    obtain ⟨a1, a2, a3, a4, -⟩ := _root_.GlobalTheory.TypeAsm.labC D large₂ X Y u hStd t (N t) hAdt
    refine ⟨N t, ?_, hTmt, a1.trans hjt, a2, ?_, ?_, hgt⟩
    · rw [hG]; exact hAdt
    · rw [a3, hjt, hδt]
    · rw [a4, hjt, hδt]
  · intro b hb
    obtain ⟨t, ht, -, hG⟩ := hGb b hb
    obtain ⟨-, -, hjt, hδt, hAdt, -, -, hdt⟩ := hT t ht
    obtain ⟨-, -, -, -, a5⟩ := _root_.GlobalTheory.TypeAsm.labC D large₂ X Y u hStd t (N t) hAdt
    refine ⟨?_, ?_⟩
    · rw [hG, ← hjt, a5, hδt]
    · rw [hG]; exact hdt
  · intro b hb b' hb' hE
    obtain ⟨t, -, hbt, hG⟩ := hGb b hb
    obtain ⟨t', -, hbt', hG'⟩ := hGb b' hb'
    rw [hG, hG'] at hE
    rw [← hbt, ← hbt']
    exact (frCls_eq_iff hK Λ t t').2 hE

end GlobalTheory.TypeAsm.PerRow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPairsDefiniteIsometryLeFrameClasses
section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc GlobalTheory.TypeAsm GlobalTheory.TypeAsm.PerRow
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeAsm.PerRow

theorem sum_pairs_le_classes_pf : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), Std D large₂ →
    ∀ (W : Submodule D.host.E (VS D).V) (HW : Formalism.HermitianLatticeCounting.S6.HermSpace D.host.E W),
    GlobalTheory.DegAsm.IsEmb (F0 X u) HW W.subtype → ∀ (Λ : Submodule (𝓞 D.host.E) (VS D).V) (h : GTu Y u → (W ≃ₗ[D.host.E] W)),
    (∀ t ∈ relSet Y u, GlobalTheory.DegAsm.IsH (F0 X u) (Ft t) W.subtype t.lin (h t)) → ∀ (Sf : Finset (GTu Y u × GTu Y u)),
    (∀ p ∈ Sf, p ∈ (Y.tO u u).allPairs (relSet Y u) ∧ p.1.lam = Λ) →
    (∀ p ∈ Sf, ∀ q ∈ Sf, h p.1 * (h p.2)⁻¹ = h q.1 * (h q.2)⁻¹) →
    ∑ p ∈ Sf, wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2) ≤
      (∑ b ∈ Sf.image (fun p => frCls Λ p.1), clsOm Y u Λ b) * ∑ b ∈ Sf.image (fun p => frCls Λ p.2), clsOm Y u Λ b := by
  intro D large₂ X Y u hS W HW he Λ h hh Sf hSf hη
  obtain ⟨hK, -⟩ := _root_.GlobalTheory.TypeAsm.hostC D large₂ hS
  have hlam : ∀ p ∈ Sf, p.2.lam = Λ ∧ p.2.lam' = p.1.lam' := by
    intro p hp
    obtain ⟨hl, hl', -⟩ := _root_.GlobalTheory.TypeAsm.CompatPf.compatC D X Y u p ⟨trivial, trivial, (hSf p hp).1.2.2⟩
    exact ⟨hl.symm.trans (hSf p hp).2, hl'.symm⟩
  have hL : ∑ p ∈ Sf, wRow D (X.Fu u) p.1.lam' * (omT p.1 * omT p.2) =
      ∑ p ∈ Sf, wRow D (X.Fu u) p.1.lam' * (clsOm Y u Λ (frCls Λ p.1) * clsOm Y u Λ (frCls Λ p.2)) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [clsOm_frCls hK Λ p.1 (hSf p hp).2, clsOm_frCls hK Λ p.2 (hlam p hp).1]
  rw [hL]
  generalize hT1 : Sf.image (fun p => frCls Λ p.1) = T₁
  generalize hT2 : Sf.image (fun p => frCls Λ p.2) = T₂
  refine GlobalTheory.sum_pairs_weight_mul_class_le_mul_sum (GTu Y u) _ Sf (frCls Λ)
    (fun t => wRow D (X.Fu u) t.lam') (clsOm Y u Λ) T₁ T₂ ?_ (clsOm_nonneg Y u Λ hK) ?_ ?_ ?_
  · intro t
    show 0 ≤ wRow D (X.Fu u) t.lam'
    unfold wRow; positivity
  · intro p hp
    subst hT1 hT2
    exact ⟨Finset.mem_image.2 ⟨p, hp, rfl⟩, Finset.mem_image.2 ⟨p, hp, rfl⟩⟩
  · intro p hp q hq h1 hc
    have hrel2 : p.2 ∈ relSet Y u := (hSf p hp).1.2.1
    have hrelq : q.2 ∈ relSet Y u := (hSf q hq).1.2.1
    have hhe : h p.2 = h q.2 := by
      have e := hη p hp q hq
      rw [h1] at e
      have e2 := congrArg (fun g => (h q.1)⁻¹ * g) e
      simp only [inv_mul_cancel_left] at e2
      exact inv_injective e2
    have hfe := (frCls_eq_iff hK Λ p.2 q.2).1 hc
    have hl : p.2.lam = q.2.lam := ((hlam p hp).1).trans ((hlam q hq).1).symm
    obtain ⟨N, hN, -⟩ := _root_.GlobalTheory.TypeAsm.nfExC_holds D large₂ X Y u hS p.2 hrel2
    have hfe' : GlobalTheory.DegAsm.FrEqv (F0 X u) p.2.lam (Ft p.2) (Ft q.2) := by rw [(hlam p hp).1]; exact hfe
    have := _root_.GlobalTheory.TypeAsm.InjProof.injC D large₂ X Y u hS W HW he p.2 q.2 ⟨N, hN⟩ hl hfe' (h p.2) (hh p.2 hrel2)
      (by rw [hhe]; exact hh q.2 hrelq)
    exact Prod.ext h1 this
  · intro b
    have gen : ∀ s : Finset (GTu Y u), (∀ t ∈ s, t.lam = Λ ∧ frCls Λ t = b) →
        ∑ a ∈ s, wRow D (X.Fu u) a.lam' ≤ 1 := by
      intro s hmem
      rcases s.eq_empty_or_nonempty with he0 | ⟨t₀, ht₀⟩
      · rw [he0, Finset.sum_empty]; exact zero_le_one
      obtain ⟨hl0, hb0⟩ := hmem t₀ ht₀
      have hrel : ∀ t ∈ s, t₀.lam = t.lam ∧ GlobalTheory.DegAsm.FrEqv (F0 X u) t₀.lam (Ft t₀) (Ft t) := by
        intro t ht
        obtain ⟨hl, hb⟩ := hmem t ht
        refine ⟨hl0.trans hl.symm, ?_⟩
        rw [hl0]
        exact (frCls_eq_iff hK Λ t₀ t).1 (hb0.trans hb.symm)
      have hw : ∀ t ∈ s, wRow D (X.Fu u) t.lam' = wRow D (X.Fu u) t₀.lam' := by
        intro t ht
        obtain ⟨hl, hf⟩ := hrel t ht
        rw [(_root_.GlobalTheory.TypeAsm.FibProof.fibC D large₂ X Y u hS t₀ t hl hf).1]
      rw [Finset.sum_congr rfl hw, Finset.sum_const, nsmul_eq_mul]
      exact _root_.GlobalTheory.TypeAsm.FibCard.fibCardC D large₂ X Y u hS t₀ s hrel
    refine gen _ fun t ht => ?_
    simp only [Finset.mem_filter, Finset.mem_image] at ht
    obtain ⟨⟨p, hp, rfl⟩, ht2⟩ := ht
    exact ⟨(hSf p hp).2, ht2⟩

end GlobalTheory.TypeAsm.PerRow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WBEqPrimeComap
section
noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.FixedConj

def adeleEquiv (D : Formalism.BasicNotions.D7) (hF : D.host.F = maximalRealSubfield D.host.E) :
    ReciprocityTheory.Aut.AL D.host.E ≃+* Formalism.IndefR.Lev.EAf D :=
  (GlobalTheory.StdFrame.tensCastR hF).symm.trans
    (Algebra.TensorProduct.comm (↥D.host.F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af ↥D.host.F) D.host.E).toRingEquiv

def primeComap {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] (ι : E ≃+* E')
    (w : HeightOneSpectrum (𝓞 E')) : HeightOneSpectrum (𝓞 E) where
  asIdeal := Ideal.comap (RingOfIntegers.mapRingEquiv ι) w.asIdeal
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    apply w.ne_bot
    have := congrArg (Ideal.map (RingOfIntegers.mapRingEquiv ι)) h
    rwa [Ideal.map_comap_of_surjective _ (RingOfIntegers.mapRingEquiv ι).surjective, Ideal.map_bot] at this

end GlobalTheory.FixedConj

end
end

