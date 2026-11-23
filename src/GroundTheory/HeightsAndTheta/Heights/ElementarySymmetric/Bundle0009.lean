module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0060
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0074
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0062
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0079
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0024
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0099
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0028
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0087
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0066
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteMapOpen
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCriticalImageNull
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0090
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0077
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.HomogeneousComponentMulForm
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0028
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationExists
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PExtension
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepTwoPiece
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0038
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0041
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0040
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.FubiniStudy
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
public import GroundTheory.HeightsAndTheta.Heights.FubiniStudyCharts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0002

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.InterSumEventuallyEqInterNum
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

section Symmetry

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem tensorSub_eq_foldl_map {n : ℕ} (L : Fin n → SubSystem S x Ω) (T : Finset (Fin n)) :
    tensorSub L T = (((List.finRange n).filter (· ∈ T)).map L).foldl
      (fun F Q => F.twist Q) (twistSys S x 0) := by
  unfold tensorSub
  rw [List.foldl_map]

theorem tensorSub_comp_perm {n : ℕ} (L : Fin n → SubSystem S x Ω) (σ : Equiv.Perm (Fin n))
    (T : Finset (Fin n)) :
    tensorSub (fun i => L (σ i)) T = tensorSub L (T.map σ.toEmbedding) := by
  rw [tensorSub_eq_foldl_map, tensorSub_eq_foldl_map]
  have hp : (((List.finRange n).filter (· ∈ T)).map σ).Perm
      ((List.finRange n).filter (· ∈ T.map σ.toEmbedding)) := by
    rw [List.perm_ext_iff_of_nodup (((List.nodup_finRange n).filter _).map σ.injective)
      ((List.nodup_finRange n).filter _)]
    intro a
    simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq,
      Finset.mem_map_equiv]
    constructor
    · rintro ⟨b, hb, rfl⟩
      simpa using hb
    · intro ha
      exact ⟨σ.symm a, ha, by simp⟩
  have hfun : (fun i => L (σ i)) = L ∘ σ := rfl
  rw [hfun, ← List.map_map]
  exact (hp.map L).foldl_eq' (fun F _ P _ Q => by
    rw [SubSystem.twist_assoc, SubSystem.twist_comm F, ← SubSystem.twist_assoc]) _

theorem interSum_comp_perm (pp : Ideal (Poly S N)) {n : ℕ} (L : Fin n → SubSystem S x Ω)
    (σ : Equiv.Perm (Fin n)) (c : ℕ) :
    interSum pp (fun i => L (σ i)) c = interSum pp L c := by
  unfold interSum
  refine Fintype.sum_equiv (Equiv.finsetCongr σ) _ _ fun T => ?_
  rw [Equiv.finsetCongr_apply, Finset.card_map, tensorSub_comp_perm]

theorem interNum_comp_perm (pp : Ideal (Poly S N)) {n : ℕ} (L : Fin n → SubSystem S x Ω)
    (σ : Equiv.Perm (Fin n)) :
    interNum pp (fun i => L (σ i)) = interNum pp L := by
  unfold interNum
  congr 1
  funext c
  exact interSum_comp_perm pp L σ c

theorem interSum_eventually_eq_interNum (pp : Ideal (Poly S N)) {n : ℕ} (L : Fin n → SubSystem S x Ω)
    {m : ℤ} (h : ∀ᶠ c : ℕ in atTop, interSum pp L c = m) :
    ∀ᶠ c : ℕ in atTop, interSum pp L c = interNum pp L := by
  have ht : Tendsto (interSum pp L) atTop (nhds m) :=
    tendsto_const_nhds.congr' (h.mono fun _ hc => hc.symm)
  have hm : interNum pp L = m := ht.limUnder_eq
  rw [hm]
  exact h

end Symmetry

theorem GenericPointSectionInput.proof (hE : InterNumEventual.Statement.{u, w})
    (hA : InterNumAdditive.Statement.{u, w}) (hC : InterNumCut.Statement.{u, w})
    (hP : InterNumPointDeg.Statement.{u, w}) : GenericPointSectionInput.Statement.{u, w} := by
  intro k _ Ω _ _ N x
  refine ⟨fun n pp L hW => ?_, fun n pp L σ _ => ?_, fun n pp L i L' L'' hW => ?_,
    fun n pp L Lc s hW hs hne => ?_, fun pp hW => ?_⟩
  · obtain ⟨m, hm⟩ := hE k Ω N x n pp L hW
    exact interSum_eventually_eq_interNum pp _ hm
  · exact interNum_comp_perm pp (fun i => (L i).toSubSystem) σ
  · exact hA k Ω N x n pp L i L' L'' hW
  · exact hC k Ω N x n pp L Lc s hW hs hne
  · exact hP k Ω N x pp hW

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PBranchChartIntX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Swarm

theorem BranchChartInt.proof : GroundTheory.Heights₂.Heights.BranchChartInt.Statement :=
  GroundTheory.Heights₂.Heights.BranchChartInt.proof
    (GroundTheory.Heights₂.Heights.HolomorphicFibreSumInt.proof GroundTheory.Heights₂.Heights.WeightedAreaFormula.proof)
    (GroundTheory.Heights₂.Heights.BranchSheetAE.proof
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.RankDeficientFibreInfinite.proof
      GroundTheory.Heights₂.Heights.ComplexSets.FibreBound.proof
      (GroundTheory.Heights₂.Heights.DiscriminantSheetCover.proof
        (GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.proof
          GroundTheory.Heights₂.Heights.ComplexSets.PrimitiveElementFibres.proof)))
    GroundTheory.Heights₂.Heights.ComplexSets.FibreBound.proof

end GroundTheory.Heights₂.Heights.Swarm
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PIntegralIndep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

theorem IntegralIndep.closed : IntegralIndep.Statement :=
  IntegralIndep.proof
    (PosPartIndep.proof
      (SheetOnlyNull.proof IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.proof
        IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.proof)
      PosPartLocal.proof PosPartSplit.proof)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSnapperQuotFiltX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace SnapperQuotFilt

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

def pieceIso (N₀ N₁ : FinGradedSub (S := S) (x := x) E) {g : E} {e : ℤ} {pp : Ideal (Poly S N)}
    (Q : LineBundle S x) (c : ℤ) (hpp : pp.IsPrime) (hg : g ∈ N₁.piece e)
    (hN : ∀ c, N₁.piece c = N₀.piece c ⊔ Submodule.span S
      {z | ∃ (f : Poly S N) (d : ℕ), f.IsHomogeneous d ∧ e + d = c ∧ z = aeval x f • g})
    (hiff : ∀ (f : Poly S N) (d : ℕ), f.IsHomogeneous d → (f ∈ pp ↔ aeval x f • g ∈ N₀.piece (e + d))) :
    QuotIso ((N₁.tildeSys 0).twist (Q.twist (twistSys S x c))) ((N₀.tildeSys 0).twist (Q.twist (twistSys S x c)))
      (Q.twist (twistSys S x (c - e))) ((Q.twist (twistSys S x (c - e))).twist (idealSys x pp)) where
  equiv I := (LinearEquiv.ofBijective (StepTwo.Piece.gBar N₀ N₁ Q c hg hiff I)
    (StepTwo.Piece.gBar_bijective N₀ N₁ Q c hpp hg hN hiff I)).symm
  comm I J h y := by
    apply (LinearEquiv.ofBijective _ (StepTwo.Piece.gBar_bijective N₀ N₁ Q c hpp hg hN hiff J)).injective
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.ofBijective_apply, StepTwo.Piece.gBar_comm]
    congr 1
    exact ((LinearEquiv.ofBijective _ (StepTwo.Piece.gBar_bijective N₀ N₁ Q c hpp hg hN hiff I)).apply_symm_apply
      y).symm

end SnapperQuotFilt


open SnapperQuotFilt in
theorem SnapperQuotFilt.proof : SnapperQuotFilt.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x E _ _ _ _ F₁ F₂ hfg hle J hJ hxJ hJF
  classical
  have hfg₂ : ∀ I, (F₂.sub I).FG := fg_of_le F₁ F₂ hfg hle
  obtain ⟨M₁, -, hM₁⟩ := Extension.proof k Ω N x E F₁ hfg
  obtain ⟨M₀, -, hM₀⟩ := Extension.proof k Ω N x E F₂ hfg₂
  obtain ⟨H, hHJ, hHspan, hHhom⟩ := IdealTwistFamily.exists_finset_forms J hJ
  set hs : Fin H.card → Poly k N := fun l => (H.equivFin.symm l : Poly k N) with hs_def
  have hrange : Set.range hs = ↑H := by
    ext f
    constructor
    · rintro ⟨l, rfl⟩
      exact (H.equivFin.symm l).2
    · intro hf
      exact ⟨H.equivFin ⟨f, hf⟩, by simp [hs_def]⟩
  have hhom : ∀ l, (hs l).IsHomogeneous (hs l).totalDegree := fun l => hHhom _ (H.equivFin.symm l).2
  have hsJ : ∀ l, hs l ∈ J := fun l => hHJ (H.equivFin.symm l).2
  set A := gsup M₁ M₀ with hA_def
  set B := gsup M₀ (gmul A hs fun l => (hs l).totalDegree) with hB_def
  have hA : ∀ I, A.tilde 0 I = F₁.sub I := fun I => by
    rw [hA_def, tilde_gsup, hM₁, hM₀]
    exact sup_eq_left.mpr (hle I)
  have hB : ∀ I, B.tilde 0 I = F₂.sub I := fun I => by
    rw [hB_def, tilde_gsup, hM₀]
    exact sup_eq_left.mpr ((tilde_gmul_le A hs _ hhom hsJ F₁.toSubSystem (fun I => (hA I).le) I).trans (hJF I))
  have hBA : ∀ c, B.piece c ≤ A.piece c := fun c => by
    refine sup_le le_sup_right (Submodule.span_le.mpr ?_)
    rintro _ ⟨l, b, m, hm, hb, rfl⟩
    have := A.smul_mem _ b (hs l) m (hhom l) hm
    rwa [hb] at this
  have hkill : ∀ (f : Poly k N) (e : ℕ), f ∈ J → f.IsHomogeneous e → ∀ (a : ℤ), ∀ z ∈ A.piece a,
      aeval x f • z ∈ B.piece (a + e) := fun f e hf hfe a z hz =>
    Submodule.mem_sup_right (smul_mem_gmul A hs _ hhom (by rw [hrange, hHspan]) hf hfe hz)
  obtain ⟨n, Nf, g, deg, pr, h0, hlast, hk⟩ :=
    StepTwo.Filt.proof PrimeFiltration.Exists.proof k Ω N x E A B hBA J hkill
  have hstep : ∀ (j : Fin n) (c : ℤ), (Nf j.castSucc).piece c ≤ (Nf j.succ).piece c := fun j c => by
    rw [(hk j).2.2.2.2.2.1 c]
    exact le_sup_left
  have hmono : ∀ (i j : ℕ) (hij : i ≤ j) (hj : j ≤ n) (c : ℤ),
      (Nf ⟨i, by omega⟩).piece c ≤ (Nf ⟨j, by omega⟩).piece c := by
    intro i j hij hj c
    induction j with
    | zero =>
      obtain rfl : i = 0 := by omega
      exact le_rfl
    | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with h | h
      · subst h
        exact le_rfl
      · exact (ih (by omega) (by omega)).trans (hstep ⟨j, by omega⟩ c)
  have hNf : ∀ m (hm : m ≤ n), Nf ⟨min m n, by omega⟩ = Nf ⟨m, by omega⟩ := fun m hm =>
    congrArg Nf (Fin.ext (Nat.min_eq_left hm))
  set G : ℕ → SubFamily k x E := fun m => tildeFam (Nf ⟨min m n, by omega⟩) with hG_def
  have hGle : ∀ m I, (G m).sub I ≤ F₁.sub I := fun m I => by
    rw [← hA, ← hlast]
    exact tilde_mono (hmono _ n (by omega) le_rfl) 0 I
  refine ⟨n, G, pr, fun m => -deg m, fun m I => fg_of_le F₁ (G m) hfg (hGle m) I, ?_, ?_, ?_, ?_, ?_⟩
  · refine SubSystem.ext_sub fun I => ?_
    change (Nf ⟨min 0 n, _⟩).tilde 0 I = F₂.sub I
    rw [hNf 0 (Nat.zero_le n), Fin.mk_zero, h0, hB]
  · refine SubSystem.ext_sub fun I => ?_
    change (Nf ⟨min n n, _⟩).tilde 0 I = F₁.sub I
    rw [hNf n le_rfl]
    change (Nf (Fin.last n)).tilde 0 I = F₁.sub I
    rw [hlast, hA]
  · intro m hm I
    change (Nf ⟨min m n, _⟩).tilde 0 I ≤ (Nf ⟨min (m + 1) n, _⟩).tilde 0 I
    rw [hNf m hm.le, hNf (m + 1) hm]
    exact tilde_mono (hstep ⟨m, hm⟩) 0 I
  · intro m
    obtain ⟨hp, hh, -, hJf, -⟩ := hk m
    exact ⟨hp, hh, le_of_forms hJ hJf⟩
  · intro m t L n' c
    obtain ⟨hp, -, -, -, hg, hN, hiff⟩ := hk m
    dsimp only
    have e1 : (G (m + 1)).toSubSystem = (Nf m.succ).tildeSys 0 := by
      change (Nf ⟨min (m + 1) n, _⟩).tildeSys 0 = _
      rw [hNf _ m.2]
      rfl
    have e2 : (G m).toSubSystem = (Nf m.castSucc).tildeSys 0 := by
      change (Nf ⟨min m n, _⟩).tildeSys 0 = _
      rw [hNf _ m.2.le]
      rfl
    have hs1 : ∀ T : SubSystem k x E, (T.twistPows t (fun j => (L j).toSubSystem) n').twist (twistSys k x c) =
        T.twist ((powsBundle t L n').toSubSystem.twist (twistSys k x c)) := fun T => by
      rw [twistPows_eq, twist_twist]
    have ht1 : ((twistSys k x (-deg m)).twistPows t (fun j => (L j).toSubSystem) n').twist (twistSys k x c) =
        (powsBundle t L n').toSubSystem.twist (twistSys k x (c - deg m)) := by
      rw [twistPows_eq]
      refine SubSystem.ext_sub fun I => ?_
      simp only [SubSystem.twist_sub_eq_mul_of_line]
      rw [sub_eq_add_neg, ← twistSys_sub_mul]
      ring
    have ht2 : (((twistSys k x (-deg m)).twist (idealSys x (pr m))).twistPows t (fun j => (L j).toSubSystem)
        n').twist (twistSys k x c) =
        ((powsBundle t L n').toSubSystem.twist (twistSys k x (c - deg m))).twist (idealSys x (pr m)) := by
      rw [twistPows_eq]
      refine SubSystem.ext_sub fun I => ?_
      simp only [SubSystem.twist_sub_eq_mul_of_line]
      rw [sub_eq_add_neg, ← twistSys_sub_mul]
      ring
    rw [e1, e2, hs1, hs1, ht1, ht2]
    exact ⟨pieceIso (Nf m.castSucc) (Nf m.succ) (powsBundle t L n') c hp hg hN hiff⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSubFamilyTwistX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

section

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]


omit [Module S E] [IsScalarTower S Ω E] in
theorem SubSystem.twist_sub_fg (F : SubSystem S x E) (Q : SubSystem S x Ω) (I : Chart x)
    (hF : (F.sub I).FG) (hQ : (Q.sub I).FG) : ((F.twist Q).sub I).FG := by
  obtain ⟨sF, hsF⟩ := hF
  obtain ⟨sQ, hsQ⟩ := hQ
  classical
  refine ⟨Finset.image₂ (fun q y => q • y) sQ sF, ?_⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    intro z hz
    rw [Finset.coe_image₂] at hz
    obtain ⟨q, hq, y, hy, rfl⟩ := hz
    exact Submodule.subset_span ⟨q, hsQ ▸ Submodule.subset_span hq, y, hsF ▸ Submodule.subset_span hy, rfl⟩
  · change Submodule.span _ _ ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨q, hq, y, hy, rfl⟩
    rw [← hsQ] at hq
    rw [← hsF] at hy
    refine Submodule.span_induction (p := fun q _ => q • y ∈
      Submodule.span (chartRing S x I) ((Finset.image₂ (fun q y => q • y) sQ sF : Finset E) : Set E)) ?_ ?_ ?_ ?_ hq
    · intro q hq
      refine Submodule.span_induction (p := fun y _ => q • y ∈
        Submodule.span (chartRing S x I) ((Finset.image₂ (fun q y => q • y) sQ sF : Finset E) : Set E)) ?_ ?_ ?_ ?_ hy
      · intro y hy
        exact Submodule.subset_span (by rw [Finset.coe_image₂]; exact ⟨q, hq, y, hy, rfl⟩)
      · rw [smul_zero]; exact Submodule.zero_mem _
      · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
      · intro a z _ hz
        rw [Subalgebra.smul_def, smul_comm]
        exact Submodule.smul_mem _ a hz
    · rw [zero_smul]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [add_smul]; exact Submodule.add_mem _ ha hb
    · intro a q _ hq
      rw [smul_assoc]
      exact Submodule.smul_mem _ a hq

end

theorem SubFamilyTwist.proof : SubFamilyTwist.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ F Q hF
  exact ⟨F.twistFam Q.toSubFamily, rfl, fun I =>
    SubSystem.twist_sub_fg F.toSubSystem Q.toSubSystem I (hF I) (Q.fg I)⟩

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PVeryAmpleZTwistX
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

universe u v w

theorem VeryAmpleZTwist.proof_closed : VeryAmpleZTwist.Statement.{u, v, w} :=
  VeryAmpleZTwist.proof VeryAmpleZFamily.proof

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StCutRestrLenExact
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

def CutRestrLenExact.Statement : Prop :=
  ∀ (k : Type u) [Field k] (Ω : Type w) [Field Ω] [Algebra k Ω] (N : ℕ) (x : Fin (N + 1) → Ω)
    (e : ℕ) (pp : Ideal (Poly k N)) (Lc : LineBundle k x) (s : Ω),
      IsSubvar x pp e → s ∈ Lc.secs → (∃ I, s ∉ (Lc.twist (idealSys x pp)).sub I) →
      ∀ Q : LineBundle k x, ∀ᶠ c : ℕ in atTop,
        restrLen pp ((Q.toSubSystem.twist Lc.toSubSystem).twist (twistSys k x (c : ℤ))) -
            restrLen pp (Q.toSubSystem.twist (twistSys k x (c : ℤ))) =
          restrLen (pp ⊔ zeroIdeal Lc.toSubSystem s)
            ((Q.toSubSystem.twist Lc.toSubSystem).twist (twistSys k x (c : ℤ)))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StSmallGenHeightsNonneg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def SmallGenHeightsNonneg.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (A : HermLine ι)
    (II : IntersectionSystem) (q : ℕ) (w : Fin q → MRing ι),
    IsIntersectionSystem II → IsSmoothHerm A → (∀ k, 0 ≤ A.a k) →
    (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (w j) fun k ↦ (A.a k).toNat) →
    (∀ Q : Ideal (MRing ι), IsMultiProjPrime Q → P ≤ Q → ∃ j, w j ∉ Q) →
    (∀ j, ∀ z ∈ mcPts P, ‖eval z (map (Int.castRingHom ℂ) (w j))‖ ≤ A.h z) →
    HeightsNonneg II P A

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

