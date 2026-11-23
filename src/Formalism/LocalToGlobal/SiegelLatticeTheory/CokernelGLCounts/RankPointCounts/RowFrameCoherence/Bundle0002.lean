module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.Regroup
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RowRegroup

section Abstract

variable {ι α Q E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem normSq_tsum_eq (w : α → E) (hw : Summable fun a => ‖w a‖) :
    Summable (fun y : α × α => (inner ℂ (w y.1) (w y.2)).re) ∧
      ‖∑' a, w a‖ ^ 2 = ∑' y : α × α, (inner ℂ (w y.1) (w y.2)).re := by
  set v := ∑' a, w a with hv
  have hs : HasSum w v := hw.of_norm.hasSum
  have hb : Summable (fun y : α × α => ‖w y.1‖ * ‖w y.2‖) :=
    hw.mul_of_nonneg hw (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hsum : Summable (fun y : α × α => (inner ℂ (w y.1) (w y.2)).re) := by
    refine Summable.of_norm_bounded hb fun y => ?_
    rw [Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
  refine ⟨hsum, ?_⟩
  have h1 : HasSum (fun a => (inner ℂ v (w a)).re) (inner ℂ v v).re := by
    have h := Complex.reCLM.hasSum ((innerSL ℂ v).hasSum hs)
    simpa [innerSL_apply_apply] using h
  have h2 : ∀ a, HasSum (fun b => (inner ℂ (w a) (w b)).re) (inner ℂ (w a) v).re := by
    intro a
    have h := Complex.reCLM.hasSum ((innerSL ℂ (w a)).hasSum hs)
    simpa [innerSL_apply_apply] using h
  have h3 : ∀ a, (inner ℂ (w a) v).re = (inner ℂ v (w a)).re := fun a => by
    simpa using inner_re_symm (𝕜 := ℂ) (w a) v
  rw [hsum.tsum_prod' (fun a => (h2 a).summable), tsum_congr (fun a => (h2 a).tsum_eq), tsum_congr h3, h1.tsum_eq]
  simpa using norm_sq_eq_re_inner (𝕜 := ℂ) v

theorem regroup (vec : ι → E) (hv : Summable fun t => ‖vec t‖) (P : ι → Prop) (q : ι → Q)
    (A : Q → Set ι) (hA : ∀ c s, s ∈ A c ↔ P s ∧ q s = c) :
    (∀ c, Summable fun s : A c => ‖vec s‖) ∧
      Summable (fun c => ‖∑' s : A c, vec s‖ ^ 2) ∧
      ∑' p : ι × ι, {p : ι × ι | P p.1 ∧ P p.2 ∧ q p.1 = q p.2}.indicator
          (fun p => (inner ℂ (vec p.1) (vec p.2)).re) p =
        ∑' c, ‖∑' s : A c, vec s‖ ^ 2 := by
  set S : Set (ι × ι) := {p : ι × ι | P p.1 ∧ P p.2 ∧ q p.1 = q p.2} with hSdef
  set G : ι × ι → ℝ := fun p => (inner ℂ (vec p.1) (vec p.2)).re with hGdef
  have hG : Summable G := (normSq_tsum_eq vec hv).1
  have hF : Summable (S.indicator G) := hG.indicator S
  have hfib := hF.hasSum.tsum_fiberwise (fun p : ι × ι => q p.1)
  have hA1 : ∀ c, Summable fun s : A c => ‖vec s‖ := fun c => hv.subtype (fun s => s ∈ A c)
  have key : ∀ c, ∑' p : (fun p : ι × ι => q p.1) ⁻¹' {c}, S.indicator G p = ‖∑' s : A c, vec s‖ ^ 2 := by
    intro c
    rw [(normSq_tsum_eq (fun s : A c => vec s) (hA1 c)).2]
    have e1 : ∑' y : A c × A c, (inner ℂ (vec y.1) (vec y.2)).re = ∑' x : ↥(A c ×ˢ A c), G x := by
      rw [← (Equiv.Set.prod (A c) (A c)).tsum_eq]
      rfl
    rw [e1, tsum_subtype (A c ×ˢ A c) G, tsum_subtype ((fun p : ι × ι => q p.1) ⁻¹' {c}) (S.indicator G)]
    refine tsum_congr fun p => ?_
    have hm : p ∈ (fun p : ι × ι => q p.1) ⁻¹' {c} ∧ p ∈ S ↔ p ∈ A c ×ˢ A c := by
      simp only [Set.mem_preimage, Set.mem_singleton_iff, hSdef, Set.mem_setOf_eq, Set.mem_prod, hA]
      constructor
      · rintro ⟨h1, hp1, hp2, h12⟩
        exact ⟨⟨hp1, h1⟩, hp2, h12 ▸ h1⟩
      · rintro ⟨⟨hp1, h1⟩, hp2, h2⟩
        exact ⟨h1, hp1, hp2, h1.trans h2.symm⟩
    rw [Set.indicator_indicator, Set.indicator_apply, Set.indicator_apply]
    by_cases h : p ∈ A c ×ˢ A c
    · rw [if_pos (Set.mem_inter_iff _ _ _ |>.2 (hm.2 h)), if_pos h]
    · rw [if_neg (fun h' => h (hm.1 ((Set.mem_inter_iff _ _ _).1 h'))), if_neg h]
  refine ⟨hA1, hfib.summable.congr key, ?_⟩
  rw [← hfib.tsum_eq, tsum_congr key]

end Abstract

end Formalism.L2.SG.Pf.RowRegroup

namespace Formalism.L2.SG.Pf.RowRegroup

theorem inner_toLp_single_same {K F : Type*} [Fintype K] [DecidableEq K] [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] (k : K) (x y : F) :
    inner ℂ (WithLp.toLp 2 (Pi.single k x : K → F)) (WithLp.toLp 2 (Pi.single k y : K → F)) = inner ℂ x y := by
  rw [PiLp.inner_apply, Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ k) h

end Formalism.L2.SG.Pf.RowRegroup

namespace Formalism.L2.SG.Pf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.MassDataForm Formalism.L2.SG.Pf.RowForm MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option linter.deprecated false in
theorem rowRegroupC_of {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
    (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)
    (hAbs : Formalism.L2.SG.TermOp.AbsConvT (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u'))
    (hS : ScalTC X Y u u' κ) :
    RowRegroupC X Y u u' κ := by
  have hvec : ∀ s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'),
      (Y.tO u u').vec s = WithLp.toLp 2 (Pi.single ((⟨s.lam, s.mem⟩, ⟨s.lam', s.mem'⟩) :
        {Λ // Λ ∈ Y.what₂ u} × {Λ' // Λ' ∈ Y.what₂ u'}) (liftVec X Y u u' s)) := by
    intro s
    change WithLp.toLp 2 _ = WithLp.toLp 2 _
    congr 1
    funext k
    by_cases h : k = (⟨s.lam, s.mem⟩, ⟨s.lam', s.mem'⟩)
    · subst h
      simp [liftVec]
    · simp [h]
  have hnorm : ∀ s, ‖(Y.tO u u').vec s‖ = ‖liftVec X Y u u' s‖ := by
    intro s
    rw [hvec s, PiLp.toLp_single, PiLp.norm_single]
  have hv : Summable fun s => ‖liftVec X Y u u' s‖ := hAbs.2.1.congr hnorm
  obtain ⟨h1, h2, h3⟩ := Formalism.L2.SG.Pf.RowRegroup.regroup (liftVec X Y u u') hv
    (fun s => (Y.tO u u').G s ≠ 0 ∧ (Y.tO u u').gener s)
    (fun s => ((Y.tO u u').rowOf s, κ s.toTerm))
    (fun c => {s | (Y.tO u u').G s ≠ 0 ∧ (Y.tO u u').gener s ∧ (Y.tO u u').rowOf s = c.1 ∧ κ s.toTerm = c.2})
    (fun c s => by simp only [Set.mem_setOf_eq, Prod.ext_iff, and_assoc])
  have hset : (Y.tO u u').sc (Y.tO u u').genSet =
      {p : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') ×
        Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') |
        ((Y.tO u u').G p.1 ≠ 0 ∧ (Y.tO u u').gener p.1) ∧ ((Y.tO u u').G p.2 ≠ 0 ∧ (Y.tO u u').gener p.2) ∧
        ((Y.tO u u').rowOf p.1, κ p.1.toTerm) = ((Y.tO u u').rowOf p.2, κ p.2.toTerm)} := by
    ext ⟨s₁, s₂⟩
    simp only [Formalism.FourierDecayAlt.PB.Terms.sc, Formalism.FourierDecayAlt.PB.Terms.allPairs, Formalism.FourierDecayAlt.PB.Terms.genSet, Set.mem_setOf_eq,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨⟨hG1, hg1⟩, ⟨hG2, hg2⟩, hr⟩, h0, hsc⟩
      exact ⟨⟨hG1, hg1⟩, ⟨hG2, hg2⟩, hr, (hS s₁ s₂ hG1 hG2 hg1 hg2 hr).1 ⟨h0, hsc⟩⟩
    · rintro ⟨⟨hG1, hg1⟩, ⟨hG2, hg2⟩, hr, hk⟩
      obtain ⟨h0, hsc⟩ := (hS s₁ s₂ hG1 hG2 hg1 hg2 hr).2 hk
      exact ⟨⟨⟨hG1, hg1⟩, ⟨hG2, hg2⟩, hr⟩, h0, hsc⟩
  have hsig : SigOf (Y.tO u u') = ∑' p, ({p : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') ×
      Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') | ((Y.tO u u').G p.1 ≠ 0 ∧ (Y.tO u u').gener p.1) ∧
      ((Y.tO u u').G p.2 ≠ 0 ∧ (Y.tO u u').gener p.2) ∧
        ((Y.tO u u').rowOf p.1, κ p.1.toTerm) = ((Y.tO u u').rowOf p.2, κ p.2.toTerm)}).indicator
      (fun p => (inner ℂ (liftVec X Y u u' p.1) (liftVec X Y u u' p.2)).re) p := by
    unfold SigOf
    rw [hset]
    refine tsum_congr fun p => ?_
    refine congrFun (Set.indicator_congr fun p hp => ?_) p
    obtain ⟨-, -, hr⟩ := hp
    have hrow : (Y.tO u u').rowOf p.1 = (Y.tO u u').rowOf p.2 := congrArg Prod.fst hr
    have hposition : ((⟨p.1.lam, p.1.mem⟩, ⟨p.1.lam', p.1.mem'⟩) : {Λ // Λ ∈ Y.what₂ u} × {Λ' // Λ' ∈ Y.what₂ u'}) =
        (⟨p.2.lam, p.2.mem⟩, ⟨p.2.lam', p.2.mem'⟩) :=
      congrArg (fun r : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR => (r.1, r.2.1)) hrow
    show (inner ℂ ((Y.tO u u').vec p.1) ((Y.tO u u').vec p.2)).re =
      (inner ℂ (liftVec X Y u u' p.1) (liftVec X Y u u' p.2)).re
    rw [hvec p.1, hvec p.2, hposition, Formalism.L2.SG.Pf.RowRegroup.inner_toLp_single_same]
  exact ⟨h1, h2, hsig.trans h3⟩

end Formalism.L2.SG.Pf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.Torsor
section
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RowForm

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
  (vR : Term D u u' (X.Fu u) (Y.what₂ u) → ℝ)
  (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

def LiftIotaFreeC : Prop :=
  ∀ s₁ s₂ : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'),
    Formalism.L2.SG.DataInst.Elig s₁.toTerm → s₁.toTerm = s₂.toTerm →
      (Y.tO u u').rowOf s₁ = (Y.tO u u').rowOf s₂ → s₁ = s₂

def LiftMassC : Prop :=
  ∀ t : Term D u u' (X.Fu u) (Y.what₂ u), Formalism.L2.SG.DataInst.Elig t →
    ∑' s : {s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') // s.toTerm = t},
      Formalism.MainNotions.S.wRow D (X.Fu u') s.1.lam' = 1

def LiftRowCohC : Prop :=
  ∀ (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'))
    (t : Term D u u' (X.Fu u) (Y.what₂ u)),
    Formalism.L2.SG.DataInst.Elig s.toTerm → Formalism.L2.SG.DataInst.Elig t → Formalism.L2.SG.Corank.TermScal D s.toTerm t →
      ∃ s' : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'),
        s'.toTerm = t ∧ (Y.tO u u').rowOf s' = (Y.tO u u').rowOf s

namespace TorsorStructure

variable {X Y u u' κ}

theorem torsor_G_gener (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'))
    (h : Formalism.L2.SG.DataInst.Elig s.toTerm) : (Y.tO u u').G s ≠ 0 ∧ (Y.tO u u').gener s := by
  refine ⟨?_, h.1⟩
  unfold Formalism.L2.SG.Full.Full.tO Formalism.L2.SG.TermOp.tOf
  dsimp only
  unfold Formalism.L2.SG.TermOp.Gt
  rw [if_neg (show s.G ≠ 0 from h.2)]
  exact one_ne_zero

theorem torsor_elig {R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR} {ρ : ℕ} (s : LiftT X Y u u' κ R ρ) :
    Formalism.L2.SG.DataInst.Elig s.1.toTerm := by
  have hG := s.2.1
  unfold Formalism.L2.SG.Full.Full.tO Formalism.L2.SG.TermOp.tOf at hG
  dsimp only at hG
  unfold Formalism.L2.SG.TermOp.Gt at hG
  refine ⟨s.2.2.1, fun h0 => hG ?_⟩
  exact if_pos (show s.1.G = 0 from h0)

theorem torsor_lam {R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR} {ρ : ℕ} (s : LiftT X Y u u' κ R ρ) :
    s.1.lam = R.1.1 ∧ s.1.lam' = R.2.1.1 := by
  obtain ⟨-, -, hR, -⟩ := s.2
  have h1 : ((Y.tO u u').rowOf s.1).1.val = R.1.val := congrArg (fun r => r.1.val) hR
  have h2 : ((Y.tO u u').rowOf s.1).2.1.val = R.2.1.val := congrArg (fun r => r.2.1.val) hR
  rw [← h1, ← h2]
  exact ⟨rfl, rfl⟩

def torsor_toCls {R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR} {ρ : ℕ} (s : LiftT X Y u u' κ R ρ) :
    ClassT X Y u u' κ ρ :=
  ⟨s.1.toTerm, torsor_elig s, s.2.2.2.2⟩

end TorsorStructure

open TorsorStructure

theorem torsorC_of (hRL : Formalism.L2.SG.DataInst.RowLabel κ) (hI : LiftIotaFreeC X Y u u')
    (hM : LiftMassC X Y u u') (hC : LiftRowCohC X Y u u') : TorsorC X Y u u' vR i0 i0' νq κ := by
  intro ρ
  have hw' : ∀ Λ, 0 ≤ Formalism.MainNotions.S.wRow D (X.Fu u') Λ := fun Λ => by
    unfold Formalism.MainNotions.S.wRow; positivity
  have hw : ∀ Λ, 0 ≤ Formalism.MainNotions.S.wRow D (X.Fu u) Λ := fun Λ => by
    unfold Formalism.MainNotions.S.wRow; positivity
  have hlift : ∀ (R : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) (s0 : LiftT X Y u u' κ R ρ)
      (t : ClassT X Y u u' κ ρ), ∃ s : LiftT X Y u u' κ R ρ, s.1.toTerm = t.1 := by
    intro R s0 t
    have he0 := torsor_elig s0
    have hsc : Formalism.L2.SG.Corank.TermScal D s0.1.toTerm t.1 :=
      (hRL _ _ he0 t.2.1).mp (s0.2.2.2.2.trans t.2.2.symm)
    obtain ⟨s', hs't, hs'r⟩ := hC s0.1 t.1 he0 t.2.1 hsc
    have hel : Formalism.L2.SG.DataInst.Elig s'.toTerm := by rw [hs't]; exact t.2.1
    obtain ⟨hG, hgen⟩ := torsor_G_gener s' hel
    have hk : κ s'.toTerm = ρ := by rw [hs't]; exact t.2.2
    exact ⟨⟨s', hG, hgen, hs'r.trans s0.2.2.2.1, hk⟩, hs't⟩
  let hE : ∀ R, LiftT X Y u u' κ R ρ → (LiftT X Y u u' κ R ρ ≃ ClassT X Y u u' κ ρ) := fun R s0 =>
    Equiv.ofBijective torsor_toCls
      ⟨fun s s' h => Subtype.ext (hI s.1 s'.1 (torsor_elig s) (congrArg Subtype.val h)
          (s.2.2.2.1.trans s'.2.2.2.1.symm)),
        fun t => by
          obtain ⟨s, hs⟩ := hlift R s0 t
          exact ⟨s, Subtype.ext hs⟩⟩
  have hF : ∀ R, liftVal X Y u u' vR i0 i0' νq κ R ρ =
      if Nonempty (LiftT X Y u u' κ R ρ) then
        ((Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u') R.2.1.1) : ℝ) : ℂ) • clsVec X Y u u' vR i0 i0' νq κ ρ
      else 0 := by
    intro R
    split_ifs with h
    · obtain ⟨s0⟩ := h
      unfold liftVal clsVec
      rw [← tsum_const_smul'', ← (hE R s0).tsum_eq]
      refine tsum_congr fun s => ?_
      rw [smul_smul]
      congr 1
      have hl := (torsor_lam s).2
      have key : (((Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) s.1.lam * Formalism.MainNotions.S.wRow D (X.Fu u') s.1.lam')) : ℝ) : ℂ) *
          Formalism.L2.SG.PairVal.cTerm vR s.1.toTerm =
          ((Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u') R.2.1.1) : ℝ) : ℂ) *
            ((((Real.sqrt (Formalism.MainNotions.S.wRow D (X.Fu u) s.1.lam)) : ℝ) : ℂ) *
              Formalism.L2.SG.PairVal.cTerm vR s.1.toTerm) := by
        rw [Real.sqrt_mul (hw _), hl]; push_cast; ring
      exact key
    · haveI : IsEmpty (LiftT X Y u u' κ R ρ) := not_nonempty_iff.mp h
      unfold liftVal
      exact tsum_empty
  by_cases hcl : Nonempty (ClassT X Y u u' κ ρ)
  · obtain ⟨t0⟩ := hcl
    let g : Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR → ℝ := fun R =>
      if Nonempty (LiftT X Y u u' κ R ρ) then Formalism.MainNotions.S.wRow D (X.Fu u') R.2.1.1 else 0
    have hnorm : ∀ R, ‖liftVal X Y u u' vR i0 i0' νq κ R ρ‖ ^ 2 =
        g R * ‖clsVec X Y u u' vR i0 i0' νq κ ρ‖ ^ 2 := by
      intro R
      simp only [g]
      rw [hF R]
      split_ifs with h
      · rw [norm_smul, mul_pow, Complex.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hw' _)]
      · simp
    let S : Set (Formalism.L2.SG.TermOp.Rw (Y.what₂ u) (Y.what₂ u') Y.TR) :=
      {R | Nonempty (LiftT X Y u u' κ R ρ)}
    have hlift0 : ∀ s : {s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') //
        s.toTerm = t0.1}, LiftT X Y u u' κ ((Y.tO u u').rowOf s.1) ρ := fun s => by
      have hel : Formalism.L2.SG.DataInst.Elig s.1.toTerm := by rw [s.2]; exact t0.2.1
      obtain ⟨hG, hgen⟩ := torsor_G_gener s.1 hel
      have hk : κ s.1.toTerm = ρ := by rw [s.2]; exact t0.2.2
      exact ⟨s.1, hG, hgen, rfl, hk⟩
    let e2 : {s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') //
        s.toTerm = t0.1} ≃ S :=
      Equiv.ofBijective (fun s => ⟨(Y.tO u u').rowOf s.1, ⟨hlift0 s⟩⟩)
        ⟨fun s s' h => by
            have hr : (Y.tO u u').rowOf s.1 = (Y.tO u u').rowOf s'.1 := congrArg Subtype.val h
            have hel : Formalism.L2.SG.DataInst.Elig s.1.toTerm := by rw [s.2]; exact t0.2.1
            exact Subtype.ext (hI s.1 s'.1 hel (s.2.trans s'.2.symm) hr),
          fun R => by
            obtain ⟨s1⟩ := R.2
            obtain ⟨s, hs⟩ := hlift R.1 s1 t0
            exact ⟨⟨s.1, hs⟩, Subtype.ext s.2.2.2.1⟩⟩
    have hmass := hM t0.1 t0.2.1
    have hsumg : ∑' R, g R = 1 := by
      have h1 : ∑' R, g R = ∑' x : S, Formalism.MainNotions.S.wRow D (X.Fu u') x.1.2.1.1 := by
        rw [tsum_subtype S (fun R => Formalism.MainNotions.S.wRow D (X.Fu u') R.2.1.1)]
        refine tsum_congr fun R => ?_
        simp only [g, S, Set.indicator_apply, Set.mem_setOf_eq]
      rw [h1, ← e2.tsum_eq]
      exact hmass
    have hg0 : ∀ R, 0 ≤ g R := fun R => by
      simp only [g]; split_ifs
      · exact hw' _
      · exact le_rfl
    have hsum : Summable g := by
      by_contra hns
      rw [tsum_eq_zero_of_not_summable hns] at hsumg
      norm_num at hsumg
    refine ⟨?_, ?_⟩
    · simp_rw [hnorm]
      exact hsum.mul_right _
    · simp_rw [hnorm]
      rw [tsum_mul_right, hsumg, one_mul]
  · haveI : IsEmpty (ClassT X Y u u' κ ρ) := not_nonempty_iff.mp hcl
    have hC0 : clsVec X Y u u' vR i0 i0' νq κ ρ = 0 := by
      unfold clsVec; exact tsum_empty
    have hF0 : ∀ R, liftVal X Y u u' vR i0 i0' νq κ R ρ = 0 := by
      intro R
      rw [hF R, if_neg]
      rintro ⟨s⟩
      exact hcl ⟨torsor_toCls s⟩
    simp [hF0, hC0]

end Formalism.L2.SG.Pf.RowForm
end
end

