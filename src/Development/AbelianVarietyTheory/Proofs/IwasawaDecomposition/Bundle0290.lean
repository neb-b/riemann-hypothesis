module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1012
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockFrameConjugationIdentity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0942
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0852
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0845
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0832
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1146
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodFixedVectorOfTypeOccurringInRows

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinXSpectralRedivisionFullChoices
section
noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe

attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 4000000 in
theorem toTerm_eTT_symm {D : D7} (Z : New D) {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (s : TT (reY Z Y) (wd Z u) (wd Z u')) :
    ((eTT Z Y u u').symm s).toTerm = (eRT Z Y u u').symm s.toTerm := (by with_unfolding_all exact (Eq.refl ((eRT Z Y u u').symm s.toTerm) :))


set_option maxHeartbeats 4000000 in
def eFib {D : D7} (Z : New D) {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)
    (t : RT (reY Z Y) (wd Z u) (wd Z u')) :
    fib Y ((eRT Z Y u u').symm t) ≃ fib (reY Z Y) t :=
  ((eTT Z Y u u').symm.subtypeEquiv fun s => by
    rw [toTerm_eTT_symm]
    exact ((eRT Z Y u u').symm.injective.eq_iff).symm).symm


set_option maxHeartbeats 4000000 in
theorem fibFin_re {D : D7} (Z : New D) {X : HidaSetting D} {Y : Full X} (h : FinX Y) (u u' : D.what₂.Word)
    (t : RT (reY Z Y) (wd Z u) (wd Z u')) : Finite (fib (reY Z Y) t) := by
  have := h.fibFin u u' ((eRT Z Y u u').symm t)
  exact Finite.of_equiv _ (eFib Z Y u u' t)


set_option maxHeartbeats 4000000 in
theorem pairIndep_re {D : D7} (Z : New D) {X : HidaSetting D} {Y : Full X} (h : FinX Y) (u u' : D.what₂.Word)
    (s₁ s₂ s₁' s₂' : TT (reY Z Y) (wd Z u) (wd Z u')) (e₁ : s₁.toTerm = s₁'.toTerm) (e₂ : s₂.toTerm = s₂'.toTerm)
    (r₁ : rowOf (reY Z Y).TR ((reY Z Y).cs u) ((reY Z Y).cs u') s₁ = rowOf (reY Z Y).TR ((reY Z Y).cs u) ((reY Z Y).cs u') s₂)
    (r₂ : rowOf (reY Z Y).TR ((reY Z Y).cs u) ((reY Z Y).cs u') s₁' = rowOf (reY Z Y).TR ((reY Z Y).cs u) ((reY Z Y).cs u') s₂') :
    s0T s₁ s₂ = s0T s₁' s₂' ∧ (liftScalar s₁ s₂ ↔ liftScalar s₁' s₂') := by
  have e₁' : ((eTT Z Y u u').symm s₁).toTerm = ((eTT Z Y u u').symm s₁').toTerm := by
    rw [toTerm_eTT_symm, toTerm_eTT_symm, e₁]
  have e₂' : ((eTT Z Y u u').symm s₂).toTerm = ((eTT Z Y u u').symm s₂').toTerm := by
    rw [toTerm_eTT_symm, toTerm_eTT_symm, e₂]
  have := h.pairIndep u u' ((eTT Z Y u u').symm s₁) ((eTT Z Y u u').symm s₂)
    ((eTT Z Y u u').symm s₁') ((eTT Z Y u u').symm s₂') e₁' e₂' ((by with_unfolding_all exact (r₁ :))) ((by with_unfolding_all exact (r₂ :)))
  with_unfolding_all exact this


set_option maxHeartbeats 16000000 in
theorem finX_reY : ∀ (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X), FinX Y → FinX (reY Z Y) := by
  intro D Z X Y h
  refine
  { shInj := (by with_unfolding_all exact (h.shInj :))
    shSurj := (by with_unfolding_all exact (h.shSurj :))
    inHH := by with_unfolding_all exact h.inHH
    puLin := by with_unfolding_all exact h.puLin
    finHH := (by with_unfolding_all exact (h.finHH :))
    fibFin := (by with_unfolding_all exact (fibFin_re Z h :))
    pairIndep := (by with_unfolding_all exact (pairIndep_re Z h :))
    Greal := ?_
    cdEx := (by with_unfolding_all exact (h.cdEx :))
    volPos := (by with_unfolding_all exact (h.volPos :)) }
  intro u u' t
  with_unfolding_all exact h.Greal u u' ((eRT Z Y u u').symm t)

end GlobalTheory.Mem.SRe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteTypeIsotypicPartEqISupEquivariantHomsFrame
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

namespace GlobalTheory.IsotHom

theorem isotIn_eq_iSup_homInto : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : DSModel V S) {n : ℕ} (P : principalLevelFrame.RowPsi V n) (π : Formalism.L2.NG.FinTyp D.host.E n), principalLevelFrame.isotIn (principalLevelFrame.actM P M) (principalLevelFrame.Minf θ P M) π = ⨆ f ∈ homInto ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv P).symm.toMonoidHom) (finRep M) (allMaps θ M), LinearMap.range f := by
  intro D V S θ M n P π
  classical
  set e := GlobalTheory.KapIsot.eqv P with he
  have hσ : ∀ κ (x : π.S), ((GlobalTheory.OccRowVec.finRep π).comp e.symm.toMonoidHom) (e κ) x = GlobalTheory.OccRowVec.finRep π κ x := fun κ x => by
    show GlobalTheory.OccRowVec.finRep π (e.symm (e κ)) x = _
    rw [MulEquiv.symm_apply_apply]
  have hact : ∀ κ (T : MMap M), principalLevelFrame.actM P M κ T = finRep M (e κ) T := fun κ T => by
    refine MultilinearMap.ext fun v => funext fun g => ?_
    rw [principalLevelFrame.actM_apply, finRep_apply]
    rfl
  have hle : principalLevelFrame.Minf θ P M ≤ allMaps θ M := iSup_le fun N => GlobalTheory.PartDims.mult_le θ M fun k hk => hk.elim
  apply le_antisymm
  · refine iSup₂_le fun Φ hΦ => ?_
    refine le_iSup₂_of_le (f := fun f (_ : f ∈ homInto ((GlobalTheory.OccRowVec.finRep π).comp e.symm.toMonoidHom) (finRep M) (allMaps θ M)) => LinearMap.range f) Φ ⟨fun s => hle (hΦ.2 ⟨s, rfl⟩), fun g s => ?_⟩ le_rfl
    obtain ⟨κ, rfl⟩ := e.surjective g
    rw [hσ, ← hact]
    exact hΦ.1 κ s
  · refine iSup₂_le fun f hf => ?_
    have hfe : principalLevelFrame.IsEqvA (principalLevelFrame.actM P M) π f := by
      intro κ x
      have h1 := hf.2 (e κ) x
      rw [hσ, ← hact] at h1
      exact h1
    have hfr : LinearMap.range f ≤ principalLevelFrame.Minf θ P M := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨N, hN, hfix⟩ := π.smooth x x.2
      obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
      refine Submodule.mem_iSup_of_mem N (Submodule.subset_span ?_)
      have h1 := (GlobalTheory.MultMem.mem_mult_iff ..).1 (hf.1 x)
      refine ⟨h1.aut, h1.cusp, ?_, h1.equiv, h1.cont⟩
      rintro v _ ⟨κ, hκ, rfl⟩ g
      have h2 := hfe κ x
      rw [show (⟨Formalism.L2.NG.rt D.host.E n κ x, π.stable κ x x.2⟩ : π.S) = x from Subtype.ext (hfix κ hκ)] at h2
      rw [one_mul]
      exact (congrArg (fun T : MMap M => T v g) h2).symm
    exact le_iSup₂_of_le (f := fun (Φ : π.S →ₗ[ℂ] MMap M) (_ : principalLevelFrame.IsEqvA (principalLevelFrame.actM P M) π Φ ∧ LinearMap.range Φ ≤ principalLevelFrame.Minf θ P M) => LinearMap.range Φ) f ⟨hfe, hfr⟩ le_rfl

end GlobalTheory.IsotHom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagBundleFunctionFieldMapDominatesLocalRingStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fullFlagBundle_functionFieldMap_dominates_localRings : ∀ (F : Type) [Field F] (ι : Type) [Fintype ι] (m : ι → ℕ) (X Y₁ Y₂ : Var F) (Eb : Fr (ratOf X) m 0) (S₁ : Fr (ratOf Y₁) m m) (φ₁ : X.Fn →ₐ[F] Y₁.Fn) (f₁ : Y₁.X ⟶ X.X) (S₂ : Fr (ratOf Y₂) m m) (φ₂ : X.Fn →ₐ[F] Y₂.Fn) (f₂ : Y₂.X ⟶ X.X), Reps Eb S₁ φ₁ f₁ → Reps Eb S₂ φ₂ f₂ → ∀ ψ : Y₂.Fn →ₐ[F] Y₁.Fn, ψ.comp φ₂ = φ₁ → CoBear Eb S₁ φ₁ S₂ φ₂ ((ratOf Y₁).pt ≫ f₁) (ratOf Y₁).pt (spMap ψ.toRingHom ≫ (ratOf Y₂).pt) → ∀ y : Y₁.X, ∃ y' : Y₂.X, ∀ a ∈ (ratOf Y₂).O y', ψ a ∈ (ratOf Y₁).O y := by
  first | exact @GlobalTheory.FlagBundle.dominates_O | exact GlobalTheory.FlagBundle.dominates_O | (intros; apply GlobalTheory.FlagBundle.dominates_O <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodParParBLast
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainModels

open Finset GlobalTheory.SignedHC GlobalTheory.ContragredientPar

theorem goodPar_image {ι : Type} [Fintype ι] {n p q : ℕ} (f : ι → ℚ × Bool) (hf : Function.Injective fun a => (f a).1)
    (hn : Fintype.card ι = n) (hc : ∀ a, ∃ z : ℤ, (f a).1 = ((n : ℚ) - 1) / 2 + z)
    (hq : (univ.filter fun a => (f a).2 = false).card = q) (hpq : p + q = n) : GoodPar n p q (univ.image f) := by
  have hinj : Function.Injective f := fun a c h => hf (congrArg Prod.fst h)
  have hcard : (univ.image f).card = n := by rw [card_image_of_injective _ hinj, card_univ, hn]
  have hminus : SignedHC.nMinus (univ.image f) = q := by
    rw [SignedHC.nMinus, filter_image, card_image_of_injective _ hinj, hq]
  have hsum := nPlus_add_nMinus (univ.image f)
  refine goodPar_iff.2 ⟨⟨?_, hcard, ?_⟩, ?_⟩
  · intro x hx y hy e
    obtain ⟨a, -, rfl⟩ := mem_image.1 hx
    obtain ⟨c, -, rfl⟩ := mem_image.1 hy
    rw [hf e]
  · intro x hx
    obtain ⟨s, hs⟩ := mem_entries.1 hx
    obtain ⟨a, -, e⟩ := mem_image.1 hs
    have e1 : (f a).1 = x := congrArg Prod.fst e
    rw [← e1]
    exact hc a
  · simp only [signature, Prod.mk.injEq]
    omega

variable {R : Ranks} (P : HCParam R)

theorem b_le_e {a c : Fin R.m} (h : a ≤ c) : P.b a + ((R.t : ℚ) + 3) / 2 ≤ P.e c := by
  have h1 := P.gap_be c
  have h2 := (b_strictMono P).monotone h
  linarith

theorem e_le_b {a c : Fin R.m} (h : c < a) : P.e c + ((R.t : ℚ) + 3) / 2 ≤ P.b a := by
  have hc : c.1 + 1 < R.m := lt_of_le_of_lt (Nat.succ_le_of_lt h) a.2
  have h1 := P.gap_eb c hc
  have h2 : P.b ⟨c.1 + 1, hc⟩ ≤ P.b a := (b_strictMono P).monotone (show c.1 + 1 ≤ a.1 from h)
  linarith

def entAt (j : ℕ) (hj : j ≤ R.m) (s : ℚ) : Fin (R.k - 1) ⊕ Fin R.m ⊕ Fin j × Fin R.t → ℚ × Bool
  | .inl i => (P.v i + s, true)
  | .inr (.inl i) => (-P.b i + s, decide (i.1 ≤ j ∨ Even (i.1 - j)))
  | .inr (.inr x) => (-P.e (Fin.castLE hj x.1) + ((R.t : ℚ) - 1) / 2 - (x.2 : ℕ) + s, true)

theorem entAt_inj (j : ℕ) (hj : j ≤ R.m) (s : ℚ) : Function.Injective fun a => (entAt P j hj s a).1 := by
  have hb : ∀ a : Fin R.t, (0 : ℚ) ≤ (a : ℕ) ∧ ((a : ℕ) : ℚ) + 1 ≤ R.t := fun a =>
    ⟨Nat.cast_nonneg _, by exact_mod_cast a.2⟩
  have hvb : ∀ i (c : Fin R.m) (a : Fin R.t), P.v i ≠ -P.e c + ((R.t : ℚ) - 1) / 2 - (a : ℕ) := fun i c a h => by
    have := neg_v_lt_b P i c
    have := b_le_e P (le_refl c)
    have := hb a
    linarith [this.1]
  have hbb : ∀ (i c : Fin R.m) (a : Fin R.t), -P.b i ≠ -P.e c + ((R.t : ℚ) - 1) / 2 - (a : ℕ) := fun i c a h => by
    have := hb a
    rcases le_or_gt i c with h' | h'
    · linarith [b_le_e P h', this.1]
    · linarith [e_le_b P h', this.2]
  have hee : ∀ (c c' : Fin R.m) (a a' : Fin R.t), c < c' →
      -P.e c + ((R.t : ℚ) - 1) / 2 - (a : ℕ) ≠ -P.e c' + ((R.t : ℚ) - 1) / 2 - (a' : ℕ) := fun c c' a a' h' h => by
    linarith [e_le_b P h', b_le_e P (le_refl c'), (hb a).2, (hb a').1]
  rintro (a | a | ⟨a, x⟩) (c | c | ⟨c, y⟩) h <;> simp only [entAt, add_left_inj] at h
  · rw [(v_strictAnti P).injective h]
  · exact absurd (by linarith) (neg_v_lt_b P a c).ne
  · exact absurd h (hvb _ _ _)
  · exact absurd (by linarith) (neg_v_lt_b P c a).ne
  · rw [(b_strictMono P).injective (neg_injective h)]
  · exact absurd h (hbb _ _ _)
  · exact absurd h.symm (hvb _ _ _)
  · exact absurd h.symm (hbb _ _ _)
  · rcases lt_trichotomy a c with h' | rfl | h'
    · exact absurd h (hee _ _ _ _ h')
    · have : ((x : ℕ) : ℚ) = (y : ℕ) := by linarith
      rw [Fin.ext (Nat.cast_injective this : (x : ℕ) = y)]
    · exact absurd h.symm (hee _ _ _ _ h')

theorem card_minus (j m : ℕ) : ((range m).filter fun i => ¬ (i ≤ j ∨ Even (i - j))).card = (m - j) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [range_add_one, filter_insert]
    split_ifs with h
    · rw [ih]
      rw [Nat.even_iff] at h
      omega
    · rw [card_insert_of_notMem (by simp), ih]
      rw [Nat.even_iff] at h
      omega

theorem card_entAt_false (j : ℕ) (hj : j ≤ R.m) (s : ℚ) :
    (univ.filter fun a => (entAt P j hj s a).2 = false).card = (R.m - j) / 2 := by
  rw [← card_minus j R.m]
  symm
  refine card_bij (fun i hi => .inr (.inl ⟨i, mem_range.1 (mem_filter.1 hi).1⟩)) ?_ ?_ ?_
  · intro i hi
    refine mem_filter.2 ⟨mem_univ _, ?_⟩
    simpa [entAt] using (mem_filter.1 hi).2
  · intro a _ c _ h
    simpa using h
  · rintro (a | a | a) hx
    · simp [entAt] at hx
    · exact ⟨a.1, mem_filter.2 ⟨mem_range.2 a.2, by simpa [entAt] using hx⟩, rfl⟩
    · simp [entAt] at hx

theorem goodPar_entAt (j : ℕ) (hj : j ≤ R.m) :
    GoodPar (R.rankY j) (sigYD R j).1 (sigYD R j).2 (univ.image (entAt P j hj (if Odd j then -(1 / 2) else 0))) := by
  have hk := R.m_add_three_le_k
  have hm := R.two_le_m
  obtain ⟨k', hk'⟩ := R.k_even
  obtain ⟨m', hm'⟩ := R.m_even
  obtain ⟨t', ht'⟩ := R.t_odd
  refine goodPar_image _ (entAt_inj P j hj _) ?_ ?_ (card_entAt_false P j hj _) ?_
  · simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Ranks.rankY, Ranks.r]
    omega
  · have hs : ∃ w : ℤ, (if Odd j then -(1 / 2) else 0 : ℚ) = ((R.rankY j : ℚ) - 1) / 2 + w := by
      have hr : R.r = 2 * (k' + m' - 1) + 1 := by unfold Ranks.r; omega
      unfold Ranks.rankY
      rw [hr, ht']
      generalize k' + m' - 1 = n
      rcases Nat.even_or_odd' j with ⟨i, rfl | rfl⟩
      · rw [if_neg (by simp)]
        exact ⟨-(n + i * (2 * t' + 1)), by push_cast; ring⟩
      · rw [if_pos (by simp)]
        exact ⟨-(n + i * (2 * t' + 1) + t' + 1), by push_cast; ring⟩
    obtain ⟨w, hw⟩ := hs
    rw [hw]
    rintro (a | a | ⟨a, x⟩)
    · obtain ⟨z, hz⟩ := P.v_int a
      exact ⟨z + w, by simp only [entAt, hz]; push_cast; ring⟩
    · obtain ⟨z, hz⟩ := P.b_int a
      exact ⟨-z + w, by simp only [entAt, hz]; push_cast; ring⟩
    · obtain ⟨z, hz⟩ := P.e_int (Fin.castLE hj a)
      refine ⟨-z + t' - (x : ℕ) + w, ?_⟩
      have ht : (R.t : ℚ) = 2 * t' + 1 := by exact_mod_cast ht'
      simp only [entAt, hz, ht]; push_cast; ring
  · simp only [sigYD, Ranks.rankY, Ranks.r]
    omega

theorem Dpar_eq (D : D7) (j : ℕ) (hj : j ≤ D.R.m) (τ : D.what₂.Tau) :
    (Ptw D).Dpar j τ = univ.image (entAt (D.hc τ) j hj (if Odd j then -(1 / 2) else 0)) := by
  ext x
  simp only [TPar.Dpar, TPar.block, mem_image, mem_union, mem_biUnion, mem_filter, mem_univ, true_and, mem_range,
    Sum.exists, Prod.exists, entAt]
  constructor
  · rintro ⟨_, _, (⟨i, e⟩ | ⟨i, e⟩) | ⟨i, hi, _, ⟨a, ha, rfl⟩, e⟩, rfl⟩ <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr (Or.inl ⟨i, rfl⟩)
    · exact Or.inr (Or.inr ⟨⟨i.1, hi⟩, ⟨a, ha⟩, rfl⟩)
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, a, rfl⟩)
    · exact ⟨_, _, Or.inl (Or.inl ⟨i, rfl⟩), rfl⟩
    · exact ⟨_, _, Or.inl (Or.inr ⟨i, rfl⟩), rfl⟩
    · exact ⟨_, _, Or.inr ⟨Fin.castLE hj i, i.2, _, ⟨a.1, a.2, rfl⟩, rfl⟩, rfl⟩

theorem goodPar_parB (D : D7) (j : ℕ) (hj : j ≤ D.R.m) (τ : D.what₂.Tau) :
    GoodPar (D.sp.Y j).rank ((D.sp.Y j).sig (tauE D τ)).1 ((D.sp.Y j).sig (tauE D τ)).2 (parB (Ptw D) j τ) := by
  rw [D.sp.Y_rank j hj, D.Y_sigval j hj, parB, Dpar_eq D j hj]
  exact GlobalTheory.RealGeo.FrameModels.goodPar_dualPar (goodPar_entAt (D.hc τ) j hj)

theorem goodPar_parB_last (D : D7) (τ : D.what₂.Tau) :
    GoodPar D.sp.X'.rank (D.sp.X'.sig (tauE D τ)).1 (D.sp.X'.sig (tauE D τ)).2 (parB (Ptw D) D.R.m τ) := by
  have h := goodPar_parB D D.R.m le_rfl τ
  rw [D.sp.Y_rank _ le_rfl] at h
  rw [GlobalTheory.ChiGrid.sig_X'_eq_sig_Y, D.sp.X'_rank]
  exact h

theorem nonempty_modelY (h : GlobalTheory.Published.DiscreteSeriesExists) (D : D7) (j : ℕ) :
    Nonempty (DSModel (Yc D j) (parB (Ptw D) (min j D.R.m))) :=
  GlobalTheory.Published.dsExists_of_discreteSeriesExists h D _ _ (D.sp.Y_sig _) (goodPar_parB D _ (min_le_right _ _))

theorem nonempty_modelX (h : GlobalTheory.Published.DiscreteSeriesExists) (D : D7) :
    Nonempty (DSModel D.sp.X' (parB (Ptw D) D.R.m)) :=
  GlobalTheory.Published.dsExists_of_discreteSeriesExists h D _ _ D.sp.X'_sig (goodPar_parB_last D)

theorem labE_embLL (D : D7) (τ : D.what₂.Tau) : labE D.what₂.embLL τ = tauE D τ := by
  ext x
  exact DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf (D.eTau τ).1 x)

theorem labE_lab_embLL (D : D7) (ρ : D.what₂.Tau) : labE D.what₂.embLL (lab D.what₂.embLL ρ) = tauE D ρ := by
  have h : ∃ τ, labE D.what₂.embLL τ = tauE D ρ ∨ labE D.what₂.embLL τ = (starRingEnd ℂ).comp (tauE D ρ) :=
    ⟨ρ, Or.inl (labE_embLL D ρ)⟩
  unfold lab
  rw [dite_eq_left h]
  have hs := h.choose_spec
  generalize h.choose = τ at hs
  rcases hs with hs | hs
  · exact hs
  · exfalso
    rw [labE_embLL] at hs
    have a := xi_zero_im_pos D τ
    have b := xi_zero_im_pos D ρ
    rw [hs] at a
    simp at a
    linarith

theorem exists_models : GlobalTheory.Published.DiscreteSeriesExists → ∀ D : D7,
    ((∀ j, Nonempty (DSModel (Yc D j) (parB (Ptw D) (min j D.R.m)))) ∧ Nonempty (DSModel D.sp.X' (parB (Ptw D) D.R.m))) ∧
    ∀ (Ks : Type) [Field Ks] [Algebra Ks D.what₂.LL], (∀ x : D.host.E, ∃ y : Ks, algebraMap Ks D.what₂.LL y = D.embE x) →
      ∃ MW : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), DSModel (Wc D i) (parAt (Wc D i) σ),
        (∀ i τ a, (MW i D.what₂.embLL).ε τ a = decide ((a : ℕ) < ((Wc D i).sig (tauE D τ)).1)) ∧
          GlobalTheory.RealGeo.FrameKs Ks MW := by
  intro h D
  refine ⟨⟨nonempty_modelY h D, nonempty_modelX h D⟩, fun Ks _ _ hK => ?_⟩
  obtain ⟨MW, hMW⟩ := GlobalTheory.RealGeo.FrameModels.exists_frameKs h D Ks hK
  exact ⟨MW, fun i => hMW.2 i _ (labE_lab_embLL D), hMW⟩

end GlobalTheory.ChainModels
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAdmissibleFiniteTypeFrameOfCuspMap
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

namespace GlobalTheory.AdmOfHom

theorem isAdmissible_finRep : GlobalTheory.Published.HarishChandraFinite → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V V' : HSp D) {S S' : D.what₂.Tau → SPar} (M : DSModel V S) (M' : DSModel V' S') (Φ : GfC V ≃ₜ* GfC V') (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r) (c : G → ℂ) (P' : LevelP L.Pg L.r ℂ) {n : ℕ} (P : principalLevelFrame.RowPsi V n) (π : Formalism.L2.NG.FinTyp D.host.E n), L.s = 0 → L.Q = ∅ → killed ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv P).symm.toMonoidHom) (eqSet V β L eG c P' (∅ : Set Empty) Empty.elim Empty.elim Empty.elim) ≠ ⊥ → (homInto ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv P).symm.toMonoidHom) (finRep M) (allMaps θ M) ≠ ⊥ ∨ homInto ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv P).symm.toMonoidHom) ((finRep M').comp Φ.toMulEquiv.toMonoidHom) (allMaps θ M') ≠ ⊥) → GlobalTheory.PRep.IsAdmissible ((GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv P).symm.toMonoidHom) := by
  intro hP D θ hθ V V' S S' M M' Φ β L G _ _ eG c P' n P π hs hQ hk hhom
  set σ : Representation ℂ (GfC V) π.S := (GlobalTheory.OccRowVec.finRep π).comp (GlobalTheory.KapIsot.eqv P).symm.toMonoidHom with hσdef
  have hirr : ∀ U : Submodule ℂ π.S, (∀ g, ∀ x ∈ U, σ g x ∈ U) → U = ⊥ ∨ U = ⊤ := fun U hU =>
    GlobalTheory.OccRowVec.finRep_irr π U fun g x hx => by
      have := hU (GlobalTheory.KapIsot.eqv P g) x hx
      simpa [σ] using this
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  have ho := GlobalTheory.PartDims.isOpen_stab hs hQ hy
  haveI := GlobalTheory.PartDims.isTopologicalGroup_GA V
  rcases hhom with h | h
  · obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    exact GlobalTheory.KapIsot.isAdmissible_of hirr hy0 ho hf hf0
      (fun K hK => GlobalTheory.CuspDec.finiteDimensional_fixed hP hθ K hK)
  · obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    refine GlobalTheory.KapIsot.isAdmissible_of hirr hy0 ho hf hf0 (fun K hK => ?_)
    have hK' : IsOpen ((K.map Φ.toMulEquiv.toMonoidHom : Subgroup (GfC V')) : Set (GfC V')) := by
      rw [Subgroup.coe_map]
      exact Φ.toHomeomorph.isOpenMap _ hK
    haveI := GlobalTheory.CuspDec.finiteDimensional_fixed (M := M') hP hθ _ hK'
    refine Submodule.finiteDimensional_of_le (S₂ := allMaps θ M' ⊓ GlobalTheory.PRep.fixed (finRep M') (K.map Φ.toMulEquiv.toMonoidHom))
      fun x hx => ⟨hx.1, GlobalTheory.CuspDec.mem_fixed.2 fun k hk => ?_⟩
    obtain ⟨k0, hk0, rfl⟩ := Subgroup.mem_map.1 hk
    exact GlobalTheory.CuspDec.mem_fixed.1 hx.2 k0 hk0

end GlobalTheory.AdmOfHom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotNeBotRead
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem.R3

namespace GlobalTheory.KapIsotRead


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem isot_ne_bot_read : GlobalTheory.Published.HarishChandraFinite → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → GlobalTheory.CuspMult.MultEq R.toRealDat → Formalism.L2.DIV.GoodStable A3.A.X → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ σ (i : Fin D.R.m), D.what₂.isot ((i : ℕ) + 1) (D.what₂.ft σ) ≠ ⊥ := by
  intro hP D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hPin hH hME hGS hgen σ i
  have hL := Y.tied.lift
  obtain ⟨w, hw, hw0⟩ := GlobalTheory.KapIsot.exists_mem_isotL hP R.toRealDat F.lv2 hH.ok.ok2 (GlobalTheory.CoreOfWeak.core_of_weak R F hPin.char hH.aux.ex).1 hME hGS hgen Y.hF Y.PY i (Y.PW i) Y.stdPsi.1 (Y.stdPsi.2 i) (principalLevelFrame.rowRepR R.θ (Y.eFT (D.what₂.ft σ))) (principalLevelFrame.rowRepR_occ _ _)
  intro hbot
  let L := RecTie.toLiftReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop Y.hinj
  let lw : L.AmbW i := (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] L.AmbW i) w
  have hgood : lw ∈ L.Wc i := Submodule.mem_map_of_mem hw.1
  let y : D.what₂.Mj ((i : ℕ) + 1) := (Y.IL.jMj i).symm ⟨lw, hgood⟩
  have hjy : ((Y.IL.jMj i y : L.Wc i) : L.AmbW i) = lw := by
    simp only [y, LinearEquiv.apply_symm_apply]
  have hmem : ((Y.IL.jMj i y : L.Wc i) : L.AmbW i) ∈ Y.IL.prtW i (D.what₂.ft σ) := by
    rw [hjy, Y.prtWE]
    exact ⟨w, hw, rfl⟩
  have hy0 : y ∈ D.what₂.isot ((i : ℕ) + 1) (D.what₂.ft σ) := (hL.isot i _ y).2 hmem
  rw [hbot, Submodule.mem_bot] at hy0
  apply hw0
  have h1 : lw = 0 := by rw [← hjy, hy0, map_zero]; rfl
  exact (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] L.AmbW i).injective (h1.trans (map_zero _).symm)

end GlobalTheory.KapIsotRead
end
end

