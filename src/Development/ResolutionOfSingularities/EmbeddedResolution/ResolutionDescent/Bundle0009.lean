module

public import Mathlib
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Bundle0001
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.Bundle0008
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SequenceIsomorphism
public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.Bundle0003
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.FieldExtensionEtaleCover
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatDescent
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.Bundle0006
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.Bundle0004

@[expose] public section

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceDescentDatum
section
universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem baseChange_projectionToBase_eq_fst {X X' : Scheme.{u}} (s : SequenceOfBlowups X)
    (φ : X' ⟶ X) [AlgebraicGeometry.Flat φ] (i : ℕ) :
    (s.baseChange φ).projectionToBase i = pullback.fst φ (s.projectionToBase i) := by
  induction i with
  | zero =>
    rw [SequenceOfBlowups.projectionToBase_zero, SequenceOfBlowups.baseChange_isoObjZero_hom]
  | succ n ih =>
    have hb : (s.baseChange φ).transitionMapSucc n ≫ (s.baseChange φ).projectionToBase n
        = (s.baseChange φ).projectionToBase (n + 1) := by
      rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap]
      exact SequenceOfBlowups.transitionMap_comp_projectionToBase _ _
    rw [← hb, ih, SequenceOfBlowups.baseChange_blowupMorphism]
    exact SequenceOfBlowups.pullbackTransitionMap_comp_fst s φ _

structure SequenceOfBlowupsDescentDatum {W Y : Scheme.{u}} (g : W ⟶ Y) (t : SequenceOfBlowups W) where
  iso : ∀ i : ℕ, i ≤ t.length → (pullbackFstSchemeAt g t i ≅ pullbackSndSchemeAt g t i)
  comp_fst : ∀ (i : ℕ) (hi : i ≤ t.length),
    (iso i hi).hom ≫ pullback.fst (pullback.snd g g) (t.projectionToBase i)
      = pullback.fst (pullback.fst g g) (t.projectionToBase i)
  center_comap : ∀ (i : ℕ) (hi : i < t.length),
    ((t.center i).comap (pullback.snd (pullback.snd g g) (t.projectionToBase i))).comap
        (iso i hi.le).hom
      = (t.center i).comap (pullback.snd (pullback.fst g g) (t.projectionToBase i))
  comp_step : ∀ (i : ℕ) (hi : i < t.length),
    (iso (i + 1) (Nat.succ_le_of_lt hi)).hom ≫ t.pullbackTransitionMap (pullback.snd g g) (Nat.le_succ i)
      = t.pullbackTransitionMap (pullback.fst g g) (Nat.le_succ i) ≫ (iso i hi.le).hom

private structure DescendedSchemeData {W Y : Scheme.{u}} (g : W ⟶ Y) (t : SequenceOfBlowups W)
    (D : SequenceOfBlowupsDescentDatum g t) (n : ℕ) where
  X : Scheme.{u}
  str : X ⟶ Y
  gam : t.schemeAt n ⟶ X
  hsq : n ≤ t.length → IsPullback gam (t.projectionToBase n) str g
  hgam : ∀ hn : n ≤ t.length,
    (D.iso n hn).hom ≫ pullback.snd (pullback.snd g g) (t.projectionToBase n) ≫ gam
      = pullback.snd (pullback.fst g g) (t.projectionToBase n) ≫ gam

private structure DescendedBlowupOfSchemeData {W Y : Scheme.{u}} (g : W ⟶ Y) (t : SequenceOfBlowups W)
    (D : SequenceOfBlowupsDescentDatum g t) (n : ℕ) (P : DescendedSchemeData g t D n) where
  next : DescendedSchemeData g t D (n + 1)
  down : next.X ⟶ P.X
  cen : P.X.IdealSheafData
  hblow : n < t.length → Blowup.IsBlowupAlongIdealSheaf down cen
  hpb : n < t.length → IsPullback next.gam (t.transitionMapSucc n) down P.gam
  hcen : n < t.length → t.center n = cen.comap P.gam

private def descendedSchemeDataZero {W Y : Scheme.{u}} (g : W ⟶ Y) (t : SequenceOfBlowups W)
    (D : SequenceOfBlowupsDescentDatum g t) : DescendedSchemeData g t D 0 where
  X := Y
  str := 𝟙 Y
  gam := t.projectionToBase 0 ≫ g
  hsq := fun _ => (IsPullback.of_horiz_isIso ⟨by simp⟩).flip
  hgam := fun h0 => by
    have c1 : pullback.fst (pullback.fst g g) (t.projectionToBase 0) ≫ pullback.fst g g
        = pullback.snd (pullback.fst g g) (t.projectionToBase 0) ≫ t.projectionToBase 0 := pullback.condition
    have c2 : pullback.fst (pullback.snd g g) (t.projectionToBase 0) ≫ pullback.snd g g
        = pullback.snd (pullback.snd g g) (t.projectionToBase 0) ≫ t.projectionToBase 0 := pullback.condition
    have c3 : pullback.fst g g ≫ g = pullback.snd g g ≫ g := pullback.condition
    have hf := D.comp_fst 0 h0
    calc (D.iso 0 h0).hom ≫ pullback.snd (pullback.snd g g) (t.projectionToBase 0) ≫
          (t.projectionToBase 0 ≫ g)
        = ((D.iso 0 h0).hom ≫ pullback.snd (pullback.snd g g) (t.projectionToBase 0) ≫
            t.projectionToBase 0) ≫ g := by
          simp only [Category.assoc]
      _ = (pullback.fst (pullback.fst g g) (t.projectionToBase 0) ≫ pullback.snd g g) ≫ g := by
          rw [← c2, ← Category.assoc, hf]
      _ = (pullback.fst (pullback.fst g g) (t.projectionToBase 0) ≫ pullback.fst g g) ≫ g := by
          rw [Category.assoc, Category.assoc, c3]
      _ = pullback.snd (pullback.fst g g) (t.projectionToBase 0) ≫ (t.projectionToBase 0 ≫ g) := by
          rw [c1, Category.assoc]

private def descendedBlowupAt {W Y : Scheme.{u}} (g : W ⟶ Y) [AlgebraicGeometry.Flat g]
    [AlgebraicGeometry.QuasiCompact g] (t : SequenceOfBlowups W) (D : SequenceOfBlowupsDescentDatum g t)
    (n : ℕ) (P : DescendedSchemeData g t D n) : DescendedBlowupOfSchemeData g t D n P :=
  if hn : n < t.length then
    let S := descendedBlowupData g t hn P.str P.gam (P.hsq hn.le) (D.iso n hn.le)
      (D.iso (n + 1) (Nat.succ_le_of_lt hn)) (D.comp_step n hn) (D.center_comap n hn)
      (D.comp_fst n hn.le) (P.hgam hn.le)
    { next :=
        { X := S.total
          str := S.totalStruct
          gam := S.totalComparison
          hsq := fun _ => S.isPullback_base
          hgam := fun _ => S.hom_comparison }
      down := S.down
      cen := S.totalCenter
      hblow := fun _ => S.isBlowup_down
      hpb := fun _ => S.isPullback_sq
      hcen := fun _ => S.center_comap.symm }
  else
    { next :=
        { X := t.schemeAt (n + 1)
          str := t.projectionToBase (n + 1) ≫ g
          gam := 𝟙 (t.schemeAt (n + 1))
          hsq := fun hle => absurd (Nat.lt_of_succ_le hle) hn
          hgam := fun hle => absurd (Nat.lt_of_succ_le hle) hn }
      down := t.transitionMapSucc n ≫ P.gam
      cen := ⊤
      hblow := fun hlt => absurd hlt hn
      hpb := fun hlt => absurd hlt hn
      hcen := fun hlt => absurd hlt hn }

private def descendedSchemeDataAt {W Y : Scheme.{u}} (g : W ⟶ Y) [AlgebraicGeometry.Flat g]
    [AlgebraicGeometry.QuasiCompact g] (t : SequenceOfBlowups W) (D : SequenceOfBlowupsDescentDatum g t)
    (n : ℕ) : DescendedSchemeData g t D n :=
  Nat.rec (motive := fun m => DescendedSchemeData g t D m) (descendedSchemeDataZero g t D)
    (fun m P => (descendedBlowupAt g t D m P).next) n

private def descendedSchemeAt {W Y : Scheme.{u}} (g : W ⟶ Y) [AlgebraicGeometry.Flat g]
    [AlgebraicGeometry.QuasiCompact g] (t : SequenceOfBlowups W) (D : SequenceOfBlowupsDescentDatum g t)
    (n : ℕ) : Scheme.{u} :=
  (descendedSchemeDataAt g t D n).X

private def descendedBlowupMorphism {W Y : Scheme.{u}} (g : W ⟶ Y) [AlgebraicGeometry.Flat g]
    [AlgebraicGeometry.QuasiCompact g] (t : SequenceOfBlowups W) (D : SequenceOfBlowupsDescentDatum g t)
    (n : ℕ) : descendedSchemeAt g t D (n + 1) ⟶ descendedSchemeAt g t D n :=
  (descendedBlowupAt g t D n (descendedSchemeDataAt g t D n)).down

private def descendedTower {W Y : Scheme.{u}} (g : W ⟶ Y) [AlgebraicGeometry.Flat g]
    [AlgebraicGeometry.QuasiCompact g] (t : SequenceOfBlowups W) (D : SequenceOfBlowupsDescentDatum g t) :
    ℕᵒᵖ ⥤ Scheme.{u} :=
  Functor.ofOpSequence (descendedBlowupMorphism g t D)

private def descendedSequenceOfBlowups {W Y : Scheme.{u}} (g : W ⟶ Y) [AlgebraicGeometry.Flat g]
    [AlgebraicGeometry.QuasiCompact g] (t : SequenceOfBlowups W) (D : SequenceOfBlowupsDescentDatum g t) :
    SequenceOfBlowups Y where
  length := t.length
  tower := descendedTower g t D
  isoZero := Iso.refl Y
  center := fun i => (descendedBlowupAt g t D i (descendedSchemeDataAt g t D i)).cen
  isBlowup := fun i hi => by
    have hmap : (descendedTower g t D).map (homOfLE (Nat.le_succ i)).op = descendedBlowupMorphism g t D i :=
      Functor.ofOpSequence_map_homOfLE_succ (descendedBlowupMorphism g t D) i
    rw [hmap]
    exact (descendedBlowupAt g t D i (descendedSchemeDataAt g t D i)).hblow hi

private theorem exists_isStrictPullbackSequenceOfBlowups_of_descentDatum {W Y : Scheme.{u}} (g : W ⟶ Y)
    [AlgebraicGeometry.Flat g] [AlgebraicGeometry.QuasiCompact g] (t : SequenceOfBlowups W)
    (D : SequenceOfBlowupsDescentDatum g t) : ∃ s : SequenceOfBlowups Y, IsStrictPullbackBlowupSeq g t s := by
  refine ⟨descendedSequenceOfBlowups g t D, rfl, fun i _ => (descendedSchemeDataAt g t D i).gam, ?_, ?_, ?_⟩
  · show (descendedSchemeDataAt g t D 0).gam ≫ (descendedSequenceOfBlowups g t D).isoZero.hom = t.isoZero.hom ≫ g
    have h0 : (descendedSchemeDataAt g t D 0).gam = t.projectionToBase 0 ≫ g := rfl
    rw [h0, SequenceOfBlowups.projectionToBase_zero]
    exact Category.comp_id _
  · intro i hi
    have hmap : (descendedSequenceOfBlowups g t D).transitionMapSucc i = descendedBlowupMorphism g t D i := by
      rw [SequenceOfBlowups.blowupMorphism_eq_transitionMap, SequenceOfBlowups.transitionMap_def]
      exact Functor.ofOpSequence_map_homOfLE_succ (descendedBlowupMorphism g t D) i
    rw [hmap]
    exact (descendedBlowupAt g t D i (descendedSchemeDataAt g t D i)).hpb hi
  · intro i hi
    exact (descendedBlowupAt g t D i (descendedSchemeDataAt g t D i)).hcen hi

theorem exists_isStrictPullback_of_isomorphic_baseChange {W Y : Scheme.{u}}
    (g : W ⟶ Y) [AlgebraicGeometry.Flat g] [AlgebraicGeometry.QuasiCompact g] (t : SequenceOfBlowups W)
    (h : (t.baseChange (pullback.fst g g)).Isomorphic (t.baseChange (pullback.snd g g))) :
    ∃ s : SequenceOfBlowups Y, IsStrictPullbackBlowupSeq g t s := by
  obtain ⟨-, e, hzero, hstep, hcen⟩ := h
  have hlp : (t.baseChange (pullback.fst g g)).length = t.length :=
    t.baseChange_length (pullback.fst g g)
  refine exists_isStrictPullbackSequenceOfBlowups_of_descentDatum g t
    { iso := fun i hi => e i (by rw [hlp]; exact hi)
      comp_fst := ?_
      center_comap := ?_
      comp_step := ?_ }
  · intro i hi
    have key := SequenceOfBlowups.iso_hom_comp_projectionToBase (t.baseChange (pullback.fst g g))
      (t.baseChange (pullback.snd g g)) _ e hstep hzero i (by rw [hlp]; exact hi)
    rw [baseChange_projectionToBase_eq_fst, baseChange_projectionToBase_eq_fst] at key
    exact key
  · intro i hi
    have key := hcen i (by rw [hlp]; exact hi)
    rw [SequenceOfBlowups.baseChange_center, SequenceOfBlowups.baseChange_center] at key
    exact key
  · intro i hi
    have key := hstep i (by rw [hlp]; exact hi)
    rw [SequenceOfBlowups.baseChange_blowupMorphism, SequenceOfBlowups.baseChange_blowupMorphism] at key
    exact key

end FunctorialResolution.EmbeddedResolution
end
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.InducedRuleFieldExtension
section
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem notMem_support_comap_top {A C : Scheme.{u}} (h : A ⟶ C) (x : ↥A) :
    x ∉ ((⊤ : C.IdealSheafData).comap h).support := by
  rw [Scheme.IdealSheafData.comap_top, Scheme.IdealSheafData.support_top]
  intro hx
  have hx' : x ∈ ((⊥ : TopologicalSpace.Closeds ↥A) : Set ↥A) := hx
  simp at hx'

theorem center_ne_top_of_isPullbackSequenceOfBlowups_id {X : Scheme.{u}} (s : SequenceOfBlowups X)
    (h : IsPullbackBlowupSequence (𝟙 X) s s) :
    ∀ i : ℕ, i < s.length → s.center i ≠ ⊤ := by
  obtain ⟨r, _e, _hlt, hmono, htop, hsupp, -⟩ := h
  have hgeid : ∀ i : ℕ, i ≤ s.length → i ≤ r i := by
    intro i
    induction i with
    | zero => intro _; exact Nat.zero_le _
    | succ n ih =>
      intro hn
      have h1 : r n < r (n + 1) := hmono n (n + 1) hn (Nat.lt_succ_self n)
      have h2 : n ≤ r n := ih (Nat.le_of_succ_le hn)
      omega
  have hleid : ∀ d i : ℕ, i + d = s.length → r i + d ≤ s.length := by
    intro d
    induction d with
    | zero =>
      intro i hi
      have hii : i = s.length := by omega
      subst hii
      rw [htop]
      omega
    | succ m ih =>
      intro i hi
      have hi1 : (i + 1) + m = s.length := by omega
      have h2 := ih (i + 1) hi1
      have h3 : r i < r (i + 1) := hmono i (i + 1) (by omega) (Nat.lt_succ_self i)
      omega
  have hrid : ∀ i : ℕ, i ≤ s.length → r i = i := by
    intro i hi
    have h1 := hgeid i hi
    have h2 := hleid (s.length - i) i (by omega)
    omega
  intro i hi hc
  obtain ⟨x, hx⟩ := (hsupp i hi).mpr ⟨i, hi, hrid i hi.le⟩
  rw [hc] at hx
  exact notMem_support_comap_top _ x hx

theorem AffineResolutionRule.center_ne_top (B : AffineResolutionRule.{u}) (hB : IsCompatibleWithOpenImmersions B)
    (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y] :
    ∀ i : ℕ, i < (B k Y p).length → (B k Y p).center i ≠ ⊤ :=
  center_ne_top_of_isPullbackSequenceOfBlowups_id (B k Y p) (hB k Y Y p p (𝟙 Y) (Category.id_comp p))

theorem inducedRuleCompatibleWithFieldExtension (B : AffineResolutionRule.{u}) : InducedRuleCompatibleWithFieldExtension B := by
  intro hoi hfe F hF k _ _ X f _ _ _ K _ _ _ _
  obtain ⟨W, c, g, hWaff, hWred, hqlft, hqqc, hcet, hcsur, hYaff, hYred, hglft, hgqc, hget,
    hgsur, hgstruct, hgproj⟩ := exists_etale_surjective_affine_cover_baseChange X f K
  have := hWaff
  have := hWred
  have := hqlft
  have := hqqc
  have := hcet
  have := hcsur
  have := hYaff
  have := hYred
  have := hglft
  have := hgqc
  have := hget
  have := hgsur
  have h0 : IsStrictPullbackBlowupSeq (baseChangeProjection f K)
      ((F k X f).baseChange (baseChangeProjection f K)) (F k X f) :=
    isStrictPullbackSequenceOfBlowups_baseChange _ _
  have hw : IsStrictPullbackBlowupSeq g
      (((F k X f).baseChange (baseChangeProjection f K)).baseChange g)
      ((F k X f).baseChange (baseChangeProjection f K)) :=
    isStrictPullbackSequenceOfBlowups_baseChange _ _
  have hcomp := hw.comp h0
  rw [hgproj] at hcomp
  have htW : IsStrictPullbackBlowupSeq c (B k W (c ≫ f)) (F k X f) :=
    hF k X f W (c ≫ f) c rfl AlgebraicGeometry.Surjective.surj
  have htK : IsStrictPullbackBlowupSeq (baseChangeProjection (c ≫ f) K)
      (B K (baseChange (c ≫ f) K) (baseChangeToSpec (c ≫ f) K)) (B k W (c ≫ f)) :=
    hfe k W (c ≫ f) K
  have hEqw := hcomp.isomorphic (htK.comp htW)
  have hntop := AffineResolutionRule.center_ne_top B hoi K (baseChange (c ≫ f) K)
      (baseChangeToSpec (c ≫ f) K)
  have hEq := (SequenceOfBlowups.Isomorphic.withoutIsoBlowups hEqw).trans (SequenceOfBlowups.withoutIsoBlowups_isomorphic_self _ hntop)
  have h₂ : IsStrictPullbackBlowupSeq g (B K (baseChange (c ≫ f) K) (baseChangeToSpec (c ≫ f) K))
      (F K (baseChange f K) (baseChangeToSpec f K)) :=
    hF K (baseChange f K) (baseChangeToSpec f K) (baseChange (c ≫ f) K)
      (baseChangeToSpec (c ≫ f) K) g hgstruct AlgebraicGeometry.Surjective.surj
  have hdesc := IsStrictPullbackBlowupSeq.isomorphic_of_isomorphic hw.withoutIsoBlowups h₂ hEq
  exact h0.isPullbackSequenceOfBlowups_withoutIsoBlowups.of_isomorphic hdesc

end FunctorialResolution.EmbeddedResolution

end
end

-- bundled from Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.StrictPullbackCriterion
section
universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem apply_eq_self_of_strictMono_of_surjective (L L' : ℕ) (r : ℕ → ℕ)
    (h1 : ∀ i, i < L' → r i < L)
    (h2 : ∀ i j, j ≤ L' → i < j → r i < r j)
    (h3 : r L' = L)
    (hsurj : ∀ i, i < L → ∃ j, j < L' ∧ r j = i) :
    ∀ i, i ≤ L' → r i = i := by
  have hA : ∀ i, i ≤ L' → i ≤ r i := by
    intro i
    induction i with
    | zero => intro _; exact Nat.zero_le _
    | succ n ih =>
      intro hn
      have hstep := h2 n (n + 1) hn (Nat.lt_succ_self n)
      have hprev := ih (Nat.le_of_succ_le hn)
      omega
  have key : ∀ i, (∀ j, j < i → j ≤ L' → r j ≤ j) → i ≤ L' → r i ≤ i := by
    intro i ih hi
    by_contra hcon
    have hlt : i < r i := by omega
    have hle : r i ≤ L := by
      rcases Nat.lt_or_ge i L' with hc | hc
      · exact le_of_lt (h1 i hc)
      · have hEq : i = L' := le_antisymm hi hc
        subst hEq
        exact le_of_eq h3
    obtain ⟨j, hjL, hrj⟩ := hsurj i (by omega)
    have hjle : j ≤ r j := hA j (le_of_lt hjL)
    rcases Nat.lt_or_ge j i with hji | hji
    · have hij := ih j hji (le_of_lt hjL)
      omega
    · have hEq : j = i := by omega
      subst hEq
      omega
  have hB' : ∀ n i, i ≤ n → i ≤ L' → r i ≤ i := by
    intro n
    induction n with
    | zero =>
      intro i hi hiL
      exact key i (fun j hj _ => by omega) hiL
    | succ n ih =>
      intro i hi hiL
      exact key i (fun j _ hjL => ih j (by omega) hjL) hiL
  intro i hi
  exact le_antisymm (hB' i i le_rfl hi) (hA i hi)

private theorem isPullback_pullbackTransitionMap_comp_transitionMap {X X' : Scheme.{u}} (s : SequenceOfBlowups X)
    (φ : X' ⟶ X) (i j j' : ℕ) (hj : j = i) (hj' : j' = i + 1) (hjj' : j ≤ j')
    (hij : i ≤ j) (hij' : i + 1 ≤ j') :
    IsPullback (pullback.snd φ (s.projectionToBase j') ≫ s.transitionMap hij')
      (s.pullbackTransitionMap φ hjj') (s.transitionMapSucc i)
      (pullback.snd φ (s.projectionToBase j) ≫ s.transitionMap hij) := by
  subst hj
  subst hj'
  simp only [SequenceOfBlowups.transitionMap_self_eq_id, Category.comp_id]
  exact s.isPullback_pullbackTransitionMap φ _

private theorem center_comap_eq_comap_comp_transitionMap_of_eq {X W V : Scheme.{u}} (s : SequenceOfBlowups X) {i j : ℕ}
    (hij : i ≤ j) (hji : j = i) (f : W ⟶ V) (g : V ⟶ s.schemeAt j) :
    (s.center j).comap (f ≫ g) = (s.center i).comap (f ≫ g ≫ s.transitionMap hij) := by
  subst hji
  rw [SequenceOfBlowups.transitionMap_self_eq_id, Category.comp_id]

private theorem support_nonempty_of_ne_top {Y : Scheme.{u}} (I : Y.IdealSheafData) (h : I ≠ ⊤) :
    ((I.support : Set ↥Y)).Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  intro he
  apply h
  have hbot : I.support = ⊥ := SetLike.ext' (by rw [he]; rfl)
  exact (Scheme.IdealSheafData.support_eq_bot_iff I).mp hbot

theorem support_comap_center_nonempty_of_mem_range {X X' : Scheme.{u}} (φ : X' ⟶ X) (s : SequenceOfBlowups X)
    (hne : ∀ i : ℕ, i < s.length → (((s.center i).support : Set ↥(s.schemeAt i))).Nonempty)
    (hran : ∀ i : ℕ, i < s.length → ∀ x ∈ ((s.center i).support : Set ↥(s.schemeAt i)),
      (s.projectionToBase i).base x ∈ Set.range (⇑φ.base)) :
    ∀ i : ℕ, i < s.length →
      ((((s.center i).comap (pullback.snd φ (s.projectionToBase i))).support :
        Set ↥(pullback φ (s.projectionToBase i)))).Nonempty := by
  intro i hi
  obtain ⟨x, hx⟩ := hne i hi
  obtain ⟨y, hy⟩ := hran i hi x hx
  obtain ⟨z, hz1, hz2⟩ :=
    Scheme.Pullback.exists_preimage_pullback (f := φ) (g := s.projectionToBase i) y x hy
  refine ⟨z, ?_⟩
  have hmem : (pullback.snd φ (s.projectionToBase i)) z ∈ ((s.center i).support : Set ↥(s.schemeAt i)) := by
    rw [hz2]; exact hx
  rw [Scheme.IdealSheafData.support_comap]
  exact hmem

theorem IsPullbackBlowupSequence.isStrictPullback_of_support_comap_center_nonempty {X X' : Scheme.{u}} {φ : X' ⟶ X} {s' : SequenceOfBlowups X'}
    {s : SequenceOfBlowups X} (h : IsPullbackBlowupSequence φ s' s)
    (hhit : ∀ i : ℕ, i < s.length →
      ((((s.center i).comap (pullback.snd φ (s.projectionToBase i))).support :
        Set ↥(pullback φ (s.projectionToBase i)))).Nonempty) :
    IsStrictPullbackBlowupSeq φ s' s := by
  obtain ⟨r, e, h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hsurj : ∀ i, i < s.length → ∃ j, j < s'.length ∧ r j = i := by
    intro i hi
    obtain ⟨x, hx⟩ := hhit i hi
    exact (h4 i hi).mp ⟨x, hx⟩
  have hid : ∀ i, i ≤ s'.length → r i = i :=
    apply_eq_self_of_strictMono_of_surjective s.length s'.length r h1 h2 h3 hsurj
  have hlen : s'.length = s.length := by
    have hfin := hid s'.length le_rfl
    omega
  refine ⟨hlen, fun i hi => (e i hi).hom ≫ pullback.snd φ (s.projectionToBase (r i)) ≫
      s.transitionMap (le_of_eq (hid i hi).symm), ?_, ?_, ?_⟩
  · have h0 := h5 0 (Nat.zero_le s'.length)
    simp only [Category.assoc]
    rw [← s.projectionToBase_zero, s.transitionMap_comp_projectionToBase, ← pullback.condition,
      ← Category.assoc, h0, s'.projectionToBase_zero]
  · intro i hi
    have hile : i ≤ s'.length := le_of_lt hi
    have hi1 : i + 1 ≤ s'.length := hi
    have hrle : r i ≤ r (i + 1) := le_of_lt (h2 i (i + 1) hi1 (Nat.lt_succ_self i))
    have sq1 : IsPullback (e (i + 1) hi).hom (s'.transitionMapSucc i) (s.pullbackTransitionMap φ hrle)
        (e i hile).hom := by
      refine IsPullback.of_horiz_isIso ⟨?_⟩
      exact (h6 i hi hrle).symm
    have sq2 : IsPullback
        (pullback.snd φ (s.projectionToBase (r (i + 1))) ≫ s.transitionMap (le_of_eq (hid (i + 1) hi1).symm))
        (s.pullbackTransitionMap φ hrle) (s.transitionMapSucc i)
        (pullback.snd φ (s.projectionToBase (r i)) ≫ s.transitionMap (le_of_eq (hid i hile).symm)) :=
      isPullback_pullbackTransitionMap_comp_transitionMap s φ i (r i) (r (i + 1)) (hid i hile) (hid (i + 1) hi1) hrle
        (le_of_eq (hid i hile).symm) (le_of_eq (hid (i + 1) hi1).symm)
    exact sq1.paste_horiz sq2
  · intro i hi
    have hile : i ≤ s'.length := le_of_lt hi
    rw [h7 i hi]
    exact center_comap_eq_comap_comp_transitionMap_of_eq s (le_of_eq (hid i hile).symm) (hid i hile) (e i hile).hom
      (pullback.snd φ (s.projectionToBase (r i)))

theorem IsPullbackBlowupSequence.isStrictPullback_of_surjective {X X' : Scheme.{u}} {φ : X' ⟶ X}
    [AlgebraicGeometry.Surjective φ] {s' : SequenceOfBlowups X'} {s : SequenceOfBlowups X}
    (h : IsPullbackBlowupSequence φ s' s) (hc : ∀ i : ℕ, i < s.length → s.center i ≠ ⊤) :
    IsStrictPullbackBlowupSeq φ s' s := by
  refine h.isStrictPullback_of_support_comap_center_nonempty ?_
  refine support_comap_center_nonempty_of_mem_range φ s
    (fun i hi => support_nonempty_of_ne_top (s.center i) (hc i hi)) ?_
  intro i _ x _
  exact φ.surjective _

end FunctorialResolution.EmbeddedResolution
end
end

