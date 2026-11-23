module

public import Mathlib
public import Development.EtaleCohomology.EtaleSheaves.Bundle0013
public import Development.EtaleCohomology.EtaleSheaves.ProperLineCovers.CoverPf
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0029
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0016
public import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0038
public import Development.EtaleCohomology.EtaleSheaves.Bundle0076

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CurveCohomologyKilledByFiniteCover
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace UpperTheory.curve_cohomology_killed_by_finite_cover

inductive AffU {C : Scheme.{0}} : ℕ → C.Opens → Prop
  | one (U : C.Opens) : IsAffineOpen U → Nonempty U → AffU 0 U
  | succ {k : ℕ} {W : C.Opens} (U : C.Opens) : AffU k W → IsAffineOpen U → Nonempty U → AffU (k + 1) (W ⊔ U)

theorem AffU.pre {C C' : Scheme.{0}} (γ : C' ⟶ C) [IsFinite γ] [Surjective γ] {k : ℕ} {W : C.Opens}
    (h : AffU k W) : AffU k (γ ⁻¹ᵁ W) := by
  induction h with
  | one U hU hn =>
    refine AffU.one _ (hU.preimage γ) ?_
    obtain ⟨⟨x, hx⟩⟩ := hn
    obtain ⟨y, rfl⟩ := Surjective.surj (f := γ) x
    exact ⟨⟨y, hx⟩⟩
  | @succ k W U h hU hn ih =>
    have e : γ ⁻¹ᵁ (W ⊔ U) = γ ⁻¹ᵁ W ⊔ γ ⁻¹ᵁ U := by
      ext x
      simp
    rw [e]
    refine AffU.succ _ ih (hU.preimage γ) ?_
    obtain ⟨⟨x, hx⟩⟩ := hn
    obtain ⟨y, rfl⟩ := Surjective.surj (f := γ) x
    exact ⟨⟨y, hx⟩⟩

theorem AffU.inter {Ω : Type} [Field Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω) (hc : IsCurve c) {k : ℕ} {W V : C.Opens}
    (h : AffU k W) (hV : IsAffineOpen V) (hn : Nonempty V) : AffU k (W ⊓ V) := by
  induction h with
  | one U hU hn' =>
    refine AffU.one _ (CurveCut.CoverPf.inf_affine c hc hU hV) ?_
    obtain ⟨⟨a, ha⟩⟩ := hn'
    obtain ⟨⟨b, hb⟩⟩ := hn
    obtain ⟨x, hx⟩ := CurveCut.CoverPf.inf_nonempty c hc (U := U) (V := V) ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨⟨x, hx⟩⟩
  | @succ k W U h hU hn' ih =>
    rw [inf_sup_right]
    refine AffU.succ _ ih (CurveCut.CoverPf.inf_affine c hc hU hV) ?_
    obtain ⟨⟨a, ha⟩⟩ := hn'
    obtain ⟨⟨b, hb⟩⟩ := hn
    obtain ⟨x, hx⟩ := CurveCut.CoverPf.inf_nonempty c hc (U := U) (V := V) ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨⟨x, hx⟩⟩

theorem exists_affU {C : Scheme.{0}} [CompactSpace C] [Nonempty C] : ∃ k, AffU k (⊤ : C.Opens) := by
  classical
  let U : C → C.Opens := fun x => (C.affineCover.f (C.affineCover.idx x)).opensRange
  have hU : ∀ x, IsAffineOpen (U x) := fun x => isAffineOpen_opensRange _
  have hx : ∀ x, x ∈ U x := fun x => C.affineCover.covers x
  have hne : ∀ x, Nonempty (U x) := fun x => ⟨⟨x, hx x⟩⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (U x : Set C))
    (fun x => (U x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩)
  have key : ∀ s : Finset C, s.Nonempty → ∃ k, AffU k (s.sup U) := by
    intro s hs
    induction hs using Finset.Nonempty.cons_induction with
    | singleton a =>
      refine ⟨0, ?_⟩
      rw [Finset.sup_singleton]
      exact AffU.one _ (hU a) (hne a)
    | cons a s ha hs ih =>
      obtain ⟨k, hk⟩ := ih
      refine ⟨k + 1, ?_⟩
      rw [Finset.sup_cons, sup_comm]
      exact AffU.succ _ hk (hU a) (hne a)
  obtain ⟨x0⟩ := ‹Nonempty C›
  have htne : t.Nonempty := by
    have := ht (Set.mem_univ x0)
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, _⟩ := this
    exact ⟨i, hi⟩
  obtain ⟨k, hk⟩ := key t htne
  have htop : t.sup U = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have := ht (Set.mem_univ y)
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, hy⟩ := this
    exact (Finset.le_sup (f := U) hi) hy
  exact ⟨k, htop ▸ hk⟩

theorem pl_eq_zero_of_iso (q : ℕ) (i : ℤ) {Y X : Scheme.{0}} (e : Y ⟶ X) [IsIso e] (m : ℤ)
    (x : Ht q (sch.obj X) m i) (h : pl q i e m x = 0) : x = 0 := by
  have h2 := pl_comp q i (inv e) e m x
  rw [h, map_zero, IsIso.inv_hom_id] at h2
  simpa [pl, pull_id] using h2

theorem AffU.nonempty {C : Scheme.{0}} {k : ℕ} {W : C.Opens} (h : AffU k W) : Nonempty W := by
  induction h with
  | one U _ hn => exact hn
  | @succ k W U h hU hn ih =>
    obtain ⟨⟨x, hx⟩⟩ := ih
    exact ⟨⟨x, (le_sup_left : W ≤ W ⊔ U) hx⟩⟩

theorem res_sq {T S : Scheme.{0}} (f : T ⟶ S) {A B : S.Opens} (h : A ≤ B) (h' : f ⁻¹ᵁ A ≤ f ⁻¹ᵁ B) :
    T.homOfLE h' ≫ (f ∣_ B) = (f ∣_ A) ≫ S.homOfLE h := by
  rw [← cancel_mono B.ι]
  simp [morphismRestrict_ι]

theorem pl_res_sq (q : ℕ) (i m : ℤ) {T S : Scheme.{0}} (f : T ⟶ S) {A B : S.Opens} (h : A ≤ B) (h' : f ⁻¹ᵁ A ≤ f ⁻¹ᵁ B)
    (x : Ht q (sch.obj B.toScheme) m i) :
    pl q i (T.homOfLE h') m (pl q i (f ∣_ B) m x) = pl q i (f ∣_ A) m (pl q i (S.homOfLE h) m x) := by
  rw [← pl_comp, ← pl_comp, res_sq f h h']

theorem killAff (hy : Hyps) (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (hq : IsUnit (q : Ω))
    {C : Scheme.{0}} (c : C ⟶ Sp Ω) (hc : IsCurve c) (U : C.Opens) (hU : IsAffineOpen U) (hn : Nonempty U)
    (m i : ℤ) (hm : 0 < m) (x : Ht q (sch.obj U.toScheme) m i) :
    ∃ (C' : Scheme.{0}) (γ : C' ⟶ C), IsCurve (γ ≫ c) ∧ Surjective γ ∧ IsFinite γ ∧ pl q i (γ ∣_ U) m x = 0 := by
  haveI : IsIntegral C := hc.1
  haveI : Nonempty U := hn
  haveI := functionField_isFractionRing_of_isAffineOpen C U hU
  have hqU : IsUnit (q : Γ(C, U)) := by
    have := hq.map ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv ≫ c.appLE ⊤ U (by simp)).hom
    simpa using this
  set x0 : Ht q (sp Γ(C, U)) m i := pl q i hU.isoSpec.inv m x with hx0
  obtain ⟨F, _, _, _, hST, hFD, hF⟩ := UpperTheory.exists_finite_ext_pullback_integralClosure_eq_zero hy q Γ(C, U) C.functionField hqU m i hm x0
  obtain ⟨C', γ, hγc, hγs, hγf, hγ⟩ := UpperTheory.exists_finite_surjective_curve_cover_of_functionField_extension Ω c hc hc.1 F
  obtain ⟨e, he⟩ := hγ U hU hn inferInstance hST
  refine ⟨C', γ, hγc, hγs, hγf, ?_⟩
  have hx : x = pl q i hU.isoSpec.hom m x0 := by
    rw [hx0, ← pl_comp, Iso.hom_inv_id]
    simp [pl, pull_id]
  have h0 : pl q i (Spec.map (CommRingCat.ofHom (algebraMap Γ(C, U) (integralClosure Γ(C, U) F)))) m x0 = 0 := hF
  rw [hx, ← pl_comp, he, pl_comp, h0, map_zero]

set_option maxHeartbeats 1000000 in
theorem kill (hy : Hyps) (hH0 : H0TwistOverClosedField) (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (hq : IsUnit (q : Ω)) (k : ℕ) :
    ∀ {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c → ∀ W : C.Opens, AffU k W → ∀ m i : ℤ, 0 < m →
    ∀ x : Ht q (sch.obj W.toScheme) m i,
    ∃ (C' : Scheme.{0}) (γ : C' ⟶ C), IsCurve (γ ≫ c) ∧ Surjective γ ∧ IsFinite γ ∧ pl q i (γ ∣_ W) m x = 0 := by
  have pm : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) {A B : Y.Opens}, A ≤ B → f ⁻¹ᵁ A ≤ f ⁻¹ᵁ B :=
    fun f _ _ h _ hy => h hy
  induction k with
  | zero =>
    intro C c hc W hW m i hm x
    cases hW with
    | one _ hU hn => exact killAff hy q Ω hq c hc _ hU hn m i hm x
  | succ k ih =>
    intro C c hc W' hW' m i hm x
    cases hW' with
    | @succ _ W U hW hU hn =>
      obtain ⟨n, rfl⟩ : ∃ n : ℤ, m = n + 1 := ⟨m - 1, by ring⟩
      obtain ⟨C1, γ1, hc1, hs1, hf1, h1⟩ := ih c hc W hW (n + 1) i hm
        (pl q i (C.homOfLE (le_sup_left : W ≤ W ⊔ U)) (n + 1) x)
      haveI := hs1
      haveI := hf1
      obtain ⟨C2, γ2, hc2, hs2, hf2, h2⟩ := killAff hy q Ω hq (γ1 ≫ c) hc1 (γ1 ⁻¹ᵁ U) (hU.preimage γ1)
        (AffU.nonempty (AffU.pre γ1 (AffU.one U hU hn))) (n + 1) i hm
        (pl q i (C1.homOfLE (pm γ1 (le_sup_right : U ≤ W ⊔ U))) (n + 1) (pl q i (γ1 ∣_ (W ⊔ U)) (n + 1) x))
      haveI := hs2
      haveI := hf2
      have hcγ : IsCurve ((γ2 ≫ γ1) ≫ c) := by simpa only [Category.assoc] using hc2
      have hW2 : AffU k ((γ2 ≫ γ1) ⁻¹ᵁ W ⊓ (γ2 ≫ γ1) ⁻¹ᵁ U) := AffU.pre (γ2 ≫ γ1) (AffU.inter c hc hW hU hn)
      have hA : pl q i (C2.homOfLE (pm (γ2 ≫ γ1) (le_sup_left : W ≤ W ⊔ U))) (n + 1)
          (pl q i ((γ2 ≫ γ1) ∣_ (W ⊔ U)) (n + 1) x) = 0 := by
        have e2 := pl_res_sq q i (n + 1) (γ2 ≫ γ1) (le_sup_left : W ≤ W ⊔ U) (pm _ le_sup_left) x
        have e3 := pl_comp q i (γ2 ∣_ (γ1 ⁻¹ᵁ W)) (γ1 ∣_ W) (n + 1)
          (pl q i (C.homOfLE (le_sup_left : W ≤ W ⊔ U)) (n + 1) x)
        rw [h1, map_zero, ← morphismRestrict_comp] at e3
        exact e2.trans e3
      have hB : pl q i (C2.homOfLE (pm (γ2 ≫ γ1) (le_sup_right : U ≤ W ⊔ U))) (n + 1)
          (pl q i ((γ2 ≫ γ1) ∣_ (W ⊔ U)) (n + 1) x) = 0 := by
        have e1 := pl_res_sq q i (n + 1) γ2 (pm γ1 (le_sup_right : U ≤ W ⊔ U)) (pm γ2 (pm γ1 le_sup_right))
          (pl q i (γ1 ∣_ (W ⊔ U)) (n + 1) x)
        rw [h2, ← pl_comp q i (γ2 ∣_ (γ1 ⁻¹ᵁ (W ⊔ U))) (γ1 ∣_ (W ⊔ U)), ← morphismRestrict_comp] at e1
        exact e1
      obtain ⟨y, hyv⟩ := UpperTheory.exists_mayerVietoris_preimage_of_restrictions_vanish (ZMod q) (tw q i) ((γ2 ≫ γ1) ⁻¹ᵁ W) ((γ2 ≫ γ1) ⁻¹ᵁ U) n
        (pl q i ((γ2 ≫ γ1) ∣_ (W ⊔ U)) (n + 1) x) hA hB
      have fin : ∀ (C3 : Scheme.{0}) (f : C3 ⟶ C2), IsCurve (f ≫ (γ2 ≫ γ1) ≫ c) → Surjective f → IsFinite f →
          pl q i (f ∣_ ((γ2 ≫ γ1) ⁻¹ᵁ W ⊔ (γ2 ≫ γ1) ⁻¹ᵁ U)) (n + 1)
            (pl q i ((γ2 ≫ γ1) ∣_ (W ⊔ U)) (n + 1) x) = 0 →
          ∃ (C' : Scheme.{0}) (γ : C' ⟶ C), IsCurve (γ ≫ c) ∧ Surjective γ ∧ IsFinite γ ∧
            pl q i (γ ∣_ (W ⊔ U)) (n + 1) x = 0 := by
        intro C3 f hc3 hs3 hf3 h3
        haveI := hs3
        haveI := hf3
        refine ⟨C3, f ≫ γ2 ≫ γ1, by simpa only [Category.assoc] using hc3, inferInstance, inferInstance, ?_⟩
        rw [morphismRestrict_comp f (γ2 ≫ γ1) (W ⊔ U)]
        exact (pl_comp q i (f ∣_ ((γ2 ≫ γ1) ⁻¹ᵁ (W ⊔ U))) ((γ2 ≫ γ1) ∣_ (W ⊔ U)) (n + 1) x).trans h3
      rcases (show (0 : ℤ) < n ∨ n = 0 by omega) with hn0 | rfl
      · obtain ⟨C3, f, hc3, hs3, hf3, h3⟩ := ih ((γ2 ≫ γ1) ≫ c) hcγ _ hW2 n i hn0 y
        refine fin C3 f (by simpa only [Category.assoc] using hc3) hs3 hf3 ?_
        exact hyv f 0 0 (by rw [map_zero, map_zero, sub_zero]; exact h3)
      · haveI : IsIntegral C2 := hc2.1
        haveI : Nonempty (((γ2 ≫ γ1) ⁻¹ᵁ W ⊓ (γ2 ≫ γ1) ⁻¹ᵁ U : C2.Opens)) := AffU.nonempty hW2
        obtain ⟨z, hz⟩ := ((hH0 hy q Ω hq i).2
          (X := ((γ2 ≫ γ1) ⁻¹ᵁ W ⊓ (γ2 ≫ γ1) ⁻¹ᵁ U : C2.Opens).toScheme)
          (Scheme.Opens.ι _ ≫ (γ2 ≫ γ1) ≫ c)).2 y
        refine fin C2 (𝟙 C2) (by rw [Category.id_comp]; exact hcγ) inferInstance inferInstance ?_
        refine hyv (𝟙 C2) (pl q i ((𝟙 C2 ⁻¹ᵁ ((γ2 ≫ γ1) ⁻¹ᵁ W)).ι ≫ (γ2 ≫ γ1) ≫ c) 0 z) 0 ?_
        rw [map_zero, sub_zero, ← hz]
        change pl q i _ 0 (pl q i _ 0 z) = pl q i _ 0 (pl q i _ 0 z)
        rw [← pl_comp, ← pl_comp, morphismRestrict_ι_assoc, Scheme.homOfLE_ι_assoc, Category.id_comp]

end UpperTheory.curve_cohomology_killed_by_finite_cover

theorem UpperTheory.Cb.curve_cohomology_killed_by_finite_cover :
    LateralTheory.E.E4.H0TwistOverClosedField → LateralTheory.E.LeafKillCut.LeafOne := by
  intro hH0 hy q _ Ω _ _ hq C c hc m i hm x
  have hI := hc.1
  have hP := hc.2.1
  haveI : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace c
  obtain ⟨k, hk⟩ := UpperTheory.curve_cohomology_killed_by_finite_cover.exists_affU (C := C)
  obtain ⟨C', γ, h1, h2, h3, h4⟩ := UpperTheory.curve_cohomology_killed_by_finite_cover.kill hy hH0 q Ω hq k c hc ⊤ hk m i hm (pl q i (⊤ : C.Opens).ι m x)
  refine ⟨C', γ, h1, h2, ?_⟩
  rw [← pl_comp] at h4
  rw [morphismRestrict_ι, pl_comp] at h4
  have hι : ∀ V : C'.Opens, V = ⊤ → IsIso V.ι := by
    rintro _ rfl
    rw [← Scheme.topIso_hom]
    infer_instance
  haveI := hι (γ ⁻¹ᵁ (⊤ : C.Opens)) rfl
  exact UpperTheory.curve_cohomology_killed_by_finite_cover.pl_eq_zero_of_iso q i ((γ ⁻¹ᵁ (⊤ : C.Opens)).ι) m _ h4

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.NeighbourhoodShrinkingOfObstructionExactNatural
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.Cb.MorphismProjectionLaws
open LateralTheory.E.E4 LateralTheory.E.EtaleTopologySheaves LateralTheory.E.SecondDegreeKilling LateralTheory.E.Bridge_yfiPf

variable {B W Y S T T' T'' : Scheme.{0}}

private def mY (p : Y ⟶ B) (u : T ⟶ B) (u' : T' ⟶ B) (f : T ⟶ T') (h : f ≫ u' = u) :
    pullback p u ⟶ pullback p u' :=
  pullback.map p u p u' (𝟙 Y) f (𝟙 B) (by simp) (by simp [h])

private lemma mY_snd (p : Y ⟶ B) (u : T ⟶ B) (u' : T' ⟶ B) (f : T ⟶ T') (h : f ≫ u' = u) :
    mY p u u' f h ≫ pullback.snd p u' = pullback.snd p u ≫ f :=
  pullback.lift_snd _ _ _

private lemma mY_fst (p : Y ⟶ B) (u : T ⟶ B) (u' : T' ⟶ B) (f : T ⟶ T') (h : f ≫ u' = u) :
    mY p u u' f h ≫ pullback.fst p u' = pullback.fst p u := by
  unfold mY pullback.map
  erw [pullback.lift_fst]
  exact Category.comp_id _

private lemma mY_comp (p : Y ⟶ B) (u : T ⟶ B) (u' : T' ⟶ B) (u'' : T'' ⟶ B) (f : T ⟶ T') (g : T' ⟶ T'')
    (k : T ⟶ T'') (h : f ≫ u' = u) (h' : g ≫ u'' = u') (hk : k ≫ u'' = u) (e : f ≫ g = k) :
    mY p u u' f h ≫ mY p u' u'' g h' = mY p u u'' k hk := by
  apply pullback.hom_ext
  · rw [Category.assoc, mY_fst, mY_fst, mY_fst]
  · rw [Category.assoc, mY_snd, reassoc_of% mY_snd, mY_snd, e]

private lemma mY_id (p : Y ⟶ B) (u : T ⟶ B) (h : 𝟙 T ≫ u = u) : mY p u u (𝟙 T) h = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [mY_fst, Category.id_comp]
  · rw [mY_snd, Category.comp_id, Category.id_comp]

private def mW (p : Y ⟶ B) (ι : W ⟶ B) (u : T ⟶ B) (u' : T' ⟶ B) (f : T ⟶ T') (h : f ≫ u' = u) :
    pullback (pullback.snd p u ≫ u) ι ⟶ pullback (pullback.snd p u' ≫ u') ι :=
  pullback.map _ _ _ _ (mY p u u' f h) (𝟙 W) (𝟙 B)
    (by rw [Category.comp_id, reassoc_of% (mY_snd p u u' f h), h]) (by simp)

private lemma mW_fst (p : Y ⟶ B) (ι : W ⟶ B) (u : T ⟶ B) (u' : T' ⟶ B) (f : T ⟶ T') (h : f ≫ u' = u) :
    mW p ι u u' f h ≫ pullback.fst _ ι = pullback.fst _ ι ≫ mY p u u' f h :=
  pullback.lift_fst _ _ _

private lemma mW_snd (p : Y ⟶ B) (ι : W ⟶ B) (u : T ⟶ B) (u' : T' ⟶ B) (f : T ⟶ T') (h : f ≫ u' = u) :
    mW p ι u u' f h ≫ pullback.snd _ ι = pullback.snd _ ι :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

private lemma mW_comp (p : Y ⟶ B) (ι : W ⟶ B) (u : T ⟶ B) (u' : T' ⟶ B) (u'' : T'' ⟶ B) (f : T ⟶ T')
    (g : T' ⟶ T'') (k : T ⟶ T'') (h : f ≫ u' = u) (h' : g ≫ u'' = u') (hk : k ≫ u'' = u) (e : f ≫ g = k) :
    mW p ι u u' f h ≫ mW p ι u' u'' g h' = mW p ι u u'' k hk := by
  apply pullback.hom_ext
  · simp only [Category.assoc, mW_fst, reassoc_of% mW_fst]
    rw [mY_comp p u u' u'' f g k h h' hk e]
  · simp only [Category.assoc, mW_snd]

private lemma mW_id (p : Y ⟶ B) (ι : W ⟶ B) (u : T ⟶ B) (h : 𝟙 T ≫ u = u) : mW p ι u u (𝟙 T) h = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [mW_fst, mY_id, Category.id_comp, Category.comp_id]
  · rw [mW_snd, Category.id_comp]

private lemma a_w {U U' : B.Etale} (a : U' ⟶ U) : a.left ≫ U.hom = U'.hom := by
  simpa using a.w

private lemma resY_comp (p : Y ⟶ B) {U U' U'' : B.Etale} (b : U'' ⟶ U') (a : U' ⟶ U) :
    resY p (b ≫ a) = resY p b ≫ resY p a := by
  have hY : ∀ {V V' : B.Etale} (c : V' ⟶ V), resY p c = mY p _ _ c.left (a_w c) := fun _ => rfl
  rw [hY (b ≫ a), hY b, hY a]
  exact (mY_comp p _ _ _ _ _ _ _ _ _ rfl).symm

private lemma resYW_comp (p : Y ⟶ B) (ι : W ⟶ B) {U U' U'' : B.Etale} (b : U'' ⟶ U') (a : U' ⟶ U) :
    resYW p ι (b ≫ a) = resYW p ι b ≫ resYW p ι a := by
  have hW : ∀ {V V' : B.Etale} (c : V' ⟶ V), resYW p ι c = mW p ι _ _ c.left (a_w c) := fun _ => rfl
  rw [hW (b ≫ a), hW b, hW a]
  exact (mW_comp p ι _ _ _ _ _ _ _ _ _ rfl).symm

private lemma tY_res (p : Y ⟶ B) {U U' : B.Etale} (a : U' ⟶ U) (t : S ⟶ U'.left)
    (h : 𝟙 S ≫ t ≫ U'.hom = (t ≫ a.left) ≫ U.hom) :
    mY p _ _ (𝟙 S) h ≫ tY p U' t ≫ resY p a = tY p U (t ≫ a.left) := by
  have hY : resY p a = mY p _ _ a.left (a_w a) := rfl
  have hT : ∀ {V : B.Etale} (s : S ⟶ V.left), tY p V s = mY p _ _ s rfl := fun _ => rfl
  have h1 : (t ≫ a.left) ≫ U.hom = t ≫ U'.hom := by rw [Category.assoc, a_w]
  rw [hY, hT, hT, mY_comp p _ _ _ t a.left (t ≫ a.left) _ _ h1 rfl,
    mY_comp p _ _ _ (𝟙 S) (t ≫ a.left) (t ≫ a.left) _ _ rfl (Category.id_comp _)]

private lemma tW_res (p : Y ⟶ B) (ι : W ⟶ B) {U U' : B.Etale} (a : U' ⟶ U) (t : S ⟶ U'.left)
    (h : 𝟙 S ≫ t ≫ U'.hom = (t ≫ a.left) ≫ U.hom) :
    mW p ι _ _ (𝟙 S) h ≫ tW p ι U' t ≫ resYW p ι a = tW p ι U (t ≫ a.left) := by
  have hW : resYW p ι a = mW p ι _ _ a.left (a_w a) := rfl
  have hT : ∀ {V : B.Etale} (s : S ⟶ V.left), tW p ι V s = mW p ι _ _ s rfl := fun _ => rfl
  have h1 : (t ≫ a.left) ≫ U.hom = t ≫ U'.hom := by rw [Category.assoc, a_w]
  rw [hW, hT, hT, mW_comp p ι _ _ _ t a.left (t ≫ a.left) _ _ h1 rfl,
    mW_comp p ι _ _ _ (𝟙 S) (t ≫ a.left) (t ≫ a.left) _ _ rfl (Category.id_comp _)]

private lemma pull_left (q : ℕ) (i n : ℤ) {X Z : Scheme.{0}} (f : X ⟶ Z) (g : Z ⟶ X) (h : f ≫ g = 𝟙 X)
    (y : Ht q (sch.obj X) n i) :
    pull (ZMod q) (sch.map f) (tw q i) n (pull (ZMod q) (sch.map g) (tw q i) n y) = y := by
  rw [← pull_comp, ← sch.map_comp, h, sch.map_id, pull_id]

private lemma pull_zero (q : ℕ) (i n : ℤ) {X Z : Scheme.{0}} (f : X ⟶ Z) (g : Z ⟶ X) (h : g ≫ f = 𝟙 Z)
    (y : Ht q (sch.obj Z) n i) (hy : pull (ZMod q) (sch.map f) (tw q i) n y = 0) : y = 0 := by
  rw [← pull_left q i n g f h y, hy, map_zero]

private lemma shrink (q : ℕ) (i : ℤ) (p : Y ⟶ B) (ι : W ⟶ B) (U U' : B.Etale) (a : U' ⟶ U) (m : ℤ)
    (u' : U'.left) (S : Sys q i p ι U' m u') : Nonempty (Sys q i p ι U m (a.left u')) := by
  have hu : 𝟙 _ ≫ S.t ≫ U'.hom = (S.t ≫ a.left) ≫ U.hom := by
    rw [Category.id_comp, Category.assoc, a_w]
  have hu' : 𝟙 _ ≫ (S.t ≫ a.left) ≫ U.hom = S.t ≫ U'.hom := by
    rw [Category.id_comp, Category.assoc, a_w]
  have eY1 : mY p _ _ (𝟙 _) hu ≫ mY p _ _ (𝟙 _) hu' = 𝟙 _ := by
    rw [mY_comp p _ _ _ _ _ (𝟙 _) _ _ (Category.id_comp _) (Category.id_comp _), mY_id]
  have eY2 : mY p _ _ (𝟙 _) hu' ≫ mY p _ _ (𝟙 _) hu = 𝟙 _ := by
    rw [mY_comp p _ _ _ _ _ (𝟙 _) _ _ (Category.id_comp _) (Category.id_comp _), mY_id]
  have eW1 : mW p ι _ _ (𝟙 _) hu ≫ mW p ι _ _ (𝟙 _) hu' = 𝟙 _ := by
    rw [mW_comp p ι _ _ _ _ _ (𝟙 _) _ _ (Category.id_comp _) (Category.id_comp _), mW_id]
  have eW2 : mW p ι _ _ (𝟙 _) hu' ≫ mW p ι _ _ (𝟙 _) hu = 𝟙 _ := by
    rw [mW_comp p ι _ _ _ _ _ (𝟙 _) _ _ (Category.id_comp _) (Category.id_comp _), mW_id]
  have pc : ∀ {X1 X2 X3 : Scheme.{0}} (f : X1 ⟶ X2) (g : X2 ⟶ X3) (n : ℤ) (y : Ht q (sch.obj X3) n i),
      pull (ZMod q) (sch.map (f ≫ g)) (tw q i) n y =
        pull (ZMod q) (sch.map f) (tw q i) n (pull (ZMod q) (sch.map g) (tw q i) n y) := by
    intro X1 X2 X3 f g n y
    rw [CategoryTheory.Functor.map_comp, pull_comp]
  letI := S.cat
  letI := S.ring
  haveI := S.filt
  refine ⟨Sys.mk S.J S.V (fun j => S.a j ≫ a) ?_ S.tr S.tr_id S.tr_comp ?_ S.A S.sh
    (S.t ≫ a.left) (fun j => mY p _ _ (𝟙 _) hu ≫ S.gY j) (fun j => mW p ι _ _ (𝟙 _) hu ≫ S.gW j)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · intro j
    obtain ⟨v, hv⟩ := S.mem j
    exact ⟨v, congrArg (fun z => a.left z) hv⟩
  · intro j k f
    rw [← Category.assoc, S.tr_a]
  · intro j
    show pullback.fst _ ι ≫ mY p _ _ (𝟙 _) hu ≫ S.gY j = (mW p ι _ _ (𝟙 _) hu ≫ S.gW j) ≫ _
    rw [← reassoc_of% (mW_fst p ι _ _ (𝟙 _) hu)]
    exact (congrArg (fun z => mW p ι _ _ (𝟙 _) hu ≫ z) (S.sq j)).trans (Category.assoc _ _ _).symm
  · intro j
    rw [resY_comp]
    refine (Category.assoc _ _ _).trans ?_
    rw [reassoc_of% (S.gY_a j)]
    exact tY_res p a S.t hu
  · intro j
    rw [resYW_comp]
    refine (Category.assoc _ _ _).trans ?_
    rw [reassoc_of% (S.gW_a j)]
    exact tW_res p ι a S.t hu
  · intro j k f
    refine (Category.assoc _ _ _).trans ?_
    rw [S.gY_tr]
  · intro j k f
    refine (Category.assoc _ _ _).trans ?_
    rw [S.gW_tr]
  · intro j y hy
    apply S.injY j y
    exact pull_zero q i m (mY p _ _ (𝟙 _) hu) (mY p _ _ (𝟙 _) hu') eY2 _ (by rw [← pc]; exact hy)
  · intro y
    obtain ⟨j, y', hy'⟩ := S.surY (pull (ZMod q) (sch.map (mY p _ _ (𝟙 _) hu')) (tw q i) (m - 1) y)
    refine ⟨j, y', ?_⟩
    rw [pc, hy', pull_left q i (m - 1) _ _ eY1 y]
  · intro j w hw
    apply S.injW j w
    exact pull_zero q i (m - 1) (mW p ι _ _ (𝟙 _) hu) (mW p ι _ _ (𝟙 _) hu') eW2 _
      (by rw [← pc]; exact hw)

end UpperTheory.Cb.MorphismProjectionLaws

theorem UpperTheory.Cb.neighbourhoodShrinking_of_obstructionExact_natural :
    LateralTheory.E.NeighbourhoodKilling.ObsExact → LateralTheory.E.NeighbourhoodKilling.ObsNat → LateralTheory.E.GeoProof.Shrink := by
  intro _ _ q _ i B W Y p ι U U' a m u' S
  exact UpperTheory.Cb.MorphismProjectionLaws.shrink q i p ι U U' a m u' S
end
end

