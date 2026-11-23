module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2808
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2899
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0817
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2489
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0413
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0412
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2412
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2902

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BiextensionTrivialOfTranslateDifferenceTrivial
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

set_option autoImplicit false
noncomputable section
open GlobalTheory.CechPic GlobalTheory.AbDual

namespace GlobalTheory.PicBilin

variable {S : Scheme.{0}}

theorem evc_pow_left {A B Y : Over S} [GrpObj A] {P : LB (A ⊗ B).left} (hP : P.IsLB)
    (hadd : ∀ (a a' : Y ⟶ A) (t : Y ⟶ B), evc hP (a * a') t = evc hP a t + evc hP a' t)
    (a : Y ⟶ A) (t : Y ⟶ B) (n : ℕ) : evc hP (a ^ n) t = n • evc hP a t := by
  induction n with
  | zero =>
    have e := hadd 1 1 t
    rw [_root_.mul_one] at e
    rw [pow_zero, zero_smul]
    exact left_eq_add.1 e
  | succ n ih => rw [pow_succ, hadd, ih, succ_nsmul]

theorem comp_pow_pt {A T Y : Over S} [GrpObj A] (f : Y ⟶ T) (g : T ⟶ A) (n : ℕ) :
    f ≫ g ^ n = (f ≫ g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem cls_heckePow {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (m : ℕ)
    (h : (GlobalTheory.UPel.HT.Hecke.lbPow L m).IsLB) : cls _ h = m • cls L hL := by
  refine (cls_linComb hL (K := Fin m) (fun _ => 𝟙 X) (fun _ => 1) h).trans ?_
  simp [pull_id]

end GlobalTheory.PicBilin

namespace GlobalTheory.PicBilin

theorem triv_pow_of_translDiff : ∀ {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (P : LB (A ⊗ A).left), P.IsLB →
    (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) →
    LBIso P (P.pull (lift (snd A A) (fst A A)).left) →
    ∀ (T : Over S), (∀ c : GlobalTheory.CechPic.Pic T.left, c = 0) →
    ∀ (h₀ : 𝟙_ (Over S) ⟶ A) (h' : T ⟶ A) (m : ℕ), h' ^ 2 = toUnit T ≫ h₀ →
    (∃ t : (Out.translDiff A (P.pull (lift (𝟙 A) (𝟙 A)).left) (h' ^ m)).Gen, t.IsGen) →
    ∃ t : (((GlobalTheory.UPel.HT.Hecke.lbPow P m).pull (lift (toUnit A ≫ h₀) (𝟙 A)).left).pull (fst A T).left).Gen, t.IsGen := by
  intro S A _ _ hA P hP rig₁ rig₂ hsym T hT h₀ h' m hsq htd
  have hs : (swap P).IsLB := pull_isLB hP _
  obtain ⟨hadd₁, hadd₂⟩ := additive_of_cube GlobalTheory.CubeTop.cubeTheorem hA hA hP rig₁ rig₂
  have eL : ∀ {Y : Over S} (a a' t : Y ⟶ A), evc hP (a * a') t = evc hP a t + evc hP a' t :=
    fun a a' t => (isAdditive_iff hP).1 hadd₁ _ a a' t
  have eR : ∀ {Y : Over S} (a t t' : Y ⟶ A), evc hP a (t * t') = evc hP a t + evc hP a t' := by
    intro Y a t t'
    have e := (isAdditive_iff hs).1 hadd₂ _ t t' a
    rwa [evc_swap hP hs, evc_swap hP hs, evc_swap hP hs] at e
  have hsymc : cls P hP = cls _ hs := (cls_eq_iff hP hs).2 hsym
  have eS : ∀ {Y : Over S} (a b : Y ⟶ A), evc hP a b = evc hP b a := by
    intro Y a b
    rw [← evc_swap hP hs a b]
    simp only [evc, hsymc]
  have hL₁ : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have hD : (Out.translDiff A (P.pull (lift (𝟙 A) (𝟙 A)).left) (h' ^ m)).IsLB := LB.isLB_linComb hL₁ _ _
  have e0 := pull_translDiff hL₁ (h' ^ m) hD (snd A T) (fst A T)
  rw [(cls_eq_zero_iff hD).2 htd, map_zero] at e0
  have hu : ∀ u : A ⊗ T ⟶ A, CechPic.pull u.left (cls _ hL₁) = evc hP u u := fun u => by
    rw [cls_ev hP, pull_evc, Category.comp_id]
  rw [hu, hu] at e0
  have hXX : evc hP (snd A T ≫ h' ^ m) (snd A T ≫ h' ^ m) = 0 := by
    rw [← pull_evc, hT (evc hP (h' ^ m) (h' ^ m)), map_zero]
  have key : evc hP (snd A T ≫ h' ^ m) (snd A T ≫ h' ^ m) + evc hP (snd A T ≫ h' ^ m) (fst A T) +
      (evc hP (fst A T) (snd A T ≫ h' ^ m) + evc hP (fst A T) (fst A T)) - evc hP (fst A T) (fst A T) = 0 := by
    rw [← eR, ← eR, ← eL]
    exact e0.symm
  rw [hXX, eS (fst A T) (snd A T ≫ h' ^ m)] at key
  have h2 : 2 • evc hP (snd A T ≫ h' ^ m) (fst A T) = 0 := by
    rw [two_nsmul, ← key]
    abel
  rw [comp_pow_pt, evc_pow_left hP (fun a a' t => eL a a' t)] at h2
  have hsq' : toUnit (A ⊗ T) ≫ h₀ = (snd A T ≫ h') ^ 2 := by
    rw [← comp_pow_pt, hsq, ← Category.assoc, toUnit_unique (snd A T ≫ toUnit T) (toUnit _)]
  have hQ : (GlobalTheory.UPel.HT.Hecke.lbPow P m).IsLB := LB.isLB_linComb hP _ _
  have eQ : ∀ {Y : Over S} (a b : Y ⟶ A), evc hQ a b = m • evc hP a b := by
    intro Y a b
    rw [evc, cls_heckePow hP m hQ, map_nsmul]
    rfl
  refine (cls_eq_zero_iff (pull_isLB (pull_isLB hQ _) _)).1 ?_
  rw [cls_pull (pull_isLB hQ _)]
  change CechPic.pull (fst A T).left (evc hQ (toUnit A ≫ h₀) (𝟙 A)) = 0
  rw [pull_evc, eQ, Category.comp_id, ← Category.assoc, toUnit_unique (fst A T ≫ toUnit A) (toUnit _), hsq',
    evc_pow_left hP (fun a a' t => eL a a' t), smul_comm]
  exact h2

end GlobalTheory.PicBilin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechClassPullHO1EqZeroOfPullbackCoboundary
section
open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

noncomputable section

open GlobalTheory.CatCoh GlobalTheory.CechDR Opposite

namespace GlobalTheory.CechCmp

abbrev PairCov {Z Y : Scheme.{0}} {J : Type} (W : J → Z.Opens) (ι : Y ⟶ Z) : Type :=
  {p : Pair ι // ∃ i, p.1.2.1 ≤ W i}

abbrev pairCovIncl {Z Y : Scheme.{0}} {J : Type} (W : J → Z.Opens) (ι : Y ⟶ Z) :
    (PairCov W ι)ᵒᵖ ⥤ (Pair ι)ᵒᵖ :=
  (Monotone.functor (f := (Subtype.val : PairCov W ι → Pair ι)) fun _ _ h ↦ h).op

abbrev pairCovSnd {Z Y : Scheme.{0}} {J : Type} (W : J → Z.Opens) (ι : Y ⟶ Z) :
    (PairCov W ι)ᵒᵖ ⥤ (Bas W)ᵒᵖ :=
  (Monotone.functor (f := fun p : PairCov W ι ↦ (⟨p.1.1.2, p.2⟩ : Bas W))
    fun _ _ h ↦ Pair.le_snd (φ := ι) h).op

def pairCovPull {R R' : Type} [CommRing R] [CommRing R'] {Z Y : Scheme.{0}} {J : Type}
    (W : J → Z.Opens) {ι : Y ⟶ Z} {s : Z ⟶ Sp R} {s' : Y ⟶ Sp R'} {σ : R →+* R'}
    (w : ι ≫ s = s' ≫ spMap σ) :
    CoefMap σ (incl W ⋙ OAff s) (pairCovIncl W ι ⋙ OPair ι s') where
  G := pairCovSnd W ι
  α p := GlobalTheory.CechDR.secPull s s' p.unop.1
  naturality {p q} a b := (GlobalTheory.CechDR.pairPull w).naturality ((pairCovIncl W ι).map a) b
  smul p := semiHom_secPull w p.unop.1

theorem pairCov_pull1_eq {R R' : Type} [CommRing R] [CommRing R'] {Z Y : Scheme.{0}} {J : Type}
    (W : J → Z.Opens) {ι : Y ⟶ Z} {s : Z ⟶ Sp R} {s' : Y ⟶ Sp R'} {σ : R →+* R'}
    (w : ι ≫ s = s' ≫ spMap σ) (x : HO1 s) :
    (CoefMap.restrict (OPair ι s') (pairCovIncl W ι)).pull1 ((GlobalTheory.CechDR.pairPull w).pull1 x) =
      (pairCovPull W w).pull1 ((CoefMap.restrict (OAff s) (incl W)).pull1 x) := by
  rw [← CoefMap.pullCohomologyOne_comp, ← CoefMap.pullCohomologyOne_comp]
  exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ (𝟙 _) (fun T b ↦ by rw [NatTrans.id_app, mp_id]) x

theorem pairCov_restrict_injective {R' : Type} [CommRing R'] {Z Y : Scheme.{0}} [Z.IsSeparated]
    {J : Type} (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤) (hWa : ∀ i, IsAffineOpen (W i)) (ι : Y ⟶ Z)
    (s' : Y ⟶ Sp R') :
    Function.Injective (CoefMap.restrict (OAff s') (pairCovIncl W ι ⋙ pairFst ι)).pull1 := by
  let G : (PairCov W ι)ᵒᵖ ⥤ AffOp Y := pairCovIncl W ι ⋙ pairFst ι
  have hcov : ∀ T : AffOp Y, ∃ (n : ℕ) (b : Fin n → (OAff s').obj T),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : AffOp Y) (u : T ⟶ S),
        IsUnit (mp (OAff s') u (b i)) →
          ∃ (t : (PairCov W ι)ᵒᵖ) (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u := by
    intro T
    have hT : IsAffineOpen T.unop.1 := T.unop.2
    let Gs : Set Γ(Y, T.unop.1) := {f | ∃ j, Y.basicOpen f ≤ ι ⁻¹ᵁ W j}
    have hG : Ideal.span Gs = ⊤ := by
      rw [← hT.self_le_iSup_basicOpen_iff]
      intro x hx
      have hxU : ι.base x ∈ ⨆ i, W i := by rw [hW]; trivial
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hxU
      obtain ⟨f, hf, hxf⟩ := hT.exists_basicOpen_le (V := ι ⁻¹ᵁ W j) ⟨x, hj⟩ hx
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, ⟨j, hf⟩⟩, hxf⟩
    obtain ⟨F, hFG, hF⟩ := (Ideal.span_eq_top_iff_finite Gs).1 hG
    refine ⟨F.card, fun i ↦ (F.equivFin.symm i).1, ?_, ?_⟩
    · have hR : Set.range (fun i : Fin F.card ↦ (F.equivFin.symm i).1) =
          (F : Set Γ(Y, T.unop.1)) := by
        ext f
        constructor
        · rintro ⟨i, rfl⟩; exact (F.equivFin.symm i).2
        · intro hf; exact ⟨F.equivFin ⟨f, hf⟩, by simp⟩
      exact hR ▸ hF
    · intro i S u hu
      obtain ⟨j, hj⟩ := hFG (F.equivFin.symm i).2
      set f : Γ(Y, T.unop.1) := (F.equivFin.symm i).1
      have hB : IsAffineOpen (Y.basicOpen f) := hT.basicOpen f
      have hBT : Y.basicOpen f ≤ T.unop.1 := Y.basicOpen_le f
      have hSB : S.unop.1 ≤ Y.basicOpen f := by
        have h1 : Y.basicOpen (Y.presheaf.map (homOfLE (leOfHom u.unop)).op f) = S.unop.1 :=
          Y.basicOpen_of_isUnit hu
        rw [Scheme.basicOpen_res] at h1
        rw [← h1]; exact inf_le_right
      let p : Pair ι := ⟨(⟨_, hB⟩, ⟨W j, hWa j⟩), hj⟩
      let t : PairCov W ι := ⟨p, j, le_rfl⟩
      refine ⟨op t, (homOfLE (show (⟨_, hB⟩ : Y.affineOpens) ≤ T.unop from hBT)).op,
        (homOfLE (show S.unop ≤ (⟨_, hB⟩ : Y.affineOpens) from hSB)).op, ?_⟩
      exact Quiver.Hom.unop_inj (Subsingleton.elim _ _)
  have hdir : ∀ (t₁ t₂ : (PairCov W ι)ᵒᵖ) (S : AffOp Y), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) →
      ∃ (n : ℕ) (b : Fin n → (OAff s').obj S), Ideal.span (Set.range b) = ⊤ ∧
        ∀ (i : Fin n) (S' : AffOp Y) (u : S ⟶ S'), IsUnit (mp (OAff s') u (b i)) →
          ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S') := by
    intro t₁ t₂ S h₁ h₂
    refine ⟨1, fun _ ↦ 1, ?_, fun _ S' u _ ↦ ?_⟩
    · rw [Ideal.span_eq_top_iff_finite]
      exact ⟨{1}, by simp, by simp⟩
    · obtain ⟨j, hj⟩ := t₁.unop.2
      have hS'S : S'.unop.1 ≤ S.unop.1 := leOfHom u.unop
      have hS1 : S.unop.1 ≤ t₁.unop.1.1.1.1 := leOfHom h₁.unop
      have hS2 : S.unop.1 ≤ t₂.unop.1.1.1.1 := leOfHom h₂.unop
      let A : Z.affineOpens := ⟨t₁.unop.1.1.2.1 ⊓ t₂.unop.1.1.2.1,
        IsAffineOpen.inf t₁.unop.1.1.2.2 t₂.unop.1.1.2.2⟩
      have hA : S'.unop.1 ≤ ι ⁻¹ᵁ A.1 := fun y hy ↦
        ⟨t₁.unop.1.2 (hS1 (hS'S hy)), t₂.unop.1.2 (hS2 (hS'S hy))⟩
      let p₃ : Pair ι := ⟨(S'.unop, A), hA⟩
      let t₃ : PairCov W ι := ⟨p₃, j, inf_le_left.trans hj⟩
      refine ⟨op t₃, ⟨(homOfLE ?_).op⟩, ⟨(homOfLE ?_).op⟩, ⟨𝟙 _⟩⟩
      · exact ⟨hS'S.trans hS1, (inf_le_left : A.1 ≤ t₁.unop.1.1.2.1)⟩
      · exact ⟨hS'S.trans hS2, (inf_le_right : A.1 ≤ t₂.unop.1.1.2.1)⟩
  have H := _root_.GlobalTheory.CechDR.hasLoc_OAff s'
  have hs := _root_.GlobalTheory.sep_of_factoring_cover (OAff s') G H hcov
  have hg := _root_.GlobalTheory.CatCoh.Desc.glue_comma_of_basis (OAff s') G H hcov hdir
  exact _root_.GlobalTheory.CatCoh.CoefMap.restrict_pull1_injective_of_sep_glue _ _ hs hg

end GlobalTheory.CechCmp

namespace GlobalTheory.CechCmp

theorem appLE_resG_eq {Z Y : Scheme.{0}} (ι : Y ⟶ Z) {A V : Z.Opens} {T B : Y.Opens} (hV : V ≤ A)
    (e : T ≤ ι ⁻¹ᵁ V) (e' : B ≤ ι ⁻¹ᵁ A) (hT : T ≤ B) (x : Γ(Z, A)) :
    (ι.appLE V T e).hom (resG Z hV x) = resG Y hT ((ι.appLE A B e').hom x) := by
  simp only [resG, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem pullHO1_cmp_eq_zero_of_coboundary : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) [Z.IsSeparated]
    (s : Z ⟶ Sp R) (J : Type) (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤), (∀ i, IsAffineOpen (W i)) →
    ∀ (R' : Type) [CommRing R'] (σ : R →+* R') (Y : Scheme.{0}) (s' : Y ⟶ Sp R') (ι : Y ⟶ Z)
    (w : ι ≫ s = s' ≫ spMap σ) (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')), GlobalTheory.CechCmp.IsCocycle W c →
    (∃ h' : ∀ i, Γ(Y, ι ⁻¹ᵁ W i), ∀ i i', (ι.appLE (W i ⊓ W i') (ι ⁻¹ᵁ W i ⊓ ι ⁻¹ᵁ W i')
      (fun _ hx => hx)).hom (c i i') = resG Y inf_le_left (h' i) - resG Y inf_le_right (h' i')) →
    GlobalTheory.CechDR.pullHO1 w (GlobalTheory.CechCmp.cmp s W hW c) = 0 := by
  intro R _ Z _ s J W hW hWa R' _ σ Y s' ι w c hc ⟨h', hh'⟩
  set y := GlobalTheory.CechDR.pullHO1 w (cmp s W hW c)
  have e1 : (GlobalTheory.CechDR.pairPull w).pull1 (cmp s W hW c) = (pairRes ι s').pull1 y :=
    isPullO_pullHO1 w _
  apply pairCov_restrict_injective W hW hWa ι s'
  rw [map_zero]
  have e2 : (CoefMap.restrict (OAff s') (pairCovIncl W ι ⋙ pairFst ι)).pull1 y =
      (CoefMap.restrict (OPair ι s') (pairCovIncl W ι)).pull1 ((pairRes ι s').pull1 y) := by
    rw [← CoefMap.pullCohomologyOne_comp]
    exact CoefMap.pullCohomologyOne_eq_of_natTrans _ _ (𝟙 _) (fun T b ↦ by rw [NatTrans.id_app, mp_id]) y
  rw [e2, ← e1, pairCov_pull1_eq, restrict_cmp s W hW hc, CoefMap.pullCohomologyOne_class, H1.mk_eq_zero]
  let ix : PairCov W ι → J := fun p ↦ idx (⟨p.1.1.2, p.2⟩ : Bas W)
  have hix : ∀ p : PairCov W ι, p.1.1.1.1 ≤ ι ⁻¹ᵁ W (ix p) := fun p y hy ↦
    le_idx (⟨p.1.1.2, p.2⟩ : Bas W) (p.1.2 hy)
  refine ⟨fun p ↦ -resG Y (hix p.unop) (h' (ix p.unop)), ?_⟩
  funext p q a
  have hqp : q.unop.1.1.1.1 ≤ p.unop.1.1.1.1 := Pair.le_fst (leOfHom a.unop)
  change -resG Y (hix q.unop) (h' (ix q.unop)) - resG Y hqp (-resG Y (hix p.unop) (h' (ix p.unop))) =
    (ι.appLE _ _ _).hom (resG Z _ (c (ix p.unop) (ix q.unop)))
  rw [map_neg, resG_resG']
  have hT : q.unop.1.1.1.1 ≤ ι ⁻¹ᵁ W (ix p.unop) ⊓ ι ⁻¹ᵁ W (ix q.unop) :=
    le_inf (hqp.trans (hix p.unop)) (hix q.unop)
  have hV : q.unop.1.1.2.1 ≤ W (ix p.unop) ⊓ W (ix q.unop) :=
    le_inf ((show q.unop.1.1.2.1 ≤ p.unop.1.1.2.1 from Pair.le_snd (leOfHom a.unop)).trans (le_idx (⟨p.unop.1.1.2, p.unop.2⟩ : Bas W)))
      (le_idx (⟨q.unop.1.1.2, q.unop.2⟩ : Bas W))
  have k := appLE_resG_eq ι (A := W (ix p.unop) ⊓ W (ix q.unop))
    (B := ι ⁻¹ᵁ W (ix p.unop) ⊓ ι ⁻¹ᵁ W (ix q.unop)) hV q.unop.1.2 (fun _ hx => hx) hT
    (c (ix p.unop) (ix q.unop))
  refine Eq.trans ?_ k.symm
  rw [hh', map_sub, resG_resG', resG_resG']
  ring

end GlobalTheory.CechCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleIsCoboundaryOfClassEqZero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CechCmp

theorem IsCocycle.res_on {Z : Scheme.{0}} {J : Type} {W : J → Z.Opens}
    {c : ∀ i i' : J, Γ(Z, W i ⊓ W i')} (hc : IsCocycle W c) {U : Z.Opens} {i j k : J}
    (hi : U ≤ W i) (hj : U ≤ W j) (hk : U ≤ W k) :
    resG Z (le_inf hi hj) (c i j) + resG Z (le_inf hj hk) (c j k) =
      resG Z (le_inf hi hk) (c i k) := by
  have e := congrArg (resG Z (le_inf (le_inf hi hj) hk)) (hc i j k)
  simp only [map_add (f := _), resG_resG'] at e
  exact e

theorem exists_coboundary_of_cmp_eq_zero (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R)
    (J : Type) (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤) (hWa : ∀ i, IsAffineOpen (W i))
    (hWb : ∀ i i', IsAffineOpen (W i ⊓ W i')) (c : ∀ i i' : J, Γ(Z, W i ⊓ W i'))
    (hc : IsCocycle W c) (h0 : cmp s W hW c = 0) :
    ∃ h : ∀ i : J, Γ(Z, W i), ∀ i i',
      c i i' = resG Z inf_le_left (h i) - resG Z inf_le_right (h i') := by
  have h1 := restrict_cmp s W hW hc
  rw [h0, map_zero] at h1
  obtain ⟨g, hg⟩ := CatCoh.H1.mk_eq_zero.1 h1.symm
  let g' : ∀ V : Bas W, Γ(Z, V.1.1) := fun V ↦ g (Opposite.op V)
  have key : ∀ (V V' : Bas W) (h : V'.1.1 ≤ V.1.1),
      g' V' - resG Z h (g' V) =
        resG Z (le_inf (h.trans (le_idx V)) (le_idx V')) (c (idx V) (idx V')) := by
    intro V V' h
    exact congrFun (congrFun (congrFun hg (Opposite.op V)) (Opposite.op V'))
      (homOfLE (show V' ≤ V from h)).op
  let Ω : J → Bas W := fun i ↦ ⟨⟨W i, hWa i⟩, i, le_rfl⟩
  have hΩ : ∀ i, W i ≤ W (idx (Ω i)) := fun i ↦ le_idx (Ω i)
  let g₁ : ∀ i, Γ(Z, W i) := fun i ↦ g' (Ω i)
  refine ⟨fun i ↦ resG Z (le_inf le_rfl (hΩ i)) (c i (idx (Ω i))) - g₁ i, fun i i' ↦ ?_⟩
  let Ω₂ : Bas W := ⟨⟨W i ⊓ W i', hWb i i'⟩, i, inf_le_left⟩
  have hd : W i ⊓ W i' ≤ W (idx Ω₂) := le_idx Ω₂
  let g₂ : Γ(Z, W i ⊓ W i') := g' Ω₂
  have k1 : g₂ - resG Z inf_le_left (g₁ i) =
      resG Z (le_inf (inf_le_left.trans (hΩ i)) hd) (c (idx (Ω i)) (idx Ω₂)) :=
    key (Ω i) Ω₂ inf_le_left
  have k2 : g₂ - resG Z inf_le_right (g₁ i') =
      resG Z (le_inf (inf_le_right.trans (hΩ i')) hd) (c (idx (Ω i')) (idx Ω₂)) :=
    key (Ω i') Ω₂ inf_le_right
  have e1 := hc.res_on (inf_le_left : W i ⊓ W i' ≤ _) (inf_le_left.trans (hΩ i)) hd
  have e2 := hc.res_on (inf_le_right : W i ⊓ W i' ≤ _) (inf_le_right.trans (hΩ i')) hd
  have e3 := hc.res_on (inf_le_left : W i ⊓ W i' ≤ _) inf_le_right hd
  have e4 : resG Z (le_inf (inf_le_left : W i ⊓ W i' ≤ _) inf_le_right) (c i i') = c i i' := by
    have : (homOfLE (le_inf (inf_le_left : W i ⊓ W i' ≤ _) inf_le_right)).op = 𝟙 _ := rfl
    simp only [resG, this, CategoryTheory.Functor.map_id]
    rfl
  rw [e4] at e3
  simp only [map_sub, resG_resG']
  linear_combination e3 - e1 + e2 - k1 + k2

end GlobalTheory.CechCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechCocycleIsCoboundaryOfIsCoboundarySubcover
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.CechFin

set_option autoImplicit false

namespace GlobalTheory.CechFin

private theorem resG_resG_ext {Z : Scheme.{0}} {U V T : Z.Opens} (h : V ≤ U) (h' : T ≤ V) (f : Γ(Z, U)) :
    resG Z h' (resG Z h f) = resG Z (h'.trans h) f := by
  simp only [resG, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem isCob_of_isCob_subcover (Z : Scheme.{0}) (J : Type) (W : J → Z.Opens) (S : Set J)
    (hS : ∀ i, W i ≤ ⨆ a ∈ S, W a) (d : ∀ i i' : J, Γ(Z, W i ⊓ W i')) (hd : IsCoc W d)
    (h₀ : ∀ i, Γ(Z, W i))
    (hh₀ : ∀ a ∈ S, ∀ b ∈ S, d a b = resG Z inf_le_left (h₀ a) - resG Z inf_le_right (h₀ b)) :
    ∃ h : ∀ i, Γ(Z, W i), ∀ i i', d i i' = resG Z inf_le_left (h i) - resG Z inf_le_right (h i') := by
  have cov : ∀ (V : Z.Opens) (i : J), V ≤ W i → V ≤ ⨆ a : S, V ⊓ W a.1 := by
    intro V i hV x hx
    have hx' := hS i (hV hx)
    obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
    obtain ⟨ha', hxa⟩ := TopologicalSpace.Opens.mem_iSup.1 ha
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, ha'⟩, hx, hxa⟩
  have glue : ∀ i, ∃ g : Γ(Z, W i), ∀ a : S,
      resG Z (inf_le_left : W i ⊓ W a.1 ≤ W i) g = d i a.1 + resG Z inf_le_right (h₀ a.1) := by
    intro i
    obtain ⟨g, hg, -⟩ := Z.sheaf.existsUnique_gluing' (fun a : S => W i ⊓ W a.1) (W i)
      (fun _ => homOfLE inf_le_left) (cov (W i) i le_rfl)
      (fun a => d i a.1 + resG Z inf_le_right (h₀ a.1)) (by
        intro a b
        show resG Z inf_le_left (d i a.1 + resG Z inf_le_right (h₀ a.1)) =
          resG Z inf_le_right (d i b.1 + resG Z inf_le_right (h₀ b.1))
        have hT : W i ⊓ W a.1 ⊓ (W i ⊓ W b.1) ≤ W i ⊓ W a.1 ⊓ W b.1 :=
          le_inf inf_le_left (inf_le_right.trans inf_le_right)
        have c := congrArg (resG Z hT) (hd i a.1 b.1)
        have e := congrArg (resG Z (hT.trans (le_inf (inf_le_left.trans inf_le_right) inf_le_right)))
          (hh₀ a.1 a.2 b.1 b.2)
        simp only [map_add (f := _), map_sub, resG_resG_ext] at c e ⊢
        linear_combination c - e)
    exact ⟨g, fun a => hg a⟩
  choose g hg using glue
  refine ⟨g, fun i i' => ?_⟩
  refine Z.sheaf.eq_of_locally_eq' (fun a : S => W i ⊓ W i' ⊓ W a.1) (W i ⊓ W i')
    (fun _ => homOfLE inf_le_left) (cov (W i ⊓ W i') i inf_le_left) _ _ (fun a => ?_)
  show resG Z inf_le_left (d i i') = resG Z inf_le_left (resG Z inf_le_left (g i) - resG Z inf_le_right (g i'))
  have k₁ := congrArg (resG Z (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
    W i ⊓ W i' ⊓ W a.1 ≤ W i ⊓ W a.1)) (hg i a)
  have k₂ := congrArg (resG Z (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
    W i ⊓ W i' ⊓ W a.1 ≤ W i' ⊓ W a.1)) (hg i' a)
  have c := hd i i' a.1
  simp only [map_add (f := _), map_sub, resG_resG_ext] at k₁ k₂ c ⊢
  linear_combination c - k₁ + k₂

end GlobalTheory.CechFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechH1ClassEqOfCocycleAffineCover
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechCmp

variable {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R) {J : Type} (W : J → Z.Opens)

def cocVal (z : Z1 (incl W ⋙ OAff s)) (V V' : Bas W) (h : V'.1.1 ≤ V.1.1) : Γ(Z, V'.1.1) :=
  z.1 (Opposite.op V) (Opposite.op V') (homOfLE (show V' ≤ V from h)).op

theorem cocVal_comp (z : Z1 (incl W ⋙ OAff s)) (A B C : Bas W) (h : B.1.1 ≤ A.1.1)
    (h' : C.1.1 ≤ B.1.1) :
    resG Z h' (cocVal s W z A B h) = cocVal s W z A C (h'.trans h) - cocVal s W z B C h' :=
  eq_sub_of_add_eq (Z1.comp z (homOfLE (show B ≤ A from h)).op
    (homOfLE (show C ≤ B from h')).op).symm

theorem exists_isCocycle_cmp_eq (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (J : Type)
    (W : J → Z.Opens) (hW : ⨆ i, W i = ⊤) (h1 : ∀ i, IsAffineOpen (W i))
    (h2 : ∀ i i', IsAffineOpen (W i ⊓ W i'))
    (h3 : ∀ i i' i'', IsAffineOpen (W i ⊓ W i' ⊓ W i'')) (x : GlobalTheory.CechDR.HO1 s) :
    ∃ c : ∀ i i' : J, Γ(Z, W i ⊓ W i'), IsCocycle W c ∧ cmp s W hW c = x := by
  obtain ⟨z, hz⟩ := H1.mk_surjective _ (resEquiv s W hW x)
  let O1 : J → Bas W := fun i ↦ ⟨⟨W i, h1 i⟩, i, le_rfl⟩
  let O2 : J → J → Bas W := fun i i' ↦ ⟨⟨W i ⊓ W i', h2 i i'⟩, i, inf_le_left⟩
  let O3 : J → J → J → Bas W := fun i i' i'' ↦
    ⟨⟨W i ⊓ W i' ⊓ W i'', h3 i i' i''⟩, i, inf_le_left.trans inf_le_left⟩
  let c : ∀ i i' : J, Γ(Z, W i ⊓ W i') := fun i i' ↦
    cocVal s W z (O1 i) (O2 i i') inf_le_left - cocVal s W z (O1 i') (O2 i i') inf_le_right
  have key : ∀ (i i' : J) (V : Bas W) (h : V.1.1 ≤ W i ⊓ W i'),
      resG Z h (c i i') = cocVal s W z (O1 i) V (h.trans inf_le_left) -
        cocVal s W z (O1 i') V (h.trans inf_le_right) := by
    intro i i' V h
    have e1 := cocVal_comp s W z (O1 i) (O2 i i') V inf_le_left h
    have e2 := cocVal_comp s W z (O1 i') (O2 i i') V inf_le_right h
    have e : resG Z h (c i i') =
        resG Z h (cocVal s W z (O1 i) (O2 i i') inf_le_left) -
          resG Z h (cocVal s W z (O1 i') (O2 i i') inf_le_right) := map_sub _ _ _
    rw [e]
    refine (congrArg₂ (· - ·) e1 e2).trans ?_
    ring
  have hc : IsCocycle W c := by
    intro i i' i''
    have e1 := key i i' (O3 i i' i'') inf_le_left
    have e2 := key i' i'' (O3 i i' i'') (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
    have e3 := key i i'' (O3 i i' i'') (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
    refine (congrArg₂ (· + ·) e1 e2).trans (Eq.trans ?_ e3.symm)
    ring
  refine ⟨c, hc, ?_⟩
  rw [cmp_of_isCocycle s W hW hc, LinearEquiv.symm_apply_eq, ← hz, H1.mk_eq_mk]
  refine ⟨fun V ↦ -cocVal s W z (O1 (idx V.unop)) V.unop (le_idx V.unop), ?_⟩
  funext V V' a
  have e1 := key (idx V.unop) (idx V'.unop) V'.unop
    (le_inf ((le_of_hom a).trans (le_idx V.unop)) (le_idx V'.unop))
  have e2 := cocVal_comp s W z (O1 (idx V.unop)) V.unop V'.unop (le_idx V.unop) (le_of_hom a)
  have goal : -cocVal s W z (O1 (idx V'.unop)) V'.unop (le_idx V'.unop) -
      resG Z (le_of_hom a) (-cocVal s W z (O1 (idx V.unop)) V.unop (le_idx V.unop)) =
      resG Z (le_inf ((le_of_hom a).trans (le_idx V.unop)) (le_idx V'.unop))
        (c (idx V.unop) (idx V'.unop)) - cocVal s W z V.unop V'.unop (le_of_hom a) := by
    rw [map_neg, e1, e2]
    ring
  exact goal

end GlobalTheory.CechCmp
end
end

