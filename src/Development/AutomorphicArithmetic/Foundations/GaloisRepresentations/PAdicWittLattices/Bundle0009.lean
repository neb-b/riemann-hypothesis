module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpTr
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pOpTr :
    OpTr.{u} := by
  intro B R _ T hT Z Y Z' p q p' s t hs ht tr htr A
  have key : ∀ (W : Scheme) (c : W ⟶ Z) (J : Type) [Fintype J] (σ : J → (W ⟶ Y))
      (hσ : ∀ j, σ j ≫ q = c ≫ p), Splits s c σ → ∀ x,
      T.pull c rfl ((tr ∘ₗ T.pull t ht) x) = ∑ j, T.pull (σ j ≫ t)
        (by rw [Category.assoc, ht]; exact hσ j) x := by
    intro W c J _ σ hσ hspl x
    rw [LinearMap.comp_apply, htr W (c ≫ p) c rfl J σ hσ hspl]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (T.pull_comp (σ j) t (hσ j) ht _ x).symm
  constructor
  · rintro ⟨W, c, G, _, _, a, J, _, σ, h, hgal, hspl, hA⟩
    have hσ : ∀ j, σ j ≫ q = c ≫ p := fun j => by
      rw [← ht, ← Category.assoc]
      exact h j
    apply LinearMap.ext
    intro x
    apply hT.inj p (c ≫ p) c rfl G a hgal
    rw [hA x, key W c J σ hσ hspl x]
  · rintro ⟨W, c, G, _, _, a, J, _, σ, hgal, hspl⟩ rfl
    have hσ : ∀ j, σ j ≫ q = c ≫ p := fun j => by
      rw [← hs, ← Category.assoc, hspl.1 j]
    refine ⟨W, c, G, inferInstance, inferInstance, a, J, inferInstance, σ,
      fun j => by rw [Category.assoc, ht]; exact hσ j, hgal, hspl, fun x => ?_⟩
    exact key W c J σ hσ hspl x
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POrdEx
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace UpperTheory.Gal.G3

private theorem ordExStep (hS : OrdStep) {Z Y W : Scheme.{0}} (s : Y ⟶ Z) [IsFinite s] [Etale s] (d : ℕ)
    (c : W ⟶ Z) (σ : Fin d → (W ⟶ Y)) (hcf : IsFinite c) (hce : Etale c) (hσ : ∀ j, σ j ≫ s = c)
    (hinj : ∀ (Ω : Type) [Field Ω] (x : sp Ω ⟶ W), Function.Injective fun j => x ≫ σ j)
    (huniv : ∀ (U : Scheme.{0}) (z : U ⟶ Z) (y : Fin d → (U ⟶ Y)), (∀ j, y j ≫ s = z) →
      (∀ (Ω : Type) [Field Ω] (x : sp Ω ⟶ U), Function.Injective fun j => x ≫ y j) →
      ∃! w : U ⟶ W, w ≫ c = z ∧ ∀ j, w ≫ σ j = y j) :
    ∃ (W' : Scheme.{0}) (c' : W' ⟶ Z) (σ' : Fin (d + 1) → (W' ⟶ Y)), IsFinite c' ∧ Etale c' ∧
      (∀ j, σ' j ≫ s = c') ∧
      (∀ (Ω : Type) [Field Ω] (x : sp Ω ⟶ W'), Function.Injective fun j => x ≫ σ' j) ∧
      ∀ (U : Scheme.{0}) (z : U ⟶ Z) (y : Fin (d + 1) → (U ⟶ Y)), (∀ j, y j ≫ s = z) →
        (∀ (Ω : Type) [Field Ω] (x : sp Ω ⟶ U), Function.Injective fun j => x ≫ y j) →
        ∃! w : U ⟶ W', w ≫ c' = z ∧ ∀ j, w ≫ σ' j = y j := by
  haveI := hcf
  haveI := hce
  let P := pullback s c
  have hsq : ∀ j, σ j ≫ s = 𝟙 W ≫ c := fun j => by rw [hσ j, Category.id_comp]
  let sec : Fin d → (W ⟶ P) := fun j => pullback.lift (σ j) (𝟙 W) (hsq j)
  have hsec1 : ∀ j, sec j ≫ pullback.fst s c = σ j := fun j => pullback.lift_fst _ _ _
  have hsec2 : ∀ j, sec j ≫ pullback.snd s c = 𝟙 W := fun j => pullback.lift_snd _ _ _
  haveI hOP : MorphismProperty.HasOfPostcompProperty (@IsOpenImmersion : MorphismProperty Scheme)
      (@Etale : MorphismProperty Scheme) := by
    apply MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.2
    intro X Y f hf
    haveI : Etale f := hf
    exact inferInstanceAs <| IsOpenImmersion (pullback.diagonal f)
  have hopen : ∀ j, IsOpenImmersion (sec j) := fun j =>
    MorphismProperty.of_postcomp (W := (@IsOpenImmersion : MorphismProperty Scheme))
      (W' := (@Etale : MorphismProperty Scheme)) (sec j) (pullback.snd s c)
      (inferInstanceAs (Etale (pullback.snd s c)))
      (by rw [hsec2]; exact inferInstanceAs (IsOpenImmersion (𝟙 W)))
  have hclosed : ∀ j, IsClosedImmersion (sec j) := fun j => by
    haveI : IsClosedImmersion (sec j ≫ pullback.snd s c) := by
      rw [hsec2]; infer_instance
    exact IsClosedImmersion.of_comp (sec j) (pullback.snd s c)
  let S : Set P := ⋃ j, Set.range (sec j).base
  have hSc : IsClosed S := isClosed_iUnion_of_finite fun j => (hclosed j).isClosedEmbedding.isClosed_range
  have hSo : IsOpen S := isOpen_iUnion fun j => (hopen j).base_open.isOpen_range
  let O : P.Opens := ⟨Sᶜ, hSc.isOpen_compl⟩
  have hOr : Set.range O.ι.base = Sᶜ := O.range_ι
  haveI : IsClosedImmersion O.ι := .of_isPreimmersion _ (by rw [hOr]; exact hSo.isClosed_compl)
  have hpt : ∀ (j : Fin d) (Ω : Type) [Field Ω] (x : sp Ω ⟶ P),
      x.base (IsLocalRing.closedPoint Ω) ∈ Set.range (sec j).base →
      x ≫ pullback.fst s c = x ≫ pullback.snd s c ≫ σ j := by
    intro j Ω _ x hx
    have hr : Set.range x.base ⊆ Set.range (sec j).base := by
      rintro _ ⟨p, rfl⟩
      rwa [Subsingleton.elim p (IsLocalRing.closedPoint Ω)]
    haveI := hopen j
    have hf := IsOpenImmersion.lift_fac (sec j) x hr
    rw [← hf, Category.assoc, Category.assoc, hsec1, reassoc_of% hsec2]
  have hback : ∀ (j : Fin d) {T : Scheme.{0}} (x : T ⟶ P),
      x ≫ pullback.fst s c = x ≫ pullback.snd s c ≫ σ j → x = (x ≫ pullback.snd s c) ≫ sec j := by
    intro j T x hx
    apply pullback.hom_ext
    · rw [Category.assoc, hsec1, hx, Category.assoc]
    · rw [Category.assoc, hsec2, Category.comp_id]
  refine ⟨O, O.ι ≫ pullback.snd s c ≫ c,
    Fin.snoc (α := fun _ => ((O : Scheme) ⟶ Y)) (fun j => O.ι ≫ pullback.snd s c ≫ σ j)
      (O.ι ≫ pullback.fst s c), inferInstance, inferInstance, ?_, ?_, ?_⟩
  · intro k
    refine Fin.lastCases ?_ (fun j => ?_) k
    · simp only [Fin.snoc_last, Category.assoc, pullback.condition]
    · simp only [Fin.snoc_castSucc, Category.assoc, hσ j]
  · intro Ω _ x
    have key : ∀ j : Fin d, x ≫ O.ι ≫ pullback.fst s c ≠ x ≫ O.ι ≫ pullback.snd s c ≫ σ j := by
      intro j h
      have h2 := hback j (x ≫ O.ι) (by simpa only [Category.assoc] using h)
      have hin : (x ≫ O.ι).base (IsLocalRing.closedPoint Ω) ∈ S := by
        rw [h2]
        exact Set.mem_iUnion.2 ⟨j, _, rfl⟩
      have hO : (x ≫ O.ι).base (IsLocalRing.closedPoint Ω) ∈ Set.range O.ι.base :=
        ⟨x.base (IsLocalRing.closedPoint Ω), rfl⟩
      rw [hOr] at hO
      exact hO hin
    intro a b hab
    simp only at hab
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => rfl
      | cast j =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
        exact absurd hab (key j)
    | cast i =>
      induction b using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
        exact absurd hab.symm (key i)
      | cast j =>
        simp only [Fin.snoc_castSucc] at hab
        exact congrArg Fin.castSucc (hinj Ω (x ≫ O.ι ≫ pullback.snd s c) (by simpa only [Category.assoc] using hab))
  · intro U z y hy hinjU
    obtain ⟨w0, ⟨hw0c, hw0σ⟩, hw0u⟩ := huniv U z (fun j => y j.castSucc) (fun j => hy _)
      (fun Ω _ x a b h => Fin.castSucc_injective _ (hinjU Ω x h))
    let φ : U ⟶ P := pullback.lift (y (Fin.last d)) w0 (by rw [hy, hw0c])
    have hφ1 : φ ≫ pullback.fst s c = y (Fin.last d) := pullback.lift_fst _ _ _
    have hφ2 : φ ≫ pullback.snd s c = w0 := pullback.lift_snd _ _ _
    have hrange : Set.range φ.base ⊆ Set.range O.ι.base := by
      rintro _ ⟨u, rfl⟩
      rw [hOr]
      intro hu
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hu
      let x := U.fromSpecResidueField u
      have hxu : x.base (IsLocalRing.closedPoint (U.residueField u)) = u :=
        U.fromSpecResidueField_apply u _
      have := hpt j (U.residueField u) (x ≫ φ) (by
        show φ.base (x.base _) ∈ _
        rw [hxu]
        exact hj)
      rw [Category.assoc, Category.assoc, hφ1, reassoc_of% hφ2, hw0σ] at this
      exact (Fin.castSucc_lt_last j).ne (hinjU _ x this).symm
    refine ⟨IsOpenImmersion.lift O.ι φ hrange, ⟨?_, fun k => ?_⟩, ?_⟩
    · rw [IsOpenImmersion.lift_fac_assoc, reassoc_of% hφ2, hw0c]
    · refine Fin.lastCases ?_ (fun j => ?_) k
      · rw [Fin.snoc_last, IsOpenImmersion.lift_fac_assoc, hφ1]
      · rw [Fin.snoc_castSucc, IsOpenImmersion.lift_fac_assoc, reassoc_of% hφ2, hw0σ]
    · rintro w' ⟨hw'c, hw'σ⟩
      rw [← cancel_mono O.ι, IsOpenImmersion.lift_fac]
      have e2 : w' ≫ O.ι ≫ pullback.snd s c = w0 := by
        refine hw0u _ ⟨by simpa only [Category.assoc] using hw'c, fun j => ?_⟩
        have := hw'σ j.castSucc
        rw [Fin.snoc_castSucc] at this
        simpa only [Category.assoc] using this
      apply pullback.hom_ext
      · have := hw'σ (Fin.last d)
        rw [Fin.snoc_last] at this
        rw [Category.assoc, this, hφ1]
      · rw [Category.assoc, e2, hφ2]

theorem pOrdEx : OrdStep → OrdEx := by
  intro hS Z Y s _ _ d
  induction d with
  | zero =>
    refine ⟨Z, 𝟙 Z, Fin.elim0, inferInstance, inferInstance, fun j => j.elim0, ?_, ?_⟩
    · intro Ω _ x a
      exact a.elim0
    · intro U z y _ _
      exact ⟨z, ⟨Category.comp_id _, fun j => j.elim0⟩, fun w hw => by simpa using hw.1⟩
  | succ d ih =>
    obtain ⟨W, c, σ, hcf, hce, hσ, hinj, huniv⟩ := ih
    exact ordExStep hS s d c σ hcf hce hσ hinj huniv

end UpperTheory.Gal.G3

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POrdStep
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem mem_range_diagonal_iff {Y Z : Scheme.{0}} (s : Y ⟶ Z) [IsOpenImmersion (pullback.diagonal s)]
    (Ω : Type) [Field Ω] (y : UpperTheory.Gal.G3.sp Ω ⟶ pullback s s) :
    y (IsLocalRing.closedPoint Ω) ∈ Set.range (pullback.diagonal s) ↔
      y ≫ pullback.fst s s = y ≫ pullback.snd s s := by
  constructor
  · rintro ⟨z, hz⟩
    have hsub : Set.range y ⊆ Set.range (pullback.diagonal s) := by
      rintro _ ⟨q, rfl⟩
      have hq : q = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
      rw [hq]
      exact ⟨z, hz⟩
    have hfac := IsOpenImmersion.lift_fac (pullback.diagonal s) y hsub
    rw [← hfac, Category.assoc, Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd]
  · intro h
    refine ⟨(y ≫ pullback.fst s s) (IsLocalRing.closedPoint Ω), ?_⟩
    have hy : (y ≫ pullback.fst s s) ≫ pullback.diagonal s = y := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
      · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, h]
    conv_rhs => rw [← hy]
    rfl

theorem UpperTheory.Gal.G3.pOrdStep :
    OrdStep := by
  intro Z Y W s _ _ c d σ hσ
  have hc : ∀ j, pullback.fst s c ≫ s = (pullback.snd s c ≫ σ j) ≫ s := fun j => by
    rw [Category.assoc, hσ j, pullback.condition]
  let φ : Fin d → (pullback s c ⟶ pullback s s) := fun j =>
    pullback.lift (pullback.fst s c) (pullback.snd s c ≫ σ j) (hc j)
  have hopen : ∀ j, IsOpen ((φ j) ⁻¹' Set.range (pullback.diagonal s)) := fun j =>
    (pullback.diagonal s).isOpenEmbedding.isOpen_range.preimage (φ j).continuous
  have hclosed : ∀ j, IsClosed ((φ j) ⁻¹' Set.range (pullback.diagonal s)) := fun j =>
    (pullback.diagonal s).isClosedEmbedding.isClosed_range.preimage (φ j).continuous
  refine ⟨⟨(⋃ j, (φ j) ⁻¹' Set.range (pullback.diagonal s))ᶜ,
    (isClosed_iUnion_of_finite hclosed).isOpen_compl⟩, (isOpen_iUnion hopen).isClosed_compl, ?_⟩
  intro Ω _ x
  have key : ∀ j, (x ≫ φ j) (IsLocalRing.closedPoint Ω) ∈ Set.range (pullback.diagonal s) ↔
      x ≫ pullback.fst s c = x ≫ pullback.snd s c ≫ σ j := by
    intro j
    rw [mem_range_diagonal_iff s Ω (x ≫ φ j)]
    simp only [Category.assoc, φ, pullback.lift_fst, pullback.lift_snd]
  show x (IsLocalRing.closedPoint Ω) ∈ (⋃ j, (φ j) ⁻¹' Set.range (pullback.diagonal s))ᶜ ↔ _
  simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_preimage, not_exists]
  refine forall_congr' (fun j => ?_)
  exact (not_congr (key j)).trans ⟨fun h e => h e.symm, fun h e => h e.symm⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPieceLe
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem unit_sp (l : ℕ) (Ω : Type) [Field Ω] (h : (l : Ω) ≠ 0) : IsUnit (l : Γ(sp Ω, ⊤)) := by
  have hu : IsUnit ((l : Ω)) := h.isUnit
  have := hu.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
  simpa using this

private theorem bc_apply {R : Type} [CommRing R] (L : Type) [CommRing L] [Algebra R L] {M N P : Type*}
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (y : L ⊗[R] M) :
    (g ∘ₗ f).baseChange L y = g.baseChange L (f.baseChange L y) := by
  rw [LinearMap.baseChange_comp]; rfl

private theorem fEt_iso {Y Z : Scheme.{0}} (f : Y ⟶ Z) [IsIso f] : FEt f 1 := by
  refine ⟨inferInstance, inferInstance, fun K _ _ x => ?_⟩
  refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨x ≫ inv f, by simp⟩⟩⟩
  rw [← cancel_mono f, a.2, b.2]

theorem UpperTheory.Gal.G3.pPieceLe :
    EtGood → BcGood.{1} → ExtGood.{1} → (∀ {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{1} B R) (L : Type) [Field L] [Algebra R L] {Z Y : Scheme.{0}} (p : Z ⟶ B) (q : Y ⟶ B) (s : Y ⟶ Z) (tr : T.H q →ₗ[R] T.H p), T.IsTr p q s tr → (T.ext L).IsTr p q s (tr.baseChange L)) → HopSpec → CoverInv.{1} → PieceLe := by
  intro hEt hBc hExt hExtTr hHop hCov l _ k L O _ _ _ _ _ hl H θ C hC Ω _ _
  have hlΩ : ((l : ℕ) : Ω) ≠ 0 := by
    intro h0
    apply hl
    have : algebraMap k Ω (l : k) = 0 := by simpa using h0
    exact (algebraMap k Ω).injective (by simpa using this)
  have hT0 : (etG l k Ω).Good := hBc _ _ (hEt l _ (unit_sp l Ω hlΩ))
  have hT : ((etG l k Ω).ext L).Good := hExt _ L hT0
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ_[l] L).injective
  obtain ⟨hinj, hsurj⟩ := hCov C hC ((etG l k Ω).ext L) hT
  refine ⟨hinj, fun y hy => hsurj y ?_⟩
  intro g hiso hθ
  haveI := hiso
  obtain ⟨tr0, htr0⟩ := hT0.tr H.q (H.s g ≫ H.q) (H.s g) rfl
  refine ⟨tr0.baseChange L, hExtTr _ L H.q (H.s g ≫ H.q) (H.s g) tr0 htr0, ?_⟩
  have hop_eq := (hHop l hl H Ω g 1 (fEt_iso (H.s g))).2 tr0 htr0
  have hy' : y ∈ Module.End.eigenspace ((hop l H Ω g).baseChange L) (θ g) :=
    (Submodule.mem_iInf _).1 hy g
  rw [Module.End.mem_eigenspace_iff, hθ, one_smul, hop_eq] at hy'
  change tr0.baseChange L (((etG l k Ω).pull (H.t g) _).baseChange L y) = y
  exact (bc_apply L _ _ y).symm.trans hy'
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPlInv
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pPlInv :
    GalInv.{u} → TwGal → PlInv.{u} := by
  intro hG hT B G _ X R _ _ T hgood m j hmj
  constructor
  · obtain ⟨m', hm'j, hnorm, hS⟩ := X.deep j {(m, 1)}
    have hm'm : X.K m' ≤ X.K m := fun u hu => by simpa using hS (m, 1) (by simp) u hu
    obtain ⟨Γ, _, _, r, c, hr, huniq, hgal⟩ := hT X m' j (X.isAdmissibleIntegralBasisChange_one hm'j) hnorm
    have hinj := hgood.inj (X.q j) (X.q m') _ (X.tr_q m' j 1 _ _) Γ _ hgal
    have key : ∀ z, X.pl T m' j 1 z = X.pl T m' m 1 (X.pl T m j 1 z) := fun z => by
      rw [X.pl_pl T (X.isAdmissibleIntegralBasisChange_one hm'm) (X.isAdmissibleIntegralBasisChange_one hmj), one_mul]
    intro x y hxy
    apply hinj
    rw [← X.pl_eq T (X.isAdmissibleIntegralBasisChange_one hm'j), key, key, hxy]
  · intro hnorm y hy
    obtain ⟨Γ, _, _, r, c, hr, huniq, hgal⟩ := hT X m j (X.isAdmissibleIntegralBasisChange_one hmj) hnorm
    have ha : ∀ g : Γ, X.tr m m (r g) (c g).1 (c g).2 ≫ X.q m = X.q m := fun g => X.tr_q _ _ _ _ _
    have hsurj := (hG T hgood (X.q j) (X.q m) _ (X.tr_q m j 1 _ _) Γ _ ha hgal y).2
    obtain ⟨x, hx⟩ := hsurj (fun g => by rw [← X.pl_eq T (c g)]; exact hy _ (hr g))
    exact ⟨x, by rw [X.pl_eq T (X.isAdmissibleIntegralBasisChange_one hmj)]; exact hx⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPtsOfSplits
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem sp_subsingleton (Ω : Type) [Field Ω] : Subsingleton ↑(UpperTheory.Gal.G3.sp Ω) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum Ω))

private theorem exists_factor_ι {J : Type} {W : Scheme.{0}} (Ω : Type) [Field Ω]
    (u : UpperTheory.Gal.G3.sp Ω ⟶ ∐ (fun _ : J => W)) :
    ∃ (j : J) (x : UpperTheory.Gal.G3.sp Ω ⟶ W), x ≫ Sigma.ι (fun _ : J => W) j = u := by
  haveI := sp_subsingleton Ω
  have p : ↑(UpperTheory.Gal.G3.sp Ω) := show PrimeSpectrum Ω from ⟨⊥, Ideal.isPrime_bot⟩
  obtain ⟨⟨j, y⟩, hq⟩ : ∃ q, (sigmaMk (fun _ : J => W)).symm (u p) = q := ⟨_, rfl⟩
  have hy : Sigma.ι (fun _ : J => W) j y = u p := by
    rw [← sigmaMk_mk, ← hq, Homeomorph.apply_symm_apply]
  refine ⟨j, IsOpenImmersion.lift (Sigma.ι (fun _ : J => W) j) u ?_,
    IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨z, rfl⟩
  obtain rfl : z = p := Subsingleton.elim _ _
  exact ⟨y, hy⟩

private theorem index_eq_of_ι {J : Type} {W : Scheme.{0}} (Ω : Type) [Field Ω] {j j' : J}
    {x x' : UpperTheory.Gal.G3.sp Ω ⟶ W}
    (h : x ≫ Sigma.ι (fun _ : J => W) j = x' ≫ Sigma.ι (fun _ : J => W) j') : j = j' := by
  by_contra hne
  have he := isEmpty_of_commSq_sigmaι_of_ne (g := fun _ : J => W) ⟨h⟩ hne
  exact he.false (show PrimeSpectrum Ω from ⟨⊥, Ideal.isPrime_bot⟩)

theorem UpperTheory.Gal.G3.pPtsOfSplits :
    PtsOfSplits := by
  intro Z Y W s c J σ hs Ω _ x y hxy
  obtain ⟨hσ, hiso⟩ := hs
  haveI := hiso
  let e := Limits.Sigma.desc (fun j : J =>
    pullback.lift (σ j) (𝟙 W) (by rw [Category.id_comp]; exact hσ j))
  have hι : ∀ j, Sigma.ι (fun _ : J => W) j ≫ e =
      pullback.lift (σ j) (𝟙 W) (by rw [Category.id_comp]; exact hσ j) :=
    fun j => Sigma.ι_desc _ _
  obtain ⟨j, x', hx'⟩ := exists_factor_ι Ω (pullback.lift y x hxy ≫ inv e)
  have h1 : x' ≫ Sigma.ι (fun _ : J => W) j ≫ e = pullback.lift y x hxy := by
    rw [← Category.assoc, hx', Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [hι] at h1
  have hsnd := congrArg (· ≫ pullback.snd s c) h1
  have hfst := congrArg (· ≫ pullback.fst s c) h1
  simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id] at hsnd hfst
  rw [hsnd] at hfst
  refine ⟨j, hfst, fun j' hj' => ?_⟩
  have hj'' : x ≫ σ j' = y := hj'
  apply index_eq_of_ι Ω (x := x) (x' := x')
  rw [hx']
  apply (cancel_mono e).mp
  rw [Category.assoc, hι, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hj'']
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsBasic
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.GalV

namespace UpperTheory.Gal.G3

private theorem splits_restrict (hS : SplitsPts) (hP : PtsOfSplits) {Z Y W W' : Scheme.{0}} (s : Y ⟶ Z) [IsFinite s] [Etale s]
    (c : W ⟶ Z) (J : Type) [Finite J] (σ : J → (W ⟶ Y)) (g : W' ⟶ W) (h : Splits s c σ) :
    Splits s (g ≫ c) fun j => g ≫ σ j := by
  have h0 := h
  obtain ⟨hc, -⟩ := h
  refine hS s (g ≫ c) J (fun j => g ≫ σ j) (fun j => by simp [hc j]) ?_
  intro Ω _ _ x y hy
  have hy' : y ≫ s = (x ≫ g) ≫ c := by simpa using hy
  obtain ⟨j, hj, huniq⟩ := hP s c J σ h0 Ω (x ≫ g) y hy'
  exact ⟨j, by simpa using hj, fun i hi => huniq i (by simpa using hi)⟩

private theorem splits_down (hS : SplitsPts) (hP : PtsOfSplits) {P Y Z' Z W : Scheme.{0}} {v : P ⟶ Y} {s' : P ⟶ Z'} {s : Y ⟶ Z}
    {g : Z' ⟶ Z} [IsFinite s] [Etale s] (sq : IsPullback v s' s g) (c : W ⟶ Z') (J : Type) [Finite J] (σ : J → (W ⟶ P))
    (hσ : ∀ j, σ j ≫ s' = c) (h : Splits s' c σ) : Splits s (c ≫ g) fun j => σ j ≫ v := by
  refine hS s (c ≫ g) J (fun j => σ j ≫ v)
    (fun j => by rw [Category.assoc, sq.w, ← Category.assoc, hσ j]) ?_
  intro Ω _ _ x y hy
  have hw : y ≫ s = (x ≫ c) ≫ g := by simpa using hy
  obtain ⟨j, hj, huniq⟩ := hP s' c J σ h Ω x (sq.lift y (x ≫ c) hw) (by simp)
  refine ⟨j, ?_, ?_⟩
  · simp only
    rw [← Category.assoc, hj, sq.lift_fst]
  · intro i hi
    apply huniq
    apply sq.hom_ext
    · simpa using hi
    · simp [hσ i]

private theorem splits_up (hS : SplitsPts) (hP : PtsOfSplits) {P Y Z' Z W : Scheme.{0}} {v : P ⟶ Y} {s' : P ⟶ Z'} {s : Y ⟶ Z}
    {g : Z' ⟶ Z} [IsFinite s] [Etale s] (sq : IsPullback v s' s g) (c : W ⟶ Z') (J : Type) [Finite J] (σ : J → (W ⟶ P))
    (hσ : ∀ j, σ j ≫ s' = c) (h : Splits s (c ≫ g) fun j => σ j ≫ v) : Splits s' c σ := by
  have : IsFinite s' := MorphismProperty.of_isPullback (P := @IsFinite) sq ‹_›
  have : Etale s' := MorphismProperty.of_isPullback (P := @Etale) sq ‹_›
  refine hS s' c J σ hσ ?_
  intro Ω _ _ x y hy
  have hw : (y ≫ v) ≫ s = x ≫ c ≫ g := by
    rw [Category.assoc, sq.w, ← Category.assoc, hy, Category.assoc]
  obtain ⟨j, hj, huniq⟩ := hP s (c ≫ g) J (fun j => σ j ≫ v) h Ω x (y ≫ v) hw
  refine ⟨j, ?_, ?_⟩
  · apply sq.hom_ext
    · simpa using hj
    · simp [hσ j, hy]
  · intro i hi
    apply huniq
    rw [← Category.assoc, hi]

theorem pSplitsBasic : SplitsPts → PtsOfSplits → SplitsBasic := fun hS hP =>
  ⟨fun s _ _ c J _ σ g h => splits_restrict hS hP s c J σ g h,
   fun _ _ _ _ _ _ sq c J _ σ hσ => ⟨splits_down hS hP sq c J σ hσ, splits_up hS hP sq c J σ hσ⟩⟩

end UpperTheory.Gal.G3

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsComp
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pSplitsComp :
    SplitsPts → PtsOfSplits → SplitsComp := by
  intro hS hP Y P Z W κ s _ _ _ _ c I J _ _ τ σ hτ hσ
  have hτc : ∀ i, τ i ≫ s = c := hτ.1
  have hσc : ∀ i j, σ i j ≫ κ = τ i := fun i => (hσ i).1
  refine hS (κ ≫ s) c (I × J) (fun x => σ x.1 x.2)
    (fun x => by rw [← Category.assoc, hσc, hτc]) ?_
  intro Ω _ _ x y hy
  obtain ⟨i, hi, hiu⟩ := hP s c I τ hτ Ω x (y ≫ κ) (by simpa using hy)
  obtain ⟨j, hj, hju⟩ := hP κ (τ i) J (σ i) (hσ i) Ω x y hi.symm
  refine ⟨(i, j), hj, ?_⟩
  rintro ⟨i', j'⟩ h'
  have h'' : x ≫ σ i' j' = y := h'
  have hi' : i' = i := hiu i' (by
    show x ≫ τ i' = y ≫ κ
    rw [← hσc i' j', ← Category.assoc, h''])
  subst hi'
  have hj' : j' = j := hju j' h''
  subst hj'
  rfl
end

