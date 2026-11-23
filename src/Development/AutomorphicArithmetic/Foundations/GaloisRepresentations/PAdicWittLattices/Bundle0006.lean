module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.Bundle0006
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0108

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PExtPts
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pExtPts :
    ExtPts := by
  intro W Z B _ p _ f g hfg hpt
  let X' : Over B := Over.mk (f ≫ p)
  let Y' : Over B := Over.mk p
  let f' : X' ⟶ Y' := Over.homMk f
  let g' : X' ⟶ Y' := Over.homMk g hfg.symm
  have : IsSeparated Y'.hom := ‹_›
  have hsurj : Surjective (equalizer.ι f' g').left := by
    constructor
    intro x
    let K := W.residueField x
    let Ω := AlgebraicClosure K
    let y : Spec (CommRingCat.of Ω) ⟶ W :=
      Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ W.fromSpecResidueField x
    have hy : y ≫ f = y ≫ g := hpt Ω y
    let U' : Over B := Over.mk (y ≫ f ≫ p)
    let y' : U' ⟶ X' := Over.homMk y
    have hy' : y' ≫ f' = y' ≫ g' := by
      ext1
      exact hy
    let pt : Spec (CommRingCat.of Ω) := IsLocalRing.closedPoint Ω
    refine ⟨(equalizer.lift y' hy').left pt, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left, equalizer.lift_ι]
    show (Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ W.fromSpecResidueField x) pt = x
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]
  have := isIso_of_isClosedImmersion_of_surjective (Y := W) (equalizer.ι f' g').left
  rw [← cancel_epi (equalizer.ι f' g').left]
  exact congr($(equalizer.condition f' g').left)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PExtTr
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pExtTr :
    ∀ {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) (L : Type) [Field L] [Algebra R L] {Z Y : Scheme.{0}} (p : Z ⟶ B) (q : Y ⟶ B) (s : Y ⟶ Z) (tr : T.H q →ₗ[R] T.H p), T.IsTr p q s tr → (T.ext L).IsTr p q s (tr.baseChange L) := by
  intro B R _ T L _ _ Z Y p q s tr h W r c hc J _ σ hσ hs x
  change LinearMap.baseChange L (T.pull c hc) (LinearMap.baseChange L tr x) =
    ∑ j, LinearMap.baseChange L (T.pull (σ j) (hσ j)) x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    simp only [LinearMap.baseChange_tmul]
    rw [h W r c hc J σ hσ hs y, TensorProduct.tmul_sum]
  | add x y hx hy =>
    simp only [map_add (f := _), hx, hy, ← Finset.sum_add_distrib]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PFEtBasic
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem fib_finite {V U : Scheme.{0}} (r : V ⟶ U) [IsFinite r] (K : Type) [Field K]
    (x : Spec (CommRingCat.of K) ⟶ U) : Finite {y : Spec (CommRingCat.of K) ⟶ V // y ≫ r = x} :=
  (UpperTheory.Gal.TranscendenceTraces.fibFin_of UpperTheory.Gal.TranscendenceTraces.chart_of r K x).to_subtype

private theorem fEt_of_pullback {P Y Z' Z : Scheme.{0}} (v : P ⟶ Y) (s' : P ⟶ Z') (s : Y ⟶ Z) (g : Z' ⟶ Z)
    (d : ℕ) (h : IsPullback v s' s g) (hs : FEt s d) : FEt s' d := by
  refine ⟨MorphismProperty.of_isPullback (P := @IsFinite) h hs.1,
    MorphismProperty.of_isPullback (P := @Etale) h hs.2.1, fun K _ _ x => ?_⟩
  let eqv : {y' : Spec (CommRingCat.of K) ⟶ P // y' ≫ s' = x} ≃
      {y : Spec (CommRingCat.of K) ⟶ Y // y ≫ s = x ≫ g} :=
    { toFun := fun y' => ⟨y'.1 ≫ v, by rw [Category.assoc, h.w, ← Category.assoc, y'.2]⟩
      invFun := fun y => ⟨h.lift y.1 x y.2, h.lift_snd _ _ _⟩
      left_inv := fun y' => Subtype.ext (h.hom_ext (by rw [h.lift_fst]) (by rw [h.lift_snd, y'.2]))
      right_inv := fun y => Subtype.ext (h.lift_fst _ _ _) }
  rw [Nat.card_congr eqv]
  exact hs.2.2 K (x ≫ g)

private theorem fEt_comp {W Y Z : Scheme.{0}} (r : W ⟶ Y) (s : Y ⟶ Z) (d e : ℕ) (hr : FEt r e) (hs : FEt s d) :
    FEt (r ≫ s) (d * e) := by
  haveI := hr.1
  haveI := hr.2.1
  haveI := hs.1
  haveI := hs.2.1
  refine ⟨inferInstance, inferInstance, fun K _ _ x => ?_⟩
  haveI : Fintype {y : Spec (CommRingCat.of K) ⟶ Y // y ≫ s = x} :=
    @Fintype.ofFinite _ (fib_finite s K x)
  haveI hfin : ∀ y : {y : Spec (CommRingCat.of K) ⟶ Y // y ≫ s = x},
      Finite {w : Spec (CommRingCat.of K) ⟶ W // w ≫ r = y.1} := fun y => fib_finite r K y.1
  let eqv : {w : Spec (CommRingCat.of K) ⟶ W // w ≫ r ≫ s = x} ≃
      Σ y : {y : Spec (CommRingCat.of K) ⟶ Y // y ≫ s = x},
        {w : Spec (CommRingCat.of K) ⟶ W // w ≫ r = y.1} :=
    { toFun := fun w => ⟨⟨w.1 ≫ r, by rw [Category.assoc]; exact w.2⟩, ⟨w.1, rfl⟩⟩
      invFun := fun p => ⟨p.2.1, by rw [← Category.assoc, p.2.2, p.1.2]⟩
      left_inv := fun w => rfl
      right_inv := by
        intro p
        rcases p with ⟨⟨y, hy⟩, ⟨w, hw⟩⟩
        dsimp only at hw
        subst hw
        rfl }
  rw [Nat.card_congr eqv, Nat.card_sigma, Finset.sum_congr rfl (fun y _ => hr.2.2 K y.1),
    Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, hs.2.2 K x, smul_eq_mul]

private theorem fEt_galois (hp : PtsOfSplits) {W Z : Scheme.{0}} (c : W ⟶ Z) (G : Type) [Group G] [Finite G]
    (a : G → (W ⟶ W)) (h : IsGalois c G a) : FEt c (Nat.card G) := by
  haveI := h.1
  haveI := h.2.1
  haveI := h.2.2.1
  refine ⟨inferInstance, inferInstance, fun Ω _ _ x => ?_⟩
  obtain ⟨w, hw⟩ := Surjective.surj (f := c) (UpperTheory.Gal.TranscendenceTraces.pt x)
  obtain ⟨z, hz, -⟩ := UpperTheory.Gal.TranscendenceTraces.ptLift_of c Ω x w hw
  have hsp := h.2.2.2.2.2
  have hac : ∀ g, a g ≫ c = c := hsp.1
  have key : ∀ y : Spec (CommRingCat.of Ω) ⟶ W, y ≫ c = x → ∃! g : G, z ≫ a g = y :=
    fun y hy => hp c c G a hsp Ω z y (by rw [hy, hz])
  let f : G → {y : Spec (CommRingCat.of Ω) ⟶ W // y ≫ c = x} :=
    fun g => ⟨z ≫ a g, by rw [Category.assoc, hac, hz]⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro g g' hgg
      have hv : z ≫ a g = z ≫ a g' := congrArg Subtype.val hgg
      obtain ⟨g0, _, hu⟩ := key (z ≫ a g) (f g).2
      exact (hu g rfl).trans (hu g' hv.symm).symm
    · rintro ⟨y, hy⟩
      obtain ⟨g, hg, _⟩ := key y hy
      exact ⟨g, Subtype.ext hg⟩
  exact (Nat.card_congr (Equiv.ofBijective f hbij)).symm

theorem UpperTheory.Gal.G3.pFEtBasic :
    PtsOfSplits → FEtBasic := by
  intro hp
  exact ⟨fun v s' s g d h hs => fEt_of_pullback v s' s g d h hs, fun r s d e hr hs => fEt_comp r s d e hr hs,
    fun c G _ _ a h => fEt_galois hp c G a h⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PFEtInj
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pFEtInj :
    GalClosD → FEtInj.{u} := by
  intro hGC B R _ T hT Z W p r c hc d hd hfet
  obtain ⟨V, e, G, _, _, a, σ, hgal, hspl⟩ := hGC c d hfet
  have h0 : σ ⟨0, hd⟩ ≫ c = e := hspl.1 _
  subst h0
  have hinj := hT.inj p ((σ ⟨0, hd⟩ ≫ c) ≫ p) (σ ⟨0, hd⟩ ≫ c) rfl G a hgal
  have hσr : σ ⟨0, hd⟩ ≫ r = (σ ⟨0, hd⟩ ≫ c) ≫ p := by
    rw [← hc, Category.assoc]
  have hcomp := T.pull_comp (σ ⟨0, hd⟩) c hσr hc rfl
  intro x y hxy
  apply hinj
  rw [hcomp x, hcomp y, hxy]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGalClos
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pGalClos :
    GalClosD → GalClos := by
  intro hD Z Y s _ _ d h
  obtain ⟨W, c, G, iG, fG, a, σ, hg, hs⟩ := hD s d ⟨inferInstance, inferInstance, h⟩
  exact ⟨W, c, G, iG, fG, a, Fin d, inferInstance, σ, hg, hs⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGalClosD
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

namespace UpperTheory.Gal.G3

private theorem fibre_finite {Y Z : Scheme.{0}} (s : Y ⟶ Z) [IsFinite s] (Ω : Type) [Field Ω] (x : sp Ω ⟶ Z) :
    Finite {y : sp Ω ⟶ Y // y ≫ s = x} := by
  have h := UpperTheory.Gal.TranscendenceTraces.fibFin_of UpperTheory.Gal.TranscendenceTraces.chart_of s Ω x
  exact h.to_subtype

private theorem epi_of_field {Ω Ω' : Type} [Field Ω] [Field Ω'] (x : sp Ω' ⟶ sp Ω) : Epi x := by
  exact Flat.epi_of_flat_of_surjective x

private theorem point_over {Z : Scheme.{0}} (z : Z) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (x : sp Ω ⟶ Z), x (IsLocalRing.closedPoint Ω) = z := by
  refine ⟨AlgebraicClosure (Z.residueField z), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) (AlgebraicClosure (Z.residueField z)))) ≫
      Z.fromSpecResidueField z, ?_⟩
  exact Scheme.fromSpecResidueField_apply z _

end UpperTheory.Gal.G3

private theorem exists_comp_sigma_eq_of_comp_eq_comp {Z Y W : Scheme.{0}} (s : Y ⟶ Z) [IsFinite s] {d : ℕ}
    (hd : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Spec (CommRingCat.of K) ⟶ Z),
      Nat.card {y // y ≫ s = x} = d)
    (c : W ⟶ Z) (σ : Fin d → (W ⟶ Y)) (hσ : ∀ j, σ j ≫ s = c)
    (hinj : ∀ (Ω : Type) [Field Ω] (x : UpperTheory.Gal.G3.sp Ω ⟶ W), Function.Injective fun j => x ≫ σ j)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : UpperTheory.Gal.G3.sp Ω ⟶ W) (y : UpperTheory.Gal.G3.sp Ω ⟶ Y)
    (hy : y ≫ s = x ≫ c) :
    ∃ j, x ≫ σ j = y := by
  have hfin := UpperTheory.Gal.G3.fibre_finite s Ω (x ≫ c)
  let f : Fin d → {y : UpperTheory.Gal.G3.sp Ω ⟶ Y // y ≫ s = x ≫ c} :=
    fun j => ⟨x ≫ σ j, by rw [Category.assoc, hσ]⟩
  have hf : Function.Injective f := by
    intro i j hij
    exact hinj Ω x (congrArg Subtype.val hij)
  have hb := hf.bijective_of_nat_card_le (by rw [hd Ω (x ≫ c), Nat.card_eq_fintype_card, Fintype.card_fin])
  obtain ⟨j, hj⟩ := hb.2 ⟨y, hy⟩
  exact ⟨j, congrArg Subtype.val hj⟩

theorem UpperTheory.Gal.G3.pGalClosD :
    SplitsPts → OrdEx → GalClosD := by
  intro hS hO Z Y s d hF
  obtain ⟨hfin, het, hd⟩ := hF
  obtain ⟨W, c, σ, hcf, hce, hσ, hinj, huniv⟩ := hO s d
  have hex : ∀ g : Equiv.Perm (Fin d), ∃! w : W ⟶ W, w ≫ c = c ∧ ∀ j, w ≫ σ j = σ (g j) := by
    intro g
    refine huniv W c (fun j => σ (g j)) (fun j => hσ (g j)) ?_
    intro Ω _ x i j hij
    exact g.injective (hinj Ω x hij)
  choose a ha using fun g => (hex g).exists
  have hone : a 1 = 𝟙 W :=
    (hex 1).unique (ha 1) ⟨Category.id_comp c, fun j => by simp⟩
  have hmul : ∀ g h, a (g * h) = a g ≫ a h := by
    intro g h
    refine (hex (g * h)).unique (ha (g * h)) ⟨?_, fun j => ?_⟩
    · rw [Category.assoc, (ha h).1, (ha g).1]
    · rw [Category.assoc, (ha h).2 j, (ha g).2 (h j)]
      rfl
  have hspl : Splits s c σ := by
    refine hS s c (Fin d) σ hσ ?_
    intro Ω _ _ x y hy
    obtain ⟨j, hj⟩ := exists_comp_sigma_eq_of_comp_eq_comp s hd c σ hσ hinj Ω x y hy
    exact ⟨j, hj, fun j' hj' => hinj Ω x (hj'.trans hj.symm)⟩
  have hsur : Surjective c := by
    constructor
    intro z
    obtain ⟨Ω, _, _, x, hx⟩ := UpperTheory.Gal.G3.point_over z
    have hfF := UpperTheory.Gal.G3.fibre_finite s Ω x
    have hcard : Nat.card {y : UpperTheory.Gal.G3.sp Ω ⟶ Y // y ≫ s = x} = d := hd Ω x
    let e := Finite.equivFin {y : UpperTheory.Gal.G3.sp Ω ⟶ Y // y ≫ s = x}
    let yy : Fin d → (UpperTheory.Gal.G3.sp Ω ⟶ Y) := fun j => (e.symm (Fin.cast hcard.symm j)).1
    have hyy : ∀ j, yy j ≫ s = x := fun j => (e.symm (Fin.cast hcard.symm j)).2
    have hinj' : ∀ (Ω' : Type) [Field Ω'] (x' : UpperTheory.Gal.G3.sp Ω' ⟶ UpperTheory.Gal.G3.sp Ω),
        Function.Injective fun j => x' ≫ yy j := by
      intro Ω' _ x' i j hij
      haveI := UpperTheory.Gal.G3.epi_of_field x'
      have h1 : yy i = yy j := (cancel_epi x').1 hij
      have h2 := Subtype.val_injective h1
      exact Fin.cast_injective _ (e.symm.injective h2)
    obtain ⟨w, ⟨hw, _⟩, _⟩ := huniv (UpperTheory.Gal.G3.sp Ω) x yy hyy hinj'
    refine ⟨w (IsLocalRing.closedPoint Ω), ?_⟩
    rw [← hx, ← hw]
    rfl
  have hgal : Splits c c a := by
    refine hS c c (Equiv.Perm (Fin d)) a (fun g => (ha g).1) ?_
    intro Ω _ _ x y hy
    have hpt : ∀ j, ∃ k, x ≫ σ k = y ≫ σ j := by
      intro j
      exact exists_comp_sigma_eq_of_comp_eq_comp s hd c σ hσ hinj Ω x (y ≫ σ j) (by rw [Category.assoc, hσ, hy])
    choose p hp using hpt
    have hpi : Function.Injective p := by
      intro i j hij
      apply hinj Ω y
      simp only
      rw [← hp i, ← hp j, hij]
    let g := Equiv.ofBijective p (Finite.injective_iff_bijective.1 hpi)
    have hinjy : ∀ (Ω' : Type) [Field Ω'] (x' : UpperTheory.Gal.G3.sp Ω' ⟶ UpperTheory.Gal.G3.sp Ω),
        Function.Injective fun j => x' ≫ (y ≫ σ j) := by
      intro Ω' _ x' i j hij
      apply hinj Ω' (x' ≫ y)
      simpa only [Category.assoc] using hij
    refine ⟨g, ?_, ?_⟩
    · refine (huniv (UpperTheory.Gal.G3.sp Ω) (x ≫ c) (fun j => y ≫ σ j)
        (fun j => by rw [Category.assoc, hσ, hy]) hinjy).unique ⟨?_, fun j => ?_⟩ ⟨hy, fun j => rfl⟩
      · rw [Category.assoc, (ha g).1]
      · rw [Category.assoc, (ha g).2 j]
        exact hp j
    · intro g' hg'
      refine Equiv.ext fun j => ?_
      apply hinj Ω x
      simp only
      rw [← (ha g').2 j, ← Category.assoc, hg', ← hp j]
      rfl
  exact ⟨W, c, Equiv.Perm (Fin d), inferInstance, inferInstance, a, σ,
    ⟨hcf, hce, hsur, hone, hmul, hgal⟩, hspl⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGalInv
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem pull_congr {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) {X Y : Scheme.{0}}
    {p : X ⟶ B} {q : Y ⟶ B} {f f' : Y ⟶ X} (e : f = f') (h : f ≫ p = q) (h' : f' ≫ p = q) (x : T.H p) :
    T.pull f h x = T.pull f' h' x := by
  subst e; rfl

theorem UpperTheory.Gal.G3.pGalInv :
    GalInv.{u} := by
  intro B R _ _ T hT Z W p r c hc G _ _ a ha hgal y
  obtain ⟨hac, -⟩ := hgal.2.2.2.2.2
  constructor
  · rintro ⟨x, rfl⟩ g
    have hcomp : (a g ≫ c) ≫ p = r := by rw [hac g, hc]
    rw [← T.pull_comp (a g) c (ha g) hc hcomp x]
    exact pull_congr T (hac g) hcomp hc x
  · intro hy
    haveI := hgal.1
    haveI := hgal.2.1
    haveI := Fintype.ofFinite G
    obtain ⟨tr, htr⟩ := hT.tr p r c hc
    have key := htr W r c hc G a ha hgal.2.2.2.2.2 y
    have hsum : ∑ g, T.pull (a g) (ha g) y = (Fintype.card G : R) • y := by
      rw [Finset.sum_congr rfl fun g _ => hy g, Finset.sum_const, Finset.card_univ,
        ← Nat.cast_smul_eq_nsmul R]
    refine ⟨(Fintype.card G : R)⁻¹ • tr y, ?_⟩
    rw [map_smul, key, hsum, smul_smul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.2 Fintype.card_ne_zero), one_smul]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHodgeFun
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem affine_point_comp {X Y : Scheme.{0}} (f : X ⟶ Y) {V : X.Opens} {U : Y.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (i : V ≤ f ⁻¹ᵁ U) {Ω : Type} [Field Ω] (x : Γ(X, V) →+* Ω) :
    (Spec.map (CommRingCat.ofHom x) ≫ hV.fromSpec) ≫ f =
      Spec.map (CommRingCat.ofHom (x.comp (f.appLE U V i).hom)) ≫ hU.fromSpec := by
  rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec f hU hV i, ← Category.assoc, ← Spec.map_comp]
  rfl

private theorem affine_point_injective {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) {Ω : Type} [Field Ω]
    {a b : Γ(X, V) →+* Ω}
    (h : Spec.map (CommRingCat.ofHom a) ≫ hV.fromSpec = Spec.map (CommRingCat.ofHom b) ≫ hV.fromSpec) : a = b := by
  have h' := Spec.map_injective ((cancel_mono _).1 h)
  exact congrArg CommRingCat.Hom.hom h'

private theorem cech_section_local_split (hP : PtsOfSplits) (hS : AlgSplit) (hT : AlgTr) {k : Type} [Field k] {Z Y W : Scheme.{0}}
    (p : Z ⟶ sp k) (q : Y ⟶ sp k) (s : Y ⟶ Z) [IsFinite s] [Etale s] (c : W ⟶ Z) (J : Type) [Fintype J]
    (σ : J → (W ⟶ Y)) (hσ : ∀ j, σ j ≫ s = c) (hsp : Splits s c σ) (U : Z.Opens) (hU : IsAffineOpen U)
    (V : W.Opens) (hV : IsAffineOpen V) (hVU : V ≤ c ⁻¹ᵁ U) (b : GlobalTheory.CechDR.Sec q (s ⁻¹ᵁ U)) :
    (c.appLE U V hVU).hom (secTrace p q hU b) =
      ∑ j, ((σ j).appLE (s ⁻¹ᵁ U) V (hVU.trans (GlobalTheory.GalTrace.preimage_le (hσ j) U))).hom b := by
  letI : Algebra (GlobalTheory.CechDR.Sec p U) (GlobalTheory.CechDR.Sec q (s ⁻¹ᵁ U)) := secAlg p q s U
  haveI : Module.Finite (GlobalTheory.CechDR.Sec p U) (GlobalTheory.CechDR.Sec q (s ⁻¹ᵁ U)) := sec_finite hU
  haveI : Algebra.Etale (GlobalTheory.CechDR.Sec p U) (GlobalTheory.CechDR.Sec q (s ⁻¹ᵁ U)) := sec_etale hU
  letI : Algebra (GlobalTheory.CechDR.Sec p U) Γ(W, V) := (c.appLE U V hVU).hom.toAlgebra
  have hcomp : ∀ j, s.app U ≫ (σ j).appLE (s ⁻¹ᵁ U) V (hVU.trans (GlobalTheory.GalTrace.preimage_le (hσ j) U)) =
      c.appLE U V hVU := by
    intro j
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    simp only [hσ j]
  let τ : J → GlobalTheory.CechDR.Sec q (s ⁻¹ᵁ U) →ₐ[GlobalTheory.CechDR.Sec p U] Γ(W, V) := fun j =>
    { toRingHom := ((σ j).appLE (s ⁻¹ᵁ U) V (hVU.trans (GlobalTheory.GalTrace.preimage_le (hσ j) U))).hom
      commutes' := fun a => congrArg (fun f => CommRingCat.Hom.hom f a) (hcomp j) }
  have hA' : IsAffineOpen (s ⁻¹ᵁ U) := hU.preimage s
  obtain ⟨e, he⟩ := hS _ _ _ J τ (by
    intro Ω _ _ x y hxy
    have hring : y.comp (s.appLE U (s ⁻¹ᵁ U) le_rfl).hom = x.comp (c.appLE U V hVU).hom := by
      rw [← Scheme.Hom.app_eq_appLE]
      exact hxy
    have hpt : (Spec.map (CommRingCat.ofHom y) ≫ hA'.fromSpec) ≫ s =
        (Spec.map (CommRingCat.ofHom x) ≫ hV.fromSpec) ≫ c :=
      (affine_point_comp s hU hA' le_rfl y).trans
        ((congrArg (fun f => Spec.map (CommRingCat.ofHom f) ≫ hU.fromSpec) hring).trans
          (affine_point_comp c hU hV hVU x).symm)
    obtain ⟨j, hj, huniq⟩ := hP s c J σ hsp Ω _ _ hpt
    refine ⟨j, ?_, fun j' hj' => huniq j' ?_⟩
    · exact affine_point_injective hA'
        ((affine_point_comp (σ j) hA' hV (hVU.trans (GlobalTheory.GalTrace.preimage_le (hσ j) U)) x).symm.trans hj)
    · exact (affine_point_comp (σ j') hA' hV (hVU.trans (GlobalTheory.GalTrace.preimage_le (hσ j') U)) x).trans
        (congrArg (fun f => Spec.map (CommRingCat.ofHom f) ≫ hA'.fromSpec) hj'))
  exact hT _ _ _ J τ e he b

theorem UpperTheory.Gal.G3.pHodgeFun :
    PtsOfSplits → AlgSplit → AlgTr → ∀ (k : Type) [Field k] {Z Y W : Scheme.{0}} (p : Z ⟶ sp k) (q : Y ⟶ sp k) (r : W ⟶ sp k) (s : Y ⟶ Z) [IsFinite s] [Etale s] (c : W ⟶ Z) (J : Type) [Fintype J] (σ : J → (W ⟶ Y)) (hσ : ∀ j, σ j ≫ s = c), Splits s c σ → ∀ (U : Z.Opens) (hU : IsAffineOpen U) (b : GlobalTheory.CechDR.Sec q (s ⁻¹ᵁ U)), GlobalTheory.HodgeCoh.appSec p r c U (secTrace p q hU b) = ∑ j, GlobalTheory.CechDR.Sec.res r (GlobalTheory.GalTrace.preimage_le (hσ j) U) (GlobalTheory.HodgeCoh.appSec q r (σ j) (s ⁻¹ᵁ U) b) := by
  intro hP hS hT k _ Z Y W p q r s _ _ c J _ σ hσ hsp U hU b
  refine TopCat.Sheaf.eq_of_locally_eq' W.sheaf (fun i : {V : W.Opens // IsAffineOpen V ∧ V ≤ c ⁻¹ᵁ U} => i.1) (c ⁻¹ᵁ U) (fun i => homOfLE i.2.2) ?_ _ _ ?_
  · intro x hx
    obtain ⟨V, hV, hxV, hVU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp W.isBasis_affineOpens hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV, hVU⟩, hxV⟩
  · rintro ⟨V, hV, hVU⟩
    have key := cech_section_local_split hP hS hT p q s c J σ hσ hsp U hU V hV hVU b
    refine key.trans ((Finset.sum_congr rfl fun j _ => ?_).trans (map_sum (W.presheaf.map (homOfLE hVU).op).hom _ _).symm)
    change _ = ((σ j).app (s ⁻¹ᵁ U) ≫ W.presheaf.map (homOfLE (GlobalTheory.GalTrace.preimage_le (hσ j) U)).op ≫ W.presheaf.map (homOfLE hVU).op).hom b
    rw [← Functor.map_comp, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHodgeGood
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pHodgeGood :
    HodgeTr → HodgeInj → HodgeGood := by
  intro hT hI k _ _ i j
  refine ⟨?_, ?_⟩
  · intro Z W p r c hc G _ _ a h
    obtain ⟨h1, h2, h3, -⟩ := h
    haveI := h1
    haveI := h2
    haveI := h3
    exact hI k i j p r c hc
  · intro Z Y p q s _ _ hs
    exact ⟨hodgeTrace hs i j, hT k i j p q s hs⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHodgeTr
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pHodgeTr :
    (∀ (k : Type) [Field k] {Z Y W : Scheme.{0}} (p : Z ⟶ sp k) (q : Y ⟶ sp k) (r : W ⟶ sp k) (s : Y ⟶ Z) [IsFinite s] [Etale s] (c : W ⟶ Z) (J : Type) [Fintype J] (σ : J → (W ⟶ Y)) (hσ : ∀ j, σ j ≫ s = c), Splits s c σ → ∀ (U : Z.Opens) (hU : IsAffineOpen U) (b : GlobalTheory.CechDR.Sec q (s ⁻¹ᵁ U)), GlobalTheory.HodgeCoh.appSec p r c U (secTrace p q hU b) = ∑ j, GlobalTheory.CechDR.Sec.res r (GlobalTheory.GalTrace.preimage_le (hσ j) U) (GlobalTheory.HodgeCoh.appSec q r (σ j) (s ⁻¹ᵁ U) b)) → HodgeTr := by
  intro h k _ a b Z Y p q s _ _ hs W r c hc J _ σ hσq hsp x
  obtain ⟨hσ, _⟩ := hsp
  have hom := GlobalTheory.GalTrace.omegaTrace_omegaPull (k := k) hs hc Finset.univ hσ hσq
    (fun U hU b => by simpa using h k p q r s c J σ hσ ⟨hσ, ‹_›⟩ U hU b) a
  exact GlobalTheory.GalTrace.hodgePull_hodgeTrace hs hc Finset.univ hσ hσq a hom b x
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PLiesOp
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pLiesOp :
    LiesGen → LiesAbs.{u} → LiesOp.{u} := by
  intro hGen hAbs k L O _ _ _ _ H θ C g D s t hst m d hL hd R _ T hT tr trg htr htrg x
  obtain ⟨κ, h, hκt, hfet⟩ := hGen C g s t hst m hL
  exact hAbs T hT _ _ _ _ (piK C) (piK_snd C) (H.s g) (H.t g) (H.comm g) _ _
    (bcMap_snd _ _ _) κ h d m rfl (bcMap_snd _ _ _) hκt hd hfet tr trg htr htrg x
end

