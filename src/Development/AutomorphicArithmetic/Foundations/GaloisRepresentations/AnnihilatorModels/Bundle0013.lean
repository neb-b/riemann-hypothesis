module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0011
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0012
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.HeckeCl
section
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV CrystallineSemistableComparison UpperTheory.Ru.crystallineComparison UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen)

namespace UpperTheory.Gal.crystallineComparison.Br

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {L : Type} [Field L] {H : HTower K} {θ : H.Γ → L}

def mdl (C : Cover H θ (OK l K)) : Model l K := ⟨C.Y, C.p⟩

def inTot (M : Model l K) (j : ℕ) : M.V j →ₗ[ℚ_[l]] Htot l M.spc :=
  DirectSum.lof ℚ_[l] ℤ (fun n : ℤ => HQ l M.spc n 0) (j : ℤ)

def piTot (C : Cover H θ (OK l K)) : Htot l (mdl C).spc →ₗ[ℚ_[l]] Htot l (sch.obj (H.geomZ (PadicAlgCl l))) :=
  (etG l K (PadicAlgCl l)).pull (piK C) (piK_snd C)

def GenFEt : Prop := ∀ (l : ℕ) (O k : Type) [CommRing O] [Field k] [Algebra O k], (l : k) ≠ 0 → ∀ {Y : Scheme.{0}} (p : Y ⟶ sp O)
  (T : Corr l Y), FEt (bcMap (gen O k) T.p (rfl : T.p ≫ p = _)) T.d

def TrTot : Prop := ∀ (l : ℕ) [Fact l.Prime] {B Z Y : Scheme.{0}} (p : Z ⟶ B) (q : Y ⟶ B) (s : Y ⟶ Z)
  (tr : ∀ n : ℤ, HQ l (sch.obj Y) n 0 →ₗ[ℚ_[l]] HQ l (sch.obj Z) n 0), (∀ n, (etn l B n 0).IsTr p q s (tr n)) →
  (et l B).IsTr p q s (DirectSum.lmap tr)

def TrBc : Prop := ∀ {B B' : Scheme.{0}} {R : Type} [Field R] (T : Th.{1} B R) (g : B ⟶ B') {Z Y : Scheme.{0}} (p : Z ⟶ B') (q : Y ⟶ B')
  (s : Y ⟶ Z) [IsFinite s] [Etale s] (hs : s ≫ p = q) (tr), T.IsTr (pullback.snd p g) (pullback.snd q g) (bcMap g s hs) tr → (T.bc g).IsTr p q s tr

def TrPush : Prop := ∀ (l : ℕ) [Fact l.Prime] {B Z Y : Scheme.{0}} (p : Z ⟶ B) (q : Y ⟶ B) (s : Y ⟶ Z), s ≫ p = q → ∀ (n : ℤ)
  (tr : HQ l (sch.obj Y) n 0 →ₗ[ℚ_[l]] HQ l (sch.obj Z) n 0), (etn l B n 0).IsTr p q s tr → LateralTheory.EtaleTrace.IsPush l s n tr

def HeckeCl : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (L : Type) [Field L] (H : HTower K)
  (θ : H.Γ → L) (C : Cover H θ (OK l K)) (T : Corr l C.Y) (hr : T.r ≫ C.p = T.p ≫ C.p) (γ : H.Γ) (m d : ℕ), FEt (H.s γ) d →
  C.Lies γ T.p T.r m → ∃ A : ∀ j : ℕ, (mdl C).V j →ₗ[ℚ_[l]] (mdl C).V j, ∀ j, IsHk (mdl C) T hr j (A j) ∧
    ∀ v, hop l H (PadicAlgCl l) γ (piTot C (inTot (mdl C) j v)) = (m : ℚ_[l]) • piTot C (inTot (mdl C) j (A j v))

end UpperTheory.Gal.crystallineComparison.Br
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PCorrPull
section
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

open CategoryTheory.Limits in
theorem UpperTheory.Gal.crystallineComparison.corrPull_of :
    CorrPull := by
  intro l S S' Y Y' u f f' h hY T hT
  have Q := IsPullback.of_hasPullback T.p h
  have hw : (pullback.fst T.p h ≫ T.r) ≫ f = (pullback.snd T.p h ≫ f') ≫ u := by
    rw [Category.assoc, hT, ← Category.assoc, pullback.condition, Category.assoc, hY.w,
      Category.assoc]
  have hfin : IsFinite (pullback.snd T.p h) := by
    have := T.fin
    exact MorphismProperty.of_isPullback Q this
  have het : Etale (pullback.snd T.p h ∣_ Y'.basicOpen (l : Γ(Y', ⊤))) := by
    have hle : Y'.basicOpen (l : Γ(Y', ⊤)) ≤ h ⁻¹ᵁ Y.basicOpen (l : Γ(Y, ⊤)) :=
      le_of_eq (by rw [Scheme.preimage_basicOpen_top, map_natCast])
    let k := Y'.homOfLE hle ≫ h ∣_ Y.basicOpen (l : Γ(Y, ⊤))
    have e1 : k ≫ (Y.basicOpen (l : Γ(Y, ⊤))).ι = (Y'.basicOpen (l : Γ(Y', ⊤))).ι ≫ h := by
      simp only [k, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc]
    have A := (isPullback_morphismRestrict (pullback.snd T.p h) (Y'.basicOpen (l : Γ(Y', ⊤)))).flip
    have outer := A.paste_horiz Q
    have R := (isPullback_morphismRestrict T.p (Y.basicOpen (l : Γ(Y, ⊤)))).flip
    have hw2 : ((pullback.snd T.p h ⁻¹ᵁ Y'.basicOpen (l : Γ(Y', ⊤))).ι ≫ pullback.fst T.p h) ≫ T.p
        = (pullback.snd T.p h ∣_ Y'.basicOpen (l : Γ(Y', ⊤)) ≫ k) ≫ (Y.basicOpen (l : Γ(Y, ⊤))).ι := by
      simp only [Category.assoc, pullback.condition, e1, morphismRestrict_ι_assoc]
    have outer' : IsPullback (R.lift _ _ hw2 ≫ (T.p ⁻¹ᵁ Y.basicOpen (l : Γ(Y, ⊤))).ι)
        (pullback.snd T.p h ∣_ Y'.basicOpen (l : Γ(Y', ⊤))) T.p (k ≫ (Y.basicOpen (l : Γ(Y, ⊤))).ι) := by
      rw [R.lift_fst, e1]
      exact outer
    have L := IsPullback.of_right outer' (R.lift_snd _ _ _) R
    exact MorphismProperty.of_isPullback L T.et
  have hdeg : ∀ (K : Type) [Field K] [IsAlgClosed K], (l : K) ≠ 0 →
      ∀ (y : Spec (CommRingCat.of K) ⟶ Y'),
        Nat.card { z // z ≫ pullback.snd T.p h = y } = T.d := by
    intro K _ _ hl y
    rw [← T.deg K hl (y ≫ h)]
    refine Nat.card_congr
      { toFun := fun z => ⟨z.1 ≫ pullback.fst T.p h, by rw [Category.assoc, pullback.condition, ← Category.assoc, z.2]⟩
        invFun := fun z => ⟨Q.lift z.1 y z.2, Q.lift_snd _ _ _⟩
        left_inv := ?_
        right_inv := ?_ }
    · intro z
      apply Subtype.ext
      apply Q.hom_ext
      · simp
      · simp [z.2]
    · intro z
      apply Subtype.ext
      simp
  refine ⟨⟨pullback T.p h, pullback.snd T.p h, hY.lift _ _ hw, T.d, hfin, het, hdeg⟩,
    pullback.fst T.p h, Q.flip, hY.lift_fst _ _ _, hY.lift_snd _ _ _, rfl⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDvdOfNil
section
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.dvdOfNil_of :
    DvdOfNil := by
  classical
  intro K W _ _ _ _ _ M s u hu hnil
  obtain ⟨n, hn⟩ := hnil
  have hroot : ∀ r ∈ (LinearMap.charpoly M).roots, r ∈ s := by
    intro r hr
    have hev : M.HasEigenvalue r := (Module.End.hasEigenvalue_iff_isRoot_charpoly M r).2
      ((Polynomial.mem_roots (LinearMap.charpoly_monic M).ne_zero).1 hr)
    obtain ⟨v, hv⟩ := hev.exists_hasEigenvector
    have h1 := Module.End.aeval_apply_of_hasEigenvector
      (p := (Polynomial.C u * rootPol s) ^ n) hv
    rw [map_pow, hn, LinearMap.zero_apply] at h1
    have h2 : ((Polynomial.C u * rootPol s) ^ n).eval r = 0 :=
      (smul_eq_zero.1 h1.symm).resolve_right hv.2
    rw [Polynomial.eval_pow, Polynomial.eval_mul, Polynomial.eval_C] at h2
    have h3 : (rootPol s).eval r = 0 :=
      (mul_eq_zero.1 (pow_eq_zero_iff'.1 h2).1).resolve_left hu
    unfold rootPol at h3
    rw [Polynomial.eval_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.map_map] at h3
    obtain ⟨a, ha, hra⟩ := Multiset.mem_map.1 h3
    simp only [Function.comp_apply, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] at hra
    rw [sub_eq_zero.1 hra]
    exact ha
  set m := (LinearMap.charpoly M).roots.card with hm
  refine ⟨m, ?_⟩
  have hcp : ((LinearMap.charpoly M).roots.map fun a => Polynomial.X - Polynomial.C a).prod
      = LinearMap.charpoly M :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (LinearMap.charpoly_monic M)
      IsAlgClosed.card_roots_eq_natDegree
  have hpow : rootPol s ^ m = ((m • s).map fun a => Polynomial.X - Polynomial.C a).prod := by
    unfold rootPol
    rw [Multiset.map_nsmul, Multiset.prod_nsmul]
  rw [← hcp, hpow]
  apply Multiset.prod_dvd_prod_of_le
  apply Multiset.map_le_map
  rw [Multiset.le_iff_count]
  intro a
  rw [Multiset.count_nsmul]
  by_cases ha : a ∈ (LinearMap.charpoly M).roots
  · have hs : 1 ≤ s.count a := Multiset.one_le_count_iff_mem.2 (hroot a ha)
    calc (LinearMap.charpoly M).roots.count a ≤ m := Multiset.count_le_card _ _
      _ = m * 1 := (mul_one m).symm
      _ ≤ m * s.count a := Nat.mul_le_mul_left m hs
  · rw [Multiset.count_eq_zero.2 ha]
    exact Nat.zero_le _
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PPtIdBC
section
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private lemma mem_basicOpen_fn {O : Type} [CommRing O] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of O)) (a : O) (x : Y) :
    x ∈ Y.basicOpen (fn f a) ↔ a ∉ (f x).asIdeal := by
  have h1 : f ⁻¹ᵁ (Spec (CommRingCat.of O)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of O)).inv a)
      = Y.basicOpen (fn f a) := Scheme.preimage_basicOpen_top f _
  rw [← h1, basicOpen_eq_of_affine]
  exact Iff.rfl

private lemma flat_h {O O' : Type} [CommRing O] [CommRing O'] (σ : O →+* O') (hσ : σ.Flat)
    {Y Y' : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of O)} {f' : Y' ⟶ Spec (CommRingCat.of O')} {h : Y' ⟶ Y}
    (hp : IsPullback h f' f (Spec.map (CommRingCat.ofHom σ))) : Flat h := by
  have : Flat (Spec.map (CommRingCat.ofHom σ)) := Flat.SpecMap_iff.2 hσ
  exact MorphismProperty.of_isPullback hp.flip this

private lemma genPt_h {O O' : Type} [CommRing O] [CommRing O'] (σ : O →+* O') (hσ : σ.Flat) (ϖ : O) (ϖ' : O')
    (hr : ∀ P : Ideal O', P.IsPrime → (σ ϖ ∈ P ↔ ϖ' ∈ P))
    {Y Y' : Scheme.{0}} {f : Y ⟶ Spec (CommRingCat.of O)} {f' : Y' ⟶ Spec (CommRingCat.of O')} {h : Y' ⟶ Y}
    (hp : IsPullback h f' f (Spec.map (CommRingCat.ofHom σ))) (x : Y') (hx : GenPt (fn f' ϖ') x) :
    GenPt (fn f ϖ) (h x) := by
  have key : ∀ w : Y', w ∈ Y'.basicOpen (fn f' ϖ') ↔ h w ∈ Y.basicOpen (fn f ϖ) := by
    intro w
    rw [mem_basicOpen_fn, mem_basicOpen_fn]
    have e : f (h w) = (Spec.map (CommRingCat.ofHom σ)) (f' w) := by
      have := congrArg (fun t => t w) (congrArg (fun t : Y' ⟶ _ => (t : Y' → _)) hp.w)
      simpa using this
    rw [e]
    have := hr (f' w).asIdeal (f' w).isPrime
    change ϖ' ∉ (f' w).asIdeal ↔ σ ϖ ∉ (f' w).asIdeal
    exact (not_congr this).symm
  have := flat_h σ hσ hp
  refine ⟨fun hb => hx.1 ((key x).2 hb), fun x' hx' hs => ?_⟩
  obtain ⟨w, hw, rfl⟩ := Flat.generalizingMap h hs
  have := hx.2 w (fun hb => hx' ((key w).1 hb)) hw
  rw [this]

private lemma twist_comp {κ : Type} [CommRing κ] (φ : κ →+* κ) {Y Y' : Scheme.{0}} (h : Y' ⟶ Y)
    (x : Spec (CommRingCat.of κ) ⟶ Y') (m : ℕ) :
    (twist φ Y)^[m] (x ≫ h) = (twist φ Y')^[m] x ≫ h := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ← ih]
    simp only [twist, Category.assoc]

private lemma twist_base {κ : Type} [CommRing κ] (φ : κ →+* κ) {S Y' : Scheme.{0}} (f' : Y' ⟶ S)
    (β : Spec (CommRingCat.of κ) ⟶ S) (hβ : Spec.map (CommRingCat.ofHom φ) ≫ β = β)
    (x : Spec (CommRingCat.of κ) ⟶ Y') (hx : x ≫ f' = β) (m : ℕ) :
    (twist φ Y')^[m] x ≫ f' = β := by
  induction m generalizing x with
  | zero => exact hx
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    refine ih _ ?_
    simp only [twist, Category.assoc, hx, hβ]

private lemma beta_fix {O' V : Type} [CommRing O'] [CommRing V] [IsLocalRing V] (q : ℕ) (ϖ' : O')
    (hq : ∀ a : O', a ^ q - a ∈ Ideal.span {ϖ'})
    (φ : IsLocalRing.ResidueField V →+* IsLocalRing.ResidueField V) (hφ : ∀ a, φ a = a ^ q)
    (c : CommRingCat.of O' ⟶ CommRingCat.of V)
    (hc : ϖ' ∈ (IsLocalRing.maximalIdeal V).comap c.hom) :
    Spec.map (CommRingCat.ofHom φ) ≫ resPt V ≫ Spec.map c = resPt V ≫ Spec.map c := by
  rw [resPt, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext a
  have h0 : IsLocalRing.residue V (c.hom ϖ') = 0 := (IsLocalRing.residue_eq_zero_iff _).2 hc
  have h1 : IsLocalRing.residue V (c.hom (a ^ q - a)) = 0 := by
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 (hq a)
    rw [← hb, map_mul, map_mul, h0, mul_zero]
  simp only [map_sub, map_pow, sub_eq_zero] at h1
  simpa [hφ] using h1

private lemma closed_mem {O' V : Type} [CommRing O'] [CommRing V] [IsLocalRing V] (ϖ' : O')
    {Y' : Scheme.{0}} (f' : Y' ⟶ Spec (CommRingCat.of O')) (y : Spec (CommRingCat.of V) ⟶ Y')
    (c : CommRingCat.of O' ⟶ CommRingCat.of V) (hc : y ≫ f' = Spec.map c)
    (hx : y (IsLocalRing.closedPoint V) ∉ Y'.basicOpen (fn f' ϖ')) :
    ϖ' ∈ (IsLocalRing.maximalIdeal V).comap c.hom := by
  rw [mem_basicOpen_fn, not_not] at hx
  have e : f' (y (IsLocalRing.closedPoint V)) = (Spec.map c) (IsLocalRing.closedPoint V) := by
    rw [← hc]; rfl
  rw [e] at hx
  exact hx

theorem UpperTheory.Gal.crystallineComparison.ptIdBC_of :
    PtIdBC := by
  classical
  intro l q n O O' _ _ σ hσ ϖ ϖ' hr hq Y Y' f f' h hp T T' g hg hrr hf hId V _ _ _ _ hl y hG φ hφ I _ z hz
  have hG' : GenPt (fn f ϖ) ((y ≫ h) (IsLocalRing.closedPoint V)) := genPt_h σ hσ ϖ ϖ' hr hp _ hG
  let z' : ∀ j, I j → (T j).Sec (y ≫ h) := fun j i => ⟨(z j i).1 ≫ g j, by
    rw [Category.assoc, ← (hg j).w, ← Category.assoc, (z j i).2]⟩
  have hz' : ∀ j, Function.Bijective (z' j) := by
    intro j
    constructor
    · intro i₁ i₂ e
      have e' : (z j i₁).1 ≫ g j = (z j i₂).1 ≫ g j := congrArg Subtype.val e
      refine (hz j).1 (Subtype.ext ((hg j).hom_ext ?_ e'))
      rw [(z j i₁).2, (z j i₂).2]
    · intro w
      obtain ⟨i, hi⟩ := (hz j).2 ⟨(hg j).lift y w.1 w.2.symm, (hg j).lift_fst _ _ _⟩
      refine ⟨i, Subtype.ext ?_⟩
      change (z j i).1 ≫ g j = w.1
      rw [hi]
      exact (hg j).lift_snd _ _ _
  have key := hId V hl (y ≫ h) hG' φ hφ I z' hz'
  let c : CommRingCat.of O' ⟶ CommRingCat.of V := Spec.preimage (y ≫ f')
  have hc : y ≫ f' = Spec.map c := (Spec.map_preimage _).symm
  have hmem := closed_mem ϖ' f' y c hc hG.1
  let β : Spec (CommRingCat.of (IsLocalRing.ResidueField V)) ⟶ Spec (CommRingCat.of O') := resPt V ≫ y ≫ f'
  have hβ : Spec.map (CommRingCat.ofHom φ) ≫ β = β := by
    simp only [β, hc]
    exact beta_fix q ϖ' hq φ hφ c hmem
  let Λ : (Spec (CommRingCat.of (IsLocalRing.ResidueField V)) ⟶ Y) → (Spec (CommRingCat.of (IsLocalRing.ResidueField V)) ⟶ Y') :=
    fun x => if hx : x ≫ f = β ≫ Spec.map (CommRingCat.ofHom σ) then hp.lift x β hx else resPt V ≫ y
  have hΛ : ∀ x' : Spec (CommRingCat.of (IsLocalRing.ResidueField V)) ⟶ Y', x' ≫ f' = β → Λ (x' ≫ h) = x' := by
    intro x' e
    have hx : (x' ≫ h) ≫ f = β ≫ Spec.map (CommRingCat.ofHom σ) := by
      rw [Category.assoc, hp.w, ← Category.assoc, e]
    simp only [Λ, dif_pos hx]
    apply hp.hom_ext
    · exact hp.lift_fst _ _ _
    · rw [hp.lift_snd, e]
  have hv : ∀ j i, (resPt V ≫ (z j i).1 ≫ (T' j).r) ≫ f' = β := by
    intro j i
    simp only [β, Category.assoc, hf j]
    rw [← Category.assoc (z j i).1, (z j i).2]
  have e1 : ∀ j i, resPt V ≫ (z' j i).1 ≫ (T j).r = (resPt V ≫ (z j i).1 ≫ (T' j).r) ≫ h := by
    intro j i
    change resPt V ≫ ((z j i).1 ≫ g j) ≫ (T j).r = _
    simp only [Category.assoc, hrr j]
  have hfin : ∀ (m : ℕ) j i, Λ ((twist φ Y)^[m] (resPt V ≫ (z' j i).1 ≫ (T j).r))
      = (twist φ Y')^[m] (resPt V ≫ (z j i).1 ≫ (T' j).r) := by
    intro m j i
    rw [e1, twist_comp]
    exact hΛ _ (twist_base φ f' β hβ _ (hv j i) m)
  unfold AltId at key ⊢
  have := congrArg (Multiset.map Λ) key
  rw [pts_map, pts_map] at this
  simpa only [hfin] using this
end

