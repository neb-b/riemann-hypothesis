module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.BaseFacts

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PCycExt
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId)
open UpperTheory.Gal UpperTheory.Gal.Mod

private lemma sp_twist {Ω Ω' : Type} [Field Ω] [Field Ω'] {Y : Scheme.{0}} (a : Ω →+* Ω')
    (φ : Ω →+* Ω) (φ' : Ω' →+* Ω') (hc : a.comp φ = φ'.comp a) (u : gp Ω ⟶ Y) :
    sp a ≫ twist φ Y u = twist φ' Y (sp a ≫ u) := by
  have h : sp a ≫ sp φ = sp φ' ≫ sp a := by
    simp only [UpperTheory.Gal.Mod.sp, ← AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
  change sp a ≫ sp φ ≫ u = sp φ' ≫ sp a ≫ u
  rw [← Category.assoc, h, Category.assoc]

private lemma sp_iter {Ω Ω' : Type} [Field Ω] [Field Ω'] {Y : Scheme.{0}} (a : Ω →+* Ω')
    (φ : Ω →+* Ω) (φ' : Ω' →+* Ω') (hc : a.comp φ = φ'.comp a) (m : ℕ) (u : gp Ω ⟶ Y) :
    sp a ≫ (twist φ Y)^[m] u = (twist φ' Y)^[m] (sp a ≫ u) := by
  induction m generalizing u with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, sp_twist a φ φ' hc]

private lemma pt_sp {Ω Ω' : Type} [Field Ω] [Field Ω'] {Z : Scheme.{0}} (a : Ω →+* Ω') (z : gp Ω ⟶ Z) :
    pt (sp a ≫ z) = pt z := by
  have h : ∀ c : gp Ω', (sp a ≫ z) c = z (sp a c) := fun c => Scheme.Hom.comp_apply _ _ _
  exact (h _).trans (congrArg (fun t : gp Ω => z t) (Subsingleton.elim (α := PrimeSpectrum Ω) _ _))

private lemma sum_eq (hF : FibExt) (hWt : TranscendenceTraces.WtPt) {p : ℕ} {Y : Scheme.{0}} (T : crystallineComparison.Corr p Y) (w : Wt T.Z)
    (hw : IsWt T.p w) (m : ℕ) {Ω Ω' : Type} [Field Ω] [IsAlgClosed Ω] [Field Ω'] [IsAlgClosed Ω'] (a : Ω →+* Ω')
    (φ : Ω →+* Ω) (φ' : Ω' →+* Ω') (hc : a.comp φ = φ'.comp a) (x y : gp Ω ⟶ Y) :
    ∑ᶠ z ∈ {z : gp Ω ⟶ T.Z | z ≫ T.p = x ∧ (twist φ Y)^[m] (z ≫ T.r) = y}, w Ω z =
      ∑ᶠ z ∈ {z : gp Ω' ⟶ T.Z | z ≫ T.p = sp a ≫ x ∧ (twist φ' Y)^[m] (z ≫ T.r) = sp a ≫ y}, w Ω' z := by
  haveI : IsFinite T.p := T.fin
  obtain ⟨-, hb, hinj⟩ := hF T.p Ω Ω' a x
  refine finsum_mem_eq_of_bijOn (fun z => sp a ≫ z) ⟨?_, ?_, ?_⟩ ?_
  · rintro z ⟨h1, h2⟩
    refine ⟨by simp only [Category.assoc, h1], ?_⟩
    rw [Category.assoc, ← sp_iter a φ φ' hc, h2]
  · intro z hz z' hz' h
    exact hb.injOn (show z ∈ fib T.p x from hz.1) (show z' ∈ fib T.p x from hz'.1) h
  · rintro z' ⟨h1, h2⟩
    obtain ⟨z, hz, rfl⟩ := hb.surjOn (show z' ∈ fib T.p (sp a ≫ x) from h1)
    refine ⟨z, ⟨hz, hinj _ _ ?_⟩, rfl⟩
    rw [sp_iter a φ φ' hc, ← Category.assoc] at *
    simpa [Category.assoc] using h2
  · intro z _
    exact hWt T.p w hw Ω Ω' z (sp a ≫ z) (pt_sp a z).symm

theorem UpperTheory.Gal.Mod.cycExt :
    FibExt → CycExt := by
  intro hF p q n Y T w hw Ω Ω' _ _ _ _ a φ φ' hc x
  have hWt : TranscendenceTraces.WtPt := TranscendenceTraces.all_holds.1.2.2.2.2.1
  have hs := fun (j : Fin (n + 1)) y => sum_eq hF hWt (T j) (w j) (hw j) (n - j) a φ φ' hc x y
  constructor
  · intro h y'
    by_cases hy : ∃ y : gp Ω ⟶ Y, y' = sp a ≫ y
    · obtain ⟨y, rfl⟩ := hy
      have := h y
      simp only [hs] at this
      exact this
    · refine Finset.sum_eq_zero fun j _ => ?_
      have : {z : gp Ω' ⟶ (T j).Z | z ≫ (T j).p = sp a ≫ x ∧ (twist φ' Y)^[n - j] (z ≫ (T j).r) = y'} = ∅ := by
        ext z'
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
        intro h1 h2
        haveI : IsFinite (T j).p := (T j).fin
        obtain ⟨z, -, rfl⟩ := (hF (T j).p Ω Ω' a x).2.1.surjOn (show z' ∈ fib (T j).p (sp a ≫ x) from h1)
        refine hy ⟨(twist φ Y)^[n - j] (z ≫ (T j).r), ?_⟩
        rw [sp_iter a φ φ' hc, ← h2, Category.assoc]
      rw [this]
      simp
  · intro h y
    have := h (sp a ≫ y)
    simp only [← hs] at this
    exact this
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PCycRes
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId)
open UpperTheory.Gal UpperTheory.Gal.Mod

private lemma finsum_fib {A P : Type*} [Finite A] (f : A → P) (S : Set P) (g : P → ℤ)
    (hg : ∀ z ∈ S, g z = (Nat.card {a // f a = z} : ℤ)) :
    ∑ᶠ z ∈ S, g z = (Nat.card {a // f a ∈ S} : ℤ) := by
  classical
  haveI := Fintype.ofFinite A
  have h1 : ∑ᶠ z ∈ S, g z = ∑ᶠ z ∈ S, (Nat.card {a // f a = z} : ℤ) :=
    finsum_mem_congr rfl hg
  set s : Finset A := Finset.univ.filter fun a => f a ∈ S with hs
  have h2 : ∑ᶠ z ∈ S, (Nat.card {a // f a = z} : ℤ) =
      ∑ z ∈ s.image f, (Nat.card {a // f a = z} : ℤ) := by
    apply finsum_mem_eq_sum_of_inter_support_eq
    ext z
    simp only [Set.mem_inter_iff, Finset.coe_image, Set.mem_image, Finset.mem_coe, hs,
      Finset.mem_filter, Finset.mem_univ, true_and, Function.mem_support, ne_eq]
    constructor
    · rintro ⟨hz, h⟩
      refine ⟨?_, h⟩
      have : Nonempty {a // f a = z} := by
        by_contra hne
        rw [not_nonempty_iff] at hne
        exact h (by simp)
      obtain ⟨⟨a, rfl⟩⟩ := this
      exact ⟨a, hz, rfl⟩
    · rintro ⟨⟨a, ha, rfl⟩, h⟩
      exact ⟨ha, h⟩
  rw [h1, h2, Nat.card_eq_fintype_card, Fintype.card_subtype, ← hs,
    Finset.card_eq_sum_card_image f s, Nat.cast_sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 2
  ext a
  simp only [hs, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro rfl
    obtain ⟨b, hb, hbz⟩ := Finset.mem_image.1 hz
    refine ⟨?_, rfl⟩
    rw [← hbz]
    exact (Finset.mem_filter.1 hb).2
  · exact fun h => h.2

private lemma co_eq (q : ℕ) {n : ℕ} (j : Fin (n + 1)) :
    co q j = (crystallineComparison.wEv q j : ℤ) - (crystallineComparison.wOd q j : ℤ) := by
  unfold co crystallineComparison.wEv crystallineComparison.wOd
  by_cases h : Even (j : ℕ)
  · simp [h, h.neg_one_pow]
  · have h' : Odd (j : ℕ) := Nat.not_even_iff_odd.1 h
    simp [h, h'.neg_one_pow]

theorem UpperTheory.Gal.Mod.cycRes :
    WtVal → CycRes := by
  intro hW p q n Y π T w hOne hPt V _ _ _ _ _ hp y hgen φ hφ y₀
  classical
  have hv := fun j => hW p Y (T j) (w j) (hOne j) V hp y
  haveI : ∀ j, Finite ((T j).Sec y) := fun j => (hv j).1
  letI : ∀ j, Fintype ((T j).Sec y) := fun j => Fintype.ofFinite _
  have hA := hPt V hp y hgen φ hφ (fun j => (T j).Sec y) (fun j => id)
    (fun j => Function.bijective_id)
  have hc := congrArg (Multiset.count y₀) hA
  simp only [crystallineComparison.pts, Multiset.count_sum', Multiset.count_nsmul, id] at hc
  have key : ∀ j : Fin (n + 1),
      ∑ᶠ z ∈ {z : gp (IsLocalRing.ResidueField V) ⟶ (T j).Z | z ≫ (T j).p = resPt V ≫ y ∧
        (twist φ Y)^[n - j] (z ≫ (T j).r) = y₀}, w j _ z =
      (Multiset.count y₀ (Finset.univ.val.map fun i : (T j).Sec y =>
        (twist φ Y)^[n - j] (resPt V ≫ i.1 ≫ (T j).r)) : ℤ) := by
    intro j
    rw [finsum_fib (fun i : (T j).Sec y => resPt V ≫ i.1)
      {z : gp (IsLocalRing.ResidueField V) ⟶ (T j).Z | z ≫ (T j).p = resPt V ≫ y ∧
        (twist φ Y)^[n - j] (z ≫ (T j).r) = y₀} (w j _)
      (fun z hz => (hv j).2 z hz.1)]
    congr 1
    rw [Multiset.count_map, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_def,
      Finset.filter_val]
    refine congrArg Multiset.card (Multiset.filter_congr fun i _ => ?_)
    have h1 : (resPt V ≫ i.1) ≫ (T j).p = resPt V ≫ y := by
      rw [Category.assoc, i.2]
    simp only [Set.mem_setOf_eq, h1, true_and, Category.assoc]
    exact eq_comm
  simp only [key, co_eq, sub_mul, Finset.sum_sub_distrib]
  rw [sub_eq_zero]
  exact_mod_cast hc
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PDenseGen
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId fn)
open GlobalTheory.SS.FrobField (absFrob)
open UpperTheory.Gal UpperTheory.Gal.Mod

private theorem mem_basicOpen_fn {O : Type} [CommRing O] {Y : Scheme.{0}} (g : Y ⟶ Spec (CommRingCat.of O)) (a : O) (y : Y) :
    y ∈ Y.basicOpen (fn g a) ↔ g y ∈ PrimeSpectrum.basicOpen a := by
  rw [fn, ← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  rfl

private theorem exists_min {S : Scheme.{0}} (x : S) : ∃ x' : S, x' ⤳ x ∧ ∀ t : S, t ⤳ x' → t = x' := by
  obtain ⟨Z, hZ, hxZ⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _
    (isIrreducible_singleton (x := x)).closure
  have hZc : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  have hZi : IsIrreducible Z := hZ.1
  set η := hZi.genericPoint with hη
  have hgen : closure {η} = Z := (hZi.isGenericPoint_genericPoint_closure).trans hZc.closure_eq
  refine ⟨η, ?_, ?_⟩
  · rw [specializes_iff_mem_closure, hgen]
    exact hxZ (subset_closure rfl)
  · intro t ht
    have h1 : Z ⊆ closure {t} := by
      rw [← hgen]
      exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp ht))
        isClosed_closure
    have h2 : closure {t} = Z := subset_antisymm (hZ.2 isIrreducible_singleton.closure h1) h1
    have h3 : η ⤳ t := by
      rw [specializes_iff_mem_closure, hgen, ← h2]
      exact subset_closure rfl
    exact (ht.antisymm h3).eq

private theorem dense_generic_points {O A k : Type} [CommRing O] [Field A] [Field k] (q : O →+* A) (hq : Function.Surjective q)
    (β₀ : A →+* k) (ϖ : O) (hϖ : RingHom.ker q = Ideal.span {ϖ}) (Y S : Scheme.{0}) (g : Y ⟶ Spec (CommRingCat.of O))
    (s : S ⟶ Y) (bS : S ⟶ gp k) (hpb : IsPullback s bS g (sp (β₀.comp q))) :
    Dense {x : S | crystallineComparison.GenPt (fn g ϖ) (s x)} := by
  classical
  have hcomp : Mod.sp (β₀.comp q) = Mod.sp β₀ ≫ Mod.sp q := by
    simp only [Mod.sp, CommRingCat.ofHom_comp, Spec.map_comp]
  haveI : IsClosedImmersion (Mod.sp q) := IsClosedImmersion.spec_of_surjective _ hq
  haveI hτ : Flat (Mod.sp β₀) := Flat.SpecMap_iff.mpr (RingHom.Flat.of_isField (Field.toIsField A) _)
  have hsq : s ≫ g = (bS ≫ Mod.sp β₀) ≫ Mod.sp q := by
    rw [Category.assoc, ← hcomp]
    exact hpb.w
  have hφi : pullback.lift s (bS ≫ Mod.sp β₀) hsq ≫ pullback.fst g (Mod.sp q) = s :=
    pullback.lift_fst _ _ _
  have hφπ : pullback.lift s (bS ≫ Mod.sp β₀) hsq ≫ pullback.snd g (Mod.sp q) = bS ≫ Mod.sp β₀ :=
    pullback.lift_snd _ _ _
  set φ := pullback.lift s (bS ≫ Mod.sp β₀) hsq with hφ
  have hφpb : IsPullback φ bS (pullback.snd g (Mod.sp q)) (Mod.sp β₀) := by
    refine IsPullback.of_right ?_ hφπ (IsPullback.of_hasPullback g (Mod.sp q))
    rw [hφi, ← hcomp]
    exact hpb
  haveI : Flat φ := MorphismProperty.of_isPullback hφpb.flip hτ
  have hgenφ : GeneralizingMap φ := Flat.generalizingMap φ
  have hind : Topology.IsInducing (pullback.fst g (Mod.sp q)) :=
    (pullback.fst g (Mod.sp q)).isClosedEmbedding.isInducing
  have memV : ∀ y : Y, y ∉ Y.basicOpen (fn g ϖ) ↔ ϖ ∈ (g y).asIdeal := by
    intro y
    rw [mem_basicOpen_fn]
    change ¬ (ϖ ∉ (g y).asIdeal) ↔ _
    exact not_not
  have hϖker : ϖ ∈ RingHom.ker q := by
    rw [hϖ]
    exact Ideal.mem_span_singleton_self ϖ
  have hV_of : ∀ p : ↥(pullback g (Mod.sp q)),
      pullback.fst g (Mod.sp q) p ∉ Y.basicOpen (fn g ϖ) := by
    intro p
    rw [memV]
    have h1 : g (pullback.fst g (Mod.sp q) p) = Mod.sp q (pullback.snd g (Mod.sp q) p) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    rw [h1]
    show ϖ ∈ Ideal.comap q _
    rw [Ideal.mem_comap, RingHom.mem_ker.mp hϖker]
    exact Ideal.zero_mem _
  have hV_to : ∀ y : Y, y ∉ Y.basicOpen (fn g ϖ) → y ∈ Set.range (pullback.fst g (Mod.sp q)) := by
    intro y hy
    rw [memV] at hy
    rw [Scheme.Pullback.range_fst]
    show g y ∈ Set.range (PrimeSpectrum.comap q)
    rw [range_comap_of_surjective _ q hq, hϖ]
    exact (PrimeSpectrum.mem_zeroLocus (g y) _).mpr
      (SetLike.coe_subset_coe.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hy))
  rw [dense_iff_inter_open]
  rintro U hU ⟨x, hx⟩
  obtain ⟨x', hx'x, hmin⟩ := exists_min x
  refine ⟨x', hx'x.mem_open hU hx, ?_⟩
  have hsx : s x' = pullback.fst g (Mod.sp q) (φ x') := by
    rw [← Scheme.Hom.comp_apply, hφi]
  refine ⟨hsx ▸ hV_of _, ?_⟩
  intro y' hy' hspec
  obtain ⟨p', rfl⟩ := hV_to y' hy'
  rw [hsx] at hspec ⊢
  have hp : p' ⤳ φ x' := hind.specializes_iff.mp hspec
  obtain ⟨x'', hx'', hφx''⟩ := hgenφ hp
  rw [hmin x'' hx''] at hφx''
  rw [hφx'']

theorem UpperTheory.Gal.Mod.denseGen :
    DenseGen := by
  intro O _ _ _ ϖ hϖ k _ β hβ Y S g s bS hpb
  obtain ⟨A, _, q, hq, β₀, hker, hβeq⟩ : ∃ (A : Type) (_ : Field A) (q : O →+* A),
      Function.Surjective q ∧ ∃ β₀ : A →+* k, RingHom.ker q = Ideal.span {ϖ} ∧ β₀.comp q = β := by
    haveI hmax : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
    refine ⟨O ⧸ Ideal.span {ϖ}, Ideal.Quotient.field _, Ideal.Quotient.mk _,
      Ideal.Quotient.mk_surjective, Ideal.Quotient.lift _ β (fun a ha => by
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
        simp [hβ]), Ideal.mk_ker, Ideal.Quotient.lift_comp_mk _ _ _⟩
  subst hβeq
  exact dense_generic_points q hq β₀ ϖ hker Y S g s bS hpb
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.PFrobTors
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.Et
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId fn)
open GlobalTheory.SS.FrobField (absFrob)
open UpperTheory.Gal UpperTheory.Gal.Mod

namespace UpperTheory.Gal.Mod.FrobeniusTorsors

open UpperTheory.Gal.TranscendenceTraces GlobalTheory.SS.FrobField

private theorem prim_pow {m : ℕ} {A : Type} [CommRing A] (ζ : Prim m A) : ζ.1 ^ m = 1 := by
  obtain ⟨g, hg⟩ := Polynomial.cyclotomic.dvd_X_pow_sub_one m ℤ
  have h := congrArg (Polynomial.aeval ζ.1) hg
  rw [map_mul, ζ.2.2, zero_mul] at h
  simpa [sub_eq_zero] using h

private theorem prim_ex (m : ℕ) [NeZero m] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (hm : IsUnit (m : Ω)) :
    Nonempty (Prim m Γ(gp Ω, ⊤)) := by
  haveI : NeZero (m : Ω) := ⟨hm.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  refine ⟨Prim.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom ⟨ζ, hm, ?_⟩⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact hζ.isRoot_cyclotomic (NeZero.pos m)

private theorem tw_sub (m : ℕ) [NeZero m] (hm : m = 1) (i : ℤ) {U : Scheme.{0}} (a b : Sec (tw m i) U) : a = b := by
  subst hm
  have e : (1 : ULift.{1} (ZMod 1)) = 0 := Subsingleton.elim _ _
  rw [← one_smul (ULift.{1} (ZMod 1)) a, ← one_smul (ULift.{1} (ZMod 1)) b, e, zero_smul, zero_smul]

private theorem frob_top (Ω : Type) [Field Ω] (p f : ℕ) (hp : p.Prime) (h : (p : Γ(gp Ω, ⊤)) = 0) (c : Γ(gp Ω, ⊤)) :
    (absFrob (gp Ω) p f hp h).appTop.hom c = c ^ p ^ f := rfl

private theorem frob_pt (m : ℕ) [NeZero m] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p f : ℕ) (hp : p.Prime)
    (h : (p : Γ(gp Ω, ⊤)) = 0) (hm : IsUnit (m : Ω)) (y : Sec (tw m 0) (gp Ω)) :
    Sec.res (absFrob (gp Ω) p f hp h) y = y := by
  obtain ⟨ζ⟩ := prim_ex m Ω hm
  obtain ⟨φ, -, hφ⟩ := secFun_holds m 0 (gp Ω) ζ y
  have hI := GlobalTheory.T.tateTwist_sections_locally_generated m 0
  have key : Sec.res (absFrob (gp Ω) p f hp h) (twGen 0 ζ) = twGen 0 ζ := by
    rw [hI.2.2.2.1]
    by_cases h1 : m = 1
    · exact tw_sub m h1 0 _ _
    · have hpΩ : (p : Ω) = 0 := by
        have := congrArg (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom h
        rw [map_natCast, map_zero] at this
        exact this
      have hcop : Nat.Coprime (p ^ f) m := by
        refine Nat.Coprime.pow_left f ((Nat.Prime.coprime_iff_not_dvd hp).2 ?_)
        rintro ⟨k, hk⟩
        apply hm.ne_zero
        rw [hk, Nat.cast_mul, hpΩ, zero_mul]
      haveI : Fact (1 < m) := ⟨by
        have := NeZero.ne m
        omega⟩
      rw [hI.2.2.2.2.1 (gp Ω) ζ _ (ZMod.unitOfCoprime (p ^ f) hcop)]
      · rw [zpow_zero, Units.val_one, ZMod.val_one, one_smul]
      · show (absFrob (gp Ω) p f hp h).appTop.hom ζ.1 = ζ.1 ^ ((ZMod.unitOfCoprime (p ^ f) hcop : ZMod m)).val
        rw [frob_top, ZMod.coe_unitOfCoprime, ZMod.val_natCast]
        conv_lhs => rw [← Nat.mod_add_div (p ^ f) m]
        rw [pow_add, pow_mul, prim_pow ζ, one_pow, mul_one]
  apply ptInj_holds m 0
  intro Ω' _ _ x
  rw [res_res, hφ Ω' _, hφ Ω' x, ← res_res, key, Subsingleton.elim (pt (x ≫ absFrob (gp Ω) p f hp h)) (pt x)]

private theorem frob_sec (m : ℕ) [NeZero m] (U : Scheme.{0}) (p f : ℕ) (hp : p.Prime) (h : (p : Γ(U, ⊤)) = 0)
    (hm : IsUnit (m : Γ(U, ⊤))) (a : Sec (tw m 0) U) : Sec.res (absFrob U p f hp h) a = a := by
  refine ptInj_holds m 0 U _ _ fun Ω _ _ x => ?_
  have hΩ : (p : Γ(gp Ω, ⊤)) = 0 := cast_zero_of_hom x h
  have hmΩ : IsUnit (m : Ω) := by
    have h1 := (hm.map x.appTop.hom).map (Scheme.ΓSpecIso (.of Ω)).hom.hom
    simpa using h1
  rw [res_res, ← absFrob_nat x p f hp hΩ h, ← res_res]
  exact frob_pt m Ω p f hp hΩ hmΩ _

variable {X : Scheme.{0}}

private noncomputable def sc (A : Sq (𝟙 X)) : A.U ⟶ A.V :=
  A.pb.lift A.u (𝟙 _) (by simp)

private theorem sc_v (A : Sq (𝟙 X)) : sc A ≫ A.v = A.u := A.pb.lift_fst _ _ _

private theorem sc_r (A : Sq (𝟙 X)) : sc A ≫ A.r = 𝟙 _ := A.pb.lift_snd _ _ _

private theorem r_sc (A : Sq (𝟙 X)) : A.r ≫ sc A = 𝟙 _ := by
  refine A.pb.hom_ext ?_ ?_
  · rw [Category.assoc, sc_v, Category.id_comp, ← A.pb.w, Category.comp_id]
  · rw [Category.assoc, sc_r, Category.comp_id, Category.id_comp]

private theorem sc_nat {A B : Sq (𝟙 X)} (t : A.To B) : sc A ≫ t.k = t.g ≫ sc B := by
  refine B.pb.hom_ext ?_ ?_
  · rw [Category.assoc, t.hv, sc_v, Category.assoc, sc_v, t.hu]
  · rw [Category.assoc, t.hr, ← Category.assoc, sc_r, Category.id_comp, Category.assoc, sc_r, Category.comp_id]

private noncomputable def fk (p f : ℕ) (hp : p.Prime) (h : (p : Γ(X, ⊤)) = 0) (A : Sq (𝟙 X)) : A.U ⟶ A.V :=
  absFrob A.U p f hp (cast_zero_of_hom A.u h) ≫ sc A

private theorem fk_nat (p f : ℕ) (hp : p.Prime) (h : (p : Γ(X, ⊤)) = 0) {A B : Sq (𝟙 X)} (t : A.To B) :
    t.g ≫ fk p f hp h B = fk p f hp h A ≫ t.k := by
  unfold fk
  rw [← Category.assoc, ← absFrob_nat t.g p f hp (cast_zero_of_hom A.u h) (cast_zero_of_hom B.u h), Category.assoc,
    ← sc_nat, Category.assoc]

private noncomputable def fam0 (p f : ℕ) (hp : p.Prime) (h : (p : Γ(X, ⊤)) = 0) {R : Type} [CommRing R] (F : GlobalTheory.EtC.Shv R) :
    Fam0 (𝟙 X) F F where
  app A := (F.obj.map (fk p f hp h A).op).hom.toAddMonoidHom
  nat {A B} t a := (res_res t.g (fk p f hp h B) a).trans
    ((congrArg (fun e => Sec.res e a) (fk_nat p f hp h t)).trans (res_res (fk p f hp h A) t.k a).symm)

private noncomputable def fam (p f : ℕ) (hp : p.Prime) (h : (p : Γ(X, ⊤)) = 0) {R : Type} [CommRing R] (I : Cx R) :
    Fam (𝟙 X) I I where
  deg s := fam0 p f hp h (I.X s)
  comm A s t a := (map_res (I.d s t) (fk p f hp h A) a)

private theorem fk_self (p f : ℕ) (hp : p.Prime) (h : (p : Γ(X, ⊤)) = 0) :
    fk p f hp h (Sq.self (𝟙 X)) = absFrob X p f hp h := by
  unfold fk
  have h1 : sc (Sq.self (𝟙 X)) = 𝟙 _ := (Category.comp_id (sc (Sq.self (𝟙 X)))).symm.trans (sc_r (Sq.self (𝟙 X)))
  rw [h1]
  exact Category.comp_id _

private theorem fam_app (p f : ℕ) (hp : p.Prime) (h : (p : Γ(X, ⊤)) = 0) {R : Type} [CommRing R] (I : Cx R) (s : ℤ)
    (A : Sq (𝟙 X)) (a : Sec (I.X s) A.V) : ((fam p f hp h I).deg s).app A a = Sec.res (fk p f hp h A) a := rfl

private theorem fam_sums (m : ℕ) [NeZero m] (p f : ℕ) (hp : p.Prime) (h : (p : Γ(X, ⊤)) = 0) (hm : IsUnit (m : Γ(X, ⊤))) :
    (fam p f hp h (res _ (tw m 0))).Sums (Wt.const X 1) := by
  intro A a
  have hmU : IsUnit (m : Γ(A.U, ⊤)) := by simpa using hm.map A.u.appTop.hom
  refine ⟨Sec.res (sc A) a, ?_, fun Ω _ _ x => ?_⟩
  · rw [fam_app, ← map_res]
    refine congrArg (Sec.map (resι _ _)) ?_
    unfold fk
    rw [← res_res]
    exact frob_sec m A.U p f hp _ hmU _
  · have hf : fib A.r x = {x ≫ sc A} := by
      ext z
      constructor
      · intro hz
        have hz' : z ≫ A.r = x := hz
        rw [Set.mem_singleton_iff, ← hz', Category.assoc, r_sc, Category.comp_id]
      · rintro rfl
        change (x ≫ sc A) ≫ A.r = x
        rw [Category.assoc, sc_r, Category.comp_id]
    rw [hf, finsum_mem_singleton, res_res]
    exact (one_smul ℤ _).symm

end UpperTheory.Gal.Mod.FrobeniusTorsors

open UpperTheory.Gal.Mod.FrobeniusTorsors in
theorem UpperTheory.Gal.Mod.frobTors :
    FrobTors := by
  intro m _ X p f hp h hm k x
  have e1 := (TranscendenceTraces.trChar_holds m 0 (𝟙 X) (Wt.const X 1) (TranscendenceTraces.wtLin_holds.2.2 (𝟙 X) 1) hm).2.2 _
    (fam_sums m p f hp h hm) k
  have e2 := (TranscendenceTraces.trLin_holds m k 0).2.2 X 1 hm x
  rw [e1, one_smul] at e2
  obtain ⟨a, ha⟩ := (TranscendenceTraces.rpBasic_of _ (res _ (tw m 0)) X k).1 x
  have h1 := (TranscendenceTraces.rpBasic_of _ (res _ (tw m 0)) X k).2.2.2.1 X (absFrob X p f hp h) x a ha
  have h2 := (TranscendenceTraces.rpOp_of TranscendenceTraces.imgBasic_of) _ _ (fam p f hp h (res _ (tw m 0))) k x a ha
  rw [e2] at h2
  refine ((TranscendenceTraces.rpBasic_of _ _ X k).2.2.1 _ _ _ _ h1 h2).2.1 ?_
  exact (congrArg (fun e => Sec.res e a) (fk_self p f hp h)).symm
end

