module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsEtIdealOfPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0813
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1514

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PCrtMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev GlobalTheory.UPel.HT.ES
open UpperTheory.Gal.FiniteEtaleModels

set_option maxHeartbeats 1000000 in
theorem UpperTheory.Gal.FiniteEtaleModels.crtMul_holds :
    CrtMul := by
  intro p _ D R _ b N S s o 𝔞 𝔟 hab T l₁ l₂ h1 h2
  have hmon : ∀ c, IsMonHom (o.act.act c) := o.act.hom
  obtain ⟨a, ha, b', hb, habe⟩ : ∃ a ∈ 𝔞, ∃ b' ∈ 𝔟, a + b' = 1 := by
    have h1m : (1 : 𝓞 D.F) ∈ 𝔞 ⊔ 𝔟 := by
      rw [hab]
      exact Submodule.mem_top
    obtain ⟨a, ha, b', hb, h⟩ := Submodule.mem_sup.1 h1m
    exact ⟨a, ha, b', hb, h⟩
  have split : ∀ {X : Over S} (f : X ⟶ o.A),
      f ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) * f ≫ o.act.act (algebraMap (𝓞 D.F) D.O b') = f := by
    intro X f
    rw [← MonObj.comp_mul, ← o.act.add, ← map_add (f := _), habe, map_one, o.act.one, Category.comp_id]
  have gen : ∀ (I : Ideal (𝓞 D.F)) (c : 𝓞 D.F), c ∈ I → ∀ y : D.La,
      algebraMap (𝓞 D.F) D.O c • y ∈ wSub D I 1 := by
    intro I c hc y
    exact Submodule.subset_span ⟨c, by simpa using hc, y, rfl⟩
  have mulsub : ∀ (I J : Ideal (𝓞 D.F)) (c : 𝓞 D.F), c ∈ I → ∀ y ∈ wSub D J 1,
      algebraMap (𝓞 D.F) D.O c • y ∈ wSub D (I * J) 1 := by
    intro I J c hc y hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c', hc', z', rfl⟩ := hz
      rw [← mul_smul, ← map_mul]
      exact gen _ _ (Ideal.mul_mem_mul hc (by simpa using hc')) z'
    | zero =>
      rw [smul_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      rw [smul_add]
      exact Submodule.add_mem _ hx hy
    | smul o' x _ hx =>
      rw [← mul_smul, Algebra.commutes, mul_smul]
      exact Submodule.smul_mem _ _ hx
  have wmono : ∀ (I J : Ideal (𝓞 D.F)), I ≤ J → wSub D I 1 ≤ wSub D J 1 := by
    intro I J h
    apply Submodule.span_mono
    rintro z ⟨c, hc, z', rfl⟩
    exact ⟨c, by simpa using h (by simpa using hc), z', rfl⟩
  have kill : ∀ (I : Ideal (𝓞 D.F)) (l : D.La → (T ⟶ o.A)), IsEtLevOver o I 1 l →
      ∀ {X : Over S} (P : X ⟶ T) (y : D.La) (c : 𝓞 D.F), c ∈ I →
        (P ≫ l y) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
    intro I l hl X P y c hc
    rw [Category.assoc, ← hl.2.1, hl.2.2.1 _ (gen I c hc y), MonObj.comp_one]
  refine ⟨fun x y => ?_, fun c x => ?_, fun x hx => ?_, fun k _ _ x => ⟨fun y hy => ?_, fun g hg => ?_⟩⟩
  · dsimp only
    rw [h1.1, h2.1]
    exact mul_mul_mul_comm _ _ _ _
  · dsimp only
    rw [h1.2.1, h2.2.1, MonObj.mul_comp]
  · dsimp only
    have hxa : x ∈ wSub D 𝔞 1 := wmono (𝔞 * 𝔟) 𝔞 (Ideal.mul_le_left : 𝔞 * 𝔟 ≤ 𝔞) hx
    have hxb : x ∈ wSub D 𝔟 1 := wmono (𝔞 * 𝔟) 𝔟 (Ideal.mul_le_right : 𝔞 * 𝔟 ≤ 𝔟) hx
    rw [h1.2.2.1 x hxa, h2.2.2.1 x hxb]
    exact mul_one 1
  · dsimp only at hy
    rw [MonObj.comp_mul] at hy
    have hu : Over.homMk (U := Over.mk (x ≫ T.hom)) (V := T) x ≫ l₁ y = 1 := by
      have e1 := congrArg (· ≫ o.act.act (algebraMap (𝓞 D.F) D.O b')) hy
      simp only [MonObj.mul_comp, MonObj.one_comp, kill _ l₂ h2 _ _ _ hb, _root_.mul_one] at e1
      rw [← split (Over.homMk (U := Over.mk (x ≫ T.hom)) (V := T) x ≫ l₁ y), kill _ l₁ h1 _ _ _ ha, e1, _root_.one_mul]
    have hv : Over.homMk (U := Over.mk (x ≫ T.hom)) (V := T) x ≫ l₂ y = 1 := by
      rw [hu, _root_.one_mul] at hy
      exact hy
    have y1 := (h1.2.2.2 k x).1 y hu
    have y2 := (h2.2.2.2 k x).1 y hv
    have hsplit : y = algebraMap (𝓞 D.F) D.O a • y + algebraMap (𝓞 D.F) D.O b' • y := by
      rw [← add_smul, ← map_add (f := _), habe, map_one, one_smul]
    rw [hsplit]
    refine Submodule.add_mem _ (mulsub 𝔞 𝔟 a ha y y2) ?_
    have h3 := mulsub 𝔟 𝔞 b' hb y y1
    rwa [mul_comm] at h3
  · have hg' : ∀ c ∈ 𝔞 * 𝔟, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := fun c hc => hg c (by simpa using hc)
    have hk1 : ∀ c ∈ 𝔞, (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O b')) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
      intro c hc
      rw [Category.assoc, ← o.act.mul, ← map_mul]
      exact hg' _ (Ideal.mul_mem_mul hc hb)
    have hk2 : ∀ c ∈ 𝔟, (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
      intro c hc
      rw [Category.assoc, ← o.act.mul, ← map_mul, mul_comm]
      exact hg' _ (Ideal.mul_mem_mul ha hc)
    obtain ⟨y₁, hy₁⟩ := (h1.2.2.2 k x).2 (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O b'))
      (fun c hc => hk1 c (by simpa using hc))
    obtain ⟨y₂, hy₂⟩ := (h2.2.2.2 k x).2 (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a))
      (fun c hc => hk2 c (by simpa using hc))
    have e1 : (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O b')) ≫ o.act.act (algebraMap (𝓞 D.F) D.O b') =
        g ≫ o.act.act (algebraMap (𝓞 D.F) D.O b') := by
      conv_rhs => rw [← split (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O b'))]
      rw [hk1 a ha, _root_.one_mul]
    have e2 : (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) =
        g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) := by
      conv_rhs => rw [← split (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a))]
      rw [hk2 b' hb, _root_.mul_one]
    refine ⟨algebraMap (𝓞 D.F) D.O b' • y₁ + algebraMap (𝓞 D.F) D.O a • y₂, ?_⟩
    dsimp only
    rw [h1.1, h2.1, h1.2.2.1 _ (gen 𝔞 a ha y₂), h2.2.2.1 _ (gen 𝔟 b' hb y₁), _root_.mul_one, _root_.one_mul,
      h1.2.1, h2.2.1, MonObj.comp_mul, ← Category.assoc, ← Category.assoc, hy₁, hy₂, e1, e2, mul_comm]
    exact split g
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PCrtProj
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev GlobalTheory.UPel.HT.ES
open UpperTheory.Gal.FiniteEtaleModels

private lemma smul_mem_prod {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {𝔞 𝔟 : Ideal (𝓞 D.F)}
    {e : 𝓞 D.F} (he : e ∈ 𝔟) {x : D.La} (hx : x ∈ wSub D 𝔞 1) :
    algebraMap (𝓞 D.F) D.O e • x ∈ wSub D (𝔞 * 𝔟) 1 := by
  rw [wSub] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, hc, z', rfl⟩ := hz
    rw [smul_smul, ← map_mul]
    refine Submodule.subset_span ⟨e * c, ?_, z', rfl⟩
    rw [pow_one] at hc ⊢
    rw [mul_comm]
    exact Ideal.mul_mem_mul he hc
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    rw [smul_smul, Algebra.commutes, mul_smul]
    exact Submodule.smul_mem _ c ha

private lemma mem_of_mem_mul {A : Type} [CommRing A] {I J : Ideal A} {c : A} (h : c ∈ I * J) : c ∈ I :=
  Ideal.mul_le_left h

private lemma wSub_mul_le {p : ℕ} [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (𝔞 𝔟 : Ideal (𝓞 D.F)) :
    wSub D (𝔞 * 𝔟) 1 ≤ wSub D 𝔞 1 := by
  refine Submodule.span_mono ?_
  rintro z ⟨c, hc, z', rfl⟩
  rw [pow_one] at hc
  exact ⟨c, by rw [pow_one]; exact mem_of_mem_mul hc, z', rfl⟩

theorem UpperTheory.Gal.FiniteEtaleModels.crtProj_holds :
    CrtProj := by
  intro p _ D R _ b N S s o 𝔞 𝔟 e he he' T l h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hcomm : ∀ (c : D.O) (x : D.La), algebraMap (𝓞 D.F) D.O e • c • x =
      c • algebraMap (𝓞 D.F) D.O e • x := fun c x => by
    rw [smul_smul, Algebra.commutes, mul_smul]
  have he1 : 1 - e ∈ 𝔞 ^ 1 := by rwa [pow_one]
  unfold IsEtLevOver
  beta_reduce
  refine ⟨fun x y => ?_, fun c x => ?_, fun x hx => h3 _ (smul_mem_prod he hx),
    fun k _ _ x => ⟨fun y hy => ?_, fun g hg => ?_⟩⟩
  · rw [smul_add, h1]
  · rw [hcomm, h2]
  · have hE := wSub_mul_le D 𝔞 𝔟 ((h4 k x).1 _ hy)
    have hy' : y = algebraMap (𝓞 D.F) D.O (1 - e) • y + algebraMap (𝓞 D.F) D.O e • y := by
      rw [← add_smul, ← map_add (f := _), sub_add_cancel, map_one, one_smul]
    rw [hy']
    exact Submodule.add_mem _ (Submodule.subset_span ⟨1 - e, he1, y, rfl⟩) hE
  · obtain ⟨y, hy⟩ := (h4 k x).2 g (fun c hc => hg c (by
      rw [pow_one] at hc ⊢
      exact mem_of_mem_mul hc))
    refine ⟨y, ?_⟩
    rw [h2, ← Category.assoc, hy]
    have key : g = (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O (1 - e))) *
        (g ≫ o.act.act (algebraMap (𝓞 D.F) D.O e)) := by
      rw [← MonObj.comp_mul, ← o.act.add, ← map_add (f := _), sub_add_cancel, map_one, o.act.one,
        Category.comp_id]
    rw [hg (1 - e) he1, _root_.one_mul] at key
    exact key.symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PFinModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev GlobalTheory.UPel.HT.ES
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.finModel_holds :
    FinCover → FinModel := by
  intro cover p _ D R _ _ b N h3 hcop 𝔞 r h𝔞 M
  haveI : Smooth M.s := M.smooth.smooth
  haveI : IsLocallyNoetherian M.X := LocallyOfFiniteType.isLocallyNoetherian M.s
  obtain ⟨Y, q, u, mu, lev, act, hlev, hgal, hrep⟩ :=
    cover p D R b N 𝔞 r h3 hcop h𝔞 M.X M.s M.univ
  let E : EtModel b N 𝔞 r :=
    { X := Y, s := q ≫ M.s, univ := u, lv := lev, isLev := hlev
      rep := by
        intro T t o l hl
        obtain ⟨c, ⟨hc, ⟨mc⟩⟩, cuniq⟩ := M.rep T t o
        subst hc
        obtain ⟨f, ⟨hfq, m₂, hm₂⟩, funiq⟩ := hrep T c o mc l hl
        refine ⟨f, ⟨?_, m₂, hm₂⟩, ?_⟩
        · rw [← Category.assoc, hfq]
        · rintro f' ⟨hs, m', hm'⟩
          refine funiq f' ⟨?_, m', hm'⟩
          obtain ⟨mcomp⟩ := objMap_comp p D R b N T Y M.X (c ≫ M.s) (q ≫ M.s) M.s o u M.univ f' q m' mu
          exact cuniq (f' ≫ q) ⟨by rw [Category.assoc, ← hs], ⟨mcomp⟩⟩ }
  exact ⟨E, q, act, rfl, ⟨mu⟩, hgal⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PGrpFin
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev GlobalTheory.UPel.HT.ES
open UpperTheory.Gal.FiniteEtaleModels

private theorem quot_finite {p : ℕ} [Fact p.Prime] (D : Datum p) (𝔞 : Ideal (𝓞 D.F)) (r : ℕ) (h𝔞 : 𝔞 ≠ ⊥) :
    Finite (D.La ⧸ wSub D 𝔞 r) := by
  have hr : 𝔞 ^ r ≠ ⊥ := pow_ne_zero r h𝔞
  have hN0 : Ideal.absNorm (𝔞 ^ r) ≠ 0 := fun h => hr (Ideal.absNorm_eq_zero_iff.mp h)
  have hNmem : ((Ideal.absNorm (𝔞 ^ r) : ℕ) : 𝓞 D.F) ∈ 𝔞 ^ r := Ideal.absNorm_mem _
  haveI hLa : AddGroup.FG D.La := Module.Finite.iff_addGroup_fg.mp D.finLa
  haveI : AddGroup.FG (D.La ⧸ wSub D 𝔞 r) :=
    AddGroup.fg_of_surjective (f := (Submodule.mkQ (wSub D 𝔞 r)).toAddMonoidHom)
      (Submodule.mkQ_surjective _)
  apply AddCommGroup.finite_of_fg_torsion
  intro x
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective (wSub D 𝔞 r) x
  refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨Ideal.absNorm (𝔞 ^ r), Nat.pos_of_ne_zero hN0, ?_⟩
  rw [← map_nsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  apply Submodule.subset_span
  refine ⟨((Ideal.absNorm (𝔞 ^ r) : ℕ) : 𝓞 D.F), hNmem, z, ?_⟩
  rw [map_natCast, Nat.cast_smul_eq_nsmul]

theorem UpperTheory.Gal.FiniteEtaleModels.grpFin_holds :
    GrpFin := by
  intro p _ D 𝔞 r h𝔞
  haveI hQ : Finite (D.La ⧸ wSub D 𝔞 r) := quot_finite D 𝔞 r h𝔞
  refine ⟨hQ, ?_⟩
  exact Finite.of_injective
    (fun e : (D.La ⧸ wSub D 𝔞 r) ≃ₗ[D.O] D.La ⧸ wSub D 𝔞 r => (e : D.La ⧸ wSub D 𝔞 r → D.La ⧸ wSub D 𝔞 r))
    (fun a b h => LinearEquiv.ext (congrFun h))
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PIdealInd
section
namespace UpperTheory.Gal.FiniteEtaleModels

theorem idealInd_holds : IdealInd := by
  intro A _ _ Q P htop hpow hmul 𝔞
  induction 𝔞 using UniqueFactorizationMonoid.induction_on_coprime with
  | h0 => exact fun h => absurd rfl h
  | h1 hx =>
    rename_i x
    intro _ _
    rw [Ideal.isUnit_iff.1 hx]
    exact htop
  | hpr i hp =>
    rename_i w
    intro _ hQ
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [pow_zero, Ideal.one_eq_top]
      exact htop
    · have hmax : w.IsMaximal :=
        (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
      exact hpow w i hmax (hQ w hmax (Ideal.pow_le_self hi.ne'))
  | hcp hxy hx hy =>
    rename_i x y
    intro hne hQ
    have hx0 : x ≠ ⊥ := fun h => hne (by rw [h]; exact Ideal.bot_mul y)
    have hy0 : y ≠ ⊥ := fun h => hne (by rw [h]; exact Ideal.mul_bot x)
    have hsup : x ⊔ y = ⊤ :=
      Ideal.isUnit_iff.1 (hxy (Ideal.dvd_iff_le.2 le_sup_left) (Ideal.dvd_iff_le.2 le_sup_right))
    exact hmul x y hsup
      (hx hx0 fun w hw hle => hQ w hw (Ideal.mul_le_left.trans hle))
      (hy hy0 fun w hw hle => hQ w hw (Ideal.mul_le_right.trans hle))

end UpperTheory.Gal.FiniteEtaleModels
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PPlaceOf
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev GlobalTheory.UPel.HT.ES
open UpperTheory.Gal.FiniteEtaleModels

private lemma map_eq_zero_of_mem_max {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CharZero O] {k : Type} [Field k] [CharP k p] (β : O →+* k) {x : O}
    (hx : x ∈ IsLocalRing.maximalIdeal O) : β x = 0 := by
  have hprime : (RingHom.ker β).IsPrime := RingHom.ker_isPrime β
  have hp : ((p : ℕ) : O) ∈ RingHom.ker β := by
    rw [RingHom.mem_ker, map_natCast]
    exact CharP.cast_eq_zero k p
  have hne : RingHom.ker β ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hp
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hp)
  have hmax : (RingHom.ker β).IsMaximal := IsPrime.to_maximal_ideal hne
  have heq : RingHom.ker β = IsLocalRing.maximalIdeal O := IsLocalRing.eq_maximalIdeal hmax
  rw [← heq] at hx
  exact hx

private lemma exists_map_ker {p : ℕ} [Fact p.Prime] {F : Type} [Field F] [NumberField F]
    (J : Ideal (𝓞 F)) (hJ : J.IsMaximal) (hp : (p : 𝓞 F) ∈ J) (hne : J ≠ ⊥)
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] :
    ∃ φ : 𝓞 F →+* k, RingHom.ker φ = J := by
  classical
  letI : Field (𝓞 F ⧸ J) := Ideal.Quotient.field J
  have hpr : p.Prime := Fact.out
  haveI : CharP (𝓞 F ⧸ J) p := by
    rw [CharP.charP_iff_prime_eq_zero hpr]
    rw [← map_natCast (Ideal.Quotient.mk J), Ideal.Quotient.eq_zero_iff_mem]
    exact hp
  haveI : Finite (𝓞 F ⧸ J) := Ideal.finiteQuotientOfFreeOfNeBot J hne
  letI : Algebra (ZMod p) (𝓞 F ⧸ J) := ZMod.algebra _ p
  letI : Algebra (ZMod p) k := ZMod.algebra _ p
  haveI : Module.Finite (ZMod p) (𝓞 F ⧸ J) := Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic (ZMod p) (𝓞 F ⧸ J) := Algebra.IsAlgebraic.of_finite _ _
  let ψ : (𝓞 F ⧸ J) →ₐ[ZMod p] k := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨(ψ : (𝓞 F ⧸ J) →+* k).comp (Ideal.Quotient.mk J), ?_⟩
  rw [RingHom.ker_comp_of_injective _ (ψ : (𝓞 F ⧸ J) →+* k).injective, Ideal.mk_ker]

theorem UpperTheory.Gal.FiniteEtaleModels.placeOf_holds :
    PlaceOf := by
  intro p _ D O _ _ _ _ b r w hw hpO ha hUw htw 𝔞 h𝔞w
  have hpr : p.Prime := Fact.out
  have i0 : Fin D.a := ⟨0, by omega⟩
  have hρ : ∀ (k : Type) [Field k] [CharP k p] (β : O →+* k), β b.ρ = (r : k) := by
    intro k _ _ β
    have hm : b.t i0 (D.ω - (r : 𝓞 D.F)) ∈ IsLocalRing.maximalIdeal O :=
      htw i0 _ (hUw (sub_mem_uIdeal D r))
    have h0 := map_eq_zero_of_mem_max (p := p) β hm
    rw [map_sub, map_intCast, map_sub, map_intCast, b.t_ω, sub_eq_zero] at h0
    exact h0
  constructor
  · intro h
    obtain ⟨hne, hall⟩ := h
    have hrad : uIdeal D r ≤ 𝔞.radical := by
      rw [Ideal.radical_eq_sInf]
      refine le_sInf ?_
      rintro P ⟨hP𝔞, hPprime⟩
      have hPne : P ≠ ⊥ := by
        rintro rfl
        exact hne (le_bot_iff.mp hP𝔞)
      have hPmax : P.IsMaximal := Ideal.IsPrime.isMaximal hPprime hPne
      obtain ⟨_, hpP, _, hφ⟩ := hall P hPmax hP𝔞
      haveI : CharP (IsLocalRing.ResidueField O) p := by
        rw [CharP.charP_iff_prime_eq_zero hpr, ← map_natCast (IsLocalRing.residue O)]
        exact (IsLocalRing.residue_eq_zero_iff _).mpr hpO
      haveI : CharP (AlgebraicClosure (IsLocalRing.ResidueField O)) p := by
        rw [CharP.charP_iff_prime_eq_zero hpr,
          ← map_natCast (algebraMap (IsLocalRing.ResidueField O) (AlgebraicClosure _)),
          CharP.cast_eq_zero, map_zero]
      obtain ⟨φ, hker⟩ :=
        exists_map_ker (p := p) P hPmax hpP hPne (AlgebraicClosure (IsLocalRing.ResidueField O))
      let β : O →+* AlgebraicClosure (IsLocalRing.ResidueField O) :=
        (algebraMap _ _).comp (IsLocalRing.residue O)
      have h1 := hφ (AlgebraicClosure (IsLocalRing.ResidueField O)) β φ hker
      rw [hρ _ β] at h1
      have hsub : D.ω - (r : 𝓞 D.F) ∈ P := by
        rw [← hker, RingHom.mem_ker, map_sub, map_intCast, h1, sub_self]
      unfold uIdeal
      rw [Ideal.span_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact hpP
      · exact hsub
    exact Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  · rintro ⟨e, he⟩
    have hpe : ((p : ℕ) : 𝓞 D.F) ^ e ∈ uIdeal D r ^ e := Ideal.pow_mem_pow (p_mem_uIdeal D r) e
    refine ⟨?_, ?_⟩
    · intro h
      rw [h] at he
      have h0 := he hpe
      rw [Ideal.mem_bot] at h0
      have h00 : ((p : ℕ) : 𝓞 D.F) = 0 := eq_zero_of_pow_eq_zero h0
      exact hpr.ne_zero (by exact_mod_cast h00)
    · intro w' hw' h𝔞w'
      haveI := hw'.isPrime
      have hUw' : uIdeal D r ≤ w' := Ideal.IsPrime.le_of_pow_le (he.trans h𝔞w')
      have hne : w' ≠ w := by
        rintro rfl
        exact hw'.ne_top (top_le_iff.mp (h𝔞w ▸ sup_le h𝔞w' le_rfl))
      refine ⟨hw', hUw' (p_mem_uIdeal D r), ?_, ?_⟩
      · intro i
        by_contra hspan
        obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hspan
        have hMeq : M = IsLocalRing.maximalIdeal O := IsLocalRing.eq_maximalIdeal hM
        have hKtop : RingHom.ker ((IsLocalRing.residue O).comp (b.t i)) ≠ ⊤ := RingHom.ker_ne_top _
        have hwK : w ≤ RingHom.ker ((IsLocalRing.residue O).comp (b.t i)) := by
          intro x hx
          rw [RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
          exact htw i x hx
        have hw'K : w' ≤ RingHom.ker ((IsLocalRing.residue O).comp (b.t i)) := by
          intro x hx
          rw [RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, ← hMeq]
          exact hle (Ideal.subset_span ⟨x, hx, rfl⟩)
        exact hne ((hw'.eq_of_le hKtop hw'K).trans (hw.eq_of_le hKtop hwK).symm)
      · intro k _ _ β φ hφ
        rw [hρ k β]
        have h2 : φ (D.ω - (r : 𝓞 D.F)) = 0 := by
          rw [← RingHom.mem_ker, hφ]
          exact hUw' (sub_mem_uIdeal D r)
        rw [map_sub, map_intCast, sub_eq_zero] at h2
        exact h2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.PRepAll
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev GlobalTheory.UPel.HT.ES
open UpperTheory.Gal.FiniteEtaleModels

namespace UpperTheory.Gal.FiniteEtaleModels

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R}

private theorem isEtLevOver_iff_pow (o : Obj b N s) (𝔞 : Ideal (𝓞 D.F)) (r : ℕ) {T : Over S}
    (l : D.La → (T ⟶ o.A)) : IsEtLevOver o 𝔞 r l ↔ IsEtLevOver o (𝔞 ^ r) 1 l := by
  simp only [IsEtLevOver, wSub, pow_one]

private theorem repLev_iff_pow (o : Obj b N s) (𝔞 : Ideal (𝓞 D.F)) (r : ℕ) :
    RepLev o 𝔞 r ↔ RepLev o (𝔞 ^ r) 1 := by
  unfold RepLev
  simp only [isEtLevOver_iff_pow o 𝔞 r]

private theorem mem_wSub_top (z : D.La) : z ∈ wSub D ⊤ 1 := by
  refine Submodule.subset_span ⟨1, by simp, z, ?_⟩
  simp

private theorem repLev_top (o : Obj b N s) : RepLev o ⊤ 1 := by
  refine ⟨S, 𝟙 S, fun _ => 1, inferInstance, inferInstance, ?_, ?_⟩
  · refine ⟨fun _ _ => (mul_one 1).symm, fun c _ => ?_, fun _ _ => by rfl, fun k _ _ x => ⟨fun y _ => mem_wSub_top y, fun g hg => ⟨0, ?_⟩⟩⟩
    · haveI := o.act.hom c
      exact (MonObj.one_comp _).symm
    · have h1 := hg 1 (by simp)
      rw [map_one, o.act.one, Category.comp_id] at h1
      rw [h1, MonObj.comp_one]
  · intro T l hl
    refine ⟨Over.mkIdTerminal.from T, fun y => ?_, fun f _ => Over.mkIdTerminal.hom_ext _ _⟩
    rw [MonObj.comp_one, hl.2.2.1 y (mem_wSub_top y)]

theorem repAll_holds : IdealInd → RepMul → RepAll := by
  intro hI hM p _ D R _ b N 𝔞 r hN h𝔞 S _ s o
  have key : ∀ k, RepLev o 𝔞 k := by
    refine hI (𝓞 D.F) (fun w => IsEtPlace b w) (fun 𝔟 => ∀ k, RepLev o 𝔟 k) ?_ ?_ ?_ 𝔞 h𝔞.1 h𝔞.2
    · intro k
      rw [repLev_iff_pow, Ideal.top_pow]
      exact repLev_top o
    · intro w j _ hQ k
      rw [repLev_iff_pow, ← pow_mul]
      exact (repLev_iff_pow o w (j * k)).mp (GlobalTheory.T.exists_finiteEtaleScheme_representing_etaleLevels p D R b N w (j * k) hN hQ S s o)
    · intro 𝔞' 𝔟 hcop h1 h2 k
      rw [repLev_iff_pow, mul_pow]
      refine hM p D R b N S s o (𝔞' ^ k) (𝔟 ^ k) ?_
        ((repLev_iff_pow o 𝔞' k).mp (h1 k)) ((repLev_iff_pow o 𝔟 k).mp (h2 k))
      exact Ideal.pow_sup_eq_top (Ideal.sup_pow_eq_top hcop)
  exact key r

end UpperTheory.Gal.FiniteEtaleModels
end

