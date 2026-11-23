module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackEquivalence
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LiePull

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
  {φ : G'.left ⟶ G.left}

def push (h : IsGrpPullback G' G f φ) {T : Over S'} {g : T.left ⟶ S} (hg : T.hom ≫ f = g) (v : T ⟶ G') :
    Over.mk g ⟶ G :=
  Over.homMk (v.left ≫ φ) (by
    have e : (v.left ≫ φ) ≫ G.hom = g := by
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w v, hg]
    exact e)

def pull (h : IsGrpPullback G' G f φ) {T : Over S'} {g : T.left ⟶ S} (hg : T.hom ≫ f = g)
    (a : Over.mk g ⟶ G) : T ⟶ G' :=
  Over.homMk (h.1.lift a.left T.hom (by rw [hg]; exact Over.w a)) (h.1.lift_snd _ _ _)

def pts (h : IsGrpPullback G' G f φ) {T : Over S'} {g : T.left ⟶ S} (hg : T.hom ≫ f = g) :
    (T ⟶ G') ≃* (Over.mk g ⟶ G) where
  toFun := push h hg
  invFun := pull h hg
  left_inv v := by
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · exact h.1.lift_fst _ _ _
    · exact (h.1.lift_snd _ _ _).trans (Over.w v).symm
  right_inv a := Over.OverMorphism.ext (h.1.lift_fst _ _ _)
  map_mul' v w := by
    subst hg
    exact Over.OverMorphism.ext (h.2 T v w _ _ rfl rfl).symm

theorem pts_left (h : IsGrpPullback G' G f φ) {T : Over S'} {g : T.left ⟶ S} (hg : T.hom ≫ f = g)
    (v : T ⟶ G') : (pts h hg v).left = v.left ≫ φ := rfl

variable {R : Type} [CommRing R]

theorem one_left (h : IsGrpPullback G' G f φ) (x' : Sp R ⟶ S') :
    (1 : Over.mk x' ⟶ G').left ≫ φ = (1 : Over.mk (x' ≫ f) ⟶ G).left := by
  have e := map_one (pts h (T := Over.mk x') (g := x' ≫ f) rfl)
  exact (pts_left h rfl _).symm.trans (congrArg (fun z => z.left) e)

theorem eps_assoc (x' : Sp R ⟶ S') : (epsAt x').hom ≫ f = (epsAt (x' ≫ f)).hom :=
  Category.assoc _ _ _

abbrev tanPts (h : IsGrpPullback G' G f φ) (x' : Sp R ⟶ S') :
    (epsAt x' ⟶ G') ≃* (epsAt (x' ≫ f) ⟶ G) :=
  pts h (T := epsAt x') (g := (epsAt (x' ≫ f)).hom) (eps_assoc x')

theorem fst_comp_base (x' : Sp R ⟶ S') :
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ (epsAt x').hom = x' := by
  have e : (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫
      CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom = 𝟙 _ := by
    ext r
    simp
  have e' := congrArg Spec.map e
  simp only [Spec.map_comp, Spec.map_id] at e'
  show _ ≫ Spec.map _ ≫ x' = x'
  rw [← Category.assoc, e', Category.id_comp]

theorem epsMul_comp_base (x' : Sp R ⟶ S') (c : R) :
    Spec.map (CommRingCat.ofHom (epsMul c)) ≫ (epsAt x').hom = (epsAt x').hom := by
  have e : (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ CommRingCat.ofHom (epsMul c) =
      CommRingCat.ofHom (algebraMap R (DualNumber R)) := by
    refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
    show epsMul c (algebraMap R (DualNumber R) r) = algebraMap R (DualNumber R) r
    rw [TrivSqZeroExt.algebraMap_eq_inl]
    ext <;> simp [epsMul]
  have e' := congrArg Spec.map e
  simp only [Spec.map_comp] at e'
  show _ ≫ Spec.map _ ≫ x' = Spec.map _ ≫ x'
  rw [← Category.assoc, e']

theorem isTan_iff (h : IsGrpPullback G' G f φ) (x' : Sp R ⟶ S') (v : epsAt x' ⟶ G') :
    IsTanAt G (x' ≫ f) (tanPts h x' v) ↔ IsTanAt G' x' v := by
  unfold IsTanAt
  constructor
  · intro t
    apply h.1.hom_ext
    · rw [Category.assoc, one_left h x', ← pts_left h (eps_assoc x') v]
      exact t
    · rw [Category.assoc, Over.w v, fst_comp_base]
      exact (Over.w (1 : Over.mk x' ⟶ G')).symm
  · intro t
    rw [← one_left h x', ← t, pts_left h (eps_assoc x') v, Category.assoc]

def modelPull (h : IsGrpPullback G' G f φ) (x' : Sp R ⟶ S') {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G (x' ≫ f) E) : LieModel G' x' E where
  pt e := (tanPts h x').symm (M.pt e)
  tan e := (isTan_iff h x' _).1 (by rw [MulEquiv.apply_symm_apply]; exact M.tan e)
  inj e e' w := M.inj ((tanPts h x').symm.injective w)
  onto v t := by
    obtain ⟨e, he⟩ := M.onto _ ((isTan_iff h x' v).2 t)
    exact ⟨e, by rw [he, MulEquiv.symm_apply_apply]⟩
  add e e' := by rw [M.add, map_mul]
  smul c e := by
    apply h.1.hom_ext
    · have a : ∀ e, ((tanPts h x').symm (M.pt e)).left ≫ φ = (M.pt e).left := fun e => by
        rw [← pts_left h (eps_assoc x'), MulEquiv.apply_symm_apply]
      rw [Category.assoc, a, a]
      exact M.smul c e
    · have b : ((tanPts h x').symm (M.pt e)).left ≫ G'.hom = (epsAt x').hom := Over.w _
      rw [Category.assoc, Over.w, b]
      exact (epsMul_comp_base x' c).symm

def modelPush (h : IsGrpPullback G' G f φ) (x' : Sp R ⟶ S') {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G' x' E) : LieModel G (x' ≫ f) E where
  pt e := tanPts h x' (M.pt e)
  tan e := (isTan_iff h x' _).2 (M.tan e)
  inj e e' w := M.inj ((tanPts h x').injective w)
  onto v t := by
    have t' : IsTanAt G (x' ≫ f) (tanPts h x' ((tanPts h x').symm v)) := by
      rw [MulEquiv.apply_symm_apply]; exact t
    obtain ⟨e, he⟩ := M.onto _ ((isTan_iff h x' _).1 t')
    exact ⟨e, by rw [he, MulEquiv.apply_symm_apply]⟩
  add e e' := by rw [M.add, map_mul]
  smul c e := by
    show (M.pt (c • e)).left ≫ φ = _ ≫ (M.pt e).left ≫ φ
    rw [M.smul, Category.assoc]

theorem lieModel_pullback : ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ (R : Type) [CommRing R] (x' : Sp R ⟶ S') (E : Type) [AddCommGroup E] [Module R E], (∀ M : LieModel G (x' ≫ f) E, ∃ M' : LieModel G' x' E, ∀ e, (M'.pt e).left ≫ φ = (M.pt e).left) ∧ ∀ M' : LieModel G' x' E, ∃ M : LieModel G (x' ≫ f) E, ∀ e, (M'.pt e).left ≫ φ = (M.pt e).left := by
  intro S S' G G' _ _ f φ h R _ x' E _ _
  refine ⟨fun M => ⟨modelPull h x' M, fun e => ?_⟩, fun M' => ⟨modelPush h x' M', fun e => rfl⟩⟩
  show ((tanPts h x').symm (M.pt e)).left ≫ φ = _
  rw [← pts_left h (eps_assoc x'), MulEquiv.apply_symm_apply]

end GlobalTheory.CompanionTheory.Ar.LiePull
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalIndexAtSinglePlace
section
open NumberField Matrix IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

namespace GlobalTheory.CompanionTheory.Ar.Cusp.LocIndex

variable {L : Type} [Field L] [NumberField L] {W : Type} [AddCommGroup W] [Module (𝓞 L) W]

def cond (A B : Submodule (𝓞 L) W) : Ideal (𝓞 L) where
  carrier := {u | ∀ x ∈ A, u • x ∈ B}
  add_mem' := fun {a b} ha hb x hx => by
    rw [add_smul]; exact B.add_mem (ha x hx) (hb x hx)
  zero_mem' := fun x _ => by rw [zero_smul]; exact B.zero_mem
  smul_mem' := fun c u hu x hx => by
    rw [smul_eq_mul, mul_smul]; exact B.smul_mem c (hu x hx)

theorem mem_cond {A B : Submodule (𝓞 L) W} {u : 𝓞 L} :
    u ∈ cond A B ↔ ∀ x ∈ A, u • x ∈ B := Iff.rfl

theorem exists_reps {A B : Submodule (𝓞 L) W}
    (hfin : B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0) :
    ∃ S : Finset W, (∀ r ∈ S, r ∈ A) ∧ ∀ x ∈ A, ∃ r ∈ S, x - r ∈ B := by
  classical
  have hQ : Finite (A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup) :=
    Nat.finite_of_card_ne_zero hfin
  have := Fintype.ofFinite (A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup)
  refine ⟨Finset.univ.image
    (fun q : A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup =>
      ((Quotient.out q : A.toAddSubgroup) : W)), ?_, ?_⟩
  · intro r hr
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hr
    exact (Quotient.out q).2
  · intro x hx
    let q : A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup :=
      QuotientAddGroup.mk ⟨x, hx⟩
    refine ⟨((Quotient.out q : A.toAddSubgroup) : W),
      Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩, ?_⟩
    have hq : (QuotientAddGroup.mk (Quotient.out q) :
        A.toAddSubgroup ⧸ B.toAddSubgroup.addSubgroupOf A.toAddSubgroup) = q := Quotient.out_eq q
    have h := QuotientAddGroup.eq.mp hq
    rw [AddSubgroup.mem_addSubgroupOf] at h
    have h' : -((Quotient.out q : A.toAddSubgroup) : W) + x ∈ B := h
    rwa [neg_add_eq_sub] at h'

theorem cond_ne_bot {A B : Submodule (𝓞 L) W}
    (hfin : B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0) : cond A B ≠ ⊥ := by
  intro hbot

  have hmem : ((B.toAddSubgroup.relIndex A.toAddSubgroup : ℕ) : 𝓞 L) ∈ cond A B := by
    refine mem_cond.mpr fun x hx => ?_
    rw [Nat.cast_smul_eq_nsmul]
    exact AddSubgroup.nsmul_relIndex_mem B.toAddSubgroup hx
  rw [hbot, Ideal.mem_bot] at hmem
  exact hfin (Nat.cast_eq_zero.mp hmem)

theorem exists_mem_cond_notMem {A B : Submodule (𝓞 L) W} (w : FinitePlace L)
    (hloc : locAt w A = locAt w B)
    (hfin : B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0) :
    ∃ s ∈ cond A B, s ∉ w.maximalIdeal.asIdeal := by
  classical
  obtain ⟨S, hSA, hS⟩ := exists_reps hfin
  have hex : ∀ r ∈ S, ∃ t : 𝓞 L, t ∉ w.maximalIdeal.asIdeal ∧ t • r ∈ B := by
    intro r hr
    have hr' : r ∈ locAt w B := by rw [← hloc]; exact le_locAt w A (hSA r hr)
    exact mem_locAt.mp hr'
  choose! t ht using hex
  have := w.maximalIdeal.isPrime
  refine ⟨∏ r ∈ S, t r, mem_cond.mpr fun x hx => ?_, ?_⟩
  · obtain ⟨r, hr, hxr⟩ := hS x hx
    have hrB : (∏ r ∈ S, t r) • r ∈ B := by
      rw [← Finset.mul_prod_erase S t hr, mul_comm, mul_smul]
      exact B.smul_mem _ (ht r hr).2
    have hx' : x = r + (x - r) := by abel
    rw [hx', smul_add]
    exact B.add_mem hrB (B.smul_mem _ hxr)
  · rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨r, hr, hmem⟩
    exact (ht r hr).1 hmem

theorem cond_sup_span_eq_top {A B : Submodule (𝓞 L) W} (v : FinitePlace L)
    (hfin : B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0)
    (hloc : ∀ w : FinitePlace L, w ≠ v → locAt w A = locAt w B)
    {t : 𝓞 L} (ht : t ∉ v.maximalIdeal.asIdeal) : cond A B ⊔ Ideal.span {t} = ⊤ := by
  by_contra hne
  obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hne
  have hPbot : P ≠ ⊥ := by
    intro hP
    apply cond_ne_bot hfin
    rw [eq_bot_iff, ← hP]
    exact le_sup_left.trans hle
  obtain ⟨Q, hQ⟩ : ∃ Q : HeightOneSpectrum (𝓞 L), Q.asIdeal = P :=
    ⟨⟨P, hPmax.isPrime, hPbot⟩, rfl⟩
  by_cases hw : FinitePlace.mk Q = v
  · apply ht
    rw [← hw, FinitePlace.maximalIdeal_mk, hQ]
    exact hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self t))
  · obtain ⟨s, hs, hsP⟩ := exists_mem_cond_notMem (FinitePlace.mk Q) (hloc _ hw) hfin
    apply hsP
    rw [FinitePlace.maximalIdeal_mk, hQ]
    exact hle (Ideal.mem_sup_left hs)

theorem exists_bezout {A B : Submodule (𝓞 L) W} (v : FinitePlace L)
    (hfin : B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0)
    (hloc : ∀ w : FinitePlace L, w ≠ v → locAt w A = locAt w B)
    {t : 𝓞 L} (ht : t ∉ v.maximalIdeal.asIdeal) :
    ∃ s u : 𝓞 L, u ∈ cond A B ∧ s * t + u = 1 := by
  have h1 : (1 : 𝓞 L) ∈ cond A B ⊔ Ideal.span {t} := by
    rw [cond_sup_span_eq_top v hfin hloc ht]; exact Submodule.mem_top
  obtain ⟨u, hu, z, hz, huz⟩ := Submodule.mem_sup.mp h1
  obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.mp hz
  exact ⟨s, u, hu, by rw [add_comm]; exact huz⟩

theorem relIndex_locAt (L : Type) [Field L] [NumberField L] (W : Type) [AddCommGroup W]
    [Module (𝓞 L) W] (v : FinitePlace L) (A B : Submodule (𝓞 L) W) (hBA : B ≤ A)
    (hfin : B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0)
    (hloc : ∀ w : FinitePlace L, w ≠ v → locAt w A = locAt w B) :
    (locAt v B).toAddSubgroup.relIndex (locAt v A).toAddSubgroup =
      B.toAddSubgroup.relIndex A.toAddSubgroup := by
  have hle : A.toAddSubgroup ≤ (locAt v A).toAddSubgroup := fun x hx => le_locAt v A hx

  have hback : ∀ x ∈ A, x ∈ locAt v B → x ∈ B := by
    intro x hxA hx
    obtain ⟨t, ht, htx⟩ := mem_locAt.mp hx
    obtain ⟨s, u, hu, hsu⟩ := exists_bezout v hfin hloc ht
    have hx' : x = s • (t • x) + u • x := by rw [smul_smul, ← add_smul, hsu, one_smul]
    rw [hx']
    exact B.add_mem (B.smul_mem s htx) (mem_cond.mp hu x hxA)

  let f := (QuotientAddGroup.mk' ((locAt v B).toAddSubgroup.addSubgroupOf
    (locAt v A).toAddSubgroup)).comp (AddSubgroup.inclusion hle)
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientAddGroup.mk'_surjective _ q
    obtain ⟨t, ht, hty⟩ := mem_locAt.mp hy
    obtain ⟨s, u, hu, hsu⟩ := exists_bezout v hfin hloc ht
    refine ⟨⟨s • (t • y), A.smul_mem s hty⟩, ?_⟩
    simp only [f, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply]
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    show -(s • (t • y)) + y ∈ locAt v B
    have hu' : u = 1 - s * t := by rw [← hsu]; ring
    have hyeq : -(s • (t • y)) + y = u • y := by
      rw [hu', sub_smul, one_smul, smul_smul, neg_add_eq_sub]
    rw [hyeq]
    exact mem_locAt.mpr ⟨t, ht, by rw [smul_comm]; exact mem_cond.mp hu _ hty⟩
  have hker : f.ker = B.toAddSubgroup.addSubgroupOf A.toAddSubgroup := by
    ext ⟨x, hx⟩
    simp only [f, AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply,
      QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_inclusion,
      Submodule.mem_toAddSubgroup]
    exact ⟨fun h => hback x hx h, fun h => le_locAt v B h⟩
  unfold AddSubgroup.relIndex
  rw [← hker, AddSubgroup.index_eq_card, AddSubgroup.index_eq_card]
  exact (Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hsurj).toEquiv).symm

end GlobalTheory.CompanionTheory.Ar.Cusp.LocIndex
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothGroupTangentLift
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Chart

theorem one_left_spMap {S : Scheme.{0}} (G : Over S) [GrpObj G] {R A : Type} [CommRing R] [CommRing A]
    (x : Sp R ⟶ S) (g : R →+* A) :
    (1 : Over.mk (spMap g ≫ x) ⟶ G).left = spMap g ≫ (1 : Over.mk x ⟶ G).left := by
  let k : Over.mk (spMap g ≫ x) ⟶ Over.mk x := Over.homMk (spMap g) rfl
  have h : (1 : Over.mk (spMap g ≫ x) ⟶ G) = k ≫ (1 : Over.mk x ⟶ G) := by
    rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (k ≫ toUnit _) (toUnit _)]
  rw [h]; rfl

theorem exists_chart_at_point (S : Scheme.{0}) (G : Over S) [GrpObj G] [Smooth G.hom] (R : Type) [CommRing R]
    (x : Sp R ⟶ S) (p : Ideal R) [p.IsPrime] :
    ∃ f : R, f ∉ p ∧ ∃ (U : G.left.Opens) (V : S.Opens) (hU : IsAffineOpen U) (_ : IsAffineOpen V)
      (hUV : U ≤ G.hom ⁻¹ᵁ V),
      RingHom.Smooth (G.hom.appLE V U hUV).hom ∧
      ∃ u : Γ(G.left, U) →+* Localization.Away f,
        (1 : Over.mk (spMap (algebraMap R (Localization.Away f)) ≫ x) ⟶ G).left = spMap u ≫ hU.fromSpec := by
  let t : Sp R ⟶ G.left := (1 : Over.mk x ⟶ G).left
  let q : PrimeSpectrum R := ⟨p, inferInstance⟩
  let q' : Sp R := q
  obtain ⟨V, hV, hqV, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := G.hom (t q')) trivial
  obtain ⟨U, hU, hqU, hUV⟩ := exists_isAffineOpen_mem_and_subset (X := G.left) (U := G.hom ⁻¹ᵁ V) (x := t q') hqV
  have hUV' : U ≤ G.hom ⁻¹ᵁ V := hUV
  have hopen : IsOpen {y : PrimeSpectrum R | t (show Sp R from y) ∈ U} := (t ⁻¹ᵁ U).isOpen
  obtain ⟨_, ⟨f, rfl⟩, hqf, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (show q ∈ _ from hqU) hopen
  refine ⟨f, hqf, U, V, hU, hV, hUV', HasRingHomProperty.appLE @Smooth G.hom inferInstance ⟨V, hV⟩ ⟨U, hU⟩ hUV', ?_⟩
  let a : Sp (Localization.Away f) ⟶ Sp R := spMap (algebraMap R (Localization.Away f))
  have hrange : Set.range (a ≫ t) ⊆ Set.range hU.fromSpec := by
    rw [hU.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    apply hsub
    have : (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) y ∈
        Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away f))) := ⟨y, rfl⟩
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f] at this
    exact this
  let l := IsOpenImmersion.lift hU.fromSpec (a ≫ t) hrange
  refine ⟨(Spec.preimage l).hom, ?_⟩
  have hl : spMap (Spec.preimage l).hom = l := by
    simp [spMap]
  rw [one_left_spMap, hl]
  exact (IsOpenImmersion.lift_fac _ _ _).symm

end GlobalTheory.CompanionTheory.Ar.Chart
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecStalkSpecializesComp
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieStalk

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor MonoidalCategory CartesianMonoidalCategory MonObj Limits

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

def regIso (h : IsCptGen ξ) (p : Cpt ξ) : X.presheaf.stalk p.1 ≃+* regAt ξ p :=
  RingEquiv.ofBijective (genMap ξ p).rangeRestrict
    ⟨fun a b hab => h.inj p (congrArg Subtype.val hab), RingHom.rangeRestrict_surjective _⟩

def regPt (h : IsCptGen ξ) (p : Cpt ξ) : Sp (regAt ξ p) ⟶ X :=
  spMap (regIso h p).toRingHom ≫ X.fromSpecStalk p.1

theorem genMap_regIso_symm (h : IsCptGen ξ) (p : Cpt ξ) (a : regAt ξ p) :
    genMap ξ p ((regIso h p).symm a) = a := by
  exact congrArg Subtype.val ((regIso h p).apply_symm_apply a)

set_option backward.isDefEq.respectTransparency false in
theorem genMap_specializes {p q : Cpt ξ} (hs : q.1 ⤳ p.1) (s : X.presheaf.stalk p.1) :
    genMap ξ q ((X.presheaf.stalkSpecializes hs).hom s) = genMap ξ p s := by
  simp only [genMap]
  rw [← CommRingCat.comp_apply, ← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]

theorem regAt_le {p q : Cpt ξ} (hs : q.1 ⤳ p.1) : regAt ξ p ≤ regAt ξ q := by
  rintro _ ⟨s, rfl⟩
  exact ⟨_, genMap_specializes hs s⟩

theorem spMap_genMap_fromSpecStalk (p : Cpt ξ) : spMap (genMap ξ p) ≫ X.fromSpecStalk p.1 = ξ := by
  have h2 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  rw [← Scheme.SpecMap_stalkSpecializes_fromSpecStalk (x := ξ (IsLocalRing.closedPoint Ω)) (y := p.1) p.2,
    ← Category.assoc, ← Spec.map_comp] at h2
  exact h2

theorem spMap_algebraMap_regPt (h : IsCptGen ξ) (p : Cpt ξ) : spMap (algebraMap (regAt ξ p) Ω) ≫ regPt h p = ξ := by
  have e : (algebraMap (regAt ξ p) Ω).comp (regIso h p).toRingHom = genMap ξ p :=
    RingHom.ext fun x => rfl
  dsimp only [regPt, spMap]
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
  exact spMap_genMap_fromSpecStalk p

abbrev regIncl {p q : Cpt ξ} (hs : q.1 ⤳ p.1) : regAt ξ p →+* regAt ξ q := Subring.inclusion (regAt_le hs)

theorem spMap_regIncl_regPt (h : IsCptGen ξ) {p q : Cpt ξ} (hs : q.1 ⤳ p.1) :
    spMap (regIncl hs) ≫ regPt h p = regPt h q := by
  have e : (regIncl hs).comp (regIso h p).toRingHom =
      (regIso h q).toRingHom.comp (X.presheaf.stalkSpecializes hs).hom :=
    RingHom.ext fun s => Subtype.ext (genMap_specializes hs s).symm
  dsimp only [regPt, spMap]
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e, CommRingCat.ofHom_comp,
    CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

def castPt {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x y : Sp R ⟶ S} (e : x = y) {E : Type}
    [AddCommGroup E] [Module R E] (M : LieModel G x E) : LieModel G y E := e ▸ M

theorem castPt_pt_left {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x y : Sp R ⟶ S} (e : x = y)
    {E : Type} [AddCommGroup E] [Module R E] (M : LieModel G x E) (a : E) :
    ((castPt e M).pt a).left = (M.pt a).left := by
  subst e
  rfl

end GlobalTheory.CompanionTheory.Ar.LieStalk
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TranslateIntoSmallerOpen
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.BT.Transl

theorem translates_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U U' : Γ.G.left.Opens), Γ.IsFinOpenSub U → Γ.IsFinOpenSub U' → U' ≤ U → ∀ g ∈ U, ∃ (σ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γ.G) (t : T), toUnit (genPt R) ≫ σ = Γ.pt t ∧ ((toUnit Γ.G ≫ σ) * 𝟙 Γ.G).left g ∈ U' := by
  intro R _ _ _ T _ _ Γ U U' hU hU' _ g hg
  haveI := Γ.flat
  haveI := Γ.separated
  let p0 : Spec (CommRingCat.of R) := ⟨⊥, Ideal.isPrime_bot⟩
  have hp0 : p0 ⤳ Γ.G.hom g := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  obtain ⟨g', hg'g, hg'⟩ := Flat.generalizingMap Γ.G.hom hp0
  obtain ⟨s, x, hx⟩ := Γ.pt_onto g' (by rw [hg'])
  have hsU : (Γ.pt s).left x ∈ U := by
    rw [hx]; exact hg'g.mem_open U.isOpen hg
  have hsub : ∀ z z' : Spec (CommRingCat.of (FractionRing R)), z = z' := fun z z' =>
    PrimeSpectrum.ext (by
      haveI := z.isPrime
      haveI := z'.isPrime
      rw [Ideal.eq_bot_of_prime z.asIdeal, Ideal.eq_bot_of_prime z'.asIdeal])
  have hsall : ∀ z, (Γ.pt s).left z ∈ U := fun z => hsub x z ▸ hsU
  have hinvU : ∀ z, (Γ.pt s⁻¹).left z ∈ U := by
    rw [map_inv]; exact hU.inv _ _ hsall
  obtain ⟨σ, -, hσ⟩ := GlobalTheory.CompanionTheory.Ar.BT.exists_section_of_generic_point
    R T Γ U hU.finite s⁻¹ (fun z _ => hinvU z)
  refine ⟨σ, s⁻¹, hσ, ?_⟩
  set τ := (toUnit Γ.G ≫ σ) * 𝟙 Γ.G with hτ
  have hτpt : Γ.pt s ≫ τ = 1 := by
    rw [hτ, Hom.mul_def, ← Category.assoc, comp_lift, ← Category.assoc, comp_toUnit, hσ,
      Category.comp_id, ← Hom.mul_def, ← map_mul, inv_mul_cancel, map_one]
  have hτx : τ.left ((Γ.pt s).left x) = (η[Γ.G]).left ((toUnit (genPt R)).left x) := by
    have h1 : (Γ.pt s ≫ τ).left = (toUnit (genPt R) ≫ η[Γ.G]).left := by
      rw [hτpt, Hom.one_def]
    rw [Over.comp_left, Over.comp_left] at h1
    have h2 := congrArg (fun h => h x) h1
    simpa using h2
  have hw : (η[Γ.G]).left ≫ Γ.G.hom = 𝟙 _ := Over.w _
  haveI : UniversallyClosed ((η[Γ.G]).left ≫ Γ.G.hom) := by rw [hw]; infer_instance
  haveI : UniversallyClosed (η[Γ.G]).left :=
    UniversallyClosed.of_comp_of_isSeparated _ Γ.G.hom
  have hcl : IsClosed (Set.range (η[Γ.G]).left) := by
    have h := (η[Γ.G]).left.isClosedMap _ isClosed_univ
    rwa [Set.image_univ] at h
  have hspec : τ.left ((Γ.pt s).left x) ⤳ τ.left g := by
    rw [hx]; exact hg'g.map τ.left.continuous
  have hsubset : ({τ.left ((Γ.pt s).left x)} : Set Γ.G.left) ⊆ Set.range (η[Γ.G]).left :=
    Set.singleton_subset_iff.2 ⟨_, hτx.symm⟩
  have hmem : τ.left g ∈ Set.range (η[Γ.G]).left :=
    closure_minimal hsubset hcl (specializes_iff_mem_closure.1 hspec)
  obtain ⟨z, hz⟩ := hmem
  rw [← hz]
  exact hU'.one z

end GlobalTheory.CompanionTheory.Ar.BT.Transl
end

