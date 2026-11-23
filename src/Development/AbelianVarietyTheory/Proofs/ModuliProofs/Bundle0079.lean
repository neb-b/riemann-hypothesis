module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSegreCoordinates
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0071
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0058

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GrpObjOfDenseFibres
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.FibreGrp

theorem hom_ext_of_fibres {S : Scheme.{0}} [IsReduced S] {Sg : Set S} (hSg : Dense Sg) {X Y : Over S}
    [Smooth X.hom] [IsSeparated Y.hom] {f g : X ⟶ Y}
    (h : ∀ p ∈ Sg, ∃ (U : Scheme.{0}) (j : U ⟶ S), p ∈ Set.range j ∧
      ∀ (T : Over U) (t : Over.mk (T.hom ≫ j) ⟶ X), t ≫ f = t ≫ g) : f = g := by
  have : IsReduced X.left := GlobalTheory.isReduced_of_smooth_of_isReduced X.hom
  choose U j hj hfg using h
  let incl : (∐ fun q : Sg => pullback X.hom (j q.1 q.2)) ⟶ X.left :=
    Sigma.desc fun q : Sg => pullback.fst X.hom (j q.1 q.2)
  have hincl : ∀ q : Sg, Sigma.ι (fun q : Sg => pullback X.hom (j q.1 q.2)) q ≫ incl =
      pullback.fst X.hom (j q.1 q.2) := fun q => Sigma.ι_desc _ q
  have hdense : Dense (X.hom ⁻¹' Sg) := hSg.preimage X.hom.isOpenMap
  have : IsDominant incl := by
    refine ⟨Dense.mono ?_ hdense⟩
    intro x hx
    have hx' : x ∈ Set.range (pullback.fst X.hom (j _ hx)) := by
      rw [Scheme.Pullback.range_fst]
      exact hj _ hx
    obtain ⟨y, hy⟩ := hx'
    refine ⟨Sigma.ι (fun q : Sg => pullback X.hom (j q.1 q.2)) ⟨_, hx⟩ y, ?_⟩
    rw [← Scheme.Hom.comp_apply, hincl]
    exact hy
  apply Over.OverMorphism.ext
  refine ext_of_isDominant_of_isSeparated Y.hom (by rw [Over.w f, Over.w g]) incl ?_
  refine Sigma.hom_ext _ _ fun q => ?_
  rw [← Category.assoc, hincl, ← Category.assoc, hincl]
  have key := hfg q.1 q.2 (Over.mk (pullback.snd X.hom (j q.1 q.2)))
    (Over.homMk (pullback.fst X.hom (j q.1 q.2)) (by simp only [Over.mk_hom]; exact pullback.condition))
  exact congrArg CommaMorphism.left key

private theorem smooth_tensor_hom {S : Scheme.{0}} (P Q : Over S) [Smooth P.hom] [Smooth Q.hom] :
    Smooth (P ⊗ Q).hom := by
  change Smooth (pullback.fst P.hom Q.hom ≫ P.hom)
  infer_instance

private theorem smooth_tensorUnit_hom (S : Scheme.{0}) : Smooth (𝟙_ (Over S)).hom := by
  change Smooth (𝟙 S)
  infer_instance

private theorem eq_of_points_lemma_3 {R : Type} [CommRing R] [IsReduced R] {Z : Over (Sp R)} [IsSeparated Z.hom]
    {m : Z ⊗ Z ⟶ Z} {i : Z ⟶ Z} {e : 𝟙_ (Over (Sp R)) ⟶ Z} {Sg : Set (Sp R)} (hSg : Dense Sg)
    (hfib : ∀ p ∈ Sg, ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ Sp R) (A : Over (Sp K)) (_ : GrpObj A) (φ : A.left ⟶ Z.left), p ∈ Set.range x ∧ IsCommMonObj A ∧ IsPullback φ A.hom Z.hom x ∧ (∀ φ₂ : (A ⊗ A).left ⟶ (Z ⊗ Z).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[A]).left ≫ φ) ∧ φ ≫ i.left = (ι[A]).left ≫ φ ∧ x ≫ e.left = (η[A]).left ≫ φ)
    {P : Over (Sp R)} [Smooth P.hom] {u v : P ⟶ Z}
    (H : ∀ (K : Type) [Field K] (x : Sp K ⟶ Sp R) (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A]
      (φ : A.left ⟶ Z.left), IsPullback φ A.hom Z.hom x →
      (∀ φ₂ : (A ⊗ A).left ⟶ (Z ⊗ Z).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[A]).left ≫ φ) →
      φ ≫ i.left = (ι[A]).left ≫ φ → x ≫ e.left = (η[A]).left ≫ φ →
      ∀ (T : Over (Sp K)) (t : Over.mk (T.hom ≫ x) ⟶ P), t ≫ u = t ≫ v) : u = v := by
  refine hom_ext_of_fibres hSg fun p hp => ?_
  obtain ⟨K, _, x, A, _, φ, hx, hc, pb, hm, hi, he⟩ := hfib p hp
  exact ⟨Sp K, x, hx, H K x A φ pb hm hi he⟩

end GlobalTheory.FibreGrp

namespace GlobalTheory

open GrpDense FibreGrp

theorem grpObj_of_dense_fibres :
    ∀ (R : Type) [CommRing R] [IsReduced R] (Z : Over (Sp R)) (m : Z ⊗ Z ⟶ Z) (i : Z ⟶ Z) (e : 𝟙_ (Over (Sp R)) ⟶ Z) (Sg : Set (Sp R)), Dense Sg → Smooth Z.hom → IsProper Z.hom → GeometricallyConnected Z.hom → (∀ p ∈ Sg, ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ Sp R) (A : Over (Sp K)) (_ : GrpObj A) (φ : A.left ⟶ Z.left), p ∈ Set.range x ∧ IsCommMonObj A ∧ IsPullback φ A.hom Z.hom x ∧ (∀ φ₂ : (A ⊗ A).left ⟶ (Z ⊗ Z).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[A]).left ≫ φ) ∧ φ ≫ i.left = (ι[A]).left ≫ φ ∧ x ≫ e.left = (η[A]).left ≫ φ) → ∃ _ : GrpObj Z, μ[Z] = m ∧ η[Z] = e ∧ ι[Z] = i ∧ IsAbelianScheme Z ∧ ∀ (S' : Scheme.{0}) (x : S' ⟶ Sp R) (A : Over S') [GrpObj A] (φ : A.left ⟶ Z.left), IsPullback φ A.hom Z.hom x → (∀ φ₂ : (A ⊗ A).left ⟶ (Z ⊗ Z).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[A]).left ≫ φ) → IsGrpPullback A Z x φ := by
  intro R _ _ Z m i e Sg hSg hsm hpr hgc hfib
  have : Smooth Z.hom := hsm
  have : IsProper Z.hom := hpr
  have : Smooth (𝟙_ (Over (Sp R))).hom := smooth_tensorUnit_hom (Sp R)
  have : Smooth (Z ⊗ Z).hom := smooth_tensor_hom Z Z
  have : Smooth (𝟙_ (Over (Sp R)) ⊗ Z).hom := smooth_tensor_hom _ _
  have : Smooth (Z ⊗ 𝟙_ (Over (Sp R))).hom := smooth_tensor_hom _ _
  have : Smooth ((Z ⊗ Z) ⊗ Z).hom := smooth_tensor_hom _ _
  have one_mul' : e ▷ Z ≫ m = (λ_ Z).hom := by
    refine eq_of_points_lemma_3 hSg hfib ?_
    intro K _ x A _ _ φ pb hm hi he T t
    obtain ⟨c, hc⟩ := GrpDense.pushPt_surjective pb T (t ≫ snd (𝟙_ (Over (Sp R))) Z)
    rw [← lift_comp_fst_snd t, toUnit_unique (t ≫ fst (𝟙_ (Over (Sp R))) Z) (toUnit _),
      lift_whiskerRight_assoc, lift_leftUnitor_hom, ← hc, GrpDense.pushPt_one pb.w he T,
      GrpDense.pushPt_mul pb.w hm, _root_.one_mul]
  have mul_one' : Z ◁ e ≫ m = (ρ_ Z).hom := by
    refine eq_of_points_lemma_3 hSg hfib ?_
    intro K _ x A _ _ φ pb hm hi he T t
    obtain ⟨c, hc⟩ := GrpDense.pushPt_surjective pb T (t ≫ fst Z (𝟙_ (Over (Sp R))))
    rw [← lift_comp_fst_snd t, toUnit_unique (t ≫ snd Z (𝟙_ (Over (Sp R)))) (toUnit _),
      lift_whiskerLeft_assoc, lift_rightUnitor_hom, ← hc, GrpDense.pushPt_one pb.w he T,
      GrpDense.pushPt_mul pb.w hm, _root_.mul_one]
  have mul_assoc' : m ▷ Z ≫ m = (α_ Z Z Z).hom ≫ Z ◁ m ≫ m := by
    refine eq_of_points_lemma_3 hSg hfib ?_
    intro K _ x A _ _ φ pb hm hi he T t
    obtain ⟨a, ha⟩ := GrpDense.pushPt_surjective pb T (t ≫ fst (Z ⊗ Z) Z ≫ fst Z Z)
    obtain ⟨b, hb⟩ := GrpDense.pushPt_surjective pb T (t ≫ fst (Z ⊗ Z) Z ≫ snd Z Z)
    obtain ⟨c, hc⟩ := GrpDense.pushPt_surjective pb T (t ≫ snd (Z ⊗ Z) Z)
    have ht : t = lift (lift (pushPt pb.w a) (pushPt pb.w b)) (pushPt pb.w c) := by
      rw [ha, hb, hc]
      simp only [← Category.assoc, lift_comp_fst_snd]
    rw [ht]
    simp only [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc,
      GrpDense.pushPt_mul pb.w hm, _root_.mul_assoc]
  have left_inv' : lift i (𝟙 Z) ≫ m = toUnit Z ≫ e := by
    refine eq_of_points_lemma_3 hSg hfib ?_
    intro K _ x A _ _ φ pb hm hi he T t
    obtain ⟨c, rfl⟩ := GrpDense.pushPt_surjective pb T t
    rw [comp_lift_assoc, Category.comp_id, GrpDense.pushPt_inv pb.w hi, GrpDense.pushPt_mul pb.w hm,
      ← Category.assoc (pushPt pb.w c) (toUnit Z) e, toUnit_unique (pushPt pb.w c ≫ toUnit Z) (toUnit _),
      GrpDense.pushPt_one pb.w he T, _root_.inv_mul_cancel]
  have right_inv' : lift (𝟙 Z) i ≫ m = toUnit Z ≫ e := by
    refine eq_of_points_lemma_3 hSg hfib ?_
    intro K _ x A _ _ φ pb hm hi he T t
    obtain ⟨c, rfl⟩ := GrpDense.pushPt_surjective pb T t
    rw [comp_lift_assoc, Category.comp_id, GrpDense.pushPt_inv pb.w hi, GrpDense.pushPt_mul pb.w hm,
      ← Category.assoc (pushPt pb.w c) (toUnit Z) e, toUnit_unique (pushPt pb.w c ≫ toUnit Z) (toUnit _),
      GrpDense.pushPt_one pb.w he T, _root_.mul_inv_cancel]
  have comm' : (β_ Z Z).hom ≫ m = m := by
    refine eq_of_points_lemma_3 hSg hfib ?_
    intro K _ x A _ _ φ pb hm hi he T t
    obtain ⟨a, ha⟩ := GrpDense.pushPt_surjective pb T (t ≫ fst Z Z)
    obtain ⟨b, hb⟩ := GrpDense.pushPt_surjective pb T (t ≫ snd Z Z)
    have ht : t = lift (pushPt pb.w a) (pushPt pb.w b) := by rw [ha, hb, lift_comp_fst_snd]
    rw [ht, lift_braiding_hom_assoc, GrpDense.pushPt_mul pb.w hm, GrpDense.pushPt_mul pb.w hm, _root_.mul_comm]
  let G : GrpObj Z :=
    { one := e, mul := m, one_mul := one_mul', mul_one := mul_one', mul_assoc := mul_assoc',
      inv := i, left_inv := left_inv', right_inv := right_inv' }
  refine ⟨G, rfl, rfl, rfl, ?_, ?_⟩
  · exact { comm := ⟨comm'⟩, smooth := hsm, proper := hpr, geomConnected := hgc }
  · intro S' x A _ φ pb hm'
    refine ⟨pb, fun T a b a₀ b₀ ha hb => ?_⟩
    have ea : a₀ = pushPt pb.w a := Over.OverMorphism.ext ha
    have eb : b₀ = pushPt pb.w b := Over.OverMorphism.ext hb
    subst ea eb
    exact congrArg CommaMorphism.left (GrpDense.pushPt_mul pb.w hm' a b)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomogeneousIdealSectionsOfLineBundlePower
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZV

noncomputable section
namespace GlobalTheory.ZV.FormSec
open GlobalTheory.SegreCoord (ev ev_eq ev_ext ev_stalkMap Loc loc_of_secCoord exists_secCoord)

theorem eval₂_scale {R A σ : Type} [CommRing R] [CommRing A] (φ : R →+* A) (x : σ → A) (c : A)
    {F : MvPolynomial σ R} {e : ℕ} (hF : F.IsHomogeneous e) :
    MvPolynomial.eval₂ φ (fun j => c * x j) F = c ^ e * MvPolynomial.eval₂ φ x F := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have h : ∑ i ∈ d.support, d i = e := by
    have := hF (MvPolynomial.mem_support_iff.1 hd)
    simpa [Finsupp.weight_apply, Finsupp.sum] using this
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, h]
  ring

variable {R σ : Type} [CommRing R] {X : Scheme.{0}} {p : X ⟶ Sp R} {M : LB X} {th : σ → M.Sec}

theorem mem_idealOf {F : MvPolynomial σ R} : F ∈ idealOf p M th (𝟙 X) ↔
    ∀ (T : Type) [CommRing T] (β : R →+* T) (y : Sp T ⟶ X) (v : σ → T), y ≫ p = spMap β → SecCoord M th y v →
      MvPolynomial.eval₂ β v F = 0 := by
  simp only [idealOf, Ideal.mem_iInf, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom, Category.comp_id, and_imp]

theorem homogeneousComponent_mem {F : MvPolynomial σ R} (hF : F ∈ idealOf p M th (𝟙 X)) (e : ℕ) :
    MvPolynomial.homogeneousComponent e F ∈ idealOf p M th (𝟙 X) := by
  refine mem_idealOf.2 fun T _ β x v hx h => ?_
  let φ : T →+* LaurentPolynomial T := (Polynomial.toLaurent (R := T)).comp Polynomial.C
  have h1 := Coord.scale (Coord.baseChange h φ) (LaurentPolynomial.isUnit_T (R := T) 1).unit
  have h2 := mem_idealOf.1 hF _ (φ.comp β) _ _ (by rw [Category.assoc, hx]; exact (spMap_comp β φ).symm) h1
  have h3 : MvPolynomial.eval₂ (Polynomial.C.comp β) (fun i => Polynomial.X * Polynomial.C (v i)) F = 0 := by
    apply Polynomial.toLaurent_injective
    rw [map_zero, MvPolynomial.eval₂_comp_left, ← h2]
    congr 1
    funext i
    simp [φ]
  have h4 : ∀ n, MvPolynomial.eval₂ (Polynomial.C.comp β) (fun i => Polynomial.X * Polynomial.C (v i))
      (MvPolynomial.homogeneousComponent n F) =
      Polynomial.monomial n (MvPolynomial.eval₂ β v (MvPolynomial.homogeneousComponent n F)) := fun n => by
    rw [eval₂_scale _ _ _ (MvPolynomial.homogeneousComponent_isHomogeneous n F), ← Polynomial.C_mul_X_pow_eq_monomial,
      _root_.mul_comm, MvPolynomial.eval₂_comp_left]
    rfl
  by_cases he : F.totalDegree < e
  · rw [MvPolynomial.homogeneousComponent_eq_zero _ _ he, MvPolynomial.eval₂_zero]
  rw [← MvPolynomial.sum_homogeneousComponent F, MvPolynomial.eval₂_sum] at h3
  have h5 := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q e) h3
  simp only [h4, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_range,
    Polynomial.coeff_zero] at h5
  rwa [if_pos (by omega)] at h5

theorem isUnit_gs_iff {Z : Scheme.{0}} (r : Z ⟶ X) (z : Z) {U : X.Opens} (h : r z ∈ U) (a : Γ(X, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ X.basicOpen a := by
  rw [gs_eq r z U h, ← Scheme.Hom.germ_stalkMap_apply, isUnit_map_iff, X.mem_basicOpen a _ h]

theorem not_mem_of_isUnit_ev {T : Type} [CommRing T] (y : Sp T) {a : T} (h : IsUnit (ev y a)) :
    a ∉ (show PrimeSpectrum T from y).asIdeal := by
  rw [ev_eq, isUnit_gs_iff (𝟙 _) y (U := ⊤) trivial] at h
  have h' : y ∈ (Spec (CommRingCat.of T)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of T)).inv a) := h
  rw [basicOpen_eq_of_affine] at h'
  exact h'

theorem span_eq_top (hc : ⨆ i, Out.nonzeroLocus (th i) = ⊤) {T : Type} [CommRing T] {x : Sp T ⟶ X} {v : σ → T}
    (h : SecCoord M th x v) : Ideal.span (Set.range v) = ⊤ := by
  by_contra hJ
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hJ
  let y : Sp T := (⟨m, hm.isPrime⟩ : PrimeSpectrum T)
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc.ge (Set.mem_univ (x y)))
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
  have hk' : x y ∈ M.U k := X.basicOpen_le _ hk
  obtain ⟨u, hu⟩ := loc_of_secCoord h y k hk'
  have := (isUnit_gs_iff x y hk' _).2 hk
  rw [hu] at this
  exact not_mem_of_isUnit_ev y (isUnit_of_mul_isUnit_left this) (hle (Ideal.subset_span ⟨i, rfl⟩))

theorem mem_of_X_mul_mem (hc : ⨆ i, Out.nonzeroLocus (th i) = ⊤) {F : MvPolynomial σ R}
    (hF : ∀ i, MvPolynomial.X i * F ∈ idealOf p M th (𝟙 X)) : F ∈ idealOf p M th (𝟙 X) := by
  refine mem_idealOf.2 fun T _ β x v hx h => ?_
  obtain ⟨s, c, e⟩ := GlobalTheory.SegreCoord.exists_comb (span_eq_top hc h)
  rw [← _root_.one_mul (MvPolynomial.eval₂ β v F), ← e, Finset.sum_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  have := mem_idealOf.1 (hF i) T β x v hx h
  rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] at this
  rw [_root_.mul_assoc, this, mul_zero]


variable (p th) in
def formSec {d : ℕ} {F : MvPolynomial σ R} (hF : F.IsHomogeneous d) : (lbPow M d).Sec where
  f j := MvPolynomial.eval₂ ((resG X le_top).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom))
    (fun i => resG X (LB.wchart_le M (fun _ : PUnit => 𝟙 X) j PUnit.unit) ((th i).f (j PUnit.unit))) F
  compat j j' := by
    have l₁ : (lbPow M d).U j ⊓ (lbPow M d).U j' ≤ M.U (j ⟨⟩) := inf_le_left.trans (Cartier.lbPow_U M d j).le
    have l₂ : (lbPow M d).U j ⊓ (lbPow M d).U j' ≤ M.U (j' ⟨⟩) := inf_le_right.trans (Cartier.lbPow_U M d j').le
    have e := fun i => Cartier.sec_compat (th i) (j ⟨⟩) (j' ⟨⟩) l₁ l₂
    change resG X _ _ = _ * resG X _ _
    refine (MvPolynomial.eval₂_comp_left _ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·)
      ((congrArg Units.val (Cartier.lbPow_g M d j j')).trans (Units.val_pow_eq_pow_val _ _))
      (MvPolynomial.eval₂_comp_left _ _ _ _)).symm)
    refine Eq.trans ?_ (eval₂_scale _ _ _ hF)
    congr 1
    · exact RingHom.ext fun a => (Cartier.resG_resG _ _ _).trans (Cartier.resG_resG _ _ _).symm
    · funext i
      exact (Cartier.resG_resG _ _ _).trans ((e i).trans (congrArg _ (Cartier.resG_resG _ _ _).symm))

theorem gs_formSec {d : ℕ} {F : MvPolynomial σ R} (hF : F.IsHomogeneous d) {T : Type} [CommRing T] {β : R →+* T}
    {x : Sp T ⟶ X} {v : σ → T} (hx : x ≫ p = spMap β) (h : SecCoord M th x v) (y : Sp T) (j : PUnit → M.ι)
    (hy : x y ∈ (lbPow M d).U j) : ∃ u : ((Sp T).presheaf.stalk y)ˣ,
      gs x y _ ((formSec p th hF).f j) = u * ev y (MvPolynomial.eval₂ β v F) := by
  obtain ⟨u, hu⟩ := loc_of_secCoord h y (j ⟨⟩) ((Cartier.lbPow_U M d j).le hy)
  refine ⟨u ^ d, ?_⟩
  let ψ : Γ(X, (lbPow M d).U j) →+* (Sp T).presheaf.stalk y :=
    ((Sp T).presheaf.germ (x ⁻¹ᵁ (lbPow M d).U j) y hy).hom.comp (x.app _).hom
  have hψ : ∀ a, gs x y _ a = ψ a := fun a => gs_eq x y _ hy a
  rw [hψ, MvPolynomial.eval₂_comp_left (ev y), Units.val_pow_eq_pow_val, ← eval₂_scale _ _ _ hF]
  refine (MvPolynomial.eval₂_comp_left ψ _ _ _).trans ?_
  congr 1
  · refine RingHom.ext fun a => ?_
    refine (hψ _).symm.trans ((gs_res x y le_top hy _).trans ((gs_pull x p y ⊤ trivial _).trans ?_))
    rw [hx, ← Category.comp_id (spMap β), GlobalTheory.SegreCoord.gs_stalkMap _ _ _ ⊤ trivial, ← ev_eq, ← ev_stalkMap]
    rfl
  · funext i
    exact (hψ _).symm.trans ((gs_res x y _ hy _).trans ((hu i).trans (_root_.mul_comm _ _)))

theorem formSec_eq_zero_iff (hM : M.IsLB) {d : ℕ} {F : MvPolynomial σ R} (hF : F.IsHomogeneous d) :
    (∀ j, (formSec p th hF).f j = 0) ↔ F ∈ idealOf p M th (𝟙 X) := by
  constructor
  · intro h0
    refine mem_idealOf.2 fun T _ β x v hx h => ev_ext fun y => ?_
    obtain ⟨k, hk⟩ := exists_chart hM (x y)
    have hy : x y ∈ (lbPow M d).U (fun _ => k) := (Cartier.lbPow_U M d _).ge hk
    obtain ⟨u, hu⟩ := gs_formSec hF hx h y _ hy
    have h1 : gs x y _ (0 : Γ(X, (lbPow M d).U (fun _ => k))) = 0 := by rw [gs_eq x y _ hy, map_zero, map_zero]
    rw [map_zero]
    exact u.mul_right_eq_zero.1 (hu.symm.trans ((congrArg (gs x y _) (h0 fun _ => k)).trans h1))
  · intro hI j
    refine fn_ext fun z hz => ?_
    obtain ⟨V, hV, hzV, hle⟩ := exists_isAffineOpen_mem_and_subset hz
    let x : Sp Γ(X, V) ⟶ X := hV.fromSpec
    haveI : IsOpenImmersion x := inferInstanceAs (IsOpenImmersion hV.fromSpec)
    have hr : Set.range x = V := hV.range_fromSpec
    obtain ⟨y, rfl⟩ : z ∈ Set.range x := hr.ge hzV
    obtain ⟨v, hv⟩ := exists_secCoord (th := th) hM (x := x) (k := j ⟨⟩)
      fun y => (Cartier.lbPow_U M d j).le (hle (hr.le ⟨y, rfl⟩))
    have hx : x ≫ p = spMap (Spec.preimage (x ≫ p)).hom := (Spec.map_preimage _).symm
    obtain ⟨u, hu⟩ := gs_formSec hF hx hv y j hz
    rw [mem_idealOf.1 hI _ _ x v hx hv, map_zero, mul_zero, ← Category.comp_id x,
      GlobalTheory.SegreCoord.gs_stalkMap x (𝟙 X) y _ hz] at hu
    rw [gs_eq (𝟙 X) (x y) _ hz 0, map_zero, map_zero]
    exact (asIso (x.stalkMap y)).commRingCatIsoToRingEquiv.injective (hu.trans (map_zero _).symm)

theorem eval_eq_zero_iff {K : Type} [Field K] {p : X ⟶ Sp K} (hM : M.IsLB) {d : ℕ} {F : MvPolynomial σ K}
    (hF : F.IsHomogeneous d) {y : Sp K ⟶ X} {v : σ → K} (hy : y ≫ p = 𝟙 _) (h : SecCoord M th y v) :
    MvPolynomial.eval v F = 0 ↔ ¬ ⊤ ≤ y ⁻¹ᵁ Out.nonzeroLocus (formSec p th hF) := by
  have hy' : y ≫ p = spMap (RingHom.id K) := hy.trans (Spec.map_id (CommRingCat.of K)).symm
  rw [← not_iff_not, not_not]
  constructor
  · intro h0 z _
    obtain ⟨k, hk⟩ := exists_chart hM (y z)
    have hz : y z ∈ (lbPow M d).U (fun _ => k) := (Cartier.lbPow_U M d _).ge hk
    obtain ⟨u, hu⟩ := gs_formSec hF hy' h z _ hz
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => k, (isUnit_gs_iff y z hz _).1 ?_⟩
    rw [hu]
    exact u.isUnit.mul ((Ne.isUnit h0).map (ev z))
  · intro hle h0
    let z : Sp K := (⊥ : PrimeSpectrum K)
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1
      (show y z ∈ Out.nonzeroLocus (formSec p th hF) from hle (Set.mem_univ z))
    have hz : y z ∈ (lbPow M d).U j := X.basicOpen_le _ hj
    obtain ⟨u, hu⟩ := gs_formSec hF hy' h z j hz
    have hun := (isUnit_gs_iff y z hz _).2 hj
    rw [hu, show MvPolynomial.eval₂ (RingHom.id K) v F = 0 from h0, map_zero, mul_zero] at hun
    exact not_isUnit_zero hun

theorem ideal_of_veryAmple : ∀ (K σ : Type) [Field K] [Finite σ] (X : Scheme.{0}) (p : X ⟶ Sp K) (M : LB X) (th : σ → M.Sec), M.IsLB → VAmp p M th → (∀ F ∈ idealOf p M th (𝟙 X), ∀ e, MvPolynomial.homogeneousComponent e F ∈ idealOf p M th (𝟙 X)) ∧ (∀ F, (∀ i, MvPolynomial.X i * F ∈ idealOf p M th (𝟙 X)) → F ∈ idealOf p M th (𝟙 X)) ∧ ∀ (d : ℕ) (F : MvPolynomial σ K), F.IsHomogeneous d → ∃ τ : (lbPow M d).Sec, (∀ j, τ.f j = MvPolynomial.eval₂ ((resG X le_top).comp (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)) (fun i => resG X (LB.wchart_le M (fun _ : PUnit => 𝟙 X) j PUnit.unit) ((th i).f (j PUnit.unit))) F) ∧ ((∀ j, τ.f j = 0) ↔ F ∈ idealOf p M th (𝟙 X)) ∧ ∀ (y : Sp K ⟶ X) (v : σ → K), y ≫ p = 𝟙 _ → SecCoord M th y v → (MvPolynomial.eval v F = 0 ↔ ¬ ⊤ ≤ y ⁻¹ᵁ Out.nonzeroLocus τ) :=
  fun _ _ _ _ _ p _ th hM hV => ⟨fun _ hF e => homogeneousComponent_mem hF e, fun _ hF => mem_of_X_mul_mem hV.1 hF,
    fun _ _ hF => ⟨formSec p th hF, fun _ => rfl, formSec_eq_zero_iff hM hF,
      fun _ _ hy h => eval_eq_zero_iff hM hF hy h⟩⟩

end GlobalTheory.ZV.FormSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MemIdealOfOfDense
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.DenseFib

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem exists_spMap {A B : Type} [CommRing A] [CommRing B] (f : Sp B ⟶ Sp A) :
    ∃ φ : A →+* B, spMap φ = f :=
  ⟨(Spec.preimage f).hom, Spec.map_preimage f⟩

theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) :
    f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem eval₂_scale {R L σ : Type} [CommRing R] [CommRing L] (φ : R →+* L) (x : σ → L) (c : L)
    {F : MvPolynomial σ R} {e : ℕ} (hF : F.IsHomogeneous e) :
    MvPolynomial.eval₂ φ (fun j => c * x j) F = c ^ e * MvPolynomial.eval₂ φ x F := by
  rw [MvPolynomial.eval₂_eq, MvPolynomial.eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = e := by
    have := hF (MvPolynomial.mem_support_iff.1 hd)
    rw [← this]; simp [Finsupp.weight_apply, Finsupp.sum]
  simp only [mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

theorem eq_zero_of_dense {A : Type} [CommRing A] [_root_.IsReduced A] (D : Set (Sp A)) (hD : Dense D) (a : A)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (κ : A →+* K), Set.range (spMap κ) ⊆ D → κ a = 0) :
    a = 0 := by
  by_contra ha
  have hne : (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)).Nonempty := by
    by_contra hn
    refine ha (IsNilpotent.eq_zero ((PrimeSpectrum.basicOpen_eq_bot_iff a).1 ?_))
    exact eq_bot_iff.2 fun z hz => (hn ⟨z, hz⟩).elim
  obtain ⟨q, hqa, hqD⟩ := hD.inter_open_nonempty _ (PrimeSpectrum.basicOpen a).isOpen hne
  let q' : PrimeSpectrum A := q
  let K := AlgebraicClosure q'.asIdeal.ResidueField
  let κ : A →+* K := (algebraMap q'.asIdeal.ResidueField K).comp (algebraMap A _)
  have hker : ∀ z, κ z = 0 ↔ z ∈ q'.asIdeal := fun z => by
    simp only [κ, RingHom.comp_apply, map_eq_zero_iff _ (algebraMap q'.asIdeal.ResidueField K).injective]
    exact Ideal.algebraMap_residueField_eq_zero
  have h0 := h K κ (by
    rintro _ ⟨p, rfl⟩
    have : spMap κ p = q := by
      apply PrimeSpectrum.ext
      ext z
      have hp : p.asIdeal = ⊥ := Ideal.eq_bot_of_prime _ (h := p.isPrime)
      change κ z ∈ p.asIdeal ↔ z ∈ q'.asIdeal
      rw [hp, ← hker]; rfl
    rwa [this])
  exact hqa ((hker a).1 h0)

theorem mem_idealOf_of_dense : ∀ (R σ : Type) [CommRing R] (Y : Scheme.{0}) (s : Y ⟶ Sp R) (N : LB Y) (ty : σ → N.Sec) (Sg : Set (Sp R)) (F : MvPolynomial σ R) (e : ℕ), IsReduced Y → Flat s → LocallyOfFinitePresentation s → N.IsLB → Dense Sg → F.IsHomogeneous e → (∀ (K : Type) [Field K] [IsAlgClosed K] (β : R →+* K) (y : Sp K ⟶ Y) (v : σ → K), y ≫ s = spMap β → Set.range (spMap β) ⊆ Sg → SecCoord N ty y v → MvPolynomial.eval₂ β v F = 0) → F ∈ idealOf s N ty (𝟙 Y) := by
  intro R σ _ Y s N ty Sg F e hred hflat hlfp hN hSg hF H
  simp only [idealOf, Ideal.mem_iInf, RingHom.mem_ker, MvPolynomial.coe_eval₂Hom, Category.comp_id]
  rintro R' _ β y v ⟨hy, hv⟩
  refine eq_zero_of_localization _ fun J hJ => ?_
  let L := Localization.AtPrime J
  let φ : R' →+* L := algebraMap R' L
  let yL : Sp L ⟶ Y := spMap φ ≫ y
  obtain ⟨A, _, x, w, hx, hp, hw⟩ := (_root_.GlobalTheory.ZM.LocalCoord.secCoord_local Y N σ ty hN).2.2 (yL (IsLocalRing.closedPoint L))
  have hrange : Set.range yL ⊆ Set.range x := by
    rintro _ ⟨p, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint (R := L) p).map yL.continuous).mem_open
      x.isOpenEmbedding.isOpen_range hp
  obtain ⟨ψ, hψ⟩ := exists_spMap (IsOpenImmersion.lift x yL hrange)
  have hψx : spMap ψ ≫ x = yL := by rw [hψ, IsOpenImmersion.lift_fac]
  obtain ⟨α, hα⟩ := exists_spMap (x ≫ s)
  have hcomp : ψ.comp α = φ.comp β := by
    apply spMap_inj
    rw [← sp_comp, ← sp_comp, hα, ← Category.assoc, hψx, ← hy, Category.assoc]
  have h1 := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N σ ty A x w hN hw).1 L ψ
  have h2 := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N σ ty R' y v hN hv).1 L φ
  rw [hψx] at h1
  obtain ⟨u, hu⟩ := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N σ ty L yL _ hN h1).2.2 _ h2
  have hredA : IsReduced (Sp A) := isReduced_of_isOpenImmersion x
  have hredA' : _root_.IsReduced A := (affine_isReduced_iff (CommRingCat.of A)).1 hredA
  have hD : Dense ((x ≫ s) ⁻¹' Sg) := hSg.preimage (x ≫ s).isOpenMap
  have hA : MvPolynomial.eval₂ α w F = 0 := by
    refine eq_zero_of_dense _ hD _ fun K _ _ κ hκ => ?_
    rw [MvPolynomial.eval₂_comp_left]
    refine H K (κ.comp α) (spMap κ ≫ x) _ ?_ ?_
      ((GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Y N σ ty A x w hN hw).1 K κ)
    · rw [Category.assoc, ← hα, sp_comp]
    · rintro _ ⟨p, rfl⟩
      rw [← sp_comp, hα, Scheme.Hom.comp_apply]
      exact hκ ⟨p, rfl⟩
  change φ (MvPolynomial.eval₂ β v F) = 0
  rw [MvPolynomial.eval₂_comp_left, ← hcomp]
  have : (φ ∘ v) = fun i => (u : L) * (ψ ∘ w) i := funext hu
  rw [this, eval₂_scale _ _ _ hF, ← MvPolynomial.eval₂_comp_left, hA, map_zero, mul_zero]

end GlobalTheory.ZM.DenseFib
end

