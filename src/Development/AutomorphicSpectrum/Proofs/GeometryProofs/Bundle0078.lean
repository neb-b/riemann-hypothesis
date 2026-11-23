module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PCoordConeArithVar
public import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Assembly
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0015

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsArithVarOfBlockAlgebraic
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open Algebra GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CoordinateConeArithVar

section Dim

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem ratioField_eq_blockFnField (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ratioField y c = blockFnField y := by
  apply le_antisymm
  · refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨p, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨p, ⟨p.1, c p.1⟩, rfl, rfl⟩
  · refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨p, q, hpq, rfl⟩
    have hp : y p / y ⟨p.1, c p.1⟩ ∈ ratioField y c := IntermediateField.subset_adjoin _ _ ⟨p, rfl⟩
    have hq : y q / y ⟨q.1, c q.1⟩ ∈ ratioField y c := IntermediateField.subset_adjoin _ _ ⟨q, rfl⟩
    have key : y p / y q = (y p / y ⟨p.1, c p.1⟩) / (y q / y ⟨q.1, c q.1⟩) := by
      rw [← hpq]
      have h0 := hc p.1
      by_cases hq0 : y q = 0
      · simp [hq0]
      · field_simp
    rw [key]
    exact div_mem hp hq

theorem ringKrullDim_coord (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    ringKrullDim (MRing ι ⧸ mCoordIdeal y) =
      (((Algebra.trdeg ℤ (blockFnField y) + (Fintype.card K : Cardinal)).toENat + 1 : ℕ∞) : WithBot ℕ∞) := by
  haveI hP : (mCoordIdeal y).IsPrime := RingHom.ker_isPrime (mConeMap y)
  have hdim := GroundTheory.Heights₂.Heights.IntDomainDim.full (MRing ι ⧸ mCoordIdeal y)
    (algebraMap_injective _ (horizontal y))
  have hne : ∀ k, ∃ i, ratioPtL y c ⟨k, i⟩ ≠ 0 := by
    intro k
    refine ⟨c k, fun h0 => ?_⟩
    have h1 := congrArg Subtype.val h0
    change ratioPt y c ⟨k, c k⟩ = 0 at h1
    simp [ratioPt, hc k] at h1
  have htr := GroundTheory.Heights₂.Heights.ConeTrdeg.full K ι (ratioField y c) (ratioPtL y c)
    (birational y c hc) hne (horizontal _)
  rw [mCoordIdeal_ratioPtL y c hc] at htr
  rw [hdim, htr, ratioField_eq_blockFnField y c hc]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem trdeg_eq_of_le_of_isAlgebraic {L₁ L₂ : IntermediateField ℚ Ω} (h : L₁ ≤ L₂)
    (halg : ∀ t ∈ L₂, IsAlgebraic L₁ t) : Algebra.trdeg ℤ L₂ = Algebra.trdeg ℤ L₁ := by
  letI : Algebra L₁ L₂ := (IntermediateField.inclusion h).toRingHom.toAlgebra
  letI : FaithfulSMul L₁ L₂ :=
    (faithfulSMul_iff_algebraMap_injective L₁ L₂).2 (RingHom.injective _)
  let f : L₂ →ₐ[L₁] Ω :=
    { toRingHom := L₂.val.toRingHom
      commutes' := fun _ => rfl }
  haveI : Algebra.IsAlgebraic L₁ L₂ :=
    ⟨fun x => (isAlgebraic_algHom_iff f Subtype.val_injective).mp (halg x x.2)⟩
  have h0 : trdeg L₁ L₂ = 0 := trdeg_eq_zero
  rw [← trdeg_add_eq (R := ℤ) (S := L₁) (A := L₂), h0, add_zero]

end Dim

theorem isArithVar_of_isAlgebraic_image (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type)
    [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → Σ k, ι' k) (Ω : Type)
    [Field Ω] [CharZero Ω] (y : (Σ k, ι' k) → Ω) (d : ℕ) (hv : IsBlockMap κ v)
    (hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) (hz : IsArithVar (mCoordIdeal (y ∘ v)) d)
    (halg : ∀ t ∈ blockFnField y, IsAlgebraic (blockFnField (y ∘ v)) t) : IsArithVar (mCoordIdeal y) d := by
  classical
  obtain ⟨hK, -, -, hdz⟩ := hz
  obtain ⟨hκ, -, hfst, hsurj⟩ := hv
  choose c' hc' using hy
  have hcv : ∀ k : K, ∃ i : ι k, (y ∘ v) ⟨k, i⟩ ≠ 0 := by
    intro k
    obtain ⟨⟨k', i⟩, hp⟩ := hsurj ⟨κ k, c' (κ k)⟩ ⟨k, rfl⟩
    have h2 : k' = k := by
      apply hκ
      have h3 := hfst ⟨k', i⟩
      rw [hp] at h3
      exact h3.symm
    subst h2
    exact ⟨i, fun h0 => hc' _ (by rw [← hp]; exact h0)⟩
  choose c hc using hcv
  have e1 := hdz.symm.trans (ringKrullDim_coord (y ∘ v) c hc)
  have hle : blockFnField (y ∘ v) ≤ blockFnField y := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro _ ⟨p, q, hpq, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨v p, v q, by rw [hfst, hfst, hpq], rfl⟩
  have htr := trdeg_eq_of_le_of_isAlgebraic hle halg
  unfold IsArithVar IsMultiProjPrime
  refine ⟨⟨κ hK.some⟩, ⟨RingHom.ker_isPrime (mConeMap y), isMultiHomogIdeal y, relevant y c' hc'⟩,
    horizontal y, ?_⟩
  rw [ringKrullDim_coord y c' hc', htr]
  generalize Algebra.trdeg ℤ ↥(blockFnField (y ∘ v)) = T at e1 ⊢
  simp only [map_add (f := _), map_natCast] at e1 ⊢
  generalize Cardinal.toENat T = e at e1 ⊢
  induction e using ENat.recTopCoe with
  | top =>
    exfalso
    have h5 : ((d + Fintype.card K : ℕ) : ℕ∞) = ⊤ := by exact_mod_cast e1
    exact ENat.natCast_ne_top _ h5
  | coe m =>
    norm_cast at e1 ⊢
    omega

end GlobalTheory.CompanionTheory.Ar.Cmp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackCorrespondence
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.LieMove

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
  {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {R : Type} [CommRing R] {x : Sp R ⟶ S'}

theorem fst_comp_alg : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have e : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
    ext r; simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [e]
  exact Spec.map_id _

theorem epsMul_comp_alg (c : R) : Spec.map (CommRingCat.ofHom (epsMul c)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber R))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have e : (epsMul c).comp (algebraMap R (DualNumber R)) = algebraMap R (DualNumber R) := by
    ext r <;> simp [epsMul, TrivSqZeroExt.algebraMap_eq_inl]
  rw [e]

def pushEps (h : IsGrpPullback G' G f φ) (p : epsAt x ⟶ G') : epsAt (x ≫ f) ⟶ G :=
  Over.homMk (p.left ≫ φ) (by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w p]
    exact Category.assoc _ _ _)

def liftEps (h : IsGrpPullback G' G f φ) (v : epsAt (x ≫ f) ⟶ G) : epsAt x ⟶ G' :=
  Over.homMk (h.1.lift v.left (epsAt x).hom ((Over.w v).trans (Category.assoc _ _ _).symm)) (h.1.lift_snd _ _ _)

theorem pushEps_left (h : IsGrpPullback G' G f φ) (p : epsAt x ⟶ G') : (pushEps h p).left = p.left ≫ φ := rfl

theorem liftEps_left (h : IsGrpPullback G' G f φ) (v : epsAt (x ≫ f) ⟶ G) : (liftEps h v).left ≫ φ = v.left :=
  h.1.lift_fst _ _ _

theorem push_lift (h : IsGrpPullback G' G f φ) (v : epsAt (x ≫ f) ⟶ G) : pushEps h (liftEps h v) = v :=
  Over.OverMorphism.ext (liftEps_left h v)

theorem pushEps_inj (h : IsGrpPullback G' G f φ) : Function.Injective (pushEps (x := x) h) := fun p q e =>
  Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun z => z.left) e) ((Over.w p).trans (Over.w q).symm))

theorem pushEps_mul (h : IsGrpPullback G' G f φ) (p q : epsAt x ⟶ G') :
    pushEps h (p * q) = pushEps h p * pushEps h q := by
  let U : epsAt (x ≫ f) ⟶ Over.mk ((epsAt x).hom ≫ f) := Over.homMk (𝟙 _) (by simp)
  let V : Over.mk ((epsAt x).hom ≫ f) ⟶ epsAt (x ≫ f) := Over.homMk (𝟙 _) (by simp)
  have UV : U ≫ V = 𝟙 _ := Over.OverMorphism.ext (by simp [U, V])
  have e := h.2 (epsAt x) p q (V ≫ pushEps h p) (V ≫ pushEps h q) (by simp [V, pushEps_left])
    (by simp [V, pushEps_left])
  have e' : U ≫ ((V ≫ pushEps h p) * (V ≫ pushEps h q)) = pushEps h p * pushEps h q := by
    rw [MonObj.comp_mul, ← Category.assoc, ← Category.assoc, UV, Category.id_comp, Category.id_comp]
  rw [← e']
  apply Over.OverMorphism.ext
  rw [pushEps_left, ← e]
  simp [U]

theorem one_left (h : IsGrpPullback G' G f φ) :
    (1 : Over.mk x ⟶ G').left ≫ φ = (1 : Over.mk (x ≫ f) ⟶ G).left :=
  congrArg (fun z => z.left) (map_one (pushHom h (Over.mk x)))

theorem tan_iff (h : IsGrpPullback G' G f φ) (p : epsAt x ⟶ G') :
    IsTanAt G' x p ↔ IsTanAt G (x ≫ f) (pushEps h p) := by
  constructor
  · intro t
    show _ ≫ p.left ≫ φ = _
    rw [← Category.assoc, t, one_left h]
  · intro t
    refine h.1.hom_ext ?_ ?_
    · rw [Category.assoc, one_left h]
      exact t
    · have w := Over.w p
      have w₁ := Over.w (1 : Over.mk x ⟶ G')
      rw [Category.assoc, w, w₁]
      show _ ≫ Spec.map _ ≫ x = x
      rw [← Category.assoc, fst_comp_alg, Category.id_comp]

def pullModel {L : Type} [AddCommGroup L] [Module R L] (h : IsGrpPullback G' G f φ) (M : LieModel G (x ≫ f) L) :
    LieModel G' x L where
  pt e := liftEps h (M.pt e)
  tan e := (tan_iff h _).2 (by rw [push_lift]; exact M.tan e)
  inj a b e := M.inj ((push_lift h _).symm.trans ((congrArg (pushEps h) e).trans (push_lift h _)))
  onto v t := by
    obtain ⟨e, he⟩ := M.onto _ ((tan_iff h v).1 t)
    exact ⟨e, pushEps_inj h (by rw [push_lift, he])⟩
  add a b := pushEps_inj h (by rw [pushEps_mul, push_lift, push_lift, push_lift, M.add])
  smul c e := by
    refine h.1.hom_ext ?_ ?_
    · rw [liftEps_left, Category.assoc, liftEps_left, M.smul]
    · have w := fun v => Over.w (liftEps (x := x) h v)
      rw [Category.assoc, w, w]
      show Spec.map _ ≫ x = _ ≫ Spec.map _ ≫ x
      rw [← Category.assoc, epsMul_comp_alg]

def pushModel {L : Type} [AddCommGroup L] [Module R L] (h : IsGrpPullback G' G f φ) (M : LieModel G' x L) :
    LieModel G (x ≫ f) L where
  pt e := pushEps h (M.pt e)
  tan e := (tan_iff h _).1 (M.tan e)
  inj a b e := M.inj (pushEps_inj h e)
  onto v t := by
    obtain ⟨e, he⟩ := M.onto (liftEps h v) ((tan_iff h _).2 (by rw [push_lift]; exact t))
    exact ⟨e, by rw [he, push_lift]⟩
  add a b := by rw [M.add, pushEps_mul]
  smul c e := by
    show (M.pt (c • e)).left ≫ φ = _ ≫ (M.pt e).left ≫ φ
    rw [M.smul, Category.assoc]

theorem models_correspond (h : IsGrpPullback G' G f φ) (L : Type) [AddCommGroup L] [Module R L] :
    (∀ M : LieModel G (x ≫ f) L, ∃ M' : LieModel G' x L, ∀ e, (M'.pt e).left ≫ φ = (M.pt e).left) ∧
      ∀ M' : LieModel G' x L, ∃ M : LieModel G (x ≫ f) L, ∀ e, (M'.pt e).left ≫ φ = (M.pt e).left :=
  ⟨fun M => ⟨pullModel h M, fun _ => liftEps_left h _⟩, fun M' => ⟨pushModel h M', fun _ => rfl⟩⟩

end GlobalTheory.CompanionTheory.Ar.LieMove

theorem GlobalTheory.CompanionTheory.Ar.LieMove.main : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (x : Sp R ⟶ X) (G : Over X) [GrpObj G]
    (G₀ : Over (Sp R)) [GrpObj G₀] (ψ : G₀.left ⟶ G.left) (L : Type) [AddCommGroup L] [Module R L],
    IsGrpPullback G₀ G x ψ → (∀ M : LieModel G x L, ∃ M₀ : LieModel G₀ (𝟙 _) L, ∀ e, (M₀.pt e).left ≫ ψ = (M.pt e).left) ∧
      ∀ M₀ : LieModel G₀ (𝟙 _) L, ∃ M : LieModel G x L, ∀ e, (M₀.pt e).left ≫ ψ = (M.pt e).left := by
  intro R _ X x G _ G₀ _ ψ L _ _ h
  have key : ∀ y : Sp R ⟶ X, 𝟙 _ ≫ x = y →
      (∀ M : LieModel G y L, ∃ M₀ : LieModel G₀ (𝟙 _) L, ∀ e, (M₀.pt e).left ≫ ψ = (M.pt e).left) ∧
        ∀ M₀ : LieModel G₀ (𝟙 _) L, ∃ M : LieModel G y L, ∀ e, (M₀.pt e).left ≫ ψ = (M.pt e).left := by
    rintro _ rfl
    exact GlobalTheory.CompanionTheory.Ar.LieMove.models_correspond h L
  exact key x (Category.id_comp x)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SabMapId
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_sabMap_id : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0})
    (t : SAB H S), ∃ m : SABMap t t (𝟙 S), m.φ = 𝟙 t.G.left :=
  fun _ _ _ _ _ _ t => ⟨GlobalTheory.ObjRebase.sabMapId t, rfl⟩

end GlobalTheory.CompanionTheory.Ar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TorBC

private theorem mul_left_congr_of_base_eq {S W : Scheme.{0}} {G : Over S} [GrpObj G] {f f' : W ⟶ S} (h : f = f')
    (y₀ z₀ : Over.mk f ⟶ G) (y₁ z₁ : Over.mk f' ⟶ G) (hy : y₁.left = y₀.left) (hz : z₁.left = z₀.left) :
    (y₁ * z₁).left = (y₀ * z₀).left := by
  subst h
  have e1 : y₁ = y₀ := Over.OverMorphism.ext hy
  have e2 : z₁ = z₀ := Over.OverMorphism.ext hz
  rw [e1, e2]

private theorem pow_eq_one_congr_of_left_eq {S W : Scheme.{0}} {G : Over S} [GrpObj G] {f f' : W ⟶ S} (h : f = f')
    (g₀ : Over.mk f ⟶ G) (g₁ : Over.mk f' ⟶ G) (hg : g₁.left = g₀.left) (N : ℕ) :
    g₁ ^ N = 1 ↔ g₀ ^ N = 1 := by
  subst h
  have e : g₁ = g₀ := Over.OverMorphism.ext hg
  rw [e]

theorem isTorsionAlong_baseChange : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] (x : Sp R ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (R' : Type) [CommRing R'] [IsDomain R'] (φ : R →+* R') (Γ' : BT.QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ φ F → Γ'.IsTorsionAlong G (Spec.map (CommRingCat.ofHom φ) ≫ x) N (F ≫ i) := by
  intro R _ _ T _ Γ S G _ x N i hT R' _ _ φ Γ' F hB
  have hw : F ≫ Γ.G.hom = Γ'.G.hom ≫ Spec.map (CommRingCat.ofHom φ) := hB.cart.w
  have hassoc : ∀ {Y : Scheme.{0}} (h : Y ⟶ Spec (CommRingCat.of R')),
      h ≫ (Spec.map (CommRingCat.ofHom φ) ≫ x) = (h ≫ Spec.map (CommRingCat.ofHom φ)) ≫ x :=
    fun _ => (Category.assoc _ _ _).symm
  have lift1 : ∀ (Y : Over (Spec (CommRingCat.of R'))) (y : Y ⟶ Γ'.G),
      (y.left ≫ F) ≫ Γ.G.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ) := by
    intro Y y
    rw [Category.assoc, hw, ← Category.assoc, Over.w y]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Category.assoc, hT.isOver, ← Category.assoc, hw, Category.assoc]
  · intro Y y z y₀ z₀ hy hz
    let Y' : Over (Spec (CommRingCat.of R)) := Over.mk (Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    let y' : Y' ⟶ Γ.G := Over.homMk (y.left ≫ F) (lift1 Y y)
    let z' : Y' ⟶ Γ.G := Over.homMk (z.left ≫ F) (lift1 Y z)
    let y₁ : Over.mk (Y'.hom ≫ x) ⟶ G := Over.homMk y₀.left ((Over.w y₀).trans (hassoc Y.hom))
    let z₁ : Over.mk (Y'.hom ≫ x) ⟶ G := Over.homMk z₀.left ((Over.w z₀).trans (hassoc Y.hom))
    have hm := hT.mul Y' y' z' y₁ z₁
      (by show y₀.left = (y.left ≫ F) ≫ i; rw [Category.assoc]; exact hy)
      (by show z₀.left = (z.left ≫ F) ≫ i; rw [Category.assoc]; exact hz)
    have hF := hB.mul Y y z y' z' rfl rfl
    rw [← mul_left_congr_of_base_eq (hassoc Y.hom) y₀ z₀ y₁ z₁ rfl rfl, hm, hF, Category.assoc]
  · intro Y y z h
    let Y' : Over (Spec (CommRingCat.of R)) := Over.mk (Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    have e := hT.inj Y' (Over.homMk (y.left ≫ F) (lift1 Y y) : Y' ⟶ Γ.G)
      (Over.homMk (z.left ≫ F) (lift1 Y z) : Y' ⟶ Γ.G)
      (by show (y.left ≫ F) ≫ i = (z.left ≫ F) ≫ i; rw [Category.assoc, Category.assoc]; exact h)
    have e2 : y.left ≫ F = z.left ≫ F := congrArg (fun m => m.left) e
    apply Over.OverMorphism.ext
    exact hB.cart.hom_ext e2 ((Over.w y).trans (Over.w z).symm)
  · intro Y g
    let Y' : Over (Spec (CommRingCat.of R)) := Over.mk (Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
    let g₁ : Over.mk (Y'.hom ≫ x) ⟶ G := Over.homMk g.left ((Over.w g).trans (hassoc Y.hom))
    rw [← pow_eq_one_congr_of_left_eq (hassoc Y.hom) g g₁ rfl N, hT.kernel Y' g₁]
    constructor
    · rintro ⟨y', hy'⟩
      refine ⟨Over.homMk (hB.cart.lift y'.left Y.hom (Over.w y')) (hB.cart.lift_snd _ _ _), ?_⟩
      show hB.cart.lift y'.left Y.hom (Over.w y') ≫ F ≫ i = g.left
      rw [← Category.assoc, hB.cart.lift_fst]
      exact hy'
    · rintro ⟨y, hy⟩
      refine ⟨(Over.homMk (y.left ≫ F) (lift1 Y y) : Y' ⟶ Γ.G), ?_⟩
      show (y.left ≫ F) ≫ i = g.left
      rw [Category.assoc]
      exact hy

end GlobalTheory.CompanionTheory.Ar.TorBC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongGroupPullback
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.TorPull

theorem pow_eq_one_congr {S X : Scheme.{0}} {G : Over S} [GrpObj G] {a b : X ⟶ S} (h : a = b)
    (x : Over.mk a ⟶ G) (x' : Over.mk b ⟶ G) (hx : x.left = x'.left) (N : ℕ) :
    x ^ N = 1 ↔ x' ^ N = 1 := by
  subst h
  rw [Over.OverMorphism.ext hx]

theorem pushHom_injective {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    Function.Injective (pushHom h T) := by
  intro x y e
  apply Over.OverMorphism.ext
  apply h.1.hom_ext
  · exact congrArg (fun z => z.left) e
  · rw [Over.w, Over.w]

theorem exists_lift_isTorsionAlong : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T) (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (x' : Sp R ⟶ S') (y : Sp R ⟶ S) (N : ℕ) (i₁ : Γ.G.left ⟶ G.left), IsGrpPullback G' G f φ → x' ≫ f = y → Γ.IsTorsionAlong G y N i₁ → ∃ i' : Γ.G.left ⟶ G'.left, i' ≫ φ = i₁ ∧ Γ.IsTorsionAlong G' x' N i' := by
  intro R _ _ T _ Γ S S' G G' _ _ f φ x' y N i₁ h e hT
  subst e
  have hw : i₁ ≫ G.hom = (Γ.G.hom ≫ x') ≫ f := by rw [hT.isOver, Category.assoc]
  have hfst : h.1.lift i₁ (Γ.G.hom ≫ x') hw ≫ φ = i₁ := h.1.lift_fst _ _ _
  have hsnd : h.1.lift i₁ (Γ.G.hom ≫ x') hw ≫ G'.hom = Γ.G.hom ≫ x' := h.1.lift_snd _ _ _
  generalize h.1.lift i₁ (Γ.G.hom ≫ x') hw = i' at hfst hsnd

  have mk : ∀ (Y : Over (Spec (CommRingCat.of R))) (g : Over.mk (Y.hom ≫ x') ⟶ G'),
      (g.left ≫ φ) ≫ G.hom = Y.hom ≫ x' ≫ f := fun Y g => by
    have w₁ : g.left ≫ G'.hom = Y.hom ≫ x' := Over.w g
    rw [Category.assoc, h.1.w, ← Category.assoc, w₁, Category.assoc]
  refine ⟨i', hfst, ⟨hsnd, ?_, ?_, ?_⟩⟩
  · intro Y a b a₀ b₀ ha hb
    have ea : (Over.homMk (a₀.left ≫ φ) (mk Y a₀) : Over.mk (Y.hom ≫ x' ≫ f) ⟶ G).left = a.left ≫ i₁ := by
      simp [ha, ← hfst]
    have eb : (Over.homMk (b₀.left ≫ φ) (mk Y b₀) : Over.mk (Y.hom ≫ x' ≫ f) ⟶ G).left = b.left ≫ i₁ := by
      simp [hb, ← hfst]
    have e₁ := hT.mul Y a b _ _ ea eb
    have e₂ := h.2 (Over.mk (Y.hom ≫ x')) a₀ b₀ (pushPt h.1.w a₀) (pushPt h.1.w b₀) rfl rfl
    have e₃ := mul_left_congr (Category.assoc Y.hom x' f) (pushPt h.1.w a₀) (pushPt h.1.w b₀)
      (Over.homMk (a₀.left ≫ φ) (mk Y a₀)) (Over.homMk (b₀.left ≫ φ) (mk Y b₀)) rfl rfl
    apply h.1.hom_ext
    · rw [← e₂, e₃, e₁, Category.assoc, hfst]
    · have w₁ : (a₀ * b₀).left ≫ G'.hom = Y.hom ≫ x' := Over.w (a₀ * b₀)
      have w₂ : (a * b).left ≫ Γ.G.hom = Y.hom := Over.w (a * b)
      rw [w₁, Category.assoc, hsnd, ← Category.assoc, w₂]
  · intro Y a b e
    apply hT.inj Y a b
    rw [← hfst, ← Category.assoc, ← Category.assoc, e]
  · intro Y g
    let g₁ : Over.mk (Y.hom ≫ x' ≫ f) ⟶ G := Over.homMk (g.left ≫ φ) (mk Y g)
    have hp : g ^ N = 1 ↔ g₁ ^ N = 1 := by
      rw [← pow_eq_one_congr (Category.assoc Y.hom x' f) (pushHom h (Over.mk (Y.hom ≫ x')) g) g₁ rfl N,
        ← map_pow, ← map_one (pushHom h (Over.mk (Y.hom ≫ x')))]
      exact (pushHom_injective h _).eq_iff.symm
    rw [hp, hT.kernel Y g₁]
    refine exists_congr fun a => ?_
    constructor
    · intro e
      apply h.1.hom_ext
      · rw [Category.assoc, hfst]; exact e
      · have w₁ : g.left ≫ G'.hom = Y.hom ≫ x' := Over.w g
        have w₂ : a.left ≫ Γ.G.hom = Y.hom := Over.w a
        rw [w₁, Category.assoc, hsnd, ← Category.assoc, w₂]
    · intro e
      show a.left ≫ i₁ = g.left ≫ φ
      rw [← e, ← hfst, Category.assoc]

end GlobalTheory.CompanionTheory.Ar.TorPull
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionAlongOrderDivides
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.BT.TorsionKilled

theorem pow_eq_one : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] (x : Sp R ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ t : T, t ^ N = 1 := by
  intro R _ _ T _ Γ S G _ x N i h t
  let lift : (genPt R ⟶ Γ.G) → (Over.mk ((genPt R).hom ≫ x) ⟶ G) := fun y =>
    Over.homMk (y.left ≫ i) (by
      have w := Over.w y
      simp only [Over.mk_hom, Category.assoc, h.isOver]
      rw [← Category.assoc, w]
      rfl)
  have lift_left : ∀ y, (lift y).left = y.left ≫ i := fun y => rfl
  have lift_mul : ∀ y z, lift (y * z) = lift y * lift z := fun y z => by
    ext1
    rw [h.mul (genPt R) y z (lift y) (lift z) rfl rfl]
    rfl
  have lift_one : lift 1 = 1 := by
    have e : lift 1 * lift 1 = lift 1 := by rw [← lift_mul, _root_.mul_one]
    exact mul_eq_left.mp e
  let L : (genPt R ⟶ Γ.G) →* (Over.mk ((genPt R).hom ≫ x) ⟶ G) :=
    { toFun := lift, map_one' := lift_one, map_mul' := lift_mul }
  have hk : lift (Γ.pt t) ^ N = 1 := (h.kernel (genPt R) (lift (Γ.pt t))).2 ⟨Γ.pt t, rfl⟩
  have hL : L (Γ.pt t ^ N) = L 1 := by
    rw [map_pow, map_one]
    exact hk
  have hy : Γ.pt t ^ N = 1 := h.inj (genPt R) _ _ (by
    have := congrArg (fun g : Over.mk ((genPt R).hom ≫ x) ⟶ G => g.left) hL
    exact this)
  have hp : Γ.pt (t ^ N) = Γ.pt 1 := by rw [map_pow, map_one, hy]
  let c : Spec (CommRingCat.of (FractionRing R)) := IsLocalRing.closedPoint (FractionRing R)
  exact Γ.pt_inj (t ^ N) 1 c c (by rw [hp])

end GlobalTheory.CompanionTheory.Ar.BT.TorsionKilled
end
end

