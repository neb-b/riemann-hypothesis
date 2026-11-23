module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0332
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1789
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.RamifiedPlacesSplitEigen
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0330
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NvalDetFrChgConst
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtOfFrameEqOfPointEq
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
public import Development.AbelianVarietyTheory.Definitions.CMLattices.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteUnitaryFinitePointsExistsOpenCompactStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitaryFinitePoints_exists_openCompact : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), ∃ K : Subgroup (finU (E := E) (n := n)), IsOpen (K : Set (finU (E := E) (n := n))) ∧ IsCompact (K : Set (finU (E := E) (n := n))) := by
  first | exact @GlobalTheory.DefU.FinCompact.exists_open_compact | exact GlobalTheory.DefU.FinCompact.exists_open_compact | (intros; apply GlobalTheory.DefU.FinCompact.exists_open_compact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FibreIff
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.FlatRow

section Lie

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x : Sp R ⟶ S} {A : Over (Sp R)} [GrpObj A]
  {φ : A.left ⟶ G.left} {m : ℕ}

theorem exists_lift (h : IsGrpPullback A G x φ) (u : FramedFlatCoordinates.epsAt x ⟶ G) :
    ∃ v : epsR R ⟶ A, v.left ≫ φ = u.left :=
  let ⟨e, he⟩ := LiePull.exists_pushEquiv h (epsR R) (spMap (algebraMap R (DualNumber R)) ≫ x) rfl
  ⟨e.symm u, by rw [← he, e.apply_symm_apply]⟩

theorem fibre_iff (h : IsGrpPullback A G x φ) {v : Fin m → (epsR R ⟶ A)} {u : Fin m → (FramedFlatCoordinates.epsAt x ⟶ G)}
    (hu : ∀ i, (v i).left ≫ φ = (u i).left) :
    (∀ (c : Fin m → R) (w : epsR R ⟶ A) (w' : FramedFlatCoordinates.epsAt x ⟶ G), w.left ≫ φ = w'.left →
      (IsLieComb c v w ↔ FramedFlatCoordinates.IsCombination x c (fun i => (u i).left) w')) ∧
    ∀ {O : Type} [CommRing O] {a : OAct O A} {b : OAct O G}, (∀ c, (a.act c).left ≫ φ = φ ≫ (b.act c).left) →
      ∀ χ : O →+* R, EigenvectorLieDegree.IsEigBasis a χ v ↔ FramedFlatCoordinates.IsEigenBasis b x χ u := by
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv h (epsR R) (spMap (algebraMap R (DualNumber R)) ≫ x) rfl
  obtain ⟨e₀, he₀⟩ := LiePull.exists_pushEquiv h (𝟙_ (Over (Sp R))) x (Category.id_comp _).symm
  obtain rfl : u = fun i => e (v i) := funext fun i => Over.OverMorphism.ext ((hu i).symm.trans (he _).symm)
  have one : (1 : Over.mk x ⟶ G).left = η[A].left ≫ φ := by
    rw [← map_one e₀, he₀, Hom.one_def, toUnit_unit, Category.id_comp]
  have sc : ∀ c : R, spMap (epsScaleR c) ≫ spMap (algebraMap R (DualNumber R)) =
      spMap (algebraMap R (DualNumber R)) := fun c => by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp
  have hR : ∀ (c : R) (u v : epsR R ⟶ A), u.left = spMap (epsScaleR c) ≫ v.left ↔
      (e u).left = spMap (epsScaleR c) ≫ (e v).left := fun c u v => by
    rw [he, he]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _,
      fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w u).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    exact (congrArg (spMap (epsScaleR c) ≫ ·) (Over.w v)).trans (sc c)
  have pr : ∀ u : Fin m → (epsR R ⟶ A), e (List.ofFn u).prod = (List.ofFn fun i => e (u i)).prod := fun u => by
    rw [map_list_prod, List.map_ofFn]; rfl
  have hC : ∀ (c : Fin m → R) (w : epsR R ⟶ A),
      IsLieComb c v w ↔ FramedFlatCoordinates.IsCombination x c (fun i => (e (v i)).left) (e w) := fun c w => by
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i => e (u i), fun i => (hR _ _ _).1 (hu i), pr u⟩
    · rintro ⟨u, hu, hw⟩
      refine ⟨fun i => e.symm (u i), fun i => (hR _ _ _).2 (by simpa using hu i), e.injective ?_⟩
      rw [pr, hw]
      simp
  refine ⟨fun c w w' hw => ?_, fun {O} _ a b hab χ => ?_⟩
  · obtain rfl : w' = e w := Over.OverMorphism.ext (hw.symm.trans (he _).symm)
    exact hC c w
  have hP : ∀ v : epsR R ⟶ A, EigenvectorLieDegree.IsEigVec a χ v ↔ FramedFlatCoordinates.IsEigenTangent b x χ (e v) := fun v => by
    refine and_congr ?_ (forall_congr' fun c => ?_)
    · rw [one, he, IsTangent]
      refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
        fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
      refine ((Category.assoc _ _ _).trans ?_).trans (Over.w η[A]).symm
      exact (congrArg (spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ ·) (Over.w v)).trans fs
    · have E : e (v ≫ a.act c) = e v ≫ b.act c := Over.OverMorphism.ext (by
        rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hab, Category.assoc])
      rw [hR, E]
  refine and_congr (forall_congr' fun i => hP _) (Iff.trans ?_ e.surjective.forall.symm)
  exact forall_congr' fun w => imp_congr (hP w) (existsUnique_congr fun c => hC c w)

end Lie

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}

def EigStable {S : Scheme.{0}} (T : SAB H S) (c : Coeff l) : Prop :=
  ∀ (R R' : Type) [CommRing R] [CommRing R'] (g : R →+* R') (j : c.F →+* R) (x : Sp R ⟶ S) (τ : E →+* ℂ) (m : ℕ)
    (v : Fin m → (FramedFlatCoordinates.epsAt x ⟶ T.G)) (v' : Fin m → (FramedFlatCoordinates.epsAt (spMap g ≫ x) ⟶ T.G)),
    FramedFlatCoordinates.IsEigenBasis T.act x (FramedFlatCoordinates.chr c τ j) v →
    (∀ i, (v' i).left = spMap (Chart.dualMapR g) ≫ (v i).left) →
    FramedFlatCoordinates.IsEigenBasis T.act (spMap g ≫ x) (FramedFlatCoordinates.chr c τ (g.comp j)) v'

variable {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {U : (Xo.XF c).Opens} {τ : E →+* ℂ}

end GlobalTheory.FlatRow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalVectorValuedDefiniteUnitaryFormStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.BasicNotions Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame GlobalTheory.FrameAut
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_vectorValued_definiteUnitaryForms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Type) [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S] (ρ : Representation ℂ (infU E n) S) (K : Subgroup (finU (E := E) (n := n))), IsOpen (K : Set (finU (E := E) (n := n))) → ∀ M : Submodule ℂ (S →ₗ[ℂ] (UA E n → ℂ)), (∀ f ∈ M, (∀ v, ∀ γ ∈ ratU E n, ∀ g, f v (γ * g) = f v g) ∧ (∀ (x : infU E n) v, f (ρ x v) = RU E n x (f v)) ∧ ∀ k ∈ K, ∀ v, RU E n (k : UA E n) (f v) = f v) → FiniteDimensional ℂ M := by
  first | exact @GlobalTheory.DefU.finiteDimensional_vecForms | exact GlobalTheory.DefU.finiteDimensional_vecForms | (intros; apply GlobalTheory.DefU.finiteDimensional_vecForms <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FlatSecInhabited
section
noncomputable section

namespace GlobalTheory.FlatLine.Definite

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem comp_eq {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf U) {k k' : U.Comp}
    (x : (U.X k).dom) (x' : (U.X k').dom) (h : (U.un k x).x = (U.un k' x').x) : k' = k := by
  obtain ⟨b, -, -, hb, t, ht⟩ := GlobalTheory.PointOfFrames.exists_frBor (Formalism.L2.PjFree.Unf.ofPj U) hU hσ k x (U.un k' x') h
  obtain ⟨γ, -, b', -, e⟩ := (hU.2.2.2.1 k k' ⟨_, hb⟩ x').1 ⟨t, ht⟩
  exact congrArg Sigma.fst e

theorem nonempty_flatSec {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (hq : Dw.q = 0) (hp : 1 ≤ Dw.p)
    (hg : ∀ p : ℕ, p.Prime → l.GoodAt p) (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) (hF : FnAlgClosed (Xo := Xo) (c := c))
    (Z : Comp Xo c) (τ : Psi H) : Nonempty (FlatSec U x Z τ) := by
  have hpq : 1 ≤ Dw.p + Dw.q := by omega
  have hP := hasPts U hpq hg hU Z
  obtain ⟨y₀, h₀, hy₀⟩ := GlobalTheory.FlatLine.DefinitePoint.main E H Dw l Xo c hq hF Z
  obtain ⟨f, f', m₁, m₂, i₁, i₂, hm, hv⟩ := exists_flatRule E H Dw l Xo c hq Z τ y₀ h₀ hy₀
  have chg : ∀ (S : Type) [CommRing S] [Algebra c.F S] (y z : FrPt Xo c S), LiesOn Z y →
      FrMap (Algebra.ofId c.F S) y₀ z → ∃ (g : (∀ ρ : E →+* ℂ, Matrix (Fin (Dw.mult ρ)) (Fin (Dw.mult ρ)) S)) (a : Sˣ), (∀ ρ, IsUnit (g ρ).det) ∧ FrChg g (a : S) y z :=
    fun S _ _ y z hy hz => (frChg_exists_unique E H Dw l Xo c S y z).1 (hz.1.trans (hy₀ S y hy).symm)

  have hinf : ∀ σ : c.F →+* ℂ, ∃ b : ℝ, 0 < b ∧ homN (U (goodOf c σ)) x (wtOf Dw (flatWt Dw τ) 0) f ''
      framesOn (U (goodOf c σ)) Z = {b} := by
    intro σ₀
    obtain ⟨⟨⟨k, x₀⟩, hx₀⟩, ht⟩ := hP.1 σ₀
    have hσ := goodEmb_goodOf c σ₀
    generalize goodOf c σ₀ = σ at *
    have hV := hU σ hσ
    obtain ⟨z, hz⟩ := exists_bc (Algebra.ofId c.F (CAt σ)) y₀
    have hτ : ∀ k, relab c σ τ.1 ∈ ((U σ).X k).Ψ := fun k => ((hV.2.1 k).2 _).2 (by
      have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
      exact (congrArg σ (Subtype.ext τ.2)).trans hσ0)
    have rd : ∀ k y (hy : (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z) g a,
        FrChg g a ((U σ).un k ⟨y, hy.1⟩) z → rdU (U σ) f k y = toC (g τ.1).det := fun k y hy g a hc => by
      simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, hy.1, dif_pos]
      exact congrArg toC (hv _ _ z g a (ht _ hy hy.1) hz hc)
    have hh : IsHorizontal (U σ) Z τ f := fun k => by
      by_cases hne : ∃ y, (⟨k, y⟩ : Σ k, Frame ((U σ).X k).Ψ r) ∈ framesOn (U σ) Z
      · obtain ⟨y₁, h₁⟩ := hne
        refine ⟨hτ k, rdU (U σ) f k y₁ * (mat y₁ ⟨_, hτ k⟩).det, fun y hy => ?_⟩
        obtain ⟨g₁, a₁, -, c₁⟩ := chg _ _ z h₁.2 hz
        obtain ⟨g, a, -, c₂⟩ := (frChg_exists_unique E H Dw l Xo c _ ((U σ).un k ⟨y, hy.1⟩)
          ((U σ).un k ⟨y₁, h₁.1⟩)).1 ((hy₀ _ _ h₁.2).trans (hy₀ _ _ hy.2).symm)
        have c₃ := (frChg_refl_and_comp E H Dw l Xo c _ _ _ _).2 _ _ _ _ c₂ c₁
        have e := GlobalTheory.FlatChange.det_frChg E H Dw l Xo c σ r (U σ) hq hσ hV k ⟨y, hy.1⟩ ⟨y₁, h₁.1⟩ τ (hτ k) g a c₂
        rw [rd k y hy _ _ c₃, rd k y₁ h₁ _ _ c₁, e, horizGen, Matrix.det_mul, mul_assoc, mul_assoc,
          mul_inv_cancel₀ (hy.1 _).1, mul_one]
        rfl
      · exact ⟨hτ k, 0, fun y hy => absurd ⟨y, hy⟩ hne⟩
    obtain ⟨b, hb⟩ := hh.homN_const hσ hV x k
    refine ⟨b, ?_, image_eq_singleton_iff.2 ⟨⟨_, hx₀⟩, ?_⟩⟩
    · have h1 := homN_mul (U σ) x (even_wtOf (-flatWt Dw τ) 0) (even_wtOf (flatWt Dw τ) 0) f' f ⟨k, x₀⟩ hx₀.1
      rw [← wtOf_add', neg_add_cancel, wtOf_zero, mul_comm f', hm, homN_idem _ x hx₀.1 hx₀.2 (ht _ hx₀ _),
        hb x₀ hx₀] at h1
      refine lt_of_le_of_ne (hb x₀ hx₀ ▸ homN_nonneg _ _ _ _ _) fun h0 => ?_
      rw [← h0, mul_zero] at h1
      exact one_ne_zero h1
    · rintro ⟨k', y⟩ hy
      obtain rfl : k' = k := comp_eq hσ hV ⟨x₀, hx₀.1⟩ ⟨y, hy.1⟩ ((hy₀ _ _ hx₀.2).trans (hy₀ _ _ hy.2).symm)
      exact hb y hy
  choose cI hI₁ hI₂ using hinf

  choose ρ hρ using GlobalTheory.FlatLine.PlaceConst.nval_det_frChg_const E H Dw l Xo c hpq hg y₀ τ.1
  obtain ⟨S, hS0, hS⟩ := GlobalTheory.FlatLine.exists_finset_integral_of_definite E H Dw l Xo c hq hp hg y₀
  refine ⟨⟨f, f', m₁, m₂, i₁, i₂, hm, cI, hI₁, hI₂, ρ, fun w => image_eq_singleton_iff.2 ⟨hP.2 w, ?_⟩, ?_⟩⟩
  · rintro _ ⟨⟨_, T, io, e, ho, y, hy, η, hη, rfl⟩, rfl⟩
    letI := io.toAlgebra
    obtain ⟨z, hz⟩ := exists_bc (Algebra.ofId c.F T.Fr) y₀
    obtain ⟨g, a, -, hc⟩ := chg _ y.1 z hy.2 hz
    show nval T.V e (evR Xo c f y.1) = _
    rw [hv _ _ z g a y.2.1 hz hc, hρ w T io e ho y.1 z g a y.2.2 hz hc]
    simp [flDefect_vw, hq]
  · refine (S.finite_toSet.biUnion fun s hs => finite_vAdd (hS0 s hs)).subset fun w hw => ?_
    by_contra hn
    simp only [Set.mem_iUnion, Function.mem_support, not_exists, not_not, Int.cast_eq_zero] at hn
    obtain ⟨_, ⟨_, T, io, e, ho, -⟩, -⟩ := hP.2 w
    letI := io.toAlgebra
    obtain ⟨z, hz⟩ := exists_bc (Algebra.ofId c.F T.Fr) y₀
    have hi := hS T io (fun s hs => by rw [ho.2 s]; exact mul_eq_zero_of_right _ (hn s hs)) z hz
    have h1 := hρ w T io e ho z z _ _ hi hz (frChg_refl_and_comp E H Dw l Xo c _ z z z).1
    rw [Matrix.det_one, nval_of_ne one_ne_zero, EReal.coe_eq_coe_iff] at h1
    exact hw (h1.symm.trans (by simp [vV]))

end GlobalTheory.FlatLine.Definite
end
end

