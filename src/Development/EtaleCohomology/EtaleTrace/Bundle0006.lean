module

public import Development.EtaleCohomology.EtaleTrace.Bundle0003
public import Development.EtaleCohomology.EtaleTrace.PNBasicPf
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.PullbackCarrier

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleTrace.GenOutChartPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

def LocOpen : Prop := ∀ (X : Scheme.{0}) [IsIntegral X] (z : X.functionField), IsOpen {y : X | z ∈ loc X y}

def ChartMap : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField) (i : Fin (N + 1)), w i ≠ 0 → ∀ (U : X.Opens),
  (∀ y ∈ U, ∀ j, w j / w i ∈ loc X y) →
  ∃ πU : U.toScheme ⟶ PN k N, πU ≫ PNto k N = U.ι ≫ p ∧ GenOn p w U πU

theorem GenOutChart_of_cut (h1 : LocOpen) (h2 : ChartMap) : GenOutChart := by
  intro k _ X _ p N w hw x
  obtain ⟨i, hi, hx⟩ := hw x
  have hop : IsOpen {y : X | ∀ j, w j / w i ∈ loc X y} := by
    have : {y : X | ∀ j, w j / w i ∈ loc X y} = ⋂ j, {y : X | w j / w i ∈ loc X y} := by
      ext y; simp
    rw [this]
    exact isOpen_iInter_of_finite fun j => h1 X (w j / w i)
  obtain ⟨πU, h1U, h2U⟩ := h2 k p N w i hi ⟨_, hop⟩ (fun y hy => hy)
  exact ⟨⟨_, hop⟩, πU, hx, h1U, h2U⟩

theorem LocOpen_pf (X : Scheme.{0}) [IsIntegral X] (z : X.functionField) : IsOpen {y : X | z ∈ loc X y} := by
  rw [isOpen_iff_forall_mem_open]
  rintro y ⟨a, rfl⟩
  obtain ⟨V, hyV, s, rfl⟩ := X.presheaf.exists_germ_eq (x := y) a
  have : Nonempty V := ⟨⟨y, hyV⟩⟩
  refine ⟨V, fun y' hy' => ?_, V.isOpen, hyV⟩
  refine ⟨X.presheaf.germ V y' hy' s, ?_⟩
  simp only [Scheme.algebraMap_germ_eq_germToFunctionField]

def ChartRing : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField) (i : Fin (N + 1)), w i ≠ 0 → ∀ (U : X.Opens),
  (∀ y ∈ U, ∀ j, w j / w i ∈ loc X y) →
  ∀ (hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1),
  ∃ φ : HomogeneousLocalization.Away (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) →+* Γ(X, U),
    ∀ (y : X) (hy : y ∈ U) (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k)
      (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • 1)),
      algebraMap (X.presheaf.stalk y) X.functionField
        (X.presheaf.germ U y hy (φ (HomogeneousLocalization.Away.mk _ hx m g hg))) = eval₂ (kHom p) w g / w i ^ m

def ChartGen : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField) (i : Fin (N + 1)), w i ≠ 0 → ∀ (U : X.Opens)
  (hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1)
  (φ : HomogeneousLocalization.Away (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) →+* Γ(X, U)),
  (∀ (y : X) (hy : y ∈ U) (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k)
      (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • 1)),
      algebraMap (X.presheaf.stalk y) X.functionField
        (X.presheaf.germ U y hy (φ (HomogeneousLocalization.Away.mk _ hx m g hg))) = eval₂ (kHom p) w g / w i ^ m) →
  ∃ πU : U.toScheme ⟶ PN k N, πU ≫ PNto k N = U.ι ≫ p ∧ GenOn p w U πU

theorem ChartMap_pf (h1 : ChartRing) (h2 : ChartGen) : ChartMap := by
  intro k _ X _ p N w i hi U hU
  have hx : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1 :=
    (mem_homogeneousSubmodule _ _).2 (isHomogeneous_X k i)
  obtain ⟨φ, hφ⟩ := h1 k p N w i hi U hU hx
  exact h2 k p N w i hi U hx φ hφ

theorem GenOutChart_of (h1 : ChartRing) (h2 : ChartGen) : GenOutChart :=
  GenOutChart_of_cut (fun X _ z => LocOpen_pf X z) (ChartMap_pf h1 h2)

end LateralTheory.EtaleTrace.Cov
end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.GenUseBackPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

lemma gub_stalk_inj {X : Scheme.{0}} [IsIntegral X] (x : X) :
    Function.Injective (algebraMap (X.presheaf.stalk x) X.functionField) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro a ha
  obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.exists_germ_eq a
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  rw [Scheme.algebraMap_germ_eq_germToFunctionField] at ha
  have := Scheme.germToFunctionField_injective X U (ha.trans (map_zero _).symm)
  rw [this, map_zero]

lemma gub_notMem {k : Type} [Field k] {N : ℕ} (h : MvPolynomial (Fin (N + 1)) k) {d : ℕ}
    (hh : h ∈ homogeneousSubmodule (Fin (N + 1)) k d) (n : ℕ) (f : MvPolynomial (Fin (N + 1)) k)
    (hf : f ∈ homogeneousSubmodule (Fin (N + 1)) k (n • d)) (y : Proj (homogeneousSubmodule (Fin (N + 1)) k))
    (hy : y ∈ (Proj (homogeneousSubmodule (Fin (N + 1)) k)).basicOpen
      (Proj.awayToSection _ h (HomogeneousLocalization.Away.mk _ hh n f hf))) :
    y ∈ Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) f := by
  obtain ⟨hyU, hu⟩ := (Scheme.mem_basicOpen'' _ _ _).mp hy
  have hu2 := hu.map (Proj.stalkIso' (homogeneousSubmodule (Fin (N + 1)) k) y)
  erw [Proj.stalkIso'_germ] at hu2
  rw [← HomogeneousLocalization.isUnit_iff_isUnit_val] at hu2
  erw [ProjectiveSpectrum.Proj.awayToSection_apply] at hu2
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk'] at hu2
  rw [Proj.mem_basicOpen]
  have hp : y.asHomogeneousIdeal.toIdeal.IsPrime := y.isPrime
  exact (IsLocalization.AtPrime.isUnit_mk'_iff (hI := hp) _ _ _ _).mp hu2

lemma gub_cover {k : Type} [Field k] {N : ℕ} (y : Proj (homogeneousSubmodule (Fin (N + 1)) k)) :
    ∃ i, y ∈ Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) := by
  have hcov : ⨆ i, Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) = ⊤ := by
    apply Proj.iSup_basicOpen_eq_top'
    · exact fun i => ⟨1, (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X k i)⟩
    · rw [eq_top_iff]
      rintro a -
      induction a using MvPolynomial.induction_on with
      | C c =>
        have : (C c : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 0 :=
          (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_C _ c)
        exact Subalgebra.algebraMap_mem _ (⟨_, this⟩ : homogeneousSubmodule (Fin (N + 1)) k 0)
      | add a b ha hb => exact Subalgebra.add_mem _ ha hb
      | mul_X a i ha => exact Subalgebra.mul_mem _ ha (Algebra.subset_adjoin ⟨i, rfl⟩)
  have hm : y ∈ (⊤ : (Proj (homogeneousSubmodule (Fin (N + 1)) k)).Opens) := trivial
  rw [← hcov, TopologicalSpace.Opens.mem_iSup] at hm
  exact hm

theorem GenUseBack_of : GenUseBack := by
  intro k _ X _ p N ι v hG n hn f hf x hne hloc
  obtain ⟨i, hxi⟩ := gub_cover (ι x)
  have hXi : (MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ∈ homogeneousSubmodule (Fin (N + 1)) k 1 :=
    (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X k i)
  have hxU : x ∈ ι ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) := hxi
  have hη := genUse_generic_mem _ x hxU
  have hvi : eval₂ (kHom p) v (MvPolynomial.X i) ≠ 0 := ((hG 1 one_pos _ hXi).1).mp hη
  have hf' : f ∈ homogeneousSubmodule (Fin (N + 1)) k (n • 1) := by
    rw [smul_eq_mul, mul_one]; exact (mem_homogeneousSubmodule _ _).mpr hf
  have key := (hG 1 one_pos _ hXi).2 n f hf' hη
  have : Nonempty (ι ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i)) := ⟨⟨x, hxU⟩⟩
  have hγ : algebraMap _ X.functionField (X.presheaf.germ _ x hxU (ι.app _ (Proj.awayToSection _ (MvPolynomial.X i)
      (HomogeneousLocalization.Away.mk _ hXi n f hf')))) =
      eval₂ (kHom p) v f / eval₂ (kHom p) v (MvPolynomial.X i) ^ n := by
    rw [Scheme.algebraMap_germ_eq_germToFunctionField, eq_div_iff (pow_ne_zero _ hvi)]
    exact key
  have hg : ((MvPolynomial.X i : MvPolynomial (Fin (N + 1)) k) ^ n).IsHomogeneous n := by
    simpa using (isHomogeneous_X k i).pow n
  obtain ⟨δ, hδ⟩ := hloc _ hg
  have hu : IsUnit (X.presheaf.germ _ x hxU (ι.app _ (Proj.awayToSection _ (MvPolynomial.X i)
      (HomogeneousLocalization.Away.mk _ hXi n f hf')))) := by
    refine isUnit_iff_exists_inv.mpr ⟨δ, gub_stalk_inj x ?_⟩
    rw [map_mul, map_one, hγ, hδ, eval₂_pow]
    have h1 := pow_ne_zero n hvi
    field_simp
  have hmem := (Scheme.mem_basicOpen'' _ _ _).mpr ⟨hxU, hu⟩
  rw [← Scheme.preimage_basicOpen] at hmem
  exact gub_notMem _ hXi n f hf' _ hmem

end LateralTheory.EtaleTrace.Cov
end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.PNIntegralPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

theorem hl_reduced (k : Type) [Field k] (d : ℕ) (P : Ideal (MvPolynomial (Fin (d + 1)) k)) [P.IsPrime] :
    _root_.IsReduced (HomogeneousLocalization.AtPrime (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) P) := by
  refine ⟨fun a ha => ?_⟩
  obtain ⟨n, hn⟩ := ha
  apply HomogeneousLocalization.val_injective
  have h : a.val ^ n = 0 := by
    rw [← HomogeneousLocalization.val_pow, hn, HomogeneousLocalization.val_zero]
  rw [HomogeneousLocalization.val_zero]
  exact IsReduced.eq_zero _ ⟨n, h⟩

theorem pn_reduced (k : Type) [Field k] (d : ℕ) : IsReduced (PN k d) := by
  have : ∀ x : PN k d, _root_.IsReduced ((PN k d).presheaf.stalk x) := by
    intro x
    haveI : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
    haveI := hl_reduced k d x.asHomogeneousIdeal.toIdeal
    let e := Proj.stalkIso' (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) x
    exact isReduced_of_injective e.toRingHom e.injective
  exact isReduced_of_isReduced_stalk _

theorem mvPolynomial_irrelevantIdeal_not_le_bot_projective (k : Type) [Field k] (d : ℕ) :
    ¬ HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) ≤ ⊥ := by
  intro h
  have hm : (X 0 : MvPolynomial (Fin (d + 1)) k) ∈ HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) := by
    rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply]
    exact DirectSum.decompose_of_mem_ne _ ((MvPolynomial.mem_homogeneousSubmodule _ _).2 (isHomogeneous_X k 0)) (by decide)
  have h2 : (X 0 : MvPolynomial (Fin (d + 1)) k) ∈ (⊥ : HomogeneousIdeal (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k)).toIdeal := h hm
  rw [HomogeneousIdeal.toIdeal_bot, Ideal.mem_bot] at h2
  exact X_ne_zero _ h2

def gen (k : Type) [Field k] (d : ℕ) : PN k d where
  asHomogeneousIdeal := ⊥
  isPrime := by
    show (⊥ : Ideal (MvPolynomial (Fin (d + 1)) k)).IsPrime
    exact Ideal.isPrime_bot
  not_irrelevant_le := mvPolynomial_irrelevantIdeal_not_le_bot_projective k d

theorem pn_irred (k : Type) [Field k] (d : ℕ) : IrreducibleSpace (PN k d) := by
  rw [irreducibleSpace_def]
  have : (Set.univ : Set (PN k d)) = closure {gen k d} := by
    ext y
    simp only [Set.mem_univ, true_iff]
    exact (ProjectiveSpectrum.le_iff_mem_closure (MvPolynomial.homogeneousSubmodule (Fin (d + 1)) k) (gen k d) y).1
      (show (gen k d).asHomogeneousIdeal ≤ y.asHomogeneousIdeal from bot_le)
  change IsIrreducible (Set.univ : Set (PN k d))
  rw [this]
  exact isIrreducible_singleton.closure

theorem PNIntegral_of : PNIntegral := fun k _ d => by
  haveI := pn_reduced k d
  haveI := pn_irred k d
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end LateralTheory.EtaleTrace.Cov
end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.PtCovPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.EtaleTrace

theorem exists_ratPt_of_etale (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} (p : X ⟶ S k)
    (hp : IsProper p) {U : Scheme.{0}} (f : U ⟶ X) [Etale f] (x : U) :
    ∃ w : S k ⟶ U, w ≫ f ≫ p = 𝟙 _ := by
  have := hp
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p
  have hopen : IsOpen (Set.range f) := f.isOpenMap.isOpen_range
  obtain ⟨y, ⟨x', rfl⟩, hy⟩ := nonempty_inter_closedPoints (show (Set.range f).Nonempty from ⟨f x, x, rfl⟩) hopen.isLocallyClosed
  let s : S k ⟶ X := pointOfClosedPoint p (f x') hy
  obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed f s x' (pointOfClosedPoint_apply p (f x') hy _).symm
  exact ⟨l, by rw [reassoc_of% hl]; exact pointOfClosedPoint_comp p (f x') hy⟩

theorem PtCov_of : PtCov := by
  intro k _ _ X p hp Sv hSv
  obtain ⟨𝒰, h𝒰⟩ := Scheme.mem_grothendieckTopology_iff.1 hSv
  let T : Sieve X :=
    { arrows := fun V g => ∃ (U : Scheme.{0}) (g' : U ⟶ X) (h : V ⟶ U),
        Sv.arrows g' ∧ h ≫ g' = g ∧ ∃ w : S k ⟶ U, w ≫ g' ≫ p = 𝟙 _
      downward_closed := by
        rintro V W g ⟨U, g', h, hg', rfl, w, hw⟩ a
        exact ⟨U, g', a ≫ h, hg', by simp, w, hw⟩ }
  refine ⟨T, ?_, fun V g hg => hg⟩
  have hG : Sieve.generate (Presieve.ofArrows 𝒰.X 𝒰.f) ∈ Scheme.etaleTopology X :=
    Scheme.mem_grothendieckTopology_iff.2 ⟨𝒰, Sieve.le_generate _⟩
  refine (Scheme.etaleTopology).transitive hG T ?_
  rintro Z _ ⟨W, a, b, hb, rfl⟩
  rw [Sieve.pullback_comp]
  refine (Scheme.etaleTopology).pullback_stable a ?_
  obtain ⟨i⟩ := hb
  by_cases hne : Nonempty (𝒰.X i)
  · obtain ⟨x⟩ := hne
    obtain ⟨w, hw⟩ := exists_ratPt_of_etale k p hp (𝒰.f i) x
    have : T.arrows (𝒰.f i) := ⟨𝒰.X i, 𝒰.f i, 𝟙 _, h𝒰 _ _ (Presieve.ofArrows.mk i), by simp, w, hw⟩
    rw [Sieve.pullback_eq_top_of_mem T this]
    exact (Scheme.etaleTopology).top_mem _
  · have : IsEmpty (𝒰.X i) := not_nonempty_iff.1 hne
    exact (Scheme.etaleTopology).superset_covering bot_le (Scheme.bot_mem_grothendieckTopology _)

end LateralTheory.EtaleTrace
end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.RatPtInPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

theorem RatPtIn_of : RatPtIn := by
  intro k _ _ P r hr V hV
  have := hr
  have : JacobsonSpace P := LocallyOfFiniteType.jacobsonSpace r
  obtain ⟨x, hxV, hxc⟩ := nonempty_inter_closedPoints hV V.isOpen.isLocallyClosed
  refine ⟨⟨pointOfClosedPoint r x hxc, pointOfClosedPoint_comp r x hxc⟩, fun a => ?_⟩
  have h := pointOfClosedPoint_apply r x hxc a
  show (pointOfClosedPoint r x hxc) a ∈ V
  rw [h]; exact hxV

end LateralTheory.EtaleTrace.Cov
end
end

-- bundled from Development.EtaleCohomology.EtaleTrace.TateTwistSectionConstantOnPointsOfTwLocPtCov
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleTrace

def ConnLoc : Prop := ∀ {X : Scheme.{0}}, ConnectedSpace X → ∀ (P Q : ∀ V : Scheme.{0}, (V ⟶ X) → Prop),
  (∀ (V W : Scheme.{0}) (g : V ⟶ X) (h : W ⟶ V), P V g → P W (h ≫ g)) →
  (∀ (V W : Scheme.{0}) (g : V ⟶ X) (h : W ⟶ V), Q V g → Q W (h ≫ g)) →
  (∀ (V : Scheme.{0}) (g : V ⟶ X), IsEmpty V → P V g ∧ Q V g) →
  (∀ (V : Scheme.{0}) (g : V ⟶ X), P V g → Q V g → IsEmpty V) →
  Loc X (fun V g => P V g ∨ Q V g) → Loc X P ∨ Loc X Q

def PtLift : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} (z : S k ⟶ X)
  (R : ∀ V : Scheme.{0}, (V ⟶ X) → Prop), Loc X R →
    ∃ (V : Scheme.{0}) (g : V ⟶ X) (w : S k ⟶ V), R V g ∧ w ≫ g = z

theorem ConnLoc_pf : ConnLoc := by
  intro X hX P Q hPs hQs hE hD hL
  obtain ⟨Sv, hSv, hSs⟩ := hL
  obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hSv
  have hi : ∀ i, P (𝒰.X i) (𝒰.f i) ∨ Q (𝒰.X i) (𝒰.f i) := fun i => hSs _ _ (h𝒰 _ _ (Presieve.ofArrows.mk i))
  have hcov := ((Scheme.presieve₀_mem_precoverage_iff _).mp 𝒰.mem₀).1
  have hop : ∀ i, IsOpen (Set.range (𝒰.f i)) := fun i => by
    haveI : Etale (𝒰.f i) := 𝒰.map_prop i
    exact (𝒰.f i).isOpenMap.isOpen_range
  let A : Set X := ⋃ (i) (_ : P (𝒰.X i) (𝒰.f i)), Set.range (𝒰.f i)
  let B : Set X := ⋃ (i) (_ : ¬ P (𝒰.X i) (𝒰.f i)), Set.range (𝒰.f i)
  have hAo : IsOpen A := isOpen_iUnion fun i => isOpen_iUnion fun _ => hop i
  have hBo : IsOpen B := isOpen_iUnion fun i => isOpen_iUnion fun _ => hop i
  have hAB : ∀ x, x ∈ A ∨ x ∈ B := by
    intro x
    obtain ⟨i, hx⟩ := hcov x
    by_cases h : P (𝒰.X i) (𝒰.f i)
    · exact Or.inl (Set.mem_iUnion₂.2 ⟨i, h, hx⟩)
    · exact Or.inr (Set.mem_iUnion₂.2 ⟨i, h, hx⟩)
  have hdis : ∀ x, x ∈ A → x ∈ B → False := by
    intro x hA hB
    obtain ⟨i, hPi, a, ha⟩ := Set.mem_iUnion₂.1 hA
    obtain ⟨j, hPj, b, hb⟩ := Set.mem_iUnion₂.1 hB
    have hQj : Q (𝒰.X j) (𝒰.f j) := (hi j).resolve_left hPj
    obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := 𝒰.f i) (g := 𝒰.f j) a b (ha.trans hb.symm)
    have h1 := hPs _ _ _ (pullback.fst (𝒰.f i) (𝒰.f j)) hPi
    have h2 := hQs _ _ _ (pullback.snd (𝒰.f i) (𝒰.f j)) hQj
    rw [← pullback.condition] at h2
    exact (hD _ _ h1 h2).false z
  have hAc : IsClosed A := by
    have : A = Bᶜ := by
      ext x; constructor
      · intro hA hB; exact hdis x hA hB
      · intro hB; exact (hAB x).resolve_right hB
    rw [this]; exact hBo.isClosed_compl
  have hmem := Scheme.Cover.mem_grothendieckTopology 𝒰
  rcases isClopen_iff.1 ⟨hAc, hAo⟩ with h0 | h1
  · right
    refine ⟨_, hmem, fun V g hg => ?_⟩
    obtain ⟨W, h, g', ⟨i⟩, rfl⟩ := hg
    apply hQs
    by_cases hP : P (𝒰.X i) (𝒰.f i)
    · refine (hE _ _ ⟨fun a => ?_⟩).2
      have : 𝒰.f i a ∈ A := Set.mem_iUnion₂.2 ⟨i, hP, a, rfl⟩
      rw [h0] at this; exact this
    · exact (hi i).resolve_left hP
  · left
    refine ⟨_, hmem, fun V g hg => ?_⟩
    obtain ⟨W, h, g', ⟨i⟩, rfl⟩ := hg
    apply hPs
    by_cases hP : P (𝒰.X i) (𝒰.f i)
    · exact hP
    · refine (hE _ _ ⟨fun a => ?_⟩).1
      have hb : 𝒰.f i a ∈ B := Set.mem_iUnion₂.2 ⟨i, hP, a, rfl⟩
      have ha : 𝒰.f i a ∈ A := by rw [h1]; trivial
      exact hdis _ ha hb

theorem res_id' {q : ℕ} {U : Scheme.{0}} (x : Sec (tw q 0) U) : Sec.res (𝟙 U) x = x := by
  simp only [Sec.res, op_id]
  rw [CategoryTheory.Functor.map_id]
  rfl

theorem res_sub' {q : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (a b : Sec (tw q 0) U) :
    Sec.res g (a - b) = Sec.res g a - Sec.res g b := map_sub _ _ _

theorem PtLift_of (hC : PtCov) : PtLift := by
  intro k _ _ X z R hR
  obtain ⟨Sv, hSv, hSs⟩ := hR
  have hpb : Sv.pullback z ∈ Scheme.etaleTopology (S k) := Scheme.etaleTopology.pullback_stable z hSv
  obtain ⟨T, hT, hTs⟩ := hC k (𝟙 (S k)) inferInstance (Sv.pullback z) hpb
  obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hT
  have hne : Nonempty (S k) := inferInstance
  obtain ⟨i, -⟩ := ((Scheme.presieve₀_mem_precoverage_iff _).mp 𝒰.mem₀).1 (Classical.choice hne)
  obtain ⟨U, g', h, hg', -, w, hw⟩ := hTs _ (𝒰.f i) (h𝒰 _ _ (Presieve.ofArrows.mk i))
  refine ⟨U, g' ≫ z, w, hSs _ _ hg', ?_⟩
  rw [Category.comp_id] at hw
  rw [← Category.assoc, hw, Category.id_comp]

theorem tateTwistSection_constantOnPoints_of_connLoc_lift (hT : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc) (hL : ConnLoc) (hP : PtLift) : EtaleTateTwistSectionConstantOnPointsOfConnectedProper := by
  intro l _ k _ _ hl j X p hp s hX y y'
  haveI : NeZero (l ^ j) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hq : ((l ^ j : ℕ) : k) ≠ 0 := by push_cast; exact pow_ne_zero _ hl
  obtain ⟨ζ0⟩ := primK k (l ^ j) hq
  let φ : k →+* Γ(X, ⊤) := (p.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  let v0 := Sec.res y.1 s
  let t := s - Sec.res p v0
  have key : ∀ z : Pt p, Sec.res z.1 t = Sec.res z.1 s - v0 := by
    intro z
    show Sec.res z.1 (s - Sec.res p v0) = _
    rw [res_sub', ← res_comp, z.2, res_id']
  have hne : Nonempty (S k) := inferInstance
  let P : ∀ V : Scheme.{0}, (V ⟶ X) → Prop := fun V g => ∀ (W : Scheme.{0}) (h : W ⟶ V), Nonempty W → Sec.res (h ≫ g) t = 0
  let Q : ∀ V : Scheme.{0}, (V ⟶ X) → Prop := fun V g => ∀ (W : Scheme.{0}) (h : W ⟶ V), Nonempty W → Sec.res (h ≫ g) t ≠ 0
  have hPs : ∀ (V W : Scheme.{0}) (g : V ⟶ X) (h : W ⟶ V), P V g → P W (h ≫ g) := by
    intro V W g h hg W' h' hW'
    rw [← Category.assoc]; exact hg W' (h' ≫ h) hW'
  have hQs : ∀ (V W : Scheme.{0}) (g : V ⟶ X) (h : W ⟶ V), Q V g → Q W (h ≫ g) := by
    intro V W g h hg W' h' hW'
    rw [← Category.assoc]; exact hg W' (h' ≫ h) hW'
  have hE : ∀ (V : Scheme.{0}) (g : V ⟶ X), IsEmpty V → P V g ∧ Q V g := by
    intro V g hV
    exact ⟨fun W h hW => (hV.false (h.base (Classical.choice hW))).elim,
      fun W h hW => (hV.false (h.base (Classical.choice hW))).elim⟩
  have hD : ∀ (V : Scheme.{0}) (g : V ⟶ X), P V g → Q V g → IsEmpty V := by
    intro V g hPg hQg
    by_contra hV
    rw [not_isEmpty_iff] at hV
    exact hQg V (𝟙 V) hV (hPg V (𝟙 V) hV)
  have hPQ : Loc X (fun V g => P V g ∨ Q V g) := by
    obtain ⟨Sv, hSv, hSs⟩ := (hT (l ^ j) 0).1 X (ζ0.map φ) t
    refine ⟨Sv, hSv, fun V g hg => ?_⟩
    obtain ⟨c, hc⟩ := hSs V g hg
    by_cases hqc : l ^ j ∣ c
    · left
      intro W h _
      rw [res_comp, hc, res_nsmul]
      obtain ⟨m, rfl⟩ := hqc
      rw [mul_comm]
      first
        | (rw [mul_nsmul, q_nsmul, nsmul_zero])
        | (rw [mul_nsmul', q_nsmul, nsmul_zero])
        | (rw [mul_nsmul', q_nsmul, smul_zero])
        | (rw [mul_nsmul, q_nsmul, smul_zero])
    · right
      intro W h hW hz
      haveI := hW
      apply hqc
      rw [res_comp, hc, res_nsmul, (hT (l ^ j) 0).2.2] at hz
      exact (hT (l ^ j) 0).2.1 W _ c hz
  have hy0 : Sec.res y.1 t = 0 := by rw [key]; exact sub_self _
  rcases hL hX P Q hPs hQs hE hD hPQ with hLP | hLQ
  · obtain ⟨V, g, w, hg, hw⟩ := hP k y'.1 P hLP
    have h1 := hg (S k) w hne
    rw [hw, key, sub_eq_zero] at h1
    exact h1.symm
  · obtain ⟨V, g, w, hg, hw⟩ := hP k y.1 Q hLQ
    exact absurd (by rw [hw]; exact hy0) (hg (S k) w hne)

theorem tateTwistSection_constantOnPoints_of_twLoc_ptCov (hT : LateralTheory.EtaleFoundations.CongruenceLocalDecomposition.TwLoc) (hC : PtCov) : EtaleTateTwistSectionConstantOnPointsOfConnectedProper :=
  tateTwistSection_constantOnPoints_of_connLoc_lift hT ConnLoc_pf (PtLift_of hC)

end LateralTheory.EtaleTrace
end
end

