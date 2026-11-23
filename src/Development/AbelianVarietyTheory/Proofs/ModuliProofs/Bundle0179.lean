module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.AlWellDefSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0164
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RatioTranslate
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubWeilPerfectOfGeneric
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0118
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushHomBijective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

noncomputable section
namespace GlobalTheory.GenericKTriv

section Pull

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
  {φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}

theorem pushHom_bijective (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Bijective (pushHom h T) := by
  refine ⟨fun x y e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun x => ?_⟩
  exact ⟨Over.homMk (h.1.lift x.left T.hom (Over.w x)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem triv_pull (h : IsGrpPullback A' A f φ) (hL : L.IsLB) (hL' : L'.IsLB) (e : LBIso L' (L.pull φ))
    {T : Over S'} (x : T ⟶ A') (hx : Triv (Out.translDiff A L (pushHom h T x))) :
    Triv (Out.translDiff A' L' x) := by
  obtain ⟨w, hw⟩ := e
  obtain ⟨c, hc⟩ := hx
  let T₀ : Over S := Over.mk (T.hom ≫ f)
  let a : Over.mk ((T ⊗ A').hom ≫ f) ⟶ T₀ := Over.homMk (fst T A').left (by
    show (fst T A').left ≫ T.hom ≫ f = (T ⊗ A').hom ≫ f
    rw [← Category.assoc, Over.w])
  let j : Over.mk ((T ⊗ A').hom ≫ f) ⟶ T₀ ⊗ A := lift a (pushPt h.1.w (snd T A'))
  have k₂ : j.left ≫ (snd T₀ A).left = (snd T A').left ≫ φ := congrArg (fun q => q.left) (lift_snd a (pushPt h.1.w (snd T A')))
  have k₁ : j.left ≫ ((fst T₀ A ≫ pushHom h T x) * snd T₀ A).left = ((fst T A' ≫ x) * snd T A').left ≫ φ := by
    have e : j ≫ ((fst T₀ A ≫ pushHom h T x) * snd T₀ A) = (a ≫ pushHom h T x) * pushPt h.1.w (snd T A') := by
      rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
    have e₁ := h.2 (T ⊗ A') (fst T A' ≫ x) (snd T A') (a ≫ pushHom h T x) (pushPt h.1.w (snd T A'))
      (Category.assoc (fst T A').left x.left φ).symm rfl
    rw [← e] at e₁
    exact e₁
  have h4 : Triv (LB.LinComb L (K := Fin 2) (fun i => j.left ≫
      ![(lift (fst T₀ A ≫ pushHom h T x) (snd T₀ A) ≫ μ[A]).left, (snd T₀ A).left] i) ![1, -1]) :=
    ⟨_, DVR.pullGen_isGen _ _ _ c hc _⟩
  have h3 : (fun i => j.left ≫
      ![(lift (fst T₀ A ≫ pushHom h T x) (snd T₀ A) ≫ μ[A]).left, (snd T₀ A).left] i) =
      fun i => ![(lift (fst T A' ≫ x) (snd T A') ≫ μ[A']).left, (snd T A').left] i ≫ φ := by
    funext i
    fin_cases i
    exacts [k₁, k₂]
  rw [h3] at h4
  obtain ⟨c', hc'⟩ := h4
  exact exists_down ((isGen_iff w).1 hw) hL hL' c' hc'

theorem eq_one_of_factor (h : IsGrpPullback A' A f φ) (hL : L.IsLB) (hL' : L'.IsLB) (e : LBIso L' (L.pull φ))
    (hK : Out.KTriv A' L') {R : Type} [CommRing R] (t : Sp R ⟶ S') {s : Sp R ⟶ S} (hs : s = t ≫ f)
    (x : Over.mk s ⟶ A) (hx : Triv (Out.translDiff A L x)) : x = 1 := by
  subst hs
  obtain ⟨y, rfl⟩ := (pushHom_bijective h (Over.mk t)).2 x
  obtain ⟨c, hc⟩ := triv_pull h hL hL' e y hx
  have : y = 1 := hK R t y fun p => ⟨⊤, trivial, _, LB.isGen_genPull _ c hc _⟩
  rw [this]
  exact map_one (pushHom h (Over.mk t))

theorem card_torsion (h : IsGrpPullback A' A f φ) {Y : Scheme.{0}} (t : Y ⟶ S') {s : Y ⟶ S} (hs : s = t ≫ f)
    (n : ℕ) : Nat.card {x : Over.mk s ⟶ A // x ^ n = 1} = Nat.card {x : Over.mk t ⟶ A' // x ^ n = 1} := by
  subst hs
  let E := MulEquiv.ofBijective _ (pushHom_bijective h (Over.mk t))
  refine (Nat.card_congr (E.toEquiv.subtypeEquiv fun x => ?_)).symm
  show x ^ n = 1 ↔ E x ^ n = 1
  rw [← map_pow, MulEquiv.map_eq_one_iff]

end Pull

theorem field_torsion (hL : Out.Laws) {O : Type} [CommRing O] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) {M : LB A.left} (hM : M.IsLB) (hamp : Out.RelAmple A M) {k : Type} [Field k]
    [IsAlgClosed k] (f : Sp k ⟶ Sp O) {s : Sp k ⟶ Sp O} (hs : s = 𝟙 _ ≫ f) (x : Over.mk s ⟶ A)
    (hx : Triv (Out.translDiff A M x)) : ∃ m : ℕ, 1 ≤ m ∧ x ^ m = 1 := by
  subst hs
  have h := PullbackComparison.isGrpPullback f A
  have hM' := pull_isLB hM (PullbackComparison.pφ f A)
  have e : LBIso (M.pull (PullbackComparison.pφ f A)) (M.pull (PullbackComparison.pφ f A)) := PolBaseChange.lbIso_refl hM'
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback hA h
  have := hA'.comm
  obtain ⟨y, rfl⟩ := (pushHom_bijective h (Out.baseOver (Sp k))).2 x
  have hy := triv_pull h hM hM' e y hx
  obtain ⟨w, hw⟩ := e
  obtain ⟨m, hm, hy⟩ := AmpleStabTorsion.exists_pow_eq_one hL k _ hA' _ hM'
    (relAmple_pull h.1 hM hM' ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) hamp) y hy
  refine ⟨m, hm, ?_⟩
  exact (map_pow (pushHom h _) y m).symm.trans ((congrArg (pushHom h _) hy).trans (map_one _))

theorem exists_cover {O K R : Type} [CommRing O] [IsDomain O] [Field K] [CommRing R] (i : O →+* K)
    (hi : Function.Injective i) (j : O →+* R) (hj : ∀ a : O, a ≠ 0 → IsUnit (j a)) :
    ∃ (R' : Type) (_ : CommRing R') (a : R →+* R') (b : K →+* R'), a.FaithfullyFlat ∧ a.comp j = b.comp i := by
  let F := FractionRing O
  let iF : F →+* K := IsFractionRing.lift hi
  let jF : F →+* R := IsLocalization.lift (M := nonZeroDivisors O) (g := j)
    fun y => hj y (nonZeroDivisors.ne_zero y.2)
  letI : Algebra F K := iF.toAlgebra
  letI : Algebra F R := jF.toAlgebra
  refine ⟨R ⊗[F] K, inferInstance, algebraMap R (R ⊗[F] K),
    (Algebra.TensorProduct.includeRight : K →ₐ[F] R ⊗[F] K).toRingHom, ?_, ?_⟩
  · rw [RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  · ext o
    have h₁ : j o = algebraMap F R (algebraMap O F o) := (IsLocalization.lift_eq _ o).symm
    have h₂ : i o = algebraMap F K (algebraMap O F o) := (IsFractionRing.lift_algebraMap hi o).symm
    show algebraMap R (R ⊗[F] K) (j o) = (Algebra.TensorProduct.includeRight : K →ₐ[F] R ⊗[F] K) (i o)
    rw [h₁, h₂, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

theorem eq_one_of_generic {O K R : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [CommRing R]
    [Algebra O R] (hi : Function.Injective (algebraMap O K)) (hj : ∀ a : O, a ≠ 0 → IsUnit (algebraMap O R a))
    {A : Over (Sp O)} [GrpObj A] {M : LB A.left} (hM : M.IsLB) (P : Out.PolAV (Sp K)) {φ : P.A.left ⟶ A.left}
    (h : IsGrpPullback P.A A (spMap (algebraMap O K)) φ) (e : LBIso P.L (M.pull φ)) (x : specO O R ⟶ A)
    (hx : Triv (Out.translDiff A M x)) : x = 1 := by
  obtain ⟨R', _, a, b, ha, hab⟩ := exists_cover _ hi _ hj
  let q : Over.mk (spMap a ≫ (specO O R).hom) ⟶ specO O R := Over.homMk (spMap a) rfl
  have hs : spMap a ≫ (specO O R).hom = spMap b ≫ spMap (algebraMap O K) := by
    show spMap a ≫ spMap (algebraMap O R) = _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hab]
  have h₁ : q ≫ x = 1 := eq_one_of_factor h hM P.isLB e P.ktriv (spMap b) hs _
    (ArtinReduction.exists_isGen_translDiff_comp A M q x hx)
  obtain ⟨_, _⟩ := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom a)).2 ha
  have : Epi (spMap a) := Flat.epi_of_flat_of_surjective _
  have h₂ : q ≫ x = q ≫ 1 := by rw [h₁, MonObj.comp_one]
  exact Over.OverMorphism.ext ((cancel_epi (spMap a)).1 (congrArg (fun z => z.left) h₂))

theorem tangent_pow {O k : Type} [CommRing O] [CommRing k] [Algebra O k] (A : Over (Sp O)) [GrpObj A] {p : ℕ}
    (hp : (p : k) = 0) (x : specO O (DualNumber k) ⟶ A) (hx : ptMap (TrivSqZeroExt.fstHom O k k) ≫ x = 1) :
    x ^ p = 1 := by
  obtain ⟨w, hw, -⟩ := (TangentPow.pow_eq_scale_and_existsUnique_torsion O A k p x hx).2 hp
  have hm : ∀ n : ℕ, mulN A n = 𝟙 A ^ n := fun n => by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, ← ih]; rfl
  have hι : torsion.ι A p ≫ mulN A p = 1 := by
    refine pullback.condition.trans ?_
    rw [toUnit_unique (pullback.snd _ _) (toUnit _)]
    rfl
  rw [hm, MonObj.comp_pow, Category.comp_id] at hι
  rw [← hw, ← MonObj.comp_pow, hι, MonObj.comp_one]

theorem kTriv_of_generic : Out.Laws → ∀ (O K : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field K] [IsAlgClosed K] [CharZero K] [Algebra O K], Function.Injective (algebraMap O K) → (∀ q : Ideal O, q.IsPrime → q ≠ ⊥ → ∃ p : ℕ, p.Prime ∧ (p : O) ∈ q) → ∀ (A : Over (Sp O)) [GrpObj A], IsAbelianScheme A → ∀ (g : ℕ), SmoothOfRelativeDimension g A.hom → ∀ M : LB A.left, M.IsLB → Out.Rigidified A M → Out.RelAmple A M → ∀ (P : Out.PolAV (Sp K)) (φ : P.A.left ⟶ A.left), IsGrpPullback P.A A (spMap (algebraMap O K)) φ → LBIso P.L (M.pull φ) → Out.KTriv A M := by
  intro hL O K _ _ _ _ _ _ _ hi hq A _ hA g hg M hM hrig hamp P φ h e
  have := hA.comm
  obtain ⟨d, -, m, s, hs⟩ := (Unif.relAmple_iff_veryAmpleBy O A M hM).1 hamp
  have hproj : IsProjBy A.hom := ⟨_, isLB_pw hM d, m, s, hs⟩
  obtain ⟨L, rfl, ⟨c⟩⟩ := Moduli.cubicalStr_of_triv_theta hL _ A hA M hM hrig (_root_.GlobalTheory.AbLaw.CubeAffine.triv_theta_of_isProjBy hL O A hA hproj M hM)
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} g
  have hgP : P.g = g := H1.dim_unique P.A.hom P.smoothDim
    (MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) h.1 hg)
    ((η[P.A]).left (Nonempty.some (inferInstanceAs (Nonempty (Sp K)))))
  have tors : ∀ (n : ℕ), 1 ≤ n → ∀ (T : Over (Sp O)) (x : T ⟶ A), x ^ n = 1 → Triv (Out.translDiff A L.L x) →
      x = 1 := by
    intro n hn T x hxn hx
    have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    obtain ⟨f₁, f₂, f₃⟩ := _root_.GlobalTheory.MulAmple.finite_flat_surjective_pow hL O A hA L.L hM hamp n hn
    refine _root_.GlobalTheory.cubWeil_perfect_of_generic O K hi A g hg L c n hn f₁ f₂ ?_ ?_ T x hxn fun T' ρ y hy => ?_
    · rw [← hgP, ← (hL.mulN _ P n hn).2.2.2.2 K (𝟙 _) hnK]
      exact card_torsion h (𝟙 _) (Category.id_comp _).symm n
    · intro y hy hp
      exact eq_one_of_factor h hM P.isLB e P.ktriv (𝟙 _) (Category.id_comp _).symm y
        (CubNondeg.main hL _ A hA L c K _ n hnK f₁ f₂ f₃ y hy hp)
    · refine UU.KerPair.cubWeil_of_gen hL.globalFns _ A hA L c n T' _ y ?_ hy
        (ArtinReduction.exists_isGen_translDiff_comp A L.L ρ x hx)
      rw [← MonObj.comp_pow, hxn, MonObj.comp_one]
  refine _root_.GlobalTheory.KCriterion.kTriv_of_points_of_tangents hL O A hA hproj L.L hM fun k _ _ _ => ⟨fun x hx => ?_, fun x hx₀ hx => ?_⟩
  · obtain ⟨n, hn, hxn⟩ := field_torsion hL A hA hM hamp _ (Category.id_comp _).symm x hx
    exact tors n hn _ x hxn hx
  · by_cases hk : RingHom.ker (algebraMap O k) = ⊥
    · refine eq_one_of_generic hi (fun a ha => ?_) hM P h e x hx
      have ha' : algebraMap O k a ≠ 0 := fun h0 => ha (by
        have : a ∈ RingHom.ker (algebraMap O k) := h0
        rwa [hk] at this)
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
      exact (congrArg IsUnit ((TrivSqZeroExt.fstHom O k k).commutes a)).mpr ha'.isUnit
    · obtain ⟨p, hp, hpq⟩ := hq _ (RingHom.ker_isPrime _) hk
      have hp0 : (p : k) = 0 := by rw [← map_natCast (algebraMap O k)]; exact hpq
      exact tors p hp.one_le _ x (tangent_pow A hp0 x hx₀) hx

end GlobalTheory.GenericKTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfGenerization
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.CharZeroPts

theorem exists_generization {o : Type} [CommRing o] [IsDomain o] [CharZero o] {S : Scheme.{0}} (s : S ⟶ Sp o) [Flat s]
    (p : S) : ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K) (x : Sp K ⟶ S) (β : o →+* K),
      x ≫ s = spMap β ∧ ∀ u, x u ⤳ p := by
  let ξ : Sp o := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum o)
  have hξ : ξ ⤳ s p := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
  obtain ⟨q, hq, hq'⟩ := Flat.generalizingMap s hξ
  obtain ⟨K, _, _, x, hx⟩ := FinEt.exists_algClosed_point S q
  have hx' : ∀ u, x u = q := fun u => by
    have : x u ∈ Set.range x := ⟨u, rfl⟩
    rwa [hx] at this
  let β : o →+* K := (Spec.preimage (x ≫ s)).hom
  have hβ : x ≫ s = spMap β := (Spec.map_preimage (x ≫ s)).symm
  have hinj : Function.Injective β := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have e : spMap β (default : PrimeSpectrum K) = ξ := by
      rw [← hβ]
      exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg s (hx' _)).trans hq')
    have e' : a ∈ (spMap β (default : PrimeSpectrum K)).asIdeal := by
      show β a ∈ (default : PrimeSpectrum K).asIdeal
      rw [ha]; exact zero_mem _
    rw [e] at e'
    exact e'
  exact ⟨K, inferInstance, inferInstance, charZero_of_injective_ringHom hinj, x, β, hβ, fun u => (hx' u).symm ▸ hq⟩

variable {S : Scheme.{0}}

abbrev toB {T : Scheme.{0}} (x : T ⟶ S) : Over.mk x ⟶ Out.baseOver S := Over.homMk x (by simp)

theorem smoothOfRelativeDimension_of_generization {X : Scheme.{0}} (f : X ⟶ S) [Smooth f] [GeometricallyConnected f]
    (g : ℕ) (h : ∀ y : X, ∃ (K : Type) (_ : Field K) (z : Sp K ⟶ X), (∀ u, z u ⤳ y) ∧
      ∀ m, SmoothOfRelativeDimension m (pullback.snd f (z ≫ f)) → m = g) : SmoothOfRelativeDimension g f := by
  choose n W hW hd using H1.exists_dim f
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_
  obtain ⟨k, _, z, hz, hg⟩ := h y
  have : ConnectedSpace ↥(pullback f (z ≫ f)) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) (z ≫ f) _ _ (IsPullback.of_hasPullback _ _)
  let z' : Sp k ⟶ pullback f (z ≫ f) := pullback.lift z (𝟙 _) (Category.id_comp _).symm
  obtain ⟨m, hm⟩ := exists_dim_of_preconnected (pullback.snd f (z ≫ f)) (z' (default : PrimeSpectrum k))
  have e₁ : n y = m := H1.dim_base (IsPullback.of_hasPullback _ _) (hd y) hm (z' (default : PrimeSpectrum k)) (by
    have e : z' ≫ pullback.fst f (z ≫ f) = z := pullback.lift_fst _ _ _
    have e' := congrArg (fun q : Sp k ⟶ X => q (default : PrimeSpectrum k)) e
    exact (congrArg (fun u => u ∈ W y) e').mpr ((hz _).mem_open (W y).isOpen (hW y)))
  rw [← hg m hm, ← e₁]
  exact hd y

theorem weilIs_of_generization (hL : Out.Laws) (P : Out.PolAV S) (n : ℕ) (x y : Out.baseOver S ⟶ P.A) (c : Γ(S, ⊤)ˣ)
    (hn : 0 < n) (hu : IsUnit (n : Γ(S, ⊤))) (hx : x ^ n = 1) (hy : y ^ n = 1) (hc : c ^ n = 1)
    (h : ∀ p : S, ∃ (K : Type) (_ : Field K) (z : Sp K ⟶ S), (∀ u, z u ⤳ p) ∧
      Out.WeilIs P.A P.L n (toB z ≫ x) (toB z ≫ y) (Units.map z.appTop.hom.toMonoidHom c)) :
    Out.WeilIs P.A P.L n x y c := by
  obtain ⟨U, hU, H⟩ := exists_clopen_weilIs_iff hL S P n (Out.baseOver S) x y c hn hu hx hy hc
  have := (H _ (𝟙 _)).2 (by
    rintro _ ⟨p, rfl⟩
    obtain ⟨K, _, z, hz, hw⟩ := h p
    exact (hz (default : PrimeSpectrum K)).mem_closed hU ((H _ (toB z)).1 hw ⟨_, rfl⟩))
  rw [Category.id_comp, Category.id_comp] at this
  convert this
  ext
  simp

theorem torsion_basis_of_generization (A : Over S) [GrpObj A] (k r : ℕ) (pt : Fin r → (Out.baseOver S ⟶ A))
    (hA : IsAbelianScheme A) (hk : 0 < k) (hu : IsUnit (k : Γ(S, ⊤))) (hpt : ∀ i, pt i ^ k = 1)
    (h : ∀ p : S, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (z : Sp K ⟶ S), (∀ u, z u ⤳ p) ∧
      ∀ y : Over.mk z ⟶ A, y ^ k = 1 →
        ∃! c : Fin r → ZMod k, Out.linComb (fun i => toB z ≫ pt i) (fun i => (c i).val) = y)
    (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (y : Over.mk x ⟶ A) (hy : y ^ k = 1) :
    ∃! c : Fin r → ZMod k, Out.linComb (fun i => toB x ≫ pt i) (fun i => (c i).val) = y := by
  let Sg : Set S := {p | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (z : Sp K ⟶ S),
    p ∈ Set.range z ∧ ∀ y : Over.mk z ⟶ A, y ^ k = 1 →
      ∃! c : Fin r → ZMod k, Out.linComb (fun i => toB z ≫ pt i) (fun i => (c i).val) = y}
  refine torsion_basis_of_dense S A k r pt Sg hA hk hu hpt ?_ (fun p hp => hp) K x y hy
  intro p
  obtain ⟨K, _, _, z, hz, H⟩ := h p
  exact (hz (default : PrimeSpectrum K)).mem_closed isClosed_closure
    (subset_closure ⟨K, inferInstance, inferInstance, z, ⟨_, rfl⟩, H⟩)

end GlobalTheory.CharZeroPts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaClosureOpenFamilyQprojFlatReducedExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem isQProjOver_opens_of_noetherian {o : Type} [CommRing o] [IsNoetherianRing o] {X : Scheme.{0}} {s : X ⟶ Sp o}
    (h : IsQProjOver s) (U : X.Opens) : IsQProjOver (U.ι ≫ s) := by
  obtain ⟨N, i, hi, hq, rfl⟩ := h
  have : IsProper (PSpace.str o N) := isProper_str o N
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (i ≫ PSpace.str o N)
  exact ⟨N, U.ι ≫ i, inferInstance, inferInstance, by simp⟩

theorem isIso_of_closedPoint_mem_range {R : Type} [CommRing R] [IsLocalRing R] {Z : Scheme.{0}} (z : Z ⟶ Sp R)
    [IsOpenImmersion z] (h : (IsLocalRing.closedPoint R : Sp R) ∈ Set.range z) : IsIso z := by
  have hs : Function.Surjective z := by
    intro p
    exact (IsLocalRing.specializes_closedPoint (R := R) p).mem_open z.isOpenEmbedding.isOpen_range h
  have : Epi z.base := (TopCat.epi_iff_surjective _).2 hs
  exact IsOpenImmersion.isIso z

theorem TObj.exists_hasTh_of_isLocalRing (h1 : Out.Laws) (h2 : Out.Laws2) {o : Type} [CommRing o] {g N' : ℕ} {J : Type}
    {b : TBase o (N' ^ 2)} (hN : Odd N') {R : Type} [CommRing R] [IsLocalRing R] {s' : Sp R ⟶ Sp o}
    (t : TObj g (N' ^ 2) J b s') : ∃ v, t.HasTh (𝟙 (Sp R)) v := by
  obtain ⟨R', _, z, v, hz, hp, hv⟩ := _root_.GlobalTheory.ThetaLocal.exists_hasTh h1 h2 o g N' J b _ s' t hN (IsLocalRing.closedPoint R)
  have := isIso_of_closedPoint_mem_range z hp
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (inv z)
  have := _root_.GlobalTheory.hasTh_baseChange h2 o g N' J b _ s' t R' R φ.hom z v hv
  have e : spMap φ.hom ≫ z = 𝟙 (Sp R) := by
    change Spec.map φ ≫ z = _
    rw [hφ, IsIso.inv_hom_id]
  rw [e] at this
  exact ⟨_, this⟩

theorem WFam.qproj_flat_reduced_ext : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g n N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (em : o →+* ℂ) (C : TObj g (N' ^ 2) J b (spMap em) → Prop) Mat κ (F : WFam n em C Mat κ), Odd N' → (IsQProjOver (F.U.ι ≫ F.Y.s) ∨ ¬ IsNoetherianRing o) ∧ Flat (F.U.ι ≫ F.Y.s) ∧ IsReduced F.U.toScheme ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (x y : Sp R ⟶ F.U.toScheme) (s' : Sp R ⟶ Sp o) (t : TObj g (N' ^ 2) J b s'), x ≫ F.U.ι ≫ F.Y.s = y ≫ F.U.ι ≫ F.Y.s → TMap t F.univ x → TMap t F.univ y → x = y := by
  intro h1 h2 o _ g n N' J b em C Mat κ F hN
  have := F.Y.flat
  have := F.Y.reduced
  refine ⟨?_, inferInstance, isReduced_of_isOpenImmersion F.U.ι, ?_⟩
  · by_cases hn : IsNoetherianRing o
    · exact Or.inl (isQProjOver_opens_of_noetherian F.Y.qproj F.U)
    · exact Or.inr hn
  · intro R _ _ x y s' t hxy hx hy
    obtain ⟨v, hv⟩ := TObj.exists_hasTh_of_isLocalRing h1 h2 hN t
    have vx := (_root_.GlobalTheory.hasTh_iff_of_tmap o g N' J b _ _ F.univ _ s' t x R (𝟙 _) v hx).1 hv
    have vy := (_root_.GlobalTheory.hasTh_iff_of_tmap o g N' J b _ _ F.univ _ s' t y R (𝟙 _) v hy).1 hv
    rw [Category.id_comp] at vx vy
    have cx := (F.th R x v).1 vx
    have cy := (F.th R y v).1 vy
    obtain ⟨β, hβ⟩ := Spec.map_surjective (x ≫ F.U.ι ≫ F.Y.s)
    have bx : (x ≫ F.U.ι) ≫ F.Y.s = spMap β.hom := by rw [Category.assoc, ← hβ]; rfl
    have by' : (y ≫ F.U.ι) ≫ F.Y.s = spMap β.hom := by rw [Category.assoc, ← hxy, ← hβ]; rfl
    have hin := F.Y.loc R β.hom _ v bx cx
    have := (F.Y.pts R β.hom v hin).unique ⟨bx, cx⟩ ⟨by', cy⟩
    exact (cancel_mono F.U.ι).1 this

end GlobalTheory.ZM
end

