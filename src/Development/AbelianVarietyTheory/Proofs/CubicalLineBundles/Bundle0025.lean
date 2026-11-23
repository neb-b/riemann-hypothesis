module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGenOfGenericFibre
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulOriginSec
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsStandardSmoothOfRelativeDimensionAwayJacobian
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGenOfFieldExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.FieldTriv

theorem exists_gen_of_isPullback {k k' : Type} [Field k] [Field k'] (β : k →+* k') {X X' : Scheme.{0}}
    (f : X ⟶ Sp k) [IsProper f] [GeometricallyIntegral f] (π : X' ⟶ X) (p : X' ⟶ Sp k')
    (H : IsPullback π p f (spMap β)) {N : LB X} (hN : N.IsLB) (t : (N.pull π).Gen) (ht : t.IsGen) :
    ∃ u : N.Gen, u.IsGen := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  have : IsIntegral X' := GeometricallyIntegral.geometrically_isIntegral _ _ _ H
  have : IsIso p.appTop := ProperFunctions.isIso_appTop_baseChange_of_field H
  have hflat : β.Flat := by
    let _ := β.toAlgebra
    exact inferInstanceAs (Module.Flat k k')
  have lift : ∀ x : X, ∃ y, π y = x := fun x => by
    obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback H x (⊥ : PrimeSpectrum k')
      (Subsingleton.elim (α := PrimeSpectrum k) _ _)
    exact ⟨y, hy⟩
  obtain ⟨σ, hσ⟩ := GenericTriv.exists_sec_isUnit β hflat f π p H
    (ConcreteCategory.bijective_of_isIso p.appTop).2 hN t ht
  have hu : ∀ i, IsUnit (σ.f i) := fun i => X.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => by
    obtain ⟨y, rfl⟩ := lift x
    have := hσ y i hx
    rw [gs_stalkMap π y _ hx, isUnit_map_iff] at this
    exact (congrArg IsUnit (gs_eq (𝟙 X) (π y) (N.U i) hx _)).mp this
  exact ⟨⟨fun i => (hu i).unit⟩, fun i i' => Units.ext (σ.compat i i')⟩

theorem exists_gen_of_field_extension : ∀ (k k' : Type) [Field k] [Field k'] (β : k →+* k') (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A → ∀ (X' : Scheme.{0}) (π : X' ⟶ A.left) (p : X' ⟶ Sp k'), IsPullback π p A.hom (spMap β) → ∀ N : LB A.left, N.IsLB → (∃ t : LB.Gen (N.pull π), t.IsGen) → ∃ t : LB.Gen N, t.IsGen := by
  intro k k' _ _ β A _ hA X' π p H N hN ⟨t, ht⟩
  have := hA.proper
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth hA.geomConnected
  exact exists_gen_of_isPullback β A.hom π p H hN t ht

end GlobalTheory.FieldTriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGrpObjPolarised
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

namespace GlobalTheory.WeierstrassCurve

theorem polarised_of_grpObj (R : Type) [CommRing R] (W : _root_.WeierstrassCurve R)
    (hΔ : IsUnit W.Δ) [GrpObj (schemeOver W)] (hc : IsCommMonObj (schemeOver W))
    (hη : η[schemeOver W].left = zero W) :
    IsAbelianScheme (schemeOver W) ∧ SmoothOfRelativeDimension 1 (schemeOver W).hom ∧
      (originLB W).IsLB ∧ Out.Rigidified (schemeOver W) (originLB W) ∧
      Out.Sym (schemeOver W) (originLB W) ∧ Out.RelAmple (schemeOver W) (originLB W) ∧
      Out.KTriv (schemeOver W) (originLB W) := by
  obtain ⟨hrig, hsym, hamp, hk⟩ := GlobalTheory.T.originLineBundle_polarisation R W hc hη
  exact ⟨isAbelianScheme_schemeOver R W hΔ hc, smoothOfRelativeDimension_toSpec_of_isUnit W hΔ,
    originLB_isLB W, hrig, hsym, hamp, hk⟩

theorem exists_grpObj_polarised (R : Type) [CommRing R] (W : _root_.WeierstrassCurve R)
    (hΔ : IsUnit W.Δ) :
    ∃ _ : GrpObj (schemeOver W), IsCommMonObj (schemeOver W) ∧ η[schemeOver W].left = zero W ∧
      (∀ (A : Type) [CommRing A] (ρ : R →+* A) (P Q T : Fin 3 → A)
        (hP : IsUnimodularSol (W.map ρ) P) (hQ : IsUnimodularSol (W.map ρ) Q)
        (hT : IsUnimodularSol (W.map ρ) T),
        (Proportional T ((W.map ρ).toProjective.addXYZ P Q) ∧
          Proportional T (diagXYZ (W.map ρ).toProjective P Q)) →
        ∀ x y : Over.mk (spMap ρ) ⟶ schemeOver W, x.left = ptHom W ρ P hP →
          y.left = ptHom W ρ Q hQ → (lift x y ≫ μ[schemeOver W]).left = ptHom W ρ T hT) ∧
      (∀ (A : Type) [CommRing A] (ρ : R →+* A) (P : Fin 3 → A)
        (hP : IsUnimodularSol (W.map ρ) P),
        ∃ hN : IsUnimodularSol (W.map ρ) ((W.map ρ).toProjective.neg P),
          ptHom W ρ P hP ≫ (GrpObj.inv : schemeOver W ⟶ schemeOver W).left = ptHom W ρ _ hN) ∧
      (IsAbelianScheme (schemeOver W) ∧ SmoothOfRelativeDimension 1 (schemeOver W).hom ∧
        (originLB W).IsLB ∧ Out.Rigidified (schemeOver W) (originLB W) ∧
        Out.Sym (schemeOver W) (originLB W) ∧ Out.RelAmple (schemeOver W) (originLB W) ∧
        Out.KTriv (schemeOver W) (originLB W)) ∧
      ∃ v : epsR R ⟶ schemeOver W,
        (∃ h : IsUnimodularSol (W.map (algebraMap R (DualNumber R))) ![DualNumber.eps, -1, 0],
          v.left = ptHom W (algebraMap R (DualNumber R)) ![DualNumber.eps, -1, 0] h) ∧
        IsLieBasis ![v] := by
  obtain ⟨inst, hc, hη, hadd, hneg⟩ := _root_.GlobalTheory.exists_grpObj_weierstrass R W hΔ
  exact ⟨inst, hc, hη, hadd, hneg, polarised_of_grpObj R W hΔ hc hη,
    GlobalTheory.WeierstrassLie.isLieBasis_eps R W hη⟩

theorem exists_polAV : ∀ (R : Type) [CommRing R] (W : _root_.WeierstrassCurve R), IsUnit W.Δ →
    ∃ (P : Out.PolAV (Sp R)) (ψ : P.A.left ⟶ scheme W) (v : epsR R ⟶ P.A), P.g = 1 ∧ IsIso ψ ∧
      ψ ≫ toSpec W = P.A.hom ∧ eSec P.A ≫ ψ = zero W ∧
      (∃ h : IsUnimodularSol (W.map (algebraMap R (DualNumber R))) ![DualNumber.eps, -1, 0],
        v.left ≫ ψ = ptHom W (algebraMap R (DualNumber R)) ![DualNumber.eps, -1, 0] h) ∧
      IsLieBasis ![v] := by
  intro R _ W hΔ
  obtain ⟨inst, hc, hη, -, -, ⟨hab, hsm, hlb, hrig, hsym, hamp, hk⟩, v, ⟨h, hv⟩, hbasis⟩ :=
    exists_grpObj_polarised R W hΔ
  let P : Out.PolAV (Sp R) :=
    { A := schemeOver W
      grp := inst
      isAb := hab
      g := 1
      smoothDim := hsm
      L := originLB W
      isLB := hlb
      rigid := hrig
      sym := hsym
      ample := hamp
      ktriv := hk }
  refine ⟨P, 𝟙 _, v, rfl, inferInstance, ?_, ?_, ⟨h, ?_⟩, hbasis⟩
  · rw [Category.id_comp]
    rfl
  · rw [Category.comp_id]
    exact hη
  · rw [Category.comp_id]
    exact hv

end GlobalTheory.WeierstrassCurve
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsOActExtendDedekind
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem exists_oAct_extend_dedekind : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (O : Type) [CommRing O] (G : Over (Sp R)) [GrpObj G] (G₀ : Over (Sp K)) [GrpObj G₀] (φ : G₀.left ⟶ G.left), IsAbelianScheme G → IsGrpPullback G₀ G (spMap (algebraMap R K)) φ → ∀ a₀ : OAct O G₀, ∃ a : OAct O G, ∀ c, (a₀.act c).left ≫ φ = φ ≫ (a.act c).left := by
  intro H R K _ _ _ _ _ O _ G _ G₀ _ φ hG hφ a₀
  have key := fun c => _root_.GlobalTheory.abelianScheme_hom_extends_dedekind_of_isGrpPullback H R K G G G₀ G₀ φ φ hG hG hφ hφ (a₀.act c) (a₀.hom c)
  choose F hF hc hu using key
  refine ⟨⟨F, hF, ?_, ?_, ?_⟩, hc⟩
  · refine (hu 1 (𝟙 G) ?_).symm
    rw [a₀.one]
    simp
  · intro a b
    refine (hu (a * b) (F a ≫ F b) ?_).symm
    rw [a₀.mul, Over.comp_left, Over.comp_left, Category.assoc, hc b, ← Category.assoc, hc a, Category.assoc]
  · intro a b
    refine (hu (a + b) (F a * F b) ?_).symm
    let ψ : Over.mk (G₀.hom ≫ spMap (algebraMap R K)) ⟶ G := Over.homMk φ hφ.1.w
    have h := hφ.2 G₀ (a₀.act a) (a₀.act b) (ψ ≫ F a) (ψ ≫ F b) (hc a).symm (hc b).symm
    rw [a₀.add, ← h, ← MonObj.comp_mul]
    rfl

end GlobalTheory.CM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem PAT.exists_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (S S' : Scheme.{0}) (f : S' ⟶ S) (T : PAT H S), ∃ (T' : PAT H S') (_ : SABMap T'.t T.t f), T'.g = T.g := by
  intro E _ _ _ H S S' f T
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull f T.t
  obtain ⟨⟨T', ht, hg⟩, -⟩ := _root_.GlobalTheory.CM.PAT.exists_of_sabMap E H S S' f T _ m
  exact ⟨T', ht ▸ m, hg⟩

end GlobalTheory.CM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IntegersOfCmFieldConjStructure
section
open NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CM

open GlobalTheory.HostModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


omit [IsCMField E] in
theorem int_dvd_of_mul_eq_ringOfIntegers {N m : ℤ} {z : 𝓞 E} (h : (N : 𝓞 E) * z = m) : N ∣ m := by
  have h1 : algebraMap ℤ (𝓞 E) N ∣ algebraMap ℤ (𝓞 E) m := ⟨z, by simpa using h.symm⟩
  have h2 := map_dvd (Algebra.norm ℤ) h1
  rw [Algebra.norm_algebraMap, Algebra.norm_algebraMap] at h2
  exact (Int.pow_dvd_pow_iff Module.finrank_pos.ne').1 h2

theorem int_dvd_of_sq_dvd_squarefree_mul_sq {d N v : ℤ} (hd : Squarefree d) (hN : N ≠ 0)
    (h : N ^ 2 ∣ d * v ^ 2) : N ∣ v := by
  obtain ⟨N', v', h1, h2, h3⟩ := extract_gcd N v
  generalize gcd N v = g at h1 h2
  subst h1 h2
  have hg : g ≠ 0 := left_ne_zero_of_mul hN
  have h4 : N' ^ 2 ∣ d * v' ^ 2 := by
    rw [mul_pow, mul_pow, mul_left_comm] at h
    exact (mul_dvd_mul_iff_left (pow_ne_zero 2 hg)).1 h
  have hc : IsCoprime N' v' := (gcd_isUnit_iff _ _).1 h3
  have h5 : N' * N' ∣ d := by
    rw [← sq]
    exact (hc.pow (m := 2) (n := 2)).dvd_of_dvd_mul_right h4
  exact mul_dvd_mul_left g (hd _ h5).dvd

theorem cm_generator_sq_quadratic_eq (H : Host E) : H.w0 ^ 2 + (((1 + H.d) / 4 : ℕ) : 𝓞 E) = H.w0 := by
  have h4 : 4 * ((1 + H.d) / 4) = 1 + H.d := by have := H.d_mod; omega
  have h5 : (4 : 𝓞 E) * (((1 + H.d) / 4 : ℕ) : 𝓞 E) = 1 + H.d := by exact_mod_cast congrArg (Nat.cast : ℕ → 𝓞 E) h4
  have h := H.rt_sq
  rw [rt_eq] at h
  apply mul_left_cancel₀ (show (4 : 𝓞 E) ≠ 0 by norm_num)
  linear_combination h + h5

theorem exists_coord (H : Host E) {a : 𝓞 E} (ha : a ∈ OK H) : ∃ u v : ℤ, a = u + v * H.w0 := by
  first
  | exact @_root_.GlobalTheory.CMGeneratorSquare.main
  | exact _root_.GlobalTheory.CMGeneratorSquare.main
  | (apply _root_.GlobalTheory.CMGeneratorSquare.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CMGeneratorSquare.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CMGeneratorSquare.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CMGeneratorSquare.main ..)

theorem coord_eq_zero (H : Host E) {u v : ℤ} (h : (u : 𝓞 E) + v * H.w0 = 0) : u = 0 ∧ v = 0 := by
  have h1 := congrArg H.bar h
  rw [map_add (f := _), map_mul, map_intCast, map_intCast, cmHost_bar_halfIntegerGenerator, map_zero] at h1
  have h2 : (v : 𝓞 E) * H.rt = 0 := by rw [rt_eq]; linear_combination h - h1
  have h3 : v = 0 := by exact_mod_cast (mul_eq_zero.1 h2).resolve_right (rt_ne_zero H)
  subst h3
  exact ⟨by simpa using h, rfl⟩

theorem coord_mem (H : Host E) (u v : ℤ) : (u : 𝓞 E) + v * H.w0 ∈ OK H :=
  add_mem (intCast_mem _ u) (mul_mem (intCast_mem _ v) (Algebra.self_mem_adjoin_singleton ℤ _))

theorem coord_mul_bar (H : Host E) (u v : ℤ) : ((u : 𝓞 E) + v * H.w0) * H.bar (u + v * H.w0) =
    ((u ^ 2 + u * v + ((1 + H.d) / 4 : ℕ) * v ^ 2 : ℤ) : 𝓞 E) := by
  have h := cm_generator_sq_quadratic_eq H
  generalize (1 + H.d) / 4 = k at h
  rw [map_add (f := _), map_mul, map_intCast, map_intCast, cmHost_bar_halfIntegerGenerator]
  push_cast
  linear_combination (-v ^ 2 : 𝓞 E) * h

theorem mem_OK_of_int_mul_mem (H : Host E) {N : ℤ} (hN : N ≠ 0) {y : 𝓞 E} (hy : (N : 𝓞 E) * y ∈ OK H) :
    y ∈ OK H := by
  obtain ⟨u, v, h⟩ := exists_coord H hy
  have hb := congrArg H.bar h
  have hn := coord_mul_bar H u v
  rw [← h, map_mul, map_intCast] at hn
  rw [map_mul, map_add (f := _), map_mul, map_intCast, map_intCast, map_intCast, cmHost_bar_halfIntegerGenerator] at hb
  have h1 : N ∣ 2 * u + v :=
    int_dvd_of_mul_eq_ringOfIntegers (z := y + H.bar y) (by push_cast; linear_combination h + hb)
  have h2 : N ^ 2 ∣ u ^ 2 + u * v + ((1 + H.d) / 4 : ℕ) * v ^ 2 :=
    int_dvd_of_mul_eq_ringOfIntegers (z := y * H.bar y) (by rw [← hn]; push_cast; ring)
  have h4 : (4 : ℤ) * ((1 + H.d) / 4 : ℕ) = 1 + H.d := by have := H.d_mod; omega
  have h3 : N ^ 2 ∣ H.d * v ^ 2 := by
    have := dvd_sub (h2.mul_left 4) (pow_dvd_pow_of_dvd h1 2)
    rwa [show 4 * (u ^ 2 + u * v + ((1 + H.d) / 4 : ℕ) * v ^ 2) - (2 * u + v) ^ 2 = H.d * v ^ 2 by
      linear_combination v ^ 2 * h4] at this
  obtain ⟨v', rfl⟩ := int_dvd_of_sq_dvd_squarefree_mul_sq
    (Int.squarefree_natCast.2 H.d_prime.squarefree) hN h3
  obtain ⟨u', rfl⟩ : N ∣ u :=
    int_dvd_of_mul_eq_ringOfIntegers (z := y - (v' : 𝓞 E) * H.w0) (by push_cast at h; linear_combination h)
  have : y = u' + v' * H.w0 :=
    mul_left_cancel₀ (show (N : 𝓞 E) ≠ 0 by exact_mod_cast hN) (by push_cast at h; linear_combination h)
  rw [this]
  exact coord_mem H u' v'

theorem finite_int_OK (H : Host E) : Module.Finite ℤ (OK H) :=
  Module.Finite.of_injective (OK H).val.toLinearMap Subtype.val_injective

theorem isIntegrallyClosed_OK (H : Host E) : IsIntegrallyClosed (OK H) := by
  have := finite_int_OK H
  rw [isIntegrallyClosed_iff (FractionRing (OK H))]
  intro x hx
  have hinj : Function.Injective (algebraMap (OK H) E) :=
    RingOfIntegers.coe_injective.comp Subtype.val_injective
  let φ : FractionRing (OK H) →ₐ[OK H] E :=
    IsFractionRing.liftAlgHom (g := Algebra.ofId (OK H) E) hinj
  have hy : IsIntegral ℤ (φ x) := isIntegral_trans _ (hx.map φ)
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OK H) x
  obtain ⟨n, hn, c, hc⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) b).exists_nonzero_dvd hb
  have hb' : algebraMap (OK H) E b ≠ 0 := (map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hb)
  have hm : (⟨_, hy⟩ : 𝓞 E) ∈ OK H := by
    refine mem_OK_of_int_mul_mem H hn ?_
    convert (a * c).2 using 1
    apply RingOfIntegers.coe_injective
    have h1 : (n : E) = algebraMap (OK H) E b * algebraMap (OK H) E c := by
      rw [← map_mul, ← hc]; simp
    change (n : E) * φ _ = algebraMap (OK H) E (a * c)
    rw [map_div₀, φ.commutes, φ.commutes, h1, map_mul]
    field_simp
  refine ⟨⟨_, hm⟩, φ.injective ?_⟩
  exact φ.commutes _

theorem isDedekindDomain_OK (H : Host E) : IsDedekindDomain (OK H) :=
  have := finite_int_OK H
  { isNoetherian_of_tower ℤ (inferInstance : IsNoetherian ℤ (OK H)),
    Ring.DimensionLEOne.of_isIntegral ℤ (OK H), isIntegrallyClosed_OK H with }

theorem existsUnique_coord (H : Host E) (a : OK H) :
    ∃! m : ℤ × ℤ, a = (m.1 : OK H) + (m.2 : OK H) * wK H := by
  obtain ⟨u, v, h⟩ := exists_coord H a.2
  refine ⟨(u, v), Subtype.ext h, ?_⟩
  rintro ⟨u', v'⟩ h'
  have h2 : (a : 𝓞 E) = u' + v' * H.w0 := congrArg Subtype.val h'
  obtain ⟨h3, h4⟩ := coord_eq_zero H (u := u' - u) (v := v' - v) (by push_cast; linear_combination h - h2)
  exact Prod.ext (sub_eq_zero.1 h3) (sub_eq_zero.1 h4)

theorem finrank_int_OK (H : Host E) : Module.finrank ℤ (OK H) = 2 := by
  let f : (ℤ × ℤ) →ₗ[ℤ] OK H := LinearMap.coprod (LinearMap.toSpanSingleton ℤ _ 1)
    (LinearMap.toSpanSingleton ℤ _ (wK H))
  have hf : Function.Bijective f := by
    rw [Function.bijective_iff_existsUnique]
    intro a
    simpa [f, eq_comm (a := a)] using existsUnique_coord H a
  rw [← (LinearEquiv.ofBijective f hf).finrank_eq]
  simp

def barOK (H : Host E) : OK H ≃+* OK H where
  toFun a := ⟨H.bar a, LevelExist.bar_mem_adjoin H a.2⟩
  invFun a := ⟨H.bar a, LevelExist.bar_mem_adjoin H a.2⟩
  left_inv a := Subtype.ext (bar_bar H a)
  right_inv a := Subtype.ext (bar_bar H a)
  map_mul' a b := Subtype.ext (map_mul H.bar _ _)
  map_add' a b := Subtype.ext (map_add H.bar _ _)

theorem two_mul_finrank_OK (H : Host E) (M : Type) [AddCommGroup M] [Module (𝓞 E) M] [Module.Finite (𝓞 E) M] :
    2 * Module.finrank (OK H) M = Module.finrank ℚ E * Module.finrank (𝓞 E) M := by
  have := finite_int_OK H
  have : Module.Finite ℤ M := Module.Finite.trans (𝓞 E) M
  have : Module.Finite (OK H) M := Module.Finite.of_restrictScalars_finite ℤ _ _
  rw [← finrank_int_OK H, ← finrank_int_eq_mul_of_finite, ← RingOfIntegers.rank,
    ← finrank_int_eq_mul_of_finite]

theorem OK_isDedekindDomain_and_projective :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), IsDedekindDomain (OK H) ∧ (∀ a : OK H, ∃! m : ℤ × ℤ, a = (m.1 : OK H) + (m.2 : OK H) * wK H) ∧ (∃ br : OK H ≃+* OK H, (∀ a, ((br a : OK H) : 𝓞 E) = H.bar a) ∧ wK H + br (wK H) = 1 ∧ ∀ a, br (br a) = a) ∧ wK H ^ 2 + (((1 + H.d) / 4 : ℕ) : OK H) = wK H ∧ 2 * Module.finrank (OK H) (𝓞 E) = Module.finrank ℚ E ∧
  ∀ (M : Type) [AddCommGroup M] [Module (𝓞 E) M], Module.Finite (𝓞 E) M → Module.Projective (𝓞 E) M → Module.Finite (OK H) M ∧ Module.Projective (OK H) M ∧ Module.finrank (OK H) M = Module.finrank ℚ E / 2 * Module.finrank (𝓞 E) M := by
  intro E _ _ _ H
  have h2 : 2 * Module.finrank (OK H) (𝓞 E) = Module.finrank ℚ E := by
    simpa using two_mul_finrank_OK H (𝓞 E)
  refine ⟨isDedekindDomain_OK H, existsUnique_coord H,
    ⟨barOK H, fun _ => rfl, Subtype.ext ?_, fun a => Subtype.ext (bar_bar H a)⟩, Subtype.ext (cm_generator_sq_quadratic_eq H), h2, ?_⟩
  · change H.w0 + H.bar H.w0 = 1
    rw [cmHost_bar_halfIntegerGenerator, add_sub_cancel]
  · intro M _ _ _ _
    have := finite_int_OK H
    have := isDedekindDomain_OK H
    have : Module.Finite ℤ M := Module.Finite.trans (𝓞 E) M
    have : Module.IsTorsionFree ℤ M := Module.IsTorsionFree.trans (𝓞 E)
    refine ⟨Module.Finite.of_restrictScalars_finite ℤ _ _, Forms.projective_of_int _ _, ?_⟩
    have h3 := two_mul_finrank_OK H M
    rw [← h2, mul_assoc] at h3
    rw [← h2, Nat.mul_div_cancel_left _ two_pos]
    omega

end GlobalTheory.CM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveAppTopOfSection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.TrivDedekind

theorem surjective_appTop_of_section {K : Type} [Field K] {Y : Scheme.{0}} [IsIntegral Y] (p : Y ⟶ Sp K)
    [UniversallyClosed p] (e : Sp K ⟶ Y) (he : e ≫ p = 𝟙 _) : Function.Surjective p.appTop.hom := by
  have hF : IsField Γ(Y, ⊤) := isField_of_universallyClosed K p
  let _ := hF.toField
  have hinj : Function.Injective e.appTop.hom := e.appTop.hom.injective
  have hc : ∀ a, e.appTop.hom (p.appTop.hom a) = a := fun a => by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, he]
    simp
  exact fun c => ⟨e.appTop.hom c, hinj (hc _)⟩

theorem exists_gen_of_generic : ∀ (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (X' : Scheme.{0}) (π : X' ⟶ A.left) (p : X' ⟶ Sp K), IsPullback π p A.hom (spMap (algebraMap R K)) → ∀ N : LB A.left, N.IsLB → (∃ t : LB.Gen (N.pull (eSec A)), t.IsGen) → (∃ t : LB.Gen (N.pull π), t.IsGen) → ∃ t : LB.Gen N, t.IsGen := by
  intro R K _ _ _ _ _ A _ hA X' π p H N hN ⟨ρ, hρ⟩ ⟨t, ht⟩
  have := hA.smooth
  have := hA.proper
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom hA.smooth hA.geomConnected
  have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have : QuasiSeparatedSpace A.left := quasiSeparatedSpace_of_quasiSeparated A.hom
  have : IsIntegral X' := DvrModel.isIntegral_of_geometricallyIntegral H
  have : UniversallyClosed p := MorphismProperty.of_isPullback H inferInstance
  have he : eSec A ≫ A.hom = 𝟙 _ := Over.w η[A]
  exact GenericTriv.exists_gen_of_fibre (algebraMap R K) (IsFractionRing.injective R K) A.hom (eSec A) he π p H
    (surjective_appTop_of_section p (H.lift (spMap (algebraMap R K) ≫ eSec A) (𝟙 _)
      (by rw [Category.assoc, he]; simp)) (H.lift_snd _ _ _)) hN ρ hρ t ht

end GlobalTheory.TrivDedekind
end

