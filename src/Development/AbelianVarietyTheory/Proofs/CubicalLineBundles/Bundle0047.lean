module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0040
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsNumberFieldDefiningCmCurveHoms
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.CmFrameOfEq
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcDatumIsArcPointBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0019
public import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0041
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0044

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmEllipticCurveExistsOfUniformisation
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

theorem half_one_add_sqrt_quadratic {K : Type} [Field K] [CharZero K] {d : ℕ} (h4 : d % 4 = 3) {r w : K}
    (hr : r ^ 2 = -(d : K)) (hw : 2 * w = 1 + r) : w * w + (((1 + d) / 4 : ℕ) : K) = w := by
  have e : 4 * ((1 + d) / 4) = 1 + d := by omega
  have e' : (4 : K) * (((1 + d) / 4 : ℕ) : K) = 1 + d := by exact_mod_cast congrArg (Nat.cast : ℕ → K) e
  have e4 : (4 : K) ≠ 0 := by norm_num
  refine mul_left_cancel₀ e4 ?_
  have hr' : r = 2 * w - 1 := by linear_combination -hw
  subst hr'
  linear_combination e' + hr

theorem cmCurve_of_uniformisation : ThetaUnifAV → Out.PolBaseChangeSt → (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → CMCurve := by
  intro hU hB hE d _ hs h4 K _ _ h2 ⟨r, hr⟩
  obtain ⟨w, bar, hw, -, hgen, hσ, σ₀, hσ₀⟩ := ringOfIntegers_sqrt_neg_three_mod_four d hs h4 K h2 r hr
  have hnr := (hσ σ₀).1
  choose 𝔟 h𝔟 using ClassGroup.mk0_surjective (R := 𝓞 K)
  obtain ⟨M, hM, κ, P, v, L₀, Q, t, L, δ, hκ, hP, hQ, hδ, hc, hβ⟩ := _root_.GlobalTheory.CommonField.exists_common_field hU hB K h2 σ₀ hnr 𝔟
    (exists_cm_curves_of_weierstrass_curves (_root_.GlobalTheory.exists_polAV_latticeFamily hU hB) K h2 σ₀ hnr 𝔟)
  have hv : IsTangent v := hP.2.1.1 0
  have hwc : ((κ (w : K) : M) : ℂ) = (1 + Complex.I * √d) / 2 := by
    have e := congrArg σ₀ hw
    rw [map_mul, map_add (f := _), map_one, map_ofNat, hσ₀] at e
    rw [hκ]
    linear_combination e / 2
  refine ⟨M, hM, κ (w : K), P, v, hwc, hP.1, hP.2.1, ?_, ?_, fun s => ?_,
    _root_.GlobalTheory.mean_log_lieNormSq_eq_mean_log_eta hU hB hE K h2 σ₀ hnr 𝔟 h𝔟 M κ P v L₀ Q t L δ ⟨hκ, hP, hQ, hδ, hc⟩ hβ⟩
  · obtain ⟨P₀, φ, hφ⟩ := exists_isPolFibre hB (algebraMap (𝓞 M) M) P
    obtain ⟨v₀, hv₀, -⟩ := existsUnique_isVecOver hφ.2.1.1 v
    obtain ⟨β, -, hend, -⟩ := hβ
    obtain ⟨W, hW, hWv⟩ := hend w P₀ P₀ φ φ v₀ v₀ hφ hφ hv₀ hv₀
    have hP₀ := _root_.GlobalTheory.curve_lattice_baseChange _ P v L₀ M _ P₀ φ v₀ hP hφ hv₀
    refine ⟨P₀, φ, v₀, W, hφ, hv₀, hP₀.2.1, hW, ?_, hWv⟩
    refine LieMultiple.quadratic_equation_of_derivative hU hB M (algebraMap M ℂ) P₀ v₀ W _ _ (hP₀.2.1.1 0)
      hP₀.2.2.1 hW hWv ?_
    have e := congrArg κ (half_one_add_sqrt_quadratic h4 hr hw)
    rwa [map_add, map_mul, map_natCast] at e
  · obtain ⟨c, hc0, hc⟩ := hc
    refine lattice_unif_fibre_eq_of_period hU _ P v _ (L₀ _) c _ hP.1 hv (hP.2.2.2 _) hc0 fun z => ?_
    rw [hc, hκ]
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨m, n, rfl⟩ := hgen a
      exact ⟨m, n, by simp⟩
    · rintro ⟨m, n, rfl⟩
      exact ⟨m + n * w, by simp⟩
  · exact ⟨_, isLieNormSq_iff_eq_pi_div_covolume hU hB _ P v _ (L₀ _) hP.1 hv (hP.2.2.2 _)⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmFamilyDescendsToNumberField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.FamDesc

theorem exists_field (hT : ThetaUnifAV) (hB : Out.PolBaseChangeSt) (k : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ k] (P Q : Out.PolAV (Sp k)) {G H : Over (Sp ℂ)} [GrpObj G] [GrpObj H]
    {φ : G.left ⟶ P.A.left} {m : H.left ⟶ Q.A.left} (hP : IsGrpPullback G P.A (spMap (algebraMap k ℂ)) φ)
    (hQ : IsGrpPullback H Q.A (spMap (algebraMap k ℂ)) m) (f : G ⟶ H) [IsMonHom f] :
    ∃ k₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ k₁ ∧ ∀ (k₂ : IntermediateField ℚ ℂ) (h₂ : k ≤ k₂), k₁ ≤ k₂ →
      ∀ (G₂ H₂ : Over (Sp k₂)) (φ₂ : G₂.left ⟶ P.A.left) (m₂ : H₂.left ⟶ Q.A.left) (φ₃ : G.left ⟶ G₂.left)
        (m₃ : H.left ⟶ H₂.left), φ₂ ≫ P.A.hom = G₂.hom ≫ spMap (IntermediateField.inclusion h₂).toRingHom →
        IsPullback m₂ H₂.hom Q.A.hom (spMap (IntermediateField.inclusion h₂).toRingHom) →
        φ₃ ≫ G₂.hom = G.hom ≫ spMap (algebraMap k₂ ℂ) → m₃ ≫ H₂.hom = H.hom ≫ spMap (algebraMap k₂ ℂ) →
        φ₃ ≫ φ₂ = φ → m₃ ≫ m₂ = m → ∃ f₂ : G₂ ⟶ H₂, f.left ≫ m₃ = φ₃ ≫ f₂.left := by
  obtain ⟨e, he, he'⟩ := grpPullback_iso hP (isGrpPullback_pullback P.A _)
  obtain ⟨d, hd, hd'⟩ := grpPullback_iso hQ (isGrpPullback_pullback Q.A _)
  obtain ⟨K, f₁, j, hK, -, j₁, j₂, j₃⟩ := hom_descends_to_numberField hT hB k P Q (e.inv ≫ f ≫ d.hom) inferInstance
  have : IsScalarTower ℚ k K := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have hfin : FiniteDimensional ℚ K := Module.Finite.trans k K
  refine ⟨K.restrictScalars ℚ, hfin, fun k₂ h₂ h₁ G₂ H₂ φ₂ m₂ φ₃ m₃ w₂ c₂ w₃ v₃ e₃ d₃ => ?_⟩
  let q : K →+* k₂ := (IntermediateField.inclusion h₁).toRingHom
  have s₁ : spMap q ≫ spMap (algebraMap k K) = spMap (IntermediateField.inclusion h₂).toRingHom :=
    (spMap_comp_spMap _ _).trans (congrArg spMap (RingHom.ext fun _ => rfl))
  have s₂ : spMap (algebraMap k₂ ℂ) ≫ spMap q = spMap K.val.toRingHom :=
    (spMap_comp_spMap _ _).trans (congrArg spMap (RingHom.ext fun _ => rfl))
  obtain ⟨i, i₁, i₂⟩ : ∃ i : G₂.left ⟶ pullback P.A.hom (spMap (algebraMap k K)),
      i ≫ pullback.fst _ _ = φ₂ ∧ i ≫ pullback.snd _ _ = G₂.hom ≫ spMap q :=
    ⟨pullback.lift φ₂ (G₂.hom ≫ spMap q) (by rw [w₂, Category.assoc, s₁]), pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩
  have fw : f₁.left ≫ pullback.snd Q.A.hom (spMap (algebraMap k K)) = pullback.snd _ _ := Over.w f₁
  have ew : e.hom.left ≫ pullback.snd P.A.hom (spMap (algebraMap k ℂ)) = G.hom := Over.w e.hom
  have w : (i ≫ f₁.left ≫ pullback.fst _ _) ≫ Q.A.hom =
      G₂.hom ≫ spMap (IntermediateField.inclusion h₂).toRingHom := by
    have h : f₁.left ≫ pullback.fst Q.A.hom (spMap (algebraMap k K)) ≫ Q.A.hom =
        pullback.snd _ _ ≫ spMap (algebraMap k K) :=
      (congrArg (f₁.left ≫ ·) pullback.condition).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) fw))
    refine (Category.assoc _ _ _).trans ((congrArg (i ≫ ·) ((Category.assoc _ _ _).trans h)).trans ?_)
    rw [← Category.assoc, i₂, Category.assoc, s₁]
  have key : φ₃ ≫ i = e.hom.left ≫ j := by
    apply pullback.hom_ext
    · exact ((Category.assoc _ _ _).trans ((congrArg (φ₃ ≫ ·) i₁).trans e₃)).trans
        ((Category.assoc _ _ _).trans ((congrArg (e.hom.left ≫ ·) j₁).trans he')).symm
    · refine ((Category.assoc _ _ _).trans ((congrArg (φ₃ ≫ ·) i₂).trans ?_)).trans
        ((Category.assoc _ _ _).trans ((congrArg (e.hom.left ≫ ·) j₂).trans ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ _) ew)))).symm
      rw [← Category.assoc, w₃, Category.assoc, s₂]
  obtain ⟨f₂, hf₂⟩ : ∃ f₂ : G₂ ⟶ H₂, f₂.left ≫ m₂ = i ≫ f₁.left ≫ pullback.fst _ _ :=
    ⟨Over.homMk (c₂.lift _ G₂.hom w) (c₂.lift_snd _ _ _), c₂.lift_fst _ _ _⟩
  refine ⟨f₂, c₂.hom_ext ?_ ?_⟩
  · have r : e.hom.left ≫ (e.inv ≫ f ≫ d.hom).left = f.left ≫ d.hom.left := by
      rw [← Over.comp_left, e.hom_inv_id_assoc, Over.comp_left]
    have a₁ : (φ₃ ≫ f₂.left) ≫ m₂ = e.hom.left ≫ j ≫ f₁.left ≫ pullback.fst _ _ :=
      (Category.assoc _ _ _).trans ((congrArg (φ₃ ≫ ·) hf₂).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) key).trans (Category.assoc _ _ _))))
    rw [a₁, Category.assoc, d₃, ← hd', ← Category.assoc, ← r, Category.assoc]
    exact congrArg (e.hom.left ≫ ·) j₃.symm
  · rw [Category.assoc, Category.assoc, Over.w, v₃, w₃, ← Category.assoc, Over.w]

theorem exists_mul {S S' : Scheme.{0}} {j : S' ⟶ S} {G H : Over S} [GrpObj H] {G' H' : Over S'} [GrpObj H']
    {φ : G'.left ⟶ G.left} {m : H'.left ⟶ H.left} (w : φ ≫ G.hom = G'.hom ≫ j) (hm : IsGrpPullback H' H j m)
    {x' y' : G' ⟶ H'} {x y : G ⟶ H} (hx : x'.left ≫ m = φ ≫ x.left) (hy : y'.left ≫ m = φ ≫ y.left) :
    (x' * y').left ≫ m = φ ≫ (x * y).left := by
  let φ₀ : Over.mk (G'.hom ≫ j) ⟶ G := Over.homMk φ w
  have h := hm.2 G' x' y' (φ₀ ≫ x) (φ₀ ≫ y) hx.symm hy.symm
  rw [← MonObj.comp_mul] at h
  rw [← h]
  rfl

end GlobalTheory.CM.FamDesc

namespace GlobalTheory.CM

open FamDesc in
theorem isFam_descends_to_numberField : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k] (ω : k) (C : Ell H k ω) (D : Datum H) (h : D.La → D.La → OK H) (T : PAT H (Sp k)) (L : Submodule (𝓞 E) D.La) (ω' : ℂ) (C' : Ell H ℂ ω') (φ : C'.P.A.left ⟶ C.P.A.left) (T' : PAT H (Sp ℂ)) (m : SABMap T'.t T.t (spMap (algebraMap k ℂ))) (ψ' : L → (C'.P.A ⟶ T'.t.G)), EllMap C' C (algebraMap k ℂ) φ → IsFam C' T' h L ψ' →
  ∃ k₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ k₁ ∧ k ≤ k₁ ∧ ∀ (k₂ : IntermediateField ℚ ℂ) (h₂ : k ≤ k₂), k₁ ≤ k₂ → ∀ (ω₂ : k₂) (C₂ : Ell H k₂ ω₂) (φ₂ : C₂.P.A.left ⟶ C.P.A.left) (φ₃ : C'.P.A.left ⟶ C₂.P.A.left) (T₂ : PAT H (Sp k₂)) (m₂ : SABMap T₂.t T.t (spMap (IntermediateField.inclusion h₂).toRingHom)) (m₃ : SABMap T'.t T₂.t (spMap (algebraMap k₂ ℂ))),
    EllMap C₂ C (IntermediateField.inclusion h₂).toRingHom φ₂ → EllMap C' C₂ (algebraMap k₂ ℂ) φ₃ → φ₃ ≫ φ₂ = φ → m₃.φ ≫ m₂.φ = m.φ → ∃ ψ : L → (C₂.P.A ⟶ T₂.t.G), IsFam C₂ T₂ h L ψ ∧ ∀ a, (ψ' a).left ≫ m₃.φ = φ₃ ≫ (ψ a).left := by
  intro hT hL E _ _ _ H k _ ω C D h T L ω' C' φ T' m ψ' hC hF
  have hfin := D.fin
  have : Module.Finite (𝓞 E) L := inferInstance
  have : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  have hg : AddMonoid.FG L := AddGroup.fg_iff_addMonoid_fg.1 (Module.Finite.iff_addGroup_fg.1 inferInstance)
  obtain ⟨S, hS⟩ := AddMonoid.isAddFG_iff.mp hg
  choose K hK hK' using fun a : L => @exists_field hT hL.polBaseChange k _ C.P T.pol _ _ _ _ _ _ hC.2.1.2.1 m.cart
    (ψ' a) (hF.1 a).isMonHom
  refine ⟨k ⊔ (K 0 ⊔ ⨆ a : S, K a), ?_, le_sup_left, ?_⟩
  · have := hK
    have : FiniteDimensional ℚ (⨆ a : S, K a : IntermediateField ℚ ℂ) := IntermediateField.finiteDimensional_iSup_of_finite
    infer_instance
  intro k₂ h₂ h₁ ω₂ C₂ φ₂ φ₃ T₂ m₂ m₃ e₂ e₃ eφ em
  have gen : ∀ a : L, K a ≤ k₂ → ∃ f₂ : C₂.P.A ⟶ T₂.t.G, (ψ' a).left ≫ m₃.φ = φ₃ ≫ f₂.left := fun a ha =>
    hK' a k₂ h₂ ha C₂.P.A T₂.t.G φ₂ m₂.φ φ₃ m₃.φ e₂.2.1.2.1.1.w m₂.cart.1 e₃.2.1.2.1.1.w m₃.cart.1.w eφ em
  have all : ∀ a : L, ∃ f₂ : C₂.P.A ⟶ T₂.t.G, (ψ' a).left ≫ m₃.φ = φ₃ ≫ f₂.left := by
    intro a
    have ha : a ∈ AddSubmonoid.closure (S : Set L) := hS ▸ AddSubmonoid.mem_top a
    induction ha using AddSubmonoid.closure_induction with
    | mem a ha => exact gen a (((le_iSup (fun a : S => K a) ⟨a, ha⟩).trans (le_sup_right.trans le_sup_right)).trans h₁)
    | zero => exact gen 0 ((le_sup_left.trans le_sup_right).trans h₁)
    | add a b _ _ ha hb =>
      obtain ⟨x, hx⟩ := ha
      obtain ⟨y, hy⟩ := hb
      exact ⟨x * y, by rw [hF.2.1]; exact exists_mul e₃.2.1.2.1.1.w m₃.cart hx hy⟩
  choose ψ hψ using all
  exact ⟨ψ, _root_.GlobalTheory.FamDescent.isFam_descend hL E H k₂ ω₂ C₂ D h T₂ L ψ ℂ ω' C' (algebraMap k₂ ℂ) φ₃ T' m₃ ψ'
    (algebraMap k₂ ℂ).injective e₃ hψ hF, hψ⟩

end GlobalTheory.CM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmFamilyExtendsOverDedekindDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory

theorem isFam_extends_dedekind :
    Out.Laws → HomExtDvr → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (ω : R) (C : Ell H R ω) (D : Datum H) (h : D.La → D.La → OK H) (T : PAT H (Sp R)) (L : Submodule (𝓞 E) D.La) (ω' : K) (C' : Ell H K ω') (φ : C'.P.A.left ⟶ C.P.A.left) (T' : PAT H (Sp K)) (m : SABMap T'.t T.t (spMap (algebraMap R K))) (ψ' : L → (C'.P.A ⟶ T'.t.G)), EllMap C' C (algebraMap R K) φ → IsFam C' T' h L ψ' → ∃ ψ : L → (C.P.A ⟶ T.t.G), IsFam C T h L ψ ∧ ∀ a, (ψ' a).left ≫ m.φ = φ ≫ (ψ a).left := by
  intro hL hD E _ _ _ H R K _ _ _ _ _ ω C D h T L ω' C' φ T' m ψ' hφ hψ'
  have key : ∀ a : L, ∃ F : C.P.A ⟶ T.t.G, (ψ' a).left ≫ m.φ = φ ≫ F.left := fun a => by
    obtain ⟨F, -, hF, -⟩ := abelianScheme_hom_extends_dedekind_of_isGrpPullback hD R K C.P.A T.t.G C'.P.A T'.t.G
      φ m.φ C.P.isAb T.ab hφ.2.1.2.1 m.cart (ψ' a) (hψ'.1 a).isMonHom
    exact ⟨F, hF⟩
  choose ψ hψ using key
  exact ⟨ψ, _root_.GlobalTheory.FamDescent.isFam_descend hL E H R ω C D h T L ψ K ω' C' (algebraMap R K) φ T' m ψ'
    (IsFractionRing.injective R K) hφ hψ hψ', hψ⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DataXOfModelOfGamAt
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory GlobalTheory.RunIn

namespace GlobalTheory.LatticeData

theorem dataXOfModel_of_gamAt : ∀ (D : D7) (T : Core D), GamAt T → ∀ j, ∀ (_h : LawsCore T), InR D j → ∀ (σ₀ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ₀ → ∀ (k : (T.U j σ₀).Comp), ∃ Xx : DataX D.host.E D.R.r, Xx.toData = (T.U j σ₀).X k ∧ Xx.g = T.Q.l.M ∧ Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xx.L', v = a • u} := by
  intro D T hG j h hj σ hσ k
  obtain ⟨Xx, h1, h2, h3, -⟩ :=
    exists_dataX_of_hasPrinc D T h j hj σ hσ (fun k γ => hG j hj σ hσ k γ) k
  exact ⟨Xx, h1, h2, h3⟩

end GlobalTheory.LatticeData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmPointLatticeDataOfAdaptedBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.CMBasis

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_pair (H : Host E) {r : ℕ} (X : FD.DataX E r) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (hr : 0 < r) (h𝔄 : 𝔄 ≠ 0) (hΨ : ∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0)
    (hΛ : X.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ X.L', v = a • u}) :
    ∃ (D₁ : Bool → Datum H) (e : ∀ b, (D₁ b).La ≃ₗ[𝓞 E] (𝔄 : Submodule (𝓞 E) E)) (s : Bool → ℤ),
      ((D₁ true).p = 1 ∧ (D₁ true).q = 0) ∧ ((D₁ false).p = 0 ∧ (D₁ false).q = 1) ∧ (∀ b, s b = 1 ∨ s b = -1) ∧
      ∀ b x y, (((D₁ b).EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (s b * X.ξ0 * (e b x : E) * FD.cc (e b y : E)) := by
  obtain ⟨t, ht, hκ⟩ : ∃ t : ℤ, (t = 1 ∨ t = -1) ∧ X.κ0 = 2 * (t * X.ξ0) := by
    rcases X.κ0_xi with h | h
    · exact ⟨1, Or.inl rfl, by rw [h]; simp⟩
    · exact ⟨-1, Or.inr rfl, by rw [h]; simp⟩
  have hd := GlobalTheory.trace_xi_mul_conj_int_iff_mem E r X 𝔄 hr h𝔄 hΛ
  obtain ⟨D, e, hp, hq, he⟩ := SelfDualDatum.exists_datum E H (𝔄 : Submodule (𝓞 E) E) (t * X.ξ0)
    (FractionalIdeal.fg_of_isUnit _ (IsUnit.mk0 _ h𝔄)) (FractionalIdeal.coeToSubmodule_ne_bot.2 h𝔄)
    (by
      have := X.ξ0_im
      rw [FD.cc] at this
      rw [map_mul, map_intCast, this, mul_neg])
    (fun τ hτ => by
      have := X.κ0_sign ⟨τ, (hΨ τ).2 hτ⟩
      rw [hκ, map_mul, map_ofNat] at this
      simp only [Complex.mul_im, Complex.re_ofNat, Complex.im_ofNat, zero_mul, add_zero] at this
      linarith)
    (fun x => by
      refine Iff.trans ?_ (hd x)
      refine forall₂_congr fun y _ => ?_
      rcases ht with rfl | rfl
      · simp [FD.cc]
      · simp only [Int.cast_neg, Int.cast_one, neg_mul, _root_.one_mul, map_neg, FD.cc]
        exact ⟨fun ⟨n, h⟩ => ⟨-n, by rw [Int.cast_neg, ← h, neg_neg]⟩, fun ⟨n, h⟩ => ⟨-n, by rw [h, Int.cast_neg]⟩⟩)
  refine ⟨fun b => match b with | true => D | false => oppDatum D,
    fun b => match b with | true => e | false => e, fun b => match b with | true => t | false => -t,
    ⟨hp, hq⟩, ⟨hq, hp⟩, ?_, ?_⟩
  · rintro (_ | _)
    · rcases ht with rfl | rfl <;> simp
    · exact ht
  · rintro (_ | _) x y
    · change D.La at x y
      change ((-(D.EF x y) : ℤ) : ℚ) = Algebra.trace ℚ E (((-t : ℤ) : E) * X.ξ0 * (e x : E) * FD.cc (e y : E))
      rw [Int.cast_neg, he, ← map_neg]
      congr 1
      simp [FD.cc]
    · exact he x y


omit [IsCMField E] in
theorem exists_nsmul_mem (𝔄 : Submodule (𝓞 E) E) (h : 𝔄 ≠ ⊥) {J : Type} [Fintype J] (c : J → E) :
    ∃ n : ℕ, 0 < n ∧ ∀ i, (n : E) * c i ∈ 𝔄 := by
  classical
  obtain ⟨a, ha, h0⟩ := (Submodule.ne_bot_iff _).1 h
  obtain ⟨n, hn, hi⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image fun i => c i / a)
  refine ⟨n.natAbs, Int.natAbs_pos.2 hn, fun i => ?_⟩
  have h1 := 𝔄.smul_mem (⟨n • (c i / a), hi _ (by simp)⟩ : 𝓞 E) ha
  have h2 : (n : E) * c i ∈ 𝔄 := by
    convert h1 using 1
    change _ = (n • (c i / a)) * a
    rw [zsmul_eq_mul, _root_.mul_assoc, div_mul_cancel₀ _ h0]
  rcases Int.natAbs_eq n with h | h
  · rwa [h, Int.cast_natCast] at h2
  · rw [h, Int.cast_neg, Int.cast_natCast, neg_mul] at h2
    exact 𝔄.neg_mem_iff.1 h2

theorem exists_cmLat (H : Host E) {r p q : ℕ} (Y : FD.Data E r) (x₀ : Y.dom) (X : FD.DataX E r) (hX : X.toData = Y)
    (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)
    (hr : 0 < r) (h𝔄 : 𝔄 ≠ 0) (hrk : r = p + q) (hp0 : Y.p0 = q) (hΨ : ∀ τ : E →+* ℂ, τ ∈ Y.Ψ ↔ τ (H.rt : E) = H.rt0)
    (hΛ : X.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ X.L', v = a • u})
    (D : Datum H) {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe)
    (φ : D.La ≃ₗ[𝓞 E] Y.Λ)
    (isom : ∀ a b, ((D.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-Y.ξ0 * FD.herm Y.Gm (φ a : Fin r → E) (φ b)))
    (ix : Fin g → ℕ) (hix : ∀ j, ty j (H.rt : E) ≠ H.rt0 → ix j < q)
    (pm : ∀ a j, Pe a j = perFr Y x₀.1 (φ a : Fin r → E) (ty j) (ix j))
    (La : ℝ) (lam : Fin r → Fin r → E) (hl : FD.LamBasis X La (hX ▸ x₀.1) lam) :
    ∃ Z : CMLat hP p q, ∀ j (τ : E →+* ℂ), ‖τ (Z.hh j : E)‖ ≤ La ^ 2 := by
  classical
  subst hX
  obtain ⟨D₁, e, s, h1, h2, hs, he⟩ := exists_pair H X 𝔄 hr h𝔄 hΨ hΛ
  have hpure := GlobalTheory.PurePer.perFr_pure E r X La x₀.1 lam x₀.2 hl
  obtain ⟨hL, hli, -, -, -, hbd, -⟩ := hl
  let σ : Fin p ⊕ Fin q ≃ Fin r := (Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr (by omega)))
  have hσl : ∀ j, q ≤ (σ (.inl j) : ℕ) := fun j => by simp [σ]
  have hσr : ∀ j, (σ (.inr j) : ℕ) < q := fun j => by simp [σ]
  have hmem : ∀ (a : (𝔄 : Submodule (𝓞 E) E)) j, (a : E) • lam j ∈ X.Λ := fun a j =>
    hΛ ▸ Submodule.subset_span ⟨a, a.2, _, hL j, rfl⟩
  let m : Fin r → (𝔄 : Submodule (𝓞 E) E) →ₗ[𝓞 E] X.Λ := fun j =>
    { toFun := fun a => ⟨_, hmem a j⟩
      map_add' := fun a b => Subtype.ext (add_smul _ _ _)
      map_smul' := fun c a => Subtype.ext (smul_assoc _ _ _) }
  let f : ∀ j : Fin p ⊕ Fin q, (D₁ j.isLeft).La →ₗ[𝓞 E] D.La := fun j =>
    φ.symm.toLinearMap ∘ₗ m (σ j) ∘ₗ (e _).toLinearMap
  have hf : ∀ j a, (φ (f j a) : Fin r → E) = (e _ a : E) • lam (σ j) := fun j a => by
    simp [f, m]
  let hh : Fin p ⊕ Fin q → 𝓞 E := fun j =>
    -(s j.isLeft : 𝓞 E) * ⟨FD.herm X.Gm (lam (σ j)) (lam (σ j)), X.L'_int _ (hL _) _ (hL _)⟩
  have hhh : ∀ j, (hh j : E) = -(s j.isLeft : E) * FD.herm X.Gm (lam (σ j)) (lam (σ j)) := fun j => by
    simp only [hh, map_mul, map_neg, map_intCast]
    rfl
  have hsq : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := fun τ => by
    refine sq_eq_sq_iff_eq_or_eq_neg.1 ?_
    rw [← map_pow, HostModel.coe_sq_eq_neg H.rt_sq, H.sqrt_neg_disc_sq, map_neg, map_natCast]
  refine ⟨⟨D₁, h1, h2, f, ?_, hh, fun j a b => ?_, ?_⟩, fun j τ => ?_⟩
  · rintro (j | j) a k hk
    · rw [pm, hf]
      have hk' : ty k (H.rt : E) ≠ H.rt0 := by simpa using hk
      exact (hpure _ _ _ _).2 (hp0 ▸ hσl j) (fun h => hk' ((hΨ _).1 h)) (hp0 ▸ hix k hk')
    · rw [pm, hf]
      have hk' : ty k (H.rt : E) ≠ -H.rt0 := by simpa using hk
      exact (hpure _ _ _ _).1 (hp0 ▸ hσr j) ((hΨ _).2 ((hsq _).resolve_right hk'))
  · apply Int.cast_injective (α := ℚ)
    rw [isom, he, hf, hf, map_smul, Submodule.coe_smul, Algebra.smul_def (hh j), ← RingOfIntegers.coe_eq_algebraMap, hhh]
    congr 1
    have h3 : ∀ (a b : E) (u : Fin r → E), FD.herm X.Gm (a • u) (b • u) = a * FD.cc b * FD.herm X.Gm u u :=
      fun a b u => by
        simp only [FD.herm, FD.cc, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [h3]
    rcases hs j.isLeft with h | h <;> rw [h] <;> push_cast <;> ring
  · haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    let B := basisOfLinearIndependentOfCardEqFinrank hli (by simp)
    have hB : ∀ j, B j = lam j := fun j => by simp [B]
    let N : Submodule (𝓞 E) D.La := LinearMap.range (∑ j, f j ∘ₗ LinearMap.proj j)
    have hN : ∀ a, a ∈ N ↔ ∃ x : ∀ j : Fin p ⊕ Fin q, (D₁ j.isLeft).La, a = ∑ j, f j (x j) := fun a => by
      simp only [N, LinearMap.mem_range, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
      exact exists_congr fun _ => eq_comm
    obtain ⟨S, hS⟩ := D.fin.fg_top
    obtain ⟨n, hn, hc⟩ := exists_nsmul_mem (𝔄 : Submodule (𝓞 E) E) (FractionalIdeal.coeToSubmodule_ne_bot.2 h𝔄)
      (fun i : S × Fin r => B.repr (φ i.1 : Fin r → E) i.2)
    refine ⟨n, hn, fun a => (hN _).1 ?_⟩
    have : (⊤ : Submodule (𝓞 E) D.La) ≤ N.comap (n • LinearMap.id) := by
      rw [← hS, Submodule.span_le]
      intro a ha
      refine (hN _).2 ⟨fun j => (e _).symm ⟨_, hc (⟨a, ha⟩, σ j)⟩, φ.injective (Subtype.ext ?_)⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, AddSubmonoidClass.coe_finsetSum]
      simp only [hf, LinearEquiv.apply_symm_apply]
      rw [Equiv.sum_comp σ (fun j => ((n : E) * B.repr (φ a : Fin r → E) j) • lam j)]
      simp only [mul_smul, ← Finset.smul_sum, ← hB, B.sum_repr]
      simp [Nat.cast_smul_eq_nsmul]
    exact this Submodule.mem_top
  · change ‖τ (hh j : E)‖ ≤ _
    have h4 : ‖τ (hh j : E)‖ = ‖τ (FD.herm X.Gm (lam (σ j)) (lam (σ j)))‖ := by
      rw [hhh]
      rcases hs j.isLeft with h | h <;> rw [h] <;> simp
    rw [h4]
    by_cases hτ : τ ∈ X.Ψ
    · exact hbd _ ⟨τ, hτ⟩
    · have := hbd (σ j) ⟨ComplexEmbedding.conjugate τ, by
        by_contra h
        exact hτ ((X.cmType τ).2 h)⟩
      simpa [ComplexEmbedding.conjugate_coe_eq] using this

theorem exists_cmLat_unfAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : Unf Xo c c.F.val.toRingHom r), IsUnf U → 0 < r → ∀ (k : U.Comp) (x₀ : (U.X k).dom) (W : PullbackSections.UnfAt U k x₀) (Xx : FD.DataX E r) (hX : Xx.toData = U.X k) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), 𝔄 ≠ 0 → Xx.Λ = Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} → ∀ (La : ℝ) (lam : Fin r → Fin r → E), FD.LamBasis Xx La (hX ▸ x₀.1) lam → ∃ Z : CMLat W.per Dw.p Dw.q, ∀ j (τ : E →+* ℂ), ‖τ (Z.hh j : E)‖ ≤ La ^ 2 := by
  intro E _ _ _ H Dw l Xo c r U hU hr k x₀ W Xx hX 𝔄 h𝔄 hΛ La lam hl
  obtain ⟨h1, h2, -⟩ := hU
  refine exists_cmLat H (U.X k) x₀ Xx hX 𝔄 hr h𝔄 h1 (h2 k).1 (h2 k).2 hΛ _ W.per (W.φ k) (W.isom k)
    (fun j => (W.e j).2) (fun j hj => ?_) W.pm_eq La lam hl
  exact (W.e j).2.2.trans_eq (if_neg hj)

end GlobalTheory.LamT.CMBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TopLieVectorNormSqEqGramDet
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

noncomputable section
namespace GlobalTheory.CM.TopLieVector

theorem sq_eq_det_gram : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left) (hf : IsPolFibre (algebraMap (𝓞 K) K) A x.P φ) (h : HermFam K (Fin x.P.g → K)), (GenFib.mk x.P φ hf x.v x.basis : GenFib A).IsHerm h → ∀ (T abelian₂ : MLine K) (s : K →+* ℂ), KeyArchAt x T abelian₂ s → abelian₂.n s ^ 2 = (h.gram s (fun i : Fin x.P.g => Pi.single i 1)).det.re := by
  intro hU _ K _ _ P x φ₀ hf₀ h hH T abelian₂ σ hx
  obtain ⟨x', u, Hm, W, χ, θ, Fd, hx, hA, -, -, hW, hF, -, hn⟩ := hx
  obtain ⟨φ, -, w, e, D, hp, hw, -, -, h₁, h₂, hv⟩ := hx
  obtain rfl := TopDifferential.eq_dualMapR h₁ h₂
  obtain ⟨Q, ψ, v, u', Hm', χ', W', a, b, c, d⟩ := hH σ
  have hf : IsPolFibre σ x.P x'.P φ := ⟨e, hp, LBIso.symm ⟨w, hw⟩⟩
  have key := LieMetric.hermForm_eq hU a hf b hA x.basis.1 c (w' := fun i => x'.v (i.cast e.symm))
    (W' := fun i => W (i.cast e.symm)) fun i => ⟨hv (i.cast e.symm), hW _⟩
  have e₁ : h.gram σ (fun i : Fin x.P.g => Pi.single i 1) =
      (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (W j) (W i)).submatrix (finCongr e.symm) (finCongr e.symm) := by
    ext i j
    exact (d i j).trans (congrArg (fun z => (Real.pi : ℂ) * z) (key j i))
  obtain ⟨Ef, t₁, t₂, -, -, t₃, -⟩ := AHWeil.tangent_and_weil_of_isAH hU x'.P _ u Hm χ hA
  have := u.discrete
  have hvol := volume_mul_det_eq_one_of_unimodular _ u.Λ u.full Hm Ef Fd hA.1 hA.2.1 t₁ t₂ hF
  rw [e₁, Matrix.det_submatrix_equiv_self, TopDifferential.det_gram, hn, div_eq_mul_inv,
    eq_inv_of_mul_eq_one_right hvol]

end GlobalTheory.CM.TopLieVector
end
end

