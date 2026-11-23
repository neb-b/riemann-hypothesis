module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0057
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ConclusionsAtIdentity
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0047
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AbelianVarietyTheory.Definitions.CMLattices.LamLetters
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsGrpPullbackPow
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LamDegStLogOm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

theorem GlobalTheory.LamF.lamDegSt_logOm : ThetaUnifAV → Out.Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [NeZero H.d] (χ : DirichletCharacter ℂ H.d), IsKroneckerChar χ → LamDegSt H (logOm E χ).re :=
  fun hΘ hL =>
    _root_.GlobalTheory.LamF.lamDegSt_of_degSt
      (_root_.GlobalTheory.CM.PureDeg.degSt (_root_.GlobalTheory.cmCurve_of_uniformisation hΘ hL.polBaseChange _root_.GlobalTheory.semiAbelian_hom_extends_uniquely_dvr) hΘ hL _root_.GlobalTheory.semiAbelian_hom_extends_uniquely_dvr) hΘ hL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PrincipalTripleExtendsOfCurveHomomorphisms
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.CurveFamily

variable {S : Scheme.{0}}

theorem comp_prod {T B A : Over S} [GrpObj A] [IsCommMonObj A] {I : Type} (s : Finset I) (x : T ⟶ B)
    (f : I → (B ⟶ A)) : x ≫ ∏ i ∈ s, f i = ∏ i ∈ s, x ≫ f i :=
  map_prod (preHom (G := A) x) f s

theorem prod_comp {T B A : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] {I : Type} (s : Finset I)
    (x : I → (T ⟶ B)) (f : B ⟶ A) [IsMonHom f] : (∏ i ∈ s, x i) ≫ f = ∏ i ∈ s, x i ≫ f :=
  map_prod (MonoidHom.mk' (fun y : T ⟶ B => y ≫ f) fun a b => MonObj.mul_comp a b f) x s

theorem exists_hom_pow {G B A : Over S} [GrpObj G] [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] {n : ℕ}
    (p : Out.IsPowGrp G B n) (ψ : Fin n → (B ⟶ A)) (hψ : ∀ i, IsMonHom (ψ i)) {k : Type} [Field k] (t : Sp k ⟶ S)
    (h : OntoAt ψ t) : ∃ Ψ : G ⟶ A, IsMonHom Ψ ∧ ∀ y : Over.mk t ⟶ A, ∃ x : Over.mk t ⟶ G, y = x ≫ Ψ := by
  have := p.hom
  have isMonHom_of_mul_comp (f : G ⟶ A)
      (hf : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) : IsMonHom f := by
    refine ⟨?_, ?_⟩
    ·
      rw [MonObj.one_eq_one, MonObj.one_eq_one]
      exact map_one (MonoidHom.mk' (fun x : 𝟙_ (Over S) ⟶ G => x ≫ f) (hf _))
    ·
      rw [MonObj.mul_eq_mul G, hf, MonObj.mul_eq_mul A, MonObj.comp_mul,
        tensorHom_fst, tensorHom_snd]
  refine ⟨∏ i, p.pr i ≫ ψ i, isMonHom_of_mul_comp _ (fun T x y => ?_), fun y => ?_⟩
  · simp only [comp_prod, ← Finset.prod_mul_distrib, ← Category.assoc, MonObj.mul_comp]
  · obtain ⟨m, i, x, rfl⟩ := h y
    let c : Fin n → (Over.mk t ⟶ B) := fun j => ∏ a ∈ Finset.univ.filter (fun a => i a = j), x a
    have hc : ∀ j, p.lim.lift (Fan.mk (Over.mk t) c) ≫ p.pr j = c j := fun j => p.lim.fac (Fan.mk (Over.mk t) c) ⟨j⟩
    refine ⟨p.lim.lift (Fan.mk (Over.mk t) c), ?_⟩
    rw [List.prod_ofFn, comp_prod, ← Finset.prod_fiberwise Finset.univ i]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← Category.assoc, hc, prod_comp]
    exact Finset.prod_congr rfl fun a ha => by rw [(Finset.mem_filter.1 ha).2]

theorem exists_extension : ThetaUnifAV → Out.Laws → Out.Laws2 → HomExtDvr → Published.KernelFiniteFlatSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (σ : K →+* ℂ) (P : Out.PolAV (Sp R)) (P₀ : Out.PolAV (Sp K)) (φ : P₀.A.left ⟶ P.A.left) (T₀ : PAT H (Sp K)) (ψ : Fin T₀.g → (P₀.A ⟶ T₀.t.G)), IsPolFibre (algebraMap R K) P P₀ φ → P.g = 1 → (∀ i, IsMonHom (ψ i)) → OntoAt ψ (spMap σ) → ∃ (T : PAT H (Sp R)) (_ : SABMap T₀.t T.t (spMap (algebraMap R K))), T.g = T₀.g := by
  intro hT hL hL₂ hE hK E _ _ _ H R K _ _ _ _ _ σ P P₀ φ T₀ ψ hφ hg hψ ho
  have := P₀.isAb.comm
  have := T₀.ab.comm
  obtain ⟨Q, p, hQ⟩ := _root_.GlobalTheory.CM.exists_polAV_isPowGrp R P T₀.g
  obtain ⟨Q₀, Φ, hΦ⟩ := exists_isPolFibre hL.polBaseChange (algebraMap R K) Q
  let p₀ := Out.powIsPowGrp P₀.A T₀.g
  obtain ⟨Φ', hΦ', -⟩ := KeyPow.exists_isGrpPullback_pow hφ.2.1 p p₀
  obtain ⟨e, he, -⟩ := grpPullback_iso hΦ.2.1 hΦ'
  obtain ⟨Ψ, hΨ, hs⟩ := exists_hom_pow p₀ ψ hψ (spMap σ) ho
  refine _root_.GlobalTheory.CM.exists_pat_model_of_isogeny hT hL hL₂ hE hK E H R K σ Q Q₀ Φ T₀ (e.hom ≫ Ψ) hΦ (by rw [hQ, hg, _root_.mul_one])
    inferInstance ?_
  refine (_root_.GlobalTheory.OntoSurj.surjective_of_onto_complex_points K σ σ.injective T₀.t.G Q₀.A (e.hom ≫ Ψ) T₀.ab Q₀.isAb fun y => ?_).1
  obtain ⟨x, rfl⟩ := hs y
  exact ⟨x ≫ e.inv, by simp⟩

end GlobalTheory.CM.CurveFamily
end
end

