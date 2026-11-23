module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0049
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1421
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1847
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0165
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0053
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0690
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0694
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLieEigenbasisOfLocalizationsAtPrime
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUnitSmulEqOfBijectiveToSpanSingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2066
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0793
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2053
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2079
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Poinc.GalAut

section General

variable {o Ω₁ Ω₂ : Type} [CommRing o] [Field Ω₁] [Algebra o Ω₁] [Field Ω₂] [Algebra o Ω₂]
  {M₁ : RatModel o Ω₁} {N : RatModel o Ω₂} {φ : Ω₁ →ₐ[o] Ω₂} {q : N.Z ⟶ M₁.Z} [IsFinite q]

theorem map_ringOn (hf : M₁.IsHom N φ q) (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N.Z) (τ : Ω₂ →ₐ[o] Ω₂) (hτ : ∀ a, τ (φ a) = φ a)
    {U₀ : M₁.Z.Opens} (hU₀ : IsAffineOpen U₀) (hne : ((q ⁻¹ᵁ U₀ : N.Z.Opens) : Set N.Z).Nonempty) :
    ∀ x ∈ N.ringOn ((q ⁻¹ᵁ U₀ : N.Z.Opens) : Set N.Z), τ x ∈ N.ringOn ((q ⁻¹ᵁ U₀ : N.Z.Opens) : Set N.Z) := by
  intro x hx
  obtain ⟨f, rfl⟩ := (RatModel.mem_ringOn_iff_exists hne).1 hx
  refine RatModel.mem_ringOn.2 fun z hz => ?_
  have hzU : q z ∈ U₀ := hz
  haveI := RatModel.isIntegrallyClosed_O hn z
  letI : Algebra Γ(M₁.Z, U₀) Γ(N.Z, q ⁻¹ᵁ U₀) := (q.app U₀).hom.toAlgebra
  have hi : IsIntegral Γ(M₁.Z, U₀) f := (IsFinite.finite_app q U₀ hU₀).to_isIntegral f
  have hmem : ∀ a : Γ(M₁.Z, U₀), φ.toRingHom (M₁.res U₀ ⟨_, hzU⟩ a) ∈ N.O z := fun a => by
    have e : φ.toRingHom (M₁.res U₀ ⟨_, hzU⟩ a) = φ (valF M₁.pt U₀ a) := congrArg φ (M₁.res_apply _ _ a)
    rw [e]
    exact hf.map_mem_O (z := z) (RatModel.valF_mem_O hzU a)
  let χ : Γ(M₁.Z, U₀) →+* N.O z :=
    RingHom.codRestrict (φ.toRingHom.comp (M₁.res U₀ ⟨_, hzU⟩)) (N.O z) hmem
  let ψ : Γ(N.Z, q ⁻¹ᵁ U₀) →+* Ω₂ := τ.toRingHom.comp (N.res (q ⁻¹ᵁ U₀) hne)
  have hc : (algebraMap (N.O z) Ω₂).comp χ = ψ.comp (algebraMap Γ(M₁.Z, U₀) Γ(N.Z, q ⁻¹ᵁ U₀)) := by
    ext a
    have e := hf.valF_app ⟨_, hzU⟩ a
    change φ (M₁.res U₀ ⟨_, hzU⟩ a) = τ (N.res (q ⁻¹ᵁ U₀) hne ((q.app U₀).hom a))
    calc φ (M₁.res U₀ ⟨_, hzU⟩ a) = φ (valF M₁.pt U₀ a) := congrArg φ (M₁.res_apply _ _ a)
      _ = τ (φ (valF M₁.pt U₀ a)) := (hτ _).symm
      _ = τ (valF N.pt (q ⁻¹ᵁ U₀) (q.app U₀ a)) := congrArg τ e.symm
      _ = τ (N.res (q ⁻¹ᵁ U₀) hne ((q.app U₀).hom a)) := congrArg τ (N.res_apply _ _ _).symm
  obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.1 (hi.map_of_comp_eq χ ψ hc)
  have e2 : ψ f = τ (valF N.pt (q ⁻¹ᵁ U₀) f) := congrArg τ (N.res_apply _ _ f)
  have e3 : τ (valF N.pt (q ⁻¹ᵁ U₀) f) = (w : Ω₂) := e2.symm.trans hw.symm
  rw [e3]
  exact w.2

theorem exists_isHom (hf : M₁.IsHom N φ q) (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N.Z) (τ : Ω₂ →ₐ[o] Ω₂)
    (hτ : ∀ a, τ (φ a) = φ a) : ∃ s : N.Z ⟶ N.Z, N.IsHom N τ s := by
  refine RatModel.exists_isHom_of_local fun z => ?_
  obtain ⟨U₀, hU₀, hz, -⟩ := exists_isAffineOpen_mem_and_subset (U := (⊤ : M₁.Z.Opens)) (x := q z) trivial
  exact ⟨q ⁻¹ᵁ U₀, q ⁻¹ᵁ U₀, hz, hU₀.preimage q, ⟨z, hz⟩, map_ringOn hf hn τ hτ hU₀ ⟨z, hz⟩⟩

end General

section Over

variable {o₁ Ω₁ o₂ Ω₂ : Type} [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂]
  [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] [Algebra o₁ Ω₂]

def overBase (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (q : M₂.Z ⟶ M₁.Z) [IsFinite q]
    (hq : M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt)
    (hA : algebraMap o₁ Ω₂ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)) : RatModel o₁ Ω₂ where
  Z := M₂.Z
  s := q ≫ M₁.s
  sep := by haveI := M₁.sep; infer_instance
  lft := by haveI := M₁.lft; infer_instance
  qc := by haveI := M₁.qc; infer_instance
  pt := M₂.pt
  pt_s := by
    rw [← Category.assoc, hq, Category.assoc, M₁.pt_s, hA]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  gen := M₂.gen
  onto := M₂.onto

def incl (hA : algebraMap o₁ Ω₂ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)) : Ω₁ →ₐ[o₁] Ω₂ :=
  { algebraMap Ω₁ Ω₂ with commutes' := fun r => by rw [hA]; rfl }

theorem autO_comm (hA : algebraMap o₁ Ω₂ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)) (σ : Ω₂ ≃ₐ[Ω₁] Ω₂)
    (r : o₁) : σ (algebraMap o₁ Ω₂ r) = algebraMap o₁ Ω₂ r := by
  rw [hA]
  exact σ.commutes (algebraMap o₁ Ω₁ r)

def autO (hA : algebraMap o₁ Ω₂ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)) (σ : Ω₂ ≃ₐ[Ω₁] Ω₂) :
    Ω₂ →ₐ[o₁] Ω₂ :=
  { (σ : Ω₂ →+* Ω₂) with commutes' := fun r => autO_comm hA σ r }

theorem autO_apply (hA : algebraMap o₁ Ω₂ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)) (σ : Ω₂ ≃ₐ[Ω₁] Ω₂)
    (x : Ω₂) : autO hA σ x = σ x := rfl

end Over

theorem autAct : ∀ (o₁ Ω₁ o₂ Ω₂ : Type) [CommRing o₁] [Field Ω₁] [Algebra o₁ Ω₁] [CommRing o₂] [Field Ω₂] [Algebra o₂ Ω₂] [Algebra Ω₁ Ω₂] (M₁ : RatModel o₁ Ω₁) (M₂ : RatModel o₂ Ω₂) (q : M₂.Z ⟶ M₁.Z), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₂.Z → IsFinite q → M₂.pt ≫ q = spMap (algebraMap Ω₁ Ω₂) ≫ M₁.pt → ∀ σ : Ω₂ ≃ₐ[Ω₁] Ω₂, ∃ s : M₂.Z ⟶ M₂.Z, M₂.pt ≫ s = spMap (σ : Ω₂ →+* Ω₂) ≫ M₂.pt ∧ s ≫ q = q ∧ ∀ (K : Type) [Field K] (y : Sp K ⟶ M₂.Z) (b : Ω₂), M₂.val (y ≫ s) b = M₂.val y (σ b) := by
  intro o₁ Ω₁ o₂ Ω₂ _ _ _ _ _ _ _ M₁ M₂ q hn hfin hq σ
  haveI := hfin
  letI : Algebra o₁ Ω₂ := ((algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁)).toAlgebra
  have hA : algebraMap o₁ Ω₂ = (algebraMap Ω₁ Ω₂).comp (algebraMap o₁ Ω₁) := rfl
  let N := overBase M₁ M₂ q hq hA
  haveI hfN : IsFinite (show N.Z ⟶ M₁.Z from q) := hfin
  have hqN : M₁.IsHom N (incl hA) q := hq
  have hnN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme N.Z := hn
  obtain ⟨s, hs⟩ := exists_isHom hqN hnN (autO hA σ) fun a => σ.commutes a
  obtain ⟨t, ht⟩ := exists_isHom hqN hnN (autO hA σ.symm) fun a => σ.symm.commutes a
  have hst : s ≫ t = 𝟙 N.Z := by
    have h1 := ht.comp hs
    have e : (autO hA σ).comp (autO hA σ.symm) = AlgHom.id o₁ Ω₂ := by
      ext x
      exact σ.apply_symm_apply x
    rw [e] at h1
    exact h1.unique (RatModel.isHom_id N)
  have hsq : s ≫ q = q := by
    have h1 := hqN.comp hs
    have e : (autO hA σ).comp (incl hA) = incl hA := by
      ext a
      exact σ.commutes a
    rw [e] at h1
    exact h1.unique hqN
  refine ⟨s, hs, hsq, fun K _ y b => ?_⟩
  let w : Sp K := IsLocalRing.closedPoint K
  have hts : ∀ z, t (s z) = z := fun z => by
    rw [← Scheme.Hom.comp_apply, hst]
    rfl
  by_cases hb : b ∈ N.O (s (y w))
  · exact hs.val_comp y w hb
  · have hb' : σ b ∉ N.O (y w) := by
      intro h
      apply hb
      have h2 := ht.map_mem_O (z := s (y w)) (x := σ b) (by
        have e : N.O (t (s (y w))) = N.O (y w) := congrArg N.O (hts (y w))
        rw [e]; exact h)
      simpa [autO_apply] using h2
    have e1 : M₂.val (y ≫ s) b = 0 := RatModel.val_of_notMem (M := N) (y := y ≫ s) w hb
    have e2 : M₂.val y (σ b) = 0 := RatModel.val_of_notMem (M := N) (y := y) w hb'
    rw [e1, e2]

end GlobalTheory.Poinc.GalAut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLambdaPolarisationSiegelObjectCharZeroFiel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.SiegelSqrtField
open MonObj GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.AbLaw GlobalTheory.SiegelSqrt GlobalTheory.SiegelPullComp GlobalTheory.SiegelRingChange

theorem exists_sqOf_of_dim (hL : Out.Laws) (h k : ℕ) (o : Type) [CommRing o] (ζ : o) (R : Type) [CommRing R]
    [Algebra ℚ R] [IsNoetherianRing R] (β : o →+* R) (c₀ : SiegPre h k ζ (spMap β))
    (hd : SmoothOfRelativeDimension h c₀.A.hom) (hc₀ : c₀.Principal) :
    ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (P : Out.PolAV (Sp R₁)) (φ : P.A.left ⟶ c₀.A.left),
      (Module.Finite R R₁ ∧ Algebra.Etale R R₁ ∧ Module.FaithfullyFlat R R₁) ∧
        SqOf P c₀ (spMap (algebraMap R R₁)) φ := by
  have h2 : IsUnit ((2 : ℕ) : R) := by
    have := (IsUnit.mk0 ((2 : ℕ) : ℚ) (by norm_num)).map (algebraMap ℚ R)
    rwa [map_natCast] at this
  obtain ⟨R', _, _, ⟨f₁, e₁, l₁⟩, H₁⟩ := _root_.GlobalTheory.TorsionCover.exists_torsion_basis_cover R c₀.A h 2 c₀.ab hd h2
  obtain ⟨c', m', hc'⟩ := pull_sieg (spMap ((algebraMap R R').comp β)) (spMap (algebraMap R R'))
    (SiegelRingChange.spMap_comp' _ _).symm c₀ hc₀
  have m'' := m'
  obtain ⟨φ', -, g', -⟩ := m''
  obtain ⟨i₀, hi₀⟩ := H₁ c'.A φ' g'
  letI : Algebra ℚ R' := ((algebraMap R R').comp (algebraMap ℚ R)).toAlgebra
  haveI : IsNoetherianRing R' := Algebra.FiniteType.isNoetherianRing R R'
  obtain ⟨R₁, _, _, ⟨f₂, e₂, l₂⟩, H₂⟩ := GlobalTheory.T.exists_symmetric_linearisation_square_diagonalBundle hL h k o ζ R' _ c' h i₀ hc'
  obtain ⟨c₁, m₁, hc₁⟩ := pull_sieg (spMap ((algebraMap R' R₁).comp ((algebraMap R R').comp β)))
    (spMap (algebraMap R' R₁)) (SiegelRingChange.spMap_comp' _ _).symm c' hc'
  have m₁' := m₁
  obtain ⟨φ₁, φ₂, g₁, sq₁, w₁, -⟩ := m₁'
  obtain ⟨i, hi, li⟩ := exists_pull_labels g₁ 2 i₀ hi₀
  letI : Algebra ℚ R₁ := ((algebraMap R' R₁).comp (algebraMap ℚ R')).toAlgebra
  haveI : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing R' R₁
  obtain ⟨u, j, huj⟩ := H₂ c₁.A φ₁ i _ g₁ hi rfl
  obtain ⟨p₁, p₂, p₃, p₄⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective _ c₁.A 2 c₁.ab (isUnit_two_sections R₁)
  have hψ : ∀ {T : Over (Sp R₁)} (x : T ⟶ c₁.A), x ≫ ((𝟙 c₁.A) ^ 2 : c₁.A ⟶ c₁.A) = x ^ 2 := fun x => by
    rw [MonObj.comp_pow, Category.comp_id]
  have two : ∀ a : Multiplicative (Fin (2 * h) → ZMod 2), a ^ 2 = 1 := fun a => by
    apply Multiplicative.toAdd.injective
    funext x
    simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply]
    generalize (Multiplicative.toAdd a x) = y
    revert y; decide
  have hD : (c'.diag.pull φ₁).IsLB := pull_isLB (diag_isLB c') _
  obtain ⟨M, hM, iM, sM⟩ := GlobalTheory.T.exists_descent_symmetric_linearised_bundle _ c₁.A c₁.A ((𝟙 c₁.A) ^ 2) _ i (lbPow (c'.diag.pull φ₁) 2)
    (GlobalTheory.isLB_lbPow hD 2) p₁ p₂ p₃ p₄ (fun a => by rw [hψ, ← map_pow, two, map_one])
    (fun K _ _ t => ⟨fun x => by rw [hψ]; exact (li K t).1 x, (li K t).2⟩) u j huj
  have iM' := (GlobalTheory.lbIso_lbPow (diag_iso sq₁ w₁) 2).trans (GlobalTheory.isLB_lbPow (diag_isLB c₁) 2) (GlobalTheory.isLB_lbPow hD 2)
    (pull_isLB hM _) iM
  have hd₁ : SmoothOfRelativeDimension h c₁.A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (g₁.comp g').1 hd
  obtain ⟨P, φ, hP⟩ := _root_.GlobalTheory.SymRoot.exists_polAV_sqOf hL h k o ζ R₁ _ c₁ M hc₁ hd₁ hM
    (_root_.GlobalTheory.LamOfDouble.lam_iso_of_pull_two hL h k o ζ R₁ _ c₁ M hc₁ hM iM') sM
  obtain ⟨ψ, hψ'⟩ := sqOf_of_pb hP (pb_comp m' m₁)
  letI : Algebra R R₁ := ((algebraMap R' R₁).comp (algebraMap R R')).toAlgebra
  haveI : IsScalarTower R R' R₁ := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨R₁, inferInstance, inferInstance, P, ψ,
    ⟨Module.Finite.trans R' R₁, Algebra.Etale.comp R R' R₁, Module.FaithfullyFlat.trans R R' R₁⟩, ?_⟩
  have e : spMap (algebraMap R R₁) = 𝟙 _ ≫ spMap (algebraMap R' R₁) ≫ spMap (algebraMap R R') := by
    rw [Category.id_comp, ← SiegelRingChange.spMap_comp']
  rw [e]; exact hψ'

end GlobalTheory.SiegelSqrtField
end

namespace GlobalTheory.SiegelSqrtField
open MonObj GlobalTheory.SiegelSqrt GlobalTheory.SiegelPullComp GlobalTheory.SiegelRingChange

theorem exists_sqrt_field : ∀ (h k : ℕ) (o : Type) [CommRing o] (ζ : o) (S : Scheme.{0}) (s : S ⟶ Sp o) (c : SiegPre h k ζ s), c.Principal →
    ∀ (K : Type) [Field K] [CharZero K] (f : Sp K ⟶ S), ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra K R₁),
      Module.Finite K R₁ ∧ Nontrivial R₁ ∧ ∃ (P : PolAV (Sp R₁)) (α : P.A.left ⟶ c.A.left) (α₂ : (G2 P.A).left ⟶ (G2 c.A).left),
        IsGrpPullback P.A c.A (spMap (algebraMap K R₁) ≫ f) α ∧ IsSquare α α₂ ∧ LBIso (abelian₂ P.A P.L) (c.P.pull α₂) := by
  intro h k o _ ζ S s c hc K _ _ f
  obtain ⟨β, hβ⟩ : ∃ β : o →+* K, f ≫ s = spMap β :=
    ⟨(Spec.preimage (f ≫ s)).hom, by simp [spMap]⟩
  obtain ⟨c₀, m₀, hc₀⟩ := pull_sieg (spMap β) f hβ c hc
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim K c₀.A c₀.ab
  let c₁ : SiegPre g 2 (0 : K) (spMap (RingHom.id K)) :=
    { A := c₀.A, ab := c₀.ab, P := c₀.P, isLB := c₀.isLB, rig₁ := c₀.rig₁, rig₂ := c₀.rig₂, symm := c₀.symm,
      lev := fun _ => 1, lev_add := fun _ _ => (mul_one 1).symm, lev_tors := fun _ => one_pow _,
      geom := fun k _ _ x β' z _ hz => absurd (hz.trans (map_zero β')) z.ne_zero }
  have hc₁ : c₁.Principal := hc₀
  obtain ⟨R₁, _, _, P, φ, ⟨hfin, -, hff⟩, hP⟩ :=
    exists_sqOf_of_dim GlobalTheory.allSixLaws.1 g 2 K 0 K (RingHom.id K) c₁ hg hc₁
  obtain ⟨χ, χ₂, hχ, hs, hw, -⟩ := m₀
  obtain ⟨hφ, -, φ₂, hs', hw'⟩ := hP
  have lam : (abelian₂ P.A P.L).IsLB := LB.isLB_linComb P.isLB _ _
  refine ⟨R₁, inferInstance, inferInstance, hfin, ?_, P, φ ≫ χ, φ₂ ≫ χ₂, hφ.comp hχ, ⟨?_, ?_⟩, ?_⟩
  · haveI := Module.FaithfullyFlat.lTensor_nontrivial K R₁ K
    exact (TensorProduct.lid K R₁).injective.nontrivial
  · rw [Category.assoc, hs.1, ← Category.assoc, hs'.1, Category.assoc]
  · rw [Category.assoc, hs.2, ← Category.assoc, hs'.2, Category.assoc]
  · exact (hw'.trans lam (pull_isLB c₀.isLB _) (pull_isLB (pull_isLB c.isLB _) _) (iso_pull φ₂ hw)).trans
      lam (pull_isLB (pull_isLB c.isLB _) _) (pull_isLB c.isLB _) (iso_pull_pull c.isLB χ₂ φ₂)

end GlobalTheory.SiegelSqrtField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeDecompositionOfIdeleApprox
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)

open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (finiteAdeleMap finiteCompletionMap finiteCompletionMap_coe finiteCompletionMap_mapsTo)

namespace GlobalTheory.LatDecomp

variable {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E]

theorem finiteAdeleMap_algebraMap (a : K) :
    finiteAdeleMap K E (algebraMap K (Af K) a) = algebraMap E (Af E) (algebraMap K E a) :=
  FiniteAdeleRing.ext _ fun w => finiteCompletionMap_coe K E w a

theorem finiteAdeleMap_integral {z : Af K} (hz : ∀ v, Valued.v (z v) ≤ 1) (w : HeightOneSpectrum (𝓞 E)) :
    (finiteAdeleMap K E z) w ∈ w.adicCompletionIntegers E :=
  finiteCompletionMap_mapsTo K E w ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hz _))

theorem algebraMap_integral (s : 𝓞 E) (w : HeightOneSpectrum (𝓞 E)) :
    (algebraMap E (Af E) (s : E)) w ∈ w.adicCompletionIntegers E := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, FiniteAdeleRing.algebraMap_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
  exact w.valuation_le_one s

theorem exists_nat_mul_integral (a : Af E) :
    ∃ d : ℕ, d ≠ 0 ∧ ∀ w, ((d : Af E) * a) w ∈ w.adicCompletionIntegers E := by
  obtain ⟨β, hβ0, hβ⟩ := GlobalTheory.Idele.exists_mul_integral (R := 𝓞 E) (K := E) a
  have hmem : ((Ideal.absNorm (Ideal.span {β}) : ℕ) : 𝓞 E) ∈ Ideal.span {β} := Ideal.absNorm_mem _
  obtain ⟨g0, hg0⟩ := Ideal.mem_span_singleton'.1 hmem
  refine ⟨Ideal.absNorm (Ideal.span {β}), ?_, fun w => ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hβ0
  · have e : ((Ideal.absNorm (Ideal.span {β}) : ℕ) : Af E) =
        algebraMap E (Af E) ((g0 : 𝓞 E) : E) * algebraMap E (Af E) (algebraMap (𝓞 E) E β) := by
      rw [← map_mul]
      have := congrArg (fun r : 𝓞 E => algebraMap E (Af E) (r : E)) hg0
      simp only [map_natCast] at this
      rw [← this]; push_cast; rfl
    rw [e, _root_.mul_assoc]
    exact mul_mem (algebraMap_integral g0 w) ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hβ w))

end GlobalTheory.LatDecomp

namespace GlobalTheory.LatDecomp

variable {E : Type} [Field E] [NumberField E]

theorem exists_nat_mul_good {c : Ideal (OF E)} (hc : c ≠ ⊥) (y : (Af E)ˣ) (e : E) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ z : Af E, (∀ w, z w ∈ w.adicCompletionIntegers E) →
      z * algebraMap E (Af E) ((N : E) * e) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c := by
  obtain ⟨d, hd0, hd⟩ := exists_nat_mul_integral (algebraMap E (Af E) e * ((y⁻¹ : (Af E)ˣ) : Af E))
  have hN : Ideal.absNorm c ≠ 0 := fun h => hc (Ideal.absNorm_eq_zero_iff.1 h)
  refine ⟨Ideal.absNorm c * d, Nat.mul_ne_zero hN hd0, fun z hz => ?_⟩
  have h := GlobalTheory.CMVal.PicFin.mul_mem_hatO (Ideal.absNorm_mem c)
    (y := z * ((d : Af E) * (algebraMap E (Af E) e * ((y⁻¹ : (Af E)ˣ) : Af E)))) (fun w => mul_mem (hz w) (hd w))
  have e1 : z * algebraMap E (Af E) (((Ideal.absNorm c * d : ℕ) : E) * e) * ((y⁻¹ : (Af E)ˣ) : Af E) =
      algebraMap E (Af E) (algebraMap (OF E) E ((Ideal.absNorm c : ℕ) : OF E)) *
        (z * ((d : Af E) * (algebraMap E (Af E) e * ((y⁻¹ : (Af E)ˣ) : Af E)))) := by
    simp only [map_mul, map_natCast, Nat.cast_mul]
    ring
  rw [e1]; exact h

end GlobalTheory.LatDecomp

namespace GlobalTheory.LatDecomp

theorem exists_decomp : ∀ (K : Type) [Field K] [NumberField K] (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E]
    (t : (Af K)ˣ) (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ → ∀ x x' : E,
    ((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * ((y⁻¹ : (Af E)ˣ) : Af E) ∈ hatO c →
    ∃ (m : ℕ) (b : Fin m → E) (a a' : Fin m → K), (∀ k (r : 𝓞 K), algebraMap K E (r : K) * b k ∈ lattice c y) ∧
      x' = ∑ k, algebraMap K E (a' k) * b k ∧ x - ∑ k, algebraMap K E (a k) * b k ∈ lattice c y ∧
      ∀ k (v : HeightOneSpectrum (𝓞 K)),
        Valued.v (((t : Af K) * algebraMap K (Af K) (a' k) - algebraMap K (Af K) (a k)) v) ≤ 1 := by
  intro K _ _ E _ _ _ _ t c y hc x x' hx
  haveI : Module.Finite K E := Module.Finite.of_restrictScalars_finite ℚ K E
  set B := Module.finBasis K E
  set yi : Af E := ((y⁻¹ : (Af E)ˣ) : Af E)
  choose N hN0 hN using fun k => exists_nat_mul_good hc y (B k)
  set b : Fin (Module.finrank K E) → E := fun k => (N k : E) * B k with hb
  set a' : Fin (Module.finrank K E) → K := fun k => B.repr x' k / (N k : K) with ha'
  have hNK : ∀ k, (N k : K) ≠ 0 := fun k => Nat.cast_ne_zero.2 (hN0 k)

  have happrox : ∀ z : Af K, ∃ a : K, ∀ v, Valued.v ((z - algebraMap K (Af K) a) v) ≤ 1 := fun z => by
    obtain ⟨a, u, hu, e⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat K 1 one_pos).1 z
    refine ⟨a, fun v => ?_⟩
    rw [e, one_smul, add_sub_cancel_left]
    exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hu v)
  choose a ha using fun k => happrox ((t : Af K) * algebraMap K (Af K) (a' k))
  have hx' : x' = ∑ k, algebraMap K E (a' k) * b k := by
    conv_lhs => rw [← B.sum_repr x']
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Algebra.smul_def, hb, ha']
    simp only
    rw [← _root_.mul_assoc, ← map_natCast (algebraMap K E), ← map_mul, div_mul_cancel₀ _ (hNK k)]
  refine ⟨Module.finrank K E, b, a, a', fun k r => ?_, hx', ?_, ha⟩
  ·
    have hr : IsIntegral ℤ (algebraMap K E (r : K)) := (RingOfIntegers.isIntegral_coe r).algebraMap
    have h := hN k (algebraMap E (Af E) ((⟨algebraMap K E (r : K), hr⟩ : 𝓞 E) : E))
      (algebraMap_integral ⟨algebraMap K E (r : K), hr⟩)
    rw [mem_lattice, map_mul]
    exact h
  ·
    have hT : (upIdele K E t : Af E) = finiteAdeleMap K E (t : Af K) := rfl
    have hkey : algebraMap E (Af E) (x - ∑ k, algebraMap K E (a k) * b k) * yi =
        -(((upIdele K E t : Af E) * algebraMap E (Af E) x' - algebraMap E (Af E) x) * yi) +
          ∑ k, finiteAdeleMap K E ((t : Af K) * algebraMap K (Af K) (a' k) - algebraMap K (Af K) (a k)) *
            algebraMap E (Af E) (b k) * yi := by
      have e2 : ∀ k, finiteAdeleMap K E ((t : Af K) * algebraMap K (Af K) (a' k) - algebraMap K (Af K) (a k)) *
            algebraMap E (Af E) (b k) * yi =
          finiteAdeleMap K E (t : Af K) * (algebraMap E (Af E) (algebraMap K E (a' k) * b k)) * yi -
            algebraMap E (Af E) (algebraMap K E (a k) * b k) * yi := fun k => by
        simp only [map_sub, map_mul, finiteAdeleMap_algebraMap]
        ring
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Finset.sum_congr rfl fun k _ => e2 k, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
        ← Finset.mul_sum, ← map_sum, ← map_sum, ← hx', hT, map_sub]
      ring
    rw [mem_lattice, hkey]
    refine add_mem (neg_mem hx) (Subring.sum_mem _ fun k _ => ?_)
    exact hN k _ (finiteAdeleMap_integral (ha k))

end GlobalTheory.LatDecomp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftGeometricGenericPointStalkOfFlat
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj
attribute [local instance] CategoryTheory.Hom.group
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelMod)
open MonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory

theorem lift_of_stalk_generic_flat : ∀ {X' W : Scheme.{0}} [IsIntegral X'] (h : W ⟶ X') [Flat h] (q : W)
    [IsDomain (W.presheaf.stalk q)] {V : Scheme.{0}} [Nonempty V] (ℓ : V ⟶ X') [IsOpenImmersion ℓ]
    (Ω : Type) [Field Ω] (y : Sp Ω ⟶ Spec (W.presheaf.stalk q)) (hy : ∀ x, (y x).asIdeal = ⊥), ∃ z : Sp Ω ⟶ V, y ≫ W.fromSpecStalk q ≫ h = z ≫ ℓ := by
  intro X' W _ h _ q _ V _ ℓ _ Ω _ y hy
  have hinj : Function.Injective (h.stalkMap q).hom := by
    letI := (h.stalkMap q).hom.toAlgebra
    haveI : Module.Flat (X'.presheaf.stalk (h q)) (W.presheaf.stalk q) := Flat.stalkMap h q
    haveI : IsLocalHom (algebraMap (X'.presheaf.stalk (h q)) (W.presheaf.stalk q)) :=
      (inferInstance : IsLocalHom (h.stalkMap q).hom)
    haveI : Module.FaithfullyFlat (X'.presheaf.stalk (h q)) (W.presheaf.stalk q) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact FaithfulSMul.algebraMap_injective _ _
  have hrange : Set.range (y ≫ W.fromSpecStalk q ≫ h) ⊆ Set.range ℓ := by
    rintro _ ⟨x, rfl⟩
    have key : (y ≫ W.fromSpecStalk q ≫ h) x =
        X'.fromSpecStalk (h q) (Spec.map (h.stalkMap q) (y x)) := by
      rw [← Scheme.SpecMap_stalkMap_fromSpecStalk]; rfl
    rw [key]
    set p : Spec (X'.presheaf.stalk (h q)) := Spec.map (h.stalkMap q) (y x) with hpdef
    have hp : p.asIdeal = ⊥ := by
      show Ideal.comap (h.stalkMap q).hom (y x).asIdeal = ⊥
      rw [hy x]
      exact Ideal.comap_bot_of_injective _ hinj
    obtain ⟨s, hs⟩ : genericPoint X' ∈ Set.range (X'.fromSpecStalk (h q)) := by
      rw [Scheme.range_fromSpecStalk]
      exact (genericPoint_spec X').specializes (Set.mem_univ _)
    have hps : p ⤳ s := (PrimeSpectrum.le_iff_specializes _ _).1 (by
      show p.asIdeal ≤ s.asIdeal
      rw [hp]; exact bot_le)
    have hgen : genericPoint X' ∈ Set.range ℓ :=
      ((genericPoint_spec X').mem_open_set_iff ℓ.isOpenEmbedding.isOpen_range).2
        (by simpa using Set.range_nonempty ℓ)
    have := (hps.map (X'.fromSpecStalk (h q)).continuous).mem_open
      ℓ.isOpenEmbedding.isOpen_range (by rw [hs]; exact hgen)
    exact this
  exact ⟨IsOpenImmersion.lift ℓ _ hrange, (IsOpenImmersion.lift_fac _ _ _).symm⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDvrLimitsCorrespondenceFiniteSndStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_dvr_limits_correspondence_finite_snd : ∀ (X Y₀ S : Scheme.{0}) (q : X ⟶ S) (U : X.Opens) (s₀ t₀ : Y₀ ⟶ X) (gt : Y₀ ⟶ U.toScheme), IsSeparated q → IsAffine S → s₀ ≫ q = t₀ ≫ q → gt ≫ U.ι = t₀ → IsFinite gt → ∀ z : X, z ∈ U → {u : X | ∃ (V K : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (_ : Field K) (_ : Algebra V K) (_ : IsFractionRing V K) (y' z' : Sp V ⟶ X) (x : Sp K ⟶ Y₀), spMap (algebraMap V K) ≫ y' = x ≫ s₀ ∧ spMap (algebraMap V K) ≫ z' = x ≫ t₀ ∧ y' (IsLocalRing.closedPoint V) = u ∧ z' (IsLocalRing.closedPoint V) = z}.Finite := by
  first | (exact @GlobalTheory.UPel.HT.ES.finite_dvr_limits_of_finite_snd) | (exact GlobalTheory.UPel.HT.ES.finite_dvr_limits_of_finite_snd) | (intros; apply GlobalTheory.UPel.HT.ES.finite_dvr_limits_of_finite_snd  <;> assumption)
end

