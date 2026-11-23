module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2277
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TraceFormTwistIsoOfPullback
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2318
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2288
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2275
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2273
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2196
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2165
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2146
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2173
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2174

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticLevelAfterFiniteExtensionBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumLevel

theorem exists_galois_root (K K' : Type) [Field K] [CharZero K] [Field K'] [Algebra K K'] [FiniteDimensional K K']
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra K E) (_ : FiniteDimensional K E) (_ : IsGalois K E) (j : K' →ₐ[K] E) (ζ : E),
      IsPrimitiveRoot ζ m := by
  let Ω := AlgebraicClosure K'
  haveI : CharZero K' := (algebraMap K K').charZero_iff (algebraMap K K').injective |>.1 inferInstance
  haveI : CharZero Ω := (algebraMap K' Ω).charZero_iff (algebraMap K' Ω).injective |>.1 inferInstance
  haveI : NeZero m := ⟨by omega⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  let K'' : IntermediateField K' Ω := IntermediateField.adjoin K' {ζ₀}
  haveI : FiniteDimensional K' K'' :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := K') ζ₀)
  haveI : FiniteDimensional K K'' := Module.Finite.trans K' K''
  haveI : IsScalarTower K K'' Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let E := IntermediateField.normalClosure K K'' Ω
  haveI : IsGalois K E := inferInstance
  haveI : FiniteDimensional K E := inferInstance
  let t : K'' →ₐ[K] E := (IsScalarTower.toAlgHom K K'' Ω).codRestrict _
    fun y => AlgHom.fieldRange_le_normalClosure _ ⟨y, rfl⟩
  have hz : ζ₀ ∈ K'' := IntermediateField.mem_adjoin_simple_self K' ζ₀
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, t.comp (IsScalarTower.toAlgHom K K' K''),
    t ⟨ζ₀, hz⟩, ?_⟩
  exact IsPrimitiveRoot.of_map_of_injective (f := E.val) (by exact hζ₀) Subtype.val_injective

end GlobalTheory.MumLevel

namespace GlobalTheory.MumLevel

def half (g : ℕ) (i : Fin (2 * g)) : Fin g ⊕ Fin g :=
  if h : (i : ℕ) < g then .inl ⟨i, h⟩ else .inr ⟨(i : ℕ) - g, by omega⟩

theorem omegaStd_single (g : ℕ) (a b : Fin g ⊕ Fin g) :
    omegaStd (Pi.single a (1 : ℤ)) (Pi.single b 1) =
      match a, b with
      | .inl p, .inr q => if p = q then 1 else 0
      | .inr p, .inl q => if p = q then -1 else 0
      | _, _ => 0 := by
  rcases a with p | p <;> rcases b with q | q <;>
    simp [omegaStd, Pi.single_apply, Finset.sum_ite_eq, Finset.sum_ite_eq', eq_comm] <;> split_ifs <;> simp

theorem stdSymp_eq (g : ℕ) (i j : Fin (2 * g)) :
    stdSymp g i j = omegaStd (Pi.single (half g i) (1 : ℤ)) (Pi.single (half g j) 1) := by
  rw [omegaStd_single]
  unfold half stdSymp
  by_cases hi : (i : ℕ) < g <;> by_cases hj : (j : ℕ) < g <;> simp only [hi, hj, dif_pos, dif_neg, not_false_eq_true, true_and, false_and, if_false]
  all_goals (try simp only [Fin.ext_iff, Fin.val_mk])
  all_goals (have := i.2; have := j.2; split_ifs <;> omega)

end GlobalTheory.MumLevel

namespace GlobalTheory.MumLevel

theorem exists_ring (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) (E : Type) [Field E]
    [Algebra (FractionRing R) E] [FiniteDimensional (FractionRing R) E] [IsGalois (FractionRing R) E] (ζ : E) (m : ℕ)
    (hm : 1 ≤ m) (hζ : IsPrimitiveRoot ζ m) :
    ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (e : E ≃+* FractionRing R₁)
      (ζ₁ : R₁ˣ), FinExt ρ ∧ (∀ r, e (algebraMap (FractionRing R) E (algebraMap R _ r)) = algebraMap R₁ _ (ρ r)) ∧
      e ζ = algebraMap R₁ _ ζ₁ ∧ IsPrimitiveRoot ζ₁ m := by
  letI : Algebra R E := (GalClosure.baseMap R E).toAlgebra
  haveI : IsScalarTower R (FractionRing R) E := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨hloc, hfe⟩ := GalClosure.finExt_integralClosure (E := E) hR
  set R₁ := integralClosure R E
  haveI : IsFractionRing R₁ E := integralClosure.isFractionRing_of_finite_extension (FractionRing R) E
  let e : E ≃+* FractionRing R₁ := (FractionRing.algEquiv R₁ E).symm.toRingEquiv
  have he : ∀ x : R₁, e (algebraMap R₁ E x) = algebraMap R₁ _ x := fun x => (FractionRing.algEquiv R₁ E).symm.commutes x
  have hint : IsIntegral R ζ := by
    refine ⟨Polynomial.X ^ m - 1, Polynomial.monic_X_pow_sub_C 1 (by omega), ?_⟩
    simp [hζ.pow_eq_one]
  let z : R₁ := ⟨ζ, hint⟩
  have hz : z ^ m = 1 := Subtype.ext (by simp [z, hζ.pow_eq_one])
  let ζ₁ : R₁ˣ := Units.ofPowEqOne z m hz (by omega)
  have hζ₁ : (ζ₁ : R₁) = z := Units.val_ofPowEqOne _ _ _ _
  refine ⟨R₁, inferInstance, inferInstance, hloc, algebraMap R R₁, e, ζ₁, hfe, fun r => ?_, ?_, ?_⟩
  · rw [← he]; rfl
  · rw [hζ₁, ← he]; rfl
  · refine IsPrimitiveRoot.coe_units_iff.1 ?_
    rw [hζ₁]
    exact IsPrimitiveRoot.of_map_of_injective (f := algebraMap R₁ E) (by exact hζ) Subtype.val_injective

end GlobalTheory.MumLevel

namespace GlobalTheory.MumLevel

theorem exists_level_finExt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (A : PolAV (Sp (FractionRing R))), (letI := A.isAb.comm; GlobalTheory.ZH.HypS A.A A.L) → ∀ m : ℕ, 1 ≤ m → IsUnit (m : R) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsDomain R₁) (_ : IsLocalRing R₁) (ρ : R →+* R₁) (A₁ : PolAV (Sp (FractionRing R₁))) (a : A₁.A.left ⟶ A.A.left) (ζ : R₁ˣ) (_ : ReciprocityTheory.ChartRestriction.G.Out.Level A₁ m (unitOn (Units.map (algebraMap R₁ (FractionRing R₁)).toMonoidHom ζ))), FinExt ρ ∧ IsFib ρ A A₁ a ∧ A₁.g = A.g ∧ (letI := A₁.isAb.comm; GlobalTheory.ZH.HypS A₁.A A₁.L) := by
  intro R _ _ _ hR A hS m hm _
  haveI : CharZero R := hR.2
  obtain ⟨K', _, _, hfin, H⟩ := LevelAfterExt.exists_ext_level (FractionRing R) A m hm
  haveI : FiniteDimensional (FractionRing R) K' := hfin
  obtain ⟨E, _, _, _, _, j, ζ, hζ⟩ := exists_galois_root (FractionRing R) K' m hm
  obtain ⟨R₁, _, _, _, ρ, e, ζ₁, hρ, he, -, hζ₁⟩ := exists_ring R hR E ζ m hm hζ
  let f : FractionRing R →+* FractionRing R₁ := ArcPull.fracMap hρ.2.1
  let i : K' →+* FractionRing R₁ := e.toRingHom.comp j.toRingHom
  have hf : i.comp (algebraMap (FractionRing R) K') = f := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors R) (RingHom.ext fun r => ?_)
    simp only [RingHom.comp_apply]
    show e (j (algebraMap _ K' _)) = _
    rw [j.commutes, he, ArcPull.fracMap_algebraMap]
  haveI : CharZero (FractionRing R₁) := f.charZero_iff f.injective |>.1 inferInstance
  obtain ⟨A₁, ψ, hA⟩ := exists_isPolFibre GlobalTheory.laws_without_cohomology.2.2.1 f A
  let ze : (FractionRing R₁)ˣ := Units.map (algebraMap R₁ (FractionRing R₁)).toMonoidHom ζ₁
  have hze : IsPrimitiveRoot (ze : FractionRing R₁) m :=
    IsPrimitiveRoot.coe_units_iff.2 (hζ₁.map_of_injective (Units.map_injective (IsFractionRing.injective R₁ _)))
  obtain ⟨lev, -, h₂, h₃⟩ := H (FractionRing R₁) i f hf A₁ ψ hA A₁.g rfl ze hze
  have hL := GlobalTheory.lawsAndExpansions.1.1
  have := A₁.isAb.comm
  have hM : (m : FractionRing R₁) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  let ek := (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R₁))).commRingCatIsoToRingEquiv.symm
  obtain ⟨L, -⟩ := exists_level_of_pairing hL.globalFns hL.weil hL.mulN _ A₁ m (unitOn ze)
    (ZH.RealDimOne.isPrimitiveRoot_unitOn (IsPrimitiveRoot.coe_units_iff.1 hze)) (fun F _ s => by
      have : Nontrivial Γ(Sp F, ⊤) :=
        (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.symm.injective.nontrivial
      refine ⟨fun e₀ => hM ?_, (ZH.RealDimOne.isPrimitiveRoot_unitOn (IsPrimitiveRoot.coe_units_iff.1 hze)).map_of_injective
        (Units.map_injective fun a b hab => ek.symm.injective ((s.appTop.hom.comp ek.toRingHom).injective (by simpa using hab)))⟩
      refine (s.appTop.hom.comp ek.toRingHom).injective ?_
      refine (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.injective ?_
      rw [map_natCast, map_natCast, map_zero, map_zero]
      exact e₀)
    (fun k => lev (Pi.single (half A₁.g k) 1)) (fun k => h₂ _) (fun k l => by
      rw [stdSymp_eq, ← ZH.RealDimOne.unitOn_zpow]
      exact h₃ _ _)
  refine ⟨R₁, inferInstance, inferInstance, inferInstance, ρ, A₁, ψ, ζ₁, L, hρ,
    ⟨f, fun r => ArcPull.fracMap_algebraMap hρ.2.1 r, hA.2.1, hA.2.2.symm⟩, hA.1, ?_⟩
  have := A.isAb.comm
  exact SymBaseChange.hypS_baseChange _ _ _ _ _ ψ _ _ A.isLB A₁.isLB hA.2.1 hA.2.2.symm hS

end GlobalTheory.MumLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorTorusPointOfComponentTuple
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor.VExist

theorem cube_corr {G U : Type} [CommGroup G] [CommGroup U] {θ : G → G → G → U} (h : IsCub θ) (a a' b b' p q : G) :
    θ b q a * θ b q p * θ a p (b * q) * (θ b' q a' * θ b' q p * θ a' p (b' * q)) * θ (a * b) (a' * b') (p * q) =
      θ a a' p * θ b b' q * θ a a' q * θ b b' p *
        (θ (b * b') q (a * a') * θ (b * b') q p * θ (a * a') p (b * b' * q)) := by
  have E := fun {x y : U} (e : x = y) => congrArg Additive.ofMul e
  have k0 := E (h.compat a b (a' * b') (p * q))
  have k1 := E (h.compat b b' q (a * a'))
  have k2 := E (h.compat a a' p (b * b' * q))
  have k3 := E (h.compat a' b' a (p * q))
  have k4 := E (h.compat a' b' b (p * q))
  have k5 := E (h.coc b b' q p)
  have k6 := E (h.coc b' q p b)
  have k7 := E (h.coc a' (b' * p * q) b a)
  have k8 := E (h.coc a a' q b)
  have k9 := E (h.coc a a' q b')
  have k10 := E (h.coc a' q b' a)
  have k11 := E (h.coc a (a' * q) b' b)
  have k12 := E (h.coc a a' b' b)
  have k13 := E (h.coc a' (b' * q) b a)
  have k14 := E (h.coc a' q b' b)
  have k15 := E (h.coc b (b' * q) p a)
  have k16 := E (h.coc b q p a)
  have k17 := E (h.coc b' q p a)
  have k18 := E (h.coc b (b' * q) p a')
  have k19 := E (h.coc a (p * q) b' a')
  have k20 := E (h.coc b (p * q) b' a')
  apply Additive.ofMul.injective
  simp only [ofMul_mul] at *
  simp only [mul_comm, mul_assoc, mul_left_comm, h.s01, h.s12] at *
  linear_combination (norm := abel) k0 - k1 - k2 + k3 + k4 - k5 - k6 + k7 - k8 - k9 - k10 - k11 + k12 - k13 - k14 - k15 + k16 - k17 - k18 + k19 + k20

end GlobalTheory.Mum.TensTor.VExist

namespace GlobalTheory.Mum.TensTor.VExist

theorem pair_mult {F : Type} [Field F] (N : NumD F) (gi gj : N.Gt) (ai aj ai' aj' : N.X) :
    gj.s (ai + ai') * gi.s (aj + aj') /
        (N.θ (N.c (aj + aj')) gj.b (N.c (ai + ai')) * N.θ (N.c (aj + aj')) gj.b gi.b *
          N.θ (N.c (ai + ai')) gi.b (N.c (aj + aj') * gj.b)) *
      (N.θ (N.c ai * N.c aj) (N.c ai' * N.c aj') (gi.b * gj.b) /
        (N.θ (N.c ai) (N.c ai') gi.b * N.θ (N.c aj) (N.c aj') gj.b)) =
    gj.s ai * gi.s aj / (N.θ (N.c aj) gj.b (N.c ai) * N.θ (N.c aj) gj.b gi.b * N.θ (N.c ai) gi.b (N.c aj * gj.b)) *
      (gj.s ai' * gi.s aj' /
        (N.θ (N.c aj') gj.b (N.c ai') * N.θ (N.c aj') gj.b gi.b * N.θ (N.c ai') gi.b (N.c aj' * gj.b))) := by
  have m₁ := congrArg Additive.ofMul (gj.mult ai ai')
  have m₂ := congrArg Additive.ofMul (gi.mult aj aj')
  have k := congrArg Additive.ofMul (cube_corr N.cub (N.c ai) (N.c ai') (N.c aj) (N.c aj') gi.b gj.b)
  rw [N.c_add, N.c_add]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div] at m₁ m₂ k ⊢
  linear_combination (norm := abel) m₁ + m₂ + k

theorem gtRelV_exists : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F),
    TensFacts W φ e wv → ∀ vs : Fin r → N.Gt, ∃ v' : N'.Gt, GtRelV W φ e wv v' vs := by
  intro F _ N N' r W φ e wv hT vs
  obtain ⟨-, hφb, he_add, -, hc, hw0, hθ, -⟩ := hT
  set b' := Function.surjInv hφb.2 (fun j => (vs j).b) with hb'def
  have hb' : ∀ j, φ b' j = (vs j).b := fun j => congrFun (Function.surjInv_eq hφb.2 _) j
  let U : N'.A → Fˣ := fun x => Units.mk0 (wv x) (hw0 x)
  let R : N'.X → Fˣ := fun χ' => ∏ i, ∏ j, ((vs j).s (e χ' i) * (vs i).s (e χ' j) /
          (N.θ (N.c (e χ' j)) (vs j).b (N.c (e χ' i)) * N.θ (N.c (e χ' j)) (vs j).b (vs i).b *
            N.θ (N.c (e χ' i)) (vs i).b (N.c (e χ' j) * (vs j).b))) ^ W i j
  let s' : N'.X → Fˣ := fun χ' => R χ' * U (N'.c χ' * b') * U 1 / (U (N'.c χ') * U b')
  have hmult : ∀ χ χ' : N'.X, s' (χ + χ') * N'.θ (N'.c χ) (N'.c χ') b' = s' χ * s' χ' := by
    intro χ χ'
    let P : Fˣ := ∏ i, ∏ j, (N.θ (N.c (e χ i) * N.c (e χ j)) (N.c (e χ' i) * N.c (e χ' j)) ((vs i).b * (vs j).b) /
        (N.θ (N.c (e χ i)) (N.c (e χ' i)) (vs i).b * N.θ (N.c (e χ j)) (N.c (e χ' j)) (vs j).b)) ^ W i j
    have hθu : N'.θ (N'.c χ) (N'.c χ') b' * U (N'.c χ * N'.c χ' * b') * U (N'.c χ) * U (N'.c χ') * U b' =
        P * U (N'.c χ * N'.c χ') * U (N'.c χ * b') * U (N'.c χ' * b') * U 1 := by
      have h := hθ (N'.c χ) (N'.c χ') b'
      simp only [hc, hb'] at h
      exact Units.ext (by simpa [U, P] using h)
    have hR : R (χ + χ') * P = R χ * R χ' := by
      simp only [R, P, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
      rw [← mul_zpow, ← mul_zpow, he_add, he_add, pair_mult]
    have a := congrArg Additive.ofMul hθu
    have b := congrArg Additive.ofMul hR
    simp only [s', N'.c_add]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div] at a b ⊢
    linear_combination (norm := abel) a + b
  refine ⟨⟨b', s', hmult⟩, hb', fun χ' => ?_⟩
  have h1 := hw0 (N'.c χ')
  have h2 := hw0 b'
  simp only [s', U, Units.val_div_eq_div_val, Units.val_mul, Units.val_mk0]
  field_simp
  simp only [R]
  ring

end GlobalTheory.Mum.TensTor.VExist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThickenedGroupEndomorphismTorusCoordinates
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Mum.EndThick

theorem exists_isCoordEnd {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    (a a' : D.P.A ⟶ D.P.A) [IsMonHom a] [IsMonHom a'] (h' : D.X →+ D.X)
    (hc : ∀ χ, D.c (h' χ) = D.c χ ≫ a') (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A a' a) rosatiε))
    (hu : u.IsGen)
    (h₀ : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L)) :
    ∃ F, IsCoordEnd g a a' h' u F := by
  let T := (Over.map (thick R I e)).obj (thickObj R I e G)
  have hcT : ∀ χ, DegPre.cT D T (h' χ) = DegPre.cT D T χ ≫ a' := fun χ => by
    simp only [DegPre.cT, hc, Category.assoc]
  have key : ∀ χ : D.X, ∃ s : LB.Gen (LB.LinComb D.P.L (DegPre.gtφT D T (g.pG ≫ a) χ) DegPre.gtε), s.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z) (J), Good D.P.L z J →
        val s r z J = val (g.t (h' χ)) r z J *
          val (LB.pullGen D.P.L _ _ u (lift (DegPre.cT D T χ) g.pG).left) r z J := by
    intro χ
    obtain ⟨s, hs, hv⟩ := exists_gen D.P.isLB (φ' := DegPre.gtφT D T (g.pG ≫ a) χ) (ε' := DegPre.gtε)
      (by
        intro U _ f
        refine (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 6) (U := U) _
          (c := (f (padd D.P.A g.pG (DegPre.cT D T (h' χ))).left)⁻¹ * f (DegPre.cT D T (h' χ)).left *
            f g.pG.left * (f (DegPre.zeroT D T).left)⁻¹) ?_
          (prod_ros a' a (DegPre.cT D T χ) g.pG f)).trans ?_
        · rw [Fin.prod_univ_four]
          show f _ ^ (-1 : ℤ) * f _ ^ (1 : ℤ) * f _ ^ (1 : ℤ) * f _ ^ (-1 : ℤ) = _
          simp only [zpow_neg, zpow_one]
          rfl
        · rw [Fin.prod_univ_four]
          show _ = f (padd D.P.A (DegPre.cT D T χ) (g.pG ≫ a)).left ^ (-1 : ℤ) * f (DegPre.cT D T χ).left ^ (1 : ℤ) *
            f (g.pG ≫ a).left ^ (1 : ℤ) * f (DegPre.zeroT D T).left ^ (-1 : ℤ)
          have p1 : padd D.P.A g.pG (DegPre.cT D T χ ≫ a') = (DegPre.cT D T χ ≫ a') * g.pG := mul_comm _ _
          have p2 : padd D.P.A (DegPre.cT D T χ) (g.pG ≫ a) = DegPre.cT D T χ * (g.pG ≫ a) := rfl
          rw [hcT χ, p1, p2]
          simp only [zpow_neg, zpow_one]
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_inv]
          abel)
      (LB.mulGen D.P.L _ _ _ _ (g.t (h' χ)) (LB.pullGen D.P.L _ _ u (lift (DegPre.cT D T χ) g.pG).left))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (g.t_gen _) (DVR.pullGen_isGen _ _ _ _ hu _))
    exact ⟨s, hs, fun Z r z J hJ => (hv Z r z J hJ).trans (val_mul hJ _ _ _)⟩

  choose s hs hv using key
  have vv : ∀ χ (y : T.left) J, Good D.P.L y J → val (s χ) (𝟙 _) y J =
      val (g.t (h' χ)) (𝟙 _) y J * val₂ u y J (DegPre.cT D T χ) g.pG := fun χ y J hJ => by
    rw [hv χ _ _ y J hJ, val_pull hJ, Category.id_comp]; rfl
  have hm : ∀ χ χ' (y : T.left) J, Good D.P.L y J → val (s (χ + χ')) (𝟙 _) y J *
      cubV D.cub y J (DegPre.cT D T χ) (DegPre.cT D T χ') (g.pG ≫ a) =
        val (s χ) (𝟙 _) y J * val (s χ') (𝟙 _) y J := fun χ χ' y J hJ => by
    have e1 : val (g.t (h' χ + h' χ')) (𝟙 _) y J *
        cubV D.cub y J (DegPre.cT D T χ ≫ a') (DegPre.cT D T χ' ≫ a') g.pG =
          val (g.t (h' χ)) (𝟙 _) y J * val (g.t (h' χ')) (𝟙 _) y J := by
      have := GlobalTheory.TorusCoord.val_t_mul g (𝟙 _) (h' χ) (h' χ') y J hJ
      rw [Category.id_comp] at this
      rw [← hcT, ← hcT]
      exact this
    have e2 := (ros_add D.cub GlobalTheory.globalFns_holds D.P.isAb a' a u hu h₀ hJ (DegPre.cT D T χ) (DegPre.cT D T χ')
      g.pG).1
    have hadd : DegPre.cT D T (χ + χ') = DegPre.cT D T χ * DegPre.cT D T χ' := DVR.cPoint_add D T χ χ'
    rw [vv _ y J hJ, vv _ y J hJ, vv _ y J hJ, map_add (f := _), hadd, _root_.mul_assoc, e2, ← _root_.mul_assoc, e1]
    exact mul_mul_mul_comm _ _ _ _
  have hcub : ∀ χ χ' (y : T.left) J, Good D.P.L y J →
      val (DegPre.cubAtT D T (DegPre.cT D T χ) (DegPre.cT D T χ') (g.pG ≫ a)) (𝟙 _) y J =
        cubV D.cub y J (DegPre.cT D T χ) (DegPre.cT D T χ') (g.pG ≫ a) := fun χ χ' y J hJ => by
    exact (val_cub D.cub (𝟙 T) hJ _ _ _).trans (by simp only [Category.id_comp])
  have hmult : ∀ χ χ' : D.X, LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (s (χ + χ')) (DegPre.cubAtT D T (DegPre.cT D T χ) (DegPre.cT D T χ') (g.pG ≫ a)))
      (LB.mulGen D.P.L _ _ _ _ (s χ) (s χ')) := fun χ χ' => corr_of_val D.P.isLB fun y J hJ => by
    exact (val_mul hJ _ _ _).trans ((congrArg₂ (· * ·) rfl (hcub χ χ' y J hJ)).trans
      ((hm χ χ' y J hJ).trans (val_mul hJ _ _ _).symm))
  have hzero : LB.Gen.Corr D.P.L _ _ _ _ (s 0) (LB.oneGen D.P.L) := corr_of_val D.P.isLB fun y J hJ => by
    have h := hm 0 0 y J hJ
    have c0 : DegPre.cT D T 0 = 1 := cPoint_zero T
    have c1 : cubV D.cub y J (DegPre.cT D T 0) (DegPre.cT D T 0) (g.pG ≫ a) = 1 := by
      rw [c0]
      exact (isCub_cubV D.cub hJ).face 1 _
    rw [c1, add_zero, _root_.mul_one] at h
    exact (mul_eq_left.1 h.symm).trans (val_one _).symm
  let ξ : GtPt D T := ⟨g.pG ≫ a, s, hs, hzero, hmult⟩
  obtain ⟨F, hF⟩ := (GlobalTheory.TorusCoord.toGtPt_bijective g (T := thickObj R I e G)).2 ξ
  have hP := (GlobalTheory.TorusCoord.toGtPt_eq_iff g F ξ).1 hF
  refine ⟨F, hP.1.symm, fun χ Z r z J hJ => ?_⟩
  exact (val_pull hJ _ _ _).symm.trans ((val_corr hJ (hP.2 χ) r).symm.trans (hv χ Z r z J hJ))

end GlobalTheory.Mum.EndThick
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransportGeneratorLbPowToAmpleBundleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_transport_generator_lbPow_to_ampleBundle : ∀ (S' Z : Scheme.{0}) (π : S' ⟶ Z) (M : LB Z) (L : LB S') (N : ℕ), M.IsLB → L.IsLB → LBIso (M.pull π) (lbPow L N) → ∃ T : ∀ (A : Scheme.{0}) (a : A ⟶ S'), LB.Gen (L.pull a) → LB.Gen (M.pull (a ≫ π)), (∀ (A : Scheme.{0}) (a : A ⟶ S') (e : LB.Gen (L.pull a)), e.IsGen → (T A a e).IsGen) ∧ ∀ (A A' Y : Scheme.{0}) (a : A ⟶ S') (a' : A' ⟶ S') (e : LB.Gen (L.pull a)) (e' : LB.Gen (L.pull a')) (r : Y ⟶ A) (r' : Y ⟶ A'), e.IsGen → e'.IsGen → r ≫ a = r' ≫ a' → (∀ (z : Y) (J : (Y ⟶ S') → L.ι), Good L z J → val (L := L) (φ := fun _ : PUnit => a) (ε := fun _ => 1) e r z J = val (L := L) (φ := fun _ : PUnit => a') (ε := fun _ => 1) e' r' z J) → ∀ (z : Y) (J : (Y ⟶ Z) → M.ι), Good M z J → val (L := M) (φ := fun _ : PUnit => a ≫ π) (ε := fun _ => 1) (T A a e) r z J = val (L := M) (φ := fun _ : PUnit => a' ≫ π) (ε := fun _ => 1) (T A' a' e') r' z J := by
  first | exact @GlobalTheory.GenTransport.transport | exact GlobalTheory.GenTransport.transport | (intros; apply GlobalTheory.GenTransport.transport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTransportedGeneratorDescendBijectiveAppStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_transported_generator_descend_bijective_app : ∀ {X X' Y Y' : Scheme.{0}} {K : Type} [Fintype K] {M : LB X} {L : LB X'} {F : X' ⟶ X} {w : LB.Iso L (M.pull F)}, PGen w → M.IsLB → L.IsLB → ∀ (π : Y' ⟶ Y), (∀ V : Y.Opens, Function.Bijective (π.app V).hom) → ∀ {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)}, (∀ k, φ' k ≫ F = π ≫ φ k) → ∀ {ε : K → ℤ} (a : LB.Gen (LB.LinComb L φ' ε)), a.IsGen → ∃ t : LB.Gen (LB.LinComb M φ ε), t.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (I : (Z ⟶ X) → M.ι) (J : (Z ⟶ X') → L.ι), Good M z I → Good L z J → val t (r ≫ π) z I = (∏ k, gw w (r ≫ φ' k) z (I ((r ≫ φ' k) ≫ F)) (J (r ≫ φ' k)) ^ ε k) * val a r z J := by
  first | exact @GlobalTheory.Mum.BijDescent.exists_descend_bij | exact GlobalTheory.Mum.BijDescent.exists_descend_bij | (intros; apply GlobalTheory.Mum.BijDescent.exists_descend_bij <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUdeep
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UPoinc.UDeepEx

theorem big_ge (g n : ℕ) (hn : 2 ≤ n) (B : ℕ) : ∃ k j₁ : ℕ, 2 ≤ k ∧ B ≤ (n ^ k) ^ 2 ∧ 1 ≤ j₁ ∧ ∀ j ≥ j₁,
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω),
      S.g = g → S.N = (n ^ k) ^ 2 → S.r = n ^ j → S.Big := by
  have lt : ∀ m : ℕ, m < n ^ m := fun m => Nat.lt_pow_self hn
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (1 + 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2))
  set K := max k₀ B with hK
  set N := (n ^ (K + 2)) ^ 2 with hN
  have hN₁ : K + 2 < N := (lt _).trans_le (Nat.le_self_pow two_ne_zero _)
  obtain ⟨j₀, hj₀⟩ := exists_nat_gt
    (2 * ((N ^ g * g.factorial : ℕ) : ℝ) * ((g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1)))
  refine ⟨K + 2, j₀ + 6 * (N ^ g * g.factorial) + 1, by omega, ?_, by omega, fun j hj o Ω _ _ _ S hg hS hr => ?_⟩
  · have : B ≤ K := le_max_right _ _
    omega
  have hj' := lt j
  unfold ThetaSys.Big
  rw [hg, hS, hr, ← hN]
  have hk₀K : k₀ ≤ K := le_max_left _ _
  refine ⟨hk₀.trans (by exact_mod_cast (by omega : k₀ < N)), ?_, ?_⟩
  · rw [Nat.cast_mul (n ^ j)]
    exact mul_lt_mul_of_pos_right (hj₀.trans (by exact_mod_cast (by omega : j₀ < n ^ j)))
      (by exact_mod_cast (by omega : 0 < N))
  · exact lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right _ (by omega))

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : Z ⟶ Y)
    {a' : Z ⟶ X} (e : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M j j rfl)
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame L _ (fun _ => a) _ j fun _ => e) h

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {cf : Coeff l} {C : UCompact Xo cf}

theorem exists_level (X₁ : USetup C) (K : ℕ) (hK : 0 < K) (hKu : IsUnit (K : X₁.o₁)) :
    ∃ (o₂ Ω₂ : Type) (_ : CommRing o₂) (_ : Field Ω₂) (_ : Algebra o₂ Ω₂) (_ : ArithBase o₂ Ω₂) (_ : Algebra X₁.Ω₁ Ω₂)
      (κ : X₁.o₁ →+* o₂), FiniteDimensional X₁.Ω₁ Ω₂ ∧ IsGalois X₁.Ω₁ Ω₂ ∧ κ.Finite ∧
      (algebraMap o₂ Ω₂).comp κ = (algebraMap X₁.Ω₁ Ω₂).comp (algebraMap X₁.o₁ X₁.Ω₁) ∧
      ∃ (R : Subalgebra o₂ Ω₂) (h : X₁.S.R →+* R) (P : PolAV (Sp R)) (ψ : P.A.left ⟶ X₁.ρ.P.A.left) (ze : o₂ˣ), R.FG ∧
        (∀ x : Ω₂, ∃ a ∈ R, ∃ b ∈ R, x = a / b) ∧ (∀ a, ((h a : R) : Ω₂) = algebraMap X₁.Ω₁ Ω₂ a) ∧ P.g = X₁.ρ.P.g ∧
        IsGrpPullback P.A X₁.ρ.P.A (spMap h) ψ ∧ LBIso P.L (X₁.ρ.P.L.pull ψ) ∧
        Nonempty (Out.Level P K (unitOn ((Units.map (algebraMap o₂ R : o₂ →* R)) ze))) := by
  haveI : CharZero X₁.Ω₁ := ArithBase.char X₁.o₁
  obtain ⟨Ω₂, _, _, Q, φ, ζ, hfd, hgal, hζ, hg, hpb, hlb, hlev⟩ := _root_.GlobalTheory.LevelGalois.exists_level_galois X₁.S.R.val.toRingHom X₁.ρ.P K hK
  obtain ⟨o₂, _, _, _, κ, ze, hfin, hcomp, hze⟩ := _root_.GlobalTheory.Poinc.exists_arithBase_rootOfUnity (o₁ := X₁.o₁) (Ω₁ := X₁.Ω₁) Ω₂ K ζ hK hζ
  have hKu₂ : IsUnit (K : o₂) := by simpa using hKu.map κ
  have hlev' : Nonempty (Out.Level Q K (unitOn (Units.map (algebraMap o₂ Ω₂ : o₂ →* Ω₂) ze))) := by rw [hze]; exact hlev
  obtain ⟨R, h, P, ψ, hR, hfr, hh, hPg, hPpb, hPlb, hPlev⟩ :=
    _root_.GlobalTheory.LevelSpread.level_spreads X₁.S.R X₁.ρ.P κ Q φ K ze X₁.S.fg X₁.S.frac hfd hcomp hKu₂ hg hpb hlb hlev'
  exact ⟨o₂, Ω₂, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, κ, hfd, hgal, hfin, hcomp,
    R, h, P, ψ, ze, hR, hfr, hh, hPg, hPpb, hPlb, hPlev⟩

end GlobalTheory.UPoinc.UDeepEx

namespace GlobalTheory.UPoinc.UDeepEx

end GlobalTheory.UPoinc.UDeepEx
end
end

