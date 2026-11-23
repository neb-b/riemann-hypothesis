module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.WinUpDown
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.PropEG
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ClosedHeckeCosets.IsClosedSmall
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0041
public import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHeckeCorrespondence
public import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHeckeLocal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PotOfFlag
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.NewformTwistNorms.PowEqOneOfKills
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.LocalEmbeddingNorms.SuppFacts
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1068
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0660

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.NotDih
section
open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Sd.EG GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.DirichletHecke
open GroundTheory.Automorphic.GodementSection (localChar coe_localChar)

private theorem loc_val (η : HeckeCharacter ℚ) (v : Ad3.Pl) (h : IsUnramifiedChar (localChar η v)) :
    ((localChar η v (unifUnit (Ad3.Qv v)) : ℂˣ) : ℂ) = (η (IdeleClassGroup.mk ℚ (IdeleGroup.finiteEmbedding v (uniformizer v))) : ℂ) := by
  have h1 : ord ((uniformizer v : (Ad3.Qv v)ˣ) : Ad3.Qv v) = 1 := by
    rw [Ad3P.DihedralUnramifiedPlaces.ord_eq v (Units.ne_zero _), valued_uniformizer, WithZero.log_exp, neg_neg]
  have hord : ord (((unifUnit (Ad3.Qv v)) * (uniformizer v)⁻¹ : (Ad3.Qv v)ˣ) : Ad3.Qv v) = 0 := by
    rw [ord_units_mul, ord_units_inv, h1, ord_unifUnit]
    norm_num
  have h2 := isUnramifiedChar_iff.1 h _ hord
  rw [map_mul, map_inv, mul_inv_eq_one] at h2
  rw [h2, coe_localChar, HeckeCharacter.localComponent_apply, HeckeCharacter.toIdele_apply]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.PotOfFlag
section
open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Sd

private theorem flag_exp {U : Type} [CommGroup U] (x y c : U) (a b : ℕ) (p q : ℤ) (ha : 0 < a) (hb : 0 < b)
    (hpq : p ≠ q + 1) (hinf : ∀ k : ℕ, k ≠ 0 → c ^ k ≠ 1)
    (hx : x ^ a = (c ^ p) ^ a) (hy : y ^ a = (c ^ q) ^ a) (h : x ^ b = (y * c) ^ b) : False := by
  have e : (x ^ a) ^ b = (y ^ a) ^ b * (c ^ a) ^ b := by
    rw [← pow_mul, ← pow_mul, ← pow_mul, ← mul_pow, mul_comm a b, pow_mul x b a, h, ← pow_mul, mul_comm b a,
      pow_mul (y * c) a b, mul_pow]
  rw [hx, hy] at e
  simp only [← zpow_natCast, ← zpow_mul] at e
  rw [← zpow_add] at e
  set m : ℤ := p * a * b - (q * a * b + a * b) with hm
  have h1 : c ^ m = 1 := by rw [hm, zpow_sub, e, mul_inv_cancel]
  have hm0 : m ≠ 0 := by
    have : m = (p - q - 1) * ((a : ℤ) * b) := by rw [hm]; ring
    rw [this]
    refine mul_ne_zero (by omega) (mul_ne_zero (by exact_mod_cast ha.ne') (by exact_mod_cast hb.ne'))
  apply hinf m.natAbs (Int.natAbs_ne_zero.mpr hm0)
  rcases Int.natAbs_eq m with hn | hn
  · rw [hn, zpow_natCast] at h1; exact h1
  · rw [hn, zpow_neg, zpow_natCast, inv_eq_one] at h1; exact h1

private theorem pow_fix {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [Algebra ℚ Ω] [IsScalarTower ℚ F Ω]
    (σ : G ℚ Ω) : ∃ n : ℕ, 0 < n ∧ ∀ x : F, (σ ^ n) (algebraMap F Ω x) = algebraMap F Ω x := by
  let ι : F →ₐ[ℚ] Ω := IsScalarTower.toAlgHom ℚ F Ω
  let f : ℕ → (F →ₐ[ℚ] Ω) := fun k => (((σ : Ω ≃ₐ[ℚ] Ω) ^ k : Ω ≃ₐ[ℚ] Ω) : Ω →ₐ[ℚ] Ω).comp ι
  have key : ∀ i j : ℕ, i < j → f i = f j →
      ∃ n : ℕ, 0 < n ∧ ∀ x : F, (σ ^ n) (algebraMap F Ω x) = algebraMap F Ω x := by
    intro i j hlt he
    refine ⟨j - i, by omega, fun x => ?_⟩
    have hx : ((σ : Ω ≃ₐ[ℚ] Ω) ^ i) (algebraMap F Ω x) = ((σ : Ω ≃ₐ[ℚ] Ω) ^ j) (algebraMap F Ω x) :=
      congrArg (fun φ : F →ₐ[ℚ] Ω => φ x) he
    apply ((σ : Ω ≃ₐ[ℚ] Ω) ^ i).injective
    show ((σ : Ω ≃ₐ[ℚ] Ω) ^ i) (((σ : Ω ≃ₐ[ℚ] Ω) ^ (j - i)) (algebraMap F Ω x)) = _
    rw [← AlgEquiv.mul_apply, ← pow_add, Nat.add_sub_cancel' hlt.le]
    exact hx.symm
  obtain ⟨i, j, hij, he⟩ := Finite.exists_ne_map_eq_of_infinite f
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact key i j hlt he
  · exact key j i hlt he.symm

private theorem cyc_inf_over (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (l : ℕ) [hl : Fact l.Prime] (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) :
    ∃ s ∈ Ine (F := F) A, ∀ k : ℕ, k ≠ 0 → cycBar F Ω l s ^ k ≠ 1 := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsAlgClosure ℚ Ω := ⟨IsAlgClosure.isAlgClosed F, Algebra.IsAlgebraic.trans ℚ F Ω⟩
  have hl2 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hnorm : ‖((1 + l : ℕ) : ℤ_[l])‖ = 1 := by
    push_cast
    have hne : ‖(1 : ℤ_[l])‖ ≠ ‖(l : ℤ_[l])‖ := by
      rw [norm_one, PadicInt.norm_p]
      exact ne_of_gt (inv_lt_one_of_one_lt₀ hl2)
    rw [PadicInt.norm_add_eq_max_of_ne hne, norm_one, PadicInt.norm_p]
    exact max_eq_left (inv_lt_one_of_one_lt₀ hl2).le
  let u : ℤ_[l]ˣ := (PadicInt.isUnit_iff.mpr hnorm).unit
  obtain ⟨σ, hσ, hσu⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA u
  obtain ⟨n, hn, hfix⟩ := pow_fix (F := F) σ
  let s : G F Ω := AlgEquiv.ofRingEquiv (f := ((σ ^ n : G ℚ Ω) : Ω ≃ₐ[ℚ] Ω).toRingEquiv) hfix
  have hσn : σ ^ n ∈ Ine (F := ℚ) A := Subgroup.pow_mem _ hσ n
  refine ⟨s, ⟨hσn.1, hσn.2⟩, ?_⟩
  intro k hk h1
  have hr : cycZ F Ω l s = u ^ n := by
    rw [← hσu, ← map_pow]
    show cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G F Ω) Ω s) =
      cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω (σ ^ n))
    congr 1
  have h2 : cycBar F Ω l s = Units.map (((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom :
      ℤ_[l] →+* Qbar l) : ℤ_[l] →* Qbar l) (u ^ n) := by
    show Units.map _ (cycZ F Ω l s) = _
    rw [hr]
    rfl
  rw [h2, ← map_pow, ← pow_mul] at h1
  have h3 := congrArg Units.val h1
  rw [Units.coe_map, Units.val_one] at h3
  have hinj : Function.Injective ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom) :=
    (algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective
  have h4 : ((u ^ (n * k) : ℤ_[l]ˣ) : ℤ_[l]) = 1 := hinj (by rw [map_one]; exact h3)
  rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, ← Nat.cast_pow] at h4
  have h5 : (1 + l) ^ (n * k) = 1 := by exact_mod_cast h4
  have h6 : 1 < (1 + l) ^ (n * k) :=
    Nat.one_lt_pow (Nat.mul_ne_zero hn.ne' hk) (by have := hl.out.one_lt; omega)
  omega

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.potOfFlag :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.PotOfFlag := by
  intro F Ω _ _ _ _ _ l _ n r m hm v hv H A hA
  obtain ⟨κ, a, ha, hflag, hκ⟩ := H A hA
  refine ⟨κ, hflag, fun i j b hb h => ?_⟩
  have hAl : A.valuation (l : Ω) < 1 := by
    have h1 := (hA ((l : ℕ) : 𝓞 F)).2 hv
    simpa only [map_natCast] using h1
  obtain ⟨s, hs, hinf⟩ := cyc_inf_over F Ω l A hAl
  let t : ↥(Dec (F := F) A) := ⟨s, Ine_le_Dec A hs⟩
  have h1 : κ i t ^ b = (κ j t * cycBar F Ω l s) ^ b := DFunLike.congr_fun h t
  exact flag_exp (κ i t) (κ j t) (cycBar F Ω l s) a b (m i) (m j) ha hb (hm i j) hinf (hκ i t hs) (hκ j t hs) h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.SphUnl
section
open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.LocGL ValuativeRel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem val_unif (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    valuation k (unif k : k) = uniformizer k := by
  obtain ⟨p, hp⟩ := valuation_surjective (uniformizer k : ValueGroupWithZero k)
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [map_zero] at hp
    exact uniformizer_ne_zero hp.symm
  have h := Classical.epsilon_spec (p := fun p : kˣ => valuation k (p : k) < 1 ∧
    ∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k (p : k))
    ⟨Units.mk0 p hp0, by rw [Units.val_mk0, hp]; exact uniformizer_lt_one,
      fun x hx => by rw [Units.val_mk0, hp]; exact le_uniformizer_iff.2 hx⟩
  exact le_antisymm (le_uniformizer_iff.2 h.1) (hp ▸ h.2 p (hp ▸ uniformizer_lt_one))

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.sphUnl :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.SphUnl := by
  intro K _ _ _ n hn π v B hB
  obtain ⟨⟨s₀, hs₀⟩, huniq, htor, hunr, -⟩ := suppFacts K n hn π v
  refine ⟨(htor s₀ hs₀).1.2 fun y hy => ?_, fun s hs => ?_⟩
  · obtain ⟨μ, hμ, rfl⟩ := hunr s₀ B hs₀ hB y hy
    rfl
  · obtain ⟨σ, hσ, -⟩ := id hs
    obtain ⟨α, hα, hS⟩ := GlobalTheory.LFun.SphComp.hasSatake_of_isLocComp π ((CG.hasSat_mk π v B).1 hB) hσ
    haveI : CharZero (v.adicCompletion K) := charZero_of_injective_algebraMap (algebraMap K _).injective
    have h := GlobalTheory.LocLanglands.hasSupport_of_isSubquotient_prinSeries (v.adicCompletion K) n (fun i => unrChar _ (α i))
      (fun i => isSmoothChar_of_isUnram (isUnram_unrChar _ (α i))) ⟨σ.V, σ.ρ, σ.smooth, σ.irred⟩ hS.2.2
    have key : ∀ ξ ∈ chars s, ξ (unif _) ∈ B := by
      rintro ξ ⟨hξ, hm⟩
      rw [huniq s _ hs ⟨σ, hσ, h⟩] at hm
      obtain ⟨i, hi, e⟩ := Multiset.mem_map.1 hm
      rw [← IrrGL.ofChar_inj.1 e, unrChar_uniformizer _ _ (val_unif _), ← hα]
      exact Multiset.mem_map_of_mem _ hi
    intro ξ hξ ξ' hξ' _ e
    refine UpperTheory.ConvolutionTheory.Sph.unlinked K n hn π v B hB _ (key ξ hξ) _ (key ξ' hξ') ?_
    rw [← e, MonoidHom.mul_apply, MonoidHom.inv_apply, ← Units.val_mul, inv_mul_cancel_right]
end

