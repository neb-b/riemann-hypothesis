module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2149
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2183
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0040
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniformisationOfPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1291

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonPullbackFractionFieldFiniteLocalExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.CommonCover

theorem exists_cover_field (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) (K' : Type) [Field K']
    (io : FractionRing R →+* K') (hfin : io.Finite) :
    ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (τ : K' →+* FractionRing R'),
      FinExt ρ ∧ IsLocalHom ρ ∧ τ.comp (io.comp (algebraMap R (FractionRing R))) = (algebraMap R' (FractionRing R')).comp ρ := by
  obtain ⟨⟨hN, -, hIC, hC⟩, hc0⟩ := hR
  letI : Algebra (FractionRing R) K' := io.toAlgebra
  letI : Algebra R K' := (io.comp (algebraMap R (FractionRing R))).toAlgebra
  haveI : IsScalarTower R (FractionRing R) K' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional (FractionRing R) K' := hfin
  haveI : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R _)
  haveI : Algebra.IsSeparable (FractionRing R) K' := inferInstance
  let C := integralClosure R K'
  haveI : Module.Finite R C := IsIntegralClosure.finite R (FractionRing R) K' C
  haveI : IsFractionRing C K' := integralClosure.isFractionRing_of_finite_extension (FractionRing R) K'
  have hφ : Function.Injective (algebraMap R C) := fun a b h => by
    have h' : io (algebraMap R (FractionRing R) a) = io (algebraMap R (FractionRing R) b) := congrArg Subtype.val h
    exact IsFractionRing.injective R (FractionRing R) (io.injective h')
  obtain ⟨R', _, _, _, ρ, σ, hCN, hρ, hfin', hloc, hσ⟩ :=
    GlobalTheory.LocExt.exists_isCN_cover_of_finite R C (algebraMap R C) ⟨hN, hIC, hC, hc0⟩ hφ (RingHom.finite_algebraMap.2 inferInstance)
  have hσi : Function.Injective σ := by
    refine (RingHom.injective_iff_ker_eq_bot σ).2 (Ideal.eq_bot_of_comap_eq_bot (R := R) ?_)
    change (RingHom.ker σ).comap (algebraMap R C) = ⊥
    rw [RingHom.comap_ker, hσ]
    exact (RingHom.injective_iff_ker_eq_bot ρ).1 hρ
  have hg : Function.Injective ((algebraMap R' (FractionRing R')).comp σ) :=
    (IsFractionRing.injective R' (FractionRing R')).comp hσi
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, IsFractionRing.lift (A := C) hg,
    ⟨⟨hCN.1, inferInstance, hCN.2.1, hCN.2.2.1⟩, hρ, hfin'⟩, hloc, ?_⟩
  ext r
  have e : io (algebraMap R (FractionRing R) r) = algebraMap C K' (algebraMap R C r) := rfl
  simp only [RingHom.comp_apply]
  rw [e, IsFractionRing.lift_algebraMap, RingHom.comp_apply, ← RingHom.comp_apply σ, hσ]

theorem exists_common_pull : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ D₂ : DegPre R) (E₁ E₂ : DegPre (FractionRing R)), IsPullDeg (algebraMap R (FractionRing R)) D₁ E₁ → IsPullDeg (algebraMap R (FractionRing R)) D₂ E₂ → ∀ (K' : Type) [Field K'] (io : FractionRing R →+* K') (E₃ : DegPre K'), io.Finite → IsPullDeg io E₁ E₃ → IsPullDeg io E₂ E₃ → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (E : DegPre (FractionRing R')), FinExt ρ ∧ IsLocalHom ρ ∧ Nonempty (IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₁ E) ∧ Nonempty (IsPullDeg ((algebraMap R' (FractionRing R')).comp ρ) D₂ E) := by
  intro R _ _ _ hR D₁ D₂ E₁ E₂ p₁ p₂ K' _ io E₃ hfin q₁ q₂
  obtain ⟨R', _, _, _, ρ, τ, hE, hloc, hτ⟩ := exists_cover_field R hR K' io hfin
  obtain ⟨hL, -⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨E, t, -⟩ := GlobalTheory.DegPull.exists_isPullDeg hL.polBaseChange K' (FractionRing R') τ E₃ ⊤
    (GlobalTheory.FieldPull.nonempty_psiOn_field E₃) trivial
  have ha : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective R _
  have hio : Function.Injective (io.comp (algebraMap R (FractionRing R))) := io.injective.comp ha
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, E, hE, hloc, ?_, ?_⟩
  · obtain ⟨a⟩ := GlobalTheory.PullDegComp.nonempty_isPullDeg_comp ha io.injective p₁ q₁
    rw [← hτ]
    exact GlobalTheory.PullDegComp.nonempty_isPullDeg_comp hio τ.injective a t
  · obtain ⟨a⟩ := GlobalTheory.PullDegComp.nonempty_isPullDeg_comp ha io.injective p₂ q₂
    rw [← hτ]
    exact GlobalTheory.PullDegComp.nonempty_isPullDeg_comp hio τ.injective a t

end GlobalTheory.CommonCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatibleMapsModPowMaximalIdealBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem exists_maximalIdeal_pow_le_map_maximalIdeal (R : Type) [CommRing R] [IsLocalRing R]
    (R' : Type) [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R'] [Algebra R R']
    [Module.Finite R R'] :
    ∃ N : ℕ, maximalIdeal R' ^ N ≤ (maximalIdeal R).map (algebraMap R R') := by
  have hrad : maximalIdeal R' ≤ ((maximalIdeal R).map (algebraMap R R')).radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro P ⟨hIP, hP⟩
    haveI := hP
    have hc : P.comap (algebraMap R R') = maximalIdeal R := by
      apply le_antisymm
      · exact IsLocalRing.le_maximalIdeal (Ideal.IsPrime.comap (algebraMap R R')).ne_top
      · exact Ideal.map_le_iff_le_comap.1 hIP
    have hmax : P.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := R) P (by
        change (P.comap (algebraMap R R')).IsMaximal
        rw [hc]; infer_instance)
    exact (IsLocalRing.eq_maximalIdeal hmax).ge
  obtain ⟨n, hn⟩ := Ideal.exists_radical_pow_le_of_fg _
    (IsNoetherian.noetherian ((maximalIdeal R).map (algebraMap R R')).radical)
  exact ⟨n, (Ideal.pow_right_mono hrad n).trans hn⟩

theorem exists_compatible_maps_mod_pow_maximalIdeal_base : ∀ (R : Type) [CommRing R] [IsLocalRing R] (R' : Type) [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R'] [Algebra R R'] [Module.Finite R R'] (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] (Γ : Type) (actC : Γ → (C' ≃ₐ[R] C')) (O : Type) [CommRing O] [Algebra R O] (i' : ∀ e : ℕ, O →ₐ[R] C' ⧸ (maximalIdeal R' ^ (e + 1)).map (algebraMap R' C')), (∀ e x y, Ideal.Quotient.mk _ y = i' (e + 1) x → Ideal.Quotient.mk _ y = i' e x) → (∀ e σ x y, Ideal.Quotient.mk _ y = i' e x → Ideal.Quotient.mk _ (actC σ y) = i' e x) → (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i' e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i' e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (maximalIdeal R' ^ (e + 1)).map (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R O R')) → ∃ i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C'), (∀ e x y, Ideal.Quotient.mk _ y = i (e + 1) x → Ideal.Quotient.mk _ y = i e x) ∧ (∀ e σ x y, Ideal.Quotient.mk _ y = i e x → Ideal.Quotient.mk _ (actC σ y) = i e x) ∧ (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (maximalIdeal R ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))) := by
  intro R _ _ R' _ _ _ _ _ C' _ _ _ _ Γ actC O _ _ i' hcomp hinv hsk
  obtain ⟨N, hN⟩ := exists_maximalIdeal_pow_le_map_maximalIdeal R R'
  have hR' : ∀ e : ℕ, maximalIdeal R' ^ (N * (e + 1) + 1) ≤
      (maximalIdeal R ^ (e + 1)).map (algebraMap R R') := by
    intro e
    calc maximalIdeal R' ^ (N * (e + 1) + 1) ≤ maximalIdeal R' ^ (N * (e + 1)) :=
          Ideal.pow_le_pow_right (Nat.le_succ _)
      _ = (maximalIdeal R' ^ N) ^ (e + 1) := pow_mul _ _ _
      _ ≤ ((maximalIdeal R).map (algebraMap R R')) ^ (e + 1) := Ideal.pow_right_mono hN _
      _ = _ := (Ideal.map_pow _ _ _).symm
  have hle : ∀ e : ℕ, (maximalIdeal R' ^ (N * (e + 1) + 1)).map (algebraMap R' C') ≤
      (maximalIdeal R ^ (e + 1)).map (algebraMap R C') := by
    intro e
    rw [Ideal.map_le_iff_le_comap]
    refine (hR' e).trans ?_
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    simp only [Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact Ideal.mem_map_of_mem _ hr
  have hJ : ∀ e : ℕ, (maximalIdeal R ^ (e + 1 + 1)).map (algebraMap R C') ≤
      (maximalIdeal R ^ (e + 1)).map (algebraMap R C') :=
    fun e => Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ _))
  have hiter : ∀ a b : ℕ, a ≤ b → ∀ x y,
      Ideal.Quotient.mk ((maximalIdeal R' ^ (b + 1)).map (algebraMap R' C')) y = i' b x →
      Ideal.Quotient.mk ((maximalIdeal R' ^ (a + 1)).map (algebraMap R' C')) y = i' a x := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => exact fun x y h => h
    | succ b _ ih => exact fun x y h => ih x y (hcomp b x y h)
  let i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C') :=
    fun e => (Ideal.Quotient.factorₐ R (hle e)).comp (i' (N * (e + 1)))
  have hi : ∀ e x, i e x = Ideal.Quotient.factorₐ R (hle e) (i' (N * (e + 1)) x) :=
    fun _ _ => rfl
  have hlift : ∀ e x y, Ideal.Quotient.mk ((maximalIdeal R ^ (e + 1)).map (algebraMap R C')) y
      = i e x → ∃ y', Ideal.Quotient.mk ((maximalIdeal R' ^ (N * (e + 1) + 1)).map
        (algebraMap R' C')) y' = i' (N * (e + 1)) x ∧
        y - y' ∈ (maximalIdeal R ^ (e + 1)).map (algebraMap R C') := by
    intro e x y h
    obtain ⟨y', hy'⟩ := Ideal.Quotient.mk_surjective (i' (N * (e + 1)) x)
    refine ⟨y', hy', ?_⟩
    rw [← Ideal.Quotient.eq, h, hi, ← hy', Ideal.Quotient.factorₐ_apply_mk]
  refine ⟨i, ?_, ?_, ?_⟩
  · intro e x y h
    obtain ⟨y', hy', hd⟩ := hlift (e + 1) x y h
    have h2 := hiter (N * (e + 1)) (N * (e + 1 + 1)) (Nat.mul_le_mul_left _ (Nat.le_succ _)) x y' hy'
    rw [Ideal.Quotient.eq.2 (hJ e hd), hi, ← h2, Ideal.Quotient.factorₐ_apply_mk]
  · intro e σ x y h
    obtain ⟨y', hy', hd⟩ := hlift e x y h
    have hst : (maximalIdeal R ^ (e + 1)).map (algebraMap R C') ≤
        ((maximalIdeal R ^ (e + 1)).map (algebraMap R C')).comap (actC σ) := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      simp only [Ideal.mem_comap, AlgEquiv.commutes]
      exact Ideal.mem_map_of_mem _ hr
    have hσ : actC σ y - actC σ y' ∈ (maximalIdeal R ^ (e + 1)).map (algebraMap R C') := by
      rw [← map_sub]; exact hst hd
    rw [Ideal.Quotient.eq.2 hσ, hi, ← hinv (N * (e + 1)) σ x y' hy', Ideal.Quotient.factorₐ_apply_mk]
  · intro e
    obtain ⟨hsur, hker⟩ := hsk (N * (e + 1))
    set L' := Algebra.TensorProduct.lift (i' (N * (e + 1)))
      ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _
      with hL'
    have hfac : Algebra.TensorProduct.lift (i e)
        ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) (fun _ _ => Commute.all _ _)
        = (Ideal.Quotient.factorₐ R (hle e)).comp L' := by
      apply Algebra.TensorProduct.ext'
      intro a b
      rw [AlgHom.comp_apply, hL', Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul,
        map_mul, hi]
      congr 1
    rw [hfac]
    refine ⟨?_, ?_⟩
    · intro z
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
      obtain ⟨t, ht⟩ := hsur (Ideal.Quotient.mk _ c)
      exact ⟨t, by simp [ht, Ideal.Quotient.factorₐ_apply_mk]⟩
    apply le_antisymm
    · intro t ht
      rw [RingHom.mem_ker, AlgHom.comp_apply] at ht
      obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (L' t)
      have hcJ : c ∈ (maximalIdeal R ^ (e + 1)).map (algebraMap R C') := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.factorₐ_apply_mk R (hle e), hc]
        exact ht
      have hsub : (maximalIdeal R ^ (e + 1)).map (algebraMap R C') ≤
          (((maximalIdeal R ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))).map L').comap
            (Ideal.Quotient.mk ((maximalIdeal R' ^ (N * (e + 1) + 1)).map (algebraMap R' C'))) := by
        rw [Ideal.map_le_iff_le_comap]
        intro r hr
        simp only [Ideal.mem_comap, Ideal.Quotient.mk_algebraMap]
        rw [← AlgHom.commutes L' r]
        exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hr)
      have hmem := hsub hcJ
      rw [Ideal.mem_comap, hc] at hmem
      obtain ⟨t', ht'K, ht'⟩ := (Ideal.mem_map_iff_of_surjective L' hsur).1 hmem
      have hdiff : t - t' ∈ RingHom.ker L' := by
        rw [RingHom.mem_ker, map_sub, ht', sub_self]
      rw [hker] at hdiff
      have hKK : (maximalIdeal R' ^ (N * (e + 1) + 1)).map
          (Algebra.TensorProduct.includeRight : R' →ₐ[R] TensorProduct R O R') ≤
          (maximalIdeal R ^ (e + 1)).map (algebraMap R (TensorProduct R O R')) := by
        rw [Ideal.map_le_iff_le_comap]
        refine (hR' e).trans ?_
        rw [Ideal.map_le_iff_le_comap]
        intro r hr
        simp only [Ideal.mem_comap, AlgHom.commutes]
        exact Ideal.mem_map_of_mem _ hr
      simpa using Ideal.add_mem _ (hKK hdiff) ht'K
    · rw [Ideal.map_le_iff_le_comap]
      intro r hr
      simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes]
      rw [← Ideal.Quotient.mk_algebraMap, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ hr

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplAtFactorOfIsAdicComplete
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem exists_complAt_factor_of_isAdicComplete : ∀ (W : Type) [CommRing W] [IsRegularLocalRing W] (I : Type) [Fintype I] (V : Type) [CommRing V] [IsLocalRing V], IsAdicComplete (maximalIdeal V) V → ∀ ψV : MvPolynomial I W →+* V, IsLocalHom (ψV.comp MvPolynomial.C) → ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (ψ : MvPolynomial I W →+* R) (θ : R →+* V), IsComplAt ψ ∧ IsLocalHom θ ∧ θ.comp ψ = ψV ∧ IsLocalHom (ψ.comp MvPolynomial.C) := by
  intro W _ _ I _ V _ _ hV ψV hC
  haveI := hV
  let A := MvPolynomial I W
  let q : Ideal A := (maximalIdeal V).comap ψV
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  let L := Localization.AtPrime q
  haveI : IsRegularRing W := GlobalTheory.isRegularRing_of_isRegularLocalRing W
  haveI : IsRegularLocalRing L := inferInstance
  let R := AdicCompletion (maximalIdeal L) L
  haveI : IsRegularLocalRing R := GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion L
  haveI : IsDomain R := inferInstance
  haveI : IsNoetherianRing R := inferInstance
  have hfg : (maximalIdeal L).FG := (maximalIdeal L).fg_of_isNoetherianRing
  have hunit : ∀ y : q.primeCompl, IsUnit (ψV y) := fun y => by
    have := y.2
    exact IsLocalRing.notMem_maximalIdeal.mp this
  let φ : L →+* V := IsLocalization.lift (M := q.primeCompl) (S := L) hunit
  have hφ : φ.comp (algebraMap A L) = ψV := IsLocalization.lift_comp hunit
  have hmL : (maximalIdeal L) = q.map (algebraMap A L) := (Localization.AtPrime.map_eq_maximalIdeal).symm
  have hk : (maximalIdeal L).map φ ^ 1 ≤ maximalIdeal V := by
    rw [pow_one, hmL, Ideal.map_map, hφ]
    exact Ideal.map_comap_le
  obtain ⟨θ, hθ, -⟩ := GlobalTheory.exists_extend_adicCompletion φ (maximalIdeal L) (maximalIdeal V) hk
  let c : L →+* R := algebraMap L R
  let ψ : A →+* R := c.comp (algebraMap A L)
  have hθψ : θ.comp ψ = ψV := by
    show θ.comp (c.comp (algebraMap A L)) = ψV
    rw [← RingHom.comp_assoc]
    show (θ.comp (algebraMap L R)).comp (algebraMap A L) = ψV
    rw [hθ, hφ]
  have hmR : maximalIdeal R = q.map ψ := by
    have h0 := AdicCompletion.maximalIdeal_eq_map (R := L)
    have hmL' : q.map (algebraMap A L) = maximalIdeal L := Localization.AtPrime.map_eq_maximalIdeal
    rw [h0]
    show _ = q.map (c.comp (algebraMap A L))
    rw [← Ideal.map_map, hmL']
  refine ⟨R, inferInstance, inferInstance, inferInstance, ψ, θ, ⟨inferInstance, inferInstance, ?_, ?_, ?_⟩, ?_, hθψ, ?_⟩
  · exact RingHom.Flat.comp (RingHom.flat_algebraMap_iff.2 (IsLocalization.flat L q.primeCompl))
      (RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian _))
  · apply le_antisymm Ideal.map_comap_le
    have : q ≤ (maximalIdeal R).comap ψ := by
      rw [← Ideal.map_le_iff_le_comap, ← hmR]
    rw [hmR]
    exact Ideal.map_mono (hmR ▸ this)
  · intro r
    obtain ⟨x, hx⟩ := (AdicCompletion.residueField_map_bijective_of_fg (R := L) hfg).2 (residue R r)
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl y
    refine ⟨a, s, ?_, ?_⟩
    · exact (IsLocalization.map_units L s).map c
    · have h1 : residue R (c (IsLocalization.mk' L a s)) = residue R r := by
        rw [← hx, ResidueField.map_residue]
      have h2 : r - c (IsLocalization.mk' L a s) ∈ maximalIdeal R := by
        rw [← residue_eq_zero_iff, (residue R).map_sub, h1, sub_self]
      have h3 : c (IsLocalization.mk' L a s) * ψ s = ψ a := by
        show c (IsLocalization.mk' L a s) * c (algebraMap A L s) = c (algebraMap A L a)
        rw [← map_mul, IsLocalization.mk'_spec]
      have : r * ψ s - ψ a = (r - c (IsLocalization.mk' L a s)) * ψ s := by
        rw [sub_mul, h3]
      rw [this]
      exact Ideal.mul_mem_right _ _ h2
  · haveI : IsLocalHom (θ.comp (algebraMap L R)) := by
      rw [hθ]
      apply ((IsLocalRing.local_hom_tfae φ).out 1 3).mpr
      simpa using hk
    exact GlobalTheory.isLocalHom_of_extend_adicCompletion hfg θ
  · refine ⟨fun a ha => hC.map_nonunit a ?_⟩
    have : θ ((ψ.comp MvPolynomial.C) a) = (ψV.comp MvPolynomial.C) a := by
      simp only [RingHom.comp_apply]
      exact congrArg (fun f : A →+* V => f (MvPolynomial.C a)) hθψ
    rw [← this]
    exact ha.map θ

end GlobalTheory.TChart
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrLocalFiniteExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.TraitPlace

theorem exists_valuationSubring_of_injective {S K : Type} [CommRing S] [Field K] (f : S →+* K)
    (hf : Function.Injective f) (I : Ideal S) (hI : I ≠ ⊤) :
    ∃ B : ValuationSubring K, ∀ x ∈ I, f x ∈ B.nonunits := by
  have hb : Function.Bijective f.rangeRestrict :=
    ⟨fun a b h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  have hI' : I.map f.rangeRestrict ≠ ⊤ := by
    intro h
    apply hI
    rw [← Ideal.comap_map_of_bijective f.rangeRestrict hb (I := I), h, Ideal.comap_top]
  obtain ⟨B, -, hB⟩ := Ideal.image_subset_nonunits_valuationSubring _ hI'
  exact ⟨B, fun x hx => hB ⟨_, Ideal.mem_map_of_mem _ hx, rfl⟩⟩

theorem mem_of_forall_prime {F : Type} [Field F] [CharZero F] [Algebra.IsAlgebraic ℚ F]
    (O : ValuationSubring F) (h : ∀ p : ℕ, p.Prime → (p : F) ∉ O.nonunits) (x : F) : x ∈ O := by
  have h1 : ∀ n : ℕ, (n : F)⁻¹ ∈ O := by
    intro n
    induction n using Nat.recOnMul with
    | zero => simp
    | one => simp
    | prime p hp =>
      have := h p hp
      rw [ValuationSubring.mem_nonunits_iff_or] at this
      push Not at this
      exact this.2
    | mul a b ha hb =>
      rw [Nat.cast_mul, mul_inv]
      exact O.mul_mem _ _ ha hb
  have h2 : ∀ q : ℚ, algebraMap ℚ F q ∈ O := by
    intro q
    rw [eq_ratCast, Rat.cast_def, div_eq_mul_inv]
    exact O.mul_mem _ _ (intCast_mem O _) (h1 _)
  let g : ℚ →+* O := (algebraMap ℚ F).codRestrict O h2
  have hx : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have hx' : IsIntegral O x := by
    obtain ⟨P, hP, hP0⟩ := hx
    refine ⟨P.map g, hP.map g, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hP0
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hx'
  rw [← hy]
  exact y.2

theorem exists_place (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F] (O : ValuationSubring F) :
    ∃ (p : ℕ) (W : ValuationSubring ℂ), p.Prime ∧ (p : ℂ) ∈ W.nonunits ∧
      ∀ x : F, (x : ℂ) ∈ W → x ∈ O := by
  by_cases h : ∀ p : ℕ, p.Prime → (p : F) ∉ O.nonunits
  · obtain ⟨B, hB⟩ := exists_valuationSubring_of_injective (Int.castRingHom ℂ) Int.cast_injective
      (Ideal.span {(2 : ℤ)}) (by
        rw [Ne, Ideal.span_singleton_eq_top]
        decide)
    refine ⟨2, B, Nat.prime_two, ?_, fun x _ => mem_of_forall_prime O h x⟩
    simpa using hB 2 (Ideal.mem_span_singleton_self _)
  · push Not at h
    obtain ⟨p, hp, hpO⟩ := h
    obtain ⟨B, hB⟩ := exists_valuationSubring_of_injective (F.val.toRingHom.comp O.subtype)
      (fun a b h => Subtype.ext (Subtype.ext h)) (maximalIdeal O) (maximalIdeal.isMaximal O).ne_top
    have hB' : ∀ x : F, x ∈ O.nonunits → (x : ℂ) ∈ B.nonunits := fun x hx =>
      hB ⟨x, O.nonunits_subset hx⟩ (ValuationSubring.coe_mem_nonunits_iff.1 hx)
    refine ⟨p, B, hp, by simpa using hB' _ hpO, fun x hx => ?_⟩
    by_contra hxO
    have h0 : x ≠ 0 := fun h => hxO (h ▸ O.zero_mem)
    have h1 : x⁻¹ ∈ O.nonunits := by
      rw [ValuationSubring.mem_nonunits_iff_or]
      right
      rwa [inv_inv]
    have h2 := hB' _ h1
    rw [ValuationSubring.mem_nonunits_iff_or] at h2
    rcases h2 with h2 | h2
    · exact h0 (by simpa using h2)
    · exact h2 (by simpa using hx)

theorem exists_finite_ext (F K : Type) [Field F] [CharZero F] [FiniteDimensional ℚ F] [Field K] [CharZero K] :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L), FiniteDimensional K L ∧ Nonempty (F →+* L) := by
  first
  | exact @_root_.GlobalTheory.FiniteExtensionEmbedding.exists_finite_extension_embedding
  | exact _root_.GlobalTheory.FiniteExtensionEmbedding.exists_finite_extension_embedding
  | (apply _root_.GlobalTheory.FiniteExtensionEmbedding.exists_finite_extension_embedding <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteExtensionEmbedding.exists_finite_extension_embedding <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteExtensionEmbedding.exists_finite_extension_embedding <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteExtensionEmbedding.exists_finite_extension_embedding ..)

theorem exists_place_finite_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), ∃ (p : ℕ) (hp : p.Prime) (W₀ : ValuationSubring ℂ) (hW : (p : ℂ) ∈ W₀.nonunits) (i : Idx H p) (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (ρ₁ : R →+* V₁) (b₁ : ↥(i.c.V W₀) →+* V₁), GlobalTheory.LN.CDvr V₁ ∧ Function.Injective ρ₁ ∧ ρ₁.Finite ∧ IsLocalHom ρ₁ ∧ Function.Injective b₁ := by
  intro R _ _ _ hR E _ _ _ H
  obtain ⟨h1, h2, h3⟩ := hR
  obtain ⟨l, -, hg, hi⟩ := GlobalTheory.exists_level_goodAt_all_primes_and_idx E H 1 one_pos
  obtain ⟨⟨l', c, hg2⟩, hl⟩ := hi 2 Nat.prime_two
  have hg' : ∀ p : ℕ, p.Prime → l'.GoodAt p := by
    subst hl
    exact hg
  haveI := c.fin
  haveI : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  obtain ⟨L, _, _, hL, ⟨jF⟩⟩ := exists_finite_ext c.F (FractionRing R)
  obtain ⟨V, _, _, hV, hVc, _, _, _, -, hfin, hinj, hloc, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension R (FractionRing R) L
  have hVL := IsFractionRing.injective V L
  let O : ValuationSubring c.F := ValuationSubring.ofSubring ((algebraMap V L).range.comap jF) (fun x => by
    rcases ValuationRing.isInteger_or_isInteger V (jF x) with h | h
    · exact Or.inl h
    · right
      change jF x⁻¹ ∈ (algebraMap V L).range
      rw [map_inv₀]
      exact h)
  obtain ⟨p, W, hp, hW, hO⟩ := exists_place c.F O
  let e : V ≃+* (algebraMap V L).range := RingEquiv.ofBijective (algebraMap V L).rangeRestrict
    ⟨fun a b h => hVL (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩
  let g : c.V W →+* (algebraMap V L).range :=
    (jF.comp (c.V W).subtype).codRestrict _ (fun x => hO x.1 x.2)
  refine ⟨p, hp, W, hW, ⟨l', c, hg' p hp⟩, V, inferInstance, inferInstance, inferInstance, algebraMap R V,
    e.symm.toRingHom.comp g, ⟨hV, hVc, charZero_of_injective_algebraMap hinj⟩, hinj,
    RingHom.finite_algebraMap.2 hfin, hloc, ?_⟩
  intro a b h
  exact Subtype.ext (jF.injective (congrArg Subtype.val (e.symm.injective h)))

end GlobalTheory.TraitPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexFibreExponentialFullLattice
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.FibreExp

theorem exists_exp_lattice : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsAbelianScheme G →
    SmoothOfRelativeDimension g G.hom → ∀ y : Sp ℂ ⟶ X, ∃ (e : (Fin g → ℂ) → (Over.mk y ⟶ G))
      (Λ : Submodule ℤ (Fin g → ℂ)), IsExp y e ∧ DiscreteTopology Λ ∧ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ ∧
        ∀ z, e z = 1 ↔ z ∈ Λ := by
  intro X G _ _ g hG hgG y
  letI : GrpObj ((Over.pullback y).obj G) := Functor.grpObjObj
  have hj := isGrpPullback_pullback G y
  have hA : IsAbelianScheme ((Over.pullback y).obj G) := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hG hj
  have hgA : SmoothOfRelativeDimension g ((Over.pullback y).obj G).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hj.1 hgG
  obtain ⟨L, ⟨u⟩⟩ := GlobalTheory.HomDescentQb.exists_holUnif _ g hA hgA
  obtain ⟨h1, h2⟩ := GlobalTheory.UnifTangent.tangent_bijection u hgA
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.LiePull.exists_pushEquiv hj (𝟙_ _) y (Category.id_comp _).symm
  have he := GlobalTheory.PointUnif.isExp_push hj u h1 h2 Φ hΦ
  exact ⟨fun z => Φ (u.ex z), u.Λ, he, u.discrete, u.full,
    fun z => (map_eq_one_iff Φ Φ.injective).trans (u.ker z)⟩

end GlobalTheory.FibreExp
end
end

