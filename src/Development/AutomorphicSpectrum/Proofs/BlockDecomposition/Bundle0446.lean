module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0371
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0237
public import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle0004
public import GroundTheory.ProfiniteCohomology.LocalClassFormation.CupSymbol
public import GroundTheory.ProfiniteCohomology.GaloisCohomology.IsZeroGroupCohomologyQuotientToInvariantsGalAdd
public import GroundTheory.ProfiniteCohomology.GaloisCohomology.Kummer
public import GroundTheory.GlobalFields.LocalFieldAtPlace
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.TransportA
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0395
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0401
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0400
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0405
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0419
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0394
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MaxEvenLatticeFlagTransitiveLocal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0425
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0390

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearOdeValueDeterminedByShifts
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.LinearODE

noncomputable def companion (p : Polynomial ℂ) (n : ℕ) : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  LinearMap.pi fun i =>
    if h : (i : ℕ) + 1 < n then LinearMap.proj ⟨i + 1, h⟩
    else - ∑ k : Fin n, p.coeff k • LinearMap.proj k

theorem top_eq {p : Polynomial ℂ} (hp : p.Monic) {F : ℕ → ℝ → ℂ}
    (hrel : ∀ s : ℝ, ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * F k s = 0) (s : ℝ) :
    F p.natDegree s = - ∑ k : Fin p.natDegree, p.coeff k * F k s := by
  have h := hrel s
  rw [Finset.sum_range_succ, hp.coeff_natDegree, one_mul] at h
  have e : ∑ k : Fin p.natDegree, p.coeff k * F k s =
      ∑ k ∈ Finset.range p.natDegree, p.coeff k * F k s :=
    (Finset.sum_range (fun k => p.coeff k * F k s)).symm
  rw [e]
  linear_combination h

theorem lower_eq_zero {p : Polynomial ℂ} (hp : p.Monic) {F : ℕ → ℝ → ℂ}
    (hF : ∀ (k : ℕ) (s : ℝ), HasDerivAt (F k) (F (k + 1) s) s)
    (hrel : ∀ s : ℝ, ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * F k s = 0)
    (h0 : ∀ k < p.natDegree, F k 0 = 0) : ∀ k < p.natDegree, F k = 0 := by
  let X : ℝ → (Fin p.natDegree → ℂ) := fun s i => F i s
  have hX : ∀ s, HasDerivAt X (companion p p.natDegree (X s)) s := by
    intro s
    rw [hasDerivAt_pi]
    intro i
    have e : companion p p.natDegree (X s) i = F (i + 1) s := by
      simp only [companion, LinearMap.pi_apply]
      split_ifs with h
      · rfl
      · have hi : (i : ℕ) + 1 = p.natDegree := by
          have := i.isLt
          omega
        rw [hi, top_eq hp hrel s]
        simp [X, LinearMap.sum_apply, smul_eq_mul]
    rw [e]
    exact hF i s
  have hA : LipschitzWith ‖LinearMap.toContinuousLinearMap (companion p p.natDegree)‖₊
      (companion p p.natDegree) := by
    have := (LinearMap.toContinuousLinearMap (companion p p.natDegree)).lipschitz
    simpa using this
  have hzero : ∀ s, X s = 0 := by
    intro s
    have key := ODE_solution_unique_of_mem_Icc (v := fun _ => companion p p.natDegree)
      (s := fun _ => Set.univ) (a := -(|s| + 1)) (b := |s| + 1) (t₀ := 0)
      (fun t _ => hA.lipschitzOnWith)
      ⟨by linarith [abs_nonneg s], by linarith [abs_nonneg s]⟩
      (fun t _ => (hX t).continuousAt.continuousWithinAt) (fun t _ => hX t)
      (fun _ _ => Set.mem_univ _)
      (continuousOn_const (c := (0 : Fin p.natDegree → ℂ)))
      (fun t _ => by simpa using hasDerivAt_const t (0 : Fin p.natDegree → ℂ))
      (fun _ _ => Set.mem_univ _)
      (by funext i; simpa [X] using h0 i i.isLt)
    exact key ⟨by linarith [neg_abs_le s], by linarith [le_abs_self s]⟩
  intro k hk
  funext s
  simpa [X] using congrFun (hzero s) ⟨k, hk⟩

theorem chain_zero {F : ℕ → ℝ → ℂ} (hF : ∀ (k : ℕ) (s : ℝ), HasDerivAt (F k) (F (k + 1) s) s)
    {m : ℕ} (h : F m = 0) : ∀ k, m ≤ k → F k = 0 := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact h
  | succ k hmk ih =>
    funext s
    have h1 := hF k s
    rw [ih] at h1
    show F (k + 1) s = 0
    exact h1.unique (hasDerivAt_const s (0 : ℂ))

theorem eq_zero_of_initial {p : Polynomial ℂ} (hp : p.Monic) {F : ℕ → ℝ → ℂ}
    (hF : ∀ (k : ℕ) (s : ℝ), HasDerivAt (F k) (F (k + 1) s) s)
    (hrel : ∀ s : ℝ, ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * F k s = 0)
    (h0 : ∀ k < p.natDegree, F k 0 = 0) : ∀ k, F k = 0 := by
  have hlow := lower_eq_zero hp hF hrel h0
  have htop : F p.natDegree = 0 := by
    funext s
    rw [top_eq hp hrel s]
    have hz : ∀ k : Fin p.natDegree, p.coeff k * F k s = 0 := fun k => by
      rw [hlow k k.isLt]
      simp
    simp [hz]
  intro k
  rcases lt_or_ge k p.natDegree with hk | hk
  · exact hlow k hk
  · exact chain_zero hF htop k hk

def solSpace (p : Polynomial ℂ) : Submodule ℂ (ℕ → ℝ → ℂ) where
  carrier := {F | (∀ (k : ℕ) (s : ℝ), HasDerivAt (F k) (F (k + 1) s) s) ∧
    ∀ s : ℝ, ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * F k s = 0}
  add_mem' := by
    rintro F G ⟨hF, rF⟩ ⟨hG, rG⟩
    refine ⟨fun k s => (hF k s).add (hG k s), fun s => ?_⟩
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, rF s, rG s, add_zero]
  zero_mem' := ⟨fun k s => hasDerivAt_const s (0 : ℂ), fun s => by simp⟩
  smul_mem' := by
    rintro c F ⟨hF, rF⟩
    refine ⟨fun k s => (hF k s).const_mul c, fun s => ?_⟩
    have h : ∀ k, p.coeff k * (c • F) k s = c * (p.coeff k * F k s) := fun k => by
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    simp only [h, ← Finset.mul_sum, rF s, mul_zero]

theorem finiteDimensional_solSpace {p : Polynomial ℂ} (hp : p.Monic) :
    FiniteDimensional ℂ (solSpace p) := by
  let Φ : solSpace p →ₗ[ℂ] (Fin p.natDegree → ℂ) :=
    { toFun := fun F i => (F : ℕ → ℝ → ℂ) i 0
      map_add' := fun F G => rfl
      map_smul' := fun c F => rfl }
  refine Module.Finite.of_injective Φ ((injective_iff_map_eq_zero Φ).2 fun F hF => ?_)
  obtain ⟨hFd, hFr⟩ := F.2
  have hz := eq_zero_of_initial hp hFd hFr (fun k hk => congrFun hF ⟨k, hk⟩)
  exact Subtype.ext (funext hz)

theorem deriv_zero_eq_sum :
    ∀ p : Polynomial ℂ, p.Monic → ∃ (T : Finset ℝ) (w : ℝ → ℂ), ∀ F : ℕ → ℝ → ℂ,
      (∀ (k : ℕ) (s : ℝ), HasDerivAt (F k) (F (k + 1) s) s) →
      (∀ s : ℝ, ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * F k s = 0) →
      F 1 0 = ∑ t ∈ T, w t * F 0 t := by
  intro p hp
  haveI := finiteDimensional_solSpace hp
  let ev : ℝ → Module.Dual ℂ (solSpace p) := fun t =>
    { toFun := fun F => (F : ℕ → ℝ → ℂ) 0 t
      map_add' := fun F G => rfl
      map_smul' := fun c F => rfl }
  let φ : Module.Dual ℂ (solSpace p) :=
    { toFun := fun F => (F : ℕ → ℝ → ℂ) 1 0
      map_add' := fun F G => rfl
      map_smul' := fun c F => rfl }
  have hco : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro F hF
    rw [Submodule.mem_dualCoannihilator] at hF
    have h0 : (F : ℕ → ℝ → ℂ) 0 = 0 :=
      funext fun t => hF (ev t) (Submodule.subset_span ⟨t, rfl⟩)
    obtain ⟨hFd, -⟩ := F.2
    have hall := chain_zero hFd h0
    rw [Submodule.mem_bot]
    exact Subtype.ext (funext fun k => hall k (Nat.zero_le k))
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev)), hco,
      Submodule.dualAnnihilator_bot]
  have hφ : φ ∈ Submodule.span ℂ (Set.range ev) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hφ
  refine ⟨c.support, c, fun F hFd hFr => ?_⟩
  have hmem : F ∈ solSpace p := ⟨hFd, hFr⟩
  have key := LinearMap.congr_fun hc ⟨F, hmem⟩
  simp only [Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply] at key
  exact key.symm

end GlobalTheory.CompanionTheory.LinearODE
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalInvariantCupUniformizer
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
open GroundTheory.ProfCoh GroundTheory.LocalField ValuativeRel CategoryTheory

namespace GlobalTheory.CompanionTheory.KummerCup

noncomputable def muEquiv {Ω : Type} [Field Ω] {n : ℕ} [NeZero n] (ζ : Ωˣ) (hζ : IsPrimitiveRoot ζ n) :
    ZMod n ≃+ Additive (rootsOfUnity n Ω) :=
  let ζ' : rootsOfUnity n Ω := ⟨ζ, (mem_rootsOfUnity _ _).2 hζ.pow_eq_one⟩
  have h1 : ζ' ^ n = 1 := Subtype.ext hζ.pow_eq_one
  let f : ZMod n →+ Additive (rootsOfUnity n Ω) :=
    { toFun := fun m => Additive.ofMul (ζ' ^ m.val)
      map_zero' := by simp
      map_add' := fun a b => by
        rw [ZMod.val_add, ← pow_eq_pow_mod _ h1, pow_add, ofMul_mul] }
  AddEquiv.ofBijective f (by
    have hinj : Function.Injective f := by
      intro a b hab
      have h2 : ζ ^ a.val = ζ ^ b.val := by
        have := congrArg (fun w => ((Additive.toMul w : rootsOfUnity n Ω) : Ωˣ)) hab
        simpa [f, ζ'] using this
      have h3 := hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h2
      exact ZMod.val_injective n h3
    refine ⟨hinj, fun w => ?_⟩
    have hζ' : IsPrimitiveRoot (ζ : Ω) n := IsPrimitiveRoot.coe_units_iff.2 hζ
    have hw : (((Additive.toMul w : rootsOfUnity n Ω) : Ωˣ) : Ω) ^ n = 1 := by
      have := (mem_rootsOfUnity _ _).1 (Additive.toMul w).2
      rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
    obtain ⟨i, hi, hie⟩ := hζ'.eq_pow_of_pow_eq_one hw
    refine ⟨(i : ZMod n), ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    change (((ζ' ^ ((i : ZMod n)).val : rootsOfUnity n Ω) : Ωˣ) : Ω) = _
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hi, ← hie]
    simp [ζ'])

theorem muEquiv_apply {Ω : Type} [Field Ω] {n : ℕ} [NeZero n] (ζ : Ωˣ) (hζ : IsPrimitiveRoot ζ n) (m : ZMod n) :
    (((Additive.toMul (muEquiv ζ hζ m) : rootsOfUnity n Ω) : Ωˣ)) = ζ ^ m.val := by
  simp [muEquiv]

attribute [local instance 2000] Rep.hV2

theorem cochainOf_cyclesMap {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A B : Rep.{0} k G} [IsDiscreteRep A] [IsDiscreteRep B] (φ : A ⟶ B) (x : cocycles A 2) (s : Fin 2 → G) :
    cochainOf B (cocycleι B 2 ((HomologicalComplex.cyclesMap (cochainsMap φ) 2).hom x)) s =
      φ.hom (cochainOf A (cocycleι A 2 x) s) := by
  have e := congrArg (fun ψ => cochainOf B (ψ.hom x)) (HomologicalComplex.cyclesMap_i (cochainsMap φ) 2)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e
  change cochainOf B (((cochainsComplex B).iCycles 2).hom _) s = _
  rw [e, cochainOf_cochainsMap_f]
  rfl

theorem inv_class (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] [ValuativeRel Ω] [TopologicalSpace Ω]
    [IsValuativeTopology Ω] [ValuativeExtension K Ω] (n : ℕ) [NeZero n]
    (ζ y : Ωˣ) (a : Kˣ) (hζ : IsPrimitiveRoot ζ n)
    (ha : ord (a : K) = 1) (hy : (y : Ω) ^ n = algebraMap K Ω a)
    (κ χ : Gal(Ω/K) → ZMod n)
    (hκ : ∀ g : Gal(Ω/K), g (y : Ω) = (ζ : Ω) ^ (κ g).val * y)
    (hadd : ∀ g h, χ (g * h) = χ g + χ h) (hcont : Continuous χ)
    (hF : ∀ g, unramifiedDegree K Ω g = Multiplicative.ofAdd 1 → χ g = 1)
    (x : cocycles (galRootsOfUnity.{0} K Ω n) 2)
    (hx : ∀ s : Fin 2 → Gal(Ω/K), cochainOf _ (cocycleι _ 2 x) s = muEquiv ζ hζ (κ (s 0) * χ (s 1))) :
    brauerInv K Ω ((cohomologyMap (rootsOfUnityToUnits K Ω n) 2).hom (cohomologyπ _ 2 x)) = - zmodToQZ n 1 := by
  have hJx := ConcreteCategory.congr_hom (cohomologyπ_comp_cohomologyMap (rootsOfUnityToUnits K Ω n) 2) x
  have hJx' : (cohomologyMap (rootsOfUnityToUnits K Ω n) 2).hom (cohomologyπ _ 2 x) =
      cohomologyπ _ 2 ((HomologicalComplex.cyclesMap (cochainsMap (rootsOfUnityToUnits K Ω n)) 2).hom x) := hJx
  rw [hJx']
  refine _root_.GlobalTheory.CompanionTheory.KummerCupInv.inv_kummerCup K Ω n ζ y a hζ.pow_eq_one ha hy κ χ hκ hadd hcont hF _ fun s => ?_
  rw [cochainOf_cyclesMap, hx, rootsOfUnityToUnits_hom_apply, muEquiv_apply]

theorem generates_of_inv {n : ℕ} [NeZero n] {H : Type} [AddCommGroup H] [Module (ZMod n) H] (T : H →+ QZ)
    (hT : Function.Injective T) (w : H) (h : T w = - zmodToQZ n 1) :
    Submodule.span (ZMod n) {w} = ⊤ := by
  have hTn : ∀ x, n • T x = 0 := by
    intro x
    rw [← map_nsmul]
    have : n • x = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]
    rw [this, map_zero]
  rw [Submodule.eq_top_iff']
  intro x
  obtain ⟨b, hb⟩ := exists_zmodToQZ_eq (hTn x)
  have hx : x = (-b) • w := by
    apply hT
    rw [← hb]
    have : (-b) • w = ((-b).val) • w := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_zmod_val]
    rw [this, map_nsmul, h, ← map_neg, ← map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]
    simp
  rw [hx]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

theorem mu_equivariant (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (n : ℕ) [NeZero n]
    (c : Gal(Ω/K) →* (ZMod n)ˣ) (ζ : Ωˣ) (hζ : IsPrimitiveRoot ζ n)
    (hc : ∀ g : Gal(Ω/K), g (ζ : Ω) = (ζ : Ω) ^ ((c g : (ZMod n)ˣ) : ZMod n).val)
    (g : Gal(Ω/K)) (m : ZMod n) : muEquiv ζ hζ (charRep c g m) =
      (galRootsOfUnity.{0} K Ω n).ρ g (muEquiv ζ hζ m) := by
  rw [galRootsOfUnity_ρ_apply]
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  change (((Additive.toMul (muEquiv ζ hζ (charRep c g m)) : rootsOfUnity n Ω) : Ωˣ) : Ω) =
    g (((Additive.toMul (muEquiv ζ hζ m) : rootsOfUnity n Ω) : Ωˣ) : Ω)
  rw [muEquiv_apply, muEquiv_apply, charRep_apply, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
    map_pow, hc, ← pow_mul, ZMod.val_mul]
  have h1 : (ζ : Ω) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, hζ.pow_eq_one, Units.val_one]
  rw [← pow_eq_pow_mod _ h1]

theorem core (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] [ValuativeRel Ω] [TopologicalSpace Ω]
    [IsValuativeTopology Ω] [ValuativeExtension K Ω] (n : ℕ) [NeZero n] (hn : (n : K) ≠ 0)
    (c : Gal(Ω/K) →* (ZMod n)ˣ) (ζ y : Ωˣ) (a : Kˣ) (hζ : IsPrimitiveRoot ζ n)
    (hc : ∀ g : Gal(Ω/K), g (ζ : Ω) = (ζ : Ω) ^ ((c g : (ZMod n)ˣ) : ZMod n).val)
    (ha : ord (a : K) = 1) (hy : (y : Ω) ^ n = algebraMap K Ω a)
    (κ χ : Gal(Ω/K) → ZMod n)
    (hκ : ∀ g : Gal(Ω/K), g (y : Ω) = (ζ : Ω) ^ (κ g).val * y)
    (hadd : ∀ g h, χ (g * h) = χ g + χ h)
    (hF : ∀ g, unramifiedDegree K Ω g = Multiplicative.ofAdd 1 → χ g = 1)
    (z : Z2 (charRep c)) (hz : ∀ g h, z.1 (g, h) = κ g * χ h) :
    Submodule.span (ZMod n) {(Submodule.Quotient.mk z : H2 (charRep c))} = ⊤ := by
  have hcont := _root_.GlobalTheory.CompanionTheory.LocalUnram.continuous_of_additive_of_frobenius_eq_one K Ω n χ hadd hF
  have he := mu_equivariant K Ω n c ζ hζ hc
  obtain ⟨e2, hex, he2⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 Gal(Ω/K) (ZMod n) (ZMod n) (charRep c)
    (galRootsOfUnity.{0} K Ω n) (muEquiv ζ hζ) he
  have hJ : Function.Injective (cohomologyMap (rootsOfUnityToUnits K Ω n) 2).hom :=
    cohomologyMap_f_injective_of_subsingleton (kummerSequence_shortExact (K := K) (L := Ω) n hn) 1
      subsingleton_cohomology_one_galUnits
  let T : H2 (charRep c) →+ QZ := ((brauerInv K Ω).comp
    (cohomologyMap (rootsOfUnityToUnits K Ω n) 2).hom.toAddMonoidHom).comp e2.toAddMonoidHom
  have hTinj : Function.Injective T :=
    (brauerInv_bijective K Ω).1.comp (hJ.comp e2.injective)
  have hT1 : T (Submodule.Quotient.mk z) = - zmodToQZ n 1 := by
    obtain ⟨x, hx⟩ := hex z
    change brauerInv K Ω ((cohomologyMap (rootsOfUnityToUnits K Ω n) 2).hom (e2 (Submodule.Quotient.mk z))) = _
    rw [he2 z x hx]
    exact inv_class K Ω n ζ y a hζ ha hy κ χ hκ hadd hcont hF x fun s => by rw [hx, hz]
  exact generates_of_inv T hTinj _ hT1

theorem core_dec (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (n : ℕ) [NeZero n] (hn : (n : K) ≠ 0)
    (D : Type) [Group D] [TopologicalSpace D] (ε : Gal(Ω/K) ≃ₜ* D)
    (c : D →* (ZMod n)ˣ) (ζ y : Ωˣ) (a : Kˣ) (hζ : IsPrimitiveRoot ζ n)
    (hc : ∀ g : Gal(Ω/K), g (ζ : Ω) = (ζ : Ω) ^ ((c (ε g) : (ZMod n)ˣ) : ZMod n).val)
    (ha : ord (a : K) = 1) (hy : (y : Ω) ^ n = algebraMap K Ω a)
    (κ χ : D → ZMod n)
    (hκ : ∀ g : Gal(Ω/K), g (y : Ω) = (ζ : Ω) ^ (κ (ε g)).val * y)
    (hadd : ∀ g h, χ (g * h) = χ g + χ h)
    (hF : ∀ g, unramifiedDegree K Ω g = Multiplicative.ofAdd 1 → χ (ε g) = 1)
    (z : Z2 (charRep c)) (hz : ∀ g h, z.1 (g, h) = κ g * χ h) :
    Submodule.span (ZMod n) {(Submodule.Quotient.mk z : H2 (charRep c))} = ⊤ := by
  letI := algebraicValuativeRel K Ω
  letI := algebraicTopology K Ω
  haveI := algebraicValuativeRel_valuativeExtension K Ω
  haveI := algebraicTopology_isValuativeTopology K Ω
  let c' : Gal(Ω/K) →* (ZMod n)ˣ := c.comp (ε : Gal(Ω/K) →* D)
  let T := ReciprocityTheory.Neutral.Bridge.equivH2OfIso ε (charRep c) (charRep c') (fun _ _ => rfl)
  let z' : Z2 (charRep c') := ReciprocityTheory.Gal.compatiblePairCocycles2 (charRep c) (charRep c')
    (ε : Gal(Ω/K) →* D) (ReciprocityTheory.Neutral.Bridge.continuous_coe_iso ε) LinearMap.id continuous_id (fun _ _ => rfl) z
  have hspan := core K Ω n hn c' ζ y a hζ hc ha hy (fun g => κ (ε g)) (fun g => χ (ε g)) hκ
    (fun g h => by rw [map_mul, hadd]) hF z' (fun g h => hz _ _)
  rw [Submodule.eq_top_iff']
  intro x
  have hx : T x ∈ Submodule.span (ZMod n) {(Submodule.Quotient.mk z' : H2 (charRep c'))} := by
    rw [hspan]; trivial
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 hx
  have : x = b • (Submodule.Quotient.mk z : H2 (charRep c)) := by
    apply T.injective
    rw [← hb, map_smul, show T (Submodule.Quotient.mk z) = Submodule.Quotient.mk z' from
      ReciprocityTheory.Neutral.Bridge.equivH2OfIso_mk ε _ _ _ z]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)

theorem cyc_apply (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosed Ω] [CharZero Ω] (l : ℕ)
    [Fact l.Prime] (r : ℕ) (ζ : Ω) (hζ : ζ ^ (l ^ r) = 1) (σ : G F Ω) :
    σ ζ = ζ ^ ((cycMod F Ω l r σ : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val := by
  haveI : ∀ i, NeZero (l ^ i) := fun i => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  exact cyclotomicCharacter.spec (L := Ω) l (σ : Ω ≃+* Ω) ζ hζ

theorem span_class_eq_top : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ), 0 < r → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ r) → ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (ϖ : 𝓞 F) (y : Ω) (κ χ : Dec (F := F) A → ZMod (l ^ r)) (z : Z2 (muLoc F l r A)), ϖ ∈ v.asIdeal → ϖ ∉ v.asIdeal ^ 2 → y ^ (l ^ r) = algebraMap F Ω (ϖ : F) → (∀ g : Dec (F := F) A, (g : G F Ω) y = ζ ^ (κ g).val * y) → (∀ g h, χ (g * h) = χ g + χ h) → (∀ g : Dec (F := F) A, (g : G F Ω) ∈ Ine (F := F) A → χ g = 0) → (∀ g : Dec (F := F) A, IsFrob (F := F) A (normV v) (g : G F Ω) → χ g = 1) → (∀ g h, z.1 (g, h) = κ g * χ h) → Submodule.span (ZMod (l ^ r)) {(Submodule.Quotient.mk z : H2 (muLoc F l r A))} = ⊤ := by
  intro F Ω _ _ _ _ _ l _ r hr ζ hζ A v hA ϖ y κ χ z h1 h2 h3 h4 h5 h6 h7 h8
  have hl0 : l ^ r ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
  haveI : NeZero (l ^ r) := ⟨hl0⟩
  obtain ⟨ι, e, hec, hes, hl⟩ := GlobalTheory.CompanionTheory.DecGal.exists_algHom_mulEquiv_dec F Ω A v hA
  haveI : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  haveI : IsSepClosure (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F)) :=
    ⟨inferInstance, inferInstance⟩
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hϖ0 : (ϖ : F) ≠ 0 := by
    intro h
    have : ϖ = 0 := by exact_mod_cast h
    exact h2 (this ▸ Ideal.zero_mem _)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [zero_pow hl0] at h3
    exact hϖ0 ((map_eq_zero_iff _ (algebraMap F Ω).injective).1 h3.symm)
  have hιζ : IsPrimitiveRoot (ι ζ) (l ^ r) := hζ.map_of_injective ι.injective
  have hιy : ι y ≠ 0 := (map_ne_zero_iff _ ι.injective).2 hy0
  have ha0 : algebraMap F (v.adicCompletion F) (ϖ : F) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap F (v.adicCompletion F)).injective).2 hϖ0
  refine core_dec (v.adicCompletion F) (AlgebraicClosure (v.adicCompletion F)) (l ^ r)
    (Nat.cast_ne_zero.2 hl0) (Dec (F := F) A) { e with continuous_toFun := hec, continuous_invFun := hes }
    ((cycMod F Ω l r).comp (Dec (F := F) A).subtype) (Units.mk0 (ι ζ) (hιζ.ne_zero hl0)) (Units.mk0 (ι y) hιy)
    (Units.mk0 _ ha0) (IsPrimitiveRoot.coe_units_iff.1 hιζ) ?_ (_root_.GlobalTheory.CompanionTheory.Completion.ord_algebraMap_eq_one F v ϖ h1 h2) ?_ κ χ ?_ h5 ?_ z h8
  · intro g
    change g (ι ζ) = (ι ζ) ^ _
    rw [← hl, cyc_apply F Ω l r ζ hζ.pow_eq_one, map_pow]
    rfl
  · change (ι y) ^ (l ^ r) = _
    rw [← map_pow, h3, ι.commutes]
    exact IsScalarTower.algebraMap_apply F _ _ _
  · intro g
    change g (ι y) = (ι ζ) ^ _ * ι y
    rw [← hl]
    refine (congrArg ι (h4 (e g))).trans ?_
    rw [map_mul, map_pow]
    rfl
  · intro g hg
    exact h7 _ (GlobalTheory.T.decomposition_group_local_galois F Ω A v hA ι _ g (e g).2 (hl g) hg)

end GlobalTheory.CompanionTheory.KummerCup
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MaxEvenLatticeAdaptedBasisStatement
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.max_even_lattice_adapted_basis : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E)), IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) Λ → IsAdapted (intLoc F E v) (hR (Fv F v) σ J) (colV v X) (colV v Y) Λ → ∀ (p m : GLoc σ J v), p ∈ stabLat σ J Λ → ∀ B : Matrix (Fin r) (Fin r) (Fv F v ⊗[F] E), B.BlockTriangular id → (matHom _ σ J p).1 * X.map (inclR (F := F) (Fv F v)) = X.map (inclR (F := F) (Fv F v)) * B → (matHom _ σ J m).1 = leviMat σ J (Fv F v) X Y (matHom _ σ J p).1 → m ∈ stabLat σ J Λ := by
  first | exact @GlobalTheory.CompanionTheory.KFin.GoodLocal.levi_mem_stabLat | exact GlobalTheory.CompanionTheory.KFin.GoodLocal.levi_mem_stabLat | (intros; apply GlobalTheory.CompanionTheory.KFin.GoodLocal.levi_mem_stabLat <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MaxEvenLatticeFlagTransitiveLocalStatement
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.max_even_lattice_flag_transitive_local : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (v : HeightOneSpectrum (𝓞 F)), FlagTransitive (sigR (Fv F v) σ) (intLoc F E v) → ∀ Λ : Submodule (intLoc F E v) (Fin n → Fv F v ⊗[F] E), IsMaxEven (sigR (Fv F v) σ) (intLoc F E v) (hR (Fv F v) σ J) Λ → ∀ g : GLoc σ J v, ∃ p : GLoc σ J v, ∃ k ∈ stabLat σ J Λ, g = p * k ∧ ∃ B : Matrix (Fin r) (Fin r) (Fv F v ⊗[F] E), B.BlockTriangular id ∧ (matHom _ σ J p).1 * X.map (inclR (F := F) (Fv F v)) = X.map (inclR (F := F) (Fv F v)) * B := by
  first | exact @GlobalTheory.CompanionTheory.KFin.Iwasawa.iwasawa_loc | exact GlobalTheory.CompanionTheory.KFin.Iwasawa.iwasawa_loc | (intros; apply GlobalTheory.CompanionTheory.KFin.Iwasawa.iwasawa_loc <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicCoefficientContinuous
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

theorem continuous_coef : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k n) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ), IsSmooth T → ∀ (v : V) (v' : V'), Continuous (coef T B v v') := by
  intro k _ _ _ _ n V V' _ _ _ _ T B hT v v'
  refine IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hcont : Continuous fun y : Fin n → k =>
      GlobalTheory.CompanionTheory.MirFourier.unipIn k n (Multiplicative.ofAdd (y - x)) :=
    (GlobalTheory.CompanionTheory.MirFourier.continuous_unipIn n).comp
      (continuous_ofAdd.comp (continuous_id.sub continuous_const))
  have hopen : IsOpen {y : Fin n → k |
      T (GlobalTheory.CompanionTheory.MirFourier.unipIn k n (Multiplicative.ofAdd (y - x))) v = v} :=
    (hT v).preimage hcont
  have hx : x ∈ {y : Fin n → k |
      T (GlobalTheory.CompanionTheory.MirFourier.unipIn k n (Multiplicative.ofAdd (y - x))) v = v} := by
    simp
  filter_upwards [hopen.mem_nhds hx] with y hy
  have hy' : T (GlobalTheory.CompanionTheory.MirFourier.unipIn k n (Multiplicative.ofAdd (y - x))) v = v := hy
  have hsplit : GlobalTheory.CompanionTheory.MirPair.uM n y =
      GlobalTheory.CompanionTheory.MirPair.uM n x * GlobalTheory.CompanionTheory.MirFourier.unipIn k n (Multiplicative.ofAdd (y - x)) := by
    unfold GlobalTheory.CompanionTheory.MirPair.uM
    rw [← map_mul, ← ofAdd_add, add_sub_cancel]
  unfold GlobalTheory.CompanionTheory.MirPair.coef
  rw [hsplit, map_mul, Module.End.mul_apply, hy']

end GlobalTheory.CompanionTheory.MirPair
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuotientMapInducedSurjectiveIntertwinerStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_map_induced_surjective_intertwiner : ∀ {G G' W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G'] [TopologicalSpace G']
    [IsTopologicalGroup G'] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (H : Subgroup G) (H' : Subgroup G') (ι : G' →* G) (σ : Representation ℂ H W) (σ' : Representation ℂ H' W')
    (q : W →ₗ[ℂ] W'), Continuous ι → IsSmooth σ → Function.Surjective q →
    (∀ x, x ∈ H' ↔ ι x ∈ H) →
    (∀ (h : H') (hh : ι h ∈ H) (w : W), q (σ ⟨ι h, hh⟩ w) = σ' h (q w)) →
    (∀ K' ∈ 𝓝 (1 : G'), ∃ K ∈ 𝓝 (1 : G), ∀ x : G', ∀ h ∈ H, ∀ κ ∈ K, ι x = h * κ →
      ∃ h' ∈ H', ∃ κ' ∈ K', x = h' * κ') →
    (∀ O ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O) →
    ∀ F : cIndSpace H' σ', ∃ f : cIndSpace H σ, ∀ x, F.1.1.1 x = q (f.1.1.1 (ι x)) := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.exists_cInd_restrict_eq | exact GlobalTheory.CompanionTheory.LeibPhi.exists_cInd_restrict_eq | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.exists_cInd_restrict_eq <;> assumption)
end

