module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CoeffEqZeroOfSumSmulEqZeroOfSeparating
section
namespace GlobalTheory

theorem coeff_eq_zero_of_sum_smul_eq_zero_of_separating {Y A M : Type*} [CommRing A]
    [AddCommGroup M] [Module A M] (P : (Y → A) → Prop) (h1 : P 1)
    (hmul : ∀ t t', P t → P t' → P (t * t')) (s : Finset Y)
    (hsep : ∀ y ∈ s, ∀ z ∈ s, y ≠ z → ∃ t, P t ∧ IsUnit (t y - t z))
    (a : Y → M) (h : ∀ t, P t → ∑ y ∈ s, t y • a y = 0) : ∀ y ∈ s, a y = 0 := by
  classical
  induction s using Finset.strongInduction generalizing a with
  | H s ih =>
    intro y₀ hy₀
    by_cases hz : ∃ z ∈ s, z ≠ y₀
    · obtain ⟨z, hzs, hzy⟩ := hz
      obtain ⟨u, hu, hunit⟩ := hsep y₀ hy₀ z hzs (Ne.symm hzy)

      set b : Y → M := fun y => (u y - u z) • a y with hb
      have hbrel : ∀ t, P t → ∑ y ∈ s.erase z, t y • b y = 0 := by
        intro t ht
        rw [Finset.sum_erase s (by simp [hb])]
        have e : ∀ y, t y • b y = (t * u) y • a y - u z • (t y • a y) := by
          intro y
          simp only [hb, Pi.mul_apply, smul_smul, ← sub_smul]
          congr 1
          ring
        simp only [e, Finset.sum_sub_distrib, ← Finset.smul_sum, h t ht, h (t * u) (hmul t u ht hu),
          smul_zero, sub_zero]
      have hsub : s.erase z ⊂ s := Finset.erase_ssubset hzs
      have key := ih (s.erase z) hsub
        (fun y hy w hw hne => hsep y (Finset.mem_of_mem_erase hy) w (Finset.mem_of_mem_erase hw) hne)
        b hbrel y₀ (Finset.mem_erase.mpr ⟨Ne.symm hzy, hy₀⟩)
      exact (hunit.smul_eq_zero).mp key
    · push Not at hz
      have := h 1 h1
      rw [Finset.sum_eq_single_of_mem y₀ hy₀ (fun z hz' hne => absurd (hz z hz') hne)] at this
      simpa using this

theorem laurent_coeff_eq_zero_of_vanish_torsion :
    ∀ (Y : Type) [AddCommGroup Y] [Module.Free ℤ Y] [Module.Finite ℤ Y] (n : ℕ), n.Prime →
    ∀ s : Finset Y, ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (A : Type) [CommRing A] [IsLocalRing A] (ζ : A),
    IsUnit (n : A) → ζ ^ (n ^ j) = 1 → IsPrimitiveRoot (IsLocalRing.residue A ζ) (n ^ j) →
    ∀ (M : Type) [AddCommGroup M] [Module A M] (a : Y → M),
    (∀ t : Multiplicative Y →* Aˣ, (∀ y, t y ^ (n ^ j) = 1) →
      ∑ y ∈ s, (t (Multiplicative.ofAdd y) : A) • a y = 0) → ∀ y ∈ s, a y = 0 := by
  intro Y _ _ _ n hn s
  let b := Module.Free.chooseBasis ℤ Y

  refine ⟨∑ p ∈ s ×ˢ s, ∑ i, (b.repr (p.1 - p.2) i).natAbs, ?_⟩
  intro j hj A _ _ ζ _ hζ hprim M _ _ a ha
  have hN : n ^ j ≠ 0 := pow_ne_zero _ hn.ne_zero
  let u : Aˣ := Units.ofPowEqOne ζ (n ^ j) hζ hN
  have hu : u ^ (n ^ j) = 1 := Units.pow_ofPowEqOne hζ hN

  let χ : _ → Multiplicative Y →* Aˣ := fun i =>
    (zpowersHom Aˣ u).comp (AddMonoidHom.toMultiplicative (b.coord i).toAddMonoidHom)
  have hχ : ∀ i y, χ i (Multiplicative.ofAdd y) = u ^ (b.repr y i) := by
    intro i y
    simp [χ, zpowersHom]
  have hχord : ∀ i y, χ i y ^ (n ^ j) = 1 := by
    intro i y
    rw [show y = Multiplicative.ofAdd (Multiplicative.toAdd y) from rfl, hχ, ← zpow_natCast,
      ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu, one_zpow]
  let P : (Y → A) → Prop := fun f =>
    ∃ t : Multiplicative Y →* Aˣ, (∀ y, t y ^ (n ^ j) = 1) ∧ f = fun y => (t (Multiplicative.ofAdd y) : A)
  refine coeff_eq_zero_of_sum_smul_eq_zero_of_separating P ⟨1, fun _ => one_pow _, by funext; simp⟩
    ?_ s ?_ a ?_
  · rintro _ _ ⟨t, ht, rfl⟩ ⟨t', ht', rfl⟩
    exact ⟨t * t', fun y => by rw [MonoidHom.mul_apply, mul_pow, ht, ht', one_mul],
      by funext y; simp⟩
  · intro y hy z hz hyz
    have hw : b.repr (y - z) ≠ 0 := by
      rw [Ne, LinearEquiv.map_eq_zero_iff]
      exact sub_ne_zero.mpr hyz
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hw
    simp only [Finsupp.coe_zero, Pi.zero_apply] at hi
    refine ⟨_, ⟨χ i, hχord i, rfl⟩, ?_⟩
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hχ, hχ, map_sub]
    let v : (IsLocalRing.ResidueField A)ˣ := Units.map (IsLocalRing.residue A).toMonoidHom u
    have hv : IsPrimitiveRoot v (n ^ j) := IsPrimitiveRoot.coe_units_iff.mp (by simpa [v, u] using hprim)
    have hres : ∀ k : ℤ, IsLocalRing.residue A ((u ^ k : Aˣ) : A) = ((v ^ k : _ˣ) : _) := by
      intro k
      rw [show v ^ k = Units.map (IsLocalRing.residue A).toMonoidHom (u ^ k) from (map_zpow _ u k).symm]
      rfl
    rw [hres, hres, sub_ne_zero, Ne, Units.val_inj, ← div_eq_one, div_eq_mul_inv, ← zpow_sub, ← Finsupp.sub_apply,
      ← map_sub, hv.zpow_eq_one_iff_dvd]
    intro hdvd
    apply hi
    apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd
    have h1 : (b.repr (y - z) i).natAbs ≤ ∑ p ∈ s ×ˢ s, ∑ i, (b.repr (p.1 - p.2) i).natAbs := by
      refine le_trans ?_ (Finset.single_le_sum (f := fun p : Y × Y => ∑ i, (b.repr (p.1 - p.2) i).natAbs)
        (fun _ _ => Nat.zero_le _) (show (y, z) ∈ s ×ˢ s from Finset.mem_product.mpr ⟨hy, hz⟩))
      exact Finset.single_le_sum (f := fun i => (b.repr (y - z) i).natAbs) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)
    have h2 : j < n ^ j := Nat.lt_pow_self hn.one_lt
    simp only [Int.natAbs_natCast]
    omega
  · rintro _ ⟨t, ht, rfl⟩
    exact ha t ht

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
section
namespace GlobalTheory

namespace CompleteFiniteExtension

open IsLocalRing

theorem isPrecomplete_of_le_of_pow_le {A : Type*} [CommRing A] {I J : Ideal A} (hJ : J ≤ I)
    {e : ℕ} (he : I ^ e ≤ J) [IsPrecomplete J A] : IsPrecomplete I A := by
  first
  | (rename_i h_1 h_7; revert A h_1 I J hJ e he h_7; exact @_root_.GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le)
  | exact @_root_.GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le
  | exact _root_.GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le
  | (apply _root_.GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrecompleteOfPowLe.isPrecomplete_of_le_of_pow_le ..)

theorem isAdicComplete_of_finite_local (R S : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [CommRing S] [IsLocalRing S]
    [Algebra R S] [Module.Finite R S] : IsAdicComplete (maximalIdeal S) S := by
  have := IsNoetherianRing.of_finite R S
  have := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isAdicComplete_finite_algebra (R := R) S
  obtain ⟨e, he⟩ : ∃ e, maximalIdeal S ^ e ≤ (maximalIdeal R).map (algebraMap R S) := by
    refine Ideal.exists_pow_le_of_le_radical_of_fg (fun b hb => ?_) (IsNoetherian.noetherian _)
    obtain ⟨N, -, hN⟩ := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.exists_pow_mem_map_maximalIdeal (R := R) S b
      fun n hn => eq_maximalIdeal hn ▸ hb
    exact ⟨N, hN⟩
  have := isPrecomplete_of_le_of_pow_le
    (ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.map_maximalIdeal_le_maximal (R := R) S _ inferInstance) he
  exact ⟨⟩

end CompleteFiniteExtension

theorem exists_complete_dvr_finite_subalgebra :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
      [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [CharZero V] (F : Type) [Field F]
      [Algebra V F] [FaithfulSMul V F] [Algebra.IsAlgebraic V F] (s : Finset F),
      ∃ (W : Subalgebra V F) (_ : IsDiscreteValuationRing W),
        IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧
        IsAdicComplete ((IsLocalRing.maximalIdeal V).map (algebraMap V W)) W ∧
        Module.Finite V W ∧ Module.Free V W ∧ IsLocalHom (algebraMap V W) ∧
        (∀ x ∈ s, ∃ a ∈ W, ∃ b ∈ W, b ≠ 0 ∧ x * b = a) ∧
        ∀ x ∈ s, IsIntegral V x → x ∈ W := by
  intro V _ _ _ _ _ F _ _ _ _ s
  let K := FractionRing V
  let _ : Algebra K F := FractionRing.liftAlgebra V F
  have : IsScalarTower V K F := FractionRing.isScalarTower_liftAlgebra V F
  have : Algebra.IsAlgebraic K F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := V) (K := K) (C := F)).mp inferInstance
  let L : IntermediateField K F := IntermediateField.adjoin K (s : Set F)
  have : FiniteDimensional K L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let f : L →ₐ[V] F := L.val.restrictScalars V
  have hf : Function.Injective f := Subtype.val_injective
  let W : Subalgebra V F := (integralClosure V L).map f
  let e : integralClosure V L ≃ₐ[V] W := Subalgebra.equivMapOfInjective _ f hf
  have : CharZero K := IsFractionRing.charZero_of_isFractionRing V
  have hB : Module.Finite V (integralClosure V L) := IsIntegralClosure.finite V K L _
  have hBd : IsDiscreteValuationRing (integralClosure V L) :=
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr V K L
  have hfin : Module.Finite V W := Module.Finite.equiv e.toLinearEquiv
  have hd : IsDiscreteValuationRing W :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  have hmem : ∀ x ∈ L, IsIntegral V x → x ∈ W := fun x hx hi =>
    ⟨⟨x, hx⟩, (isIntegral_algHom_iff f hf).1 hi, rfl⟩
  have hsL : ∀ x ∈ s, x ∈ L := fun x hx => IntermediateField.subset_adjoin K _ hx
  refine ⟨W, hd, CompleteFiniteExtension.isAdicComplete_of_finite_local V W,
    ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isAdicComplete_finite_algebra W, hfin, inferInstance, inferInstance,
    fun x hx => ?_, fun x hx => hmem x (hsL x hx)⟩
  obtain ⟨y, hy, h⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := V) x).exists_integral_multiple
  refine ⟨y • x, hmem _ ?_ h, algebraMap V F y, W.algebraMap_mem y,
    (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective V F)).2 hy, ?_⟩
  · rw [← algebraMap_smul K y x]
    exact L.smul_mem (hsL x hx)
  · rw [Algebra.smul_def, mul_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenLiftOfIsNilpotent
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.GenLift

open GlobalTheory.LB

variable {X Y : Scheme.{0}}

theorem pullSec_surjective_of_le (f : Y ⟶ X) [IsClosedImmersion f] {L : LB X} (hL : L.IsLB)
    {V : X.Opens} (hV : IsAffineOpen V) (i : L.ι) (h : V ≤ L.U i) :
    Function.Surjective (pullSec L f V) := by
  intro s
  have h' : f ⁻¹ᵁ V ≤ (L.pull f).U (fun _ => i) :=
    (f.preimage_mono h).trans (pull_U f (fun _ => i)).ge
  obtain ⟨a, ha⟩ := f.app_surjective V hV (chartEquiv (Semi.LB.isLB_pull hL f) (fun _ => i) h' s)
  refine ⟨(chartEquiv hL i h).symm a, ?_⟩
  apply (chartEquiv (Semi.LB.isLB_pull hL f) (fun _ => i) h').injective
  rw [chartEquiv_pullSec f hL (fun _ => i) h h', LinearEquiv.apply_symm_apply]
  exact ha

theorem pullSec_surjective (f : Y ⟶ X) [IsClosedImmersion f] [IsAffine X] {L : LB X}
    (hL : L.IsLB) : Function.Surjective (pullSec L f ⊤) := by
  intro s
  haveI := isQuasicoherent_toMod hL
  haveI := isQuasicoherent_toMod (Semi.LB.isLB_pull hL f)
  let I : Ideal Γ(X, ⊤) :=
    { carrier := {c | ∃ σ, pullSec L f ⊤ σ = (f.app ⊤).hom c • s}
      add_mem' := by
        rintro a b ⟨σ, hσ⟩ ⟨τ, hτ⟩
        exact ⟨σ + τ, by rw [map_add (f := _), hσ, hτ, map_add (f := _), add_smul]⟩
      zero_mem' := ⟨0, by rw [map_zero, map_zero, zero_smul]⟩
      smul_mem' := by
        rintro a b ⟨σ, hσ⟩
        exact ⟨a • σ, by rw [LinearMap.map_smulₛₗ, hσ, smul_eq_mul, map_mul, mul_smul]⟩ }
  have key : ∀ x : X, ∃ c ∈ I, x ∈ X.basicOpen c := by
    intro x
    obtain ⟨i, hi⟩ := exists_chart hL x
    obtain ⟨a, ha, hx⟩ := (isAffineOpen_top X).exists_basicOpen_le ⟨x, hi⟩ (Opens.mem_top x)
    obtain ⟨u, hu⟩ := pullSec_surjective_of_le f hL ((isAffineOpen_top X).basicOpen a) i ha
      ((toMod (L.pull f)).presheaf.map (homOfLE (f.preimage_mono (X.basicOpen_le a))).op s)
    obtain ⟨n, σ, hσ⟩ := QCoh.exists_pow_smul_eq_res (toMod L) (isAffineOpen_top X) a
      (X.basicOpen_le a) rfl u
    obtain ⟨m, hm⟩ := QCoh.exists_pow_smul_eq_zero (toMod (L.pull f))
      ((isAffineOpen_top X).preimage f) ((f.app ⊤).hom a) (f.preimage_mono (X.basicOpen_le a))
      (f.preimage_basicOpen a) (pullSec L f ⊤ σ - (f.app ⊤).hom a ^ n • s) (by
        rw [map_sub, ← pullSec_map f (X.basicOpen_le a), ← hσ, LinearMap.map_smulₛₗ, hu, Scheme.Modules.map_smul,
          map_pow, map_pow, sub_eq_zero]
        congr 2
        exact congrArg (fun q => q.hom a) (f.naturality (homOfLE (X.basicOpen_le a)).op))
    refine ⟨a ^ (m + n + 1), ?_, by rwa [X.basicOpen_pow a (Nat.succ_pos _)]⟩
    rw [pow_succ']
    refine I.mul_mem_left a ⟨a ^ m • σ, ?_⟩
    rw [smul_sub, sub_eq_zero] at hm
    rw [LinearMap.map_smulₛₗ, map_pow, hm, map_pow, pow_add, mul_smul]
  have hI : I = ⊤ := by
    rw [← Ideal.span_eq I, ← (isAffineOpen_top X).iSup_basicOpen_eq_self_iff]
    refine top_le_iff.1 fun x _ => ?_
    obtain ⟨c, hc, hx⟩ := key x
    exact Opens.mem_iSup.2 ⟨⟨c, hc⟩, hx⟩
  obtain ⟨σ, hσ⟩ : (1 : Γ(X, ⊤)) ∈ I := hI ▸ Submodule.mem_top
  exact ⟨σ, by rw [hσ, map_one, one_smul]⟩

theorem isUnit_of_isUnit_app (f : Y ⟶ X) [Surjective f] {U : X.Opens} (a : Γ(X, U))
    (ha : IsUnit ((f.app U).hom a)) : IsUnit a := by
  refine X.toRingedSpace.isUnit_of_isUnit_germ U a fun x hx => ?_
  obtain ⟨y, rfl⟩ := f.surjective x
  have h₁ : y ∈ Y.basicOpen ((f.app U).hom a) := by
    rw [Y.basicOpen_of_isUnit ha]; exact hx
  have h₂ : y ∈ f ⁻¹ᵁ X.basicOpen a := by rw [f.preimage_basicOpen]; exact h₁
  exact (X.mem_basicOpen a (f y) hx).1 h₂

theorem exists_genPull_eq (f : Y ⟶ X) [IsClosedImmersion f] [Surjective f] [IsAffine X]
    {L : LB X} (hL : L.IsLB) (t₀ : LB.Gen (L.pull f)) (ht₀ : t₀.IsGen) :
    ∃ t : LB.Gen L, t.IsGen ∧ LB.genPull L t f = t₀ := by
  obtain ⟨σ, hσ⟩ := pullSec_surjective f hL (ofSec (genSec t₀ ht₀) _)
  obtain ⟨s, rfl⟩ := (globalEquiv L).symm.surjective σ
  have e : ∀ j : (L.pull f).ι,
      (f.appLE _ _ (pull_U_le f j)).hom (s.f (j PUnit.unit)) = (t₀.s j).val := fun j => by
    rw [← globalEquiv_pullSec_f f s j]
    exact congrArg (fun z : LB.Sec (L.pull f) => z.f j)
      ((congrArg (globalEquiv (L.pull f)) hσ).trans
        ((globalEquiv (L.pull f)).apply_symm_apply (genSec t₀ ht₀)))
  have hu : ∀ i, IsUnit (s.f i) := fun i => by
    refine isUnit_of_isUnit_app f _ ?_
    have h := ((e fun _ => i).symm ▸ (t₀.s fun _ => i).isUnit :
      IsUnit ((f.appLE _ _ (pull_U_le f fun _ => i)).hom (s.f i))).map
      (resG Y (pull_U f fun _ => i).ge)
    rwa [resG_appLE, Scheme.Hom.appLE_eq_app] at h
  refine ⟨⟨fun i => (hu i).unit⟩, fun i j => Units.ext (s.compat i j), ?_⟩
  cases t₀ with | mk t₀ => ?_
  exact congrArg LB.Gen.mk (funext fun j => Units.ext (e j))

end GlobalTheory.GenLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsRankOneBundle
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RankBundle

variable {X : Scheme.{0}}

theorem gs_one (x : X) (U : X.Opens) (h : x ∈ U) : gs (𝟙 X) x U 1 = 1 := by
  rw [gs_eq (𝟙 X) x U h, map_one, map_one]

theorem mem_basicOpen_iff (x : X) (U : X.Opens) (h : x ∈ U) (a : Γ(X, U)) :
    x ∈ X.basicOpen a ↔ IsUnit (gs (𝟙 X) x U a) := by
  rw [gs_eq (𝟙 X) x U h]
  exact X.mem_basicOpen a x h

theorem sec_compat {N : LB X} (s : LB.Sec N) (x : X) {k k' : N.ι} (hk : x ∈ N.U k) (hk' : x ∈ N.U k') :
    gs (𝟙 X) x (N.U k) (s.f k) = (gm (𝟙 X) x (N.U k ⊓ N.U k') (N.g k k')).val * gs (𝟙 X) x (N.U k') (s.f k') := by
  have hm : x ∈ N.U k ⊓ N.U k' := ⟨hk, hk'⟩
  exact (gs_res (𝟙 X) x _ hm _).symm.trans ((congrArg (gs (𝟙 X) x _) (s.compat k k')).trans
    ((gs_mul (𝟙 X) x _ hm _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 X) x _ hm _) (gs_res (𝟙 X) x _ hm _))))

theorem exists_ratio {U : X.Opens} (a b : Γ(X, U)) : ∃ r : Γ(X, X.basicOpen b), ∀ x ∈ X.basicOpen b,
    gs (𝟙 X) x (X.basicOpen b) r * gs (𝟙 X) x U b = gs (𝟙 X) x U a := by
  obtain ⟨u, hu⟩ : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le b)).op).hom b) :=
    X.toRingedSpace.isUnit_res_basicOpen b
  refine ⟨(X.presheaf.map (homOfLE (X.basicOpen_le b)).op).hom a * (u⁻¹).val, fun x hx => ?_⟩
  rw [← gs_res (𝟙 X) x (X.basicOpen_le b) hx b, ← gs_res (𝟙 X) x (X.basicOpen_le b) hx a,
    ← gs_mul (𝟙 X) x _ hx, ← hu, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]

theorem exists_rank_one_bundle : ∀ (X : Scheme.{0}) (N : LB X) (n m : ℕ) (w : Fin (n + 1) → Fin (m + 1) → LB.Sec N), N.IsLB → (⨆ i, ⨆ j, nonzeroLocus (w i j) = ⊤) → (∀ i i' j j' k, (w i j).f k * (w i' j').f k = (w i j').f k * (w i' j).f k) → ∃ (H' : LB X) (s' : Fin (n + 1) → LB.Sec H'), H'.IsLB ∧ (⨆ i, nonzeroLocus (s' i) = ⊤) ∧ ∀ (x : X) (c : H'.ι), x ∈ H'.U c → ∃ j, ∀ k, x ∈ N.U k → ∃ v : (X.presheaf.stalk x)ˣ, ∀ i, gs (𝟙 X) x (N.U k) ((w i j).f k) = v.val * gs (𝟙 X) x (H'.U c) ((s' i).f c) := by
  intro X N n m w hN hcov hr
  choose S hS using fun (l : Fin (n + 1)) (c : Fin (n + 1) × Fin (m + 1) × N.ι) =>
    exists_ratio ((w l c.2.1).f c.2.2) ((w c.1 c.2.1).f c.2.2)
  let U : Fin (n + 1) × Fin (m + 1) × N.ι → X.Opens := fun c => X.basicOpen ((w c.1 c.2.1).f c.2.2)
  have hle : ∀ c x, x ∈ U c → x ∈ N.U c.2.2 := fun c x hx => X.basicOpen_le _ hx
  have hu : ∀ c x, x ∈ U c → IsUnit (gs (𝟙 X) x (N.U c.2.2) ((w c.1 c.2.1).f c.2.2)) := fun c x hx =>
    (mem_basicOpen_iff x _ (hle c x hx) _).1 hx
  have one : ∀ c x, x ∈ U c → gs (𝟙 X) x (U c) (S c.1 c) = 1 := fun c x hx =>
    (hu c x hx).mul_right_cancel ((hS c.1 c x hx).trans (_root_.one_mul _).symm)
  have key : ∀ l c c' x, x ∈ U c → x ∈ U c' →
      gs (𝟙 X) x (U c) (S l c) = gs (𝟙 X) x (U c) (S c'.1 c) * gs (𝟙 X) x (U c') (S l c') := by
    intro l c c' x hx hx'
    have e₁ := hS l c x hx
    have e₂ := hS c'.1 c x hx
    have e₃ := hS l c' x hx'
    have e₄ := congrArg (gs (𝟙 X) x (N.U c.2.2)) (hr l c'.1 c.2.1 c'.2.1 c.2.2)
    rw [gs_mul (𝟙 X) x _ (hle c x hx), gs_mul (𝟙 X) x _ (hle c x hx),
      sec_compat (w c'.1 c'.2.1) x (hle c x hx) (hle c' x hx'),
      sec_compat (w l c'.2.1) x (hle c x hx) (hle c' x hx')] at e₄
    apply (((hu c x hx).mul (hu c' x hx')).mul
      (gm (𝟙 X) x (N.U c.2.2 ⊓ N.U c'.2.2) (N.g c.2.2 c'.2.2)).isUnit).mul_right_cancel
    rw [← e₁, ← e₂, ← e₃] at e₄
    exact Eq.trans (by ring) (e₄.trans (by ring))
  have hg : ∀ c c', IsUnit (rs X (inf_le_left : U c ⊓ U c' ≤ U c) (S c'.1 c)) := fun c c' =>
    IsUnit.of_mul_eq_one (rs X (inf_le_right : U c ⊓ U c' ≤ U c') (S c.1 c')) (fn_ext fun x hx => by
      rw [gs_mul (𝟙 X) x _ hx, gs_res (𝟙 X) x _ hx, gs_res (𝟙 X) x _ hx, ← key c.1 c c' x hx.1 hx.2,
        one c x hx.1, gs_one x _ hx])
  have gv : ∀ c c' x, x ∈ U c ⊓ U c' →
      (gm (𝟙 X) x (U c ⊓ U c') (hg c c').unit).val = gs (𝟙 X) x (U c) (S c'.1 c) := fun c c' x hx =>
    (gs_unit (𝟙 X) x _ hx _).symm.trans (gs_res (𝟙 X) x _ hx _)
  have ex : ∀ x : X, ∃ c, x ∈ U c := fun x => by
    have hx : x ∈ ⨆ i, ⨆ j, nonzeroLocus (w i j) := by rw [hcov]; trivial
    obtain ⟨i, hx⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    obtain ⟨j, hx⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    obtain ⟨k, hx⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    exact ⟨(i, j, k), hx⟩
  let H : LB X := ⟨Fin (n + 1) × Fin (m + 1) × N.ι, U, fun c c' => (hg c c').unit⟩
  let s : Fin (n + 1) → LB.Sec H := fun l => ⟨S l, fun c c' => fn_ext fun x hx =>
    (gs_res (𝟙 X) x _ hx _).trans ((key l c c' x hx.1 hx.2).trans ((gs_mul (𝟙 X) x _ hx _ _).trans
      (congrArg₂ (· * ·) (gs_res (𝟙 X) x _ hx _) (gs_res (𝟙 X) x _ hx _))).symm)⟩
  refine ⟨H, s, ⟨?_, fun c => unit_ext fun x hx => Units.ext ?_, fun a b c => unit_ext fun x hx => Units.ext ?_⟩, ?_, ?_⟩
  · exact top_unique fun x _ => TopologicalSpace.Opens.mem_iSup.2 (ex x)
  · rw [gm_res (𝟙 X) x _ hx, map_one, Units.val_one]
    exact (gv c c x ⟨hx, hx⟩).trans (one c x hx)
  · rw [map_mul, gm_res (𝟙 X) x _ hx, gm_res (𝟙 X) x _ hx, gm_res (𝟙 X) x _ hx, Units.val_mul]
    exact (congrArg₂ (· * ·) (gv a b x hx.1) (gv b c x ⟨hx.1.2, hx.2⟩)).trans
      ((key c.1 a b x hx.1.1 hx.1.2).symm.trans (gv a c x ⟨hx.1.1, hx.2⟩).symm)
  · refine top_unique fun x _ => ?_
    obtain ⟨c, hc⟩ := ex x
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨c.1, TopologicalSpace.Opens.mem_iSup.2 ⟨c, ?_⟩⟩
    exact (mem_basicOpen_iff x (U c) hc _).2 ((one c x hc).symm ▸ isUnit_one)
  · intro x c hc
    refine ⟨c.2.1, fun k hk => ⟨gm (𝟙 X) x (N.U k ⊓ N.U c.2.2) (N.g k c.2.2) * (hu c x hc).unit, fun l => ?_⟩⟩
    rw [sec_compat (w l c.2.1) x hk (hle c x hc), ← hS l c x hc, Units.val_mul, IsUnit.unit_spec, _root_.mul_assoc]
    exact congrArg _ (_root_.mul_comm _ _)

end GlobalTheory.RankBundle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecGeneratesSpecialFibre
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory

namespace SpecialFibreGenerator

open TopologicalSpace Opposite

variable {X Y : Scheme.{0}}

theorem mem_basicOpen_of_chart {L : LB X} (s : L.Sec) {a b : L.ι} {x : X} (ha : x ∈ L.U a)
    (hb : x ∈ X.basicOpen (s.f b)) : x ∈ X.basicOpen (s.f a) := by
  have h := congrArg X.basicOpen (s.compat a b)
  rw [Scheme.basicOpen_mul, X.basicOpen_of_isUnit (Units.isUnit _)] at h
  have h₁ := X.basicOpen_res (s.f a) (homOfLE (inf_le_left : L.U a ⊓ L.U b ≤ L.U a)).op
  have h₂ := X.basicOpen_res (s.f b) (homOfLE (inf_le_right : L.U a ⊓ L.U b ≤ L.U b)).op
  have hab : x ∈ L.U a ⊓ L.U b := ⟨ha, X.basicOpen_le _ hb⟩
  exact (h₁.le (h.ge ⟨hab, h₂.ge ⟨hab, hb⟩⟩)).2

noncomputable def secAlong {L : LB X} (s : L.Sec) (φ : Y ⟶ X) :
    (LB.LinComb L (K := Fin 1) (fun _ ↦ φ) fun _ ↦ ((1 : ℕ) : ℤ)).Sec where
  f a := φ.appLE (L.U (a 0)) (LB.wchart L (fun _ ↦ φ) a) (LB.wchart_le L (fun _ ↦ φ) a 0) (s.f (a 0))
  compat a b := by
    have hle : LB.wchart L (fun _ : Fin 1 ↦ φ) a ⊓ LB.wchart L (fun _ : Fin 1 ↦ φ) b ≤
        φ ⁻¹ᵁ (L.U (a 0) ⊓ L.U (b 0)) :=
      inf_le_inf (LB.wchart_le L (fun _ ↦ φ) a 0) (LB.wchart_le L (fun _ ↦ φ) b 0)
    have h := congrArg (φ.appLE (L.U (a 0) ⊓ L.U (b 0)) _ hle) (s.compat (a 0) (b 0))
    rw [map_mul] at h
    have hg : ((LB.LinComb L (K := Fin 1) (fun _ ↦ φ) fun _ ↦ ((1 : ℕ) : ℤ)).g a b).val =
        φ.appLE (L.U (a 0) ⊓ L.U (b 0)) _ hle (L.g (a 0) (b 0)).val := by
      simp only [LB.LinComb, Fin.prod_univ_one, Nat.cast_one, zpow_one]
      rfl
    rw [hg]
    refine ((PrimeSection.res_appLE φ _ _ _).trans (PrimeSection.appLE_res φ _ _ _).symm).trans
      (h.trans (congrArg (_ * ·) ?_))
    exact (PrimeSection.appLE_res φ _ _ _).trans (PrimeSection.res_appLE φ _ _ _).symm

theorem mem_nonzeroLocus_secAlong {L : LB X} (s : L.Sec) (φ : Y ⟶ X) {y : Y} {a : L.ι}
    (h : φ y ∈ X.basicOpen (s.f a)) : y ∈ nonzeroLocus (secAlong s φ) := by
  refine Opens.mem_iSup.2 ⟨fun _ ↦ a, ?_⟩
  change y ∈ Y.basicOpen (φ.appLE _ _ _ _)
  rw [Scheme.basicOpen_appLE]
  exact ⟨Set.mem_iInter.2 fun _ ↦ X.basicOpen_le _ h, h⟩

end SpecialFibreGenerator


end GlobalTheory
end

