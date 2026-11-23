module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import ReciprocityTheory.DualLattices.Bundle0003
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0003
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.CompletionDVR

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.BtOrderOfPoints
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

namespace PositivityTheory.HtPt.Mk

theorem bt_pgsh : ∀ (R C : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field C] [Algebra R C], Function.Injective (algebraMap R C) → ∀ (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (A : Subalgebra R (Multiplicative N → R)), IsHopfOrder A → ∃ AA : ReciprocityTheory.PGsh.L2.HopfOrder R (C := C) N, ∀ f : N → C, f ∈ AA.carrier ↔ ∃ g ∈ A, ∀ x, f x = algebraMap R C (g (Multiplicative.ofAdd x)) := by
  intro R C _ _ _ _ _ hinj N _ _ _ A hA
  classical
  let φ : (Multiplicative N → R) →ₗ[R] (N → C) :=
    { toFun := fun g x => algebraMap R C (g (Multiplicative.ofAdd x))
      map_add' := by
        intro g h
        funext x
        simp
      map_smul' := by
        intro r g
        funext x
        simp [Algebra.smul_def] }
  have hφ : ∀ g x, φ g x = algebraMap R C (g (Multiplicative.ofAdd x)) := fun _ _ => rfl
  haveI := hA.finite
  haveI := hA.projective
  haveI : Module.Free R A := Module.free_of_flat_of_isLocalRing
  obtain ⟨d, hd0, hd⟩ := hA.full
  have hcardT : Module.finrank R (Multiplicative N → R) = Fintype.card N := by
    rw [Module.finrank_fintype_fun_eq_card]
    exact Fintype.card_congr Multiplicative.toAdd
  have hrank : Module.finrank R A = Fintype.card N := by
    apply le_antisymm
    · rw [← hcardT]
      exact LinearMap.finrank_le_finrank_of_injective (f := A.val.toLinearMap) Subtype.val_injective
    · let sc : (Multiplicative N → R) →ₗ[R] A :=
        { toFun := fun f => ⟨d • f, hd f⟩
          map_add' := fun f g => Subtype.ext (smul_add d f g)
          map_smul' := fun r f => Subtype.ext (smul_comm d r f) }
      have hsc : Function.Injective sc := by
        intro f g hfg
        have h2 : d • f = d • g := congrArg Subtype.val hfg
        exact smul_right_injective _ hd0 h2
      rw [← hcardT]
      exact LinearMap.finrank_le_finrank_of_injective hsc
  let b : Module.Basis N R A := (Module.finBasisOfFinrankEq R A hrank).reindex (Fintype.equivFin N).symm
  refine ⟨{ carrier := (Subalgebra.toSubmodule A).map φ
            lat := ?_
            le_int := ?_
            one_mem := ?_
            mul_mem := ?_
            comul := ?_
            antipode := ?_ }, ?_⟩
  · refine ⟨fun x j => φ (b j) x, ?_, ?_⟩
    · let M : Matrix N N R := fun x j => (b j : Multiplicative N → R) (Multiplicative.ofAdd x)
      have hdet : Matrix.det (fun x j => φ (b j) x : Matrix N N C) = algebraMap R C M.det := by
        rw [RingHom.map_det]
        rfl
      rw [hdet]
      apply isUnit_iff_ne_zero.mpr
      rw [map_ne_zero_iff _ hinj]
      intro h0
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
      apply hv0
      have hsum : ∑ j, v j • b j = 0 := by
        apply Subtype.ext
        funext t
        have h3 := congrFun hv (Multiplicative.toAdd t)
        simpa [Matrix.mulVec, dotProduct, M, mul_comm] using h3
      exact funext (Fintype.linearIndependent_iff.mp b.linearIndependent v hsum)
    · apply le_antisymm
      · rintro f ⟨g, hg, rfl⟩
        have hg' : (⟨g, hg⟩ : A) = ∑ j, b.repr ⟨g, hg⟩ j • b j := (b.sum_repr _).symm
        have hgs : g = ∑ j, b.repr ⟨g, hg⟩ j • (b j : Multiplicative N → R) := by
          have h4 : ((⟨g, hg⟩ : A) : Multiplicative N → R)
              = ((∑ j, b.repr ⟨g, hg⟩ j • b j : A) : Multiplicative N → R) := congrArg Subtype.val hg'
          rw [AddSubmonoidClass.coe_finsetSum] at h4
          exact h4
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hgs, map_sum]
        refine Submodule.sum_mem _ fun j _ => ?_
        rw [map_smul]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      · rw [Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        exact ⟨b j, (b j).2, rfl⟩
  · rintro f ⟨g, hg, rfl⟩ x
    exact ⟨g (Multiplicative.ofAdd x), rfl⟩
  · refine ⟨1, A.one_mem, ?_⟩
    funext x
    simp [hφ]
  · rintro f g ⟨f', hf', rfl⟩ ⟨g', hg', rfl⟩
    refine ⟨f' * g', A.mul_mem hf' hg', ?_⟩
    funext x
    simp [hφ]
  · rintro f ⟨g, hg, rfl⟩
    let ψ : (Multiplicative N × Multiplicative N → R) →ₗ[R] (N × N → C) :=
      { toFun := fun F p => algebraMap R C (F (Multiplicative.ofAdd p.1, Multiplicative.ofAdd p.2))
        map_add' := by
          intro F G
          funext p
          simp
        map_smul' := by
          intro r F
          funext p
          simp [Algebra.smul_def] }
    have hle : GlobalTheory.CompanionTheory.Ar.BT.prodSpan A ≤
        (ReciprocityTheory.PGsh.L2.tensorSpan R ((Subalgebra.toSubmodule A).map φ)).comap ψ := by
      rw [GlobalTheory.CompanionTheory.Ar.BT.prodSpan, Submodule.span_le]
      rintro _ ⟨a, ha, a', ha', rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap]
      apply Submodule.subset_span
      refine ⟨φ a, ⟨a, ha, rfl⟩, φ a', ⟨a', ha', rfl⟩, ?_⟩
      funext p
      simp [hφ, ψ]
    have h5 := hle (hA.comul g hg)
    rw [Submodule.mem_comap] at h5
    convert h5 using 1
    funext p
    simp [hφ, ψ, ReciprocityTheory.PGsh.L2.addPull, LinearMap.funLeft_apply]
  · rintro f ⟨g, hg, rfl⟩
    refine ⟨fun t => g t⁻¹, hA.inv g hg, ?_⟩
    funext x
    simp [hφ]
  · intro f
    show f ∈ (Subalgebra.toSubmodule A).map φ ↔ _
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨g, hg, fun x => rfl⟩
    · rintro ⟨g, hg, hfg⟩
      exact ⟨g, hg, funext fun x => (hfg x).symm⟩

end PositivityTheory.HtPt.Mk
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfDesc
section
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace PositivityTheory.HtPt.Htat.HopfOrderFlatLocal

theorem flat_localized_of_flat_baseChange {R : Type} [CommRing R] (M : Type) [AddCommGroup M]
    [Module R M] (P : Ideal R) [P.IsMaximal] (R' : Type) [CommRing R'] [IsLocalRing R']
    [Algebra R R'] [Module.Flat R R']
    (hP : (IsLocalRing.maximalIdeal R').comap (algebraMap R R') = P)
    [Module.Flat R' (R' ⊗[R] M)] : Module.Flat R (LocalizedModule P.primeCompl M) := by
  let Rp := Localization.AtPrime P
  have hu : ∀ y : P.primeCompl, IsUnit (algebraMap R R' y) := by
    intro y
    by_contra h
    have h1 : (y : R) ∈ (IsLocalRing.maximalIdeal R').comap (algebraMap R R') :=
      (IsLocalRing.mem_maximalIdeal _).2 h
    exact y.2 (hP.le h1)
  let ψ : Rp →+* R' := IsLocalization.lift hu
  letI : Algebra Rp R' := ψ.toAlgebra
  have hψ : ∀ r : R, algebraMap Rp R' (algebraMap R Rp r) = algebraMap R R' r :=
    fun r => IsLocalization.lift_eq hu r
  haveI : IsScalarTower R Rp R' := .of_algebraMap_eq (fun r => (hψ r).symm)
  haveI : Module.Flat Rp R' := (Module.flat_iff_of_isLocalization Rp P.primeCompl R').2 inferInstance
  haveI : IsLocalHom (algebraMap Rp R') := ⟨fun x hx => by
    obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl x
    have e : algebraMap R R' r =
        algebraMap Rp R' (IsLocalization.mk' Rp r s) * algebraMap R R' s := by
      rw [← hψ s, ← map_mul, IsLocalization.mk'_spec, hψ]
    have hr : IsUnit (algebraMap R R' r) := by
      rw [e]; exact hx.mul (hu s)
    have hrP : r ∈ P.primeCompl := by
      intro hmem
      rw [← hP] at hmem
      exact (IsLocalRing.mem_maximalIdeal _).1 hmem hr
    have h3 : IsUnit (algebraMap R Rp r) :=
      IsLocalization.map_units Rp (⟨r, hrP⟩ : P.primeCompl)
    rw [← IsLocalization.mk'_spec Rp r s] at h3
    exact isUnit_of_mul_isUnit_left h3⟩
  haveI : Module.FaithfullyFlat Rp R' := Module.FaithfullyFlat.of_flat_of_isLocalHom
  haveI : Module.Flat R' (R' ⊗[Rp] (Rp ⊗[R] M)) :=
    Module.Flat.of_linearEquiv (AlgebraTensorModule.cancelBaseChange R Rp R' R' M)
  haveI : Module.Flat Rp (Rp ⊗[R] M) := Module.Flat.of_flat_tensorProduct Rp (Rp ⊗[R] M) R'
  haveI : Module.Flat R (Rp ⊗[R] M) :=
    (Module.flat_iff_of_isLocalization Rp P.primeCompl (Rp ⊗[R] M)).1 inferInstance
  exact Module.Flat.of_linearEquiv
    (IsLocalizedModule.linearEquiv P.primeCompl (LocalizedModule.mkLinearMap P.primeCompl M)
      (TensorProduct.mk R Rp M 1))

theorem flat_baseChange_of_flat_extOrder {R : Type} [CommRing R] {T : Type} [CommGroup T] [Finite T]
    (A : Subalgebra R (T → R)) (R' : Type) [CommRing R'] [Algebra R R'] [Module.Flat R R']
    [Module.Flat R' (extOrder (algebraMap R R') A)] : Module.Flat R' (R' ⊗[R] A) := by
  classical
  cases nonempty_fintype T
  let L : R' ⊗[R] A →ₗ[R'] (T → R') :=
    (TensorProduct.piScalarRight R R' R' T).toLinearMap ∘ₗ LinearMap.baseChange R' A.val.toLinearMap
  have hL : ∀ (r : R') (a : A), L (r ⊗ₜ a) = fun t => r * algebraMap R R' ((a : T → R) t) := by
    intro r a
    ext t
    simp [L, Algebra.smul_def, mul_comm]
  have hinj : Function.Injective L := by
    have h1 : Function.Injective (LinearMap.baseChange R' A.val.toLinearMap) := by
      rw [LinearMap.baseChange_eq_ltensor]
      exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
    exact (TensorProduct.piScalarRight R R' R' T).injective.comp h1
  have hrange : LinearMap.range L = Subalgebra.toSubmodule (extOrder (algebraMap R R') A) := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      induction x using TensorProduct.inductionOn with
      | tmul r a =>
        rw [hL]
        have : (fun t => algebraMap R R' ((a : T → R) t)) ∈ extOrder (algebraMap R R') A :=
          Algebra.subset_adjoin ⟨a, a.2, rfl⟩
        exact (extOrder (algebraMap R R') A).smul_mem this r
      | add x y hx hy => rw [map_add]; exact add_mem hx hy
    · intro g hg
      have h := (PositivityTheory.HtPt.Htat.ext_span R T R' (algebraMap R R') A g).1 hg
      refine Submodule.span_le.2 ?_ h
      rintro _ ⟨f, hf, rfl⟩
      exact ⟨(1 : R') ⊗ₜ ⟨f, hf⟩, by rw [hL]; simp⟩
  haveI : Module.Flat R' (Subalgebra.toSubmodule (extOrder (algebraMap R R') A)) :=
    inferInstanceAs (Module.Flat R' (extOrder (algebraMap R R') A))
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofInjective L hinj ≪≫ₗ LinearEquiv.ofEq _ _ hrange)

theorem mul_mem_span_prodSpan_of_mem_span {R : Type} [CommRing R] {T : Type} [CommGroup T] {R' : Type} [CommRing R']
    (φ : R →+* R') (A : Subalgebra R (T → R)) {a b : T → R'}
    (ha : a ∈ Submodule.span R' {g : T → R' | ∃ f ∈ A, g = fun t => φ (f t)})
    (hb : b ∈ Submodule.span R' {g : T → R' | ∃ f ∈ A, g = fun t => φ (f t)}) :
    (fun z : T × T => a z.1 * b z.2) ∈
      Submodule.span R' {g : T × T → R' | ∃ n ∈ prodSpan A, g = fun i => φ (n i)} := by
  induction ha using Submodule.span_induction with
  | mem a h =>
    obtain ⟨a₀, ha₀, rfl⟩ := h
    induction hb using Submodule.span_induction with
    | mem b h =>
      obtain ⟨b₀, hb₀, rfl⟩ := h
      exact Submodule.subset_span ⟨fun z => a₀ z.1 * b₀ z.2,
        Submodule.subset_span ⟨a₀, ha₀, b₀, hb₀, rfl⟩, by ext z; simp⟩
    | zero =>
      convert Submodule.zero_mem _ using 1
      ext z; simp
    | add x y _ _ hx hy =>
      convert add_mem hx hy using 1
      ext z; simp [mul_add]
    | smul c x _ hx =>
      convert Submodule.smul_mem _ c hx using 1
      ext z; simp; ring
  | zero =>
      convert Submodule.zero_mem _ using 1
      ext z; simp
  | add x y _ _ hx hy =>
    convert add_mem hx hy using 1
    ext z; simp [add_mul]
  | smul c x _ hx =>
    convert Submodule.smul_mem _ c hx using 1
    ext z; simp; ring

theorem prodSpan_extOrder_le {R : Type} [CommRing R] {T : Type} [CommGroup T] {R' : Type}
    [CommRing R'] (φ : R →+* R') (A : Subalgebra R (T → R)) :
    prodSpan (extOrder φ A) ≤
      Submodule.span R' {g : T × T → R' | ∃ n ∈ prodSpan A, g = fun i => φ (n i)} := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, ha, b, hb, rfl⟩
  exact mul_mem_span_prodSpan_of_mem_span φ A ((PositivityTheory.HtPt.Htat.ext_span R T R' φ A a).1 ha) ((PositivityTheory.HtPt.Htat.ext_span R T R' φ A b).1 hb)

theorem isHopfOrder_of_flat_local :
    ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] [IsNoetherianRing R]
      (A : Subalgebra R (T → R)), (∃ d : R, d ≠ 0 ∧ ∀ f : T → R, d • f ∈ A) →
      (∀ P : Ideal R, P.IsMaximal → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R')
        (_ : IsLocalRing R') (_ : Algebra R R'), Module.Flat R R' ∧
        (IsLocalRing.maximalIdeal R').comap (algebraMap R R') = P ∧
        IsHopfOrder (extOrder (algebraMap R R') A)) → IsHopfOrder A := by
  intro R _ _ T _ _ _ A hfull H
  haveI hfin : Module.Finite R A :=
    Module.Finite.of_injective A.val.toLinearMap Subtype.val_injective
  haveI : Module.FinitePresentation R A := Module.finitePresentation_of_finite R A
  haveI hflat : Module.Flat R A := Module.flat_of_localized_maximal A fun P hP => by
    obtain ⟨R', _, _, _, _, hf, hP', hH⟩ := H P hP
    haveI := hH.projective
    haveI : Module.Flat R' (R' ⊗[R] A) := flat_baseChange_of_flat_extOrder A R'
    exact flat_localized_of_flat_baseChange A P R' hP'
  refine ⟨hfin, Module.Flat.projective_of_finitePresentation, hfull, ?_, ?_⟩
  · intro f hf
    refine PositivityTheory.HtPt.Htat.mem_descent R (T × T) (prodSpan A) _ fun P hP => ?_
    obtain ⟨R', i1, i2, i3, i4, hf', hP', hH⟩ := H P hP
    refine ⟨R', i1, i3, i4, hf', hP', ?_⟩
    have h1 : (fun t => algebraMap R R' (f t)) ∈ extOrder (algebraMap R R') A :=
      Algebra.subset_adjoin ⟨f, hf, rfl⟩
    exact prodSpan_extOrder_le _ A (hH.comul _ h1)
  · intro f hf
    refine PositivityTheory.HtPt.Htat.mem_descent R T (Subalgebra.toSubmodule A) _ fun P hP => ?_
    obtain ⟨R', i1, i2, i3, i4, hf', hP', hH⟩ := H P hP
    refine ⟨R', i1, i3, i4, hf', hP', ?_⟩
    have h1 : (fun t => algebraMap R R' (f t)) ∈ extOrder (algebraMap R R') A :=
      Algebra.subset_adjoin ⟨f, hf, rfl⟩
    exact (PositivityTheory.HtPt.Htat.ext_span R T R' (algebraMap R R') A _).1 (hH.inv _ h1)

end PositivityTheory.HtPt.Htat.HopfOrderFlatLocal
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.KftwoExt
section
noncomputable section

open IsLocalRing Formalism.L2.Pj

namespace PositivityTheory.HtPt.Kftwo

theorem exists_completion (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W] :
    ∃ (T : CDVR) (g : W →+* T.V), IsLocalHom g ∧ Function.Injective g := by
  obtain ⟨⟨hdom, hdvr⟩, hcpl, hinj, hloc, -⟩ := ReciprocityTheory.CA.Pt.completionDVR W
  haveI : CharZero (AdicCompletion (maximalIdeal W) W) := charZero_of_injective_algebraMap hinj
  exact ⟨CDVR.mk (AdicCompletion (maximalIdeal W) W),
    algebraMap W (AdicCompletion (maximalIdeal W) W), hloc, hinj⟩

theorem exists_cdvr_of_isIntegral {V A : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing A]
    [IsDedekindDomain A] [CharZero A] [Algebra V A] [Algebra.IsIntegral V A] (hinj : Function.Injective (algebraMap V A)) :
    ∃ (T : CDVR) (g : A →+* T.V), IsLocalHom (g.comp (algebraMap V A)) ∧ Function.Injective g := by
  have hker : RingHom.ker (algebraMap V A) ≤ maximalIdeal V := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
    exact bot_le
  obtain ⟨P, hPmax, hPc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (maximalIdeal V) hker
  haveI : P.IsPrime := hPmax.isPrime
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    apply IsDiscreteValuationRing.not_a_field V
    rw [← hPc, Ideal.under_def, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp hinj]
  haveI : IsDomain (Localization.AtPrime P) :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors P)
  haveI : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hP0 (Localization.AtPrime P)
  have hAinj : Function.Injective (algebraMap A (Localization.AtPrime P)) :=
    IsLocalization.injective (Localization.AtPrime P) (Ideal.primeCompl_le_nonZeroDivisors P)
  haveI : CharZero (Localization.AtPrime P) := charZero_of_injective_algebraMap hAinj
  obtain ⟨T, g0, hg0, hg0inj⟩ := exists_completion (Localization.AtPrime P)
  refine ⟨T, g0.comp (algebraMap A (Localization.AtPrime P)), ⟨fun x hx => ?_⟩, hg0inj.comp hAinj⟩
  simp only [RingHom.comp_apply] at hx
  have h1 : IsUnit (algebraMap A (Localization.AtPrime P) (algebraMap V A x)) := isUnit_of_map_unit g0 _ hx
  rw [IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime P) P] at h1
  by_contra hxu
  have hx' : x ∈ maximalIdeal V := hxu
  rw [← hPc] at hx'
  exact h1 (Ideal.mem_comap.mp hx')

theorem exists_cdvr {V K K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [CharZero K]
    [Algebra V K] [IsFractionRing V K] [Field K'] [Algebra K K'] [FiniteDimensional K K'] :
    ∃ (T : CDVR) (g : V →+* T.V) (j : K' →+* T.Fr), IsLocalHom g ∧
      (algebraMap T.V T.Fr).comp g = (j.comp (algebraMap K K')).comp (algebraMap V K) := by
  letI : Algebra V K' := ((algebraMap K K').comp (algebraMap V K)).toAlgebra
  haveI : IsScalarTower V K K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : CharZero K' := charZero_of_injective_algebraMap (algebraMap K K').injective
  haveI : IsDedekindDomain (integralClosure V K') := integralClosure.isDedekindDomain V K K'
  haveI : IsFractionRing (integralClosure V K') K' :=
    integralClosure.isFractionRing_of_finite_extension K K'
  haveI : CharZero (integralClosure V K') :=
    ⟨fun m n h => Nat.cast_injective (R := K')
      (by simpa using congrArg (algebraMap (integralClosure V K') K') h)⟩
  have hVK' : Function.Injective (algebraMap V K') :=
    (algebraMap K K').injective.comp (IsFractionRing.injective V K)
  have hinj : Function.Injective (algebraMap V (integralClosure V K')) := by
    refine Function.Injective.of_comp (f := algebraMap (integralClosure V K') K') ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
    exact hVK'
  obtain ⟨T, g, hg, hginj⟩ := exists_cdvr_of_isIntegral hinj
  have hjinj : Function.Injective ((algebraMap T.V T.Fr).comp g) :=
    (IsFractionRing.injective T.V T.Fr).comp hginj
  refine ⟨T, g.comp (algebraMap V (integralClosure V K')),
    IsFractionRing.lift (K := K') hjinj, hg, ?_⟩
  ext x
  simp only [RingHom.comp_apply]
  rw [← IsScalarTower.algebraMap_apply V K K',
    IsScalarTower.algebraMap_apply V (integralClosure V K') K', IsFractionRing.lift_algebraMap]
  rfl

end PositivityTheory.HtPt.Kftwo
end
end

