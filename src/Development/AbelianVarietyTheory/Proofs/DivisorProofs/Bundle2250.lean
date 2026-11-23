module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0721
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
public import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0574
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0230
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2084
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2155
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteNormalGaloisCoverOfFinite
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.GalCover

theorem exists_isCN_galois_of_finite : ∀ (A R : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [CommRing R] [IsDomain R] (b : A →+* R), IsCN A → b.Finite → Function.Injective b → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (θ : R →+* R'), IsCN R' ∧ IsLocalHom θ ∧ Function.Injective θ ∧ θ.Finite ∧ ∀ r : R, (∀ σ : R' ≃+* R', IsOfFinOrder σ → (∀ a, σ (θ (b a)) = θ (b a)) → σ (θ r) = θ r) → r ∈ b.range := by
  intro A R _ _ _ _ _ b hA hfin hinj
  obtain ⟨hnoeth, hnorm, hcomp, hchar⟩ := hA
  letI : Algebra A R := b.toAlgebra
  haveI : Module.Finite A R := hfin
  haveI : Algebra.IsIntegral A R := Algebra.IsIntegral.of_finite A R
  let K := FractionRing A
  haveI : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective A K)
  let Ω := AlgebraicClosure K
  have hιK : Function.Injective (algebraMap A Ω) := by
    rw [IsScalarTower.algebraMap_eq A K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective A K)
  haveI : Module.IsTorsionFree A R := Module.isTorsionFree_iff_algebraMap_injective.2 hinj
  haveI : Module.IsTorsionFree A Ω := Module.isTorsionFree_iff_algebraMap_injective.2 hιK
  haveI : Algebra.IsAlgebraic A R := Algebra.IsIntegral.isAlgebraic
  let φ : R →ₐ[A] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hφinj : Function.Injective φ := by
    have hk : (RingHom.ker (φ : R →+* Ω)).comap (algebraMap A R) = ⊥ := by
      refine eq_bot_iff.2 fun a ha => ?_
      have h1 : φ (algebraMap A R a) = 0 := ha
      rw [φ.commutes] at h1
      exact (Ideal.mem_bot).2 (hιK (h1.trans (map_zero _).symm))
    have h2 := Ideal.eq_bot_of_under_eq_bot hk
    exact (RingHom.injective_iff_ker_eq_bot _).2 h2
  have hint : ∀ x : R, IsIntegral A (φ x) := fun x => (Algebra.IsIntegral.isIntegral (R := A) x).map φ
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := R)
  let L : IntermediateField K Ω := IntermediateField.adjoin K ((φ '' (s : Set R)) : Set Ω)
  have hintK : ∀ x : R, IsIntegral K (φ x) := fun x => (hint x).tower_top
  haveI : FiniteDimensional K L := IntermediateField.finiteDimensional_adjoin (by
    rintro _ ⟨x, -, rfl⟩
    exact hintK x)
  have hmemL : ∀ x : R, φ x ∈ L := fun x => by
    have hx : x ∈ Submodule.span A (s : Set R) := hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact IntermediateField.subset_adjoin K _ ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact zero_mem L
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | smul r y _ hy =>
      rw [map_smul, Algebra.smul_def]
      refine mul_mem ?_ hy
      rw [IsScalarTower.algebraMap_apply A K Ω]
      exact L.algebraMap_mem _
  let M : IntermediateField K Ω := IntermediateField.normalClosure K L Ω
  have hmem : ∀ x : R, φ x ∈ M := fun x => IntermediateField.le_normalClosure L (hmemL x)
  let W := integralClosure A M
  haveI hWf : Module.Finite A W := IsIntegralClosure.finite A K M W
  haveI : IsLocalRing W := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := A) W
  have hAM : Function.Injective (algebraMap A M) := by
    rw [IsScalarTower.algebraMap_eq A K M]
    exact (algebraMap K M).injective.comp (IsFractionRing.injective A K)
  have hinjW : Function.Injective (algebraMap A W) := fun x y h => hAM (congrArg Subtype.val h)
  let φM : R →+* M := (φ : R →+* Ω).codRestrict M hmem
  have hran : ∀ x : R, φM x ∈ W := fun x => by
    show IsIntegral A (φM x)
    exact (isIntegral_algHom_iff ((IntermediateField.val M).restrictScalars A) Subtype.val_injective).1 (hint x)
  let θ : R →+* W := φM.codRestrict W hran
  have hθval : ∀ x : R, (((θ x : M)) : Ω) = φ x := fun x => rfl
  have hθinj : Function.Injective θ := fun x y h => hφinj (by
    rw [← hθval, ← hθval, h])
  have hcomm : θ.comp b = algebraMap A W := RingHom.ext fun a => by
    apply Subtype.val_injective
    apply Subtype.val_injective
    exact φ.commutes a
  haveI : CharZero W := charZero_of_injective_algebraMap hinjW
  have hθfin : θ.Finite := RingHom.Finite.of_comp_finite (f := b) (by rw [hcomm]; exact RingHom.finite_algebraMap.2 hWf)
  have hθloc : IsLocalHom θ := RingHom.IsIntegral.isLocalHom hθfin.to_isIntegral hθinj

  let res : (M ≃ₐ[K] M) →* (W ≃+* W) :=
    { toFun := fun σ =>
        { toFun := fun x => ⟨σ (x : M), x.2.map ((σ : M →ₐ[K] M).restrictScalars A)⟩
          invFun := fun x => ⟨σ.symm (x : M), x.2.map ((σ.symm : M →ₐ[K] M).restrictScalars A)⟩
          left_inv := fun x => Subtype.ext (σ.symm_apply_apply (x : M))
          right_inv := fun x => Subtype.ext (σ.apply_symm_apply (x : M))
          map_mul' := fun x y => Subtype.ext (map_mul σ (x : M) y)
          map_add' := fun x y => Subtype.ext (map_add σ (x : M) y) }
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨W, inferInstance, inferInstance, inferInstance, θ,
    ⟨IsNoetherianRing.of_finite A W, integralClosure.isIntegrallyClosedOfFiniteExtension K,
      GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local A W, inferInstance⟩,
    hθloc, hθinj, hθfin, fun r hr => ?_⟩
  have hfix : ∀ σ : M ≃ₐ[K] M, σ (θ r : M) = (θ r : M) := fun σ => by
    have h1 := hr (res σ) (res.isOfFinOrder (isOfFinOrder_of_finite σ)) (fun a => by
      rw [← RingHom.comp_apply θ b, hcomm]
      apply Subtype.ext
      show σ (algebraMap A M a) = algebraMap A M a
      rw [IsScalarTower.algebraMap_apply A K M]
      exact σ.commutes _)
    exact congrArg Subtype.val h1
  obtain ⟨k, hk⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (θ r : M)).2 hfix
  have hkint : IsIntegral A k := by
    have : IsIntegral A (algebraMap K M k) := hk ▸ (θ r).2
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom A K M) (algebraMap K M).injective).1 this
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 hkint
  refine ⟨a, hφinj ?_⟩
  show φ (algebraMap A R a) = φ r
  rw [φ.commutes, ← hθval, ← hk, ← ha, IsScalarTower.algebraMap_apply A K Ω]
  rfl

end GlobalTheory.GalCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesGenerateConnectedLevels
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

theorem aeval_surjective_of_dUnit_span {K A : Type} [Field K] [CommRing A] [Bialgebra K A]
    [Module.Finite K A] (hconn : ∀ a ∈ augIdeal K A, IsNilpotent a) {d : ℕ} (x : Fin d → A)
    (hx : ∀ i, Coalgebra.counit (R := K) (x i) = 0)
    (hspan : ∀ c : Cot K A, ∃ l : Fin d → K, c = ∑ i, l i • dUnit (R := K) (x i)) :
    Function.Surjective (MvPolynomial.aeval (R := K) x) := by
  haveI : IsNoetherianRing A := isNoetherian_of_tower K inferInstance
  have hxm : ∀ i, x i ∈ RingHom.ker (counitAlgHom K A) := fun i => by
    rw [RingHom.mem_ker]; exact hx i
  have hnil : IsNilpotent (RingHom.ker (counitAlgHom K A)) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro a ha
    exact mem_nilradical.2 (hconn a ha)
  refine GlobalTheory.HeightOneHopf.aeval_surjective_of_span_cotangent (counitAlgHom K A) hnil x hxm ?_
  intro y hy
  obtain ⟨l, hl⟩ := hspan (dUnit (R := K) y)
  refine ⟨l, ?_⟩
  have hmem : y - ∑ i, l i • x i ∈ RingHom.ker (counitAlgHom K A) :=
    sub_mem hy (Ideal.sum_mem _ fun i _ => by
      rw [Algebra.smul_def]; exact Ideal.mul_mem_left _ _ (hxm i))
  have h0 : dUnit (R := K) (y - ∑ i, l i • x i) = 0 := by
    have e : dUnit (R := K) (y - ∑ i, l i • x i) = dUnit (R := K) y - ∑ i, l i • dUnit (R := K) (x i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [dUnit, map_sub, map_sum, map_smul]
    rw [e, ← hl, sub_self]
  rwa [dUnit, AugCot.d_of_mem _ hmem, Ideal.toCotangent_eq_zero] at h0

theorem exists_coords_generate (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0)
    (G : PDivGroup p K) (hG : G.IsConn) :
    ∃ x : ∀ n, Fin (Module.finrank K G.omega) → G.A n,
      (∀ n i, G.res n (x (n + 1) i) = x n i) ∧ (∀ n i, Coalgebra.counit (R := K) (x n i) = 0) ∧
        ∀ n, Function.Surjective (MvPolynomial.aeval (R := K) (x n)) := by
  haveI : Module.Finite K (Cot K (G.A 1)) :=
    Module.Finite.of_surjective (AugCot.d (counitAlgHom K (G.A 1))) (AugCot.d_surjective _)
  haveI : Module.Finite K G.omega :=
    Module.Finite.equiv (LinearEquiv.ofBijective _ (G.omegaLevel_one_bijective h)).symm
  set d := Module.finrank K G.omega with hd
  let b := Module.finBasis K G.omega
  have h1 : ∀ i, ∃ a : G.A 1, Coalgebra.counit (R := K) a = 0 ∧ dUnit (R := K) a = (b i).1 1 := by
    intro i
    obtain ⟨a, ha⟩ := AugCot.d_surjective (counitAlgHom K (G.A 1)) ((b i).1 1)
    refine ⟨a - algebraMap K _ (Coalgebra.counit (R := K) a), ?_, ?_⟩
    · have e : Coalgebra.counit (R := K) (algebraMap K (G.A 1) (Coalgebra.counit (R := K) a)) =
          Coalgebra.counit (R := K) a := by
        have := (counitAlgHom K (G.A 1)).commutes (Coalgebra.counit (R := K) a)
        simpa using this
      rw [map_sub, e, sub_self]
    · rw [dUnit, map_sub, AugCot.d_algebraMap, sub_zero]; exact ha
  choose x1 hx1c hx1d using h1
  let z : (n : ℕ) → Fin d → G.A (n + 1) := fun n =>
    Nat.rec (motive := fun n => Fin d → G.A (n + 1)) x1
      (fun n zn i => Function.surjInv (G.res_surjective (n + 1)) (zn i)) n
  let x : ∀ n, Fin d → G.A n := fun n =>
    Nat.rec (motive := fun n => Fin d → G.A n) (fun i => G.res 0 (x1 i)) (fun n _ => z n) n
  have hres : ∀ n i, G.res n (x (n + 1) i) = x n i := by
    intro n i
    cases n with
    | zero => rfl
    | succ n => exact Function.surjInv_eq (G.res_surjective (n + 1)) (z n i)
  have hcou1 : ∀ n i, Coalgebra.counit (R := K) (x (n + 1) i) = 0 := by
    intro n
    induction n with
    | zero => exact hx1c
    | succ n ih =>
      intro i
      rw [← ih i, ← hres (n + 1) i, CoalgHomClass.counit_comp_apply]
  have hcou : ∀ n i, Coalgebra.counit (R := K) (x n i) = 0 := by
    intro n i
    cases n with
    | zero => rw [← hres 0 i, CoalgHomClass.counit_comp_apply]; exact hcou1 0 i
    | succ n => exact hcou1 n i
  have hdu : ∀ n i, dUnit (R := K) (x (n + 1) i) = (b i).1 (n + 1) := by
    intro n
    induction n with
    | zero => exact hx1d
    | succ n ih =>
      intro i
      obtain ⟨u, hu⟩ := G.omegaLevel_surjective (n + 2) (dUnit (R := K) (x (n + 2) i))
      rw [omegaLevel_apply] at hu
      have hn : (u - b i).1 (n + 1) = 0 := by
        change u.1 (n + 1) - (b i).1 (n + 1) = 0
        rw [← ih i, ← cotMap_res_omega, hu, cotMap_d, hres, sub_self]
      have h1' : G.omegaLevel 1 (u - b i) = 0 :=
        G.omega_val_eq_zero_of_le (by omega) hn
      have hub : u = b i := sub_eq_zero.1
        ((G.omegaLevel_one_bijective h).1 (h1'.trans (map_zero _).symm))
      rw [← hu, hub]
  have hspan : ∀ n (c : Cot K (G.A n)), ∃ l : Fin d → K, c = ∑ i, l i • dUnit (R := K) (x n i) := by
    intro n c
    cases n with
    | zero => exact ⟨0, by rw [G.cot_zero_eq_zero c]; simp⟩
    | succ n =>
      obtain ⟨w, rfl⟩ := G.omegaLevel_surjective (n + 1) c
      refine ⟨b.repr w, ?_⟩
      conv_lhs => rw [← b.sum_repr w]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, omegaLevel_apply, hdu]
      rfl
  exact ⟨x, hres, hcou, fun n =>
    aeval_surjective_of_dUnit_span (hG n) (x n) (hcou n) (hspan n)⟩

end GlobalTheory.PDivGroup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCorrectionApproximateIdealSections
section
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Poinc

namespace GlobalTheory.ApproxCorr

theorem map_mem_pow {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] (φ : A →+* B) [IsLocalHom φ]
    {n : ℕ} {a : A} (h : a ∈ maximalIdeal A ^ n) : φ a ∈ maximalIdeal B ^ n := by
  have h1 := Ideal.mem_map_of_mem φ h
  rw [Ideal.map_pow] at h1
  exact Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le φ) n h1

theorem mem_of_forall_mem_sup {C : Type} [CommRing C] [IsLocalRing C] [IsNoetherianRing C] (I : Ideal C) (c : C)
    (h : ∀ n : ℕ, c ∈ I ⊔ maximalIdeal C ^ n) : c ∈ I := by
  have k := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := C ⧸ I) (maximalIdeal C) (maximalIdeal.isMaximal C).ne_top
  have : Submodule.mkQ I c ∈ (⊥ : Submodule C (C ⧸ I)) := by
    rw [← k, Submodule.mem_iInf]
    intro n
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (h n)
    have e : Submodule.mkQ I (a + b) = b • Submodule.mkQ I 1 := by
      rw [map_add (f := _), ← map_smul, smul_eq_mul, mul_one, (Submodule.Quotient.mk_eq_zero I).2 ha |> (Submodule.mkQ_apply I a).trans,
        zero_add]
    rw [e]
    exact Submodule.smul_mem_smul hb trivial
  exact (Submodule.Quotient.mk_eq_zero I).1 ((Submodule.mem_bot C).1 this)

theorem exists_stalk_map {Z S : Scheme.{0}} (π : S ⟶ Z) (x : S) (z : Z) (h : π x = z) :
    ∃ ψ : Z.presheaf.stalk z →+* S.presheaf.stalk x, IsLocalHom ψ ∧
      spMap ψ ≫ Z.fromSpecStalk z = S.fromSpecStalk x ≫ π := by
  subst h
  exact ⟨(π.stalkMap x).hom, π.toLRSHom.prop x, Scheme.SpecMap_stalkMap_fromSpecStalk π⟩

theorem mem_map_of_approx {Z S : Scheme.{0}} (π : S ⟶ Z) [IsProper π] (I : S.IdealSheafData) (z : Z)
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (i : Z.presheaf.stalk z →+* R) [IsLocalHom i] (hi : i.Flat)
    (F : R) (a : ℕ → Z.presheaf.stalk z) (ha : ∀ n, F - i (a n) ∈ maximalIdeal R ^ n)
    (H : ∀ (x : S) (ψ : Z.presheaf.stalk z →+* S.presheaf.stalk x), IsLocalHom ψ →
      spMap ψ ≫ Z.fromSpecStalk z = S.fromSpecStalk x ≫ π → ∀ n, ψ (a n) ∈ FinalTheorems.stalkId I x ⊔ maximalIdeal _ ^ n) :
    F ∈ (FinalTheorems.stalkId (I.map π) z).map i := by
  rw [← GlobalTheory.PolDiv.idlAlong_fromSpecStalk]
  generalize hξ : Spec.map (CommRingCat.ofHom i) ≫ Z.fromSpecStalk z = ξ
  have hfl : Flat ξ := by
    rw [← hξ]
    haveI := GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk Z z
    haveI : Flat (Spec.map (CommRingCat.ofHom i)) := (HasRingHomProperty.Spec_iff (P := @Flat)).2 hi
    infer_instance
  have hξc : ξ (closedPoint R) = z := by
    rw [← hξ]
    have : Spec.map (CommRingCat.ofHom i) (closedPoint R) = closedPoint (Z.presheaf.stalk z) :=
      IsLocalRing.comap_closedPoint i
    exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg (Z.fromSpecStalk z) this).trans Scheme.fromSpecStalk_closedPoint)
  refine GlobalTheory.FlatPush.mem_idlAlong_map_of_flat π I ξ ?_ F ?_
  · rw [Scheme.stalkClosedPointTo, CommRingCat.hom_comp]
    exact RingHom.Flat.comp (Flat.stalkMap ξ _) (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _))
  refine _root_.GlobalTheory.SpreadIdeal.mem_stalkId_of_closedFibre _ R (Limits.pullback.fst ξ π) _ _ fun v hv => ?_
  haveI : IsLocallyNoetherian (Limits.pullback ξ π) := LocallyOfFiniteType.isLocallyNoetherian (Limits.pullback.fst ξ π)
  set p := Limits.pullback.fst ξ π with hp
  set q := Limits.pullback.snd ξ π with hq
  have hpq : p ≫ ξ = q ≫ π := Limits.pullback.condition
  have hx : π (q v) = z := by
    rw [← Scheme.Hom.comp_apply, ← hpq, Scheme.Hom.comp_apply, hv, hξc]
  obtain ⟨ψ, hψ, hψc⟩ := exists_stalk_map π (q v) z hx
  let α : CommRingCat.of R ⟶ (Limits.pullback ξ π).presheaf.stalk v :=
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Sp R).presheaf.germ ⊤ (p v) trivial) ≫ p.stalkMap v
  have hα : Spec.map α = (Limits.pullback ξ π).fromSpecStalk v ≫ p := by
    rw [Spec.map_comp, ← Spec.fromSpecStalk_eq, Scheme.SpecMap_stalkMap_fromSpecStalk]
  haveI : IsLocalHom α.hom := by
    refine (IsLocalRing.isLocalHom_iff_comap_closedPoint _).2 ?_
    change Spec.map α (closedPoint _) = _
    rw [hα]
    exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg p Scheme.fromSpecStalk_closedPoint).trans hv)
  haveI : IsLocalHom (q.stalkMap v).hom := q.toLRSHom.prop v
  have hc : CommRingCat.ofHom i ≫ α = CommRingCat.ofHom ψ ≫ q.stalkMap v := by
    refine Spec.map_injective ((cancel_mono (Z.fromSpecStalk z)).1 ?_)
    rw [Spec.map_comp _ α, Spec.map_comp _ (q.stalkMap v), Category.assoc, Category.assoc, hξ, hα, Category.assoc, hpq]
    erw [hψc]
    rw [Scheme.SpecMap_stalkMap_fromSpecStalk_assoc]
  have hc' : ∀ t, α.hom (i t) = (q.stalkMap v).hom (ψ t) := fun t => congrArg (fun f => f.hom t) hc
  have e : ((Limits.pullback ξ π).presheaf.germ ⊤ v trivial).hom (p.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom F)) = α.hom F :=
    (Scheme.Hom.germ_stalkMap_apply p ⊤ v trivial _).symm
  rw [e]
  refine mem_of_forall_mem_sup _ _ fun n => ?_
  obtain ⟨b, hb, c, hc, hbc⟩ := Submodule.mem_sup.1 (H (q v) ψ hψ hψc n)
  have e2 : α.hom F = (q.stalkMap v).hom b + ((q.stalkMap v).hom c + α.hom (F - i (a n))) := by
    rw [← add_assoc, ← map_add (f := _), hbc, ← hc', map_sub]; ring
  rw [e2]
  exact Submodule.add_mem_sup (GlobalTheory.VanStalk.map_le_stalkId_comap q I v (Ideal.mem_map_of_mem _ hb))
    (add_mem (map_mem_pow _ hc) (map_mem_pow _ (ha n)))

theorem charZero_essFiniteType {S : Scheme.{0}} (s : S ⟶ Sp ℤ) [Flat s] [LocallyOfFiniteType s] (x : S) :
    CharZero (S.presheaf.stalk x) ∧ Algebra.EssFiniteType ℤ (S.presheaf.stalk x) := by
  let y : PrimeSpectrum ℤ := s x
  letI A : Algebra ℤ ((Sp ℤ).presheaf.stalk (s x)) := StructureSheaf.stalkAlgebra _ y
  haveI : @IsLocalization.AtPrime ℤ _ ((Sp ℤ).presheaf.stalk (s x)) _ A y.asIdeal _ :=
    StructureSheaf.IsLocalization.to_stalk _ y
  let φ := @algebraMap ℤ ((Sp ℤ).presheaf.stalk (s x)) _ _ A
  have h₁ : (s.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap s x
  have h₂ : φ.EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ y.asIdeal.primeCompl)
  have hφ : Function.Injective φ :=
    IsLocalization.injective ((Sp ℤ).presheaf.stalk (s x)) y.asIdeal.primeCompl_le_nonZeroDivisors
  have : IsLocalHom (s.stalkMap x).hom := s.toLRSHom.prop x
  have hσ : Function.Injective (s.stalkMap x).hom := by
    have h := Flat.stalkMap s x
    algebraize [(s.stalkMap x).hom]
    have : IsLocalHom (algebraMap ((Sp ℤ).presheaf.stalk (s x)) (S.presheaf.stalk x)) := this
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := (Sp ℤ).presheaf.stalk (s x)) (B := S.presheaf.stalk x)
    exact FaithfulSMul.algebraMap_injective ((Sp ℤ).presheaf.stalk (s x)) (S.presheaf.stalk x)
  refine ⟨charZero_of_injective_ringHom (f := (s.stalkMap x).hom.comp φ) (hσ.comp hφ), ?_⟩
  refine RingHom.essFiniteType_algebraMap.1 ?_
  convert h₂.comp h₁ using 1
  exact Subsingleton.elim _ _

theorem range_subset {S : Scheme.{0}} [IsIntegral S] (U : S.Opens) (hU : (U : Set S).Nonempty) (x : S)
    {V : Type} [CommRing V] [IsDomain V] (ρ : S.presheaf.stalk x →+* V) (hρ : Function.Injective ρ) :
    Set.range (jK V ≫ spMap ρ ≫ S.fromSpecStalk x) ⊆ U := by
  rintro _ ⟨t, rfl⟩
  have hg : genericPoint S ∈ Set.range (S.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]; exact genericPoint_specializes x
  obtain ⟨w, hw⟩ := hg
  have ht : (jK V ≫ spMap ρ) t ⤳ w := by
    refine (PrimeSpectrum.le_iff_specializes _ _).1 fun r hr => ?_
    have h0 : algebraMap V (FractionRing V) (ρ r) ∈ t.asIdeal := hr
    have h1 : algebraMap V (FractionRing V) (ρ r) = 0 := by
      by_contra hne
      exact t.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h0 (Ne.isUnit hne))
    have h2 : r = 0 := hρ (by rw [map_zero]; exact IsFractionRing.injective V (FractionRing V) (by rw [h1, map_zero]))
    rw [h2]; exact zero_mem _
  have h3 := ht.map (S.fromSpecStalk x).continuous
  rw [← Category.assoc, Scheme.Hom.comp_apply]
  have h4 : S.fromSpecStalk x ((jK V ≫ spMap ρ) t) = genericPoint S :=
    ((show _ ⤳ genericPoint S from hw ▸ h3).antisymm (genericPoint_specializes _)).eq
  rw [h4]
  exact ((genericPoint_spec S).mem_open_set_iff U.2).2 (by simpa using hU)

theorem exists_correction : ∀ (Z S : Scheme.{0}) [IsIntegral Z] [IsIntegral S] (sZ : Z ⟶ Sp ℤ) [LocallyOfFiniteType sZ] [QuasiCompact sZ] (π : S ⟶ Z) [IsProper π] [IsDominant π] [Flat (π ≫ sZ)], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S → ∀ (U : S.Opens), (U : Set S).Nonempty → ∀ (E : GlobalTheory.EffCartierData S) (z : Z) (k : ℕ), ∃ e : ℕ, ∀ f : Z.presheaf.stalk z, (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ (ξ : Sp V ⟶ S) (ev : Z.presheaf.stalk z →+* V), IsLocalHom ev → spMap ev ≫ Z.fromSpecStalk z = ξ ≫ π → Set.range (jK V ≫ ξ) ⊆ U → ev f ∈ idlAlong E.idealSheaf ξ ⊔ ((maximalIdeal _).map ev) ^ e) → f ∈ FinalTheorems.stalkId (E.idealSheaf.map π) z ⊔ maximalIdeal _ ^ k := by
  intro Z S _ _ sZ _ _ π _ _ _ hS U hU E z k
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  let K : ℕ → Ideal (Z.presheaf.stalk z) := fun e =>
    { carrier := {f | ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
        IsAdicComplete (maximalIdeal V) V → ∀ (ξ : Sp V ⟶ S) (ev : Z.presheaf.stalk z →+* V), IsLocalHom ev →
        spMap ev ≫ Z.fromSpecStalk z = ξ ≫ π → Set.range (jK V ≫ ξ) ⊆ U →
        ev f ∈ idlAlong E.idealSheaf ξ ⊔ ((maximalIdeal _).map ev) ^ e}
      add_mem' := fun ha hb V _ _ _ _ hV ξ ev h1 h2 h3 => by
        rw [map_add]; exact add_mem (ha V hV ξ ev h1 h2 h3) (hb V hV ξ ev h1 h2 h3)
      zero_mem' := fun V _ _ _ _ hV ξ ev h1 h2 h3 => by rw [map_zero]; exact zero_mem _
      smul_mem' := fun c a ha V _ _ _ _ hV ξ ev h1 h2 h3 => by
        rw [smul_eq_mul, map_mul]; exact Ideal.mul_mem_left _ _ (ha V hV ξ ev h1 h2 h3) }
  refine _root_.GlobalTheory.Chevalley.exists_le_sup_maximalIdeal_pow_of_antitone (Z.presheaf.stalk z) K (FinalTheorems.stalkId (E.idealSheaf.map π) z) ?_ ?_ ?_ k
  · intro m n hmn f hf V _ _ _ _ hV ξ ev h1 h2 h3
    exact (show _ ≤ (_ : Ideal V) from sup_le_sup_left (Ideal.pow_le_pow_right hmn) _) (hf V hV ξ ev h1 h2 h3)
  · intro e f hf V _ _ _ _ hV ξ ev h1 h2 h3
    refine Ideal.mem_sup_right ?_
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hf
  intro F a ha hK
  haveI := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ (maximalIdeal (Z.presheaf.stalk z))
  haveI : Module.FaithfullyFlat (Z.presheaf.stalk z) (AdicCompletion (maximalIdeal (Z.presheaf.stalk z)) (Z.presheaf.stalk z)) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  refine mem_map_of_approx π E.idealSheaf z _ (RingHom.flat_algebraMap_iff.2 inferInstance) F a ha fun x ψ hψ hc => ?_
  obtain ⟨i, hi⟩ : ∃ i, x ∈ E.U i := TopologicalSpace.Opens.mem_iSup.1 (E.cover ▸ trivial)
  obtain ⟨h0, hft⟩ := charZero_essFiniteType (π ≫ sZ) x
  haveI := (hS x).2
  have hI := E.stalkId_idealSheaf i x hi
  rw [hI]
  refine _root_.GlobalTheory.Poinc.mem_span_sup_pow_of_forall_complete_dvr (S.presheaf.stalk x) _ (fun n => ψ (a n))
    (nonZeroDivisors.ne_zero (GlobalTheory.Cartier.isRegularFn_iff_germ.1 (E.regular i) x hi)) ?_ ?_
  · intro m n hmn
    rw [← map_sub]
    refine map_mem_pow ψ ?_
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := AdicCompletion (maximalIdeal (Z.presheaf.stalk z)) (Z.presheaf.stalk z))
      (maximalIdeal (Z.presheaf.stalk z) ^ m), Ideal.mem_comap, Ideal.map_pow, ← AdicCompletion.maximalIdeal_eq_map, map_sub]
    have := sub_mem (Ideal.pow_le_pow_right hmn (ha n)) (ha m)
    rwa [sub_sub_sub_cancel_left] at this
  · intro V _ _ _ _ hV ρ hρ hl e
    have hl' : IsLocalHom (ρ.comp ψ) := inferInstance
    have h1 := hK e V hV (spMap ρ ≫ S.fromSpecStalk x) (ρ.comp ψ) hl' (by
      rw [Category.assoc, ← hc, ← Category.assoc, spMap, CommRingCat.ofHom_comp, Spec.map_comp]) (range_subset U hU x ρ hρ)
    rw [GlobalTheory.PolDiv.idlAlong_fromSpecStalk, hI, Ideal.map_span, Set.image_singleton] at h1
    exact (show _ ≤ (_ : Ideal V) from
      sup_le_sup_left (Ideal.pow_right_mono (IsLocalRing.map_maximalIdeal_le (ρ.comp ψ)) e) _) h1

end GlobalTheory.ApproxCorr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDatOfIsAdd
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

theorem exists_dat_of_isAdd : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) (f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))), CatCoh.H1.mk _ f = c.1 →
    ∀ g : Fn2 A, IsAdd (fv f) g → ∃ d : Dat t c, d.f = f ∧ d.g = g := by
  intro R _ A _ p G t c f hf g hg
  choose liftRes liftRes_spec using fun n ↦ G.res_surjective n
  let value (n : ℕ) : G.A n :=
    fv f (G.A (n + 1)) (G.A n) (G.res n).toAlgHom (t.y (n + 1))
  let h : ∀ n, G.A n := Nat.rec (motive := G.A) 0 (fun n a ↦ liftRes n (a - value n))
  refine ⟨⟨f, hf, g, hg, h, ?_⟩, rfl, rfl⟩
  intro n
  have hres : G.res n (h (n + 1)) = h n - value n := liftRes_spec n _
  change value n = h n - G.res n (h (n + 1))
  rw [hres, sub_sub_cancel]

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAgreementLocusSeparatedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_agreementLocus_separated : ∀ (H : Scheme.{0}) (Z G : Over H), IsFinite Z.hom → IsSeparated G.hom → ∀ (Ix : Type) [Finite Ix] (a b : Ix → (Z ⟶ G)), ∃ (Y : Over H) (i : Y ⟶ Z), IsFinite Y.hom ∧ (∀ k, i ≫ a k = i ≫ b k) ∧ ∀ (T : Over H) (h : T ⟶ Z), (∀ k, h ≫ a k = h ≫ b k) → ∃! h' : T ⟶ Y, h' ≫ i = h := by
  first | (exact @GlobalTheory.EqLocus.exists_finite_eqLocus) | (exact GlobalTheory.EqLocus.exists_finite_eqLocus) | (intros; apply GlobalTheory.EqLocus.exists_finite_eqLocus  <;> assumption)
end

