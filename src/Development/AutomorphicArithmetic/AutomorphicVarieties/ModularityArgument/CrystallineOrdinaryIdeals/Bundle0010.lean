module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.Imports
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.SaturatedOrdinaryIdealCutsOutCrystallineLocus
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OrdinaryLocusIdealLeKerOfIsBasePointStatement
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.UnramifiedLiftDeformation
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0017
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.SaturatedOrdinaryIdealTangentFinrankEqTwelve
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0013

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OnOrdinaryComponentIffContinuousCrystallineLift
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc.OrdinaryEmbeddings

open nonZeroDivisors

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
  [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ))

omit [IsAdicComplete (maximalIdeal O) O] [IsDiscreteValuationRing O] [CharZero O] in
theorem inj_OE (E : Type) [Field E] [Algebra ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E]
    [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] : Function.Injective (algebraMap O E) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  refine Ideal.eq_bot_of_under_eq_bot (R := ℤ_[l]) ?_
  rw [Ideal.under_def, RingHom.comap_ker, ← IsScalarTower.algebraMap_eq, ← RingHom.injective_iff_ker_eq_bot,
    IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] E]
  exact (algebraMap ℚ_[l] E).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])

omit [IsAdicComplete (maximalIdeal O) O] [CharZero O] in
theorem inj_ZO : Function.Injective (algebraMap ℤ_[l] O) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  by_contra h
  have hp : (Ideal.comap (algebraMap ℤ_[l] O) ⊥).IsPrime := inferInstance
  have hm : (Ideal.comap (algebraMap ℤ_[l] O) ⊥).IsMaximal := hp.isMaximal h
  have h2 : (⊥ : Ideal O).IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := ℤ_[l]) _ hm
  exact IsDiscreteValuationRing.not_a_field O (IsLocalRing.eq_maximalIdeal h2).symm

theorem cont_push (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B]
    [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] (f : U.R →ₐ[O] B) (a b : Fin 3) :
    QCont l fun g => (push f U.r.hom g).mat a b :=
  (ptCont (l := l) U.R B f).1 (GQ l) (fun g => (U.r.hom g).mat a b) (U.r.cont a b)

omit [CharZero O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] in
theorem push_base (E : Type) [Field E] [Algebra O E] {x : U.R →ₐ[O] O} (hx : IsBase D.η D.Ψ U.r.hom x) :
    push ((Algebra.ofId O E).comp x) U.r.hom = D.rz E := by
  unfold Dat3.rz
  rw [← show push x U.r.hom = r0 D.η D.Ψ from hx]
  rfl


omit [CharZero O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] in
theorem IY_le_It : GlobalTheory.OrdLoc.IY D U ≤ GlobalTheory.OrdLoc.It D U :=
  Ideal.le_radical.trans (le_sInf fun _ hP => hP.1.1.2)

theorem reg (hP : LocalPublishedTheorems) {x : U.R →ₐ[O] O} (hx : IsBase D.η D.Ψ U.r.hom x) :
    ∃ y, x y ≠ 0 ∧ ∀ a ∈ GlobalTheory.OrdLoc.It D U, y * a ∈ GlobalTheory.OrdLoc.IY D U := by
  have hi := inj_ZO (l := l) (O := O)
  haveI : FaithfulSMul ℤ_[l] O := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  have hi2 : Function.Injective (algebraMap ℤ_[l] (FractionRing O)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] O (FractionRing O)]
    exact (IsFractionRing.injective O _).comp hi
  letI : Algebra ℚ_[l] (FractionRing O) := (IsFractionRing.lift hi2).toAlgebra
  haveI : IsScalarTower ℤ_[l] ℚ_[l] (FractionRing O) :=
    IsScalarTower.of_algebraMap_eq fun x => (IsFractionRing.lift_algebraMap hi2 x).symm
  haveI : IsLocalization (Algebra.algebraMapSubmonoid O ℤ_[l]⁰) (FractionRing O) := inferInstance
  haveI : Module.Finite ℚ_[l] (FractionRing O) := Module.Finite.of_isLocalization ℤ_[l] O ℤ_[l]⁰
  obtain ⟨-, n, P, φ, -, -, ⟨y, hy, hyP⟩, hPt, -⟩ := GlobalTheory.T.exists_unique_ordinaryPrime_dim_succ_near_base hP D U (FractionRing O) x hx
  exact ⟨y, hy, fun a ha => hyP a (hPt ▸ ha)⟩

end GlobalTheory.OrdLoc.OrdinaryEmbeddings


open GlobalTheory.OrdLoc.OrdinaryEmbeddings in
theorem GlobalTheory.OrdLoc.on_iff_inDcr : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ)) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] (B : Type) [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [Algebra O B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] O B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower O E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (r : GQ l →* UpperTheory.V.U3.GG (m := 3) (R := B)), (UpperTheory.V.U3.GG.map (π : B →+* E)).comp r = D.rz E → (GlobalTheory.OrdLoc.On D U r ↔ D.InDcr (π : B →+* E) r) := by
  intro hP l _ O _ _ _ _ _ _ _ D U E _ _ _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ r hr
  obtain ⟨hPts, hCr⟩ := _root_.GlobalTheory.OrdLoc.ideal_cuts_crystalline_locus hP D U
  constructor
  · rintro ⟨f, rfl, hf⟩
    exact ⟨fun g => U.r.hasMult g, hr, cont_push D U B f, hPts B f ((IY_le_It D U).trans hf)⟩
  · intro hd
    obtain ⟨x, hx, -⟩ := univEx D U
    obtain ⟨f, hf, -⟩ := unramified_lift_deformation D U E B π hπ ((Algebra.ofId O E).comp x) r hd.mult
      (hd.red.trans (push_base D U E hx).symm) hd.cont
    have hfY : GlobalTheory.OrdLoc.IY D U ≤ RingHom.ker f := hCr E B π hπ f (hf ▸ hd)
    have hfx : ∀ a, π (f a) = algebraMap O E (x a) := by
      intro a
      obtain ⟨g, -, hu⟩ := unramified_lift_deformation D U E E (AlgHom.id E E) (fun a ha => by simpa using ha)
        ((π.restrictScalars O).comp f) (push ((π.restrictScalars O).comp f) U.r.hom)
        (fun g => U.r.hasMult g) rfl (cont_push D U E _)
      have h1 : push ((π.restrictScalars O).comp f) U.r.hom = D.rz E := by
        rw [← hd.red, ← hf]; rfl
      have h := (hu ((π.restrictScalars O).comp f) rfl).trans
        (hu ((Algebra.ofId O E).comp x) ((push_base D U E hx).trans h1.symm)).symm
      exact congrArg (fun φ : U.R →ₐ[O] E => φ a) h
    obtain ⟨y, hy, hya⟩ := reg D U hP hx
    refine ⟨f, hf, fun a ha => ?_⟩
    have hne : algebraMap O E (x y) ≠ 0 := (map_ne_zero_iff _ (inj_OE (l := l) E)).2 hy
    have hnil : IsNilpotent (f y - algebraMap E B (algebraMap O E (x y))) := hπ _ (by
      rw [map_sub, hfx, AlgHom.commutes]
      exact sub_self _)
    have hu : IsUnit (f y) := by
      have := hnil.isUnit_add_right_of_commute (hne.isUnit.map (algebraMap E B)) (Commute.all _ _)
      simpa using this
    have h0 : f y * f a = 0 := by
      rw [← map_mul]
      exact hfY (hya a ha)
    exact (hu.mul_right_eq_zero).1 h0
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.OrdinaryComponentUniquePrimeDimThirteenNearBase
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory.OrdLoc

theorem component_basic : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ)), GlobalTheory.OrdLoc.primesAt0 D U = {GlobalTheory.OrdLoc.It D U} ∧ (GlobalTheory.OrdLoc.It D U).IsPrime ∧ (l : U.R) ∉ GlobalTheory.OrdLoc.It D U ∧ GlobalTheory.OrdLoc.Icr D U ≤ GlobalTheory.OrdLoc.It D U ∧ ringKrullDim (GlobalTheory.OrdLoc.Rt D U) = 13 ∧ GlobalTheory.OrdLoc.On D U (r0 D.η D.Ψ) ∧ ∀ x, IsBase D.η D.Ψ U.r.hom x → ∃ y, x y ≠ 0 ∧ ∀ a ∈ GlobalTheory.OrdLoc.It D U, y * a ∈ GlobalTheory.OrdLoc.Icr D U := by
  intro hP l _ O _ _ _ _ _ _ _ D U
  have hi : Function.Injective (algebraMap ℤ_[l] O) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra h
    have hp : (Ideal.comap (algebraMap ℤ_[l] O) ⊥).IsPrime := inferInstance
    have hm : (Ideal.comap (algebraMap ℤ_[l] O) ⊥).IsMaximal := hp.isMaximal h
    have h2 : (⊥ : Ideal O).IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := ℤ_[l]) ⊥ hm
    exact IsDiscreteValuationRing.not_a_field O (IsLocalRing.eq_maximalIdeal h2).symm
  haveI : FaithfulSMul ℤ_[l] O := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  have hi2 : Function.Injective (algebraMap ℤ_[l] (FractionRing O)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] O (FractionRing O)]
    exact (IsFractionRing.injective O _).comp hi
  letI : Algebra ℚ_[l] (FractionRing O) := (IsFractionRing.lift hi2).toAlgebra
  haveI : IsScalarTower ℤ_[l] ℚ_[l] (FractionRing O) :=
    IsScalarTower.of_algebraMap_eq fun x => (IsFractionRing.lift_algebraMap hi2 x).symm
  haveI : IsLocalization (Algebra.algebraMapSubmonoid O (nonZeroDivisors ℤ_[l])) (FractionRing O) := inferInstance
  haveI : Module.Finite ℚ_[l] (FractionRing O) :=
    Module.Finite.of_isLocalization ℤ_[l] O (nonZeroDivisors ℤ_[l])
  obtain ⟨x, hx, hxu⟩ := univEx D U
  obtain ⟨-, n, P, φ, hφ, hIP, ⟨y, hy, hyP⟩, hPI, h0, hdim⟩ := GlobalTheory.T.exists_unique_ordinaryPrime_dim_succ_near_base hP D U (FractionRing O) x hx
  have hmem : P ∈ primesAt0 D U := by rw [h0]; rfl
  have hmin := hmem.1
  have hPx : P ≤ RingHom.ker x := hmem.2 x hx
  let T : Submodule (FractionRing O) (U.R →ₗ[O] FractionRing O) :=
    { carrier := {δ | (∀ a b, δ (a * b) = algebraMap O _ (x a) * δ b + algebraMap O _ (x b) * δ a) ∧
        ∀ a ∈ IY D U, δ a = 0}
      zero_mem' := ⟨fun a b => by simp, fun a _ => rfl⟩
      add_mem' := by
        rintro δ δ' ⟨h1, h2⟩ ⟨h3, h4⟩
        refine ⟨fun a b => ?_, fun a ha => ?_⟩
        · simp only [LinearMap.add_apply, h1 a b, h3 a b]; ring
        · simp only [LinearMap.add_apply, h2 a ha, h4 a ha, add_zero]
      smul_mem' := by
        rintro c δ ⟨h1, h2⟩
        refine ⟨fun a b => ?_, fun a ha => ?_⟩
        · simp only [LinearMap.smul_apply, h1 a b, smul_eq_mul]; ring
        · simp only [LinearMap.smul_apply, h2 a ha, smul_zero] }
  have hT : ∀ δ, δ ∈ T ↔ (∀ a b, δ (a * b) = algebraMap O _ (x a) * δ b + algebraMap O _ (x b) * δ a) ∧
      ∀ a ∈ IY D U, δ a = 0 := fun δ => Iff.rfl
  have h1 := _root_.GlobalTheory.OrdLoc.tangent_finrank_eq_twelve hP D U (FractionRing O) x hx T hT
  have h2 : finrank (FractionRing O) ↥T = n := UpperTheory.finrank_pointDerivations_vanishing_eq_of_isCompl n P x φ hφ T fun δ => by
    rw [hT]
    refine and_congr_right fun h => ⟨fun h' a ha => ?_, fun h' a ha => h' a (hIP ha)⟩
    have e := h y a
    rw [h' _ (hyP a ha), show x a = 0 from hPx ha, map_zero, zero_mul, add_zero] at e
    exact (mul_eq_zero.1 e.symm).resolve_left fun h0 =>
      hy (IsFractionRing.injective O (FractionRing O) (h0.trans (map_zero _).symm))
  obtain rfl : n = 12 := by rw [← h2, h1]
  subst hPI
  refine ⟨h0, hmin.1.1, fun hl => ?_, hmin.1.2, hdim, ⟨x, hx, hPx⟩, fun x' hx' => ?_⟩
  · have h2 : x (l : U.R) = 0 := hPx hl
    rw [map_natCast] at h2
    exact (Fact.out : l.Prime).ne_zero (Nat.cast_eq_zero.1 h2)
  · rw [hxu x' hx']
    exact ⟨y, hy, fun a ha => Ideal.le_radical (hyP a ha)⟩

end GlobalTheory.OrdLoc
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.RtCompl
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

theorem GlobalTheory.OrdLoc.rtCompl : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (U : _root_.UpperTheory.V.U3.Univ (_root_.UpperTheory.V.U3.GCond.noCondition O D.η D.Ψ)) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing O E] (x : U.R →ₐ[O] O), IsBase D.η D.Ψ U.r.hom x → GlobalTheory.OrdLoc.primesAt0 D U = {GlobalTheory.OrdLoc.It D U} ∧ ∃ φ : U.R →ₐ[O] MvPowerSeries (Fin 12) E, UpperTheory.V.Loc.IsCompl (GlobalTheory.OrdLoc.It D U) x φ := by
  intro hL l _ O _ _ _ _ _ _ _ D U E _ _ _ _ _ _ _ _ x hx
  obtain ⟨-, n, P, φ, hφ, hIP, ⟨y, hy, hyP⟩, hIt, h0, -⟩ := GlobalTheory.T.exists_unique_ordinaryPrime_dim_succ_near_base hL D U E x hx
  have hPx : P ≤ RingHom.ker x := by
    have hm : P ∈ GlobalTheory.OrdLoc.primesAt0 D U := by rw [h0]; rfl
    exact hm.2 x hx
  let T : Submodule E (U.R →ₗ[O] E) :=
    { carrier := {δ | (∀ a b, δ (a * b) = algebraMap O E (x a) * δ b + algebraMap O E (x b) * δ a) ∧
        ∀ a ∈ GlobalTheory.OrdLoc.IY D U, δ a = 0}
      zero_mem' := ⟨by simp, by simp⟩
      add_mem' := by
        rintro δ δ' ⟨h1, h2⟩ ⟨h3, h4⟩
        refine ⟨fun a b => ?_, fun a ha => ?_⟩
        · simp only [LinearMap.add_apply, h1 a b, h3 a b]; ring
        · simp only [LinearMap.add_apply, h2 a ha, h4 a ha, add_zero]
      smul_mem' := by
        rintro c δ ⟨h1, h2⟩
        refine ⟨fun a b => ?_, fun a ha => ?_⟩
        · simp only [LinearMap.smul_apply, h1 a b, smul_eq_mul]; ring
        · simp only [LinearMap.smul_apply, h2 a ha, smul_zero] }
  have hT : ∀ δ, δ ∈ T ↔ (∀ a b, δ (a * b) = algebraMap O E (x a) * δ b + algebraMap O E (x b) * δ a) ∧
      ∀ a ∈ GlobalTheory.OrdLoc.IY D U, δ a = 0 := fun δ => Iff.rfl
  have h1 := _root_.GlobalTheory.OrdLoc.tangent_finrank_eq_twelve hL D U E x hx T hT
  have h2 : finrank E ↥T = n := UpperTheory.finrank_pointDerivations_vanishing_eq_of_isCompl n P x φ hφ T fun δ => by
    rw [hT]
    refine and_congr_right fun h => ⟨fun h' a ha => ?_, fun h' a ha => h' a (hIP ha)⟩
    have e := h y a
    rw [h' _ (hyP a ha), show x a = 0 from hPx ha, map_zero, zero_mul, add_zero] at e
    exact (mul_eq_zero.1 e.symm).resolve_left fun h0 =>
      hy (IsFractionRing.injective O E (h0.trans (map_zero _).symm))
  obtain rfl : n = 12 := by rw [← h2, h1]
  exact ⟨by rw [← hIt, h0], φ, hIt ▸ hφ⟩
end

