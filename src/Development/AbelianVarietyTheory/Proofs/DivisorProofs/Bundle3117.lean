module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3107
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0693
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0695
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0690
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0694
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0689
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1161
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1141
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3110
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3097

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RemainderTermSummable
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open scoped TensorProduct

namespace GlobalTheory.QuotientCardinalityFinrank

theorem free_baseChange_quot (K : Type) [Field K] [NumberField K] (L : Type) [AddCommGroup L]
    [Module (𝓞 K) L] [Module.Finite (𝓞 K) L] [Module.IsTorsionFree (𝓞 K) L] (ℓ : ℕ) (hℓ : ℓ.Prime)
    (j : ℕ) :
    Module.Free (𝓞 K ⧸ Ideal.span {((ℓ ^ j : ℕ) : 𝓞 K)})
      ((𝓞 K ⧸ Ideal.span {((ℓ ^ j : ℕ) : 𝓞 K)}) ⊗[𝓞 K] L) := by
  set I := Ideal.span {((ℓ ^ j : ℕ) : 𝓞 K)}
  let P : Ideal ℤ := Ideal.span {(ℓ : ℤ)}
  haveI : P.IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hℓ.ne_zero)).mpr (Nat.prime_iff_prime_int.mp hℓ)
  have hP0 : P ≠ ⊥ := by simp [P, hℓ.ne_zero]
  let T := Algebra.algebraMapSubmonoid (𝓞 K) P.primeCompl
  have hT : T ≤ nonZeroDivisors (𝓞 K) :=
    map_le_nonZeroDivisors_of_injective _ (FaithfulSMul.algebraMap_injective ℤ (𝓞 K))
      P.primeCompl_le_nonZeroDivisors
  haveI : IsDomain (Localization T) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hT
  haveI : IsDedekindDomain (Localization T) := IsLocalization.isDedekindDomain (𝓞 K) hT _
  haveI : IsPrincipalIdealRing (Localization T) :=
    IsDedekindDomain.isPrincipalIdealRing_localization_over_prime (𝓞 K) P hP0
  have hunit : ∀ t : T, IsUnit (Ideal.Quotient.mk I (t : 𝓞 K)) := by
    rintro ⟨_, z, hz, rfl⟩
    have hz' : ¬ (ℓ : ℤ) ∣ z := fun h => hz (Ideal.mem_span_singleton.mpr h)
    have hc : IsCoprime z ((ℓ : ℤ) ^ j) :=
      (((Nat.prime_iff_prime_int.mp hℓ).irreducible.coprime_iff_not_dvd).mpr hz').symm.pow_right
    obtain ⟨u, v, huv⟩ := hc
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk I (u : 𝓞 K)) ?_
    have hmem : (((ℓ ^ j : ℕ) : 𝓞 K)) ∈ I := Ideal.mem_span_singleton_self _
    have : (algebraMap ℤ (𝓞 K) z) * (u : 𝓞 K) = 1 - (v : 𝓞 K) * ((ℓ ^ j : ℕ) : 𝓞 K) := by
      have := congrArg (Int.cast : ℤ → 𝓞 K) huv
      push_cast at this ⊢
      linear_combination this
    rw [← map_mul, this, map_sub, map_one, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr hmem, mul_zero,
      sub_zero]
  letI : Algebra (Localization T) (𝓞 K ⧸ I) := (IsLocalization.lift hunit).toAlgebra
  haveI : IsScalarTower (𝓞 K) (Localization T) (𝓞 K ⧸ I) :=
    IsScalarTower.of_algebraMap_eq fun c => by
      rw [RingHom.algebraMap_toAlgebra, IsLocalization.lift_eq, Ideal.Quotient.algebraMap_eq]
  haveI : Module.Flat (Localization T) (Localization T ⊗[𝓞 K] L) := Module.Flat.baseChange _ _ _
  haveI : Module.IsTorsionFree (Localization T) (Localization T ⊗[𝓞 K] L) := Module.Flat.isTorsionFree
  haveI : Module.Free (Localization T) (Localization T ⊗[𝓞 K] L) := Module.free_of_finite_type_torsion_free'
  exact Module.Free.of_equiv
    (TensorProduct.AlgebraTensorModule.cancelBaseChange (𝓞 K) (Localization T) (𝓞 K ⧸ I) (𝓞 K ⧸ I) L)

end GlobalTheory.QuotientCardinalityFinrank

namespace GlobalTheory.QuotientCardinalityFinrank

theorem card_eq_pow_finrank (A M : Type) [CommRing A] [Nontrivial A] [AddCommGroup M] [Module A M]
    [Module.Free A M] [Module.Finite A M] : Nat.card M = Nat.card A ^ Module.finrank A M := by
  rw [Nat.card_congr (Module.finBasis A M).equivFun.toEquiv, Nat.card_fun]
  simp

theorem card_quot_int (L : Type) [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L] (n : ℕ)
    (hn : 2 ≤ n) :
    Nat.card (L ⧸ (Ideal.span {((n : ℕ) : ℤ)} • ⊤ : Submodule ℤ L)) = n ^ Module.finrank ℤ L := by
  rw [← Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul L (Ideal.span {((n : ℕ) : ℤ)})).toEquiv]
  haveI : NeZero n := ⟨by omega⟩
  haveI : Fact (1 < n) := ⟨by omega⟩
  have hA : Nat.card (ℤ ⧸ Ideal.span {((n : ℕ) : ℤ)}) = n := by
    rw [Nat.card_congr (Int.quotientSpanNatEquivZMod n).toEquiv, Nat.card_zmod]
  haveI : Nontrivial (ℤ ⧸ Ideal.span {((n : ℕ) : ℤ)}) := (Int.quotientSpanNatEquivZMod n).nontrivial
  rw [card_eq_pow_finrank (ℤ ⧸ Ideal.span {((n : ℕ) : ℤ)}), Module.finrank_baseChange, hA]

theorem card_ringOfIntegers_quot (K : Type) [Field K] [NumberField K] (n : ℕ) :
    Nat.card (𝓞 K ⧸ Ideal.span {((n : ℕ) : 𝓞 K)}) = n ^ Module.finrank ℚ K := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, Ideal.absNorm_span_singleton]
  have : ((n : ℕ) : 𝓞 K) = algebraMap ℤ (𝓞 K) ((n : ℕ) : ℤ) := by simp
  rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank]
  simp [Int.natAbs_pow]

theorem restrictScalars_span_smul_top (K : Type) [Field K] [NumberField K] (L : Type) [AddCommGroup L]
    [Module (𝓞 K) L] (n : ℕ) :
    (Ideal.span {((n : ℕ) : 𝓞 K)} • ⊤ : Submodule (𝓞 K) L).restrictScalars ℤ =
      (Ideal.span {((n : ℕ) : ℤ)} • ⊤ : Submodule ℤ L) := by
  rw [Submodule.ideal_span_singleton_smul, Submodule.ideal_span_singleton_smul]
  ext x
  simp only [Submodule.restrictScalars_mem, Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top,
    true_and, Nat.cast_smul_eq_nsmul]

theorem quot_equiv_pi_pos (K : Type) [Field K] [NumberField K] (L : Type) [AddCommGroup L]
    [Module (𝓞 K) L] [Module.Free ℤ L] [Module.Finite ℤ L] [Module.IsTorsionFree (𝓞 K) L] (r : ℕ)
    (hr : Module.finrank ℤ L = r * Module.finrank ℚ K) (ℓ : ℕ) (hℓ : ℓ.Prime) (j : ℕ) (hj : 0 < j) :
    Nonempty ((Fin r → 𝓞 K ⧸ Ideal.span {((ℓ ^ j : ℕ) : 𝓞 K)}) ≃ₗ[𝓞 K ⧸ Ideal.span {((ℓ ^ j : ℕ) : 𝓞 K)}]
      L ⧸ (Ideal.span {((ℓ ^ j : ℕ) : 𝓞 K)} • ⊤ : Submodule (𝓞 K) L)) := by
  set I := Ideal.span {((ℓ ^ j : ℕ) : 𝓞 K)}
  haveI : Module.Finite (𝓞 K) L := Module.Finite.of_restrictScalars_finite ℤ (𝓞 K) L
  have hn : 2 ≤ ℓ ^ j := by
    calc 2 ≤ ℓ := hℓ.two_le
      _ ≤ ℓ ^ j := Nat.le_self_pow hj.ne' ℓ
  have hd : 0 < Module.finrank ℚ K := Module.finrank_pos
  have hcardA := card_ringOfIntegers_quot K (ℓ ^ j)
  haveI : Finite (𝓞 K ⧸ I) := Nat.finite_of_card_ne_zero (by rw [hcardA]; positivity)
  haveI : Nontrivial (𝓞 K ⧸ I) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    rw [hcardA]
    exact Nat.one_lt_pow hd.ne' (by omega)
  haveI := free_baseChange_quot K L ℓ hℓ j
  let e1 : ((𝓞 K ⧸ I) ⊗[𝓞 K] L) ≃ₗ[𝓞 K ⧸ I] L ⧸ (I • ⊤ : Submodule (𝓞 K) L) :=
    (TensorProduct.quotTensorEquivQuotSMul L I).extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  haveI : Module.Free (𝓞 K ⧸ I) (L ⧸ (I • ⊤ : Submodule (𝓞 K) L)) := Module.Free.of_equiv e1
  haveI : Module.Finite (𝓞 K ⧸ I) (L ⧸ (I • ⊤ : Submodule (𝓞 K) L)) := Module.Finite.equiv e1
  have hM := card_eq_pow_finrank (𝓞 K ⧸ I) (L ⧸ (I • ⊤ : Submodule (𝓞 K) L))
  have hM2 : Nat.card (L ⧸ (I • ⊤ : Submodule (𝓞 K) L)) = (ℓ ^ j) ^ (r * Module.finrank ℚ K) := by
    rw [← hr, ← card_quot_int L (ℓ ^ j) hn, ← restrictScalars_span_smul_top K L (ℓ ^ j)]
    exact Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv ℤ _).toEquiv.symm
  have hM' : (ℓ ^ j) ^ (r * Module.finrank ℚ K) =
      (ℓ ^ j) ^ (Module.finrank ℚ K * Module.finrank (𝓞 K ⧸ I) (L ⧸ (I • ⊤ : Submodule (𝓞 K) L))) := by
    rw [← hM2, hM, hcardA, pow_mul]
  have hk : Module.finrank (𝓞 K ⧸ I) (L ⧸ (I • ⊤ : Submodule (𝓞 K) L)) = r := by
    have := Nat.pow_right_injective hn hM'
    have : Module.finrank ℚ K * Module.finrank (𝓞 K ⧸ I) (L ⧸ (I • ⊤ : Submodule (𝓞 K) L)) =
      Module.finrank ℚ K * r := by rw [← this]; ring
    exact (Nat.eq_of_mul_eq_mul_left hd this)
  exact ⟨(Module.finBasisOfFinrankEq (𝓞 K ⧸ I) _ hk).equivFun.symm⟩

theorem quot_equiv_pi (K : Type) [Field K] [NumberField K] (L : Type) [AddCommGroup L]
    [Module (𝓞 K) L] [Module.Free ℤ L] [Module.Finite ℤ L] [Module.IsTorsionFree (𝓞 K) L] (r : ℕ)
    (hr : Module.finrank ℤ L = r * Module.finrank ℚ K) (ℓ : ℕ) (hℓ : ℓ.Prime) (j : ℕ) :
    Nonempty ((Fin r → 𝓞 K ⧸ Ideal.span {((ℓ ^ j : ℕ) : 𝓞 K)}) ≃ₗ[𝓞 K ⧸ Ideal.span {((ℓ ^ j : ℕ) : 𝓞 K)}]
      L ⧸ (Ideal.span {((ℓ ^ j : ℕ) : 𝓞 K)} • ⊤ : Submodule (𝓞 K) L)) := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have hI : Ideal.span {((ℓ ^ 0 : ℕ) : 𝓞 K)} = ⊤ := by simp
    haveI : Subsingleton (𝓞 K ⧸ Ideal.span {((ℓ ^ 0 : ℕ) : 𝓞 K)}) := Ideal.Quotient.subsingleton_iff.mpr hI
    haveI : Subsingleton (L ⧸ (Ideal.span {((ℓ ^ 0 : ℕ) : 𝓞 K)} • ⊤ : Submodule (𝓞 K) L)) := by
      rw [hI, Submodule.top_smul]
      exact Submodule.Quotient.subsingleton_iff.mpr rfl
    exact ⟨LinearEquiv.ofSubsingleton _ _⟩
  · exact quot_equiv_pi_pos K L r hr ℓ hℓ j hj

theorem isTorsionFree_of_free_int (K : Type) [Field K] [NumberField K] (L : Type) [AddCommGroup L]
    [Module (𝓞 K) L] [Module.Free ℤ L] : Module.IsTorsionFree (𝓞 K) L := by
  refine Module.IsTorsionFree.of_smul_eq_zero fun c y h => ?_
  by_cases hc : c = 0
  · exact Or.inl hc
  right
  have hmem := Ideal.absNorm_mem (Ideal.span {c})
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.mp hmem
  have hne : Ideal.absNorm (Ideal.span {c}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hc
  have : (Ideal.absNorm (Ideal.span {c})) • y = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (𝓞 K), ← hc', mul_smul, h, smul_zero]
  rw [← Nat.cast_smul_eq_nsmul ℤ] at this
  exact (smul_eq_zero.mp this).resolve_left (by exact_mod_cast hne)

end GlobalTheory.QuotientCardinalityFinrank

namespace GlobalTheory.QuotientCardinalityFinrank

theorem torsion_points_free : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (ℓ : ℕ), ℓ.Prime → ℓ ≠ p → ∀ j : ℕ, ∃ f : (Fin (D.m * D.n) → 𝓞 D.F ⧸ Ideal.span {((ℓ ^ j : ℕ) : 𝓞 D.F)}) → (Over.mk x ⟶ o.A), (∀ a a', f (a + a') = f a * f a') ∧ (∀ (c : 𝓞 D.F) a, f (Ideal.Quotient.mk (Ideal.span {((ℓ ^ j : ℕ) : 𝓞 D.F)}) c • a) = f a ≫ o.act.act (algebraMap (𝓞 D.F) D.O c)) ∧ Function.Injective f ∧ ∀ g : Over.mk x ⟶ o.A, g ^ (ℓ ^ j) = 1 → ∃ a, f a = g := by
  intro p _ D R _ b N S s o k _ _ x ℓ hℓ hℓp j
  obtain ⟨β, hβ⟩ : ∃ β : R →+* k, x ≫ s = spMap β :=
    ⟨(Spec.preimage (x ≫ s)).hom, by simp [spMap]⟩
  obtain ⟨I, -⟩ := o.geom k x β hβ
  letI : Module (𝓞 D.F) D.La := Module.compHom D.La (algebraMap (𝓞 D.F) D.O)
  haveI := D.freeLa
  haveI := D.finLa
  haveI := isTorsionFree_of_free_int D.F D.La
  obtain ⟨e⟩ := quot_equiv_pi D.F D.La (D.m * D.n) D.rankLa ℓ hℓ j
  have hpos : 0 < ℓ ^ j := pow_pos hℓ.pos j
  have hcop : (ℓ ^ j).Coprime p :=
    Nat.Coprime.pow_left j ((Nat.coprime_primes hℓ (Fact.out : p.Prime)).mpr hℓp)
  set Sub := (Ideal.span {((ℓ ^ j : ℕ) : 𝓞 D.F)} • ⊤ : Submodule (𝓞 D.F) D.La) with hSub
  have hmem : ∀ y : D.La, y ∈ Sub ↔ ∃ z, y = (ℓ ^ j) • z := by
    intro y
    rw [hSub, Submodule.ideal_span_singleton_smul]
    simp only [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and,
      Nat.cast_smul_eq_nsmul]
    exact ⟨fun ⟨z, hz⟩ => ⟨z, hz.symm⟩, fun ⟨z, hz⟩ => ⟨z, hz.symm⟩⟩
  let φ : D.La →+ Additive (Over.mk x ⟶ o.A) :=
    { toFun := fun y => Additive.ofMul (I.ev (ℓ ^ j) y)
      map_zero' := by
        show Additive.ofMul (I.ev (ℓ ^ j) 0) = Additive.ofMul 1
        rw [(I.ker (ℓ ^ j) hpos hcop 0).mpr ⟨0, by simp⟩]
      map_add' := fun y y' => by
        show Additive.ofMul (I.ev (ℓ ^ j) (y + y')) = Additive.ofMul (I.ev (ℓ ^ j) y * I.ev (ℓ ^ j) y')
        rw [I.add] }
  have hle : Sub.toAddSubgroup ≤ φ.ker := by
    intro y hy
    obtain ⟨z, rfl⟩ := (hmem y).mp hy
    show Additive.ofMul (I.ev (ℓ ^ j) ((ℓ ^ j) • z)) = 0
    rw [(I.ker (ℓ ^ j) hpos hcop _).mpr ⟨z, rfl⟩]
    rfl
  let ψ : D.La ⧸ Sub →+ Additive (Over.mk x ⟶ o.A) := QuotientAddGroup.lift Sub.toAddSubgroup φ hle
  have hψ : ∀ y : D.La, ψ (Submodule.Quotient.mk y) = Additive.ofMul (I.ev (ℓ ^ j) y) := fun y => rfl
  refine ⟨fun a => Additive.toMul (ψ (e a)), ?_, ?_, ?_, ?_⟩
  · intro a a'
    simp only [map_add (f := _), toMul_add]
  · intro c a
    dsimp only
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective Sub (e a)
    rw [map_smul, ← hy, Module.Quotient.mk_smul_mk, hψ, hψ]
    exact I.lin (ℓ ^ j) (algebraMap (𝓞 D.F) D.O c) y
  · intro a a' h
    dsimp only at h
    apply e.injective
    rw [← sub_eq_zero, ← map_sub]
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective Sub (e (a - a'))
    have h1 : ψ (e (a - a')) = 0 := by
      rw [map_sub, map_sub, sub_eq_zero]
      exact congrArg Additive.ofMul h
    rw [← hy, Submodule.Quotient.mk_eq_zero, hmem]
    rw [← hy, hψ] at h1
    exact (I.ker (ℓ ^ j) hpos hcop y).mp (congrArg Additive.toMul h1)
  · intro g hg
    obtain ⟨y, hy⟩ := (I.onto (ℓ ^ j) hpos hcop g).mp hg
    refine ⟨e.symm (Submodule.Quotient.mk y), ?_⟩
    dsimp only
    rw [LinearEquiv.apply_symm_apply, hψ]
    exact hy

end GlobalTheory.QuotientCardinalityFinrank
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareCommutationIntegralIdentity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

namespace GlobalTheory.ThetaAgreeConv

theorem map_finRel_eq_zero {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {W W₁ X : HSp D}
    {A : GlobalTheory.ChainFr.Fr W} {A₁ : GlobalTheory.ChainFr.Fr W₁} {B : GlobalTheory.ChainFr.Fr X} {α β : (AE D)ˣ →* Circle} {ωA ωB Pi rf rl p p'}
    (hM : GlobalTheory.SquareComm.IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p') {Ψ}
    (hΨ : Ψ ∈ GlobalTheory.SquareComm.finRel ωB (GlobalTheory.SquareComm.algF ψ θ false A₁ B)) : p' Ψ = 0 := by
  have hle : GlobalTheory.SquareComm.finRel ωB (GlobalTheory.SquareComm.algF ψ θ false A₁ B) ≤ LinearMap.ker p' := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, hu, Ψ, hΨ, rfl⟩
    show p' (ωB (u, 1) Ψ - Ψ) = 0
    rw [map_sub, hM.mapB.invf u hu Ψ hΨ, sub_self]
  exact hle hΨ

section Reg

open MeasureTheory GlobalTheory.SquareComm GlobalTheory.RegCompare

variable {D : D7}

theorem intg_right {M X : HSp D} {ω : GlobalTheory.Grid.WRep M X} {ν : Measure (GA D M)} {𝓕 : Set (GA D M)}
    (hν : IsHaarFD M ν 𝓕) {Φ : WO M X → ℂ} (hL : ∀ γ ∈ GQ M, ∀ g h, thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ)
    (hΦ : Intg ω ν 𝓕 Φ) (k : GA D M) :
    Intg ω ν 𝓕 (ω (k, 1) Φ) ∧ thetaInt ω ν 𝓕 (ω (k, 1) Φ) = thetaInt ω ν 𝓕 Φ := by
  haveI := hν.1
  have key := fun h => setIntegral_mul_right' M ν 𝓕 hν.2 (fun g => thetaKO ω g h Φ)
    (fun γ hγ u => hL γ hγ u h) (hΦ h) k
  refine ⟨fun h => ?_, ?_⟩
  · simpa only [thetaKO_right] using (key h).1
  · funext h
    simp only [thetaInt, thetaKO_right]
    exact (key h).2

theorem thetaInt_wop_of_intg {M X : HSp D} {ω : GlobalTheory.Grid.WRep M X} {ν : Measure (GA D M)} {𝓕 : Set (GA D M)}
    (hν : IsHaarFD M ν 𝓕) {Φ : WO M X → ℂ} (hL : ∀ γ ∈ GQ M, ∀ g h, thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ)
    (hΦ : Intg ω ν 𝓕 Φ) (z : GA D M →₀ ℂ) :
    thetaInt ω ν 𝓕 (wop ω z Φ) = GlobalTheory.FunObj.zdeg z • thetaInt ω ν 𝓕 Φ := by
  have hk := fun k => intg_right hν hL hΦ k
  rw [wop_apply, thetaInt_sum _ fun k _ => ((hk k).1).smul _]
  simp only [thetaInt_smul, (hk _).2, GlobalTheory.FunObj.zdeg, Finsupp.sum, Finset.sum_smul]

end Reg

end GlobalTheory.ThetaAgreeConv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoPointInductionKltPairSeparation
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem add_le_sum_Icc_of_lt (h : ℕ → ℚ) (ε : ℚ) (hpos : ∀ e, 0 < h e + ε) {n i j : ℕ}
    (hij : i < j) (hjn : j ≤ n) {d : ℚ} (hd : d ≤ ∑ e ∈ Finset.Icc (j + 1) n, (h e + ε)) :
    d + (h (i + 1) + ε) ≤ ∑ e ∈ Finset.Icc (i + 1) n, (h e + ε) := by
  rw [Finset.Icc_eq_cons_Ioc (by omega : i + 1 ≤ n), Finset.sum_cons]
  have : ∑ e ∈ Finset.Icc (j + 1) n, (h e + ε) ≤ ∑ e ∈ Finset.Ioc (i + 1) n, (h e + ε) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun e he => by simp only [Finset.mem_Icc, Finset.mem_Ioc] at he ⊢; omega)
      fun e _ _ => (hpos e).le
  linarith

theorem sum_Icc_le_sum_Icc_one (h : ℕ → ℚ) (ε : ℚ) (hpos : ∀ e, 0 < h e + ε) (n j : ℕ) :
    ∑ e ∈ Finset.Icc (j + 1) n, (h e + ε) ≤ ∑ e ∈ Finset.Icc 1 n, (h e + ε) :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc (by omega) le_rfl)
    fun e _ _ => (hpos e).le

end GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem two_point_induction : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair →
    GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    letI := algebraΓOfHom p; ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (ε : ℚ)
    (h : ℕ → ℚ) (x₁ x₂ : X), IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m →
    IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → IsClosed ({x₁} : Set X) →
    IsClosed ({x₂} : Set X) → x₁ ≠ x₂ → (∀ e, 0 < h e) →
    (∀ (z : X) (e : ℕ), z ⤳ x₁ ∨ z ⤳ x₂ → 1 ≤ e →
      topologicalKrullDim (closure ({z} : Set X)) = e →
      2 * (e : ℚ) ^ e < h e ^ e * (interNumRed ℂ (Closeds.closure ({z} : Set X))
        fun _ : Fin e => N : ℤ)) → 0 < ε →
    ∃ (D : X → ℚ) (d : ℚ), d ≤ ∑ e ∈ Finset.Icc 1 n, (h e + ε) ∧ QNum p N d D ∧
      ((LcCut p n (Δ + D) x₁ 0 ∧ ¬ KltAt p n (Δ + D) x₂) ∨
        (LcCut p n (Δ + D) x₂ 0 ∧ ¬ KltAt p n (Δ + D) x₁)) := by
  intro hP hNV hNef X _ _ _ p n hproj hdim
  letI := algebraΓOfHom p
  intro Δ m G N ε h x₁ x₂ hΔ hklt hm hG hNa hc₁ hc₂ hne hh hint hε
  have hpos : ∀ e, 0 < h e + ε := fun e => add_pos (hh e) hε

  have hξ : ∀ x : X, genericPoint X ⤳ x := fun x => (genericPoint_spec X).specializes trivial
  have hdimξ : topologicalKrullDim (closure ({genericPoint X} : Set X)) = n := by
    rw [genericPoint_closure,
      IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph, hdim]

  have hn : 1 ≤ n := by
    obtain ⟨e, -, he, he1⟩ := _root_.GlobalTheory.closure_point_topologicalKrullDim X n (genericPoint X) hdim
    have hen : e = n := by
      rw [hdimξ] at he; exact_mod_cast he.symm
    subst hen
    by_cases h₁ : x₁ = genericPoint X
    · exact he1 x₂ (hξ x₂) fun h₂ => hne (h₁.trans h₂.symm)
    · exact he1 x₁ (hξ x₁) h₁
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩

  have key : ∀ j, j ≤ k → ∀ (D : X → ℚ) (d : ℚ), 0 ≤ d →
      d ≤ ∑ e ∈ Finset.Icc (j + 1) (k + 1), (h e + ε) → QNum p N d D →
      ((LcCut p (k + 1) (Δ + D) x₁ j ∧ ¬ KltAt p (k + 1) (Δ + D) x₂) ∨
        (LcCut p (k + 1) (Δ + D) x₂ j ∧ ¬ KltAt p (k + 1) (Δ + D) x₁)) →
      ∃ (D : X → ℚ) (d : ℚ), d ≤ ∑ e ∈ Finset.Icc 1 (k + 1), (h e + ε) ∧ QNum p N d D ∧
        ((LcCut p (k + 1) (Δ + D) x₁ 0 ∧ ¬ KltAt p (k + 1) (Δ + D) x₂) ∨
          (LcCut p (k + 1) (Δ + D) x₂ 0 ∧ ¬ KltAt p (k + 1) (Δ + D) x₁)) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
    intro hjk D d hd0 hd hQ hcut
    have hd1 := hd.trans (sum_Icc_le_sum_Icc_one h ε hpos (k + 1) j)
    rcases hcut with ⟨hc, hnk⟩ | ⟨hc, hnk⟩
    · rcases GlobalTheory.T.twoPoint_induction_step_logCanonical hP hNV hNef X p (k + 1) hproj hdim Δ m G N D d ε h x₁ x₂ j hΔ hklt hm
          hG hNa hc₁ hc₂ hne hh hint hε hQ hd0 hc hnk with h0 | ⟨i, D', d', hij, hd'0, hd', hQ', hc'⟩
      · exact ⟨D, d, hd1, hQ, Or.inl ⟨h0, hnk⟩⟩
      · exact ih i hij (by omega) D' d' hd'0
          (hd'.trans (add_le_sum_Icc_of_lt h ε hpos hij (by omega) hd)) hQ' hc'
    · rcases GlobalTheory.T.twoPoint_induction_step_logCanonical hP hNV hNef X p (k + 1) hproj hdim Δ m G N D d ε h x₂ x₁ j hΔ hklt hm
          hG hNa hc₂ hc₁ hne.symm hh (fun z e hz => hint z e hz.symm) hε hQ hd0 hc hnk with
        h0 | ⟨i, D', d', hij, hd'0, hd', hQ', hc'⟩
      · exact ⟨D, d, hd1, hQ, Or.inr ⟨h0, hnk⟩⟩
      · exact ih i hij (by omega) D' d' hd'0
          (hd'.trans (add_le_sum_Icc_of_lt h ε hpos hij (by omega) hd)) hQ' hc'.symm

  have hlc : ∀ x, LcAt p (k + 1) (Δ + 0) x := fun x => by rw [add_zero]; exact (hklt x).lcAt
  have hdimξ' : topologicalKrullDim (closure ({genericPoint X} : Set X)) = ((k + 1 : ℕ) : WithBot ℕ∞) :=
    hdimξ
  obtain ⟨D', d', hd'0, hd', hQ', hc'⟩ := GlobalTheory.T.lc_cut_two_closed_points_one_centre hP hNV hNef X p (k + 1) hproj hdim Δ m G N 0
    0 (h (k + 1)) x₁ x₂ (genericPoint X) k hΔ hklt hm hG hNa (qNum_zero_zero X p hproj N) le_rfl
    hc₁ hc₂ (hlc x₁) (hlc x₂) (hξ x₁) (hξ x₂) (Or.inl rfl) hdimξ' (hh _)
    (hint (genericPoint X) (k + 1) (Or.inl (hξ x₁)) (by omega) hdimξ')
  refine key k le_rfl D' d' hd'0 ?_ hQ' hc'
  rw [Finset.Icc_self, Finset.sum_singleton]
  linarith [hε]

end GlobalTheory.PairStep
end

