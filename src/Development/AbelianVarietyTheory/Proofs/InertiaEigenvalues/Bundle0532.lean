module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0511
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0023
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0433
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0478
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0479
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0482
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0483
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0518
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0503
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0472
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0505
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0502
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0332
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0396
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0514
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0513
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0471
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0507

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteClassesOfSeparableCharPoly
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.ClFin

variable {K : UQ} (B : InvAlg K)

def sigU : B.Aˣ →* B.Aˣ := Units.map (B.σ : B.A →* B.A)

theorem sigU_val (u : B.Aˣ) : ((sigU B u : B.Aˣ) : B.A) = B.σ u := rfl

def fixG : Subgroup B.Aˣ where
  carrier := {x | B.σ (x : B.A) = x}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, map_mul] at ha hb ⊢
    rw [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have h : B.σ ((a⁻¹ : B.Aˣ) : B.A) * (a : B.A) = 1 := by
      calc B.σ ((a⁻¹ : B.Aˣ) : B.A) * (a : B.A) = B.σ ((a⁻¹ : B.Aˣ) : B.A) * B.σ (a : B.A) := by
            rw [ha]
        _ = 1 := by rw [← map_mul, Units.inv_mul, map_one]
    calc B.σ ((a⁻¹ : B.Aˣ) : B.A)
        = B.σ ((a⁻¹ : B.Aˣ) : B.A) * ((a : B.A) * ((a⁻¹ : B.Aˣ) : B.A)) := by
          rw [Units.mul_inv, mul_one]
      _ = ((a⁻¹ : B.Aˣ) : B.A) := by rw [← mul_assoc, h, one_mul]

def normHom : B.Aˣ →* fixG B where
  toFun u := ⟨u * sigU B u, by
    show B.σ ((u : B.A) * B.σ u) = (u : B.A) * B.σ u
    rw [map_mul, B.σ_σ, mul_comm]⟩
  map_one' := by
    apply Subtype.ext; apply Units.ext
    simp [sigU_val]
  map_mul' := by
    intro a b
    apply Subtype.ext; apply Units.ext
    simp only [Units.val_mul, sigU_val, map_mul, Subgroup.coe_mul]
    ring

theorem finite_quot (hsq : Finite (B.Aˣ ⧸ (powMonoidHom 2 : B.Aˣ →* B.Aˣ).range))
    (hmu : Set.Finite {x : B.A | x ^ 2 = 1}) : Finite (fixG B ⧸ (normHom B).range) := by
  set Sq := (powMonoidHom 2 : B.Aˣ →* B.Aˣ).range
  set φ : fixG B →* B.Aˣ ⧸ Sq := (QuotientGroup.mk' Sq).comp (fixG B).subtype
  haveI : Finite (fixG B ⧸ φ.ker) := Finite.of_injective _ (QuotientGroup.kerLift_injective φ)
  set M := {x : fixG B | ((x : B.Aˣ) : B.A) ^ 2 = 1}
  haveI : Finite M := by
    have : Finite {x : B.A | x ^ 2 = 1} := hmu.to_subtype
    refine Finite.of_injective (fun x : M => (⟨((x.1 : B.Aˣ) : B.A), x.2⟩ : {x : B.A | x ^ 2 = 1})) ?_
    intro a b h
    apply Subtype.ext; apply Subtype.ext; apply Units.ext
    exact congrArg Subtype.val h
  let g : (fixG B ⧸ φ.ker) × M → fixG B ⧸ (normHom B).range :=
    fun p => QuotientGroup.mk (Quotient.out p.1 * p.2.1)
  refine Finite.of_surjective g ?_
  intro z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  set x₀ : fixG B := Quotient.out (QuotientGroup.mk x : fixG B ⧸ φ.ker)
  have hx₀ : x₀⁻¹ * x ∈ φ.ker := by
    have : (QuotientGroup.mk x₀ : fixG B ⧸ φ.ker) = QuotientGroup.mk x := Quotient.out_eq' _
    exact QuotientGroup.eq.mp this
  rw [MonoidHom.mem_ker] at hx₀
  simp only [φ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx₀
  obtain ⟨y, hy⟩ := hx₀
  rw [powMonoidHom_apply] at hy

  have hfix : B.σ ((y : B.A) ^ 2) = (y : B.A) ^ 2 := by
    have := (x₀⁻¹ * x).2
    rw [← Units.val_pow_eq_pow_val, hy]
    exact this
  set ε : B.Aˣ := y * (sigU B y)⁻¹
  have hε2 : (ε : B.A) ^ 2 = 1 := by
    have h1 : ((sigU B y : B.Aˣ) : B.A) ^ 2 = (y : B.A) ^ 2 := by rw [sigU_val, ← map_pow, hfix]
    have h1' : (sigU B y) ^ 2 = y ^ 2 :=
      Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, h1])
    have h2 : ((sigU B y)⁻¹ : B.Aˣ) ^ 2 = (y ^ 2)⁻¹ := by rw [inv_pow, h1']
    rw [← Units.val_pow_eq_pow_val]
    simp only [ε, mul_pow, h2, mul_inv_cancel, Units.val_one]
  have hεfix : B.σ (ε : B.A) = ε := by

    have hσ : B.σ (ε : B.A) * (ε : B.A) = 1 := by
      have hyinv : B.σ (((sigU B y)⁻¹ : B.Aˣ) : B.A) = ((y⁻¹ : B.Aˣ) : B.A) := by
        have : B.σ (((sigU B y)⁻¹ : B.Aˣ) : B.A) * (y : B.A) = 1 := by
          calc B.σ (((sigU B y)⁻¹ : B.Aˣ) : B.A) * (y : B.A)
              = B.σ (((sigU B y)⁻¹ : B.Aˣ) : B.A) * B.σ (B.σ (y : B.A)) := by rw [B.σ_σ]
            _ = 1 := by rw [← map_mul, ← sigU_val, Units.inv_mul, map_one]
        calc B.σ (((sigU B y)⁻¹ : B.Aˣ) : B.A)
            = B.σ (((sigU B y)⁻¹ : B.Aˣ) : B.A) * ((y : B.A) * ((y⁻¹ : B.Aˣ) : B.A)) := by
              rw [Units.mul_inv, mul_one]
          _ = ((y⁻¹ : B.Aˣ) : B.A) := by rw [← mul_assoc, this, one_mul]
      simp only [ε, Units.val_mul, map_mul, hyinv]
      calc B.σ (y : B.A) * ((y⁻¹ : B.Aˣ) : B.A) * ((y : B.A) * (((sigU B y)⁻¹ : B.Aˣ) : B.A))
          = (((sigU B y) : B.Aˣ) : B.A) * (((sigU B y)⁻¹ : B.Aˣ) : B.A) *
              ((y : B.A) * ((y⁻¹ : B.Aˣ) : B.A)) := by rw [sigU_val]; ring
        _ = 1 := by rw [Units.mul_inv, Units.mul_inv, one_mul]
    calc B.σ (ε : B.A) = B.σ (ε : B.A) * ((ε : B.A) * (ε : B.A)) := by rw [← sq, hε2, mul_one]
      _ = ε := by rw [← mul_assoc, hσ, one_mul]
  let εG : fixG B := ⟨ε, hεfix⟩
  refine ⟨(QuotientGroup.mk x, ⟨εG, hε2⟩), ?_⟩
  show QuotientGroup.mk (x₀ * εG) = QuotientGroup.mk x
  rw [QuotientGroup.eq]
  refine ⟨y, ?_⟩
  apply Subtype.ext; apply Units.ext

  have hxy : ((x : fixG B) : B.Aˣ) = (x₀ : B.Aˣ) * y ^ 2 := by
    rw [hy]; simp
  show ((y : B.A) * B.σ (y : B.A)) = (((x₀ * εG)⁻¹ * x : fixG B) : B.Aˣ).val
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hxy, εG, ε]
  simp only [mul_inv_rev, inv_inv, Units.val_mul, Units.val_pow_eq_pow_val, sigU_val]
  have : ((x₀ : B.Aˣ)⁻¹ : B.Aˣ).val * (x₀ : B.Aˣ).val = 1 := Units.inv_mul _
  have hy1 : (y : B.A) * ((y⁻¹ : B.Aˣ) : B.A) = 1 := Units.mul_inv y
  rw [sq]
  linear_combination (-(B.σ (y : B.A) * (y : B.A))) * hy1 +
    (-(B.σ (y : B.A) * (y : B.A) * (y : B.A) * ((y⁻¹ : B.Aˣ) : B.A))) * this

def toCl : fixG B ⧸ (normHom B).range → B.Cl :=
  Quotient.lift (fun x : fixG B => (Quot.mk _ ⟨(x : B.Aˣ), x.2⟩ : B.Cl)) (by
    intro a b hab
    have h := QuotientGroup.leftRel_apply.mp hab
    obtain ⟨u, hu⟩ := h
    apply Quot.sound
    refine ⟨u, ?_⟩
    have hb : (b : B.Aˣ) = (a : B.Aˣ) * ((normHom B u : fixG B) : B.Aˣ) := by
      rw [hu]; simp
    show ((b : B.Aˣ) : B.A) = ((a : B.Aˣ) : B.A) * ((u : B.A) * B.σ (u : B.A))
    rw [hb, Units.val_mul]
    rfl)

theorem toCl_surjective : Function.Surjective (toCl B) := by
  intro k
  induction k using Quot.ind with
  | mk x => exact ⟨QuotientGroup.mk ⟨x.1, x.2⟩, rfl⟩

theorem finite_Cl (K : UQ) (B : InvAlg K) : Finite B.Cl := by
  have hsq := _root_.GlobalTheory.units_modSq_finite_of_fields K.E (_root_.GlobalTheory.UnitLemma.UQ.finite_units_mod_sq K) B.A
  have hmu := _root_.GlobalTheory.finite_sq_eq_one_of_finite_algebra K.E B.A
  haveI := finite_quot B hsq hmu
  exact Finite.of_surjective _ (toCl_surjective B)

theorem finite_Cl_of_separable : ∀ (K : UQ) (B : InvAlg K), B.P.Separable → Finite B.Cl :=
  fun K B _ => finite_Cl K B

end GlobalTheory.UnitLemma.ClFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLengthCokerOfSurjectiveModUniformizer
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

theorem GlobalTheory.BK.Hom.finiteLength_coker_of_generic : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (κ : Type) [Fintype κ] [DecidableEq κ] (P : PhiMod O K l e a ι) (Q : PhiMod O K l e a κ) (F : GlobalTheory.BK.Hom P Q), ((∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ (∃ n, ‖coeff n g‖ = 1) ∧ F.mat τ * Y = g • (1 : Matrix κ κ K⟦X⟧)) → IsFiniteLength (A O K) F.coker) ∧ ((∀ τ, ∃ (Y : Matrix ι κ K⟦X⟧) (g : K⟦X⟧), (∀ i j, Y i j ∈ A O K) ∧ (∃ n, ‖coeff n g‖ = 1) ∧ Y * F.mat τ = g • (1 : Matrix ι ι K⟦X⟧)) → ∀ v ∈ Q.M, ∀ f ∈ A O K, f ≠ 0 → f • v ∈ F.imM → v ∈ F.imM) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ κ _ _ P Q F
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have h1 : (l : K) = algebraMap ℚ_[l] K (l : ℚ_[l]) := (map_natCast _ _).symm
  have hlK : ‖(l : K)‖ < 1 := by
    rw [h1, norm_algebraMap', Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hl2)
  have hl0 : (l : K) ≠ 0 := by
    rw [h1]
    exact (map_ne_zero _).2 (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
  have he : 0 < e := Nat.pos_of_ne_zero (NeZero.ne e)
  have hone : ∃ c : ℝ, ∀ n, ‖coeff n (1 : K⟦X⟧)‖ ≤ c :=
    ⟨1, fun n => by rw [coeff_one]; split_ifs <;> simp⟩
  refine ⟨fun hyp => _root_.GlobalTheory.CokerFinLen.main O K l e a ι κ P Q F hyp ?_, fun hyp => _root_.GlobalTheory.BK.Hom.coker_torsionFree O K l e a ι κ P Q F hyp ?_⟩
  · rcases isEmpty_or_nonempty κ with hκ | ⟨⟨i0⟩⟩
    · intro τ
      exact ⟨hone, 0, ⟨0, fun _ j => isEmptyElim j⟩, Subsingleton.elim _ _⟩
    · obtain ⟨M₁, h₁⟩ := _root_.GlobalTheory.BK.Hom.exists_E_pow_mul_frob_mem_rdivSet O K l e a ι κ P Q F
      obtain ⟨M₂, h₂⟩ := _root_.GlobalTheory.BK.RdivSlice.exists_frobSlice_mem_rdivSet O K l e a ι κ P Q F
      refine _root_.GlobalTheory.BK.GcdCore.one_mem K l e a M₁ M₂ he hl0 hlK F.rdivSet (fun τ x hx y hy => Hom.rdivSet_add F τ hx hy)
        (fun τ x hx b hb => Hom.rdivSet_mul F τ hx b hb) (fun τ x hx => hx.1) ?_ h₁ h₂
      intro τ
      obtain ⟨Y, g, hY, hg, hFY⟩ := hyp τ
      have hgA : g ∈ A O K := by
        have : (F.mat τ * Y) i0 i0 = g := by rw [hFY]; simp
        rw [← this, Matrix.mul_apply]
        exact Subalgebra.sum_mem _ fun j _ => mul_mem (F.mem τ i0 j) (hY j i0)
      exact ⟨g, ⟨⟨1, mem_A.1 hgA⟩, Y, ⟨1, fun i j => mem_A.1 (hY i j)⟩, hFY⟩, mem_A.1 hgA, hg⟩
  · rcases isEmpty_or_nonempty ι with hι | ⟨⟨i0⟩⟩
    · intro τ
      exact ⟨hone, 0, ⟨0, fun i _ => isEmptyElim i⟩, Subsingleton.elim _ _⟩
    · obtain ⟨M₁, h₁⟩ := _root_.GlobalTheory.BK.Hom.frob_mem_ldivSet_target O K l e a ι κ P Q F
      obtain ⟨M₂, h₂⟩ := _root_.GlobalTheory.BK.SliceLdiv.frobSlice_mem_ldivSet O K l e a ι κ P Q F
      refine _root_.GlobalTheory.BK.GcdCore.one_mem K l e a M₁ M₂ he hl0 hlK F.ldivSet (fun τ x hx y hy => Hom.ldivSet_add F τ hx hy)
        (fun τ x hx b hb => Hom.ldivSet_mul F τ hx b hb) (fun τ x hx => hx.1) ?_ h₁ h₂
      intro τ
      obtain ⟨Y, g, hY, hg, hFY⟩ := hyp τ
      have hgA : g ∈ A O K := by
        have : (Y * F.mat τ) i0 i0 = g := by rw [hFY]; simp
        rw [← this, Matrix.mul_apply]
        exact Subalgebra.sum_mem _ fun j _ => mul_mem (hY i0 j) (F.mem τ j i0)
      exact ⟨g, ⟨⟨1, mem_A.1 hgA⟩, Y, ⟨1, fun i j => mem_A.1 (hY i j)⟩, hFY⟩, mem_A.1 hgA, hg⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteLengthInvariantsNegTwistKmodO
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations

noncomputable section

namespace GlobalTheory.FinInvKO

theorem isFiniteLength_of_killed {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {M : Type} [AddCommGroup M] [Module O M] [Module.Finite O M] {c : O}
    (hc : c ≠ 0) (h : ∀ x : M, c • x = 0) : IsFiniteLength O M := by
  have hfl := isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero hc)
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hfl ⊢
  refine ⟨inferInstance, ?_⟩
  have ht : Module.IsTorsionBySet O M (Ideal.span {c}) :=
    (Module.isTorsionBySet_span_singleton_iff c).mpr (fun x => h x)
  letI := ht.module
  haveI : IsScalarTower O (O ⧸ Ideal.span {c}) M := ht.isScalarTower
  haveI : IsArtinianRing (O ⧸ Ideal.span {c}) := isArtinian_of_tower O hfl.2
  haveI : Module.Finite (O ⧸ Ideal.span {c}) M := Module.Finite.of_restrictScalars_finite O _ _
  exact isArtinian_of_surjective_algebraMap (R := O ⧸ Ideal.span {c}) Ideal.Quotient.mk_surjective

theorem length_lt_top_of_killed {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S : Submodule O (KmodO O)) {c : O} (hc : c ≠ 0) (h : ∀ x ∈ S, c • x = 0) :
    Module.length O S < ⊤ := by
  have hc' : algebraMap O (FractionRing O) c ≠ 0 := by
    simpa using (IsFractionRing.injective O (FractionRing O)).ne hc
  let x₀ : KmodO O := Submodule.Quotient.mk ((algebraMap O (FractionRing O) c)⁻¹)
  let ψ : O →ₗ[O] KmodO O := LinearMap.toSpanSingleton O _ x₀
  have hS : S ≤ LinearMap.range ψ := by
    intro x hx
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 := h _ hx
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨a, ha⟩ := h1
    have ha' : algebraMap O (FractionRing O) a = algebraMap O (FractionRing O) c * y := by
      rw [← Algebra.smul_def]; exact ha
    refine ⟨a, ?_⟩
    simp only [ψ, LinearMap.toSpanSingleton_apply, x₀, ← Submodule.Quotient.mk_smul]
    congr 1
    rw [Algebra.smul_def, ha', mul_comm (algebraMap O (FractionRing O) c) y, mul_assoc,
      mul_inv_cancel₀ hc', mul_one]
  have hk : ∀ z : LinearMap.range ψ, c • z = 0 := by
    rintro ⟨_, a, rfl⟩
    ext1
    simp only [SetLike.val_smul, ψ, LinearMap.toSpanSingleton_apply, x₀, ← Submodule.Quotient.mk_smul,
      smul_smul, Submodule.coe_zero]
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨a, ?_⟩
    rw [Algebra.linearMap_apply, Algebra.smul_def, map_mul, mul_comm (algebraMap O (FractionRing O) c), mul_assoc, mul_inv_cancel₀ hc', mul_one]
  have hfl := isFiniteLength_of_killed hc hk
  exact lt_of_le_of_lt (Module.length_le_of_injective (Submodule.inclusion hS) (Submodule.inclusion_injective hS))
    (lt_top_iff_ne_top.2 (Module.length_ne_top_iff.2 hfl))

theorem finiteLength_invariants_negTwist_KmodO : ∀ (D : D7) (i : D.nd.Loc), ∀ w ∈ placesOver D.host.E (D.nd.l i), ∀ e : ℕ, 0 < e →
    Module.length (D.nd.O i) ↥(Representation.invariants
      ((Formalism.MainNotions.N.Glob.KOtw D.nd i (e : ℤ)).comp (decS D.nd w))) < ⊤ := by
  intro D i w hw e he
  obtain ⟨g, hgI, hg⟩ := GlobalTheory.EpsInertia.epsAll D i w hw 1
  have hgD : g ∈ Dec (F := D.host.E) (D.nd.plOm.1 w) := hgI.1
  have hp : (D.nd.l i).Prime := (D.nd.lPrime i).out
  haveI : CharZero (FractionRing (D.nd.O i)) :=
    (D.nd.embK i).charZero_iff (D.nd.embK i).injective |>.1 inferInstance
  haveI : CharZero (D.nd.O i) := (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).charZero
  have hle : 1 ≤ (1 + D.nd.l i ^ D.nd.s0 i) ^ e := Nat.one_le_pow _ _ (by omega)
  have hlt : 1 < (1 + D.nd.l i ^ D.nd.s0 i) ^ e :=
    Nat.one_lt_pow he.ne' (by have := pow_pos hp.pos (D.nd.s0 i); omega)
  have hc : (((1 + D.nd.l i ^ D.nd.s0 i) ^ e - 1 : ℕ) : D.nd.O i) ≠ 0 :=
    Nat.cast_ne_zero.2 (by omega)
  refine length_lt_top_of_killed _ hc fun v hv => ?_
  have h1 := hv ⟨g, hgD⟩
  change ((((Glob.epsO D.nd i) ^ (-(e : ℤ))) g : (D.nd.O i)ˣ) : D.nd.O i) • v = v at h1
  have hu : ((Glob.epsO D.nd i g : (D.nd.O i)ˣ) : D.nd.O i) = 1 + (D.nd.l i : D.nd.O i) ^ D.nd.s0 i := by
    simp [Glob.epsO, hg]
  have h2 : (((Glob.epsO D.nd i g) ^ e : (D.nd.O i)ˣ) : D.nd.O i) • v = v := by
    conv_lhs => rw [← h1]
    rw [smul_smul, ← Units.val_mul, MonoidHom.zpow_apply, ← zpow_natCast, ← zpow_add, add_neg_cancel,
      zpow_zero, Units.val_one, one_smul]
  rw [Nat.cast_sub hle, Nat.cast_one, sub_smul, one_smul, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
    Nat.cast_pow, ← hu, ← Units.val_pow_eq_pow_val, h2, sub_self]

end GlobalTheory.FinInvKO
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsumCountNeg
section
noncomputable section

namespace GlobalTheory.TopSteps.FinSummandJumps

open Module

theorem finsum_count_neg (U : Multiset ℤ) (m : ℤ → ℤ) (h : ∀ a, m a = (U.count a : ℤ)) :
    ∑ᶠ (a : ℤ) (_ : a < 0), m a = (Multiset.card (U.filter (· < 0)) : ℤ) := by
  classical
  have h1 : ∀ a : ℤ, ∑ᶠ (_ : a < 0), m a = (((U.filter (· < 0)).count a : ℕ) : ℤ) := fun a => by
    rw [finsum_eq_if, h, Multiset.count_filter]
    split_ifs <;> simp
  rw [finsum_congr h1, finsum_eq_sum_of_support_subset (s := (U.filter (· < 0)).toFinset),
    ← Nat.cast_sum, Multiset.toFinset_sum_count_eq]
  intro a ha
  have ha' : (U.filter (· < 0)).count a ≠ 0 := fun h0 => ha (by simp only [h0, Nat.cast_zero])
  exact Finset.mem_coe.2 (Multiset.mem_toFinset.2 (Multiset.count_ne_zero.1 ha'))

section General

open GlobalTheory.AdmLoc Formalism.WeaklyAdmissibleFiltrations

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {ρ : Representation LL G V}

theorem finsum_multV_neg {n : ℕ} [NeZero n] (emb : ZMod n → (K₀ →ₐ[Qp] LL)) (hemb : Function.Bijective emb)
    (hK : Function.Bijective (algebraMap K₀ K)) (U : ZMod n → Multiset ℤ)
    (hU : ∀ i, HasJumps PD ρ (emb i) (U i)) :
    ∑ᶠ (τ : K →ₐ[Qp] LL), ∑ᶠ (a : ℤ) (_ : a < 0), multV PD ρ τ a =
      ∑ i, (Multiset.card ((U i).filter (· < 0)) : ℤ) := by
  let E : K₀ ≃ₐ[Qp] K := AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hK
  let e : ZMod n ≃ (K →ₐ[Qp] LL) := (Equiv.ofBijective emb hemb).trans (E.arrowCongr AlgEquiv.refl)
  have he : ∀ i x, e i (algebraMap K₀ K x) = emb i x := fun i x => by
    change emb i (E.symm (E x)) = emb i x
    rw [AlgEquiv.symm_apply_apply]
  rw [← finsum_comp_equiv e, finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun i _ => finsum_count_neg (U i) _ (hU i (e i) (he i))

end General


open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions GlobalTheory.TopSteps.FinSummandDim in
theorem fSummand : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P), tableLineDegreeTwo.BlochKatoJumpDimension (P.PD S.K) (LL := ↥S.LL.1) (O := S.O) (IK S.K) → S.CrysCalc → S.Vanish → S.FreeH → S.FSummand := by
  intro l _ P S hB hC hV hH
  obtain ⟨⟨-, -, -, hemb, -⟩, -⟩ := S.hyp
  have : IsTopologicalAddGroup (tw S hC).V := IsModuleTopology.topologicalAddGroup ↥S.LL.1 (tw S hC).V
  have h := hB.1 (tw S hC).V (tw S hC).ρ (tw S hC).cont (tw_crysWith S hC).1
  exact fSummand_of_dim S hC hV hH (h.trans (congrArg _
    (finsum_multV_neg (P.PD S.K) S.emb hemb (bijective_maxUnramifiedSubfield_algebraMap S) _ (tw_crysWith S hC).2)))

end GlobalTheory.TopSteps.FinSummandJumps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlatPowDvdPerPowMod
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

theorem flatPow_dvd_perPow_mod : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ →
    ∀ (M n : ℕ), ∃ (c : ℕ) (y : Ainf l), (l : Ainf l) ^ n ∣ bk.ev X ^ c - τ ^ M * y := by
  intro l _ K bk τ hτ M n
  have hU : IsUnit (inclW l (τ ^ M)) := by
    rw [map_pow]
    exact (GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ).1.pow M
  obtain ⟨m, t, h⟩ := GlobalTheory.BSP.BddDen.main l K bk (τ ^ M) hU n
  refine ⟨m, t, ?_⟩
  have : bk.ev X ^ m - τ ^ M * t = -(t * τ ^ M - bk.ev X ^ m) := by ring
  rw [this]
  exact (dvd_neg).2 h

end GlobalTheory.BKLim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FramedCrystalFrobeniusCoordinates
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem coord_of_frac_rel {A N : Type} [CommRing A] [AddCommGroup N] [Module A N] {d : ℕ}
    (b : Module.Basis (Fin d) A N) (b' : Fin d → N) (hb : ∀ i, b i = b' i) (T c : A) (v w : Fin d → A) (n : N) (r s j k : ℕ)
    (h1 : (T * T) ^ r • (T ^ j • ∑ i, v i • b' i - T ^ k • n) = 0)
    (h2 : T ^ s • (c • n - T ^ j • ∑ i, w i • b' i) = 0) :
    T ^ (r + r + s + j) • (c • v - T ^ k • w) = 0 := by
  obtain rfl : ⇑b = b' := funext hb
  apply b.equivFun.symm.injective
  rw [map_zero, map_smul, map_sub, map_smul, map_smul, Module.Basis.equivFun_symm_apply,
    Module.Basis.equivFun_symm_apply]
  generalize ∑ i, v i • b i = V at *
  generalize ∑ i, w i • b i = W at *
  linear_combination (norm := module) (T ^ s * c) • h1 + (T ^ (r + r + k)) • h2

theorem coord_frobenius : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d) (M : FCrys l ↥(OL K)) (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)), Framed S M e → ∀ (B : Obj l ↥(OL K)) (V : Eval S B (M.M B)), IsCoord e V → ∀ (t : ↥B.I) (x m : M.M B) (k : ℕ), IsFrac (t : B.A) (M.Φ B t x) m k → ∀ (Q : Obj l ↥(OL K)) (a : Hom B Q) (g : Hom bk.prism Q), ∃ r : ℕ, a.f t ^ r • (BK.hf g bk.E ^ S.a • V.v a g m - a.f t ^ k • (S.A.map (BK.hf g)).mulVec fun i => Q.D.φ (V.v a g x i)) = 0 := by
  intro l _ K bk d S M e hF B V hV t x m k h Q a g
  refine (exists_isFrac (a.f t) (M.Φ Q ⟨a.f t, a.f_I _ t.2⟩ (M.tr a x))).elim fun n hn => hn.elim fun j hn => ?_
  refine (M.Φ_nat a t ⟨a.f t, a.f_I _ t.2⟩ x m k n j h hn).elim fun r hr => ?_
  refine (GlobalTheory.T.prismaticFCrystal_frobenius_pullback_basis l K bk d M e S.a S.A hF.Φ Q g ⟨a.f t, a.f_I _ t.2⟩ (V.v a g x) n j
    ((congrArg (M.Φ Q ⟨a.f t, a.f_I _ t.2⟩) (hV a g x)).symm.trans hn)).elim fun s hs => ?_
  refine (GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ g.f _ _ (M.tr g) (M.tr_bc g) _ e).elim fun b hb => ?_
  exact ⟨r + r + s + j, coord_of_frac_rel b (fun i => M.tr g (e i)) hb (a.f t) (BK.hf g bk.E ^ S.a)
    (V.v a g m) ((S.A.map (BK.hf g)).mulVec fun i => Q.D.φ (V.v a g x i)) n r s j k
    ((congrArg (fun z => (a.f t * a.f t) ^ r • (a.f t ^ j • z - a.f t ^ k • n)) (hV a g m)).symm.trans hr) hs⟩

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPreservesLadicDecayDividedPowerStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_preserves_ladic_decay_dividedPower : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ τ : ZMod a, Function.Injective fun c : Wq l a => algebraMap O K (emb t τ c)) → (∀ x ∈ QSet t K e, ∀ y ∈ QSet t K e, x * y ∈ QSet t K e) → (∀ z ∈ QSet t K e, z ∈ GoodSet t e φ₂) → (∀ (N : ℕ) (w : ℕ × ℕ → Wq l a), (∀ i n, N < i ∨ N < n → w (i, n) = 0) → ∃ M : ℕ, ∀ (τ : ZMod a) (i n : ℕ), M < i ∨ M < n → coeff n (coeff i (frob2 φ₂ (ofW t K e w) τ)) = 0 ∧ coeff n (coeff i ((ofW t K e w ^ l) τ)) = 0) → ∀ w : ℕ × ℕ → Wq l a, LTo0 l w → ∀ v b : ℕ × ℕ → Wq l a, frob2 φ₂ (ofW t K e w) = ofW t K e v → frob2 φ₂ (ofW t K e w) = ofW t K e w ^ l + (l : ZMod a → K⟦X⟧⟦X⟧) * ofW t K e b → LTo0 l v ∧ LTo0 l b := by
  first | exact @GlobalTheory.CrysPrism.frob_keeps_decay | exact GlobalTheory.CrysPrism.frob_keeps_decay | (intros; apply GlobalTheory.CrysPrism.frob_keeps_decay <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeLAdicCharacterAboveOfPublished
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.Published

namespace GlobalTheory.HeckeAboveBridge

theorem heckeLAdicCharacterAbove_of_potSemistable :
    HeckeLAdicCharacterDeRham → HeckeLAdicCharacterCrystalline → DeRhamPotSemistable →
      HeckeLAdicCharacterAbove := by
  intro hdR hcr hpst
  rw [heckeLAdicCharacterAbove_iff]
  intro E Ω _ _ _ _ _ l _ P AI hT ι art hart χ n μ hχ hμ hl w A hA O _ _ _ Bw hB
  have h1 := hdR E Ω l P AI hT ι art hart χ n μ hχ hμ hl w A hA O Bw hB
  exact ⟨h1.1, GlobalTheory.PotCrysRankOne.isPotCrystalline_of_deRham_character hpst E Ω l P AI hT μ hμ A O Bw hB h1.1,
    hcr E Ω l P AI hT ι art hart χ n μ hχ hμ hl w A hA O Bw hB, h1.2⟩

end GlobalTheory.HeckeAboveBridge

end
end

