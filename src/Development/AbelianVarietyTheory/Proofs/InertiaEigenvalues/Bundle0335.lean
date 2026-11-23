module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0316
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0307
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0314
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
public import Formalism.PadicSubsetSums.CentralIdempotents.Bundle0002
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0007
public import Formalism.PadicSubsetSums.StableGradedCounts.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelSurjective.Simple
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0328
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0077
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0118
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0182
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0121

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeWildJumpSumTotallyRamified
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem card_le_jumpSum_wild_of_exponent :
    ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L]
      [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L]
      [FiniteDimensional F L] [IsGalois F L] (p E : ℕ) (B : Subgroup (L ≃ₐ[F] L)), p.Prime → 0 < E →
      lowerRamificationGroup F L 0 = ⊤ → OrdIs L p E → (∀ σ τ : L ≃ₐ[F] L, σ * τ * σ⁻¹ * τ⁻¹ ∈ B) →
      (∀ σ : L ≃ₐ[F] L, σ ^ p ∈ B) → B ≠ ⊤ → Nat.card (L ≃ₐ[F] L) ≤ jumpSum (wild F L) ⊤ B := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ p E B hp hE h0 hord hcomm hpow hB
  have hBn : B.Normal := ⟨fun b hb σ => by
    have h := B.mul_mem (hcomm σ b) hb
    simpa [mul_assoc] using h⟩
  set M := IntermediateField.fixedField B
  have hker : (AlgEquiv.restrictNormalHom (F := F) (K₁ := L) M).ker = B := by
    rw [IntermediateField.restrictNormalHom_ker, IntermediateField.fixingSubgroup_fixedField]
  have hsurj := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := M) L
  obtain ⟨e, hordF, hEe, -⟩ := _root_.GlobalTheory.PMon.Ram.ordIs_of_ordIs_ext F L p E hord
  have he : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; omega
    · exact h
  have hM0 : upperRamificationGroup F M 0 = ⊤ := by
    rw [← map_upperRamificationGroup M 0, upperRamificationGroup_zero, h0, Subgroup.map_top_of_surjective _ hsurj]
  have hMexp : ∀ s : M ≃ₐ[F] M, s ^ p = 1 := by
    intro s
    obtain ⟨σ, rfl⟩ := hsurj s
    rw [← map_pow, ← MonoidHom.mem_ker, hker]
    exact hpow σ
  have hM1 := _root_.GlobalTheory.PMon.Ram.upperRamificationGroup_one_eq_top_of_exponent F M p e hp he hordF hM0 hMexp
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀, σ₀ ∉ B := by
    by_contra h
    push_neg at h
    exact hB (eq_top_iff.mpr fun x _ => h x)
  have hmem : AlgEquiv.restrictNormalHom M σ₀ ∈ (upperRamificationGroup F L 1).map (AlgEquiv.restrictNormalHom M) := by
    rw [map_upperRamificationGroup M 1, hM1]; trivial
  obtain ⟨σ, hσ, hσe⟩ := hmem
  have hσB : σ ∉ B := by
    intro hσB
    apply hσ₀
    rw [← hker, MonoidHom.mem_ker, ← hσe, ← MonoidHom.mem_ker, hker]
    exact hσB
  have := _root_.GlobalTheory.PMon.Ram.card_mul_le_jumpSum_of_mem_upper_not_mem F L B 1 h0 σ hσ hσB
  rw [mul_one] at this
  exact_mod_cast this

end GlobalTheory.PMon.Ram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentsSimpleFDRepFiniteFinsumEqOne
section
open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerOSys
open Polynomial CategoryTheory

namespace GlobalTheory.SerOSys.ZSum

variable {Γ : Type} [Group Γ] [Fintype Γ]

theorem zIdem_eq_centralIdem (τ : FDRep ℂ Γ) : zIdem τ = Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.centralIdem τ.ρ := by
  unfold zIdem Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.centralIdem
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [MonoidAlgebra.of_apply, MonoidAlgebra.smul_single', mul_one]
  rfl

theorem zIdem_eq_charIdem' (τ : FDRep ℂ Γ) : zIdem τ = PI.CharIdem.charIdem τ := by
  unfold zIdem PI.CharIdem.charIdem
  rfl

theorem isIrreducible_of_simple (τ : FDRep ℂ Γ) (h : Simple τ) : Representation.IsIrreducible τ.ρ := by
  haveI := h
  have hc : (Nat.card Γ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have : Invertible (Nat.card Γ : ℂ) := invertibleOfNonzero hc
  apply GlobalTheory.AbsIrrDescent.isIrreducible_of_norm_one
  have hs := FDRep.char_orthonormal τ τ
  rw [if_pos ⟨Iso.refl _⟩, inv_mul_eq_one₀ hc] at hs
  exact hs.symm

theorem isIrr_of_simple (τ : FDRep ℂ Γ) (h : Simple τ) : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.IsIrr τ.ρ :=
  Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.CISum.isIrr_of_isIrreducible _ (isIrreducible_of_simple τ h)

theorem isIrreducible_of_isIrr {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ Γ W)
    (h : Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.IsIrr σ) : σ.IsIrreducible := by
  obtain ⟨hnt, hW⟩ := h
  refine { exists_pair_ne := ⟨⊥, ⊤, fun e => ?_⟩, eq_bot_or_eq_top := fun U => ?_ }
  · have h1 := congrArg Subrepresentation.toSubmodule e
    exact (bot_ne_top : (⊥ : Submodule ℂ W) ≠ ⊤) h1
  · rcases hW U.toSubmodule (fun g x hx => U.apply_mem_toSubmodule g hx) with h1 | h1
    · left; exact Subrepresentation.toSubmodule_injective h1
    · right; exact Subrepresentation.toSubmodule_injective h1

theorem zIdem_eq_of_iso {τ τ' : FDRep ℂ Γ} (i : τ ≅ τ') : zIdem τ = zIdem τ' := by
  have h1 : τ.character = τ'.character := FDRep.char_iso i
  have h2 : Module.finrank ℂ τ = Module.finrank ℂ τ' := (FDRep.isoToLinearEquiv i).finrank_eq
  change ∑ γ : Γ, MonoidAlgebra.single γ ((Module.finrank ℂ τ : ℂ) / Fintype.card Γ * τ.character γ⁻¹) =
    ∑ γ : Γ, MonoidAlgebra.single γ ((Module.finrank ℂ τ' : ℂ) / Fintype.card Γ * τ'.character γ⁻¹)
  rw [h1, h2]

theorem zIdem_eq_of_equiv (τ τ' : FDRep ℂ Γ) (φ : τ ≃ₗ[ℂ] τ') (hφ : ∀ g x, φ (τ.ρ g x) = τ'.ρ g (φ x)) :
    zIdem τ = zIdem τ' := by
  have h2 : Module.finrank ℂ τ = Module.finrank ℂ τ' := φ.finrank_eq
  have h1 : ∀ g, LinearMap.trace ℂ τ' (τ'.ρ g) = LinearMap.trace ℂ τ (τ.ρ g) := by
    intro g
    have : τ'.ρ g = φ.conj (τ.ρ g) := by
      ext x; simp [LinearEquiv.conj_apply, hφ]
    rw [this, LinearMap.trace_conj']
  unfold zIdem
  simp only [h1, h2]

theorem zIdem_ne_zero (τ : FDRep ℂ Γ) (h : Simple τ) : zIdem τ ≠ 0 := by
  intro h0
  have ha := (orthogonalCentral Γ τ τ h h).1
  rw [← zIdem_eq_charIdem', h0, map_zero] at ha
  obtain ⟨hnt, -⟩ := isIrr_of_simple τ h
  obtain ⟨v, hv⟩ := exists_ne (0 : τ)
  exact hv (by simpa using (LinearMap.congr_fun ha v).symm)

theorem zIdem_mul_self (τ : FDRep ℂ Γ) (h : Simple τ) : zIdem τ * zIdem τ = zIdem τ := by
  have := (orthogonalCentral Γ τ τ h h).2.2.1
  rw [zIdem_eq_charIdem']; exact this

theorem zIdem_mul_of_ne (τ τ' : FDRep ℂ Γ) (h : Simple τ) (h' : Simple τ') (hne : zIdem τ ≠ zIdem τ') :
    zIdem τ * zIdem τ' = 0 := by
  have := (orthogonalCentral Γ τ τ' h h').2.2.2.2 ⟨fun i => hne (zIdem_eq_of_iso i)⟩
  rw [zIdem_eq_charIdem', zIdem_eq_charIdem']; exact this

end GlobalTheory.SerOSys.ZSum

namespace GlobalTheory.SerOSys.ZSum

variable {Γ : Type} [Group Γ] [Fintype Γ]

theorem zIdem_set_finite :
    {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z}.Finite := by
  set S := {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z}
  have hli : LinearIndependent ℂ (fun z : S => (z : MonoidAlgebra ℂ Γ)) := by
    rw [linearIndependent_iff']
    intro s c hs j hj
    obtain ⟨τ, hτ, hτz⟩ := j.2
    have hmul := congrArg (· * (j : MonoidAlgebra ℂ Γ)) hs
    simp only [Finset.sum_mul, zero_mul, smul_mul_assoc] at hmul
    rw [Finset.sum_eq_single j] at hmul
    · rw [← hτz, zIdem_mul_self τ hτ] at hmul
      exact (smul_eq_zero.1 hmul).resolve_right (zIdem_ne_zero τ hτ)
    · intro i _ hij
      obtain ⟨σ, hσ, hσz⟩ := i.2
      have hne : zIdem σ ≠ zIdem τ := by
        rw [hσz, hτz]; exact fun e => hij (Subtype.ext e)
      rw [← hσz, ← hτz, zIdem_mul_of_ne σ τ hσ hτ hne, smul_zero]
    · intro hn; exact absurd hj hn
  exact Set.finite_coe_iff.1 hli.finite

theorem zIdem_set_finsum :
    ∑ᶠ z ∈ {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z}, z = 1 := by
  classical
  set S := {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z} with hS
  have hfin : S.Finite := zIdem_set_finite
  letI : Fintype S := hfin.fintype
  choose τ hτ hτz using fun z : S => z.2
  have key := Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.central_idempotents_sum_one Γ S (fun z => (τ z : Type)) (fun z => (τ z).ρ)
    (fun z => isIrr_of_simple (τ z) (hτ z))
    (fun i j ⟨φ, hφ⟩ => Subtype.ext ((hτz i).symm.trans ((zIdem_eq_of_equiv (τ i) (τ j) φ hφ).trans (hτz j))))
    (fun W _ _ _ σ hσ => by
      haveI := isIrreducible_of_isIrr σ hσ
      have hs : Simple (FDRep.of σ) := PI.GreenLabelSurjWork.simple_of_irr σ
      let i : S := ⟨zIdem (FDRep.of σ), FDRep.of σ, hs, rfl⟩
      obtain ⟨e, he⟩ := repIso_of_zIdem_eq_of_simple (FDRep.of σ) (τ i) hs (hτ i) (hτz i).symm
      exact ⟨i, e, fun g x => he g x⟩)
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin,
    Finset.sum_subtype hfin.toFinset (fun x => Set.Finite.mem_toFinset hfin) (fun z => z), ← key]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [← zIdem_eq_centralIdem, hτz z]

end GlobalTheory.SerOSys.ZSum

namespace GlobalTheory.SerOSys

theorem zIdem_finite_and_finsum_eq_one : ∀ (Γ : Type) [Group Γ] [Fintype Γ],
    {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z}.Finite ∧
      ∑ᶠ z ∈ {z : MonoidAlgebra ℂ Γ | ∃ τ : FDRep ℂ Γ, Simple τ ∧ zIdem τ = z}, z = 1 :=
  fun _ _ _ => ⟨ZSum.zIdem_set_finite, ZSum.zIdem_set_finsum⟩

end GlobalTheory.SerOSys
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChevalleyUnits
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.ChevalleyUnitsProof

theorem normFacts (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (b : ℕ)
    (hb : ((b : ℕ) : 𝓞 F) ∉ v.asIdeal) :
    0 < normV v ∧ ((normV v : ℕ) : 𝓞 F) ∈ v.asIdeal ∧ (normV v).Coprime b := by
  classical
  have hN : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hne : v.asIdeal ≠ ⊥ := v.ne_bot
  refine ⟨?_, ?_, ?_⟩
  · rw [hN]; exact Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hne)
  · rw [hN]; exact Ideal.absNorm_mem _
  · haveI : v.asIdeal.IsMaximal := v.isMaximal
    letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
    haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
    letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
    obtain ⟨p, hp⟩ := CharP.exists (𝓞 F ⧸ v.asIdeal)
    haveI := hp
    haveI : Fact p.Prime := ⟨CharP.char_is_prime (𝓞 F ⧸ v.asIdeal) p⟩
    obtain ⟨n, hp', hcard⟩ := FiniteField.card (𝓞 F ⧸ v.asIdeal) p
    have hNv : normV v = p ^ (n : ℕ) := by
      unfold normV; rw [Nat.card_eq_fintype_card, hcard]
    apply Nat.coprime_of_dvd
    intro q hq hqN hqb
    rw [hNv] at hqN
    have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq hp').1 (hq.dvd_of_dvd_pow hqN)
    subst hqp
    apply hb
    obtain ⟨e, rfl⟩ := hqb
    rw [Nat.cast_mul]
    apply Ideal.mul_mem_right
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ _

theorem core (E : Type) [Field E] [NumberField E] (l r b : ℕ) (hl : l.Prime) (hb : 0 < b) :
    ∃ a : ℕ, 0 < a ∧ a.Coprime b ∧ ∀ u : (𝓞 E)ˣ, (a : 𝓞 E) ∣ (u : 𝓞 E) - 1 → ∃ v : (𝓞 E)ˣ, u = v ^ (l ^ r) := by
  classical
  have hm : 0 < l ^ r := pow_pos hl.pos r
  set m := l ^ r with hmdef
  obtain ⟨M, hM0, hmM, hD⟩ := _root_.GlobalTheory.exists_pow_descent_cyclotomic E l r hl
  let Ω := AlgebraicClosure E
  haveI : NeZero (M : Ω) := ⟨by exact_mod_cast hM0.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  let K : IntermediateField E Ω := IntermediateField.adjoin E {ζ}
  haveI : FiniteDimensional E K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  haveI : NumberField K := NumberField.of_module_finite E K
  haveI : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.tower_top (K := E) K
  haveI : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  let ζK : K := ⟨ζ, IntermediateField.mem_adjoin_simple_self E ζ⟩
  have hζK : IsPrimitiveRoot ζK M :=
    (show IsPrimitiveRoot (algebraMap K Ω ζK) M from hζ).of_map_of_injective (algebraMap K Ω).injective
  obtain ⟨L, hLfin, hLgal, hLroots⟩ := _root_.GlobalTheory.KummerUnits.exists_finite_galois_mem_of_pow_eq_unit E K Ω M hM0 ⟨ζK, hζK⟩
  let S : Set (HeightOneSpectrum (𝓞 K)) := {v | ((M * b : ℕ) : 𝓞 K) ∈ v.asIdeal}
  have hS : S.Finite := by
    have hne : Ideal.span {((M * b : ℕ) : 𝓞 K)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Nat.mul_pos hM0 hb).ne'
    refine (Ideal.finite_factors hne).subset ?_
    intro v hv
    exact Ideal.dvd_span_singleton.2 hv
  have hchoice : ∀ g : L ≃ₐ[K] L, ∃ v : HeightOneSpectrum (𝓞 K), v ∉ S ∧ ∃ B : ValuationSubring Ω,
      IsPlaceOver B v ∧ ∃ σ : G K Ω, IsFrob B (normV v) σ ∧ AlgEquiv.restrictNormalHom L σ = g := by
    intro g
    obtain ⟨v, hv, -, B, hB, -, σ, hσ, hg⟩ := GlobalTheory.Published.chebotarevDegreeOne' K Ω L g S hS
    exact ⟨v, hv, B, hB, σ, hσ, hg⟩
  choose v hvS B hB σ hσ hg using hchoice
  have hvb : ∀ g, ((b : ℕ) : 𝓞 K) ∉ (v g).asIdeal := fun g h =>
    hvS g (by simp only [S, Set.mem_setOf_eq, Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h)
  have hvM : ∀ g, ((M : ℕ) : 𝓞 K) ∉ (v g).asIdeal := fun g h =>
    hvS g (by simp only [S, Set.mem_setOf_eq, Nat.cast_mul]; exact Ideal.mul_mem_right _ _ h)
  have hnf := fun g => normFacts K (v g) b (hvb g)
  let a : ℕ := ∏ g : L ≃ₐ[K] L, normV (v g)
  refine ⟨a, Finset.prod_pos fun g _ => (hnf g).1, Nat.Coprime.prod_left fun g _ => (hnf g).2.2, ?_⟩
  intro u hu
  obtain ⟨c, hc⟩ := hu
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω ((u : 𝓞 E) : E)) hM0
  have hwL := hLroots u w hw
  let x : 𝓞 K := ⟨algebraMap E K ((u : 𝓞 E) : E), ((u : 𝓞 E).2).map (IsScalarTower.toAlgHom ℤ E K)⟩
  let c' : 𝓞 K := ⟨algebraMap E K (c : E), (c.2).map (IsScalarTower.toAlgHom ℤ E K)⟩
  have hx1 : ∀ g, x - 1 ∈ (v g).asIdeal := by
    intro g
    have hxc : x - 1 = ((a : ℕ) : 𝓞 K) * c' := by
      apply RingOfIntegers.ext
      change algebraMap E K ((u : 𝓞 E) : E) - 1 = ((a : ℕ) : K) * algebraMap E K ((c : 𝓞 E) : E)
      have h2 := congrArg (fun t : 𝓞 E => algebraMap E K (t : E)) hc
      simpa using h2
    rw [hxc]
    apply Ideal.mul_mem_right
    have hdvd : normV (v g) ∣ a := Finset.dvd_prod_of_mem _ (Finset.mem_univ g)
    obtain ⟨e, he⟩ := hdvd
    rw [he, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (hnf g).2.1
  have hwx : w ^ M = algebraMap K Ω (x : K) := by
    rw [hw]; rfl
  have hfix : ∀ g : L ≃ₐ[K] L, g ⟨w, hwL⟩ = ⟨w, hwL⟩ := by
    intro g
    have h1 := GlobalTheory.T.isFrob_fixes_root_of_one_mod_place K Ω M ζK hζK (v g) (hvM g) (B g) (hB g) (σ g) (hσ g) x (hx1 g) w hwx
    rw [← hg g]
    apply Subtype.ext
    rw [AlgEquiv.restrictNormalHom_apply]
    exact h1
  have hwK : (⟨w, hwL⟩ : L) ∈ (⊥ : IntermediateField K L) := (IsGalois.mem_bot_iff_fixed _).2 hfix
  obtain ⟨k, hk⟩ := IntermediateField.mem_bot.1 hwK
  have hwK' : w ∈ K := by
    have : algebraMap K Ω k = w := congrArg Subtype.val hk
    rw [← this]; exact k.2
  obtain ⟨y, hy⟩ := hD Ω ζ hζ _ w hwK' hw
  have hu0 : ((u : 𝓞 E) : E) ≠ 0 := by
    intro h0
    have : ((u : 𝓞 E)) = 0 := RingOfIntegers.ext (by simpa using h0)
    exact u.ne_zero this
  have hy0 : y ≠ 0 := by
    rintro rfl; exact hu0 (by rw [← hy, zero_pow hm.ne'])
  have hyi : IsIntegral ℤ y := IsIntegral.of_pow hm (by rw [hy]; exact (u : 𝓞 E).2)
  have hyi' : IsIntegral ℤ y⁻¹ := IsIntegral.of_pow hm (by
    rw [inv_pow, hy]
    have : (((u⁻¹ : (𝓞 E)ˣ) : 𝓞 E) : E) = ((u : 𝓞 E) : E)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      have h3 := congrArg (fun t : 𝓞 E => (t : E)) u.inv_mul
      simpa using h3
    rw [← this]; exact ((u⁻¹ : (𝓞 E)ˣ) : 𝓞 E).2)
  refine ⟨⟨⟨y, hyi⟩, ⟨y⁻¹, hyi'⟩, RingOfIntegers.ext (by change y * y⁻¹ = 1; exact mul_inv_cancel₀ hy0), RingOfIntegers.ext (by change y⁻¹ * y = 1; exact inv_mul_cancel₀ hy0)⟩, ?_⟩
  apply Units.ext
  apply RingOfIntegers.ext
  rw [Units.val_pow_eq_pow_val]
  change ((u : 𝓞 E) : E) = y ^ m
  rw [hy]

theorem combine (E : Type) [Field E] [NumberField E] (b m₁ m₂ : ℕ) (hcop : m₁.Coprime m₂)
    (h₁ : ∃ a : ℕ, 0 < a ∧ a.Coprime b ∧ ∀ u : (𝓞 E)ˣ, (a : 𝓞 E) ∣ (u : 𝓞 E) - 1 → ∃ v : (𝓞 E)ˣ, u = v ^ m₁)
    (h₂ : ∃ a : ℕ, 0 < a ∧ a.Coprime b ∧ ∀ u : (𝓞 E)ˣ, (a : 𝓞 E) ∣ (u : 𝓞 E) - 1 → ∃ v : (𝓞 E)ˣ, u = v ^ m₂) :
    ∃ a : ℕ, 0 < a ∧ a.Coprime b ∧ ∀ u : (𝓞 E)ˣ, (a : 𝓞 E) ∣ (u : 𝓞 E) - 1 →
      ∃ v : (𝓞 E)ˣ, u = v ^ (m₁ * m₂) := by
  obtain ⟨a₁, ha₁, hc₁, hu₁⟩ := h₁
  obtain ⟨a₂, ha₂, hc₂, hu₂⟩ := h₂
  refine ⟨a₁ * a₂, Nat.mul_pos ha₁ ha₂, Nat.Coprime.mul_left hc₁ hc₂, ?_⟩
  intro u hu
  have hd₁ : (a₁ : 𝓞 E) ∣ (u : 𝓞 E) - 1 := dvd_trans ⟨(a₂ : 𝓞 E), by push_cast; ring⟩ hu
  have hd₂ : (a₂ : 𝓞 E) ∣ (u : 𝓞 E) - 1 := dvd_trans ⟨(a₁ : 𝓞 E), by push_cast; ring⟩ hu
  obtain ⟨v₁, hv₁⟩ := hu₁ u hd₁
  obtain ⟨v₂, hv₂⟩ := hu₂ u hd₂
  set s := Nat.gcdA m₁ m₂
  set t := Nat.gcdB m₁ m₂
  have hg : ((1 : ℕ) : ℤ) = (m₁ : ℤ) * s + (m₂ : ℤ) * t := by
    rw [← hcop.gcd_eq_one]; exact Nat.gcd_eq_gcd_ab m₁ m₂
  have key : u = u ^ ((m₁ : ℤ) * s + (m₂ : ℤ) * t) := by
    rw [← hg]; simp
  have e1 : u ^ ((m₁ : ℤ) * s) = v₂ ^ (s * ((m₁ * m₂ : ℕ) : ℤ)) := by
    conv_lhs => rw [hv₂]
    rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
  have e2 : u ^ ((m₂ : ℤ) * t) = v₁ ^ (t * ((m₁ * m₂ : ℕ) : ℤ)) := by
    conv_lhs => rw [hv₁]
    rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
  refine ⟨v₂ ^ s * v₁ ^ t, ?_⟩
  calc u = u ^ ((m₁ : ℤ) * s + (m₂ : ℤ) * t) := key
    _ = u ^ ((m₁ : ℤ) * s) * u ^ ((m₂ : ℤ) * t) := zpow_add _ _ _
    _ = (v₂ ^ s * v₁ ^ t) ^ (m₁ * m₂) := by
      rw [e1, e2, zpow_mul, zpow_mul, ← mul_zpow, zpow_natCast]

end GlobalTheory.ChevalleyUnitsProof

theorem GlobalTheory.Published.chevalleyUnits' : GlobalTheory.Published.ChevalleyUnits := by
  intro E _ _ m b hm hb
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn => exact GlobalTheory.ChevalleyUnitsProof.core E p n b hp hb
  | zero => exact absurd hm (lt_irrefl 0)
  | one => exact ⟨1, one_pos, Nat.coprime_one_left b, fun u _ => ⟨u, (pow_one u).symm⟩⟩
  | coprime a b' ha hb' hab iha ihb => exact GlobalTheory.ChevalleyUnitsProof.combine E b a b' hab (iha (by omega)) (ihb (by omega))

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassFunctionDegreeEqSumDerivatives
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLq.DegDer

variable {g : ℕ} [Fact g.Prime]

theorem tl_one {a n : ℕ} (h : a ≤ n) : tl a (1 : Mt g n) = (1 : Mt g a) := by
  ext i j
  have hi : (i : ℕ) < n := by omega
  have hj : (j : ℕ) < n := by omega
  simp only [tl, entN, hi, hj, and_self, dif_pos, Matrix.one_apply, Fin.ext_iff]

theorem br_one {a b n : ℕ} (h : a + b ≤ n) : br a b (1 : Mt g n) = (1 : Mt g b) := by
  ext i j
  have hi : a + (i : ℕ) < n := by omega
  have hj : a + (j : ℕ) < n := by omega
  simp only [br, entN, hi, hj, and_self, dif_pos, Matrix.one_apply, Fin.ext_iff]
  simp

theorem toG_one {n : ℕ} : toG (1 : Mt g n) = 1 := by
  unfold toG
  rw [dif_pos isUnit_one]
  ext : 1
  simp

theorem hc_one (a b : ℕ) (α : Gn g a → ℂ) (β : Gn g b → ℂ) :
    hc a b α β (a + b) 1 = ((Fintype.card (Gn g a) * Fintype.card (Gn g b) * g ^ (a * b) : ℕ) : ℂ)⁻¹ *
      ((Fintype.card (Gn g (a + b)) : ℂ) * (α 1 * β 1)) := by
  unfold hc hcT
  rw [← GlobalTheory.GLm.ParBasic.card_par]
  congr 1
  simp only [mul_one, inv_mul_cancel, Units.val_one, GlobalTheory.GLm.ParBasic.inPar_one, if_true,
    tl_one (Nat.le_add_right a b), br_one (le_refl (a + b)), toG_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]

theorem blockDiagonalWithIdentityGL_one (k : ℕ) : diag1 (1 : Gn g k) (k + 1) = 1 := by
  unfold diag1
  have : (fun i j : Fin (k + 1) => if (i : ℕ) < k ∧ (j : ℕ) < k then entN ((1 : Gn g k) : Mt g k) i j
      else (1 : Mt g (k + 1)) i j) = (1 : Mt g (k + 1)) := by
    ext i j
    split_ifs with h
    · simp only [Units.val_one, entN, h, and_self, dif_pos, Matrix.one_apply, Fin.ext_iff]
    · rfl
  rw [this, toG_one]

theorem prod_pow_add (a b : ℕ) :
    (∏ i : Fin (a + b), (g : ℂ) ^ (i : ℕ)) =
      (∏ i : Fin a, (g : ℂ) ^ (i : ℕ)) * (∏ i : Fin b, (g : ℂ) ^ (i : ℕ)) * (g : ℂ) ^ (a * b) := by
  rw [Fin.prod_univ_add]
  simp only [Fin.coe_castAdd, Fin.coe_natAdd, pow_add, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [← pow_mul]
  ring

theorem prod_Icc_add (f : ℕ → ℂ) (a b : ℕ) :
    (∏ i ∈ Finset.Icc 1 (a + b), f i) = (∏ i ∈ Finset.Icc 1 a, f i) * ∏ i ∈ Finset.Ico (a + 1) (a + b + 1), f i := by
  have e : ∀ n, Finset.Icc 1 n = Finset.Ico 1 (n + 1) := fun n => by ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [e, e, Finset.prod_Ico_consecutive _ (by omega) (by omega)]

theorem card_Gn_factors_ne_zero (n : ℕ) :
    (∏ i : Fin n, (g : ℂ) ^ (i : ℕ)) ≠ 0 ∧ (∏ i ∈ Finset.Icc 1 n, ((g : ℂ) ^ i - 1)) ≠ 0 := by
  have h : (Fintype.card (Gn g n) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [GlobalTheory.GLq.GGDeg.card_Gn] at h
  exact mul_ne_zero_iff.mp h

theorem one_eq_sum_der : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (n : ℕ) (χ : Gn g n → ℂ),
    0 < n → IsClass χ → χ 1 = ∑ m ∈ Finset.range n, der ψ m χ 1 * ∏ i ∈ Finset.Ico (m + 1) n, ((g : ℂ) ^ i - 1) := by
  intro g _ ψ hψ n χ hn hχ
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hM : IsMirClass χ := fun p x _ _ => hχ x p
  have h1 : χ 1 = χ (diag1 (1 : Gn g k) (k + 1)) := by rw [blockDiagonalWithIdentityGL_one]
  rw [h1, GlobalTheory.GLm.mirClass_diag1_eq_sum g ψ hψ k χ hM 1]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ k := by have := Finset.mem_range.mp hi; omega
  obtain ⟨b, rfl⟩ : ∃ b, k = i + b := ⟨k - i, by omega⟩
  have hkb : i + b - i = b := by omega
  rw [hkb, hc_one, (GlobalTheory.GLq.GGDeg.gg_one_and_isClass g ψ b).1]
  push_cast
  rw [GlobalTheory.GLq.GGDeg.card_Gn i, GlobalTheory.GLq.GGDeg.card_Gn b, GlobalTheory.GLq.GGDeg.card_Gn (i + b), prod_pow_add,
    prod_Icc_add]
  obtain ⟨hPi, hQi⟩ := card_Gn_factors_ne_zero (g := g) i
  obtain ⟨hPb, hQb⟩ := card_Gn_factors_ne_zero (g := g) b
  have hg : (g : ℂ) ^ (i * b) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : g.Prime).ne_zero)
  field_simp

end GlobalTheory.GLq.DegDer
end

