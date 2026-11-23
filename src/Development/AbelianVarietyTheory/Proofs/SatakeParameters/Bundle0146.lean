module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmithNormalFormIntegralMatrix
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0018
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0940
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0143
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FourthPowerTheta

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLimitDvdUniformizerPowCauchy
section
open Matrix Filter Topology

namespace GlobalTheory.Hk3.IntWittBase

open Formalism.UG GlobalTheory.Hk3.IntWitt

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem val_lt_exp_of_dvdPow_succ {ϖ x : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    {N : ℕ} (hx : DvdPow ϖ (N + 1) x) : Valued.v x < WithZero.exp (-(N : ℤ)) := by
  obtain ⟨b, hb, hxb⟩ := hx
  rw [hxb, map_mul, map_pow, hϖ]
  calc (WithZero.exp (-1 : ℤ)) ^ (N + 1) * Valued.v b ≤ (WithZero.exp (-1 : ℤ)) ^ (N + 1) * 1 :=
        mul_le_mul' le_rfl hb
    _ = WithZero.exp (-((N + 1 : ℕ) : ℤ)) := by
        rw [mul_one, ← WithZero.exp_nsmul]; congr 1; push_cast; ring
    _ < WithZero.exp (-(N : ℤ)) := WithZero.exp_lt_exp.2 (by push_cast; omega)

theorem isClosed_dvdPow_sub {ϖ : L} (h0 : ϖ ≠ 0) (m : ℕ) (c : L) : IsClosed {x : L | DvdPow ϖ m (x - c)} := by
  have hp : ϖ ^ m ≠ 0 := pow_ne_zero _ h0
  have he : {x : L | DvdPow ϖ m (x - c)} =
      (fun x => (ϖ ^ m)⁻¹ * (x - c)) ⁻¹' ((Valued.v (R := L)).integer : Set L) := by
    ext x
    constructor
    · rintro ⟨b, hb, hxb⟩
      show Valued.v ((ϖ ^ m)⁻¹ * (x - c)) ≤ 1
      rw [hxb, inv_mul_cancel_left₀ hp]; exact hb
    · intro hx
      exact ⟨(ϖ ^ m)⁻¹ * (x - c), hx, by rw [mul_inv_cancel_left₀ hp]⟩
  rw [he]
  exact (Valued.isClosed_integer L).preimage (by fun_prop)

theorem exists_limit_dvdPow (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (a : ℕ → L) (ha : ∀ k, DvdPow ϖ (k + 1) (a (k + 1) - a k)) :
    ∃ b : L, ∀ k, DvdPow ϖ (k + 1) (b - a k) := by
  have h0 : ϖ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  have hint : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [hϖ]
    show WithZero.exp (-1 : ℤ) ≤ WithZero.exp 0
    exact WithZero.exp_le_exp.2 (by omega)
  have hstep : ∀ k m, k ≤ m → DvdPow ϖ (k + 1) (a m - a k) := by
    intro k m hkm
    induction m, hkm using Nat.le_induction with
    | base => rw [sub_self]; exact dvdPow_zero ϖ _
    | succ m hkm ih =>
      have := dvdPow_add (dvdPow_mono hint (Nat.succ_le_succ hkm) (ha m)) ih
      rwa [sub_add_sub_cancel] at this
  have hc : CauchySeq a := by
    rw [(Valued.hasBasis_uniformity L (WithZero (Multiplicative ℤ))).cauchySeq_iff]
    intro γ _
    have hγ : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ (0 : WithZero (Multiplicative ℤ)) := by
      simp
    obtain ⟨e, he⟩ : ∃ e, MonoidWithZeroHom.ValueGroup₀.embedding γ.1 = WithZero.exp e :=
      ⟨_, (WithZero.exp_log hγ).symm⟩
    refine ⟨(-e).toNat, fun m hm n hn => ?_⟩
    show Valued.v.restrict (a n - a m) < γ.1
    rw [Valuation.restrict_lt_iff_lt_embedding, he]
    have h1 := dvdPow_sub (hstep _ n hn) (hstep _ m hm)
    rw [sub_sub_sub_cancel_right] at h1
    refine (val_lt_exp_of_dvdPow_succ hϖ h1).trans_le (WithZero.exp_le_exp.2 ?_)
    have := Int.self_le_toNat (-e)
    omega
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨b, fun k => ?_⟩
  exact (isClosed_dvdPow_sub h0 (k + 1) (a k)).mem_of_tendsto hb
    (eventually_atTop.2 ⟨k, fun m hm => hstep k m hm⟩)

end GlobalTheory.Hk3.IntWittBase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSmithNormalFormGeneratorsExactOrders
section
open Matrix

noncomputable section

namespace GlobalTheory.Hk3.SnfGen

open GlobalTheory.Hk3.Smith

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem mulVec_int {a b : ℕ} {A : Matrix (Fin a) (Fin b) L} {x : Fin b → L}
    (hA : ∀ i j, A i j ∈ Formalism.UG.intL L) (hx : ∀ j, x j ∈ Formalism.UG.intL L) :
    ∀ i, (A *ᵥ x) i ∈ Formalism.UG.intL L := fun i => by
  simp only [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hA i k) (hx k)

theorem exp_of_gt {ϖ : L}
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    {d : L} (hd : 1 < Valued.v d) :
    1 ≤ (-Formalism.UG.ordL d).toNat ∧ Valued.v (d * ϖ ^ (-Formalism.UG.ordL d).toNat) = 1 := by
  have hϖ0 : ϖ ≠ 0 := by
    intro h; rw [h, map_zero] at hϖ; exact WithZero.zero_ne_coe hϖ
  have hd0 : d ≠ 0 := by rintro rfl; simp at hd
  have hv := v_eq_ord hd0
  rw [hv] at hd
  have hpos : 0 < -Formalism.UG.ordL d := by
    rw [← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero, Multiplicative.ofAdd_lt] at hd; exact hd
  refine ⟨by omega, ?_⟩
  have h2 := v_inv_pow hϖ (-Formalism.UG.ordL d).toNat
  rw [Int.toNat_of_nonneg hpos.le, ← hv] at h2
  rw [map_mul, ← h2, ← map_mul, ← mul_pow, inv_mul_cancel₀ hϖ0, one_pow, map_one]

theorem main_gen (ϖ : L)
    (hϖ : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)))
    (n : ℕ) (b : Matrix (Fin n) (Fin n) L) :
    ∃ (r : ℕ) (M : Matrix (Fin n) (Fin r) L) (e : Fin r → ℕ),
    (∀ k, 1 ≤ e k) ∧ (∀ i k, M i k ∈ Formalism.UG.intL L) ∧ (∀ i k, (b * M) i k * ϖ ^ e k ∈ Formalism.UG.intL L) ∧
    (∀ m : Fin n → L, (∀ i, m i ∈ Formalism.UG.intL L) → ∃ α : Fin r → L, (∀ k, α k ∈ Formalism.UG.intL L) ∧
      ∀ i, (b *ᵥ (m - M *ᵥ α)) i ∈ Formalism.UG.intL L) ∧
    (∀ β : Fin r → L, (∀ k, β k ∈ Formalism.UG.intL L) → (∀ i, (b *ᵥ (M *ᵥ β)) i ∈ Formalism.UG.intL L) →
      ∀ k, Valued.v (β k) ≤ Valued.v ϖ ^ e k) := by
  classical
  obtain ⟨P, Q, ⟨hPi, P', hP'i, hPP'⟩, ⟨hQi, Q', hQ'i, hQQ'⟩, hD⟩ := exists_diag n n b
  have hP'P : P' * P = 1 := mul_eq_one_comm.mp hPP'
  obtain ⟨D, hDdef⟩ : ∃ D, D = P * b * Q := ⟨_, rfl⟩
  rw [← hDdef] at hD
  have hDd : ∀ i j, i ≠ j → D i j = 0 := fun i j h => hD i j (fun h' => h (Fin.ext h'))
  have hbQ : b * Q = P' * D := by
    rw [hDdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hP'P, Matrix.one_mul]
  obtain ⟨r, σ, hσinj, hσ⟩ : ∃ (r : ℕ) (σ : Fin r → Fin n), Function.Injective σ ∧
      ∀ j, (1 < Valued.v (D j j) ↔ ∃ k, σ k = j) := by
    let S := {i : Fin n // 1 < Valued.v (D i i)}
    refine ⟨Fintype.card S, fun k => ((Fintype.equivFin S).symm k).1,
      fun k l h => (Fintype.equivFin S).symm.injective (Subtype.ext h), fun j => ⟨fun h => ?_, ?_⟩⟩
    · exact ⟨Fintype.equivFin S ⟨j, h⟩, by simp⟩
    · rintro ⟨k, rfl⟩; exact ((Fintype.equivFin S).symm k).2
  have hσsel : ∀ k, 1 < Valued.v (D (σ k) (σ k)) := fun k => (hσ _).2 ⟨k, rfl⟩
  have hsum : ∀ g : Fin n → L, ∑ k, g (σ k) = ∑ j, if 1 < Valued.v (D j j) then g j else 0 := by
    intro g
    rw [← Finset.sum_filter, ← Finset.sum_image (hσinj.injOn)]
    congr 1; ext j; simp [hσ]
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin n) (Fin r) L, ∀ i k, M i k = Q i (σ k) :=
    ⟨Matrix.of fun i k => Q i (σ k), fun _ _ => rfl⟩
  have hbM : ∀ i k, (b * M) i k = P' i (σ k) * D (σ k) (σ k) := by
    intro i k
    have : (b * M) i k = (b * Q) i (σ k) := by simp only [Matrix.mul_apply, hM]
    rw [this, hbQ, Matrix.mul_apply, Finset.sum_eq_single (σ k)]
    · intro l _ hl; rw [hDd l (σ k) hl, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hPbM : ∀ j k, (P * b * M) j k = D j (σ k) := by
    intro j k; simp only [hDdef, Matrix.mul_apply, hM]
  refine ⟨r, M, fun k => (-Formalism.UG.ordL (D (σ k) (σ k))).toNat, fun k => (exp_of_gt hϖ (hσsel k)).1,
    fun i k => by rw [hM]; exact hQi _ _, fun i k => ?_, fun m hm => ?_, fun β hβ hbβ k => ?_⟩
  · rw [hbM, mem_intL, mul_assoc, map_mul, (exp_of_gt hϖ (hσsel k)).2, mul_one]
    exact mem_intL.1 (hP'i _ _)
  · obtain ⟨c, hc⟩ : ∃ c, c = Q' *ᵥ m := ⟨_, rfl⟩
    have hci : ∀ j, c j ∈ Formalism.UG.intL L := by rw [hc]; exact mulVec_int hQ'i hm
    have hmc : m = Q *ᵥ c := by rw [hc, Matrix.mulVec_mulVec, hQQ', Matrix.one_mulVec]
    obtain ⟨cs, hcs⟩ : ∃ cs : Fin n → L, ∀ j, cs j = if 1 < Valued.v (D j j) then c j else 0 :=
      ⟨fun j => if 1 < Valued.v (D j j) then c j else 0, fun _ => rfl⟩
    refine ⟨fun k => c (σ k), fun k => hci _, ?_⟩
    have hMα : M *ᵥ (fun k => c (σ k)) = Q *ᵥ cs := by
      funext i
      simp only [Matrix.mulVec, dotProduct, hM, hcs]
      exact (hsum (fun j => Q i j * c j)).trans (by simp only [mul_ite, mul_zero])
    rw [hmc, hMα, ← Matrix.mulVec_sub, Matrix.mulVec_mulVec, hbQ, ← Matrix.mulVec_mulVec]
    refine mulVec_int hP'i (fun j => ?_)
    have hDv : (D *ᵥ (c - cs)) j = D j j * (c j - cs j) := by
      simp only [Matrix.mulVec, dotProduct, Pi.sub_apply]
      rw [Finset.sum_eq_single j]
      · intro l _ hl; rw [hDd j l (Ne.symm hl), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hDv, hcs]
    split_ifs with hj
    · rw [sub_self, mul_zero]; exact Subring.zero_mem _
    · rw [sub_zero]; exact Subring.mul_mem _ (mem_intL.2 (not_lt.1 hj)) (hci j)
  · have h1 := mulVec_int hPi hbβ (σ k)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at h1
    have h2 : ((P * b * M) *ᵥ β) (σ k) = D (σ k) (σ k) * β k := by
      simp only [Matrix.mulVec, dotProduct, hPbM]
      rw [Finset.sum_eq_single k]
      · intro l _ hl; rw [hDd _ _ (fun h => hl (hσinj h).symm), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h2, mem_intL] at h1
    have hex := (exp_of_gt hϖ (hσsel k)).2
    beta_reduce
    calc Valued.v (β k) = Valued.v (β k) * Valued.v (D (σ k) (σ k) * ϖ ^ (-Formalism.UG.ordL (D (σ k) (σ k))).toNat) := by
          rw [hex, mul_one]
      _ = Valued.v (D (σ k) (σ k) * β k) * Valued.v ϖ ^ (-Formalism.UG.ordL (D (σ k) (σ k))).toNat := by
          rw [map_mul, map_mul, map_pow]; ac_rfl
      _ ≤ Valued.v ϖ ^ (-Formalism.UG.ordL (D (σ k) (σ k))).toNat := mul_le_of_le_one_left' h1

end GlobalTheory.Hk3.SnfGen

theorem GlobalTheory.Hk3.snf_generators : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L), Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
  ∀ (n : ℕ) (a : GL (Fin n) L), ∃ (r : ℕ) (M : Matrix (Fin n) (Fin r) L) (e : Fin r → ℕ),
    (∀ k, 1 ≤ e k) ∧ (∀ i k, M i k ∈ Formalism.UG.intL L) ∧ (∀ i k, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * M) i k * ϖ ^ e k ∈ Formalism.UG.intL L) ∧ (∀ m : Fin n → L, (∀ i, m i ∈ Formalism.UG.intL L) → ∃ α : Fin r → L, (∀ k, α k ∈ Formalism.UG.intL L) ∧
      ∀ i, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ (m - M *ᵥ α)) i ∈ Formalism.UG.intL L) ∧ (∀ β : Fin r → L, (∀ k, β k ∈ Formalism.UG.intL L) → (∀ i, (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) *ᵥ (M *ᵥ β)) i ∈ Formalism.UG.intL L) →
      ∀ k, Valued.v (β k) ≤ Valued.v ϖ ^ e k) := by
  intro L _ _ ϖ hϖ n a
  exact GlobalTheory.Hk3.SnfGen.main_gen ϖ hϖ n _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsWeilGroupRestrictExtension
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

namespace GlobalTheory.AboveL
section
variable {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [Field L] [NumberField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω]

theorem comap_eq_of_placeOver {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)}
    (h : IsPlaceOver A v) (h' : IsPlaceOver A v') :
    v'.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal := by
  ext x
  rw [Ideal.mem_comap, ← h x, ← h' (algebraMap (𝓞 K) (𝓞 L) x)]
  have : ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) = algebraMap K L (x : K) := rfl
  rw [this, ← IsScalarTower.algebraMap_apply]

end

theorem normV_eq_pow {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L))
    (hc : v'.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = v.asIdeal) :
    ∃ f : ℕ, normV v' = normV v ^ f := by
  classical
  haveI := v.isMaximal
  haveI := v'.isMaximal
  letI : Field (𝓞 K ⧸ v.asIdeal) := Ideal.Quotient.field _
  letI : Field (𝓞 L ⧸ v'.asIdeal) := Ideal.Quotient.field _
  haveI : Finite (𝓞 K ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
  haveI : Finite (𝓞 L ⧸ v'.asIdeal) := v'.asIdeal.finiteQuotientOfFreeOfNeBot v'.ne_bot
  letI : Fintype (𝓞 K ⧸ v.asIdeal) := Fintype.ofFinite _
  letI : Fintype (𝓞 L ⧸ v'.asIdeal) := Fintype.ofFinite _
  letI : Algebra (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ v'.asIdeal) :=
    (Ideal.quotientMap v'.asIdeal (algebraMap (𝓞 K) (𝓞 L)) hc.ge).toAlgebra
  refine ⟨Module.finrank (𝓞 K ⧸ v.asIdeal) (𝓞 L ⧸ v'.asIdeal), ?_⟩
  simp only [normV, Nat.card_eq_fintype_card]
  exact Module.card_eq_pow_finrank
end GlobalTheory.AboveL

namespace GlobalTheory.AboveL
section
variable {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [Field L] [NumberField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω]

theorem restrictScalars_mem_Dec {A : ValuationSubring Ω} {σ : G L Ω} (hσ : σ ∈ Dec (F := L) A) :
    (σ.restrictScalars K : G K Ω) ∈ Dec (F := K) A := hσ

theorem actsAs_restrictScalars {A : ValuationSubring Ω} {σ : G L Ω} {q f a b : ℕ} (hσ : ActsAs A (q ^ f) σ a b) :
    ActsAs A q (σ.restrictScalars K : G K Ω) (f * a) (f * b) := by
  refine ⟨restrictScalars_mem_Dec hσ.1, fun x hx => ?_⟩
  have := hσ.2 x hx
  rw [← pow_mul, ← pow_mul] at this
  exact this

theorem restrictScalars_mem_Ine_iff {A : ValuationSubring Ω} {σ : G L Ω} :
    (σ.restrictScalars K : G K Ω) ∈ Ine (F := K) A ↔ σ ∈ Ine (F := L) A := Iff.rfl

end

theorem exists_weil_restrict : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (σ' : Weil h'), ∃ σ : Weil h, (∀ z : Ω, (σ : G K Ω) z = (σ' : G L Ω) z) ∧ (deg σ = 0 ↔ deg σ' = 0) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' σ'
  obtain ⟨f, hf⟩ := normV_eq_pow v v' (comap_eq_of_placeOver h h')
  obtain ⟨a, b, hab⟩ := (mem_Weil h').mp σ'.2
  rw [hf] at hab
  refine ⟨⟨(σ' : G L Ω).restrictScalars K, (mem_Weil h).mpr ⟨_, _, actsAs_restrictScalars hab⟩⟩, fun z => rfl, ?_⟩
  rw [deg_eq_zero_iff, deg_eq_zero_iff]
  exact restrictScalars_mem_Ine_iff
end GlobalTheory.AboveL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExponentHeckeCharCompNormConjEmbedding
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Published GlobalTheory.ContraPair
open GlobalTheory.CuspRep.InfType GlobalTheory.CuspRep.AlgExpo

namespace GlobalTheory.NormExpo

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

theorem adeleMap_real_injective :
    Function.Injective (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap (maximalRealSubfield E) E) := by
  intro x y h
  rw [← GlobalTheory.UnitaryHeckeBaseChange.toAdele_algebraMap, ← GlobalTheory.UnitaryHeckeBaseChange.toAdele_algebraMap] at h
  have h2 := (GlobalTheory.UnitaryHeckeBaseChange.adeleEquiv (isCMExt_real E)).injective (a₁ := algebraMap _ _ x) (a₂ := algebraMap _ _ y) h
  exact Algebra.TensorProduct.includeLeft_injective (S := maximalRealSubfield E)
    (algebraMap (maximalRealSubfield E) E).injective h2

theorem conjAd_infId (u : (Cinf E)ˣ) :
    Units.map (GlobalTheory.UnitaryBC.conjAd E).toMonoidHom (infId E u) = infId E (Units.map (starRingEnd (Cinf E)).toMonoidHom u) := by
  refine Units.ext (Prod.ext ?_ ?_)
  · change infEq E (starRingEnd (Cinf E) ((infEq E).symm (1 - infEq E 1 + infEq E u))) =
      1 - infEq E 1 + infEq E (starRingEnd (Cinf E) u)
    simp
  · change conjFin _ ((1 : Af E) - 0 + 0) = (1 : Af E) - 0 + 0
    simp

theorem ideleNorm_infId_star (u : (Cinf E)ˣ) :
    ideleNorm E (infId E (Units.map (starRingEnd (Cinf E)).toMonoidHom u)) = ideleNorm E (infId E u) := by
  refine Units.ext (adeleMap_real_injective E ?_)
  refine congrArg Units.val (a₁ := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap _ E _) (a₂ := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap _ E _) ?_
  rw [ideleMap_ideleNorm, ideleMap_ideleNorm, GlobalTheory.PolChar.ideleConj_eq, GlobalTheory.PolChar.ideleConj_eq, conjAd_infId,
    conjAd_infId, mul_comm]
  congr 2
  exact Units.ext (star_star _)

theorem star_expU_atEmb (τ : E →+* ℂ) (z : ℂ) :
    Units.map (starRingEnd (Cinf E)).toMonoidHom (expU (atEmb τ z)) = expU (atEmb τ (starRingEnd ℂ z)) := by
  classical
  refine Units.ext (funext fun w => ?_)
  change starRingEnd ℂ (Complex.exp (atEmb τ z w)) = Complex.exp (atEmb τ (starRingEnd ℂ z) w)
  rw [← Complex.exp_conj]
  congr 1
  unfold atEmb
  by_cases hw : w = InfinitePlace.mk τ
  · subst hw; split_ifs <;> simp
  · simp [Pi.single_eq_of_ne hw]

theorem expo_compNorm_conjugate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (χ : HChar (maximalRealSubfield E)) (τ : E →+* ℂ),
    expo (compNorm E χ) (ComplexEmbedding.conjugate τ) = expo (compNorm E χ) τ := by
  intro E _ _ _ χ τ
  refine (GlobalTheory.CuspRep.expo_eq_of_exp _ τ _ (expo (compNorm E χ) τ) fun z => ?_).symm
  have h : chiInf (compNorm E χ) (expU (atEmb τ z)) = chiInf (compNorm E χ) (expU (atEmb τ (starRingEnd ℂ z))) := by
    rw [← star_expU_atEmb]
    exact congrArg χ.1 (ideleNorm_infId_star E _).symm
  rw [h, chiInf_expU_atEmb, Complex.conj_conj, add_comm]

end GlobalTheory.NormExpo
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FamilySplitOperatorsEqLabelOperatorsModels
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitHeckeLabel

theorem ext_mul {Gr Γ W K : Type} [Group Gr] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Field K] [NumberField K]
    [StarRing K] {ι : Γ →* Gr} {S : CSD K} {σ : K →+* ℂ} {ρ : Γ →* Module.End ℂ W} {J : Subgroup Gr} {χ : J →* ℂˣ}
    (P : Bridge.ClassPres ι S σ ρ J χ) (f : S.Forms) (g : Gr) (k : J) (hk : χ k = 1) : P.ext f.1 (g * k) = P.ext f.1 g := by
  have h2 := (GlobalTheory.classPres_basic ι S σ ρ J χ P).1 f 1 g k
  rwa [map_one, map_one, one_mul, Module.End.one_apply, hk, Units.val_one, one_smul] at h2

def rightTr {H Gr : Type} [Group H] [Group Gr] (φ : H →* Gr) (W : Type) [AddCommGroup W] [Module ℂ W] :
    H →* Module.End ℂ (Gr → W) where
  toFun g := LinearMap.funLeft ℂ W (fun h => h * φ g)
  map_one' := by ext F h; simp [LinearMap.funLeft]
  map_mul' g g' := by ext F h; simp [LinearMap.funLeft, mul_assoc]

theorem rightTr_sum {H Gr : Type} [Group H] [Group Gr] (φ : H →* Gr) {W : Type} [AddCommGroup W] [Module ℂ W] (s : Finset H)
    (F : Gr → W) (h : Gr) : (∑ γ ∈ s, rightTr φ W γ) F h = ∑ γ ∈ s, F (h * φ γ) := by
  rw [LinearMap.sum_apply, Finset.sum_apply]
  rfl

theorem opOf_single {D : D7} {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M)
    (P : Pl D.host.E) (d : List ℤ) : opOf π P (Finsupp.single d 1) = ∑ γ ∈ Hk3.rep V P d, π γ := by
  unfold opOf
  rw [Finsupp.sum_single_index (by exact zero_smul ℂ _), one_smul]

theorem hkF_single {D : D7} (V : HSp D) {W : Type} [AddCommGroup W] [Module ℂ W] (P : Pl D.host.E) (d : List ℤ)
    (F : Bridge.Gf V → W) :
    hkF V P (Finsupp.single d 1) F = opOf (rightTr (finHom V).rangeRestrict W) P (Finsupp.single d 1) F := by
  funext h
  have e1 : hkF V P (Finsupp.single d 1) F h = (1 : ℂ) • ∑ γ ∈ Hk3.rep V P d, F (h * (finHom V).rangeRestrict γ) :=
    Finsupp.sum_single_index (h := fun d (z : ℂ) => z • ∑ γ ∈ Hk3.rep V P d, F (h * (finHom V).rangeRestrict γ))
      (zero_smul ℂ _)
  exact e1.trans ((one_smul ℂ _).trans ((rightTr_sum (finHom V).rangeRestrict _ F h).symm.trans
    (congrArg (fun u : Module.End ℂ (Bridge.Gf V → W) => u F h) (opOf_single _ P d).symm)))

theorem side_label {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (L : LevDat D.host.E ℂ V.rank) (hβ : IsSDFrame V β Λ 1) {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {ρ : GQ V →* Module.End ℂ W} {K : Type} [Field K] [NumberField K] [StarRing K] {σ : K →+* ℂ} {S : CSD K}
    (Pr : Bridge.ClassPres (Bridge.ratF V) S σ ρ (levEnv V β L).J (levEnv V β L).χ) {Pl0 : Type} (pl : Pl0 → Pl D.host.E)
    (ok : Set Pl0) (op : ok × ℕ → Module.End K S.Forms)
    (Comparison₂ : Bridge.HeckeTie (Bridge.ratF V) Pr op (fun i => 1 ≤ i.2 ∧ i.2 ≤ V.rank) (isTEnv V pl ok) (isLocEnv V pl ok))
    (P : ok) (h0 : op (P, 0) = 1) (hoff : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ pl P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP (pl P))
    (k : ℕ) (hk : k ≤ V.rank) (f : S.Forms) :
    Pr.ext (op (P, k) f).1 = hkF V (pl P) (Finsupp.single (splitLab V.rank k) 1) (Pr.ext f.1) := by
  refine hβ.elim fun c hc => ?_
  have hc' : IsBaseFrame V β Λ 1 := (one_pow c : (1 : ℕ) ^ c = 1) ▸ hc
  have h1 : ((1 : ℕ) : 𝓞 D.host.E) ∉ (pl P).asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 (pl P).isPrime.ne_top
  have hl := fun e f' he => (GlobalTheory.LevSplit.lev_split V β Λ 1 (flag1L L) hc').2 (pl P) e f' he h1 hoff
  have hinv : ∀ g (x : (levEnv V β L).J), IsLocElt V (pl P) x → Pr.ext f.1 (g * x) = Pr.ext f.1 g := by
    rintro g ⟨x, hx⟩ ⟨e, f', a, he, ha, hxa, hs⟩
    obtain rfl : x = (finHom V).rangeRestrict a := Subtype.ext hxa
    exact ext_mul Pr f g _ (Units.ext ((hl e f' he).2.1 a ⟨ha, hx⟩ hs))
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · have e0 : splitLab V.rank 0 = List.replicate V.rank 0 := by simp [splitLab]
    rw [h0, e0, hkF_single]
    refine ((_root_.GlobalTheory.SphLabelOps.label_operators V (pl P)).2.2.1.2 _ _ _ fun a ha => ?_).symm
    obtain ⟨ha, e, f', he, hs⟩ := ha
    funext g
    exact hinv g ⟨(finHom V).rangeRestrict a, (((hl e f' he).1 a hs).2 ha).2⟩ ⟨e, f', a, he, ha.1, rfl, hs⟩
  · have hi : 1 ≤ ((P, k) : ok × ℕ).2 ∧ ((P, k) : ok × ℕ).2 ≤ V.rank := ⟨hpos, hk⟩
    have hs := fun x => _root_.GlobalTheory.Hk3Split.isLabElt_of_isTEnv V pl ok (P, k) x
    have hd := _root_.GlobalTheory.HkDict.dcOp_eq_label V β Λ 1 L hc' (pl P) h1 hoff (splitLab V.rank k) (Comparison₂.hx (P, k)) (Comparison₂.hA (P, k)) (hs 1).2.2
      ((hs _).1 hk (Comparison₂.hx_ok _ hi)) (fun a ha => (hs a).2.1 (Comparison₂.hA_loc _ hi a ha)) (Comparison₂.hDC _ hi)
    exact (Comparison₂.op_eq _ hi f).trans (hd.2 W _ hinv)

theorem split_ops : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → (∀ t h, IsOpsX R t h → ∀ (P : A.ok t) k, k ≤ D.sp.X'.rank → ∀ f, R.jX t (A.heckeR t (P, k) f) = h (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1) (R.jX t f)) ∧ ∀ j t h, IsOpsV R j t h → ∀ (P : A.ok t) k, k ≤ (Vc D j).rank → ∀ f, R.jV j t (A.heckeL j t (P, k) f) = h (R.pl P) (Finsupp.single (splitLab (Vc D j).rank k) 1) (R.jV j t f) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF hM
  have hgood : ∀ t (P : A.ok t), Good R t (R.pl P) := fun t P => ((_root_.GlobalTheory.GoodPrimes.good_primes R F hL).2.2.2 hF t P P.2).1
  refine ⟨fun t h hh P k hk f => ?_, fun j t h hh P k hk f => ?_⟩
  · have hd := side_label D.sp.X' R.βX R.ΛX (R.datXt t) hL.βX (R.B.R t).pres R.pl (A.ok t) (A.heckeR t) (R.B.R t).hecke
      P (hF.degR t P).1 (hgood t P) k hk f
    refine (hM.HX t).1 ?_
    refine (hM.jX t _).trans (Eq.trans ?_ (hh _ (hgood t P) _ _).symm)
    exact hd.trans (congrArg (hkF D.sp.X' (R.pl P) (Finsupp.single (splitLab D.sp.X'.rank k) 1)) (hM.jX t f).symm)
  · have hd := side_label (Vc D j) (R.βV j) (R.ΛV j) (R.datVt j t) (hL.βV j) (R.B.L j t).pres R.pl (A.ok t) (A.heckeL j t)
      (R.B.L j t).hecke P (hF.degL j t P).1 (hgood t P) k hk f
    refine (hM.HV j t).1 ?_
    refine (hM.jV j t _).trans (Eq.trans ?_ (hh _ (hgood t P) _ _).symm)
    exact hd.trans (congrArg (hkF (Vc D j) (R.pl P) (Finsupp.single (splitLab (Vc D j).rank k) 1)) (hM.jV j t f).symm)

end GlobalTheory.SplitHeckeLabel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocJetsAll
section
namespace GlobalTheory.ThLoc

theorem locJets_all :
    Formalism.L2.Th1.GD.IntOpLoc ∧ Formalism.L2.Th1.GD.IntOpTwoLoc ∧
      (Formalism.L2.Th1.GD.EmbSep → Formalism.L2.Th1.GD.ShapeEigenLoc) :=
  ⟨LocJets.jetsOdd, LocJets.jetsTwo, LocJets.shape⟩

end GlobalTheory.ThLoc
end

