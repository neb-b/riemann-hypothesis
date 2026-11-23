module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1711
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1528
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0769
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalisationEqStdAtOfCongruentOneAtPrime
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1705
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Definitions.Divisors.TupleReadBaseTupleEqFamily
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1708
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1712
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1290
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0133

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertPlaceLocalFieldData
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.InertCoord
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertPsi

open Formalism.UG GlobalTheory.LFun.InertChart GlobalTheory.InertCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem trace_tmul (R : Type) [CommRing R] [Algebra F R] [Module.Free F E] [Module.Finite F E] (c : R) (x : E) :
    Algebra.trace R (R ⊗[F] E) (c ⊗ₜ[F] x) = c * algebraMap F R (Algebra.trace F E x) := by
  have h1 : c ⊗ₜ[F] x = c • ((1 : R) ⊗ₜ[F] x) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, LinearMap.map_smul, smul_eq_mul]
  congr 1
  rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange]
  congr 1
  refine LinearMap.ext fun y => ?_
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem trace_singleTens (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E) :
    Algebra.trace (AF F) (AF F ⊗[F] E) (Supp.singleTens E v y) =
      GlobalTheory.EmbChart.atPlace v (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) y) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [show Supp.singleTens E v (a ⊗ₜ[F] x) = GlobalTheory.EmbChart.atPlace v a ⊗ₜ[F] x from
      GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.tensNU_tmul _ _ a x, trace_tmul, trace_tmul, mul_comm a, ← Algebra.smul_def,
      LinearMap.map_smul, Algebra.smul_def, mul_comm]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem trace_mem {v : HeightOneSpectrum (𝓞 F)} {y : Fv F v ⊗[F] E} (hy : y ∈ intLoc F E v) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) y ∈ v.adicCompletionIntegers F := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  refine intLoc_induction (p := fun y => Algebra.trace (Fv F v) (Fv F v ⊗[F] E) y ∈ v.adicCompletionIntegers F)
    (fun a ha x => ?_) (by simp) (fun y z hy hz => by rw [map_add]; exact add_mem hy hz)
    (fun y hy => by rw [map_neg]; exact neg_mem hy) hy
  rw [trace_tmul]
  refine mul_mem ha ?_
  have hint : IsIntegral ℤ (Algebra.trace F E (x : E)) := Algebra.isIntegral_trace (RingOfIntegers.isIntegral_coe x)
  have := HeightOneSpectrum.coe_mem_adicCompletionIntegers (K := F) v (⟨_, hint⟩ : 𝓞 F)
  convert this using 1
  first | rfl | simp | (exact (IsScalarTower.algebraMap_apply (𝓞 F) F (Fv F v) (⟨_, hint⟩ : 𝓞 F)))

theorem odd_absNorm {v : HeightOneSpectrum (𝓞 F)} (h2 : (2 : 𝓞 F) ∉ v.asIdeal) : Odd (Ideal.absNorm v.asIdeal) := by
  have hc : Nat.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  haveI := v.isMaximal
  letI := Ideal.Quotient.field v.asIdeal
  haveI : Finite (𝓞 F ⧸ v.asIdeal) := Nat.finite_of_card_ne_zero (hc ▸ h0)
  letI := Fintype.ofFinite (𝓞 F ⧸ v.asIdeal)
  by_contra hodd
  have h1 : ringChar (𝓞 F ⧸ v.asIdeal) = 2 := by
    rw [FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card, hc]
    exact Nat.even_iff.1 (Nat.not_odd_iff_even.1 hodd)
  have h3 : ((2 : ℕ) : 𝓞 F ⧸ v.asIdeal) = 0 := (ringChar.spec _ 2).2 (by rw [h1])
  apply h2
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  rw [map_ofNat]
  simpa using h3

end GlobalTheory.InertPsi

namespace GlobalTheory.InertPsi

open Formalism.UG GlobalTheory.LFun.InertChart GlobalTheory.InertCoord

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} {σ : E →ₐ[F] E}
  {h : w.under (𝓞 F) = v} {c : w.adicCompletion E →+* w.adicCompletion E}

theorem exists_unif (hσ : IsCMExt F E σ) (hw : IsInertAt F E v w) (hc : IsConjAt σ h c) :
    ∃ s : F, IsUnramInv (complMap h (algebraMap F (Fv F v) s)) c (qV F v) := by
  have hval : ∀ a : E, Valued.v (algebraMap E (w.adicCompletion E) a) = w.valuation E a := fun a =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  obtain ⟨s, hs, hs2⟩ := SetLike.not_le_iff_exists.1 (mt Ideal.map_le_iff_le_comap.2 (not_map_le_sq hw))
  have hs1 : algebraMap (𝓞 F) (𝓞 E) s ∈ w.asIdeal := hw ▸ Ideal.mem_map_of_mem _ hs
  refine ⟨(s : F), ?_⟩
  have hϖ : complMap h (algebraMap F (Fv F v) (s : F)) =
      algebraMap E (w.adicCompletion E) (algebraMap (𝓞 F) (𝓞 E) s : E) := by
    rw [complMap_algebraMap]; rfl
  rw [hϖ]
  set ϖ : w.adicCompletion E := algebraMap E _ (algebraMap (𝓞 F) (𝓞 E) s : E) with hϖ'
  have h1 : c ϖ = ϖ := (conj_algebraMap hc _).trans (congrArg _ (σ.commutes (s : F)))
  have h2 : Valued.v ϖ = WithZero.exp (-1 : ℤ) := by
    rw [hϖ', hval, HeightOneSpectrum.valuation_of_algebraMap]
    have a := (w.intValuation_le_pow_iff_mem _ 1).2 (by rwa [pow_one])
    have b := not_le.1 (mt (w.intValuation_le_pow_iff_mem _ 2).1 hs2)
    have h0 : w.intValuation (algebraMap (𝓞 F) (𝓞 E) s) ≠ 0 := b.ne_bot
    rw [← WithZero.exp_log h0] at a b ⊢
    rw [WithZero.exp_le_exp] at a
    rw [WithZero.exp_lt_exp] at b
    congr 1
    omega
  have h3 : ∀ u, Valued.v u = 1 → Valued.v (c u) = 1 := fun u hu => by
    have a : Valued.v (c u) ≤ 1 := conj_mem hw hc hu.le
    have b : Valued.v (c u⁻¹) ≤ 1 := conj_mem hw hc (show Valued.v u⁻¹ ≤ 1 by rw [map_inv₀, hu, inv_one])
    have h0 : u ≠ 0 := fun h0 => by simp [h0] at hu
    rw [map_inv₀, map_inv₀, inv_le_one₀ (by simpa [pos_iff_ne_zero] using h0)] at b
    exact le_antisymm a b
  refine ⟨fun x => ?_, fun x => ?_, h1, h2, ?_, one_lt_absNorm v, ?_⟩
  · obtain ⟨y, rfl⟩ := toCompl_surjective h x
    rw [hc, hc]
    congr 1
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (conj_conj hσ x)
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · by_cases h0 : x = 0
    · simp [h0]
    have h0' : Valued.v x ≠ 0 := by simpa using h0
    have a : Valued.v (x * ϖ ^ WithZero.log (Valued.v x)) = 1 := by
      rw [map_mul, map_zpow₀, h2, ← WithZero.exp_zsmul, ← WithZero.exp_log h0', ← WithZero.exp_add]
      simp
    have b := h3 _ a
    rw [map_mul, map_zpow₀, h1, ← a, map_mul, map_mul] at b
    exact mul_right_cancel₀ (by rw [map_zpow₀, h2]; exact zpow_ne_zero _ WithZero.exp_ne_zero) b
  · obtain ⟨x, hx⟩ := exists_conj_sub_unit hσ hw
    exact ⟨algebraMap E _ (x : E), GlobalTheory.AdeleBaseChange.algebraMap_int_mem x w, by
      rw [conj_algebraMap hc, ← map_sub, hval, hx]⟩
  · exact (P.tjcosets_card_residue w).trans (absNorm_eq hσ.2.2.1 hw)

end GlobalTheory.InertPsi

open GlobalTheory.InertPsi in
theorem GlobalTheory.InertPsi.exists_field_data : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)) (hw : Formalism.UG.IsInertAt F E v w) (h : w.under (𝓞 F) = v),
    ∃ (ϖ : w.adicCompletion E) (σL : w.adicCompletion E →+* w.adicCompletion E) (q : ℕ) (ψL : AddChar (w.adicCompletion E) ℂ),
      IsConjAt σ h σL ∧ Formalism.UG.IsUnramInv ϖ σL q ∧ Odd q ∧
      (∀ z ∈ Formalism.UG.intL (w.adicCompletion E), σL z = z → ψL z = 1) ∧
      (∃ z ∈ Formalism.UG.intL (w.adicCompletion E), σL z = z ∧ ψL (ϖ⁻¹ * z) ≠ 1) ∧
      ∀ z, ψL ((z + σL z) / 2) = B.ψ (⅟(2 : AF F) * Algebra.trace (AF F) (AE F E) (-1 * ptAt hw h z)) := by
  intro F E _ _ _ _ _ σ B hB v w hw h
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨c, hc, -⟩ := InertChart.existsUnique_isConjAt σ hw h
  obtain ⟨s, hU⟩ := exists_unif hB.cm hw hc
  obtain ⟨h2, -, hψ⟩ := hB.inert v w hw
  set k := evFin F v (⅟(2 : AF F)) with hk'
  have hk2 : k * 2 = 1 := by
    rw [hk', ← map_ofNat (evFin F v) 2, ← map_mul, invOf_mul_self, map_one]
  have hv2 : Valued.v (2 : Fv F v) = 1 := by
    rw [← map_ofNat (algebraMap F (Fv F v)) 2]
    refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (2 : F)).trans ?_
    rw [← map_ofNat (algebraMap (𝓞 F) F) 2, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 h2
  have hk : k ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    have := congrArg Valued.v hk2
    rw [map_mul, hv2, mul_one, map_one] at this
    exact this.le
  have hO : ∀ y ∈ v.adicCompletionIntegers F, psiLoc B.ψ v y = 1 := fun y hy => by
    simpa using (hψ 1).2 (one_mem _) y hy
  let ψL : AddChar (w.adicCompletion E) ℂ :=
    { toFun := fun z => B.ψ (⅟(2 : AF F) * Algebra.trace (AF F) (AE F E) (-1 * ptAt hw h z))
      map_zero_eq_one' := by simp
      map_add_eq_mul' := fun a b => by
        simp only [map_add (f := _), mul_add, AddChar.map_add_eq_mul] }
  have hval : ∀ z, ψL z = psiLoc B.ψ v
      (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) ((InertChart.complEquiv hw h).symm (-z)) * k) := fun z => by
    show B.ψ _ = _
    rw [neg_one_mul, ← map_neg (ptAt hw h), ptAt_apply, trace_singleTens, mul_comm,
      GlobalTheory.EmbChart.atPlace_mul_right]
    rfl
  have hcm : ∀ a : Fv F v, (InertChart.complEquiv hw h).symm (complMap h a) = a ⊗ₜ[F] (1 : E) := fun a =>
    (InertChart.complEquiv hw h).symm_apply_eq.2 (by
      show complMap h a = toCompl h (a ⊗ₜ[F] (1 : E))
      rw [toCompl_tmul, map_one, mul_one])
  have htr1 : algebraMap F (Fv F v) (Algebra.trace F E 1) = 2 := by
    rw [show (1 : E) = algebraMap F E 1 from (map_one _).symm, Algebra.trace_algebraMap, hB.cm.2.2.1]
    first | simp [map_ofNat] | (simp; exact map_ofNat _ 2) | (rw [nsmul_eq_mul, mul_one, Nat.cast_ofNat, map_ofNat])
  have hvalc : ∀ a, ψL (complMap h a) = psiLoc B.ψ v (-a) := fun a => by
    rw [hval, ← map_neg, hcm, trace_tmul, htr1, mul_assoc, mul_comm 2 k, hk2, mul_one]
  refine ⟨complMap h (algebraMap F (Fv F v) s), c, Formalism.UG.qV F v, ψL, hc, hU, odd_absNorm h2, ?_, ?_, ?_⟩
  · intro z hz _
    rw [hval]
    refine hO _ (mul_mem (trace_mem ((InertChart.mem_intLoc_iff hw h _).2 ?_)) hk)
    rw [show toCompl h ((InertChart.complEquiv hw h).symm (-z)) = -z from
      (InertChart.complEquiv hw h).apply_symm_apply (-z)]
    exact neg_mem ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hz)
  · have hs : (algebraMap F (Fv F v) s)⁻¹ ∉ v.adicCompletionIntegers F := fun hm => by
      have h4 := complMap_mem h hm
      have h5 : Valued.v (complMap h (algebraMap F (Fv F v) s))⁻¹ ≤ 1 := by
        rw [← map_inv₀]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 h4
      rw [map_inv₀, hU.2.2.2.1] at h5
      exact absurd h5 (by decide)
    obtain ⟨y, hy, hne⟩ : ∃ y ∈ v.adicCompletionIntegers F,
        psiLoc B.ψ v ((algebraMap F (Fv F v) s)⁻¹ * y) ≠ 1 := by
      have := mt (hψ _).1 hs
      push_neg at this
      exact this
    have ht : ∀ a, toCompl h (a ⊗ₜ[F] (1 : E)) = complMap h a := fun a => by
      rw [toCompl_tmul, map_one, mul_one]
    refine ⟨complMap h (-y), (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (complMap_mem h (neg_mem hy)),
      ?_, ?_⟩
    · rw [← ht, hc]
      congr 1
      show (-y) ⊗ₜ[F] σ 1 = _
      rw [map_one]
    · rw [← map_inv₀, ← map_mul, hvalc]
      convert hne using 2
      ring
  · intro z
    show B.ψ _ = B.ψ _
    have hcc : ∀ x, cA σ (cA σ x) = x := fun x => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (InertChart.conj_conj hB.cm x)
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    let cE : AE F E ≃ₐ[AF F] AE F E := AlgEquiv.ofAlgHom (cA σ) (cA σ) (AlgHom.ext hcc) (AlgHom.ext hcc)
    have hT : ∀ x, Algebra.trace (AF F) (AE F E) (cA σ x) = Algebra.trace (AF F) (AE F E) x := fun x =>
      Algebra.trace_eq_of_algEquiv cE x
    haveI : NeZero (2 : w.adicCompletion E) := ⟨fun h0 => two_ne_zero ((map_eq_zero_iff _ (algebraMap E (w.adicCompletion E)).injective).1 ((map_ofNat _ 2).trans h0))⟩
    set y := (z + c z) / 2
    have hy : y + y = z + c z := add_halves _
    have key : Algebra.trace (AF F) (AE F E) (ptAt hw h y) = Algebra.trace (AF F) (AE F E) (ptAt hw h z) := by
      have e1 : Algebra.trace (AF F) (AE F E) (ptAt hw h y) + Algebra.trace (AF F) (AE F E) (ptAt hw h y) =
          Algebra.trace (AF F) (AE F E) (ptAt hw h z) + Algebra.trace (AF F) (AE F E) (ptAt hw h z) := by
        rw [← map_add (f := _), ← map_add (ptAt hw h), hy, map_add (f := _), map_add (f := _), ← cA_ptAt hw h σ hc, hT]
      have e2 : ∀ t : AF F, t = ⅟(2 : AF F) * (t + t) := fun t => by
        rw [← two_mul, ← mul_assoc, invOf_mul_self, one_mul]
      rw [e2 (Algebra.trace _ _ (ptAt hw h y)), e1, ← e2]
    rw [neg_one_mul, neg_one_mul, map_neg, map_neg, key]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaLiftIdempotentForm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.UnitaryMove

section Generic

variable {A : Type} [CommRing A] {n : ℕ} (c : A →+* A)

def ct (X : Matrix (Fin n) (Fin n) A) : Matrix (Fin n) (Fin n) A := (X.map c).transpose

theorem ct_add (X Y : Matrix (Fin n) (Fin n) A) : ct c (X + Y) = ct c X + ct c Y := by
  simp only [ct, Matrix.map_add _ (map_add c), Matrix.transpose_add]

theorem ct_smul (a : A) (X : Matrix (Fin n) (Fin n) A) : ct c (a • X) = c a • ct c X := by
  ext i j
  simp [ct]

theorem ct_one : ct c (1 : Matrix (Fin n) (Fin n) A) = 1 := by
  rw [ct, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]

theorem ct_mul (X Y : Matrix (Fin n) (Fin n) A) : ct c (X * Y) = ct c Y * ct c X := by
  rw [ct, ct, ct, Matrix.map_mul, Matrix.transpose_mul]

theorem ct_ct (hc : ∀ a, c (c a) = a) (X : Matrix (Fin n) (Fin n) A) : ct c (ct c X) = X := by
  ext i j
  exact hc _

theorem blockUnit (hc : ∀ a, c (c a) = a) {e : A} (he : e * e = e) (he' : e * c e = 0)
    (P Q : Matrix (Fin n) (Fin n) A) (hPQ : e • (P * Q) = e • (1 : Matrix (Fin n) (Fin n) A))
    (hQP : e • (Q * P) = e • (1 : Matrix (Fin n) (Fin n) A)) :
    ((1 - e - c e) • (1 : Matrix (Fin n) (Fin n) A) + e • P + c e • ct c Q) *
        ((1 - e - c e) • (1 : Matrix (Fin n) (Fin n) A) + e • Q + c e • ct c P) = 1 ∧
      ((1 - e - c e) • (1 : Matrix (Fin n) (Fin n) A) + e • Q + c e • ct c P) *
        ((1 - e - c e) • (1 : Matrix (Fin n) (Fin n) A) + e • P + c e • ct c Q) = 1 ∧
      ct c ((1 - e - c e) • (1 : Matrix (Fin n) (Fin n) A) + e • P + c e • ct c Q) =
        (1 - e - c e) • (1 : Matrix (Fin n) (Fin n) A) + e • Q + c e • ct c P := by
  have hee : c e * c e = c e := by rw [← map_mul, he]
  have he2 : c e * e = 0 := by rw [mul_comm, he']
  set f := 1 - e - c e with hf
  have hcf : c f = f := by rw [hf, map_sub, map_sub, map_one, hc]; ring
  have h1 : e * f = 0 := by rw [hf]; linear_combination -he - he'
  have h2 : c e * f = 0 := by rw [hf]; linear_combination -hee - he'
  have h3 : f * e = 0 := by rw [mul_comm, h1]
  have h4 : f * c e = 0 := by rw [mul_comm, h2]
  have h5 : f * f = f := by linear_combination f * hf - h3 - h4
  have hsum : f + e + c e = 1 := by rw [hf]; ring
  have hPQ' : c e • (ct c Q * ct c P) = c e • (1 : Matrix (Fin n) (Fin n) A) := by
    rw [← ct_mul, ← ct_smul, hPQ, ct_smul, ct_one]
  have hQP' : c e • (ct c P * ct c Q) = c e • (1 : Matrix (Fin n) (Fin n) A) := by
    rw [← ct_mul, ← ct_smul, hQP, ct_smul, ct_one]
  refine ⟨?_, ?_, ?_⟩
  · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, he, he', hee, he2,
      h1, h2, h3, h4, h5, zero_smul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, hPQ, hPQ']
    rw [← add_smul, ← add_smul, hsum, one_smul]
  · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, he, he', hee, he2,
      h1, h2, h3, h4, h5, zero_smul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, hQP, hQP']
    rw [← add_smul, ← add_smul, hsum, one_smul]
  · rw [ct_add, ct_add, ct_smul, ct_smul, ct_smul, ct_one, ct_ct c hc, hcf, hc]
    abel

end Generic

variable {D : D7}

theorem cA_cA (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | tmul a x => exact congrArg (fun y : D.host.E => a ⊗ₜ[D.host.F] y) (star_star x)
  | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb]

theorem exists_blockUnit : ∀ {D : D7} (V : HSp D), V.gram = 1 → ∀ (e : AE D), e * e = e → e * cA D e = 0 →
    ∀ (P Q : Matrix (Fin V.rank) (Fin V.rank) (AE D)), e • (P * Q) = e • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) →
      e • (Q * P) = e • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) →
    ∃ g : GA D V,
      Formalism.L2.Theta.mt V g = (1 - e - cA D e) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) + e • P + cA D e • (Q.map (cA D)).transpose ∧
      Formalism.L2.Theta.mt V g⁻¹ = (1 - e - cA D e) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) + e • Q + cA D e • (P.map (cA D)).transpose := by
  intro D V hV e he he' P Q hPQ hQP
  obtain ⟨h1, h2, h3⟩ := blockUnit (cA D) cA_cA he he' P Q hPQ hQP
  have hmem : (((1 - e - cA D e) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) + e • P + cA D e • ct (cA D) Q).map (cA D)).transpose *
      V.gram.map (incA D) * ((1 - e - cA D e) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) + e • P + cA D e • ct (cA D) Q) =
      V.gram.map (incA D) := by
    rw [hV, Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
    exact (congrArg (· * _) h3).trans h2
  let u : GL (Fin V.rank) (AE D) := ⟨_, _, h1, h2⟩
  have hu : u ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF D.host.F) D.sp.cm.sig V.gram := hmem
  let g : GA D V := (⟨u, hu⟩ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF D.host.F) D.sp.cm.sig V.gram)
  have hg : Formalism.L2.Theta.mt V g = u.1 := rfl
  have hg' : Formalism.L2.Theta.mt V g⁻¹ = u⁻¹.1 := rfl
  exact ⟨g, hg, hg'⟩
end GlobalTheory.UnitaryMove
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryInvTransposeOfScaledInverseGram
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SiegelThetaInvT

private theorem invTranspose_abstract {E A n : Type} [Field E] [CommRing A] [Fintype n] [DecidableEq n]
    (ι : E →+* A) (c : A →+* A) (G J : Matrix n n E) (hG : G.det ≠ 0) (x : E) (hx : x ≠ 0) (ξ : A)
    (hξ : ξ • J.map ι = (x • G⁻¹).map ι) (M N : Matrix n n A) (hMN : M * N = 1) (hNM : N * M = 1)
    (hb : Mᵀ * J.map ι * M.map c = J.map ι) :
    (Nᵀ.map c)ᵀ * G.map ι * Nᵀ = G.map ι := by
  have hdet : IsUnit G.det := isUnit_iff_ne_zero.2 hG
  have hKG : G⁻¹.map ι * G.map ι = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hGK : G.map ι * G⁻¹.map ι = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hdet, Matrix.map_one _ (map_zero _) (map_one _)]
  have hsm : (x • G⁻¹).map ι = ι x • G⁻¹.map ι := by
    ext i j
    simp [smul_eq_mul, map_mul]
  have hd : ι x⁻¹ * ι x = 1 := by rw [← map_mul, inv_mul_cancel₀ hx, map_one]
  generalize G⁻¹.map ι = K at hKG hGK hsm
  generalize G.map ι = G' at hKG hGK ⊢
  have h1 : ι x • (Mᵀ * K * M.map c) = ι x • K := by
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, ← hsm, ← hξ, Matrix.mul_smul, Matrix.smul_mul, hb]
  have h2 : Mᵀ * K * M.map c = K := by
    have := congrArg (fun X => ι x⁻¹ • X) h1
    simpa only [smul_smul, hd, one_smul] using this
  have hcNM : N.map c * M.map c = 1 := by
    rw [← Matrix.map_mul, hNM]
    exact Matrix.map_one _ (map_zero c) (map_one c)
  have hX : N.map c * G' * Nᵀ * K = 1 := by
    calc N.map c * G' * Nᵀ * K = N.map c * G' * Nᵀ * (Mᵀ * K * M.map c) := by rw [h2]
      _ = N.map c * G' * ((M * N)ᵀ * K) * M.map c := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = N.map c * M.map c := by
          rw [hMN, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_assoc (N.map c), hGK, Matrix.mul_one]
      _ = 1 := hcNM
  have hT : (Nᵀ.map c)ᵀ = N.map c := rfl
  rw [hT]
  calc N.map c * G' * Nᵀ = N.map c * G' * Nᵀ * (K * G') := by rw [hKG, Matrix.mul_one]
    _ = G' := by rw [← Matrix.mul_assoc, hX, Matrix.one_mul]

private def invT {A n : Type} [CommRing A] [Fintype n] [DecidableEq n] (m : GL n A) : GL n A :=
  ⟨(m⁻¹).1ᵀ, m.1ᵀ, by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩

private theorem sigR_eq_cA {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) (x : AF F ⊗[F] E) : sigR (AF F) σ x = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => simp [sigR, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]

private theorem invT_mem_HR {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {r : ℕ}
    (G J : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0) (x : E) (hx : x ≠ 0) (ξ : AF F ⊗[F] E)
    (hξ : ξ • incM F J = incM F (x • G⁻¹))
    (b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) (incM F J)) :
    ∃ g : HR (AF F) σ G, g.1.1 = (b⁻¹).1.1ᵀ := by
  obtain ⟨m, hm⟩ := b
  have hb : m.1ᵀ * incM F J * m.1.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) = incM F J := hm
  have hc : (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ : AF F ⊗[F] E → AF F ⊗[F] E) = sigR (AF F) σ :=
    funext fun y => (sigR_eq_cA σ y).symm
  rw [hc] at hb
  have key := invTranspose_abstract (inclR (F := F) (AF F)) (sigR (AF F) σ) G J hG x hx ξ hξ m.1 (m⁻¹).1
    (Units.mul_inv m) (Units.inv_mul m) hb
  exact ⟨⟨invT m, key⟩, rfl⟩

theorem _root_.GlobalTheory.T.exists_unitary_invTranspose_of_scaledInverseGram : ∀ (D : D7) (V : HSp D) (J : Matrix (Fin V.rank) (Fin V.rank) D.host.E)
    (ξ : AF D.host.F ⊗[D.host.F] D.host.E), ξ • incM D.host.F J = incM D.host.F (D.host.xi0 • V.gram⁻¹) →
    ∀ b : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F J),
      ∃ g : GA D V, Formalism.L2.Theta.mt V g = (b⁻¹).1.1ᵀ := by
  intro D V J ξ hξ b
  obtain ⟨g, hg⟩ := invT_mem_HR D.sp.cm.sig V.gram J (GlobalTheory.Doubling.isHermND_gram V).2 D.host.xi0
    (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D) ξ hξ b
  exact ⟨g, hg⟩

end GlobalTheory.SiegelThetaInvT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamilyHypothesesOfWorkingClassSevenDuties
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX

namespace GlobalTheory.BigTop

theorem famHyp_of_working_duty : ∀ (𝒜 : FamClass) (eps : ℝ) (Fm : FamP eps),
    GlobalTheory.Fc.W3 𝒜 Fm → GlobalTheory.EX.DQ.Duty7 Fm → GlobalTheory.BigTop.FamHyp Fm := by
  intro 𝒜 eps Fm hW hD
  obtain ⟨⟨⟨⟨_, hDvd, _, hBox, hQD, hCYL⟩, hSm⟩, hTw⟩, hCE, hTu, hDG⟩ := hW
  obtain ⟨h1, h2, h3, h4, h5, _, _⟩ := GlobalTheory.EX.DQ.duty_seven_library eps Fm hD
  exact ⟨h1, h2, h3, h4, h5, hDvd, hBox, hQD, hCYL, hSm, hTw, hCE, hTu, hDG⟩

end GlobalTheory.BigTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarVectorScalingIdele
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.LemF.QuotInv

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (tensNU)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem continuous_compFinV (v : HeightOneSpectrum (𝓞 F)) : Continuous (compFin F E v) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact GlobalTheory.AutFunCompare.continuous_tensNU (E := E) (evFin F v).toLinearMap (map_mul (evFin F v))
    ((RestrictedProduct.continuous_eval v).comp continuous_snd)


end GlobalTheory.ThK.LemF.QuotInv

end
end

