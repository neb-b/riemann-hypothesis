module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0362
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0033
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ChiNHomPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0011
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0018
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LevelSubgroupCharacterUnitary
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0010
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.PoincareConstantEq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0115

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameFactorsLocalUnitsAlmostAll
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped nonZeroDivisors

namespace GlobalTheory.FrameFactorUnit

open Formalism.MainNotions.S.LocNG IsDedekindDomain
open scoped nonZeroDivisors

variable {D : D7}

theorem ddS_ne_zero : ddS D ≠ 0 := by
  unfold ddS
  rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.map_eq_bot_iff_of_injective]
  · exact differentIdeal_ne_bot
  · exact FaithfulSMul.algebraMap_injective _ _

theorem one_mem_inv_pow (k : ℕ) : (1 : D.host.E) ∈ (ddS D)⁻¹ ^ k := by
  have hle : ddS D ≤ 1 := by
    unfold ddS
    exact FractionalIdeal.coeIdeal_le_one
  have h1 : (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≤ (ddS D)⁻¹ := by
    simpa using FractionalIdeal.inv_anti_mono ddS_ne_zero hle
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    simpa using FractionalIdeal.mul_mem_mul ih (h1 (FractionalIdeal.one_mem_one _))

private theorem exists_nat_mul_mem_ringOfIntegers_of_fractionalIdeal {E : Type} [Field E] [NumberField E]
    (J : FractionalIdeal (𝓞 E)⁰ E) :
    ∃ N : ℕ, N ≠ 0 ∧ ∀ y ∈ J, ∃ z : 𝓞 E, (N : E) * y = (z : E) := by
  obtain ⟨b, hb, hint⟩ := J.isFractional
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  refine ⟨Ideal.absNorm (Ideal.span {b}), ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hb0
  · intro y hy
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {b}))
    obtain ⟨z, hz⟩ := hint y hy
    refine ⟨c * z, ?_⟩
    have hz' : (z : E) = (b : E) * y := by
      rw [Algebra.smul_def] at hz
      exact hz
    have hN : ((Ideal.absNorm (Ideal.span {b}) : 𝓞 E) : E) = (Ideal.absNorm (Ideal.span {b}) : E) := by
      push_cast
      rfl
    calc (Ideal.absNorm (Ideal.span {b}) : E) * y
        = ((c * b : 𝓞 E) : E) * y := by rw [hc, hN]
      _ = (c : E) * ((b : E) * y) := by push_cast; ring
      _ = (c : E) * (z : E) := by rw [hz']
      _ = ((c * z : 𝓞 E) : E) := by push_cast; ring

private theorem ιE_ringOfIntegers_mem_O (D : D7) (p : PlF D) (z : 𝓞 D.host.E) :
    (D.s.atP p).ιE (z : D.host.E) ∈ (D.s.atP p).O := by
  rw [(D.s.atP p).O_def]
  have h : IsIntegral ℤ ((D.s.atP p).ιE (z : D.host.E)) :=
    (RingOfIntegers.isIntegral_coe z).map ((D.s.atP p).ιE.toIntAlgHom)
  exact h.tower_top

private theorem finite_setOf_not_isUnit_natCast_atP (D : D7) (N : ℕ) (hN : N ≠ 0) :
    {p : PlF D | ¬ ∃ w ∈ (D.s.atP p).O, (D.s.atP p).ιE (N : D.host.E) * w = 1}.Finite := by
  have hI : Ideal.span {(N : 𝓞 D.host.F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN
  refine (Ideal.finite_factors hI).subset ?_
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp ⊢
  rw [Ideal.dvd_span_singleton]
  by_contra hmem
  apply hp
  have hv : p.valuation D.host.F (N : D.host.F) = 1 := by
    have := (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem
      (K := D.host.F) (v := p)).mpr hmem
    simpa using this
  have hle : (D.s.atP p).ιF ((N : D.host.F)⁻¹) ≤ᵥ (D.s.atP p).ιF 1 := by
    rw [(D.s.atP p).val]
    simp [map_inv₀, hv]
  rw [map_one] at hle
  have hint : (D.s.atP p).ιF ((N : D.host.F)⁻¹) ∈ Valuation.integer (ValuativeRel.valuation (D.s.atP p).Fp) := by
    rw [Valuation.mem_integer_iff, ← (ValuativeRel.valuation _).vle_one_iff]
    exact hle
  have hNE : (N : D.host.E) ≠ 0 := by exact_mod_cast hN
  refine ⟨algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF ((N : D.host.F)⁻¹)), ?_, ?_⟩
  · rw [(D.s.atP p).O_def]
    exact isIntegral_algebraMap (R := Valuation.integer (ValuativeRel.valuation (D.s.atP p).Fp)) (A := (D.s.atP p).Ep) (x := ⟨_, hint⟩)
  · rw [← (D.s.atP p).compat, ← map_mul, map_inv₀, map_natCast, mul_inv_cancel₀ hNE, map_one]

end GlobalTheory.FrameFactorUnit


open GlobalTheory.FrameFactorUnit in
theorem GlobalTheory.FrameFactorUnit.frFac_isUnitO_finite : ∀ (D : D7) (Z : LocDat D) (a : Fin (D.R.rS + 1)),
    {p : PlF D | ¬ Formalism.MainNotions.S.LocNG.IsUnitO (Z.M p) (frFac Z.δ p a)}.Finite := by
  intro D Z a
  have hL := Formalism.L2.SG.Pf.locDiffC_holds D Z
  unfold Formalism.L2.SG.Pf.LocDiffC at hL
  obtain ⟨N, hN0, hN⟩ := exists_nat_mul_mem_ringOfIntegers_of_fractionalIdeal (ddS D ^ (-((D.R.rS : ℤ) - ((a : ℕ) : ℤ))))
  refine (finite_setOf_not_isUnit_natCast_atP D N hN0).subset ?_
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp ⊢
  intro hgood
  apply hp
  obtain ⟨w, hwO, hw1⟩ := hgood
  have hO := Formalism.L2.SG.Pf.LocFacts.lf_hO Z p
  have hc : Formalism.L2.SG.Pf.LocFacts.cP p Z ^ (D.R.rS - a.val) ∈ (D.s.atP p).O := by
    have := Formalism.L2.SG.Pf.LocFacts.lf_mem_pow p Formalism.L2.SG.Pf.dualLoc_holds Z (D.R.rS - a.val) 1
      (one_mem_inv_pow _)
    simpa using this
  have hunit : IsUnit (Formalism.L2.SG.Pf.LocFacts.cP p Z ^ (D.R.rS - a.val)) :=
    (Formalism.L2.SG.Pf.LocFacts.isUnit_localConstant p Z).pow _
  have hinv : frFac Z.δ p a * Formalism.L2.SG.Pf.LocFacts.cP p Z ^ (D.R.rS - a.val) = 1 := by
    unfold frFac
    exact Ring.inverse_mul_cancel _ hunit
  have hmem : frFac Z.δ p a ∈ (Z.M p).L.O := by
    have hs := Submodule.mem_span_singleton_self (R := (Z.M p).L.O) (frFac Z.δ p a)
    rw [← hL p a] at hs
    revert hs
    generalize frFac Z.δ p a = f
    intro hs
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨z, hz⟩ := hN y hy
      rw [hO]
      have hy' : (D.s.atP p).ιE y = w * (D.s.atP p).ιE (z : D.host.E) := by
        rw [← hz, map_mul, ← mul_assoc, mul_comm w, hw1, one_mul]
      rw [hy']
      exact mul_mem hwO (ιE_ringOfIntegers_mem_O D p z)
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul r x _ hx =>
      rw [Subring.smul_def]
      exact mul_mem r.2 hx
  show frFac Z.δ p a ∈ (Z.M p).L.O ∧ ∃ y ∈ (Z.M p).L.O, frFac Z.δ p a * y = 1
  exact ⟨hmem, _, hO ▸ hc, hinv⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LevelCharacterUnipotentPartOfAdmissibilityWitnes
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdmWitChar

open Formalism.L2.SG.Pf.unitaryCongruence Matrix
open scoped TensorProduct

private theorem coprime_absNorm_of_isCoprime_span {K : Type} [Field K] [NumberField K] (J : Ideal (𝓞 K)) (g : ℕ)
    (hJ : J ⊔ Ideal.span {((g : ℕ) : 𝓞 K)} = ⊤) : Nat.Coprime (Ideal.absNorm J) g := by
  have h1mem : (1 : 𝓞 K) ∈ J ⊔ Ideal.span {((g : ℕ) : 𝓞 K)} := by rw [hJ]; exact Submodule.mem_top
  obtain ⟨j, hj, y, hy, hjy⟩ := Submodule.mem_sup.1 h1mem
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  apply Nat.coprime_of_dvd
  intro p hp hpc hpg
  obtain ⟨k, rfl⟩ := hpg
  by_cases hJb : J = ⊥
  · have hj0 : j = 0 := (Submodule.mem_bot _).1 (hJb ▸ hj)
    have h1 : ((p * k : ℕ) : 𝓞 K) * r = 1 := by rw [← hjy, hj0, zero_add, mul_comm]
    have h2 := congrArg (Algebra.norm ℤ) h1
    rw [map_mul, map_one, ← map_natCast (algebraMap ℤ (𝓞 K)), Algebra.norm_algebraMap] at h2
    have hd : 0 < Module.finrank ℤ (𝓞 K) := Module.finrank_pos
    have h3 : ((p : ℤ)) ∣ 1 := by
      rw [← h2]
      apply Dvd.dvd.mul_right
      apply Dvd.dvd.pow _ hd.ne'
      push_cast
      exact dvd_mul_right _ _
    have h4 := Int.eq_one_of_dvd_one (by positivity) h3
    norm_cast at h4
    exact hp.one_lt.ne' h4
  · haveI : Finite (𝓞 K ⧸ J) := J.finiteQuotientOfFreeOfNeBot hJb
    haveI : Fintype (𝓞 K ⧸ J) := Fintype.ofFinite _
    haveI := Fact.mk hp
    have hcard : p ∣ Fintype.card (𝓞 K ⧸ J) := by
      rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
      exact hpc
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card p hcard
    have hpx : ((p : ℕ) : 𝓞 K ⧸ J) * x = 0 := by
      rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
    have hunit : ((p : ℕ) : 𝓞 K ⧸ J) * Ideal.Quotient.mk J ((k : 𝓞 K) * r) = 1 := by
      rw [← map_natCast (Ideal.Quotient.mk J), ← map_mul, ← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq]
      have : ((p : ℕ) : 𝓞 K) * ((k : 𝓞 K) * r) - 1 = -j := by
        rw [← hjy]; push_cast; ring
      rw [this]
      exact J.neg_mem hj
    have hx0 : x = 0 := by
      calc x = (((p : ℕ) : 𝓞 K ⧸ J) * Ideal.Quotient.mk J ((k : 𝓞 K) * r)) * x := by rw [hunit, one_mul]
        _ = Ideal.Quotient.mk J ((k : 𝓞 K) * r) * (((p : ℕ) : 𝓞 K ⧸ J) * x) := by ring
        _ = 0 := by rw [hpx, mul_zero]
    rw [hx0, addOrderOf_zero] at hx
    exact hp.one_lt.ne hx

private theorem hidaSetting_modGAt {D : D7} (X : HidaSetting D) : Formalism.L2.SG.NormCut.ModGAt X := by
  intro g1 Λ hΛ v hv
  have hgg : X.B.g = gS D := X.g_eq
  have hg0 : ((gS D : ℕ) : 𝓞 D.host.E) ≠ 0 := by
    have : (gS D) ≠ 0 := hgg ▸ Formalism.L2.SG.Pf.modulus_g_ne_zero X
    exact_mod_cast this
  let J : Ideal (𝓞 D.host.E) :=
    Submodule.comap (LinearMap.toSpanSingleton (𝓞 D.host.E) (VS D).V v) (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ)
  have hJ : J ⊔ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hgM : ((gS D : ℕ) : 𝓞 D.host.E) ∈ M := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hMb : M ≠ ⊥ := fun h => hg0 (by rw [h] at hgM; exact (Submodule.mem_bot _).1 hgM)
    obtain ⟨s, hs, hsv⟩ := hv ⟨M, hM.isPrime, hMb⟩ hgM
    exact hs (hle (Ideal.mem_sup_left (show s ∈ J from hsv)))
  have hcop : Nat.Coprime (Ideal.absNorm J) (gS D) := coprime_absNorm_of_isCoprime_span J (gS D) hJ
  have hcJ : ((Ideal.absNorm J : ℕ) : 𝓞 D.host.E) ∈ J := Ideal.absNorm_mem J
  have hcv : ((Ideal.absNorm J : ℕ) : 𝓞 D.host.E) • v ∈ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ := hcJ
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hcv
  obtain ⟨w, hw, hwv⟩ := hcv
  have hlin : ∀ (n : ℕ) (y : (VS D).V), X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd (((n : 𝓞 D.host.E)) • y)) =
      (n : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd y)) := by
    intro n y
    have h1 : ((n : 𝓞 D.host.E)) • y = ((n : D.host.E)) • y := by
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    rw [h1, Formalism.L2.SG.NormCut.crd_smul' X, map_natCast, Formalism.L2.SG.NormCut.incl_smul' X, map_natCast,
      Matrix.mulVec_smul]
  refine ⟨Ideal.absNorm J, hgg ▸ hcop, ?_⟩
  rw [← hlin, ← hwv, hlin]
  exact Submodule.subset_span ⟨_, (hΛ w).1 hw, by rw [hgg]⟩

private theorem psiEf_divN_eq {D : D7} (X : HidaSetting D) (y : X.B.I.E) :
    X.psiEf (Formalism.L2.SG.HidaSetting.divN X.B.I X.B.g (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) y)) =
      (Formalism.L2.SG.PairVal.psiInf (gS D) (X.ιE y))⁻¹ := by
  have hg : X.B.g = gS D := X.g_eq
  have hdiv : Formalism.L2.SG.HidaSetting.divN X.B.I X.B.g (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) y) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (algebraMap X.B.I.F X.B.I.E ((X.B.g : X.B.I.F)⁻¹) * y) := by
    unfold Formalism.L2.SG.HidaSetting.divN
    simp [Formalism.UG.inclE, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
  rw [hdiv]
  have h1 := X.psiEf_rat (algebraMap X.B.I.F X.B.I.E ((X.B.g : X.B.I.F)⁻¹) * y)
  have h2 := Formalism.L2.SG.RealObj.PlaceEmbeddingTraceSums.TraceSum_holds D X X.B.g y
  have h3 : Formalism.L2.SG.HidaSetting.psiEinf X.B.I (algebraMap X.B.I.F X.B.I.E ((X.B.g : X.B.I.F)⁻¹) * y) =
      Formalism.L2.SG.PairVal.psiInf X.B.g (X.ιE y) := by
    rw [← h2]
    unfold Formalism.L2.SG.HidaSetting.psiEinf
    refine Finset.prod_congr rfl (fun v _ => ?_)
    congr 1
    have hφ : X.B.I.φ v (algebraMap X.B.I.F X.B.I.E ((X.B.g : X.B.I.F)⁻¹)) = ((X.B.g : ℂ))⁻¹ := by
      rw [map_inv₀, map_natCast, map_inv₀, map_natCast]
    rw [map_mul, hφ]
    simp [star_mul', div_eq_mul_inv]
    ring
  rw [h3] at h1
  rw [← hg]
  exact eq_inv_of_mul_eq_one_left h1

private theorem chiN_eq_of_fmat_mulVec_snoc {D : D7} (X : HidaSetting D) (κ : X.B.I.Gf)
    (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (key : ∀ c, X.B.I.fmat κ *ᵥ Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 c -
        ∑ a, Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((ξ a c : 𝓞 D.host.E) : D.host.E)) •
          Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 a ∈ mL X.B.I X.B.g) :
    chiN X κ = X.psiEf (Formalism.L2.SG.HidaSetting.divN X.B.I X.B.g (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)
      (X.ιE.symm (∑ a : Fin D.R.rS, ((ξ a.castSucc a.succ : 𝓞 D.host.E) : D.host.E))))) := by
  have hg : X.B.g ≠ 0 := Formalism.L2.SG.Pf.modulus_g_ne_zero X
  obtain ⟨hfe, hfz, -, -⟩ := Formalism.L2.SG.Pf.reference_frame_congruences X
  have hf0 : ∀ a, X.f0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).2
  have hint : ∀ x : 𝓞 D.host.E,
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm (x : D.host.E)) ∈ IntAf X.B.I.F X.B.I.E :=
    fun x => Formalism.L2.SG.NormCut.inclE_int X x
  have hZ : ZMod' X.B.I X.B.g ((∑ a, hA X.B.I (X.f0 a) (X.B.I.fmat κ *ᵥ nxt X.e0 X.z0 a)) -
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)
        (X.ιE.symm (∑ a : Fin D.R.rS, ((ξ a.castSucc a.succ : 𝓞 D.host.E) : D.host.E))) - 0) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [sub_zero, map_sum, map_sum, ← Finset.sum_sub_distrib]
    refine Z_sum X.B.I X.B.g _ _ (fun a _ => ?_)
    have hnxt : nxt X.e0 X.z0 a = Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 a.succ := by
      unfold nxt
      split_ifs with h
      · have hs : (a.succ : Fin (D.R.rS + 1)) = Fin.castSucc ⟨a.1 + 1, h⟩ :=
          Fin.ext (by simp only [Fin.val_succ, Fin.val_castSucc])
        rw [hs, Fin.snoc_castSucc]
      · have hs : (a.succ : Fin (D.R.rS + 1)) = Fin.last _ :=
          Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega)
        rw [hs, Fin.snoc_last]
    rw [hnxt]
    have hw : ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) (X.B.I.fmat κ *ᵥ Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 a.succ -
        ∑ c, Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((ξ c a.succ : 𝓞 D.host.E) : D.host.E)) •
          Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 c)) :=
      mL_Qs X.B.I X.B.g (hf0 a) (key a.succ)
    rw [hA_sub_right] at hw
    have hsum : hA X.B.I (X.f0 a) (∑ c, Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((ξ c a.succ : 𝓞 D.host.E) : D.host.E)) •
          Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 c) =
        ∑ c, Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((ξ c a.succ : 𝓞 D.host.E) : D.host.E)) *
          hA X.B.I (X.f0 a) (Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 c) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hL_apply, map_sum]
      simp [hL_apply]
    rw [hsum] at hw
    have hrest : ZMod' X.B.I X.B.g ((∑ c, Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((ξ c a.succ : 𝓞 D.host.E) : D.host.E)) *
          hA X.B.I (X.f0 a) (Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 c)) -
        Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((ξ a.castSucc a.succ : 𝓞 D.host.E) : D.host.E))) := by
      have he : (∑ c, Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((ξ c a.succ : 𝓞 D.host.E) : D.host.E)) *
          hA X.B.I (X.f0 a) (Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 c)) -
        Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((ξ a.castSucc a.succ : 𝓞 D.host.E) : D.host.E)) =
          ∑ c, Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((ξ c a.succ : 𝓞 D.host.E) : D.host.E)) *
            (hA X.B.I (X.f0 a) (Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 c) - if c = a.castSucc then 1 else 0) := by
        simp [mul_sub, Finset.sum_sub_distrib]
      rw [he]
      refine Z_sum X.B.I X.B.g _ _ (fun c _ => Z_smul X.B.I X.B.g (hint _) ?_)
      refine Fin.lastCases ?_ (fun b => ?_) c
      · have hne : (Fin.last D.R.rS) ≠ a.castSucc := (Fin.castSucc_lt_last a).ne'
        simpa [hne] using hfz a
      · by_cases hb : b = a
        · subst hb
          have h1 := (X.gramIntegral b b).2.2
          simp only at h1
          have h2 := Z_sig X.B.I X.B.g h1
          simpa [hA_symm X.B.I (X.e0 b) (X.f0 b), map_sub, map_one] using h2
        · have hne : b.castSucc ≠ a.castSucc := fun h => hb (Fin.castSucc_injective _ h)
          simpa [hne] using hfe a b (Ne.symm hb)
    have := Z_add X.B.I X.B.g hw hrest
    convert this using 1
    ring
  have hmul := psi_mul_of_Z X.B.I X.B.g X.psiEf_add X.psiEf_int hg hZ
  unfold chiN
  rw [hmul, psi_Z X.B.I X.B.g X.psiEf_add X.psiEf_int hg (Z_zero X.B.I X.B.g), mul_one]

theorem chiN_kOf_eq_inv_psiInf_sgUp : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → ∀ (t : TauC Y u u') (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)), AdmWit t.lam (gS D) (lf D (X.Fu u)) t.frame ξ → chiN X (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf) ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) t.pt) = (Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp (ξ.map (algebraMap (𝓞 D.host.E) D.host.E))))⁻¹ := by
  intro D X Y u u' hS t ξ hξ
  have hK := Formalism.L2.SG.NormCut.termK_car (Y.cs u) (Y.cs u') t.mem t.mem' t.rep
  have hRL : Formalism.L2.SG.TermOp.RatLink X t.pt t.lin := t.rep.2.1
  have hiso : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hM : Formalism.L2.SG.NormCut.ModGAt X := hidaSetting_modGAt X
  have hξm : ∀ c, ModG (VS D) t.lam (gS D) (t.lin (frame (lf D (X.Fu u')) c) - frameAct (frame (lf D (X.Fu u))) ξ c) := by
    intro c
    have h3 := hξ.2.2 c
    have h4 := Formalism.L2.SG.NormCut.frame_mapLF hiso (lf D (X.Fu u')) c
    unfold GTerm.frame at h3
    exact h4 ▸ h3
  have key := Formalism.L2.SG.NormCut.key_gen (Y.cs u) (Y.cs u') (Formalism.L2.SG.Full.Full.frameTie (X := X) u u') hM t.mem t.pt t.lin hRL ξ hξm hK
  rw [chiN_eq_of_fmat_mulVec_snoc X _ ξ key, psiEf_divN_eq, RingEquiv.apply_symm_apply]
  congr 2
  rw [GlobalTheory.RatIsomPoint.sgUp_eq]
  simp [Matrix.map_apply]

end GlobalTheory.AdmWitChar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalFlagScaledFrameEqBaseChangeFlag
section
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlagBaseChange

theorem isUnit_frFac {D : D7} {T : D.host.E} (G : LFlag (D.sp.Y 0) D.R.rS T) (Z : LocDat D) (p : PlF D)
    (A : LocNG.FrameD (locH Z p) D.R.rS) (hA : A.f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a))
    (b : Fin D.R.rS) : IsUnit (frFac Z.δ p b.castSucc) := by
  rcases A with ⟨f, es, T0, h1, h2, h3, h4, h5⟩
  dsimp only at hA
  subst hA
  have hb := h4 b b
  dsimp only at hb
  rw [if_pos rfl, (locH Z p).h_smul_left] at hb
  exact ⟨⟨_, _, hb, (mul_comm _ _).trans hb⟩, rfl⟩

theorem span_bcP_Xa_eq_Fj : ∀ (D : D7) (T : D.host.E) (G : LFlag (D.sp.Y 0) D.R.rS T) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ (p : PlF D) (j : ℕ), Submodule.span (D.s.atP p).Ep (baseChange₂ D p '' (G.fl.Xa j : Set (VS D).V)) = (A p).Fj j := by
  intro D T G Z A hA p j
  unfold LocNG.FrameD.Fj LocNG.FrameD.e FlagG.Xa
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, hi, rfl⟩ := hy
      obtain ⟨u, hu⟩ := GlobalTheory.FlagBaseChange.isUnit_frFac G Z p (A p) (hA p) i
      have hmem : (A p).f i.castSucc ∈
          Submodule.span (D.s.atP p).Ep ((fun a : Fin D.R.rS => (A p).f a.castSucc) '' {a : Fin D.R.rS | (a : ℕ) < j}) :=
        Submodule.subset_span ⟨i, hi, rfl⟩
      have hf : (A p).f i.castSucc = frFac Z.δ p i.castSucc • baseChange₂ D p (G.fl.e i) := by
        rw [hA p]
        dsimp only
        rw [Formalism.L2.SG.Pf.frame_castSucc_sat]
      rw [hf, ← hu] at hmem
      have hv := Submodule.smul_mem _ (↑u⁻¹ : (D.s.atP p).Ep) hmem
      rw [smul_smul, Units.inv_mul, one_smul] at hv
      exact hv
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [baseChange_smul₂]
      exact Submodule.smul_mem _ _ hx
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    dsimp only
    rw [hA p]
    dsimp only
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨G.fl.e i, Submodule.subset_span ⟨i, hi, rfl⟩, ?_⟩
    rw [Formalism.L2.SG.Pf.frame_castSucc_sat]

end GlobalTheory.FlagBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalModelsUnsplitAlmostAll
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocSplitFinite

theorem finite_resChar_eq (F : Type) [Field F] [NumberField F] (l : ℕ) (hl : l ≠ 0) :
    {p : IsDedekindDomain.HeightOneSpectrum (𝓞 F) | Formalism.MainNotions.S.Loc.resChar p = l}.Finite := by
  have hx : ((l : 𝓞 F)) ≠ 0 := Nat.cast_ne_zero.2 hl
  have hI : Ideal.span {((l : 𝓞 F))} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hx
  refine (Ideal.finite_factors hI).subset ?_
  intro p hp
  simp only [Set.mem_setOf_eq] at hp ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  unfold Formalism.MainNotions.S.Loc.resChar at hp
  rw [← hp]
  exact ringChar.Nat.cast_ringChar

theorem split_finite : ∀ (D : D7) (Z : LocDat D), {p : PlF D | (Z.M p).split ≠ none}.Finite := by
  intro D Z
  have h0 := finite_resChar_eq D.host.F (D.host.g 0) (D.host.g_prime 0).ne_zero
  have h1 := finite_resChar_eq D.host.F (D.host.g 1) (D.host.g_prime 1).ne_zero
  refine (h0.union h1).subset ?_
  intro p hp
  simp only [Set.mem_setOf_eq] at hp
  have hs : (D.s.atP p).split.isSome := by
    have ha := (Z.agree p).2.2.2.2.2
    revert ha
    cases h : (Z.M p).split with
    | none => exact absurd h hp
    | some g =>
      cases h' : (D.s.atP p).split with
      | none => intro ha; exact ha.elim
      | some sg => intro _; rfl
  have hm := (D.s_split p).1 hs
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hm | hm
  · exact Or.inl hm
  · exact Or.inr hm

end GlobalTheory.LocSplitFinite
end

