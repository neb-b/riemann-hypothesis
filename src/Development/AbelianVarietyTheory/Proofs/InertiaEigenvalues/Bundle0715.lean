module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0219
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0695
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0701
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0665
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0383
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0986
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0961
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0853
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0290
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPlaceOverMoveValConjPl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCsdOfCharOfRes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0020
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolySmulOfProd
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0170
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0145
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0704
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0522

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertOfUnramifiedIsometricInvolution
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.InertOfUnramInv

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem exists_int_approx (w : HeightOneSpectrum (𝓞 L)) (x : w.adicCompletion L) (hx : Valued.v x ≤ 1) :
    ∃ a : 𝓞 L, Valued.v (x - algebraMap L (w.adicCompletion L) (a : L)) < 1 := by
  have hval : ∀ k : L, Valued.v (algebraMap L (w.adicCompletion L) k) = w.valuation L k :=
    fun k => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := w) k
  have hU : IsOpen {z : w.adicCompletion L | Valued.v (z - x) < 1} := by
    have h := (Valued.isOpen_ball (w.adicCompletion L) 1).preimage (continuous_sub_right x)
    simpa [Valuation.restrict_lt_one_iff] using h
  obtain ⟨y, hy⟩ :=
    (HeightOneSpectrum.denseRange_algebraMap (K := L) (v := w)).exists_mem_open hU ⟨x, by simp⟩
  have hy' : Valued.v (algebraMap L (w.adicCompletion L) y - x) < 1 := hy
  have hyv : w.valuation L y ≤ 1 := by
    rw [← hval]
    calc Valued.v (algebraMap L (w.adicCompletion L) y)
        = Valued.v ((algebraMap L (w.adicCompletion L) y - x) + x) := by rw [sub_add_cancel]
      _ ≤ max (Valued.v (algebraMap L (w.adicCompletion L) y - x)) (Valued.v x) := Valuation.map_add _ _ _
      _ ≤ 1 := max_le hy'.le hx
  obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer (K := L) (v := w) hyv 1
  refine ⟨a, ?_⟩
  have e : x - algebraMap L (w.adicCompletion L) (a : L) =
      -(algebraMap L (w.adicCompletion L) y - x) + -(algebraMap L (w.adicCompletion L) (a : L) -
        algebraMap L (w.adicCompletion L) y) := by ring
  rw [e]
  refine Valuation.map_add_lt _ (by rw [Valuation.map_neg]; exact hy') ?_
  rw [Valuation.map_neg, ← map_sub, hval]
  simpa using ha

theorem inert_of_isUnramInv : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L) (q : ℕ), (∀ x : L, s (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → Formalism.UG.IsUnramInv ϖ s q → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal ∧ ¬ IsSplitAt w ∧ q = Formalism.UG.qV (maximalRealSubfield L) v := by
  intro L _ _ _ v w hvw s ϖ q hsc hU
  unfold Formalism.UG.IsUnramInv at hU
  obtain ⟨-, hsv, -, -, ⟨x, hxO, hx1⟩, -, hcard⟩ := hU
  have hvw' : w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L)) = v.asIdeal := hvw
  have hlo : w.asIdeal.LiesOver v.asIdeal := ⟨hvw'.symm⟩
  let φ : 𝓞 L →+* w.adicCompletion L := (algebraMap L (w.adicCompletion L)).comp (algebraMap (𝓞 L) L)
  have hφ : ∀ b : 𝓞 L, Valued.v (φ b) = w.valuation L (algebraMap (𝓞 L) L b) :=
    fun b => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := w) (algebraMap (𝓞 L) L b)
  have hval : ∀ b : 𝓞 L, Valued.v (φ b) < 1 ↔ b ∈ w.asIdeal := by
    intro b
    rw [hφ]
    exact HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) w b
  have hfix : ∀ a : 𝓞 (maximalRealSubfield L),
      s (φ (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a)) = φ (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a) := by
    intro a
    show s (algebraMap L _ _) = algebraMap L _ _
    rw [hsc]
    congr 1
    exact (IsCMField.complexConj L).commutes (a : maximalRealSubfield L)
  have hxv : Valued.v x ≤ 1 := hxO

  have hf1 : w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield L)) ≠ 1 := by
    intro hf
    have hn := Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal
    rw [hf, pow_one, Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
      Submodule.cardQuot_apply] at hn
    have hle : v.asIdeal ≤ w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L)) := hvw'.ge
    have hinj : Function.Injective (Ideal.quotientMap w.asIdeal _ hle) :=
      Ideal.quotientMap_injective' hvw'.le
    have hbij := (Nat.bijective_iff_injective_and_card _).mpr ⟨hinj, hn⟩
    obtain ⟨b, hb⟩ := exists_int_approx w x hxv
    obtain ⟨a, ha⟩ := hbij.2 (Ideal.Quotient.mk w.asIdeal b)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at ha
    have hsz := hfix a
    set z := φ (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a) with hz
    have h1 : Valued.v (x - z) < 1 := by
      have e : x - z = (x - φ b) + -(φ (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a - b)) := by
        rw [map_sub]; ring
      rw [e]
      refine Valuation.map_add_lt _ hb ?_
      rw [Valuation.map_neg, hval]
      exact ha
    have h2 : s x - x = s (x - z) + -(x - z) := by
      rw [map_sub, hsz]; ring
    have h3 : Valued.v (s x - x) < 1 := by
      rw [h2]
      refine Valuation.map_add_lt _ ?_ ?_
      · rw [hsv]; exact h1
      · rw [Valuation.map_neg]; exact h1
    exact absurd hx1 (ne_of_lt h3)
  have hfpos := Ideal.inertiaDeg_pos w.asIdeal (𝓞 (maximalRealSubfield L))
  have hepos := Ideal.ramificationIdx_pos (R := 𝓞 (maximalRealSubfield L)) w.asIdeal

  have hG2 : Nat.card (L ≃ₐ[maximalRealSubfield L] L) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]
  have hsum := Ideal.sum_ramification_inertia_eq_card v.asIdeal (𝓞 L)
    (G := L ≃ₐ[maximalRealSubfield L] L)
  let F : v.asIdeal.primesOver (𝓞 L) → ℕ := fun P =>
    P.1.ramificationIdx (𝓞 (maximalRealSubfield L)) * P.1.inertiaDeg (𝓞 (maximalRealSubfield L))
  have hsum' : ∑ P, F P = 2 := by
    rw [← hG2, ← hsum]
  let W : v.asIdeal.primesOver (𝓞 L) := ⟨w.asIdeal, w.isPrime, hlo⟩
  have hW : F W ≤ 2 := by
    rw [← hsum']
    exact Finset.single_le_sum (f := F) (fun _ _ => Nat.zero_le _) (Finset.mem_univ W)
  have hW' : w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield L)) *
      w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield L)) ≤ 2 := hW
  have hf2 : w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield L)) = 2 := by
    have : 2 ≤ w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield L)) := by omega
    nlinarith
  have he1 : w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield L)) = 1 := by
    rw [hf2] at hW'
    omega
  refine ⟨?_, ?_, ?_⟩
  · have : (w.asIdeal.under (𝓞 (maximalRealSubfield L))).IsMaximal := by
      rw [← hlo.over]
      exact v.isMaximal
    exact Ideal.ramificationIdx_eq_one_iff.mp he1
  · rintro ⟨u, hne, hu⟩
    have hlu : u.asIdeal.LiesOver v.asIdeal := ⟨by
      rw [hlo.over]
      exact (congrArg HeightOneSpectrum.asIdeal hu).symm⟩
    let U : v.asIdeal.primesOver (𝓞 L) := ⟨u.asIdeal, u.isPrime, hlu⟩
    have hWU : W ≠ U := fun h => hne (HeightOneSpectrum.ext (congrArg Subtype.val h).symm)
    have h2 : F W + F U ≤ 2 := by
      rw [← hsum', ← Finset.sum_pair hWU]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have hu1 := Ideal.inertiaDeg_pos u.asIdeal (𝓞 (maximalRealSubfield L))
    have hu2 := Ideal.ramificationIdx_pos (R := 𝓞 (maximalRealSubfield L)) u.asIdeal
    have hFU : 1 ≤ F U := Nat.mul_pos hu2 hu1
    have hFW : F W = 2 := by
      show w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield L)) *
        w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield L)) = 2
      rw [he1, hf2]
    omega
  ·
    let O := (Valued.v : Valuation (w.adicCompletion L) (WithZero (Multiplicative ℤ))).valuationSubring
    have hmemO : ∀ b : 𝓞 L, φ b ∈ O := by
      intro b
      show Valued.v (φ b) ≤ 1
      rw [hφ]
      exact HeightOneSpectrum.valuation_le_one (K := L) w b
    let g : 𝓞 L →+* O := φ.codRestrict O hmemO
    have hmax : ∀ y : O, y ∈ IsLocalRing.maximalIdeal O ↔ Valued.v (y : w.adicCompletion L) < 1 := by
      intro y
      have hle : Valued.v (y : w.adicCompletion L) ≤ 1 := y.2
      have hu : IsUnit y ↔ Valued.v (y : w.adicCompletion L) = 1 :=
        HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one (K := L) (v := w) (a := y)
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hu]
      exact ⟨fun h => lt_of_le_of_ne hle h, fun h => ne_of_lt h⟩
    let G := (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)).comp g
    have hGs : Function.Surjective G := by
      intro Y
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective Y
      obtain ⟨b, hb⟩ := exists_int_approx w (y : w.adicCompletion L) y.2
      refine ⟨b, ?_⟩
      show Ideal.Quotient.mk _ (g b) = Ideal.Quotient.mk _ y
      rw [Ideal.Quotient.eq, hmax]
      show Valued.v (φ b - (y : w.adicCompletion L)) < 1
      rw [← Valuation.map_neg, neg_sub]
      exact hb
    have hker : RingHom.ker G = w.asIdeal := by
      ext b
      rw [RingHom.mem_ker]
      show Ideal.Quotient.mk _ (g b) = 0 ↔ _
      rw [Ideal.Quotient.eq_zero_iff_mem, hmax]
      exact hval b
    have hc := Nat.card_congr (RingHom.quotientKerEquivOfSurjective hGs).toEquiv
    rw [hker] at hc
    have hcard' : Nat.card (O ⧸ IsLocalRing.maximalIdeal O) = q ^ 2 := hcard
    have hn := Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal
    rw [hf2, Ideal.absNorm_apply w.asIdeal, Submodule.cardQuot_apply, hc, hcard'] at hn
    show q = Ideal.absNorm v.asIdeal
    exact Nat.pow_left_injective (n := 2) (by norm_num) hn.symm

end GlobalTheory.InertOfUnramInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotCrysAtOfMono0
section
noncomputable section

namespace GlobalTheory.TripleLocal

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.HeightCounting
open GlobalTheory.RowTie (WDTie)
open Matrix (GeneralLinearGroup)

section Twist

variable {Γ k : Type} [Group Γ] [Field k] {a : ℕ}

theorem coe_scalar (u : kˣ) : ((GeneralLinearGroup.scalar (Fin a) u : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
    (u : k) • (1 : Matrix (Fin a) (Fin a) k) := by
  ext i j
  by_cases h : i = j <;> simp [GeneralLinearGroup.scalar, Matrix.diagonal, Matrix.one_apply, h]

def twistBy (c : Γ →* kˣ) (r : Γ →* GL (Fin a) k) : Γ →* GL (Fin a) k where
  toFun g := GeneralLinearGroup.scalar (Fin a) (c g) * r g
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, map_mul, map_mul]
    have e : GeneralLinearGroup.scalar (Fin a) (c h) * r g = r g * GeneralLinearGroup.scalar (Fin a) (c h) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, coe_scalar, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    simp only [mul_assoc]
    rw [← mul_assoc (GeneralLinearGroup.scalar (Fin a) (c h)), e, mul_assoc]

theorem coe_twistBy (c : Γ →* kˣ) (r : Γ →* GL (Fin a) k) (g : Γ) :
    (twistBy c r g : Matrix (Fin a) (Fin a) k) = (c g : k) • (r g : Matrix (Fin a) (Fin a) k) := by
  change ((GeneralLinearGroup.scalar (Fin a) (c g) * r g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) = _
  rw [Units.val_mul, coe_scalar, Matrix.smul_mul, Matrix.one_mul]

end Twist

section G
variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}

theorem isPolarized_twist {π : CuspSub E a} (hc : π.IsCsd) {ν : HChar E} {s : ℝ} (hν : ν.IsAbsPow s) :
    ∃ ψ, IsPolarized (π.twist ν) ψ := by
  obtain ⟨ψ, h1, h2⟩ := GlobalTheory.PolChar.exists_compNorm_eq hν
  refine ⟨_, IsConjDualBy.isPolarized (m := 0) (χ := ψ) ?_ ?_⟩
  · rw [h1]; exact _root_.GlobalTheory.ConjDualTwist.isConjDualBy_twist_thetaChar hc ν
  · simpa using h2

theorem expo_mul (χ χ' : HChar E) (τ : E →+* ℂ) : expo (χ * χ') τ = expo χ τ + expo χ' τ := by
  have h := (CG.hasInfChar_ofChar χ τ).twist χ'
  rw [CG.twist_ofChar, Multiset.map_singleton] at h
  have := h.infChar_eq
  rw [CG.infChar_ofChar] at this
  simpa using this

theorem expo_inv (χ : HChar E) (τ : E →+* ℂ) : expo χ⁻¹ τ = -expo χ τ := by
  have := expo_mul χ χ⁻¹ τ
  rw [mul_inv_cancel, CG.expo_one] at this
  linear_combination -this

theorem isSSRep_twistBy {Γ K : Type} [Group Γ] [Field K] {n : ℕ} (c : Γ →* Kˣ) {ρ : Γ →* GL (Fin n) K} (hs : IsSSRep ρ) :
    IsSSRep (twistBy c ρ) := by
  have key : ∀ W, IsInv (twistBy c ρ) W ↔ IsInv ρ W := fun W => forall_congr' fun g => forall₂_congr fun v _ => by
    rw [coe_twistBy, Matrix.smul_mulVec, W.smul_mem_iff (c g).ne_zero]
  exact fun W hW => (hs W ((key W).1 hW)).imp fun W' h' => ⟨(key W').2 h'.1, h'.2⟩

theorem conj_of_frob (hD : ∀ S : Set (HeightOneSpectrum (𝓞 E)), S.Finite → Dense {g : G E Ω | ∃ w ∉ S, ∃ B : ValuationSubring Ω,
      IsPlaceOver (F := E) B w ∧ IsFrob (F := E) B (normV w) g})
    {r r' : G E Ω →* GL (Fin a) (Qbar l)} (hc : Continuous fun g => (r g : Matrix (Fin a) (Fin a) (Qbar l)))
    (hc' : Continuous fun g => (r' g : Matrix (Fin a) (Fin a) (Qbar l))) (hs : IsSSRep r) (hs' : IsSSRep r')
    (h : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ (B : ValuationSubring Ω) (g : G E Ω),
      IsPlaceOver (F := E) B w → IsFrob (F := E) B (normV w) g →
      (r g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly = (r' g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly) :
    ∃ A : GL (Fin a) (Qbar l), ∀ g, r' g = A * r g * A⁻¹ := by
  have htr : ∀ g, ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace =
      ((r' g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace := by
    intro g
    refine congrFun (Continuous.ext_on (hD _ (Filter.eventually_cofinite.1 h))
      (hc.matrix_trace) (hc'.matrix_trace) ?_) g
    rintro σ ⟨w, hw, B, hB, hσ⟩
    have e := not_not.1 hw B σ hB hσ
    show Matrix.trace _ = Matrix.trace _
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      simp [Matrix.trace]
    · haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
      rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, e]
  exact GlobalTheory.TraceConj.conj_of_trace_eq _ _ a r r' hs hs' htr

theorem potCrys_twistBy {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (c : ↥Gw →* (Om l)ˣ) (r : ↥Gw →* GL (Fin a) (Om l))
    (hr : IsPotCrysAt P Bw r) (hc : IsCrysAt P Bw ((GeneralLinearGroup.scalar (Fin 1)).comp c)) :
    IsPotCrysAt P Bw (twistBy c r) := by
  obtain ⟨L₁, r₁, m₁, hp₁⟩ := hr
  obtain ⟨L₂, c₂, m₂, hc₂⟩ := hc
  have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have m₁' := m₁.enlarge l₁
  have m₂' := m₂.enlarge l₂
  obtain ⟨K', hK, hcr⟩ := (local_ext P Bw l₁ r₁).2.2.1.2 hp₁
  have hq := (local_ext P Bw l₂ c₂).1.2 hc₂
  set L := supExt L₁ L₂ with hL
  set r₁' := Formalism.MainNotions.N.mapRep (IntermediateField.inclusion l₁).toRingHom r₁ with hr₁'
  set c₂' := Formalism.MainNotions.N.mapRep (IntermediateField.inclusion l₂).toRingHom c₂ with hc₂'
  let d : ↥Gw →* (↥L.1)ˣ := Matrix.GeneralLinearGroup.det.comp c₂'
  have hd : ∀ g, ((c₂' g : GL (Fin 1) ↥L.1) : Matrix (Fin 1) (Fin 1) ↥L.1) 0 0 = (d g : ↥L.1) := fun g => by
    change _ = Matrix.det _
    rw [Matrix.det_fin_one]
  have hcd : ∀ g, ((d g : ↥L.1) : Om l) = (c g : Om l) := fun g => by
    have e := congrArg (fun f : ↥Gw →* GL (Fin 1) (Om l) => ((f g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) 0 0) m₂'.2
    rw [← hd]
    refine e.trans ?_
    rw [MonoidHom.comp_apply, coe_scalar]
    simp
  have hM : IsModel Bw (twistBy c r) L (twistBy d r₁') := by
    refine ⟨m₁'.1, ?_⟩
    ext g i j
    have e : algebraMap ↥L.1 (Om l) (((r₁' g : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) i j) =
        (r g : Matrix (Fin a) (Fin a) (Om l)) i j :=
      congrArg (fun f : ↥Gw →* GL (Fin a) (Om l) => ((f g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j) m₁'.2
    change algebraMap ↥L.1 (Om l) (((twistBy d r₁' g : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) i j) =
      ((twistBy c r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j
    rw [coe_twistBy, coe_twistBy, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, e]
    exact congrArg₂ (· * ·) (hcd g) rfl
  refine ⟨L, _, hM, K', hK, ?_⟩
  let θ : ↥(GK K') →* (↥L.1)ˣ := (d.comp Bw.e.symm.toMonoidHom).comp (Subgroup.inclusion (GK_le hK))
  refine (GlobalTheory.TopSteps.CrysRules.isCrys_iff T K' L _ _ θ (fun g x => ?_) ?_).1 hcr
  · change Bw.repE L (twistBy d r₁') _ x = _ • Bw.repE L r₁' _ x
    rw [GlobalTheory.ConjLocal.repE_apply, GlobalTheory.ConjLocal.repE_apply, coe_twistBy, Matrix.smul_mulVec]
    rfl
  · have h1 := GlobalTheory.Per.TiedRestrict.isCrys_restrict hK (Bw.repE L c₂') T hq
    refine GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv (P.PD K') (LinearEquiv.funUnique (Fin 1) ↥L.1 ↥L.1) (fun g x => ?_) h1
    change (Bw.repE L c₂' _ x) 0 = ((θ g : (↥L.1)ˣ) : ↥L.1) * x 0
    rw [GlobalTheory.ConjLocal.repE_apply]
    simp only [Matrix.mulVec, dotProduct, Finset.univ_unique, Finset.sum_singleton]
    exact congrArg (· * x 0) (hd (Bw.e.symm (Subgroup.inclusion (GK_le hK) g)))

end G

theorem exists_halfChar (D : D7) : haveI := host_isCMField D.host; ∃ ξ : HChar D.host.E, (∀ v, ξ.UnrAt v) ∧
    (CG.ofChar ξ).IsCsd ∧ (CG.ofChar ξ⁻¹).IsCsd ∧ ∀ τ, ∃ n : ℤ, expo ξ τ = n + 1 / 2 := by
  have := host_isCMField D.host
  obtain ⟨ξ, h⟩ := GlobalTheory.Mem.EtaT.etaT_exists D.R D.host
  have hneg : (-1 : ℂˣ)⁻¹ = -1 := inv_eq_of_mul_eq_one_left (by simp)
  refine ⟨ξ, h.unr, isCsd_ofChar_of_res _ _ (Or.inr h.res), isCsd_ofChar_of_res _ _ (Or.inr ⟨fun v k => ?_, fun w k => ?_⟩), fun τ => ?_⟩
  · have e1 := h.res.1 v k
    have e2 : (ξ⁻¹.resFin v) k = ((ξ.resFin v) k)⁻¹ := by
      simp only [HChar.resFin, MonoidHom.finsetProd_apply, ← Finset.prod_inv_distrib]
      rfl
    rw [e2, e1]
    unfold etaFin
    split_ifs
    · rw [← inv_zpow, hneg]
    · exact inv_one
  · have e1 := h.res.2 w k
    have e2 : (ξ⁻¹.resInf w) k = ((ξ.resInf w) k)⁻¹ := by
      simp only [HChar.resInf, MonoidHom.finsetProd_apply, ← Finset.prod_inv_distrib]
      rfl
    rw [e2, e1]
    unfold etaInf
    split_ifs
    · exact hneg
    · exact inv_one
  · have hI : Function.Injective fun i => InfinitePlace.mk (embPsi D.host i) := fun i j e => by
      rcases InfinitePlace.mk_eq_iff.1 e with e | e
      · exact GlobalTheory.HalfIntChars.embPsi_inj D.host e
      · exact (GlobalTheory.HalfIntChars.embPsi_ne_conj D.host j i (e.symm.trans (RingHom.ext fun x => rfl))).elim
    obtain ⟨ρ, b, rfl⟩ := GlobalTheory.JumpDictionaryFoundation.exists_embOver D τ
    have h3 := (_root_.GlobalTheory.CuspRep.InfType.expo_of_infType _ ξ).2.2 _ _ _ hI h.inf (D.eTau ρ)
    cases b
    · exact ⟨0, by rw [show GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D ρ false = embPsi D.host (D.eTau ρ) from rfl, h3.1]; simp⟩
    · refine ⟨-1, ?_⟩
      rw [show GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D ρ true = ComplexEmbedding.conjugate (embPsi D.host (D.eTau ρ)) from
        RingHom.ext (GlobalTheory.JumpDictionaryFoundation.embOver_true_apply D ρ), h3.2]
      norm_num

end GlobalTheory.TripleLocal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.L2OHeisOEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.HeisTranslateBound

open GlobalTheory.Size GlobalTheory.OrientedHeis

theorem l2O_heisO_eq {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hμ : IsCovolOne (ratL T S) μ 𝓕) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) (u : WO S T) :
    l2O μ 𝓕 (heisO ψ S T u g) = l2O μ 𝓕 g := by
  have hg' := GlobalTheory.Unf.MatCoef.theta_heisO_any hψ hθ hg u
  have e := ipO_heisO hψ hμ.1 hμ.2.1 hg hg u
  rw [ipO_self, ipO_self, sqNormIntegralFundamentalDomain_eq_l2Norm_sq μ 𝓕 hg'.cont, sqNormIntegralFundamentalDomain_eq_l2Norm_sq μ 𝓕 hg.cont, Complex.ofReal_inj,
    pow_left_inj₀ ENNReal.toReal_nonneg ENNReal.toReal_nonneg two_ne_zero] at e
  exact (ENNReal.toReal_eq_toReal_iff' (l2NormOnFundamentalDomain_thetaFunction_ne_top hψ hμ.1 hμ.2.1 hg') (l2NormOnFundamentalDomain_thetaFunction_ne_top hψ hμ.1 hμ.2.1 hg)).1 e

theorem sobO_heisO_eq {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hμ : IsCovolOne (ratL T S) μ 𝓕) {h : WO S T → ℂ} (hh : IsThetaFunO ψ S T h) {u : WO S T}
    (hu : u.map (infPart D) = 0) (d : ℕ) :
    sobO ψ θ μ 𝓕 d (heisO ψ S T u h) = sobO ψ θ μ 𝓕 d h := by
  have := wordSum_eq_mul (A := heisDer ψ θ) (p := l2O μ 𝓕) (d := d) (x := h) (y := heisO ψ S T u h) (c := 1)
    fun l => by
      have e : wordAct (heisDer ψ θ) l (heisO ψ S T u h) = heisO ψ S T u (wordAct (heisDer ψ θ) l h) :=
        wordAct_rel (R := fun g g' => g = heisO ψ S T u g') l
          (fun a _ _ _ e => e ▸ GlobalTheory.FinTranslate.dRho_heisO hθ hu a.1 _ _) rfl
      rw [e, one_mul, l2O_heisO_eq hψ hθ hμ (theta_word hψ hθ l hh) u]
  rw [one_mul] at this
  exact this

end GlobalTheory.HeisTranslateBound


open GlobalTheory.Size GlobalTheory.HeisTranslateBound GlobalTheory.OrientedHeis in
theorem GlobalTheory.HeisTranslateBound.sobO_finsupp_sum_le : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ c : WO S T →₀ ℂ, (∀ u ∈ c.support, u.map (infPart D) = 0) → ∀ h : WO S T → ℂ, IsThetaFunO ψ S T h → ∀ d : ℕ, GlobalTheory.Size.sobO ψ θ μ 𝓕 d (c.sum fun u z => z • heisO ψ S T u h) ≤ (∑ u ∈ c.support, ‖c u‖ₑ) * GlobalTheory.Size.sobO ψ θ μ 𝓕 d h := by
  intro D ψ θ S T hψ hθ μ 𝓕 hμ c hc h hh d
  have ht : ∀ u, IsThetaFunO ψ S T (c u • heisO ψ S T u h) := fun u =>
    theta_smul (c u) (GlobalTheory.Unf.MatCoef.theta_heisO_any hψ hθ hh u)
  refine (sobO_sum_le hψ hθ c.support (g := fun u => c u • heisO ψ S T u h) (fun u _ => ht u) d).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun u hu => ?_
  rw [sobO_smul, sobO_heisO_eq hψ hθ hμ hh (hc u hu)]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedTorsionClassTheoremGoodCase
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.TheoremTB

theorem tb_assembled : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
    admitted D HW F → Conclusion5 D → Conclusion4 D HW F := by
  intro D HW F hA h5 l _ K s LL h
  exact ⟨GlobalTheory.T.crystalline_extension_class_bound D HW F hA l K s LL h, GlobalTheory.T.weight_good_reduction_at_prime D HW F hA h5 l K s LL h⟩

end GlobalTheory.TheoremTB
end

