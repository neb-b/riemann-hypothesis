module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0735
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0715
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NatCastMemPlaceAt
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0736
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0605
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0737
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0720
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0739
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLocalMatrixDivisionPointQuotient
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.DivPtLocal.Count

variable {E : Type} [Field E] [NumberField E] (w : IsDedekindDomain.HeightOneSpectrum (𝓞 E))

def red (N m n : ℕ) : ↥(locDiv w N m n) →+
    (Fin m → Fin n → (w.adicCompletionIntegers E ⧸ Ideal.span {((N : ℕ) : w.adicCompletionIntegers E)})) where
  toFun X i j := Ideal.Quotient.mk _ (⟨(N : w.adicCompletion E) * X.1 i j, X.2 i j⟩ : w.adicCompletionIntegers E)
  map_zero' := by
    funext i j
    rw [Pi.zero_apply, Pi.zero_apply, ← map_zero (Ideal.Quotient.mk _)]
    congr 1
    apply Subtype.ext
    simp
  map_add' X Y := by
    funext i j
    rw [Pi.add_apply, Pi.add_apply, ← map_add (f := _)]
    congr 1
    apply Subtype.ext
    simp [mul_add]

theorem natCast_ne_zero {N : ℕ} (hN : 0 < N) : (N : w.adicCompletion E) ≠ 0 := by
  have h : (N : w.adicCompletion E) = algebraMap E (w.adicCompletion E) (N : E) := by simp
  rw [h]
  exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hN.ne')

theorem red_surjective {N : ℕ} (hN : 0 < N) (m n : ℕ) : Function.Surjective (red w N m n) := by
  intro Y
  have hN' := natCast_ne_zero w hN
  choose Z hZ using fun i j => Ideal.Quotient.mk_surjective (Y i j)
  have key : ∀ i j, (N : w.adicCompletion E) * ((N : w.adicCompletion E)⁻¹ * (Z i j : w.adicCompletion E))
      = Z i j := fun i j => by rw [← mul_assoc, mul_inv_cancel₀ hN', one_mul]
  refine ⟨⟨Matrix.of fun i j => (N : w.adicCompletion E)⁻¹ * (Z i j : w.adicCompletion E), ?_⟩, ?_⟩
  · intro i j
    rw [Matrix.of_apply, key]
    exact (Z i j).2
  · funext i j
    rw [← hZ]
    change Ideal.Quotient.mk _ _ = _
    congr 1
    apply Subtype.ext
    exact key i j

theorem ker_red {N : ℕ} (hN : 0 < N) (m n : ℕ) :
    (red w N m n).ker = (locInt w m n).addSubgroupOf (locDiv w N m n) := by
  have hN' := natCast_ne_zero w hN
  ext X
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, mem_locInt]
  simp only [funext_iff, Pi.zero_apply]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  change Ideal.Quotient.mk _ _ = _ ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    have h := congrArg (fun z : w.adicCompletionIntegers E => (z : w.adicCompletion E)) hc
    simp only [MulMemClass.coe_mul, SubringClass.coe_natCast] at h
    rw [mul_left_cancel₀ hN' h]
    exact c.2
  · intro h
    refine ⟨⟨X.1 i j, h⟩, ?_⟩
    apply Subtype.ext
    simp

theorem card_locQ (E : Type) [Field E] [NumberField E] (w : IsDedekindDomain.HeightOneSpectrum (𝓞 E))
    (N m n : ℕ) (hN : 0 < N) :
    Nat.card (GlobalTheory.DivPtLocal.LocQ w N m n) =
      Nat.card (w.adicCompletionIntegers E ⧸ Ideal.span {((N : ℕ) : w.adicCompletionIntegers E)}) ^ (m * n) := by
  have e := (QuotientAddGroup.quotientAddEquivOfEq (ker_red w hN m n).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (red w N m n) (red_surjective w hN m n))
  rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_fun, ← pow_mul]
  simp [mul_comm]

end GlobalTheory.DivPtLocal.Count

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCanonicalInertTensorCompletionEquiv
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical
noncomputable section

namespace GlobalTheory.InertTransferCanon

theorem exists_canonical_equiv : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ Dv : InertDatum L n v w, (∀ x : L, Dv.σw (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → ∃ e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) ≃+* w.adicCompletion L, (∀ x, e (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (v.adicCompletion (maximalRealSubfield L)) x) = Dv.σw (e x)) ∧ (∀ x, x ∈ Formalism.UG.tensInt (F := maximalRealSubfield L) (v.adicCompletion (maximalRealSubfield L)) (Formalism.UG.intOE L) (Formalism.UG.Ov (maximalRealSubfield L) v) ↔ e x ∈ Formalism.UG.intL (w.adicCompletion L)) ∧ ∀ z : AL L, e (compAt L v z) = F.κ z w := by
  intro L _ _ _ n F v w hov Dv hs
  obtain ⟨hu, hns, -⟩ := GlobalTheory.InertOfUnramInv.inert_of_isUnramInv L v w hov Dv.σw Dv.ϖ _ hs Dv.unram
  have hunder : w.under (𝓞 (maximalRealSubfield L)) = v := HeightOneSpectrum.ext hov
  have hw : Formalism.UG.IsInertAt (maximalRealSubfield L) L v w := by
    have h := GlobalTheory.InertPlaceConj.isInertAt_of_not_split w hu hns
    rwa [hunder] at h
  obtain ⟨c, hc, -⟩ := GlobalTheory.LFun.InertChart.existsUnique_isConjAt
    (IsCMField.complexConj L).toAlgHom hw hunder
  obtain ⟨ϖ', hU'⟩ := GlobalTheory.LFun.InertChart.exists_isUnramInv (GlobalTheory.InertDatumExist.isCMExt L) hw hc
  have hsc : Dv.σw = c := by
    apply DFunLike.coe_injective
    refine GlobalTheory.UnramCompletion.ringHom_ext_of_continuous w
      (GlobalTheory.InertDatumGiven.continuous_of_valued_eq _ Dv.unram.2.1)
      (GlobalTheory.InertDatumGiven.continuous_of_valued_eq c hU'.2.1) fun k => ?_
    rw [hs, GlobalTheory.LFun.InertChart.conj_algebraMap hc]
    rfl
  have hO : Formalism.UG.Ov L w = Formalism.UG.intL (w.adicCompletion L) := Subring.ext fun _ => Iff.rfl
  let e := (Algebra.TensorProduct.comm (maximalRealSubfield L) L
    (v.adicCompletion (maximalRealSubfield L))).toRingEquiv.trans (GlobalTheory.LFun.InertChart.complEquiv hw hunder)

  obtain ⟨i, hic, hi⟩ := F.right w v hov
  have hiy : ∀ y : maximalRealSubfield L,
      i (algebraMap _ (v.adicCompletion (maximalRealSubfield L)) y) =
        GlobalTheory.LFun.complMap hunder (algebraMap _ (v.adicCompletion (maximalRealSubfield L)) y) := by
    intro y
    rw [GlobalTheory.LFun.complMap_algebraMap]
    have h1 := hi (algebraMap (maximalRealSubfield L) _ y)
    have h2 : (1 : L) ⊗ₜ[maximalRealSubfield L]
        (algebraMap (maximalRealSubfield L) (FiniteAdeleRing (𝓞 (maximalRealSubfield L)) (maximalRealSubfield L)) y) =
        (algebraMap (maximalRealSubfield L) L y) ⊗ₜ 1 := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul']
    rw [h2, F.left] at h1
    exact h1.symm
  have hieq : (i : v.adicCompletion (maximalRealSubfield L) → w.adicCompletion L) = GlobalTheory.LFun.complMap hunder :=
    (HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield L) v).equalizer hic
      (GlobalTheory.LFun.InertChart.continuous_complMap hunder) (funext hiy)
  refine ⟨e, ?_, ?_, ?_⟩
  · intro x
    show GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _
        (Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom _ x)) =
      Dv.σw (GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _ x))
    rw [hsc, hc]
    congr 1
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  · intro x
    rw [GlobalTheory.InertDatumExist.mem_tensInt_iff, GlobalTheory.LFun.InertChart.mem_intLoc_iff hw hunder, hO]
    exact Iff.rfl
  · intro z
    induction z using TensorProduct.induction_on with
    | zero => simp; rfl
    | add x y hx hy => simp only [map_add (f := _), hx, hy]; rfl
    | tmul x a =>
      have hk : F.κ (x ⊗ₜ a) = F.κ (x ⊗ₜ 1) * F.κ (1 ⊗ₜ a) := by
        rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      show GlobalTheory.LFun.toCompl hunder (Algebra.TensorProduct.comm _ _ _ (compAt L v (x ⊗ₜ a))) = _
      have hm : ∀ p q : FiniteAdeleRing (𝓞 L) L, (p * q) w = p w * q w := fun _ _ => rfl
      rw [hk, F.left, hm, hi, hieq]
      show GlobalTheory.LFun.complMap hunder (a v) * algebraMap L _ x = _
      rw [mul_comm]
      rfl

end GlobalTheory.InertTransferCanon

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteUnramifiedApproximationPadic
section
open NumberField IsDedekindDomain Formalism.L2.Pj GlobalTheory.GeoTie

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KurApprox
open Polynomial
variable {p : ℕ} [Fact p.Prime]

section Val

variable {K : Type} [Field K] [NumberField K] (ψ : K →+* ℂ_[p])

theorem valuation_eq_exp {x : K} (hx : x ≠ 0) :
    (placeAt ψ).valuation K x = WithZero.exp (-vLa (placeAt ψ) x) := by
  rw [vLa, neg_neg, WithZero.exp_log (((placeAt ψ).valuation K).ne_zero_iff.2 hx)]

theorem exists_uniformizer : ∃ π : K, π ≠ 0 ∧ vLa (placeAt ψ) π = 1 ∧ ‖ψ π‖ < 1 := by
  set P := placeAt ψ
  obtain ⟨π, hπ⟩ := P.intValuation_exists_uniformizer
  have hπ1 : P.intValuation π < 1 := by
    rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  have hπn : ‖ψ (π : K)‖ < 1 := (mem_placeAt ψ π).1 ((P.intValuation_lt_one_iff_mem π).1 hπ1)
  have hνπ : P.valuation K (π : K) = WithZero.exp (-1) := by
    rw [← hπ]; exact HeightOneSpectrum.valuation_of_algebraMap P π
  have hπ0 : (π : K) ≠ 0 := by
    intro h
    rw [h, map_zero] at hνπ
    exact WithZero.exp_ne_zero hνπ.symm
  refine ⟨π, hπ0, ?_, hπn⟩
  simp [vLa, P, hνπ]

theorem norm_eq_zpow {π : K} (hπ0 : π ≠ 0) (hπ : vLa (placeAt ψ) π = 1) {x : K} (hx : x ≠ 0) :
    ‖ψ x‖ = ‖ψ π‖ ^ vLa (placeAt ψ) x := by
  set P := placeAt ψ
  set n := vLa P x
  set b := x * π ^ (-n) with hb
  have hb0 : b ≠ 0 := mul_ne_zero hx (zpow_ne_zero _ hπ0)
  have hνb : P.valuation K b = 1 := by
    rw [hb, map_mul, map_zpow₀, valuation_eq_exp ψ hx, valuation_eq_exp ψ hπ0, hπ, ← WithZero.exp_zsmul,
      ← WithZero.exp_add]
    simp only [smul_eq_mul, mul_neg, mul_one, neg_neg, n]
    rw [show -vLa (placeAt ψ) x + vLa P x = 0 from neg_add_cancel _, WithZero.exp_zero]
  have h1 : ‖ψ b‖ ≤ 1 := GlobalTheory.ReadingOver.norm_le_one_of_valuation_le_one ψ hνb.le
  have h2 : ‖ψ b⁻¹‖ ≤ 1 := GlobalTheory.ReadingOver.norm_le_one_of_valuation_le_one ψ (by rw [map_inv₀, hνb, inv_one])
  have hpos : 0 < ‖ψ b‖ := norm_pos_iff.2 ((map_ne_zero ψ).2 hb0)
  have hb1 : ‖ψ b‖ = 1 := by
    rw [map_inv₀, norm_inv] at h2
    exact le_antisymm h1 ((inv_le_one₀ hpos).1 h2)
  have hxb : x = b * π ^ n := by
    rw [hb, mul_assoc, ← zpow_add₀ hπ0, neg_add_cancel, zpow_zero, mul_one]
  rw [hxb, map_mul, norm_mul, hb1, one_mul, map_zpow₀, norm_zpow]

end Val

section Unram

variable {F F' : Type} [Field F] [NumberField F] [Field F'] [NumberField F'] [Algebra F F']

theorem vLa_eq_of_mem_kurC (φ : F →+* ℂ_[p]) (φ' : F' →+* ℂ_[p]) (hcomp : ∀ a, φ' (algebraMap F F' a) = φ a)
    (hk : ∀ x, φ' x ∈ kurC φ) (a : F) : vLa (placeAt φ') (algebraMap F F' a) = vLa (placeAt φ) a := by
  by_cases ha : a = 0
  · subst ha; simp [vLa]
  obtain ⟨π, hπ0, hπ, hπn⟩ := exists_uniformizer φ
  obtain ⟨π', hπ0', hπ', hπn'⟩ := exists_uniformizer φ'
  set c := ‖φ π‖ with hc
  set c' := ‖φ' π'‖ with hc'
  have hc0 : 0 < c := norm_pos_iff.2 ((map_ne_zero φ).2 hπ0)
  have hc0' : 0 < c' := norm_pos_iff.2 ((map_ne_zero φ').2 hπ0')
  obtain ⟨b, hb⟩ := GlobalTheory.KurValue.exists_norm_eq φ (hk π')
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [map_zero, norm_zero] at hb
    exact hc0'.ne' hb
  have e1 : c' = c ^ vLa (placeAt φ) b := by rw [hc', hb, norm_eq_zpow φ hπ0 hπ hb0]
  have hι0 : algebraMap F F' π ≠ 0 := (_root_.map_ne_zero _).2 hπ0
  have e2 : c = c' ^ vLa (placeAt φ') (algebraMap F F' π) := by
    rw [hc, ← hcomp, norm_eq_zpow φ' hπ0' hπ' hι0]
  have hinj := zpow_right_injective₀ hc0 hπn.ne
  have hmk : vLa (placeAt φ) b * vLa (placeAt φ') (algebraMap F F' π) = 1 := by
    apply hinj
    change c ^ (_ * _) = c ^ (1 : ℤ)
    rw [zpow_mul, ← e1, ← e2, zpow_one]
  have hm : vLa (placeAt φ) b = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hmk with h | h
    · exact h.1
    · exfalso
      rw [h.1, zpow_neg_one] at e1
      have : 1 < c⁻¹ := (one_lt_inv₀ hc0).2 hπn
      linarith
  rw [hm, zpow_one] at e1
  have hιa : algebraMap F F' a ≠ 0 := (_root_.map_ne_zero _).2 ha
  have e3 := norm_eq_zpow φ' hπ0' hπ' hιa
  rw [hcomp, norm_eq_zpow φ hπ0 hπ ha, ← hc, ← hc', e1] at e3
  exact (hinj e3).symm

end Unram

section Approx

variable {F : Type} [Field F] (φ : F →+* ℂ_[p])

def adjRoots (N : ℕ) : IntermediateField F (PAt φ) :=
  IntermediateField.adjoin F {x : PAt φ | x ^ N = 1}

theorem finite_roots {N : ℕ} (hN : 0 < N) : {x : PAt φ | x ^ N = 1}.Finite := by
  classical
  refine ((nthRoots N (1 : PAt φ)).toFinset.finite_toSet).subset fun x hx => ?_
  simpa [Polynomial.mem_nthRoots hN] using hx

theorem finiteDimensional_adjRoots {N : ℕ} (hN : 0 < N) : FiniteDimensional F (adjRoots φ N) := by
  haveI := (finite_roots φ hN).to_subtype
  refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
  have h : x ^ N = 1 := hx
  exact IsIntegral.of_pow hN (by rw [h]; exact isIntegral_one)

theorem numberField_adjRoots [NumberField F] {N : ℕ} (hN : 0 < N) : NumberField (adjRoots φ N) := by
  haveI := finiteDimensional_adjRoots φ hN
  haveI : FiniteDimensional ℚ (adjRoots φ N) := Module.Finite.trans F (adjRoots φ N)
  constructor

theorem adjRoots_mono {N M : ℕ} (h : N ∣ M) : adjRoots φ N ≤ adjRoots φ M := by
  obtain ⟨k, rfl⟩ := h
  refine IntermediateField.adjoin.mono _ _ _ fun x hx => ?_
  have hx' : x ^ N = 1 := hx
  show x ^ (N * k) = 1
  rw [pow_mul, hx', one_pow]

theorem adjRoots_le_kurC {N : ℕ} (hN : 0 < N) (hpN : ¬ p ∣ N) (z : PAt φ) (hz : z ∈ adjRoots φ N) :
    toCp φ z ∈ kurC φ := by
  let Kt : IntermediateField F (PAt φ) :=
    (show Subfield (PAt φ) from kurC φ).toIntermediateField fun a => mem_kurC φ a
  have hle : adjRoots φ N ≤ Kt := by
    refine IntermediateField.adjoin_le_iff.2 fun x hx => ?_
    have hx' : x ^ N = 1 := hx
    exact root_mem_kurC (p := p) φ hpN hx'
  exact hle hz

def kurAlg : Subfield ℂ_[p] where
  carrier := {z | ∃ N : ℕ, 0 < N ∧ ¬ p ∣ N ∧ (show PAt φ from z) ∈ adjRoots φ N}
  mul_mem' := by
    rintro x y ⟨N, hN, hpN, hx⟩ ⟨M, hM, hpM, hy⟩
    refine ⟨N * M, Nat.mul_pos hN hM, fun h => ?_, ?_⟩
    · rcases (Nat.Prime.dvd_mul (Fact.out : p.Prime)).1 h with h | h
      exacts [hpN h, hpM h]
    · exact mul_mem (adjRoots_mono φ (dvd_mul_right N M) hx) (adjRoots_mono φ (dvd_mul_left M N) hy)
  one_mem' := ⟨1, one_pos, (Fact.out : p.Prime).not_dvd_one, one_mem _⟩
  add_mem' := by
    rintro x y ⟨N, hN, hpN, hx⟩ ⟨M, hM, hpM, hy⟩
    refine ⟨N * M, Nat.mul_pos hN hM, fun h => ?_, ?_⟩
    · rcases (Nat.Prime.dvd_mul (Fact.out : p.Prime)).1 h with h | h
      exacts [hpN h, hpM h]
    · exact add_mem (adjRoots_mono φ (dvd_mul_right N M) hx) (adjRoots_mono φ (dvd_mul_left M N) hy)
  zero_mem' := ⟨1, one_pos, (Fact.out : p.Prime).not_dvd_one, zero_mem _⟩
  neg_mem' := by
    rintro x ⟨N, hN, hpN, hx⟩
    exact ⟨N, hN, hpN, neg_mem hx⟩
  inv_mem' := by
    rintro x ⟨N, hN, hpN, hx⟩
    exact ⟨N, hN, hpN, inv_mem hx⟩

theorem kurC_le : kurC φ ≤ (kurAlg φ).topologicalClosure := by
  refine Subfield.topologicalClosure_minimal _ (sup_le ?_ ?_) (Subfield.isClosed_topologicalClosure _)
  · rintro _ ⟨a, rfl⟩
    exact Subfield.le_topologicalClosure _ ⟨1, one_pos, (Fact.out : p.Prime).not_dvd_one,
      IntermediateField.algebraMap_mem _ a⟩
  · refine Subfield.topologicalClosure_minimal _ ?_ (Subfield.isClosed_topologicalClosure _)
    refine (Subfield.closure_le.2 ?_).trans (Subfield.le_topologicalClosure _)
    rintro ζ ⟨n, hn, hpn, hζ⟩
    exact ⟨n, hn, hpn, IntermediateField.subset_adjoin _ _ hζ⟩

end Approx

end GlobalTheory.KurApprox

namespace GlobalTheory.KurApprox

theorem kur_approx : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]) (n : ℕ)
    (y : Fin n → ℂ_[p]), (∀ s, y s ∈ kurC φ) → ∀ ε : ℝ, 0 < ε →
    ∃ (F' : Type) (_ : Field F') (_ : NumberField F') (_ : Algebra F F') (φ' : F' →+* ℂ_[p]),
      (∀ a, φ' (algebraMap F F' a) = φ a) ∧ (∀ a : F, vLa (placeAt φ') (algebraMap F F' a) = vLa (placeAt φ) a) ∧
      ∃ a' : Fin n → F', ∀ s, ‖y s - φ' (a' s)‖ < ε := by
  intro p _ F _ _ φ n y hy ε hε
  have h1 : ∀ s, ∃ z : ℂ_[p], ∃ N : ℕ, 0 < N ∧ ¬ p ∣ N ∧ (show PAt φ from z) ∈ adjRoots φ N ∧ ‖y s - z‖ < ε := by
    intro s
    have hs : y s ∈ closure ((kurAlg φ : Subfield ℂ_[p]) : Set ℂ_[p]) := kurC_le φ (hy s)
    obtain ⟨z, ⟨N, hN, hpN, hz⟩, hd⟩ := Metric.mem_closure_iff.1 hs ε hε
    exact ⟨z, N, hN, hpN, hz, by rwa [dist_eq_norm] at hd⟩
  choose z N hN hpN hz hd using h1
  set M := ∏ s, N s with hM
  have hM0 : 0 < M := Finset.prod_pos fun s _ => hN s
  have hpM : ¬ p ∣ M := by
    intro h
    obtain ⟨s, _, hs⟩ := ((Fact.out : p.Prime).prime.dvd_finsetProd_iff _).1 h
    exact hpN s hs
  let K := adjRoots φ M
  haveI : NumberField K := numberField_adjRoots φ hM0
  let φ' : K →+* ℂ_[p] := (toCp φ).comp (algebraMap K (PAt φ))
  have hcomp : ∀ a, φ' (algebraMap F K a) = φ a := fun a => rfl
  have hk : ∀ x : K, φ' x ∈ kurC φ := fun x => adjRoots_le_kurC φ hM0 hpM x x.2
  have hzM : ∀ s, (show PAt φ from z s) ∈ K := fun s =>
    adjRoots_mono φ (Finset.dvd_prod_of_mem N (Finset.mem_univ s)) (hz s)
  exact ⟨K, inferInstance, inferInstance, inferInstance, φ', hcomp, vLa_eq_of_mem_kurC φ φ' hcomp hk,
    fun s => ⟨z s, hzM s⟩, fun s => hd s⟩

end GlobalTheory.KurApprox
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodRankinSelbergPlaceSetSupersetTotallyCoStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.JSW Filter Topology Formalism.UG GlobalTheory.RSNonvan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_goodRankinSelbergPlaceSet_superset_totallyComplex : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (T : Finset (HeightOneSpectrum (𝓞 E))), ∃ T' : Finset (HeightOneSpectrum (𝓞 E)), T ⊆ T' ∧ IsGood T' := by
  first | (exact @GlobalTheory.RSNonvan.exists_isGood_superset_all) | (exact GlobalTheory.RSNonvan.exists_isGood_superset_all) | (intros; apply GlobalTheory.RSNonvan.exists_isGood_superset_all  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRamificationOverPlaceOfCdvrReadingInCpStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.GeoTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ramification_overPlace_of_cdvrReadingInCp : ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [NumberField F] (φ : F →+* ℂ_[p]) (T : CDVR) (io : F →+* T.Fr) (k : T.Fr →+* ℂ_[p]), IsReading φ T io k → ∃ e : ℕ, OverLa (placeAt φ) T.V io e := by
  first | exact @GlobalTheory.ReadingOver.overLa_placeAt | exact GlobalTheory.ReadingOver.overLa_placeAt | (intros; apply GlobalTheory.ReadingOver.overLa_placeAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubquotientJacquetModuleOfSupercuspidalSupStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_subquotient_jacquetModule_of_supercuspidalSupport : GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL (k := k)) (s : Multiset (IrrGL (k := k))), HasSupport x.rep s → ∃ (r : ℕ) (u : Fin r → IrrGL (k := k)) (e : (Σ a, Fin (u a).1) ≃ Fin x.1), (∀ a, u a ∈ s) ∧ IsSubquotient (piTensor fun a => (u a).rep) (jac e x.rep) := by
  first | exact @GlobalTheory.CuspQuot.exists_isSubquotient_jac_of_hasSupport | exact GlobalTheory.CuspQuot.exists_isSubquotient_jac_of_hasSupport | (intros; apply GlobalTheory.CuspQuot.exists_isSubquotient_jac_of_hasSupport <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorEqGoodIdempotentTypePlacesStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodProjector_eq_goodIdempotent_typePlaces : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) {X0 : BaseLevelRowSide D} (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → ∀ (s : ∀ k : Fin 2, D.nd.PlG k → SplitPlace D.host.E) (j : ∀ k v, ℚ_[D.host.g k] ≃+* (s k v).v.adicCompletion (maximalRealSubfield D.host.E)), (∀ k v, (s k v).w = D.naut.plGw k v) → (∀ k v, Continuous (j k v)) → ∀ (c : GAf D.host.E D.R.r), (∀ (k : Fin 2) (v : D.nd.PlG k) (y : GL (Fin D.R.r) ℤ_[D.host.g k]) (x : GAf D.host.E D.R.r), IsLiftAt (s k v) (j k v) y x → IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (cG.symm (GlobalTheory.GoodTypes.facHom D k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y))) (Y.PY.ψ (c * x * c⁻¹))) → ∀ (ρ : Representation ℂ (G0g D.nd) (KFix D s j ((principalLevelFrame.actM Y.PY (R.MY 0)).comp (MulAut.conj c).toMonoidHom))), (∀ (k : Fin 2) (v : D.nd.PlG k) (y : GL (Fin D.R.r) ℤ_[D.host.g k]) (x : GAf D.host.E D.R.r), IsLiftAt (s k v) (j k v) y x → ∀ z, ((ρ (GlobalTheory.GoodTypes.facHom D k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y)) z : KFix D s j ((principalLevelFrame.actM Y.PY (R.MY 0)).comp (MulAut.conj c).toMonoidHom)) : Mult.MMap (R.MY 0)) = ((principalLevelFrame.actM Y.PY (R.MY 0)).comp (MulAut.conj c).toMonoidHom) x z) → ∀ (b : Bool) (Tm : Mult.MMap (R.MY 0)) (hK : Tm ∈ KFix D s j ((principalLevelFrame.actM Y.PY (R.MY 0)).comp (MulAut.conj c).toMonoidHom)), Tm ∈ Mult.goodPart R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) R.toRealDat.e0 → ρ.asAlgebraHom D.ntypes.e0 ⟨Tm, hK⟩ = ⟨Tm, hK⟩ := by
  first | exact @GlobalTheory.RowGood.good_idem_fix_conj | exact GlobalTheory.RowGood.good_idem_fix_conj | (intros; apply GlobalTheory.RowGood.good_idem_fix_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsSpehProductStatement
section
open NumberField ReciprocityTheory.Gal Formalism.ConjugateSelfDual IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.DefiniteBC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_langlands_speh_product : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)),
    letI := GlobalTheory.LocalData.complRel w
    haveI := GlobalTheory.LocalData.isLocalField w
    ∀ (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h),
    IsRec h rc → GlobalTheory.Published.GenericUnitaryDualGL → GlobalTheory.Published.StandardCosocleGL →
    ∀ (a d n : ℕ) (hd : ∑ _ : Fin d, a = n) (σ : LocIrr w a) (σ' : LocIrr w n),
      IsUnitarisable σ.ρ → IsGeneric σ.ρ → IsSpehQuot hd σ σ' →
      rc (cls (ParLaws.toRep σ')) =
        sumList ((List.range d).map fun k : ℕ => (rc (cls (ParLaws.toRep σ))).lpTw (((d : ℝ) - 1) / 2 - k)) := by
  first | exact @GlobalTheory.SpehRec.rec_spehQuot | exact GlobalTheory.SpehRec.rec_spehQuot | (intros; apply GlobalTheory.SpehRec.rec_spehQuot <;> assumption)
end

