module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0350
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0310
public import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocG
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.LocalRingCardinality.Bundle0003
public import Formalism.LocalRingCardinality.SpanPowerMembership.RankRecordRowDimensionZero
public import Formalism.LocalRingCardinality.SpanPowerMembership.SignSplitEquivInl
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0434
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0200
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0436
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0217
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelExtensionFirst
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0983
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0225
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatB
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0096
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnCharacterReductionEqExp
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSplittingCharacterSelf
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormLeOneOfMemClC
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Df NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Df

open Formalism.L2.TwC

theorem norm_le_one_of_mem_clC' (l : ℕ) [Fact l.Prime] (F : IntermediateField ℚ_[l] (PadicAlgCl l)) {z : ℂ_[l]}
    (hz : z ∈ clC l F) : ‖z‖ ≤ 1 := by
  have hm : z ∈ PadicComplexInt l := (Subring.mem_inf.1 hz).2
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff] at hm
  rw [PadicComplex.norm_eq_norm]
  exact (Valued.toNormedField.norm_le_one_iff).2 hm

theorem exists_iC_of_clC (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O]
    (F : IntermediateField ℚ_[l] (PadicAlgCl l)) (e : O ≃+* clC l F)
    (hratio : ∀ x ∈ clC l F, ∀ y ∈ clC l F, ‖x‖ ≤ ‖y‖ → x / y ∈ clC l F) :
    ∃ iC : FractionRing O →+* ℂ_[l],
      ∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap O (FractionRing O)).range := by
  let ψ : O →+* ℂ_[l] := (clC l F).subtype.comp e.toRingHom
  have hψ : Function.Injective ψ := fun a b h => e.injective (Subtype.ext h)
  let iC : FractionRing O →+* ℂ_[l] := IsFractionRing.lift hψ
  have hiC : ∀ a : O, iC (algebraMap O (FractionRing O) a) = ψ a := fun a => IsFractionRing.lift_algebraMap hψ a
  refine ⟨iC, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) x
    have hb0 : algebraMap O (FractionRing O) b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have hψb : ψ b ≠ 0 := by
      rw [← hiC]; exact (map_ne_zero iC).2 hb0
    rw [map_div₀, hiC, hiC, norm_div, div_le_one (norm_pos_iff.2 hψb)] at hx
    have hmem := hratio _ (e a).2 _ (e b).2 hx
    refine ⟨e.symm ⟨_, hmem⟩, ?_⟩
    apply iC.injective
    rw [hiC, map_div₀, hiC, hiC]
    show ((e (e.symm ⟨_, hmem⟩) : clC l F) : ℂ_[l]) = _
    rw [e.apply_symm_apply]
    rfl
  · rintro ⟨a, rfl⟩
    rw [hiC]
    exact norm_le_one_of_mem_clC' l F (e a).2

end GlobalTheory.Mem.Df

namespace GlobalTheory.Mem.Df

open Formalism.L2.TwC

end GlobalTheory.Mem.Df
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NumberFieldGLDenseInCompletionGLTwoSided
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.DenseGL

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

theorem approx (x : P.adicCompletion E) (M : ℤ) :
    ∃ e : E, Valued.v (x - algebraMap E (P.adicCompletion E) e) ≤ WithZero.exp (-M) := by
  have hd := HeightOneSpectrum.denseRange_algebraMap (K := E) P
  obtain ⟨π, hπ⟩ := HeightOneSpectrum.valuation_exists_uniformizer (K := E) P
  set c : P.adicCompletion E := algebraMap E (P.adicCompletion E) (π ^ M.toNat) with hc
  have hvc : Valued.v c = WithZero.exp (-(M.toNat : ℤ)) := by
    have hv : ∀ k : E, Valued.v (algebraMap E (P.adicCompletion E) k) = P.valuation E k :=
      fun k => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P k
    rw [hc, hv, map_pow, hπ,
      ← WithZero.exp_nsmul]
    congr 1
    simp
  have hc0 : Valued.v c ≠ 0 := by rw [hvc]; exact WithZero.exp_ne_zero
  have hN : {y : P.adicCompletion E | Valued.v (x - y) < Valued.v c} ∈ nhds x := by
    have ho := (Valued.isOpen_ball (P.adicCompletion E) (Valued.v.restrict c)).preimage
      (continuous_const.sub continuous_id : Continuous fun y : P.adicCompletion E => x - y)
    simp only [Set.preimage_ofPred_eq, Valuation.restrict_lt_iff] at ho
    refine ho.mem_nhds ?_
    show Valued.v (x - x) < _
    rw [sub_self, map_zero]
    exact zero_lt_iff.2 hc0
  obtain ⟨e, he⟩ := hd.mem_nhds hN
  refine ⟨e, le_of_lt (lt_of_lt_of_le he ?_)⟩
  rw [hvc, WithZero.exp_le_exp]
  have := Int.self_le_toNat M
  omega

theorem bound {n : ℕ} (B : Matrix (Fin n) (Fin n) (P.adicCompletion E)) :
    ∃ L : ℕ, ∀ r k, Valued.v (B r k) ≤ WithZero.exp (L : ℤ) := by
  obtain ⟨c, hc⟩ := Finite.bddAbove_range (fun p : Fin n × Fin n => Valued.v (B p.1 p.2))
  refine ⟨(WithZero.log (max c 1)).toNat, fun r k => ?_⟩
  have h1 : Valued.v (B r k) ≤ max c 1 := (hc ⟨(r, k), rfl⟩).trans (le_max_left _ _)
  have h0 : max c 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  refine h1.trans ?_
  rw [← WithZero.exp_log h0, WithZero.exp_le_exp, WithZero.log_exp]
  exact Int.self_le_toNat _

end GlobalTheory.DenseGL

namespace GlobalTheory.DenseGL

variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

def smallIdeal : Ideal (P.adicCompletionIntegers E) where
  carrier := {x | Valued.v (x : P.adicCompletion E) < 1}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Subring.coe_add] at *
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha hb)
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq, smul_eq_mul] at *
    have hc : Valued.v (c : P.adicCompletion E) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 c.2
    rw [show ((c * x : P.adicCompletionIntegers E) : P.adicCompletion E) = c * x from rfl, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hc) hx

theorem one_add_small {n : ℕ} (X : Matrix (Fin n) (Fin n) (P.adicCompletion E))
    (hX : ∀ r s, Valued.v (X r s) < 1) :
    Valued.v (1 + X).det = 1 ∧ ∀ r s, Valued.v ((1 + X)⁻¹ r s) ≤ 1 := by
  set O := P.adicCompletionIntegers E
  have hmem : ∀ r s, X r s ∈ O := fun r s =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hX r s).le
  let X' : Matrix (Fin n) (Fin n) O := fun r s => ⟨X r s, hmem r s⟩
  have hmap : O.subtype.mapMatrix (1 + X') = 1 + X := by
    rw [map_add (f := _), map_one]; rfl
  have hq : (Ideal.Quotient.mk (smallIdeal P)).mapMatrix (1 + X') = 1 := by
    rw [map_add (f := _), map_one, add_eq_left]
    ext r s
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hX r s)
  have hd : (1 + X').det - 1 ∈ smallIdeal P := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, RingHom.map_det, hq, Matrix.det_one, map_one,
      sub_self]
  have hdet : Valued.v (1 + X).det = 1 := by
    rw [← hmap, ← RingHom.map_det]
    have h1 : (O.subtype (1 + X').det) = 1 + (((1 + X').det - 1 : O) : P.adicCompletion E) := by
      simp [O]
    rw [h1]
    exact Valuation.map_one_add_of_lt _ hd
  refine ⟨hdet, fun r s => ?_⟩
  have hdet0 : (1 + X).det ≠ 0 := fun h => by rw [h, map_zero] at hdet; exact zero_ne_one hdet
  rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, hdet,
    inv_one, one_mul, ← hmap, ← RingHom.map_adjugate]
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 ((1 + X').adjugate r s).2

end GlobalTheory.DenseGL

namespace GlobalTheory.DenseGL

theorem entry_le {n : ℕ} {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] (B C : Matrix (Fin n) (Fin n) K)
    (a b : WithZero (Multiplicative ℤ)) (hB : ∀ r k, Valued.v (B r k) ≤ a) (hC : ∀ k s, Valued.v (C k s) ≤ b) (r s : Fin n) :
    Valued.v ((B * C) r s) ≤ a * b := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun k _ => ?_
  rw [map_mul]
  exact mul_le_mul' (hB r k) (hC k s)

theorem dense_two_sided : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (n N : ℕ) (A : GL (Fin n) (P.adicCompletion E)), ∃ γ : GL (Fin n) E, ∀ r s, Valued.v (((A⁻¹).1 * γ.1.map (algebraMap E (P.adicCompletion E)) - 1) r s) ≤ WithZero.exp (-(N : ℤ)) ∧ Valued.v (((γ⁻¹).1.map (algebraMap E (P.adicCompletion E)) * A.1 - 1) r s) ≤ WithZero.exp (-(N : ℤ)) := by
  intro E _ _ P n N A
  set f := algebraMap E (P.adicCompletion E)
  set B := (A⁻¹).1 with hBdef
  have hBA : B * A.1 = 1 := Units.inv_mul A
  obtain ⟨L, hL⟩ := bound P B
  choose C hC using fun r s => approx P (A.1 r s) ((N : ℤ) + 1 + L)
  let Cm : Matrix (Fin n) (Fin n) E := Matrix.of C
  set C' := Cm.map f with hC'
  set X := B * C' - 1 with hXdef
  have hXe : X = B * (C' - A.1) := by rw [Matrix.mul_sub, hBA]
  have hsmall : ∀ r s, Valued.v (X r s) ≤ WithZero.exp (-((N : ℤ) + 1)) := by
    intro r s
    rw [hXe]
    refine (entry_le B (C' - A.1) _ (WithZero.exp (-((N : ℤ) + 1 + L))) hL (fun k s => ?_) r s).trans (le_of_eq ?_)
    · show Valued.v (f (C k s) - A.1 k s) ≤ _
      rw [Valuation.map_sub_swap]
      exact hC k s
    · rw [← WithZero.exp_add]; congr 1; ring
  have hN1 : WithZero.exp (-((N : ℤ) + 1)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
  have hNN : WithZero.exp (-((N : ℤ) + 1)) ≤ WithZero.exp (-(N : ℤ)) := by
    rw [WithZero.exp_le_exp]; omega
  have hX1 : ∀ r s, Valued.v (X r s) < 1 := fun r s => (hsmall r s).trans_lt hN1
  obtain ⟨hdet, hint⟩ := one_add_small P X hX1
  have hY : 1 + X = B * C' := by rw [hXdef]; abel
  have hCdet : Cm.det ≠ 0 := by
    intro h0
    have : (1 + X).det = 0 := by
      rw [hY, Matrix.det_mul, hC', ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero,
        mul_zero]
    rw [this, map_zero] at hdet
    exact zero_ne_one hdet
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero Cm hCdet, fun r s => ⟨?_, ?_⟩⟩
  · exact (hsmall r s).trans hNN
  · set γ := Matrix.GeneralLinearGroup.mkOfDetNeZero Cm hCdet
    have hγ : γ.1 = Cm := rfl
    set D := (γ⁻¹).1.map f
    have hCD : C' * D = 1 := by
      rw [hC', ← hγ, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero f) (map_one f)]
    have hYZ : (1 + X) * (D * A.1) = 1 := by
      rw [hY, Matrix.mul_assoc, ← Matrix.mul_assoc C', hCD, Matrix.one_mul, hBA]
    have hZ : D * A.1 = (1 + X)⁻¹ := (Matrix.inv_eq_right_inv hYZ).symm
    have hZY : (D * A.1) * (1 + X) = 1 := by
      rw [hZ]; exact Matrix.nonsing_inv_mul _ (by
        refine isUnit_iff_ne_zero.2 fun h => ?_; rw [h, map_zero] at hdet; exact zero_ne_one hdet)
    have hdiff : D * A.1 - 1 = -((D * A.1) * X) := by
      rw [Matrix.mul_add, Matrix.mul_one] at hZY
      rw [← hZY]; abel
    rw [hdiff, Matrix.neg_apply, Valuation.map_neg]
    refine (entry_le _ X 1 _ (by rw [hZ]; exact hint) hsmall r s).trans ?_
    rw [one_mul]; exact hNN

end GlobalTheory.DenseGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OmegaFormRationality
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

noncomputable section

namespace GlobalTheory.OneMapRef.IoCmp

theorem pure_rename {ι ι' κ X : Type} {A : ι → (X → ℂ) → (X → ℂ)} {A' : ι' → (X → ℂ) → (X → ℂ)} {g : X → ℂ}
    (hX : ∀ v Q, pureTensorL A g (MvPolynomial.X v * Q) = A v (pureTensorL A g Q))
    (hX' : ∀ v Q, pureTensorL A' g (MvPolynomial.X v * Q) = A' v (pureTensorL A' g Q))
    (e : κ → ι) (e' : κ → ι') (h : ∀ k, A (e k) = A' (e' k)) (Q : MvPolynomial κ ℂ) :
    pureTensorL A g (MvPolynomial.rename e Q) = pureTensorL A' g (MvPolynomial.rename e' Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.rename_C, MvPolynomial.rename_C, ← mul_one (MvPolynomial.C a : MvPolynomial ι ℂ),
      ← mul_one (MvPolynomial.C a : MvPolynomial ι' ℂ), MvPolynomial.C_mul', MvPolynomial.C_mul', map_smul, map_smul,
      GlobalTheory.FockIndep.pure_one, GlobalTheory.FockIndep.pure_one]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    rw [mul_comm, map_mul (MvPolynomial.rename e), map_mul (MvPolynomial.rename e'), MvPolynomial.rename_X, MvPolynomial.rename_X, hX, hX', hp, h]

theorem aeval_scale {L Y : Type} (f : L → Y) (s : ℂ) {N : ℕ} {Q : MvPolynomial L ℂ} (hQ : Q.IsHomogeneous N) :
    MvPolynomial.aeval (fun ℓ => MvPolynomial.C s * MvPolynomial.X (f ℓ)) Q =
      MvPolynomial.C (s ^ N) * MvPolynomial.rename f Q := by
  conv_lhs => rw [Q.as_sum]
  conv_rhs => rw [Q.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : m.degree = N := by
    have := hQ (MvPolynomial.mem_support_iff.1 hm)
    rwa [Finsupp.degree_eq_weight_one]
  rw [MvPolynomial.rename_eq_aeval, MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial, ← hd]
  simp only [mul_pow, Finsupp.prod, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Function.comp_apply, map_pow,
    Finsupp.degree_apply]
  ring

theorem isHomogeneous_of_span {T : Type} [Fintype T] (r : T → ℕ) (n : ℕ) (k : Type) [Field k] (cc : T → T) (isX : T → Prop)
    (a : T → ℕ → ℕ) {P : MvPolynomial (Letter T r n) k} (hP : P ∈ Submodule.span k (HHa r n k cc isX a)) :
    P.IsHomogeneous (∑ σ, ∑ i : Fin (r σ), a σ i) := by
  refine (Submodule.span_le (p := MvPolynomial.homogeneousSubmodule _ k _)).2 (fun Q hQ m hm => ?_) hP
  have h := hQ.2.2 m (MvPolynomial.mem_support_iff.2 hm)
  refine Eq.trans (b := m.degree) (by rw [Finsupp.degree_eq_weight_one]; rfl) ?_
  rw [Finsupp.degree_eq_sum, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun i _ => h σ i

theorem lieFac_eq_pow {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (Dw : Datum H) (hx : 0 < xiR D)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) :
    lieFac Dw (xiR D) a = (Real.sqrt (2 * Real.pi * xiR D))⁻¹ ^ (∑ σ, ∑ i : Fin (Dw.mult σ), a (σ, i)) := by
  have h : 0 < 2 * Real.pi * xiR D := by positivity
  have h2 : (Real.sqrt (2 * Real.pi * xiR D))⁻¹ = Real.exp (-(Real.log (2 * Real.pi * xiR D) / 2)) := by
    rw [Real.exp_neg, ← Real.log_sqrt h.le, Real.exp_log (Real.sqrt_pos.2 h)]
  rw [h2, ← Real.exp_nat_mul, lieFac]
  congr 1
  push_cast
  ring

theorem two_div_fockScale (D : D7) (τ : D.what₂.Tau) : 2 / fockScale D τ = (Real.sqrt (2 * Real.pi * xiR D))⁻¹ := by
  rw [fockScale, ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatB.norm_embedding_hostFormConstant_eq, div_mul_cancel_left₀ two_ne_zero]

theorem unitMap_submatrix {m n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (B' : Matrix (Fin m) (Fin m) ℂ) (π : Fin m → Fin m)
    (c : Fin m) (j : Fin n) :
    Formalism.IndefR.Datum.unitMap B (B'.submatrix id π) c j = Formalism.IndefR.Datum.unitMap B B' (π c) j := by
  unfold Formalism.IndefR.Datum.unitMap
  congr 1
  ext a b
  by_cases h : b = j
  · subst h
    simp
  · simp [Matrix.mul_single_apply_of_ne _ _ _ _ _ h]

theorem pureTensorO_rename {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} (hψ : IsStdChar D ψ (-1))
    (hθ : IsInfFam θ) {s : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ} (hS : ∀ τ, IsCartanInv (gramAt D S τ) 1)
    (hT : ∀ τ, IsCartanInv (gramAt D T τ) (s τ)) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (B : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (Z Z' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (π : D.what₂.Tau → Fin T.rank → Fin T.rank) (hZ : ∀ τ, Z' τ = (Z τ).submatrix id (π τ)) {κ : Type} (ρ : κ → D.what₂.Tau)
    (c : κ → Fin T.rank) (b : κ → Fin S.rank) (Q : MvPolynomial κ ℂ) :
    pureTensorO ψ θ S T (fun _ => 1) s B Z f (MvPolynomial.rename (fun k => (ρ k, π (ρ k) (c k), b k)) Q) =
      pureTensorO ψ θ S T (fun _ => 1) s B Z' f (MvPolynomial.rename (fun k => (ρ k, c k, b k)) Q) := by
  have hX : ∀ B' v Q, pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (s τ)) B B') f (MvPolynomial.X v * Q) =
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (s τ)) B B' v
        (pureTensorL (aPlusAll (heisO ψ S T) θ (fun τ => cplxO 1 (s τ)) B B') f Q) := fun B' v Q => by
    refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add)
      (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) (fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h) ?_ ?_ ?_ hf Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' (sS := fun _ => 1) hψ hθ i.1 _ hS hT j.1 _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h
  unfold pureTensorO
  refine pure_rename (hX Z) (hX Z') _ _ (fun k => ?_) Q
  simp only [aPlusAll, hZ, unitMap_submatrix]

end GlobalTheory.OneMapRef.IoCmp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PassStepCongr
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.GroupRetwisting

theorem pass_step_congr {α : Type*} (g : ∀ P : Pre, Fr P → α) {P P' : Pre} {f : Fr P} {f' : Fr P'} (h : P = P') (hf : HEq f f') :
    g P f = g P' f' := by
  subst h
  rw [eq_of_heq hf]

theorem pass_step : ∀ (KP : BaseP) (Q : V4.Slot) (r r' : AtP), BaseCond KP → Pass KP Q r → Step KP r r' → Pass KP Q r' := by
  classical
  intro KP Q r r' hK hR hS
  refine (EvG.inter hS hR).imp fun K _ _ _ _ H => ?_
  obtain ⟨hs, hr⟩ := H
  have hs' : large₂ K fun B f T => KP B f → r K B f T → r' K B f T :=
    (hs.inter (lg_forced K)).imp fun _ _ _ _ G a b => G.1 a G.2 b
  obtain ⟨S₁, P₁, A₀, S₂₀, a₁, a₂, hlg⟩ := hs'
  have hb : large₂ K fun B f T => (∀ z ∈ S₁ B.toPre f B.KsC, z ∈ B.fixedCoefficientFieldInComplex) ∧ P₁ B.toPre f B.KsC B.fixedCoefficientFieldInComplex ⊆ T.pl :=
    ⟨S₁, P₁, fun _ _ _ _ _ => ∅, S₂₀, a₁, a₂, fun _ _ _ _ h p _ => ⟨h.1, p⟩⟩
  refine (hr.inter hb).imp ?_
  rintro B f T hO ⟨hr, h₁, hp⟩ hKP hT C W V S N G c q hx A S₂ hS₂
  obtain ⟨B', f', T', e, hf, hpl, hAv, hS', hr'⟩ := hr hKP hT C W V S N G c q hx
    (fun l => A l ∪ A₀ B.toPre f B.KsC B.fixedCoefficientFieldInComplex l) (fun P g Ξ => S₂ P g Ξ ∪ S₂₀ P g B.KsC B.fixedCoefficientFieldInComplex Ξ)
    (fun P g Ξ z hz => (Finset.mem_union.1 hz).elim (hS₂ P g Ξ z) (a₂ P g _ _ Ξ z))
  have hP : B'.toPre = B.toPre := e.1
  have hk : B'.KsC = B.KsC := e.KsC_eq
  have hl : B'.fixedCoefficientFieldInComplex = B.fixedCoefficientFieldInComplex := e.fixedCoefficientField_eq
  have hO' : K.Over B'.toPre := hP ▸ hO
  have hLL : ∀ z ∈ S₂₀ B'.toPre f' B'.KsC B'.fixedCoefficientFieldInComplex (T'.set f'), z ∈ B'.LLC := by
    intro z hz
    rw [hk, hl] at hz
    obtain ⟨x, rfl⟩ := hS' z (Finset.mem_union_right _ hz)
    exact ⟨x, rfl⟩
  have r'' := hlg B' f' T' hO'
    ⟨by rw [hk, hl, pass_step_congr S₁ hP hf]; exact h₁, hLL⟩
    (by rw [hk, hl, pass_step_congr P₁ hP hf, hpl]; exact hp)
    (fun w v hv hA => hAv w v hv (Finset.mem_union_right _ (by
      rw [hk, hl, pass_step_congr A₀ hP hf] at hA; exact hA)))
    (hK.enl B B' f f' e hf hKP) hr'
  exact ⟨B', f', T', e, hf, hpl, fun w v hv hA => hAv w v hv (Finset.mem_union_left _ hA),
    fun z hz => hS' z (Finset.mem_union_left _ hz), r''⟩

end GlobalTheory.Mem.Top.GroupRetwisting
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodLatticeIdealTrivialAtChainBadPrimes
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.AdT


open Formalism.HermitianLatticesTheory GlobalTheory.ThetaMove in
theorem inverseHalfDifferent_local_trivial_at_prime_norm {R : Ranks} (H : Host R) (P : HeightOneSpectrum (𝓞 H.E)) (hp : (Ideal.absNorm P.asIdeal).Prime)
    (h2 : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 H.E) ∉ P.asIdeal ^ 2) :
    Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (H.AA0 : Submodule (𝓞 H.E) H.E) = Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (1 : Submodule (𝓞 H.E) H.E) := by
  have := P.isPrime
  have hmem : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 H.E) ∈ P.asIdeal := Ideal.absNorm_mem _
  have hnd := GlobalTheory.PeriodIdealUnit.not_dvd_different (K := H.K) hp P.asIdeal hmem h2
  have hnot : ¬ H.𝔟 ≤ P.asIdeal := fun hle => hnd (by
    rw [H.𝔟_spec.1]
    exact (Ideal.dvd_iff_le.2 hle).mul_right _)
  obtain ⟨z, hz, hzP⟩ := IsConcreteLE.not_le_iff_exists.1 hnot
  have hB : ((H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 fun h => by
      have h3 := H.𝔟_spec.2
      simp [h] at h3
  refine GlobalTheory.PeriodIdealUnit.locP_eq_one P _ ?_ ?_
  · intro t ht
    have ht' : t ∈ H.AA0 := ht
    unfold Host.AA0 at ht'
    obtain ⟨w, hw⟩ := (FractionalIdeal.mem_one_iff _).1
      ((FractionalIdeal.mem_inv_iff hB).1 ht' _ (FractionalIdeal.mem_coeIdeal_of_mem _ hz))
    refine (mem_locP P 1 t).2 ⟨z, hzP, Submodule.mem_one.2 ⟨w, ?_⟩⟩
    rw [Algebra.smul_def, hw, mul_comm]
  · refine ⟨1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), ?_⟩
    rw [one_smul]
    show (1 : H.E) ∈ H.AA0
    unfold Host.AA0
    refine (FractionalIdeal.mem_inv_iff hB).2 fun y hy => ?_
    rw [one_mul]
    exact FractionalIdeal.coeIdeal_le_one hy

theorem aaUnit_sall : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (a : I.ι) (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ), (I.J.amb B χ).AAUnit (Sall (Pr := B.primes X) I.sel (I.tup a) u) := by
  intro B X I hOk u a χ P hP
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  have bad := GlobalTheory.ThetaMove.BadPrimes.bad_primes B.fields (B.primes X) I.sel I.S (I.tup a) u hX hPr hOk.sel_ok
    (hOk.T_mem u) hOk.g_mem P hP
  show Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Th.perAA B.host ⊤) = _
  rw [Th.perAA_top]
  exact inverseHalfDifferent_local_trivial_at_prime_norm B.host P bad.2.1 bad.2.2.1

end GlobalTheory.Mem.Col2.AdT
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiGTrue
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Mem.TypePrimes.psiG_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), ColIn.Ok I → TC.Pins B X → ∀ (l : TC.Laws I) (Z : TC.Later B (TC.cols I l)) (G : GLoc (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.E (sigD (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G)) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g), TC.IdG I l Z G → ∀ ψ, Formalism.L2.Theta.IsStdChar (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) ψ (-1) → ∀ (k : Fin 2) (v : HeightOneSpectrum (𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F)) (h : ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g k : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ∈ v.asIdeal) (ε : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F), Formalism.L2.Theta.IsPlaceIdem (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) v ε → ∀ c y : 𝓞 (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F, Valued.v (algebraMap (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F (v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (c : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) - G.phi k v h (inclE (F := (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.xi0)) < 1 → ∀ z : v.adicCompletionIntegers (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F, (z : v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) = algebraMap (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F (v.adicCompletion (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) (y : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) → G.psi0 k v h (IsLocalRing.residue _ z) = ψ (ε * algebraMap (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) ((c : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) * (y : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F) / ((_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.g k : (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).host.F))) :=
  by
    intro B X I hI _ l Z G hG ψ hψ k v h ε hε c y hc z hz
    have hs := (TC.rec7 I l Z).nd.g_split k
    have hgp := l.pr.g_prime k
    obtain ⟨hN, hsq⟩ := GlobalTheory.Mem.TypePrimes.Red.absNorm_and_unram hgp hs v h
    obtain ⟨t, ht⟩ := GlobalTheory.Mem.TypePrimes.Red.exists_hostXi0_inverse_integer B.host
    obtain ⟨b, hb, e⟩ := GlobalTheory.Mem.TypePrimes.Red.columnCharacter_reduction_eq_exp
      (X := B.fields) (Pr := B.primes X) I.Ch l.pr B.sp.cm B.embLL B.host.xi0 hI.weil t ht G hG.piG
      (fun _ => rfl) hG.psi k v h hN c y hc z hz
    refine e.trans ?_
    exact (_root_.GlobalTheory.StdCharDegOne.stdChar_placeIdem_div (TC.rec7 I l Z) ψ hψ _
      hgp v hN hsq ε hε (c * y) (b : ℤ) (by rw [Int.cast_natCast]; exact hb)).symm
end

