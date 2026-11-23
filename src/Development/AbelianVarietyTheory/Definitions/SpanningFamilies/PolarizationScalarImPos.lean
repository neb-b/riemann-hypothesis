module

public import Mathlib
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0045
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate

namespace GlobalTheory.Ker.Model

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Char

variable {F : Type} [Field F] [NumberField F]

theorem isOpen_int (F : Type) [Field F] [NumberField F] : IsOpen (intAf F) :=
  RestrictedProduct.isOpen_forall_mem
    (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    fun v => Valued.isOpen_valuationSubring _

theorem trace_int {a : F} (h : algebraMap F (Af F) a ∈ intAf F) : ∃ n : ℤ, Algebra.trace ℚ F a = n := by
  have h1 : a ∈ (algebraMap (𝓞 F) F).range := by
    refine HeightOneSpectrum.mem_integers_of_valuation_le_one F a fun v => ?_
    have h2 : Valued.v ((a : F) : v.adicCompletion F) ≤ 1 := h v
    rwa [HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h2
  obtain ⟨b, rfl⟩ := h1
  have h3 : IsIntegral ℤ (Algebra.trace ℚ F (algebraMap (𝓞 F) F b)) := Algebra.isIntegral_trace b.2
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 h3
  exact ⟨n, hn.symm⟩

theorem int_sub {a b : Af F} (ha : a ∈ intAf F) (hb : b ∈ intAf F) : a - b ∈ intAf F := fun v => by
  rw [map_sub]; exact sub_mem (ha v) (hb v)

theorem int_add {a b : Af F} (ha : a ∈ intAf F) (hb : b ∈ intAf F) : a + b ∈ intAf F := fun v => by
  rw [map_add]; exact add_mem (ha v) (hb v)

theorem int_zero : (0 : Af F) ∈ intAf F := fun v => by
  rw [map_zero]; exact zero_mem _

theorem exists_char (t : Ainf F →+ ℂ) (hc : Continuous t) (hre : ∀ x, (t x).im = 0)
    (ht : ∀ a : F, t (algebraMap F (Ainf F) a) = ((Algebra.trace ℚ F a : ℚ) : ℂ)) :
    ∃ ψ : AddChar (AF F) ℂ, IsCharAF F ψ ∧
      ∀ x, psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℤ)) : ℂ) * t x) := by
  have hap : ∀ y : Af F, ∃ a : F, y - algebraMap F (Af F) a ∈ intAf F := fun y => by
    obtain ⟨a, β, hβ, h⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F 1 one_pos).1 y
    refine ⟨a, ?_⟩
    rw [h, one_smul, add_sub_cancel_left]
    exact hβ
  choose ap hap using hap
  let c : ℂ := 2 * Real.pi * Complex.I
  let f : AF F → ℂ := fun x => Complex.exp (c * (((Algebra.trace ℚ F (ap x.2) : ℚ) : ℂ) - t x.1))
  have key : ∀ (x : AF F) (a : F), x.2 - algebraMap F (Af F) a ∈ intAf F →
      f x = Complex.exp (c * (((Algebra.trace ℚ F a : ℚ) : ℂ) - t x.1)) := by
    intro x a h
    have h1 : algebraMap F (Af F) (ap x.2 - a) ∈ intAf F := by
      have := int_sub h (hap x.2)
      rw [map_sub]
      convert this using 1
      ring
    obtain ⟨n, hn⟩ := trace_int h1
    rw [map_sub, sub_eq_iff_eq_add] at hn
    show Complex.exp _ = _
    rw [hn, Complex.exp_eq_exp_iff_exists_int]
    refine ⟨n, ?_⟩
    push_cast
    ring
  have f0 : ∀ x : AF F, x.2 ∈ intAf F → f x = Complex.exp (-(c * t x.1)) := fun x hx => by
    rw [key x 0 (by rwa [map_zero, sub_zero])]
    simp
  have fadd : ∀ x y, f (x + y) = f x * f y := fun x y => by
    rw [key (x + y) (ap x.2 + ap y.2) (by
      have := int_add (hap x.2) (hap y.2)
      rw [map_add (f := _)]
      convert this using 1
      show x.2 + y.2 - _ = _
      ring), ← Complex.exp_add]
    congr 1
    rw [map_add (f := _), show (x + y).1 = x.1 + y.1 from rfl, map_add (f := _)]
    push_cast
    ring
  let ψ : AddChar (AF F) ℂ :=
    { toFun := f
      map_zero_eq_one' := by
        rw [f0 0 int_zero, show (0 : AF F).1 = 0 from rfl, map_zero]; simp
      map_add_eq_mul' := fadd }
  have hinf : ∀ x, psiInf F ψ x = Complex.exp (2 * Real.pi * Complex.I * (((-1 : ℤ)) : ℂ) * t x) := fun x => by
    show f (x, 0) = _
    rw [f0 (x, 0) int_zero]
    congr 1
    push_cast
    ring
  refine ⟨ψ, ⟨?_, fun x => ?_, fun a => ?_, ?_⟩, hinf⟩
  · rw [continuous_iff_continuousAt]
    intro x₀
    have hU : {x : AF F | x.2 - x₀.2 ∈ intAf F} ∈ nhds x₀ :=
      ((isOpen_int F).preimage (continuous_snd.sub continuous_const)).mem_nhds (by
        show x₀.2 - x₀.2 ∈ intAf F
        rw [sub_self]; exact int_zero)
    have hg : Continuous fun x : AF F => f x₀ * Complex.exp (-(c * t (x.1 - x₀.1))) :=
      continuous_const.mul (Complex.continuous_exp.comp
        (continuous_const.mul (hc.comp (continuous_fst.sub continuous_const))).neg)
    refine hg.continuousAt.congr (Filter.eventually_of_mem hU fun x hx => ?_)
    show _ = f x
    rw [← add_sub_cancel x₀ x, fadd, f0 (x - x₀) hx, add_sub_cancel]
    rfl
  · show ‖Complex.exp _‖ = 1
    rw [Complex.norm_exp]
    simp [c, hre]
  · show f _ = 1
    rw [key _ a (by
      show algebraMap F (Af F) a - _ ∈ _
      rw [sub_self]; exact int_zero)]
    show Complex.exp (c * (_ - t (algebraMap F (Ainf F) a))) = 1
    rw [ht, sub_self, mul_zero, Complex.exp_zero]
  · have hn : (Module.finrank ℚ F : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
    refine ⟨pairA F (algebraMap F (Ainf F) (algebraMap ℚ F (1 / (2 * Module.finrank ℚ F)))) 0, ?_⟩
    show psiInf F ψ _ ≠ 1
    rw [hinf, ht, Algebra.trace_algebraMap, nsmul_eq_mul,
      show (Module.finrank ℚ F : ℚ) * (1 / (2 * Module.finrank ℚ F)) = 1 / 2 by field_simp,
      show 2 * (Real.pi : ℂ) * Complex.I * (((-1 : ℤ)) : ℂ) * ((1 / 2 : ℚ) : ℂ) = -(Real.pi * Complex.I) by
        push_cast; ring, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num

end Char

theorem exists_stdChar (D : D7) : ∃ ψ, IsStdChar D ψ (-1) := by
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D
  let t : Ainf D.host.F →+ ℂ := AddMonoidHom.mk' (fun x => ∑ ρ, θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E)))
    fun x y => by simp only [TensorProduct.add_tmul, map_add (f := _), Finset.sum_add_distrib]
  have hts : ∀ x, t x = (GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.trInf D x : ℂ) := GlobalTheory.DualPairCompare.sum_infFam θ hθ
  obtain ⟨ψ, h1, h2⟩ := exists_char t (continuous_finsetSum _ fun ρ _ => (hθ ρ).2)
    (fun x => by rw [hts, Complex.ofReal_im]) (fun a => by
      show ∑ ρ, θ ρ _ = _
      rw [GlobalTheory.StdRat.tmul_one_eq, Finset.sum_congr rfl fun ρ _ => (hθ ρ).1 _, GlobalTheory.StdRat.sum_tauE_eq_trace])
  exact ⟨ψ, h1, ⟨θ, hθ⟩, fun θ' hθ' x => by rw [h2, hts, GlobalTheory.DualPairCompare.sum_infFam θ' hθ']⟩

section Lattice

open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA FractionalIdeal

variable (D : D7)

end Lattice

variable {D : D7} {S T : HSp D} (C : Ctx S T)

end GlobalTheory.Ker.Model

end
