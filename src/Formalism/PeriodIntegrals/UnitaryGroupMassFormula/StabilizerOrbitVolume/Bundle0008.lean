module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0007
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.Bundle0006
public import Formalism.PeriodIntegrals.Bundle0019
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
public import Formalism.PeriodIntegrals.Bundle0009
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.StepBruhat
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.LintegralMulAvgComm
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.Bruhat
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0006
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TensTop
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.TensTopOf

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensInfSS
section
noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField
open scoped TensorProduct

theorem isReduced_tens_field (F E C : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [Field C] [Algebra F C] : IsReduced (C ⊗[F] E) := by
  have : Algebra.IsSeparable F E := Algebra.IsSeparable.of_integral F E
  have : Algebra.FormallyUnramified F E := Algebra.FormallyUnramified.of_isSeparable F E
  exact Algebra.FormallyUnramified.isReduced_of_field C (C ⊗[F] E)

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVSecSt
section
noncomputable section

namespace PI.VolStabSW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct

def SecGram : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (_hσ : ∀ x, σ (σ x) = x) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (_hJ : ∀ i j, σ (J j i) = J i j), J.det ≠ 0 →
    ∀ (R : Type) [CommRing R] [Algebra F R], IsSemisimpleRing (R ⊗[F] E) →
    ∀ (a : ℕ) (x : Fin a → Fin M → R ⊗[F] E), LinearIndependent (R ⊗[F] E) x →
      ∃ q : Fin M → Fin a → R ⊗[F] E, ∀ S : Matrix (Fin a) (Fin a) (R ⊗[F] E),
        S ∈ HermR R σ a →
        gramB R σ J x (fun j k => ∑ i', (algebraMap F (R ⊗[F] E) (1 / 2) * S i' j) * q k i') = S

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.EventuallyStruct
section
noncomputable section

namespace PI.VolStabSW

namespace CompGAux

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R S : Type} [CommRing R] [Algebra F R]
  [CommRing S] [Algebra F S] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem tmap_sigR (φ : R →ₐ[F] S) (x : R ⊗[F] E) :
    Algebra.TensorProduct.map φ (AlgHom.id F E) (PI.UJClassFin.sigR R σ x) =
      PI.UJClassFin.sigR S σ (Algebra.TensorProduct.map φ (AlgHom.id F E) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [PI.UJClassFin.sigR]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem tmap_inclR (φ : R →ₐ[F] S) (e : E) :
    Algebra.TensorProduct.map φ (AlgHom.id F E) (inclR R e) = inclR S e := by
  simp [inclR]

end Gen

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)

end Loc

end CompGAux

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensHSt
section
noncomputable section

namespace PI.VolStabSW

open MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

def FibLatGen : Prop :=
  ∀ (V X Y : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X),
    μ.IsAddHaarMeasure → ν.IsAddHaarMeasure →
    ∀ (f : V → Y) (ι : X → Y), Function.Injective ι → ∀ (G : V → X), Continuous G →
    (∀ x, f x = ι (G x)) → ∀ (U : Set V) (B : Set X) (fib : X → Measure V),
    IsFibreFamily μ f ι U ν B fib → ∀ (T : X), B ∈ 𝓝 T →
    ∀ (L : AddSubgroup V), IsOpen (L : Set V) → IsCompact (L : Set V) →
    ∀ (Λ : ℕ → AddSubgroup V) (H : ℕ → AddSubgroup X), Λ 0 ≤ L →
      (∀ n, IsOpen (Λ n : Set V)) → (∀ n, IsCompact (Λ n : Set V)) → Antitone Λ →
      (∀ n, IsOpen (H n : Set X)) → (∀ n, IsCompact (H n : Set X)) →
      (∀ N' ∈ 𝓝 (0 : X), ∃ n, (H n : Set X) ⊆ N') →
    ∀ (P : Set V), P ⊆ L → (∀ y ∈ P, ∀ Z ∈ Λ 0, y + Z ∈ P) → IsOpen P → IsClosed P →
    ∀ Nb ∈ 𝓝 T, (∀ x ∈ P, G x ∈ Nb → x ∈ U) →
      (∀ y ∈ P, G y - T ∈ H 0 → ∃ D : V →+ X, (∀ n, (Λ n).map D = H n) ∧
        ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1)) →
      ∫ x, P.indicator (1 : V → ℂ) x ∂(fib T) =
        (((μ (P ∩ G ⁻¹' {z | z - T ∈ H 0})) / ν (H 0)).toReal : ℂ)

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.SdUniq
section
noncomputable section

namespace PI.VolStabSW

namespace SdUniqW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW

def ann {V : Type} (χ : V → V → ℂ) (L : Set V) : Set V := {y | ∀ x ∈ L, χ x y = 1}

section Lattice

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (χ : V → V → ℂ)
  (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y) (L : AddSubgroup V)


include hχ in
theorem transform_indicator (hLo : IsOpen (L : Set V)) (y : V) :
    ∫ x, (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y ∂μ =
      (ann χ L).indicator (fun _ => ((μ.real (L : Set V) : ℝ) : ℂ)) y := by
  classical
  by_cases hy : y ∈ ann χ L
  · rw [Set.indicator_of_mem hy]
    have e : (fun x => (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y) =
        (L : Set V).indicator (fun _ => (1 : ℂ)) := by
      funext x
      by_cases hx : x ∈ (L : Set V)
      · simp [Set.indicator, hx, hy x hx]
      · simp [Set.indicator, hx]
    rw [e, integral_indicator_const _ hLo.measurableSet]
    simp
  · rw [Set.indicator_apply, if_neg hy]
    simp only [ann, Set.mem_setOf_eq, not_forall] at hy
    obtain ⟨t, ht, hty⟩ := hy
    set f : V → ℂ := fun x => (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y with hf
    have key : ∫ x, f x ∂μ = χ t y * ∫ x, f x ∂μ := by
      calc ∫ x, f x ∂μ = ∫ x, f (t + x) ∂μ := (integral_add_left_eq_self f t).symm
        _ = ∫ x, χ t y * f x ∂μ := by
          congr 1
          funext x
          by_cases hx : x ∈ (L : Set V)
          · have htx : t + x ∈ L := L.add_mem ht hx
            have hx' : x ∈ L := hx
            simp [hf, Set.indicator, hx', htx, hχ]
          · have htx : t + x ∉ L := fun h => hx (by simpa using L.sub_mem h ht)
            have hx' : x ∉ L := hx
            simp [hf, Set.indicator, hx', htx]
        _ = χ t y * ∫ x, f x ∂μ := integral_const_mul _ _
    have h2 : (1 - χ t y) * ∫ x, f x ∂μ = 0 := by rw [sub_mul, one_mul, ← key, sub_self]
    rcases mul_eq_zero.mp h2 with h1 | h1
    · exact absurd (sub_eq_zero.mp h1).symm hty
    · exact h1


end Lattice

section Triv

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (χ : V → V → ℂ)

end Triv

section Nontriv

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

def DualAt {V : Type} [AddCommGroup V] [TopologicalSpace V] (B : V → V → Fv F v) : Prop :=
  ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧
    (∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ L, ∃ x' ∈ L, ∀ y, B x' y = s * B x y) ∧
    ∀ c : Fv F v, ∃ K, IsCompact K ∧
      {y | ∀ x ∈ L, B x y ∈ (fun s => c * s) '' (v.adicCompletionIntegers F : Set (Fv F v))} ⊆ K

theorem mem_of_psi (ψ0 : Fv F v → ℂ) (r0 t : Fv F v) (h0 : ψ0 r0 ≠ 1)
    (ht : ∀ s ∈ v.adicCompletionIntegers F, ψ0 (s * t) = 1) :
    t ∈ (fun s => r0 * s) '' (v.adicCompletionIntegers F : Set (Fv F v)) := by
  by_contra hn
  have ht0 : t ≠ 0 := fun h => hn ⟨0, zero_mem _, by simp [h]⟩
  have hs : r0 * t⁻¹ ∉ v.adicCompletionIntegers F := fun hs => h0 (by
    have := ht _ hs
    rwa [inv_mul_cancel_right₀ ht0] at this)
  have hs0 : r0 * t⁻¹ ≠ 0 := fun h => hs (by rw [h]; exact zero_mem _)
  have hr0 : r0 ≠ 0 := fun h => hs0 (by rw [h, zero_mul])
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, not_le] at hs
  have hlt := ((Valued.v : Valuation (Fv F v) _).one_lt_val_iff hs0).mp hs
  refine hn ⟨(r0 * t⁻¹)⁻¹, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (le_of_lt hlt), ?_⟩
  field_simp

end Nontriv

section Add

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

open Classical in
theorem singleV_add (v : HeightOneSpectrum (𝓞 F)) (r s : Fv F v) :
    singleV F v (r + s) = singleV F v r + singleV F v s := by
  apply Subtype.ext
  exact Pi.single_add v r s

theorem psiV_add (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (r s : Fv F v) :
    psiV F ψ v (r + s) = psiV F ψ v r * psiV F ψ v s := by
  have e : pairA F 0 (singleV F v (r + s)) =
      pairA F 0 (singleV F v r) + pairA F 0 (singleV F v s) := by
    rw [singleV_add]
    show ((0 : Ainf F), singleV F v r + singleV F v s) =
      ((0 : Ainf F) + 0, singleV F v r + singleV F v s)
    rw [add_zero]
  unfold psiV
  rw [e, AddChar.map_add_eq_mul]

theorem continuous_singleV (v : HeightOneSpectrum (𝓞 F)) : Continuous (singleV F v) := by
  classical
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
    Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
  let s0 : Fv F v → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
      (Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F)))) := fun y =>
    ⟨Pi.single v y, Filter.eventually_principal.2 fun w hw => by
      rw [Pi.single_eq_of_ne (by simpa using hw)]
      exact zero_mem _⟩
  have hc : Continuous s0 := by
    rw [RestrictedProduct.continuous_rng_of_principal_iff_forall]
    intro w
    by_cases hw : w = v
    · subst hw
      exact continuous_id.congr fun y => (Pi.single_eq_same _ _).symm
    · exact (continuous_const (y := (0 : Fv F w))).congr fun y => (Pi.single_eq_of_ne hw y).symm
  have e : singleV F v = fun y => RestrictedProduct.inclusion _ _ hS (s0 y) := by
    funext y
    apply RestrictedProduct.ext
    intro j
    rfl
  rw [e]
  exact (RestrictedProduct.continuous_inclusion hS).comp hc

theorem continuous_psiV (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (psiV F ψ v) := by
  unfold psiV
  exact hψ.comp (continuous_const.prodMk (continuous_singleV v))

variable (R : Type) [CommRing R] [Algebra F R]

theorem BR_add (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X T Y : Fin n → Fin M → R ⊗[F] E) : BR R σ J (T + X) Y = BR R σ J T Y + BR R σ J X Y := by
  simp only [BR, hR, Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem pairHerm_add (σ : E →ₐ[F] E) (n : ℕ) (S T U : HermR R σ n) :
    pairHerm R σ n (T + S) U = pairHerm R σ n T U + pairHerm R σ n S U := by
  simp only [pairHerm, AddSubgroup.coe_add, Matrix.add_apply, add_mul, Finset.sum_add_distrib,
    map_add, mul_add]

end Add

section ContY

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [T2Space R]

theorem continuous_trace_tens : Continuous (Algebra.trace R (R ⊗[F] E)) :=
  IsModuleTopology.continuous_of_linearMap _

end ContY

end SdUniqW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW SdUniqW

end PI.VolStabSW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAFTop
section
namespace PI.VolStabSW.TopoAF

theorem afTop_holds : PI.VolSemiDirect.W.Lc.AFTop := fun F _ _ =>
  ⟨inferInstance, inferInstance, inferInstance⟩

end PI.VolStabSW.TopoAF
end

