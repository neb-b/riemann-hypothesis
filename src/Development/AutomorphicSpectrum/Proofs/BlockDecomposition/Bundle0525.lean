module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0496
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0027
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0480
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0497
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0045
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0501
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0381
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0506
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0454
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilStabilizerIntegrable
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open NumberField IsDedekindDomain
open scoped HeckeCharacterZeroLocus.SiegelWeilU

namespace GlobalTheory.CompanionTheory.WhitFree.CoefLim

theorem repr_map {F E A B : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] (f : A →ₐ[F] B) {d : ℕ} (b : Module.Basis (Fin d) F E) (y : A ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis B b).repr (Algebra.TensorProduct.map f (AlgHom.id F E) y) k =
      f ((Algebra.TensorProduct.basis A b).repr y k) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp [map_add (f := _), hx, hy]

section Cont

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  [TopologicalSpace R] [IsTopologicalRing R]

theorem continuous_linear (L : (R ⊗[F] E) →ₗ[R] R) : Continuous L := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  exact IsModuleTopology.continuous_of_linearMap L

theorem continuous_entry (σ : E →ₐ[F] E) {n : ℕ} (a c : Fin n) :
    Continuous fun B : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n => (B : Matrix (Fin n) (Fin n) (R ⊗[F] E)) a c :=
  (continuous_id.matrix_elem a c).comp continuous_subtype_val

theorem continuous_trace_pair [FiniteDimensional F E] (σ : E →ₐ[F] E) {n : ℕ}
    (T : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    Continuous fun B : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n => Algebra.trace R (R ⊗[F] E)
      (Matrix.trace (T * (B : Matrix (Fin n) (Fin n) (R ⊗[F] E)))) := by
  have h : (fun B : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n => Algebra.trace R (R ⊗[F] E)
      (Matrix.trace (T * (B : Matrix (Fin n) (Fin n) (R ⊗[F] E))))) =
      fun B : HeckeCharacterZeroLocus.SiegelWeilU.HermR R σ n => ∑ a, ∑ c, (Algebra.trace R (R ⊗[F] E) ∘ₗ LinearMap.mulLeft R (T a c))
        ((B : Matrix (Fin n) (Fin n) (R ⊗[F] E)) c a) := by
    funext B
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.trace, Matrix.mul_apply, map_sum]
  rw [h]
  exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun c _ =>
    (continuous_linear _).comp (continuous_entry σ c a)

end Cont

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem mem_intH_iff (σ : E →ₐ[F] E) {d n : ℕ} (b : Module.Basis (Fin d) F E)
    (S : Finset (HeightOneSpectrum (𝓞 F))) (B : HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.AF F) σ n) :
    B ∈ intH σ b S ↔ ∀ v, v ∉ S → ∀ a i k, (HeckeCharacterZeroLocus.SiegelWeilU.sndA F ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr
      ((B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i) k)) v ∈ v.adicCompletionIntegers F := by
  have key : ∀ (v : HeightOneSpectrum (𝓞 F)) (a i : Fin n) (k : Fin d),
      (Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v) b).repr
        (HeckeCharacterZeroLocus.SiegelWeilU.projV v (HeckeCharacterZeroLocus.SiegelWeilU.projFin (fun a i => (B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i)) a i) k =
      (HeckeCharacterZeroLocus.SiegelWeilU.sndA F ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr
        ((B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i) k)) v := by
    intro v a i k
    simp only [HeckeCharacterZeroLocus.SiegelWeilU.projV, HeckeCharacterZeroLocus.SiegelWeilU.projFin]
    rw [repr_map, repr_map]
    rfl
  simp only [intH, HeckeCharacterZeroLocus.SiegelWeilU.latV, Set.mem_setOf_eq, key]

theorem measurableSet_intH (σ : E →ₐ[F] E) {d n : ℕ} (b : Module.Basis (Fin d) F E)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : MeasurableSet (intH (n := n) σ b S) := by
  haveI : BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.AF F) σ n) := ⟨rfl⟩
  haveI := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.placesCountable F
  have hset : intH (n := n) σ b S = ⋂ v : HeightOneSpectrum (𝓞 F), ⋂ _ : v ∉ S, ⋂ a : Fin n, ⋂ i : Fin n,
      ⋂ k : Fin d, {B : HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.AF F) σ n | (HeckeCharacterZeroLocus.SiegelWeilU.sndA F ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr
        ((B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i) k)) v ∈ v.adicCompletionIntegers F} := by
    ext B
    simp only [mem_intH_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [hset]
  refine MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => MeasurableSet.iInter fun a =>
    MeasurableSet.iInter fun i => MeasurableSet.iInter fun k => ?_
  have hO : IsOpen (v.adicCompletionIntegers F : Set (HeckeCharacterZeroLocus.SiegelWeilU.Fv F v)) := Valued.isOpen_valuationSubring _
  have hev : Continuous fun y : HeckeCharacterZeroLocus.SiegelWeilU.Af F => y v := RestrictedProduct.continuous_eval v
  have hsnd : Continuous (fun c : HeckeCharacterZeroLocus.SiegelWeilU.AF F => HeckeCharacterZeroLocus.SiegelWeilU.sndA F c) := continuous_snd
  have hc : Continuous fun B : HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.AF F) σ n => (HeckeCharacterZeroLocus.SiegelWeilU.sndA F ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr
      ((B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i) k)) v :=
    hev.comp (hsnd.comp ((continuous_linear (Finsupp.lapply k ∘ₗ
      (Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr.toLinearMap)).comp (continuous_entry σ a i)))
  exact (hO.preimage hc).measurableSet

theorem eventually_mem_intH (σ : E →ₐ[F] E) {d n : ℕ} (b : Module.Basis (Fin d) F E) (B : HeckeCharacterZeroLocus.SiegelWeilU.HermR (HeckeCharacterZeroLocus.SiegelWeilU.AF F) σ n) :
    ∀ᶠ S : Finset (HeightOneSpectrum (𝓞 F)) in Filter.atTop, B ∈ intH σ b S := by
  have hfin : ∀ (a i : Fin n) (k : Fin d), {v : HeightOneSpectrum (𝓞 F) |
      ¬ (HeckeCharacterZeroLocus.SiegelWeilU.sndA F ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr
        ((B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i) k)) v ∈ v.adicCompletionIntegers F}.Finite :=
    fun a i k => (HeckeCharacterZeroLocus.SiegelWeilU.sndA F ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr
        ((B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i) k)).2
  have hall : ∀ (a i : Fin n) (k : Fin d), ∀ᶠ S : Finset (HeightOneSpectrum (𝓞 F)) in Filter.atTop,
      ∀ v, v ∉ S → (HeckeCharacterZeroLocus.SiegelWeilU.sndA F ((Algebra.TensorProduct.basis (HeckeCharacterZeroLocus.SiegelWeilU.AF F) b).repr
        ((B : Matrix (Fin n) (Fin n) (HeckeCharacterZeroLocus.SiegelWeilU.AF F ⊗[F] E)) a i) k)) v ∈ v.adicCompletionIntegers F := by
    intro a i k
    filter_upwards [Filter.eventually_ge_atTop (hfin a i k).toFinset] with S hS v hv
    by_contra hcon
    exact hv (hS ((hfin a i k).mem_toFinset.2 hcon))
  have hall' := Filter.eventually_all.2 fun a : Fin n => Filter.eventually_all.2 fun i : Fin n =>
    Filter.eventually_all.2 fun k : Fin d => hall a i k
  filter_upwards [hall'] with S hS
  exact (mem_intH_iff σ b S B).2 fun v hv a i k => hS a i k v hv

end Adelic

theorem coefS_tendsto : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 0 < n → 2 * n < M → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (dx : Measure (Fin n → Fin M → AF F ⊗[F] E)) (db : Measure (HermR (AF F) σ n)) (d : ℕ) (b : Module.Basis (Fin d) F E) (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ), Integrable (starN σ J ψ dx Φ) db → ∀ T : Matrix (Fin n) (Fin n) E, Filter.Tendsto (fun S => coefS σ J ψ dx db Φ T b S) Filter.atTop (nhds (coefN σ J ψ dx db Φ T)) := by
  intro F E _ _ _ _ _ σ _ M J _ n _ _ ψ hψ dx db d b Φ hI T
  haveI : BorelSpace (HermR (AF F) σ n) := ⟨rfl⟩
  haveI := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.placesCountable F
  obtain ⟨hψc, hψn, -, -⟩ := hψ
  have hchar : Continuous fun B : HermR (AF F) σ n =>
      ψ (-(algebraMap F (AF F) (1 / 2) * Algebra.trace (AF F) (AF F ⊗[F] E)
        (Matrix.trace (T.map (inclR (AF F)) * (B : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)))))) :=
    hψc.comp ((continuous_const.mul (continuous_trace_pair σ _)).neg)
  have hf := hI.aestronglyMeasurable.mul hchar.aestronglyMeasurable
  unfold coefS coefN
  refine tendsto_integral_filter_of_dominated_convergence (fun B => ‖starN σ J ψ dx Φ B‖) ?_ ?_ hI.norm ?_
  · refine Filter.Eventually.of_forall fun S => ?_
    have hind : Measurable ((intH (n := n) σ b S).indicator (fun _ => (1 : ℂ))) :=
      measurable_const.indicator (measurableSet_intH σ b S)
    exact hind.aestronglyMeasurable.mul hf
  · refine Filter.Eventually.of_forall fun S => Filter.Eventually.of_forall fun B => ?_
    have h1 : ‖(intH (n := n) σ b S).indicator (fun _ => (1 : ℂ)) B‖ ≤ 1 := by
      by_cases h : B ∈ intH (n := n) σ b S <;> simp [h]
    rw [norm_mul, norm_mul, hψn, mul_one]
    exact mul_le_of_le_one_left (norm_nonneg _) h1
  · refine Filter.Eventually.of_forall fun B => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_mem_intH σ b B] with S hS
    simp only [Set.indicator_of_mem hS, one_mul]
    rfl

end GlobalTheory.CompanionTheory.WhitFree.CoefLim
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummablePeriodicBoundByDenominator
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Compare

theorem summable_comp_of_injective_prod {X Y Q : Type*} [Finite Q] {d : Y → ℝ}
    (hd : ∀ y, 0 ≤ d y) (hs : Summable d) (y : X → Y) (q : X → Q)
    (hinj : Function.Injective fun x => (y x, q x)) : Summable fun x => d (y x) := by
  have h1 : Summable (fun p : Y × Q => d p.1 * (fun _ : Q => (1 : ℝ)) p.2) :=
    Summable.mul_of_nonneg hs (Summable.of_finite) hd (fun _ => zero_le_one)
  have h2 := h1.comp_injective hinj
  simpa [Function.comp_def] using h2

theorem finite_quot_nsmul {M : Type*} [AddCommGroup M] [Module.Finite ℤ M] {τ : ℕ} (hτ : 0 < τ) :
    Finite (M ⧸ (nsmulAddMonoidHom τ : M →+ M).range) := by
  haveI : Module.Finite ℤ (M ⧸ (nsmulAddMonoidHom τ : M →+ M).range) :=
    Module.Finite.of_surjective (QuotientAddGroup.mk' _).toIntLinearMap
      (QuotientAddGroup.mk'_surjective _)
  apply Module.finite_of_fg_torsion
  intro x
  induction x using QuotientAddGroup.induction_on with
  | H m =>
    refine ⟨⟨(τ : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hτ.ne')⟩, ?_⟩
    have : ((τ : ℤ) • (m : M ⧸ (nsmulAddMonoidHom τ : M →+ M).range))
        = ((τ • m : M) : M ⧸ (nsmulAddMonoidHom τ : M →+ M).range) := by
      rw [natCast_zsmul]; rfl
    show ((τ : ℤ) • (m : M ⧸ (nsmulAddMonoidHom τ : M →+ M).range)) = 0
    rw [this, QuotientAddGroup.eq_zero_iff]
    exact ⟨m, rfl⟩

variable {F E : Type} [Field F] [Field E] [NumberField E] [Algebra F E]

theorem mem_hermO_iff (σ : E →ₐ[F] E) (n : ℕ) (c : hermE σ n) :
    c ∈ hermO σ n ↔ ∀ a b, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = c.1 a b := Iff.rfl

def toInt (σ : E →ₐ[F] E) (n : ℕ) : hermO σ n →+ Matrix (Fin n) (Fin n) (𝓞 E) where
  toFun c := Matrix.of fun a b => Classical.choose ((mem_hermO_iff σ n c.1).1 c.2 a b)
  map_zero' := by
    ext a b
    have h := Classical.choose_spec ((mem_hermO_iff σ n (0 : hermO σ n).1).1 (0 : hermO σ n).2 a b)
    refine Eq.trans h ?_
    change _ = algebraMap (𝓞 E) E 0
    rw [map_zero]
    rfl
  map_add' := by
    intro c d
    ext a b
    have h1 := Classical.choose_spec ((mem_hermO_iff σ n (c + d).1).1 (c + d).2 a b)
    have h2 := Classical.choose_spec ((mem_hermO_iff σ n c.1).1 c.2 a b)
    have h3 := Classical.choose_spec ((mem_hermO_iff σ n d.1).1 d.2 a b)
    refine Eq.trans h1 ?_
    change _ = algebraMap (𝓞 E) E (_ + _)
    rw [map_add (f := _)]
    exact Eq.trans rfl (Eq.symm (Eq.trans (congrArg₂ (· + ·) h2 h3) rfl))

theorem algebraMap_toInt (σ : E →ₐ[F] E) (n : ℕ) (c : hermO σ n) (a b : Fin n) :
    algebraMap (𝓞 E) E (toInt σ n c a b) = c.1.1 a b :=
  Classical.choose_spec ((mem_hermO_iff σ n c.1).1 c.2 a b)

theorem toInt_injective (σ : E →ₐ[F] E) (n : ℕ) : Function.Injective (toInt σ n) := by
  intro c d h
  apply Subtype.ext
  apply Subtype.ext
  ext a b
  rw [← algebraMap_toInt σ n c a b, ← algebraMap_toInt σ n d a b, h]

theorem finite_hermO (σ : E →ₐ[F] E) (n : ℕ) : Module.Finite ℤ (hermO σ n) :=
  Module.Finite.of_injective (toInt σ n).toIntLinearMap (toInt_injective σ n)

theorem Kc_le_add {n : ℕ} (c l : Matrix (Fin n) (Fin n) E)
    (hl : ∀ a b, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = l a b) : Kc c ≤ Kc (c + l) := by
  intro y hy i
  obtain ⟨o, ho⟩ := hy i
  choose m hm using hl
  refine ⟨o + ∑ j, m i j * y j, ?_⟩
  rw [Matrix.add_mulVec, Pi.add_apply, map_add (f := _), ho]
  congr 1
  simp [Matrix.mulVec, dotProduct, hm]

theorem delta_add {n : ℕ} (c l : Matrix (Fin n) (Fin n) E)
    (hl : ∀ a b, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = l a b) : delta (c + l) = delta c := by
  have h1 := Kc_le_add c l hl
  have h2 := Kc_le_add (c + l) (-l) (fun a b => by
    obtain ⟨o, ho⟩ := hl a b
    exact ⟨-o, by simp [ho]⟩)
  rw [add_neg_cancel_right] at h2
  unfold delta
  rw [le_antisymm h2 h1]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Compare

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua


open GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Compare in
theorem summable_quot_of_le_delta_rpow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (Λ : AddSubgroup (hermE σ n)) (t : F), t ≠ 0 → ∀ τ : ℕ, 0 < τ →
    (∀ c ∈ hermO σ n, ((τ : F) / t) • c ∈ Λ) →
    ∀ g : hermE σ n → ℝ, (∀ c, 0 ≤ g c) → (∀ c, ∀ l ∈ Λ, g (c + l) = g c) →
    ∀ C s : ℝ, (∀ c, g c ≤ C * (delta (t • c).1 : ℝ) ^ (-s)) →
    Summable (fun x : hermE σ n ⧸ hermO σ n => (delta (Quotient.out x).1 : ℝ) ^ (-s)) →
    Summable (fun x : hermE σ n ⧸ Λ => g (Quotient.out x)) := by
  intro F E _ _ _ _ _ σ n Λ t ht τ hτ hΛ g hg hper C s hb hsum
  haveI : Module.Finite ℤ (hermO σ n) := finite_hermO σ n
  haveI := finite_quot_nsmul (M := hermO σ n) hτ
  let y : hermE σ n ⧸ Λ → hermE σ n ⧸ hermO σ n :=
    fun x => QuotientAddGroup.mk (t • Quotient.out x)
  have hmem : ∀ x, t • Quotient.out x - Quotient.out (y x) ∈ hermO σ n := by
    intro x
    have h : (QuotientAddGroup.mk (Quotient.out (y x)) : hermE σ n ⧸ hermO σ n)
        = QuotientAddGroup.mk (t • Quotient.out x) := QuotientAddGroup.out_eq' (y x)
    have := QuotientAddGroup.eq.1 h
    rwa [neg_add_eq_sub] at this
  let w : hermE σ n ⧸ Λ → hermO σ n := fun x => ⟨_, hmem x⟩
  let q : hermE σ n ⧸ Λ → hermO σ n ⧸ (nsmulAddMonoidHom τ : hermO σ n →+ hermO σ n).range :=
    fun x => QuotientAddGroup.mk (w x)
  have hinj : Function.Injective fun x => (y x, q x) := by
    intro x x' h
    have hy : y x = y x' := congrArg Prod.fst h
    have hq : q x = q x' := congrArg Prod.snd h
    obtain ⟨c, hc⟩ := QuotientAddGroup.eq.1 hq
    have hc' : τ • (c.1 : hermE σ n) = t • (Quotient.out x' - Quotient.out x) := by
      have := congrArg Subtype.val hc
      simp only [nsmulAddMonoidHom_apply, AddSubgroup.coe_add, AddSubgroup.coe_neg,
        AddSubgroup.coe_nsmul] at this
      rw [this]
      simp only [w, hy, smul_sub]
      abel
    have hd : Quotient.out x' - Quotient.out x = ((τ : F) / t) • (c.1 : hermE σ n) := by
      rw [div_eq_inv_mul, mul_smul, Nat.cast_smul_eq_nsmul F τ, hc', smul_smul,
        inv_mul_cancel₀ ht, one_smul]
    have hmemΛ : Quotient.out x' - Quotient.out x ∈ Λ := hd ▸ hΛ _ c.2
    rw [← QuotientAddGroup.out_eq' x, ← QuotientAddGroup.out_eq' x']
    apply QuotientAddGroup.eq.2
    rwa [neg_add_eq_sub]
  have hdnn : ∀ z : hermE σ n ⧸ hermO σ n,
      0 ≤ (delta (Quotient.out z).1 : ℝ) ^ (-s) := fun z => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hs := summable_comp_of_injective_prod hdnn hsum y q hinj
  refine Summable.of_nonneg_of_le (fun x => hg _) (fun x => ?_) (hs.mul_left |C|)
  have hdelta : delta (t • Quotient.out x).1 = delta (Quotient.out (y x)).1 := by
    have hl : ∀ a b, ∃ o : 𝓞 E, algebraMap (𝓞 E) E o = (w x).1.1 a b := (w x).2
    rw [← delta_add (Quotient.out (y x)).1 (w x).1.1 hl]
    congr 1
    simp [w]
  refine (hb _).trans ?_
  rw [hdelta]
  exact mul_le_mul_of_nonneg_right (le_abs_self C) (hdnn _)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TupleArchimedeanComplexCoordinates
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.TupHaar

theorem tup_coord_haar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (e : Ainf F ≃+* (InfinitePlace F → ℝ)) (τ : InfinitePlace F → (E →+* ℂ))
  (Θ : Ainf F ⊗[F] E ≃+* (InfinitePlace F → ℂ)), IsCoord σ e τ Θ →
  ∀ n M : ℕ, ∃ Φ : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (InfinitePlace F → Fin n → Fin M → ℂ),
    (∀ X, Φ X = tupC Θ X) ∧ Continuous Φ ∧ Continuous Φ.symm ∧
    ∀ μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E), μ.IsAddHaarMeasure →
      (μ.map Φ).IsAddHaarMeasure ∧ ∀ g : (InfinitePlace F → Fin n → Fin M → ℂ) → ℂ, ∫ X, g (Φ X) ∂μ = ∫ Y, g Y ∂(μ.map Φ) := by
  intro F E _ _ _ _ _ σ _ e τ Θ hco n M
  have hΘ : IsHomeomorph Θ := hco.1
  have hΘc : Continuous Θ := hΘ.continuous
  have hs : Continuous (Θ.symm : (InfinitePlace F → ℂ) → Ainf F ⊗[F] E) := by
    have h := (IsHomeomorph.homeomorph (⇑Θ) hΘ).symm.continuous
    convert h using 1
    funext y
    apply Θ.injective
    rw [RingEquiv.apply_symm_apply]
    exact ((IsHomeomorph.homeomorph (⇑Θ) hΘ).apply_symm_apply y).symm
  let Φ : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (InfinitePlace F → Fin n → Fin M → ℂ) :=
    { toFun := fun X w a i => Θ (X a i) w
      invFun := fun Y a i => Θ.symm (fun w => Y w a i)
      left_inv := fun X => by funext a i; simp
      right_inv := fun Y => by funext w a i; simp
      map_add' := fun X X' => by funext w a i; simp }
  have hc' : Continuous (fun (X : Fin n → Fin M → Ainf F ⊗[F] E) (w : InfinitePlace F) (a : Fin n)
      (i : Fin M) => Θ (X a i) w) := by fun_prop
  have hcs' : Continuous (fun (Y : InfinitePlace F → Fin n → Fin M → ℂ) (a : Fin n) (i : Fin M) =>
      Θ.symm (fun w => Y w a i)) := by fun_prop
  have hc : Continuous Φ := hc'
  have hcs : Continuous Φ.symm := hcs'
  refine ⟨Φ, fun X => rfl, hc, hcs, fun μ hμ => ?_⟩
  haveI := hμ
  refine ⟨AddEquiv.isAddHaarMeasure_map μ Φ hc hcs, fun g => ?_⟩
  let h : (Fin n → Fin M → Ainf F ⊗[F] E) ≃ₜ (InfinitePlace F → Fin n → Fin M → ℂ) :=
    ⟨Φ.toEquiv, hc, hcs⟩
  exact (h.measurableEmbedding.integral_map g).symm

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.TupHaar
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRankExtensionBound
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenUniq

theorem nonempty_equiv_of_generic_subquotients (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (hψ : Continuous ψ)
    (N : ℕ) {V W₁ W₂ : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W₁] [Module ℂ W₁]
    [AddCommGroup W₂] [Module ℂ W₂] (ρ : Representation ℂ (GL (Fin N) k) V)
    (π : Representation ℂ (GL (Fin N) k) W₁) (σ : Representation ℂ (GL (Fin N) k) W₂)
    (hρ : IsSmooth ρ)
    (hrank : Module.rank ℂ (TwJacquet ρ (unipB k (Fin N)) (whitChar ψ N)) ≤ 1)
    (hπ : π.IsIrreducible) (hσ : σ.IsIrreducible)
    (hπρ : IsSubquotient π ρ) (hσρ : IsSubquotient σ ρ)
    (hgπ : IsGenericFor ψ π) (hgσ : IsGenericFor ψ σ) : Nonempty (π.Equiv σ) := by
  obtain ⟨A, B, hBA, ⟨e₁⟩⟩ := _root_.GlobalTheory.CompanionTheory.SubquotPres.exists_equiv_subQuot ρ π hπρ
  obtain ⟨C, D, hDC, ⟨e₂⟩⟩ := _root_.GlobalTheory.CompanionTheory.SubquotPres.exists_equiv_subQuot ρ σ hσρ
  have hiAB : (subQuot A B).IsIrreducible := GlobalTheory.Parabolic.isIrreducible_of_equiv e₁ hπ
  have hiCD : (subQuot C D).IsIrreducible := GlobalTheory.Parabolic.isIrreducible_of_equiv e₂ hσ
  have hAB := (_root_.GlobalTheory.CompanionTheory.PRep.WhitQuot.isGenericFor_subQuot_iff k ψ hψ N ρ hρ A B hBA).1 (IsGenericFor.of_equiv hgπ e₁)
  have hCD := (_root_.GlobalTheory.CompanionTheory.PRep.WhitQuot.isGenericFor_subQuot_iff k ψ hψ N ρ hρ C D hDC).1 (IsGenericFor.of_equiv hgσ e₂)
  obtain ⟨e⟩ := GlobalTheory.T.nonempty_equiv_subQuot_of_not_le_sup ρ (twKer ρ (unipB k (Fin N)) (whitChar ψ N)) hrank
    (_root_.GlobalTheory.CompanionTheory.PRep.WhitSup.sup_inf_twKer_le k ψ hψ N ρ hρ) A B C D hBA hDC hiAB hiCD hAB hCD
  exact ⟨(e₁.trans e).trans e₂.symm⟩

end GlobalTheory.CompanionTheory.GenUniq
end

