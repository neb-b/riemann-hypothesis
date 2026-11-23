module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.FockSt
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0008

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.FinLift
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.finLift :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), FinLift W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ k
  obtain ⟨κ, -, hκ⟩ := finTr F E D
  refine ⟨TR.finRep F 2 (κ k) f, π.stable (.fin (κ k)) f hf, W.L (finGL E 2 k) φ,
    (fockSt F E D W).fin k φ hφ, fun h => ?_⟩
  have e : (fun x => f.1 (x * dM (nu F (finGL E 2 k)))) = (TR.finRep F 2 (κ k) f).1 := by
    funext x
    rw [hκ k]
    rfl
  rw [transl F E D W M f.1 φ h (finGL E 2 k), e]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.FiniteFamilyOfCompact
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem finite_family_of_compact {X T V : Type} [TopologicalSpace X] [AddCommGroup T] [Module ℂ T]
    (ev : V → T →ₗ[ℂ] ℂ) (hev : ∀ t : T, (∀ v, ev v t = 0) → t = 0)
    (U : Submodule ℂ T) [FiniteDimensional ℂ U] (K : Set X) (hK : IsCompact K) (f : X → T)
    (hf : ∀ k ∈ K, f k ∈ U) (hc : ∀ v, ContinuousOn (fun k => ev v (f k)) K) :
    ∃ (n : ℕ) (e : Fin n → T), ∀ k ∈ K, ∃ c : Fin n → ℂ, (∀ i, ‖c i‖ ≤ 1) ∧ f k = ∑ i, c i • e i := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let r : V → Module.Dual ℂ U := fun v => (ev v).domRestrict U
  let S : Submodule ℂ (Module.Dual ℂ U) := Submodule.span ℂ (Set.range r)
  have hS : S = ⊤ := by
    have hco : S.dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      rw [Submodule.mem_dualCoannihilator] at hu
      have : (u : T) = 0 := hev _ fun v => hu (r v) (Submodule.subset_span ⟨v, rfl⟩)
      simpa using this
    have := Subspace.dualCoannihilator_dualAnnihilator_eq (W := S)
    rw [hco] at this
    rw [← this]
    simp
  let g : K → U := fun k => ⟨f k.1, hf k.1 k.2⟩
  have hcont : ∀ l : Module.Dual ℂ U, Continuous fun k : K => l (g k) := by
    intro l
    have hl : l ∈ S := hS ▸ Submodule.mem_top
    induction hl using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, rfl⟩ := hx
      exact continuousOn_iff_continuous_restrict.mp (hc v)
    | zero => simpa using continuous_const
    | add x y _ _ hx hy =>
      change Continuous fun k : K => x (g k) + y (g k)
      exact hx.add hy
    | smul a x _ hx =>
      change Continuous fun k : K => a * x (g k)
      exact continuous_const.mul hx
  let b := Module.finBasis ℂ U
  have hbd : ∀ i, ∃ R : ℝ, 0 < R ∧ ∀ k : K, ‖b.coord i (g k)‖ ≤ R := by
    intro i
    obtain ⟨R, hR⟩ := isCompact_univ.exists_bound_of_continuousOn (hcont (b.coord i)).continuousOn
    exact ⟨max R 1, by positivity, fun k => (hR k (Set.mem_univ _)).trans (le_max_left _ _)⟩
  choose R hR0 hR using hbd
  refine ⟨_, fun i => (R i : ℂ) • ((b i : U) : T), fun k hk => ?_⟩
  refine ⟨fun i => b.coord i (g ⟨k, hk⟩) / (R i : ℂ), fun i => ?_, ?_⟩
  · rw [norm_div, Complex.norm_real, Real.norm_of_nonneg (hR0 i).le]
    exact (div_le_one (hR0 i)).mpr (hR i _)
  · have h : ((∑ i, b.repr (g ⟨k, hk⟩) i • b i : U) : T) = f k := by rw [b.sum_repr]
    rw [AddSubmonoidClass.coe_finsetSum] at h
    have h2 : f k = ∑ i, b.coord i (g ⟨k, hk⟩) • ((b i : U) : T) := h.symm
    rw [h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hne : (R i : ℂ) ≠ 0 := by exact_mod_cast (hR0 i).ne'
    rw [smul_smul, div_mul_cancel₀ _ hne]

theorem UpperTheory.ConvolutionTheory.R2.Ff.omFin :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), OmFin W := by
  intro F E _ _ _ _ _ _ _ D W φ hφ
  obtain ⟨hKc, -⟩ := iwa F
  obtain ⟨U, -, hfd, hmem⟩ := (fockSt F E D W).om φ hφ (KK F) hKc fun k hk => hk.1
  let ev : V4 F → S4 F →ₗ[ℂ] ℂ := fun v =>
    { toFun := fun t => t.1 v, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  refine finite_family_of_compact ev (fun t ht => Subtype.ext (funext ht)) U (KK F) hKc
    (fun k => W.Om k φ) hmem fun v => ?_
  have h := W.cont φ
  exact (h.comp (Continuous.prodMk continuous_id continuous_const : Continuous fun k : G1 F => (k, v))).continuousOn
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.RedLift
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.redLift :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (M : Meas F) (π : TR.CuspSub F 2), RedLift W M π := by
  intro F E _ _ _ _ _ _ _ D W M π f hf φ hφ h
  obtain ⟨κ, -, hκ⟩ := UpperTheory.ConvolutionTheory.R2.Ff.finTr F E D
  have ht := UpperTheory.ConvolutionTheory.R2.Ff.transl F E D W M
  have hF := (UpperTheory.ConvolutionTheory.R2.fockSt F E D W).fin
  obtain ⟨y₀, k, hh⟩ : ∃ y₀ k, h = infGL E 2 y₀ * finGL E 2 k := ⟨_, _, (infGL_mul_finGL h).symm⟩
  have hv : ∀ x, (TR.finRep F 2 (κ k) f).1 x = f.1 (x * dM (nu F (finGL E 2 k))) := fun x => by
    rw [hκ k]; rfl
  refine ⟨TR.finRep F 2 (κ k) f, π.stable (.fin (κ k)) f hf, W.L (finGL E 2 k) φ, hF k φ hφ, y₀, k, hh, rfl, hv, ?_⟩
  intro φ₁ y
  have e : h * infGL E 2 y = infGL E 2 (y₀ * y) * finGL E 2 k := by
    rw [hh, map_mul, mul_assoc, mul_assoc, infGL_comm]
  have hfun : (TR.finRep F 2 (κ k) f).1 = fun x => f.1 (x * dM (nu F (finGL E 2 k))) := funext hv
  rw [e, ht f.1 φ₁ (infGL E 2 (y₀ * y)) (finGL E 2 k), hfun]
end

