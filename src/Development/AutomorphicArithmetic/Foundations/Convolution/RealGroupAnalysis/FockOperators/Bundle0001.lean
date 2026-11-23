module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.InfinitesimalCharacterPullback.HasInfCharPullSub
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.InfEmbGrpEq
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.ActMat

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.CapAbs
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private theorem qdet_fin_two {V : Type} [AddCommGroup V] [Module ℂ V] (X : Fin 2 → Fin 2 → Module.End ℂ V) (u : ℂ) :
    Formalism.REAL.qdet X u = (algebraMap ℂ (Module.End ℂ V) u + X 0 0) * (algebraMap ℂ (Module.End ℂ V) (u - 1) + X 1 1) - X 1 0 * X 0 1 := by
  have hp : (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} := by decide
  rw [Formalism.REAL.qdet, Formalism.REAL.qminor, hp, Finset.sum_pair (by decide)]
  simp [Formalism.REAL.Tm, List.ofFn_succ, sub_eq_add_neg]

private theorem four_qdet {V : Type} [AddCommGroup V] [Module ℂ V] (X : Fin 2 → Fin 2 → Module.End ℂ V)
    (hX : Formalism.REAL.GlRel X) (u : ℂ) (w : V) :
    (4 : ℂ) • Formalism.REAL.qdet X u w = ((2 * u - 1) ^ 2 - 1) • w + (2 * (2 * u - 1)) • (X 0 0 + X 1 1) w
      + (X 0 0 + X 1 1) ((X 0 0 + X 1 1) w)
      - ((X 0 0 - X 1 1) ((X 0 0 - X 1 1) w) + (2 : ℂ) • (X 0 1 (X 1 0 w) + X 1 0 (X 0 1 w))) := by
  have r1 : X 0 0 (X 1 1 w) - X 1 1 (X 0 0 w) = 0 := by
    simpa using LinearMap.congr_fun (hX 0 0 1 1) w
  have r2 : X 0 1 (X 1 0 w) - X 1 0 (X 0 1 w) = X 0 0 w - X 1 1 w := by
    simpa using LinearMap.congr_fun (hX 0 1 1 0) w
  rw [qdet_fin_two]
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, Module.algebraMap_end_apply, map_add (f := _),
    map_sub, map_smul]
  linear_combination (norm := module) (2 : ℂ) • r1 + (2 : ℂ) • r2

theorem UpperTheory.ConvolutionTheory.R2.Fo.capAbs :
    ∀ (V S T : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup S] [Module ℂ S] [AddCommGroup T] [Module ℂ T]
    (V₀ : Submodule ℂ V) (S₀ : Submodule ℂ S) (Λ : V →ₗ[ℂ] S →ₗ[ℂ] T) (E : Fin 2 → Fin 2 → Module.End ℂ V) (P : Fin 2 → Fin 2 → Module.End ℂ T)
    (a : Fin 2 → Fin 2 → Module.End ℂ S) (e f h : Module.End ℂ S), Formalism.REAL.GlRel E → Formalism.REAL.GlRel P →
    (∀ i j, ∀ v ∈ V₀, E i j v ∈ V₀) → (∀ i j, ∀ s ∈ S₀, a i j s ∈ S₀) → (∀ s ∈ S₀, e s ∈ S₀) → (∀ s ∈ S₀, f s ∈ S₀) →
    (∀ i j, ∀ v ∈ V₀, ∀ s ∈ S₀, P i j (Λ v s) = Λ v (a i j s) + if i = j then Λ (E 1 1 v) s else 0) →
    (∀ v ∈ V₀, ∀ s ∈ S₀, Λ v (e s) = -Λ (E 0 1 v) s) → (∀ v ∈ V₀, ∀ s ∈ S₀, Λ v (f s) = -Λ (E 1 0 v) s) →
    e * f - f * e = h → a 0 0 + a 1 1 = -h →
    (a 0 0 - a 1 1) * (a 0 0 - a 1 1) + 2 * (a 0 1 * a 1 0 + a 1 0 * a 0 1) = h * h + 2 * (e * f + f * e) →
    ∀ u, ∀ v ∈ V₀, ∀ s ∈ S₀, Formalism.REAL.qdet P u (Λ v s) = Λ (Formalism.REAL.qdet E u v) s := by
  intro V S T _ _ _ _ _ _ V₀ S₀ Λ E P a e f h hE hP hEV haS heS hfS hPΛ heΛ hfΛ hh hz hb u v hv s hs
  have hH : ∀ w, E 0 1 (E 1 0 w) - E 1 0 (E 0 1 w) = (E 0 0 - E 1 1) w := fun w => by
    simpa using LinearMap.congr_fun (hE 0 1 1 0) w
  have hef : ∀ v ∈ V₀, ∀ s ∈ S₀, Λ v (e (f s)) = Λ (E 1 0 (E 0 1 v)) s := fun v hv s hs => by
    rw [heΛ v hv _ (hfS s hs), hfΛ _ (hEV 0 1 v hv) s hs, neg_neg]
  have hfe : ∀ v ∈ V₀, ∀ s ∈ S₀, Λ v (f (e s)) = Λ (E 0 1 (E 1 0 v)) s := fun v hv s hs => by
    rw [hfΛ v hv _ (heS s hs), heΛ _ (hEV 1 0 v hv) s hs, neg_neg]
  have hhS : ∀ s ∈ S₀, h s ∈ S₀ := fun s hs => by
    rw [← hh]
    exact S₀.sub_mem (heS _ (hfS s hs)) (hfS _ (heS s hs))
  have hHV : ∀ v ∈ V₀, (E 0 0 - E 1 1) v ∈ V₀ := fun v hv =>
    V₀.sub_mem (hEV 0 0 v hv) (hEV 1 1 v hv)
  have hZV : ∀ v ∈ V₀, (E 0 0 + E 1 1) v ∈ V₀ := fun v hv =>
    V₀.add_mem (hEV 0 0 v hv) (hEV 1 1 v hv)
  have hhΛ : ∀ v ∈ V₀, ∀ s ∈ S₀, Λ v (h s) = -Λ ((E 0 0 - E 1 1) v) s := fun v hv s hs => by
    rw [← hh, ← hH v, LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, map_sub, hef v hv s hs,
      hfe v hv s hs, map_sub, LinearMap.sub_apply, neg_sub]
  have hZ : ∀ v ∈ V₀, ∀ s ∈ S₀, (P 0 0 + P 1 1) (Λ v s) = Λ ((E 0 0 + E 1 1) v) s := fun v hv s hs => by
    have h1 : a 0 0 s + a 1 1 s = -h s := by simpa using LinearMap.congr_fun hz s
    have h2 : Λ v (a 0 0 s) + Λ v (a 1 1 s) = Λ ((E 0 0 - E 1 1) v) s := by
      rw [← map_add (f := _), h1, map_neg, hhΛ v hv s hs, neg_neg]
    simp only [LinearMap.add_apply, hPΛ _ _ v hv s hs, if_true, map_add (f := _)]
    simp only [LinearMap.sub_apply, map_sub] at h2
    linear_combination (norm := module) h2
  have hHP : ∀ v ∈ V₀, ∀ s ∈ S₀, (P 0 0 - P 1 1) (Λ v s) = Λ v ((a 0 0 - a 1 1) s) := fun v hv s hs => by
    simp only [LinearMap.sub_apply, hPΛ _ _ v hv s hs, if_true, map_sub]
    abel
  have hA : ∀ s ∈ S₀, (a 0 0 - a 1 1) s ∈ S₀ := fun s hs => S₀.sub_mem (haS 0 0 s hs) (haS 1 1 s hs)
  have hBr : (P 0 0 - P 1 1) ((P 0 0 - P 1 1) (Λ v s)) + (2 : ℂ) • (P 0 1 (P 1 0 (Λ v s)) + P 1 0 (P 0 1 (Λ v s)))
      = Λ ((E 0 0 - E 1 1) ((E 0 0 - E 1 1) v) + (2 : ℂ) • (E 0 1 (E 1 0 v) + E 1 0 (E 0 1 v))) s := by
    have p10 : P 1 0 (Λ v s) = Λ v (a 1 0 s) := by simpa using hPΛ 1 0 v hv s hs
    have p01 : P 0 1 (Λ v s) = Λ v (a 0 1 s) := by simpa using hPΛ 0 1 v hv s hs
    have p01' : P 0 1 (Λ v (a 1 0 s)) = Λ v (a 0 1 (a 1 0 s)) := by
      simpa using hPΛ 0 1 v hv _ (haS 1 0 s hs)
    have p10' : P 1 0 (Λ v (a 0 1 s)) = Λ v (a 1 0 (a 0 1 s)) := by
      simpa using hPΛ 1 0 v hv _ (haS 0 1 s hs)
    have hb' : (a 0 0 - a 1 1) ((a 0 0 - a 1 1) s) + (2 : ℂ) • (a 0 1 (a 1 0 s) + a 1 0 (a 0 1 s))
        = h (h s) + (2 : ℂ) • (e (f s) + f (e s)) := by
      have := LinearMap.congr_fun hb s
      simp only [two_mul, LinearMap.add_apply, Module.End.mul_apply] at this
      rw [two_smul, two_smul]
      exact this
    rw [hHP v hv s hs, hHP v hv _ (hA s hs), p10, p01, p01', p10', ← map_add (f := _), ← map_smul, ← map_add (f := _), hb', map_add (f := _), map_smul,
      map_add, hef v hv s hs, hfe v hv s hs, hhΛ v hv _ (hhS s hs), hhΛ _ (hHV v hv) s hs, neg_neg,
      map_add, map_smul, map_add, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.add_apply, add_comm (Λ (E 1 0 _) s)]
  have key : (4 : ℂ) • Formalism.REAL.qdet P u (Λ v s) = (4 : ℂ) • Λ (Formalism.REAL.qdet E u v) s := by
    have k2 : (4 : ℂ) • Λ (Formalism.REAL.qdet E u v) s = Λ ((4 : ℂ) • Formalism.REAL.qdet E u v) s := by
      rw [map_smul, LinearMap.smul_apply]
    rw [k2, four_qdet P hP u, four_qdet E hE u v, hBr, hZ v hv s hs, hZ _ (hZV v hv) s hs]
    simp only [map_add (f := _), map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply]
  exact smul_right_injective T (by norm_num : (4 : ℂ) ≠ 0) key
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.Capelli
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.capelli :
    ∀ (A : Type) [Ring A] (X D a : Fin 2 → Fin 2 → A) (q Δ h : A), (∀ i j k l, X i j * X k l = X k l * X i j) → (∀ i j k l, D i j * D k l = D k l * D i j) →
    (∀ i j k l, D i j * X k l = X k l * D i j + if i = k ∧ j = l then 1 else 0) →
    (∀ i j, a i j = -(if i = j then 1 else 0) - ∑ b, X j b * D i b) → q = X 0 1 * X 1 0 - X 0 0 * X 1 1 → Δ = D 0 1 * D 1 0 - D 0 0 * D 1 1 →
    h = (∑ i, ∑ j, X i j * D i j) + 2 →
    Δ * q - q * Δ = h ∧ a 0 0 + a 1 1 = -h ∧
    (a 0 0 - a 1 1) * (a 0 0 - a 1 1) + 2 * (a 0 1 * a 1 0 + a 1 0 * a 0 1) = h * h - 2 * (q * Δ + Δ * q) := by
  intro A _ X D a q Δ h hX hD hDX ha hq hΔ hh
  have hDX' : ∀ i j k l z, D i j * (X k l * z) = X k l * (D i j * z) + if i = k ∧ j = l then z else 0 := by
    intro i j k l z
    rw [← mul_assoc, hDX, add_mul, mul_assoc]
    split_ifs <;> simp
  have hX' : ∀ i j k l z, X i j * (X k l * z) = X k l * (X i j * z) := by
    intro i j k l z
    rw [← mul_assoc, hX, mul_assoc]
  have h2 : (2 : A) = 1 + 1 := by norm_num
  have h01 : ¬ ((0 : Fin 2) = 1) := by decide
  have h10 : ¬ ((1 : Fin 2) = 0) := by decide
  subst hq hΔ hh
  simp only [ha, Fin.sum_univ_two, h2, h01, h10, if_true, if_false]
  refine ⟨?_, ?_, ?_⟩
  all_goals
    try simp only [mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, neg_zero, zero_sub, neg_neg, mul_one, one_mul, mul_assoc, hDX, hDX', h01, h10, and_self, and_true, true_and, and_false, false_and, if_true, if_false, add_zero,
      hX 1 1 0 0, hX 1 1 0 1, hX 1 1 1 0, hX 1 0 0 0, hX 1 0 0 1, hX 0 1 0 0,
      hX' 1 1 0 0, hX' 1 1 0 1, hX' 1 1 1 0, hX' 1 0 0 0, hX' 1 0 0 1, hX' 0 1 0 0,
      hD 1 1 0 0, hD 1 1 0 1, hD 1 1 1 0, hD 1 0 0 0, hD 1 0 0 1, hD 0 1 0 0]
  all_goals abel
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.ContinuousPlaceEmbedReal
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private theorem infPartPi_add' {F : Type} [Field F] [NumberField F] (x y : V4 F) :
    infPartPi (x + y) = infPartPi x + infPartPi y := by
  funext j
  simp only [infPartPi, Pi.add_apply, homeomorphMixedSpace_apply]
  exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) (x j).1 (y j).1

private theorem placeEmbedReal_add {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) (s t : ℝ) :
    at1 w (s + t) = at1 w s + at1 w t := by
  simp only [at1, Pi.single_add, map_add (f := _)]

private theorem continuous_placeEmbedReal {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) :
    Continuous (at1 w : ℝ → A F) := by
  have h : Continuous fun t : ℝ => (Pi.single w t : TR.Rinf F) := by
    refine continuous_pi fun u => ?_
    by_cases hu : u = w
    · subst hu; simp only [Pi.single_eq_same]; exact continuous_id
    · simpa [Pi.single_eq_of_ne hu] using continuous_const
  exact ((TR.continuous_infEq F).comp h).prodMk continuous_const

private theorem inf_line {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) (i : Fin 4)
    (v : V4 F) (t : ℝ) :
    infPartPi (v + Pi.single i (at1 w t)) = infPartPi v + t • infPartPi (Pi.single i (at1 w 1) : V4 F) := by
  let L : ℝ →+ (Fin 4 → mixedEmbedding.mixedSpace F) :=
    { toFun := fun t => infPartPi (Pi.single i (at1 w t) : V4 F)
      map_zero' := by
        have h0 : at1 w (0 : ℝ) = (0 : A F) := by simp [at1]
        rw [h0, Pi.single_zero]
        funext j
        simp only [infPartPi, Pi.zero_apply, homeomorphMixedSpace_apply]
        exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
      map_add' := fun s t => by
        rw [placeEmbedReal_add, Pi.single_add, infPartPi_add'] }
  have hL : Continuous L := by
    refine continuous_infPartPi.comp (continuous_pi fun j => ?_)
    by_cases hj : j = i
    · subst hj; simpa using continuous_placeEmbedReal w
    · simpa [Pi.single_eq_of_ne hj] using continuous_const
  have h := map_real_smul L hL t (1 : ℝ)
  rw [infPartPi_add']
  have e : t • (1 : ℝ) = t := by simp
  rw [e] at h
  exact congrArg (infPartPi v + ·) h

private theorem fin_line {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) (i : Fin 4)
    (v : V4 F) (t : ℝ) : finPartPi (v + Pi.single i (at1 w t)) = finPartPi v := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp only [finPartPi, Pi.add_apply, Pi.single_eq_same]
    change (v j).2 + 0 = (v j).2
    exact add_zero _
  · simp [finPartPi, Pi.single_eq_of_ne hj]

theorem UpperTheory.ConvolutionTheory.R2.Fo.dEx :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) (i : Fin 4) (φ : V4 F → ℂ), φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4) →
    ∃ φ' ∈ schwartzBruhatPi (K := F) (ι := Fin 4), ∀ v, HasDerivAt (fun t : ℝ => φ (v + Pi.single i (at1 w t))) (φ' v) 0 := by
  intro F _ _ _ w i φ hφ
  induction hφ using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨f, g, hg, rfl⟩ := hG
    set e := infPartPi (Pi.single i (at1 w 1) : V4 F) with he
    refine ⟨schwartzBruhatTensorPi (LineDeriv.lineDerivOpCLM ℂ (SchwartzMap (Fin 4 → mixedEmbedding.mixedSpace F) ℂ) e f) g,
      schwartzBruhatTensorPi_mem _ hg, fun v => ?_⟩
    have hfun : (fun t : ℝ => schwartzBruhatTensorPi f g (v + Pi.single i (at1 w t))) =
        fun t : ℝ => f (infPartPi v + t • e) * g (finPartPi v) := by
      funext t
      simp only [schwartzBruhatTensorPi, inf_line, fin_line, he]
    rw [hfun]
    have hline : HasDerivAt (fun t : ℝ => infPartPi v + t • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add (infPartPi v)
    have hf : HasFDerivAt (f : (Fin 4 → mixedEmbedding.mixedSpace F) → ℂ) (fderiv ℝ f (infPartPi v))
        (infPartPi v + (0 : ℝ) • e) :=
      by
        rw [zero_smul, add_zero]
        exact (f.differentiableAt).hasFDerivAt
    have hc := (hf.comp_hasDerivAt (0 : ℝ) hline).mul_const (g (finPartPi v))
    simpa [schwartzBruhatTensorPi, LineDeriv.lineDerivOpCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv] using hc
  | zero =>
    exact ⟨0, Submodule.zero_mem _, fun v => by simpa using hasDerivAt_const (0 : ℝ) (0 : ℂ)⟩
  | add G H _ _ hG hH =>
    obtain ⟨a, ha, ha'⟩ := hG
    obtain ⟨b, hb, hb'⟩ := hH
    exact ⟨a + b, Submodule.add_mem _ ha hb, fun v => (ha' v).add (hb' v)⟩
  | smul c G _ hG =>
    obtain ⟨a, ha, ha'⟩ := hG
    exact ⟨c • a, Submodule.smul_mem _ c ha, fun v => (ha' v).const_mul c⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.CoordMk
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

noncomputable section

namespace UpperTheory.ConvolutionTheory.R2.Fo

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E]

private theorem continuous_coordE (τ : E →+* ℂ) : Continuous (coord τ) :=
  AddMonoidHomClass.continuous_of_bound (coord τ) 1 fun x => by
    simpa using FieldIso.norm_coord_le τ x

private theorem continuous_infEqE_symm : Continuous (GlobalTheory.CuspRep.infEq E).symm :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)

private theorem continuous_infEqF_symm : Continuous (TR.infEq F).symm :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)

private theorem cw_rt (w : InfinitePlace F) (k : F) :
    cw w (rt k) = w.embedding k := by
  have h : TR.pInf F (rt k) w = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) k := by
    change InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)
      ((algebraMap F (A F) k).1 w) = _
    rw [AdeleRing.algebraMap_fst_apply, InfinitePlace.Completion.ringEquivRealOfIsReal_apply]
    exact InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe (IsTotallyReal.isReal w) (WithAbs.toAbs _ k)
  rw [cw, h, InfinitePlace.embedding_of_isReal_apply]

private theorem embedding_pl (τ : E →+* ℂ) (k : F) :
    (pl F τ).embedding k = τ (algebraMap F E k) := by
  have h : (pl F τ).IsReal := IsTotallyReal.isReal _
  have h' := InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 h)
  exact RingHom.congr_fun h' k

private theorem cw_rt_pl (τ : E →+* ℂ) (k : F) : cw (pl F τ) (rt k) = τ (algebraMap F E k) := by
  rw [cw_rt, embedding_pl]

private theorem coord_adeleMap (τ : E →+* ℂ) (a : A F) :
    coord τ (pInf E (AdeleBaseChange.adeleMap F E a)) = cw (pl F τ) a := by
  have key : (fun b : InfiniteAdeleRing F =>
        coord τ ((GlobalTheory.CuspRep.infEq E).symm (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := E) b))) =
      fun b => (((TR.infEq F).symm b (pl F τ) : ℝ) : ℂ) := by
    refine (InfiniteAdeleRing.denseRange_algebraMap F).equalizer
      ((continuous_coordE τ).comp (continuous_infEqE_symm.comp
        GroundTheory.Global.InfinitePlace.continuous_infiniteAdeleRingMap))
      (Complex.continuous_ofReal.comp ((continuous_apply _).comp continuous_infEqF_symm)) (funext fun k => ?_)
    have h1 := cw_rt_pl (E := E) τ k
    have h2 := coord_algebraMap τ (algebraMap F E k)
    simp only [Function.comp_apply]
    rw [GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap_algebraMap]
    exact h2.trans h1.symm
  exact congrFun key a.1

end UpperTheory.ConvolutionTheory.R2.Fo

open UpperTheory.ConvolutionTheory.R2.Fo in
theorem UpperTheory.ConvolutionTheory.R2.Fo.coordMk :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] (D : Dat F E), (∀ (τ : E →+* ℂ) u t, coord τ (pInf E (D.mkE u t)) = cw (pl F τ) u + τ D.θ * cw (pl F τ) t) ∧
    (∀ τ : E →+* ℂ, τ D.θ ^ 2 = cw (pl F τ) (rt D.δ) ∧ starRingEnd ℂ (τ D.θ) = -τ D.θ ∧ τ D.θ ≠ 0) ∧
    (∀ w, cw w (rt D.δ) ≠ 0) ∧ ∀ w, ∃ τ : E →+* ℂ, pl F τ = w := by
  intro F E _ _ _ _ _ _ _ D
  have hneg : ∀ w : InfinitePlace F, ∃ r : ℝ, r < 0 ∧ cw w (rt D.δ) = r := fun w =>
    ⟨InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) D.δ, D.neg _, by
      rw [cw_rt, InfinitePlace.embedding_of_isReal_apply]⟩
  have hsq : ∀ τ : E →+* ℂ, τ D.θ ^ 2 = cw (pl F τ) (rt D.δ) := fun τ => by
    rw [cw_rt_pl, ← map_pow, D.sq]
  refine ⟨fun τ u t => ?_, fun τ => ⟨hsq τ, ?_, ?_⟩, fun w => ?_, fun w => ?_⟩
  · rw [Dat.mkE, map_add (f := _), map_add (f := _), map_mul, map_mul, coord_adeleMap, coord_adeleMap, coord_algebraMap, mul_comm (cw _ t)]
  · obtain ⟨r, hr, e⟩ := hneg (pl F τ)
    have h := (hsq τ).trans e
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im] at hre him
    have h0 : (τ D.θ).re = 0 := by
      by_contra hc
      have : (τ D.θ).im = 0 := by
        have : (τ D.θ).re * (τ D.θ).im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hc
      rw [this] at hre
      nlinarith [mul_self_nonneg (τ D.θ).re]
    apply Complex.ext <;> simp [h0]
  · intro h0
    obtain ⟨r, hr, e⟩ := hneg (pl F τ)
    have h := (hsq τ).trans e
    rw [h0] at h
    have : (r : ℂ) = 0 := by simpa using h.symm
    exact hr.ne (by exact_mod_cast this)
  · obtain ⟨r, hr, e⟩ := hneg w
    rw [e]
    exact_mod_cast hr.ne
  · obtain ⟨W, hW⟩ := InfinitePlace.comap_surjective (k := F) (K := E) w
    refine ⟨W.embedding, ?_⟩
    rw [← hW]
    change InfinitePlace.mk (W.embedding.comp (algebraMap F E)) = W.comap (algebraMap F E)
    rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.CwSum
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private theorem cw_sum {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F)
    (a b : Fin 4 → A F) : cw w (∑ j, a j * b j) = ∑ j, cw w (a j) * cw w (b j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [cw, map_sum, map_mul, Finset.sum_apply, Pi.mul_apply, Complex.ofReal_sum, Complex.ofReal_mul]

theorem UpperTheory.ConvolutionTheory.R2.Fo.lX :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) (O : Ops F) (h : GL (Fin 2) (A E)) w i φ, W.L h (O.x w i φ) ∈ Submodule.span ℂ {χ : S4 F | ∃ w' j, χ = O.x w' j (W.L h φ) ∨ χ = O.d w' j (W.L h φ)} := by
  intro F E _ _ _ _ _ _ _ D W O h w i φ
  obtain ⟨ρ, hρ, -, -⟩ := UpperTheory.ConvolutionTheory.R2.D.actMat F E D
  have key : W.L h (O.x w i φ) = ∑ j, cw w ((ρ h⁻¹).val i j) • O.x w j (W.L h φ) := by
    apply Subtype.ext
    funext v
    have hs : ((∑ j, cw w ((ρ h⁻¹).val i j) • O.x w j (W.L h φ) : S4 F)).1 v
        = ∑ j, cw w ((ρ h⁻¹).val i j) * (O.x w j (W.L h φ)).1 v := by
      rw [Submodule.coe_sum, Finset.sum_apply]
      rfl
    rw [hs, W.L_apply, O.x_apply]
    simp only [O.x_apply, W.L_apply]
    have hi : D.act h⁻¹ v i = ∑ j, (ρ h⁻¹).val i j * v j := by
      rw [hρ]; rfl
    rw [hi, cw_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [key]
  refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, j, Or.inl rfl⟩)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FixGen
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private theorem psi_add {F : Type} [Field F] [NumberField F] (x y : A F) : ψ (x + y) = ψ x * ψ y := by
  simp only [ψ, AddChar.map_add_eq_mul, Circle.coe_mul]

private theorem quaternaryForm_add_left {F : Type} [Field F] [NumberField F] (δ : F) (y a v : V4 F) :
    B4 δ (y + a) v = B4 δ y v + B4 δ a v := by
  simp only [B4, Pi.add_apply]
  ring

private theorem bilinearFour_comm {F : Type} [Field F] [NumberField F] (δ : F) (y v : V4 F) :
    B4 δ y v = B4 δ v y := by
  simp only [B4]
  ring

private theorem quadraticForm_shift_expand {F : Type} [Field F] [NumberField F] (δ : F) (b : A F) (hb : b.2 = 0) (a v : V4 F)
    (ha : ∀ i, (a i).1 = 0) : b * q4 δ (v + a) = b * q4 δ v := by
  have h : ∀ i, b * a i = 0 := fun i => Prod.ext (by
    change b.1 * (a i).1 = 0
    rw [ha i, mul_zero]) (by
    change b.2 * (a i).2 = 0
    rw [hb, zero_mul])
  simp only [q4, Pi.add_apply]
  linear_combination (2 * v 2 + a 2) * h 2 - rt δ * (2 * v 3 + a 3) * h 3 - v 1 * h 0 - (v 0 + a 0) * h 1

theorem UpperTheory.ConvolutionTheory.R2.Fo.fixGen :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D) Λ, ∀ φ ∈ Fix D.δ Λ, W.Om (wW F) φ ∈ Fix D.δ Λ ∧ ∀ b : A F, b.2 = 0 → W.Om (nU b) φ ∈ Fix D.δ Λ := by
  intro F E _ _ _ _ _ _ _ D W Λ φ hφ
  refine ⟨?_, fun b hb => ?_⟩
  · intro a ha v
    refine ⟨?_, ?_⟩
    · rw [W.Om_w, W.Om_w]
      unfold ft4
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      have h := (hφ a ha y).2
      change φ.1 y * ψ (B4 D.δ y (v + a)) = φ.1 y * ψ (B4 D.δ y v)
      have e : B4 D.δ y (v + a) = B4 D.δ y v + B4 D.δ a y := by
        rw [bilinearFour_comm D.δ y (v + a), quaternaryForm_add_left, bilinearFour_comm D.δ v y]
      rw [e, psi_add]
      calc φ.1 y * (ψ (B4 D.δ y v) * ψ (B4 D.δ a y))
          = ψ (B4 D.δ y v) * (ψ (B4 D.δ a y) * φ.1 y) := by ring
        _ = φ.1 y * ψ (B4 D.δ y v) := by rw [h]; ring
    · rw [W.Om_w]
      unfold ft4
      rw [← integral_const_mul]
      have key : ∀ y, ψ (B4 D.δ a v) * (φ.1 y * ψ (B4 D.δ y v)) =
          φ.1 (y + a) * ψ (B4 D.δ (y + a) v) := fun y => by
        rw [quaternaryForm_add_left, psi_add, (hφ a ha y).1]
        ring
      simp_rw [key]
      exact integral_add_right_eq_self (μ := adeleMeasurePi F) (fun y => φ.1 y * ψ (B4 D.δ y v)) a
  · intro a ha v
    have ha1 : ∀ i, (a i).1 = 0 := fun i => (ha i).1
    refine ⟨?_, ?_⟩
    · rw [W.Om_n, W.Om_n, quadraticForm_shift_expand D.δ b hb a v ha1, (hφ a ha v).1]
    · rw [W.Om_n, mul_left_comm, (hφ a ha v).2]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FkBasic
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.fkBasic :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (O : Ops F), (∀ N N' : Submodule ℂ (S4 F), N ≤ N' → ∀ m m', m ≤ m' → O.Fk N m ≤ O.Fk N' m') ∧
    (∀ N m w i, ∀ φ ∈ O.Fk N m, O.x w i φ ∈ O.Fk N (m + 1)) ∧
    ∀ N : Submodule ℂ (S4 F), FiniteDimensional ℂ N → ∀ m, FiniteDimensional ℂ (O.Fk N m) := by
  intro F _ _ _ O
  have hs : ∀ (N : Submodule ℂ (S4 F)) (m : ℕ),
      O.Fk N (m + 1) = O.Fk N m ⊔ ⨆ w, ⨆ i, (O.Fk N m).map (O.x w i) := fun _ _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · intro N N' h m m' hm
    have h1 : ∀ k, O.Fk N k ≤ O.Fk N' k := by
      intro k
      induction k with
      | zero => exact h
      | succ k ih =>
        rw [hs, hs]
        exact sup_le_sup ih (iSup_mono fun w => iSup_mono fun i => Submodule.map_mono ih)
    have h2 : Monotone (O.Fk N') := monotone_nat_of_le_succ fun k => by
      rw [hs]; exact le_sup_left
    exact (h1 m).trans (h2 hm)
  · intro N m w i φ hφ
    rw [hs]
    refine Submodule.mem_sup_right ?_
    refine Submodule.mem_iSup_of_mem w ?_
    refine Submodule.mem_iSup_of_mem i ?_
    exact Submodule.mem_map_of_mem hφ
  · intro N hN m
    induction m with
    | zero => exact hN
    | succ k ih =>
      rw [hs]
      haveI := ih
      haveI : ∀ w : InfinitePlace F, FiniteDimensional ℂ
          (⨆ i, (O.Fk N k).map (O.x w i) : Submodule ℂ (S4 F)) := fun w =>
        Submodule.finiteDimensional_iSup _
      haveI : FiniteDimensional ℂ
          (⨆ w, ⨆ i, (O.Fk N k).map (O.x w i) : Submodule ℂ (S4 F)) :=
        Submodule.finiteDimensional_iSup _
      exact Submodule.finiteDimensional_sup _ _
end

