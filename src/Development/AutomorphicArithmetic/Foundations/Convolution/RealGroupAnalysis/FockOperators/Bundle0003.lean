module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CapCentral

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.StableOfOrth
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

section

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private theorem wW_val : (wW F).1 = !![0, 1; -1, 0] := rfl

private theorem wInv_val : ((wW F)⁻¹).1 = !![0, -1; 1, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, wW_val]
  simp

private theorem orth_w : InfOrth (wW F) := by
  intro i j
  rw [wW_val]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem orth_wInv : InfOrth (wW F)⁻¹ := by
  intro i j
  rw [wInv_val]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem orth_unitary (h : G1 F) (ho : InfOrth h) :
    (GeneralLinearGroup.map (TR.pInf F) (gl h)).val ∈ Matrix.unitaryGroup (Fin 2) (TR.Rinf F) := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext1 i j
  have e : TR.pInf F ((h.1 * h.1ᵀ) i j) = TR.pInf F ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j) :=
    congrArg (TR.infEq F).symm (ho i j)
  have e1 : ((GeneralLinearGroup.map (TR.pInf F) (gl h)).val * star (GeneralLinearGroup.map (TR.pInf F) (gl h)).val) i j =
      TR.pInf F ((h.1 * h.1ᵀ) i j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, map_sum, map_mul, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, star_trivial,
      Matrix.transpose_apply]
    rfl
  have e2 : TR.pInf F ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j) = (1 : Matrix (Fin 2) (Fin 2) (TR.Rinf F)) i j := by
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  rw [e1, e, e2]

private theorem rt_split (g : GL (Fin 2) (A F)) :
    TR.rt F 2 g = TR.rt F 2 (TR.infGL F 2 (GeneralLinearGroup.map (TR.pInf F) g)) *
      TR.rt F 2 (finGL F 2 (GeneralLinearGroup.map (pFin F) g)) := by
  rw [← map_mul, TR.infGL_mul_finGL]

private theorem stable_of_orth (π : TR.CuspSub F 2) {h : G1 F} (ho : InfOrth h) {f : TR.Sm F 2} (hf : f ∈ π.V) :
    TR.rt F 2 (gl h) f ∈ π.V := by
  rw [rt_split, Module.End.mul_apply]
  have h1 := π.stable (.fin (GeneralLinearGroup.map (pFin F) (gl h))) f hf
  have h2 := π.stable (.cpt ⟨_, orth_unitary h ho⟩) _ h1
  have e : Unitary.toUnits (⟨_, orth_unitary h ho⟩ : TR.Kinf F 2) = GeneralLinearGroup.map (TR.pInf F) (gl h) :=
    Units.ext rfl
  change TR.rt F 2 (TR.infGL F 2 (Unitary.toUnits (⟨_, orth_unitary h ho⟩ : TR.Kinf F 2)))
    (TR.rt F 2 (finGL F 2 (GeneralLinearGroup.map (pFin F) (gl h))) f) ∈ π.V at h2
  rwa [e] at h2

private theorem ad_eop (v : InfinitePlace F) :
    TR.rt F 2 (gl (wW F)) * TR.Eop v 0 1 = -(TR.Eop v 1 0 * TR.rt F 2 (gl (wW F))) := by
  have hy : (GeneralLinearGroup.map (TR.pInf F) (gl (wW F))).val = !![0, 1; -1, 0] := by
    ext1 i j
    fin_cases i <;> fin_cases j <;> simp [wW_val]
  have hyi : ((GeneralLinearGroup.map (TR.pInf F) (gl (wW F)))⁻¹).val = !![0, -1; 1, 0] := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hy, Matrix.mul_fin_two, Matrix.one_fin_two]
    simp
  have hfin : ∀ k : GL (Fin 2) (Af F), TR.rt F 2 (finGL F 2 k) * TR.Eop v 0 1 = TR.Eop v 0 1 * TR.rt F 2 (finGL F 2 k) :=
    fun k => (TR.lie_rt_fin _ k).symm
  rw [rt_split (gl (wW F)), mul_assoc, hfin, ← mul_assoc, TR.Cen.rt_Eop, hy, hyi]
  simp [Fin.sum_univ_two, mul_assoc]

end

theorem UpperTheory.ConvolutionTheory.R2.Fo.adW :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], (∀ π : TR.CuspSub F 2, ∀ f ∈ π.V, TR.rt F 2 (gl (wW F)) f ∈ π.V ∧ TR.rt F 2 (gl (wW F)⁻¹) f ∈ π.V) ∧
    (∀ v, TR.rt F 2 (gl (wW F)) * TR.Eop v 0 1 = -(TR.Eop v 1 0 * TR.rt F 2 (gl (wW F)))) ∧ InfOrth (wW F)⁻¹ := by
  intro F _ _ _
  exact ⟨fun π f hf => ⟨stable_of_orth π orth_w hf, stable_of_orth π orth_wInv hf⟩, ad_eop, orth_wInv⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.VacForm
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private theorem slice_mem {F : Type} [Field F] [NumberField F] {f : V4 F → ℂ}
    (hf : f ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) :
    (fun y : Fin 4 → FiniteAdeleRing (𝓞 F) F => f fun i => ((0, y i) : A F)) ∈
      finiteSchwartzBruhatPi F (ι := Fin 4) := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨p, g, hg, rfl⟩ := hx
    have e : (fun y : Fin 4 → FiniteAdeleRing (𝓞 F) F =>
        schwartzBruhatTensorPi p g fun i => ((0, y i) : A F)) =
        p (infPartPi fun _ : Fin 4 => (0 : A F)) • g := by
      funext y
      rfl
    rw [e]
    exact Submodule.smul_mem _ _ hg
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

private theorem gauss_fin {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (δ : F)
    (y : Fin 4 → FiniteAdeleRing (𝓞 F) F) : gauss δ (fun i => ((0, y i) : A F)) = 1 := by
  have key : ∀ a : V4 F, (∀ i, TR.pInf F (a i) = 0) → gauss δ a = 1 := fun a h => by
    simp only [gauss, map_add (f := _), map_sub, map_mul, map_pow, h]
    simp
  exact key _ fun i => map_zero (TR.infEq F).symm

theorem UpperTheory.ConvolutionTheory.R2.Fo.vacForm :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F), ∀ φ ∈ Vac δ, ∃ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4), φ.1 = fun v => gauss δ v * g (finPartPi v) := by
  intro F _ _ _ δ φ hφ
  refine ⟨_, slice_mem φ.2, funext fun v => ?_⟩
  have h := hφ v (fun i => ((0, (v i).2) : A F)) rfl
  rw [gauss_fin, mul_one] at h
  rw [h, mul_comm]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XEx
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

namespace UpperTheory.ConvolutionTheory.R2.Fo

open NumberField.mixedEmbedding

private noncomputable def lin {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
    (w : InfinitePlace F) (i : Fin 4) : (Fin 4 → mixedSpace F) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp
    ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : {w : InfinitePlace F // w.IsReal} => ℝ)
      ⟨w, IsTotallyReal.isReal w⟩).comp
      ((ContinuousLinearMap.fst ℝ ({w : InfinitePlace F // w.IsReal} → ℝ)
        ({w : InfinitePlace F // w.IsComplex} → ℂ)).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => mixedSpace F) i)))

end UpperTheory.ConvolutionTheory.R2.Fo

theorem UpperTheory.ConvolutionTheory.R2.Fo.xEx :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (w : InfinitePlace F) (i : Fin 4) (φ : V4 F → ℂ), φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4) → (fun v => cw w (v i) * φ v) ∈ schwartzBruhatPi (K := F) (ι := Fin 4) := by
  intro F _ _ _ w i φ hφ
  induction hφ using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨f, g, hg, rfl⟩ := hG
    have e : (fun v => cw w (v i) * schwartzBruhatTensorPi f g v) =
        schwartzBruhatTensorPi (SchwartzMap.smulLeftCLM ℂ (lin w i) f) g := by
      funext v
      simp only [schwartzBruhatTensorPi]
      rw [SchwartzMap.smulLeftCLM_apply_apply (lin w i).hasTemperateGrowth, smul_eq_mul, mul_assoc]
      congr 1
    rw [e]
    exact schwartzBruhatTensorPi_mem _ hg
  | zero =>
    have e : (fun v => cw w (v i) * (0 : V4 F → ℂ) v) = 0 := by
      funext v
      simp
    rw [e]
    exact zero_mem _
  | add G H _ _ hG hH =>
    have e : (fun v => cw w (v i) * (G + H) v) = (fun v => cw w (v i) * G v) + fun v => cw w (v i) * H v := by
      funext v
      simp [mul_add]
    rw [e]
    exact add_mem hG hH
  | smul c G _ hG =>
    have e : (fun v => cw w (v i) * (c • G) v) = c • fun v => cw w (v i) * G v := by
      funext v
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [e]
    exact Submodule.smul_mem _ c hG
end

