module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.MetaplecticRepresentation
public import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ChirpInf
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.chirpInf :
    ∀ (K ι : Type) [Field K] [NumberField K] [Fintype ι] (p : MvPolynomial ι (mixedEmbedding.mixedSpace K)) (l : mixedEmbedding.mixedSpace K →L[ℝ] ℝ),
    Function.HasTemperateGrowth fun x : ι → mixedEmbedding.mixedSpace K => ((Real.fourierChar (l (MvPolynomial.eval x p)) : Circle) : ℂ) := by
  intro K ι _ _ _ p l
  have hp : Function.HasTemperateGrowth
      fun x : ι → mixedEmbedding.mixedSpace K => MvPolynomial.eval x p := by
    induction p using MvPolynomial.induction_on with
    | C a =>
      simpa using Function.HasTemperateGrowth.const (E := ι → mixedEmbedding.mixedSpace K) a
    | add p q hp hq =>
      simp only [map_add (f := _)]
      exact hp.fun_add hq
    | mul_X p i hp =>
      have hi : Function.HasTemperateGrowth fun x : ι → mixedEmbedding.mixedSpace K => x i :=
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => mixedEmbedding.mixedSpace K)
          i).hasTemperateGrowth
      simp only [map_mul, MvPolynomial.eval_X]
      exact hp.fun_mul hi
  exact GlobalTheory.Published.Metaplectic.hasTemperateGrowth_eChar.comp (l.hasTemperateGrowth.comp hp)
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ContEntry
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

namespace UpperTheory.ConvolutionTheory.R2.C.NearIdentityUnipotents

variable {F : Type} [Field F] [NumberField F]

private noncomputable def fstR : A F →+* InfiniteAdeleRing F :=
  RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)

private theorem cont_fst : Continuous (fun x : A F => x.1) :=
  continuous_fst (X := InfiniteAdeleRing F) (Y := FiniteAdeleRing (𝓞 F) F)

private theorem cont_pair (y : FiniteAdeleRing (𝓞 F) F) :
    Continuous (fun x : InfiniteAdeleRing F => ((x, y) : A F)) :=
  Continuous.prodMk_left (X := InfiniteAdeleRing F) (Y := FiniteAdeleRing (𝓞 F) F) y

private theorem cont_entry (i j : Fin 2) : Continuous (fun h : G1 F => h i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)

private theorem d_one : ((1 : G1 F) 1 1).1 = 1 := by
  simp

private theorem cont_d (v : InfinitePlace F) : Continuous (fun h : G1 F => (h 1 1).1 v) :=
  (continuous_apply (A := fun v : InfinitePlace F => v.Completion) v).comp (cont_fst.comp (cont_entry 1 1))

private theorem ne_one (v : InfinitePlace F) : ((1 : G1 F) 1 1).1 v ≠ 0 := by
  rw [d_one]
  exact one_ne_zero

private theorem ev_ne : ∀ᶠ h in 𝓝 (1 : G1 F), ∀ v, (h 1 1).1 v ≠ 0 := by
  rw [Filter.eventually_all]
  intro v
  exact (cont_d v).continuousAt.eventually_ne (ne_one v)

private noncomputable def eI (h : G1 F) : InfiniteAdeleRing F := fun v => ((h 1 1).1 v)⁻¹

private theorem eI_mul {h : G1 F} (hu : ∀ v, (h 1 1).1 v ≠ 0) : eI h * (h 1 1).1 = 1 := by
  funext v
  exact inv_mul_cancel₀ (hu v)

private theorem eI_cont : ContinuousAt (eI : G1 F → InfiniteAdeleRing F) 1 :=
  continuousAt_pi.2 fun v => (cont_d v).continuousAt.inv₀ (ne_one v)

private theorem eI_one : eI (1 : G1 F) = 1 := by
  funext v
  show (((1 : G1 F) 1 1).1 v)⁻¹ = 1
  rw [d_one]
  exact inv_one

private noncomputable def aU (h : G1 F) : (A F)ˣ :=
  if hu : ∀ v, (h 1 1).1 v ≠ 0 then
    ⟨(eI h, 1), ((h 1 1).1, 1), Prod.ext (eI_mul hu) (mul_one _),
      Prod.ext ((mul_comm _ _).trans (eI_mul hu)) (mul_one _)⟩
  else 1

private noncomputable def bU (h : G1 F) : A F := ((h 0 1).1 * eI h, 0)
private noncomputable def cU (h : G1 F) : A F := (-(h 1 0).1 * eI h, 0)

private noncomputable def pU (b : A F) (a : (A F)ˣ) (c : A F) : G1 F :=
  nU b * mD a * wW F * nU c * (wW F)⁻¹

private theorem pU_coe (b : A F) (a : (A F)ˣ) (c : A F) :
    (pU b a c).1 = !![(a : A F) - b * c * ((a⁻¹ : (A F)ˣ) : A F), b * ((a⁻¹ : (A F)ˣ) : A F);
      -c * ((a⁻¹ : (A F)ˣ) : A F), ((a⁻¹ : (A F)ˣ) : A F)] := by
  have hw : ((wW F)⁻¹).1 = !![0, -1; 1, 0] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [wW]
  simp only [pU, Matrix.SpecialLinearGroup.coe_mul, hw]
  simp only [nU, mD, wW, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

private theorem fstR_a {h : G1 F} (hu : ∀ v, (h 1 1).1 v ≠ 0) : fstR (aU h : A F) = eI h := by
  simp only [aU, dif_pos hu]
  rfl

private theorem fstR_ai {h : G1 F} (hu : ∀ v, (h 1 1).1 v ≠ 0) :
    fstR (((aU h)⁻¹ : (A F)ˣ) : A F) = (h 1 1).1 := by
  simp only [aU, dif_pos hu]
  rfl

private theorem fstR_b (h : G1 F) : fstR (bU h) = (h 0 1).1 * eI h := rfl
private theorem fstR_c (h : G1 F) : fstR (cU h) = -(h 1 0).1 * eI h := rfl

private theorem pU_fst {h : G1 F} (hu : ∀ v, (h 1 1).1 v ≠ 0) (i j : Fin 2) :
    ((pU (bU h) (aU h) (cU h)).1 i j).1 = (h i j).1 := by
  have hdet : (h 0 0).1 * (h 1 1).1 - (h 0 1).1 * (h 1 0).1 = 1 := by
    have h1 : h 0 0 * h 1 1 - h 0 1 * h 1 0 = 1 := by
      have := h.det_coe
      rwa [Matrix.det_fin_two] at this
    have := congrArg fstR h1
    rw [map_sub, map_mul, map_mul, map_one] at this
    exact this
  have he := eI_mul hu
  have e00 : fstR ((aU h : A F) - bU h * cU h * (((aU h)⁻¹ : (A F)ˣ) : A F)) = (h 0 0).1 := by
    rw [map_sub, map_mul, map_mul, fstR_a hu, fstR_ai hu, fstR_b, fstR_c]
    linear_combination ((h 0 1).1 * (h 1 0).1 * eI h + (h 0 0).1) * he - eI h * hdet
  have e01 : fstR (bU h * (((aU h)⁻¹ : (A F)ˣ) : A F)) = (h 0 1).1 := by
    rw [map_mul, fstR_ai hu, fstR_b]
    linear_combination (h 0 1).1 * he
  have e10 : fstR (-cU h * (((aU h)⁻¹ : (A F)ˣ) : A F)) = (h 1 0).1 := by
    rw [map_mul, map_neg, fstR_ai hu, fstR_c]
    linear_combination (h 1 0).1 * he
  have e11 : fstR (((aU h)⁻¹ : (A F)ˣ) : A F) = (h 1 1).1 := fstR_ai hu
  rw [pU_coe]
  fin_cases i <;> fin_cases j
  exacts [e00, e01, e10, e11]

private noncomputable def kU (h : G1 F) : G1 F := (pU (bU h) (aU h) (cU h))⁻¹ * h

private theorem infOne_kU {h : G1 F} (hu : ∀ v, (h 1 1).1 v ≠ 0) : InfOne (kU h) := by
  have hP : Matrix.SpecialLinearGroup.map fstR (pU (bU h) (aU h) (cU h)) =
      Matrix.SpecialLinearGroup.map fstR h := by
    ext i j
    exact pU_fst hu i j
  have hk : Matrix.SpecialLinearGroup.map fstR (kU h) = 1 := by
    rw [kU, map_mul, map_inv, hP, inv_mul_cancel]
  intro i j
  have h1 : fstR ((kU h).1 i j) = (Matrix.SpecialLinearGroup.map fstR (kU h)).1 i j := rfl
  have h2 : fstR ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j) =
      (fstR.mapMatrix (1 : Matrix (Fin 2) (Fin 2) (A F))) i j := rfl
  have h3 := h1.trans (by rw [hk]; rfl : _ = (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j)
  rw [map_one] at h2
  exact h3.trans h2.symm

private theorem cont_nU : Continuous (nU : A F → G1 F) := by
  refine Continuous.subtype_mk (continuous_matrix fun i j => ?_) _
  fin_cases i <;> fin_cases j <;> simp <;> fun_prop

private theorem cont_mD : Continuous (mD : (A F)ˣ → G1 F) := by
  refine Continuous.subtype_mk (continuous_matrix fun i j => ?_) _
  fin_cases i <;> fin_cases j <;> simp
  · exact Units.continuous_val
  · exact continuous_const
  · exact continuous_const
  · exact Units.continuous_val.comp continuous_inv

private theorem bU_cont : ContinuousAt (bU : G1 F → A F) 1 :=
  (cont_pair 0).continuousAt.comp
    (((cont_fst.comp (cont_entry 0 1)).continuousAt).mul eI_cont)

private theorem cU_cont : ContinuousAt (cU : G1 F → A F) 1 :=
  (cont_pair 0).continuousAt.comp
    ((((continuous_neg.comp (cont_fst.comp (cont_entry 1 0))).continuousAt)).mul eI_cont)

private theorem aU_cont : ContinuousAt (aU : G1 F → (A F)ˣ) 1 := by
  rw [Units.isEmbedding_embedProduct.isInducing.continuousAt_iff]
  have hf : ContinuousAt (fun h : G1 F => ((((eI h, 1) : A F), MulOpposite.op (((h 1 1).1, 1) : A F)) :
      A F × (A F)ᵐᵒᵖ)) 1 := by
    refine ContinuousAt.prodMk ((cont_pair 1).continuousAt.comp eI_cont) ?_
    exact (MulOpposite.continuous_op.comp ((cont_pair 1).comp (cont_fst.comp (cont_entry 1 1)))).continuousAt
  refine hf.congr ?_
  filter_upwards [ev_ne] with h hu
  simp only [Function.comp, aU, dif_pos hu]
  rfl

private theorem bU_one : bU (1 : G1 F) = 0 := by
  have : (1 : G1 F) 0 1 = 0 := by simp
  simp only [bU, this]
  exact Prod.ext (zero_mul _) rfl

private theorem cU_one : cU (1 : G1 F) = 0 := by
  have : (1 : G1 F) 1 0 = 0 := by simp
  simp only [cU, this]
  exact Prod.ext (by show -(0 : InfiniteAdeleRing F) * _ = 0; simp) rfl

private theorem aU_one : aU (1 : G1 F) = 1 := by
  refine Units.ext ?_
  simp only [aU, dif_pos (ne_one (F := F))]
  exact Prod.ext eI_one rfl

private theorem pU_one : pU (bU (1 : G1 F)) (aU 1) (cU 1) = 1 := by
  rw [bU_one, cU_one, aU_one]
  ext i j
  rw [pU_coe]
  fin_cases i <;> fin_cases j <;> simp

private theorem kU_tendsto : Tendsto (kU : G1 F → G1 F) (𝓝 1) (𝓝 1) := by
  have hb : ContinuousAt (fun h : G1 F => nU (bU h)) 1 := cont_nU.continuousAt.comp bU_cont
  have hc : ContinuousAt (fun h : G1 F => nU (cU h)) 1 := cont_nU.continuousAt.comp cU_cont
  have ha : ContinuousAt (fun h : G1 F => mD (aU h)) 1 := cont_mD.continuousAt.comp aU_cont
  have hp : ContinuousAt (fun h : G1 F => pU (bU h) (aU h) (cU h)) 1 :=
    (((hb.mul ha).mul continuousAt_const).mul hc).mul continuousAt_const
  have hk : ContinuousAt (kU : G1 F → G1 F) 1 := hp.inv.mul continuousAt_id
  have h1 : kU (1 : G1 F) = 1 := by simp [kU, pU_one]
  have := hk.tendsto
  rwa [h1] at this

end UpperTheory.ConvolutionTheory.R2.C.NearIdentityUnipotents

open UpperTheory.ConvolutionTheory.R2.C.NearIdentityUnipotents in
theorem UpperTheory.ConvolutionTheory.R2.C.near :
    ∀ (F : Type) [Field F] [NumberField F], ∃ (b c : G1 F → A F) (a : G1 F → (A F)ˣ) (k : G1 F → G1 F), ContinuousAt b 1 ∧ ContinuousAt c 1 ∧ ContinuousAt a 1 ∧
    Tendsto k (𝓝 1) (𝓝 1) ∧ ∀ᶠ h in 𝓝 (1 : G1 F), InfOne (k h) ∧ h = nU (b h) * mD (a h) * wW F * nU (c h) * (wW F)⁻¹ * k h := by
  intro F _ _
  refine ⟨bU, cU, aU, kU, bU_cont, cU_cont, aU_cont, kU_tendsto, ?_⟩
  filter_upwards [ev_ne] with h hu
  refine ⟨infOne_kU hu, ?_⟩
  show h = pU (bU h) (aU h) (cU h) * kU h
  rw [kU, mul_inv_cancel_left]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ContKer
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private lemma cont_param {X Y : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y] [SecondCountableTopology Y]
    {μ : Measure Y} {f : Y → ℂ} (hfc : Continuous f) (hfi : Integrable f μ)
    {a b : X × Y → ℂ} (ha : Continuous a) (hb : Continuous b)
    (ha1 : ∀ z, ‖a z‖ = 1) (hb1 : ∀ z, ‖b z‖ = 1) :
    Continuous fun p : X => ∫ y, a (p, y) * f y * b (p, y) ∂μ := by
  refine continuous_of_dominated (bound := fun y => ‖f y‖) ?_ ?_ hfi.norm ?_
  · intro p
    refine Continuous.aestronglyMeasurable ?_
    exact ((ha.comp (continuous_const.prodMk continuous_id)).mul hfc).mul
      (hb.comp (continuous_const.prodMk continuous_id))
  · intro p
    refine Eventually.of_forall fun y => ?_
    rw [norm_mul, norm_mul, ha1, hb1, one_mul, mul_one]
  · refine Eventually.of_forall fun y => ?_
    exact ((ha.comp (continuous_id.prodMk continuous_const)).mul continuous_const).mul
      (hb.comp (continuous_id.prodMk continuous_const))

section
variable {F : Type} [Field F] [NumberField F]

private theorem cψ : Continuous (ψ : A F → ℂ) := continuous_subtype_val.comp continuous_adelicChar
private theorem nψ (x : A F) : ‖ψ x‖ = 1 := Circle.norm_coe _
private theorem cq (δ : F) : Continuous (q4 δ : V4 F → A F) := by
  unfold q4
  fun_prop
private theorem ca (δ : F) : Continuous fun z : (A F × V4 F) × V4 F => ψ (z.1.1 * q4 δ z.2) :=
  cψ.comp ((continuous_fst.comp continuous_fst).mul ((cq δ).comp continuous_snd))
private theorem cb (δ : F) : Continuous fun z : (A F × V4 F) × V4 F => ψ (B4 δ z.2 z.1.2) := by
  have h : Continuous fun z : (A F × V4 F) × V4 F => B4 δ z.2 z.1.2 := by
    unfold B4
    fun_prop
  exact cψ.comp h
private theorem key (δ : F) (φ : S4 F) :
    Continuous fun p : A F × V4 F => ∫ y, ψ (p.1 * q4 δ y) * φ.1 y * ψ (B4 δ y p.2) ∂(adeleMeasurePi F) :=
  cont_param (continuous_of_mem_schwartzBruhatPi φ.2) (integrable_of_mem_schwartzBruhatPi φ.2)
    (ca δ) (cb δ) (fun _ => nψ _) (fun _ => nψ _)
end

theorem UpperTheory.ConvolutionTheory.R2.C.contKer :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F) (φ : S4 F), Continuous fun p : A F × V4 F => ft4 δ (fun y => ψ (p.1 * q4 δ y) * φ.1 y) p.2 := by
  intro F _ _ δ φ
  exact key δ φ
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.ContinuousFiniteAdeleEmbed
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private lemma exists_cube {ι Y : Type} [Finite ι] [TopologicalSpace Y] {y₀ : Y} {W : Set (ι → Y)}
    (hW : W ∈ 𝓝 (fun _ => y₀ : ι → Y)) :
    ∃ U ∈ 𝓝 y₀, ∀ y : ι → Y, (∀ i, y i ∈ U) → y ∈ W := by
  rw [nhds_pi, Filter.mem_pi'] at hW
  obtain ⟨I, t, ht, hsub⟩ := hW
  exact ⟨⋂ i, t i, Filter.iInter_mem.2 ht, fun y hy => hsub fun i _ => Set.mem_iInter.1 (hy i) i⟩

private noncomputable def fin0 {F : Type} [Field F] [NumberField F] (x : FiniteAdeleRing (𝓞 F) F) : A F := (0, x)

private lemma continuous_finiteAdeleEmbed {F : Type} [Field F] [NumberField F] :
    Continuous (fin0 (F := F)) :=
  show Continuous fun x : FiniteAdeleRing (𝓞 F) F => ((0, x) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) from
    continuous_const.prodMk continuous_id

private noncomputable def oneAdd {F : Type} [Field F] [NumberField F]
    (X : Fin 2 × Fin 2 → FiniteAdeleRing (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (A F) :=
  fun i j => (1 : Matrix (Fin 2) (Fin 2) (A F)) i j + fin0 (X (i, j))

private lemma continuous_oneAdd {F : Type} [Field F] [NumberField F] :
    Continuous (oneAdd (F := F)) := by
  refine continuous_matrix fun i j => ?_
  exact continuous_const.add (continuous_finiteAdeleEmbed.comp (continuous_apply _))

private lemma oneAdd_zero {F : Type} [Field F] [NumberField F] :
    oneAdd (F := F) (fun _ => 0) = 1 := by
  ext i j : 2
  change (1 : Matrix (Fin 2) (Fin 2) (A F)) i j + 0 = _
  exact add_zero _

theorem UpperTheory.ConvolutionTheory.R2.C.unrOf :
    ∀ (F : Type) [Field F] [NumberField F] (P : G1 F → Prop), (∀ᶠ g in 𝓝 (1 : G1 F), InfOne g → P g) → ∀ᶠ v in cofinite, ∀ g, At v g → IntAt v g → P g := by
  intro F _ _ P h
  have hind : IsInducing (fun g : G1 F => (g : Matrix (Fin 2) (Fin 2) (A F))) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.isInducing
  rw [Filter.Eventually, hind.nhds_eq_comap, Filter.mem_comap] at h
  obtain ⟨S, hS, hSP⟩ := h
  have h1 : S ∈ 𝓝 (oneAdd (F := F) fun _ => 0) := by
    rw [oneAdd_zero]; simpa using hS
  have h2 := continuous_oneAdd.continuousAt.preimage_mem_nhds h1
  obtain ⟨U, hU, hUS⟩ := exists_cube h2
  obtain ⟨J, hJ⟩ := exists_idealFiniteAdeles_subset hU
  have hfin : ((idealSupport J : Finset _) : Set (HeightOneSpectrum (𝓞 F))).Finite :=
    Finset.finite_toSet _
  refine Filter.eventually_cofinite.2 (hfin.subset fun v hv => ?_)
  by_contra hvJ
  apply hv
  intro g hg hint
  have hone : ∀ i j, ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).2 v ∈ v.adicCompletionIntegers F := by
    intro i j
    by_cases hij : i = j
    · simp [Matrix.one_apply, hij]
    · simp only [Matrix.one_apply, hij, if_false, Prod.snd_zero]
      change (0 : v.adicCompletion F) ∈ v.adicCompletionIntegers F
      exact zero_mem _
  set X : Fin 2 × Fin 2 → FiniteAdeleRing (𝓞 F) F :=
    fun p => (g p.1 p.2).2 - ((1 : Matrix (Fin 2) (Fin 2) (A F)) p.1 p.2).2 with hX
  have hXm : ∀ p, X p ∈ U := by
    intro p
    apply hJ
    rw [SetLike.mem_coe, mem_idealFiniteAdeles]
    intro w
    by_cases hw : w = v
    · subst hw
      rw [count_eq_zero_of_not_mem_idealSupport J (by simpa using hvJ)]
      simp only [neg_zero, WithZero.exp_zero]
      exact sub_mem (hint p.1 p.2) (hone p.1 p.2)
    · have : X p w = 0 := by
        have := hg.2 w hw p.1 p.2
        simp only [hX]
        exact sub_eq_zero.2 this
      rw [this, map_zero]
      exact zero_le
  have hgX : (g : Matrix (Fin 2) (Fin 2) (A F)) = oneAdd X := by
    ext i j : 2
    apply Prod.ext
    · have : (oneAdd X i j).1 = ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).1 + 0 := rfl
      rw [this, add_zero]
      exact hg.1 i j
    · have : (oneAdd X i j).2 = ((1 : Matrix (Fin 2) (Fin 2) (A F)) i j).2 + X (i, j) := rfl
      rw [this, hX]
      simp
  apply hSP
  · show (g : Matrix (Fin 2) (Fin 2) (A F)) ∈ S
    rw [hgX]
    exact hUS X hXm
  · exact hg.1
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.FtBasic
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

namespace UpperTheory.ConvolutionTheory.R2.C

variable {F : Type} [Field F] [NumberField F]

private noncomputable def Gm (δ : F) : Matrix (Fin 4) (Fin 4) F :=
  !![0, -1, 0, 0; -1, 0, 0, 0; 0, 0, 2, 0; 0, 0, 0, -(2 * δ)]

private noncomputable def Hm (δ : F) : Matrix (Fin 4) (Fin 4) F :=
  !![0, -1, 0, 0; -1, 0, 0, 0; 0, 0, 2⁻¹, 0; 0, 0, 0, -(2 * δ)⁻¹]

private lemma Gm_mul_Hm {δ : F} (hδ : δ ≠ 0) : Gm δ * Hm δ = 1 := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Gm, Hm, Matrix.mul_apply, Fin.sum_univ_four, h2, hδ]
  field_simp

private lemma Hm_mul_Gm {δ : F} (hδ : δ ≠ 0) : Hm δ * Gm δ = 1 :=
  mul_eq_one_comm.1 (Gm_mul_Hm hδ)

private lemma Gm_transpose (δ : F) : (Gm δ)ᵀ = Gm δ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Gm]

private lemma sum_eq_quaternaryForm (δ : F) (y v : V4 F) :
    ∑ i, y i * ((Gm δ).map (algebraMap F (A F)) *ᵥ v) i = B4 δ y v := by
  have h2 : algebraMap F (A F) 2 = 2 := map_ofNat _ 2
  simp [Gm, B4, Fin.sum_univ_four, Matrix.mulVec, dotProduct, rt, h2]
  ring

private lemma quaternaryFourier_eq_adelic (δ : F) (φ : V4 F → ℂ) (v : V4 F) :
    ft4 δ φ v = adelicFourierPi F φ ((Gm δ).map (algebraMap F (A F)) *ᵥ v) := by
  simp only [ft4, adelicFourierPi, sum_eq_quaternaryForm, ψ]

end UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.ftBasic :
    ∀ (F : Type) [Field F] [NumberField F] (δ : F), δ ≠ 0 → ∀ φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4),
    ft4 δ φ ∈ schwartzBruhatPi (K := F) (ι := Fin 4) ∧ (∀ v, ft4 δ (ft4 δ φ) v = φ (-v)) ∧ Th (ft4 δ φ) = Th φ := by
  intro F _ _ δ hδ φ hφ
  have hGH := Gm_mul_Hm hδ
  have hHG := Hm_mul_Gm hδ
  have hfun : ft4 δ φ = fun v => adelicFourierPi F φ ((Gm δ).map (algebraMap F (A F)) *ᵥ v) :=
    funext (quaternaryFourier_eq_adelic δ φ)
  have hF := adelicFourierPi_mem_schwartzBruhatPi hφ
  refine ⟨?_, ?_, ?_⟩
  · rw [hfun]
    exact GroundTheory.Heights₂.Theta.comp_mulVec_mem_schwartzBruhatPi (Gm δ) (Hm δ) hHG hGH hF
  · intro v
    rw [quaternaryFourier_eq_adelic, hfun, GroundTheory.Heights₂.Theta.adelicFourierPi_comp_mulVec (Gm δ) (Hm δ) hHG hGH,
      adelicFourierPi_adelicFourierPi hφ]
    have hT : ((Hm δ).map (algebraMap F (A F)))ᵀ * (Gm δ).map (algebraMap F (A F)) = 1 := by
      have h : (Hm δ)ᵀ * Gm δ = 1 := by
        have h' := congrArg Matrix.transpose hGH
        rwa [Matrix.transpose_mul, Gm_transpose, Matrix.transpose_one] at h'
      rw [← Matrix.transpose_map]
      exact GroundTheory.Heights₂.Theta.map_mul_map_eq_one _ h
    simp only [Matrix.mulVec_mulVec, hT, Matrix.one_mulVec]
  · have hmap : ∀ ξ : Fin 4 → F, ((Gm δ).map (algebraMap F (A F)) *ᵥ fun i => rt (ξ i)) =
        fun i => rt ((Gm δ *ᵥ ξ) i) := by
      intro ξ
      exact (GroundTheory.Heights₂.Theta.map_mulVec_eq (algebraMap F (A F)) (Gm δ) ξ).symm
    let e : (Fin 4 → F) ≃ (Fin 4 → F) :=
      { toFun := fun ξ => Gm δ *ᵥ ξ
        invFun := fun ξ => Hm δ *ᵥ ξ
        left_inv := fun ξ => by simp only [Matrix.mulVec_mulVec, hHG, Matrix.one_mulVec]
        right_inv := fun ξ => by simp only [Matrix.mulVec_mulVec, hGH, Matrix.one_mulVec] }
    have h1 : Th (ft4 δ φ) = ∑' ξ : Fin 4 → F, adelicFourierPi F φ fun i => rt (ξ i) := by
      unfold Th
      rw [← e.tsum_eq (fun ξ : Fin 4 → F => adelicFourierPi F φ fun i => rt (ξ i))]
      refine tsum_congr fun ξ => ?_
      rw [quaternaryFourier_eq_adelic, hmap]
      rfl
    rw [h1]
    exact (tsum_algebraMap_eq_tsum_adelicFourierPi hφ).symm
end

