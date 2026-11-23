module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.NApply

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.TorusEq
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

private lemma eqm {F : Type} [Field F] [NumberField F] (p q : G1 F)
    (h : (p : Matrix (Fin 2) (Fin 2) (A F)) = (q : Matrix (Fin 2) (Fin 2) (A F))) : p = q := Subtype.ext h

private lemma m4 {R : Type} (a b c d a' b' c' d' : R) (h1 : a = a') (h2 : b = b') (h3 : c = c')
    (h4 : d = d') : !![a, b; c, d] = !![a', b'; c', d'] := by
  subst h1 h2 h3 h4; rfl

private noncomputable def nL {F : Type} [Field F] [NumberField F] (c : A F) : G1 F :=
  ⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two]⟩

private lemma nL_eq {F : Type} [Field F] [NumberField F] (c : A F) :
    nL c = wW F * nU (-c) * (wW F)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  apply eqm
  show !![1, 0; c, 1] * !![0, 1; -1, 0] = !![0, 1; -1, 0] * !![1, -c; 0, 1]
  simp [Matrix.mul_fin_two]

private lemma torus_eq {F : Type} [Field F] [NumberField F] (u : (A F)ˣ) (x y : A F)
    (h : ((u⁻¹ : (A F)ˣ) : A F) = 1 + x * y) :
    nL (y * (u : A F)) * mD u⁻¹ * nU (x * (u : A F)) = nU x * nL y := by
  have hu : (u : A F) * ((u⁻¹ : (A F)ˣ) : A F) = 1 := Units.mul_inv u
  apply eqm
  show !![1, 0; y * (u : A F), 1] * !![((u⁻¹ : (A F)ˣ) : A F), 0; 0, (((u⁻¹)⁻¹ : (A F)ˣ) : A F)] *
      !![1, x * (u : A F); 0, 1] = !![1, x; 0, 1] * !![1, 0; y, 1]
  rw [inv_inv]
  generalize ((u⁻¹ : (A F)ˣ) : A F) = v at h hu
  generalize (u : A F) = t at hu
  simp only [Matrix.mul_fin_two]
  refine m4 _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_
  · linear_combination h
  · linear_combination x * hu
  · linear_combination y * hu
  · linear_combination (y * x * t + 1) * hu - t * h

private lemma g_eq {F : Type} [Field F] [NumberField F] (g : G1 F) (u : (A F)ˣ) (ε : A F)
    (he : g 1 1 + g 1 0 * ε = u) :
    g * nU ε = nU ((g 0 0 * ε + g 0 1) * ((u⁻¹ : (A F)ˣ) : A F)) * mD u⁻¹ *
      nL (g 1 0 * ((u⁻¹ : (A F)ˣ) : A F)) := by
  have hu : (u : A F) * ((u⁻¹ : (A F)ˣ) : A F) = 1 := Units.mul_inv u
  have hd : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := g.det_coe
    rwa [Matrix.det_fin_two] at this
  apply eqm
  show (g : Matrix (Fin 2) (Fin 2) (A F)) * !![1, ε; 0, 1] =
    !![1, (g 0 0 * ε + g 0 1) * ((u⁻¹ : (A F)ˣ) : A F); 0, 1] *
      !![((u⁻¹ : (A F)ˣ) : A F), 0; 0, (((u⁻¹)⁻¹ : (A F)ˣ) : A F)] *
      !![1, 0; g 1 0 * ((u⁻¹ : (A F)ˣ) : A F), 1]
  rw [inv_inv]
  have hg := Matrix.eta_fin_two (g : Matrix (Fin 2) (Fin 2) (A F))
  generalize ((u⁻¹ : (A F)ˣ) : A F) = v at hu
  generalize (u : A F) = t at hu he
  generalize (g : Matrix (Fin 2) (Fin 2) (A F)) 0 0 = a at hg hd he ⊢
  generalize (g : Matrix (Fin 2) (Fin 2) (A F)) 0 1 = b at hg hd he ⊢
  generalize (g : Matrix (Fin 2) (Fin 2) (A F)) 1 0 = c at hg hd he ⊢
  generalize (g : Matrix (Fin 2) (Fin 2) (A F)) 1 1 = d at hg hd he ⊢
  rw [hg]
  simp only [Matrix.mul_fin_two]
  refine m4 _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_
  · linear_combination v * hd - v * a * he - a * hu - (a * ε + b) * c * v * hu
  · linear_combination -(a * ε + b) * hu
  · linear_combination -c * hu
  · linear_combination he

theorem UpperTheory.ConvolutionTheory.R2.C.lvAlg :
    ∀ (F : Type) [Field F] [NumberField F] (H : Subgroup (G1 F)) (R : Subring (A F)) (I : AddSubgroup (A F)), (∀ r ∈ R, ∀ x ∈ I, r * x ∈ I) →
    (∀ b ∈ I, nU b ∈ H ∧ wW F * nU b * (wW F)⁻¹ ∈ H) → ∀ (g : G1 F) (u : (A F)ˣ), g 0 0 ∈ R → g 0 1 ∈ I → g 1 0 ∈ I → (u : A F) ∈ R →
    ((u⁻¹ : (A F)ˣ) : A F) ∈ R → ∀ ε ∈ I, ∀ x ∈ I, ∀ y ∈ I, g 1 1 + g 1 0 * ε = u → ((u⁻¹ : (A F)ˣ) : A F) = 1 + x * y → g ∈ H := by
  intro F _ _ H R I hRI hH g u ha hb hc huR hviR ε hε x hx y hy he hxy
  have hmul : ∀ r ∈ R, ∀ z ∈ I, z * r ∈ I := fun r hr z hz => by
    rw [mul_comm]; exact hRI r hr z hz
  have hU : ∀ b ∈ I, nU b ∈ H := fun b hb => (hH b hb).1
  have hL : ∀ b ∈ I, nL b ∈ H := fun b hb => by
    rw [nL_eq]; exact (hH (-b) (I.neg_mem hb)).2
  have hm : mD u⁻¹ ∈ H := by
    have h1 : mD u⁻¹ = (nL (y * (u : A F)))⁻¹ * (nU x * nL y) * (nU (x * (u : A F)))⁻¹ := by
      rw [← torus_eq u x y hxy]; group
    rw [h1]
    exact H.mul_mem (H.mul_mem (H.inv_mem (hL _ (hmul _ huR _ hy)))
      (H.mul_mem (hU _ hx) (hL _ hy))) (H.inv_mem (hU _ (hmul _ huR _ hx)))
  have h2 : g = nU ((g 0 0 * ε + g 0 1) * ((u⁻¹ : (A F)ˣ) : A F)) * mD u⁻¹ *
      nL (g 1 0 * ((u⁻¹ : (A F)ˣ) : A F)) * (nU ε)⁻¹ := by
    rw [← g_eq g u ε he]; group
  rw [h2]
  exact H.mul_mem (H.mul_mem (H.mul_mem (hU _ (hmul _ hviR _ (I.add_mem (hRI _ ha _ hε) hb))) hm)
    (hL _ (hmul _ hviR _ hc))) (H.inv_mem (hU _ hε))
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianForms.UnitA
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.C

theorem UpperTheory.ConvolutionTheory.R2.C.unitA :
    ∀ (F : Type) [Field F] [NumberField F] (x : A F), IsUnit x ↔ (∀ w, x.1 w ≠ 0) ∧ (∀ v, x.2 v ≠ 0) ∧ ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, Valued.v (x.2 v) = 1 := by
  intro F _ _ x
  constructor
  · rintro ⟨a, rfl⟩
    have hinf : ∀ w, (a : A F).1 w * ((a⁻¹ : (A F)ˣ) : A F).1 w = 1 := fun w =>
      congrArg (fun z : A F => z.1 w) a.mul_inv
    have hfin : ∀ v, (a : A F).2 v * ((a⁻¹ : (A F)ˣ) : A F).2 v = 1 := fun v =>
      congrArg (fun z : A F => z.2 v) a.mul_inv
    refine ⟨fun w h => ?_, fun v h => ?_, ?_⟩
    · have := hinf w
      rw [h, zero_mul] at this
      exact zero_ne_one this
    · have := hfin v
      rw [h, zero_mul] at this
      exact zero_ne_one this
    · filter_upwards [(a : A F).2.2, ((a⁻¹ : (A F)ˣ) : A F).2.2] with v h3 h4
      have hm := congrArg Valued.v (hfin v)
      rw [map_mul, map_one] at hm
      refine le_antisymm h3 ?_
      rw [← hm]
      exact mul_le_of_le_one_right' h4
  · rintro ⟨h1, h2, h3⟩
    have hmem : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite,
        (x.2 v)⁻¹ ∈ v.adicCompletionIntegers F := by
      filter_upwards [h3] with v hv
      change Valued.v (x.2 v)⁻¹ ≤ 1
      rw [map_inv₀, hv, inv_one]
    let y : A F := (fun w => (x.1 w)⁻¹, ⟨fun v => (x.2 v)⁻¹, hmem⟩)
    refine IsUnit.of_mul_eq_one y (Prod.ext (funext fun w => ?_) ?_)
    · exact mul_inv_cancel₀ (h1 w)
    · apply RestrictedProduct.ext
      intro v
      exact mul_inv_cancel₀ (h2 v)
end

