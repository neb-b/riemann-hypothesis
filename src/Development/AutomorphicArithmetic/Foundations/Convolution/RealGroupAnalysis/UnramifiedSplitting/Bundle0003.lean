module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.StdHat
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

private theorem psi_add' {K : Type} [Field K] [NumberField K] (a b : A K) : ψ (a + b) = ψ a * ψ b := by
  simp [ψ, AddChar.map_add_eq_mul]

private theorem psi_neg_one {K : Type} [Field K] [NumberField K] {a : A K} (h : ψ (-a) = 1) : ψ a = 1 := by
  have h0 : ψ (0 : A K) = 1 := by simp [ψ]
  have h1 := psi_add' a (-a)
  rw [add_neg_cancel, h, mul_one, h0] at h1
  exact h1.symm

private theorem isInt_zero {K : Type} [Field K] [NumberField K] (v : P K) : IsInt (0 : Kv v) := by
  simp [IsInt]

private theorem isInt_mul {K : Type} [Field K] [NumberField K] {v : P K} {a b : Kv v}
    (ha : IsInt a) (hb : IsInt b) : IsInt (a * b) := by
  unfold IsInt at *
  rw [map_mul]
  exact mul_le_one' ha hb

private theorem isInt_neg {K : Type} [Field K] [NumberField K] {v : P K} {a : Kv v}
    (ha : IsInt a) : IsInt (-a) := by
  unfold IsInt at *
  rwa [Valuation.map_neg]

theorem UpperTheory.ConvolutionTheory.R2.H.stdHat :
    ∀ (K : Type) [Field K] [NumberField K] (δ : K) (v : P K), Gd δ v → ∀ φ : V4 K → ℂ, Std v φ → Std v (hat φ) := by
  intro K _ _ δ v hG φ hφ
  obtain ⟨hadd, hmul, hcp, -, -, -, -, -, -, -⟩ := sgLaws K v
  have hsg0 : sg v 0 = 0 := by simpa using hadd 0 0

  have hshift : ∀ (x : V4 K) (s : A K) (c : Kv v), IsInt c →
      φ (Function.update x 1 (s + sg v c)) = φ (Function.update x 1 s) := by
    intro x s c hc
    have h1 : Function.update x 1 (s + sg v c) =
        fun i => Function.update x 1 s i + sg v (Function.update (0 : Fin 4 → Kv v) 1 c i) := by
      funext i
      by_cases hi : i = 1
      · subst hi; simp
      · simp [Function.update_of_ne hi, hsg0]
    rw [h1]
    refine hφ.2 _ _ fun i => ?_
    by_cases hi : i = 1
    · subst hi; simpa using hc
    · simpa [Function.update_of_ne hi] using isInt_zero v
  refine ⟨fun x hx i => ?_, fun x y hy => ?_⟩
  · by_cases hi : i = 1
    · subst hi
      refine hG.psi.2.2 (cp v (x 1)) fun c hc => ?_
      have key : hat φ x = ψ (-(sg v c * x 1)) * hat φ x := by
        calc hat φ x = ∫ s, φ (Function.update x 1 (s + sg v c)) * ψ (-((s + sg v c) * x 1)) ∂(adeleMeasure K) :=
              (integral_add_right_eq_self
                (fun s => φ (Function.update x 1 s) * ψ (-(s * x 1))) (sg v c)).symm
          _ = ∫ s, ψ (-(sg v c * x 1)) * (φ (Function.update x 1 s) * ψ (-(s * x 1))) ∂(adeleMeasure K) := by
              congr 1
              funext s
              rw [hshift x s c hc, show -((s + sg v c) * x 1) = -(s * x 1) + -(sg v c * x 1) by ring, psi_add']
              ring
          _ = ψ (-(sg v c * x 1)) * hat φ x := integral_const_mul _ _
      have h1 : ψ (-(sg v c * x 1)) = 1 := by
        have h2 : (ψ (-(sg v c * x 1)) - 1) * hat φ x = 0 := by
          rw [sub_mul, one_mul, ← key, sub_self]
        exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right hx)
      have h3 := psi_neg_one h1
      rw [mul_comm (sg v c), hmul, mul_comm] at h3
      exact h3
    · have ex : ∃ s, φ (Function.update x 1 s) ≠ 0 := by
        by_contra h
        push_neg at h
        exact hx (by simp [hat, h])
      obtain ⟨s, hs⟩ := ex
      have := hφ.1 _ hs i
      rwa [Function.update_of_ne hi] at this
  · unfold hat
    congr 1
    funext s
    have h1 : Function.update (fun i => x i + sg v (y i)) 1 s =
        fun i => Function.update x 1 s i + sg v (Function.update y 1 0 i) := by
      funext i
      by_cases hi : i = 1
      · subst hi; simp [hsg0]
      · simp [Function.update_of_ne hi]
    have h2 : φ (Function.update (fun i => x i + sg v (y i)) 1 s) = φ (Function.update x 1 s) := by
      rw [h1]
      refine hφ.2 _ _ fun i => ?_
      by_cases hi : i = 1
      · subst hi; simpa using isInt_zero v
      · simpa [Function.update_of_ne hi] using hy i
    rw [h2]
    by_cases h0 : φ (Function.update x 1 s) = 0
    · simp [h0]
    · have hs : IsInt (cp v s) := by simpa using hφ.1 _ h0 1
      have h3 : ψ (-(s * sg v (y 1))) = 1 := by
        rw [← neg_mul, hmul]
        exact hG.psi.2.1 _ (isInt_mul (by rw [map_neg]; exact isInt_neg hs) (hy 1))
      show φ (Function.update x 1 s) * ψ (-(s * (x 1 + sg v (y 1)))) = φ (Function.update x 1 s) * ψ (-(s * x 1))
      rw [show -(s * (x 1 + sg v (y 1))) = -(s * x 1) + -(s * sg v (y 1)) by ring, psi_add', h3, mul_one]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.WeLoc
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.H.weLoc :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (v : P F) (w : P E), Gd D.δ v → Inert D v w →
      ∃ χ : Kv w → ℂ, Good χ ∧ ∀ x, ∃ u t, sg w x = D.mkE u t ∧ ψ (-(2 * u)) = χ x := by
  intro F E _ _ _ _ _ D v w hG hI
  obtain ⟨e, h1, h2, h3, -⟩ := hI.coord
  obtain ⟨sa, sm, sc, -⟩ := sgLaws F v
  obtain ⟨-, tm, tc, -⟩ := sgLaws E w
  obtain ⟨ga, gi, gm⟩ := hG.psi
  have hs : ∀ u, -(2 * sg v u) = sg v (-(2 * u)) := fun u => by
    rw [← neg_mul, sm, map_neg, map_ofNat, neg_mul]
  have s0 : sg v (0 : Kv v) = 0 := by simpa using (sm 0 0).symm
  have h4 : ∀ c u t, e (0, c) * e (u, t) = e (algebraMap F (Kv v) D.δ * (c * t), c * u) := fun c u t => by
    have a1 : ∀ x y, sg v (x * y) = sg v x * sg v y := fun x y => by rw [sm, sc]
    have a2 : ∀ x, sg v (algebraMap F (Kv v) D.δ * x) = rt D.δ * sg v x := fun x => (sm (rt D.δ) x).symm
    have a3 : (rt D.θ : A E) ^ 2 = AdeleBaseChange.adeleMap F E (rt D.δ) := by
      rw [← map_pow, D.sq]
      exact (AdeleBaseChange.adeleMap_algebraMap _).symm
    have : sg w (e (0, c) * e (u, t)) = sg w (e (algebraMap F (Kv v) D.δ * (c * t), c * u)) := by
      rw [← tc (e (0, c)), ← tm, h1, h1, h1, s0, a2, a1, a1]
      simp only [Dat.mkE, map_mul, map_zero, ← a3]
      ring
    simpa only [tc] using congrArg (cp w) this
  have key : ∀ y : Kv v, (∀ c, IsInt c → ψ (sg v (-(2 * (c * y)))) = 1) → IsInt y := fun y hy => by
    have : Valued.v (-(2 * y)) ≤ 1 := gm _ fun c hc => by
      have := hy c hc
      rwa [show -(2 * (c * y)) = c * -(2 * y) by ring] at this
    rwa [Valuation.map_neg, map_mul, hG.two, one_mul] at this
  refine ⟨fun x => ψ (sg v (-(2 * (e.symm x).1))), ⟨fun x y => ?_, fun x hx => ?_, fun x hx => ?_⟩, fun x => ?_⟩
  · beta_reduce
    rw [map_add (f := _), Prod.fst_add, mul_add, neg_add]
    exact ga _ _
  · obtain ⟨⟨u, t⟩, rfl⟩ := e.surjective x
    have hu : Valued.v u ≤ 1 := (le_max_left _ _).trans ((h2 u t).symm.le.trans hx)
    beta_reduce
    rw [e.symm_apply_apply]
    refine gi _ ?_
    show Valued.v _ ≤ 1
    rwa [Valuation.map_neg, map_mul, hG.two, one_mul]
  · obtain ⟨⟨u, t⟩, rfl⟩ := e.surjective x
    have hu : IsInt u := key u fun c hc => by
      have := hx (e (c, 0)) ((h2 c 0).le.trans (max_le hc (by simp)))
      beta_reduce at this
      rwa [h3, e.symm_apply_apply] at this
    have ht : Valued.v (algebraMap F (Kv v) D.δ * t) ≤ 1 := key _ fun c hc => by
      have := hx (e (0, c)) ((h2 0 c).le.trans (max_le (by simp) hc))
      beta_reduce at this
      rwa [h4, e.symm_apply_apply, mul_left_comm _ c t] at this
    rw [map_mul, hG.del, one_mul] at ht
    exact (h2 u t).le.trans (max_le hu ht)
  · obtain ⟨⟨u, t⟩, rfl⟩ := e.surjective x
    exact ⟨_, _, h1 u t, by beta_reduce; rw [hs, e.symm_apply_apply]⟩
end

