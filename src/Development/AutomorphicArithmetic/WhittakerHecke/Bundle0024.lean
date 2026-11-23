module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.GaussianProducts.ExistsRowSec

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.WhittakerUnipotentMulEqAdditiveCharMul
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

theorem UpperTheory.whittaker_unipotent_mul_eq_additiveChar_mul :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (f : GL (Fin 2) (A E) → ℂ), Pp.Lf f → ∀ (v : Fin 2 → A ℚ) (h : GL (Fin 2) (A E)),
        Wo D f (nE D v * h) = ψ (-(v 1)) * Wo D f h := by
  intro E _ _ D f hf v h
  have hadd : ∀ u w : Fin 2 → A ℚ, nE D (u + w) = nE D u * nE D w := fun u w => by
    simp only [nE, Pi.add_apply, D.mkE_add, Pp.n_add]
  let G : (Fin 2 → A ℚ) → ℂ := fun u => f (nE D u * h) * ψ (u 1)
  have hper : ∀ ξ ∈ GroundTheory.Automorphic.FourierWhittaker.vecLattice ℚ (Fin 2), ∀ x, G (ξ + x) = G x := by
    intro ξ hξ x
    obtain ⟨η, rfl⟩ := GroundTheory.Automorphic.FourierWhittaker.mem_vecLattice.1 hξ
    have e1 : D.mkE (rt (η 0) + x 0) (rt (η 1) + x 1) =
        rt (algebraMap ℚ E (η 0) + algebraMap ℚ E (η 1) * D.θ) + D.mkE (x 0) (x 1) := by
      rw [D.mkE_add, D.mkE_rt]
    change f (gl (nU (D.mkE (rt (η 0) + x 0) (rt (η 1) + x 1))) * h) * ψ (rt (η 1) + x 1) =
      f (gl (nU (D.mkE (x 0) (x 1))) * h) * ψ (x 1)
    rw [e1, hf.per, Pp.ψ_add, Pp.ψ_rt, one_mul]
  have key : ∫ u in FS2 ℚ, G (u + v) ∂(adeleMeasurePi ℚ) = ∫ u in FS2 ℚ, G u ∂(adeleMeasurePi ℚ) :=
    GroundTheory.Automorphic.FourierWhittaker.setIntegral_comp_add v hper
  have pt : ∀ u : Fin 2 → A ℚ, f (nE D u * (nE D v * h)) * ψ (u 1) = ψ (-(v 1)) * G (u + v) := by
    intro u
    have e2 : ψ (u 1) = ψ (-(v 1)) * ψ ((u + v) 1) := by
      rw [← Pp.ψ_add]
      congr 1
      simp only [Pi.add_apply]
      ring
    change _ = ψ (-(v 1)) * (f (nE D (u + v) * h) * ψ ((u + v) 1))
    rw [hadd, mul_assoc, e2]
    ring
  simp only [Wo, pt]
  rw [integral_const_mul]
  exact congrArg _ key
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.WhittakerUnipotentTranslateOfInfiniteComponentZe
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.whittaker_unipotent_translate_of_infinite_component_zero :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (φ : GL (Fin 2) (A E) → ℂ), Continuous φ → (∀ γ g, φ (ratGL E 2 γ * g) = φ g) → ∀ x : A ℚ, x.1 = 0 → ∀ (y : (A ℚ)ˣ) (X : GL (Fin 2) (Cinf E)), Wo D (fun g => φ (g * nu D x)) (em E (aE y) * infGL E 2 X) = ψ (-((y : A ℚ) * x)) * Wo D φ (em E (aE y) * infGL E 2 X) := by
  intro E _ _ _ D φ _ hL x hx y X
  have hfst : (AdeleBaseChange.adeleMap ℚ E x).1 = 0 := by
    obtain ⟨c1, c2⟩ := x
    obtain rfl : c1 = 0 := hx
    exact map_zero (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := ℚ) (L := E))
  have h0 : pInf E (D.mkE 0 x) = 0 := by
    have h1 : (D.mkE 0 x).1 = 0 := by
      have e : D.mkE 0 x = AdeleBaseChange.adeleMap ℚ E x * rt D.θ := by
        simp only [Dat.mkE, map_zero, zero_add]
      rw [e]
      change (AdeleBaseChange.adeleMap ℚ E x).1 * _ = 0
      rw [hfst, zero_mul]
    change (infEq E).symm (D.mkE 0 x).1 = 0
    rw [h1]
    exact map_zero _
  have hk : GeneralLinearGroup.map (pInf E) (Xg.nu D x) = 1 := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    change pInf E ((!![1, D.mkE 0 x; 0, 1] : Matrix (Fin 2) (Fin 2) (A E)) i j) = (1 : Matrix (Fin 2) (Fin 2) (Cinf E)) i j
    fin_cases i <;> fin_cases j <;> simp [h0]
  have hc : infGL E 2 X * Xg.nu D x = Xg.nu D x * infGL E 2 X := by
    have e := infGL_mul_finGL (Xg.nu D x)
    rw [hk, map_one, one_mul] at e
    rw [← e]
    exact infGL_comm X _
  rw [Nz.Wo_right, mul_assoc, hc, ← mul_assoc, Xg.nu, Nz.em_conj, mul_assoc, Nz.Wo_shift D hL]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.ZetaIntegralEqZeroOfMemMaximalCompactNotMemLevel
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem loc_dv {K Γ : Type} [Field K] [LinearOrderedCommGroupWithZero Γ] (w : Valuation K Γ) {c d z n : K}
    (hc : w c ≤ 1) (hd : w d ≤ 1) (hn : w n ≤ 1) (h0 : w (z * c) ≤ w n) (h1 : w (z * d - 1) ≤ w n) : w c ≤ w n := by
  rcases lt_or_eq_of_le hn with hlt | heq
  · have h2 : w (z * d - 1) < w 1 := by rw [map_one]; exact h1.trans_lt hlt
    have h3 : w (z * d) = 1 := by
      have e : z * d = (z * d - 1) + 1 := by ring
      rw [e, Valuation.map_add_eq_of_lt_right w h2, map_one]
    have h4 : 1 ≤ w z := by
      rw [map_mul] at h3
      calc (1 : Γ) = w z * w d := h3.symm
        _ ≤ w z * 1 := mul_le_mul' le_rfl hd
        _ = w z := mul_one _
    calc w c = 1 * w c := (one_mul _).symm
      _ ≤ w z * w c := mul_le_mul' h4 le_rfl
      _ = w (z * c) := (map_mul _ _ _).symm
      _ ≤ w n := h0
  · rw [heq]
    exact hc

private theorem nat_le_one (v : H.P ℚ) (N : ℕ) : Valued.v (N : H.Kv v) ≤ 1 := by
  have h : (N : H.Kv v) ∈ v.adicCompletionIntegers ℚ := natCast_mem _ N
  exact h

theorem UpperTheory.zeta_integral_eq_zero_of_mem_maximal_compact_not_mem_level :
    ∀ (N : ℕ), 0 < N → ∀ (p : MvPolynomial (Fin 2) ℂ) (s : ℂ), ∀ k ∈ KK ℚ, k ∉ SS N → Zr N p s k = 0 := by
  intro N _ p s k hk hkS
  have hz : ∀ z : IdeleGroup ℚ, (PhiN N p fun j => ((z : (A ℚ)ˣ) : A ℚ) * row k j) = 0 := by
    intro z
    unfold PhiN
    rw [if_neg]
    intro h
    apply hkS
    intro v
    obtain ⟨h0, h1⟩ := h v
    have hint : ∀ i j, Valued.v (H.cp v (k i j)) ≤ 1 := fun i j => hk.2 v i j
    have e0 : H.cp v (((z : (A ℚ)ˣ) : A ℚ) * row k 0) = H.cp v ((z : (A ℚ)ˣ) : A ℚ) * H.cp v (k 1 0) := map_mul _ _ _
    have e1 : H.cp v (((z : (A ℚ)ˣ) : A ℚ) * row k 1 - 1) = H.cp v ((z : (A ℚ)ˣ) : A ℚ) * H.cp v (k 1 1) - 1 := by
      rw [map_sub, map_one]
      exact congrArg (· - 1) (map_mul _ _ _)
    have h0' : Valued.v (H.cp v (((z : (A ℚ)ˣ) : A ℚ) * row k 0)) ≤ Valued.v (N : H.Kv v) := h0
    have h1' : Valued.v (H.cp v (((z : (A ℚ)ˣ) : A ℚ) * row k 1 - 1)) ≤ Valued.v (N : H.Kv v) := h1
    rw [e0] at h0'
    rw [e1] at h1'
    exact loc_dv Valued.v (hint 1 0) (hint 1 1) (nat_le_one v N) h0' h1'
  simp only [Zr, hz, zero_mul, MeasureTheory.integral_zero]
end

