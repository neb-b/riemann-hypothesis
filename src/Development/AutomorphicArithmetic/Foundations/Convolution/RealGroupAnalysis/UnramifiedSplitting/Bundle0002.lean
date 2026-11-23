module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.SplitAt
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.Bundle0010
public import GroundTheory.AutomorphicForms.MacdonaldHecke

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.CosetShift
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical
open scoped nonZeroDivisors

private theorem coset_shift {K : Type} [Field K] [NumberField K]
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (b x s : FiniteAdeleRing (𝓞 K) K)
    (hs : s ∈ idealFiniteAdeles J) : cosetIndicator J b (x + s) = cosetIndicator J b x := by
  rw [cosetIndicator_apply, cosetIndicator_apply]
  have e : x + s - b = (x - b) + s := by ring
  have h : x + s - b ∈ idealFiniteAdeles J ↔ x - b ∈ idealFiniteAdeles J := by
    rw [e]
    exact AddSubgroup.add_mem_cancel_right _ hs
  simp only [h]

private theorem std_gen {K : Type} [Field K] [NumberField K]
    (J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (v : P K)
    (hJ : FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K) = 0) (y : Kv v) (hy : IsInt y) :
    (sg v y).2 ∈ idealFiniteAdeles J := by
  rw [mem_idealFiniteAdeles]
  intro v'
  obtain ⟨-, -, -, -, -, -, -, h8, -⟩ := sgLaws K v
  by_cases hv : v' = v
  · subst hv
    have h3 := ((sgLaws K v').2.2.1 y)
    have : (sg v' y).2 v' = y := h3
    rw [this, hJ, neg_zero, WithZero.exp_zero]
    exact hy
  · rw [(h8 y).2 v' hv]
    change Valued.v (0 : v'.adicCompletion K) ≤ _
    rw [map_zero]
    exact zero_le

theorem UpperTheory.ConvolutionTheory.R2.H.stdAe :
    ∀ (K : Type) [Field K] [NumberField K] (φ : S4 K), ∀ᶠ v in cofinite, Std v φ.1 := by
  intro K _ _ φ
  obtain ⟨f, hf⟩ := φ
  change ∀ᶠ v in cofinite, Std v f
  rw [schwartzBruhatPi_eq_cosetSpanPi] at hf
  induction hf using Submodule.span_induction with
  | mem F h =>
    obtain ⟨g, J, b, rfl⟩ := h
    have h1 : ∀ᶠ v : P K in cofinite, FractionalIdeal.count K v (J : FractionalIdeal (𝓞 K)⁰ K) = 0 :=
      FractionalIdeal.finite_factors (J : FractionalIdeal (𝓞 K)⁰ K)
    have h2 : ∀ᶠ v : P K in cofinite, ∀ i, Valued.v ((b i) v) ≤ 1 :=
      eventually_all.2 fun i => (b i).2
    filter_upwards [h1, h2] with v hJ hb
    refine ⟨fun x hx i => ?_, fun x y hy => ?_⟩
    · have hi : cosetIndicator J (b i) ((x i).2) ≠ 0 := by
        intro h0
        apply hx
        simp only [schwartzBruhatTensorPi, finiteTensor, finPartPi]
        rw [Finset.prod_eq_zero (Finset.mem_univ i) h0, mul_zero]
      rw [cosetIndicator_apply] at hi
      have hm : (x i).2 - b i ∈ idealFiniteAdeles J := by
        by_contra hc
        exact hi (if_neg hc)
      have hv := (mem_idealFiniteAdeles J).1 hm v
      rw [hJ, neg_zero, WithZero.exp_zero] at hv
      have e : (x i).2 v = ((x i).2 - b i) v + (b i) v := by
        change _ = (x i).2 v - (b i) v + (b i) v
        ring
      change Valued.v ((x i).2 v) ≤ 1
      rw [e]
      exact (Valuation.map_add _ _ _).trans (max_le hv (hb i))
    · have e : ∀ i, (x i + sg v (y i)).1 = (x i).1 := fun i => by
        change (x i).1 + (sg v (y i)).1 = _
        rw [((sgLaws K v).2.2.2.2.2.2.2.1 (y i)).1, add_zero]
      have e2 : ∀ i, cosetIndicator J (b i) (x i + sg v (y i)).2 = cosetIndicator J (b i) (x i).2 :=
        fun i => coset_shift J (b i) _ _ (std_gen J v hJ (y i) (hy i))
      have e3 : infPartPi (fun i => x i + sg v (y i)) = infPartPi x := by
        unfold infPartPi
        simp only [e]
      simp only [schwartzBruhatTensorPi, finiteTensor, finPartPi, e2, e3]
  | zero =>
    refine Eventually.of_forall fun v => ⟨fun x hx => absurd rfl hx, fun x y _ => rfl⟩
  | add f g _ _ ihf ihg =>
    filter_upwards [ihf, ihg] with v a c
    refine ⟨fun x hx i => ?_, fun x y hy => ?_⟩
    · by_cases h : f x = 0
      · refine c.1 x (fun h' => hx ?_) i
        simp [h, h']
      · exact a.1 x h i
    · simp only [Pi.add_apply, a.2 x y hy, c.2 x y hy]
  | smul t f _ ih =>
    filter_upwards [ih] with v a
    refine ⟨fun x hx i => ?_, fun x y hy => ?_⟩
    · refine a.1 x (fun h' => hx ?_) i
      simp [h']
    · simp only [Pi.smul_apply, a.2 x y hy]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.GoodOfGoodAt
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

private theorem psi_sg {K : Type} [Field K] [NumberField K] (v : P K) (x : Kv v) :
    ψ (sg v x) = UpperTheory.V.Af.Smo.psiL v x := rfl

private theorem val_ae {K : Type} [Field K] [NumberField K] (a : K) (ha : a ≠ 0) :
    ∀ᶠ v : P K in cofinite, Valued.v (algebraMap K (Kv v) a) = 1 := by
  have h1 := HeightOneSpectrum.Support.finite (𝓞 K) a
  have h2 := HeightOneSpectrum.Support.finite (𝓞 K) a⁻¹
  filter_upwards [h1.compl_mem_cofinite, h2.compl_mem_cofinite] with v hv1 hv2
  have e : Valued.v (algebraMap K (Kv v) a) = v.valuation K a :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a
  rw [e]
  have n1 : v.valuation K a ≤ 1 := not_lt.1 hv1
  have n2 : (v.valuation K a)⁻¹ ≤ 1 := by
    have : v.valuation K a⁻¹ ≤ 1 := not_lt.1 hv2
    rwa [map_inv₀] at this
  have h0 : v.valuation K a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  exact le_antisymm n1 ((inv_le_one₀ (zero_lt_iff.2 h0)).1 n2)

private theorem good_of_goodAt {K : Type} [Field K] [NumberField K] (v : P K)
    (h : UpperTheory.V.Af.Smo.GoodAt v (UpperTheory.V.Af.Smo.psiL v)) :
    Good fun x : Kv v => ψ (sg v x) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun x y => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · simp only [psi_sg]
    exact AddChar.map_add_eq_mul _ x y
  · exact (psi_sg v x).trans (h1 x hx)
  · by_contra hni
    have hlt : 1 < Valued.v x := not_le.1 hni
    obtain ⟨ϖ, hϖ⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective K v (WithZero.exp (-1 : ℤ))
    obtain ⟨y, hy, hy1⟩ := h2 ϖ hϖ
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hlt
      exact not_lt_zero' hlt
    have hv0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx0
    have hxe : WithZero.exp (1 : ℤ) ≤ Valued.v x := by
      rw [← WithZero.exp_log hv0]
      rw [← WithZero.exp_log hv0, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
      rw [WithZero.exp_le_exp]
      omega
    have hyv : Valued.v (ϖ * y) ≤ 1 := hy
    rw [map_mul, hϖ] at hyv
    have hye : Valued.v y ≤ WithZero.exp (1 : ℤ) := by
      have := mul_le_mul_right hyv (WithZero.exp (1 : ℤ))
      rwa [← mul_assoc, ← WithZero.exp_add, show (1 : ℤ) + -1 = 0 by norm_num, WithZero.exp_zero,
        one_mul, mul_one] at this
    have hc : IsInt (y * x⁻¹) := by
      change Valued.v (y * x⁻¹) ≤ 1
      rw [map_mul, map_inv₀]
      exact mul_inv_le_one_of_le₀ (hye.trans hxe) zero_le'
    have := hx _ hc
    rw [mul_assoc, inv_mul_cancel₀ hx0, mul_one] at this
    exact hy1 ((psi_sg v y).symm.trans this)

theorem UpperTheory.ConvolutionTheory.R2.H.gdAe :
    ∀ (K : Type) [Field K] [NumberField K] (δ : K), δ ≠ 0 → ∀ᶠ v in cofinite, Gd δ v := by
  intro K _ _ δ hδ
  have h2 : (2 : K) ≠ 0 := two_ne_zero
  filter_upwards [(UpperTheory.V.Af.Smo.psiLoc K).2, val_ae (2 : K) h2, val_ae δ hδ] with v hg ht hd
  rw [map_ofNat] at ht
  exact ⟨good_of_goodAt v hg, ht, hd⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.HeckeExpl
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

section Cosets

open GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GLnLocal Iwasawa HeckeAlgebra
open scoped ValuativeRel

attribute [local instance] GroundTheory.Automorphic.Spherical.fintypeResidue

private theorem coset_sum {K : Type} [Field K] [NumberField K] (v : P K) (n : ℕ) {B : Multiset ℂˣ}
    {W : GL (Fin n) (Kv v) → ℂ} (hE : Eig v B W) {r : ℕ} (hr : r ≤ n) (g : GL (Fin n) (Kv v)) :
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard r, ∑ c : Pairs S → 𝓀[Kv v], W (g * gMat S c) =
      GlobalTheory.LFun.satEig (Formalism.UG.qV K v) n B r * W g := by
  obtain ⟨hK, hu, -, -⟩ := UpperTheory.V.Af.Smo.sphDict K n v
  borelize (GL (Fin n) (Kv v))
  let μ : Measure (GL (Fin n) (Kv v)) := Measure.haar
  have hf : ∀ g, ∀ k ∈ integralGL (Kv v) n, W (g * k) = W g := by
    rw [hK]
    exact hE.inv
  have hKp : (μ.real (integralGL (Kv v) n : Set (GL (Fin n) (Kv v))) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2
      (measureReal_compactOpen_pos μ (isCompact_integralGL _ n) (isOpen_integralGL _ n)).ne'
  have h1 := integral_minusculeHecke_mul (F := Kv v) (n := n) (μ := μ) hf g r
  have hcs : HasCompactSupport fun x => (minusculeHecke μ r : HeckeAlgebra μ) x * W (g * x) := by
    refine HasCompactSupport.intro (isCompact_minusculeSet r) fun x hx => ?_
    simp only [minusculeHecke_apply, Set.indicator_of_notMem hx, zero_mul]
  have h2 := integral_eq_smul_finsum_coset μ (integralOpen (Kv v) n) (isCompact_integralGL _ n) hcs (fun x k hk => by
      rw [(HeckeAlgebraLevel.val_mem _ _ (minusculeHecke μ r) k hk x).2, ← mul_assoc, hf _ k hk])
  have h3 : ∑ᶠ c : GL (Fin n) (Kv v) ⧸ integralGL (Kv v) n,
      (minusculeSet (Kv v) n r).indicator (fun _ => (1 : ℂ)) c.out * W (g * c.out) =
        GlobalTheory.LFun.satEig (Formalism.UG.qV K v) n B r * W g := by
    rw [hK, ← UpperTheory.V.Af.Smo.tjSet UpperTheory.V.Af.Smo.sphDict K n v r hr]
    exact hE.eig _ hu r hr g
  refine mul_left_cancel₀ hKp (h1.symm.trans (h2.trans ?_))
  change μ.real (integralGL (Kv v) n : Set _) •
    (∑ᶠ c : GL (Fin n) (Kv v) ⧸ integralGL (Kv v) n,
      (minusculeHecke μ r : HeckeAlgebra μ) c.out * W (g * c.out)) = _
  rw [Complex.real_smul]
  simp only [minusculeHecke_apply, h3]

end Cosets

section Cosets2

open GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GLnLocal Iwasawa HeckeAlgebra
open scoped ValuativeRel

attribute [local instance] GroundTheory.Automorphic.Spherical.fintypeResidue

variable {K : Type} [Field K] [NumberField K]

private theorem dL_mul {v : P K} (a a' d d' : (Kv v)ˣ) : dL a d * dL a' d' = dL (a * a') (d * d') :=
  Units.ext (by ext i j; fin_cases i <;> fin_cases j <;> simp [dL])

private theorem dL_mem {v : P K} {a d : (Kv v)ˣ} (ha : Valued.v (a : Kv v) = 1) (hd : Valued.v (d : Kv v) = 1) :
    dL a d ∈ GlobalTheory.LFun.KGL v (n := 2) := by
  obtain ⟨hK, -, -, -⟩ := UpperTheory.V.Af.Smo.sphDict K 2 v
  have e : ∀ x : Kv v, Valued.v x ≤ 1 → x ∈ (ValuativeRel.valuation (Kv v)).integer :=
    fun x hx => (GroundTheory.Global.mem_valuationInteger_iff v x).2 hx
  have ha' : Valued.v ((a⁻¹ : (Kv v)ˣ) : Kv v) = 1 := by simp [ha]
  have hd' : Valued.v ((d⁻¹ : (Kv v)ˣ) : Kv v) = 1 := by simp [hd]
  rw [← hK, mem_integralGL_iff]
  refine ⟨fun i j => e _ ?_, fun i j => e _ ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [dL, ha, hd]
  · change Valued.v ((!![((a⁻¹ : (Kv v)ˣ) : Kv v), 0; 0, ((d⁻¹ : (Kv v)ˣ) : Kv v)] : Matrix (Fin 2) (Fin 2) (Kv v)) i j) ≤ 1
    fin_cases i <;> fin_cases j <;> simp [ha, hd]

private noncomputable def pi0 (v : P K) : (Kv v)ˣ := Units.mk0 (GLnLocal.uniformizer (Kv v) : Kv v) (Cartan.uniformizer_ne_zero _)

private noncomputable def lf (v : P K) (a : 𝓀[Kv v]) : Kv v := ((residueLift (Kv v) a : 𝒪[Kv v]) : Kv v)

private theorem lf_inj (v : P K) : Function.Injective (lf v) := by
  intro a b h
  have : residueLift (Kv v) a = residueLift (Kv v) b := Subtype.ext h
  rw [← residue_residueLift (F := Kv v) a, this, residue_residueLift]

private def p0 : Pairs ({0} : Finset (Fin 2)) := ⟨(0, 1), by simp, by simp, by simp⟩

private instance : Unique (Pairs ({0} : Finset (Fin 2))) where
  default := p0
  uniq := by
    rintro ⟨⟨a, b⟩, ha, hb, hab⟩
    have key : ∀ b : Fin 2, b ≠ 0 → b = 1 := by decide
    obtain rfl : a = 0 := Finset.mem_singleton.1 ha
    obtain rfl : b = 1 := key b fun h => hb (Finset.mem_singleton.2 h)
    rfl

private instance : IsEmpty (Pairs ({1} : Finset (Fin 2))) where
  false := by
    rintro ⟨⟨a, b⟩, ha, hb, hab⟩
    fin_cases a <;> fin_cases b <;> simp_all

private instance : IsEmpty (Pairs (Finset.univ : Finset (Fin 2))) where
  false := by
    rintro ⟨⟨a, b⟩, ha, hb, hab⟩
    simp at hb

private theorem gMat_zero (v : P K) (c : Pairs ({0} : Finset (Fin 2)) → 𝓀[Kv v]) :
    gMat {0} c = nL (lf v (c default)) * dL (pi0 v) 1 := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have hg (S : Finset (Fin 2)) (c : Pairs S → 𝓀[Kv v]) (i j : Fin 2) :
      (gMat S c : GL (Fin 2) (Kv v)) i j = ((1 : Matrix (Fin 2) (Fin 2) (Kv v)) i j + cMat S c i j) *
        GLnLocal.uniformizer (Kv v) ^ lamS S j := by
    change (((unipC S c : GL (Fin 2) (Kv v)) * (torusPow (Kv v) 2 (lamS S) : GL (Fin 2) (Kv v))) : Matrix (Fin 2) (Fin 2) (Kv v)) i j = _
    rw [coe_torusPow, mul_diagonal, coe_unipC, Matrix.add_apply]
  rw [hg]
  fin_cases i <;> fin_cases j <;> simp [cMat, lamS, nL, dL, pi0, lf]
  rfl

private theorem gMat_one (v : P K) (c : Pairs ({1} : Finset (Fin 2)) → 𝓀[Kv v]) :
    gMat {1} c = dL 1 (pi0 v) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have hg (S : Finset (Fin 2)) (c : Pairs S → 𝓀[Kv v]) (i j : Fin 2) :
      (gMat S c : GL (Fin 2) (Kv v)) i j = ((1 : Matrix (Fin 2) (Fin 2) (Kv v)) i j + cMat S c i j) *
        GLnLocal.uniformizer (Kv v) ^ lamS S j := by
    change (((unipC S c : GL (Fin 2) (Kv v)) * (torusPow (Kv v) 2 (lamS S) : GL (Fin 2) (Kv v))) : Matrix (Fin 2) (Fin 2) (Kv v)) i j = _
    rw [coe_torusPow, mul_diagonal, coe_unipC, Matrix.add_apply]
  rw [hg]
  fin_cases i <;> fin_cases j <;> simp [cMat, lamS, dL, pi0]

private theorem gMat_top (v : P K) (c : Pairs (Finset.univ : Finset (Fin 2)) → 𝓀[Kv v]) :
    gMat Finset.univ c = dL (pi0 v) (pi0 v) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  have hg (S : Finset (Fin 2)) (c : Pairs S → 𝓀[Kv v]) (i j : Fin 2) :
      (gMat S c : GL (Fin 2) (Kv v)) i j = ((1 : Matrix (Fin 2) (Fin 2) (Kv v)) i j + cMat S c i j) *
        GLnLocal.uniformizer (Kv v) ^ lamS S j := by
    change (((unipC S c : GL (Fin 2) (Kv v)) * (torusPow (Kv v) 2 (lamS S) : GL (Fin 2) (Kv v))) : Matrix (Fin 2) (Fin 2) (Kv v)) i j = _
    rw [coe_torusPow, mul_diagonal, coe_unipC, Matrix.add_apply]
  rw [hg]
  fin_cases i <;> fin_cases j <;> simp [cMat, lamS, dL, pi0]

private theorem sum_one (v : P K) (f : GL (Fin 2) (Kv v) → ℂ) :
    ∑ S ∈ (Finset.univ : Finset (Fin 2)).powersetCard 1, ∑ c : Pairs S → 𝓀[Kv v], f (gMat S c) =
      ∑ a : 𝓀[Kv v], f (nL (lf v a) * dL (pi0 v) 1) + f (dL 1 (pi0 v)) := by
  rw [Finset.powersetCard_one, Finset.sum_map, Fin.sum_univ_two]
  simp only [Function.Embedding.coeFn_mk]
  congr 1
  · refine Fintype.sum_equiv (Equiv.funUnique (Pairs ({0} : Finset (Fin 2))) 𝓀[Kv v]) _ _ fun c => ?_
    rw [gMat_zero]
    rfl
  · rw [Fintype.sum_unique, gMat_one]

private theorem sum_two (v : P K) (f : GL (Fin 2) (Kv v) → ℂ) :
    ∑ S ∈ (Finset.univ : Finset (Fin 2)).powersetCard 2, ∑ c : Pairs S → 𝓀[Kv v], f (gMat S c) =
      f (dL (pi0 v) (pi0 v)) := by
  have hp : (Finset.univ : Finset (Fin 2)).powersetCard 2 = {Finset.univ} := by
    have := Finset.powersetCard_self (Finset.univ : Finset (Fin 2))
    rwa [Finset.card_univ, Fintype.card_fin] at this
  rw [hp, Finset.sum_singleton, Fintype.sum_unique, gMat_top]

private theorem sat_one (q : ℕ) (α β : ℂˣ) :
    GlobalTheory.LFun.satEig q 2 {α, β} 1 = (q : ℂ) ^ (1 / 2 : ℂ) * ((α : ℂ) + β) := by
  have : GlobalTheory.LFun.satEig q 2 {α, β} 1 = (q : ℂ) ^ ((((1 : ℕ) : ℂ) * (((2 : ℕ) : ℂ) - ((1 : ℕ) : ℂ))) / 2) * (Multiset.map (fun b : ℂˣ => (b : ℂ)) {α, β}).esymm 1 := rfl
  rw [this]
  norm_num [Multiset.esymm, Multiset.insert_eq_cons, Multiset.powersetCard_one]
  exact Or.inl (add_comm _ _)

private theorem sat_two (q : ℕ) (α β : ℂˣ) :
    GlobalTheory.LFun.satEig q 2 {α, β} 2 = (α : ℂ) * β := by
  have : GlobalTheory.LFun.satEig q 2 {α, β} 2 = (q : ℂ) ^ ((((2 : ℕ) : ℂ) * (((2 : ℕ) : ℂ) - ((2 : ℕ) : ℂ))) / 2) * (Multiset.map (fun b : ℂˣ => (b : ℂ)) {α, β}).esymm 2 := rfl
  rw [this]
  norm_num [Multiset.esymm, Multiset.insert_eq_cons, Multiset.powersetCard_cons, Multiset.powersetCard_one]

private theorem card_res (v : P K) : Fintype.card 𝓀[Kv v] = Ideal.absNorm v.asIdeal := by
  rw [← Nat.card_eq_fintype_card, GroundTheory.Global.natCard_residueField_integer, Ideal.absNorm_apply, Submodule.cardQuot_apply]

end Cosets2

section Main

attribute [local instance] GroundTheory.Automorphic.Spherical.fintypeResidue

theorem UpperTheory.ConvolutionTheory.R2.H.heckeExpl :
    ∀ (K : Type) [Field K] [NumberField K] (v : P K) (ϖ : (Kv v)ˣ), IsU ϖ → ∃ R : Finset (Kv v), R.card = Ideal.absNorm v.asIdeal ∧ (∀ b ∈ R, IsInt b) ∧
      ∀ (α β : ℂˣ) (W : GL (Fin 2) (Kv v) → ℂ), Eig v {α, β} W → ∀ g,
        q v ^ (1 / 2 : ℂ) * ((α : ℂ) + β) * W g = ∑ b ∈ R, W (g * nL b * dL ϖ 1) + W (g * dL 1 ϖ) ∧ W (g * dL ϖ ϖ) = (α : ℂ) * β * W g := by
  intro K _ _ v ϖ hϖ
  obtain ⟨-, hu, -, -⟩ := UpperTheory.V.Af.Smo.sphDict K 2 v
  have hv : Valued.v (((pi0 v)⁻¹ * ϖ : (Kv v)ˣ) : Kv v) = 1 := by
    have h0 : Valued.v ((pi0 v : (Kv v)ˣ) : Kv v) = Valued.v (ϖ : Kv v) := hu.trans hϖ.symm
    have hne : Valued.v ((pi0 v : (Kv v)ˣ) : Kv v) ≠ 0 := by simp
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, ← h0, inv_mul_cancel₀ hne]
  set u : (Kv v)ˣ := (pi0 v)⁻¹ * ϖ with hu_def
  have hϖu : ϖ = pi0 v * u := by rw [hu_def, mul_inv_cancel_left]
  have hone : Valued.v (((1 : (Kv v)ˣ)) : Kv v) = 1 := by simp
  refine ⟨Finset.univ.image (lf v), ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ (lf_inj v), Finset.card_univ, card_res]
  · intro b hb
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hb
    exact (GroundTheory.Global.mem_valuationInteger_iff v _).1 (GroundTheory.Automorphic.Spherical.residueLift (Kv v) a).2
  · intro α β W hE g
    have inv := hE.inv
    have s1 := coset_sum v 2 hE (r := 1) (by norm_num) g
    have s2 := coset_sum v 2 hE (r := 2) le_rfl g
    rw [sum_one v fun x => W (g * x), sat_one] at s1
    rw [sum_two v fun x => W (g * x), sat_two] at s2
    have e1 : ∀ b, W (g * nL b * dL ϖ 1) = W (g * (nL b * dL (pi0 v) 1)) := by
      intro b
      have : dL ϖ (1 : (Kv v)ˣ) = dL (pi0 v) 1 * dL u 1 := by rw [dL_mul, ← hϖu, mul_one]
      rw [this, ← mul_assoc, ← mul_assoc, inv _ _ (dL_mem hv hone)]
    have e2 : W (g * dL 1 ϖ) = W (g * dL 1 (pi0 v)) := by
      have : dL (1 : (Kv v)ˣ) ϖ = dL 1 (pi0 v) * dL 1 u := by rw [dL_mul, ← hϖu, mul_one]
      rw [this, ← mul_assoc, inv _ _ (dL_mem hone hv)]
    have e3 : W (g * dL ϖ ϖ) = W (g * dL (pi0 v) (pi0 v)) := by
      have : dL ϖ ϖ = dL (pi0 v) (pi0 v) * dL u u := by rw [dL_mul, ← hϖu]
      rw [this, ← mul_assoc, inv _ _ (dL_mem hv hv)]
    refine ⟨?_, ?_⟩
    · rw [Finset.sum_image fun a _ b _ h => lf_inj v h, e2]
      simp only [e1]
      exact s1.symm
    · rw [e3]
      exact s2

end Main
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.LcLaws
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.H.lcLaws :
    ∀ (K : Type) [Field K] [NumberField K] (v : P K), (∀ b, lc v (nL b) = gl (nU (sg v b))) ∧ (∀ a, lc v (dL a a⁻¹) = gl (mD (idl v a))) ∧ (∀ t, lc v (dL 1 t) = dM (idl v t)) ∧
      (∀ a, lc v (dL a 1) = aE (idl v a)) ∧ (∀ a, lc v (dL a a) = Matrix.GeneralLinearGroup.scalar (Fin 2) (idl v a)) ∧
      (∀ y, Matrix.GeneralLinearGroup.map (cp v) (lc v y) = y) ∧
      ∀ (g : GL (Fin 2) (A K)) y, lc v y * g = g * lc v ((Matrix.GeneralLinearGroup.map (cp v) g)⁻¹ * y * Matrix.GeneralLinearGroup.map (cp v) g) := by
  intro K _ _ v
  obtain ⟨hadd, hmul, hcp, hidl, hlc, -, -, -, -, -⟩ := sgLaws K v
  have h0 : sg v 0 = 0 := by
    have := hadd 0 0
    simpa using this
  have hinv : ∀ a : (Kv v)ˣ, idl v a⁻¹ = (idl v a)⁻¹ := fun a => map_inv (localIdele K v) a
  have hv : ∀ a : (Kv v)ˣ, 1 + sg v ((a : Kv v) - 1) = ((idl v a : (A K)ˣ) : A K) := fun a => (hidl a).symm
  have hvi : ∀ a : (Kv v)ˣ, 1 + sg v (((a⁻¹ : (Kv v)ˣ) : Kv v) - 1) = (((idl v a)⁻¹ : (A K)ˣ) : A K) := fun a => by
    rw [← hinv, hidl]
  have hvi' : ∀ a : (Kv v)ˣ, 1 + sg v ((a : Kv v)⁻¹ - 1) = (((idl v a)⁻¹ : (A K)ˣ) : A K) := fun a => by
    rw [← hvi a, Units.val_inv_eq_inv_val]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    apply Units.ext
    ext i j
    rw [hlc]
    fin_cases i <;> fin_cases j <;> simp [nL, nU, h0] <;> rfl
  · intro a
    apply Units.ext
    ext i j
    rw [hlc]
    fin_cases i <;> fin_cases j <;> simp [dL, mD, h0, hv, hvi'] <;> rfl
  · intro t
    apply Units.ext
    ext i j
    rw [hlc]
    fin_cases i <;> fin_cases j <;> simp [dL, dM, h0, hv]
  · intro a
    apply Units.ext
    ext i j
    rw [hlc]
    fin_cases i <;> fin_cases j <;> simp [dL, aE, h0, hv]
  · intro a
    apply Units.ext
    ext i j
    rw [hlc]
    fin_cases i <;> fin_cases j <;> simp [dL, h0, hv]
  · intro y
    apply Units.ext
    ext i j
    rw [Matrix.GeneralLinearGroup.map_apply, hlc, map_add (f := _), hcp]
    fin_cases i <;> fin_cases j <;> simp
  · intro g y
    have one_l : ∀ (R : Type) [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) (i j : Fin 2),
        (1 : Matrix (Fin 2) (Fin 2) R) i 0 * M 0 j + (1 : Matrix (Fin 2) (Fin 2) R) i 1 * M 1 j = M i j := fun R _ M i j => by
      have := congrFun (congrFun (Matrix.one_mul M) i) j
      rwa [Matrix.mul_apply, Fin.sum_univ_two] at this
    have one_r : ∀ (R : Type) [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) (i j : Fin 2),
        M i 0 * (1 : Matrix (Fin 2) (Fin 2) R) 0 j + M i 1 * (1 : Matrix (Fin 2) (Fin 2) R) 1 j = M i j := fun R _ M i j => by
      have := congrFun (congrFun (Matrix.mul_one M) i) j
      rwa [Matrix.mul_apply, Fin.sum_univ_two] at this
    have hr : ∀ (x : Kv v) (a : A K), sg v x * a = sg v (x * cp v a) := fun x a => by
      rw [mul_comm, hmul, mul_comm]
    set gv := Matrix.GeneralLinearGroup.map (cp v) g with hgv
    have hgva : ∀ i j, gv.val i j = cp v (g.val i j) := fun i j => by
      rw [hgv, Matrix.GeneralLinearGroup.map_apply]
    generalize hzd : gv⁻¹ * y * gv = z
    have hz : gv * z = y * gv := by
      rw [← hzd]; group
    apply Units.ext
    ext i j
    have hz' : gv.val i 0 * z.val 0 j + gv.val i 1 * z.val 1 j = y.val i 0 * gv.val 0 j + y.val i 1 * gv.val 1 j := by
      have := congrArg (fun h : GL (Fin 2) (Kv v) => h.val i j) hz
      simpa only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two] using this
    simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hlc]
    simp only [add_mul, mul_add, hr, hmul, ← hgva]
    have e : (y.val i 0 - (1 : Matrix (Fin 2) (Fin 2) (Kv v)) i 0) * gv.val 0 j + (y.val i 1 - (1 : Matrix (Fin 2) (Fin 2) (Kv v)) i 1) * gv.val 1 j
        = gv.val i 0 * (z.val 0 j - (1 : Matrix (Fin 2) (Fin 2) (Kv v)) 0 j) + gv.val i 1 * (z.val 1 j - (1 : Matrix (Fin 2) (Fin 2) (Kv v)) 1 j) := by
      linear_combination -hz' - one_l (Kv v) gv.val i j + one_r (Kv v) gv.val i j
    have es := congrArg (sg v) e
    rw [hadd, hadd] at es
    linear_combination es + one_l (A K) g.val i j - one_r (A K) g.val i j
end

