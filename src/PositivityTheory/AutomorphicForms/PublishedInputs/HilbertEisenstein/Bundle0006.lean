module

public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.IdeleModuleInfIdDetLe
public import GroundTheory.GlobalFields.Adele.Bundle0001
public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.Bundle0004
public import GroundTheory.AutomorphicForms.GL2.GodementSectionFactor
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalPlace
public import GroundTheory.LocalFields.LocalZetaGauss
public import GroundTheory.LocalFields.LocalZeta
public import GroundTheory.GlobalFields.TateThesis.Bundle0010
public import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
public import GroundTheory.GlobalFields.TateThesis.Bundle0008
public import GroundTheory.GlobalFields.TateThesis.Bundle0002
public import GroundTheory.GlobalFields.TateThesis.Bundle0009

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.AbsPInfModuleSection
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix nonZeroDivisors
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.eisensteinGrowth

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def sig (v : InfinitePlace F) (x : F) : ℝ := UpperTheory.V.TR.pInf F (algebraMap F (Ad F) x) v

theorem abs_pInf (x : Ad F) (v : InfinitePlace F) : |UpperTheory.V.TR.pInf F x v| = ‖x.1 v‖ := by
  have h := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    (IsTotallyReal.isReal v)).norm_map_of_map_zero (map_zero _) (x.1 v)
  rw [Real.norm_eq_abs] at h
  exact h

theorem abs_sig (v : InfinitePlace F) (x : F) : |sig v x| = v x := by
  rw [sig, abs_pInf]
  exact GroundTheory.Global.norm_algebraMap_apply F x v

theorem one_le_norm_mul_prod {D : 𝓞 F} (hD : D ≠ 0) {x : F} (hx0 : x ≠ 0) (hx : ∃ r : 𝓞 F, (D : F) * x = r) :
    1 ≤ |((Algebra.norm ℚ (D : F) : ℚ) : ℝ)| * ∏ v, |sig v x| := by
  have hprod : ∀ y : F, ∏ v, |sig v y| = |((Algebra.norm ℚ y : ℚ) : ℝ)| := by
    intro y
    simp_rw [abs_sig]
    rw [← Rat.cast_abs, ← InfinitePlace.prod_eq_abs_norm]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [(IsTotallyReal.isReal w).mult_eq_one, pow_one]
  obtain ⟨r, hr⟩ := hx
  have hDF : (D : F) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hD
  have hr0 : r ≠ 0 := by
    rintro rfl
    have : (D : F) * x = 0 := by rw [hr]; simp
    exact mul_ne_zero hDF hx0 this
  rw [hprod, ← abs_mul, ← Rat.cast_mul, ← map_mul, hr]
  exact GroundTheory.Global.one_le_abs_norm_of_ne_zero hr0

omit [IsTotallyReal F] in
theorem arch_factor_bound (k m : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ p q : ℝ,
    ‖((p : ℂ) + Complex.I * (q : ℂ)) * Complex.exp (-(Real.pi : ℂ) * ((p : ℂ) ^ 2 + (q : ℂ) ^ 2))‖ *
      (max |p| |q|) ^ k * (1 + (max |p| |q|) ^ 2) ^ m ≤ C := by
  refine ⟨Real.exp 1 * (Nat.factorial (1 + k + m) : ℝ), by positivity, fun p q => ?_⟩
  set s := p ^ 2 + q ^ 2 with hs
  have hs0 : 0 ≤ s := by positivity
  have hnorm : ‖((p : ℂ) + Complex.I * (q : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * ((p : ℂ) ^ 2 + (q : ℂ) ^ 2))‖ =
      Real.sqrt s * Real.exp (-Real.pi * s) := by
    rw [norm_mul]
    congr 1
    · rw [mul_comm Complex.I, Complex.norm_add_mul_I]
    · have : -(Real.pi : ℂ) * ((p : ℂ) ^ 2 + (q : ℂ) ^ 2) = ((-Real.pi * s : ℝ) : ℂ) := by
        rw [hs]; push_cast; ring
      rw [this, Complex.norm_exp_ofReal]
  set ρ := max |p| |q| with hρ
  have hρ0 : 0 ≤ ρ := le_max_of_le_left (abs_nonneg p)
  have hρs : ρ ^ 2 ≤ s := by
    rcases max_choice |p| |q| with h | h
    · rw [hρ, h, sq_abs]; nlinarith [sq_nonneg q]
    · rw [hρ, h, sq_abs]; nlinarith [sq_nonneg p]
  have hsq : Real.sqrt s ≤ 1 + s := by nlinarith [Real.sq_sqrt hs0, Real.sqrt_nonneg s]
  have hρ1 : ρ ≤ 1 + s := by
    have h := Real.sqrt_le_sqrt hρs
    rw [Real.sqrt_sq hρ0] at h
    linarith
  have hρ2 : 1 + ρ ^ 2 ≤ 1 + s := by linarith
  have hexp : Real.exp (-Real.pi * s) ≤ Real.exp (-s) :=
    Real.exp_le_exp.2 (by nlinarith [Real.pi_gt_three])
  have hfact := Real.pow_div_factorial_le_exp (1 + s) (by linarith) (1 + k + m)
  have hN : (0 : ℝ) < Nat.factorial (1 + k + m) := by positivity
  rw [div_le_iff₀ hN] at hfact
  rw [hnorm]
  calc Real.sqrt s * Real.exp (-Real.pi * s) * ρ ^ k * (1 + ρ ^ 2) ^ m
      ≤ (1 + s) * Real.exp (-s) * (1 + s) ^ k * (1 + s) ^ m := by
        gcongr
    _ = (1 + s) ^ (1 + k + m) * Real.exp (-s) := by ring
    _ ≤ Real.exp (1 + s) * Nat.factorial (1 + k + m) * Real.exp (-s) := by gcongr
    _ = Real.exp 1 * Nat.factorial (1 + k + m) * (Real.exp s * Real.exp (-s)) := by
        rw [Real.exp_add]; ring
    _ = Real.exp 1 * Nat.factorial (1 + k + m) := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

omit [IsTotallyReal F] in
theorem arch_bound (k m : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ x y : UpperTheory.V.TR.Rinf F,
    ‖arch x y‖ * ∏ v, ((max |x v| |y v|) ^ k * (1 + (max |x v| |y v|) ^ 2) ^ m) ≤ C := by
  obtain ⟨C, hC0, hC⟩ := arch_factor_bound k m
  refine ⟨C ^ Fintype.card (InfinitePlace F), by positivity, fun x y => ?_⟩
  rw [arch, norm_prod, ← Finset.prod_mul_distrib, ← Finset.card_univ, ← Finset.prod_const]
  refine Finset.prod_le_prod₀ (fun v _ => by positivity) fun v _ => ?_
  rw [← mul_assoc]
  exact hC (x v) (y v)

open Classical in
theorem summable_beta (D : 𝓞 F) (hD : D ≠ 0) : ∃ m : ℕ, Summable (fun x : F =>
    if ∃ r : 𝓞 F, (D : F) * x = r then ((∏ v, (1 + sig v x ^ 2)) ^ m)⁻¹ else 0) := by
  have hDF : (D : F) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hD
  set J : (FractionalIdeal (𝓞 F)⁰ F)ˣ := Units.mk0 (FractionalIdeal.spanSingleton (𝓞 F)⁰ (D : F)⁻¹)
    ((FractionalIdeal.spanSingleton_ne_zero_iff).mpr (inv_ne_zero hDF)) with hJ
  have hmem : ∀ x : F, x ∈ (J : FractionalIdeal (𝓞 F)⁰ F) ↔ ∃ r : 𝓞 F, (D : F) * x = r := by
    intro x
    rw [hJ, Units.val_mk0, FractionalIdeal.mem_spanSingleton]
    constructor
    · rintro ⟨r, rfl⟩
      refine ⟨r, ?_⟩
      rw [Algebra.smul_def, mul_comm, mul_assoc, inv_mul_cancel₀ hDF, mul_one]
    · rintro ⟨r, hr⟩
      refine ⟨r, ?_⟩
      have hr' : algebraMap (𝓞 F) F r = (D : F) * x := hr.symm
      rw [Algebra.smul_def, hr', mul_comm, ← mul_assoc, inv_mul_cancel₀ hDF, one_mul]
  set n := Module.finrank ℤ (mixedEmbedding.idealLattice F J)
  refine ⟨n + 1, ?_⟩
  have hh := (GroundTheory.Global.summable_inv_one_add_norm_pow_idealLattice J).mul_left ((2 : ℝ) ^ (n + 1))
  have hs := GroundTheory.Global.summable_ite_mem_of_summable_idealLattice J
    (h := fun e => (2 : ℝ) ^ (n + 1) * ((1 + ‖e‖) ^ (n + 1))⁻¹) hh
  refine hs.of_nonneg_of_le (fun x => ?_) (fun x => ?_)
  · split_ifs
    · have : 0 ≤ ∏ v, (1 + sig v x ^ 2) := Finset.prod_nonneg fun v _ => by positivity
      positivity
    · exact le_rfl
  · by_cases hx : ∃ r : 𝓞 F, (D : F) * x = r
    · rw [if_pos hx, if_pos ((hmem x).2 hx)]
      set P := ∏ v, (1 + sig v x ^ 2) with hP
      have hP1 : ∀ v, 1 + sig v x ^ 2 ≤ P := by
        intro v
        rw [hP, ← Finset.mul_prod_erase Finset.univ (fun v => 1 + sig v x ^ 2) (Finset.mem_univ v)]
        have h1 : (1 : ℝ) ≤ ∏ w ∈ Finset.univ.erase v, (1 + sig w x ^ 2) := by
          have := Finset.prod_le_prod₀ (s := Finset.univ.erase v) (f := fun _ => (1 : ℝ))
            (g := fun w => 1 + sig w x ^ 2) (fun _ _ => zero_le_one) (fun w _ => by nlinarith [sq_nonneg (sig w x)])
          simpa using this
        nlinarith [sq_nonneg (sig v x)]
      have hPpos : 1 ≤ P := by
        obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace F))
        nlinarith [hP1 v, sq_nonneg (sig v x)]
      have he : ‖mixedEmbedding F x‖ ≤ P := by
        rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
        refine Finset.sup'_le _ _ fun v _ => ?_
        rw [mixedEmbedding.normAtPlace_apply, ← abs_sig]
        nlinarith [hP1 v, abs_nonneg (sig v x), sq_abs (sig v x)]
      have h1 : (1 + ‖mixedEmbedding F x‖) ^ (n + 1) ≤ 2 ^ (n + 1) * P ^ (n + 1) := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) (by linarith) _
      have hpos : 0 < (1 + ‖mixedEmbedding F x‖) ^ (n + 1) := by positivity
      have hPn : 0 < P ^ (n + 1) := by positivity
      show (P ^ (n + 1))⁻¹ ≤ 2 ^ (n + 1) * ((1 + ‖mixedEmbedding F x‖) ^ (n + 1))⁻¹
      rw [inv_le_iff_one_le_mul₀ hPn]
      rw [← div_eq_mul_inv, div_mul_eq_mul_div, le_div_iff₀ hpos, one_mul]
      linarith
    · rw [if_neg hx, if_neg (fun h => hx ((hmem x).1 h))]


omit [IsTotallyReal F] in
theorem exists_bound_inf {K : Set (Ideles F)} (hK : IsCompact K) : ∃ B : ℝ, 1 ≤ B ∧ ∀ a ∈ K, ∀ v,
    ‖((a : Ideles F) : Ad F).1 v‖ ≤ B ∧ ‖((a⁻¹ : Ideles F) : Ad F).1 v‖ ≤ B := by
  set f : Ideles F → ℝ := fun a => ∑ v, (‖((a : Ideles F) : Ad F).1 v‖ + ‖((a⁻¹ : Ideles F) : Ad F).1 v‖)
  have h1 : Continuous (fun a : Ideles F => ((a : Ideles F) : Ad F)) := Units.continuous_val
  have h2 : Continuous (fun a : Ideles F => ((a⁻¹ : Ideles F) : Ad F)) := Units.continuous_coe_inv
  have h3 : ∀ v : InfinitePlace F, Continuous (fun x : Ad F => x.1 v) := fun v =>
    (continuous_apply v).comp continuous_fst
  have hf : Continuous f := by
    refine continuous_finsetSum _ fun v _ => ?_
    exact (continuous_norm.comp ((h3 v).comp h1)).add (continuous_norm.comp ((h3 v).comp h2))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C 1, le_max_right _ _, fun a ha v => ?_⟩
  have h1 := hC a ha
  rw [Real.norm_eq_abs] at h1
  have hle : ‖((a : Ideles F) : Ad F).1 v‖ + ‖((a⁻¹ : Ideles F) : Ad F).1 v‖ ≤ f a :=
    Finset.single_le_sum (f := fun v => ‖((a : Ideles F) : Ad F).1 v‖ + ‖((a⁻¹ : Ideles F) : Ad F).1 v‖)
      (fun v _ => by positivity) (Finset.mem_univ v)
  have h2 := le_abs_self (f a)
  constructor <;> nlinarith [norm_nonneg (((a : Ideles F) : Ad F).1 v), norm_nonneg (((a⁻¹ : Ideles F) : Ad F).1 v),
    le_max_left C 1]

open Classical in
theorem abs_pInf_moduleSection (t : {r : ℝ // 0 < r}) (v : InfinitePlace F) :
    |UpperTheory.V.TR.pInf F ((moduleSection (w0 F) t : Ideles F) : Ad F) v| = if v = w0 F then (t : ℝ) else 1 := by
  rw [abs_pInf, norm_moduleSection_apply]
  split_ifs with h
  · have h1 := norm_posRealElem_pow (w0 F) t.2.le
    rwa [InfinitePlace.mult, if_pos (IsTotallyReal.isReal _), pow_one] at h1
  · rfl

end UpperTheory.HilbertEisensteinWeightOne.eisensteinGrowth
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.ArchInt
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published GroundTheory.LocalField

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L4

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def rc (a : (InfiniteAdeleRing F)ˣ) (v : InfinitePlace F) : ℝ :=
  (UpperTheory.V.TR.infEq F).symm (a : InfiniteAdeleRing F) v

def archK (y : (UpperTheory.V.TR.Rinf F)ˣ) (ξ : F) (a : (InfiniteAdeleRing F)ˣ) : ℂ :=
  ∏ v, ((((rc a v * y.val v + (rc a v)⁻¹ * reAt v ξ : ℝ)) : ℂ) *
    Complex.exp (-(Real.pi : ℂ) * (((rc a v * y.val v) ^ 2 + ((rc a v)⁻¹ * reAt v ξ) ^ 2 : ℝ) : ℂ)))

def ωI (ω : HChar F) (a : (InfiniteAdeleRing F)ˣ) : ℂ := ((ω.1 (ofInfinite a) : ℂˣ) : ℂ)

def chiW (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (w : HeightOneSpectrum (𝓞 F)) : ℂ :=
  if c w = 0 then ((ω.val w : ℂˣ) : ℂ) else 0

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L4

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open L4

def ArchInt : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F)
  (c : HeightOneSpectrum (𝓞 F) → ℕ), Hyp ω c → ∀ (y : (UpperTheory.V.TR.Rinf F)ˣ), (∀ v, 0 < y.val v) → ∀ ξ : Fˣ,
    Integrable (fun a => archK y (ξ : F) a * (ωI ω a)⁻¹) (infiniteIdeleMeasure F) ∧
      ∫ a, archK y (ξ : F) a * (ωI ω a)⁻¹ ∂infiniteIdeleMeasure F =
        if ∀ v, 0 < reAt v (ξ : F) then (2 : ℂ) ^ Fintype.card (InfinitePlace F) *
          Complex.exp (-(2 * Real.pi : ℂ) * ∑ v, (reAt v (ξ : F) : ℂ) * (y.val v : ℂ)) else 0

def CoefDiv : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F)
  (c : HeightOneSpectrum (𝓞 F) → ℕ) (z : Af F) (m : HeightOneSpectrum (𝓞 F) → ℤ) (S : Finset (HeightOneSpectrum (𝓞 F))),
    (∀ w, Valued.v (pLoc F w z) = WithZero.exp (dd w - m w)) → (∀ w ∉ S, m w = 0) →
    coefAt (divS ω c) z =
      if ∀ w ∈ S, 0 ≤ m w then ∏ w ∈ S, ∑ j ∈ Finset.range ((m w).toNat + 1), chiW ω c w ^ j else 0

def LocRam : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F)
  (c : HeightOneSpectrum (𝓞 F) → ℕ), Hyp ω c → ∀ w : HeightOneSpectrum (𝓞 F), c w ≠ 0 →
    (∀ k : ℤ, -((c w : ℤ) + dd w) < k →
      ∫ x in ordShell (w.adicCompletion F) k, ((ω.loc w x : ℂˣ) : ℂ) *
        (localAdelicChar F w (x : w.adicCompletion F) : ℂ) ∂multHaar (w.adicCompletion F) = 0) ∧
    ∫ x in ordShell (w.adicCompletion F) (-((c w : ℤ) + dd w)), ((ω.loc w x : ℂˣ) : ℂ) *
        (localAdelicChar F w (x : w.adicCompletion F) : ℂ) ∂multHaar (w.adicCompletion F) ≠ 0

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.HasTemperateGrowthArchPoly
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix nonZeroDivisors
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L1

open NumberField.mixedEmbedding NumberField.InfinitePlace Function
open scoped SchwartzMap FourierTransform Real Classical

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def levelIdeal (c : HeightOneSpectrum (𝓞 F) → ℕ) : (FractionalIdeal (𝓞 F)⁰ F)ˣ :=
  ∏ᶠ w, primeIdealUnit w ^ (c w : ℤ)

theorem count_levelIdeal {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite)
    (w : HeightOneSpectrum (𝓞 F)) :
    FractionalIdeal.count F w ((levelIdeal c : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) = c w := by
  unfold levelIdeal
  rw [count_finprod_primeIdealUnit_zpow]
  refine Filter.eventually_cofinite.2 (hc.subset fun v hv => ?_)
  simp only [Set.mem_setOf_eq, Nat.cast_eq_zero] at hv ⊢
  exact hv

theorem mem_level_iff {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite) (B : Af F) :
    B ∈ idealFiniteAdeles (levelIdeal c) ↔ ∀ w, Valued.v (pLoc F w B) ≤ WithZero.exp (-(c w : ℤ)) := by
  rw [mem_idealFiniteAdeles]
  refine forall_congr' fun w => ?_
  rw [count_levelIdeal hc]
  rfl

theorem count_different (w : HeightOneSpectrum (𝓞 F)) :
    FractionalIdeal.count F w ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = dd w := by
  rw [FractionalIdeal.count_coe F w (differentIdeal_ne_bot (A := ℤ))]
  rfl

theorem mem_dual_iff {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite) (Z : Af F) :
    Z ∈ idealFiniteAdeles (traceDualIdeal F (levelIdeal c)) ↔
      ∀ w, Valued.v (pLoc F w Z) ≤ WithZero.exp ((c w : ℤ) + dd w) := by
  rw [mem_idealFiniteAdeles]
  refine forall_congr' fun w => ?_
  rw [count_traceDualIdeal, count_levelIdeal hc, count_different, neg_neg]
  rfl

theorem isEmpty_complex : IsEmpty {w : InfinitePlace F // IsComplex w} :=
  ⟨fun w => (not_isComplex_iff_isReal.2 (IsTotallyReal.isReal w.1)) w.2⟩

theorem prod_real (f : InfinitePlace F → ℂ) : ∏ w : {w : InfinitePlace F // IsReal w}, f w.1 = ∏ v, f v :=
  (Equiv.subtypeUnivEquiv (fun w : InfinitePlace F => IsTotallyReal.isReal w)).prod_comp f

def archPoly (a : InfinitePlace F → ℝ) (x : mixedSpace F) : ℂ :=
  ∏ w : {w : InfinitePlace F // IsReal w},
    (((a w.1 : ℝ) : ℂ) + Complex.I * ((x.1 w : ℝ) : ℂ)) * Complex.exp (-(π : ℂ) * ((a w.1 : ℝ) : ℂ) ^ 2)

theorem hasTemperateGrowth_archPoly (a : InfinitePlace F → ℝ) : (archPoly (F := F) a).HasTemperateGrowth := by
  unfold archPoly
  refine hasTemperateGrowth_finsetProd _ fun w _ => ?_
  have hlin : (fun x : mixedSpace F => ((x.1 w : ℝ) : ℂ)).HasTemperateGrowth :=
    ((Complex.ofRealCLM.comp ((ContinuousLinearMap.proj w :
      ({w // IsReal w} → ℝ) →L[ℝ] ℝ).comp (ContinuousLinearMap.fst ℝ ({w // IsReal w} → ℝ)
        ({w // IsComplex w} → ℂ))) : mixedSpace F →L[ℝ] ℂ)).hasTemperateGrowth
  exact ((HasTemperateGrowth.const _).add ((HasTemperateGrowth.const Complex.I).mul hlin)).mul
    (HasTemperateGrowth.const _)

def archSchwartz (a : InfinitePlace F → ℝ) : 𝓢(mixedSpace F, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (archPoly a)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mixedToEuclidean F)
      (gaussianSchwartz (euclidean.mixedSpace F)))

theorem archSchwartz_apply (a : InfinitePlace F → ℝ) (x : mixedSpace F) :
    archSchwartz a x = archPoly a x * ((Real.exp (-π * (∑ w, x.1 w ^ 2 + 2 * ∑ w, ‖x.2 w‖ ^ 2)) : ℝ) : ℂ) := by
  rw [archSchwartz, SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_archPoly a),
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, gaussianSchwartz_apply,
    norm_mixedToEuclidean_sq, smul_eq_mul]

theorem archSchwartz_eq_prod (a : InfinitePlace F → ℝ) (x : mixedSpace F) :
    archSchwartz a x = ∏ w : {w : InfinitePlace F // IsReal w},
      (((a w.1 : ℝ) : ℂ) + Complex.I * ((x.1 w : ℝ) : ℂ)) *
        Complex.exp (-(π : ℂ) * (((a w.1 : ℝ) : ℂ) ^ 2 + ((x.1 w : ℝ) : ℂ) ^ 2)) := by
  haveI := isEmpty_complex (F := F)
  rw [archSchwartz_apply, archPoly, Finset.univ_eq_empty (α := {w : InfinitePlace F // IsComplex w}),
    Finset.sum_empty, mul_zero, add_zero, Finset.mul_sum, Real.exp_sum, Complex.ofReal_prod,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem archSchwartz_homeo (A B : Ad F) :
    archSchwartz (UpperTheory.V.TR.pInf F A) (homeomorphMixedSpace F B.1) =
      arch (UpperTheory.V.TR.pInf F A) (UpperTheory.V.TR.pInf F B) := by
  rw [archSchwartz_eq_prod, arch]
  exact prod_real (fun v => (((UpperTheory.V.TR.pInf F A v : ℝ) : ℂ) + Complex.I * ((UpperTheory.V.TR.pInf F B v : ℝ) : ℂ)) *
    Complex.exp (-(π : ℂ) * (((UpperTheory.V.TR.pInf F A v : ℝ) : ℂ) ^ 2 + ((UpperTheory.V.TR.pInf F B v : ℝ) : ℂ) ^ 2)))

open Classical in
theorem slice_eq {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite) (A : Ad F) :
    slice c A = (if ∀ w, Valued.v (pLoc F w (pFin F A)) ≤ WithZero.exp (-(c w : ℤ)) then (1 : ℂ) else 0) •
      schwartzBruhatTensor (archSchwartz (UpperTheory.V.TR.pInf F A)) (cosetIndicator (levelIdeal c) 1) := by
  funext B
  simp only [slice, Phi, Pi.smul_apply, smul_eq_mul, schwartzBruhatTensor, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  rw [archSchwartz_homeo, cosetIndicator_apply, mem_level_iff hc]
  have hB : ∀ w, pLoc F w (B.2 - 1) = pLoc F w (pFin F B) - 1 := fun w => by
    rw [map_sub, map_one]; rfl
  simp only [hB]
  by_cases h1 : ∀ w, Valued.v (pLoc F w (pFin F A)) ≤ WithZero.exp (-(c w : ℤ))
  · by_cases h2 : ∀ w, Valued.v (pLoc F w (pFin F B) - 1) ≤ WithZero.exp (-(c w : ℤ))
    · have h3 : ∀ w, Valued.v (pLoc F w (pFin F A)) ≤ WithZero.exp (-(c w : ℤ)) ∧
          Valued.v (pLoc F w (pFin F B) - 1) ≤ WithZero.exp (-(c w : ℤ)) := fun w => ⟨h1 w, h2 w⟩
      simp only [forall_and, h1, h2, and_self, implies_true, ↓reduceIte, mul_one, one_mul]
    · have h3 : ¬ ∀ w, Valued.v (pLoc F w (pFin F A)) ≤ WithZero.exp (-(c w : ℤ)) ∧
          Valued.v (pLoc F w (pFin F B) - 1) ≤ WithZero.exp (-(c w : ℤ)) := fun h => h2 fun w => (h w).2
      simp only [forall_and, h1, h2, true_and, and_false, ↓reduceIte, mul_zero, one_mul]
  · have h3 : ¬ ∀ w, Valued.v (pLoc F w (pFin F A)) ≤ WithZero.exp (-(c w : ℤ)) ∧
        Valued.v (pLoc F w (pFin F B) - 1) ≤ WithZero.exp (-(c w : ℤ)) := fun h => h1 fun w => (h w).1
    simp only [forall_and, h1, false_and, ↓reduceIte, mul_zero, zero_mul]

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L1

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

theorem slice_mem_sb {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite) (A : Ad F) :
    slice c A ∈ schwartzBruhat F := by
  rw [L1.slice_eq hc A]
  exact Submodule.smul_mem _ _ (schwartzBruhatTensor_mem _ (cosetIndicator_mem_finiteSchwartzBruhat _ _))

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.P5meas
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix SchwartzMap
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published
open NumberField.mixedEmbedding
open scoped Classical nonZeroDivisors

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L5

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]


variable (F) in
def wpoly (x : mixedSpace F) : ℂ :=
  ∏ v : InfinitePlace F, (1 + ((x.1 ⟨v, IsTotallyReal.isReal v⟩ : ℝ) : ℂ) ^ 2)


variable (F) in
def phi1 : 𝓢(mixedSpace F, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (wpoly F)
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mixedToEuclidean F)
      (gaussianSchwartz (euclidean.mixedSpace F)))


variable (F) in
def H1 : Ad F → ℂ := schwartzBruhatTensor (phi1 F) (cosetIndicator 1 0)

def condZ (c : HeightOneSpectrum (𝓞 F) → ℕ) (Z : Ad F) : Prop :=
  ∀ w, Valued.v (pLoc F w (pFin F Z)) ≤ WithZero.exp ((c w : ℤ) + dd w)

def theta (G : Ad F → ℂ) (b : IdeleGroup F) : ℝ := ∑' ξ : Fˣ, ‖G (b • algebraMap F (Ad F) (ξ : F))‖

def gB (t : {r : ℝ // 0 < r}) : ℝ := if 1 ≤ (t : ℝ) then (t : ℝ)⁻¹ else (t : ℝ)

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein.L5

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

open L5

def P5dom : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F],
  H1 F ∈ schwartzBruhat F ∧ (∀ x : Ad F, H1 F x = ((‖H1 F x‖ : ℝ) : ℂ)) ∧
    ∀ (c : HeightOneSpectrum (𝓞 F) → ℕ) (A Z Z' : Ad F), Z'.1 = Z.1 →
      (condZ c Z → Z'.2 ∈ idealFiniteAdeles (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)) →
      ‖kernF c A Z‖ ≤ ‖H1 F A‖ * ‖H1 F Z'‖

def P5mu : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (c : HeightOneSpectrum (𝓞 F) → ℕ),
  {w | c w ≠ 0}.Finite → ∃ μ : IdeleGroup F, (∀ Z : Ad F, (μ • Z).1 = Z.1) ∧
    ∀ Z : Ad F, condZ c Z → (μ • Z).2 ∈ idealFiniteAdeles (1 : (FractionalIdeal (𝓞 F)⁰ F)ˣ)

def P5meas : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (c : HeightOneSpectrum (𝓞 F) → ℕ) (κ : ℂ),
  (∀ A Z : Ad F, adelicFourier F (slice c A) Z = κ * kernF c A Z) → ∀ (Y : Ad F) (ξ : F),
    Measurable fun p : {r : ℝ // 0 < r} × normOneSubgroup F => coefK c Y (tau p.1 p.2) ξ

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
end
end

