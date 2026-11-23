module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.GeoAbs
section
open MeasureTheory PositivityTheory.Rg.Tf.Geo
open scoped ENNReal Pointwise
namespace UpperTheory.ConvolutionTheory.L1

section
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private lemma cont_prod (m : ℕ) : Continuous fun y : Fin m → G => (List.ofFn y).prod := by
  induction m with
  | zero => simpa using continuous_const
  | succ m ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    exact (continuous_apply 0).mul (ih.comp (continuous_pi fun i => continuous_apply i.succ))

private lemma cont_fib (m : ℕ) : Continuous fun p : (Fin m → G) × G => fib p.1 p.2 := by
  unfold fib
  refine continuous_pi fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Fin.snoc_last]
    exact ((cont_prod m).comp continuous_fst).inv.mul continuous_snd
  · simp only [Fin.snoc_castSucc]
    exact (continuous_apply j).comp continuous_fst

private lemma prod_fib {m : ℕ} (y : Fin m → G) (x : G) : (List.ofFn (fib y x)).prod = x := by
  unfold fib
  rw [List.ofFn_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append, List.prod_append, List.prod_cons, List.prod_nil,
    mul_one, mul_inv_cancel_left]

private lemma closed_centr [T2Space G] (γ : G) : IsClosed ((Subgroup.centralizer {γ} : Subgroup G) : Set G) := by
  have : ((Subgroup.centralizer {γ} : Subgroup G) : Set G) = {g | g * γ = γ * g} := by
    ext g; simp [Subgroup.mem_centralizer_singleton_iff, commute_iff_eq]
  rw [this]
  exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)

private lemma inv_inv_meas [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Z : Subgroup G) (hc : IsClosed (Z : Set G)) (hcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    (ν : Measure Z) [ν.IsHaarMeasure] : ν.IsInvInvariant := by
  haveI : LocallyCompactSpace Z := hc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology Z := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI : TopologicalSpace.MetrizableSpace Z := TopologicalSpace.metrizableSpace_of_t3_secondCountable Z
  haveI : ν.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure ν
  letI : CommGroup Z := { (inferInstance : Group Z) with
    mul_comm := fun a b => Subtype.ext (hcomm a a.2 b b.2) }
  exact Measure.IsHaarMeasure.isInvInvariant_of_regular ν

private lemma supp_bound {m : ℕ} (γ : G) (Z : Subgroup G) (hcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a)
    (δ : Fin (m + 1) → G) (hδ : ∀ i, δ i ∈ Z) (K : Set (Fin (m + 1) → G)) (hK : IsCompact K)
    (hprod : ∀ x : Fin (m + 1) → G, (fun i => (x i)⁻¹ * δ i * x (i + 1)) ∈ K →
      (x 0)⁻¹ * γ * x 0 ∈ (fun g : Fin (m + 1) → G => (List.ofFn g).prod) '' K)
    (hprop : ∀ D : Set G, IsCompact D → ∃ C : Set G, IsCompact C ∧ ∀ x, x⁻¹ * γ * x ∈ D → ∃ t ∈ Z, ∃ y ∈ C, x = t * y) :
    ∃ C : Set (Fin (m + 1) → G), IsCompact C ∧ ∀ x : Fin (m + 1) → G, (fun i => (x i)⁻¹ * δ i * x (i + 1)) ∈ K →
      ∃ t : Z, ∃ y ∈ C, x = (fun _ => (t : G)) * y := by
  obtain ⟨C₀, hC₀, hC⟩ := hprop _ (hK.image (cont_prod (m + 1)))
  let K' : Set G := ⋃ i, (fun g : Fin (m + 1) → G => g i) '' K
  have hK' : IsCompact K' := isCompact_iUnion fun i => hK.image (continuous_apply i)
  let Dl : Set G := Set.range fun i => (δ i)⁻¹
  have hDl : IsCompact Dl := (Set.finite_range _).isCompact
  let A : ℕ → Set G := fun k => Nat.rec C₀ (fun _ S => Dl * S * K') k
  have hA : ∀ k, IsCompact (A k) := by
    intro k
    induction k with
    | zero => exact hC₀
    | succ k ih => exact (hDl.mul ih).mul hK'
  refine ⟨Set.pi Set.univ fun i : Fin (m + 1) => A i, isCompact_univ_pi fun i => hA i, ?_⟩
  intro x hx
  obtain ⟨t, ht, y₀, hy₀, hx₀⟩ := hC (x 0) (hprod x hx)
  refine ⟨⟨t, ht⟩, fun i => t⁻¹ * x i, ?_, ?_⟩
  · have key : ∀ k (hk : k < m + 1), t⁻¹ * x ⟨k, hk⟩ ∈ A k := by
      intro k
      induction k with
      | zero =>
        intro hk
        have : (⟨0, hk⟩ : Fin (m + 1)) = 0 := rfl
        rw [this, hx₀, inv_mul_cancel_left]
        exact hy₀
      | succ k ih =>
        intro hk
        have hk' : k < m + 1 := by omega
        have hs : (⟨k, hk'⟩ : Fin (m + 1)) + 1 = ⟨k + 1, hk⟩ := by
          ext
          simp [Fin.val_add, Nat.mod_eq_of_lt hk]
        have hc := hcomm t ht (δ ⟨k, hk'⟩) (hδ _)
        have e : t⁻¹ * x ⟨k + 1, hk⟩ = (δ ⟨k, hk'⟩)⁻¹ * (t⁻¹ * x ⟨k, hk'⟩) *
            ((x ⟨k, hk'⟩)⁻¹ * δ ⟨k, hk'⟩ * x (⟨k, hk'⟩ + 1)) := by
          rw [hs]
          have h2 : (δ ⟨k, hk'⟩)⁻¹ * t⁻¹ * δ ⟨k, hk'⟩ = t⁻¹ := by
            have h3 : t⁻¹ * δ ⟨k, hk'⟩ = δ ⟨k, hk'⟩ * t⁻¹ := by
              rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hc, mul_inv_cancel_right]
            rw [mul_assoc, h3, inv_mul_cancel_left]
          calc _ = ((δ ⟨k, hk'⟩)⁻¹ * t⁻¹ * δ ⟨k, hk'⟩) * x ⟨k + 1, hk⟩ := by rw [h2]
            _ = _ := by group
        rw [e]
        exact Set.mul_mem_mul (Set.mul_mem_mul ⟨⟨k, hk'⟩, rfl⟩ (ih hk'))
          (Set.mem_iUnion.2 ⟨⟨k, hk'⟩, _, hx, rfl⟩)
    intro i _
    exact key i i.2
  · funext i
    simp
end

theorem geoAbs : GeoAbs := by
  intro G _ _ _ _ _ _ _ _ μ _ m γ hcl hcomm ν _ δ hδ hprod Φ hΦ hΦc
  have hZc := closed_centr γ
  haveI : LocallyCompactSpace (Subgroup.centralizer {γ} : Subgroup G) :=
    hZc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (Subgroup.centralizer {γ} : Subgroup G) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  haveI := inv_inv_meas _ hZc hcomm ν
  have CV := changeVar G μ m δ
  obtain ⟨pc, -, pne, -, -, -⟩ := pushTest G μ m Φ hΦ hΦc
  have CP := closedProper G γ hcl
  let dg : (Subgroup.centralizer {γ} : Subgroup G) →* (Fin (m + 1) → G) :=
    { toFun := fun t _ => (t : G), map_one' := rfl, map_mul' := fun _ _ => rfl }
  have hdg : Continuous dg := continuous_pi fun _ => continuous_subtype_val
  let F : (Fin (m + 1) → G) → ℂ := fun x => Φ fun i => (x i)⁻¹ * δ i * x (i + 1)
  have hFc : Continuous F := hΦ.comp (continuous_pi fun i =>
    ((continuous_apply i).inv.mul continuous_const).mul (continuous_apply (i + 1)))
  have hFinv : ∀ t x, F (dg t * x) = F x := by
    intro t x
    show (Φ fun i => ((t : G) * x i)⁻¹ * δ i * ((t : G) * x (i + 1))) = Φ fun i => (x i)⁻¹ * δ i * x (i + 1)
    congr 1
    funext i
    have hc := hcomm t t.2 (δ i) (hδ i)
    have h2 : (t : G)⁻¹ * δ i * t = δ i := by rw [mul_assoc, ← hc, inv_mul_cancel_left]
    calc ((t : G) * x i)⁻¹ * δ i * ((t : G) * x (i + 1)) = (x i)⁻¹ * ((t : G)⁻¹ * δ i * t) * x (i + 1) := by group
      _ = _ := by rw [h2]
  let f : G → ℂ := fun x => push μ m Φ (x⁻¹ * γ * x)
  have hfc : Continuous f := pc.comp ((continuous_inv.mul continuous_const).mul continuous_id)
  have hfinv : ∀ (t : (Subgroup.centralizer {γ} : Subgroup G)) x, f ((Subgroup.centralizer {γ} : Subgroup G).subtype t * x) = f x := by
    intro t x
    show push μ m Φ (((t : G) * x)⁻¹ * γ * ((t : G) * x)) = push μ m Φ (x⁻¹ * γ * x)
    have hc : (t : G) * γ = γ * t := Subgroup.mem_centralizer_singleton_iff.1 t.2
    have h2 : (t : G)⁻¹ * γ * t = γ := by rw [mul_assoc, ← hc, inv_mul_cancel_left]
    congr 1
    calc ((t : G) * x)⁻¹ * γ * ((t : G) * x) = x⁻¹ * ((t : G)⁻¹ * γ * t) * x := by group
      _ = _ := by rw [h2]
  have hw : ∀ x : Fin (m + 1) → G, (List.ofFn fun i => (x i)⁻¹ * δ i * x (i + 1)).prod = (x 0)⁻¹ * γ * x 0 := by
    intro x
    rw [CV.2 x, prod_fib, hprod]
  obtain ⟨C, hC, hCx⟩ := supp_bound γ _ hcomm δ hδ (tsupport Φ) hΦc
    (fun x hx => ⟨_, hx, hw x⟩) CP
  obtain ⟨C', hC', hCx'⟩ := CP _ (hΦc.image (cont_prod (m + 1)))
  have fin1 : ∀ ρ, IsNormAlong id dg ν ρ → ∫⁻ x, ‖F x‖ₑ * ρ x ∂(Measure.pi fun _ => μ) < ⊤ := fun ρ hρ =>
    quotFin (Fin (m + 1) → G) _ (Measure.pi fun _ => μ) ν dg hdg F ρ hFc hFinv
      ⟨C, hC, fun x hx => by
        obtain ⟨t, y, hy, e⟩ := hCx x (subset_tsupport _ (Function.mem_support.2 hx))
        exact ⟨t, y, hy, e⟩⟩ hρ
  have fin2 : ∀ ρ, IsNormAlong id (Subgroup.centralizer {γ} : Subgroup G).subtype ν ρ → ∫⁻ x, ‖f x‖ₑ * ρ x ∂μ < ⊤ := fun ρ hρ =>
    quotFin G _ μ ν (Subgroup.centralizer {γ} : Subgroup G).subtype continuous_subtype_val f ρ hfc hfinv
      ⟨C', hC', fun x hx => by
        obtain ⟨g, hg, e⟩ := pne _ hx
        obtain ⟨t, ht, y, hy, e'⟩ := hCx' x ⟨g, subset_tsupport _ (Function.mem_support.2 hg), e⟩
        exact ⟨⟨t, ht⟩, y, hy, e'⟩⟩ hρ
  refine ⟨fin1, ?_⟩
  by_cases hex : ∃ ρ', IsNormAlong id (fun t : (Subgroup.centralizer {γ} : Subgroup G) => (t : G)) ν ρ'
  · obtain ⟨ρ', hρ'⟩ := hex
    have hρ : IsNormAlong id dg ν (fun x => ρ' (x 0)) :=
      ⟨hρ'.1.comp (measurable_pi_apply 0), fun x => hρ'.2 (x 0)⟩
    have L : quotInt (Measure.pi fun _ => μ) id (fun t : (Subgroup.centralizer {γ} : Subgroup G) => fun _ : Fin (m + 1) => (t : G)) ν F =
        ∫ x, F x * ((ρ' (x 0)).toReal : ℂ) ∂(Measure.pi fun _ => μ) :=
      quotAny (Fin (m + 1) → G) _ (Measure.pi fun _ => μ) ν dg hdg.measurable F _ hFc.measurable hFinv hρ (fin1 _ hρ)
    have R : quotInt μ id (fun t : (Subgroup.centralizer {γ} : Subgroup G) => (t : G)) ν f =
        ∫ x, f x * ((ρ' x).toReal : ℂ) ∂μ :=
      quotAny G _ μ ν (Subgroup.centralizer {γ} : Subgroup G).subtype continuous_subtype_val.measurable f _ hfc.measurable hfinv hρ' (fin2 _ hρ')
    refine L.trans (Eq.trans ?_ R.symm)
    let H : G × (Fin m → G) → ℂ := fun p => Φ (fib p.2 (p.1⁻¹ * γ * p.1)) * ((ρ' p.1).toReal : ℂ)
    have hHm : Measurable H := by
      have h1 : Continuous fun p : G × (Fin m → G) => Φ (fib p.2 (p.1⁻¹ * γ * p.1)) :=
        hΦ.comp ((cont_fib m).comp (continuous_snd.prodMk
          ((continuous_fst.inv.mul continuous_const).mul continuous_fst)))
      exact h1.measurable.mul (Complex.measurable_ofReal.comp (hρ'.1.comp measurable_fst).ennreal_toReal)
    let φ : (Fin (m + 1) → G) → G × (Fin m → G) :=
      fun x => (x 0, fun i : Fin m => (x i.castSucc)⁻¹ * δ i.castSucc * x i.succ)
    have hcomp : ∀ x, H (φ x) = F x * ((ρ' (x 0)).toReal : ℂ) := by
      intro x
      show Φ _ * _ = Φ _ * _
      rw [CV.2 x, hprod]
    have hint : Integrable (fun x => F x * ((ρ' (x 0)).toReal : ℂ)) (Measure.pi fun _ => μ) := by
      refine ⟨(hFc.measurable.mul (Complex.measurable_ofReal.comp hρ.1.ennreal_toReal)).aestronglyMeasurable, ?_⟩
      refine lt_of_le_of_lt (lintegral_mono fun x => ?_) (fin1 _ hρ)
      rw [enorm_mul]
      gcongr
      rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
      exact ENNReal.ofReal_toReal_le
    have hHint : Integrable H (μ.prod (Measure.pi fun _ => μ)) := by
      refine (CV.1.integrable_comp hHm.aestronglyMeasurable).1 ?_
      exact hint.congr (Filter.Eventually.of_forall fun x => (hcomp x).symm)
    calc ∫ x, F x * ((ρ' (x 0)).toReal : ℂ) ∂(Measure.pi fun _ => μ)
        = ∫ x, H (φ x) ∂(Measure.pi fun _ => μ) := by simp only [hcomp]
      _ = ∫ p, H p ∂(μ.prod (Measure.pi fun _ => μ)) := by
        rw [← CV.1.map_eq]
        exact (integral_map CV.1.aemeasurable hHm.aestronglyMeasurable).symm
      _ = ∫ a, ∫ v, H (a, v) ∂(Measure.pi fun _ => μ) ∂μ := integral_prod H hHint
      _ = ∫ a, f a * ((ρ' a).toReal : ℂ) ∂μ := by
        congr 1
        funext a
        show ∫ v, Φ (fib v (a⁻¹ * γ * a)) * ((ρ' a).toReal : ℂ) ∂(Measure.pi fun _ => μ) =
          (∫ v, Φ (fib v (a⁻¹ * γ * a)) ∂(Measure.pi fun _ => μ)) * ((ρ' a).toReal : ℂ)
        rw [integral_mul_const]
  · have no : ¬∃ ρ, IsNormAlong id (fun t : (Subgroup.centralizer {γ} : Subgroup G) => fun _ : Fin (m + 1) => (t : G)) ν ρ := by
      rintro ⟨ρ, hρ⟩
      refine hex ⟨fun g => ρ fun _ => g, hρ.1.comp (Measurable.of_eval fun _ => measurable_id), fun x => ?_⟩
      exact hρ.2 fun _ => x
    unfold quotInt
    rw [dite_eq_right no, dite_eq_right hex]

end UpperTheory.ConvolutionTheory.L1
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.IntPow
section
open MeasureTheory NumberField
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.L1

section

variable {K : Type} [Field K] [NumberField K] {n : ℕ} (ν : Measure (archGroup K n)) [ν.IsHaarMeasure]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : UnitaryRep (archGroup K n) H)

private theorem int_cv (f e g : TI K n) (hg : ∀ x, g x = cv ν f e x) :
    π.integrated ν (UnitaryRep.ccToL1 ν g) =
      π.integrated ν (UnitaryRep.ccToL1 ν f) * π.integrated ν (UnitaryRep.ccToL1 ν e) := by
  obtain ⟨g', h1, -, h2⟩ := UpperTheory.ConvolutionTheory.Tf.homConv (archGroup K n) (archGroup K n) (MonoidHom.id _)
    continuous_id ν ν f e
  have hgg : g = g' := by
    ext x
    rw [hg, h1]
    rfl
  subst hgg
  rw [h2 H π]
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply,
    UnitaryRep.integrated_ccToL1_apply, UnitaryRep.compHom_apply]
  rfl

private theorem int_pow (a : TI K n) (k : ℕ) :
    ∃ c : TI K n, (∀ g, c g = cvPow ν a k g) ∧
      π.integrated ν (UnitaryRep.ccToL1 ν c) = π.integrated ν (UnitaryRep.ccToL1 ν a) ^ (k + 1) := by
  induction k with
  | zero => exact ⟨a, fun _ => rfl, by simp⟩
  | succ k ih =>
    obtain ⟨c, hc, hT⟩ := ih
    obtain ⟨h1, h2, -⟩ := UpperTheory.ConvolutionTheory.L1.cvBasic (archGroup K n) ν a c a a.continuous a.hasCompactSupport
      c.continuous c.hasCompactSupport a.continuous a.hasCompactSupport
    have hfun : (c : archGroup K n → ℂ) = cvPow ν a k := funext hc
    refine ⟨⟨⟨cv ν a c, h1⟩, h2⟩, fun g => ?_, ?_⟩
    · change cv ν a c g = cv ν a (cvPow ν a k) g
      rw [hfun]
    · rw [int_cv ν π a c _ (fun _ => rfl), hT, pow_succ' _ (k + 1)]

end

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.sqOp :
    UpperTheory.ConvolutionTheory.L1.SqOp := by
  intro K _ _ n ν _ b a aF m ha haF hb H _ _ _ π
  obtain ⟨-, hinv⟩ := (UpperTheory.ConvolutionTheory.Tf.unimod K n).1 ν
  let bs : TI K n := ⟨⟨fun x => conj (b x⁻¹),
      Complex.continuous_conj.comp (b.continuous.comp continuous_inv)⟩,
    (b.hasCompactSupport.comp_homeomorph (Homeomorph.inv _)).comp_left (g := fun z => conj z) (map_zero _)⟩
  obtain ⟨hadj, hnorm, -⟩ := UpperTheory.ConvolutionTheory.Tf.adjInt (archGroup K n) H π ν b bs (fun _ => rfl)
  have hT : π.integrated ν (UnitaryRep.ccToL1 ν a) =
      π.integrated ν (UnitaryRep.ccToL1 ν b) * star (π.integrated ν (UnitaryRep.ccToL1 ν b)) := by
    rw [ContinuousLinearMap.star_eq_adjoint, hadj]
    exact int_cv ν π b bs a ha
  have hb1 : ‖π.integrated ν (UnitaryRep.ccToL1 ν b)‖ ≤ 1 := hnorm.trans hb
  obtain ⟨c, hc, hcT⟩ := int_pow ν π a m
  have hcF : c = aF := by
    ext g
    rw [hc, haF]
  refine ⟨hT, ?_, ?_, hcF ▸ hcT⟩
  · rw [hT]
    exact mul_star_self_nonneg _
  · rw [hT]
    calc _ ≤ ‖π.integrated ν (UnitaryRep.ccToL1 ν b)‖ * ‖star (π.integrated ν (UnitaryRep.ccToL1 ν b))‖ := norm_mul_le _ _
      _ = ‖π.integrated ν (UnitaryRep.ccToL1 ν b)‖ * ‖π.integrated ν (UnitaryRep.ccToL1 ν b)‖ := by rw [norm_star]
      _ ≤ 1 := mul_le_one₀ hb1 (norm_nonneg _) hb1
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.JointNe
section
open GroundTheory.Automorphic UpperTheory.ConvolutionTheory.C
open scoped InnerProductSpace

namespace UpperTheory.ConvolutionTheory.L1

private lemma proj_comm {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Z : Submodule ℂ H) [Z.HasOrthogonalProjection] (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (hZ : ∀ z ∈ Z, T z ∈ Z) (x : H) : Z.starProjection (T x) = T (Z.starProjection x) := by
  have hp : Z.starProjection x ∈ Z := Submodule.starProjection_apply_mem Z x
  apply Submodule.eq_starProjection_of_mem_orthogonal (hZ _ hp)
  rw [Submodule.mem_orthogonal]
  intro z hz
  have hxo : x - Z.starProjection x ∈ Zᗮ := Submodule.sub_starProjection_mem_orthogonal x
  have hsym : ⟪z, T (x - Z.starProjection x)⟫_ℂ = ⟪T z, x - Z.starProjection x⟫_ℂ := by
    have := ContinuousLinearMap.adjoint_inner_left T (x - Z.starProjection x) z
    rw [← this, ← ContinuousLinearMap.star_eq_adjoint, hT.star_eq]
  rw [← map_sub, hsym]
  exact (Submodule.mem_orthogonal _ _).1 hxo _ (hZ z hz)

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.jointNe :
    UpperTheory.ConvolutionTheory.L1.JointNe := by
  intro Γ G H _ _ _ _ _ _ π V m ι E A U h i y hy
  obtain ⟨hcl, hinv, hirr⟩ := UpperTheory.ConvolutionTheory.L1.cutIrr Γ G H π V m ι E A U h
  have hmemVE : ∀ w, w ∈ eigIn V E 1 ↔ w ∈ V ∧ E w = w := by
    intro w
    simp [eigIn, Module.End.mem_eigenspace_iff, Submodule.mem_inf]
  have hmemZ : ∀ (k : Fin (m + 1)) w, w ∈ eigIn (eigIn V E 1) (A k) y ↔
      w ∈ eigIn V E 1 ∧ A k w = (y : ℂ) • w := by
    intro k w
    simp only [eigIn, Submodule.mem_inf, Module.End.mem_eigenspace_iff]
    rfl
  have hsa : ∀ k, IsSelfAdjoint (A k) := fun k =>
    (ContinuousLinearMap.nonneg_iff_isPositive.1 (h.A_pos k)).isSelfAdjoint
  have hAVE : ∀ j, ∀ w ∈ eigIn V E 1, A j w ∈ eigIn V E 1 := by
    intro j w hw
    obtain ⟨hwV, hwE⟩ := (hmemVE w).1 hw
    refine (hmemVE _).2 ⟨h.A_mem j w hwV, ?_⟩
    rw [← h.A_E, hwE]

  have hstep : ∀ j, eigIn (eigIn V E 1) (A j) y ≠ ⊥ → eigIn (eigIn V E 1) (A (j + 1)) y ≠ ⊥ := by
    intro j hj
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hj
    obtain ⟨hvE, hvA⟩ := (hmemZ j v).1 hv
    obtain ⟨hvV, hvE'⟩ := (hmemVE v).1 hvE
    have hvm : v ∈ V.map (U : H →ₗ[ℂ] H) := by rw [h.U_mem]; exact hvV
    obtain ⟨u, hu, rfl⟩ := hvm
    have hU : ∀ a b : H, U a = U b → a = b := fun a b hab => U.injective hab
    refine (Submodule.ne_bot_iff _).2 ⟨u, (hmemZ _ u).2 ⟨(hmemVE u).2 ⟨hu, ?_⟩, ?_⟩, ?_⟩
    · apply hU
      rw [h.U_E]
      exact hvE'
    · apply hU
      rw [h.U_A, map_smul]
      exact hvA
    · rintro rfl
      exact hv0 (by simp)
  have hall : ∀ j, eigIn (eigIn V E 1) (A j) y ≠ ⊥ := by
    have ht : ∀ t : Fin (m + 1), eigIn (eigIn V E 1) (A (i + t)) y ≠ ⊥ := by
      intro t
      induction t using Fin.induction with
      | zero => simpa using hy
      | succ t ih =>
        rw [← Fin.coeSucc_eq_succ, ← add_assoc]
        exact hstep _ ih
    intro j
    have := ht (j - i)
    rwa [add_sub_cancel] at this

  have hS : ∀ S : Finset (Fin (m + 1)), ∃ w ∈ eigIn V E 1, w ≠ 0 ∧ ∀ j ∈ S, A j w = (y : ℂ) • w := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have hne : eigIn V E 1 ≠ ⊥ := by
        intro hb
        obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 (hall i)
        have := ((hmemZ i v).1 hv).1
        rw [hb] at this
        exact hv0 (by simpa using this)
      obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hne
      exact ⟨v, hv, hv0, by simp⟩
    | insert k S hk ih =>
      obtain ⟨w₀, hw₀, hw₀0, hw₀A⟩ := ih
      by_contra hno
      have hno' : ∀ w ∈ eigIn V E 1, (∀ j ∈ S, A j w = (y : ℂ) • w) → A k w = (y : ℂ) • w → w = 0 := by
        intro w hw hwS hwk
        by_contra hw0
        exact hno ⟨w, hw, hw0, fun j hj => by
          rcases Finset.mem_insert.1 hj with rfl | hj
          · exact hwk
          · exact hwS j hj⟩
      set Z := eigIn (eigIn V E 1) (A k) y with hZdef
      have hZcl : IsClosed (Z : Set H) := by
        have h2 : IsClosed {w : H | A k w = (y : ℂ) • w} :=
          isClosed_eq (A k).continuous (continuous_const_smul _)
        have : (Z : Set H) = (eigIn V E 1 : Set H) ∩ {w : H | A k w = (y : ℂ) • w} := by
          ext w
          exact hmemZ k w
        rw [this]
        exact hcl.inter h2
      haveI : CompleteSpace Z := hZcl.completeSpace_coe
      have hZA : ∀ j, ∀ z ∈ Z, A j z ∈ Z := by
        intro j z hz
        obtain ⟨hzVE, hzA⟩ := (hmemZ k z).1 hz
        refine (hmemZ k _).2 ⟨hAVE j z hzVE, ?_⟩
        rw [h.A_A, hzA, map_smul]
      have hZπ : ∀ j, j ≠ k → ∀ g, ∀ z ∈ Z, π (ι j g) z ∈ Z := by
        intro j hj g z hz
        obtain ⟨hzVE, hzA⟩ := (hmemZ k z).1 hz
        refine (hmemZ k _).2 ⟨hinv j g z hzVE, ?_⟩
        rw [h.A_ι k j (Ne.symm hj), hzA, map_smul]

      have hNo : ∀ w ∈ eigIn V E 1, (∀ j ∈ S, A j w = (y : ℂ) • w) → w ∈ Zᗮ := by
        intro w hw hwS
        rw [← Submodule.starProjection_apply_eq_zero_iff]
        have hp : Z.starProjection w ∈ Z := Submodule.starProjection_apply_mem Z w
        obtain ⟨hpVE, hpA⟩ := (hmemZ k _).1 hp
        refine hno' _ hpVE (fun j hj => ?_) hpA
        rw [← proj_comm Z (A j) (hsa j) (hZA j), hwS j hj, map_smul]
      let M : Submodule ℂ H :=
        { carrier := {w | w ∈ eigIn V E 1 ∧ ∀ g, π (ι k g) w ∈ Zᗮ}
          add_mem' := fun {a b} ha hb => ⟨Submodule.add_mem _ ha.1 hb.1, fun g => by
            rw [map_add (f := _)]; exact Submodule.add_mem _ (ha.2 g) (hb.2 g)⟩
          zero_mem' := ⟨Submodule.zero_mem _, fun g => by
            rw [map_zero]; exact Submodule.zero_mem _⟩
          smul_mem' := fun c a ha => ⟨Submodule.smul_mem _ c ha.1, fun g => by
            rw [map_smul]; exact Submodule.smul_mem _ c (ha.2 g)⟩ }
      have hMmem : ∀ w, w ∈ M ↔ w ∈ eigIn V E 1 ∧ ∀ g, π (ι k g) w ∈ Zᗮ := fun w => Iff.rfl
      have hMle : M ≤ eigIn V E 1 := fun w hw => hw.1
      have hMcl : IsClosed (M : Set H) := by
        have : (M : Set H) = (eigIn V E 1 : Set H) ∩ ⋂ g, (π (ι k g)) ⁻¹' (Zᗮ : Set H) := by
          ext w
          simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
          exact hMmem w
        rw [this]
        exact hcl.inter (isClosed_iInter fun g =>
          (Submodule.isClosed_orthogonal Z).preimage (π (ι k g)).continuous)
      have hMinv : ∀ j g, ∀ v ∈ M, π (ι j g) v ∈ M := by
        intro j g v hv
        refine (hMmem _).2 ⟨hinv j g v hv.1, fun g' => ?_⟩
        by_cases hjk : j = k
        · subst hjk
          rw [← π.map_mul_apply, ← map_mul]
          exact hv.2 _
        · rw [← π.map_mul_apply, ((h.ι_comm k j (Ne.symm hjk)) g' g).eq, π.map_mul_apply]
          rw [Submodule.mem_orthogonal]
          intro z hz
          rw [π.inner_map_right, ← map_inv]
          exact (Submodule.mem_orthogonal _ _).1 (hv.2 g') _ (hZπ j hjk _ z hz)
      have hw₀M : w₀ ∈ M := by
        refine (hMmem _).2 ⟨hw₀, fun g => hNo _ (hinv k g w₀ hw₀) fun j hj => ?_⟩
        have hjk : j ≠ k := fun e => hk (e ▸ hj)
        rw [h.A_ι j k hjk, hw₀A j hj, map_smul]
      have hMtop : M = eigIn V E 1 := by
        rcases hirr M hMle hMcl hMinv with hb | he
        · exfalso
          rw [hb] at hw₀M
          exact hw₀0 (by simpa using hw₀M)
        · exact he
      obtain ⟨z, hz, hz0⟩ := (Submodule.ne_bot_iff _).1 (hall k)
      have hzM : z ∈ M := by
        rw [hMtop]
        exact ((hmemZ k z).1 hz).1
      have hzo := hzM.2 1
      rw [map_one, π.map_one_apply] at hzo
      have := (Submodule.mem_orthogonal _ _).1 hzo z hz
      exact hz0 (inner_self_eq_zero.1 this)
  obtain ⟨w, hw, hw0, hwA⟩ := hS Finset.univ
  refine (Submodule.ne_bot_iff _).2 ⟨w, ?_, hw0⟩
  simp only [jointEig, Submodule.mem_iInf]
  exact fun j => (hmemZ j w).2 ⟨hw, hwA j (Finset.mem_univ j)⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.LactLaws
section
theorem UpperTheory.ConvolutionTheory.L1.lactLaws :
    UpperTheory.ConvolutionTheory.L1.LactLaws := by
  intro K _ _ n β hβ
  obtain ⟨_, _, hs, h1, hm, hc, _, _⟩ := UpperTheory.ConvolutionTheory.Tf.lactSpec K n β hβ
  exact ⟨fun u => (hs u).1, h1, fun u v => (hm u v).1, fun u v => (hm u v).2, fun c u => (hc c u).1⟩
end

