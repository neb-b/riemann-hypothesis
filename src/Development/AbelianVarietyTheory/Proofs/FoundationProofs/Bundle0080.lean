module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTowerPlaceAtUpperHalfPlanePoint
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

noncomputable section

namespace GlobalTheory.KZ.H3

open Filter Topology

theorem isOpen_Hs_place : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

theorem isConnected_Hs_place : IsConnected Hs :=
  ⟨⟨Complex.I, by simp [Hs]⟩, (convex_halfSpace_im_gt (0 : ℝ)).isPreconnected⟩

theorem exists_analyticAt_of_order_nonneg {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    {τ : ℂ} (hτ : τ ∈ Hs) (f : X.K) (a b : ℂ → ℂ) (ha : DifferentiableOn ℂ a Hs) (hb : DifferentiableOn ℂ b Hs)
    (hb0 : (b : Mero) ≠ 0) (hab : X.an f * (b : Mero) = (a : Mero))
    (hord : 0 ≤ meromorphicOrderAt (a / b) τ) :
    ∃ φ : ℂ → ℂ, X.an f = (φ : Mero) ∧ AnalyticAt ℂ φ τ := by
  have hA : AnalyticOnNhd ℂ a Hs := ha.analyticOnNhd isOpen_Hs_place
  have hB : AnalyticOnNhd ℂ b Hs := hb.analyticOnNhd isOpen_Hs_place
  have hx : ∃ x ∈ Hs, b x ≠ 0 := by
    by_contra h
    push_neg at h
    apply hb0
    rw [← Filter.Germ.coe_zero]
    refine Filter.Germ.coe_eq.2 ?_
    filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz using h z hz
  obtain ⟨x, hxH, hx0⟩ := hx
  have hne : b ⁻¹' {0}ᶜ ∈ codiscreteWithin Hs :=
    hB.preimage_zero_mem_codiscreteWithin hx0 hxH isConnected_Hs_place
  have hM : MeromorphicAt (a / b) τ := (hA τ hτ).meromorphicAt.div (hB τ hτ).meromorphicAt
  refine ⟨toMeromorphicNFAt (a / b) τ, ?_, hM.meromorphicOrderAt_nonneg_iff_analyticAt_toMeromorphicNFAt.1 hord⟩
  have h1 : ((b * b⁻¹ : ℂ → ℂ) : Mero) = 1 := by
    rw [← Filter.Germ.coe_one]
    refine Filter.Germ.coe_eq.2 ?_
    filter_upwards [hne] with z hz
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.one_apply]
    exact mul_inv_cancel₀ hz
  have h2 : X.an f = ((a / b : ℂ → ℂ) : Mero) := by
    calc X.an f = X.an f * ((b * b⁻¹ : ℂ → ℂ) : Mero) := by rw [h1, mul_one]
      _ = (X.an f * (b : Mero)) * ((b⁻¹ : ℂ → ℂ) : Mero) := by rw [Filter.Germ.coe_mul, mul_assoc]
      _ = ((a / b : ℂ → ℂ) : Mero) := by rw [hab, ← Filter.Germ.coe_mul, div_eq_mul_inv]
  rw [h2]
  refine Filter.Germ.coe_eq.2 ?_
  filter_upwards [compl_finite_mem_codiscreteWithin (s := Hs) (Set.finite_singleton τ)] with z hz
  exact hM.eqOn_compl_singleton_toMeromorphicNFAt hz

end GlobalTheory.KZ.H3

namespace GlobalTheory.KZ.H3

open Filter Topology

theorem exists_place_at_point : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) , JHol X → ∀ τ ∈ Hs,
    ∃ W : ValuationSubring X.K, X.OverY W ∧ ∀ f : X.K, f ∈ W ↔ ∃ φ : ℂ → ℂ, X.an f = (φ : Mero) ∧ AnalyticAt ℂ φ τ := by
  intro Ω _ _ ε X hj τ hτ
  have h0 : ∃ φ : ℂ → ℂ, X.an 0 = (φ : Mero) ∧ AnalyticAt ℂ φ τ :=
    ⟨0, by rw [map_zero, Filter.Germ.coe_zero], analyticAt_const⟩
  let W : ValuationSubring X.K :=
    { carrier := {f | ∃ φ : ℂ → ℂ, X.an f = (φ : Mero) ∧ AnalyticAt ℂ φ τ}
      zero_mem' := h0
      one_mem' := ⟨1, by rw [map_one, Filter.Germ.coe_one], analyticAt_const⟩
      add_mem' := by
        rintro f g ⟨φ, h1, h2⟩ ⟨ψ, h3, h4⟩
        exact ⟨φ + ψ, by rw [map_add (f := _), h1, h3, Filter.Germ.coe_add], h2.add h4⟩
      mul_mem' := by
        rintro f g ⟨φ, h1, h2⟩ ⟨ψ, h3, h4⟩
        exact ⟨φ * ψ, by rw [map_mul, h1, h3, Filter.Germ.coe_mul], h2.mul h4⟩
      neg_mem' := by
        rintro f ⟨φ, h1, h2⟩
        exact ⟨-φ, by rw [map_neg, h1, Filter.Germ.coe_neg], h2.neg⟩
      mem_or_inv_mem' := by
        intro f
        by_cases hf : f = 0
        · left; rw [hf]; exact h0
        obtain ⟨a, b, ha, hb, hb0, hab⟩ := X.an_mero f
        have hu : X.an f⁻¹ * X.an f = 1 := by rw [← map_mul, inv_mul_cancel₀ hf, map_one]
        by_cases hord : 0 ≤ meromorphicOrderAt (a / b) τ
        · left
          exact exists_analyticAt_of_order_nonneg X hτ f a b ha hb hb0 hab hord
        · right
          have ha0 : (a : Mero) ≠ 0 := by
            intro h
            apply hb0
            calc (b : Mero) = X.an f⁻¹ * (X.an f * (b : Mero)) := by rw [← mul_assoc, hu, one_mul]
              _ = 0 := by rw [hab, h, mul_zero]
          have hba : X.an f⁻¹ * (a : Mero) = (b : Mero) := by rw [← hab, ← mul_assoc, hu, one_mul]
          have hinv : b / a = (a / b)⁻¹ := by
            funext z; simp [inv_div]
          have hord' : 0 ≤ meromorphicOrderAt (b / a) τ := by
            rw [hinv, meromorphicOrderAt_inv]
            push_neg at hord
            generalize meromorphicOrderAt (a / b) τ = o at hord ⊢
            induction o with
            | top => simp at hord
            | coe n =>
              have hn : n < 0 := by exact_mod_cast hord
              have : (0 : WithTop ℤ) ≤ ((-n : ℤ) : WithTop ℤ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ -n)
              simpa using this
          exact exists_analyticAt_of_order_nonneg X hτ f⁻¹ b a hb ha ha0 hba hord' }
  refine ⟨W, ⟨fun c => ⟨fun _ => ε c, X.an_c c, analyticAt_const⟩, ?_⟩, fun f => Iff.rfl⟩
  obtain ⟨φ, h1, h2⟩ := hj
  exact ⟨φ, h1, h2.analyticAt (isOpen_Hs_place.mem_nhds hτ)⟩

end GlobalTheory.KZ.H3
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpUpperInt
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem Tower.exp_upper_int {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (a b d : ℤ)
    (ha : 0 < a) (hd : 0 < d) (f : X.K) (r : ℚ) :
    (X.exp (X.sl (toGQ !![a, b; 0, d]) f)).coeff (r * a / d) = eOm ε (r * b / d) * (X.exp f).coeff r := by
  have hdet : (0 : ℤ) < (!![a, b; 0, d] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    simp [Matrix.det_fin_two]; positivity
  have e : ∀ i j, ent (toGQ !![a, b; 0, d]) i j = ((!![a, b; 0, d] : Matrix (Fin 2) (Fin 2) ℤ) i j : ℚ) := by
    intro i j; rw [ent, toGQ, dite_eq_left hdet]; rfl
  have h := X.exp_upper (toGQ !![a, b; 0, d]) (by rw [e]; simp) f r
  simpa [e] using h

end GlobalTheory.KZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExponentsIntegralOfTranslationInvariant
section
open scoped MatrixGroups
open GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem exp_two_pi_rat_mem_range {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (r : ℚ) :
    ∃ a : Ω, ε a = Complex.exp (2 * Real.pi * Complex.I * (r : ℂ)) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero r.den := ⟨r.den_nz⟩
  haveI : NeZero (r.den : Ω) := ⟨Nat.cast_ne_zero.2 r.den_nz⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω r.den
  have hζ' : IsPrimitiveRoot (ε ζ) r.den := hζ.map_of_injective ε.injective
  have he : Complex.exp (2 * Real.pi * Complex.I * (r : ℂ)) ^ r.den = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨r.num, ?_⟩
    have h1 : ((r.den : ℚ) * r : ℚ) = r.num := Rat.den_mul_eq_num r
    have h2 : (r.den : ℂ) * (r : ℂ) = (r.num : ℂ) := by exact_mod_cast congrArg (fun x : ℚ => (x : ℂ)) h1
    rw [← h2]; ring
  obtain ⟨i, -, hi⟩ := hζ'.eq_pow_of_pow_eq_one he
  exact ⟨ζ ^ i, by rw [map_pow, hi]⟩

theorem Tower.exponent_integral_of_translation_invariant {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    {ε : Ω →+* ℂ} (X : Tower Ω ε) (h : X.K) (hh : X.sl (ofSL ModularGroup.T) h = h) (r : ℚ)
    (hr : (X.exp h).coeff r ≠ 0) : ∃ m : ℤ, r = m := by
  have e : ∀ (γ : SL(2, ℤ)) (i j : Fin 2), ent (ofSL γ) i j = ((γ.1 i j : ℤ) : ℚ) := fun _ _ _ => rfl
  have e10 : ent (ofSL ModularGroup.T) 1 0 = 0 := by rw [e]; simp [ModularGroup.T]
  have e00 : ent (ofSL ModularGroup.T) 0 0 = 1 := by rw [e]; simp [ModularGroup.T]
  have e01 : ent (ofSL ModularGroup.T) 0 1 = 1 := by rw [e]; simp [ModularGroup.T]
  have e11 : ent (ofSL ModularGroup.T) 1 1 = 1 := by rw [e]; simp [ModularGroup.T]
  have key := X.exp_upper _ e10 h r
  rw [hh, e00, e01, e11, mul_one, div_one] at key
  have h1 : eOm ε r = 1 := by
    have : eOm ε r * (X.exp h).coeff r = 1 * (X.exp h).coeff r := by rw [one_mul]; exact key.symm
    exact mul_right_cancel₀ hr this
  have h2 : ε (eOm ε r) = Complex.exp (2 * Real.pi * Complex.I * (r : ℂ)) :=
    Function.invFun_eq (exp_two_pi_rat_mem_range ε r)
  rw [h1, map_one] at h2
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h2.symm
  refine ⟨n, ?_⟩
  have h3 : (r : ℂ) = (n : ℂ) := by
    have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
    apply mul_left_cancel₀ hne
    rw [hn]; ring
  exact_mod_cast h3

end GlobalTheory.KZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExteriorTensorProductConvolutionCalculus
section
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem conv_tens {ι G : Type} [Fintype ι] [Group G] [Fintype G] (a b : ι → G → ℂ) :
    conv (tens a) (tens b) = tens fun v => conv (a v) (b v) := by
  funext x
  simp only [conv, tens]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← Finset.prod_mul_distrib]
  rfl

theorem conv_tens2 {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] (a a' : G → ℂ) (b b' : G' → ℂ) :
    conv (tens2 a b) (tens2 a' b') = tens2 (conv a a') (conv b b') := by
  funext x
  simp only [conv, tens2]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
  simp only [Prod.fst_mul, Prod.snd_mul, Prod.fst_inv, Prod.snd_inv]
  ring

theorem tens_calculus : ∀ (ι G G' : Type) [Fintype ι] [Group G] [Fintype G] [Group G'] [Fintype G'], (∀ a b : ι → G → ℂ, conv (tens a) (tens b) = tens fun v => conv (a v) (b v)) ∧ (∀ a : ι → G → ℂ, (∀ v, IsProj (a v)) → IsProj (tens a)) ∧ (∀ (a a' : G → ℂ) (b b' : G' → ℂ), conv (tens2 a b) (tens2 a' b') = tens2 (conv a a') (conv b b')) ∧ (∀ (a : G → ℂ) (b : G' → ℂ), IsProj a → IsProj b → IsProj (tens2 a b)) ∧ tens2 (dirac : G → ℂ) (dirac : G' → ℂ) = dirac ∧ ∀ (a a' : G → ℂ) (b b' : G' → ℂ), tens2 (a - a') b = tens2 a b - tens2 a' b ∧ tens2 a (b - b') = tens2 a b - tens2 a b' := by
  intro ι G G' _ _ _ _ _
  refine ⟨conv_tens, fun a h => ⟨?_, fun x => ?_⟩, conv_tens2, fun a b ha hb => ⟨?_, fun x => ?_⟩, ?_,
    fun a a' b b' => ⟨?_, ?_⟩⟩
  · rw [conv_tens]
    congr 1
    funext v
    exact (h v).1
  · simp only [tens, map_prod]
    exact Finset.prod_congr rfl fun v _ => (h v).2 (x v)
  · rw [conv_tens2, ha.1, hb.1]
  · simp only [tens2, map_mul, Prod.fst_inv, Prod.snd_inv, ha.2, hb.2]
  · funext ⟨x, y⟩
    simp only [tens2, dirac, Prod.mk_eq_one]
    by_cases hx : x = 1 <;> by_cases hy : y = 1 <;> simp [hx, hy]
  · funext x
    simp only [tens2, Pi.sub_apply, sub_mul]
  · funext x
    simp only [tens2, Pi.sub_apply, mul_sub]

end GlobalTheory.BadShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankEichlerShimuraCocyclesLeGamma1
section
section

open GlobalTheory.HeckeFamilyMatrices Polynomial
open scoped MatrixGroups

namespace GlobalTheory.HeckeFamilyMatrices.CocBound

theorem polySlash_apply (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w g p = ∑ i ∈ Finset.range (w + 1), p.coeff i •
      ((C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ)) ^ i *
        (C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)) ^ (w - i)) := by
  simp only [slP, LinearMap.sum_apply, LinearMap.comp_apply, lcoeff_apply,
    LinearMap.toSpanSingleton_apply]

theorem homogenize_eq_sum (w : ℕ) (p : ℂ[X]) :
    p.homogenize w = ∑ i ∈ Finset.range (w + 1),
      p.coeff i • ((MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) ^ i * MvPolynomial.X 1 ^ (w - i)) := by
  rw [homogenize, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i ≤ w := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [← homogenize_monomial hi', ← homogenize_X_pow hi', ← homogenize_smul, smul_X_eq_monomial]

theorem polySlash_eq_aeval (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w g p = MvPolynomial.aeval
      ![C ((g 0 0 : ℤ) : ℂ) * X + C ((g 0 1 : ℤ) : ℂ), C ((g 1 0 : ℤ) : ℂ) * X + C ((g 1 1 : ℤ) : ℂ)]
      (p.homogenize w) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [polySlash_apply, homogenize_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, map_mul, map_pow, map_pow, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  rfl

theorem isHomogeneous_lin (a b : ℂ) :
    (MvPolynomial.C a * MvPolynomial.X 0 + MvPolynomial.C b * MvPolynomial.X 1 :
      MvPolynomial (Fin 2) ℂ).IsHomogeneous 1 :=
  ((MvPolynomial.isHomogeneous_X ℂ (0 : Fin 2)).C_mul a).add
    ((MvPolynomial.isHomogeneous_X ℂ (1 : Fin 2)).C_mul b)

theorem homogenize_slP (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    (slP w g p).homogenize w = ∑ i ∈ Finset.range (w + 1), MvPolynomial.C (p.coeff i) *
      ((MvPolynomial.C ((g 0 0 : ℤ) : ℂ) * MvPolynomial.X 0 + MvPolynomial.C ((g 0 1 : ℤ) : ℂ) * MvPolynomial.X 1) ^ i *
        (MvPolynomial.C ((g 1 0 : ℤ) : ℂ) * MvPolynomial.X 0 +
          MvPolynomial.C ((g 1 1 : ℤ) : ℂ) * MvPolynomial.X 1) ^ (w - i)) := by
  apply homogenize_eq_of_isHomogeneous
  · refine MvPolynomial.IsHomogeneous.sum _ _ _ fun i hi => ?_
    have hi' : i ≤ w := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h := (((isHomogeneous_lin ((g 0 0 : ℤ) : ℂ) ((g 0 1 : ℤ) : ℂ)).pow i).mul
      ((isHomogeneous_lin ((g 1 0 : ℤ) : ℂ) ((g 1 1 : ℤ) : ℂ)).pow (w - i))).C_mul (p.coeff i)
    rwa [one_mul, one_mul, Nat.add_sub_of_le hi'] at h
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [polySlash_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [map_mul, map_pow, map_add (f := _), MvPolynomial.aeval_C, MvPolynomial.aeval_X, Matrix.cons_val_zero,
        Matrix.cons_val_one, mul_one, ← C_eq_algebraMap, smul_eq_C_mul]

theorem polySlash_polySlash (w : ℕ) (g h : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w h (slP w g p) = slP w (g * h) p := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [polySlash_eq_aeval w h, homogenize_slP, polySlash_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul, map_pow, map_add (f := _), MvPolynomial.aeval_C, MvPolynomial.aeval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, ← C_eq_algebraMap, smul_eq_C_mul, Matrix.mul_apply, Fin.sum_univ_two, Int.cast_add,
      Int.cast_mul]
  congr 3 <;> ring

theorem polySlash_mem_degreeLT (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) :
    slP w g p ∈ degreeLT ℂ (w + 1) := by
  rw [polySlash_apply]
  refine Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _ ?_
  have hi' : i ≤ w := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [mem_degreeLT]
  refine lt_of_le_of_lt degree_le_natDegree ?_
  have h1 : ∀ a b : ℂ, (C a * X + C b).natDegree ≤ 1 := fun a b => natDegree_linear_le
  have h2 := natDegree_mul_le_of_le (natDegree_pow_le_of_le i (h1 ((g 0 0 : ℤ) : ℂ) ((g 0 1 : ℤ) : ℂ)))
    (natDegree_pow_le_of_le (w - i) (h1 ((g 1 0 : ℤ) : ℂ) ((g 1 1 : ℤ) : ℂ)))
  rw [mul_one, mul_one, Nat.add_sub_of_le hi'] at h2
  exact_mod_cast Nat.lt_succ_of_le h2

theorem polySlash_one (w : ℕ) (p : ℂ[X]) (hp : p ∈ degreeLT ℂ (w + 1)) : slP w 1 p = p := by
  rw [polySlash_apply]
  have h : p.natDegree < w + 1 := by
    by_cases h0 : p = 0
    · simp [h0]
    · exact (natDegree_lt_iff_degree_lt h0).2 (mem_degreeLT.1 hp)
  conv_rhs => rw [p.as_sum_range' (w + 1) h]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [smul_X_eq_monomial]

theorem polySlash_action (w : ℕ) :
    (∀ (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]), slP w g p ∈ degreeLT ℂ (w + 1)) ∧
      (∀ p ∈ degreeLT ℂ (w + 1), slP w 1 p = p) ∧
      ∀ (g h : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]), slP w (g * h) p = slP w h (slP w g p) :=
  ⟨polySlash_mem_degreeLT w, polySlash_one w, fun g h p => (polySlash_polySlash w g h p).symm⟩

theorem dvd_trace_sub_two (N : ℕ) (x g : SL(2, ℤ)) (h : x * g * x⁻¹ ∈ CongruenceSubgroup.Gamma1 N) :
    (N : ℤ) ∣ (mat g).trace - 2 := by
  rw [CongruenceSubgroup.Gamma1_mem] at h
  have ht : (mat (x * g * x⁻¹)).trace = (mat g).trace := by
    change (mat (x * g) * mat x⁻¹).trace = _
    rw [Matrix.trace_mul_comm]
    change (mat (x⁻¹ * (x * g))).trace = _
    rw [inv_mul_cancel_left]
  rw [← ht, ← ZMod.intCast_zmod_eq_zero_iff_dvd, Matrix.trace_fin_two]
  push_cast
  rw [h.1, h.2.1]
  norm_num

theorem not_conj_mem (N : ℕ) (hN : 5 ≤ N) (x g : SL(2, ℤ)) (h1 : -2 ≤ (mat g).trace) (h2 : (mat g).trace < 2) :
    x * g * x⁻¹ ∉ CongruenceSubgroup.Gamma1 N := by
  intro h
  have := Int.le_of_dvd (by omega) ((dvd_neg).2 (dvd_trace_sub_two N x g h))
  omega

theorem torsion_not_mem (N : ℕ) (hN : 5 ≤ N) (x : SL(2, ℤ)) (k : ℕ) (hk : 0 < k) :
    (k < 4 → x * ModularGroup.S ^ k * x⁻¹ ∉ CongruenceSubgroup.Gamma1 N) ∧
      (k < 6 → x * (ModularGroup.S * ModularGroup.T) ^ k * x⁻¹ ∉ CongruenceSubgroup.Gamma1 N) := by
  constructor <;> intro hk' <;> interval_cases k <;> exact not_conj_mem N hN x _ (by decide) (by decide)

end GlobalTheory.HeckeFamilyMatrices.CocBound

end

open GlobalTheory.HeckeFamilyMatrices Polynomial
open scoped MatrixGroups

noncomputable section

namespace GlobalTheory.HeckeFamilyMatrices.CocBound

def rho (w : ℕ) (g : SL(2, ℤ)) : degreeLT ℂ (w + 1) →ₗ[ℂ] degreeLT ℂ (w + 1) :=
  ((slP w (mat g)).comp (degreeLT ℂ (w + 1)).subtype).codRestrict _ (fun p => (polySlash_action w).1 _ _)

theorem rho_mul (w : ℕ) (g h : SL(2, ℤ)) (v : degreeLT ℂ (w + 1)) :
    rho w (g * h) v = rho w h (rho w g v) := by
  apply Subtype.ext
  change slP w (mat (g * h)) v = slP w (mat h) (slP w (mat g) v)
  rw [← (polySlash_action w).2.2]
  rfl

theorem rho_one (w : ℕ) (v : degreeLT ℂ (w + 1)) : rho w 1 v = v := by
  apply Subtype.ext
  change slP w (mat 1) v = v
  exact (polySlash_action w).2.1 _ v.2

theorem rho_pow (w : ℕ) (g : SL(2, ℤ)) (m : ℕ) : rho w g ^ m = rho w (g ^ m) := by
  induction m with
  | zero => ext1 v; simp [rho_one]
  | succ m ih => ext1 v; rw [pow_succ', pow_succ, rho_mul, ← ih]; rfl

theorem rho_pow_eq_one (w : ℕ) (g : SL(2, ℤ)) (m : ℕ) (h : g ^ m = 1) : rho w g ^ m = 1 := by
  rw [rho_pow, h]; ext1 v; exact rho_one w v

def zMap (Γ : Subgroup SL(2, ℤ)) (w : ℕ) : Z1 Γ w →ₗ[ℂ] cocyc Γ (rho w) where
  toFun z := ⟨fun γ => ⟨z.1 γ, z.2.1 γ⟩, fun γ δ => Subtype.ext (z.2.2 γ δ)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem zMap_injective (Γ : Subgroup SL(2, ℤ)) (w : ℕ) : Function.Injective (zMap Γ w) := by
  intro z z' h
  apply Subtype.ext
  funext γ
  exact congrArg (fun f : cocyc Γ (rho w) => (f.1 γ : ℂ[X])) h

open ModularGroup in
theorem closure_S_ST : Subgroup.closure ({S, S * T} : Set SL(2, ℤ)) = ⊤ := by
  rw [eq_top_iff, ← SpecialLinearGroup.SL2Z_generators, Subgroup.closure_le]
  have hS : S ∈ Subgroup.closure ({S, S * T} : Set SL(2, ℤ)) := Subgroup.subset_closure (by simp)
  have hU : S * T ∈ Subgroup.closure ({S, S * T} : Set SL(2, ℤ)) := Subgroup.subset_closure (by simp)
  intro x hx
  rcases hx with rfl | rfl
  · exact hS
  · have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hS) hU
    simpa using this

end GlobalTheory.HeckeFamilyMatrices.CocBound

namespace GlobalTheory.HeckeFamilyMatrices


open CocBound ModularGroup in
theorem finrank_eichlerShimuraCocycles_le_Gamma1 (N : ℕ) (Γ : Subgroup SL(2, ℤ)) (w : ℕ) (hN : 5 ≤ N)
    (hΓ : Γ ≤ CongruenceSubgroup.Gamma1 N) (hfi : Γ.FiniteIndex) :
    FiniteDimensional ℂ (Z1 Γ w) ∧ 12 * Module.finrank ℂ (Z1 Γ w) ≤ (w + 1) * (12 + Γ.index) := by
  have hE : FiniteDimensional ℂ (degreeLT ℂ (w + 1)) := inferInstance
  have hr : Module.finrank ℂ (degreeLT ℂ (w + 1)) = w + 1 := by
    rw [(degreeLTEquiv ℂ (w + 1)).finrank_eq]; simp
  have hS4 : S ^ 4 = 1 := by decide
  have hU6 : (S * T) ^ 6 = 1 := by decide
  have hSU : S ^ 2 = (S * T) ^ 3 := by decide
  have hU3 : ((S * T) ^ 3) ^ 2 = 1 := by rw [← pow_mul]; exact hU6
  obtain ⟨-, h4⟩ := GlobalTheory.T.finrank_twistedLeftInvariant_mul_of_free_action Γ S (rho w S) 4 hfi hE (by norm_num) hS4 (rho_pow_eq_one w _ _ hS4)
    (fun x k hk hk' h => (torsion_not_mem N hN x k hk).1 hk' (hΓ h))
  obtain ⟨-, h6⟩ := GlobalTheory.T.finrank_twistedLeftInvariant_mul_of_free_action Γ (S * T) (rho w (S * T)) 6 hfi hE (by norm_num) hU6 (rho_pow_eq_one w _ _ hU6)
    (fun x k hk hk' h => (torsion_not_mem N hN x k hk).2 hk' (hΓ h))
  obtain ⟨f2, h2⟩ := GlobalTheory.T.finrank_twistedLeftInvariant_mul_of_free_action Γ ((S * T) ^ 3) (rho w ((S * T) ^ 3)) 2 hfi hE (by norm_num) hU3
    (rho_pow_eq_one w _ _ hU3) (fun x k hk hk' h => by
      obtain rfl : k = 1 := by omega
      rw [pow_one] at h
      exact (torsion_not_mem N hN x 3 (by norm_num)).2 (by norm_num) (hΓ h))
  obtain ⟨fC, hC⟩ := _root_.GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_relThree_add_finrank_twInv_le Γ (rho w) (S * T) (rho_mul w) (rho_one w) hU6 f2
  obtain ⟨fB, hB⟩ := GlobalTheory.T.finrank_cocycleExtension_le_orderThreeRelation_add Γ (rho w) S (S * T) (rho_mul w) (rho_one w) hSU closure_S_ST hE fC
  obtain ⟨fA, hA⟩ := GlobalTheory.T.finrank_cocycles_add_twistedInvariant_le_extension Γ (rho w) S (rho_mul w) (rho_one w) hS4 fB
  have hZ := LinearMap.finrank_le_finrank_of_injective (zMap_injective Γ w)
  refine ⟨Module.Finite.of_injective _ (zMap_injective Γ w), ?_⟩
  rw [hr] at h4 h6 h2 hB
  have : (w + 1) * (12 + Γ.index) = 12 * (w + 1) + Γ.index * (w + 1) := by ring
  omega

end GlobalTheory.HeckeFamilyMatrices
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesQDerivativeSubstUpperTriangularStatement
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hahnSeriesQDerivative_substUpperTriangular : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (a b d : ℚ), 0 < a / d → ∀ φ : HahnSeries ℚ Ω,
  qD (sub ε a b d φ) = HahnSeries.C (algebraMap ℚ Ω (a / d)) * sub ε a b d (qD φ) := by
  first | exact @GlobalTheory.CyclotomicQExpansion.qD_sub | exact GlobalTheory.CyclotomicQExpansion.qD_sub | (intros; apply GlobalTheory.CyclotomicQExpansion.qD_sub <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemMonicSquarefreeUnitConstPolysIffMonicSquarefrStatement
section
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_monicSquarefreeUnitConstPolys_iff_monic_squarefree : ∀ (g : ℕ) [Fact g.Prime], ∀ (N : ℕ) (f : (ZMod g)[X]), f ∈ sqSet g N ↔ f.Monic ∧ f.natDegree = N ∧ Squarefree f ∧ f.coeff 0 ≠ 0 := by
  first | exact @GlobalTheory.BadShare.mem_sqSet_iff | exact GlobalTheory.BadShare.mem_sqSet_iff | (intros; apply GlobalTheory.BadShare.mem_sqSet_iff <;> assumption)
end

