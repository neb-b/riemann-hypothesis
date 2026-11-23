module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0220
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0247
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0241
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VecMulVecComm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0124
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0005

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionEqUnitSmulOfDiagonalCoefficientEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ThetaCoefficient

open GlobalTheory.FinTranslate

theorem exists_unit_smul {X : Type} (f f' : X → ℂ) (h : ∀ x y, f' y * star (f' x) = f y * star (f x)) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ f' = c • f := by
  have hn : ∀ x, ‖f' x‖ = ‖f x‖ := fun x => by
    have := congrArg norm (h x x)
    rw [norm_mul, norm_mul, norm_star, norm_star] at this
    exact (mul_self_inj (norm_nonneg _) (norm_nonneg _)).1 this
  by_cases h0 : ∀ x, f x = 0
  · refine ⟨1, norm_one, funext fun x => ?_⟩
    have := hn x
    rw [h0, norm_zero, norm_eq_zero] at this
    simp [this, h0]
  · obtain ⟨x, hx⟩ := not_forall.1 h0
    have hx' : f' x ≠ 0 := fun e => hx (by rw [← norm_eq_zero, ← hn, e, norm_zero])
    refine ⟨star (f x) / star (f' x), ?_, funext fun y => ?_⟩
    · rw [norm_div, norm_star, norm_star, hn, div_self (norm_ne_zero_iff.2 hx)]
    · have hs : star (f' x) ≠ 0 := star_ne_zero.2 hx'
      rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hs, h x y, mul_comm]

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem symplO_eq (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    norm_num
  unfold symplOH
  linear_combination (-symplO S T x y) * h2

theorem char_mul_heisO {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) {γ : WO S T} (hγ : γ ∈ ratL T S) (w x : WO S T) :
    ψ (symplO S T x γ) * heisO ψ S T w g x = ψ (symplOH S T γ w) * heisO ψ S T (γ + w) g x := by
  obtain ⟨γ, rfl⟩ := hγ
  have h := hg.quasi γ (x + w)
  show ψ (symplO S T x (ratW T S γ)) * (ψ (symplOH S T x w) * g (x + w)) =
    ψ (symplOH S T (ratW T S γ) w) * (ψ (symplOH S T x (ratW T S γ + w)) * g (x + (ratW T S γ + w)))
  rw [add_left_comm, h]
  simp only [← mul_assoc, ← AddChar.map_add_eq_mul]
  rw [symplO_eq, symplOH_add_right, symplOH_add_right, symplOH_skew S T x (ratW T S γ)]
  congr 2
  ring

theorem exists_unit_smul_of_coefficient_eq : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f f' : WO S T → ℂ, IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → (∀ w, ∫ x in 𝓕, heisO ψ S T w f' x * star (f' x) ∂μ = ∫ x in 𝓕, heisO ψ S T w f x * star (f x) ∂μ) → ∃ c : ℂ, ‖c‖ = 1 ∧ f' = c • f := by
  intro D ψ hψ S T μ 𝓕 hμ h𝓕 f f' hf hf' h
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  have : BorelSpace (WO S T) := ⟨rfl⟩
  have hT := @GlobalTheory.ThetaClosed.isThetaFunO_heisO_all D ψ hψ S T
  refine exists_unit_smul f f' fun x y => ?_
  obtain ⟨w, rfl⟩ : ∃ w, y = x + w := ⟨y - x, by abel⟩
  have key := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (WO S T) (ratL T S) K hK hKc (ratL T S)
    (fun γ x => ψ (symplO S T x γ))
    (fun γ => by
      simp only [symplO_eq]
      exact hψ.1.1.comp ((continuous_symplOH S T _).add (continuous_symplOH S T _)))
    (fun γ x y => by
      simp only [symplO_eq, symplOH_add_left, ← AddChar.map_add_eq_mul]
      rw [add_add_add_comm])
    (fun γ γ' x => by
      show ψ (symplO S T x (γ + γ')) = ψ (symplO S T x γ) * ψ (symplO S T x γ')
      simp only [symplO_eq, symplOH_add_right, ← AddChar.map_add_eq_mul]
      rw [add_add_add_comm])
    (fun x => by
      show ψ (symplO S T x 0) = 1
      rw [symplO_eq, symplOH_zero_right, add_zero, AddChar.map_zero_eq_one])
    (fun γ x => hψ.1.2.1 _)
    (fun x => by rw [← _root_.GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ S T x]; exact Subtype.forall)
    μ 𝓕 hμ h𝓕 (fun x => heisO ψ S T w f' x * star (f' x) - heisO ψ S T w f x * star (f x))
    (by
      have a := (hT hf' w).cont
      have b := (hT hf w).cont
      have a' := hf'.cont
      have b' := hf.cont
      generalize heisO ψ S T w f' = u at a
      generalize heisO ψ S T w f = v at b
      exact (a.mul a'.star).sub (b.mul b'.star))
    (fun γ hγ x => by
      have a := GlobalTheory.Size.mul_conj_periodic hψ (hT hf' w) hf' γ hγ x
      have b := GlobalTheory.Size.mul_conj_periodic hψ (hT hf w) hf γ hγ x
      simp only [starRingEnd_apply] at a b
      simp only [a, b])
    (fun γ => by
      have e : ∀ x, ψ (symplO S T x γ) * (heisO ψ S T w f' x * star (f' x) - heisO ψ S T w f x * star (f x)) =
          ψ (symplOH S T γ w) * (heisO ψ S T (γ + w) f' x * star (f' x) - heisO ψ S T (γ + w) f x * star (f x)) :=
        fun x => by
          linear_combination star (f' x) * char_mul_heisO hf' γ.2 w x - star (f x) * char_mul_heisO hf γ.2 w x
      simp only [e]
      have a := GlobalTheory.Size.integrableOn_mul_conj hψ hμ h𝓕 (hT hf' (γ + w)) hf'
      have b := GlobalTheory.Size.integrableOn_mul_conj hψ hμ h𝓕 (hT hf (γ + w)) hf
      rw [integral_const_mul]
      refine mul_eq_zero_of_right _ ((integral_sub a b).trans (sub_eq_zero.2 (h _))))
  have e := congrFun key x
  have hne : ψ (symplOH S T x w) ≠ 0 := fun e => by simpa [e] using hψ.1.2.1 (symplOH S T x w)
  simp only [heisO, Pi.zero_apply] at e
  refine mul_left_cancel₀ hne ?_
  linear_combination e

end GlobalTheory.ThetaCoefficient
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaKernelLiftConvergesContinuousGrowthDeriv
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum GlobalTheory.Mem.AutSpace GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
open scoped TensorProduct ContDiff Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Lift

theorem IsKerSys.mul_decay_le {D : D7} {θ : InfF D} {V W : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M]
    {κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)} (hκ : IsKerSys θ V W κ) {F : GA D V → ℂ} (hF : IsRapidDecay θ V F) :
    ∃ N : ℕ, ∀ f, ∃ C : ℝ, 0 ≤ C ∧ ∀ g h, ‖κ f g h * F g‖ ≤ C * (height θ W h : ℝ) ^ N := by
  obtain ⟨N, hN⟩ := hκ.growth
  obtain ⟨C', hC'⟩ := hF N
  refine ⟨N, fun f => ?_⟩
  obtain ⟨C, hC⟩ := hN f
  refine ⟨|C| * 2 ^ N * |C'|, by positivity, fun g h => ?_⟩
  obtain ⟨γ, hγ, hle⟩ := exists_height_le (θ := θ) g
  have h1 : (height θ V (γ * g) : ℝ) ≤ 2 * (quotHeight θ V g : ℝ) := by exact_mod_cast hle
  have h2 : ‖κ f g h‖ ≤ |C| * (2 * (quotHeight θ V g : ℝ) * (height θ W h : ℝ)) ^ N := by
    have := hκ.left f γ hγ 1 (one_mem _) g h
    rw [one_mul] at this
    rw [← this]
    exact (hC _ _).trans (mul_le_mul (le_abs_self _)
      (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right h1 (NNReal.coe_nonneg _)) N)
      (by positivity) (abs_nonneg _))
  calc ‖κ f g h * F g‖ = ‖κ f g h‖ * ‖F g‖ := norm_mul _ _
    _ ≤ |C| * (2 * (quotHeight θ V g : ℝ) * (height θ W h : ℝ)) ^ N * ‖F g‖ :=
        mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    _ = |C| * 2 ^ N * (‖F g‖ * (quotHeight θ V g : ℝ) ^ N) * (height θ W h : ℝ) ^ N := by
        rw [mul_pow, mul_pow]; ring
    _ ≤ |C| * 2 ^ N * |C'| * (height θ W h : ℝ) ^ N :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ((hC' g).trans (le_abs_self _)) (by positivity))
          (by positivity)

theorem lift_conv_cont_growth_deriv : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V W : HSp D) (M : Type) [AddCommGroup M] [Module ℂ M] (κ : M →ₗ[ℂ] (GA D V → GA D W → ℂ)), IsKerSys θ V W κ → ∀ μ 𝓕, IsQuot V μ 𝓕 → ∀ F ∈ Decay θ V, (∀ f h, IntegrableOn (fun g => κ f g h * F g) 𝓕 μ) ∧ (∀ f, Continuous fun h => ∫ g in 𝓕, κ f g h * F g ∂μ) ∧ (∃ N : ℕ, ∀ f, ∃ C : ℝ, ∀ h, ‖∫ g in 𝓕, κ f g h * F g ∂μ‖ ≤ C * (height θ W h : ℝ) ^ N) ∧ ∀ τ, ∀ X ∈ lieAt W τ, ∀ f f', (∀ g h, HasDerivAt (fun t : ℝ => κ f g (h * oneP θ W τ X t)) (κ f' g h) 0) → ∀ h, HasDerivAt (fun t : ℝ => ∫ g in 𝓕, κ f g (h * oneP θ W τ X t) * F g ∂μ) (∫ g in 𝓕, κ f' g h * F g ∂μ) 0 := by
  intro D θ hθ V W M _ _ κ hκ μ 𝓕 hQ F hF
  have : BorelSpace (GA D V) := ⟨rfl⟩
  have : SecondCountableTopology (GA D V) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V).2.1
  have : SecondCountableTopology (GA D W) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W).2.1
  have : IsTopologicalGroup (GA D W) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W).2.2.2.2.1
  have hfin : μ 𝓕 ≠ ⊤ := (GlobalTheory.Mem.QuotVol.quot_volume_ne_zero_ne_top D V μ 𝓕 hQ).2
  have : IsFiniteMeasure (μ.restrict 𝓕) := isFiniteMeasure_restrict.2 hfin
  obtain ⟨hc, hd⟩ : Continuous F ∧ IsRapidDecay θ V F := hF.2.2 [] (by simp)
  obtain ⟨N, hN⟩ := hκ.mul_decay_le hd
  have hm : ∀ f h, AEStronglyMeasurable (fun g => κ f g h * F g) (μ.restrict 𝓕) := fun f h =>
    (((hκ.cont f).comp (Continuous.prodMk_left h)).mul hc).aestronglyMeasurable
  have hint : ∀ f h, IntegrableOn (fun g => κ f g h * F g) 𝓕 μ := fun f h => by
    obtain ⟨C, -, hC⟩ := hN f
    exact Measure.integrableOn_of_bounded hfin
      (((hκ.cont f).comp (Continuous.prodMk_left h)).mul hc).aestronglyMeasurable (.of_forall fun g => hC g h)
  have hloc : ∀ f h₀, ∃ B : ℝ, ∀ᶠ h in 𝓝 h₀, ∀ g, ‖κ f g h * F g‖ ≤ B := fun f h₀ => by
    obtain ⟨C, h0, hC⟩ := hN f
    obtain ⟨B, hB⟩ := GlobalTheory.Mem.LiftHeight.height_locally_bounded D θ hθ W h₀
    exact ⟨C * B ^ N, hB.mono fun h hh g => (hC g h).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) hh N) h0)⟩
  refine ⟨hint, fun f => continuous_iff_continuousAt.2 fun h₀ => ?_, ⟨N, fun f => ?_⟩, fun τ X hX f f' hder h => ?_⟩
  · obtain ⟨B, hB⟩ := hloc f h₀
    exact continuousAt_of_dominated (bound := fun _ => B) (.of_forall (hm f)) (hB.mono fun h hh => .of_forall hh)
      (integrable_const B) (.of_forall fun g =>
        (((hκ.cont f).comp (Continuous.prodMk_right g)).mul continuous_const).continuousAt)
  · obtain ⟨C, -, hC⟩ := hN f
    refine ⟨C * (μ.restrict 𝓕).real Set.univ, fun h => ?_⟩
    refine (norm_integral_le_of_norm_le_const (.of_forall fun g => hC g h)).trans_eq ?_
    ring
  · obtain ⟨B, hB⟩ := hloc f' h
    have hco : Filter.Tendsto (fun t : ℝ => h * oneP θ W τ X t) (𝓝 0) (𝓝 h) := by
      have := (continuous_const (y := h).mul (continuous_oneP hθ hX)).tendsto 0
      rw [Pi.mul_apply, oneP_zero hθ, mul_one] at this
      exact this
    have := (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict 𝓕) (x₀ := (0 : ℝ))
      (F := fun t g => κ f g (h * oneP θ W τ X t) * F g) (F' := fun t g => κ f' g (h * oneP θ W τ X t) * F g)
      (bound := fun _ => B) (hco.eventually hB) (.of_forall fun t => hm f _) (hint f _) (hm f' _)
      (.of_forall fun g t ht => ht g) (integrable_const B)
      (.of_forall fun g t _ => (hasDerivAt_oneP hθ hX (φ := κ f g) (φ' := κ f' g) (hder g) h t).mul_const (F g))).2
    simpa only [oneP_zero hθ, mul_one] using this

end GlobalTheory.Mem.Lift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffEqTensorSquareTopCoefficient
section
noncomputable section

open MvPolynomial TensorProduct

namespace GlobalTheory.GrassModel.TopRead

variable {n : ℕ}

theorem list_prod_gen {m : ℕ} (x : Fin m → Fin n × Fin n) :
    (List.ofFn fun j => gen n (x j)).prod =
      (List.ofFn fun j => vec n (x j).1).prod ⊗ₜ (List.ofFn fun j => vec n (x j).2).prod := by
  induction m with
  | zero => simp [Algebra.TensorProduct.one_def]
  | succ m ih =>
    rw [List.ofFn_succ, List.prod_cons, ih (fun j => x j.succ)]
    simp only [List.ofFn_succ, List.prod_cons, gen, Algebra.TensorProduct.tmul_mul_tmul]

theorem topBig_toEven_prod {m : ℕ} (x : Fin m → Fin n × Fin n) :
    topBig n ((toEven n (∏ j, X (x j)) : EvenPart n) : Big n) =
      topForm n m (fun j => Pi.single (x j).1 1) * topForm n m (fun j => Pi.single (x j).2 1) := by
  have h1 : ((toEven n (∏ j, X (x j)) : EvenPart n) : Big n) = (List.ofFn fun j => gen n (x j)).prod := by
    rw [map_prod, ← List.prod_ofFn, ← Subalgebra.coe_val, map_list_prod, List.map_ofFn]
    congr 1
    exact congrArg List.ofFn (funext fun j => by simp [toEven, aeval_X])
  rw [h1, list_prod_gen, topBig_tmul]
  simp only [topExt, vec]
  rw [← ExteriorAlgebra.ιMulti_apply, ← ExteriorAlgebra.ιMulti_apply,
    ExteriorAlgebra.liftAlternating_apply_ιMulti, ExteriorAlgebra.liftAlternating_apply_ιMulti]

theorem toMultiset_sum_single {α : Type*} [DecidableEq α] {m : ℕ} (x : Fin m → α) :
    Finsupp.toMultiset (∑ j, Finsupp.single (x j) 1) = Finset.univ.val.map x := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_multiset_sum]
  simp only [Finsupp.toMultiset_single, one_nsmul]
  have : (fun j => ({x j} : Multiset α)) = (fun a => ({a} : Multiset α)) ∘ x := rfl
  rw [this, ← Multiset.map_map, Multiset.sum_map_singleton]

theorem toMultiset_injective' {α : Type*} [DecidableEq α] :
    Function.Injective (Finsupp.toMultiset : (α →₀ ℕ) → Multiset α) := fun f g h => by
  rw [← Finsupp.toMultiset_toFinsupp f, h, Finsupp.toMultiset_toFinsupp]

theorem coeff_prod_X {m : ℕ} (x : Fin m → Fin n × Fin n) (d : Fin n × Fin n →₀ ℕ) :
    AddMonoidAlgebra.coeff (∏ j, X (x j) : MvPolynomial (Fin n × Fin n) ℂ) d =
      if Finset.univ.val.map x = Finsupp.toMultiset d then 1 else 0 := by
  classical
  have e : (∏ j, X (x j) : MvPolynomial (Fin n × Fin n) ℂ) = monomial (∑ j, Finsupp.single (x j) 1) 1 :=
    (monomial_sum_one _ _).symm
  rw [e, coeff_monomial, ← toMultiset_sum_single]
  simp only [toMultiset_injective'.eq_iff]

theorem topForm_self (v : Fin n → Fin n → ℂ) : topForm n n v = (Pi.basisFun ℂ (Fin n)).det v := by
  simp [topForm]

theorem det_single_perm (π : Equiv.Perm (Fin n)) :
    (Pi.basisFun ℂ (Fin n)).det (fun j => Pi.single (π j) 1) = ((Equiv.Perm.sign π : ℤ) : ℂ) := by
  have : (fun j => (Pi.single (π j) 1 : Fin n → ℂ)) = (Pi.basisFun ℂ (Fin n)) ∘ π := by
    funext j; simp
  rw [this, AlternatingMap.map_perm, Module.Basis.det_self, Units.smul_def, zsmul_eq_mul, mul_one]

theorem det_single_not_inj (a : Fin n → Fin n) (ha : ¬ Function.Injective a) :
    (Pi.basisFun ℂ (Fin n)).det (fun j => Pi.single (a j) 1) = 0 := by
  refine AlternatingMap.map_eq_zero_of_not_injective _ _ fun h => ha fun i j hij => h ?_
  simp [hij]


open Classical in
theorem topCoeff_prod {m : ℕ} (x : Fin m → Fin n × Fin n) :
    GlobalTheory.GoodMetric.topCoeff (∏ j, X (x j) : MvPolynomial (Fin n × Fin n) ℂ) =
      topForm n m (fun j => Pi.single (x j).1 1) * topForm n m (fun j => Pi.single (x j).2 1) := by
  unfold GlobalTheory.GoodMetric.topCoeff
  simp_rw [coeff_prod_X, toMultiset_sum_single]
  by_cases hm : m = n
  swap
  · have h0 : topForm n m = 0 := by simp [topForm, hm]
    rw [h0]
    simp only [AlternatingMap.zero_apply, mul_zero]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [if_neg, mul_zero]
    intro heq
    have := congrArg Multiset.card heq
    simp at this
    exact hm this
  subst hm
  rw [topForm_self, topForm_self]
  set a : Fin m → Fin m := fun j => (x j).1 with ha_def
  set b : Fin m → Fin m := fun j => (x j).2 with hb_def

  have hcond : ∀ w : Equiv.Perm (Fin m),
      Finset.univ.val.map x = Finset.univ.val.map (fun c => (c, w c)) →
        Function.Injective a ∧ Function.Injective b := by
    intro w heq
    have h1 := congrArg (Multiset.map Prod.fst) heq
    have h2 := congrArg (Multiset.map Prod.snd) heq
    simp only [Multiset.map_map] at h1 h2
    have e1 : Multiset.map (Prod.fst ∘ fun c => (c, w c)) Finset.univ.val = Finset.univ.val := by
      simp
    have e2 : Multiset.map (Prod.snd ∘ fun c => (c, w c)) Finset.univ.val = Finset.univ.val := by
      simpa using Multiset.map_univ_val_equiv w
    rw [e1] at h1
    rw [e2] at h2
    constructor
    · have hn : (Multiset.map (Prod.fst ∘ x) Finset.univ.val).Nodup := by rw [h1]; exact Finset.univ.nodup
      exact fun i j hij => (Multiset.nodup_map_iff_inj_on Finset.univ.nodup).mp hn i (by simp) j (by simp) hij
    · have hn : (Multiset.map (Prod.snd ∘ x) Finset.univ.val).Nodup := by rw [h2]; exact Finset.univ.nodup
      exact fun i j hij => (Multiset.nodup_map_iff_inj_on Finset.univ.nodup).mp hn i (by simp) j (by simp) hij
  by_cases hab : Function.Injective a ∧ Function.Injective b
  swap
  · have : (Pi.basisFun ℂ (Fin m)).det (fun j => Pi.single (x j).1 1) *
        (Pi.basisFun ℂ (Fin m)).det (fun j => Pi.single (x j).2 1) = 0 := by
      rcases not_and_or.mp hab with h | h
      · rw [det_single_not_inj a h, zero_mul]
      · rw [det_single_not_inj b h, mul_zero]
    rw [this]
    refine Finset.sum_eq_zero fun w _ => ?_
    rw [if_neg, mul_zero]
    exact fun heq => hab (hcond w heq)
  obtain ⟨ha, hb⟩ := hab
  let π : Equiv.Perm (Fin m) := Equiv.ofBijective a (Finite.injective_iff_bijective.mp ha)
  let τ : Equiv.Perm (Fin m) := Equiv.ofBijective b (Finite.injective_iff_bijective.mp hb)
  have hπ : ∀ j, (x j).1 = π j := fun j => rfl
  have hτ : ∀ j, (x j).2 = τ j := fun j => rfl
  simp_rw [hπ, hτ, det_single_perm]
  have hx : x = (fun c => (c, (τ * π⁻¹) c)) ∘ π := by
    funext j
    simp [Prod.ext_iff, hπ, hτ]
  have hmap : Finset.univ.val.map x = Finset.univ.val.map (fun c => (c, (τ * π⁻¹) c)) := by
    rw [hx, ← Multiset.map_map, Multiset.map_univ_val_equiv]
  rw [Finset.sum_eq_single (τ * π⁻¹)]
  · rw [if_pos hmap, mul_one, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv]
    push_cast
    ring
  · intro w _ hw
    rw [if_neg, mul_zero]
    intro heq
    apply hw
    ext c
    have hc : (c, w c) ∈ Finset.univ.val.map (fun c => (c, (τ * π⁻¹) c)) := by
      rw [← hmap, heq]; simp
    obtain ⟨c', _, hc'⟩ := Multiset.mem_map.mp hc
    simp only [Prod.mk.injEq] at hc'
    obtain ⟨rfl, h⟩ := hc'
    exact congrArg Fin.val h.symm
  · intro h; exact absurd (Finset.mem_univ _) h

theorem topCoeff_eq_topBig (n : ℕ) (P : MvPolynomial (Fin n × Fin n) ℂ) :
    GlobalTheory.GoodMetric.topCoeff P = topBig n (toEven n P : Big n) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial u c =>
    obtain ⟨l, hl⟩ : ∃ l : List (Fin n × Fin n), (l : Multiset _) = Finsupp.toMultiset u :=
      ⟨_, Multiset.coe_toList _⟩
    have hu : u = ∑ j, Finsupp.single (l.get j) 1 := by
      apply toMultiset_injective'
      rw [toMultiset_sum_single, Fin.univ_val_map, List.ofFn_get, hl]
    have hmon : (monomial u c : MvPolynomial (Fin n × Fin n) ℂ) = c • ∏ j, X (l.get j) := by
      rw [hu, show (∏ j, X (l.get j) : MvPolynomial (Fin n × Fin n) ℂ) = monomial (∑ j, Finsupp.single (l.get j) 1) 1 from
        (monomial_sum_one _ _).symm, smul_monomial, smul_eq_mul, mul_one]
    rw [hmon, map_smul, Subalgebra.coe_smul, map_smul, smul_eq_mul, topBig_toEven_prod, ← topCoeff_prod]
    unfold GlobalTheory.GoodMetric.topCoeff
    simp only [coeff_smul, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => by ring
  | add p q hp hq =>
    rw [map_add (f := _), Subalgebra.coe_add, map_add (f := _), ← hp, ← hq]
    unfold GlobalTheory.GoodMetric.topCoeff
    simp only [MvPolynomial.coeff_add, mul_add, Finset.sum_add_distrib]

end GlobalTheory.GrassModel.TopRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValPowClassNumber
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.ChiVal

theorem val_pow_classNumber {L : Type} [Field L] [NumberField L] (ξ : Formalism.L2.Host.HChar L) (hu : ∀ v, ξ.UnrAt v) (hi : ∀ k, ξ.inf k = 1)
    (v : HeightOneSpectrum (𝓞 L)) : ξ.val v ^ classNumber L = 1 := by
  obtain ⟨γ, h0, hγ⟩ := GlobalTheory.Mem.FieldsEx.exists_gen v.asIdeal v.ne_bot
  have h1 : (γ : L) ≠ 0 := by exact_mod_cast h0
  have h2 := GlobalTheory.Mem.ValPow.inf_mul_val_pow L ξ ∅ (fun w _ => hu w) (fun w hw => absurd hw (Finset.notMem_empty w)) v
    (Finset.notMem_empty v) (classNumber L) (Units.mk0 _ h1)
    (by rw [← FractionalIdeal.coeIdeal_pow, hγ, FractionalIdeal.coeIdeal_span_singleton]; rfl)
    (fun w hw => absurd hw (Finset.notMem_empty w))
  rwa [hi, one_mul] at h2

theorem mem_of_pow_eq_one (M : Subfield ℂ) {n : ℕ} (hn : n ≠ 0)
    (hM : Complex.exp (2 * Real.pi * Complex.I / (n : ℕ)) ∈ M) {x : ℂ} (hx : x ^ n = 1) : x ∈ M := by
  have : NeZero n := ⟨hn⟩
  obtain ⟨i, -, rfl⟩ := (Complex.isPrimitiveRoot_exp n hn).eq_pow_of_pow_eq_one hx
  exact pow_mem hM i

theorem val_sq_eq {L : Type} [Field L] [NumberField L] (η : Formalism.L2.Host.HChar L) (v : HeightOneSpectrum (𝓞 L)) :
    ((η.val v : ℂˣ) : ℂ) * ((η.val v : ℂˣ) : ℂ) = η.valTw (1 / 2) v ^ 2 * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) := by
  have h0 : ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  have h1 : (((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (-(((1 / 2 : ℝ)) : ℂ))) ^ 2 * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) = 1 := by
    rw [sq, ← Complex.cpow_add _ _ h0, show -(((1 / 2 : ℝ)) : ℂ) + -(((1 / 2 : ℝ)) : ℂ) = -1 by push_cast; ring,
      Complex.cpow_neg_one, inv_mul_cancel₀ h0]
  unfold Formalism.L2.Host.HChar.valTw
  rw [mul_pow, mul_assoc, h1, mul_one, sq]

theorem chiId_mem {L : Type} [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (M : Subfield ℂ)
    (h : ∀ w, ((χ.val w : ℂˣ) : ℂ) ∈ M) (𝔞 : Submodule (𝓞 L) L) : chiId χ 𝔞 ∈ M := by
  unfold chiId
  refine finprod_induction (fun u : ℂˣ => (u : ℂ) ∈ M) (one_mem M) (fun a b ha hb => mul_mem ha hb) fun w => ?_
  rw [Units.val_pow_eq_pow_val]
  exact pow_mem (h w) _

theorem chi_values : ∀ (B : Base) (X : PreX B.toPre) (I : ColIn B X), I.Ok →
    (∀ w, ∃ k : B.LL, B.embLL k = ((I.C.chiPsi.val w : ℂˣ) : ℂ)) ∧ ∀ 𝔞, ∃ k : B.LL, B.embLL k = I.chi 𝔞 := by
  intro B X I h
  have key : ∀ w, ((I.C.chiPsi.val w : ℂˣ) : ℂ) ∈ B.embLL.fieldRange := by
    intro w
    have hc := I.C.isEta.sq_chiPsi.div_cls I.C.isChi
    have h1 := val_pow_classNumber _ hc.unr hc.inf w
    obtain ⟨z, -, hz⟩ := B.roots_Ks' (classNumber B.host.E) (by simp)
    have h2 : (((I.C.chiPsi * (I.C.eta * I.C.eta)⁻¹).val w : ℂˣ) : ℂ) ∈ B.embLL.fieldRange :=
      mem_of_pow_eq_one B.embLL.fieldRange (classNumber_ne_zero B.host.E) ⟨z, hz⟩
        (by rw [← Units.val_pow_eq_pow_val, h1, Units.val_one])
    have h3 : I.C.eta.valTw (1 / 2) w ∈ B.embLL.fieldRange := ⟨_, h.ch_tied.etaVal w⟩
    have h4 : I.C.chiPsi.val w = (I.C.chiPsi * (I.C.eta * I.C.eta)⁻¹).val w * (I.C.eta.val w * I.C.eta.val w) := by
      rw [Formalism.L2.Host.HChar.val_mul, Formalism.L2.Host.HChar.val_inv, Formalism.L2.Host.HChar.val_mul, inv_mul_cancel_right]
    rw [h4, Units.val_mul, Units.val_mul (I.C.eta.val w), val_sq_eq]
    exact mul_mem h2 (mul_mem (pow_mem h3 2) (natCast_mem _ _))
  exact ⟨key, fun 𝔞 => chiId_mem _ _ key 𝔞⟩

end GlobalTheory.Mem.ChiVal

end
end

