module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThHEqThSDictionary
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UnitaryActHalfSpace
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsRationalSymplecticOfUnitaryCmField
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IMemSiegel
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.HermitianWeilActionUnitaryGroupTestFunctions
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW

namespace WeilAct

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Ψ : Finset (E →+* ℂ)} {n N : ℕ}


omit [IsCMField E] in
theorem thH_smul (c : ℂ) (φ : Matrix (Fin n) (Fin N) E → ℂ) (Z : CM Ψ N N) (z z' : CM Ψ n N) :
    thH Ψ (c • φ) Z z z' = c * thH Ψ φ Z z z' := by
  unfold thH
  rw [← tsum_mul_left]
  refine tsum_congr fun x => ?_
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem thH_add (hΨ : IsType Ψ) {φ ψ : Matrix (Fin n) (Fin N) E → ℂ} (hφ : IsSB φ) (hψ : IsSB ψ)
    {Z : CM Ψ N N} (hZ : Z ∈ Hn Ψ N) (z z' : CM Ψ n N) :
    thH Ψ (φ + ψ) Z z z' = thH Ψ φ Z z z' + thH Ψ ψ Z z z' := by
  have h1 := ((_root_.GlobalTheory.SW.thH_summable_and_inj E Ψ hΨ n N φ hφ Z hZ).1 z z').of_norm
  have h2 := ((_root_.GlobalTheory.SW.thH_summable_and_inj E Ψ hΨ n N ψ hψ Z hZ).1 z z').of_norm
  unfold thH
  rw [← h1.tsum_add h2]
  refine tsum_congr fun x => ?_
  simp only [Pi.add_apply, add_mul]

theorem unique (hΨ : IsType Ψ) {γ : M2 E N} (hγ : γ ∈ UU E N)
    {φ ψ ψ' : Matrix (Fin n) (Fin N) E → ℂ} (hψ : IsSB ψ) (hψ' : IsSB ψ')
    (t : TransH Ψ γ φ ψ) (t' : TransH Ψ γ φ ψ') : ψ = ψ' := by
  have hZ := Base.I_mem_Hn (N := N) Ψ
  set Z : CM Ψ N N := fun _ => I • (1 : Matrix (Fin N) (Fin N) ℂ) with hZdef
  obtain ⟨hd, hA, -⟩ := (unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ
  refine (_root_.GlobalTheory.SW.thH_summable_and_inj E Ψ hΨ n N ψ hψ _ hA).2 ψ' hψ' fun w w' => ?_
  have u1 : ∀ τ, IsUnit (hDen Ψ γ Z τ).det := fun τ => (hd τ).1.isUnit
  have u2 : ∀ τ, IsUnit (hDen' Ψ γ Z τ).det := fun τ => by
    refine Ne.isUnit fun h => (hd τ).1 ?_
    rw [← (hd τ).2.1, h, zero_mul]
  have e1 := t Z hZ (fun τ => Matrix.of fun k => hDen' Ψ γ Z τ *ᵥ w τ k)
    (fun τ => Matrix.of fun k => w' τ k ᵥ* hDen Ψ γ Z τ)
  have e2 := t' Z hZ (fun τ => Matrix.of fun k => hDen' Ψ γ Z τ *ᵥ w τ k)
    (fun τ => Matrix.of fun k => w' τ k ᵥ* hDen Ψ γ Z τ)
  have a1 : (fun τ => Matrix.of fun k => (hDen' Ψ γ Z τ)⁻¹ *ᵥ
      (Matrix.of fun k => hDen' Ψ γ Z τ *ᵥ w τ k) k : CM Ψ n N) = w := by
    funext τ
    ext k i
    change ((hDen' Ψ γ Z τ)⁻¹ *ᵥ (hDen' Ψ γ Z τ *ᵥ w τ k)) i = _
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (u2 τ), Matrix.one_mulVec]
  have a2 : (fun τ => Matrix.of fun k =>
      (Matrix.of fun k => w' τ k ᵥ* hDen Ψ γ Z τ) k ᵥ* (hDen Ψ γ Z τ)⁻¹ : CM Ψ n N) = w' := by
    funext τ
    ext k i
    change ((w' τ k ᵥ* hDen Ψ γ Z τ) ᵥ* (hDen Ψ γ Z τ)⁻¹) i = _
    rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ (u1 τ), Matrix.vecMul_one]
  have e := e1.trans e2.symm
  beta_reduce at e
  rw [a1, a2] at e
  exact e

theorem ip_ofQ (E : Type) [Field E] [NumberField E] [IsCMField E] (n N : ℕ) :
    ∃ d : ℂ, d ≠ 0 ∧ ∀ φ ψ : Matrix (Fin n) (Fin N) E → ℂ, IsSB φ → IsSB ψ →
      ip (fun m : Matrix (Fin n) (QI E N) ℚ => φ (ofQ m)) (fun m => ψ (ofQ m)) = d * ip φ ψ := by
  obtain ⟨d, hd, h⟩ := _root_.GlobalTheory.SW.haar_ofQ_proportional E n N
  refine ⟨d, by exact_mod_cast hd.ne', fun φ ψ hφ hψ => ?_⟩
  have h1 : IsSB fun x => conj (ψ x) := (_root_.GlobalTheory.SW.isSB_algebra_haar_linear E _ _ ψ ψ hψ hψ).2.2.2.1
  exact h (fun x => φ x * conj (ψ x)) (_root_.GlobalTheory.SW.isSB_algebra_haar_linear E _ _ φ _ hφ h1).2.2.1

theorem ip_smul {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι] {c : ℂ}
    (hc : ‖c‖ = 1) (φ ψ : Matrix κ ι K → ℂ) : ip (c • φ) (c • ψ) = ip φ ψ := by
  unfold ip
  congr 1
  funext x
  have : c * conj c = 1 := by rw [Complex.mul_conj', hc]; simp
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  linear_combination (φ x * conj (ψ x)) * this

theorem exists_op (hΨ : IsType Ψ) (hn : Even n) {γ : M2 E N} (hγ : γ ∈ UU E N) :
    ∃ W : (Matrix (Fin n) (Fin N) E → ℂ) → Matrix (Fin n) (Fin N) E → ℂ, ∀ φ, IsSB φ →
      IsSB (W φ) ∧ TransH Ψ γ φ (W φ) ∧ ∀ φ', IsSB φ' → ip (W φ) (W φ') = ip φ φ' := by
  obtain ⟨hb, hS, -, hth, hsb⟩ := thH_eq_thS_dictionary E Ψ hΨ n N
  obtain ⟨σ, hσ, c, hc, hdict⟩ := _root_.GlobalTheory.SW.exists_symplectic_of_unitary E Ψ hΨ n N γ hγ
  obtain ⟨ω, hω⟩ := _root_.GlobalTheory.SW.exists_weil_of_symplectic (Fin n) (QI E N) σ (by simpa using hn) hσ
  obtain ⟨d, hd, hip⟩ := ip_ofQ E n N
  let e := Equiv.ofBijective _ hb
  let V : (Matrix (Fin n) (Fin N) E → ℂ) → Matrix (Fin n) (Fin N) E → ℂ := fun φ x =>
    ω (fun m => φ (ofQ m)) (e.symm x)
  have hV : ∀ φ, (fun m => V φ (ofQ m)) = ω fun m => φ (ofQ m) := fun φ => by
    funext m
    exact congrArg _ (e.symm_apply_apply m)
  have hVsb : ∀ φ, IsSB φ → IsSB (V φ) := fun φ hφ => by
    rw [hsb, hV]
    exact (hω _ ((hsb φ).1 hφ)).1
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc
  refine ⟨fun φ => (c ^ (n / 2))⁻¹ • V φ, fun φ hφ => ⟨?_, ?_, fun φ' hφ' => ?_⟩⟩
  · exact (_root_.GlobalTheory.SW.isSB_algebra_haar_linear E _ _ _ _ (hVsb φ hφ) (hVsb φ hφ)).2.1 _
  · intro Z hZ z z'
    obtain ⟨h1, h2, h3⟩ := hdict Z hZ
    obtain ⟨h3, h4⟩ := h3 z z'
    have key := (hω _ ((hsb φ).1 hφ)).2.1 _ (hS Z hZ) (zetaOf Ψ z z')
    rw [thH_smul, hth, hth, hV, ← h1, h3, key, h2, Finset.sum_congr rfl fun k _ => h4 k,
      Fintype.card_fin, mul_pow, ← Finset.prod_pow, hFac, Finset.prod_mul_distrib,
      ← Complex.exp_sum, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
    have hp : ∀ τ : Ψ, ((hDen Ψ γ Z τ).det ^ 2) ^ (n / 2) = (hDen Ψ γ Z τ).det ^ n := fun τ => by
      rw [← pow_mul, Nat.mul_div_cancel' hn.two_dvd]
    simp only [hp]
    have := pow_ne_zero (n / 2) hc0
    rw [← mul_assoc (π * I : ℂ) 2, show (π * I * 2 : ℂ) = 2 * π * I by ring]
    field_simp
  · rw [ip_smul (by simp [hc])]
    refine mul_left_cancel₀ hd ?_
    rw [← hip _ _ (hVsb φ hφ) (hVsb φ' hφ'), ← hip _ _ hφ hφ', hV, hV]
    exact (hω _ ((hsb φ).1 hφ)).2.2 _ ((hsb φ').1 hφ')

theorem weil_spec (hΨ : IsType Ψ) (hn : Even n) {γ : M2 E N} (hγ : γ ∈ UU E N)
    {φ : Matrix (Fin n) (Fin N) E → ℂ} (hφ : IsSB φ) :
    IsSB (weil Ψ γ φ) ∧ TransH Ψ γ φ (weil Ψ γ φ) := by
  obtain ⟨W, hW⟩ := exists_op hΨ hn hγ
  have h : ∃ ψ, IsSB ψ ∧ TransH Ψ γ φ ψ := ⟨W φ, (hW φ hφ).1, (hW φ hφ).2.1⟩
  rw [weil, dite_eq_left h]
  exact h.choose_spec

end WeilAct


open WeilAct in
theorem weil_action : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ), Even n → ∀ γ ∈ UU E N, ∀ φ : Matrix (Fin n) (Fin N) E → ℂ, IsSB φ → IsSB (weil Ψ γ φ) ∧ TransH Ψ γ φ (weil Ψ γ φ) ∧ (∀ ψ, IsSB ψ → TransH Ψ γ φ ψ → ψ = weil Ψ γ φ) ∧ (∀ ψ, IsSB ψ → ip (weil Ψ γ φ) (weil Ψ γ ψ) = ip φ ψ ∧ weil Ψ γ (φ + ψ) = weil Ψ γ φ + weil Ψ γ ψ) ∧ (∀ c : ℂ, weil Ψ γ (c • φ) = c • weil Ψ γ φ) ∧ (∀ γ' ∈ UU E N, weil Ψ (γ' * γ) φ = weil Ψ γ' (weil Ψ γ φ)) ∧ weil Ψ 1 φ = φ := by
  intro E _ _ _ Ψ hΨ n N hn γ hγ φ hφ
  obtain ⟨s1, t1⟩ := weil_spec hΨ hn hγ hφ
  refine ⟨s1, t1, fun ψ hψ t => unique hΨ hγ hψ s1 t t1, fun ψ hψ => ⟨?_, ?_⟩, fun c => ?_,
    fun γ' hγ' => ?_, ?_⟩
  · obtain ⟨s2, t2⟩ := weil_spec hΨ hn hγ hψ
    obtain ⟨W, hW⟩ := exists_op (n := n) hΨ hn hγ
    rw [unique hΨ hγ s1 (hW φ hφ).1 t1 (hW φ hφ).2.1,
      unique hΨ hγ s2 (hW ψ hψ).1 t2 (hW ψ hψ).2.1]
    exact (hW φ hφ).2.2 ψ hψ
  · obtain ⟨s2, t2⟩ := weil_spec hΨ hn hγ hψ
    obtain ⟨s3, t3⟩ := weil_spec hΨ hn hγ (_root_.GlobalTheory.SW.isSB_algebra_haar_linear E _ _ φ ψ hφ hψ).1
    refine unique hΨ hγ s3 (_root_.GlobalTheory.SW.isSB_algebra_haar_linear E _ _ _ _ s1 s2).1 t3 fun Z hZ z z' => ?_
    rw [thH_add hΨ s1 s2 ((unitary_act_halfSpace E Ψ N γ hγ).2 Z hZ).2.1, thH_add hΨ hφ hψ hZ,
      t1 Z hZ, t2 Z hZ, mul_add]
  · obtain ⟨s3, t3⟩ := weil_spec hΨ hn hγ ((_root_.GlobalTheory.SW.isSB_algebra_haar_linear E _ _ φ φ hφ hφ).2.1 c)
    refine unique hΨ hγ s3 ((_root_.GlobalTheory.SW.isSB_algebra_haar_linear E _ _ _ _ s1 s1).2.1 c) t3 fun Z hZ z z' => ?_
    rw [thH_smul, thH_smul, t1 Z hZ, mul_left_comm]
  · have hm := (unitary_act_halfSpace E Ψ N γ hγ).1.2.2.2.2 γ' hγ'
    obtain ⟨s2, t2⟩ := weil_spec hΨ hn hγ' s1
    obtain ⟨s3, t3⟩ := weil_spec hΨ hn hm hφ
    exact unique hΨ hm s3 s2 t3 ((transH_comp E Ψ n N γ γ' hγ hγ').2 _ _ _ t1 t2)
  · obtain ⟨s3, t3⟩ := weil_spec hΨ hn Base.one_mem_UU hφ
    exact unique hΨ Base.one_mem_UU s3 hφ t3 (Base.transH_one Ψ φ)

end GlobalTheory.SW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IsHeatThH
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW.ExpSum

section General

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {ι : Type*} {U : Set V}


omit [FiniteDimensional ℂ V] in
theorem convexOn_norm_term (c : ℂ) (L : V →L[ℂ] ℂ) :
    ConvexOn ℝ Set.univ fun p => ‖c * cexp (L p)‖ := by
  have h : ConvexOn ℝ Set.univ fun p => Real.exp ((L p).re) := by
    have := convexOn_exp.comp_linearMap
      (Complex.reLm ∘ₗ (L.toLinearMap.restrictScalars ℝ))
    exact this
  simpa only [norm_mul, Complex.norm_exp, smul_eq_mul] using h.smul (norm_nonneg c)

theorem locally_normal (hU : IsOpen U) (c : ι → ℂ) (L : ι → V →L[ℂ] ℂ)
    (hs : ∀ p ∈ U, Summable fun i => ‖c i * cexp (L i p)‖) :
    ∀ x ∈ U, ∃ W ∈ 𝓝 x, ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ p ∈ W, ‖c i * cexp (L i p)‖ ≤ u i := by
  intro x hx
  have : FiniteDimensional ℝ V := Module.Finite.trans ℂ V
  obtain ⟨b, hb, hbU⟩ := exists_mem_interior_convexHull_affineBasis (hU.mem_nhds hx)
  refine ⟨_, mem_interior_iff_mem_nhds.1 hb, fun i => ∑ j, ‖c i * cexp (L i (b j))‖,
    summable_sum fun j _ => hs _ (hbU (subset_convexHull ℝ _ ⟨j, rfl⟩)), fun i p hp => ?_⟩
  obtain ⟨y, ⟨j, rfl⟩, hy⟩ := (convexOn_norm_term (c i) (L i)).exists_ge_of_mem_convexHull
    (Set.subset_univ _) hp
  exact hy.trans (Finset.single_le_sum (f := fun j => ‖c i * cexp (L i (b j))‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ j))

theorem differentiableOn (hU : IsOpen U) (c : ι → ℂ) (L : ι → V →L[ℂ] ℂ)
    (hs : ∀ p ∈ U, Summable fun i => ‖c i * cexp (L i p)‖) :
    DifferentiableOn ℂ (fun p => ∑' i, c i * cexp (L i p)) U :=
  GlobalTheory.SCV.differentiableOn_tsum_of_locally_normal hU
    (fun i => Differentiable.differentiableOn (by fun_prop)) (locally_normal hU c L hs)

theorem hasSum_deriv (hU : IsOpen U) (c : ι → ℂ) (L : ι → V →L[ℂ] ℂ)
    (hs : ∀ p ∈ U, Summable fun i => ‖c i * cexp (L i p)‖) {p : V} (hp : p ∈ U) (v : V) :
    HasSum (fun i => c i * L i v * cexp (L i p))
      (deriv (fun s : ℂ => ∑' i, c i * cexp (L i (p + s • v))) 0) := by
  have h1 := GlobalTheory.SCV.hasSum_fderiv_of_locally_normal (F := fun i p => c i * cexp (L i p)) hU
    (fun i => Differentiable.differentiableOn (by fun_prop)) (locally_normal hU c L hs) hp
  have h2 := (ContinuousLinearMap.apply ℂ ℂ v).hasSum h1
  have h3 := ((differentiableOn hU c L hs).differentiableAt (hU.mem_nhds hp)).lineDeriv_eq_fderiv
    (v := v)
  rw [lineDeriv] at h3
  rw [h3]
  have e : (fun i => c i * L i v * cexp (L i p)) = fun i =>
      ContinuousLinearMap.apply ℂ ℂ v (fderiv ℂ (fun p => c i * cexp (L i p)) p) := by
    funext i
    have : HasFDerivAt (fun p => c i * cexp (L i p)) (c i • cexp (L i p) • L i) p :=
      ((L i).hasFDerivAt.cexp).const_mul (c i)
    rw [this.fderiv]
    simp
    ring
  rw [e]
  exact h2

theorem hasSum_deriv_deriv (hU : IsOpen U) (c : ι → ℂ) (L : ι → V →L[ℂ] ℂ)
    (hs : ∀ p ∈ U, Summable fun i => ‖c i * cexp (L i p)‖) {p : V} (v w : V)
    (hp : ∀ s : ℂ, p + s • v ∈ U) :
    HasSum (fun i => c i * L i w * L i v * cexp (L i p))
      (deriv (fun s : ℂ => deriv (fun t : ℂ => ∑' i, c i * cexp (L i (p + s • v + t • w))) 0) 0) := by
  have h := hasSum_deriv hU (fun i => c i * L i w) L
    (fun q hq => summable_norm_iff.2 (hasSum_deriv hU c L hs hq w).summable)
    (p := p) (by simpa using hp 0) v
  convert h using 3 with s
  exact (hasSum_deriv hU c L hs (hp s) w).tsum_eq.symm

end General

variable {E : Type} [Field E] (Ψ : Finset (E →+* ℂ)) {n N : ℕ}

theorem imH_isHermitian (Z : Matrix (Fin N) (Fin N) ℂ) : (imH Z).IsHermitian := by
  unfold imH IsHermitian
  rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_conjTranspose, ← neg_sub Z, smul_neg,
    ← neg_smul]
  congr 1
  simp

theorem isOpen_dom : IsOpen {p : CF Ψ N N × CF Ψ n N × CF Ψ n N | (p.1 : CM Ψ N N) ∈ Hn Ψ N} := by
  refine isOpen_iff_mem_nhds.2 fun p hp => ?_
  refine Filter.eventually_all.2 fun τ => ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB.posDef_eventually
    (fun q : CF Ψ N N × CF Ψ n N × CF Ψ n N => imH (q.1 τ)) (fun i j => ?_)
    (fun q => imH_isHermitian _) p (hp τ)
  change Continuous fun q : CF Ψ N N × CF Ψ n N × CF Ψ n N =>
    (2 * I)⁻¹ * (q.1 τ i j - star (q.1 τ j i))
  fun_prop

theorem expo_eq (x : Matrix (Fin n) (Fin N) E) (Z : CF Ψ N N) (z z' : CF Ψ n N) :
    expo Ψ x Z z z' = ∑ τ : Ψ, ∑ k, (∑ a, ∑ b, τ.1 (x k a) * (Z τ a b * conj (τ.1 (x k b))) +
      ∑ a, τ.1 (x k a) * z τ k a + ∑ a, z' τ k a * conj (τ.1 (x k a))) := by
  simp only [expo, dotProduct, mulVec, Finset.mul_sum]

noncomputable def form (x : Matrix (Fin n) (Fin N) E) :
    (CF Ψ N N × CF Ψ n N × CF Ψ n N) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => 2 * π * I * expo Ψ x p.1 p.2.1 p.2.2
      map_add' := fun p q => by
        simp only [expo_eq, Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, add_mul,
          Finset.sum_add_distrib]
        ring
      map_smul' := fun c p => by
        simp only [expo_eq, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
          RingHom.id_apply, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
        congr 1
        · congr 1
          · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
              Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
          · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
              Finset.sum_congr rfl fun _ _ => by ring
        · exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
            Finset.sum_congr rfl fun _ _ => by ring }

theorem form_apply (x : Matrix (Fin n) (Fin N) E) (p : CF Ψ N N × CF Ψ n N × CF Ψ n N) :
    form Ψ x p = 2 * π * I * expo Ψ x p.1 p.2.1 p.2.2 := rfl


open Classical in
noncomputable def dir {m : ℕ} (τ : Ψ) (k : Fin m) (a : Fin N) : CF Ψ m N :=
  fun σ i j => if σ = τ then if i = k then if j = a then 1 else 0 else 0 else 0


open Classical in
theorem add_smul_dir {m : ℕ} (x : CM Ψ m N) (τ : Ψ) (k : Fin m) (a : Fin N) (s : ℂ) :
    (fun σ => x σ + if σ = τ then Matrix.single k a s else 0 : CM Ψ m N) =
      (HAdd.hAdd (α := CF Ψ m N) (β := CF Ψ m N) x (s • dir Ψ τ k a) : CF Ψ m N) := by
  funext σ i j
  change x σ i j + (if σ = τ then Matrix.single k a s else 0 : Matrix (Fin m) (Fin N) ℂ) i j =
    x σ i j + s * dir Ψ τ k a σ i j
  by_cases h : σ = τ <;> by_cases h1 : i = k <;> by_cases h2 : j = a <;>
    simp [dir, h, h1, h2, Matrix.single] <;> tauto

theorem form_dir₁ (x : Matrix (Fin n) (Fin N) E) (τ : Ψ) (a b : Fin N) :
    form Ψ x (dir Ψ τ a b, 0, 0) = 2 * π * I * ∑ k, τ.1 (x k a) * conj (τ.1 (x k b)) := by
  classical
  rw [form_apply, expo_eq, Finset.sum_eq_single τ]
  · simp [dir]
  · intro σ _ h
    simp [dir, h]
  · simp

theorem form_dir₂ (x : Matrix (Fin n) (Fin N) E) (τ : Ψ) (k : Fin n) (a : Fin N) :
    form Ψ x (0, dir Ψ τ k a, 0) = 2 * π * I * τ.1 (x k a) := by
  classical
  rw [form_apply, expo_eq, Finset.sum_eq_single τ]
  · simp [dir]
  · intro σ _ h
    simp [dir, h]
  · simp

theorem form_dir₃ (x : Matrix (Fin n) (Fin N) E) (τ : Ψ) (k : Fin n) (a : Fin N) :
    form Ψ x (0, 0, dir Ψ τ k a) = 2 * π * I * conj (τ.1 (x k a)) := by
  classical
  rw [form_apply, expo_eq, Finset.sum_eq_single τ]
  · simp [dir]
  · intro σ _ h
    simp [dir, h]
  · simp


open Classical in
theorem line₁ (Z : CF Ψ N N) (z z' : CF Ψ n N) (τ : Ψ) (a b : Fin N) (s : ℂ) :
    (Z, z, z') + s • ((dir Ψ τ a b, 0, 0) : CF Ψ N N × CF Ψ n N × CF Ψ n N) =
      (Z + s • dir Ψ τ a b, z, z') := by simp

theorem line₂ (Z : CF Ψ N N) (z z' v : CF Ψ n N) (s : ℂ) :
    (Z, z, z') + s • ((0, v, 0) : CF Ψ N N × CF Ψ n N × CF Ψ n N) = (Z, z + s • v, z') := by simp

theorem line₃ (Z : CF Ψ N N) (z z' v : CF Ψ n N) (s : ℂ) :
    (Z, z, z') + s • ((0, 0, v) : CF Ψ N N × CF Ψ n N × CF Ψ n N) = (Z, z, z' + s • v) := by simp

theorem heat_dir (φ : Matrix (Fin n) (Fin N) E → ℂ)
    (hs : ∀ p ∈ {p : CF Ψ N N × CF Ψ n N × CF Ψ n N | (p.1 : CM Ψ N N) ∈ Hn Ψ N},
      Summable fun x => ‖φ x * cexp (form Ψ x p)‖)
    (Z : CF Ψ N N) (hZ : (Z : CM Ψ N N) ∈ Hn Ψ N) (z z' : CF Ψ n N) (τ : Ψ) (a b : Fin N) :
    2 * π * I * deriv (fun s : ℂ => ∑' x, φ x * cexp (form Ψ x (Z + s • dir Ψ τ a b, z, z'))) 0 =
      ∑ k, deriv (fun s : ℂ => deriv (fun t : ℂ => ∑' x, φ x *
        cexp (form Ψ x (Z, z + s • dir Ψ τ k a, z' + t • dir Ψ τ k b))) 0) 0 := by
  have h1 := (hasSum_deriv (isOpen_dom Ψ) φ (form Ψ) hs (p := (Z, z, z')) hZ
    (dir Ψ τ a b, 0, 0)).mul_left (2 * π * I)
  have h2 := hasSum_sum (s := Finset.univ) fun k _ =>
    hasSum_deriv_deriv (isOpen_dom Ψ) φ (form Ψ) hs (p := (Z, z, z'))
      (0, dir Ψ τ k a, 0) (0, 0, dir Ψ τ k b) (fun s => by rw [line₂]; exact hZ)
  have e : (fun x => 2 * π * I * (φ x * form Ψ x (dir Ψ τ a b, 0, 0) * cexp (form Ψ x (Z, z, z')))) =
      fun x => ∑ k, φ x * form Ψ x (0, 0, dir Ψ τ k b) * form Ψ x (0, dir Ψ τ k a, 0) *
        cexp (form Ψ x (Z, z, z')) := by
    funext x
    simp only [form_dir₁, form_dir₂, form_dir₃, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [e] at h1
  have h3 := h1.unique h2
  simp only [line₁, line₂, line₃] at h3
  exact h3

end GlobalTheory.SW.ExpSum


open GlobalTheory.SW.ExpSum in
theorem GlobalTheory.SW.isHeat_thH : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (n N : ℕ) (φ : Matrix (Fin n) (Fin N) E → ℂ), IsSB φ → IsHeat Ψ (thH Ψ φ) := by
  intro E _ _ _ Ψ hΨ n N φ hφ
  have hs : ∀ p ∈ {p : CF Ψ N N × CF Ψ n N × CF Ψ n N | (p.1 : CM Ψ N N) ∈ Hn Ψ N},
      Summable fun x => ‖φ x * cexp (form Ψ x p)‖ := fun p hp =>
    (GlobalTheory.SW.thH_summable_and_inj E Ψ hΨ n N φ hφ _ hp).1 _ _
  refine ⟨differentiableOn (isOpen_dom Ψ) φ (form Ψ) hs, fun Z hZ z z' τ a b => ?_⟩
  simp only [add_smul_dir]
  exact heat_dir Ψ φ hs Z hZ z z' τ a b
end

