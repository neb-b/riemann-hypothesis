module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0212

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GlCharacterEqOneOfTransposeInv
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage

namespace GlobalTheory

theorem gl_character_eq_one_of_transpose_inv (k : Type) [Field k] [Infinite k] (n : Type)
    [Fintype n] [DecidableEq n] (χ : GL n k →* NNReal)
    (h : ∀ g g' : GL n k, g'.val = (g⁻¹ : GL n k).valᵀ → χ g' = χ g) (g : GL n k) :
    χ g = 1 := by
  classical
  have hne : ∀ g : GL n k, χ g ≠ 0 := by
    intro g h0
    have : χ (g * g⁻¹) = 1 := by simp
    rw [map_mul, h0, zero_mul] at this
    exact zero_ne_one this
  have hdiag : ∀ (D : n → k) (g : GL n k), g.val = diagonal D → χ g = 1 := by
    intro D g hg
    have h1 : χ g⁻¹ = χ g := by
      apply h
      rw [Matrix.coe_units_inv, Matrix.transpose_nonsing_inv, hg, diagonal_transpose]
    have h2 : χ g * χ g = 1 := by
      calc χ g * χ g = χ g * χ g⁻¹ := by rw [h1]
        _ = 1 := by rw [← map_mul]; simp
    have h3 : χ g ^ 2 = 1 := by rw [sq, h2]
    exact (pow_eq_one_iff_of_nonneg (zero_le) two_ne_zero).1 h3
  obtain ⟨a, ha⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset k)
  have ha0 : a ≠ 0 := by intro h0; apply ha; simp [h0]
  have ha1 : 1 - a ≠ 0 := by
    intro h0; apply ha; have : a = 1 := by linear_combination -h0
    simp [this]
  have htr : ∀ (t : TransvectionStruct n k) (g : GL n k), g.val = t.toMatrix → χ g = 1 := by
    rintro ⟨i, j, hij, x⟩ g hg
    let T : k → GL n k := fun y => GeneralLinearGroup.mkOfDetNeZero (transvection i j y)
      (by rw [det_transvection_of_ne i j hij]; exact one_ne_zero)
    have hT : ∀ y, (T y).val = transvection i j y := fun y => rfl
    have hgT : g = T x := Units.ext (by rw [hg, hT]; rfl)
    have hconj : ∀ b : k, b ≠ 0 → χ (T (b * x)) = χ (T x) := by
      intro b hb
      let D : GL n k := GeneralLinearGroup.mkOfDetNeZero (diagonal (Function.update 1 i b))
        (by
          rw [det_diagonal]
          refine Finset.prod_ne_zero_iff.2 fun l _ => ?_
          by_cases hl : l = i
          · subst hl; simpa using hb
          · simp [Function.update_of_ne hl])
      have hD : D.val = diagonal (Function.update 1 i b) := rfl
      have e : D * T x = T (b * x) * D := by
        apply Units.ext
        rw [Units.val_mul, Units.val_mul, hD, hT, hT]
        ext p q
        rw [diagonal_mul, mul_diagonal]
        simp only [transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
        by_cases hp : i = p
        · subst hp
          by_cases hq : j = q
          · subst hq
            simp [hij, Function.update_of_ne hij.symm]
          · by_cases hpq : i = q
            · subst hpq; simp [hq]
            · simp [hq, hpq]
        · by_cases hpq : p = q
          · subst hpq; simp [hp]
          · simp [hp, hpq]
      have := congrArg χ e
      rw [map_mul, map_mul, hdiag _ D hD, one_mul, mul_one] at this
      exact this.symm
    have e : T x = T (a * x) * T ((1 - a) * x) := by
      apply Units.ext
      rw [Units.val_mul, hT, hT, hT, transvection_mul_transvection_same i j hij]
      congr 1
      ring
    have e2 := congrArg χ e
    rw [map_mul, hconj a ha0, hconj _ ha1] at e2
    rw [hgT]
    exact (mul_eq_left₀ (hne _)).1 e2.symm
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M => ∀ g : GL n k, g.val = M → χ g = 1) g.val g.det_ne_zero
    (fun D _ => hdiag D) htr ?_ g rfl
  intro A B hA hB pA pB u hu
  have : u = GeneralLinearGroup.mkOfDetNeZero A hA * GeneralLinearGroup.mkOfDetNeZero B hB :=
    Units.ext hu
  rw [this, map_mul, pA _ rfl, pB _ rfl, one_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantCosetInd
section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace

noncomputable section

namespace GlobalTheory.InvBilinTest

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

local instance (p : Prop) : Decidable p := Classical.propDecidable p


open Classical in
def cosetInd (K : Subgroup G) (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G)) (g : G) :
    SB G := by
  classical
  exact ⟨fun x => if x * g⁻¹ ∈ K then 1 else 0, by
    constructor
    · have h1 : IsOpen {x : G | x * g⁻¹ ∈ K} := ho.preimage (continuous_id.mul continuous_const)
      have h2 : IsClosed {x : G | x * g⁻¹ ∈ K} :=
        (K.isClosed_of_isOpen ho).preimage (continuous_id.mul continuous_const)
      rw [IsLocallyConstant.iff_exists_open]
      intro y
      by_cases hy : y * g⁻¹ ∈ K
      · exact ⟨_, h1, hy, fun x hx => by rw [if_pos hy]; exact if_pos hx⟩
      · exact ⟨_, h2.isOpen_compl, hy, fun x hx => by rw [if_neg hy]; exact if_neg hx⟩
    · refine HasCompactSupport.intro (hK.image (continuous_id.mul (continuous_const (y := g))))
        fun x hx => if_neg fun h => hx ⟨x * g⁻¹, h, by change (x * g⁻¹) * g = x; group⟩⟩


open Classical in
theorem cosetInd_apply (K : Subgroup G) (ho : IsOpen (K : Set G)) (hK : IsCompact (K : Set G))
    (g x : G) : (cosetInd K ho hK g).1 x = if x * g⁻¹ ∈ K then 1 else 0 := rfl

variable [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
  {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V}
  {Y : Type} [AddCommGroup Y] [Module ℂ Y]


open Classical in
theorem _root_.GlobalTheory.InvBilinTest.integral_ite (K : Subgroup G) (ho : IsOpen (K : Set G)) (c : ℂ) :
    ∫ g, (if g ∈ K then c else 0) ∂μ = (μ.real K : ℂ) * c := by
  classical
  have hm : MeasurableSet (K : Set G) := ho.measurableSet
  have h : (fun g : G => if g ∈ K then c else 0) = (K : Set G).indicator (fun _ => c) := by
    ext g
    simp [Set.indicator_apply]
  rw [h, integral_indicator_const c hm, Complex.real_smul]

end GlobalTheory.InvBilinTest
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LinearChangeOfVariablesLocalFieldMatrix
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Kronecker

namespace GlobalTheory.SplitWeil

theorem map_curry_symm_pi_pi {X a b : Type} [MeasurableSpace X] [Fintype a] [Fintype b] (ν : Measure X)
    [SigmaFinite ν] :
    Measure.map (MeasurableEquiv.curry b a X).symm (Measure.pi fun _ : b => Measure.pi fun _ : a => ν) =
      Measure.pi fun _ : b × a => ν := by
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (MeasurableEquiv.curry b a X).symm.measurable (MeasurableSet.univ_pi hs)]
  have hpre : (MeasurableEquiv.curry b a X).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi fun i : b => Set.univ.pi fun j : a => s (i, j) := by
    ext x
    simp [MeasurableEquiv.coe_curry_symm, Prod.forall]
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  (ν : Measure k) [ν.IsAddHaarMeasure]

omit [MeasurableSpace k] [BorelSpace k] in
theorem nabs_pos' (x : kˣ) : 0 < nabs k x := by
  show (0 : ℝ) < ((distribHaarChar k x : NNReal) : ℝ)
  exact NNReal.coe_pos.mpr distribHaarChar_pos

private lemma measurable_mulVec' {ι : Type} [Fintype ι] (M : Matrix ι ι k) : Measurable M.mulVec := by
  have : SecondCountableTopology k := secondCountable k
  exact (Continuous.matrix_mulVec continuous_const continuous_id).measurable

private lemma map_diagonal_mulVec_measure_pi (D : a → k) (u : kˣ) (hu : (u : k) = (Matrix.diagonal D).det) :
    Measure.map (Matrix.diagonal D).mulVec (Measure.pi fun _ : a => ν) =
      distribHaarChar k u⁻¹ • Measure.pi fun _ : a => ν := by
  have : SecondCountableTopology k := secondCountable k
  have hD : ∀ i, D i ≠ 0 := by
    intro i hi
    have h0 : (u : k) ≠ 0 := u.ne_zero
    rw [hu, Matrix.det_diagonal] at h0
    exact h0 (Finset.prod_eq_zero (Finset.mem_univ i) hi)
  let e : a → kˣ := fun i => Units.mk0 (D i) (hD i)
  have hue : u = ∏ i, e i := by
    ext
    rw [hu, Matrix.det_diagonal, Units.coe_prod]
    rfl
  have hm := measurable_mulVec' (Matrix.diagonal D)
  have E : distribHaarChar k u • Measure.map (Matrix.diagonal D).mulVec (Measure.pi fun _ : a => ν) =
      Measure.pi fun _ : a => ν := by
    refine (Measure.pi_eq fun s hs => ?_).symm
    rw [Measure.smul_apply, Measure.map_apply hm (MeasurableSet.univ_pi hs)]
    have hpre : (Matrix.diagonal D).mulVec ⁻¹' Set.univ.pi s =
        Set.univ.pi fun i => (fun x : k => e i • x) ⁻¹' s i := by
      ext x
      simp [Matrix.mulVec_diagonal, Units.smul_def, e]
    rw [hpre, Measure.pi_pi, hue, map_prod, ENNReal.smul_def, smul_eq_mul, ENNReal.ofNNReal_finsetProd,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Set.preimage_smul, ← distribHaarChar_mul ν (e i)⁻¹, ← mul_assoc, ← ENNReal.coe_mul, ← map_mul, mul_inv_cancel,
      map_one, ENNReal.coe_one, one_mul]
  calc Measure.map (Matrix.diagonal D).mulVec (Measure.pi fun _ : a => ν)
      = (distribHaarChar k u⁻¹ * distribHaarChar k u) •
          Measure.map (Matrix.diagonal D).mulVec (Measure.pi fun _ : a => ν) := by
        rw [← map_mul, inv_mul_cancel, map_one, one_smul]
    _ = distribHaarChar k u⁻¹ • Measure.pi fun _ : a => ν := by rw [mul_smul, E]

private lemma map_transvection_mulVec_measure_pi (t : Matrix.TransvectionStruct a k) :
    Measure.map t.toMatrix.mulVec (Measure.pi fun _ : a => ν) = Measure.pi fun _ : a => ν := by
  have : SecondCountableTopology k := secondCountable k
  obtain ⟨i, j, hij, c⟩ := t
  show Measure.map (Matrix.transvection i j c).mulVec (Measure.pi fun _ : a => ν) = Measure.pi fun _ : a => ν
  have hm := measurable_mulVec' (Matrix.transvection i j c)
  have key : ∀ (x : a → k) (y : k), (Matrix.transvection i j c).mulVec (Function.update x i y) =
      Function.update x i (y + c * x j) := by
    intro x y
    ext l
    by_cases hl : l = i
    · subst hl
      simp [Matrix.transvection, Matrix.mulVec, dotProduct, Matrix.single_apply, add_mul,
        Finset.sum_add_distrib, Matrix.one_apply, Function.update_of_ne hij.symm]
    · simp [Matrix.transvection, Matrix.mulVec, dotProduct, Matrix.single_apply, add_mul,
        Finset.sum_add_distrib, Matrix.one_apply, Function.update_of_ne hl, Ne.symm hl]
  refine (Measure.pi_eq fun s hs => ?_).symm
  have hbox : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  have hind : Measurable ((Set.univ.pi s).indicator (1 : (a → k) → ENNReal)) := measurable_one.indicator hbox
  rw [← Measure.pi_pi, ← lintegral_indicator_one hbox, ← lintegral_indicator_one hbox,
    lintegral_map hind hm]
  refine lintegral_eq_of_lmarginal_eq {i} (hind.comp hm) hind ?_
  ext x
  rw [lmarginal_singleton, lmarginal_singleton]
  simp only [Function.comp_apply, key]
  exact lintegral_add_right_eq_self (fun y => (Set.univ.pi s).indicator 1 (Function.update x i y)) (c * x j)

private lemma map_mulVec_measure_pi_eq_distribHaarChar_smul {M : Matrix a a k} (hM : M.det ≠ 0) (u : kˣ) (hu : (u : k) = M.det) :
    Measure.map M.mulVec (Measure.pi fun _ : a => ν) = distribHaarChar k u⁻¹ • Measure.pi fun _ : a => ν := by
  have : SecondCountableTopology k := secondCountable k
  revert u
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M => ∀ u : kˣ, (u : k) = M.det →
      Measure.map M.mulVec (Measure.pi fun _ : a => ν) = distribHaarChar k u⁻¹ • Measure.pi fun _ : a => ν)
    M hM ?_ ?_ ?_
  · intro D _ u hu
    exact map_diagonal_mulVec_measure_pi ν D u hu
  · intro t u hu
    have h1 : u = 1 := Units.ext (by rw [hu, Matrix.TransvectionStruct.det, Units.val_one])
    rw [h1, inv_one, map_one, one_smul, map_transvection_mulVec_measure_pi ν t]
  · intro A B hA hB IA IB u hu
    have hfun : (A * B).mulVec = A.mulVec ∘ B.mulVec := by
      funext x
      simp [Matrix.mulVec_mulVec]
    have hinv : u⁻¹ = (Units.mk0 _ hB)⁻¹ * (Units.mk0 _ hA)⁻¹ := by
      rw [← mul_inv]
      congr 1
      ext
      simp [hu, Matrix.det_mul, mul_comm]
    rw [hfun, ← Measure.map_map (measurable_mulVec' A) (measurable_mulVec' B), IB (Units.mk0 _ hB) rfl,
      Measure.map_smul _ (measurable_mulVec' A).aemeasurable, IA (Units.mk0 _ hA) rfl,
      hinv, map_mul, mul_smul]

private lemma integral_comp_mulVec_eq_nabs_inv_smul {M : Matrix a a k} (hM : M.det ≠ 0) (u : kˣ) (hu : (u : k) = M.det)
    (f : (a → k) → ℂ) :
    ∫ x, f (M.mulVec x) ∂(Measure.pi fun _ : a => ν) =
      ((nabs k u)⁻¹ : ℝ) • ∫ x, f x ∂(Measure.pi fun _ : a => ν) := by
  have : SecondCountableTopology k := secondCountable k
  have hdet : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  let e : (a → k) ≃ᵐ (a → k) :=
    { toFun := M.mulVec
      invFun := M⁻¹.mulVec
      left_inv := fun x => by simp [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet]
      right_inv := fun x => by simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet]
      measurable_toFun := measurable_mulVec' M
      measurable_invFun := measurable_mulVec' M⁻¹ }
  have h1 : ∫ x, f (M.mulVec x) ∂(Measure.pi fun _ : a => ν) =
      ∫ y, f y ∂(Measure.map e (Measure.pi fun _ : a => ν)) := (e.measurableEmbedding.integral_map f).symm
  have h2 : (e : (a → k) → (a → k)) = M.mulVec := rfl
  rw [h1, h2, map_mulVec_measure_pi_eq_distribHaarChar_smul ν hM u hu, integral_smul_nnreal_measure, map_inv, NNReal.smul_def,
    NNReal.coe_inv]
  rfl

theorem integral_comp_mulVec_eq_smul (g : GL a k) (f : (a → k) → ℂ) :
    ∫ x, f (g.val.mulVec x) ∂(Measure.pi fun _ => ν) =
      ((nabs k (Matrix.GeneralLinearGroup.det g))⁻¹ : ℝ) • ∫ x, f x ∂(Measure.pi fun _ => ν) := by
  exact integral_comp_mulVec_eq_nabs_inv_smul ν (Matrix.GeneralLinearGroup.det g).ne_zero _ rfl f

omit [BorelSpace k] [DecidableEq a] [DecidableEq b] in
theorem integral_volM_eq_pi (Φ : Matrix b a k → ℂ) :
    ∫ x, Φ x ∂(volM ν b a) = ∫ y, Φ (Matrix.of (Function.curry y)) ∂(Measure.pi fun _ : b × a => ν) := by
  have : SecondCountableTopology k := secondCountable k
  rw [← map_curry_symm_pi_pi ν, (MeasurableEquiv.curry b a k).symm.measurableEmbedding.integral_map]
  rfl

private lemma mul_of_curry_mul_eq_of_curry_kronecker_mulVec (g : GL a k) (h : GL b k) (y : b × a → k) :
    h.val * Matrix.of (Function.curry y) * g.val =
      Matrix.of (Function.curry ((h.val ⊗ₖ g.valᵀ).mulVec y)) := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.of_apply, Function.curry_apply, Matrix.mulVec, dotProduct,
    Matrix.kroneckerMap_apply, Matrix.transpose_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  ring

theorem integral_comp_mul_mul_volM (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ) :
    ∫ x, Φ (h.val * x * g.val) ∂(volM ν b a) =
      (nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card a : ℝ)) *
        nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card b : ℝ))) • ∫ x, Φ x ∂(volM ν b a) := by
  have hK : (h.val ⊗ₖ g.valᵀ).det ≠ 0 := by
    rw [Matrix.det_kronecker, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ (Matrix.GeneralLinearGroup.det h).ne_zero)
      (pow_ne_zero _ (Matrix.GeneralLinearGroup.det g).ne_zero)
  set u : kˣ := Matrix.GeneralLinearGroup.det h ^ Fintype.card a *
    Matrix.GeneralLinearGroup.det g ^ Fintype.card b with hu_def
  have hu : (u : k) = (h.val ⊗ₖ g.valᵀ).det := by
    rw [Matrix.det_kronecker, Matrix.det_transpose, hu_def, Units.val_mul, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val]
    rfl
  rw [integral_volM_eq_pi ν (fun x => Φ (h.val * x * g.val)), integral_volM_eq_pi ν Φ]
  simp only [mul_of_curry_mul_eq_of_curry_kronecker_mulVec g h]
  rw [integral_comp_mulVec_eq_nabs_inv_smul ν hK u hu (fun y => Φ (Matrix.of (Function.curry y)))]
  congr 1
  have hn : nabs k u = nabs k (Matrix.GeneralLinearGroup.det h) ^ Fintype.card a *
      nabs k (Matrix.GeneralLinearGroup.det g) ^ Fintype.card b := by
    simp only [nabs, hu_def, map_mul, map_pow, NNReal.coe_mul, NNReal.coe_pow]
  rw [hn, mul_inv, Real.rpow_neg (nabs_pos' _).le, Real.rpow_neg (nabs_pos' _).le, Real.rpow_natCast,
    Real.rpow_natCast]

theorem linear_change_of_variables : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (ν : Measure k) [ν.IsAddHaarMeasure], (∀ (g : GL a k) (f : (a → k) → ℂ), ∫ x, f (g.val.mulVec x) ∂(Measure.pi fun _ => ν) = ((nabs k (Matrix.GeneralLinearGroup.det g))⁻¹ : ℝ) • ∫ x, f x ∂(Measure.pi fun _ => ν)) ∧ ∀ (g : GL a k) (h : GL b k) (Φ : Matrix b a k → ℂ), ∫ x, Φ (h.val * x * g.val) ∂(volM ν b a) = (nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(Fintype.card a : ℝ)) * nabs k (Matrix.GeneralLinearGroup.det g) ^ (-(Fintype.card b : ℝ))) • ∫ x, Φ x ∂(volM ν b a) := by
  intro k _ _ _ _ _ _ a b _ _ _ _ ν _
  exact ⟨fun g f => integral_comp_mulVec_eq_smul ν g f, fun g h Φ => integral_comp_mul_mul_volM ν g h Φ⟩

end GlobalTheory.SplitWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyEquivOfSmoothTraceEqAdmissible
section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace

namespace GlobalTheory.CharIndep

theorem exists_smul_eq_self_and_smul_eq_zero {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [IsSimpleModule R M] [IsSimpleModule R N]
    (h1 : ∀ f : M →ₗ[R] N, f = 0) (h2 : ∀ f : N →ₗ[R] M, f = 0) (s : Finset M) (t : Finset N) :
    ∃ r : R, (∀ m ∈ s, r • m = m) ∧ ∀ n ∈ t, r • n = 0 := by
  classical
  let p : Module.End (Module.End R (M × N)) (M × N) :=
    { toFun := fun x => (x.1, 0)
      map_add' := fun x y => by simp
      map_smul' := fun φ x => by
        have a1 : (φ (x.1, 0)).2 = 0 :=
          congr($(h1 (LinearMap.snd R M N ∘ₗ φ ∘ₗ LinearMap.inl R M N)) x.1)
        have a2 : (φ (0, x.2)).1 = 0 :=
          congr($(h2 (LinearMap.fst R M N ∘ₗ φ ∘ₗ LinearMap.inr R M N)) x.2)
        have a3 : φ x = φ (x.1, 0) + φ (0, x.2) := by rw [← map_add (f := _)]; simp
        simp only [Module.End.smul_def, RingHom.id_apply]
        ext
        · simp [a3, a2]
        · simp [a1] }
  have : IsSemisimpleModule R (M × N) := by
    have hs := IsSemisimpleModule.sup (IsSemisimpleModule.range (LinearMap.inl R M N))
      (IsSemisimpleModule.range (LinearMap.inr R M N))
    rw [LinearMap.sup_range_inl_inr] at hs
    exact IsSemisimpleModule.congr Submodule.topEquiv.symm
  obtain ⟨r, hr⟩ := jacobson_density p
    (s.image (fun m => (m, (0 : N))) ∪ t.image (fun n => ((0 : M), n)))
  refine ⟨r, fun m hm => ?_, fun n hn => ?_⟩
  · have := hr (m, 0) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hm))
    exact (congrArg Prod.fst this).symm
  · have := hr (0, n) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hn))
    exact (congrArg Prod.snd this).symm

theorem exists_smoothOp_eq_comp {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    [μ.IsMulLeftInvariant] {f₀ : G → ℂ} (hf : IsLocallyConstant f₀) (hc : HasCompactSupport f₀)
    (a : MonoidAlgebra ℂ G) :
    ∃ f : G → ℂ, IsLocallyConstant f ∧ HasCompactSupport f ∧
      ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), IsSmooth ρ →
        smoothOp ρ μ f = ρ.asAlgebraHom a ∘ₗ smoothOp ρ μ f₀ := by
  induction a using MonoidAlgebra.induction_on with
  | of g =>
    have h1 : IsLocallyConstant fun x => f₀ (g⁻¹ * x) :=
      hf.comp_continuous (continuous_const.mul continuous_id)
    have h2 : HasCompactSupport fun x => f₀ (g⁻¹ * x) :=
      hc.comp_homeomorph (Homeomorph.mulLeft g⁻¹)
    refine ⟨_, h1, h2, fun V _ _ ρ hρ => ?_⟩
    ext v
    refine eq_of_forall_dual fun l => ?_
    rw [hρ.map_smoothOp h1 h2 l, ← integral_mul_left_eq_self _ g]
    simpa using (hρ.map_smoothOp (μ := μ) hf hc (l ∘ₗ ρ g) v).symm
  | add a b ha hb =>
    obtain ⟨f, f1, f2, f3⟩ := ha
    obtain ⟨f', f1', f2', f3'⟩ := hb
    refine ⟨f + f', f1.add f1', f2.add f2', fun V _ _ ρ hρ => ?_⟩
    rw [hρ.smoothOp_add f1 f2 f1' f2', f3 V ρ hρ, f3' V ρ hρ, map_add (f := _), LinearMap.add_comp]
  | smul c a ha =>
    obtain ⟨f, f1, f2, f3⟩ := ha
    refine ⟨c • f, f1.comp (c • ·), f2.comp_left (g := (c • ·)) (smul_zero c),
      fun V _ _ ρ hρ => ?_⟩
    rw [hρ.smoothOp_smul f1 f2, f3 V ρ hρ, map_smul, LinearMap.smul_comp]

theorem exists_asAlgebraHom_eq {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G V) (π' : Representation ℂ G W)
    [π.IsIrreducible] [π'.IsIrreducible] [IsEmpty (π.Equiv π')] (S : Submodule ℂ V)
    (T : Submodule ℂ W) [FiniteDimensional ℂ S] [FiniteDimensional ℂ T] :
    ∃ a : MonoidAlgebra ℂ G, (∀ v ∈ S, π.asAlgebraHom a v = v) ∧
      ∀ w ∈ T, π'.asAlgebraHom a w = 0 := by
  have : IsEmpty (π'.Equiv π) := ⟨fun e => IsEmpty.false (α := π.Equiv π') e.symm⟩
  have s1 := (Representation.IntertwiningMap.equivLinearMapAsModule π π').toEquiv.symm.subsingleton
  have s2 := (Representation.IntertwiningMap.equivLinearMapAsModule π' π).toEquiv.symm.subsingleton
  obtain ⟨s, hs⟩ := (Submodule.fg_iff_finiteDimensional S).2 inferInstance
  obtain ⟨t, ht⟩ := (Submodule.fg_iff_finiteDimensional T).2 inferInstance
  obtain ⟨a, h1, h2⟩ := exists_smul_eq_self_and_smul_eq_zero (R := MonoidAlgebra ℂ G)
    (M := π.asModule) (N := π'.asModule) (fun f => Subsingleton.elim _ _)
    (fun f => Subsingleton.elim _ _) s t
  refine ⟨a, fun v hv => ?_, fun w hw => ?_⟩
  · rw [← hs] at hv
    exact LinearMap.eqOn_span (f := π.asAlgebraHom a) (g := LinearMap.id) (fun x hx => h1 x hx) hv
  · rw [← ht] at hw
    exact LinearMap.eqOn_span (f := π'.asAlgebraHom a) (g := 0) (fun x hx => h2 x hx) hw

theorem nonempty_equiv_of_smoothTrace_eq : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], (∀ U ∈ nhds (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ U) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G V) (π' : Representation ℂ G W), IsAdmissible π → IsAdmissible π' → π.IsIrreducible → π'.IsIrreducible → (∀ f : G → ℂ, IsLocallyConstant f → HasCompactSupport f → smoothTrace π μ f = smoothTrace π' μ f) → Nonempty (π.Equiv π') := by
  intro G _ _ _ _ _ _ μ _ _ hG V _ _ W _ _ π π' hπ hπ' hi hi' htr
  by_contra hne
  have : IsEmpty (π.Equiv π') := not_nonempty_iff.1 hne
  have : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) π.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨K, ho, hK, hKv⟩ := hG _ ((hπ.1 v).mem_nhds (by simp))
  have hvK : v ∈ fixed π K := mem_fixed.2 fun k hk => hKv hk
  have := hπ.2 K ho hK
  have := hπ'.2 K ho hK
  have hf : IsLocallyConstant ((K : Set G).indicator fun _ => (1 : ℂ)) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro g
    by_cases hg : g ∈ (K : Set G)
    · exact ⟨K, ho, hg, fun x hx => by simp only [Set.indicator_of_mem, hx, hg]⟩
    · exact ⟨(K : Set G)ᶜ, (K.isClosed_of_isOpen ho).isOpen_compl, hg, fun x hx => by
        rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hg]⟩
  have hc : HasCompactSupport ((K : Set G).indicator fun _ => (1 : ℂ)) :=
    HasCompactSupport.intro hK fun x hx => Set.indicator_of_notMem hx _
  have hl : ∀ k ∈ K, ∀ g, (K : Set G).indicator (fun _ => (1 : ℂ)) (k * g) =
      (K : Set G).indicator (fun _ => (1 : ℂ)) g := fun k hk g => by
    by_cases hg : g ∈ (K : Set G)
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem (K.mul_mem hk hg)]
    · rw [Set.indicator_of_notMem hg,
        Set.indicator_of_notMem fun h => hg ((K.mul_mem_cancel_left hk).1 h)]
  obtain ⟨a, ha, ha'⟩ := exists_asAlgebraHom_eq π π' (fixed π K) (fixed π' K)
  obtain ⟨f, f1, f2, f3⟩ := exists_smoothOp_eq_comp μ hf hc a
  have e1 : smoothOp π μ f = smoothOp π μ ((K : Set G).indicator fun _ => (1 : ℂ)) := by
    rw [f3 V π hπ.1]
    ext x
    exact ha _ (hπ.1.smoothOp_mem_fixed hf hc hl x)
  have e2 : smoothOp π' μ f = 0 := by
    rw [f3 W π' hπ'.1]
    ext x
    exact ha' _ (hπ'.1.smoothOp_mem_fixed hf hc hl x)
  have e3 := htr f f1 f2
  have e4 := hπ.smoothTrace_indicator (μ := μ) ho hK
  have e5 : smoothTrace π' μ f = 0 := by
    rw [smoothTrace, e2, finRankTrace_eq _ ⊥ (by simp)]
    rw [Subsingleton.elim (LinearMap.restrict _ _) 0, map_zero]
  rw [e5, smoothTrace, e1, ← smoothTrace, e4] at e3
  have : Nontrivial (fixed π K) := ⟨⟨⟨v, hvK⟩, 0, fun h => hv (congrArg Subtype.val h)⟩⟩
  have p1 : 0 < Module.finrank ℂ (fixed π K) := Module.finrank_pos
  have p2 : μ.real K ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨ho.measure_ne_zero μ ⟨1, K.one_mem⟩, hK.measure_ne_top⟩
  exact mul_ne_zero (by exact_mod_cast p2) (by exact_mod_cast p1.ne') e3

end GlobalTheory.CharIndep
end

