module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0004
public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.Bundle0002

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.IsCMUnram
section
open NumberField

noncomputable section

namespace HcS.HermitianLatticesTheory

def IsCMUnram (K : Type*) [Field K] [NumberField K] [StarRing K] : Prop :=
  IsTotallyComplex K ∧ (∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a)) ∧
    ∀ P : Ideal (RingOfIntegers K), P.IsMaximal →
      ∃ θ t : RingOfIntegers K, algebraMap (RingOfIntegers K) K t =
        star (algebraMap (RingOfIntegers K) K θ) ∧ θ - t ∉ P

end HcS.HermitianLatticesTheory

namespace HcS.HermitianLatticesTheory

open NumberField

end HcS.HermitianLatticesTheory
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.MpOfIsomProd
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Matrix ComplexConjugate

section Iso

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

theorem mp_of_isom (f : E →ₗ[ℝ] F) (hn : ∀ x, ‖f x‖ = ‖x‖) (hs : Function.Surjective f) :
    MeasurePreserving f volume volume := by
  have hinj : Function.Injective f := by
    intro a b hab
    have h0 : ‖a - b‖ = 0 := by rw [← hn, map_sub, hab, sub_self, norm_zero]
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  let e : E ≃ₗ[ℝ] F := LinearEquiv.ofBijective f ⟨hinj, hs⟩
  let g : E ≃ₗᵢ[ℝ] F := { e with norm_map' := hn }
  exact g.measurePreserving

variable {U V : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem mp_of_isom_prod (f : U × V →ₗ[ℝ] F) (hn : ∀ a b, ‖f (a, b)‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2)
    (hs : Function.Surjective f) : MeasurePreserving f volume volume := by
  let L : WithLp 2 (U × V) ≃ₗ[ℝ] U × V := WithLp.linearEquiv 2 ℝ (U × V)
  have h1 : MeasurePreserving (f.comp L.toLinearMap) volume volume := by
    apply mp_of_isom
    · intro t
      have h := hn (L t).1 (L t).2
      have h2 := WithLp.prod_norm_sq_eq_of_L2 t
      have e : (L t) = ((L t).1, (L t).2) := rfl
      rw [← e] at h
      have h3 : ‖f (L t)‖ ^ 2 = ‖t‖ ^ 2 := by rw [h, h2]; rfl
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h3
    · exact hs.comp L.surjective
  have h2 := WithLp.volume_preserving_toLp U V
  have h3 : (⇑(f.comp L.toLinearMap) ∘ WithLp.toLp 2) = ⇑f := by
    funext x
    rfl
  have h4 := h1.comp h2
  rwa [h3] at h4

end Iso

def reimL {n m : ℕ} : Matrix (Fin n) (Fin m) ℂ →ₗ[ℝ] EuclideanSpace ℝ (Fin n × Fin m × Bool) where
  toFun := reim
  map_add' Y Z := by
    ext p
    rcases p with ⟨i, j, s⟩
    cases s <;> simp [reim]
  map_smul' c Y := by
    ext p
    rcases p with ⟨i, j, s⟩
    cases s <;> simp [reim]

theorem reimL_apply {n m : ℕ} (Y : Matrix (Fin n) (Fin m) ℂ) : reimL Y = reim Y := rfl

theorem norm_reim_sq {n m : ℕ} (Y : Matrix (Fin n) (Fin m) ℂ) :
    ‖reim Y‖ ^ 2 = ∑ i, ∑ j, ‖Y i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  simp only [reim, Fintype.sum_prod_type, Fintype.sum_bool]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring

theorem reim_surj {n m : ℕ} (y : EuclideanSpace ℝ (Fin n × Fin m × Bool)) :
    ∃ Y : Matrix (Fin n) (Fin m) ℂ, reim Y = y := by
  refine ⟨Matrix.of fun i j => ⟨y.ofLp (i, j, true), y.ofLp (i, j, false)⟩, ?_⟩
  ext p
  rcases p with ⟨i, j, s⟩
  cases s <;> simp [reim]

theorem herm_cross {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) (hA : Aᴴ = A) (hB : Bᴴ = B) :
    (∑ i, ∑ j, A i j * conj (B i j)).im = 0 := by
  have hA' : ∀ i j, A j i = conj (A i j) := fun i j => by
    simpa [Matrix.conjTranspose_apply] using (congrFun (congrFun hA j) i).symm
  have hB' : ∀ i j, B j i = conj (B i j) := fun i j => by
    simpa [Matrix.conjTranspose_apply] using (congrFun (congrFun hB j) i).symm
  have hc : conj (∑ i, ∑ j, A i j * conj (B i j)) = ∑ i, ∑ j, A i j * conj (B i j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul, Complex.conj_conj]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hA' j i, hB' j i, Complex.conj_conj]
  exact Complex.conj_eq_iff_im.mp hc

theorem herm_pyth {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) (hA : Aᴴ = A) (hB : Bᴴ = B) :
    ∑ i, ∑ j, ‖(Complex.I • A + B) i j‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 + ∑ i, ∑ j, ‖B i j‖ ^ 2 := by
  have key : ∀ i j, ‖(Complex.I • A + B) i j‖ ^ 2 =
      ‖A i j‖ ^ 2 + ‖B i j‖ ^ 2 - 2 * (A i j * conj (B i j)).im := by
    intro i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.sq_norm,
      Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im]
    ring
  have h0 := herm_cross A B hA hB
  simp only [Complex.im_sum] at h0
  simp only [key, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, h0]
  ring

def psiLp {m : ℕ} {η : Type} [Fintype η] (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ) :
    EuclideanSpace ℝ η × EuclideanSpace ℝ η →ₗ[ℝ] EuclideanSpace ℝ (Fin m × Fin m × Bool) where
  toFun z := reimL (Complex.I • H z.1 + H z.2)
  map_add' a b := by
    show reimL (Complex.I • H (a + b).1 + H (a + b).2) =
      reimL (Complex.I • H a.1 + H a.2) + reimL (Complex.I • H b.1 + H b.2)
    rw [← map_add (f := _)]
    congr 1
    simp only [Prod.fst_add, Prod.snd_add, map_add (f := _), smul_add]
    abel
  map_smul' c z := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, RingHom.id_apply]
    rw [smul_comm Complex.I c, ← smul_add, map_smul]

theorem psiLp_apply {m : ℕ} {η : Type} [Fintype η] (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ)
    (z : EuclideanSpace ℝ η × EuclideanSpace ℝ η) : psiLp H z = reim (Complex.I • H z.1 + H z.2) := rfl

theorem psi_mp {m : ℕ} {η : Type} [Fintype η] (H : EuclideanSpace ℝ η →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ)
    (hH : ∀ t, (H t)ᴴ = H t) (hn : ∀ t, ∑ i, ∑ j, ‖H t i j‖ ^ 2 = ‖t‖ ^ 2)
    (hs : ∀ M : Matrix (Fin m) (Fin m) ℂ, Mᴴ = M → ∃ t, H t = M) :
    MeasurePreserving (psiLp H) volume volume := by
  apply mp_of_isom_prod
  · intro a b
    rw [psiLp_apply, norm_reim_sq, herm_pyth _ _ (hH a) (hH b), hn a, hn b]
  · intro y
    obtain ⟨Y, rfl⟩ := reim_surj y
    set A : Matrix (Fin m) (Fin m) ℂ := (-(Complex.I / 2)) • (Y - Yᴴ) with hAdef
    set B : Matrix (Fin m) (Fin m) ℂ := (1 / 2 : ℂ) • (Y + Yᴴ) with hBdef
    have hA : Aᴴ = A := by
      rw [hAdef, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
        Matrix.conjTranspose_conjTranspose]
      ext i j
      simp [Complex.ext_iff]
      constructor <;> ring
    have hB : Bᴴ = B := by
      rw [hBdef, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
        Matrix.conjTranspose_conjTranspose]
      ext i j
      simp [Complex.ext_iff]
      constructor <;> ring
    obtain ⟨s, hsA⟩ := hs A hA
    obtain ⟨t, htB⟩ := hs B hB
    refine ⟨(s, t), ?_⟩
    rw [psiLp_apply]
    congr 1
    simp only [hsA, htB]
    ext i j
    simp [hAdef, hBdef, Complex.ext_iff]
    constructor <;> ring

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PlaceAll
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Matrix
open scoped ENNReal NNReal

theorem pi_smul_measure {V : Type} [Fintype V] {X : V → Type} [∀ v, MeasurableSpace (X v)]
    (μ : ∀ v, Measure (X v)) [∀ v, SigmaFinite (μ v)] (c : V → ℝ≥0) :
    Measure.pi (fun v => c v • μ v) = (∏ v, (c v : ℝ≥0∞)) • Measure.pi μ := by
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Measure.smul_apply]
  rfl

theorem pi_map_smul {V : Type} [Fintype V] {X Y : V → Type} [∀ v, MeasurableSpace (X v)]
    [∀ v, MeasurableSpace (Y v)] (μ : ∀ v, Measure (X v)) (ν : ∀ v, Measure (Y v)) [∀ v, SigmaFinite (ν v)]
    (f : ∀ v, X v → Y v) (hf : ∀ v, Measurable (f v)) (c : V → ℝ≥0)
    (hc : ∀ v, (μ v).map (f v) = c v • ν v) :
    (Measure.pi μ).map (fun x v => f v (x v)) = (∏ v, (c v : ℝ≥0∞)) • Measure.pi ν := by
  haveI : ∀ v, SigmaFinite (μ v) := fun v =>
    SigmaFinite.of_map (μ v) (hf v).aemeasurable (by rw [hc v]; infer_instance)
  rw [← pi_smul_measure]
  symm
  refine Measure.pi_eq fun s hs => ?_
  have hmeas : Measurable (fun x : ∀ v, X v => fun v => f v (x v)) :=
    Measurable.of_eval fun v => (hf v).comp (measurable_pi_apply v)
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs)]
  have hpre : (fun x : ∀ v, X v => fun v => f v (x v)) ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun v => f v ⁻¹' s v) := by
    ext x
    simp
  rw [hpre, Measure.pi_pi]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [← hc v, Measure.map_apply (hf v) (hs v)]

theorem bij_of_map {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] (μ : Measure E) [μ.IsAddHaarMeasure] (ν : Measure F) [ν.IsAddHaarMeasure]
    (f : E →ₗ[ℝ] F) (c : ℝ≥0∞) (h0 : c ≠ 0) (htop : c ≠ ⊤) (h : μ.map f = c • ν) : Function.Bijective f := by
  have key : ∀ s : Set F, MeasurableSet s → μ ((f : E → F) ⁻¹' s) = c * ν s := by
    intro s hs
    have h1 := congrArg (fun ρ : Measure F => ρ s) h
    simp only [Measure.smul_apply, smul_eq_mul] at h1
    rwa [Measure.map_apply (LinearMap.continuous_of_finiteDimensional f).measurable hs] at h1
  have hsurj : Function.Surjective f := by
    by_contra hns
    have hr : LinearMap.range f ≠ ⊤ := fun hh => hns (LinearMap.range_eq_top.mp hh)
    have h0 : ν (LinearMap.range f : Set F) = 0 := Measure.addHaar_submodule ν _ hr
    have hm : MeasurableSet (LinearMap.range f : Set F) :=
      (Submodule.closed_of_finiteDimensional (LinearMap.range f)).measurableSet
    have h1 := key _ hm
    rw [h0, mul_zero] at h1
    have hpre : (f : E → F) ⁻¹' (LinearMap.range f : Set F) = Set.univ := by
      ext x
      simp
    rw [hpre] at h1
    exact (IsOpen.measure_pos μ isOpen_univ Set.univ_nonempty).ne' h1
  have hdim : Module.finrank ℝ E = Module.finrank ℝ F := by
    set K : Set F := Metric.closedBall 0 1 with hKdef
    have hKc : IsCompact K := isCompact_closedBall 0 1
    have hKm : MeasurableSet K := hKc.isClosed.measurableSet
    have hK0 : ν K ≠ 0 := (Metric.measure_closedBall_pos ν (0 : F) one_pos).ne'
    have hKt : ν K ≠ ⊤ := hKc.measure_lt_top.ne
    open Pointwise in
    have h2m : MeasurableSet ((2 : ℝ) • K) := (hKc.smul (2 : ℝ)).isClosed.measurableSet
    open Pointwise in
    have hpre : (f : E → F) ⁻¹' ((2 : ℝ) • K) = (2 : ℝ) • ((f : E → F) ⁻¹' K) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_smul_set]
      constructor
      · rintro ⟨y, hy, hxy⟩
        refine ⟨(1 / 2 : ℝ) • x, ?_, ?_⟩
        · rw [map_smul, ← hxy, smul_smul]
          norm_num
          exact hy
        · rw [smul_smul]
          norm_num
      · rintro ⟨y, hy, rfl⟩
        exact ⟨f y, hy, (map_smul f (2 : ℝ) y).symm⟩
    have e1 := key _ h2m
    rw [hpre, Measure.addHaar_smul, key K hKm, Measure.addHaar_smul] at e1
    set X := c * ν K with hX
    have hX0 : X ≠ 0 := mul_ne_zero h0 hK0
    have hXt : X ≠ ⊤ := ENNReal.mul_ne_top htop hKt
    have e2 : ENNReal.ofReal |(2 : ℝ) ^ Module.finrank ℝ E| * X =
        ENNReal.ofReal |(2 : ℝ) ^ Module.finrank ℝ F| * X := by
      rw [e1, hX]
      ring
    have hu : IsUnit X := isUnit_iff_exists_inv.mpr ⟨X⁻¹, ENNReal.mul_inv_cancel hX0 hXt⟩
    have e3 := hu.mul_left_inj.mp e2
    rw [ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)] at e3
    have e4 : (2 : ℕ) ^ Module.finrank ℝ E = 2 ^ Module.finrank ℝ F := by
      have e5 : ((2 : ℕ) : ℝ) ^ Module.finrank ℝ E = ((2 : ℕ) : ℝ) ^ Module.finrank ℝ F := by
        simpa using e3
      exact_mod_cast e5
    exact Nat.pow_right_injective (le_refl 2) e4
  exact ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj, hsurj⟩

theorem norm_reimE_sq {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℂ) :
    ‖reimE (r := a) (m := b) M‖ ^ 2 = ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool, Complex.sq_norm, Complex.normSq_apply]
  simp [reimE, reim, Real.norm_eq_abs, sq_abs, sq]


set_option maxHeartbeats 800000 in
theorem place_split {V : Type} [Fintype V] {a b : ℕ} {ι : Type} [Fintype ι]
    (L : EuclideanSpace ℝ ι →ₗ[ℝ] (V → Matrix (Fin a) (Fin b) ℂ)) (Q : V → Matrix (Fin a) (Fin b) ℂ → Prop)
    (hQ : ∀ x v, Q v (L x v)) (hQ0 : ∀ v, Q v 0)
    (hn : ∀ x, ∑ v, ∑ i, ∑ j, ‖L x v i j‖ ^ 2 = ‖x‖ ^ 2)
    (hs : ∀ M : V → Matrix (Fin a) (Fin b) ℂ, (∀ v, Q v (M v)) → ∃ x, L x = M) :
    ∃ (κ : V → Type) (_ : ∀ v, Fintype (κ v)) (Lv : ∀ v, EuclideanSpace ℝ (κ v) →ₗ[ℝ] Matrix (Fin a) (Fin b) ℂ)
      (T : EuclideanSpace ℝ ι →ₗ[ℝ] ∀ v, EuclideanSpace ℝ (κ v)),
      (∀ v y, Q v (Lv v y)) ∧ (∀ v y, ∑ i, ∑ j, ‖Lv v y i j‖ ^ 2 = ‖y‖ ^ 2) ∧
      (∀ v M, Q v M → ∃ y, Lv v y = M) ∧ (∀ x v, Lv v (T x v) = L x v) ∧ Function.Bijective T ∧
      (∀ x, ∑ v, ‖T x v‖ ^ 2 = ‖x‖ ^ 2) := by
  classical
  let R : Matrix (Fin a) (Fin b) ℂ ≃ₗ[ℝ] EuclideanSpace ℝ (Fin a × Fin b × Bool) := reimE (r := a) (m := b)
  have hRn : ∀ M : Matrix (Fin a) (Fin b) ℂ, ‖R M‖ ^ 2 = ∑ i, ∑ j, ‖M i j‖ ^ 2 := fun M => norm_reimE_sq M
  let S : V → Submodule ℝ (EuclideanSpace ℝ (Fin a × Fin b × Bool)) := fun v =>
    LinearMap.range (R.toLinearMap ∘ₗ (LinearMap.proj v ∘ₗ L))
  have hmem : ∀ v (M : Matrix (Fin a) (Fin b) ℂ), R M ∈ S v ↔ Q v M := by
    intro v M
    constructor
    · intro hM
      obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hM
      have hx' : R (L x v) = R M := by simpa using hx
      rw [← R.injective hx']
      exact hQ x v
    · intro hq
      obtain ⟨x, hx⟩ := hs (Pi.single v M) (fun w => by
        by_cases hw : w = v
        · subst hw
          rw [Pi.single_eq_same]
          exact hq
        · rw [Pi.single_eq_of_ne hw]
          exact hQ0 w)
      refine LinearMap.mem_range.mpr ⟨x, ?_⟩
      simp [hx]
  let n : V → ℕ := fun v => Module.finrank ℝ (S v)
  let B : ∀ v, OrthonormalBasis (Fin (n v)) ℝ (S v) := fun v => stdOrthonormalBasis ℝ (S v)
  let Lv : ∀ v, EuclideanSpace ℝ (Fin (n v)) →ₗ[ℝ] Matrix (Fin a) (Fin b) ℂ := fun v =>
    R.symm.toLinearMap ∘ₗ (S v).subtype ∘ₗ (B v).repr.symm.toLinearEquiv.toLinearMap
  have hLv_apply : ∀ v y, R (Lv v y) = ((B v).repr.symm y : EuclideanSpace ℝ (Fin a × Fin b × Bool)) := by
    intro v y
    simp [Lv]
  have hLv_norm : ∀ v y, ∑ i, ∑ j, ‖Lv v y i j‖ ^ 2 = ‖y‖ ^ 2 := by
    intro v y
    rw [← hRn, hLv_apply]
    exact congrArg (fun t => t ^ 2) ((B v).repr.symm.norm_map y)
  have hLvQ : ∀ v y, Q v (Lv v y) := by
    intro v y
    refine (hmem v _).mp ?_
    rw [hLv_apply]
    exact ((B v).repr.symm y).2
  have hLvSurj : ∀ v M, Q v M → ∃ y, Lv v y = M := by
    intro v M hq
    refine ⟨(B v).repr ⟨R M, (hmem v M).mpr hq⟩, ?_⟩
    apply R.injective
    rw [hLv_apply, LinearIsometryEquiv.symm_apply_apply]
  have hLvinj : ∀ v, Function.Injective (Lv v) := by
    intro v
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h1 := hLv_norm v y
    rw [hy] at h1
    have h2 : ‖y‖ ^ 2 = 0 := by
      rw [← h1]
      simp
    exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)
  have hLinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h1 := hn y
    rw [hy] at h1
    have h2 : ‖y‖ ^ 2 = 0 := by
      rw [← h1]
      simp
    exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h2)
  let Tv : ∀ v, EuclideanSpace ℝ ι →ₗ[ℝ] S v := fun v =>
    LinearMap.codRestrict (S v) (R.toLinearMap ∘ₗ (LinearMap.proj v ∘ₗ L))
      (fun x => LinearMap.mem_range_self _ x)
  let T : EuclideanSpace ℝ ι →ₗ[ℝ] ∀ v, EuclideanSpace ℝ (Fin (n v)) :=
    LinearMap.pi fun v => (B v).repr.toLinearEquiv.toLinearMap ∘ₗ Tv v
  have hTL : ∀ x v, Lv v (T x v) = L x v := by
    intro x v
    apply R.injective
    rw [hLv_apply]
    simp [T, Tv]
  have hTinj : Function.Injective T := by
    intro x x' hxx
    apply hLinj
    funext v
    rw [← hTL x v, ← hTL x' v, hxx]
  have hTsurj : Function.Surjective T := by
    intro y
    obtain ⟨x, hx⟩ := hs (fun v => Lv v (y v)) (fun v => hLvQ v (y v))
    refine ⟨x, ?_⟩
    funext v
    apply hLvinj v
    rw [hTL, hx]
  have hTnorm : ∀ x, ∑ v, ‖T x v‖ ^ 2 = ‖x‖ ^ 2 := by
    intro x
    rw [← hn x]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← hLv_norm v (T x v), hTL]
  exact ⟨fun v => Fin (n v), fun v => inferInstance, Lv, T, hLvQ, hLv_norm, hLvSurj, hTL, ⟨hTinj, hTsurj⟩, hTnorm⟩

end PI.AprimeInfW
end
end

