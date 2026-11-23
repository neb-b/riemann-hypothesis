module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0135
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0130

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianQuadraticUnitaryLocalComponents
section
noncomputable section

namespace GlobalTheory.GaugeEx

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct NNReal ENNReal

section BaseMap

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']

theorem qloc_trace_tmul [FiniteDimensional F E] (r : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] e) = r * algebraMap F R (Algebra.trace F E e) := by
  have h1 : (r ⊗ₜ[F] e : R ⊗[F] E) = r • ((1 : R) ⊗ₜ[F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, smul_eq_mul]

variable (φ : R →ₐ[F] R') (π : R ⊗[F] E →+* R' ⊗[F] E)
  (hπ : ∀ r e, π (r ⊗ₜ[F] e) = φ r ⊗ₜ[F] e)
include hπ

theorem qloc_trace [FiniteDimensional F E] (z : R ⊗[F] E) :
    Algebra.trace R' (R' ⊗[F] E) (π z) = φ (Algebra.trace R (R ⊗[F] E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => rw [hπ, qloc_trace_tmul, qloc_trace_tmul, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem qloc_sig (σ : E →ₐ[F] E) (z : R ⊗[F] E) : sigR R' σ (π z) = π (sigR R σ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, hπ]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem qloc_incl (e : E) : π (inclR R e) = inclR R' e := by
  simp [inclR, hπ]

theorem qloc_q [FiniteDimensional F E] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (z : Fin M → R ⊗[F] E) : qR R' σ J (fun i => π (z i)) = φ (qR R σ J z) := by
  have h : hR R' σ J (fun i => π (z i)) (fun i => π (z i)) = π (hR R σ J z z) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hR, Formalism.UG.hform, JR, Matrix.map_apply, map_sum, map_mul, qloc_sig φ π hπ,
      qloc_incl φ π hπ]
  rw [qR, qR, h, qloc_trace φ π hπ, map_mul, AlgHom.commutes]

theorem qloc_group (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (g : HA R σ J) :
    ∃ g' : HA R' σ J, (HA.mat R' σ J g').val = (HA.mat R σ J g).val.map π := by
  have hg : Formalism.UG.cT (sigR R σ) (HA.mat R σ J g).val * JR R J * (HA.mat R σ J g).val = JR R J :=
    Subtype.property (p := fun x => x ∈ HR R σ J) g
  have hJ : (JR R J).map π = JR R' J := by
    ext i j
    exact qloc_incl φ π hπ _
  have hc : Formalism.UG.cT (sigR R' σ) ((HA.mat R σ J g).val.map π) =
      (Formalism.UG.cT (sigR R σ) (HA.mat R σ J g).val).map π := by
    ext i j
    exact qloc_sig φ π hπ σ _
  have hm : Formalism.UG.bc π (HA.mat R σ J g) ∈ HR R' σ J := by
    change Formalism.UG.cT (sigR R' σ) ((HA.mat R σ J g).val.map π) * JR R' J *
      ((HA.mat R σ J g).val.map π) = JR R' J
    rw [hc, ← hJ, ← Matrix.map_mul, ← Matrix.map_mul, hg]
  exact ⟨(⟨_, hm⟩ : HR R' σ J), rfl⟩

end BaseMap

theorem qloc_adele_ext {F : Type} [Field F] [NumberField F] (a b : AF F)
    (h1 : fstA F a = fstA F b) (h2 : ∀ v, evalV F v (sndA F a) = evalV F v (sndA F b)) : a = b := by
  refine Prod.ext h1 ?_
  exact FiniteAdeleRing.ext F fun v => h2 v

theorem q_and_unitary_local_components : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), (∀ (z : Fin M → AF F ⊗[F] E) (β : F), qR (AF F) σ J z = algebraMap F (AF F) β ↔ qR (Ainf F) σ J (fun i => prInf (z i)) = algebraMap F (Ainf F) β ∧ ∀ v : HeightOneSpectrum (𝓞 F), qR (Fv F v) σ J (fun i => prV v (z i)) = algebraMap F (Fv F v) β) ∧ ∀ g : HA (AF F) σ J, (∃ gi : HA (Ainf F) σ J, (HA.mat (Ainf F) σ J gi).val = (HA.mat (AF F) σ J g).val.map prInf) ∧ ∀ v : HeightOneSpectrum (𝓞 F), ∃ gv : HA (Fv F v) σ J, (HA.mat (Fv F v) σ J gv).val = (HA.mat (AF F) σ J g).val.map (prV v) := by
  intro F E _ _ _ _ _ σ M J
  have hI : ∀ (r : AF F) (e : E), prInf (r ⊗ₜ[F] e) = fstA F r ⊗ₜ[F] e := fun r e => rfl
  have hV : ∀ v (r : AF F) (e : E),
      prV v (r ⊗ₜ[F] e) = ((evalV F v).comp (sndA F)) r ⊗ₜ[F] e := fun v r e => rfl
  refine ⟨fun z β => ?_, fun g => ⟨qloc_group _ _ hI σ J g, fun v => qloc_group _ _ (hV v) σ J g⟩⟩
  simp only [qloc_q _ _ hI, qloc_q _ _ (hV _)]
  constructor
  · intro h
    rw [h]
    exact ⟨AlgHom.commutes _ _, fun v => AlgHom.commutes _ _⟩
  · rintro ⟨h1, h2⟩
    refine qloc_adele_ext _ _ (by rw [h1, AlgHom.commutes]) fun v => ?_
    rw [AlgHom.commutes, AlgHom.commutes]
    exact h2 v

end GlobalTheory.GaugeEx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HformMulVecRight
section
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal Matrix

namespace GlobalTheory.GaugeEx.GramPair

section Ring

variable {A : Type} [CommRing A] (s : A →+* A) {M N : ℕ} (G : Matrix (Fin M) (Fin M) A)

theorem hform_eq_dot (x y : Fin M → A) :
    Formalism.UG.hform s G x y = (fun i => s (x i)) ⬝ᵥ G *ᵥ y := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_mulVec (P : Matrix (Fin M) (Fin N) A) (x y : Fin N → A) :
    Formalism.UG.hform s G (P *ᵥ x) (P *ᵥ y) = Formalism.UG.hform s (Formalism.UG.cT s P * G * P) x y := by
  have e : (fun i => s ((P *ᵥ x) i)) = (fun i => s (x i)) ᵥ* Formalism.UG.cT s P := by
    funext i
    rw [Formalism.UG.cT, Matrix.vecMul_transpose]
    exact RingHom.map_mulVec _ _ _ i
  rw [hform_eq_dot, hform_eq_dot, e, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]

theorem hform_mulVec_right (P : Matrix (Fin M) (Fin N) A) (x : Fin M → A) (w : Fin N → A) :
    Formalism.UG.hform s G x (P *ᵥ w) = ∑ j, Formalism.UG.hform s G x (fun i => P i j) * w j := by
  simp only [Formalism.UG.hform, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  symm
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_comm

theorem hform_symm (hs : ∀ a, s (s a) = a) (hG : ∀ i j, s (G j i) = G i j) (x y : Fin M → A) :
    Formalism.UG.hform s G y x = s (Formalism.UG.hform s G x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Formalism.UG.hform, map_sum, map_mul, hs]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hG]
  ring

theorem hform_lin (a b c d : A) (x y : Fin M → A) :
    Formalism.UG.hform s G (a • x + b • y) (c • x + d • y) =
      s a * c * Formalism.UG.hform s G x x + s a * d * Formalism.UG.hform s G x y +
        s b * c * Formalism.UG.hform s G y x + s b * d * Formalism.UG.hform s G y y := by
  simp only [Formalism.UG.hform, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, map_add, map_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Ring

section Tens

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R]

theorem conj_conj (h : IsCMExt F E σ) (e : E) : σ (σ e) = e := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sigR_sigR (h : IsCMExt F E σ) (z : R ⊗[F] E) : sigR R σ (sigR R σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul a e =>
    show a ⊗ₜ[F] σ (σ e) = _
    rw [conj_conj σ h]

omit [NumberField F] [NumberField E] in
theorem sigR_alg (r : R) : sigR R σ (algebraMap R (R ⊗[F] E) r) = algebraMap R (R ⊗[F] E) r := by
  show r ⊗ₜ[F] σ 1 = r ⊗ₜ[F] 1
  rw [map_one]

omit [NumberField F] [NumberField E] in
theorem hR_rat {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x z : Fin M → E) :
    hR R σ J (fun i => inclR R (x i)) (fun i => inclR R (z i)) = inclR R (hE σ J x z) := by
  simp [hR, hE, Formalism.UG.hform, sigR, JR, inclR, TensorProduct.tmul_sum]

theorem half_trace (h : IsCMExt F E σ) (k : R) :
    algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E) (algebraMap R (R ⊗[F] E) k) = k := by
  have h2 : Algebra.trace F E 1 = 2 := by
    have := Algebra.trace_algebraMap (R := F) (S := E) 1
    rw [map_one, h.2.2.1] at this
    rw [this]; norm_num
  have h1 : Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] (1 : E)) = algebraMap F R 2 := by
    rw [Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange,
      ← Algebra.trace_apply, h2]
  rw [Algebra.algebraMap_eq_smul_one k, map_smul, Algebra.TensorProduct.one_def, h1, smul_eq_mul,
    mul_left_comm, ← map_mul, show (1 / 2 * 2 : F) = 1 by norm_num, map_one, mul_one]

omit [NumberField F] [NumberField E] in
theorem JR_cT {M N : ℕ} (J : Matrix (Fin M) (Fin M) E) (B : Matrix (Fin M) (Fin N) E) :
    Formalism.UG.cT (sigR R σ) (B.map (inclR (F := F) R)) * JR (F := F) R J * B.map (inclR (F := F) R) =
      JR (F := F) R (Formalism.UG.cT (σ : E →+* E) B * J * B) := by
  rw [JR, JR, Matrix.map_mul, Matrix.map_mul]
  rfl

end Tens

theorem gram_pair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (a : F) (B : Matrix (Fin (M + 1)) (Fin M) E) (J' : Matrix (Fin M) (Fin M) E), StepData σ J x a B J' → Continuous (gram3 R σ J) ∧ ∃ n : R ⊗[F] E → R, Continuous n ∧ n 0 = 0 ∧ ∀ (g : HA R σ J) (y : Fin 1 → Fin (M + 1) → R ⊗[F] E) (y' : Fin 1 → Fin M → R ⊗[F] E) (r r' : R) (t : R ⊗[F] E), g • ratTup (F := F) R x = y → gram3 R σ J ![algebraMap R (R ⊗[F] E) r • y 0, t • y 0 + algebraMap R (R ⊗[F] E) r' • pairOf R σ J B y g y' 1] = (r * r * algebraMap F R a, algebraMap R (R ⊗[F] E) (r * algebraMap F R a) * t, n t + r' * r' * qR R σ J' (y' 0)) := by
  intro F E _ _ _ _ _ σ h R _ _ _ _ _ _ _ _ _ M J x a B J' hS
  obtain ⟨hJ, -, hx, hB, hJ', -⟩ := hS
  have h1 : Continuous (Algebra.trace R (R ⊗[F] E)) :=
    IsModuleTopology.continuous_of_linearMap _
  have h2 := GlobalTheory.AdelicUnitaryTop.continuous_sigR R σ
  have hc : ∀ i j : Fin 2, Continuous fun X : Fin 2 → Fin (M + 1) → R ⊗[F] E =>
      hR R σ J (X i) (X j) := by
    intro i j
    unfold hR Formalism.UG.hform
    fun_prop
  refine ⟨(continuous_const.mul (h1.comp (hc 0 0))).prodMk
    ((hc 0 1).prodMk (continuous_const.mul (h1.comp (hc 1 1)))),
    fun t => algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E)
      (sigR R σ t * t * algebraMap R (R ⊗[F] E) (algebraMap F R a)),
    continuous_const.mul (h1.comp ((h2.mul continuous_id).mul continuous_const)), by simp, ?_⟩
  intro g y y' r r' t hy
  set G : Matrix (Fin (M + 1)) (Fin (M + 1)) (R ⊗[F] E) := (HA.mat R σ J g).1 with hG
  have hk : Formalism.UG.cT (sigR R σ) G * JR R J * G = JR R J := (show HR R σ J from g).2
  have hact : ∀ u v, hR R σ J (G *ᵥ u) (G *ᵥ v) = hR R σ J u v := fun u v => by
    rw [hR, hform_mulVec, hk, hR]
  have hy0 : y 0 = G *ᵥ (fun i => inclR R (x 0 i)) := by rw [← hy]; rfl
  set z := pairOf R σ J B y g y' 1 with hz
  have hz0 : z = G *ᵥ (B.map (inclR (F := F) R) *ᵥ y' 0) := rfl
  have e00 : hR R σ J (y 0) (y 0) = algebraMap R (R ⊗[F] E) (algebraMap F R a) := by
    rw [hy0, hact, hR_rat, hx, ← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes a
  have e01 : hR R σ J (y 0) z = 0 := by
    rw [hy0, hz0, hact, hR, hform_mulVec_right]
    refine Finset.sum_eq_zero fun j _ => ?_
    have := hR_rat σ R J (x 0) (fun i => B i j)
    rw [hB, map_zero] at this
    exact mul_eq_zero_of_left this _
  have hJs : ∀ i j, sigR R σ (JR R J j i) = JR R J i j := by
    intro i j
    show (1 : R) ⊗ₜ[F] σ (J j i) = (1 : R) ⊗ₜ[F] J i j
    rw [hJ.1]
  have e10 : hR R σ J z (y 0) = 0 := by
    rw [hR, hform_symm _ _ (sigR_sigR σ R h) hJs, ← hR, e01, map_zero]
  have e11 : hR R σ J z z = hR R σ J' (y' 0) (y' 0) := by
    rw [hz0, hact, hR, hform_mulVec, JR_cT, ← hJ', hR]
  have lin : ∀ p q u v : R ⊗[F] E, hR R σ J (p • y 0 + q • z) (u • y 0 + v • z) =
      sigR R σ p * u * algebraMap R (R ⊗[F] E) (algebraMap F R a) +
        sigR R σ q * v * hR R σ J' (y' 0) (y' 0) := by
    intro p q u v
    rw [hR, hform_lin, ← hR, ← hR, ← hR, ← hR, e00, e01, e10, e11]
    ring
  have f0 : algebraMap R (R ⊗[F] E) r • y 0 =
      algebraMap R (R ⊗[F] E) r • y 0 + (0 : R ⊗[F] E) • z := by simp
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show qR R σ J (algebraMap R (R ⊗[F] E) r • y 0) = r * r * algebraMap F R a
    rw [qR, f0, lin, sigR_alg, mul_zero, zero_mul, add_zero, ← map_mul, ← map_mul, half_trace σ R h]
  · show hR R σ J (algebraMap R (R ⊗[F] E) r • y 0) (t • y 0 + algebraMap R (R ⊗[F] E) r' • z) =
      algebraMap R (R ⊗[F] E) (r * algebraMap F R a) * t
    rw [f0, lin, sigR_alg, map_zero, map_mul]
    ring
  · show qR R σ J (t • y 0 + algebraMap R (R ⊗[F] E) r' • z) =
      algebraMap F R (1 / 2) * Algebra.trace R (R ⊗[F] E)
      (sigR R σ t * t * algebraMap R (R ⊗[F] E) (algebraMap F R a)) + r' * r' * qR R σ J' (y' 0)
    rw [qR, lin, sigR_alg, ← map_mul, ← Algebra.smul_def (r' * r'), map_add (f := _), map_smul, qR, smul_eq_mul]
    ring

end GlobalTheory.GaugeEx.GramPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointsFinitePlaceTensorProperties
section
noncomputable section

namespace GlobalTheory.GaugeEx.IntBasis

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem ev_int (a : F) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
    algebraMap F (Fv F v) a ∈ v.adicCompletionIntegers F := by
  have h := (algebraMap F (Af F) a).2
  filter_upwards [h] with v hv
  exact hv

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
theorem _root_.GlobalTheory.GaugeEx.IntBasis.ev_int_coord {d : ℕ}
    (b : Module.Basis (Fin d) F E) (e : E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ k, algebraMap F (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (b.repr e k) ∈ v.adicCompletionIntegers F := by
  rw [Filter.eventually_all]
  intro k
  exact RestrictedProduct.eventually _ _ (algebraMap F (FiniteAdeleRing (𝓞 F) F) (b.repr e k))

theorem eq_sum {d : ℕ} (b : Module.Basis (Fin d) F E) (R : Type) [CommRing R] [Algebra F R]
    (y : R ⊗[F] E) :
    y = ∑ i, (Algebra.TensorProduct.basis R b).repr y i ⊗ₜ[F] b i := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis R b).sum_repr y]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

variable {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
variable {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) in
private theorem mem_intV_iff_basis_repr_mem_integers (y : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E) :
    y ∈ _root_.GlobalTheory.GaugeEx.intV b v ↔
      ∀ k, (Algebra.TensorProduct.basis (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) b).repr y k ∈
        v.adicCompletionIntegers F := by
  unfold _root_.GlobalTheory.GaugeEx.intV
  rfl

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
variable {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) in
theorem _root_.GlobalTheory.GaugeEx.IntBasis.tmul_mem {r : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v}
    (hr : r ∈ v.adicCompletionIntegers F) {e : E}
    (he : ∀ k, algebraMap F (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (b.repr e k) ∈ v.adicCompletionIntegers F) :
    r ⊗ₜ[F] e ∈ _root_.GlobalTheory.GaugeEx.intV b v := by
  rw [mem_intV_iff_basis_repr_mem_integers]
  intro k
  rw [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
    smul_eq_mul]
  exact mul_mem hr (he k)

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
variable {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) in
theorem _root_.GlobalTheory.GaugeEx.IntBasis.sum_mem' {ι : Type} (s : Finset ι)
    (f : ι → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E) (hf : ∀ i ∈ s, f i ∈ _root_.GlobalTheory.GaugeEx.intV b v) :
    ∑ i ∈ s, f i ∈ _root_.GlobalTheory.GaugeEx.intV b v := by
  rw [mem_intV_iff_basis_repr_mem_integers]
  intro k
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finsupp.finsetSum_apply]
  exact sum_mem fun i hi => (mem_intV_iff_basis_repr_mem_integers b v (f i)).1 (hf i hi) k

theorem compact_open : IsCompact (intV b v) ∧ IsOpen (intV b v) := by
  let l := (Algebra.TensorProduct.basis (Fv F v) b).equivFun
  have h1 : Continuous l := IsModuleTopology.continuous_of_linearMap l.toLinearMap
  have h2 : Continuous l.symm := by
    haveI : ContinuousAdd (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousAdd (Fv F v) _
    haveI : ContinuousSMul (Fv F v) (Fv F v ⊗[F] E) := IsModuleTopology.toContinuousSMul (Fv F v) _
    exact IsModuleTopology.continuous_of_linearMap l.symm.toLinearMap
  let e : (Fv F v ⊗[F] E) ≃ₜ (Fin d → Fv F v) := ⟨l.toEquiv, h1, h2⟩
  have he : intV b v = e ⁻¹' Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff]
    rfl
  have ho : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have hc : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) := by
    exact isCompact_iff_compactSpace.2 (GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
  rw [he]
  exact ⟨e.isCompact_preimage.2 (isCompact_univ_pi fun _ => hc),
    (isOpen_set_pi Set.finite_univ fun _ _ => ho).preimage e.continuous⟩

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
variable {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) in
private theorem eventually_basis_repr_mem_adicCompletionIntegers {ι : Type} [Finite ι] (e : ι → E) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ i k, algebraMap F (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F w) (b.repr (e i) k) ∈ w.adicCompletionIntegers F :=
  Filter.eventually_all.2 fun i => _root_.GlobalTheory.GaugeEx.IntBasis.ev_int_coord b (e i)

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
variable {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) in
private theorem eq_sum_basis_repr_tmul_basis (y : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E) :
    y = ∑ k, (Algebra.TensorProduct.basis (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) b).repr y k ⊗ₜ[F] b k := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) b).sum_repr y]
  simp only [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
variable {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) in
private theorem zero_mem_intV : (0 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E) ∈ _root_.GlobalTheory.GaugeEx.intV b v := by
  rw [mem_intV_iff_basis_repr_mem_integers]
  intro k
  rw [map_zero, Finsupp.zero_apply]
  exact zero_mem _

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
variable {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) in
private theorem add_mem_intV {y z : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E}
    (hy : y ∈ _root_.GlobalTheory.GaugeEx.intV b v) (hz : z ∈ _root_.GlobalTheory.GaugeEx.intV b v) :
    y + z ∈ _root_.GlobalTheory.GaugeEx.intV b v := by
  rw [mem_intV_iff_basis_repr_mem_integers] at hy hz ⊢
  intro k
  rw [map_add (f := _), Finsupp.add_apply]
  exact add_mem (hy k) (hz k)

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
variable {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) in
private theorem intV_subset_intV_of_basis_repr_integral {d' : ℕ} (b' : Module.Basis (Fin d') F E)
    (h : ∀ i k, algebraMap F (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (b'.repr (b i) k) ∈ v.adicCompletionIntegers F) :
    _root_.GlobalTheory.GaugeEx.intV b v ⊆ _root_.GlobalTheory.GaugeEx.intV b' v := by
  intro y hy
  rw [eq_sum_basis_repr_tmul_basis b v y]
  exact _root_.GlobalTheory.GaugeEx.IntBasis.sum_mem' b' v _ _ fun i _ =>
    _root_.GlobalTheory.GaugeEx.IntBasis.tmul_mem b' v
      ((mem_intV_iff_basis_repr_mem_integers b v y).1 hy i) (h i)

open NumberField IsDedekindDomain MeasureTheory Topology in
open scoped TensorProduct NNReal ENNReal in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] in
variable {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) in
theorem _root_.GlobalTheory.GaugeEx.IntBasis.main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), (∀ v : HeightOneSpectrum (𝓞 F), IsCompact (_root_.GlobalTheory.GaugeEx.intV b v) ∧ IsOpen (_root_.GlobalTheory.GaugeEx.intV b v)) ∧ (∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, (1 : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E) ∈ _root_.GlobalTheory.GaugeEx.intV b v ∧ (∀ y ∈ _root_.GlobalTheory.GaugeEx.intV b v, ∀ z ∈ _root_.GlobalTheory.GaugeEx.intV b v, y * z ∈ _root_.GlobalTheory.GaugeEx.intV b v) ∧ ∀ y ∈ _root_.GlobalTheory.GaugeEx.intV b v, _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) σ y ∈ _root_.GlobalTheory.GaugeEx.intV b v) ∧ (∀ z : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, _root_.GlobalTheory.GaugeEx.prV v z ∈ _root_.GlobalTheory.GaugeEx.intV b v) ∧ ∀ (d' : ℕ) (b' : Module.Basis (Fin d') F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, _root_.GlobalTheory.GaugeEx.intV b v = _root_.GlobalTheory.GaugeEx.intV b' v := by
  intro F E _ _ _ _ _ σ d b
  refine ⟨fun v => ?_, ?_, fun z => ?_, fun d' b' => ?_⟩
  · let φ := (Algebra.TensorProduct.basis (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) b).equivFun
    have hφ : Continuous φ := IsModuleTopology.continuous_of_linearMap φ.toLinearMap
    have hφs : Continuous φ.symm := IsModuleTopology.continuous_of_linearMap φ.symm.toLinearMap
    let h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E ≃ₜ (Fin d → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) :=
      { φ.toEquiv with continuous_toFun := hφ, continuous_invFun := hφs }
    have hS : _root_.GlobalTheory.GaugeEx.intV b v =
        h ⁻¹' Set.univ.pi (fun _ => (v.adicCompletionIntegers F : Set (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v))) := by
      ext y
      rw [mem_intV_iff_basis_repr_mem_integers]
      simp only [Set.mem_preimage, Set.mem_univ_pi]
      rfl
    have hO : IsCompact (v.adicCompletionIntegers F : Set (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) :=
      isCompact_iff_compactSpace.mpr (_root_.GlobalTheory.AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
    rw [hS]
    exact ⟨h.isCompact_preimage.2 (isCompact_univ_pi fun _ => hO),
      (isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_integer _).preimage h.continuous⟩
  · filter_upwards [_root_.GlobalTheory.GaugeEx.IntBasis.ev_int_coord b (1 : E),
      eventually_basis_repr_mem_adicCompletionIntegers b (fun p : Fin d × Fin d => b p.1 * b p.2),
      eventually_basis_repr_mem_adicCompletionIntegers b (fun k => σ (b k))] with v hv1 hv2 hv3
    refine ⟨?_, ?_, ?_⟩
    · rw [Algebra.TensorProduct.one_def]
      exact _root_.GlobalTheory.GaugeEx.IntBasis.tmul_mem b v (one_mem _) hv1
    · intro y hy z hz
      rw [eq_sum_basis_repr_tmul_basis b v y, eq_sum_basis_repr_tmul_basis b v z, Finset.sum_mul_sum]
      refine _root_.GlobalTheory.GaugeEx.IntBasis.sum_mem' b v _ _ fun k _ =>
        _root_.GlobalTheory.GaugeEx.IntBasis.sum_mem' b v _ _ fun l _ => ?_
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact _root_.GlobalTheory.GaugeEx.IntBasis.tmul_mem b v
        (mul_mem ((mem_intV_iff_basis_repr_mem_integers b v y).1 hy k)
          ((mem_intV_iff_basis_repr_mem_integers b v z).1 hz l)) (hv2 (k, l))
    · intro y hy
      set_option synthInstance.maxHeartbeats 100000 in
        rw [eq_sum_basis_repr_tmul_basis b v y, map_sum]
      refine _root_.GlobalTheory.GaugeEx.IntBasis.sum_mem' b v _ _ fun k _ => ?_
      simp only [_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      exact _root_.GlobalTheory.GaugeEx.IntBasis.tmul_mem b v
        ((mem_intV_iff_basis_repr_mem_integers b v y).1 hy k) (hv3 k)
  · induction z using TensorProduct.induction_on with
    | zero =>
      exact Filter.Eventually.of_forall fun v => by
        rw [map_zero]
        exact zero_mem_intV b v
    | tmul a e =>
      filter_upwards [RestrictedProduct.eventually _ _ (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA F a),
        _root_.GlobalTheory.GaugeEx.IntBasis.ev_int_coord b e] with v ha he
      simp only [_root_.GlobalTheory.GaugeEx.prV, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
      exact _root_.GlobalTheory.GaugeEx.IntBasis.tmul_mem b v ha he
    | add x y hx hy =>
      filter_upwards [hx, hy] with v hxv hyv
      rw [map_add (f := _)]
      exact add_mem_intV b v hxv hyv
  · filter_upwards [eventually_basis_repr_mem_adicCompletionIntegers b' (fun k => b k),
      eventually_basis_repr_mem_adicCompletionIntegers b (fun k => b' k)] with v h h'
    exact Set.Subset.antisymm (intV_subset_intV_of_basis_repr_integral b v b' h)
      (intV_subset_intV_of_basis_repr_integral b' v b h')

end GlobalTheory.GaugeEx.IntBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelStepZeroAtTwistPrimeFullStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_stepZero_at_twistPrime_full : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs → cst.Ok → GrpQ (R := R) sel mu cst 0 P 1 ⟨⊤, 1⟩ ∧ ChrQ Ch sel mu cst 0 P 1 ⟨⊤, 1⟩ := by
  first | exact @GlobalTheory.Mem.Col2.IdxExZeroQ.zero_level | exact GlobalTheory.Mem.Col2.IdxExZeroQ.zero_level | (intros; apply GlobalTheory.Mem.Col2.IdxExZeroQ.zero_level <;> assumption)
end

