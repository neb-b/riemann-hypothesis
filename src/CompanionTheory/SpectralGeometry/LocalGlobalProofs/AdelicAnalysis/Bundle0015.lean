module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0010
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0007

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsSizeMulLe
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.SizeScale

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}

theorem continuous_size (b : Module.Basis (Fin d) F E) :
    Continuous (sizeInf b : Ainf F ⊗[F] E → ℝ) := by
  have : IsModuleTopology (Ainf F) (Ainf F ⊗[F] E) := ⟨rfl⟩
  unfold sizeInf
  refine continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun v _ => ?_
  have hk : Continuous fun y : Ainf F ⊗[F] E =>
      (Algebra.TensorProduct.basis (Ainf F) b).coord k y :=
    IsModuleTopology.continuous_of_linearMap _
  simp only [← Module.Basis.coord_apply]
  exact continuous_norm.comp ((continuous_apply v).comp hk)

theorem size_nonneg (b : Module.Basis (Fin d) F E) (y : Ainf F ⊗[F] E) : 0 ≤ sizeInf b y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem tup_nonneg {M n : ℕ} (b : Module.Basis (Fin d) F E) (X : Fin n → Fin M → Ainf F ⊗[F] E) :
    0 ≤ sizeTup b X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => size_nonneg b _

theorem size_add_le (b : Module.Basis (Fin d) F E) (x y : Ainf F ⊗[F] E) :
    sizeInf b (x + y) ≤ sizeInf b x + sizeInf b y := by
  unfold sizeInf
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun v _ => ?_
  rw [map_add (f := _)]
  exact norm_add_le _ _

theorem size_zero (b : Module.Basis (Fin d) F E) : sizeInf b (0 : Ainf F ⊗[F] E) = 0 := by
  unfold sizeInf
  refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun v _ => ?_
  have h0 : ((0 : Fin d →₀ Ainf F) k) v = 0 := rfl
  rw [map_zero, h0, norm_zero]

theorem size_sum_le {ι : Type} (b : Module.Basis (Fin d) F E) (s : Finset ι)
    (f : ι → Ainf F ⊗[F] E) : sizeInf b (∑ c ∈ s, f c) ≤ ∑ c ∈ s, sizeInf b (f c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [size_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (size_add_le b _ _).trans (by gcongr)

theorem coord_le_size (b : Module.Basis (Fin d) F E) (y : Ainf F ⊗[F] E) (j : Fin d)
    (v : InfinitePlace F) :
    ‖(Algebra.TensorProduct.basis (Ainf F) b).repr y j v‖ ≤ sizeInf b y := by
  unfold sizeInf
  calc ‖(Algebra.TensorProduct.basis (Ainf F) b).repr y j v‖
      ≤ ∑ w, ‖(Algebra.TensorProduct.basis (Ainf F) b).repr y j w‖ :=
        Finset.single_le_sum
          (f := fun w => ‖(Algebra.TensorProduct.basis (Ainf F) b).repr y j w‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_univ v)
    _ ≤ _ := Finset.single_le_sum
        (f := fun k => ∑ w, ‖(Algebra.TensorProduct.basis (Ainf F) b).repr y k w‖)
        (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ j)

theorem repr_mul (b : Module.Basis (Fin d) F E) (x y : Ainf F ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Ainf F) b).repr (x * y) k =
      ∑ i, ∑ j, (Algebra.TensorProduct.basis (Ainf F) b).repr x i *
        (Algebra.TensorProduct.basis (Ainf F) b).repr y j *
          algebraMap F (Ainf F) (b.repr (b i * b j) k) := by
  set B := Algebra.TensorProduct.basis (Ainf F) b with hB
  have hBB : ∀ i j, B.repr (B i * B j) k = algebraMap F (Ainf F) (b.repr (b i * b j) k) := by
    intro i j
    simp [hB, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.basis_repr_tmul]
  conv_lhs => rw [← B.sum_repr x, ← B.sum_repr y, Finset.sum_mul_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, smul_mul_smul_comm, map_smul,
    Finsupp.smul_apply, hBB, smul_eq_mul]

theorem exists_size_mul_le (b : Module.Basis (Fin d) F E) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x y : Ainf F ⊗[F] E, sizeInf b (x * y) ≤ K * sizeInf b x * sizeInf b y := by
  obtain ⟨S₀, hS₀⟩ := (Set.finite_range (fun p : Fin d × Fin d × Fin d × InfinitePlace F =>
    ‖(algebraMap F (Ainf F) (b.repr (b p.1 * b p.2.1) p.2.2.1)) p.2.2.2‖)).bddAbove
  set S := |S₀| with hS
  have hS0 : 0 ≤ S := abs_nonneg _
  have hs : ∀ i j k v, ‖(algebraMap F (Ainf F) (b.repr (b i * b j) k)) v‖ ≤ S := fun i j k v =>
    (hS₀ ⟨(i, j, k, v), rfl⟩).trans (le_abs_self _)
  refine ⟨(d : ℝ) * d * S, by positivity, fun x y => ?_⟩
  set B := Algebra.TensorProduct.basis (Ainf F) b with hB
  have hpt : ∀ k (v : InfinitePlace F), ‖B.repr (x * y) k v‖ ≤
      (d : ℝ) * S * sizeInf b y * ∑ i, ‖B.repr x i v‖ := by
    intro k v
    have hev : B.repr (x * y) k v =
        ∑ i, ∑ j, B.repr x i v * B.repr y j v * (algebraMap F (Ainf F) (b.repr (b i * b j) k)) v := by
      rw [repr_mul b x y k]
      have := map_sum (Pi.evalRingHom (fun w : InfinitePlace F => w.Completion) v)
        (fun i => ∑ j, B.repr x i * B.repr y j * algebraMap F (Ainf F) (b.repr (b i * b j) k))
        Finset.univ
      refine this.trans (Finset.sum_congr rfl fun i _ => ?_)
      exact map_sum (Pi.evalRingHom (fun w : InfinitePlace F => w.Completion) v) _ _
    rw [hev]
    calc ‖∑ i, ∑ j, B.repr x i v * B.repr y j v * (algebraMap F (Ainf F) (b.repr (b i * b j) k)) v‖
        ≤ ∑ i, ∑ j : Fin d, ‖B.repr x i v‖ * sizeInf b y * S := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          rw [norm_mul, norm_mul]
          exact mul_le_mul (mul_le_mul_of_nonneg_left (coord_le_size b y j v) (norm_nonneg _))
            (hs i j k v) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (size_nonneg b y))
      _ = (d : ℝ) * S * sizeInf b y * ∑ i, ‖B.repr x i v‖ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
  calc sizeInf b (x * y) = ∑ k, ∑ v : InfinitePlace F, ‖B.repr (x * y) k v‖ := rfl
    _ ≤ ∑ k : Fin d, ∑ v : InfinitePlace F, (d : ℝ) * S * sizeInf b y * ∑ i, ‖B.repr x i v‖ :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun v _ => hpt k v
    _ = (d : ℝ) * ((d : ℝ) * S * sizeInf b y * ∑ v : InfinitePlace F, ∑ i, ‖B.repr x i v‖) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Finset.mul_sum]
    _ = (d : ℝ) * d * S * sizeInf b x * sizeInf b y := by
        have : sizeInf b x = ∑ v : InfinitePlace F, ∑ i, ‖B.repr x i v‖ := Finset.sum_comm
        rw [this]; ring

end

theorem size_rmul_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ (n M : ℕ) (C : Set (Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))), IsCompact C → ∃ c : ℝ, 0 < c ∧ ∀ g ∈ C, ∀ X : Fin n → Fin M → Ainf F ⊗[F] E, sizeTup b (rmul (Ainf F) X g) ≤ c * sizeTup b X := by
  intro F E _ _ _ _ _ σ _ d b n M C hC
  obtain ⟨K, hK0, hK⟩ := exists_size_mul_le b
  have hcont : Continuous fun g : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) =>
      ∑ c, ∑ a, sizeInf b (g c a) :=
    continuous_finsetSum _ fun c _ => continuous_finsetSum _ fun a _ =>
      (continuous_size b).comp (continuous_id.matrix_elem c a)
  obtain ⟨D, hD⟩ := (hC.image hcont).bddAbove
  refine ⟨K * |D| + 1, by positivity, fun g hg X => ?_⟩
  have hg' : ∀ c, ∑ a, sizeInf b (g c a) ≤ |D| := fun c =>
    (Finset.single_le_sum (f := fun c => ∑ a, sizeInf b (g c a))
      (fun _ _ => Finset.sum_nonneg fun _ _ => size_nonneg b _) (Finset.mem_univ c)).trans
      ((hD ⟨g, hg, rfl⟩).trans (le_abs_self _))
  calc sizeTup b (rmul (Ainf F) X g)
      = ∑ a, ∑ i, sizeInf b (∑ c, X c i * g c a) := rfl
    _ ≤ ∑ a, ∑ i, ∑ c, K * sizeInf b (X c i) * sizeInf b (g c a) :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun i _ =>
          (size_sum_le b _ _).trans (Finset.sum_le_sum fun c _ => hK _ _)
    _ = ∑ i, ∑ c, K * sizeInf b (X c i) * ∑ a, sizeInf b (g c a) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun c _ => (Finset.mul_sum _ _ _).symm
    _ ≤ ∑ i, ∑ c, K * sizeInf b (X c i) * |D| :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun c _ =>
          mul_le_mul_of_nonneg_left (hg' c) (mul_nonneg hK0 (size_nonneg b _))
    _ = K * |D| * sizeTup b X := by
        unfold sizeTup
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ (K * |D| + 1) * sizeTup b X := by
        nlinarith [tup_nonneg b X]

end GlobalTheory.CompanionTheory.SW.SizeScale
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsTraceFormGramMatrixInBasis
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.TraceCoord

section Abstract

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {d M : ℕ}

def coord (β : Module.Basis (Fin d) R A) (x : Fin M → A) : Fin M × Fin d → R :=
  fun p => β.repr (x p.1) p.2

def gramB (s : A →+* A) (β : Module.Basis (Fin d) R A) (J : Matrix (Fin M) (Fin M) A) :
    Matrix (Fin M × Fin d) (Fin M × Fin d) R :=
  fun p q => Algebra.trace R A (s (β p.2) * J p.1 q.1 * β q.2)

theorem trace_hform (s : A →+* A) (hs : ∀ (r : R) (a : A), s (r • a) = r • s a)
    (β : Module.Basis (Fin d) R A) (J : Matrix (Fin M) (Fin M) A) (x y : Fin M → A) :
    Algebra.trace R A (hform s J x y) = coord β x ⬝ᵥ (gramB s β J *ᵥ coord β y) := by
  have hx : ∀ i, s (x i) = ∑ k, β.repr (x i) k • s (β k) := by
    intro i
    calc s (x i) = s (∑ k, β.repr (x i) k • β k) := by rw [β.sum_repr]
      _ = ∑ k, β.repr (x i) k • s (β k) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        exact Finset.sum_congr rfl fun k _ => hs _ _
  have hy : ∀ j, y j = ∑ l, β.repr (y j) l • β l := fun j => (β.sum_repr (y j)).symm
  have term : ∀ i j, Algebra.trace R A (s (x i) * J i j * y j) =
      ∑ k, ∑ l, β.repr (x i) k *
        (Algebra.trace R A (s (β k) * J i j * β l) * β.repr (y j) l) := by
    intro i j
    rw [hx i]
    conv_lhs => rw [hy j]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_mul, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    ring
  unfold hform coord gramB dotProduct Matrix.mulVec dotProduct
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, term, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Finset.sum_comm

theorem coord_mulVec (β : Module.Basis (Fin d) R A) (H : Matrix (Fin M) (Fin M) A)
    (g : Matrix (Fin M × Fin d) (Fin M × Fin d) R)
    (hg : ∀ p q, g p q = β.repr (H p.1 q.1 * β q.2) p.2) (x : Fin M → A) :
    coord β (H *ᵥ x) = g *ᵥ coord β x := by
  funext p
  have hterm : ∀ j, H p.1 j * x j = ∑ l, β.repr (x j) l • (H p.1 j * β l) := by
    intro j
    conv_lhs => rw [← β.sum_repr (x j)]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => mul_smul_comm _ _ _
  simp only [coord, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, hg]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hterm, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem coord_surj (β : Module.Basis (Fin d) R A) (u : Fin M × Fin d → R) :
    ∃ x : Fin M → A, coord β x = u := by
  refine ⟨fun i => ∑ k, u (i, k) • β k, ?_⟩
  funext p
  change β.repr (∑ k, u (p.1, k) • β k) p.2 = u p
  rw [Module.Basis.repr_sum_self]

theorem hform_eq (s : A →+* A) (J : Matrix (Fin M) (Fin M) A) (x y : Fin M → A) :
    hform s J x y = (s ∘ x) ⬝ᵥ (J *ᵥ y) := by
  simp only [hform, dotProduct, Matrix.mulVec, Function.comp, Finset.mul_sum, mul_assoc]

theorem dot_mulVec_left {n : Type} [Fintype n] (P : Matrix n n R) (u w : n → R) :
    (P *ᵥ u) ⬝ᵥ w = u ⬝ᵥ (Pᵀ *ᵥ w) := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem hform_mulVec (s : A →+* A) (J H : Matrix (Fin M) (Fin M) A)
    (hH : cT s H * J * H = J) (x y : Fin M → A) :
    hform s J (H *ᵥ x) (H *ᵥ y) = hform s J x y := by
  have h1 : s ∘ (H *ᵥ x) = (H.map s) *ᵥ (s ∘ x) := by
    funext i
    exact RingHom.map_mulVec s H x i
  have h2 : (H.map s)ᵀ * J * H = J := hH
  rw [hform_eq, hform_eq, h1, dot_mulVec_left, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h2]

theorem mat_ext {n : Type} [Fintype n] [DecidableEq n] (P Q : Matrix n n R)
    (h : ∀ u v : n → R, u ⬝ᵥ (P *ᵥ v) = u ⬝ᵥ (Q *ᵥ v)) : P = Q := by
  ext p q
  simpa using h (Pi.single p 1) (Pi.single q 1)

end Abstract

section Concrete

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem sigR_smul (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (r : R) (a : R ⊗[F] E) :
    sigR R σ (r • a) = r • sigR R σ a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [sigR, TensorProduct.smul_tmul']
  | add a c ha hc => simp only [smul_add, map_add (f := _), ha, hc]

theorem trace_one_tmul (R : Type) [CommRing R] [Algebra F R] [Module.Finite F E] (e : E) :
    Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) = algebraMap F R (Algebra.trace F E e) := by
  have h : Algebra.lmul R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) =
      LinearMap.baseChange R (Algebra.lmul F E e) := by
    ext y
    simp
  rw [Algebra.trace_apply, Algebra.trace_apply, h]
  exact LinearMap.trace_baseChange _ _

theorem gramB_tensor (R : Type) [CommRing R] [Algebra F R] [Module.Finite F E] {d M : ℕ}
    (σ : E →ₐ[F] E) (b : Module.Basis (Fin d) F E) (J : Matrix (Fin M) (Fin M) E) :
    gramB (sigR R σ) (Algebra.TensorProduct.basis R b) (JR R J) =
      (gramB (σ : E →+* E) b J).map (algebraMap F R) := by
  ext p q
  have h : sigR R σ ((1 : R) ⊗ₜ[F] b p.2) * inclR R (J p.1 q.1) * ((1 : R) ⊗ₜ[F] b q.2) =
      (1 : R) ⊗ₜ[F] (σ (b p.2) * J p.1 q.1 * b q.2) := by
    simp [sigR, inclR]
  simp only [gramB, Matrix.map_apply, Algebra.TensorProduct.basis_apply, JR]
  rw [h, trace_one_tmul]
  rfl

end Concrete

section Number

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sig_smul (σ : E →ₐ[F] E) (r : F) (a : E) :
    (σ : E →+* E) (r • a) = r • (σ : E →+* E) a := by
  simp only [Algebra.smul_def]
  rw [map_mul]
  congr 1
  exact σ.commutes r

theorem sig_sig (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hσ.2.2.2, hσ.2.2.2, star_star]

theorem gramB_symm (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {M d : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (b : Module.Basis (Fin d) F E) :
    (gramB (σ : E →+* E) b J).IsSymm := by
  haveI : Module.Finite F E := Module.Finite.of_basis b
  ext p q
  let e : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  change Algebra.trace F E (σ (b q.2) * J q.1 p.1 * b p.2) =
    Algebra.trace F E (σ (b p.2) * J p.1 q.1 * b q.2)
  rw [← Algebra.trace_eq_of_algEquiv e (σ (b q.2) * J q.1 p.1 * b p.2)]
  congr 1
  change σ (σ (b q.2) * J q.1 p.1 * b p.2) = _
  rw [map_mul, map_mul, sig_sig σ hσ, hJ.1 p.1 q.1]
  ring

theorem gramB_det (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {M d : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (b : Module.Basis (Fin d) F E) :
    (gramB (σ : E →+* E) b J).det ≠ 0 := by
  haveI : Module.Finite F E := Module.Finite.of_basis b
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  obtain ⟨y, rfl⟩ := coord_surj (M := M) b v
  have hz : J *ᵥ y = 0 := by
    funext i
    refine (traceForm_nondegenerate F E).1 _ fun a => ?_
    have h1 := trace_hform (σ : E →+* E) (sig_smul σ) b J (Pi.single i (σ a)) y
    rw [hv, dotProduct_zero, hform_eq] at h1
    have h2 : ((σ : E →+* E) ∘ (Pi.single i (σ a) : Fin M → E)) ⬝ᵥ (J *ᵥ y) = a * (J *ᵥ y) i := by
      have h3 : ((σ : E →+* E) ∘ (Pi.single i (σ a) : Fin M → E)) = Pi.single i a := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp [sig_sig σ hσ]
        · simp [Pi.single_eq_of_ne hj]
      rw [h3, single_dotProduct]
    rw [h2] at h1
    rw [Algebra.traceForm_apply, mul_comm]
    exact h1
  have hy : y = 0 := Matrix.eq_zero_of_mulVec_eq_zero hJ.2 hz
  apply hv0
  funext p
  simp [hy, coord]

end Number

theorem exists_trace_coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ B : Matrix (Fin M × Fin d) (Fin M × Fin d) F, B.IsSymm ∧ B.det ≠ 0 ∧ (∀ x : Fin M → E, Algebra.trace F E (hE σ J x x) = (fun p : Fin M × Fin d => b.repr (x p.1) p.2) ⬝ᵥ (B *ᵥ fun p : Fin M × Fin d => b.repr (x p.1) p.2)) ∧ ∀ (R : Type) [CommRing R] [Algebra F R], (∀ x y : Fin M → R ⊗[F] E, Algebra.trace R (R ⊗[F] E) (hR R σ J x y) = (fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2) ⬝ᵥ (B.map (algebraMap F R) *ᵥ fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (y p.1) p.2)) ∧ ∀ h : HA R σ J, ∀ g : Matrix (Fin M × Fin d) (Fin M × Fin d) R, (∀ p q, g p q = (Algebra.TensorProduct.basis R b).repr ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) p.1 q.1 * inclR R (b q.2)) p.2) → gᵀ * B.map (algebraMap F R) * g = B.map (algebraMap F R) ∧ ∀ x : Fin M → R ⊗[F] E, (fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x) p.1) p.2) = g *ᵥ fun p : Fin M × Fin d => (Algebra.TensorProduct.basis R b).repr (x p.1) p.2 := by
  intro F E _ _ _ _ _ σ hσ M J hJ d b
  haveI : Module.Finite F E := Module.Finite.of_basis b
  refine ⟨gramB (σ : E →+* E) b J, gramB_symm σ hσ J hJ b, gramB_det σ hσ J hJ b, fun x => ?_,
    fun R _ _ => ?_⟩
  · exact trace_hform (σ : E →+* E) (sig_smul σ) b J x x
  · have key : ∀ x y : Fin M → R ⊗[F] E, Algebra.trace R (R ⊗[F] E) (hR R σ J x y) =
        coord (Algebra.TensorProduct.basis R b) x ⬝ᵥ
          ((gramB (σ : E →+* E) b J).map (algebraMap F R) *ᵥ
            coord (Algebra.TensorProduct.basis R b) y) := fun x y => by
      rw [← gramB_tensor]
      exact trace_hform (sigR R σ) (sigR_smul R σ) _ (JR R J) x y
    refine ⟨key, fun h g hg => ?_⟩
    have hact := coord_mulVec (Algebra.TensorProduct.basis R b)
      (HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) g (fun p q => by
        rw [hg, Algebra.TensorProduct.basis_apply]
        rfl)
    refine ⟨?_, hact⟩
    have hU : cT (sigR R σ) (HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J *
        (HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) = JR R J :=
      (show HR R σ J from h).2
    apply mat_ext
    intro u v
    obtain ⟨x, rfl⟩ := coord_surj (M := M) (Algebra.TensorProduct.basis R b) u
    obtain ⟨y, rfl⟩ := coord_surj (M := M) (Algebra.TensorProduct.basis R b) v
    have h1 := key ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x)
      ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ y)
    have h2 : hR R σ J ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ x)
        ((HA.mat R σ J h : Matrix (Fin M) (Fin M) (R ⊗[F] E)) *ᵥ y) = hR R σ J x y :=
      hform_mulVec _ _ _ hU x y
    rw [h2, key x y, hact x, hact y, dot_mulVec_left, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec] at h1
    exact h1.symm

end GlobalTheory.CompanionTheory.SW.TraceCoord
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramRightMulActionLaws
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.RMulGram

theorem mul_regroup {A : Type} [CommRing A] {m n : Type} [Fintype m] [Fintype n]
    (P : Matrix n n A) (B : Matrix n m A) (J : Matrix m m A) (C : Matrix m n A)
    (g : Matrix n n A) :
    (P * B) * J * (C * g) = P * ((B * J : Matrix n m A) * C) * g := by
  simp only [Matrix.mul_assoc]

section
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def colsM {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) : Matrix (Fin M) (Fin n) (R ⊗[F] E) :=
  fun i a => X a i

theorem colsM_injective {M n : ℕ} {X Y : Fin n → Fin M → R ⊗[F] E}
    (h : colsM R X = colsM R Y) : X = Y := by
  funext a i
  exact congrFun (congrFun h i) a

theorem gramR_eq_mul (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ J X =
      (cT (sigR R σ) (colsM R X) * JR R J : Matrix (Fin n) (Fin M) (R ⊗[F] E)) * colsM R X := by
  ext a b
  simp only [gramR, hR, hform, Matrix.mul_apply, cT, Matrix.transpose_apply, Matrix.map_apply,
    colsM, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_mul]
  congr 1

theorem colsM_rmul {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E)
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    colsM R (rmul R X g) = colsM R X * g := by
  ext i a
  simp only [rmul, colsM, Matrix.mul_apply]

theorem gramR_rmul (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    gramR R σ J (rmul R X g) = cT (sigR R σ) g * gramR R σ J X * g := by
  rw [gramR_eq_mul, gramR_eq_mul, colsM_rmul, cT_mul]
  exact mul_regroup _ _ _ _ _

theorem rmul_rmul {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E)
    (g g' : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    rmul R (rmul R X g) g' = rmul R X (g * g') := by
  apply colsM_injective
  rw [colsM_rmul, colsM_rmul, colsM_rmul, Matrix.mul_assoc]

theorem rmul_one {M n : ℕ} (X : Fin n → Fin M → R ⊗[F] E) : rmul R X 1 = X := by
  apply colsM_injective
  rw [colsM_rmul, Matrix.mul_one]

theorem actTup_rmul {M n : ℕ} (k : GL (Fin M) (R ⊗[F] E)) (X : Fin n → Fin M → R ⊗[F] E)
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    actTup R k (rmul R X g) = rmul R (actTup R k X) g := by
  funext a i
  simp only [actTup, rmul, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm

end

theorem rmul_gram_facts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → R ⊗[F] E) (g g' : Matrix (Fin n) (Fin n) (R ⊗[F] E)), gramR R σ J (rmul R X g) = cT (sigR R σ) g * gramR R σ J X * g ∧ rmul R (rmul R X g) g' = rmul R X (g * g') ∧ rmul R X 1 = X ∧ ∀ k : GL (Fin M) (R ⊗[F] E), actTup R k (rmul R X g) = rmul R (actTup R k X) g := by
  intro F E _ _ _ _ _ σ _ R _ _ M n J X g g'
  exact ⟨gramR_rmul R σ J X g, rmul_rmul R X g g', rmul_one R X, fun k => actTup_rmul R k X g⟩

end GlobalTheory.CompanionTheory.SW.RMulGram
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeMatrixDeterminantFormulaStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.ThW
open scoped ENNReal NNReal MatrixGroups Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_matrix_determinant_formula : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] [DecidableEq (InfinitePlace F)] (ρ : InfinitePlace F → (F →+* ℝ)), IsTotallyReal F → (∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) → ∀ (b : Module.Basis (InfinitePlace F) ℤ (𝓞 F)) (N : ℕ), |(gM (ι := ι) ρ (fun v => b v) N).det| = ((N : ℝ) ^ Module.finrank ℚ F * Real.sqrt |(discr F : ℝ)|) ^ Fintype.card ι := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThW.abs_det_gM_all | exact GlobalTheory.CompanionTheory.SW.ThW.abs_det_gM_all | (intros; apply GlobalTheory.CompanionTheory.SW.ThW.abs_det_gM_all <;> assumption)
end

