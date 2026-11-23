module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0017
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetMulVolMulConj
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsBinaryEqAdicCompletion
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FromBlocksMapIntCastMemSymplecticGroup
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslate
section
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors

namespace GlobalTheory.AdLat.Translate

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

lemma fv_add (x y : Fin n → E) : fv F (x + y) = fv F x + fv F y := by
  ext i; simp [fv, TensorProduct.tmul_add]

lemma fv_zero : fv F (0 : Fin n → E) = 0 := by
  ext i; simp [fv]

lemma fv_nsmul (d : ℕ) (x : Fin n → E) : fv F (d • x) = d • fv F x := by
  induction d with
  | zero => simp [fv_zero]
  | succ k ih => rw [succ_nsmul, succ_nsmul, fv_add, ih]

lemma fv_smul (b : E) (x : Fin n → E) :
    fv F (b • x) = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] b : RA F E) • fv F x := by
  ext i; simp [fv]

lemma gen_eq (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    (fun i => (a ⊗ₜ[F] x i : RA F E)) = (a ⊗ₜ[F] (1 : E) : RA F E) • fv F x := by
  ext i; simp [fv]

lemma fv_mem_hat {S : Set (Fin n → E)} {x : Fin n → E} (hx : x ∈ S) : fv F x ∈ hat F S :=
  AddSubgroup.subset_closure ⟨1, fun v => one_mem _, x, hx, rfl⟩

lemma hat_smul_int {S : Set (Fin n → E)} {a : FiniteAdeleRing (𝓞 F) F}
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) {z : Fin n → RA F E} (hz : z ∈ hat F S) :
    (a ⊗ₜ[F] (1 : E) : RA F E) • z ∈ hat F S := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a', ha', x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a * a', fun v => mul_mem (ha v) (ha' v), x, hx, ?_⟩
    ext i; simp
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

lemma hat_smul_ring (L : Submodule (𝓞 E) (Fin n → E)) (b : 𝓞 E) {z : Fin n → RA F E}
    (hz : z ∈ hat F (L : Set (Fin n → E))) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (b : E) : RA F E) • z ∈ hat F (L : Set (Fin n → E)) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a', ha', x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a', ha', b • x, L.smul_mem b hx, ?_⟩
    ext i; simp [Algebra.smul_def]
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

def pre (M : Matrix (Fin n) (Fin n) (RA F E)) (L : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (𝓞 E) (Fin n → E) where
  carrier := {v | M.mulVec (fv F v) ∈ hat F (L : Set (Fin n → E))}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_ofPred_eq] at *
    rw [fv_add, Matrix.mulVec_add]; exact add_mem hx hy
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    rw [fv_zero, Matrix.mulVec_zero]; exact zero_mem _
  smul_mem' := by
    intro b x hx
    simp only [Set.mem_ofPred_eq] at *
    have : b • x = (b : E) • x := rfl
    rw [this, fv_smul, Matrix.mulVec_smul]
    exact hat_smul_ring L b hx

lemma mem_pre {M : Matrix (Fin n) (Fin n) (RA F E)} {L : Submodule (𝓞 E) (Fin n → E)} {v : Fin n → E} :
    v ∈ pre M L ↔ M.mulVec (fv F v) ∈ hat F (L : Set (Fin n → E)) := Iff.rfl

lemma mulVec_mem_hat {M : Matrix (Fin n) (Fin n) (RA F E)} {L : Submodule (𝓞 E) (Fin n → E)}
    {S : Set (Fin n → E)} (hS : S ⊆ pre M L) {z : Fin n → RA F E} (hz : z ∈ hat F S) :
    M.mulVec z ∈ hat F (L : Set (Fin n → E)) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a', ha', x, hx, rfl⟩ := hz
    rw [gen_eq, Matrix.mulVec_smul]
    exact hat_smul_int ha' (hS hx)
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mulVec_neg]; exact neg_mem hx

lemma exists_bound (M : Matrix (Fin n) (Fin n) (RA F E)) {L : Submodule (𝓞 E) (Fin n → E)} (hL : L.FG)
    (h : ∀ z : Fin n → RA F E, ∃ d : ℕ, 0 < d ∧ d • z ∈ hat F (L : Set (Fin n → E))) :
    ∃ d : ℕ, 0 < d ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), d • M.mulVec z ∈ hat F (L : Set (Fin n → E)) := by
  classical
  choose f hf0 hf using h
  obtain ⟨s, hs⟩ := hL
  refine ⟨∏ x ∈ s, f (M.mulVec (fv F x)), Finset.prod_pos fun _ _ => hf0 _, fun z hz => ?_⟩
  rw [← Matrix.smul_mulVec]
  refine mulVec_mem_hat ?_ hz
  have : L ≤ pre ((∏ x ∈ s, f (M.mulVec (fv F x))) • M) L := by
    conv_lhs => rw [← hs]
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun x => f (M.mulVec (fv F x))) (Finset.mem_coe.1 hx)
    rw [SetLike.mem_coe, mem_pre, Matrix.smul_mulVec, hk, mul_comm, mul_smul]
    exact nsmul_mem (hf _) _
  exact this

lemma nsmul_mem_hat {S S' : Set (Fin n → E)} {d : ℕ} (h : ∀ x ∈ S, d • x ∈ S') {z : Fin n → RA F E}
    (hz : z ∈ hat F S) : d • z ∈ hat F S' := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a', ha', x, hx, rfl⟩ := hz
    rw [gen_eq, smul_comm, ← fv_nsmul]
    exact hat_smul_int ha' (fv_mem_hat (h x hx))
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

lemma nsmul_cancel {d : ℕ} (hd : 0 < d) {x y : Fin n → RA F E} (h : d • x = d • y) : x = y := by
  rw [← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F] at h
  have hd' : (d : F) ≠ 0 := by exact_mod_cast hd.ne'
  have := congrArg (fun z => (d : F)⁻¹ • z) h
  simpa [smul_smul, inv_mul_cancel₀ hd'] using this

end GlobalTheory.AdLat.Translate


open GlobalTheory.AdLat.Translate in
theorem GlobalTheory.AdLat.exists_lattice_latOf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (g : GL (Fin n) (RA F E)), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∃ Λ : Submodule (𝓞 E) (Fin n → E), (Λ : Set (Fin n → E)) = latOf F (g : Matrix (Fin n) (Fin n) (RA F E)) L ∧ Λ.FG ∧ Submodule.span E (Λ : Set (Fin n → E)) = ⊤ ∧ (hat F (Λ : Set (Fin n → E)) : Set (Fin n → RA F E)) = (g : Matrix (Fin n) (Fin n) (RA F E)).mulVec '' (hat F (L : Set (Fin n → E))) := by
  intro F E _ _ _ _ _ n L g hL hspan
  obtain ⟨h1, h2, -, h4⟩ := GlobalTheory.AdLat.hat_rational_points_and_approx F E n L hL hspan
  set G : Matrix (Fin n) (Fin n) (RA F E) := (g : Matrix (Fin n) (Fin n) (RA F E)) with hG
  set H : Matrix (Fin n) (Fin n) (RA F E) := ((g⁻¹ : GL (Fin n) (RA F E)) : Matrix (Fin n) (Fin n) (RA F E))
    with hH
  have hGH : ∀ z, G.mulVec (H.mulVec z) = z := by
    intro z; rw [Matrix.mulVec_mulVec, hG, hH, Units.mul_inv, Matrix.one_mulVec]
  have hHG : ∀ z, H.mulVec (G.mulVec z) = z := by
    intro z; rw [Matrix.mulVec_mulVec, hG, hH, Units.inv_mul, Matrix.one_mulVec]
  have him : ∀ z, z ∈ G.mulVec '' (hat F (L : Set (Fin n → E)) : Set (Fin n → RA F E)) ↔
      H.mulVec z ∈ hat F (L : Set (Fin n → E)) := by
    intro z
    constructor
    · rintro ⟨u, hu, rfl⟩; rw [hHG]; exact hu
    · intro h; exact ⟨_, h, hGH z⟩
  obtain ⟨d, hd, hdG⟩ := exists_bound G hL h4
  obtain ⟨e, he, heH⟩ := exists_bound H hL h4
  have hd' : (d : E) ≠ 0 := by exact_mod_cast hd.ne'
  have he' : (e : E) ≠ 0 := by exact_mod_cast he.ne'
  have hlow : ∀ x ∈ L, e • x ∈ pre H L := by
    intro x hx
    rw [mem_pre, fv_nsmul, Matrix.mulVec_smul]
    exact heH _ (fv_mem_hat hx)
  have hup : ∀ x ∈ pre H L, d • x ∈ L := by
    intro x hx
    rw [← h1, fv_nsmul, ← hGH (fv F x)]
    exact hdG _ hx
  refine ⟨pre H L, ?_, ?_, ?_, ?_⟩
  · ext v
    exact (him _).symm
  · have hinj : Function.Injective (d • (LinearMap.id : (Fin n → E) →ₗ[𝓞 E] (Fin n → E))) := by
      intro x y hxy
      simp only [LinearMap.smul_apply, LinearMap.id_apply] at hxy
      rw [← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E] at hxy
      exact smul_right_injective _ hd' hxy
    refine Submodule.fg_of_fg_map_injective _ hinj ?_
    have hle : (pre H L).map (d • (LinearMap.id : (Fin n → E) →ₗ[𝓞 E] (Fin n → E))) ≤ L := by
      rintro _ ⟨x, hx, rfl⟩
      exact hup x hx
    have : IsNoetherian (𝓞 E) L := isNoetherian_of_fg_of_noetherian _ hL
    exact (isNoetherian_submodule.1 this) _ hle
  · rw [eq_top_iff, ← hspan, Submodule.span_le]
    intro x hx
    have hx' : x = (e : E)⁻¹ • (e • x) := by
      rw [← Nat.cast_smul_eq_nsmul E, smul_smul, inv_mul_cancel₀ he', one_smul]
    rw [hx']
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hlow x hx))
  · ext z
    rw [him]
    constructor
    · intro hz
      exact mulVec_mem_hat subset_rfl hz
    · intro hz
      have hdz : d • z ∈ hat F (L : Set (Fin n → E)) := by
        rw [← hGH z]; exact hdG _ hz
      obtain ⟨x, -, w, hw, hxw⟩ := h2 (d * e) (Nat.mul_pos hd he) _ hdz
      have hx' : x = d • ((d : E)⁻¹ • x) := by
        rw [← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hd', one_smul]
      have hz' : z = fv F ((d : E)⁻¹ • x) + e • w := by
        apply nsmul_cancel hd
        rw [smul_add, ← fv_nsmul, ← hx', smul_smul, hxw]
      have hy : (d : E)⁻¹ • x ∈ pre H L := by
        rw [mem_pre, eq_sub_of_add_eq hz'.symm, Matrix.mulVec_sub, Matrix.mulVec_smul]
        exact sub_mem hz (heH _ hw)
      rw [hz']
      exact add_mem (fv_mem_hat hy) (nsmul_mem_hat hlow hw)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HermitianFormsSameSignatureSameSpace
section
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.OneSpace

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem emb_cc (τ : E →+* ℂ) (x : E) : τ (FD.cc x) = starRingEnd ℂ (τ x) :=
  IsCMField.complexEmbedding_complexConj E τ x

theorem rt_sq' (H : Host E) : (H.rt : E) ^ 2 = -(H.d : E) := by
  have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
  simpa using this

theorem conj_of_sq {z : ℂ} {d : ℕ} (hd : 0 < d) (h : z ^ 2 = -(d : ℂ)) :
    starRingEnd ℂ z = -z := by
  first
  | exact @_root_.GlobalTheory.ConjNegSquareNat.conj_eq_neg_of_sq_eq_neg_nat
  | exact _root_.GlobalTheory.ConjNegSquareNat.conj_eq_neg_of_sq_eq_neg_nat
  | (apply _root_.GlobalTheory.ConjNegSquareNat.conj_eq_neg_of_sq_eq_neg_nat <;> assumption)
  | (intros; apply _root_.GlobalTheory.ConjNegSquareNat.conj_eq_neg_of_sq_eq_neg_nat <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ConjNegSquareNat.conj_eq_neg_of_sq_eq_neg_nat <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ConjNegSquareNat.conj_eq_neg_of_sq_eq_neg_nat ..)

theorem emb_rt_sq (H : Host E) (τ : E →+* ℂ) : τ (H.rt : E) ^ 2 = -(H.d : ℂ) := by
  rw [← map_pow, rt_sq']; simp

theorem cc_rt (H : Host E) : FD.cc (H.rt : E) = -(H.rt : E) := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [emb_cc, map_neg]
  exact conj_of_sq H.d_prime.pos (emb_rt_sq H τ)

theorem rt_ne (H : Host E) : (H.rt : E) ≠ 0 := by
  intro h
  have := rt_sq' H
  rw [h] at this
  have h2 : (H.d : E) = 0 := by simpa using this
  exact H.d_prime.ne_zero (by exact_mod_cast h2)

theorem gram_eq {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (Q : Matrix (Fin r) (Fin r) ℂ) :
    FD.gram τ G Q = Qᵀ * G.map τ * Q.map (starRingEnd ℂ) := by
  ext a b
  simp only [FD.gram, FD.hermC, FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem det_gram {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (Q : Matrix (Fin r) (Fin r) ℂ) :
    (FD.gram τ G Q).det = ((‖Q.det‖ ^ 2 : ℝ) : ℂ) * τ G.det := by
  rw [gram_eq, det_mul, det_mul, det_transpose]
  have h1 : (G.map τ).det = τ G.det := (RingHom.map_det τ G).symm
  have h2 : (Q.map (starRingEnd ℂ)).det = starRingEnd ℂ Q.det := (RingHom.map_det _ Q).symm
  rw [h1, h2, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  ring

theorem gram_conj {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (p : ℕ)
    (h : ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      FD.gram (ComplexEmbedding.conjugate τ) G Q =
        Matrix.diagonal fun a : Fin r => ((FD.sgn p (a : ℕ) : ℝ) : ℂ)) :
    ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      FD.gram τ G Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p (a : ℕ) : ℝ) : ℂ) := by
  obtain ⟨Q, hQ, h⟩ := h
  refine ⟨Q.map (starRingEnd ℂ), ?_, ?_⟩
  · have h2 : (Q.map (starRingEnd ℂ)).det = starRingEnd ℂ Q.det := (RingHom.map_det _ Q).symm
    rw [h2]
    simpa using hQ
  · ext a b
    have := congrArg (starRingEnd ℂ) (congrFun (congrFun h a) b)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [FD.gram, FD.hermC, FD.col, Matrix.of_apply, Matrix.map_apply, map_sum, map_mul,
      ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj, Matrix.diagonal_apply] at this ⊢
    rw [this]
    split_ifs <;> simp

theorem cc_det {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (h : ∀ a b, FD.cc (G a b) = G b a) :
    FD.cc G.det = G.det := by
  have h1 : IsCMField.complexConj E G.det = (G.map (IsCMField.complexConj E)).det :=
    RingHom.map_det (IsCMField.complexConj E).toRingEquiv.toRingHom G
  have h2 : G.map (IsCMField.complexConj E) = Gᵀ := by
    ext a b
    exact h a b
  rw [FD.cc, h1, h2, det_transpose]

theorem im_ne (τ : E →+* ℂ) {ξ : E} (h : FD.cc ξ = -ξ) (h0 : ξ ≠ 0) : (τ ξ).im ≠ 0 := by
  intro hi
  have h1 := emb_cc τ ξ
  rw [h, map_neg] at h1
  have h2 := congrArg Complex.re h1
  simp at h2
  apply h0
  apply τ.injective
  rw [map_zero]
  apply Complex.ext <;> simp [hi]
  linarith

end GlobalTheory.OneSpace

namespace GlobalTheory

open GlobalTheory.OneSpace

theorem model_in_same_space : (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G G' : Matrix (Fin r) (Fin r) E), (∀ a b, FD.cc (G a b) = G b a) → (∀ a b, FD.cc (G' a b) = G' b a) → G.det ≠ 0 → G'.det ≠ 0 → (∀ τ : E →+* ℂ, ∃ p0 : ℕ, (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ G Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ)) ∧ (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ G' Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ))) → (∃ z : E, G'.det = z * FD.cc z * G.det) → ∃ γ : GL (Fin r) E, ∀ x y, FD.herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = FD.herm G' x y) → (∀ (F : Type) [Field F] [NumberField F] (δ x : F), δ ≠ 0 → x ≠ 0 → (∀ σ : F →+* ℝ, ∃ a b : ℝ, σ x = a ^ 2 - σ δ * b ^ 2) → (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ∃ a b : v.adicCompletion F, algebraMap F (v.adicCompletion F) x = a ^ 2 - algebraMap F (v.adicCompletion F) δ * b ^ 2) → ∃ a b : F, x = a ^ 2 - δ * b ^ 2) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D D' : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)), D'.p = D.p → D'.q = D.q → FD.cc ξ = -ξ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → ∃ φ' : D'.La →ₗ[𝓞 E] (Fin r → E), (Function.Injective φ' ∧ Submodule.span E (Set.range φ') = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D'.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ' x) (φ' y))) := by
  intro hL hH E _ _ _ H D D' r ξ Gm φ hp hq hξ hM
  have hr : r = D'.p + D'.q := by
    rw [hp, hq]
    exact (GlobalTheory.HermModel.rank_integral_selfDual E H D r ξ Gm φ hξ hM).1
  by_cases h0 : ξ = 0
  · obtain ⟨Gm', ψ, hinj, hspan, -, -, -⟩ :=
      GlobalTheory.exists_herm_coord_of_datum E H D' (H.rt : E) (cc_rt H) (rt_ne H) r hr
    obtain ⟨-, hs, hG, hdet, hEF⟩ := hM
    have hz : ∀ x : D.La, x = 0 := by
      intro x
      apply D.unimod.1
      ext y
      have := hEF x y
      rw [h0, zero_mul, map_zero] at this
      rw [map_zero, LinearMap.zero_apply]
      exact_mod_cast this
    have hz' : ∀ v : Fin r → E, v = 0 := by
      intro v
      have hv : v ∈ Submodule.span E (Set.range φ) := hs ▸ Submodule.mem_top
      have : Submodule.span E (Set.range φ) ≤ ⊥ := by
        rw [Submodule.span_le]
        rintro _ ⟨x, rfl⟩
        rw [hz x, map_zero]
        exact Submodule.zero_mem _
      exact (Submodule.mem_bot E).1 (this hv)
    refine ⟨ψ, hinj, hspan, hG, hdet, fun x y => ?_⟩
    have : x = 0 := hinj ((hz' _).trans (hz' _).symm)
    rw [this, h0]
    simp
  obtain ⟨Gm', ψ, hM'⟩ := GlobalTheory.exists_herm_coord_of_datum E H D' ξ hξ h0 r hr
  have hsΨ : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → ∃ p0 : ℕ, (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ Gm Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ)) ∧ (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ Gm' Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ)) := by
    intro τ hτ
    have s1 := GlobalTheory.T.signature_hermitian_model_of_datum E H D r ξ Gm φ hξ hM τ hτ
    have s2 := GlobalTheory.T.signature_hermitian_model_of_datum E H D' r ξ Gm' ψ hξ hM' τ hτ
    rw [hp, hq] at s2
    rcases lt_or_gt_of_ne (im_ne τ hξ h0) with h | h
    · exact ⟨_, s1.2 h, s2.2 h⟩
    · exact ⟨_, s1.1 h, s2.1 h⟩
  have hs : ∀ τ : E →+* ℂ, ∃ p0 : ℕ, (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ Gm Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ)) ∧ (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ Gm' Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ)) := by
    intro τ
    have h1 : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by rw [emb_rt_sq, H.sqrt_neg_disc_sq]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
    · exact hsΨ τ h
    · obtain ⟨p0, a, b⟩ := hsΨ (ComplexEmbedding.conjugate τ) (by
        rw [ComplexEmbedding.conjugate_coe_eq, conj_of_sq H.d_prime.pos (emb_rt_sq H τ), h, neg_neg])
      exact ⟨p0, gram_conj τ _ _ a, gram_conj τ _ _ b⟩
  have hI := GlobalTheory.DetIdeal.det_ideal E H D D' r ξ Gm φ Gm' ψ hξ hM hM'
  obtain ⟨-, -, hG, hdet, -⟩ := hM
  obtain ⟨hinj, hspan, hG', hdet', hEF⟩ := hM'
  have hx : Gm'.det / Gm.det ∈ maximalRealSubfield E := by
    rw [← IsCMField.complexConj_eq_self_iff, map_div₀]
    have e1 := cc_det Gm hG
    have e2 := cc_det Gm' hG'
    rw [FD.cc] at e1 e2
    rw [e1, e2]
  set x : maximalRealSubfield E := ⟨Gm'.det / Gm.det, hx⟩ with hxdef
  have hx0 : x ≠ 0 := by
    intro h
    exact div_ne_zero hdet' hdet (congrArg Subtype.val h)
  have hloc := GlobalTheory.local_norm_of_ideal_norm E H x hx0 hI
  have hreal : ∀ σ : maximalRealSubfield E →+* ℝ, ∃ a b : ℝ,
      σ x = a ^ 2 - σ (-(H.d : maximalRealSubfield E)) * b ^ 2 := by
    intro σ
    let τ : E →+* ℂ := ComplexEmbedding.lift E (Complex.ofRealHom.comp σ)
    have hτ : τ (Gm'.det / Gm.det) = (σ x : ℂ) :=
      ComplexEmbedding.lift_algebraMap_apply E (Complex.ofRealHom.comp σ) x
    obtain ⟨p0, ⟨Q, hQ, e⟩, ⟨Q', hQ', e'⟩⟩ := hs τ
    have e2 := congrArg Matrix.det (e.trans e'.symm)
    rw [det_gram, det_gram] at e2
    have n1 : τ Gm.det ≠ 0 := by simpa using hdet
    have n2 : ((‖Q'.det‖ : ℝ) : ℂ) ≠ 0 := by simpa using hQ'
    refine ⟨‖Q.det‖ / ‖Q'.det‖, 0, ?_⟩
    apply Complex.ofReal_injective
    rw [← hτ, map_div₀]
    push_cast at e2 ⊢
    field_simp
    linear_combination -e2
  obtain ⟨a, b, hab⟩ := hH (maximalRealSubfield E) (-(H.d : maximalRealSubfield E)) x
    (by simpa using H.d_prime.ne_zero) hx0 hreal hloc
  have hz : ∃ z : E, Gm'.det = z * FD.cc z * Gm.det := by
    refine ⟨(a : E) + (b : E) * (H.rt : E), ?_⟩
    have e1 : FD.cc ((a : E) + (b : E) * (H.rt : E)) = (a : E) - (b : E) * (H.rt : E) := by
      have c := cc_rt H
      rw [FD.cc] at c ⊢
      rw [map_add (f := _), map_mul, c, IsCMField.complexConj_apply_eq_self,
        IsCMField.complexConj_apply_eq_self]
      ring
    have e2 : Gm'.det / Gm.det = (a : E) ^ 2 + (H.d : E) * (b : E) ^ 2 := by
      have := congrArg Subtype.val hab
      simpa using this
    rw [e1, (div_eq_iff hdet).1 e2]
    have := rt_sq' H
    linear_combination (b : E) ^ 2 * Gm.det * this
  obtain ⟨γ, hγ⟩ := hL E r Gm Gm' hG hG' hdet hdet' hs hz
  let g : (Fin r → E) ≃ₗ[E] (Fin r → E) := Matrix.toLin'OfInv γ.inv_mul γ.mul_inv
  have hg : ∀ v, g v = (γ : Matrix (Fin r) (Fin r) E) *ᵥ v := fun v => rfl
  refine ⟨(g.toLinearMap.restrictScalars (𝓞 E)).comp ψ, g.injective.comp hinj, ?_, hG, hdet, ?_⟩
  · have : Set.range ((g.toLinearMap.restrictScalars (𝓞 E)).comp ψ) =
        g.toLinearMap '' Set.range ψ := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, hspan, Submodule.map_top, LinearEquiv.range]
  · intro u v
    rw [hEF, ← hγ, ← hg, ← hg]
    rfl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaSqTransformLevelEight
section
open Complex Matrix NumberField
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem theta_sq_transform_level_eight :
    ∀ (g : ℕ) (γ : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ),
      γ ∈ Matrix.symplecticGroup (Fin g) ℤ →
      (∀ i j, (8 : ℤ) ∣ γ (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ γ (Sum.inr i) (Sum.inl j)) →
      (∀ τ ∈ SiegelH (Fin g), ∀ z : Fin g → ℂ,
        theta (halfVec 0) (halfVec 0) (zAct γ τ z) (spAct γ τ) ^ 2 =
          ((ZMod.χ₄ ((γ.toBlocks₂₂.det : ℤ) : ZMod 4) : ℤ) : ℂ) * (jAut γ τ).det *
            eC (expArg γ τ z) * theta (halfVec 0) (halfVec 0) z τ ^ 2) := by
  intro g γ hγ h τ hτ z
  have h48 : (4 : ℤ) ∣ 8 := by norm_num
  exact theta_halfVec_sq_transform hγ (fun i j => h48.trans (h i j).1)
    (fun i j => h48.trans (h i j).2) (k := 0) (k' := 0) (m := 0) (m' := 0)
    (fun i => by rw [mulVec_zero]) (fun i => by rw [mulVec_zero]) hτ z

end GlobalTheory
end

