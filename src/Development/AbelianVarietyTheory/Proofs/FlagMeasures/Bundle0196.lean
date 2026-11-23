module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0181
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutPointLatticeIntersectionSelfDualProperties

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalBlockFrameOfComplexFlag
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

noncomputable section

namespace GlobalTheory.RadCov

open scoped InnerProductSpace

theorem mem_of_orth_piece {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {A B : Submodule ℂ E} (hAB : A ≤ B) {y : E} (hy : y ∈ B)
    (ho : y ∈ (Aᗮ ⊓ B)ᗮ) : y ∈ A := by
  obtain ⟨v, hv, w, hw, rfl⟩ := Submodule.exists_add_mem_mem_orthogonal (K := A) y
  have hwB : w ∈ B := by
    have := B.sub_mem hy (hAB hv)
    simpa using this
  have h1 : ⟪w, v + w⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).1 ho w ⟨hw, hwB⟩
  have h2 : ⟪w, v⟫_ℂ = 0 := (Submodule.mem_orthogonal' _ _).1 hw v hv
  rw [inner_add_right, h2, zero_add, inner_self_eq_zero] at h1
  simpa [h1] using hv

theorem exists_orthonormal_family {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (P : Submodule ℂ E) {r : ℕ} (hr : Module.finrank ℂ P = r) :
    ∃ e : Fin r → E, Orthonormal ℂ e ∧ (∀ j, e j ∈ P) ∧
      ∀ y, (∀ j, ⟪e j, y⟫_ℂ = 0) → y ∈ Pᗮ := by
  subst hr
  let b := stdOrthonormalBasis ℂ P
  refine ⟨fun j => (b j : E), ?_, fun j => (b j).2, fun y hy => ?_⟩
  · exact b.orthonormal.comp_linearIsometry P.subtypeₗᵢ
  · rw [Submodule.mem_orthogonal]
    intro u hu
    have h := congrArg (fun x : P => (x : E)) (b.sum_repr ⟨u, hu⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    rw [← h, sum_inner]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [inner_smul_left, hy j, mul_zero]

theorem exists_orthonormal_block_frame :
    ∀ (n m : ℕ) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (r : ℕ → ℕ), Monotone W → W 0 = ⊥ →
      (∀ b, m ≤ b → W b = ⊤) →
      (∀ b, Module.finrank ℂ (W (b + 1)) = Module.finrank ℂ (W b) + r b) →
      ∃ U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ, Biorth r m U (fun b => (U b)ᴴ) ∧
        ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0 := by
  intro n m W r hmono h0 htop hr
  let L : (Fin n → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n) := (WithLp.linearEquiv 2 ℂ (Fin n → ℂ)).symm
  let V : ℕ → Submodule ℂ (EuclideanSpace ℂ (Fin n)) := fun b => (W b).map L.toLinearMap
  have hV : ∀ b y, L y ∈ V b ↔ y ∈ W b := fun b y => by
    simp [V]
  have hVm : Monotone V := fun a b h => Submodule.map_mono (hmono h)
  have hfin : ∀ b, Module.finrank ℂ ((V b)ᗮ ⊓ V (b + 1) : Submodule ℂ _) = r b := fun b => by
    have h1 := Submodule.finrank_add_inf_finrank_orthogonal (hVm (Nat.le_succ b))
    have h2 : ∀ c, Module.finrank ℂ (V c) = Module.finrank ℂ (W c) := fun c =>
      LinearEquiv.finrank_map_eq L (W c)
    rw [h2, h2, hr] at h1
    exact Nat.add_left_cancel h1
  choose e he hmem hdet using fun b => exists_orthonormal_family _ (hfin b)
  let U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ := fun b => Matrix.of fun i j => e b j i
  have hU : ∀ b y j, ((U b)ᴴ *ᵥ y) j = ⟪e b j, L y⟫_ℂ := fun b y j => by
    simp [U, L, Matrix.mulVec, dotProduct, PiLp.inner_apply, mul_comm]
  have hUU : ∀ b b' j j', ((U b)ᴴ * U b') j j' = ⟪e b j, e b' j'⟫_ℂ := fun b b' j j' => by
    simp [U, Matrix.mul_apply, PiLp.inner_apply, mul_comm]
  have hflag : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → (U b)ᴴ *ᵥ y = 0 := by
    intro k y
    constructor
    · intro hy b hb
      funext j
      rw [hU]
      exact (Submodule.mem_orthogonal' _ _).1 (hmem b j).1 _ (hVm hb ((hV k y).2 hy))
    · intro hy
      have key : ∀ d, L y ∈ V (k + d) → L y ∈ V k := by
        intro d
        induction d with
        | zero => exact id
        | succ d ih =>
          intro h
          refine ih (mem_of_orth_piece (hVm (Nat.le_succ (k + d))) h (hdet _ _ fun j => ?_))
          rw [← hU, hy _ (Nat.le_add_right k d)]
          rfl
      refine (hV k y).1 (key m ((hV _ y).2 ?_))
      rw [htop _ (Nat.le_add_left m k)]
      trivial
  have h1 : ∀ b, (U b)ᴴ * U b = 1 := fun b => by
    ext j j'
    rw [hUU, orthonormal_iff_ite.1 (he b), Matrix.one_apply]
  have hlt : ∀ b b', b' < b → ∀ j j', ⟪e b j, e b' j'⟫_ℂ = 0 := fun b b' h j j' =>
    (Submodule.mem_orthogonal' _ _).1 (hmem b j).1 _ (hVm (Nat.succ_le_of_lt h) (hmem b' j').2)
  have h2 : ∀ b b', b ≠ b' → (U b)ᴴ * U b' = 0 := fun b b' h => by
    ext j j'
    rw [hUU, Matrix.zero_apply]
    rcases lt_or_gt_of_ne h with h | h
    · rw [inner_eq_zero_symm]; exact hlt _ _ h _ _
    · exact hlt _ _ h _ _
  refine ⟨U, ⟨h1, h2, ?_⟩, hflag⟩
  have h3 : ∀ y, (1 - ∑ b ∈ Finset.range m, U b * (U b)ᴴ) *ᵥ y = 0 := by
    intro y
    rw [← Submodule.mem_bot ℂ, ← h0, hflag]
    intro b _
    by_cases hb : m ≤ b
    · refine (hflag m _).1 ?_ b hb
      rw [htop m le_rfl]; trivial
    · rw [Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_sum,
        Finset.sum_eq_single b, ← Matrix.mul_assoc, h1]
      · simp
      · intro c _ hc
        rw [← Matrix.mul_assoc, h2 _ _ hc.symm, Matrix.zero_mul]
      · intro hc
        exact absurd (Finset.mem_range.2 (by omega)) hc
  refine (sub_eq_zero.1 ?_).symm
  ext i k
  have := congrFun (h3 (Pi.single k 1)) i
  simpa using this

end GlobalTheory.RadCov
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalTriangular
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso.BlockGS

theorem exists_coeff_of_mem_span {ι V : Type} [Fintype ι] [AddCommGroup V] [Module ℂ V]
    (g : ι → V) (s : Set ι) (v : V) (hv : v ∈ Submodule.span ℂ (g '' s)) :
    ∃ c : ι → ℂ, (∀ y, y ∉ s → c y = 0) ∧ v = ∑ y, c y • g y := by
  obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ).1 hv
  refine ⟨l, fun y hy => ?_, ?_⟩
  · by_contra h
    exact hy (hl (Finsupp.mem_support_iff.2 h))
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    simp

theorem exists_orthonormal_triangular {ι V : Type} [Fintype ι] [LinearOrder ι]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] (f : ι → V) (hf : LinearIndependent ℂ f) :
    ∃ (g : ι → V) (P Q : ι → ι → ℂ), Orthonormal ℂ g ∧ (∀ y x, x < y → P y x = 0 ∧ Q y x = 0) ∧
      (∀ x, f x = ∑ y, P y x • g y) ∧ ∀ x, g x = ∑ y, Q y x • f y := by
  classical
  let _ : LocallyFiniteOrderBot ι := LocallyFiniteOrderBot.ofIic ι (fun x => Finset.univ.filter (· ≤ x)) (by simp)
  have : WellFoundedLT ι := Finite.to_wellFoundedLT
  have hs : ∀ x, Submodule.span ℂ (InnerProductSpace.gramSchmidtNormed ℂ f '' Set.Iic x)
      = Submodule.span ℂ (f '' Set.Iic x) := fun x => by
    rw [InnerProductSpace.span_gramSchmidtNormed, InnerProductSpace.span_gramSchmidt_Iic]
  have h1 : ∀ x, ∃ c : ι → ℂ, (∀ y, y ∉ Set.Iic x → c y = 0) ∧
      f x = ∑ y, c y • InnerProductSpace.gramSchmidtNormed ℂ f y := fun x =>
    exists_coeff_of_mem_span _ _ _ (by
      rw [hs]; exact Submodule.subset_span ⟨x, le_refl x, rfl⟩)
  have h2 : ∀ x, ∃ c : ι → ℂ, (∀ y, y ∉ Set.Iic x → c y = 0) ∧
      InnerProductSpace.gramSchmidtNormed ℂ f x = ∑ y, c y • f y := fun x =>
    exists_coeff_of_mem_span _ _ _ (by
      rw [← hs]; exact Submodule.subset_span ⟨x, le_refl x, rfl⟩)
  choose P hP hP' using h1
  choose Q hQ hQ' using h2
  exact ⟨_, fun y x => P x y, fun y x => Q x y, InnerProductSpace.gramSchmidtNormed_orthonormal hf,
    fun y x h => ⟨hP x y (not_le.2 h), hQ x y (not_le.2 h)⟩, hP', hQ'⟩

theorem linearIndependent_columns (n a : ℕ) (j : Fin a → ℕ)
    (A : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (C : ∀ i, Matrix (Fin (j i)) (Fin n) ℂ)
    (h1 : ∀ i, C i * A i = 1) (h0 : ∀ i k, i ≠ k → C i * A k = 0) :
    LinearIndependent ℂ (fun x : (Σ i, Fin (j i)) =>
      (WithLp.toLp 2 (fun r => A x.1 r x.2) : EuclideanSpace ℂ (Fin n))) := by
  classical
  rw [Fintype.linearIndependent_iff]
  rintro c hc ⟨i, u⟩
  have hr : ∀ r, ∑ x : (Σ i, Fin (j i)), c x * A x.1 r x.2 = 0 := fun r => by
    have := congrArg (fun v : EuclideanSpace ℂ (Fin n) => v r) hc
    simpa using this
  have h : ∑ x : (Σ i, Fin (j i)), c x * (C i * A x.1) u x.2 = 0 := by
    simp only [Matrix.mul_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun r _ => ?_
    have := congrArg (fun z => C i u r * z) (hr r)
    simp only [Finset.mul_sum, mul_zero] at this
    rw [← this]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [Fintype.sum_sigma, Finset.sum_eq_single i] at h
  · simpa [h1, Matrix.one_apply] using h
  · intro k _ hk
    simp [h0 i k hk.symm]
  · simp

theorem block_gramSchmidt : ∀ (n a : ℕ) (j : Fin a → ℕ) (A : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (C : ∀ i, Matrix (Fin (j i)) (Fin n) ℂ), (∀ i, C i * A i = 1) → (∀ i k, i ≠ k → C i * A k = 0) → ∃ (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (p q : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ), (∀ i, (B i)ᴴ * B i = 1) ∧ (∀ i k, i ≠ k → (B i)ᴴ * B k = 0) ∧ (∀ k i, i < k → p k i = 0 ∧ q k i = 0) ∧ (∀ i, A i = ∑ k, B k * p k i) ∧ (∀ i, B i = ∑ k, A k * q k i) ∧ ∀ i, p i i * q i i = 1 := by
  classical
  intro n a j A C h1 h0
  let _ : LinearOrder (Σ i, Fin (j i)) := inferInstanceAs (LinearOrder (Σₗ i, Fin (j i)))
  obtain ⟨g, P, Q, hg, htri, hf, hg'⟩ :=
    exists_orthonormal_triangular _ (linearIndependent_columns n a j A C h1 h0)
  let B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ := fun i => Matrix.of fun r u => g ⟨i, u⟩ r
  let p : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ := fun k i => Matrix.of fun v u => P ⟨k, v⟩ ⟨i, u⟩
  let q : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ := fun k i => Matrix.of fun v u => Q ⟨k, v⟩ ⟨i, u⟩
  have hBB : ∀ i k u v, ((B i)ᴴ * B k) u v = inner ℂ (g ⟨i, u⟩) (g ⟨k, v⟩) := by
    intro i k u v
    simp [B, Matrix.mul_apply, PiLp.inner_apply, mul_comm]
  have e1 : ∀ i, (B i)ᴴ * B i = 1 := by
    intro i
    ext u v
    rw [hBB, orthonormal_iff_ite.1 hg, Matrix.one_apply]
    simp
  have e2 : ∀ i k, i ≠ k → (B i)ᴴ * B k = 0 := by
    intro i k h
    ext u v
    rw [hBB, orthonormal_iff_ite.1 hg]
    simp [h]
  have e3 : ∀ k i, i < k → p k i = 0 ∧ q k i = 0 := by
    intro k i h
    constructor <;> ext v u
    · exact (htri _ _ (Sigma.Lex.left _ _ h)).1
    · exact (htri _ _ (Sigma.Lex.left _ _ h)).2
  have e4 : ∀ i, A i = ∑ k, B k * p k i := by
    intro i
    ext r u
    have := congrArg (fun v : EuclideanSpace ℂ (Fin n) => v r) (hf ⟨i, u⟩)
    simp only [Matrix.sum_apply, Matrix.mul_apply, B, p, Matrix.of_apply]
    simpa [Fintype.sum_sigma, mul_comm] using this
  have e5 : ∀ i, B i = ∑ k, A k * q k i := by
    intro i
    ext r u
    have := congrArg (fun v : EuclideanSpace ℂ (Fin n) => v r) (hg' ⟨i, u⟩)
    simp only [Matrix.sum_apply, Matrix.mul_apply, B, q, Matrix.of_apply]
    simpa [Fintype.sum_sigma, mul_comm] using this
  refine ⟨B, p, q, e1, e2, e3, e4, e5, fun i => ?_⟩
  have hp : ∀ k, (B i)ᴴ * A k = p i k := by
    intro k
    rw [e4 k, Matrix.mul_sum, Finset.sum_eq_single i]
    · rw [← Matrix.mul_assoc, e1, Matrix.one_mul]
    · intro l _ hl
      rw [← Matrix.mul_assoc, e2 i l hl.symm, Matrix.zero_mul]
    · simp
  have h : (B i)ᴴ * (∑ k, A k * q k i) = 1 := by rw [← e5, e1]
  rw [Matrix.mul_sum, Finset.sum_eq_single i] at h
  · rw [← h, ← Matrix.mul_assoc, hp]
  · intro l _ hl
    rw [← Matrix.mul_assoc, hp]
    rcases lt_or_gt_of_ne hl with hl | hl
    · rw [(e3 i l hl).1, Matrix.zero_mul]
    · rw [(e3 l i hl).2, Matrix.mul_zero]
  · simp

end GlobalTheory.LeviIso.BlockGS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRationalFlagBlockFixingLattice
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

noncomputable section

namespace GlobalTheory.LeviRat

open GlobalTheory.AdaptedMove GlobalTheory.FlagConj GlobalTheory.PointEquivariance

theorem mem_conj_iff (I : AutInst) (x : I.Gf) (c : I.GA) (γ : GL (Fin I.n) I.E)
    (hc : I.fmat c.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F))) :
    x⁻¹ * c.2 * x ∈ I.Kset ↔ ratIso I γ (lamX I (1, x)) = lamX I (1, x) := by
  have hk := GlobalTheory.PointEquivariance.lamX_mul_eq_iff I ((1 : I.Ginf), x) (((1 : I.Ginf), x)⁻¹ * c * ((1 : I.Ginf), x))
  have hcx : ((1 : I.Ginf), x) * (((1 : I.Ginf), x)⁻¹ * c * ((1 : I.Ginf), x)) = c * ((1 : I.Ginf), x) := by
    group
  rw [hcx, GlobalTheory.PointEquivariance.lamX_rat I ((1 : I.Ginf), x) c γ hc] at hk
  exact hk

private theorem mem_UJ_iff_flag_measures {E : Type} [Field E] [StarRing E] {m : ℕ} (J : Matrix (Fin m) (Fin m) E)
    (g : GL (Fin m) E) :
    g ∈ Formalism.UG.UJ (starRingEnd E) J ↔ (g : Matrix (Fin m) (Fin m) E)ᴴ * J * g = J := by
  have key : ((g : Matrix (Fin m) (Fin m) E).map (starRingEnd E))ᵀ = (g : Matrix (Fin m) (Fin m) E)ᴴ := by
    ext r s
    simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply]
    rfl
  show ((g : Matrix (Fin m) (Fin m) E).map (starRingEnd E))ᵀ * J * g = J ↔ _
  rw [key]

private theorem inv_mul_eq_mul_inv_of_mul_eq_mul {R : Type} [CommRing R] {m p : ℕ} (G G' : Matrix (Fin m) (Fin m) R)
    (C C' : Matrix (Fin p) (Fin p) R) (X : Matrix (Fin m) (Fin p) R) (hG : G' * G = 1) (hC : C * C' = 1)
    (h : G * X = X * C) : G' * X = X * C' := by
  calc G' * X = G' * (X * C) * C' := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hC, Matrix.mul_one]
    _ = X * C' := by rw [← h, ← Matrix.mul_assoc, hG, Matrix.one_mul]

private theorem lat_mulVec_lemma_3 (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) {a : ℕ} (j : Fin a → ℕ)
    (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf)
    (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E)
    (hlat : ∀ z, z ∈ lamX I (1, xf) ↔ ∃ (u u' : ∀ i, Fin (j i) → I.E) (y : Fin I₀.n → I₀.E), (∀ i, u i ∈ Λ i) ∧
      (∀ i, ∀ t ∈ Λ i, star t ⬝ᵥ u' i ∈ (algebraMap (𝓞 I.E) I.E).range) ∧ y ∈ lamX I₀ (1, x₀) ∧
      z = ∑ i, T i *ᵥ u i + ∑ i, T' i *ᵥ u' i + T₀ *ᵥ fun l => e (y l))
    (G : Matrix (Fin I.n) (Fin I.n) I.E) (c A : ∀ i, Matrix (Fin (j i)) (Fin (j i)) I.E)
    (d : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E)
    (hc : ∀ i, ∀ u ∈ Λ i, c i *ᵥ u ∈ Λ i) (hA : ∀ i, ∀ u ∈ Λ i, A i *ᵥ u ∈ Λ i)
    (hd : ∀ y ∈ lamX I₀ (1, x₀), d *ᵥ y ∈ lamX I₀ (1, x₀))
    (hT : ∀ i, G * T i = T i * c i) (hT' : ∀ i, G * T' i = T' i * (A i)ᴴ) (h₀ : G * T₀ = T₀ * d.map e) :
    ∀ z ∈ lamX I (1, xf), G *ᵥ z ∈ lamX I (1, xf) := by
  intro z hz
  obtain ⟨u, u', y, hu, hu', hy, rfl⟩ := (hlat z).1 hz
  refine (hlat _).2 ⟨fun i => c i *ᵥ u i, fun i => (A i)ᴴ *ᵥ u' i, d *ᵥ y, fun i => hc i _ (hu i), ?_, hd y hy, ?_⟩
  · intro i t ht
    rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    exact hu' i _ (hA i t ht)
  · beta_reduce
    rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_sum]
    congr 1
    · congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.mulVec_mulVec, hT i, ← Matrix.mulVec_mulVec]
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.mulVec_mulVec, hT' i, ← Matrix.mulVec_mulVec]
    · rw [Matrix.mulVec_mulVec, h₀, ← Matrix.mulVec_mulVec]
      congr 1
      funext l
      exact (RingHom.map_mulVec (e : I₀.E →+* I.E) d y l).symm

theorem exists_rat_block : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E)) (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E), IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ → ∀ γ : ∀ i, GL (Fin (j i)) I.E, (∀ i y, (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E) *ᵥ y ∈ Λ i ↔ y ∈ Λ i) → ∀ g₀ ∈ latGroup I₀ x₀, ∃ g ∈ latGroup I xf, ∃ (Γ : Matrix (Fin I.n) (Fin I.n) I.E) (γ₀ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E), (∀ v, uMat (g v) = (I.P v)⁻¹ * Γ.map (I.φ v) * I.P v) ∧ (∀ v, uMat (g₀ v) = (I₀.P v)⁻¹ * γ₀.map (I₀.φ v) * I₀.P v) ∧ (∀ i, Γ * T i = T i * (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E)) ∧ Γ * T₀ = T₀ * γ₀.map e := by
  intro I I₀ e xf a j S Λ x₀ T T' T₀ hAd γ hγ g₀ hg₀
  obtain ⟨he, hn, -, h1, h2, h3, hlat, -⟩ := hAd
  obtain ⟨c₀, ⟨δ, hδU, hδP, hδf⟩, rfl, hc₀K⟩ := hg₀
  have hδL := (mem_conj_iff I₀ x₀ c₀ δ hδf).1 hc₀K
  have hJ : I.Jᴴ = I.J := by
    have hH : (I.J.map (starRingEnd I.E))ᵀ = I.J := I.J_herm
    ext r s
    have := congrArg (fun M => M r s) hH
    simp only [Matrix.transpose_apply, Matrix.map_apply] at this
    rw [Matrix.conjTranspose_apply, ← this]
    rfl
  have hJ₀ : (I₀.J.map e).det ≠ 0 := by
    intro h
    apply I₀.J_det
    have h' : (e : I₀.E →+* I.E) I₀.J.det = 0 := by
      rw [RingHom.map_det]
      exact h
    simpa using h'
  have hsemi : Function.Semiconj e star star := he
  have hδU' := (mem_UJ_iff_flag_measures I₀.J δ).1 hδU
  obtain ⟨U, hU⟩ : ∃ U : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E,
      ∀ i, U i = T i * (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E) := ⟨_, fun _ => rfl⟩
  obtain ⟨U', hU'⟩ : ∃ U' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E,
      ∀ i, U' i = T' i * (((γ i)⁻¹ : GL (Fin (j i)) I.E) : Matrix (Fin (j i)) (Fin (j i)) I.E)ᴴ :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨U₀, hU₀⟩ : ∃ U₀ : Matrix (Fin I.n) (Fin I₀.n) I.E,
      U₀ = T₀ * (δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E).map e := ⟨_, rfl⟩
  have g1 : ∀ i k, (U i)ᴴ * I.J * U k = 0 ∧ (U' i)ᴴ * I.J * U' k = 0 ∧
      (i ≠ k → (U i)ᴴ * I.J * U' k = 0) := by
    intro i k
    obtain ⟨a1, a2, a3⟩ := h1 i k
    refine ⟨?_, ?_, fun hik => ?_⟩
    · rw [hU, hU, GlobalTheory.AdaptedMove.gram_mul, a1, Matrix.mul_zero, Matrix.zero_mul]
    · rw [hU', hU', GlobalTheory.AdaptedMove.gram_mul, a2, Matrix.mul_zero, Matrix.zero_mul]
    · rw [hU, hU', GlobalTheory.AdaptedMove.gram_mul, a3 hik, Matrix.mul_zero, Matrix.zero_mul]
  have g2 : ∀ i, (U i)ᴴ * I.J * U' i = 1 ∧ (U i)ᴴ * I.J * U₀ = 0 ∧ (U' i)ᴴ * I.J * U₀ = 0 := by
    intro i
    obtain ⟨b1, b2, b3⟩ := h2 i
    refine ⟨?_, ?_, ?_⟩
    · rw [hU, hU', GlobalTheory.AdaptedMove.gram_mul, b1, Matrix.mul_one, ← Matrix.conjTranspose_mul, Units.inv_mul,
        Matrix.conjTranspose_one]
    · rw [hU, hU₀, GlobalTheory.AdaptedMove.gram_mul, b2, Matrix.mul_zero, Matrix.zero_mul]
    · rw [hU', hU₀, GlobalTheory.AdaptedMove.gram_mul, b3, Matrix.mul_zero, Matrix.zero_mul]
  have g3 : U₀ᴴ * I.J * U₀ = I₀.J.map e := by
    rw [hU₀, GlobalTheory.AdaptedMove.gram_mul, h3, ← Matrix.conjTranspose_map _ hsemi]
    calc ((δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E)ᴴ).map e * I₀.J.map e * (δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E).map e
        = ((δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E)ᴴ * I₀.J * δ).map (e : I₀.E →+* I.E) := by
          rw [Matrix.map_mul, Matrix.map_mul]
          rfl
      _ = I₀.J.map e := by
          rw [hδU']
          rfl
  obtain ⟨Γ, hΓJ, hΓT, hΓT', hΓ₀⟩ :=
    GlobalTheory.FlagConj.exists_unitary_adapted hn I.J hJ (I₀.J.map e) hJ₀ T T' U U' T₀ U₀ h1 h2 h3 g1 g2 g3
  have hΓU : Γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J := (mem_UJ_iff_flag_measures I.J Γ).2 hΓJ
  obtain ⟨c, hc1, hc2⟩ := GlobalTheory.FlagConj.exists_point I Γ hΓU
  have hγf : ∀ i, ∀ u ∈ Λ i, (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E) *ᵥ u ∈ Λ i :=
    fun i u hu => (hγ i u).2 hu
  have hγb : ∀ i, ∀ u ∈ Λ i, (((γ i)⁻¹ : GL (Fin (j i)) I.E) : Matrix (Fin (j i)) (Fin (j i)) I.E) *ᵥ u ∈ Λ i := by
    intro i u hu
    apply (hγ i _).1
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    exact hu
  have hδf' : ∀ y ∈ lamX I₀ (1, x₀), (δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E) *ᵥ y ∈ lamX I₀ (1, x₀) := by
    intro y hy
    rw [← hδL, GlobalTheory.FlagConj.mem_ratIso]
    exact ⟨y, hy, rfl⟩
  have hδb : ∀ y ∈ lamX I₀ (1, x₀),
      ((δ⁻¹ : GL (Fin I₀.n) I₀.E) : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E) *ᵥ y ∈ lamX I₀ (1, x₀) := by
    intro y hy
    rw [← hδL, GlobalTheory.FlagConj.mem_ratIso] at hy
    obtain ⟨y', hy', rfl⟩ := hy
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    exact hy'
  have hT : ∀ i, (Γ : Matrix (Fin I.n) (Fin I.n) I.E) * T i = T i * (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E) :=
    fun i => (hΓT i).trans (hU i)
  have hT' : ∀ i, (Γ : Matrix (Fin I.n) (Fin I.n) I.E) * T' i =
      T' i * (((γ i)⁻¹ : GL (Fin (j i)) I.E) : Matrix (Fin (j i)) (Fin (j i)) I.E)ᴴ :=
    fun i => (hΓT' i).trans (hU' i)
  have hT₀ : (Γ : Matrix (Fin I.n) (Fin I.n) I.E) * T₀ = T₀ * (δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E).map e :=
    hΓ₀.trans hU₀
  have hΓi : (((Γ⁻¹ : GL (Fin I.n) I.E)) : Matrix (Fin I.n) (Fin I.n) I.E) * Γ = 1 := Units.inv_mul Γ
  have hTb : ∀ i, (((Γ⁻¹ : GL (Fin I.n) I.E)) : Matrix (Fin I.n) (Fin I.n) I.E) * T i =
      T i * (((γ i)⁻¹ : GL (Fin (j i)) I.E) : Matrix (Fin (j i)) (Fin (j i)) I.E) :=
    fun i => inv_mul_eq_mul_inv_of_mul_eq_mul _ _ _ _ _ hΓi (Units.mul_inv (γ i)) (hT i)
  have hT'b : ∀ i, (((Γ⁻¹ : GL (Fin I.n) I.E)) : Matrix (Fin I.n) (Fin I.n) I.E) * T' i =
      T' i * (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E)ᴴ := by
    intro i
    refine inv_mul_eq_mul_inv_of_mul_eq_mul _ _ _ _ _ hΓi ?_ (hT' i)
    rw [← Matrix.conjTranspose_mul, Units.mul_inv, Matrix.conjTranspose_one]
  have hT₀b : (((Γ⁻¹ : GL (Fin I.n) I.E)) : Matrix (Fin I.n) (Fin I.n) I.E) * T₀ =
      T₀ * (((δ⁻¹ : GL (Fin I₀.n) I₀.E)) : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E).map e := by
    refine inv_mul_eq_mul_inv_of_mul_eq_mul _ _ _ _ _ hΓi ?_ hT₀
    have hm : (δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E).map e *
        (((δ⁻¹ : GL (Fin I₀.n) I₀.E)) : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E).map e =
        ((δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E) *
          (((δ⁻¹ : GL (Fin I₀.n) I₀.E)) : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E)).map (e : I₀.E →+* I.E) :=
      (Matrix.map_mul).symm
    rw [hm, Units.mul_inv]
    exact Matrix.map_one _ (map_zero e) (map_one e)
  have hfw := lat_mulVec_lemma_3 I I₀ e xf j Λ x₀ T T' T₀ hlat Γ
    (fun i => (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E))
    (fun i => (((γ i)⁻¹ : GL (Fin (j i)) I.E) : Matrix (Fin (j i)) (Fin (j i)) I.E)) δ hγf hγb hδf' hT hT' hT₀
  have hbw := lat_mulVec_lemma_3 I I₀ e xf j Λ x₀ T T' T₀ hlat (((Γ⁻¹ : GL (Fin I.n) I.E)) : Matrix (Fin I.n) (Fin I.n) I.E)
    (fun i => (((γ i)⁻¹ : GL (Fin (j i)) I.E) : Matrix (Fin (j i)) (Fin (j i)) I.E))
    (fun i => (γ i : Matrix (Fin (j i)) (Fin (j i)) I.E))
    (((δ⁻¹ : GL (Fin I₀.n) I₀.E)) : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E) hγb hγf hδb hTb hT'b hT₀b
  have hLat : ratIso I Γ (lamX I (1, xf)) = lamX I (1, xf) := by
    ext z
    rw [GlobalTheory.FlagConj.mem_ratIso]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hfw y hy
    · intro hz
      refine ⟨(((Γ⁻¹ : GL (Fin I.n) I.E)) : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ z, hbw z hz, ?_⟩
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  exact ⟨c.1, ⟨c, ⟨Γ, hΓU, hc1, hc2⟩, rfl, (mem_conj_iff I xf c Γ hc2).2 hLat⟩,
    (Γ : Matrix (Fin I.n) (Fin I.n) I.E), (δ : Matrix (Fin I₀.n) (Fin I₀.n) I₀.E), hc1, hδP, hT, hT₀⟩

end GlobalTheory.LeviRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SizeQSaturatedIsotropicFlagPos
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

theorem satIn_of_trace (I : AutInst) (x : I.GA) (S : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (h : ∀ y, y ∈ S ↔ y ∈ lamX I x ∧ y ∈ Submodule.span I.E (S : Set (Fin I.n → I.E))) :
    GlobalTheory.IndefiniteRowSideFullHecke.SaturatedPerpDuality.SatIn I x S := by
  have := GlobalTheory.StepDualityCompare.totallyComplex I

  obtain ⟨q, hq⟩ := Submodule.exists_isCompl (Submodule.span I.E (S : Set (Fin I.n → I.E)))
  let φ : (Fin I.n → I.E) →ₗ[I.E] (Fin I.n → I.E) := q.subtype ∘ₗ Submodule.linearProjOfIsCompl q _ hq.symm
  have hker : LinearMap.ker φ = Submodule.span I.E (S : Set (Fin I.n → I.E)) := by
    rw [LinearMap.ker_comp_of_ker_eq_bot _ q.ker_subtype]
    exact Submodule.linearProjOfIsCompl_ker _
  have hX : ∀ v, IsUnit (frm I x v).det := GlobalTheory.StepDualityCompare.frm_det I x
  have hfg : (lamX I x).FG := (GlobalTheory.PointLattice.lamX_selfDual I x).2.1

  have hsat := (Formalism.HN.htImage I.E (Fin I.n → I.E) (Fin I.n) (Fin I.n → I.E) (Fin I.n) (bas I) (frm I x)
    (bas I) (frm I x) hX hX φ (lamX I x) hfg).1
  have hS : lamX I x ⊓ (LinearMap.ker φ).restrictScalars (𝓞 I.E) = S := by
    ext y
    rw [hker, Submodule.mem_inf, Submodule.restrictScalars_mem, h]
  rw [hS] at hsat
  exact hsat

theorem sizeQ_flag_pos : ∀ (I : AutInst) (x : I.GA) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I x) j S → ∀ i : Fin a, 0 < Formalism.HN.sizeQ (bas I) (frm I x) (S i.succ) (S i.castSucc) := by
  intro I x a j S hS i
  obtain ⟨-, hmono, -, htr, -⟩ := hS
  have hfg : (lamX I x).FG := (GlobalTheory.PointLattice.lamX_selfDual I x).2.1

  have hsat : GlobalTheory.IndefiniteRowSideFullHecke.SaturatedPerpDuality.SatIn I x (S i.castSucc) := satIn_of_trace I x _ (htr i.castSucc)
  have hle : S i.succ ≤ lamX I x := fun y hy => ((htr i.succ y).1 hy).1
  have hmn : S i.castSucc ≤ S i.succ := hmono (Fin.castSucc_le_succ i)
  have hpos := GlobalTheory.StepDualityCompare.htQ_pos I x hfg _ _ hsat hle hmn
  unfold Formalism.HN.sizeQ
  exact Real.rpow_pos_of_pos hpos _

end GlobalTheory.LeviIso
end

