module

public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.CgSplit
section
namespace PositivityTheory.HtPt.Cg

open Matrix

theorem left_inv_of_residue {A : Type} [CommRing A] [IsLocalRing A] {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (M : Matrix m n A)
    (h : ∀ u, (M.map (IsLocalRing.residue A)).mulVec u = 0 → u = 0) : ∃ N : Matrix n m A, N * M = 1 := by
  have hi : LinearMap.ker (Matrix.toLin' (M.map (IsLocalRing.residue A))) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro u hu
    exact h u (by simpa using hu)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hi
  have h1 : LinearMap.toMatrix' g * M.map (IsLocalRing.residue A) = 1 := by
    have := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  choose l hl using fun i j => IsLocalRing.residue_surjective (LinearMap.toMatrix' g i j)
  have h2 : (Matrix.of l * M).map (IsLocalRing.residue A) = 1 := by
    rw [Matrix.map_mul, ← h1]
    congr 1
    ext i j
    exact hl i j
  have h3 : IsUnit (Matrix.of l * M).det := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply, h2, det_one]
    exact one_ne_zero
  exact ⟨(Matrix.of l * M)⁻¹ * Matrix.of l, by rw [Matrix.mul_assoc, nonsing_inv_mul _ h3]⟩

theorem split_local : ∀ (A : Type) [CommRing A] [IsLocalRing A] (d : ℕ) (h a S : Matrix (Fin d) (Fin d) A), a * h - h.transpose * S * h - h.transpose * a.transpose = 0 → (∀ u : Fin d → IsLocalRing.ResidueField A, (h.map (IsLocalRing.residue A)).mulVec u = 0 → (a.transpose.map (IsLocalRing.residue A)).mulVec u = 0 → u = 0) → ∃ r₁ r₂ s₁ s₂ : Matrix (Fin d) (Fin d) A, r₁ * h + r₂ * a.transpose = 1 ∧ (a - h.transpose * S) * s₁ - h.transpose * s₂ = 1 ∧ h * r₁ + s₁ * (a - h.transpose * S) = 1 ∧ h * r₂ - s₁ * h.transpose = 0 ∧ a.transpose * r₁ + s₂ * (a - h.transpose * S) = 0 ∧ a.transpose * r₂ - s₂ * h.transpose = 1 := by
  intro A _ _ d h a S hiso hinj
  obtain ⟨N, hN⟩ := left_inv_of_residue (fromRows h a.transpose) (fun u hu => by
    rw [fromRows_map, fromRows_mulVec] at hu
    exact hinj u (funext fun i => congrFun hu (Sum.inl i)) (funext fun i => congrFun hu (Sum.inr i)))
  obtain ⟨x, y, rfl⟩ : ∃ x y, N = fromCols x y := ⟨_, _, (fromCols_toCols N).symm⟩
  rw [fromCols_mul_fromRows] at hN
  have hT : h.transpose * x.transpose + a * y.transpose = 1 := by
    have := congrArg Matrix.transpose hN
    simpa [transpose_add, transpose_mul] using this
  set b := a - h.transpose * S with hb
  set s₁ := y.transpose
  set s₂ := -(x.transpose + S * y.transpose) with hs₂
  have e2 : b * s₁ - h.transpose * s₂ = 1 := by
    rw [← hT, hb, hs₂]; noncomm_ring
  have e0 : b * h - h.transpose * a.transpose = 0 := by
    rw [← hiso, hb]; noncomm_ring
  set w := x * s₁ + y * s₂ with hw
  have e1 : (x - w * b) * h + (y + w * h.transpose) * a.transpose = 1 := by
    have : (x - w * b) * h + (y + w * h.transpose) * a.transpose =
      (x * h + y * a.transpose) - w * (b * h - h.transpose * a.transpose) := by noncomm_ring
    rw [this, hN, e0]; simp
  have e3 : (x - w * b) * s₁ + (y + w * h.transpose) * s₂ = 0 := by
    have : (x - w * b) * s₁ + (y + w * h.transpose) * s₂ =
      (x * s₁ + y * s₂) - w * (b * s₁ - h.transpose * s₂) := by noncomm_ring
    rw [this, e2, ← hw]; simp
  have hNM : fromBlocks (x - w * b) (y + w * h.transpose) b (-h.transpose) *
      fromBlocks h s₁ a.transpose s₂ = 1 := by
    rw [fromBlocks_multiply, e1, e3, ← fromBlocks_one]
    congr 1
    · rw [← e0]; noncomm_ring
    · rw [← e2]; noncomm_ring
  have hMN := mul_eq_one_comm.1 hNM
  rw [fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj] at hMN
  obtain ⟨f1, f2, f3, f4⟩ := hMN
  refine ⟨_, _, s₁, s₂, e1, e2, f1, ?_, f3, ?_⟩
  · rw [← f2]; noncomm_ring
  · rw [← f4]; noncomm_ring

end PositivityTheory.HtPt.Cg
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.DvrOfHeightOne
section
namespace PositivityTheory.HtPt.Gc

theorem dvr_of_height_one {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (q : Ideal A) [q.IsPrime] (h1 : q.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime q) := by
  have hdim : ringKrullDim (Localization.AtPrime q) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q, h1]; rfl
  have hnf : ¬ IsField (Localization.AtPrime q) := fun hf => by
    rw [ringKrullDim_eq_zero_of_isField hf] at hdim
    exact zero_ne_one hdim
  have hic : IsIntegrallyClosed (Localization.AtPrime q) :=
    isIntegrallyClosed_of_isLocalization _ q.primeCompl q.primeCompl_le_nonZeroDivisors
  have hk : Ring.KrullDimLE 1 (Localization.AtPrime q) := by
    rw [Ring.krullDimLE_iff, hdim]; rfl
  have hD : IsDedekindDomain (Localization.AtPrime q) := by
    have : Ring.DimensionLEOne (Localization.AtPrime q) :=
      ⟨fun {P} hP hP' => (Ring.krullDimLE_one_iff_of_noZeroDivisors.1 hk) P hP hP'⟩
    exact {}
  exact ((IsDiscreteValuationRing.TFAE (Localization.AtPrime q) hnf).out 1 3).2 hD

end PositivityTheory.HtPt.Gc
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.EqOfProdEq
section
open scoped Matrix TensorProduct
open Matrix

namespace PositivityTheory.HtPt.Rh

theorem epi : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B], (∀ b : B, b ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] b) → Function.Surjective (algebraMap A B) := by
  intro A B _ _ _ _ h
  exact Algebra.isEpi_iff_surjective_algebraMap_of_finite.mp
    ((Algebra.isEpi_iff_forall_one_tmul_eq A B).mpr fun b => (h b).symm)

theorem eq_of_prod_eq {T : Type} [Fintype T] (f g : T → NNReal) (hle : ∀ t, f t ≤ g t)
    (h : ∏ t, f t = ∏ t, g t) (h0 : ∏ t, f t ≠ 0) (t : T) : f t = g t := by
  by_contra hne
  have hpos : ∀ i ∈ Finset.univ, 0 < f i := fun i _ =>
    pos_iff_ne_zero.mpr ((Finset.prod_ne_zero_iff.mp h0) i (Finset.mem_univ i))
  have hlt := Finset.prod_lt_prod₀ hpos (fun i _ => hle i)
    ⟨t, Finset.mem_univ t, lt_of_le_of_ne (hle t) hne⟩
  exact hlt.ne h

theorem grcount : ∀ (T S : Type) [Fintype T] [Fintype S] (a b : ℕ), 0 < a → 0 < b → ∀ (x D d : T → S → NNReal) (r : S → NNReal) (cA cN cO : NNReal), cN ≠ 0 → (∀ t s, x t s ≤ D t s) → ∏ t, ∏ s, D t s = cA → (∏ t, ∏ s, x t s) ^ (a * b) = cN ^ 2 → cA ^ (a * b) = cN ^ 2 → (∀ s, ∏ t, d t s ≤ r s) → ∏ s, r s = cO → ∏ t, ∏ s, d t s = (∏ t, ∏ s, x t s) ^ b → cO ^ a = cN ^ 2 → (∀ t s, D t s = x t s) ∧ ∀ s, ∏ t, d t s = r s := by
  intro T S _ _ a b ha hb x D d r cA cN cO hcN hxD hD hx hA hd hr hdx hOa
  have hab : a * b ≠ 0 := (Nat.mul_pos ha hb).ne'
  have hX : ∏ t, ∏ s, x t s = ∏ t, ∏ s, D t s := by
    rw [hD]
    exact (pow_left_inj₀ (by positivity) (by positivity) hab).mp (hx.trans hA.symm)
  have hX0 : ∏ t, ∏ s, x t s ≠ 0 := by
    intro h0
    rw [h0, zero_pow hab] at hx
    exact pow_ne_zero 2 hcN hx.symm
  have hrow : ∀ t, ∏ s, x t s = ∏ s, D t s :=
    PositivityTheory.HtPt.Rh.eq_of_prod_eq (fun t => ∏ s, x t s) (fun t => ∏ s, D t s)
      (fun t => Finset.prod_le_prod' fun s _ => hxD t s) hX hX0
  have hrow0 : ∀ t, ∏ s, x t s ≠ 0 := fun t =>
    (Finset.prod_ne_zero_iff.mp hX0) t (Finset.mem_univ t)
  have hxD' : ∀ t s, D t s = x t s := fun t s =>
    (PositivityTheory.HtPt.Rh.eq_of_prod_eq (x t) (D t) (hxD t) (hrow t) (hrow0 t) s).symm
  have hO : cO = ∏ t, ∏ s, d t s := by
    rw [hdx]
    apply (pow_left_inj₀ (by positivity) (by positivity) ha.ne').mp
    rw [hOa, ← pow_mul, mul_comm b a, hx]
  have hcol : ∏ s, ∏ t, d t s = ∏ s, r s := by
    rw [hr, hO, Finset.prod_comm]
  have hcol0 : ∏ s, ∏ t, d t s ≠ 0 := by
    rw [Finset.prod_comm, hdx]
    exact pow_ne_zero _ hX0
  exact ⟨hxD', PositivityTheory.HtPt.Rh.eq_of_prod_eq (fun s => ∏ t, d t s) r hd hcol hcol0⟩

end PositivityTheory.HtPt.Rh
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLieA
section
noncomputable section

namespace PositivityTheory.HtPt.Htat.Lie

open TensorProduct

theorem bijective_of_cover {R M N J : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : J → R) (hf : Ideal.span (Set.range f) = ⊤) (φ : M →ₗ[R] N)
    (h : ∀ i, ∃ (Q : Type) (_ : AddCommGroup Q) (_ : Module R Q) (a : N →ₗ[R] Q),
      IsLocalizedModule (Submonoid.powers (f i)) a ∧ IsLocalizedModule (Submonoid.powers (f i)) (a ∘ₗ φ)) :
    Function.Bijective φ := by
  constructor
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro m hm
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ _ hf m ?_
    rintro ⟨_, i, rfl⟩
    obtain ⟨Q, _, _, a, -, h2⟩ := h i
    have h0 : (a ∘ₗ φ) m = (a ∘ₗ φ) 0 := by
      rw [LinearMap.comp_apply, LinearMap.mem_ker.1 hm, map_zero, map_zero]
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers (f i)) h0
    refine ⟨k, ?_⟩
    simpa [Submonoid.smul_def] using hk
  · intro n
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem (LinearMap.range φ) _ hf n ?_
    rintro ⟨_, i, rfl⟩
    obtain ⟨Q, _, _, a, h1, h2⟩ := h i
    obtain ⟨⟨m, ⟨_, k, rfl⟩⟩, hk⟩ := IsLocalizedModule.surj (Submonoid.powers (f i)) (a ∘ₗ φ) (a n)
    have h0 : a (f i ^ k • n) = a (φ m) := by
      rw [map_smul]
      exact hk
    obtain ⟨⟨_, l, rfl⟩, hl⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers (f i)) h0
    refine ⟨l + k, f i ^ l • m, ?_⟩
    have hl' : f i ^ l • f i ^ k • n = f i ^ l • φ m := hl
    show φ (f i ^ l • m) = f i ^ (l + k) • n
    rw [map_smul, pow_add, mul_smul, hl']

theorem isBaseChange_hom {R A C P : Type} [CommRing R] [CommRing A] [CommRing C] [Algebra R A] [Algebra R C]
    [Algebra A C] [IsScalarTower R A C] [AddCommGroup P] [Module R P] [Module A P] [IsScalarTower R A P]
    [Module.Finite A P] [Module.Projective A P]
    (hA : ∀ (φ : P →ₗ[R] A) (a : A) p, φ (a • p) = a * φ p)
    (hC : ∀ (φ : P →ₗ[R] C) (a : A) p, φ (a • p) = algebraMap A C a * φ p)
    (g : (P →ₗ[R] A) →ₗ[A] (P →ₗ[R] C)) (hg : ∀ φ p, g φ p = algebraMap A C (φ p)) : IsBaseChange C g := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' A P
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  let b : Fin n → P := fun k => π (fun j => if k = j then 1 else 0)
  have hexp : ∀ p : P, ∑ k, s p k • b k = p := by
    intro p
    have h1 := LinearMap.congr_fun hs p
    have h2 := LinearMap.pi_apply_eq_sum_univ π (s p)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h1
    rw [h1] at h2
    exact h2.symm
  let co : Fin n → (P →ₗ[R] A) := fun k => (LinearMap.proj k ∘ₗ s).restrictScalars R
  have hco : ∀ k p, co k p = s p k := fun _ _ => rfl
  have hsum : ∀ φ : P →ₗ[R] A, ∑ k, φ (b k) • co k = φ := by
    intro φ
    ext p
    conv_rhs => rw [← hexp p]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, hA, hco, mul_comm]
  let θ : C ⊗[A] (P →ₗ[R] A) →ₗ[C] (P →ₗ[R] C) := g.liftBaseChange C
  have hθ : ∀ c φ, θ (c ⊗ₜ φ) = c • g φ := fun c φ => LinearMap.liftBaseChange_tmul _ _ _ _
  let inv : (P →ₗ[R] C) → C ⊗[A] (P →ₗ[R] A) := fun ψ => ∑ k, ψ (b k) ⊗ₜ co k
  have hl : ∀ z, inv (θ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp [inv]
    | add x y hx hy =>
      have : inv (θ (x + y)) = inv (θ x) + inv (θ y) := by
        simp [inv, add_tmul, Finset.sum_add_distrib]
      rw [this, hx, hy]
    | tmul c φ =>
      rw [hθ]
      conv_rhs => rw [← hsum φ, tmul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [LinearMap.smul_apply, hg, tmul_smul, smul_tmul', Algebra.smul_def (φ (b k)), smul_eq_mul, mul_comm]
  have hr : ∀ ψ, θ (inv ψ) = ψ := by
    intro ψ
    ext p
    conv_rhs => rw [← hexp p]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [inv, map_sum, hθ, LinearMap.sum_apply, LinearMap.smul_apply, hg, hco, hC, smul_eq_mul, mul_comm]
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective θ
    ⟨Function.LeftInverse.injective hl, Function.RightInverse.surjective hr⟩) fun φ => ?_
  exact (hθ 1 φ).trans (one_smul _ _)

end PositivityTheory.HtPt.Htat.Lie
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MulEqSmulOneSymm
section
open scoped Matrix TensorProduct
open Matrix

namespace PositivityTheory.HtPt.Rh

theorem mul_eq_smul_one_symm {R n : Type} [CommRing R] [IsDomain R] [Fintype n] [DecidableEq n]
    {A B : Matrix n n R} {c : R} (hc : c ≠ 0) (h : A * B = c • (1 : Matrix n n R)) :
    B * A = c • (1 : Matrix n n R) := by
  have hd : B.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det h
    rw [det_mul, h0, mul_zero, det_smul, det_one, mul_one] at this
    exact pow_ne_zero _ hc this.symm
  have h1 : (B * A - c • (1 : Matrix n n R)) * B = 0 := by
    rw [sub_mul, Matrix.mul_assoc, h]; simp
  have h2 : B.det • (B * A - c • (1 : Matrix n n R)) = 0 := by
    have := congrArg (· * B.adjugate) h1
    simpa only [Matrix.mul_assoc, mul_adjugate, Matrix.mul_smul, Matrix.mul_one, Matrix.zero_mul]
      using this
  exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_left hd)

theorem gp_mat : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → ∀ (g : ℕ) (Ht Bt : Matrix (Fin g) (Fin g ⊕ Fin g) R) (E : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R) (cp : R), cp ≠ 0 → Eᵀ = -E → IsUnit E.det → Btᵀ * Ht - Htᵀ * Bt = cp • E → let φ := algebraMap R C; let intg : (Fin g → C) → Prop := fun w => ∀ k, v (w k) ≤ 1; let hb : Matrix (Fin g ⊕ Fin g) (Fin g) C := ((Eᵀ)⁻¹ * Htᵀ).map φ; v (φ (Matrix.fromRows Ht Bt).det) = v (φ cp) ^ g ∧ (∀ x : Fin g ⊕ Fin g → C, ((Ht.map φ) *ᵥ x = 0 ∧ intg ((Bt.map φ) *ᵥ x)) ↔ ∃ w, intg w ∧ x = (φ cp)⁻¹ • (hb *ᵥ w)) ∧ (∀ w, intg w → ∃ x : Fin g ⊕ Fin g → C, (Ht.map φ) *ᵥ x = w ∧ (Bt.map φ) *ᵥ x = 0) ∧ (∀ l : Fin g ⊕ Fin g → R, cp • l ∈ Submodule.span R (Set.range fun k => Matrix.fromRows Ht Bt k)) := by
  intro C _ v R _ _ hv g Ht Bt E cp hcp hE hEu hform φ intg hb
  have : IsDomain R := hv.hom_inj.isDomain _
  have hcp' : φ cp ≠ 0 := fun h => hcp (hv.hom_inj (by rw [map_zero]; exact h))
  have hEt : IsUnit (Eᵀ).det := by rwa [det_transpose]
  set U : Matrix (Fin g ⊕ Fin g) (Fin g) R := -((Eᵀ)⁻¹ * Btᵀ) with hU
  set W : Matrix (Fin g ⊕ Fin g) (Fin g) R := (Eᵀ)⁻¹ * Htᵀ with hW
  have h1 : U * Ht + W * Bt = cp • (1 : Matrix _ _ R) := by
    have : U * Ht + W * Bt = (Eᵀ)⁻¹ * (-(Btᵀ * Ht - Htᵀ * Bt)) := by
      rw [hU, hW, neg_sub, Matrix.mul_sub, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc]
      abel
    rw [this, hform, ← smul_neg, ← hE, Matrix.mul_smul, nonsing_inv_mul _ hEt]
  have h2 : fromCols U W * fromRows Ht Bt = cp • (1 : Matrix _ _ R) := by
    rw [fromCols_mul_fromRows, h1]
  have h3 := mul_eq_smul_one_symm hcp h2
  rw [fromRows_mul_fromCols, ← fromBlocks_one, fromBlocks_smul, fromBlocks_inj] at h3
  obtain ⟨a11, a12, a21, a22⟩ := h3
  rw [smul_zero] at a12 a21
  have hone : ∀ {n : Type} [DecidableEq n], (cp • (1 : Matrix n n R)).map φ = φ cp • (1 : Matrix n n C) := by
    intro n _
    ext i j
    by_cases h : i = j <;> simp [h]
  have b1 := congrArg (·.map φ) h1
  have b11 := congrArg (·.map φ) a11
  have b12 := congrArg (·.map φ) a12
  have b21 := congrArg (·.map φ) a21
  have b22 := congrArg (·.map φ) a22
  simp only [Matrix.map_add _ (map_add φ), Matrix.map_mul, hone, Matrix.map_zero _ (map_zero φ)]
    at b1 b11 b12 b21 b22
  refine ⟨?_, fun x => ⟨fun hx => ⟨_, hx.2, ?_⟩, ?_⟩, fun w _ => ⟨(φ cp)⁻¹ • (U.map φ *ᵥ w), ?_, ?_⟩,
    fun l => ?_⟩
  · have hJ : (fromRows Ht Bt)ᵀ * Matrix.J (Fin g) R * fromRows Ht Bt = cp • E := by
      rw [← hform, Matrix.J, transpose_fromRows, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
      simp [sub_eq_add_neg]
    have hd := congrArg (fun M => v (φ M.det)) hJ
    simp only [det_mul, det_transpose, det_smul, map_mul, map_pow, Fintype.card_sum,
      Fintype.card_fin] at hd
    rw [hv.one_of_isUnit (Matrix.isUnit_det_J (Fin g) R), hv.one_of_isUnit hEu, mul_one, mul_one,
      pow_add] at hd
    exact (mul_self_inj zero_le zero_le).1 hd
  · have := congrArg (· *ᵥ x) b1
    simp only [add_mulVec, ← mulVec_mulVec, hx.1, mulVec_zero, zero_add, smul_mulVec,
      one_mulVec] at this
    change x = (φ cp)⁻¹ • (W.map φ *ᵥ _)
    rw [this, inv_smul_smul₀ hcp']
  · rintro ⟨w, hw, rfl⟩
    change Ht.map φ *ᵥ ((φ cp)⁻¹ • (W.map φ *ᵥ w)) = 0 ∧
      intg (Bt.map φ *ᵥ ((φ cp)⁻¹ • (W.map φ *ᵥ w)))
    rw [mulVec_smul, mulVec_smul, mulVec_mulVec, mulVec_mulVec, b12, b22, zero_mulVec, smul_zero,
      smul_mulVec, one_mulVec, inv_smul_smul₀ hcp']
    exact ⟨rfl, hw⟩
  · rw [mulVec_smul, mulVec_mulVec, b11, smul_mulVec, one_mulVec, inv_smul_smul₀ hcp']
  · rw [mulVec_smul, mulVec_mulVec, b21, zero_mulVec, smul_zero]
  · have : cp • l = (l ᵥ* fromCols U W) ᵥ* fromRows Ht Bt := by
      rw [vecMul_vecMul, h2, vecMul_smul, vecMul_one]
    rw [this, vecMul_eq_sum]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

end PositivityTheory.HtPt.Rh
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.PmonoCount
section
open scoped Matrix TensorProduct
open Matrix

namespace PositivityTheory.HtPt.Pmono

lemma prod_digits_sq (p f : ℕ) (P : NNReal) (y : Fin f → NNReal) (hy : ∀ n, y n ^ (p - 1) = P) :
    (∏ d : Fin f → Fin p, ∏ n, y n ^ (d n : ℕ)) ^ 2 = P ^ (f * p ^ f) := by
  have hrev : ∏ d : Fin f → Fin p, ∏ n, y n ^ ((Fin.rev (d n) : Fin p) : ℕ) =
      ∏ d : Fin f → Fin p, ∏ n, y n ^ (d n : ℕ) :=
    Fintype.prod_equiv (Equiv.piCongrRight fun _ => Fin.revPerm) _ _ (fun d => rfl)
  rw [sq]
  nth_rewrite 2 [← hrev]
  rw [← Finset.prod_mul_distrib]
  have hterm : ∀ d : Fin f → Fin p,
      (∏ n, y n ^ (d n : ℕ)) * ∏ n, y n ^ ((Fin.rev (d n) : Fin p) : ℕ) = P ^ f := by
    intro d
    rw [← Finset.prod_mul_distrib]
    have h : ∀ n, y n ^ (d n : ℕ) * y n ^ ((Fin.rev (d n) : Fin p) : ℕ) = P := by
      intro n
      rw [← pow_add, Fin.val_rev, ← hy n]
      congr 1
      have := (d n).isLt
      omega
    rw [Finset.prod_congr rfl (fun n _ => h n)]
    simp
  rw [Finset.prod_congr rfl (fun d _ => hterm d)]
  simp [← pow_mul, mul_comm]

lemma eq_of_prod_eq {ι : Type} [Fintype ι] [DecidableEq ι] (a b : ι → NNReal) (ha : ∀ i, 0 < a i)
    (hab : ∀ i, a i ≤ b i) (h : ∏ i, b i = ∏ i, a i) (i : ι) : b i = a i := by
  refine le_antisymm ?_ (hab i)
  have hQ : 0 < ∏ j ∈ Finset.univ.erase i, a j := Finset.prod_pos (fun j _ => ha j)
  have h1 : ∏ j ∈ Finset.univ.erase i, a j ≤ ∏ j ∈ Finset.univ.erase i, b j :=
    Finset.prod_le_prod' (fun j _ => hab j)
  have h2 : b i * ∏ j ∈ Finset.univ.erase i, a j ≤ a i * ∏ j ∈ Finset.univ.erase i, a j :=
    calc b i * ∏ j ∈ Finset.univ.erase i, a j ≤ b i * ∏ j ∈ Finset.univ.erase i, b j :=
          mul_le_mul' le_rfl h1
      _ = ∏ j, b j := Finset.mul_prod_erase _ _ (Finset.mem_univ i)
      _ = ∏ j, a j := h
      _ = a i * ∏ j ∈ Finset.univ.erase i, a j := (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  exact le_of_mul_le_mul_right h2 hQ

theorem count : ∀ (p f : ℕ), 2 ≤ p → ∀ (P : NNReal), P ≠ 0 → ∀ (x xD : Fin f → NNReal) (X XD : (Fin f → Fin p) → NNReal), (∀ n, (x n * xD n) ^ (p - 1) = P) → (∀ d, ∏ n, x n ^ (d n : ℕ) ≤ X d) → (∀ d, ∏ n, xD n ^ (d n : ℕ) ≤ XD d) → (∏ d, X d * XD d) ^ 2 = P ^ (f * p ^ f) → ∀ d, X d = ∏ n, x n ^ (d n : ℕ) ∧ XD d = ∏ n, xD n ^ (d n : ℕ) := by
  intro p f hp P hP x xD X XD hxy hX hXD hprod d
  have hne : ∀ n, x n ≠ 0 ∧ xD n ≠ 0 := by
    intro n
    have hmul : x n * xD n ≠ 0 := by
      intro h0
      have h := hxy n
      rw [h0, zero_pow (by omega)] at h
      exact hP h.symm
    exact ⟨left_ne_zero_of_mul hmul, right_ne_zero_of_mul hmul⟩
  have hApos : ∀ d : Fin f → Fin p, 0 < ∏ n, x n ^ (d n : ℕ) :=
    fun d => Finset.prod_pos (fun n _ => pow_pos (pos_iff_ne_zero.mpr (hne n).1) _)
  have hBpos : ∀ d : Fin f → Fin p, 0 < ∏ n, xD n ^ (d n : ℕ) :=
    fun d => Finset.prod_pos (fun n _ => pow_pos (pos_iff_ne_zero.mpr (hne n).2) _)
  have hsq : (∏ d : Fin f → Fin p, (∏ n, x n ^ (d n : ℕ)) * ∏ n, xD n ^ (d n : ℕ)) ^ 2 =
      P ^ (f * p ^ f) := by
    rw [← PositivityTheory.HtPt.Pmono.prod_digits_sq p f P (fun n => x n * xD n) hxy]
    congr 1
    refine Finset.prod_congr rfl fun d _ => ?_
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun n _ => (mul_pow _ _ _).symm
  have heq : ∏ d, X d * XD d = ∏ d : Fin f → Fin p, (∏ n, x n ^ (d n : ℕ)) * ∏ n, xD n ^ (d n : ℕ) :=
    (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp (hprod.trans hsq.symm)
  have hd := PositivityTheory.HtPt.Pmono.eq_of_prod_eq
    (fun d : Fin f → Fin p => (∏ n, x n ^ (d n : ℕ)) * ∏ n, xD n ^ (d n : ℕ))
    (fun d => X d * XD d) (fun d => mul_pos (hApos d) (hBpos d))
    (fun d => mul_le_mul' (hX d) (hXD d)) heq d
  have hXDpos : 0 < XD d := lt_of_lt_of_le (hBpos d) (hXD d)
  have hXpos : 0 < X d := lt_of_lt_of_le (hApos d) (hX d)
  constructor
  · refine le_antisymm ?_ (hX d)
    have h1 : X d * XD d ≤ (∏ n, x n ^ (d n : ℕ)) * XD d :=
      hd.le.trans (mul_le_mul' le_rfl (hXD d))
    exact le_of_mul_le_mul_right h1 hXDpos
  · refine le_antisymm ?_ (hXD d)
    have h1 : X d * XD d ≤ X d * ∏ n, xD n ^ (d n : ℕ) :=
      hd.le.trans (mul_le_mul' (hX d) le_rfl)
    exact le_of_mul_le_mul_left h1 hXpos

end PositivityTheory.HtPt.Pmono
end

