module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvPowSubNsmulMemAugIdealSq
section
open TensorProduct Polynomial

namespace GlobalTheory

theorem convPow_sub_nsmul_mem_augIdeal_sq : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (ε : B →ₐ[A] A) (Δ : B →ₐ[A] B ⊗[A] B) (α : ℕ → (B →ₐ[A] B)), (Algebra.TensorProduct.lift ((Algebra.ofId A B).comp ε) (AlgHom.id A B) (fun _ _ => Commute.all _ _)).comp Δ = AlgHom.id A B → (Algebra.TensorProduct.lift (AlgHom.id A B) ((Algebra.ofId A B).comp ε) (fun _ _ => Commute.all _ _)).comp Δ = AlgHom.id A B → α 0 = (Algebra.ofId A B).comp ε → (∀ n, α (n+1) = (Algebra.TensorProduct.lift (α n) (AlgHom.id A B) (fun _ _ => Commute.all _ _)).comp Δ) → ∀ n, ∀ x ∈ RingHom.ker ε, α n x - (n : B) * x ∈ (RingHom.ker ε) ^ 2 := by
  intro A B _ _ _ ε Δ α hL hR h0 hS
  have hεu : ∀ a : A, ε (algebraMap A B a) = a := fun a => by simp
  have hL' : ∀ b, Algebra.TensorProduct.lift ((Algebra.ofId A B).comp ε) (AlgHom.id A B)
      (fun _ _ => Commute.all _ _) (Δ b) = b := fun b => by
    simpa only [AlgHom.comp_apply, AlgHom.id_apply] using DFunLike.congr_fun hL b
  have hR' : ∀ b, Algebra.TensorProduct.lift (AlgHom.id A B) ((Algebra.ofId A B).comp ε)
      (fun _ _ => Commute.all _ _) (Δ b) = b := fun b => by
    simpa only [AlgHom.comp_apply, AlgHom.id_apply] using DFunLike.congr_fun hR b

  have hε : ∀ n b, ε (α n b) = ε b := by
    intro n
    induction n with
    | zero => intro b; rw [h0]; simp [hεu]
    | succ n ih =>
      intro b
      have key : ∀ t : B ⊗[A] B,
          ε (Algebra.TensorProduct.lift (α n) (AlgHom.id A B) (fun _ _ => Commute.all _ _) t) =
          ε (Algebra.TensorProduct.lift ((Algebra.ofId A B).comp ε) (AlgHom.id A B)
            (fun _ _ => Commute.all _ _) t) := by
        intro t
        induction t using TensorProduct.induction_on with
        | zero => simp
        | tmul b c => simp [Algebra.TensorProduct.lift_tmul, ih, hεu]
        | add s t hs ht => simp only [map_add (f := _), hs, ht]
      rw [hS n, AlgHom.comp_apply, key, hL' b]

  have hright : ∀ (ψ : B →ₐ[A] B) (t : B ⊗[A] B),
      Algebra.TensorProduct.lift ψ ((Algebra.ofId A B).comp ε) (fun _ _ => Commute.all _ _) t =
      ψ (Algebra.TensorProduct.lift (AlgHom.id A B) ((Algebra.ofId A B).comp ε)
        (fun _ _ => Commute.all _ _) t) := by
    intro ψ t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b c => simp [Algebra.TensorProduct.lift_tmul]
    | add s t hs ht => simp only [map_add (f := _), hs, ht]

  have gen : ∀ (φ : B →ₐ[A] B), (∀ b, ε (φ b) = ε b) → ∀ t : B ⊗[A] B,
      Algebra.TensorProduct.lift φ (AlgHom.id A B) (fun _ _ => Commute.all _ _) t
        - Algebra.TensorProduct.lift ((Algebra.ofId A B).comp ε) (AlgHom.id A B)
            (fun _ _ => Commute.all _ _) t
        - Algebra.TensorProduct.lift φ ((Algebra.ofId A B).comp ε) (fun _ _ => Commute.all _ _) t
        + Algebra.TensorProduct.lift ((Algebra.ofId A B).comp ε) ((Algebra.ofId A B).comp ε)
            (fun _ _ => Commute.all _ _) t ∈ RingHom.ker ε ^ 2 := by
    intro φ hφ t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b c =>
      simp only [Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, AlgHom.id_apply,
        Algebra.ofId_apply]
      have e : φ b * c - algebraMap A B (ε b) * c - φ b * algebraMap A B (ε c)
          + algebraMap A B (ε b) * algebraMap A B (ε c)
          = (φ b - algebraMap A B (ε b)) * (c - algebraMap A B (ε c)) := by ring
      rw [e, sq]
      exact Ideal.mul_mem_mul (by rw [RingHom.mem_ker]; simp [hφ, hεu])
        (by rw [RingHom.mem_ker]; simp [hεu])
    | add s t hs ht =>
      have e := add_mem hs ht
      simp only [map_add (f := _)]
      convert e using 1
      abel
  intro n
  induction n with
  | zero =>
    intro x hx
    rw [h0]
    simp [RingHom.mem_ker.mp hx]
  | succ n ih =>
    intro x hx
    have E := gen (α n) (hε n) (Δ x)
    rw [hL' x, hright (α n) (Δ x), hright ((Algebra.ofId A B).comp ε) (Δ x), hR' x] at E
    have hx0 : ε x = 0 := by simpa using hx
    have h4 : ((Algebra.ofId A B).comp ε) x = 0 := by simp [hx0]
    rw [h4, add_zero] at E
    rw [hS n, AlgHom.comp_apply]
    convert add_mem E (ih x hx) using 1
    push_cast
    ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentMapInjectiveOfSquarePresentationAtPoint
section
open scoped TensorProduct

namespace GlobalTheory.CotangentSquare

open MvPolynomial

variable {O B σ : Type} [CommRing O] [CommRing B]

def firstOrderKer (η : MvPolynomial σ B →+* O) : Ideal (MvPolynomial σ B) where
  carrier := {F | η F = 0 ∧ ∀ l, η (pderiv l F) = 0}
  add_mem' := by
    rintro F G ⟨hF, hF'⟩ ⟨hG, hG'⟩
    exact ⟨by simp [hF, hG], fun l => by simp [hF' l, hG' l]⟩
  zero_mem' := ⟨by simp, fun l => by simp⟩
  smul_mem' := by
    rintro G F ⟨hF, hF'⟩
    exact ⟨by simp [hF], fun l => by simp [pderiv_mul, hF, hF' l]⟩

theorem pderiv_comb [Fintype σ] (η : MvPolynomial σ B →+* O) (f g : σ → MvPolynomial σ B)
    (hf : ∀ i, η (f i) = 0) (k : MvPolynomial σ B) (hk : k ∈ firstOrderKer η) (l : σ) :
    η (pderiv l (∑ i, g i * f i + k)) = ∑ i, η (g i) * η (pderiv l (f i)) := by
  have := hk.2 l
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, pderiv_mul, hf, this]

theorem det_ne_zero_of_mul_eq [Fintype σ] [DecidableEq σ] [IsDomain O] {N J : Matrix σ σ O}
    {c : O} (hc : c ≠ 0) (h : N * J = c • (1 : Matrix σ σ O)) : J.det ≠ 0 := by
  intro hJ
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, hJ, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one] at this
  exact pow_ne_zero _ hc this.symm

theorem cotangent_map_injective_of_square_presentation : ∀ (O B A σ : Type) [CommRing O] [IsDomain O] [CommRing B] [CommRing A] [Algebra O B] [Algebra O A] [Algebra B A] [IsScalarTower O B A] [Fintype σ] (ε : A →ₐ[O] O) (x : σ → A) (f : σ → MvPolynomial σ B) (c : O), c ≠ 0 → Function.Surjective (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) → (∀ i, MvPolynomial.aeval x (f i) = 0) → RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) ≤ Ideal.span (Set.range f) ⊔ (RingHom.ker ε).comap (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) * RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) → (∀ a ∈ RingHom.ker ε, c • a ∈ RingHom.ker ε ^ 2 ⊔ ((RingHom.ker ε).comap (algebraMap B A)).map (algebraMap B A)) → ∀ b : B, algebraMap B A b ∈ RingHom.ker ε ^ 2 → b ∈ ((RingHom.ker ε).comap (algebraMap B A)) ^ 2 := by
  intro O B A σ _ _ _ _ _ _ _ _ _ ε x f c hc hsurj hf hker hc2 b hb
  classical
  set Ψ := (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) with hΨ
  let η : MvPolynomial σ B →+* O := (ε : A →+* O).comp (Ψ : MvPolynomial σ B →+* A)
  have hη : ∀ F, η F = ε (Ψ F) := fun F => rfl
  set q := (RingHom.ker ε).comap Ψ with hq
  have hqmem : ∀ F, F ∈ q ↔ η F = 0 := fun F => by
    rw [hq, Ideal.mem_comap, RingHom.mem_ker, hη]
  have hkerq : RingHom.ker Ψ ≤ q := fun F hF => by
    rw [hqmem, hη, (RingHom.mem_ker).1 hF, map_zero]
  have hηf : ∀ i, η (f i) = 0 := fun i => by rw [hη, hf i, map_zero]
  set K := firstOrderKer η with hK
  have hq2 : q ^ 2 ≤ K := by
    rw [pow_two]
    refine Ideal.mul_le.2 fun a ha b' hb' => ?_
    rw [hqmem] at ha hb'
    exact ⟨by simp [ha, hb'], fun l => by simp [pderiv_mul, ha, hb']⟩
  have hkerL : RingHom.ker Ψ ≤ Ideal.span (Set.range f) ⊔ q ^ 2 := by
    refine hker.trans (sup_le_sup_left ?_ _)
    rw [pow_two]; exact Ideal.mul_mono_right hkerq
  have hkerK : RingHom.ker Ψ ≤ Ideal.span (Set.range f) ⊔ K := hkerL.trans (sup_le_sup_left hq2 _)
  have hsq : RingHom.ker ε ^ 2 = (q ^ 2).map Ψ := by
    rw [Ideal.map_pow, hq, Ideal.map_comap_of_surjective Ψ hsurj]
  have lift : ∀ (L : Ideal (MvPolynomial σ B)), RingHom.ker Ψ ≤ Ideal.span (Set.range f) ⊔ L →
      ∀ F, Ψ F ∈ L.map Ψ → F ∈ Ideal.span (Set.range f) ⊔ L := by
    intro L hL F hF
    obtain ⟨G, hG, hGF⟩ := (Ideal.mem_map_iff_of_surjective Ψ hsurj).1 hF
    have h1 : F - G ∈ RingHom.ker Ψ := by rw [RingHom.mem_ker, map_sub, hGF, sub_self]
    have h2 : F = (F - G) + G := by ring
    rw [h2]; exact Ideal.add_mem _ (hL h1) (Ideal.mem_sup_right hG)
  have hIB : ((RingHom.ker ε).comap (algebraMap B A)).map (algebraMap B A) ≤ K.map Ψ := by
    rw [Ideal.map_le_iff_le_comap]
    intro i hi
    rw [Ideal.mem_comap, RingHom.mem_ker] at hi
    rw [Ideal.mem_comap]
    have : algebraMap B A i = Ψ (C i) := by simp [hΨ]
    rw [this]
    refine Ideal.mem_map_of_mem _ ⟨?_, fun l => by simp⟩
    rw [hη]; simpa [hΨ] using hi
  let Jac : Matrix σ σ O := fun i l => η (pderiv l (f i))
  have hrow : ∀ j, ∃ g : σ → MvPolynomial σ B, ∀ l,
      (if j = l then c else 0) = ∑ i, η (g i) * Jac i l := by
    intro j
    set F := C (algebraMap O B c) * (X j - C (algebraMap O B (ε (x j)))) with hF
    have ha : x j - algebraMap O A (ε (x j)) ∈ RingHom.ker ε := by
      rw [RingHom.mem_ker]; simp
    have hΨF : Ψ F = c • (x j - algebraMap O A (ε (x j))) := by
      simp [hF, hΨ, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
    have hmem : Ψ F ∈ K.map Ψ := by
      rw [hΨF]
      refine (sup_le ?_ hIB) (hc2 _ ha)
      rw [hsq]; exact Ideal.map_mono hq2
    have hF2 := lift K hkerK F hmem
    rw [Submodule.mem_sup] at hF2
    obtain ⟨s, hs, k, hk, hsk⟩ := hF2
    obtain ⟨g, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hs
    refine ⟨g, fun l => ?_⟩
    have e1 := pderiv_comb η f g hηf k hk l
    rw [hsk] at e1
    rw [← e1, hF]
    by_cases hjl : j = l
    · subst hjl
      simp [pderiv_X_self, hη, hΨ, ← IsScalarTower.algebraMap_apply]
    · simp [hjl, pderiv_X_of_ne (Ne.symm hjl)]
  choose g hg using hrow
  let N : Matrix σ σ O := fun j i => η (g j i)
  have hNJ : N * Jac = c • (1 : Matrix σ σ O) := by
    ext j l
    rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, ← hg j l]
    split_ifs <;> simp
  have hdet : Jac.det ≠ 0 := det_ne_zero_of_mul_eq hc hNJ
  have hCb : C b ∈ Ideal.span (Set.range f) ⊔ q ^ 2 := by
    refine lift _ hkerL (C b) ?_
    rw [← hsq]; simpa [hΨ] using hb
  rw [Submodule.mem_sup] at hCb
  obtain ⟨s, hs, k, hk, hsk⟩ := hCb
  obtain ⟨g', rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hs
  have hv : Matrix.vecMul (fun i => η (g' i)) Jac = 0 := by
    funext l
    have e1 := pderiv_comb η f g' hηf k (hq2 hk) l
    rw [hsk] at e1
    simp only [pderiv_C, map_zero] at e1
    change ∑ i, η (g' i) * Jac i l = 0
    exact e1.symm
  have hv0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hv
  have hCq : C b ∈ q ^ 2 := by
    rw [← hsk]
    refine Ideal.add_mem _ (Ideal.sum_mem _ fun i _ => ?_) hk
    rw [pow_two]
    refine Ideal.mul_mem_mul ?_ (hkerq ?_)
    · rw [hqmem]; exact congrFun hv0 i
    · rw [RingHom.mem_ker]; exact hf i
  let ev : MvPolynomial σ B →ₐ[B] B := aeval (fun j => algebraMap O B (ε (x j)))
  have hev : ((ε : A →+* O).comp (algebraMap B A)).comp (ev : MvPolynomial σ B →+* B) = η := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [ev, η, hΨ]
    · intro i; simp [ev, η, hΨ, ← IsScalarTower.algebraMap_apply]
  have hqev : q.map ev ≤ (RingHom.ker ε).comap (algebraMap B A) := by
    rw [Ideal.map_le_iff_le_comap]
    intro F hF
    rw [hqmem] at hF
    rw [Ideal.mem_comap, Ideal.mem_comap, RingHom.mem_ker, ← hF, ← hev]
    rfl
  have : b = ev (C b) := by simp [ev]
  rw [this]
  exact Ideal.pow_right_mono hqev 2 (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hCq)

end GlobalTheory.CotangentSquare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeNumericalBoundsCollect
section
open Real

namespace GlobalTheory

theorem covol_numerical_collect : ∀ (CG CB f r Lb S N0 sz c₁ q ℓ lb dd : ℝ), 0 ≤ CG → 0 ≤ CB → 1 ≤ f → 1 ≤ r → 1 ≤ Lb → 0 ≤ S → 0 ≤ q → q ≤ r → 0 ≤ ℓ → ℓ ≤ 3 * Lb → |c₁| ≤ 9 * r * Lb → 0 ≤ N0 → N0 ≤ S + f * (4 * (f * r + 1) + 1) → 0 ≤ sz → sz ≤ (1 + r) * S + r * f * (4 * (f * r + 1) + 1) → lb ≤ CB * (f * r * Lb) ^ 2 → dd ≤ 391 / 2 * (f * r * Lb) ^ 2 → (f * r + 1) * (2 * (f * r) * Real.log (2 * Real.pi)) + ((|c₁| + q * ℓ) * N0 + lb + dd + 1) + CG * (f * r * Lb) ^ 2 * sz ≤ (11 * CG + CB + 500) * ((f * r * Lb) ^ 3 * S + (f * r * Lb) ^ 5) := by
  intro CG CB f r Lb S N0 sz c₁ q ℓ lb dd hCG hCB hf hr hLb hS hq hqr hℓ hℓL hc hN0 hN0u hsz hszu hlb hdd
  have hfr : 1 ≤ f * r := by nlinarith
  have hfrF : f * r ≤ f * r * Lb := by nlinarith
  have hrLbF : r * Lb ≤ f * r * Lb := by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ r) (by linarith : (0:ℝ) ≤ Lb)]
  have hrF : r ≤ f * r * Lb := by nlinarith
  obtain ⟨F, hFd⟩ : ∃ F, F = f * r * Lb := ⟨_, rfl⟩
  rw [← hFd] at hlb hdd hfrF hrLbF hrF ⊢
  have hF : 1 ≤ F := by linarith
  have hF2 : F ^ 2 ≤ F ^ 5 := pow_le_pow_right₀ hF (by norm_num)
  have hF3 : F ^ 3 ≤ F ^ 5 := pow_le_pow_right₀ hF (by norm_num)
  have hF4 : F ^ 4 ≤ F ^ 5 := pow_le_pow_right₀ hF (by norm_num)
  have hF1 : F ≤ F ^ 3 := by simpa using pow_le_pow_right₀ hF (by norm_num : 1 ≤ 3)
  have hY : 1 ≤ F ^ 5 := one_le_pow₀ hF
  have hX : 0 ≤ F ^ 3 * S := mul_nonneg (by positivity) hS

  have hlog : Real.log (2 * π) ≤ 7 := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < 2 * π)
    have := Real.pi_le_four
    linarith
  have hfrsq : (f * r) ^ 2 ≤ F ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hfrF) (by linarith : (0:ℝ) ≤ F + f * r)]
  have hT1a : (f * r + 1) * (2 * (f * r) * Real.log (2 * π)) ≤ (f * r + 1) * (2 * (f * r) * 7) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlog (by linarith)) (by linarith)
  have hT1 : (f * r + 1) * (2 * (f * r) * Real.log (2 * π)) ≤ 28 * F ^ 5 := by nlinarith

  have hql : q * ℓ ≤ r * (3 * Lb) := mul_le_mul hqr hℓL hℓ (by linarith)
  have hA : |c₁| + q * ℓ ≤ 12 * (r * Lb) := by linarith
  have hffr : f ≤ f * (f * r) := by nlinarith
  have hB : N0 ≤ S + 9 * (f * (f * r)) := by
    have e : f * (4 * (f * r + 1) + 1) = 4 * (f * (f * r)) + 5 * f := by ring
    linarith
  have hAB : (|c₁| + q * ℓ) * N0 ≤ 12 * (r * Lb) * (S + 9 * (f * (f * r))) :=
    mul_le_mul hA hB hN0 (by positivity)
  have hrLbS : r * Lb * S ≤ F ^ 3 * S := mul_le_mul_of_nonneg_right (by linarith) hS
  have hFfr : r * Lb * (f * (f * r)) ≤ F ^ 5 := by
    have e : r * Lb * (f * (f * r)) = F * (f * r) := by rw [hFd]; ring
    rw [e]
    have : F * (f * r) ≤ F * F := mul_le_mul_of_nonneg_left hfrF (by linarith)
    nlinarith
  have hT2 : (|c₁| + q * ℓ) * N0 ≤ 12 * (F ^ 3 * S) + 108 * F ^ 5 := by
    have e : 12 * (r * Lb) * (S + 9 * (f * (f * r))) = 12 * (r * Lb * S) + 108 * (r * Lb * (f * (f * r))) := by ring
    linarith

  have hsz1 : (1 + r) * S ≤ 2 * F * S := mul_le_mul_of_nonneg_right (by linarith) hS
  have hsz2 : r * f * (4 * (f * r + 1) + 1) ≤ 9 * F ^ 2 := by
    have e : r * f * (4 * (f * r + 1) + 1) = 4 * (f * r) ^ 2 + 5 * (f * r) := by ring
    rw [e]; nlinarith
  have hsz' : sz ≤ 2 * F * S + 9 * F ^ 2 := by linarith
  have hT6a : CG * F ^ 2 * sz ≤ CG * F ^ 2 * (2 * F * S + 9 * F ^ 2) :=
    mul_le_mul_of_nonneg_left hsz' (by positivity)
  have hT6b : CG * F ^ 4 ≤ CG * F ^ 5 := mul_le_mul_of_nonneg_left hF4 hCG
  have hT6 : CG * F ^ 2 * sz ≤ 2 * (CG * (F ^ 3 * S)) + 9 * (CG * F ^ 5) := by
    have e : CG * F ^ 2 * (2 * F * S + 9 * F ^ 2) = 2 * (CG * (F ^ 3 * S)) + 9 * (CG * F ^ 4) := by ring
    linarith
  have hlb' : lb ≤ CB * F ^ 5 := le_trans hlb (mul_le_mul_of_nonneg_left hF2 hCB)
  have hdd' : dd ≤ 196 * F ^ 5 := by linarith
  have p1 : 0 ≤ CG * (F ^ 3 * S) := mul_nonneg hCG hX
  have p2 : 0 ≤ CB * (F ^ 3 * S) := mul_nonneg hCB hX
  have p3 : 0 ≤ CG * F ^ 5 := mul_nonneg hCG (by positivity)
  have e : (11 * CG + CB + 500) * (F ^ 3 * S + F ^ 5)
      = 11 * (CG * (F ^ 3 * S)) + CB * (F ^ 3 * S) + 500 * (F ^ 3 * S) + 11 * (CG * F ^ 5) + CB * F ^ 5 + 500 * F ^ 5 := by ring
  rw [e]
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurveLieLatticeDegree
section
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.EtaleHeightOne

theorem height_comap_le_one_of_goingDown {A B : Type} [CommRing A] [IsDomain A] [CommRing B]
    [Algebra A B] [Algebra.HasGoingDown A B] (Q : Ideal B) [Q.IsPrime] (hQ : Q.height ≤ 1) :
    (Q.comap (algebraMap A B)).height ≤ 1 := by
  set p : Ideal A := Q.comap (algebraMap A B) with hp
  haveI : p.IsPrime := Ideal.comap_isPrime _ Q
  haveI : Q.LiesOver p := ⟨rfl⟩
  rw [show ((1 : ℕ∞)) = ((1 : ℕ) : ℕ∞) from rfl, Ideal.height_le_iff]
  intro r hr hrp
  by_contra hcon
  have hr0 : r ≠ ⊥ := by
    rintro rfl
    simp at hcon
  haveI := hr
  obtain ⟨P₁, hP₁Q, hP₁, hP₁o⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := r) (q := p) Q hrp
  haveI := hP₁
  haveI : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
  obtain ⟨P₀, hP₀P₁, hP₀, -⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := ⊥) (q := r) P₁
    (bot_lt_iff_ne_bot.mpr hr0)
  haveI := hP₀
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hP₀P₁
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hP₁Q
  have h4 : (1 : ℕ∞) ≤ P₁.height := le_trans le_add_self h1
  have h3 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr) (h2.trans hQ)
  exact absurd h3 (by decide)

theorem height_one_and_comap_eq_map_C : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (E : Type) [CommRing E] [Algebra A[X] E] [Algebra A E] [IsScalarTower A A[X] E]
    [Algebra.Etale A[X] E] (Q : Ideal E) [Q.IsPrime] (P : Ideal (Localization.AtPrime Q)) [P.IsPrime]
    (a : A), a ≠ 0 → algebraMap A (Localization.AtPrime Q) a ∈ P → P.height ≤ 1 →
    (P.comap (algebraMap A (Localization.AtPrime Q))).height = 1 ∧
      P.comap (algebraMap A[X] (Localization.AtPrime Q)) =
        (P.comap (algebraMap A (Localization.AtPrime Q))).map (Polynomial.C : A →+* A[X]) := by
  intro A _ _ _ _ E _ _ _ _ _ Q _ P _ a ha haP hP
  set R := Localization.AtPrime Q
  haveI : Module.Flat A[X] E := inferInstance
  haveI : Module.Flat A E := Module.Flat.trans A A[X] E
  haveI : Module.Flat E R := inferInstance
  haveI : Module.Flat A R := Module.Flat.trans A E R
  haveI : Module.Flat A[X] R := Module.Flat.trans A[X] E R
  haveI : Algebra.HasGoingDown A R := Algebra.HasGoingDown.of_flat
  haveI : Algebra.HasGoingDown A[X] R := Algebra.HasGoingDown.of_flat
  set p := P.comap (algebraMap A R) with hp
  haveI : p.IsPrime := Ideal.comap_isPrime _ P
  have hpne : p ≠ ⊥ := by
    intro h
    have : a ∈ p := haP
    rw [h, Ideal.mem_bot] at this
    exact ha this
  haveI : (⊥ : Ideal A).IsPrime := Ideal.isPrime_bot
  have hp1 : 1 ≤ p.height := by
    have := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hpne)
    simpa using this
  refine ⟨le_antisymm (height_comap_le_one_of_goingDown P hP) hp1, ?_⟩
  have htower : algebraMap A R = (algebraMap A[X] R).comp (Polynomial.C : A →+* A[X]) := by
    rw [IsScalarTower.algebraMap_eq A E R, IsScalarTower.algebraMap_eq A[X] E R,
      IsScalarTower.algebraMap_eq A A[X] E, ← Polynomial.algebraMap_eq]
    rfl
  set P' := P.comap (algebraMap A[X] R) with hP'
  haveI : P'.IsPrime := Ideal.comap_isPrime _ P
  haveI hCp : (p.map (Polynomial.C : A →+* A[X])).IsPrime := Ideal.isPrime_map_C_of_isPrime
  have hle : p.map (Polynomial.C : A →+* A[X]) ≤ P' := by
    rw [Ideal.map_le_iff_le_comap, hP', Ideal.comap_comap, ← htower]
  have hP'1 : P'.height ≤ 1 := height_comap_le_one_of_goingDown P hP
  by_contra hne
  have hlt : p.map (Polynomial.C : A →+* A[X]) < P' := lt_of_le_of_ne hle (Ne.symm hne)
  have hCne : p.map (Polynomial.C : A →+* A[X]) ≠ ⊥ := by
    intro h
    apply hpne
    rw [eq_bot_iff]
    intro x hx
    have : Polynomial.C x ∈ p.map (Polynomial.C : A →+* A[X]) := Ideal.mem_map_of_mem _ hx
    rw [h, Ideal.mem_bot, Polynomial.C_eq_zero] at this
    simp [this]
  haveI : (⊥ : Ideal A[X]).IsPrime := Ideal.isPrime_bot
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hCne)
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have h4 : (1 : ℕ∞) ≤ (p.map (Polynomial.C : A →+* A[X])).height := by simpa using h1
  have h3 : (1 : ℕ∞) + 1 ≤ 1 := le_trans (by gcongr) (h2.trans hP'1)
  exact absurd h3 (by decide)

end GlobalTheory.EtaleHeightOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenExists
section
namespace GlobalTheory.DenominatorExistence

open NumberField

theorem den_exists {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * c) := by
  have hc : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨y, hy, hint⟩ := hc.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  rcases Int.natAbs_eq y with h | h
  · have h' : (y.natAbs : ℤ) = y := by omega
    have h2 : ((y.natAbs : ℤ) : E) = (y : E) := congrArg _ h'
    rw [Int.cast_natCast] at h2
    rw [h2, ← zsmul_eq_mul]; exact hint
  · have h' : (y.natAbs : ℤ) = -y := by omega
    have h2 : ((y.natAbs : ℤ) : E) = ((-y : ℤ) : E) := congrArg _ h'
    rw [Int.cast_natCast, Int.cast_neg] at h2
    rw [h2, neg_mul, ← zsmul_eq_mul]; exact hint.neg

theorem main {E : Type} [Field E] [NumberField E] {r : ℕ}
    (Λ Λ' : Submodule (RingOfIntegers E) (Fin r → E)) (hfg : Λ'.FG)
    (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤) :
    ∃ n : ℕ, 0 < n ∧ ∀ v ∈ Λ', (n : E) • v ∈ Λ := by

  have key : ∀ v : Fin r → E, ∃ n : ℕ, 0 < n ∧ n • v ∈ Λ := by
    intro v
    have hv : v ∈ Submodule.span E (Λ : Set (Fin r → E)) := by rw [hspan]; trivial
    induction hv using Submodule.span_induction with
    | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
    | zero => exact ⟨1, one_pos, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha, hax⟩ := hx
      obtain ⟨b, hb, hby⟩ := hy
      refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
      rw [smul_add]
      refine Λ.add_mem ?_ ?_
      · rw [mul_nsmul]; exact Λ.toAddSubmonoid.nsmul_mem hax b
      · rw [mul_comm, mul_nsmul]; exact Λ.toAddSubmonoid.nsmul_mem hby a
    | smul c x _ hx =>
      obtain ⟨a, ha, hax⟩ := hx
      obtain ⟨d, hd, hdc⟩ := den_exists c
      refine ⟨d * a, Nat.mul_pos hd ha, ?_⟩
      have e1 : (⟨(d : E) * c, hdc⟩ : RingOfIntegers E) • (a • x)
          = ((d : E) * c) • (a • x) := by
        rw [← algebraMap_smul E]; rfl
      have e : (d * a) • (c • x) = (⟨(d : E) * c, hdc⟩ : RingOfIntegers E) • (a • x) := by
        rw [e1, ← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E, smul_smul, smul_smul]
        congr 1
        push_cast; ring
      rw [e]; exact Λ.smul_mem _ hax
  obtain ⟨s, hs⟩ := hfg
  classical
  choose f hfpos hfmem using key
  refine ⟨∏ x ∈ s, f x, Finset.prod_pos (fun x _ => hfpos x), ?_⟩
  intro v hv
  rw [Nat.cast_smul_eq_nsmul]
  rw [← hs] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.mul_prod_erase s f hx, mul_nsmul]
    exact Λ.toAddSubmonoid.nsmul_mem (hfmem x) _
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Λ.add_mem hx hy
  | smul o x _ hx => rw [smul_comm]; exact Λ.smul_mem o hx

end GlobalTheory.DenominatorExistence
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsFurtherTer
section
universe u_1 u_2

namespace GlobalTheory.BandLemmaSecond

theorem main : (let d1 : {k : Type u_1} → [Field k] → {ι : Type u_2} → (ι → ℕ) → ℕ → Matrix ι ι k → Prop := @(fun {k : Type u_1} [Field k] {ι : Type u_2} (ℓ : ι → ℕ) (j : ℕ) (X : Matrix ι ι k) ↦ ∀ (r s : ι), ℓ s < ℓ r + j → X r s = (0 : k)); ∀ {k : Type u_1} [inst : Field k] {ι : Type u_2} [Fintype ι] [DecidableEq ι] {ℓ : ι → ℕ} {j : ℕ} {X : Matrix ι ι k}, d1 ℓ j X → d1 ℓ j (-X)) := by
  intro d1 k _ ι _ _ ℓ j X h r s hrs
  simp only [Matrix.neg_apply, h r s hrs, neg_zero]

end GlobalTheory.BandLemmaSecond
end

