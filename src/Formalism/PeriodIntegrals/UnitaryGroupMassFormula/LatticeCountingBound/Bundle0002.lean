module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.SepDefs
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeSizeContinuity.Bundle0001

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.ArchIneq
section
noncomputable section

open Matrix

namespace PI.UnitaryGroupMassFormula.LCG

theorem archimedean_inequality : ArchIneq := by
  intro n k A C D κ hκ hA hker
  have hGdet := (PI.UnitaryGroupMassFormula.LSC.determinant_monotone n k D 1 1 zero_le_one (by intro w; simp)).1
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Fin k) (Fin k) ℂ, G = Dᴴ * D := ⟨_, rfl⟩
  rw [← hG] at hGdet ⊢
  have hGh : Gᴴ = G := by
    rw [hG, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have him : G.det.im = 0 := by
    have hstar : star G.det = G.det := by rw [← Matrix.det_conjTranspose, hGh]
    have h1 := congrArg Complex.im hstar
    simp only [Complex.star_def, Complex.conj_im] at h1
    linarith
  by_cases hg : G.det = 0
  · rw [hg, Complex.zero_re, mul_zero]
    exact mul_nonneg (pow_nonneg hκ k) (sq_nonneg _)
  · have hGu : IsUnit G.det := isUnit_iff_ne_zero.mpr hg
    obtain ⟨X, hX⟩ : ∃ X : Matrix (Fin n) (Fin k) ℂ, X = D * G⁻¹ * Dᴴ * C := ⟨_, rfl⟩
    have hAP : A * (D * G⁻¹ * Dᴴ) = A := by
      apply Matrix.ext_of_mulVec_single
      intro j
      have h1 : Dᴴ *ᵥ ((Pi.single j 1 : Fin n → ℂ) - (D * G⁻¹ * Dᴴ) *ᵥ Pi.single j 1) = 0 := by
        have h3 : Dᴴ * (D * G⁻¹ * Dᴴ) = G * G⁻¹ * Dᴴ := by
          rw [hG]
          simp only [Matrix.mul_assoc]
        rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, h3, Matrix.mul_nonsing_inv G hGu, Matrix.one_mul, sub_self]
      have h2 := hker _ h1
      rw [Matrix.mulVec_sub, sub_eq_zero] at h2
      rw [← Matrix.mulVec_mulVec, ← h2]
    have hAX : A * X = A * C := by
      rw [hX, ← Matrix.mul_assoc, hAP]
    have hdm := (PI.UnitaryGroupMassFormula.LSC.determinant_monotone n k X A κ hκ hA).2
    rw [hAX] at hdm
    have hXh : Xᴴ = Cᴴ * D * G⁻¹ * Dᴴ := by
      rw [hX]
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_nonsing_inv,
        hGh, Matrix.mul_assoc]
    have hXX : Xᴴ * X = Cᴴ * D * G⁻¹ * (Dᴴ * C) := by
      rw [hXh, hX]
      have hGG : G⁻¹ * (Dᴴ * D) = 1 := by
        rw [← hG]
        exact Matrix.nonsing_inv_mul G hGu
      calc Cᴴ * D * G⁻¹ * Dᴴ * (D * G⁻¹ * Dᴴ * C) = Cᴴ * D * (G⁻¹ * (Dᴴ * D)) * G⁻¹ * (Dᴴ * C) := by
            simp only [Matrix.mul_assoc]
        _ = Cᴴ * D * G⁻¹ * (Dᴴ * C) := by rw [hGG, Matrix.mul_one]
    have hdetX : (Xᴴ * X).det = star (Dᴴ * C).det * (Dᴴ * C).det / G.det := by
      have hCD : Cᴴ * D = (Dᴴ * C)ᴴ := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      rw [hXX, Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hCD,
        Matrix.det_conjTranspose]
      ring
    have h5 : (Xᴴ * X).det * G.det = star (Dᴴ * C).det * (Dᴴ * C).det := by
      rw [hdetX, div_mul_cancel₀ _ hg]
    have hval : (Xᴴ * X).det.re * G.det.re = ‖(Dᴴ * C).det‖ ^ 2 := by
      have h6 := congrArg Complex.re h5
      rw [Complex.mul_re, him, mul_zero, sub_zero] at h6
      rw [h6, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
      ring
    calc (((A * C)ᴴ * (A * C)).det).re * G.det.re ≤ κ ^ k * (Xᴴ * X).det.re * G.det.re :=
          mul_le_mul_of_nonneg_right hdm hGdet
      _ = κ ^ k * ‖(Dᴴ * C).det‖ ^ 2 := by rw [mul_assoc, hval]

end PI.UnitaryGroupMassFormula.LCG
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.Choose
section
noncomputable section

open NumberField Matrix

namespace PI.UnitaryGroupMassFormula.LCG

namespace ChooseW

section Gen

variable {K : Type*} [Field K] {n : ℕ}

lemma ann_range (δ : Matrix (Fin n) (Fin n) K) (a : Fin n → K)
    (ha : ∀ z, δ *ᵥ z = 0 → a ⬝ᵥ z = 0) : ∃ t, a = t ᵥ* δ := by
  let ℓ : Module.Dual K (Fin n → K) :=
    { toFun := fun z => a ⬝ᵥ z
      map_add' := fun x y => dotProduct_add a x y
      map_smul' := fun c x => by simp [dotProduct_smul] }
  have hmem : ℓ ∈ (LinearMap.ker δ.mulVecLin).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    intro z hz
    exact ha z (by simpa using hz)
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hmem
  obtain ⟨φ, hφ⟩ := hmem
  refine ⟨fun j => φ (fun r => if j = r then 1 else 0), ?_⟩
  funext i
  have h1 := LinearMap.congr_fun hφ (fun r => if i = r then 1 else 0)
  rw [LinearMap.dualMap_apply] at h1
  have h2 : ℓ (fun r => if i = r then 1 else 0) = a i := by
    simp [ℓ, dotProduct]
  rw [h2, LinearMap.pi_apply_eq_sum_univ φ] at h1
  rw [← h1]
  simp [Matrix.vecMul, dotProduct, Matrix.mulVec, mul_comm]

lemma scaled_li {ι : Type*} {V : Type*} [AddCommGroup V] [Module K V] (d : ι → V)
    (hli : LinearIndependent K d) (m : ι → K) (hm : ∀ c, m c ≠ 0) :
    LinearIndependent K (fun c => m c • d c) := by
  have := hli.units_smul (fun c => Units.mk0 (m c) (hm c))
  convert this using 1
  funext c
  simp [Units.smul_def]

lemma scaled_span {ι : Type*} {V : Type*} [AddCommGroup V] [Module K V] (d : ι → V) (m : ι → K)
    (hm : ∀ c, m c ≠ 0) :
    Submodule.span K (Set.range d) ≤ Submodule.span K (Set.range fun c => m c • d c) := by
  rw [Submodule.span_le]
  rintro _ ⟨c, rfl⟩
  have : d c = (m c)⁻¹ • (m c • d c) := by rw [smul_smul, inv_mul_cancel₀ (hm c), one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

lemma basis_range (A : Matrix (Fin n) (Fin n) K) (k : ℕ) (hk : A.rank = k) :
    ∃ z : Fin k → Fin n → K, LinearIndependent K (fun c => A *ᵥ z c) ∧
      ∀ w, A *ᵥ w ∈ Submodule.span K (Set.range fun c => A *ᵥ z c) := by
  let R := LinearMap.range A.mulVecLin
  let bas := Module.finBasisOfFinrankEq K R hk
  have hz : ∀ c, ∃ z, A *ᵥ z = (bas c : Fin n → K) := fun c => by
    obtain ⟨z, hz⟩ := LinearMap.mem_range.mp (bas c).2
    exact ⟨z, by simpa using hz⟩
  choose z hz using hz
  have hspan : Submodule.span K (Set.range fun c => (bas c : Fin n → K)) = R := by
    rw [show (fun c => (bas c : Fin n → K)) = R.subtype ∘ bas from rfl, Set.range_comp,
      ← Submodule.map_span, bas.span_eq, Submodule.map_top, Submodule.range_subtype]
  refine ⟨z, ?_, ?_⟩
  · simp only [hz]
    exact bas.linearIndependent.map' R.subtype (Submodule.ker_subtype R)
  · intro w
    simp only [hz]
    rw [hspan]
    exact LinearMap.mem_range.mpr ⟨w, by simp⟩

lemma rank_pos (δ : Matrix (Fin n) (Fin n) K) (hδ : δ ≠ 0) : 1 ≤ δ.rank := by
  by_contra h
  have h0 : δ.rank = 0 := by omega
  have hbot : LinearMap.range δ.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h0
  have hz : Matrix.toLin' δ = 0 := by
    rw [Matrix.toLin'_apply']
    exact LinearMap.range_eq_bot.mp hbot
  exact hδ (Matrix.toLin'.injective (by rw [hz, map_zero]))

end Gen

section Star

variable {E : Type*} [Field E] [StarRing E] {n : ℕ}

def sv (w : Fin n → E) : Fin n → E := fun i => starRingEnd E (w i)

lemma sv_sv (w : Fin n → E) : sv (sv w) = w := by
  funext i; simp [sv]

lemma star_li {k : ℕ} (v : Fin k → Fin n → E) (h : LinearIndependent E v) :
    LinearIndependent E (fun a => sv (v a)) := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg i
  have h0 : ∑ a, starRingEnd E (g a) • v a = 0 := by
    funext j
    have := congrArg (starRingEnd E) (congrFun hg j)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sv, map_sum, map_mul,
      starRingEnd_self_apply, map_zero, Pi.zero_apply] at this ⊢
    rw [← this]
  have := h _ h0 i
  simpa using this

lemma star_span {k : ℕ} (v : Fin k → Fin n → E) (w : Fin n → E)
    (hw : sv w ∈ Submodule.span E (Set.range v)) :
    w ∈ Submodule.span E (Set.range fun a => sv (v a)) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp hw
  refine (Submodule.mem_span_range_iff_exists_fun E).mpr ⟨fun a => starRingEnd E (c a), ?_⟩
  rw [← sv_sv w, ← hc]
  funext j
  set_option synthInstance.maxHeartbeats 100000 in
    simp [sv, Finset.sum_apply, map_sum, map_mul]

end Star

lemma scale {E : Type} [Field E] [NumberField E] {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hΛ : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) (w : Fin n → E) :
    ∃ m : ℤ, m ≠ 0 ∧ (m : E) • w ∈ Λ := by
  classical
  have hw : w ∈ Submodule.span E (Λ : Set (Fin n → E)) := hΛ ▸ Submodule.mem_top
  obtain ⟨N, f, g, hfg⟩ := Submodule.mem_span_set'.mp hw
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image f)
  refine ⟨y, hy, ?_⟩
  rw [← hfg, Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hi : IsIntegral ℤ ((y : E) * f i) := by
    have := hint (f i) (Finset.mem_image_of_mem f (Finset.mem_univ i))
    simpa [zsmul_eq_mul] using this
  rw [smul_smul]
  have := Λ.smul_mem (⟨(y : E) * f i, hi⟩ : 𝓞 E) (g i).2
  convert this using 1
  exact (algebraMap_smul E _ _).symm

lemma hf_eq (I : Formalism.MainNotions.S.AutInst) (w z : Fin I.n → I.E) : hf I w z = (sv w ᵥ* I.J) ⬝ᵥ z := by
  simp only [hf, Formalism.UG.hform, dotProduct, vecMul, Finset.sum_mul, sv]
  rw [Finset.sum_comm]

end ChooseW

open ChooseW in
theorem choice_of_generators : Choose := by
  intro I y δ hδ
  obtain ⟨Λ, _, hΛs, hΛ0⟩ := PI.UnitaryGroupMassFormula.LSC.lattice_isometry I y
  have hΛ : PI.LatCountG.latSet I y = (Λ : Set (Fin I.n → I.E)) := hΛ0
  have hJ : IsUnit I.J.det := isUnit_iff_ne_zero.mpr I.J_det
  set k := δ.rank with hk
  have hk1 : 1 ≤ k := rank_pos δ hδ

  obtain ⟨z, hzli, hzsp⟩ := basis_range δ k hk.symm
  have hsc : ∀ c, ∃ m : ℤ, m ≠ 0 ∧ ((m : I.E) • z c) ∈ Λ := fun c => scale Λ hΛs (z c)
  choose mu hmu0 hmuΛ using hsc

  set B : Matrix (Fin I.n) (Fin I.n) I.E := (δ * I.J⁻¹)ᵀ with hB
  have hBr : B.rank = k := by
    rw [hB, Matrix.rank_transpose, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnit_nonsing_inv_det I.J hJ)]
  obtain ⟨t, htli, htsp⟩ := basis_range B k hBr
  have hsc' : ∀ a, ∃ m : ℤ, m ≠ 0 ∧ ((m : I.E) • sv (B *ᵥ t a)) ∈ Λ := fun a => scale Λ hΛs _
  choose mb hmb0 hmbΛ using hsc'
  have hmu0' : ∀ c, ((mu c : ℤ) : I.E) ≠ 0 := fun c => Int.cast_ne_zero.mpr (hmu0 c)
  have hmb0' : ∀ a, ((mb a : ℤ) : I.E) ≠ 0 := fun a => Int.cast_ne_zero.mpr (hmb0 a)

  have hperpB : ∀ s w, δ *ᵥ w = 0 → ((B *ᵥ s) ᵥ* I.J) ⬝ᵥ w = 0 := by
    intro s w hw
    rw [hB, Matrix.mulVec_transpose, Matrix.vecMul_vecMul, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hJ, Matrix.mul_one, ← Matrix.dotProduct_mulVec, hw, dotProduct_zero]
  refine ⟨k, fun c => ((mu c : ℤ) : I.E) • z c, fun a => ((mb a : ℤ) : I.E) • sv (B *ᵥ t a), hk1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c; rw [hΛ]; exact hmuΛ c
  · simp only [Matrix.mulVec_smul]
    exact scaled_li (fun c => δ *ᵥ z c) hzli (fun c => ((mu c : ℤ) : I.E)) hmu0'
  · intro w
    simp only [Matrix.mulVec_smul]
    exact scaled_span (fun c => δ *ᵥ z c) (fun c => ((mu c : ℤ) : I.E)) hmu0' (hzsp w)
  · intro a; rw [hΛ]; exact hmbΛ a
  · exact scaled_li (fun a => sv (B *ᵥ t a)) (star_li (fun a => B *ᵥ t a) htli)
      (fun a => ((mb a : ℤ) : I.E)) hmb0'
  · intro a w hw
    rw [hf_eq]
    have hs : sv (((mb a : ℤ) : I.E) • sv (B *ᵥ t a)) = ((mb a : ℤ) : I.E) • (B *ᵥ t a) := by
      funext i; simp [sv]
    rw [hs, Matrix.smul_vecMul, smul_dotProduct, hperpB _ _ hw, smul_zero]
  · intro w hw
    have hann : ∀ z', δ *ᵥ z' = 0 → (sv w ᵥ* I.J) ⬝ᵥ z' = 0 := fun z' hz' => by
      rw [← hf_eq]; exact hw z' hz'
    obtain ⟨s, hs⟩ := ann_range δ _ hann
    have hsv : sv w = B *ᵥ s := by
      have : sv w = (sv w ᵥ* I.J) ᵥ* I.J⁻¹ := by
        rw [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hJ, Matrix.vecMul_one]
      rw [this, hs, Matrix.vecMul_vecMul, hB, Matrix.mulVec_transpose]
    have h1 : sv w ∈ Submodule.span I.E (Set.range fun a => B *ᵥ t a) := hsv ▸ htsp s
    exact scaled_span (fun a => sv (B *ᵥ t a)) (fun a => ((mb a : ℤ) : I.E)) hmb0'
      (star_span (fun a => B *ᵥ t a) w h1)

end PI.UnitaryGroupMassFormula.LCG
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.IndexDefs
section
noncomputable section

open NumberField Matrix

namespace PI.UnitaryGroupMassFormula.LCG

def oLat (K : Type) [Field K] [NumberField K] (k : ℕ) : Submodule (𝓞 K) (Fin k → K) :=
  LinearMap.range (LinearMap.compLeft (Algebra.linearMap (𝓞 K) K) (Fin k))

def dualL {K : Type} [Field K] [NumberField K] {k : ℕ} (X : Submodule (𝓞 K) (Fin k → K)) :
    Submodule (𝓞 K) (Fin k → K) where
  carrier := {t | ∀ s ∈ X, s ⬝ᵥ t ∈ (algebraMap (𝓞 K) K).range}
  add_mem' := by
    intro a b ha hb s hs
    rw [Set.mem_setOf_eq] at ha hb
    rw [dotProduct_add]
    exact add_mem (ha s hs) (hb s hs)
  zero_mem' := by
    intro s _
    rw [dotProduct_zero]
    exact zero_mem _
  smul_mem' := by
    intro c t ht s hs
    rw [Set.mem_setOf_eq] at ht
    have h1 := ht (c • s) (X.smul_mem c hs)
    have h2 : s ⬝ᵥ (c • t) = (c • s) ⬝ᵥ t := by
      simp only [dotProduct, Pi.smul_apply, Algebra.smul_def]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [h2]
    exact h1

def DualIdx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (k : ℕ) (X Y : Submodule (𝓞 K) (Fin k → K)), X ≤ Y →
    X.toAddSubgroup.relIndex Y.toAddSubgroup ≠ 0 →
    (dualL Y).toAddSubgroup.relIndex (dualL X).toAddSubgroup ≠ 0 ∧
      (dualL Y).toAddSubgroup.relIndex (dualL X).toAddSubgroup ≤ X.toAddSubgroup.relIndex Y.toAddSubgroup

def DetIdx : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (k : ℕ) (N : Matrix (Fin k) (Fin k) K) (Q D : AddSubgroup (Fin k → K)),
    (oLat K k).toAddSubgroup ≤ Q → (oLat K k).toAddSubgroup.relIndex Q ≠ 0 →
    D ≤ (oLat K k).toAddSubgroup → D.relIndex (oLat K k).toAddSubgroup ≠ 0 →
    (∀ r ∈ D, ∃ s ∈ Q, s ᵥ* N = r) →
    |((Algebra.norm ℚ N.det : ℚ) : ℝ)| ≤
      ((oLat K k).toAddSubgroup.relIndex Q : ℝ) * (D.relIndex (oLat K k).toAddSubgroup : ℝ)

def IndexOf : Prop := DualIdx → DetIdx → IndexIneq

end PI.UnitaryGroupMassFormula.LCG
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.LatticeIsDiscreteGroup
section
noncomputable section

open NumberField Matrix

namespace PI.UnitaryGroupMassFormula.LCG

open PI.LatCountG

theorem hsN_nonneg' {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hsN A := by
  unfold hsN
  exact Real.sqrt_nonneg _

theorem lattice_is_discrete_group : LatIsG := by
  intro I x
  obtain ⟨Λ, h1, h2, h3⟩ := PI.UnitaryGroupMassFormula.LSC.lattice_isometry I x
  exact ⟨Λ, h1, h2, h3⟩

theorem gram_nonneg (hDM : PI.UnitaryGroupMassFormula.LSC.DetMono) (I : Formalism.MainNotions.S.AutInst) (z : I.GA) (v : InfinitePlace I.F) {j : ℕ}
    (b : Fin j → Fin I.n → I.E) : 0 ≤ ((gramV I z v b).det).re := by
  let C : Matrix (Fin I.n) (Fin j) ℂ := Matrix.of fun i a => coordV I z v (b a) i
  have hG : gramV I z v b = Cᴴ * C := by
    ext a c
    simp [gramV, C, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [hG]
  exact (hDM I.n j C 1 1 zero_le_one (fun w => by simp)).1

theorem ht_eq (I : Formalism.MainNotions.S.AutInst) {z : I.GA} (s : Sub I z) :
    ht I s = (∏ v, ((gramV I z v s.b).det).re) / (idx I s.B s.b : ℝ) := rfl

theorem tau_pow_le_ht (hDM : PI.UnitaryGroupMassFormula.LSC.DetMono) (I : Formalism.MainNotions.S.AutInst) (z : I.GA) (hz : 0 < tau1 I z) (s : Sub I z) :
    tau1 I z ^ (2 * I.f * s.j) ≤ ht I s ∧ idx I s.B s.b ≠ 0 := by
  have hf : 0 < I.f := Module.finrank_pos
  have hj : 0 < s.j := s.j_pos
  have hN : (0 : ℝ) < 2 * (I.f : ℝ) * (s.j : ℝ) := by
    have : (0 : ℝ) < I.f := by exact_mod_cast hf
    have : (0 : ℝ) < s.j := by exact_mod_cast hj
    positivity
  have hht : ∀ t : Sub I z, 0 ≤ ht I t := by
    intro t
    rw [ht_eq]
    exact div_nonneg (Finset.prod_nonneg fun v _ => gram_nonneg hDM I z v t.b) (Nat.cast_nonneg _)
  have hsize : ∀ t : Sub I z, 0 ≤ size I t := fun t => Real.rpow_nonneg (hht t) _
  have hle : tau1 I z ≤ size I s :=
    (min_le_right _ _).trans (ciInf_le ⟨0, by rintro _ ⟨t, rfl⟩; exact hsize t⟩ s)
  have hpow : size I s ^ (2 * I.f * s.j) = ht I s := by
    unfold size
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hht s)]
    push_cast
    rw [one_div_mul_cancel hN.ne', Real.rpow_one]
  refine ⟨?_, ?_⟩
  · calc tau1 I z ^ (2 * I.f * s.j) ≤ size I s ^ (2 * I.f * s.j) := pow_le_pow_left₀ hz.le hle _
      _ = ht I s := hpow
  · intro h0
    have h1 : ht I s = 0 := by
      rw [ht_eq, h0]
      simp
    have hs0 : size I s = 0 := by
      unfold size
      rw [h1, Real.zero_rpow (one_div_pos.2 hN).ne']
    linarith

theorem separation_of_points : SepOf := by
  intro hLat hDual hCh hArch hIdx hNP hDM _hCard I x y hx hy δ hδ hmap
  obtain ⟨Λ, hFG, hspan, hΛ⟩ := hLat I y
  obtain ⟨k, u, b', hk, hu, hind1, hspan1, hb', hind2, hperp, hspan2⟩ := hCh I y δ hδ
  have huΛ : ∀ c, u c ∈ Λ := fun c => by
    have := hu c
    rw [hΛ] at this
    exact this
  have hbΛ : ∀ a, b' a ∈ Λ := fun a => by
    have := hb' a
    rw [hΛ] at this
    exact this
  let s₁ : Sub I x :=
    { j := k
      j_pos := hk
      b := fun c => δ *ᵥ u c
      b_ind := hind1
      B := imSub I Λ δ
      B_lat := by
        intro z hz
        obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hz
        exact hmap w (by rw [hΛ]; exact hw)
      b_mem := fun c => Submodule.mem_map.2 ⟨u c, huΛ c, rfl⟩
      B_span := by
        intro z hz
        obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.1 hz
        exact hspan1 w }
  let s₂ : Sub I y :=
    { j := k
      j_pos := hk
      b := b'
      b_ind := hind2
      B := perpSub I Λ δ
      B_lat := by
        intro z hz
        rw [hΛ]
        exact (Submodule.mem_inf.1 hz).1
      b_mem := fun a => Submodule.mem_inf.2 ⟨hbΛ a, hperp a⟩
      B_span := fun z hz => hspan2 z (Submodule.mem_inf.1 hz).2 }
  obtain ⟨h1, hi1⟩ := tau_pow_le_ht hDM I x hx s₁
  obtain ⟨h2, hi2⟩ := tau_pow_le_ht hDM I y hy s₂
  rw [ht_eq] at h1 h2
  change tau1 I x ^ (2 * I.f * k) ≤ (∏ v, ((gramV I x v (fun c => δ *ᵥ u c)).det).re) /
    (idx I (imSub I Λ δ) (fun c => δ *ᵥ u c) : ℝ) at h1
  change tau1 I y ^ (2 * I.f * k) ≤ (∏ v, ((gramV I y v b').det).re) / (idx I (perpSub I Λ δ) b' : ℝ) at h2
  change idx I (imSub I Λ δ) (fun c => δ *ᵥ u c) ≠ 0 at hi1
  change idx I (perpSub I Λ δ) b' ≠ 0 at hi2
  have hdualΛ : ∀ w, (∀ w' ∈ Λ, hf I w' w ∈ (algebraMap (𝓞 I.E) I.E).range) → w ∈ Λ := by
    intro w hw
    have := hDual I y w (by rw [hΛ]; exact hw)
    rw [hΛ] at this
    exact this
  have hN := hIdx I Λ hFG hspan hdualΛ δ k u b' huΛ hind1 hspan1 hbΛ hind2 hperp hspan2 hi1 hi2
  have hNP' := hNP I (pairM I b' u).det
  have hi1' : (0 : ℝ) < idx I (imSub I Λ δ) (fun c => δ *ᵥ u c) := by exact_mod_cast Nat.pos_of_ne_zero hi1
  have hi2' : (0 : ℝ) < idx I (perpSub I Λ δ) b' := by exact_mod_cast Nat.pos_of_ne_zero hi2
  have hHp : 0 ≤ ∏ v, hsN (amat I x y v δ) := Finset.prod_nonneg fun v _ => hsN_nonneg' _
  have key : ((tau1 I x * tau1 I y) ^ I.f) ^ (2 * k) ≤ (∏ v, hsN (amat I x y v δ)) ^ (2 * k) := by
    rw [← pow_mul, mul_pow, show I.f * (2 * k) = 2 * I.f * k by ring]
    calc tau1 I x ^ (2 * I.f * k) * tau1 I y ^ (2 * I.f * k)
        ≤ ((∏ v, ((gramV I x v (fun c => δ *ᵥ u c)).det).re) / (idx I (imSub I Λ δ) (fun c => δ *ᵥ u c) : ℝ)) *
          ((∏ v, ((gramV I y v b').det).re) / (idx I (perpSub I Λ δ) b' : ℝ)) :=
          mul_le_mul h1 h2 (pow_nonneg (hy.le) _) ((pow_nonneg hx.le _).trans h1)
      _ = (∏ v, (((gramV I x v (fun c => δ *ᵥ u c)).det).re * ((gramV I y v b').det).re)) /
          ((idx I (imSub I Λ δ) (fun c => δ *ᵥ u c) : ℝ) * (idx I (perpSub I Λ δ) b' : ℝ)) := by
          rw [Finset.prod_mul_distrib, div_mul_div_comm]
      _ ≤ (∏ v, (hsN (amat I x y v δ) ^ (2 * k) * ‖I.φ v (pairM I b' u).det‖ ^ 2)) /
          ((idx I (imSub I Λ δ) (fun c => δ *ᵥ u c) : ℝ) * (idx I (perpSub I Λ δ) b' : ℝ)) := by
          apply div_le_div_of_nonneg_right _ (mul_pos hi1' hi2').le
          exact Finset.prod_le_prod₀ (fun v _ => mul_nonneg (gram_nonneg hDM I x v _) (gram_nonneg hDM I y v _))
            (fun v _ => hArch I x y δ k u b' v hind1 hspan1 hind2 hperp)
      _ = (∏ v, hsN (amat I x y v δ)) ^ (2 * k) * |((Algebra.norm ℚ (pairM I b' u).det : ℚ) : ℝ)| /
          ((idx I (imSub I Λ δ) (fun c => δ *ᵥ u c) : ℝ) * (idx I (perpSub I Λ δ) b' : ℝ)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow, hNP']
      _ ≤ (∏ v, hsN (amat I x y v δ)) ^ (2 * k) := by
          rw [div_le_iff₀ (mul_pos hi1' hi2')]
          exact mul_le_mul_of_nonneg_left hN (pow_nonneg hHp _)
  exact le_of_pow_le_pow_left₀ (by omega) hHp key

end PI.UnitaryGroupMassFormula.LCG
end
end

