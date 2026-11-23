module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.NegBound
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.EqZeroOfNegMap

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.ColsConjTranspose
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section
namespace PI.FrameInd.UPosW

def cols (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) :
    Matrix (Fin (2 * r + k + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ :=
  Matrix.of fun p j => gramVec k r z z' γ j p

lemma cols_conjTranspose (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) :
    (cols k r z z' γ)ᴴ = Matrix.of fun i j => star (gramVec k r z z' γ i j) := by
  ext i j
  simp only [cols, Matrix.conjTranspose_apply, Matrix.of_apply]

lemma gram_eq (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) :
    (cols k r z z' γ)ᴴ * Hpk k r * cols k r z z' γ = gramM k r z z' γ := by
  ext i j
  rw [cols_conjTranspose]
  simp only [Matrix.mul_apply, Matrix.of_apply, cols, gramM, herm, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

lemma herm_cols (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r)
    (c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) :
    herm (Hpk k r) (cols k r z z' γ *ᵥ c) (cols k r z z' γ *ᵥ c) = star c ⬝ᵥ (gramM k r z z' γ *ᵥ c) := by
  rw [← gram_eq]
  simp only [herm, Matrix.star_mulVec]
  rw [← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

lemma herm_perp (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r)
    (v : Fin (2 * r + k + 1) → ℂ) (hv : v ∈ Uperp k r z z' γ) (c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) :
    herm (Hpk k r) v (cols k r z z' γ *ᵥ c) = 0 := by
  have h0 : ((cols k r z z' γ)ᴴ * Hpk k r) *ᵥ v = 0 := by
    have h := hv
    simp only [Uperp, LinearMap.mem_ker, Matrix.mulVecLin_apply] at h
    rw [cols_conjTranspose]
    exact h
  simp only [herm, Matrix.star_mulVec]
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h0, dotProduct_zero]

lemma herm_perp' (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r)
    (v : Fin (2 * r + k + 1) → ℂ) (hv : v ∈ Uperp k r z z' γ) (c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) :
    herm (Hpk k r) (cols k r z z' γ *ᵥ c) v = 0 := by
  rw [ggHerm_swap _ (Formalism.QuantumDeterminants.GBasic.Hpk_herm k r), herm_perp k r z z' γ v hv c, star_zero]

lemma herm_add_smul {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (w v : Fin n → ℂ) (t : ℂ)
    (h1 : herm H v w = 0) (h2 : herm H w v = 0) :
    herm H (w + t • v) (w + t • v) = herm H w w + (star t * t) * herm H v v := by
  simp only [herm] at h1 h2 ⊢
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, star_add, star_smul, add_dotProduct,
    dotProduct_add, smul_dotProduct, dotProduct_smul, h1, h2, smul_eq_mul]
  ring

lemma blk_re {m : ℕ} (a : Fin m → ℂ) :
    (star (Sum.elim (0 : Fin m → ℂ) a) ⬝ᵥ
      (fromBlocks (1 : Matrix (Fin m) (Fin m) ℂ) 0 0 (-1) *ᵥ Sum.elim (0 : Fin m → ℂ) a)).re =
      -∑ b, Complex.normSq (a b) := by
  have hm : fromBlocks (1 : Matrix (Fin m) (Fin m) ℂ) 0 0 (-1) *ᵥ Sum.elim (0 : Fin m → ℂ) a =
      Sum.elim (0 : Fin m → ℂ) (-a) := by
    ext i
    cases i <;> simp [Matrix.fromBlocks_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec]
  rw [hm]
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.star_apply,
    Pi.zero_apply, Pi.neg_apply, star_zero, zero_mul, Finset.sum_const_zero, zero_add,
    Complex.re_sum, Complex.normSq_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  ring

def emb (m : ℕ) : (Fin m → ℂ) →ₗ[ℂ] (Fin m ⊕ Fin m → ℂ) where
  toFun a := Sum.elim 0 a
  map_add' a b := by funext i; cases i <;> simp
  map_smul' c a := by funext i; cases i <;> simp

theorem uPos_of (hN : NegBound) : UPos := by
  intro k r z z' γ hs hp hdet hQ v hv hv0
  obtain ⟨Q, -, hQG⟩ := hQ
  by_contra hneg
  have hvv : (herm (Hpk k r) v v).re ≤ 0 := not_lt.mp hneg
  let L : (Fin (r + 1) → ℂ) →ₗ[ℂ] (Fin (2 * r + k + 1) → ℂ) :=
    (Matrix.mulVecLin (cols k r z z' γ * Q)).comp (emb (r + 1))
  have hLa : ∀ a, L a = cols k r z z' γ *ᵥ (Q *ᵥ Sum.elim 0 a) := by
    intro a
    show (cols k r z z' γ * Q) *ᵥ Sum.elim 0 a = _
    rw [Matrix.mulVec_mulVec]
  have hLre : ∀ a, (herm (Hpk k r) (L a) (L a)).re = -∑ b, Complex.normSq (a b) := by
    intro a
    rw [hLa, herm_cols, ← blk_re a, ← hQG, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hperp : ∀ a, herm (Hpk k r) v (L a) = 0 ∧ herm (Hpk k r) (L a) v = 0 := fun a => by
    rw [hLa]
    exact ⟨herm_perp k r z z' γ v hv _, herm_perp' k r z z' γ v hv _⟩
  let M : ((Fin (r + 1) → ℂ) × ℂ) →ₗ[ℂ] (Fin (2 * r + k + 1) → ℂ) :=
    L.coprod (LinearMap.toSpanSingleton ℂ _ v)
  have hM : ∀ p, M p = L p.1 + p.2 • v := fun p => by
    simp [M, LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply]
  have hMre : ∀ p, (herm (Hpk k r) (M p) (M p)).re =
      -∑ b, Complex.normSq (p.1 b) + Complex.normSq p.2 * (herm (Hpk k r) v v).re := by
    intro p
    have ht : star p.2 * p.2 = (Complex.normSq p.2 : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]; rfl
    rw [hM, herm_add_smul _ _ _ _ (hperp p.1).1 (hperp p.1).2, Complex.add_re, hLre, ht,
      Complex.re_ofReal_mul]
  have hsum : ∀ a : Fin (r + 1) → ℂ, 0 ≤ ∑ b, Complex.normSq (a b) :=
    fun a => Finset.sum_nonneg fun b _ => Complex.normSq_nonneg _
  have hnp : ∀ x ∈ LinearMap.range M, (herm (Hpk k r) x x).re ≤ 0 := by
    rintro x ⟨p, rfl⟩
    rw [hMre]
    have h1 := hsum p.1
    have h2 : Complex.normSq p.2 * (herm (Hpk k r) v v).re ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) hvv
    linarith
  have hinj : Function.Injective M := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp0
    have hre := hMre p
    rw [hp0] at hre
    have h0 : (herm (Hpk k r) (0 : Fin (2 * r + k + 1) → ℂ) 0).re = 0 := by simp [herm]
    rw [h0] at hre
    have h1 := hsum p.1
    have h2 : Complex.normSq p.2 * (herm (Hpk k r) v v).re ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) hvv
    have hs0 : ∑ b, Complex.normSq (p.1 b) = 0 := by linarith
    have ha : p.1 = 0 := by
      funext b
      have hb := (Finset.sum_eq_zero_iff_of_nonneg
        (fun b _ => Complex.normSq_nonneg (p.1 b))).1 hs0 b (Finset.mem_univ b)
      simpa using hb
    have ht : p.2 • v = 0 := by
      rw [hM, ha, map_zero, zero_add] at hp0
      exact hp0
    exact Prod.ext ha ((smul_eq_zero.1 ht).resolve_right hv0)
  have hdim := hN k r (LinearMap.range M) hnp
  rw [LinearMap.finrank_range_of_inj hinj] at hdim
  simp [Module.finrank_prod, Module.finrank_fin_fun] at hdim

end PI.FrameInd.UPosW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.FinrankUperpOfDet
section
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section

namespace PI.FrameInd

def Vc (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) :
    Matrix (Fin (2 * r + k + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ :=
  Matrix.of fun l i => gramVec k r z z' g i l

lemma herm_mulVec_mulVec {ι κ : Type*} [Fintype ι] [Fintype κ] (H : Matrix ι ι ℂ) (A : Matrix ι κ ℂ)
    (v w : κ → ℂ) : herm H (A *ᵥ v) (A *ᵥ w) = herm (Aᴴ * H * A) v w := by
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

lemma gramM_eq (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) :
    gramM k r z z' g = (Vc k r z z' g)ᴴ * Hpk k r * Vc k r z z' g := by
  ext i j
  simp only [gramM, herm, Vc, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, dotProduct,
    Matrix.mulVec, Finset.sum_mul, Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

lemma Uperp_mat (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) :
    Uperp k r z z' g = LinearMap.ker (Matrix.mulVecLin ((Vc k r z z' g)ᴴ * Hpk k r)) := rfl

lemma herm_Vc (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) (c d : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) :
    herm (Hpk k r) (Vc k r z z' g *ᵥ c) (Vc k r z z' g *ᵥ d) = herm (gramM k r z z' g) c d := by
  rw [herm_mulVec_mulVec, ← gramM_eq]

lemma Vc_mulVec (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r) (c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) :
    Vc k r z z' g *ᵥ c = ∑ i, c i • gramVec k r z z' g i := by
  ext l
  simp [Vc, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

lemma Vc_inj (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r)
    (hdet : (gramM k r z z' g).det ≠ 0) (c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ)
    (hc : Vc k r z z' g *ᵥ c = 0) : c = 0 := by
  have h1 : gramM k r z z' g *ᵥ c = 0 := by
    funext j
    have h2 := herm_Vc k r z z' g c (Pi.single j 1)
    rw [hc] at h2
    simp only [herm, Matrix.mulVec_zero, dotProduct_zero] at h2
    rw [Pi.zero_apply]
    have h3 : star (Pi.single j (1 : ℂ)) ⬝ᵥ (gramM k r z z' g *ᵥ c) = (gramM k r z z' g *ᵥ c) j := by
      simp [dotProduct, Pi.single_apply]
    rw [← h3, ← h2]
  exact Matrix.eq_zero_of_mulVec_eq_zero hdet h1

theorem indep_of_det (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r)
    (hdet : (gramM k r z z' g).det ≠ 0) : LinearIndependent ℂ (gramVec k r z z' g) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have h1 : Vc k r z z' g *ᵥ c = 0 := by rw [Vc_mulVec]; exact hc
  exact congrFun (Vc_inj k r z z' g hdet c h1) i

theorem finrank_Uperp_of_det (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r)
    (hdet : (gramM k r z z' g).det ≠ 0) :
    Module.finrank ℂ (Uperp k r z z' g) = k - 1 := by
  obtain ⟨R, hR⟩ : ∃ R, R = (Vc k r z z' g)ᴴ * Hpk k r := ⟨_, rfl⟩
  have hRV : R * Vc k r z z' g = gramM k r z z' g := by rw [hR, gramM_eq]
  have hrk1 : (gramM k r z z' g).rank = 2 * r + 2 := by
    rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))]
    simp; ring
  have hrk2 : (gramM k r z z' g).rank ≤ R.rank := by rw [← hRV]; exact Matrix.rank_mul_le_left _ _
  have hrk3 : R.rank ≤ 2 * r + 2 := by
    have := Matrix.rank_le_card_height R
    simp at this; omega
  have hrn := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin R)
  have hrank : R.rank = Module.finrank ℂ (LinearMap.range (Matrix.mulVecLin R)) := rfl
  rw [Uperp_mat, ← hR]
  simp only [Module.finrank_fin_fun] at hrn
  omega

theorem det_ne (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (hs : Std k r z z')
    (hp : PosPt k r z z' γ) : (gramM k r z z' γ).det ≠ 0 := by
  intro h0
  have h := Formalism.QuantumDeterminants.group_gram_holds k r z z' hs.2.1.1 hs.2.2.1 γ hp.1
  rw [h0, mul_zero] at h
  have : Gf k r z z' γ = 0 := by exact_mod_cast h
  linarith [hp.2]

end PI.FrameInd
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.NegativeBound
section
open Matrix Formalism.QuantumDeterminants

noncomputable section
namespace PI.FrameInd

theorem negative_bound : NegBound := fun k r S hS => NegB.negBound k r S hS

end PI.FrameInd
end
end

